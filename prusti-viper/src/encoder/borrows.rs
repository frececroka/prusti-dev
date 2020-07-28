// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::places;
use prusti_interface::data::ProcedureDefId;
// use prusti_interface::specifications::{
//     AssertionKind, SpecificationSet, TypedAssertion, TypedExpression, TypedSpecification,
//     TypedSpecificationSet,
// };
use rustc_hir::{self as hir, Mutability};
use rustc_middle::mir;
use rustc_middle::ty::subst::SubstsRef;
use rustc_index::vec::Idx;
use rustc_middle::ty::{self, Ty, TyCtxt};
// use rustc_data_structures::indexed_vec::Idx;
use std::collections::HashMap;
use std::hash::Hash;
use std::fmt;
use crate::utils::type_visitor::{self, TypeVisitor};
use prusti_interface::specs::typed;
use prusti_interface::environment::reborrow_signature::ReborrowSignature;
use prusti_interface::environment::mir_utils::PlaceAddProjection;
use log::{trace, debug};

#[derive(Clone, Debug)]
pub struct BorrowInfo<P>
where
    P: fmt::Debug,
{
    pub blocking_paths: Vec<(P, Mutability)>,
    pub blocked_paths: Vec<(P, Mutability)>,
}

/// Contract of a specific procedure. It is a separate struct from a
/// general procedure info because we want to be able to translate
/// procedure calls before translating call targets.
/// TODO: Move to some properly named module.
#[derive(Clone, Debug)]
pub struct ProcedureContractGeneric<'tcx, L, P>
where
    L: fmt::Debug,
    P: fmt::Debug + Eq + Hash,
{
    /// Definition ID of the procedure to which the contract is attached.
    pub def_id: rustc_hir::def_id::DefId,
    /// Formal arguments for which we should have permissions in the
    /// precondition. This includes both borrows and moved in values.
    /// For example, if `_2` is in the vector, this means that we have
    /// `T(_2)` in the precondition.
    pub args: Vec<L>,
    /// The returned value for which we should have permission in
    /// the postcondition.
    pub returned_value: L,
    /// Magic wands passed out of the procedure.
    /// TODO: Implement support for `blocked_lifetimes` via nested magic wands.
    pub borrow_infos: ReborrowSignature<P>,
    /// The functional specification: precondition and postcondition
    pub specification: typed::SpecificationSet<'tcx>,
}

impl<'tcx, L: fmt::Debug, P: fmt::Debug + Eq + Hash> ProcedureContractGeneric<'tcx, L, P> {
    pub fn functional_precondition(&self) -> &[typed::Assertion<'tcx>] {
        if let typed::SpecificationSet::Procedure(spec) = &self.specification {
            &spec.pres
        } else {
            unreachable!("Unexpected: {:?}", self.specification)
        }
    }

    pub fn functional_postcondition(&self) -> &[typed::Assertion<'tcx>] {
        if let typed::SpecificationSet::Procedure(spec) = &self.specification {
            &spec.posts
        } else {
            unreachable!("Unexpected: {:?}", self.specification)
        }
    }

    pub fn pledges(&self) -> &[typed::Pledge<'tcx>] {
        if let typed::SpecificationSet::Procedure(spec) = &self.specification {
            &spec.pledges
        } else {
            unreachable!("Unexpected: {:?}", self.specification)
        }
    }
}

/// Procedure contract as it is defined in MIR.
pub type ProcedureContractMirDef<'tcx> = ProcedureContractGeneric<'tcx, mir::Local, mir::Place<'tcx>>;

/// Specialized procedure contract for use in translation.
pub type ProcedureContract<'tcx> = ProcedureContractGeneric<'tcx, places::Local, places::Place<'tcx>>;

impl<L: fmt::Debug, P: fmt::Debug + Eq + Hash> fmt::Display for ProcedureContractGeneric<'_, L, P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "ProcedureContract {{")?;
        writeln!(f, "IN:")?;
        for path in self.args.iter() {
            writeln!(f, "  {:?}", path)?;
        }
        writeln!(f, "OUT:")?;
        for path in self.borrow_infos.returned_inputs().iter() {
            writeln!(f, "  {:?}", path)?;
        }
        writeln!(f, "MAGIC: {:?}", self.borrow_infos)?;
        writeln!(f, "}}")
    }
}

fn get_place_root<'tcx>(place: &mir::Place<'tcx>) -> mir::Local {
    // match place {
    //     &mir::Place::Local(local) => local,
    //     &mir::Place::Projection(ref projection) => get_place_root(&projection.base),
    //     _ => unimplemented!(),
    // }
    place.local
}

impl<'tcx> ProcedureContractMirDef<'tcx> {
    /// Specialize to the definition site contract.
    pub fn to_def_site_contract(&self) -> ProcedureContract<'tcx> {
        ProcedureContract {
            def_id: self.def_id,
            args: self.args.iter().map(|&a| a.into()).collect(),
            returned_value: self.returned_value.into(),
            borrow_infos: self.borrow_infos.clone().map_with_into(),
            specification: self.specification.clone(),
        }
    }

    /// Specialize to the call site contract.
    pub fn to_call_site_contract(
        &self,
        args: &Vec<places::Local>,
        target: places::Local,
    ) -> ProcedureContract<'tcx> {
        assert_eq!(self.args.len(), args.len());
        let mut substitutions = HashMap::new();
        substitutions.insert(self.returned_value, target);
        for (from, to) in self.args.iter().zip(args) {
            substitutions.insert(*from, *to);
        }
        let borrow_infos = self.borrow_infos.clone().map(|place| {
            let root = &get_place_root(&place);
            let substituted_root = *substitutions.get(root).unwrap();
            places::Place::SubstitutedPlace { substituted_root, place }
        });
        let result = ProcedureContract {
            def_id: self.def_id,
            args: args.clone(),
            returned_value: target,
            borrow_infos,
            specification: self.specification.clone(),
        };
        result
    }
}

pub fn compute_procedure_contract<'p, 'a, 'tcx>(
    proc_def_id: ProcedureDefId,
    tcx: TyCtxt<'tcx>,
    specification: typed::SpecificationSet<'tcx>,
    maybe_tymap: Option<&HashMap<ty::Ty<'tcx>, ty::Ty<'tcx>>>,
) -> ProcedureContractMirDef<'tcx>
where
    'a: 'p,
    'tcx: 'a,
{
    trace!("[compute_borrow_infos] enter name={:?}", proc_def_id);

    let fn_sig = tcx.fn_sig(proc_def_id);
    trace!("fn_sig: {:?}", fn_sig);

    // FIXME; "skip_binder" is most likely wrong
    // FIXME: Replace with FakeMirEncoder.
    let mut args = Vec::new();
    for i in 0usize..fn_sig.inputs().skip_binder().len() {
        args.push(mir::Local::new(i + 1));
    }

    let empty_tymap = HashMap::new();
    let tymap = maybe_tymap.unwrap_or(&empty_tymap);
    let borrow_infos = ReborrowSignature::construct(tcx, tymap, proc_def_id);

    let contract = ProcedureContractGeneric {
        def_id: proc_def_id,
        args,
        returned_value: mir::RETURN_PLACE,
        borrow_infos,
        specification,
    };

    trace!("[compute_borrow_infos] exit result={}", contract);
    contract
}
