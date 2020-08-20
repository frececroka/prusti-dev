use itertools::Itertools;

use prusti_common::vir;
use prusti_interface::environment::borrowck::facts;
use prusti_interface::environment::mir_utils::PlaceAddProjection;
use rustc_hir::Mutability;
use rustc_middle::mir;

use crate::encoder::borrows::ProcedureContract;
use crate::encoder::places;
use crate::encoder::procedure_encoder::ProcedureEncoder;
use crate::encoder::procedure_encoder::Result;
use crate::utils::fresh_name::FreshName;

use super::binding::Binding;
use super::binding::encode_binding;
use super::binding::LiftBindings;
use super::ExpirationToolEncoder;
use super::super::ExpirationTool;
use super::super::MagicWand;

impl<'p, 'v: 'p, 'tcx: 'v> ProcedureEncoder<'p, 'v, 'tcx> {
    pub fn encode_expiration_tool_as_package(&mut self,
        expiration_tools: &[ExpirationTool<'tcx>],
        contract: &ProcedureContract<'tcx>,
        location: mir::Location,
        pre_label: &str,
        post_label: &str
    ) -> Result<Vec<vir::Stmt>> {
        // All blocked permissions must be folded before the post label.
        let obtains = expiration_tools.iter()
            .flat_map(|expiration_tool| &expiration_tool.blocking)
            .flat_map(|place| {
                let place_perm = self.encode_place_perm(place, Mutability::Mut, None, post_label);
                let place_perm = place_perm.map_labels(|label|
                    if label == post_label { None } else { Some(label) });
                self.encode_obtain(place_perm, vir::Position::default())
            })
            .collect::<Vec<_>>();

        // The post label.
        let post_label_stmt = vec![vir::Stmt::Label(post_label.to_owned())];

        let mut encoder = ExpirationToolEncoder::new(
            self, contract, Some(location), None, pre_label, post_label);

        // The expiration tool proper.
        let mut fresh_name = FreshName::new("et");
        let (package_stmts, bindings): (Vec<_>, Vec<_>) = expiration_tools.into_iter()
            .map(|expiration_tool| {
                let fresh_name = fresh_name.next_child();
                encoder.expiration_tool_as_package(expiration_tool, fresh_name)
            })
            .collect::<Result<Vec<_>>>()?
            .into_iter().lift_bindings();
        let package_stmts = package_stmts.into_iter().flatten().collect::<Vec<_>>();

        // If there are still open bindings at this point we did something wrong.
        assert_eq!(bindings.len(), 0);

        // Everything concatenated.
        Ok([
            &obtains[..],
            &post_label_stmt[..],
            &package_stmts[..]
        ].concat())
    }
}

impl<'a, 'p, 'v: 'p, 'tcx: 'v> ExpirationToolEncoder<'a, 'p, 'v, 'tcx> {
    /// This encodes the given expiration tool as a sequence of Viper statements that package
    /// all the magic wands it contains directly.
    pub(super) fn expiration_tool_as_package(&mut self,
        expiration_tool: &ExpirationTool<'tcx>,
        fresh_name: FreshName,
    ) -> Result<(Vec<vir::Stmt>, Vec<Binding>)> {
        self.encode_expiration_tool_branches(
            expiration_tool, fresh_name,
            |encoder, antecedent, magic_wand, fresh_name| {
                let (encoded_magic_wand, bindings) =
                    encoder.magic_wand_as_package(magic_wand, fresh_name)?;
                let branch = vir!(if ([antecedent]) { [encoded_magic_wand] });
                Ok((branch, bindings))
            }
        )
    }

    /// This encodes the given magic wand as a Viper package statement.
    fn magic_wand_as_package(&mut self,
        magic_wand: &MagicWand<'tcx>,
        mut fresh_name: FreshName
    ) -> Result<(vir::Stmt, Vec<Binding>)> {
        let (magic_wand_expr, magic_wand_bindings) =
            self.magic_wand_as_expression(magic_wand, fresh_name.clone());
        let (lhs, rhs) = match magic_wand_expr {
            vir::Expr::MagicWand(lhs, rhs, _, _) => (lhs.as_ref().clone(), rhs.as_ref().clone()),
            _ => unreachable!()
        };

        // Determine the actual reference that is expired.
        let expired_place = if let places::Place::NormalPlace(place) = magic_wand.expired() {
            place
        } else {
            unreachable!(format!("cannot expire place {:?}, because it is not a normal place",
                magic_wand.expired))
        };

        // Assert that it is a dereference.
        assert_eq!(expired_place.projection.last(), Some(&mir::ProjectionElem::Deref),
            "cannot expire place {:?}, because it is not a dereference",
            magic_wand.expired);

        // Determine the loans that are kept alive by this reference.
        let base = expired_place.truncate(self.procedure_encoder.procedure.get_tcx(), 1);
        let region = self.procedure_encoder.polonius_info().place_regions.for_place(base).unwrap();
        let point_index = self.procedure_encoder.polonius_info().get_point(
            self.return_location.unwrap(), facts::PointType::Start);
        let (expired_loans, expired_zombie_loans) =
            self.procedure_encoder.polonius_info().get_all_loans_kept_alive_by(point_index, region);

        // Expire the loans that are kept alive by this reference.
        let expire_loans = self.procedure_encoder.encode_expiration_of_loans(
            expired_loans, &expired_zombie_loans, self.return_location.unwrap(), None)?;

        // Fold the places that are unblocked by this magic wand.
        let transfer_permissions_to_old = magic_wand.unblocked()
            .flat_map(|unblocked| self.procedure_encoder.transfer_permissions_to_old(
                unblocked, self.return_location.unwrap(), &self.encoded_args, self.pre_label))
            .collect::<Vec<_>>();

        // Fold the places that are unblocked by this magic wand.
        let fold_unblocked_references = magic_wand.unblocked()
            .flat_map(|unblocked| self.procedure_encoder.fold_unblocked_reference(
                unblocked, &self.encoded_args, self.pre_label))
            .collect::<Vec<_>>();

        // Package the nested expiration tools.
        let (package_expiration_tools, expiration_tools_bindings): (Vec<_>, Vec<_>) =
            magic_wand.expiration_tools()
                .map(|et| {
                    let fresh_name = fresh_name.next_child();
                    self.expiration_tool_as_package(et, fresh_name)
                })
                .collect::<Result<Vec<_>>>()?.into_iter()
                .lift_bindings();
        let package_expiration_tools = package_expiration_tools
            .into_iter().flatten().collect::<Vec<_>>();

        // Determine which of the bindings required by the nested expiration tools are "ripe"
        // (and can be turned into variables right away) and which bindings need to be passed on
        // to the parent expiration tool.
        let (ripe_expiration_tools_bindings, expiration_tools_bindings) =
            self.partition_bindings(expiration_tools_bindings,
                magic_wand.expired(), magic_wand.unblocked());

        let (vars, materialize_ripe_expiration_tools_bindings): (Vec<_>, Vec<_>) =
            ripe_expiration_tools_bindings.into_iter().map(|binding| {
                let (var, expr) = encode_binding(binding);
                let assignment = vir::Stmt::Assign(
                    vir::Expr::local(var.clone()), expr, vir::AssignKind::Copy);
                (var, assignment)
            }).unzip();

        // The open bindings are the ones that are required by this magic wand itself or by any
        // of the nested expiration tools.
        let open_bindings = std::iter::empty()
            .chain(magic_wand_bindings)
            .chain(expiration_tools_bindings)
            .unique_by(|(var, _, _)| var.clone())
            .collect();

        let package_body_stmts: Vec<_> = [
            &expire_loans[..],
            &transfer_permissions_to_old[..],
            &materialize_ripe_expiration_tools_bindings[..],
            &fold_unblocked_references[..],
            &package_expiration_tools[..]
        ].concat();
        let package_stmt = vir::Stmt::package_magic_wand(
            lhs, rhs, package_body_stmts,
            self.post_label.to_owned(),
            vars,
            vir::Position::default());

        Ok((package_stmt, open_bindings))
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> ProcedureEncoder<'p, 'v, 'tcx> {
    // TODO: What purpose serves this?
    fn transfer_permissions_to_old(&mut self,
        unblocked: &places::Place<'tcx>,
        location: mir::Location,
        encoded_args: &[vir::Expr],
        pre_label: &str
    ) -> Vec<vir::Stmt> {
        let (unblocked, _, _) = self.encode_generic_place(
            self.procedure.get_id(), None, unblocked);
        let contract = self.procedure_contract.as_ref().unwrap();
        let old_unblocked = self.wrap_arguments_into_old(
            unblocked.clone(), pre_label, contract, encoded_args);

        self.encode_transfer_permissions(unblocked, old_unblocked.clone(), location)
    }

    fn fold_unblocked_reference(&mut self,
        unblocked: &places::Place<'tcx>,
        encoded_args: &[vir::Expr],
        pre_label: &str
    ) -> Vec<vir::Stmt> {
        let (unblocked, _, _) = self.encode_generic_place(
            self.procedure.get_id(), None, unblocked);
        let contract = self.procedure_contract.as_ref().unwrap();
        let old_unblocked = self.wrap_arguments_into_old(
            unblocked.clone(), pre_label, contract, encoded_args);

        // Obtain the unblocked permission.
        let unblocked = vir::Expr::pred_permission(
            old_unblocked, vir::PermAmount::Write
        ).unwrap();
        self.encode_obtain(unblocked, vir::Position::default())
    }
}
