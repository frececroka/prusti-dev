use prusti_common::vir;
use prusti_common::vir::ExprIterator;
use prusti_interface::environment::borrowck::facts;
use prusti_interface::environment::mir_utils::PlaceAddProjection;
use rustc_hir::Mutability;
use rustc_middle::mir;

use crate::encoder::expires_first_domain;
use crate::encoder::places;
use crate::encoder::procedure_encoder::ProcedureEncoder;
use crate::encoder::procedure_encoder::Result;

use super::ExpirationTool;
use super::MagicWand;

impl<'p, 'v: 'p, 'tcx: 'v> ProcedureEncoder<'p, 'v, 'tcx> {
    pub fn encode_expiration_tool_end_of_method(&mut self,
        expiration_tool: &ExpirationTool<'tcx>,
        location: mir::Location,
        pre_label: &str,
        post_label: &str
    ) -> Result<Vec<vir::Stmt>> {
        // All blocked permissions must be folded before the post label.
        let obtains = expiration_tool.blocking.iter()
            .flat_map(|place| {
                let place_perm = self.encode_place_perm(place, Mutability::Mut, None, post_label);
                let place_perm = place_perm.map_labels(|label|
                    if label == post_label { None } else { Some(label) });
                self.encode_obtain(place_perm, vir::Position::default())
            })
            .collect::<Vec<_>>();

        // The post label
        let post_label_stmt = vec![vir::Stmt::Label(post_label.to_owned())];

        // The expiration tool proper.
        let package_stmts = self.encode_expiration_tool_as_package(
            &expiration_tool, location, pre_label, post_label)?;

        // Everything concatenated.
        Ok([
            &obtains[..],
            &post_label_stmt[..],
            &package_stmts[..]
        ].concat())
    }

    /// This encodes the given expiration tool as a sequence of Viper statements that package
    /// all the magic wands it contains directly.
    pub fn encode_expiration_tool_as_package(&mut self,
        expiration_tool: &ExpirationTool<'tcx>,
        location: mir::Location,
        pre_label: &str,
        post_label: &str
    ) -> Result<Vec<vir::Stmt>> {
        expiration_tool.magic_wands().map(|magic_wand| {
            let encoded_magic_wand = self.encode_magic_wand_as_package(
                magic_wand, location, pre_label, post_label)?;
            let expired_place = expiration_tool.place_mapping[&magic_wand.expired];
            let expires_first = vir::Expr::domain_func_app(
                expires_first_domain::EXPIRES_FIRST.clone(),
                vec![vir::Expr::const_int(expired_place as i64)]);
            Ok(vir!(if ([expires_first]) { [encoded_magic_wand] }))
        }).collect()
    }

    /// This encodes the given magic wand as a Viper package statement.
    fn encode_magic_wand_as_package(&mut self,
        magic_wand: &MagicWand<'tcx>,
        location: mir::Location,
        pre_label: &str,
        post_label: &str
    ) -> Result<vir::Stmt> {
        let magic_wand_expr = self.encode_magic_wand_as_expression(
            magic_wand, pre_label, post_label);
        let (lhs, rhs) = match magic_wand_expr {
            vir::Expr::MagicWand(lhs, rhs, _, _) => (lhs.as_ref().clone(), rhs.as_ref().clone()),
            _ => unreachable!()
        };

        // Determine the actual reference that is expired.
        let expired_place = if let places::Place::NormalPlace(place) = &magic_wand.expired {
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
        let base = expired_place.truncate(self.procedure.get_tcx(), 1);
        let region = self.polonius_info().place_regions.for_place(base).unwrap();
        let point_index = self.polonius_info().get_point(location, facts::PointType::Start);
        let (expired_loans, expired_zombie_loans) =
            self.polonius_info().get_all_loans_kept_alive_by(point_index, region);

        // Expire the loans that are kept alive by this reference.
        let expire_loans = self.encode_expiration_of_loans(
            expired_loans, &expired_zombie_loans, location, None)?;

        // Fold the places that are unblocked by this magic wand.
        let fold_unblocked = magic_wand.unblocked()
            .flat_map(|unblocked| {
                let (unblocked, _, _) = self.encode_generic_place(
                    self.procedure.get_id(), None, unblocked);
                let unblocked = vir::Expr::pred_permission(
                    unblocked, vir::PermAmount::Write
                ).unwrap();
                self.encode_obtain(unblocked, vir::Position::default())
            })
            .collect::<Vec<_>>();

        // Package the nested expiration tools.
        let package_nested = magic_wand.expiration_tools.iter()
            .map(|et|
                self.encode_expiration_tool_as_package(et, location, pre_label, post_label))
            .collect::<Result<Vec<_>>>()?
            .into_iter().flatten()
            .collect::<Vec<_>>();

        let package_body_stmts: Vec<_> = [&expire_loans[..], &fold_unblocked[..], &package_nested[..]].concat();
        let package_stmt = vir::Stmt::package_magic_wand(
            lhs, rhs, package_body_stmts,
            post_label.to_owned(),
            vec![],
            vir::Position::default());

        Ok(package_stmt)
    }

    /// This encodes the given expiration tool as a Viper expression.
    pub fn encode_expiration_tool_as_expression(&self,
        expiration_tool: &ExpirationTool<'tcx>,
        pre_label: &str,
        post_label: &str
    ) -> vir::Expr {
        expiration_tool.magic_wands()
            .map(|magic_wand| {
                let expired_place = expiration_tool.place_mapping[&magic_wand.expired];
                let antecedent = vir::Expr::domain_func_app(
                    expires_first_domain::EXPIRES_FIRST.clone(),
                    vec![vir::Expr::const_int(expired_place as i64)]);
                let encoded_magic_wand = self.encode_magic_wand_as_expression(
                    magic_wand, pre_label, post_label);
                vir!([antecedent] ==> [encoded_magic_wand])
            })
            .conjoin()
    }

    /// This encodes the given magic wand as a Viper expression.
    fn encode_magic_wand_as_expression(&self,
        magic_wand: &MagicWand<'tcx>,
        pre_label: &str,
        post_label: &str
    ) -> vir::Expr {
        let expired = self.encode_place_perm(
            &magic_wand.expired, Mutability::Mut, None, post_label);
        let unblocked = magic_wand.unblocked()
            .map(|unblocked|
                self.encode_place_perm(unblocked, Mutability::Mut, None, pre_label));
        let nested_expiration_tools = magic_wand.expiration_tools.iter()
            .map(|expiration_tool|
                self.encode_expiration_tool_as_expression(
                    expiration_tool, pre_label, post_label));
        let rhs = unblocked.chain(nested_expiration_tools).conjoin();
        vir!([expired] --* [rhs])
    }

    fn encode_place_perm(&self,
        place: &places::Place<'tcx>,
        mutability: Mutability,
        location: Option<mir::Location>,
        label: &str
    ) -> vir::Expr {
        let perm_amount = match mutability {
            Mutability::Not => vir::PermAmount::Read,
            Mutability::Mut => vir::PermAmount::Write,
        };
        let (place_expr, place_ty, _) = self.encode_generic_place(
            self.procedure.get_id(), location, place);
        let vir_access = vir::Expr::pred_permission(place_expr.clone().old(label), perm_amount)
            .unwrap();
        let inv = self.encoder.encode_invariant_func_app(
            place_ty, place_expr.old(label));
        vir::Expr::and(vir_access, inv)
    }
}
