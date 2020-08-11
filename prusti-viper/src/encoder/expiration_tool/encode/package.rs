use prusti_common::vir;
use prusti_interface::environment::borrowck::facts;
use prusti_interface::environment::mir_utils::PlaceAddProjection;
use rustc_middle::mir;

use crate::encoder::expires_first_domain;
use crate::encoder::places;
use crate::encoder::procedure_encoder::ProcedureEncoder;
use crate::encoder::procedure_encoder::Result;

use super::ExpirationTool;
use super::MagicWand;

impl<'p, 'v: 'p, 'tcx: 'v> ProcedureEncoder<'p, 'v, 'tcx> {
    /// This encodes the given expiration tool as a sequence of Viper statements that package
    /// all the magic wands it contains directly.
    pub(super) fn expiration_tool_as_package(&mut self,
        expiration_tool: &ExpirationTool<'tcx>,
        location: mir::Location,
        encoded_args: &[vir::Expr],
        encoded_return: &vir::Expr,
        pre_label: &str,
        post_label: &str
    ) -> Result<Vec<vir::Stmt>> {
        expiration_tool.magic_wands().map(|magic_wand| {
            let encoded_magic_wand = self.magic_wand_as_package(
                magic_wand, location, encoded_args, encoded_return, pre_label, post_label)?;
            let expired_place = expiration_tool.place_mapping[magic_wand.expired()];
            let expires_first = vir::Expr::domain_func_app(
                expires_first_domain::EXPIRES_FIRST.clone(),
                vec![vir::Expr::const_int(expired_place as i64)]);
            Ok(vir!(if ([expires_first]) { [encoded_magic_wand] }))
        }).collect()
    }

    /// This encodes the given magic wand as a Viper package statement.
    fn magic_wand_as_package(&mut self,
        magic_wand: &MagicWand<'tcx>,
        location: mir::Location,
        encoded_args: &[vir::Expr],
        encoded_return: &vir::Expr,
        pre_label: &str,
        post_label: &str
    ) -> Result<vir::Stmt> {
        let (magic_wand_expr, _) = self.magic_wand_as_expression(
            magic_wand, encoded_args, encoded_return, pre_label, post_label);
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
            .map(|et| self.expiration_tool_as_package(
                et, location, encoded_args, encoded_return, pre_label, post_label
            ))
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
}
