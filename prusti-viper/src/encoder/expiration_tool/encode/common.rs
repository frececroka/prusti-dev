use prusti_common::vir;

use crate::encoder::expires_first_domain;
use crate::encoder::procedure_encoder::Result;

use super::binding::Binding;
use super::binding::LiftBindings;
use super::ExpirationToolEncoder;
use super::super::ExpirationTool;
use super::super::MagicWand;

impl<'a, 'p, 'v: 'p, 'tcx: 'v> ExpirationToolEncoder<'a, 'p, 'v, 'tcx> {
    pub(super) fn encode_expiration_tool_branches<B>(&mut self,
        expiration_tool: &ExpirationTool<'tcx>,
        mut encode_branch: impl FnMut(
            &mut Self, vir::Expr, &MagicWand<'tcx>
        ) -> Result<(B, Vec<Binding>)>
    ) -> Result<(Vec<B>, Vec<Binding>)> {
        let blocking_representative = expiration_tool.blocking.len();
        let branches = expiration_tool.magic_wands()
            .map(|magic_wand| {
                let expired_place = expiration_tool.place_mapping[magic_wand.expired()];
                let antecedent = vir::Expr::domain_func_app(
                    expires_first_domain::EXPIRES_FIRST.clone(),
                    vec![
                        vir::Expr::const_int(expired_place as i64),
                        vir::Expr::const_int(blocking_representative as i64)]);
                encode_branch(self, antecedent, magic_wand)
            })
            .collect::<Result<Vec<_>>>()?
            .into_iter().lift_bindings();
        Ok(branches)
    }
}
