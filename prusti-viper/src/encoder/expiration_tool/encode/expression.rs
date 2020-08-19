use prusti_common::vir;
use prusti_common::vir::ExprIterator;
use rustc_hir::Mutability;
use rustc_middle::mir;

use crate::encoder::procedure_encoder::ProcedureEncoder;
use crate::utils::fresh_name::FreshName;

use super::binding::Binding;
use super::binding::encode_binding;
use super::ExpirationToolEncoder;
use super::LiftBindings;
use super::super::ExpirationTool;
use super::super::MagicWand;
use super::utils::replace_old_expression;

impl<'p, 'v: 'p, 'tcx: 'v> ProcedureEncoder<'p, 'v, 'tcx> {
    pub fn encode_expiration_tool_as_expression(&mut self,
        expiration_tools: &[ExpirationTool<'tcx>],
        call_location: Option<mir::Location>,
        pre_label: &str,
        post_label: &str
    ) -> vir::Expr {
        let mut encoder = ExpirationToolEncoder::new(
            self, None, call_location, pre_label, post_label);

        let mut fresh_name = FreshName::new("et");
        let (encoded_expiration_tools, bindings): (Vec<_>, Vec<_>) = expiration_tools.into_iter()
            .map(|expiration_tool| {
                let fresh_name = fresh_name.next_child();
                encoder.expiration_tool_as_expression(expiration_tool, fresh_name)
            })
            .collect::<Vec<_>>()
            .into_iter().lift_bindings();
        let encoded_expiration_tools = encoded_expiration_tools.into_iter().conjoin();

        // If there are still open bindings at this point we did something wrong.
        assert!(bindings.is_empty());

        encoded_expiration_tools
    }
}

impl<'a, 'p, 'v: 'p, 'tcx: 'v> ExpirationToolEncoder<'a, 'p, 'v, 'tcx> {
    /// This encodes the given expiration tool as a Viper expression.
    pub(super) fn expiration_tool_as_expression(&mut self,
        expiration_tool: &ExpirationTool<'tcx>,
        fresh_name: FreshName
    ) -> (vir::Expr, Vec<Binding>) {
        let (branches, bindings) = self.encode_expiration_tool_branches(
            expiration_tool, fresh_name,
            |encoder, antecedent, magic_wand, fresh_name| {
                let (encoded_magic_wand, bindings) =
                    encoder.magic_wand_as_expression(magic_wand, fresh_name);
                let encoded_branch = vir!([antecedent] ==> [encoded_magic_wand]);
                Ok((encoded_branch, bindings))
            }
        ).unwrap();
        let branches = branches.into_iter().conjoin();
        (branches, bindings)
    }

    /// This encodes the given magic wand as a Viper expression.
    pub(super) fn magic_wand_as_expression(&mut self,
        magic_wand: &MagicWand<'tcx>,
        mut fresh_name: FreshName
    ) -> (vir::Expr, Vec<Binding>) {
        let expired_perm = self.procedure_encoder.encode_place_perm(
            magic_wand.expired(), Mutability::Mut, self.call_location, self.post_label);

        let unblocked_perm = magic_wand.unblocked()
            .map(|unblocked| self.procedure_encoder.encode_place_perm(
                unblocked, Mutability::Mut, self.call_location, self.pre_label
            ))
            .conjoin();

        let nested_expiration_tools = magic_wand.expiration_tools()
            .map(|expiration_tool| {
                let fresh_name = fresh_name.next_child();
                self.expiration_tool_as_expression(expiration_tool, fresh_name)
            })
            .collect::<Vec<_>>();

        let pledges = magic_wand.pledges()
            .map(|pledge| self.encode_pledge(pledge))
            .map(|pledge| replace_old_expression(pledge, &mut fresh_name))
            .collect::<Vec<_>>();

        // A list of conjuncts representing the encoded pledges and expiration tools, with a list
        // of open bindings.
        let (pledges_and_nested_expiration_tools, bindings): (Vec<_>, Vec<_>) = std::iter::empty()
            .chain(pledges)
            .chain(nested_expiration_tools)
            .lift_bindings();

        // A single expression encoding the pledges and nested expiration tools, still without let
        // bindings.
        let pledges_and_nested_expiration_tools =
            pledges_and_nested_expiration_tools.into_iter().conjoin();

        let (ripe_bindings, bindings) = self.partition_bindings(
            bindings, magic_wand.expired(), magic_wand.unblocked());

        // Wrap the pledges and nested expiration tools with the let bindings that can be evaluated
        // right now.
        let pledges_and_nested_expiration_tools = ripe_bindings.into_iter()
            .fold(pledges_and_nested_expiration_tools, |rhs, binding| {
                let (var, expr) = encode_binding(binding);
                let pos = rhs.pos();
                vir::Expr::LetExpr(var, Box::new(expr), Box::new(rhs), pos)
            });

        let expr = vir!([expired_perm] --* (
            [unblocked_perm] &&
            [pledges_and_nested_expiration_tools]
        ));

        (expr, bindings)
    }
}
