use prusti_common::vir;
use prusti_common::vir::Expr;
use prusti_common::vir::ExprIterator;
use prusti_common::vir::LocalVar;
use rustc_hir::Mutability;

use crate::encoder::expires_first_domain;
use crate::encoder::procedure_encoder::ProcedureEncoder;

use super::Binding;
use super::ExpirationTool;
use super::MagicWand;
use super::super::Context::*;
use super::utils::contains_subexpr;
use super::utils::lift_bindings;
use super::utils::replace_old_expression;
use crate::encoder::expiration_tool::encode::utils::{rename_locals, rename_local};

impl<'p, 'v: 'p, 'tcx: 'v> ProcedureEncoder<'p, 'v, 'tcx> {
    pub fn encode_expiration_tool_as_expression(&self,
        expiration_tool: &ExpirationTool<'tcx>,
        encoded_args: &[vir::Expr],
        encoded_return: &vir::Expr,
        pre_label: &str,
        post_label: &str
    ) -> vir::Expr {
        let (encoded_expiration_tool, bindings) = self.expiration_tool_as_expression(
            expiration_tool, encoded_args, encoded_return, pre_label, post_label);
        assert!(bindings.is_empty());
        encoded_expiration_tool
    }

    /// This encodes the given expiration tool as a Viper expression.
    pub(super) fn expiration_tool_as_expression(&self,
        expiration_tool: &ExpirationTool<'tcx>,
        encoded_args: &[vir::Expr],
        encoded_return: &vir::Expr,
        pre_label: &str,
        post_label: &str
    ) -> (vir::Expr, Vec<Binding>) {
        let branches = expiration_tool.magic_wands()
            .map(|magic_wand| {
                let expired_place = expiration_tool.place_mapping[magic_wand.expired()];
                let antecedent = vir::Expr::domain_func_app(
                    expires_first_domain::EXPIRES_FIRST.clone(),
                    vec![vir::Expr::const_int(expired_place as i64)]);
                let (encoded_magic_wand, let_bindings) = self.magic_wand_as_expression(
                    magic_wand, encoded_args, encoded_return, pre_label, post_label);
                let encoded_branch = vir!([antecedent] ==> [encoded_magic_wand]);
                (encoded_branch, let_bindings)
            })
            .collect();

        // Lift the bindings out of the branches.
        let (branches, bindings) = lift_pledge_bindings(branches);

        // The whole expiration tool is simply the conjunction of all branches.
        let expiration_tool = branches.into_iter().conjoin();

        (expiration_tool, bindings)
    }

    /// This encodes the given magic wand as a Viper expression.
    pub(super) fn magic_wand_as_expression(&self,
        magic_wand: &MagicWand<'tcx>,
        encoded_args: &[vir::Expr],
        encoded_return: &vir::Expr,
        pre_label: &str,
        post_label: &str
    ) -> (vir::Expr, Vec<Binding>) {
        let expired_perm = self.encode_place_perm(
            magic_wand.expired(), Mutability::Mut, None, post_label);

        let unblocked_perm = magic_wand.unblocked()
            .map(|unblocked| self.encode_place_perm(
                unblocked, Mutability::Mut, None, pre_label
            ))
            .map(|unblocked| (unblocked, vec![]));

        let pledges = magic_wand.pledges()
            .map(|pledge| self.encode_pledge(
                encoded_args, encoded_return, pledge, pre_label, post_label
            ))
            .map(|pledge| replace_old_expression(pledge));

        let nested_expiration_tools = magic_wand.expiration_tools.iter()
            .map(|expiration_tool| self.expiration_tool_as_expression(
                expiration_tool, encoded_args, encoded_return, pre_label, post_label
            ));

        let rhs = std::iter::empty()
            .chain(unblocked_perm)
            .chain(pledges)
            .chain(nested_expiration_tools)
            .collect();

        // Lift the bindings out of the individual conjuncts.
        let (rhs, bindings) = lift_pledge_bindings(rhs);

        // The right-hand side of the magic wand, still without let expressions.
        let rhs = rhs.into_iter().conjoin();

        let (encoded_expired, _, _) = self.encode_generic_place(
            self.procedure.get_id(), None, magic_wand.expired());

        let encoded_unblocked = magic_wand.unblocked()
            .map(|unblocked| {
                let (encoded_unblocked, _, _) = self.encode_generic_place(
                    self.procedure.get_id(), None, unblocked);
                encoded_unblocked
            })
            .collect::<Vec<_>>();

        // Determine which bindings are "ripe" (and can be materialized into let expressions right
        // now). A binding is ripe if the output it depends on just expired or the input it depends
        // on was just unblocked. The ripe bindings will become let expressions in the next step,
        // the other bindings will be passed on to the caller.
        let (ripe_bindings, bindings) = bindings.into_iter()
            .partition::<Vec<_>, _>(|(_, context, bound_expr)| match context {
                BeforeExpiry => contains_subexpr(bound_expr, &encoded_expired),
                AfterUnblocked => encoded_unblocked.iter().any(|encoded_unblocked|
                    contains_subexpr(bound_expr, &encoded_unblocked))
            });

        // Build the final magic wand expression.
        let rhs = ripe_bindings.into_iter().fold(rhs, |rhs, (mut var, context, expr)| {
            let old_name = var.name;
            var.name = "TODO".into();
            let rhs = rename_local(rhs, old_name, var.name.clone());
            let pos = rhs.pos();
            vir::Expr::LetExpr(var, Box::new(expr), Box::new(rhs), pos)
        });

        let expr = vir!([expired_perm] --* [rhs]);

        (expr, bindings)
    }
}

fn lift_pledge_bindings(expressions: Vec<(vir::Expr, Vec<Binding>)>) -> (Vec<Expr>, Vec<Binding>) {
    lift_bindings(
        expressions,
        |(local, _, _)| local.clone(),
        |(_, context, expr), local| (local, context, expr),
        |ident| format!("pledge$free${}", ident))
}
