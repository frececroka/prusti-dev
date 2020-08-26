use prusti_common::vir;
use prusti_common::vir::ExprFolder;

use crate::utils::fresh_name::FreshName;

use super::super::Binding;
use super::super::super::Context;

pub(in super::super) fn replace_old_expression(
    pledge: vir::Expr,
    fresh_name: &mut FreshName
) -> (vir::Expr, Vec<Binding>) {
    let mut replacer = OldReplacer { fresh_name, replacements: Vec::new() };
    let pledge = replacer.fold(pledge);
    let replacements = replacer.replacements;
    (pledge, replacements)
}

struct OldReplacer<'a> {
    fresh_name: &'a mut FreshName,
    replacements: Vec<Binding>
}

impl<'a> OldReplacer<'a> {
    fn next_var(&mut self) -> vir::LocalVar {
        vir::LocalVar::new(self.fresh_name.next(), vir::Type::Int)
    }
}

impl<'a> ExprFolder for OldReplacer<'a> {
    fn fold_labelled_old(&mut self,
        label: String,
        body: Box<vir::Expr>,
        pos: vir::Position
    ) -> vir::Expr {
        let context = match label.as_ref() {
            "before_expiry/xxx" => Context::BeforeExpiry,
            "after_unblocked/xxx" => Context::AfterUnblocked,
            _ => return vir::Expr::LabelledOld(label, body, pos),
        };

        let var = self.next_var();
        self.replacements.push((var.clone(), context, *body));

        vir::Expr::Local(var, pos)
    }
}

