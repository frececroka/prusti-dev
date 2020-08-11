use prusti_common::vir;
use prusti_common::vir::ExprFolder;

use super::super::Context;
use super::super::Binding;

pub(in super::super) fn replace_old_expression(pledge: vir::Expr) -> (vir::Expr, Vec<Binding>) {
    let mut replacer = OldReplacer::default();
    let pledge = replacer.fold(pledge);
    let replacements = replacer.replacements;
    (pledge, replacements)
}

#[derive(Default)]
struct OldReplacer {
    identifier: usize,
    replacements: Vec<Binding>
}

impl OldReplacer {
    fn next_var(&mut self) -> vir::LocalVar {
        self.identifier += 1;
        let name = format!("pledge$free${}", self.identifier);
        vir::LocalVar::new(name, vir::Type::Int)
    }
}

impl ExprFolder for OldReplacer {
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

