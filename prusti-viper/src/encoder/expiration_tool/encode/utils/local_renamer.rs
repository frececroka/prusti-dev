use std::collections::HashMap;

use prusti_common::vir;
use prusti_common::vir::ExprFolder;

pub(in super::super) fn rename_local(
    expr: vir::Expr,
    old_name: String,
    new_name: String
) -> vir::Expr {
    let mut renamings = HashMap::new();
    renamings.insert(old_name, new_name);
    rename_locals(expr, &renamings)
}

pub(in super::super) fn rename_locals(
    expr: vir::Expr,
    renamings: &HashMap<String, String>
) -> vir::Expr {
    let mut renamer = VariableRenamer { renamings: &renamings };
    renamer.fold(expr)
}

struct VariableRenamer<'a> {
    renamings: &'a HashMap<String, String>
}

impl<'a> ExprFolder for VariableRenamer<'a> {
    fn fold_local(&mut self, mut v: vir::LocalVar, p: vir::Position) -> vir::Expr {
        if let Some(new_name) = self.renamings.get(&v.name) {
            v.name = new_name.into();
        }
        vir::Expr::Local(v, p)
    }
}
