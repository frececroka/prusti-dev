use std::collections::HashMap;

use prusti_common::vir;

use super::rename_locals;
use super::super::super::Context;

pub(in super::super) fn lift_bindings<T>(
    expressions: Vec<(vir::Expr, Vec<T>)>,
    to_local: impl Fn(&T) -> vir::LocalVar,
    replace_local: impl Fn(T, vir::LocalVar) -> T,
    generate_name: impl Fn(usize) -> String
) -> (Vec<vir::Expr>, Vec<T>) {
    let mut ident = 0;

    let mut new_expressions = vec![];
    let mut new_bindings = vec![];

    for (expr, bindings) in expressions {
        let mut renamings = HashMap::new();
        for binding in bindings {
            let mut local = to_local(&binding);

            // Make sure the local variable has a fresh name.
            let old_name = local.name;
            local.name = { ident += 1; generate_name(ident) };

            // Replace the old name with the new name in the expression.
            renamings.insert(old_name, local.name.clone());

            // Remember the new binding with the new name.
            let new_binding = replace_local(binding, local);
            new_bindings.push(new_binding);
        }

        // Perform the renamings.
        let expr = rename_locals(expr, &renamings);

        // Store the new expression.
        new_expressions.push(expr);
    }

    (new_expressions, new_bindings)
}
