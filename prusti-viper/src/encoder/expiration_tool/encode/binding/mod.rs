pub(super) use lift::LiftBindings;
use prusti_common::vir;

use super::super::Context;

mod partition;
mod lift;

/// This represents a single binding of a pledge, magic wand, or expiration tool. For example,
/// consider the following (encoded) pledge:
/// ```ignore
/// old[before_expiry](_0.tuple_0.val_ref.val_int) == old[after_unblocked](_1.val_ref.f$x.val_int)
/// ```
/// Because we must manually evaluate the two `old` expressions at the right times, they are pulled
/// out of the encoded pledge. This gives the following expression:
/// ```ignore
/// pledge$0 == pledge$1
/// ```
/// With the following bindings:
///  - `pledge$0 // BeforeExpiry // _0.tuple_0.val_ref.val_int`
///  - `pledge$1 // AfterUnblocked // _1.val_ref.f$x.val_int`
pub(super) type Binding = (vir::LocalVar, Context, vir::Expr);

pub(super) fn encode_binding((var, context, expr): Binding) -> (vir::LocalVar, vir::Expr) {
    use super::super::Context::*;
    let expr = match context {
        BeforeExpiry => expr.old("lhs"),
        AfterUnblocked => expr
    };
    (var, expr)
}
