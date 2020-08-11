use prusti_common::vir;
use rustc_hir::Mutability;
use rustc_middle::mir;

use crate::encoder::procedure_encoder::ProcedureEncoder;
use crate::encoder::procedure_encoder::Result;

use super::Context;
use super::ExpirationTool;
use super::MagicWand;

mod expression;
mod package;
mod utils;

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

        // The procedure contract.
        let contract = self.procedure_contract.as_ref().unwrap();

        // The arguments as Viper expressions.
        let encoded_args = contract.args.iter()
            .map(|local| self.encode_prusti_local(*local).into())
            .collect::<Vec<_>>();

        // The return value as a Viper expression.
        let encoded_return = self.encode_prusti_local(contract.returned_value).into();

        // The expiration tool proper.
        let package_stmts = self.expiration_tool_as_package(
            &expiration_tool, location, &encoded_args, &encoded_return, pre_label, post_label)?;

        // Everything concatenated.
        Ok([
            &obtains[..],
            &post_label_stmt[..],
            &package_stmts[..]
        ].concat())
    }
}

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
type Binding = (vir::LocalVar, Context, vir::Expr);
