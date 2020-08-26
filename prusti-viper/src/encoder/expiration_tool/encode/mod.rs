use binding::Binding;
use binding::LiftBindings;
use prusti_common::vir;
use rustc_middle::mir;

use crate::encoder::procedure_encoder::ProcedureEncoder;

mod expression;
mod package;
mod common;
mod pledge;
mod binding;
mod utils;

struct ExpirationToolEncoder<'a, 'p, 'v: 'p, 'tcx: 'v> {
    procedure_encoder: &'a mut ProcedureEncoder<'p, 'v, 'tcx>,
    location: Option<mir::Location>,
    encoded_args: Vec<vir::Expr>,
    encoded_return: vir::Expr,
    pre_label: &'a str,
    post_label: &'a str
}

impl<'a, 'p, 'v: 'p, 'tcx: 'v> ExpirationToolEncoder<'a, 'p, 'v, 'tcx> {
    fn new(
        procedure_encoder: &'a mut ProcedureEncoder<'p, 'v, 'tcx>,
        location: Option<mir::Location>,
        pre_label: &'a str,
        post_label: &'a str
    ) -> Self {
        // The procedure contract.
        let contract = procedure_encoder.procedure_contract.as_ref().unwrap();

        // The arguments as Viper expressions.
        let encoded_args = contract.args.iter()
            .map(|local| procedure_encoder.encode_prusti_local(*local).into())
            .collect();

        // The return value as a Viper expression.
        let encoded_return = procedure_encoder.encode_prusti_local(contract.returned_value).into();

        ExpirationToolEncoder {
            procedure_encoder,
            location,
            encoded_args, encoded_return,
            pre_label, post_label
        }
    }
}
