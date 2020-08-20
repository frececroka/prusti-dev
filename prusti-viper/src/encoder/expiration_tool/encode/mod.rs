use binding::Binding;
use binding::LiftBindings;
use prusti_common::vir;
use rustc_middle::mir;

use crate::encoder::procedure_encoder::ProcedureEncoder;
use crate::encoder::borrows::ProcedureContract;

mod expression;
mod package;
mod common;
mod pledge;
mod binding;
mod utils;

struct ExpirationToolEncoder<'a, 'p, 'v: 'p, 'tcx: 'v> {
    procedure_encoder: &'a mut ProcedureEncoder<'p, 'v, 'tcx>,
    /// If we encode an expiration tool for a function call, this location should point to the
    /// function call statement. If we encode an expiration for a function itself, this location
    /// should be `None`.
    call_location: Option<mir::Location>,
    /// If we encode an expiration tool for a function, this location should point to the return
    /// statement of the function. If we encode an expiration for a function call, this location
    /// should be `None`.
    return_location: Option<mir::Location>,
    /// The function arguments, encoded as Viper expressions.
    encoded_args: Vec<vir::Expr>,
    /// The function return value, encoded as a Viper expression.
    encoded_return: vir::Expr,
    /// The labels at the end and the beginning of the function or before and after the function
    /// call.
    pre_label: &'a str,
    post_label: &'a str
}

impl<'a, 'p, 'v: 'p, 'tcx: 'v> ExpirationToolEncoder<'a, 'p, 'v, 'tcx> {
    fn for_function(
        procedure_encoder: &'a mut ProcedureEncoder<'p, 'v, 'tcx>,
        location: mir::Location,
        pre_label: &'a str,
        post_label: &'a str
    ) -> Self {
        Self::new(procedure_encoder, Some(location), None, pre_label, post_label)
    }

    fn for_function_call(
        procedure_encoder: &'a mut ProcedureEncoder<'p, 'v, 'tcx>,
        location: mir::Location,
        pre_label: &'a str,
        post_label: &'a str
    ) -> Self {
        Self::new(procedure_encoder, None, Some(location), pre_label, post_label)
    }

    fn new(
        procedure_encoder: &'a mut ProcedureEncoder<'p, 'v, 'tcx>,
        contract: &ProcedureContract<'tcx>,
        return_location: Option<mir::Location>,
        call_location: Option<mir::Location>,
        pre_label: &'a str,
        post_label: &'a str
    ) -> Self {
        // The arguments as Viper expressions.
        let encoded_args = contract.args.iter()
            .map(|local| procedure_encoder.encode_prusti_local(*local).into())
            .collect();

        // The return value as a Viper expression.
        let encoded_return = procedure_encoder.encode_prusti_local(contract.returned_value).into();

        ExpirationToolEncoder {
            procedure_encoder,
            return_location, call_location,
            encoded_args, encoded_return,
            pre_label, post_label
        }
    }
}
