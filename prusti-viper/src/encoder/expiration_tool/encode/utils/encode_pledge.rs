use prusti_common::vir;
use prusti_interface::environment::mir_utils::AllPlacesForLocal;
use prusti_interface::specs::typed;
use rustc_middle::mir;

use crate::encoder::errors::ErrorCtxt;
use crate::encoder::mir_encoder::PlaceEncoder;
use crate::encoder::procedure_encoder::ProcedureEncoder;

impl<'p, 'v: 'p, 'tcx: 'v> ProcedureEncoder<'p, 'v, 'tcx> {
    pub fn encode_pledge(&self,
        encoded_args: &[vir::Expr],
        encoded_return: &vir::Expr,
        pledge: &typed::Assertion<'tcx>,
        pre_label: &str,
        post_label: &str,
    ) -> vir::Expr {
        let encoded = self.encoder.encode_assertion(
            pledge,
            self.mir,
            pre_label,
            encoded_args,
            Some(&encoded_return),
            false,
            None,
            ErrorCtxt::GenericExpression);
        let contract = self.procedure_contract.as_ref().unwrap();
        let mut encoded = self.wrap_arguments_into_old(
            encoded, pre_label, contract, encoded_args);
        let tcx = self.procedure.get_tcx();
        let return_places = mir::RETURN_PLACE.all_places_with_ty(tcx, self.mir);
        let return_places = return_places.into_iter()
            .filter(|(_, ty)| self.mir_encoder.is_reference(ty))
            .map(|(place, _)| self.mir_encoder.encode_place(&place).unwrap())
            .map(|(place, ty, _)| self.mir_encoder.encode_deref(place, ty).0)
            .map(|place| (place.clone(), vir::Expr::labelled_old(post_label, place)))
            .collect::<Vec<_>>();
        for (p, p_old) in &return_places {
            encoded = encoded.replace_place(p, p_old);
        }
        encoded
    }
}
