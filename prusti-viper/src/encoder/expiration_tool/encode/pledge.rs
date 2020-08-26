use prusti_common::vir;
use prusti_interface::environment::mir_utils::AllPlacesForLocal;
use prusti_interface::specs::typed;
use rustc_middle::mir;

use crate::encoder::errors::ErrorCtxt;
use crate::encoder::expiration_tool::encode::ExpirationToolEncoder;
use crate::encoder::mir_encoder::PlaceEncoder;

impl<'a, 'p, 'v: 'p, 'tcx: 'v> ExpirationToolEncoder<'a, 'p, 'v, 'tcx> {
    pub fn encode_pledge(&mut self, pledge: &typed::Assertion<'tcx>) -> vir::Expr {
        let encoded = self.procedure_encoder.encoder.encode_assertion(
            pledge,
            self.procedure_encoder.mir,
            self.pre_label,
            &self.encoded_args,
            Some(&self.encoded_return),
            false,
            None,
            ErrorCtxt::GenericExpression);
        let contract = self.procedure_encoder.procedure_contract.as_ref().unwrap();
        let mut encoded = self.procedure_encoder.wrap_arguments_into_old(
            encoded, self.pre_label, contract, &self.encoded_args);
        let tcx = self.procedure_encoder.procedure.get_tcx();
        let return_places = mir::RETURN_PLACE.all_places_with_ty(tcx, self.procedure_encoder.mir);
        let return_places = return_places.into_iter()
            .filter(|(_, ty)| self.procedure_encoder.mir_encoder.is_reference(ty))
            .map(|(place, _)| self.procedure_encoder.mir_encoder.encode_place(&place).unwrap())
            .map(|(place, ty, _)| self.procedure_encoder.mir_encoder.encode_deref(place, ty).0)
            .map(|place| (place.clone(), vir::Expr::labelled_old(self.post_label, place)))
            .collect::<Vec<_>>();
        for (p, p_old) in &return_places {
            encoded = encoded.replace_place(p, p_old);
        }
        encoded
    }
}
