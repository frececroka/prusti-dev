use std::iter::once;

use rustc_middle::mir;
use rustc_middle::ty;

pub trait PlaceAddField<'tcx> {
    fn field(self, tcx: ty::TyCtxt<'tcx>, field: mir::Field, ty: ty::Ty<'tcx>) -> mir::Place<'tcx>;
}

impl<'tcx> PlaceAddField<'tcx> for mir::Place<'tcx> {
    fn field(self, tcx: ty::TyCtxt<'tcx>, field: mir::Field, ty: ty::Ty<'tcx>) -> mir::Place<'tcx> {
        let local = self.local;
        let projection = self.projection.iter()
            .chain(once(mir::ProjectionElem::Field(field, ty)))
            .collect::<Vec<_>>();
        let projection = tcx.intern_place_elems(&projection);
        mir::Place { local, projection }
    }
}
