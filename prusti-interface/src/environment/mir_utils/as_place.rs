use rustc_middle::mir;
use rustc_middle::ty;

pub trait AsPlace<'tcx> {
    fn as_place(&self) -> mir::Place<'tcx>;
}

impl<'tcx> AsPlace<'tcx> for mir::Local {
    fn as_place(&self) -> mir::Place<'tcx> {
        mir::Place { local: *self, projection: ty::List::empty() }
    }
}
