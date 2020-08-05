use rustc_middle::mir;

pub trait PlaceAsLocal {
    /// Tries to interpret the given `mir::Place` as a local variable. If this fails, it returns `None`.
    fn as_local(&self) -> Option<mir::Local>;
}

impl<'tcx> PlaceAsLocal for mir::Place<'tcx> {
    fn as_local(&self) -> Option<mir::Local> {
        if self.projection.len() == 0 {
            Some(self.local)
        } else {
            None
        }
    }
}
