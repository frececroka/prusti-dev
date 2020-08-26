use std::iter::FromIterator;

pub(in super::super) trait LiftBindings<T, B, TS, BS> {
    fn lift_bindings(self) -> (TS, BS);
}

impl<T, B, TS, BS, BI, I> LiftBindings<T, B, TS, BS> for I
    where
        BI: IntoIterator<Item=B>,
        I: Iterator<Item=(T, BI)>,
        TS: Default + Extend<T>,
        BS: FromIterator<B>
{
    fn lift_bindings(self) -> (TS, BS) {
        let (objects, bindings): (_, Vec<_>) = self.unzip();
        let bindings = bindings.into_iter().flatten().collect();
        (objects, bindings)
    }
}
