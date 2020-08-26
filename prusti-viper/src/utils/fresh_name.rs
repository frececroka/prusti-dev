#[derive(Clone)]
pub struct FreshName {
    prefix: String,
    counter: u64
}

impl FreshName {
    pub fn new(prefix: impl ToString) -> Self {
        let prefix = prefix.to_string();
        FreshName { prefix, counter: 0 }
    }

    pub fn next(&mut self) -> String {
        self.counter += 1;
        format!("{}${}", self.prefix, self.counter)
    }

    pub fn next_child(&mut self) -> FreshName {
        FreshName::new(self.next())
    }
}
