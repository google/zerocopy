// RFC 2229 motivating example. Expect: rejected in edition 2018, accepted in edition 2021.
pub struct Filter;
impl Filter { fn allowed(&self, _i: &u32) -> bool { true } }
pub struct S { list: Vec<u32>, filter: Filter }
impl S {
    pub fn update(&mut self) {
        self.list.retain(|i| self.filter.allowed(i));
    }
}
