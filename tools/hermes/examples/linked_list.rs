pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

impl<T> List<T> {
    /// ```lean, hermes, spec
    /// ensures self.len = old(self).len + 1
    /// proof
    ///   unfold push
    ///   simp_all
    /// ```
    pub fn push(&mut self, val: T) {
        let old_self = std::mem::replace(self, List::Nil);
        *self = List::Cons(val, Box::new(old_self));
    }
}

fn main() {}
