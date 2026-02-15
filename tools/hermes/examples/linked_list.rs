pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

impl<T> List<T> {
    /// ```lean, hermes, spec
    /// context
    ///   open _root_.linked_list
    ///   open _root_.linked_list.List
    ///   variable {T : Type}
    ///   abbrev Self := _root_.linked_list.List T
    ///   def _root_.linked_list.List.len (self : _root_.linked_list.List T) : Nat :=
    ///     match self with
    ///     | .Nil => 0
    ///     | .Cons _ tl => 1 + tl.len
    /// ensures self.len = old_self.len + 1
    /// proof
    ///   unfold linked_list.List.push
    ///   unfold _root_.linked_list.List.len
    ///   simp_all [Nat.add_comm]
    /// ```
    pub fn push(&mut self, val: T) {
        let old_self = std::mem::replace(self, List::Nil);
        *self = List::Cons(val, Box::new(old_self));
    }
}

fn main() {}
