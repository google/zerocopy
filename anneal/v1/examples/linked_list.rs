pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

impl<T> List<T> {
    /// ```lean, anneal, spec
    /// context:
    ///   open _root_.linked_list
    ///   open _root_.linked_list.List
    ///   variable {T : Type}
    ///   @[simp] def _root_.linked_list.List.len (self : _root_.linked_list.List T) : Nat :=
    ///     match self with
    ///     | .Nil => 0
    ///     | .Cons _ tl => 1 + tl.len
    /// -- We use absolute namespaces globally to reference items (e.g., `_root_.linked_list.List.len`).
    /// -- This definitively stabilizes method field projection inference in Lean.
    /// ensures: self'.len = self.len + 1
    /// proof (h_anon):
    ///   unfold push at h_returns
    ///   simp_all
    ///   rw [← h_returns]
    ///   simp_all
    ///   omega
    /// proof (h_progress):
    ///   unfold push
    ///   simp_all
    /// ```
    pub fn push(&mut self, val: T) {
        let old_self = std::mem::replace(self, List::Nil);
        *self = List::Cons(val, Box::new(old_self));
    }
}

fn main() {}
