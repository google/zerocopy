pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

impl<T> List<T> {
    /// ```lean, anneal, spec
    /// open _root_.linked_list
    /// open _root_.linked_list.List
    /// variable {T : Type}
    /// @[simp] def _root_.linked_list.List.len (self : _root_.linked_list.List T) : Nat :=
    ///   match self with
    ///   | .Nil => 0
    ///   | .Cons _ tl => 1 + tl.len
    /// 
    /// theorem spec {T : Type} (self : _root_.linked_list.List T) (val : T) :
    ///   Aeneas.Std.WP.spec (List.push self val) (fun ret_ =>
    ///     ret_.len = self.len + 1) := by
    ///   sorry
    /// ```
    pub fn push(&mut self, val: T) {
        let old_self = std::mem::replace(self, List::Nil);
        *self = List::Cons(val, Box::new(old_self));
    }
}

fn main() {}
