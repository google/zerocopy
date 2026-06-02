pub mod a {
    pub mod b {
        /// ```lean, anneal, unsafe(axiom)
        /// axiom spec (x : Std.U32) :
        ///   Aeneas.Std.WP.spec (a.b.foo x) (fun ret_ => True)
        /// ```
        pub fn foo(x: u32) -> u32 {
            x
        }
    }
}

pub struct S;
impl S {
    /// ```lean, anneal, unsafe(axiom)
    /// axiom spec (x : Std.U32) :
    ///   Aeneas.Std.WP.spec (S.bar x) (fun ret_ => True)
    /// ```
    pub fn bar(x: u32) -> u32 {
        x
    }
}

pub mod inner {
    use super::S;
    impl S {
        /// ```lean, anneal, unsafe(axiom)
        /// axiom spec (x : Std.U32) :
        ///   Aeneas.Std.WP.spec (inner.S.baz x) (fun ret_ => True)
        /// ```
        pub fn baz(x: u32) -> u32 {
            x
        }
    }
}

pub mod ffi {
    unsafe extern "C" {
        /// ```lean, anneal
        /// theorem ext_fn_ok : True := trivial
        /// ```
        pub fn ext_fn(x: u32) -> u32;

        /// ```lean, anneal, unsafe(axiom)
        /// axiom spec :
        ///   Aeneas.Std.WP.spec (ffi.diverge) (fun ret_ => False)
        /// ```
        pub fn diverge() -> !;
    }
}

pub struct SafeArray<const N: usize> {
    pub data: [u8; N],
}

impl<const N: usize> SafeArray<N> {
    /// ```lean, anneal, spec
    /// theorem spec {N : Std.Usize} (self : SafeArray N) :
    ///   Aeneas.Std.WP.spec (SafeArray.len self) (fun ret_ => ret_.val = 0) := by
    ///   sorry
    /// ```
    pub fn len(&self) -> usize {
        N
    }
}

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (diverge) (fun ret_ => False) := by
///   sorry
/// ```
pub fn diverge() -> ! {
    panic!()
}

/// ```lean, anneal, spec
/// theorem spec (x : Std.U32) :
///   Aeneas.Std.WP.spec (die x) (fun ret_ => False ∧ ret_ = 42) := by
///   sorry
/// ```
pub fn die(x: &mut u32) -> ! {
    panic!()
}
