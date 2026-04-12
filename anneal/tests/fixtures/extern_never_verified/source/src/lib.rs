pub mod a {
    pub mod b {
        /// ```lean, anneal, unsafe(axiom)
        /// ensures: True
        /// ```
        pub fn foo(x: u32) -> u32 {
            x
        }
    }
}

pub struct S;
impl S {
    /// ```lean, anneal, unsafe(axiom)
    /// ensures: True
    /// ```
    pub fn bar(x: u32) -> u32 {
        x
    }
}

pub mod inner {
    use super::S;
    impl S {
        /// ```lean, anneal, unsafe(axiom)
        /// ensures: True
        /// ```
        pub fn baz(x: u32) -> u32 {
            x
        }
    }
}

pub mod ffi {
    unsafe extern "C" {
        /// ```lean, anneal
        /// context:
        /// theorem ext_fn_ok : True := trivial
        /// ```
        pub fn ext_fn(x: u32) -> u32;

        /// ```lean, anneal, unsafe(axiom)
        /// ensures:
        ///   False
        /// ```
        pub fn diverge() -> !;
    }
}

pub struct SafeArray<const N: usize> {
    pub data: [u8; N],
}

impl<const N: usize> SafeArray<N> {
    /// ```lean, anneal
    /// ensures:
    ///   ret = 0
    /// proof:
    ///   sorry
    /// ```
    pub fn len(&self) -> usize {
        N
    }
}

/// ```lean, anneal
/// ensures:
///   False
/// proof:
///   sorry
/// ```
pub fn diverge() -> ! {
    panic!()
}

/// ```lean, anneal
/// ensures:
///   False && x = 42
/// proof:
///   sorry
/// ```
pub fn die(x: &mut u32) -> ! {
    panic!()
}
