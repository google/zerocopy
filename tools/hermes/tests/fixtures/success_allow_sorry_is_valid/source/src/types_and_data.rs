//! Tests for Rust-to-Lean type mapping, including primitives, structs, enums, and tuples.

/// Tests for primitive type widths (isize/usize).
pub struct Widths {
    pub a: isize,
    pub b: usize,
}

/// ```lean, hermes, spec
/// ```
pub fn check_widths(x: isize, y: usize) -> (isize, usize) {
    (x, y)
}

/// Generic struct testing.
/// @spec
/// isValid self := isValid self.inner
pub struct Container<T> {
    pub inner: T,
}

/// Dependent type testing with const generics.
/// @spec
/// isValid self := self.a.len = N
pub struct ArrayPair<const N: usize> {
    pub a: [u8; N],
    pub b: [u8; N],
}

/// Recursive struct testing.
/// @spec
/// isValid self := match self.next with | .none => True | .some n => isValid n
pub struct Node {
    pub next: Option<Box<Node>>,
}

/// Struct with where clauses.
/// @spec
/// isValid self := True
pub struct Foo<T> where T: Copy + Clone + Default {
    pub inner: T,
}

/// Tests for tuple types.
/// ```lean, hermes, spec
/// ```
pub fn one_tuple(x: (u32,)) -> (u32,) {
    x
}

pub fn long_tuple() -> (u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8) {
    (0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0)
}

pub mod enums {
    /// An uninhabited enum.
    pub enum Void {}

    /// ```lean, hermes, spec
    /// proof:
    ///   unfold invert at *
    ///   contradiction
    /// ```
    pub fn invert(v: Void) -> ! {
        match v {}
    }

    /// Enum with explicit discriminants.
    pub enum Color {
        Red = 0xff,
        Green = 0x00,
    }

    /// Uninhabited type wrapper.
    /// ```lean, hermes
    /// isValid self := nomatch self
    /// ```
    pub struct Wrapper {
        pub v: Void,
    }
}

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_hermes_padding_1() {}

/// @spec
/// isValid self := isValid self.inner
pub struct ContainerValid<T> {
    pub inner: T,
}

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_hermes_padding_2() {}

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_hermes_padding_3() {}

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_hermes_padding_4() {}

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_hermes_padding_5() {}

