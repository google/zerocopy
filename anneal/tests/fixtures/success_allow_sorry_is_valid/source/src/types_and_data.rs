//! Tests for Rust-to-Lean type mapping, including primitives, structs, enums, and tuples.

/// Tests for primitive type widths (isize/usize).
pub struct Widths {
    pub a: isize,
    pub b: usize,
}

/// ```lean, anneal, spec
/// ```
pub fn check_widths(x: isize, y: usize) -> (isize, usize) {
    (x, y)
}

/// Generic struct testing.
/// ```anneal
/// isValid self := True
/// ```
pub struct Container<T> {
    pub inner: T,
}

/// Dependent type testing with const generics.
/// ```anneal
/// isValid self := True
/// ```
pub struct ArrayPair<const N: usize> {
    pub a: [u8; N],
    pub b: [u8; N],
}

/// Recursive struct testing.
/// ```anneal
/// isValid self := True
/// ```
pub struct Node {
    pub next: Option<Box<Node>>,
}

/// Struct with where clauses.
/// ```anneal
/// isValid self := True
/// ```
pub struct Foo<T> {
    pub inner: T,
}

/// Tests for tuple types.
/// ```lean, anneal, spec
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

    /// ```lean, anneal, spec
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
    /// ```lean, anneal
    /// isValid self := nomatch self
    /// ```
    pub struct Wrapper {
        pub v: Void,
    }
}

/// ```lean, anneal
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_anneal_padding_1() {}

/// ```anneal
/// isValid self := True
/// ```
pub struct ContainerValid<T> {
    pub inner: T,
}

/// ```lean, anneal
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_anneal_padding_2() {}

/// ```lean, anneal
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_anneal_padding_3() {}

/// ```lean, anneal
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_anneal_padding_4() {}

/// ```lean, anneal
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_anneal_padding_5() {}

