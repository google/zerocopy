//! Tests for complex specification logic (match, if, let), shadowing, and control flow.

pub enum E {
    A(u32),
    B(u32),
}

/// ```anneal
/// isValid self := True
/// ```
pub struct MatchSpec {
    pub e: E,
}

/// ```anneal
/// isValid self := True
/// ```
pub struct LetSpec {
    pub x: u32,
}

/// ```anneal
/// isValid self := True
/// ```
pub struct IfSpec {
    pub check: bool,
    pub val: u32,
}

pub mod shadowing {
    /// Test for shadowing in function bodies.
    /// ```lean, anneal, spec
    /// ```
    pub fn body_shadow(x: u32) -> u32 {
        let x = x + 1;
        let x = x * 2;
        x
    }

    /// Test for shadowing in specifications.
    /// `ret` is a reserved keyword in some contexts.
    pub fn result_shadow(ret: u32) -> u32 {
        ret
    }

    /// Shadowing the concept of 'old' value in mutable references.
    pub fn old_shadow(old_x: &mut u32) {
        *old_x += 1;
    }

    pub fn internal_shadow(ret: u32, x_new: u32) -> u32 {
        ret + x_new
    }
}

/// Tests for the never type and panics.
/// ```lean, anneal, spec
/// ```
pub fn crash() -> ! {
    panic!("crash")
}

/// ```lean, anneal
/// proof (h_progress):
///   sorry
/// proof context:
///   sorry
/// ```
pub fn shadow(x: u32) -> u32 {
    let x = x + 1;
    let x = x * 2;
    x
}

/// ```anneal
/// isValid self := True
/// ```
pub struct S {
    pub e: E,
}

/// ```lean, anneal
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_anneal_padding_6() {}

/// ```lean, anneal
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_anneal_padding_7() {}

/// ```lean, anneal
/// isValid self := True
/// ```
pub struct Checked {
    pub check: bool,
    pub val: u32,
}

/// ```anneal
/// ensures:
///   True
/// ```
pub fn add_one(x: u32) -> u32 {
    x + 1
}

/// ```anneal
/// ensures:
///   True
/// ```
pub fn unknown_decrease(n: u32) -> u32 {
    if n > 0 {
        unknown_decrease(n - 1)
    } else {
        42
    }
}

/// ```lean, anneal
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn old<T>(x: T) -> T { x }
