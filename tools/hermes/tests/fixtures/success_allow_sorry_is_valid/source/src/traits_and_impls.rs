//! Tests for traits, trait inheritance, and implementation blocks on various types.

pub mod inheritance {
    /// ```hermes
    /// isSafe : True
    /// ```
    pub unsafe trait A {}

    /// ```hermes
    /// isSafe : True
    /// ```
    pub unsafe trait B: A {}

    /// ```hermes
    /// isSafe : True
    /// ```
    pub unsafe trait C: A {}

    /// ```hermes
    /// isSafe : True
    /// ```
    pub unsafe trait D: B + C {}
}

pub mod advanced_impls {
    pub struct Foo;
    pub trait T1 { fn m1(); }
    pub trait T2 { fn m2(); }
    pub trait T3 { fn m3(); }

    // Traits on raw pointers
    impl T1 for *const Foo {
        /// ```lean, hermes, spec
        /// ```
        fn m1() {}
    }

    // Traits on slices
    impl T2 for [Foo] {
        /// ```lean, hermes, spec
        /// ```
        fn m2() {}
    }

    // Traits on fixed-size arrays
    impl T3 for [Foo; 5] {
        /// ```lean, hermes, spec
        /// ```
        fn m3() {}
    }
}

pub mod simple_impl {
    pub struct Data;

    impl Data {
        /// ```lean, hermes, spec
        /// ```
        pub fn process() {}
    }
}

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_hermes_padding_8() {}

