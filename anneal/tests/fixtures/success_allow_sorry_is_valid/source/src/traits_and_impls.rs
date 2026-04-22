//! Tests for traits, trait inheritance, and implementation blocks on various types.

pub mod inheritance {
    /// ```lean, anneal
    /// def isSafe {Self : Type} (inst : A Self) : Prop := True
    /// ```
    pub unsafe trait A {}

    /// ```lean, anneal
    /// def isSafe {Self : Type} (inst : B Self) : Prop := True
    /// ```
    pub unsafe trait B: A {}

    /// ```lean, anneal
    /// def isSafe {Self : Type} (inst : C Self) : Prop := True
    /// ```
    pub unsafe trait C: A {}

    /// ```lean, anneal
    /// def isSafe {Self : Type} (inst : D Self) : Prop := True
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
        /// ```lean, anneal, spec
        /// theorem spec :
        ///   Aeneas.Std.WP.spec (m1) (fun ret_ => True) := by
        ///   sorry
        /// ```
        fn m1() {}
    }

    // Traits on slices
    impl T2 for [Foo] {
        /// ```lean, anneal, spec
        /// theorem spec :
        ///   Aeneas.Std.WP.spec (m2) (fun ret_ => True) := by
        ///   sorry
        /// ```
        fn m2() {}
    }

    // Traits on fixed-size arrays
    impl T3 for [Foo; 5] {
        /// ```lean, anneal, spec
        /// theorem spec :
        ///   Aeneas.Std.WP.spec (m3) (fun ret_ => True) := by
        ///   sorry
        /// ```
        fn m3() {}
    }
}

pub mod simple_impl {
    pub struct Data;

    impl Data {
        /// ```lean, anneal, spec
        /// theorem spec :
        ///   Aeneas.Std.WP.spec (process) (fun ret_ => True) := by
        ///   sorry
        /// ```
        pub fn process() {}
    }
}

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (dummy_anneal_padding_8) (fun ret_ => True) := by
///   sorry
/// ```
pub fn dummy_anneal_padding_8() {}

