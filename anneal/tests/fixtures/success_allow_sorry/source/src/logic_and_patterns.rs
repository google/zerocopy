pub mod edge_cases_modules_test_6_2_logic_visibility {
    
    pub mod inner {
        pub(crate) fn helper() -> u32 { 42 }
        
        /// ```lean, anneal, spec
        /// -- FIXME: Remove manual sorry once we support omitting proofs
        /// theorem spec :
        ///   Aeneas.Std.WP.spec (public_api) (fun ret_ => True) := by
        ///   sorry
        /// ```
        pub fn public_api() -> u32 {
            helper()
        }
    }
    
    
    /// ```lean, anneal, spec
    /// theorem spec :
    ///   Aeneas.Std.WP.spec (dummy_anneal_padding) (fun ret_ => True) := by
    ///   sorry
    /// ```
    pub fn dummy_anneal_padding() {}
}

pub mod start_patterns {
    /// ```lean, anneal
    /// ```
    fn foo() {}
    
    mod nested {
        /// ```lean, anneal
        /// ```
        fn bar() {}
    }
}

