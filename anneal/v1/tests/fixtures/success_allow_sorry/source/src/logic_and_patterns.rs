pub mod edge_cases_modules_test_6_2_logic_visibility {
    
    pub mod inner {
        pub(crate) fn helper() -> u32 { 42 }
        
        /// ```anneal
        /// ensures:
        ///   True
        /// ```
        pub fn public_api() -> u32 {
            helper()
        }
    }
    
    
    /// ```lean, anneal
    /// proof (h_progress):
    ///   sorry
    /// proof context:
    ///   have h_foo : True := True.intro
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

