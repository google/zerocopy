pub mod edge_cases_modules_test_6_2_logic_visibility {
    
    pub mod inner {
        pub(crate) fn helper() -> u32 { 42 }
        
        /// ```hermes
        /// ensures:
        ///   True
        /// ```
        pub fn public_api() -> u32 {
            helper()
        }
    }
    
    
    /// ```lean, hermes
    /// proof (h_progress):
    ///   sorry
    /// proof context:
    ///   have h_foo : True := True.intro
    /// ```
    pub fn dummy_hermes_padding() {}
}

pub mod start_patterns {
    /// ```lean, hermes
    /// ```
    fn foo() {}
    
    mod nested {
        /// ```lean, hermes
        /// ```
        fn bar() {}
    }
}

