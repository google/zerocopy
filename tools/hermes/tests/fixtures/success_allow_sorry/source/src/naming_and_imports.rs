pub mod edge_cases_naming_test_1_4_module_names {
    pub mod init {
        pub fn foo() {}
    }
    
    pub mod std {
        pub fn foo() {}
    }
    
    pub mod aeneas {
        pub fn foo() {}
    }
    
    pub mod header {
        pub fn foo() {}
    }
    
    pub mod root {
        pub fn foo() {}
    }
    
    pub mod lean {
        pub fn foo() {}
    }
    
    pub mod mathlib {
        pub fn foo() {}
    }
    
    
    /// ```lean, hermes
    /// proof (h_progress):
    ///   sorry
    /// proof context:
    ///   have h_foo : True := True.intro
    /// ```
    pub fn dummy_hermes_padding() {}
}

pub mod edge_cases_modules_test_6_4_ambiguous_imports {
    pub mod a {
        pub struct S;
    }
    
    pub mod b {
        pub struct S;
    }
    
    /// ```lean, hermes
    /// proof (h_progress):
    ///   sorry
    /// proof context:
    ///   have h_foo : True := True.intro
    /// ```
    pub fn func(x: a::S, y: b::S) {}
}

