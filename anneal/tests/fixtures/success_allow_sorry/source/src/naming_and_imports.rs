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
    
    
    /// ```lean, anneal, spec
    /// theorem spec :
    ///   Aeneas.Std.WP.spec (dummy_anneal_padding) (fun ret_ => True) := by
    ///   sorry
    /// ```
    pub fn dummy_anneal_padding() {}
}

pub mod edge_cases_modules_test_6_4_ambiguous_imports {
    pub mod a {
        pub struct S;
    }
    
    pub mod b {
        pub struct S;
    }
    
    /// ```lean, anneal, spec
    /// theorem spec (x : a.S) (y : b.S) :
    ///   Aeneas.Std.WP.spec (func x y) (fun ret_ => True) := by
    ///   sorry
    /// ```
    pub fn func(x: a::S, y: b::S) {}
}
/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (dummy_naming) (fun ret_ => True) := by
///   sorry
/// ```
pub fn dummy_naming() {}

