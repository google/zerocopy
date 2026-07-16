pub mod edge_cases_stress_test_11_4_namespace_bomb {
    
    pub mod a {
        pub mod a {
            pub mod a {
                pub mod a {
                    pub fn f() {}
                }
            }
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

pub mod edge_cases_stress_test_11_1_chain {
    
    pub mod a {
        pub fn f() -> u32 { 1 }
    }
    pub mod b {
        pub fn f() -> u32 { crate::hierarchy_and_stress::edge_cases_stress_test_11_1_chain::a::f() + 1 }
    }
    pub mod c {
        pub fn f() -> u32 { crate::hierarchy_and_stress::edge_cases_stress_test_11_1_chain::b::f() + 1 }
    }
    pub mod d {
        pub fn f() -> u32 { crate::hierarchy_and_stress::edge_cases_stress_test_11_1_chain::c::f() + 1 }
    }
    
    
    /// ```lean, anneal
    /// proof (h_progress):
    ///   sorry
    /// proof context:
    ///   have h_foo : True := True.intro
    /// ```
    pub fn dummy_anneal_padding() {}
}

pub mod edge_cases_stress_test_11_3_cycle {
    
    pub mod a {
        use super::b;
        pub struct A {
            pub b: Box<b::B>,
        }
    }
    
    pub mod b {
        use super::a;
        pub struct B {
            pub a: Option<Box<a::A>>,
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

pub mod deep_invocation {
    pub mod nested;
    
    
    /// ```lean, anneal
    /// ```
    fn _anneal_dummy() {}
}

