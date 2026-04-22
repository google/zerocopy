pub mod edge_cases_types_test_2_2_string_types {
    
    use std::borrow::Cow;
    
    pub struct Strings<'a> {
        pub a: String,
        pub b: &'a str,
        pub c: Box<str>,
        pub d: Cow<'a, str>,
        pub e: char,
    }
    
    /// ```lean, anneal, spec
    /// theorem spec (s : String) :
    ///   Aeneas.Std.WP.spec (check_strings s) (fun ret_ => True) := by
    ///   sorry
    /// ```
    pub fn check_strings(s: String) -> String {
        s
    }
}

pub mod edge_cases_types_test_2_5_pointers {
    use std::ptr::NonNull;
    
    pub struct Pointers {
        pub a: *const u8,
        pub b: *mut u8,
        pub c: NonNull<u8>,
    }
    
    /// ```lean, anneal, spec
    /// theorem spec (p : *const u8) :
    ///   Aeneas.Std.WP.spec (ptr_arg p) (fun ret_ => True) := by
    ///   sorry
    /// ```
    pub fn ptr_arg(p: *const u8) -> *const u8 {
        p
    }
}

