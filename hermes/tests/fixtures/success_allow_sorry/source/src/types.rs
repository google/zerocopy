pub mod edge_cases_types_test_2_2_string_types {
    
    use std::borrow::Cow;
    
    pub struct Strings<'a> {
        pub a: String,
        pub b: &'a str,
        pub c: Box<str>,
        pub d: Cow<'a, str>,
        pub e: char,
    }
    
    /// ```lean, anneal
    /// proof (h_progress):
    ///   sorry
    /// proof context:
    ///   have h_foo : True := True.intro
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
    
    /// ```lean, anneal
    /// proof (h_progress):
    ///   sorry
    /// proof context:
    ///   have h_foo : True := True.intro
    /// ```
    pub fn ptr_arg(p: *const u8) -> *const u8 {
        p
    }
}

