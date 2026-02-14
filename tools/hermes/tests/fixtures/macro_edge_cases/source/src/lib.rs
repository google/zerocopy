/// ```hermes
/// isSafe Self := x > 0
/// ```
unsafe trait MyTrait {
    fn foo();
}

macro_rules! decl_trait {
    ($n:ident) => {
        /// ```hermes
        /// isSafe Self := true
        /// ```
        unsafe trait $n {
            fn bar();
        }
    }
}

// Macro invocation usage
decl_trait!(HiddenTrait);

// Macro invocation with attributes
/// ```hermes
/// -- Doc comment on macro invocation
/// ```
#[allow(dead_code)]
decl_trait!(VisibleTrait);
