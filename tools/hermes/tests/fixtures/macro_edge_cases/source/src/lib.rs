/// ```hermes
/// isSafe Self := ∀ (self : Self), True
/// ```
unsafe trait MyTrait {
    fn foo();
}

macro_rules! decl_trait {
    ($n:ident) => {
        /// ```hermes
/// isSafe Self := x > 0
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
/// context
/// -- Doc comment on macro invocation
/// ```
#[allow(dead_code)]
decl_trait!(VisibleTrait);
