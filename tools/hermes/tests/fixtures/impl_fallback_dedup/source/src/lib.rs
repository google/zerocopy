pub mod my_module {
    pub struct Foo;

    impl Foo {
        /// ```lean, hermes
        /// context
        /// theorem meth_one : True := trivial
        /// ```
        pub fn method_one() {}

        /// ```lean, hermes
        /// context
        /// theorem meth_two : True := trivial
        /// ```
        pub fn method_two() {}
    }

    /// ```lean, hermes
    /// isValid self := True
    /// ```
    pub struct Bar;

    impl Bar {
        pub fn trait_method(&self) {}
    }
}
