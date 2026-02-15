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

    pub trait Bar {
        /// ```lean, hermes
        /// context
        /// theorem trait_meth : True := trivial
        /// ```
        fn trait_method();
    }
}
