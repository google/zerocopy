macro_rules! make_proof {
    () => {
        /// ```lean
        /// theorem hidden_proof : True := trivial
        /// ```
        pub fn hidden_proof() {}
    }
}
make_proof!();
