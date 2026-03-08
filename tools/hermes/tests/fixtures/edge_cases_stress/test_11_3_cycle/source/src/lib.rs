
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


/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_hermes_padding() {}
