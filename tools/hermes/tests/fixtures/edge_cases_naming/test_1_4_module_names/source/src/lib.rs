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


/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold dummy_hermes_padding at *
///   simp_all
/// ```
pub fn dummy_hermes_padding() {}
