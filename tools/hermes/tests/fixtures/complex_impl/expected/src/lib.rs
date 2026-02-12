pub struct Foo;
pub trait T1 { fn m1(); }
pub trait T2 { fn m2(); }
pub trait T3 { fn m3(); }

// Case 1: Raw Pointer (*const Foo)
impl T1 for *const Foo {
    /// ```lean, hermes
    /// ```
    fn m1() {}
}

// Case 2: Slice ([Foo])
impl T2 for [Foo] {
    /// ```lean, hermes
    /// ```
    fn m2() {}
}

// Case 3: Array ([Foo; 5])
impl T3 for [Foo; 5] {
    /// ```lean, hermes
    /// ```
    fn m3() {}
}
