/// ```lean, hermes, spec
/// theorem simple_spec_spec : True := trivial
/// ```
fn simple_spec(x: u32) -> bool {
    x > 10
}

/// ```lean, hermes, unsafe(axiom)
/// axiom unsafe_axiom_spec : True
/// ```
fn unsafe_axiom(x: u32) -> u32 {
    x + 1
}

/// ```lean, hermes
/// isValid (True)
/// ```
struct Positive {
    val: u32,
}

/// ```lean, hermes
/// isSafe (True)
/// ```
unsafe trait SafeTrait {
    fn method(&self);
}

/// ```lean, hermes, spec
/// theorem ref_lowering_spec : True := trivial
/// ```
fn ref_lowering(x: &mut u32) {
    *x += 1;
}

/// ```lean, hermes, spec
/// theorem complex_args_spec : True := trivial
/// ```
fn complex_args(slice: &[u8], array: [u8; 16]) {
    // Verify Slice/Array mapping
}

/// ```lean, hermes
/// isValid (true)
/// ```
struct InlineBound<T: Clone> {
    val: T,
}

/// ```lean, hermes
/// isValid (true)
/// ```
struct WhereBound<T>
where
    T: Copy,
{
    val: T,
}

