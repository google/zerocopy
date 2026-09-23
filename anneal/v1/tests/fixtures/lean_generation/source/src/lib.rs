/// ```lean, anneal, spec
/// context:
/// theorem simple_spec_spec : True := trivial
/// ```
fn simple_spec(x: u32) -> bool {
    x > 10
}

/// ```lean, anneal, unsafe(axiom)
/// ```
fn unsafe_axiom(x: u32) -> u32 {
    x + 1
}

/// ```lean, anneal
/// isValid self := True
/// ```
struct Positive {
    val: u32,
}

/// ```lean, anneal
/// isSafe :
///   True
/// ```
unsafe trait SafeTrait {
    fn method(&self);
}

/// ```lean, anneal, spec
/// context:
/// theorem ref_lowering_spec : True := trivial
/// ```
fn ref_lowering(x: &mut u32) {
    *x += 1;
}

/// ```lean, anneal, spec
/// context:
/// theorem complex_args_spec : True := trivial
/// ```
fn complex_args(slice: &[u8], array: [u8; 16]) {
    // Verify Slice/Array mapping
}

/// ```lean, anneal
/// isValid self := true
/// ```
struct InlineBound<T: Clone> {
    val: T,
}

/// ```lean, anneal
/// isValid self := true
/// ```
struct WhereBound<T>
where
    T: Copy,
{
    val: T,
}

