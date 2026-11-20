// A returned reference whose origin is the join of two parameter origins, with an under-specified signature.
pub fn pick<'a, 'b>(c: bool, x: &'a u32, y: &'b u32) -> &'a u32 {
    if c { x } else { y }
}
