/// ```anneal, unsafe(axiom)
/// ```
unsafe fn unsafe_axiom(x: u32) -> u32 {
    x
}

/// ```anneal, unsafe(axiom)
/// context:
/// -- Empty axiom section should default to something safe or be ignored
/// ```
unsafe fn unsafe_axiom_empty(x: u32) -> u32 {
    x
}

fn collision_args(result: u32, old_result: u32, ret: u32) -> u32 {
    result + old_result + ret
}

/// ```anneal
/// context:
/// requires: ret > 0 -- 'ret' as argument name vs binder
/// ensures:
///   True
/// proof context:
/// ```
unsafe fn collision_spec(ret: u32) {
}

/// ```anneal
/// context:
/// -- Multiline complex spec
/// requires (h_req0):
///   x > 0
/// requires (h_req1):
///   x < 100#u32
/// ensures:
///   ret = ()
/// proof context:
/// ```
unsafe fn complex_spec(x: u32) {
}
