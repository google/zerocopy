/// ```hermes, unsafe(axiom)
/// axiom unsafe_axiom_spec : True
/// ```
unsafe fn unsafe_axiom(x: u32) -> u32 {
    x
}

/// ```hermes, unsafe(axiom)
/// context
/// -- Empty axiom section should default to something safe or be ignored
/// ```
unsafe fn unsafe_axiom_empty(x: u32) -> u32 {
    x
}

fn collision_args(result: u32, old_result: u32, ret: u32) -> u32 {
    result + old_result + ret
}

/// ```hermes
/// context
/// requires result > 0 -- 'result' as argument name vs binder
/// ensures True
/// ```
fn collision_spec(result: u32) {
}

/// ```hermes
/// context
/// -- Multiline complex spec
/// requires x > 0
/// requires x < 100#u32
/// ensures result = ()
/// ```
fn complex_spec(x: u32) {
}
