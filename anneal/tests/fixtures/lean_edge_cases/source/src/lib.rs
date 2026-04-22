/// ```lean, anneal, unsafe(axiom)
/// axiom spec (x : Std.U32) :
///   Aeneas.Std.WP.spec (unsafe_axiom x) (fun ret_ => True)
/// ```
unsafe fn unsafe_axiom(x: u32) -> u32 {
    x
}

/// ```lean, anneal, unsafe(axiom)
/// -- Empty axiom section should default to something safe or be ignored
/// axiom spec (x : Std.U32) :
///   Aeneas.Std.WP.spec (unsafe_axiom_empty x) (fun ret_ => True)
/// ```
unsafe fn unsafe_axiom_empty(x: u32) -> u32 {
    x
}

fn collision_args(result: u32, old_result: u32, ret: u32) -> u32 {
    result + old_result + ret
}

/// ```lean, anneal, spec
/// theorem spec (ret : Std.U32) (h_req : ret.val > 0) :
///   Aeneas.Std.WP.spec (collision_spec ret) (fun ret_ => True) := by
///   sorry
/// ```
unsafe fn collision_spec(ret: u32) {
}

/// ```lean, anneal, spec
/// theorem spec (x : Std.U32) (h_req0 : x.val > 0) (h_req1 : x.val < 100) :
///   Aeneas.Std.WP.spec (complex_spec x) (fun ret_ => True) := by
///   sorry
/// ```
unsafe fn complex_spec(x: u32) {
}
