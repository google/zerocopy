/// ```lean, anneal, spec
/// theorem spec (x : Std.U32) :
///   Aeneas.Std.WP.spec (crashes x) (fun ret_ => False) := by
///   sorry
/// ```
pub fn crashes(x: u32) -> ! {
    if x > 0 {
        panic!("nonzero");
    } else {
        panic!("zero");
    }
}

pub fn may_crash(x: u32) -> u32 {
    if x == 0 { crashes(x) } else { x }
}

fn main() {}
