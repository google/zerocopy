///@ lean spec safe_def (x : U32)
///@ : ∃ ret, safe_def x = ok ret
pub fn safe_def(x: u32) -> u32 {
    x
}

fn main() {}
