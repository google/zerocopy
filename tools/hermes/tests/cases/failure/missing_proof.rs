///@ lean spec safe_def (x : U32)
///@ ensures |ret| ret = x
pub fn safe_def(x: u32) -> u32 {
    x
}

fn main() {}
