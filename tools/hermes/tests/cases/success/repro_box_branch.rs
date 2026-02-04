///@ lean spec foo(x : U32)
///@ ensures |ret| ret.val = x.val
///@ proof
///@   simp [foo]
pub fn foo(x: u32) -> u32 {
    x
}

pub fn trigger_branch_box(cond: bool) -> Box<u32> {
    if cond {
        Box::new(1)
    } else {
        Box::new(2)
    }
}

fn main() {
    foo(42);
    trigger_branch_box(true);
}
