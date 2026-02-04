///@ lean spec foo(x : U32)
///@ ensures |ret| ret.val = x.val
///@ proof
///@   simp [foo]
pub fn foo(x: u32) -> u32 {
    x
}

pub fn trigger_dyn_trait() {
    let _x: Box<dyn std::fmt::Debug> = Box::new(42);
}

fn main() {
    foo(42);
    trigger_dyn_trait();
}
