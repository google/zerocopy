
///@ lean spec foo(x : U32)
///@ ensures |ret| ret.val = x.val
///@ proof
///@   simp [foo]
pub fn foo(x: u32) -> u32 {
    x
}

pub fn trigger_box_error(fail: bool) -> Result<(), Box<dyn std::fmt::Debug>> {
    let e = if fail {
        Box::new("failed")
    } else {
        Box::new("succeeded")
    };
    if fail {
        return Err(e);
    }
    Ok(())
}

fn main() {
    let _ = foo(42);
    let _ = trigger_box_error(true);
}
