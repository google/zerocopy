///@ lean spec add_mod (x y : Usize)
///@ requires _h_safe : x.val + y.val < 100
///@ ensures |ret| ret.val = (x.val + y.val) % Usize.size
///@ proof
///@   simp [add]
fn add(x: usize, y: usize) -> usize {
    x.wrapping_add(y)
}

fn main() {}
