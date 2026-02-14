
pub fn nested(x: &&u32, y: &mut &u32, z: &&mut u32) {
    let _ = **x;
    let _ = **y;
    let _ = **z;
}
