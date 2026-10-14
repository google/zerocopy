#[allow(dead_code)]
#[derive(Clone, Copy)]
union Wide { p: *const [u8],
    words: [usize; 2],
}
#[inline(never)] fn identity(x: Wide) -> Wide { x }
fn main() {
    let data = [11u8, 22, 33];
    let pointer: *const [u8] = &data;
    let copied = identity(Wide { p: pointer });
    let roundtrip = unsafe { copied.p };
    assert!(roundtrip.len() == 3);
    assert!(unsafe { (&*roundtrip)[2] } == 33);
}
