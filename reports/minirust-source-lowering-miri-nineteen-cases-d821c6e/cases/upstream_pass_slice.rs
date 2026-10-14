// Pass slice reference accross function boundaries
pub fn assert_some_elements(a: &[i32]) {
    assert!(a[1] == -40);
    assert!(a[2] == 30);
    assert!(a[3] == -20);
}

pub fn change_some_elements(a: &mut [u8]) {
    a[0] += 1;
    a[1] -= 1;
}

const THE_SLICE: &'static [u16] = &[1, 2, 3, 4, 5, 6, 7, 8];

fn slice_test() {
    let x: [u32; 5] = [41, 42, 43, 44, 45];
    let y = &x as &[u32];

    assert!(y[1] == 42);
    assert!(y.len() == 5);
    assert!(y.iter().count() == 5);
    assert!(y[1..].len() == 4);
    assert!(y[1..][0] == 42);
    assert!(y[1..=2] == [42, 43]);

    let z = unsafe { core::slice::from_raw_parts::<'_, u32>(y.as_ptr().add(1), 3) };
    assert!(z.len() == 3);
    assert!(z[0] == 42);
}

fn main() {
    // Check unsizing
    let x: [i32; 5] = [50, -40, 30, -20, 10];
    let slice: &[i32] = &x;

    // Check indexablity
    assert_some_elements(slice);

    let mut a2 = [1, 2, 3, 4];
    change_some_elements(&mut a2);
    assert!(a2[0] == 2);

    assert!(slice.len() == 5);

    // Check constant slices
    assert!(THE_SLICE.len() == 8);
    assert!(THE_SLICE[3] == 4);

    // Check iterators
    assert!(slice.iter().count() == 5);

    // check the iterator in a for loop, checking alternating signs
    let mut sign = 1;
    for elem in slice {
        assert!(sign * elem > 0);
        sign *= -1;
    }
    assert!(sign == -1);

    // Check `from_raw_parts`
    let elem1_ptr = unsafe { slice.as_ptr().add(1) };
    let sub_slice = unsafe { core::slice::from_raw_parts::<'_, i32>(elem1_ptr, 4) };
    assert!(sub_slice.len() == 4);
    assert!(sub_slice[0] == -40);

    // Check subslicing
    let sub_slice = &slice[1..];
    assert!(sub_slice.len() == 4);
    assert!(sub_slice[0] == -40);

    let sub_slice = &slice[1..4];
    assert!(sub_slice.len() == 3);
    assert!(sub_slice[0] == -40);

    let sub_slice = &slice[..4];
    assert!(sub_slice.len() == 4);
    assert!(sub_slice[0] == 50);

    // Check equality
    assert!(&slice[1..4] == &[-40, 30, -20]);
    assert!(slice[1..4] == [-40, 30, -20]);
    // This fails, since it uses the `compare_bytes` intrinsic.
    // let u8_slice: &[u8] = b"ABCABC";
    // assert!(&u8_slice[..2] == &u8_slice[2..4]);

    slice_test();
}
