//! Basic checks that niches work.
use std::num::NonZeroI32;

fn convert_option_bool(b: Option<bool>) -> i8 {
    match b {
        None => -1,
        Some(false) => 0,
        Some(true) => 1,
    }
}

fn convert_result_bool(r: Result<bool, ()>) -> i8 {
    match r {
        Err(_) => -1,
        Ok(false) => 0,
        Ok(true) => 1,
    }
}

fn convert_option_ref(o: Option<&u8>) -> u8 {
    match o {
        Some(v) => *v,
        None => 0,
    }
}

fn convert_option_nz(o: Option<NonZeroI32>) -> i32 {
    match o {
        Some(v) => v.get(),
        None => 0,
    }
}

enum Outer {
    V1(u32, Inner, u16),
    V2,
    V3,
}

#[repr(i16)]
enum Inner {
    V1 = -32767,
    V2 = -32768,
}

/// Checks that negative niches work.
fn convert_outer(o: Outer) -> u8 {
    match o {
        Outer::V1(_x, Inner::V1, _y) => 0,
        Outer::V1(_x, Inner::V2, _y) => 1,
        Outer::V2 => 2,
        Outer::V3 => 3,
    }
}

#[repr(C, packed)]
struct WeirdNicheAlign {
    x: u8,
    /// inner has offset of 1 and a large enough niche for `Option` to use
    inner: Inner
}

/// Checks that enums with tag alignment smaller than its size work.
fn convert_option_weird_niche_align(instance: Option<WeirdNicheAlign>) -> u8 {
    if instance.is_some() { 1 } else { 0 }
}

fn main() {
    assert!(convert_option_bool(Some(true)) == 1);
    assert!(convert_option_bool(Some(false)) == 0);
    assert!(convert_option_bool(None) == -1);

    assert!(convert_result_bool(Ok(true)) == 1);
    assert!(convert_result_bool(Ok(false)) == 0);
    assert!(convert_result_bool(Err(())) == -1);

    assert!(convert_option_ref(Some(&42)) == 42);
    assert!(convert_option_ref(None) == 0);

    assert!(convert_option_nz(None) == 0);
    assert!(convert_option_nz(NonZeroI32::new(0)) == 0);
    assert!(convert_option_nz(NonZeroI32::new(14)) == 14);
    assert!(convert_option_nz(NonZeroI32::new(-14)) == -14);

    assert!(convert_outer(Outer::V1(12, Inner::V1, 42)) == 0);
    assert!(convert_outer(Outer::V1(8888, Inner::V2, 127)) == 1);
    assert!(convert_outer(Outer::V2) == 2);
    assert!(convert_outer(Outer::V3) == 3);

    assert!(convert_option_weird_niche_align(None) == 0);
    assert!(convert_option_weird_niche_align(Some(WeirdNicheAlign { x: 42, inner: Inner::V1 })) == 1);
}
