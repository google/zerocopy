//! `unsafe { match *p { .. } }` (place scrutinee) versus
//! `match unsafe { *p } { .. }` (block scrutinee, i.e. a value) on a type
//! that is not `Copy`. Compile with `--cfg value_scrutinee` to include the
//! second form.

pub struct Payload(pub u32);

pub enum Msg {
    A(Payload),
    B,
}

#[inline(never)]
pub fn place_scrutinee(p: *const Msg) -> u32 {
    unsafe {
        match *p {
            Msg::A(ref x) => x.0,
            Msg::B => 0,
        }
    }
}

#[cfg(value_scrutinee)]
#[inline(never)]
pub fn value_scrutinee(p: *const Msg) -> u32 {
    match unsafe { *p } {
        Msg::A(ref x) => x.0,
        Msg::B => 0,
    }
}

fn main() {
    let m = Msg::A(Payload(41));
    println!("PLACE={}", place_scrutinee(&m));
    let _ = Msg::B;
}
