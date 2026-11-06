#[allow(dead_code)]
#[repr(u8)]
#[derive(Clone, Copy)]
enum E { Zero = 0, One = 1 }
fn main() {
 let byte = 2u8;
 let pointer = std::ptr::addr_of!(byte).cast::<E>();
 let value = unsafe { pointer.read() };
 match value { E::Zero => (), E::One => () }
}
