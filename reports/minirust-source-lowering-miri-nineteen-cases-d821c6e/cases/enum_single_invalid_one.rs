#[allow(dead_code)]
#[repr(u8)]
#[derive(Clone, Copy)]
enum E { Only = 0 }
fn main() {
 let byte = 1u8;
 let pointer = std::ptr::addr_of!(byte).cast::<E>();
 let value = unsafe { pointer.read() };
 match value { E::Only => () }
}
