#[repr(C, packed)]
struct Packet { tag: u8, value: u32 }
fn main() {
    let packet = Packet { tag: 7, value: 0x12345678 };
    let pointer = &raw const packet.value;
    // The field is initialized; the raw address stays within this live object.
    // read_unaligned does not form a potentially unaligned reference.
    let value = unsafe { pointer.read_unaligned() };
    assert_eq!(value, 0x12345678);
    println!("value={value:08x}");
}
