#[repr(C, packed)]
struct Packet { tag: u8, value: u32 }
fn main() {
    let packet = Packet { tag: 7, value: 0x12345678 };
    let _reference = &packet.value;
}
