#[repr(C, packed)]
struct Packed { byte: u8, word: u32 }

fn main() {
    let mut cases = 0;
    for k in 0..=4 {
        let mut bytes = [10u8, 20, 30, 40];
        {
            let (left, right) = bytes.split_at_mut(k);
            for x in left { *x = x.wrapping_add(1); }
            for x in right { *x = x.wrapping_add(2); }
        }
        assert_eq!(bytes, std::array::from_fn(|i| [10u8,20,30,40][i] + if i < k {1} else {2}));
        let p = bytes.as_mut_ptr();
        let erased = p.cast::<()>();
        assert_eq!(erased.cast::<u8>(), p);
        // The original reference's allocation remains live. No access occurs
        // through the erased raw pointer; equality is only an address control.
        cases += 1;
    }
    let p = Packed { byte: 1, word: 0x12345678 };
    let raw = std::ptr::addr_of!(p.word);
    // A raw address does not form an unaligned &u32. The live initialized field
    // contains a valid u32 and read_unaligned handles its packed placement.
    let value = unsafe { raw.read_unaligned() };
    assert_eq!(value, 0x12345678);
    println!("split_cases={cases} raw_cast_roundtrip=5 packed_value={value:08x}");
}
