use zerocopy::{FromBytes, IntoBytes, TryFromBytes};
use zerocopy::byteorder::{U16, BE, LE};

#[unsafe(no_mangle)]
pub extern "C" fn validate_bool(byte: u32) -> u32 {
    if byte > 255 { return 99; }
    match bool::try_read_from_bytes(&[byte as u8]) {
        Ok(value) => 1 + u32::from(value),
        Err(_) => 0,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn validate_pair(first: u32, second: u32) -> u32 {
    if first > 255 || second > 255 { return 99; }
    match <[bool; 2]>::try_read_from_bytes(&[first as u8, second as u8]) {
        Ok([a, b]) => 1 + 4 * u32::from(a) + 8 * u32::from(b),
        Err(_) => 0,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn byte_controls() -> u32 {
    let mut passed = 0;
    passed += u32::from(bool::try_read_from_bytes(&[]).is_err());
    passed += u32::from(bool::try_read_from_bytes(&[0, 1]).is_err());
    passed += u32::from(<[(); 3]>::read_from_bytes(&[]).is_ok());
    passed += u32::from(<[(); 3]>::read_from_bytes(&[0]).is_err());
    passed += u32::from(U16::<LE>::read_from_bytes(&[1, 0]).unwrap().get() == 1);
    passed += u32::from(U16::<BE>::read_from_bytes(&[1, 0]).unwrap().get() == 256);
    let source = [1u8, 2, 3, 4];
    let mut prefix = [0xAA; 6];
    source.write_to_prefix(&mut prefix).unwrap();
    passed += u32::from(prefix == [1, 2, 3, 4, 0xAA, 0xAA]);
    let mut suffix = [0xAA; 6];
    source.write_to_suffix(&mut suffix).unwrap();
    passed += u32::from(suffix == [0xAA, 0xAA, 1, 2, 3, 4]);
    let mut short = [0xAA; 3];
    passed += u32::from(source.write_to_prefix(&mut short).is_err());
    passed += u32::from(short == [0xAA; 3]);
    let aligned = [0u64; 2];
    let bytes = aligned.as_bytes();
    for offset in 0..8 {
        let actual = u16::ref_from_bytes(&bytes[offset..offset + 2]).is_ok();
        let expected = (bytes.as_ptr() as usize + offset) % std::mem::align_of::<u16>() == 0;
        passed += u32::from(actual == expected);
    }
    passed
}

#[repr(C)]
struct LayoutCase { byte: u8, word: usize }
#[repr(C, packed)]
struct PackedCase { byte: u8, word: usize }

#[unsafe(no_mangle)]
pub extern "C" fn layout(field: u32) -> u32 {
    match field {
        0 => std::mem::size_of::<usize>() as u32,
        1 => std::mem::size_of::<LayoutCase>() as u32,
        2 => std::mem::align_of::<LayoutCase>() as u32,
        3 => std::mem::offset_of!(LayoutCase, word) as u32,
        4 => std::mem::size_of::<PackedCase>() as u32,
        5 => std::mem::align_of::<PackedCase>() as u32,
        6 => std::mem::offset_of!(PackedCase, word) as u32,
        _ => 99,
    }
}
