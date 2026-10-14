use zerocopy::{FromBytes, IntoBytes, TryFromBytes};
use zerocopy::byteorder::{U16, BE, LE};

fn main() {
    let mut accepted = Vec::new();
    for byte in 0..=u8::MAX {
        let input = [byte];
        let actual = bool::try_read_from_bytes(&input);
        assert_eq!(actual.is_ok(), byte <= 1);
        if let Ok(value) = actual {
            assert_eq!(value, byte == 1);
            accepted.push(byte);
        }
    }
    for first in 0..=u8::MAX {
        for second in 0..=u8::MAX {
            let input = [first, second];
            let actual = <[bool; 2]>::try_read_from_bytes(&input);
            assert_eq!(actual.is_ok(), first <= 1 && second <= 1);
            if let Ok(value) = actual {
                assert_eq!(value, [first == 1, second == 1]);
            }
        }
    }
    assert!(bool::try_read_from_bytes(&[]).is_err());
    assert!(bool::try_read_from_bytes(&[0, 1]).is_err());
    assert_eq!(<[(); 3]>::read_from_bytes(&[]).unwrap(), [(), (), ()]);
    assert!(<[(); 3]>::read_from_bytes(&[0]).is_err());
    assert_eq!(U16::<LE>::read_from_bytes(&[1, 0]).unwrap().get(), 1);
    assert_eq!(U16::<BE>::read_from_bytes(&[1, 0]).unwrap().get(), 256);

    // An initialized array gives a safely accessible aligned byte region.
    let allocation = [0u64; 2];
    let bytes = allocation.as_bytes();
    for offset in 0..8 {
        let actual = u16::ref_from_bytes(&bytes[offset..offset + 2]);
        assert_eq!(actual.is_ok(), (bytes.as_ptr() as usize + offset) % std::mem::align_of::<u16>() == 0);
    }

    let source = [1u8, 2, 3, 4];
    let mut prefix = [0xAA; 6];
    source.write_to_prefix(&mut prefix).unwrap();
    assert_eq!(prefix, [1, 2, 3, 4, 0xAA, 0xAA]);
    let mut suffix = [0xAA; 6];
    source.write_to_suffix(&mut suffix).unwrap();
    assert_eq!(suffix, [0xAA, 0xAA, 1, 2, 3, 4]);
    let mut too_short = [0xAA; 3];
    assert!(source.write_to_prefix(&mut too_short).is_err());
    assert_eq!(too_short, [0xAA; 3]);
    println!("bool_candidates=256;accepted={accepted:?}");
    println!("bool_array_candidates=65536;accepted=4;all_results_match");
    println!("width_and_zero_sized_controls=passed");
    println!("byte_order_controls=passed");
    println!("aligned_reference_candidates=8;all_results_match");
    println!("prefix_suffix_and_rejection_preservation=passed");
}
