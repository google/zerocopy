#[test]
fn test_bitreader_reversed() {
    use crate::bit_io::BitReaderReversed;

    let encoded: [u8; 16] = [
        0xC1, 0x41, 0x08, 0x00, 0x00, 0xEC, 0xC8, 0x96, 0x42, 0x79, 0xD4, 0xBC, 0xF7, 0x2C, 0xD5,
        0x48,
    ];
    //just the u128 in encoded
    let num_rev: u128 = 0x48_D5_2C_F7_BC_D4_79_42_96_C8_EC_00_00_08_41_C1;

    let mut br = BitReaderReversed::new(&encoded[..]);
    let mut accumulator = 0;
    let mut bits_read = 0;
    let mut x = 0;

    loop {
        x += 3;
        //semi random access pattern
        let mut num_bits = x % 16;
        if bits_read > 128 - num_bits {
            num_bits = 128 - bits_read;
        }

        let bits = br.get_bits(num_bits);
        bits_read += num_bits;
        accumulator |= u128::from(bits) << (128 - bits_read);
        if bits_read >= 128 {
            break;
        }
    }

    if accumulator != num_rev {
        panic!(
            "Bitreader failed somewhere. Accumulated bits: {:?}, Should be: {:?}",
            accumulator, num_rev
        );
    }
}

#[test]
fn test_bitreader_normal() {
    use crate::bit_io::BitReader;

    let encoded: [u8; 16] = [
        0xC1, 0x41, 0x08, 0x00, 0x00, 0xEC, 0xC8, 0x96, 0x42, 0x79, 0xD4, 0xBC, 0xF7, 0x2C, 0xD5,
        0x48,
    ];
    //just the u128 in encoded
    let num: u128 = 0x48_D5_2C_F7_BC_D4_79_42_96_C8_EC_00_00_08_41_C1;

    let mut br = BitReader::new(&encoded[..]);
    let mut accumulator = 0;
    let mut bits_read = 0;
    let mut x = 0;

    loop {
        x += 3;
        //semi random access pattern
        let mut num_bits = x % 16;
        if bits_read > 128 - num_bits {
            num_bits = 128 - bits_read;
        }

        let bits = br.get_bits(num_bits).unwrap();
        accumulator |= u128::from(bits) << bits_read;
        bits_read += num_bits;
        if bits_read >= 128 {
            break;
        }
    }

    if accumulator != num {
        panic!(
            "Bitreader failed somewhere. Accumulated bits: {:?}, Should be: {:?}",
            accumulator, num
        );
    }
}
