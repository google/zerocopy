use alloc::vec::Vec;

/// Returns the minimum number of bytes needed to represent this value, as
/// either 1, 2, 4, or 8 bytes. A value of 0 will still return one byte.
///
/// Used for variable length fields like `Dictionary_ID` or `Frame_Content_Size`.
pub fn find_min_size(val: u64) -> usize {
    if val == 0 {
        return 1;
    }
    if val >> 8 == 0 {
        return 1;
    }
    if val >> 16 == 0 {
        return 2;
    }
    if val >> 32 == 0 {
        return 4;
    }
    8
}

/// Returns the same value, but represented using the smallest number of bytes needed.
/// Returned vector will be 1, 2, 4, or 8 bytes in length. Zero is represented as 1 byte.
///
/// Operates in **little-endian**.
pub fn minify_val(val: u64) -> Vec<u8> {
    let new_size = find_min_size(val);
    val.to_le_bytes()[0..new_size].to_vec()
}

#[cfg(test)]
mod tests {
    use super::find_min_size;
    use super::minify_val;
    use alloc::vec;

    #[test]
    fn min_size_detection() {
        assert_eq!(find_min_size(0), 1);
        assert_eq!(find_min_size(0xff), 1);
        assert_eq!(find_min_size(0xff_ff), 2);
        assert_eq!(find_min_size(0x00_ff_ff_ff), 4);
        assert_eq!(find_min_size(0xff_ff_ff_ff), 4);
        assert_eq!(find_min_size(0x00ff_ffff_ffff_ffff), 8);
        assert_eq!(find_min_size(0xffff_ffff_ffff_ffff), 8);
    }

    #[test]
    fn bytes_minified() {
        assert_eq!(minify_val(0), vec![0]);
        assert_eq!(minify_val(0xff), vec![0xff]);
        assert_eq!(minify_val(0xff_ff), vec![0xff, 0xff]);
        assert_eq!(minify_val(0xff_ff_ff_ff), vec![0xff, 0xff, 0xff, 0xff]);
        assert_eq!(
            minify_val(0xffff_ffff_ffff_ffff),
            vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
        );
    }
}
