//! Use [BitWriter] to write an arbitrary amount of bits into a buffer.
use alloc::vec::Vec;

/// An interface for writing an arbitrary number of bits into a buffer. Write new bits into the buffer with `write_bits`, and
/// obtain the output using `dump`.
#[derive(Debug)]
pub(crate) struct BitWriter<V: AsMut<Vec<u8>>> {
    /// The buffer that's filled with bits
    output: V,
    /// holds a partially filled byte which gets put in outpu when it's fill with a write_bits call
    partial: u64,
    bits_in_partial: usize,
    /// The index pointing to the next unoccupied bit. Effectively just
    /// the number of bits that have been written into the buffer so far.
    bit_idx: usize,
}

impl BitWriter<Vec<u8>> {
    /// Initialize a new writer.
    pub fn new() -> Self {
        Self {
            output: Vec::new(),
            partial: 0,
            bits_in_partial: 0,
            bit_idx: 0,
        }
    }
}

impl<V: AsMut<Vec<u8>>> BitWriter<V> {
    /// Initialize a new writer.
    pub fn from(mut output: V) -> BitWriter<V> {
        BitWriter {
            bit_idx: output.as_mut().len() * 8,
            output,
            partial: 0,
            bits_in_partial: 0,
        }
    }

    /// Get the current index. Can be used to reset to this index or to later change the bits at this index
    pub fn index(&self) -> usize {
        self.bit_idx + self.bits_in_partial
    }

    /// Reset to an index. Currently only supports resetting to a byte aligned index
    pub fn reset_to(&mut self, index: usize) {
        assert!(index.is_multiple_of(8));
        self.partial = 0;
        self.bits_in_partial = 0;
        self.bit_idx = index;
        self.output.as_mut().resize(index / 8, 0);
    }

    /// Change the bits at the index. `bits` contains the ǹum_bits` new bits that should be written
    /// Instead of the current content. `bits` *MUST* only contain zeroes in the upper bits outside of the `0..num_bits` range.
    pub fn change_bits(&mut self, idx: usize, bits: impl Into<u64>, num_bits: usize) {
        self.change_bits_64(idx, bits.into(), num_bits);
    }

    /// Monomorphized version of `change_bits`
    pub fn change_bits_64(&mut self, mut idx: usize, mut bits: u64, mut num_bits: usize) {
        self.flush();
        assert!(idx + num_bits < self.index());
        assert!(self.index() - (idx + num_bits) > self.bits_in_partial);

        // We might be changing bits unaligned to byte borders.
        // This means the lower bits of the first byte we are touching must stay the same
        if !idx.is_multiple_of(8) {
            // How many (upper) bits will change in the first byte?
            let bits_in_first_byte = 8 - (idx % 8);
            // We don't support only changing a few bits in the middle of a byte
            assert!(bits_in_first_byte <= num_bits);
            // Zero out the upper bits that will be changed while keeping the lower bits intact
            self.output.as_mut()[idx / 8] &= 0xFFu8 >> bits_in_first_byte;
            // Shift the bits up and put them in the now zeroed out bits
            let new_bits = (bits << (8 - bits_in_first_byte)) as u8;
            self.output.as_mut()[idx / 8] |= new_bits;
            // Update the state. Note that we are now definitely working byte aligned
            num_bits -= bits_in_first_byte;
            bits >>= bits_in_first_byte;
            idx += bits_in_first_byte;
        }

        assert!(idx.is_multiple_of(8));
        // We are now byte aligned, change idx to byte resolution
        let mut idx = idx / 8;

        // Update full bytes by just shifting and extracting bytes from the bits
        while num_bits >= 8 {
            self.output.as_mut()[idx] = bits as u8;
            num_bits -= 8;
            bits >>= 8;
            idx += 1;
        }

        // Deal with leftover bits that wont fill a full byte, keeping the upper bits of the original byte intact
        if num_bits > 0 {
            self.output.as_mut()[idx] &= 0xFFu8 << num_bits;
            self.output.as_mut()[idx] |= bits as u8;
        }
    }

    /// Simply append bytes to the buffer. Only works if the buffer was already byte aligned
    pub fn append_bytes(&mut self, data: &[u8]) {
        if self.misaligned() != 0 {
            panic!("Don't append bytes when writer is misaligned")
        }
        self.flush();
        self.output.as_mut().extend_from_slice(data);
        self.bit_idx += data.len() * 8;
    }

    /// Flush temporary internal buffers to the output buffer. Only works if this is currently byte aligned
    pub fn flush(&mut self) {
        assert!(self.bits_in_partial.is_multiple_of(8));
        let full_bytes = self.bits_in_partial / 8;
        self.output
            .as_mut()
            .extend_from_slice(&self.partial.to_le_bytes()[..full_bytes]);
        self.partial >>= full_bytes * 8;
        self.bits_in_partial -= full_bytes * 8;
        self.bit_idx += full_bytes * 8;
    }

    /// Write the lower `num_bits` from `bits` into the writer. `bits` *MUST* only contain zeroes in the upper bits outside of the `0..num_bits` range.
    pub fn write_bits(&mut self, bits: impl Into<u64>, num_bits: usize) {
        self.write_bits_64(bits.into(), num_bits);
    }

    /// This is the special case where we need to flush the partial buffer to the output.
    /// Marked as cold and in a separate function so the optimizer has more information.
    #[cold]
    fn write_bits_64_cold(&mut self, bits: u64, num_bits: usize) {
        assert!(self.bits_in_partial + num_bits >= 64);
        // Fill the partial buffer so it contains 64 bits
        let bits_free_in_partial = 64 - self.bits_in_partial;
        let part = bits << (64 - bits_free_in_partial);
        let merged = self.partial | part;
        // Put the 8 bytes into the output buffer
        self.output
            .as_mut()
            .extend_from_slice(&merged.to_le_bytes());
        self.bit_idx += 64;
        self.partial = 0;
        self.bits_in_partial = 0;

        let mut num_bits = num_bits - bits_free_in_partial;
        let mut bits = bits >> bits_free_in_partial;

        // While we are at it push full bytes into the output buffer instead of polluting the partial buffer
        while num_bits / 8 > 0 {
            let byte = bits as u8;
            self.output.as_mut().push(byte);
            num_bits -= 8;
            self.bit_idx += 8;
            bits >>= 8;
        }

        // The last few bits belong into the partial buffer
        assert!(num_bits < 8);
        if num_bits > 0 {
            let mask = (1 << num_bits) - 1;
            self.partial = bits & mask;
            self.bits_in_partial = num_bits;
        }
    }

    /// Monomorphized version of `change_bits`
    pub fn write_bits_64(&mut self, bits: u64, num_bits: usize) {
        if num_bits == 0 {
            return;
        }

        if bits > 0 {
            debug_assert!(bits.ilog2() <= num_bits as u32);
        }

        // fill partial byte first
        if num_bits + self.bits_in_partial < 64 {
            let part = bits << self.bits_in_partial;
            let merged = self.partial | part;
            self.partial = merged;
            self.bits_in_partial += num_bits;
        } else {
            // If the partial buffer can't hold the num_bits we need to make space
            self.write_bits_64_cold(bits, num_bits);
        }
    }

    /// Returns the populated buffer that you've been writing bits into.
    ///
    /// This function consumes the writer, so it cannot be used after
    /// dumping
    pub fn dump(mut self) -> V {
        if self.misaligned() != 0 {
            panic!("`dump` was called on a bit writer but an even number of bytes weren't written into the buffer. Was: {}", self.index())
        }
        self.flush();
        debug_assert_eq!(self.partial, 0);
        self.output
    }

    /// Returns how many bits are missing for an even byte
    pub fn misaligned(&self) -> usize {
        let idx = self.index();
        if idx.is_multiple_of(8) {
            0
        } else {
            8 - (idx % 8)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::BitWriter;
    use alloc::vec;

    #[test]
    fn from_existing() {
        // Define an existing vec, write some bits into it
        let mut existing_vec = vec![255_u8];
        let mut bw = BitWriter::from(&mut existing_vec);
        bw.write_bits(0u8, 8);
        bw.flush();
        assert_eq!(vec![255, 0], existing_vec);
    }

    #[test]
    fn change_bits() {
        let mut writer = BitWriter::new();
        writer.write_bits(0u32, 24);
        writer.change_bits(8, 0xFFu8, 8);
        assert_eq!(vec![0, 0xFF, 0], writer.dump());

        let mut writer = BitWriter::new();
        writer.write_bits(0u32, 24);
        writer.change_bits(6, 0x0FFFu16, 12);
        assert_eq!(vec![0b11000000, 0xFF, 0b00000011], writer.dump());
    }

    #[test]
    fn single_byte_written_4_4() {
        // Write the first 4 bits as 1s and the last 4 bits as 0s
        // 1010 is used where values should never be read from.
        let mut bw = BitWriter::new();
        bw.write_bits(0b1111u8, 4);
        bw.write_bits(0b0000u8, 4);
        let output = bw.dump();
        assert!(output.len() == 1, "Single byte written into writer returned a vec that wasn't one byte, vec was {} elements long", output.len());
        assert_eq!(
            0b0000_1111, output[0],
            "4 bits and 4 bits written into buffer"
        );
    }

    #[test]
    fn single_byte_written_3_5() {
        // Write the first 3 bits as 1s and the last 5 bits as 0s
        let mut bw = BitWriter::new();
        bw.write_bits(0b111u8, 3);
        bw.write_bits(0b0_0000u8, 5);
        let output = bw.dump();
        assert!(output.len() == 1, "Single byte written into writer return a vec that wasn't one byte, vec was {} elements long", output.len());
        assert_eq!(0b0000_0111, output[0], "3 and 5 bits written into buffer");
    }

    #[test]
    fn single_byte_written_1_7() {
        // Write the first bit as a 1 and the last 7 bits as 0s
        let mut bw = BitWriter::new();
        bw.write_bits(0b1u8, 1);
        bw.write_bits(0u8, 7);
        let output = bw.dump();
        assert!(output.len() == 1, "Single byte written into writer return a vec that wasn't one byte, vec was {} elements long", output.len());
        assert_eq!(0b0000_0001, output[0], "1 and 7 bits written into buffer");
    }

    #[test]
    fn single_byte_written_8() {
        // Write an entire byte
        let mut bw = BitWriter::new();
        bw.write_bits(1u8, 8);
        let output = bw.dump();
        assert!(output.len() == 1, "Single byte written into writer return a vec that wasn't one byte, vec was {} elements long", output.len());
        assert_eq!(1, output[0], "1 and 7 bits written into buffer");
    }

    #[test]
    fn multi_byte_clean_boundary_4_4_4_4() {
        // Writing 4 bits at a time for 2 bytes
        let mut bw = BitWriter::new();
        bw.write_bits(0u8, 4);
        bw.write_bits(0b1111u8, 4);
        bw.write_bits(0b1111u8, 4);
        bw.write_bits(0u8, 4);
        assert_eq!(vec![0b1111_0000, 0b0000_1111], bw.dump());
    }

    #[test]
    fn multi_byte_clean_boundary_16_8() {
        // Writing 16 bits at once
        let mut bw = BitWriter::new();
        bw.write_bits(0x0100u16, 16);
        bw.write_bits(69u8, 8);
        assert_eq!(vec![0, 1, 69], bw.dump())
    }

    #[test]
    fn multi_byte_boundary_crossed_4_12() {
        // Writing 4 1s and then 12 zeros
        let mut bw = BitWriter::new();
        bw.write_bits(0b1111u8, 4);
        bw.write_bits(0b0000_0011_0100_0010u16, 12);
        assert_eq!(vec![0b0010_1111, 0b0011_0100], bw.dump());
    }

    #[test]
    fn multi_byte_boundary_crossed_4_5_7() {
        // Writing 4 1s and then 5 zeros then 7 1s
        let mut bw = BitWriter::new();
        bw.write_bits(0b1111u8, 4);
        bw.write_bits(0b0_0000u8, 5);
        bw.write_bits(0b111_1111u8, 7);
        assert_eq!(vec![0b0000_1111, 0b1111_1110], bw.dump());
    }

    #[test]
    fn multi_byte_boundary_crossed_1_9_6() {
        // Writing 1 1 and then 9 zeros then 6 1s
        let mut bw = BitWriter::new();
        bw.write_bits(0b1u8, 1);
        bw.write_bits(0b0_0000_0000u16, 9);
        bw.write_bits(0b11_1111u8, 6);
        assert_eq!(vec![0b0000_0001, 0b1111_1100], bw.dump());
    }

    #[test]
    #[should_panic]
    fn catches_unaligned_dump() {
        // Write a single bit in then dump it, making sure
        // the correct error is returned
        let mut bw = BitWriter::new();
        bw.write_bits(0u8, 1);
        bw.dump();
    }

    #[test]
    #[should_panic]
    fn catches_dirty_upper_bits() {
        let mut bw = BitWriter::new();
        bw.write_bits(10u8, 1);
    }

    #[test]
    fn add_multiple_aligned() {
        let mut bw = BitWriter::new();
        bw.write_bits(0x00_0F_F0_FFu32, 32);
        assert_eq!(vec![0xFF, 0xF0, 0x0F, 0x00], bw.dump());
    }

    // #[test]
    // fn catches_more_than_in_buf() {
    //     todo!();
    // }
}
