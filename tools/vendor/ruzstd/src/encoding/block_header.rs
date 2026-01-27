use crate::blocks::block::BlockType;
use alloc::vec::Vec;

#[derive(Debug)]
pub struct BlockHeader {
    /// Signals if this block is the last one.
    /// The frame will end after this block.
    pub last_block: bool,
    /// Influences the meaning of `block_size`.
    pub block_type: BlockType,
    /// - For `Raw` blocks, this is the size of the block's
    ///   content in bytes.
    /// - For `RLE` blocks, there will be a single byte follwing
    ///   the header, repeated `block_size` times.
    /// - For `Compressed` blocks, this is the length of
    ///   the compressed data.
    ///
    /// **This value must not be greater than 21 bits in length.**
    pub block_size: u32,
}

impl BlockHeader {
    /// Write encoded binary representation of this header into the provided buffer.
    pub fn serialize(self, output: &mut Vec<u8>) {
        vprintln!("Serializing block with the header: {self:?}");
        let encoded_block_type = match self.block_type {
            BlockType::Raw => 0,
            BlockType::RLE => 1,
            BlockType::Compressed => 2,
            BlockType::Reserved => panic!("You cannot use a reserved block type"),
        };
        let mut block_header = self.block_size << 3;
        block_header |= encoded_block_type << 1;
        block_header |= self.last_block as u32;
        output.extend_from_slice(&block_header.to_le_bytes()[0..3]);
    }
}

#[cfg(test)]
mod tests {
    use super::BlockHeader;
    use crate::{blocks::block::BlockType, decoding::block_decoder};
    use alloc::vec::Vec;

    #[test]
    fn block_header_serialize() {
        let header = BlockHeader {
            last_block: true,
            block_type: super::BlockType::Compressed,
            block_size: 69,
        };
        let mut serialized_header = Vec::new();
        header.serialize(&mut serialized_header);
        let mut decoder = block_decoder::new();
        let parsed_header = decoder
            .read_block_header(serialized_header.as_slice())
            .unwrap()
            .0;

        assert!(parsed_header.last_block);
        assert_eq!(parsed_header.block_type, BlockType::Compressed);
        assert_eq!(parsed_header.content_size, 69);
    }
}
