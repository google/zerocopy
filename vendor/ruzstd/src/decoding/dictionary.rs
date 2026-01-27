use alloc::vec::Vec;
use core::convert::TryInto;

use crate::decoding::errors::DictionaryDecodeError;
use crate::decoding::scratch::FSEScratch;
use crate::decoding::scratch::HuffmanScratch;

/// Zstandard includes support for "raw content" dictionaries, that store bytes optionally used
/// during sequence execution.
///
/// <https://github.com/facebook/zstd/blob/dev/doc/zstd_compression_format.md#dictionary-format>
pub struct Dictionary {
    /// A 4 byte value used by decoders to check if they can use
    /// the correct dictionary. This value must not be zero.
    pub id: u32,
    /// A dictionary can contain an entropy table, either FSE or
    /// Huffman.
    pub fse: FSEScratch,
    /// A dictionary can contain an entropy table, either FSE or
    /// Huffman.
    pub huf: HuffmanScratch,
    /// The content of a dictionary acts as a "past" in front of data
    /// to compress or decompress,
    /// so it can be referenced in sequence commands.
    /// As long as the amount of data decoded from this frame is less than or
    /// equal to Window_Size, sequence commands may specify offsets longer than
    /// the total length of decoded output so far to reference back to the
    /// dictionary, even parts of the dictionary with offsets larger than Window_Size.
    /// After the total output has surpassed Window_Size however,
    /// this is no longer allowed and the dictionary is no longer accessible
    pub dict_content: Vec<u8>,
    /// The 3 most recent offsets are stored so that they can be used
    /// during sequence execution, see
    /// <https://github.com/facebook/zstd/blob/dev/doc/zstd_compression_format.md#repeat-offsets>
    /// for more.
    pub offset_hist: [u32; 3],
}

/// This 4 byte (little endian) magic number refers to the start of a dictionary
pub const MAGIC_NUM: [u8; 4] = [0x37, 0xA4, 0x30, 0xEC];

impl Dictionary {
    /// Parses the dictionary from `raw` and set the tables
    /// it returns the dict_id for checking with the frame's `dict_id``
    pub fn decode_dict(raw: &[u8]) -> Result<Dictionary, DictionaryDecodeError> {
        let mut new_dict = Dictionary {
            id: 0,
            fse: FSEScratch::new(),
            huf: HuffmanScratch::new(),
            dict_content: Vec::new(),
            offset_hist: [2, 4, 8],
        };

        let magic_num: [u8; 4] = raw[..4].try_into().expect("optimized away");
        if magic_num != MAGIC_NUM {
            return Err(DictionaryDecodeError::BadMagicNum { got: magic_num });
        }

        let dict_id = raw[4..8].try_into().expect("optimized away");
        let dict_id = u32::from_le_bytes(dict_id);
        new_dict.id = dict_id;

        let raw_tables = &raw[8..];

        let huf_size = new_dict.huf.table.build_decoder(raw_tables)?;
        let raw_tables = &raw_tables[huf_size as usize..];

        let of_size = new_dict.fse.offsets.build_decoder(
            raw_tables,
            crate::decoding::sequence_section_decoder::OF_MAX_LOG,
        )?;
        let raw_tables = &raw_tables[of_size..];

        let ml_size = new_dict.fse.match_lengths.build_decoder(
            raw_tables,
            crate::decoding::sequence_section_decoder::ML_MAX_LOG,
        )?;
        let raw_tables = &raw_tables[ml_size..];

        let ll_size = new_dict.fse.literal_lengths.build_decoder(
            raw_tables,
            crate::decoding::sequence_section_decoder::LL_MAX_LOG,
        )?;
        let raw_tables = &raw_tables[ll_size..];

        let offset1 = raw_tables[0..4].try_into().expect("optimized away");
        let offset1 = u32::from_le_bytes(offset1);

        let offset2 = raw_tables[4..8].try_into().expect("optimized away");
        let offset2 = u32::from_le_bytes(offset2);

        let offset3 = raw_tables[8..12].try_into().expect("optimized away");
        let offset3 = u32::from_le_bytes(offset3);

        new_dict.offset_hist[0] = offset1;
        new_dict.offset_hist[1] = offset2;
        new_dict.offset_hist[2] = offset3;

        let raw_content = &raw_tables[12..];
        new_dict.dict_content.extend(raw_content);

        Ok(new_dict)
    }
}
