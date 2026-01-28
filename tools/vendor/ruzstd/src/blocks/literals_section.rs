//! Utilities and representations for the first half of a block, the literals section.
//! It contains data that is then copied from by the sequences section.
use crate::bit_io::BitReader;
use crate::decoding::errors::LiteralsSectionParseError;

/// A compressed block consists of two sections, a literals section, and a sequences section.
///
/// This is the first of those two sections. A literal is just any arbitrary data, and it is copied by the sequences section
pub struct LiteralsSection {
    /// - If this block is of type [LiteralsSectionType::Raw], then the data is `regenerated_bytes`
    ///   bytes long, and it contains the raw literals data to be used during the second section,
    ///   the sequences section.
    /// - If this block is of type [LiteralsSectionType::RLE],
    ///   then the literal consists of a single byte repeated `regenerated_size` times.
    /// - For types [LiteralsSectionType::Compressed] or [LiteralsSectionType::Treeless],
    ///   then this is the size of the decompressed data.
    pub regenerated_size: u32,
    /// - For types [LiteralsSectionType::Raw] and [LiteralsSectionType::RLE], this value is not present.
    /// - For types [LiteralsSectionType::Compressed] and [LiteralsSectionType::Treeless], this value will
    ///   be set to the size of the compressed data.
    pub compressed_size: Option<u32>,
    /// This value will be either 1 stream or 4 streams if the literal is of type
    /// [LiteralsSectionType::Compressed] or [LiteralsSectionType::Treeless], and it
    /// is not used for RLE or uncompressed literals.
    pub num_streams: Option<u8>,
    /// The type of the literal section.
    pub ls_type: LiteralsSectionType,
}

/// The way which a literal section is encoded.
pub enum LiteralsSectionType {
    /// Literals are stored uncompressed.
    Raw,
    /// Literals consist of a single byte value repeated [LiteralsSection::regenerated_size] times.
    #[allow(clippy::upper_case_acronyms)]
    RLE,
    /// This is a standard Huffman-compressed block, starting with a Huffman tree description.
    /// In this mode, there are at least *2* different literals represented in the Huffman tree
    /// description.
    Compressed,
    /// This is a Huffman-compressed block,
    /// using the Huffman tree from the previous [LiteralsSectionType::Compressed] block
    /// in the sequence. If this mode is triggered without any previous Huffman-tables in the
    /// frame (or dictionary), it should be treated as data corruption.
    Treeless,
}

impl Default for LiteralsSection {
    fn default() -> Self {
        Self::new()
    }
}

impl LiteralsSection {
    /// Create a new [LiteralsSection].
    pub fn new() -> LiteralsSection {
        LiteralsSection {
            regenerated_size: 0,
            compressed_size: None,
            num_streams: None,
            ls_type: LiteralsSectionType::Raw,
        }
    }

    /// Given the first byte of a header, determine the size of the whole header, from 1 to 5 bytes.
    pub fn header_bytes_needed(&self, first_byte: u8) -> Result<u8, LiteralsSectionParseError> {
        let ls_type: LiteralsSectionType = Self::section_type(first_byte)?;
        let size_format = (first_byte >> 2) & 0x3;
        match ls_type {
            LiteralsSectionType::RLE | LiteralsSectionType::Raw => {
                match size_format {
                    0 | 2 => {
                        // size_format actually only uses one bit
                        // regenerated_size uses 5 bits
                        Ok(1)
                    }
                    1 => {
                        // size_format uses 2 bit
                        // regenerated_size uses 12 bits
                        Ok(2)
                    }
                    3 => {
                        // size_format uses 2 bit
                        // regenerated_size uses 20 bits
                        Ok(3)
                    }
                    _ => panic!(
                        "This is a bug in the program. There should only be values between 0..3"
                    ),
                }
            }
            LiteralsSectionType::Compressed | LiteralsSectionType::Treeless => {
                match size_format {
                    0 | 1 => {
                        // Only differ in num_streams
                        // both regenerated and compressed sizes use 10 bit
                        Ok(3)
                    }
                    2 => {
                        // both regenerated and compressed sizes use 14 bit
                        Ok(4)
                    }
                    3 => {
                        // both regenerated and compressed sizes use 18 bit
                        Ok(5)
                    }

                    _ => panic!(
                        "This is a bug in the program. There should only be values between 0..3"
                    ),
                }
            }
        }
    }

    /// Parse the header into `self`, and returns the number of bytes read.
    pub fn parse_from_header(&mut self, raw: &[u8]) -> Result<u8, LiteralsSectionParseError> {
        let mut br: BitReader<'_> = BitReader::new(raw);
        let block_type = br.get_bits(2)? as u8;
        self.ls_type = Self::section_type(block_type)?;
        let size_format = br.get_bits(2)? as u8;

        let byte_needed = self.header_bytes_needed(raw[0])?;
        if raw.len() < byte_needed as usize {
            return Err(LiteralsSectionParseError::NotEnoughBytes {
                have: raw.len(),
                need: byte_needed,
            });
        }

        match self.ls_type {
            LiteralsSectionType::RLE | LiteralsSectionType::Raw => {
                self.compressed_size = None;
                match size_format {
                    0 | 2 => {
                        // size_format actually only uses one bit
                        // regenerated_size uses 5 bits
                        self.regenerated_size = u32::from(raw[0]) >> 3;
                        Ok(1)
                    }
                    1 => {
                        // size_format uses 2 bit
                        // regenerated_size uses 12 bits
                        self.regenerated_size = (u32::from(raw[0]) >> 4) + (u32::from(raw[1]) << 4);
                        Ok(2)
                    }
                    3 => {
                        // size_format uses 2 bit
                        // regenerated_size uses 20 bits
                        self.regenerated_size = (u32::from(raw[0]) >> 4)
                            + (u32::from(raw[1]) << 4)
                            + (u32::from(raw[2]) << 12);
                        Ok(3)
                    }
                    _ => panic!(
                        "This is a bug in the program. There should only be values between 0..3"
                    ),
                }
            }
            LiteralsSectionType::Compressed | LiteralsSectionType::Treeless => {
                match size_format {
                    0 => {
                        self.num_streams = Some(1);
                    }
                    1..=3 => {
                        self.num_streams = Some(4);
                    }
                    _ => panic!(
                        "This is a bug in the program. There should only be values between 0..3"
                    ),
                };

                match size_format {
                    0 | 1 => {
                        // Differ in num_streams see above
                        // both regenerated and compressed sizes use 10 bit

                        // 4 from the first, six from the second byte
                        self.regenerated_size =
                            (u32::from(raw[0]) >> 4) + ((u32::from(raw[1]) & 0x3f) << 4);

                        // 2 from the second, full last byte
                        self.compressed_size =
                            Some(u32::from(raw[1] >> 6) + (u32::from(raw[2]) << 2));
                        Ok(3)
                    }
                    2 => {
                        // both regenerated and compressed sizes use 14 bit

                        // 4 from first, full second, 2 from the third byte
                        self.regenerated_size = (u32::from(raw[0]) >> 4)
                            + (u32::from(raw[1]) << 4)
                            + ((u32::from(raw[2]) & 0x3) << 12);

                        // 6 from the third, full last byte
                        self.compressed_size =
                            Some((u32::from(raw[2]) >> 2) + (u32::from(raw[3]) << 6));
                        Ok(4)
                    }
                    3 => {
                        // both regenerated and compressed sizes use 18 bit

                        // 4 from first, full second, six from third byte
                        self.regenerated_size = (u32::from(raw[0]) >> 4)
                            + (u32::from(raw[1]) << 4)
                            + ((u32::from(raw[2]) & 0x3F) << 12);

                        // 2 from third, full fourth, full fifth byte
                        self.compressed_size = Some(
                            (u32::from(raw[2]) >> 6)
                                + (u32::from(raw[3]) << 2)
                                + (u32::from(raw[4]) << 10),
                        );
                        Ok(5)
                    }

                    _ => panic!(
                        "This is a bug in the program. There should only be values between 0..3"
                    ),
                }
            }
        }
    }

    /// Given the first two bits of a header, determine the type of a header.
    fn section_type(raw: u8) -> Result<LiteralsSectionType, LiteralsSectionParseError> {
        let t = raw & 0x3;
        match t {
            0 => Ok(LiteralsSectionType::Raw),
            1 => Ok(LiteralsSectionType::RLE),
            2 => Ok(LiteralsSectionType::Compressed),
            3 => Ok(LiteralsSectionType::Treeless),
            other => Err(LiteralsSectionParseError::IllegalLiteralSectionType { got: other }),
        }
    }
}
