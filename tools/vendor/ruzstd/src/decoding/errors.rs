//! Errors that might occur while decoding zstd formatted data

use crate::bit_io::GetBitsError;
use crate::blocks::block::BlockType;
use crate::blocks::literals_section::LiteralsSectionType;
use crate::io::Error;
use alloc::vec::Vec;
use core::fmt;
#[cfg(feature = "std")]
use std::error::Error as StdError;

#[derive(Debug)]
#[non_exhaustive]
pub enum FrameDescriptorError {
    InvalidFrameContentSizeFlag { got: u8 },
}

impl fmt::Display for FrameDescriptorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidFrameContentSizeFlag { got } => write!(
                f,
                "Invalid Frame_Content_Size_Flag; Is: {got}, Should be one of: 0, 1, 2, 3"
            ),
        }
    }
}

#[cfg(feature = "std")]
impl StdError for FrameDescriptorError {}

#[derive(Debug)]
#[non_exhaustive]
pub enum FrameHeaderError {
    WindowTooBig { got: u64 },
    WindowTooSmall { got: u64 },
    FrameDescriptorError(FrameDescriptorError),
    DictIdTooSmall { got: usize, expected: usize },
    MismatchedFrameSize { got: usize, expected: u8 },
    FrameSizeIsZero,
    InvalidFrameSize { got: u8 },
}

impl fmt::Display for FrameHeaderError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WindowTooBig { got } => write!(
                f,
                "window_size bigger than allowed maximum. Is: {}, Should be lower than: {}",
                got,
                crate::common::MAX_WINDOW_SIZE
            ),
            Self::WindowTooSmall { got } => write!(
                f,
                "window_size smaller than allowed minimum. Is: {}, Should be greater than: {}",
                got,
                crate::common::MIN_WINDOW_SIZE
            ),
            Self::FrameDescriptorError(e) => write!(f, "{e:?}"),
            Self::DictIdTooSmall { got, expected } => write!(
                f,
                "Not enough bytes in dict_id. Is: {got}, Should be: {expected}"
            ),
            Self::MismatchedFrameSize { got, expected } => write!(
                f,
                "frame_content_size does not have the right length. Is: {got}, Should be: {expected}"
            ),
            Self::FrameSizeIsZero => write!(f, "frame_content_size was zero"),
            Self::InvalidFrameSize { got } => write!(
                f,
                "Invalid frame_content_size. Is: {got}, Should be one of 1, 2, 4, 8 bytes"
            ),
        }
    }
}

#[cfg(feature = "std")]
impl StdError for FrameHeaderError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            FrameHeaderError::FrameDescriptorError(source) => Some(source),
            _ => None,
        }
    }
}

impl From<FrameDescriptorError> for FrameHeaderError {
    fn from(error: FrameDescriptorError) -> Self {
        Self::FrameDescriptorError(error)
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum ReadFrameHeaderError {
    MagicNumberReadError(Error),
    BadMagicNumber(u32),
    FrameDescriptorReadError(Error),
    InvalidFrameDescriptor(FrameDescriptorError),
    WindowDescriptorReadError(Error),
    DictionaryIdReadError(Error),
    FrameContentSizeReadError(Error),
    SkipFrame { magic_number: u32, length: u32 },
}

impl fmt::Display for ReadFrameHeaderError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MagicNumberReadError(e) => write!(f, "Error while reading magic number: {e}"),
            Self::BadMagicNumber(e) => write!(f, "Read wrong magic number: 0x{e:X}"),
            Self::FrameDescriptorReadError(e) => {
                write!(f, "Error while reading frame descriptor: {e}")
            }
            Self::InvalidFrameDescriptor(e) => write!(f, "{e:?}"),
            Self::WindowDescriptorReadError(e) => {
                write!(f, "Error while reading window descriptor: {e}")
            }
            Self::DictionaryIdReadError(e) => write!(f, "Error while reading dictionary id: {e}"),
            Self::FrameContentSizeReadError(e) => {
                write!(f, "Error while reading frame content size: {e}")
            }
            Self::SkipFrame {
                magic_number,
                length,
            } => write!(
                f,
                "SkippableFrame encountered with MagicNumber 0x{magic_number:X} and length {length} bytes"
            ),
        }
    }
}

#[cfg(feature = "std")]
impl StdError for ReadFrameHeaderError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            ReadFrameHeaderError::MagicNumberReadError(source) => Some(source),
            ReadFrameHeaderError::FrameDescriptorReadError(source) => Some(source),
            ReadFrameHeaderError::InvalidFrameDescriptor(source) => Some(source),
            ReadFrameHeaderError::WindowDescriptorReadError(source) => Some(source),
            ReadFrameHeaderError::DictionaryIdReadError(source) => Some(source),
            ReadFrameHeaderError::FrameContentSizeReadError(source) => Some(source),
            _ => None,
        }
    }
}

impl From<FrameDescriptorError> for ReadFrameHeaderError {
    fn from(error: FrameDescriptorError) -> Self {
        Self::InvalidFrameDescriptor(error)
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum BlockHeaderReadError {
    ReadError(Error),
    FoundReservedBlock,
    BlockTypeError(BlockTypeError),
    BlockSizeError(BlockSizeError),
}

#[cfg(feature = "std")]
impl std::error::Error for BlockHeaderReadError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            BlockHeaderReadError::ReadError(source) => Some(source),
            BlockHeaderReadError::BlockTypeError(source) => Some(source),
            BlockHeaderReadError::BlockSizeError(source) => Some(source),
            BlockHeaderReadError::FoundReservedBlock => None,
        }
    }
}

impl ::core::fmt::Display for BlockHeaderReadError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> ::core::fmt::Result {
        match self {
            BlockHeaderReadError::ReadError(_) => write!(f, "Error while reading the block header"),
            BlockHeaderReadError::FoundReservedBlock => write!(
                f,
                "Reserved block occured. This is considered corruption by the documentation"
            ),
            BlockHeaderReadError::BlockTypeError(e) => write!(f, "Error getting block type: {e}"),
            BlockHeaderReadError::BlockSizeError(e) => {
                write!(f, "Error getting block content size: {e}")
            }
        }
    }
}

impl From<Error> for BlockHeaderReadError {
    fn from(val: Error) -> Self {
        Self::ReadError(val)
    }
}

impl From<BlockTypeError> for BlockHeaderReadError {
    fn from(val: BlockTypeError) -> Self {
        Self::BlockTypeError(val)
    }
}

impl From<BlockSizeError> for BlockHeaderReadError {
    fn from(val: BlockSizeError) -> Self {
        Self::BlockSizeError(val)
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum BlockTypeError {
    InvalidBlocktypeNumber { num: u8 },
}

#[cfg(feature = "std")]
impl std::error::Error for BlockTypeError {}

impl core::fmt::Display for BlockTypeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            BlockTypeError::InvalidBlocktypeNumber { num } => {
                write!(f,
                    "Invalid Blocktype number. Is: {num} Should be one of: 0, 1, 2, 3 (3 is reserved though",
                )
            }
        }
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum BlockSizeError {
    BlockSizeTooLarge { size: u32 },
}

#[cfg(feature = "std")]
impl std::error::Error for BlockSizeError {}

impl core::fmt::Display for BlockSizeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            BlockSizeError::BlockSizeTooLarge { size } => {
                write!(
                    f,
                    "Blocksize was bigger than the absolute maximum {} (128kb). Is: {}",
                    crate::common::MAX_BLOCK_SIZE,
                    size,
                )
            }
        }
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum DecompressBlockError {
    BlockContentReadError(Error),
    MalformedSectionHeader {
        expected_len: usize,
        remaining_bytes: usize,
    },
    DecompressLiteralsError(DecompressLiteralsError),
    LiteralsSectionParseError(LiteralsSectionParseError),
    SequencesHeaderParseError(SequencesHeaderParseError),
    DecodeSequenceError(DecodeSequenceError),
    ExecuteSequencesError(ExecuteSequencesError),
}

#[cfg(feature = "std")]
impl std::error::Error for DecompressBlockError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            DecompressBlockError::BlockContentReadError(source) => Some(source),
            DecompressBlockError::DecompressLiteralsError(source) => Some(source),
            DecompressBlockError::LiteralsSectionParseError(source) => Some(source),
            DecompressBlockError::SequencesHeaderParseError(source) => Some(source),
            DecompressBlockError::DecodeSequenceError(source) => Some(source),
            DecompressBlockError::ExecuteSequencesError(source) => Some(source),
            _ => None,
        }
    }
}

impl core::fmt::Display for DecompressBlockError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DecompressBlockError::BlockContentReadError(e) => {
                write!(f, "Error while reading the block content: {e}")
            }
            DecompressBlockError::MalformedSectionHeader {
                expected_len,
                remaining_bytes,
            } => {
                write!(f,
                    "Malformed section header. Says literals would be this long: {expected_len} but there are only {remaining_bytes} bytes left",
                )
            }
            DecompressBlockError::DecompressLiteralsError(e) => write!(f, "{e:?}"),
            DecompressBlockError::LiteralsSectionParseError(e) => write!(f, "{e:?}"),
            DecompressBlockError::SequencesHeaderParseError(e) => write!(f, "{e:?}"),
            DecompressBlockError::DecodeSequenceError(e) => write!(f, "{e:?}"),
            DecompressBlockError::ExecuteSequencesError(e) => write!(f, "{e:?}"),
        }
    }
}

impl From<Error> for DecompressBlockError {
    fn from(val: Error) -> Self {
        Self::BlockContentReadError(val)
    }
}

impl From<DecompressLiteralsError> for DecompressBlockError {
    fn from(val: DecompressLiteralsError) -> Self {
        Self::DecompressLiteralsError(val)
    }
}

impl From<LiteralsSectionParseError> for DecompressBlockError {
    fn from(val: LiteralsSectionParseError) -> Self {
        Self::LiteralsSectionParseError(val)
    }
}

impl From<SequencesHeaderParseError> for DecompressBlockError {
    fn from(val: SequencesHeaderParseError) -> Self {
        Self::SequencesHeaderParseError(val)
    }
}

impl From<DecodeSequenceError> for DecompressBlockError {
    fn from(val: DecodeSequenceError) -> Self {
        Self::DecodeSequenceError(val)
    }
}

impl From<ExecuteSequencesError> for DecompressBlockError {
    fn from(val: ExecuteSequencesError) -> Self {
        Self::ExecuteSequencesError(val)
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum DecodeBlockContentError {
    DecoderStateIsFailed,
    ExpectedHeaderOfPreviousBlock,
    ReadError { step: BlockType, source: Error },
    DecompressBlockError(DecompressBlockError),
}

#[cfg(feature = "std")]
impl std::error::Error for DecodeBlockContentError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            DecodeBlockContentError::ReadError { step: _, source } => Some(source),
            DecodeBlockContentError::DecompressBlockError(source) => Some(source),
            _ => None,
        }
    }
}

impl core::fmt::Display for DecodeBlockContentError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DecodeBlockContentError::DecoderStateIsFailed => {
                write!(
                    f,
                    "Can't decode next block if failed along the way. Results will be nonsense",
                )
            }
            DecodeBlockContentError::ExpectedHeaderOfPreviousBlock => {
                write!(f,
                            "Can't decode next block body, while expecting to decode the header of the previous block. Results will be nonsense",
                        )
            }
            DecodeBlockContentError::ReadError { step, source } => {
                write!(f, "Error while reading bytes for {step}: {source}",)
            }
            DecodeBlockContentError::DecompressBlockError(e) => write!(f, "{e:?}"),
        }
    }
}

impl From<DecompressBlockError> for DecodeBlockContentError {
    fn from(val: DecompressBlockError) -> Self {
        Self::DecompressBlockError(val)
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum DecodeBufferError {
    NotEnoughBytesInDictionary { got: usize, need: usize },
    OffsetTooBig { offset: usize, buf_len: usize },
}

#[cfg(feature = "std")]
impl std::error::Error for DecodeBufferError {}

impl core::fmt::Display for DecodeBufferError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DecodeBufferError::NotEnoughBytesInDictionary { got, need } => {
                write!(
                    f,
                    "Need {need} bytes from the dictionary but it is only {got} bytes long",
                )
            }
            DecodeBufferError::OffsetTooBig { offset, buf_len } => {
                write!(f, "offset: {offset} bigger than buffer: {buf_len}",)
            }
        }
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum DictionaryDecodeError {
    BadMagicNum { got: [u8; 4] },
    FSETableError(FSETableError),
    HuffmanTableError(HuffmanTableError),
}

#[cfg(feature = "std")]
impl std::error::Error for DictionaryDecodeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            DictionaryDecodeError::FSETableError(source) => Some(source),
            DictionaryDecodeError::HuffmanTableError(source) => Some(source),
            _ => None,
        }
    }
}

impl core::fmt::Display for DictionaryDecodeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DictionaryDecodeError::BadMagicNum { got } => {
                write!(
                    f,
                    "Bad magic_num at start of the dictionary; Got: {:#04X?}, Expected: {:#04x?}",
                    got,
                    crate::decoding::dictionary::MAGIC_NUM,
                )
            }
            DictionaryDecodeError::FSETableError(e) => write!(f, "{e:?}"),
            DictionaryDecodeError::HuffmanTableError(e) => write!(f, "{e:?}"),
        }
    }
}

impl From<FSETableError> for DictionaryDecodeError {
    fn from(val: FSETableError) -> Self {
        Self::FSETableError(val)
    }
}

impl From<HuffmanTableError> for DictionaryDecodeError {
    fn from(val: HuffmanTableError) -> Self {
        Self::HuffmanTableError(val)
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum FrameDecoderError {
    ReadFrameHeaderError(ReadFrameHeaderError),
    FrameHeaderError(FrameHeaderError),
    WindowSizeTooBig { requested: u64 },
    DictionaryDecodeError(DictionaryDecodeError),
    FailedToReadBlockHeader(BlockHeaderReadError),
    FailedToReadBlockBody(DecodeBlockContentError),
    FailedToReadChecksum(Error),
    NotYetInitialized,
    FailedToInitialize(FrameHeaderError),
    FailedToDrainDecodebuffer(Error),
    FailedToSkipFrame,
    TargetTooSmall,
    DictNotProvided { dict_id: u32 },
}

#[cfg(feature = "std")]
impl StdError for FrameDecoderError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            FrameDecoderError::ReadFrameHeaderError(source) => Some(source),
            FrameDecoderError::FrameHeaderError(source) => Some(source),
            FrameDecoderError::DictionaryDecodeError(source) => Some(source),
            FrameDecoderError::FailedToReadBlockHeader(source) => Some(source),
            FrameDecoderError::FailedToReadBlockBody(source) => Some(source),
            FrameDecoderError::FailedToReadChecksum(source) => Some(source),
            FrameDecoderError::FailedToInitialize(source) => Some(source),
            FrameDecoderError::FailedToDrainDecodebuffer(source) => Some(source),
            _ => None,
        }
    }
}

impl core::fmt::Display for FrameDecoderError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> ::core::fmt::Result {
        match self {
            FrameDecoderError::ReadFrameHeaderError(e) => {
                write!(f, "{e:?}")
            }
            FrameDecoderError::FrameHeaderError(e) => {
                write!(f, "{e:?}")
            }
            FrameDecoderError::WindowSizeTooBig { requested } => {
                write!(
                    f,
                    "Specified window_size is too big; Requested: {}, Max: {}",
                    requested,
                    crate::common::MAX_WINDOW_SIZE,
                )
            }
            FrameDecoderError::DictionaryDecodeError(e) => {
                write!(f, "{e:?}")
            }
            FrameDecoderError::FailedToReadBlockHeader(e) => {
                write!(f, "Failed to parse/decode block body: {e}")
            }
            FrameDecoderError::FailedToReadBlockBody(e) => {
                write!(f, "Failed to parse block header: {e}")
            }
            FrameDecoderError::FailedToReadChecksum(e) => {
                write!(f, "Failed to read checksum: {e}")
            }
            FrameDecoderError::NotYetInitialized => {
                write!(f, "Decoder must initialized or reset before using it",)
            }
            FrameDecoderError::FailedToInitialize(e) => {
                write!(f, "Decoder encountered error while initializing: {e}")
            }
            FrameDecoderError::FailedToDrainDecodebuffer(e) => {
                write!(
                    f,
                    "Decoder encountered error while draining the decodebuffer: {e}",
                )
            }
            FrameDecoderError::FailedToSkipFrame => {
                write!(
                    f,
                    "Failed to skip bytes for the length given in the frame header"
                )
            }
            FrameDecoderError::TargetTooSmall => {
                write!(f, "Target must have at least as many bytes as the contentsize of the frame reports")
            }
            FrameDecoderError::DictNotProvided { dict_id } => {
                write!(f, "Frame header specified dictionary id 0x{dict_id:X} that wasnt provided by add_dict() or reset_with_dict()")
            }
        }
    }
}

impl From<DictionaryDecodeError> for FrameDecoderError {
    fn from(val: DictionaryDecodeError) -> Self {
        Self::DictionaryDecodeError(val)
    }
}

impl From<BlockHeaderReadError> for FrameDecoderError {
    fn from(val: BlockHeaderReadError) -> Self {
        Self::FailedToReadBlockHeader(val)
    }
}

impl From<FrameHeaderError> for FrameDecoderError {
    fn from(val: FrameHeaderError) -> Self {
        Self::FrameHeaderError(val)
    }
}

impl From<ReadFrameHeaderError> for FrameDecoderError {
    fn from(val: ReadFrameHeaderError) -> Self {
        Self::ReadFrameHeaderError(val)
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum DecompressLiteralsError {
    MissingCompressedSize,
    MissingNumStreams,
    GetBitsError(GetBitsError),
    HuffmanTableError(HuffmanTableError),
    HuffmanDecoderError(HuffmanDecoderError),
    UninitializedHuffmanTable,
    MissingBytesForJumpHeader { got: usize },
    MissingBytesForLiterals { got: usize, needed: usize },
    ExtraPadding { skipped_bits: i32 },
    BitstreamReadMismatch { read_til: isize, expected: isize },
    DecodedLiteralCountMismatch { decoded: usize, expected: usize },
}

#[cfg(feature = "std")]
impl std::error::Error for DecompressLiteralsError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            DecompressLiteralsError::GetBitsError(source) => Some(source),
            DecompressLiteralsError::HuffmanTableError(source) => Some(source),
            DecompressLiteralsError::HuffmanDecoderError(source) => Some(source),
            _ => None,
        }
    }
}
impl core::fmt::Display for DecompressLiteralsError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DecompressLiteralsError::MissingCompressedSize => {
                write!(f,
                    "compressed size was none even though it must be set to something for compressed literals",
                )
            }
            DecompressLiteralsError::MissingNumStreams => {
                write!(f,
                    "num_streams was none even though it must be set to something (1 or 4) for compressed literals",
                )
            }
            DecompressLiteralsError::GetBitsError(e) => write!(f, "{e:?}"),
            DecompressLiteralsError::HuffmanTableError(e) => write!(f, "{e:?}"),
            DecompressLiteralsError::HuffmanDecoderError(e) => write!(f, "{e:?}"),
            DecompressLiteralsError::UninitializedHuffmanTable => {
                write!(
                    f,
                    "Tried to reuse huffman table but it was never initialized",
                )
            }
            DecompressLiteralsError::MissingBytesForJumpHeader { got } => {
                write!(f, "Need 6 bytes to decode jump header, got {got} bytes",)
            }
            DecompressLiteralsError::MissingBytesForLiterals { got, needed } => {
                write!(
                    f,
                    "Need at least {needed} bytes to decode literals. Have: {got} bytes",
                )
            }
            DecompressLiteralsError::ExtraPadding { skipped_bits } => {
                write!(f,
                    "Padding at the end of the sequence_section was more than a byte long: {skipped_bits} bits. Probably caused by data corruption",
                )
            }
            DecompressLiteralsError::BitstreamReadMismatch { read_til, expected } => {
                write!(
                    f,
                    "Bitstream was read till: {read_til}, should have been: {expected}",
                )
            }
            DecompressLiteralsError::DecodedLiteralCountMismatch { decoded, expected } => {
                write!(
                    f,
                    "Did not decode enough literals: {decoded}, Should have been: {expected}",
                )
            }
        }
    }
}

impl From<HuffmanDecoderError> for DecompressLiteralsError {
    fn from(val: HuffmanDecoderError) -> Self {
        Self::HuffmanDecoderError(val)
    }
}

impl From<GetBitsError> for DecompressLiteralsError {
    fn from(val: GetBitsError) -> Self {
        Self::GetBitsError(val)
    }
}

impl From<HuffmanTableError> for DecompressLiteralsError {
    fn from(val: HuffmanTableError) -> Self {
        Self::HuffmanTableError(val)
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum ExecuteSequencesError {
    DecodebufferError(DecodeBufferError),
    NotEnoughBytesForSequence { wanted: usize, have: usize },
    ZeroOffset,
}

impl core::fmt::Display for ExecuteSequencesError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ExecuteSequencesError::DecodebufferError(e) => {
                write!(f, "{e:?}")
            }
            ExecuteSequencesError::NotEnoughBytesForSequence { wanted, have } => {
                write!(
                    f,
                    "Sequence wants to copy up to byte {wanted}. Bytes in literalsbuffer: {have}"
                )
            }
            ExecuteSequencesError::ZeroOffset => {
                write!(f, "Illegal offset: 0 found")
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ExecuteSequencesError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            ExecuteSequencesError::DecodebufferError(source) => Some(source),
            _ => None,
        }
    }
}

impl From<DecodeBufferError> for ExecuteSequencesError {
    fn from(val: DecodeBufferError) -> Self {
        Self::DecodebufferError(val)
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum DecodeSequenceError {
    GetBitsError(GetBitsError),
    FSEDecoderError(FSEDecoderError),
    FSETableError(FSETableError),
    ExtraPadding { skipped_bits: i32 },
    UnsupportedOffset { offset_code: u8 },
    ZeroOffset,
    NotEnoughBytesForNumSequences,
    ExtraBits { bits_remaining: isize },
    MissingCompressionMode,
    MissingByteForRleLlTable,
    MissingByteForRleOfTable,
    MissingByteForRleMlTable,
}

#[cfg(feature = "std")]
impl std::error::Error for DecodeSequenceError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            DecodeSequenceError::GetBitsError(source) => Some(source),
            DecodeSequenceError::FSEDecoderError(source) => Some(source),
            DecodeSequenceError::FSETableError(source) => Some(source),
            _ => None,
        }
    }
}

impl core::fmt::Display for DecodeSequenceError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DecodeSequenceError::GetBitsError(e) => write!(f, "{e:?}"),
            DecodeSequenceError::FSEDecoderError(e) => write!(f, "{e:?}"),
            DecodeSequenceError::FSETableError(e) => write!(f, "{e:?}"),
            DecodeSequenceError::ExtraPadding { skipped_bits } => {
                write!(f,
                    "Padding at the end of the sequence_section was more than a byte long: {skipped_bits} bits. Probably caused by data corruption",
                )
            }
            DecodeSequenceError::UnsupportedOffset { offset_code } => {
                write!(
                    f,
                    "Do not support offsets bigger than 1<<32; got: {offset_code}",
                )
            }
            DecodeSequenceError::ZeroOffset => write!(
                f,
                "Read an offset == 0. That is an illegal value for offsets"
            ),
            DecodeSequenceError::NotEnoughBytesForNumSequences => write!(
                f,
                "Bytestream did not contain enough bytes to decode num_sequences"
            ),
            DecodeSequenceError::ExtraBits { bits_remaining } => write!(f, "{bits_remaining}"),
            DecodeSequenceError::MissingCompressionMode => write!(
                f,
                "compression modes are none but they must be set to something"
            ),
            DecodeSequenceError::MissingByteForRleLlTable => {
                write!(f, "Need a byte to read for RLE ll table")
            }
            DecodeSequenceError::MissingByteForRleOfTable => {
                write!(f, "Need a byte to read for RLE of table")
            }
            DecodeSequenceError::MissingByteForRleMlTable => {
                write!(f, "Need a byte to read for RLE ml table")
            }
        }
    }
}

impl From<GetBitsError> for DecodeSequenceError {
    fn from(val: GetBitsError) -> Self {
        Self::GetBitsError(val)
    }
}

impl From<FSETableError> for DecodeSequenceError {
    fn from(val: FSETableError) -> Self {
        Self::FSETableError(val)
    }
}

impl From<FSEDecoderError> for DecodeSequenceError {
    fn from(val: FSEDecoderError) -> Self {
        Self::FSEDecoderError(val)
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum LiteralsSectionParseError {
    IllegalLiteralSectionType { got: u8 },
    GetBitsError(GetBitsError),
    NotEnoughBytes { have: usize, need: u8 },
}

#[cfg(feature = "std")]
impl std::error::Error for LiteralsSectionParseError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            LiteralsSectionParseError::GetBitsError(source) => Some(source),
            _ => None,
        }
    }
}
impl core::fmt::Display for LiteralsSectionParseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            LiteralsSectionParseError::IllegalLiteralSectionType { got } => {
                write!(
                    f,
                    "Illegal literalssectiontype. Is: {got}, must be in: 0, 1, 2, 3"
                )
            }
            LiteralsSectionParseError::GetBitsError(e) => write!(f, "{e:?}"),
            LiteralsSectionParseError::NotEnoughBytes { have, need } => {
                write!(
                    f,
                    "Not enough byte to parse the literals section header. Have: {have}, Need: {need}",
                )
            }
        }
    }
}

impl From<GetBitsError> for LiteralsSectionParseError {
    fn from(val: GetBitsError) -> Self {
        Self::GetBitsError(val)
    }
}

impl core::fmt::Display for LiteralsSectionType {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        match self {
            LiteralsSectionType::Compressed => write!(f, "Compressed"),
            LiteralsSectionType::Raw => write!(f, "Raw"),
            LiteralsSectionType::RLE => write!(f, "RLE"),
            LiteralsSectionType::Treeless => write!(f, "Treeless"),
        }
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum SequencesHeaderParseError {
    NotEnoughBytes { need_at_least: u8, got: usize },
}

#[cfg(feature = "std")]
impl std::error::Error for SequencesHeaderParseError {}

impl core::fmt::Display for SequencesHeaderParseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SequencesHeaderParseError::NotEnoughBytes { need_at_least, got } => {
                write!(
                    f,
                    "source must have at least {need_at_least} bytes to parse header; got {got} bytes",
                )
            }
        }
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum FSETableError {
    AccLogIsZero,
    AccLogTooBig {
        got: u8,
        max: u8,
    },
    GetBitsError(GetBitsError),
    ProbabilityCounterMismatch {
        got: u32,
        expected_sum: u32,
        symbol_probabilities: Vec<i32>,
    },
    TooManySymbols {
        got: usize,
    },
}

#[cfg(feature = "std")]
impl std::error::Error for FSETableError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            FSETableError::GetBitsError(source) => Some(source),
            _ => None,
        }
    }
}

impl core::fmt::Display for FSETableError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            FSETableError::AccLogIsZero => write!(f, "Acclog must be at least 1"),
            FSETableError::AccLogTooBig { got, max } => {
                write!(
                    f,
                    "Found FSE acc_log: {got} bigger than allowed maximum in this case: {max}"
                )
            }
            FSETableError::GetBitsError(e) => write!(f, "{e:?}"),
            FSETableError::ProbabilityCounterMismatch {
                got,
                expected_sum,
                symbol_probabilities,
            } => {
                write!(f,
                    "The counter ({got}) exceeded the expected sum: {expected_sum}. This means an error or corrupted data \n {symbol_probabilities:?}",
                )
            }
            FSETableError::TooManySymbols { got } => {
                write!(
                    f,
                    "There are too many symbols in this distribution: {got}. Max: 256",
                )
            }
        }
    }
}

impl From<GetBitsError> for FSETableError {
    fn from(val: GetBitsError) -> Self {
        Self::GetBitsError(val)
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum FSEDecoderError {
    GetBitsError(GetBitsError),
    TableIsUninitialized,
}

#[cfg(feature = "std")]
impl std::error::Error for FSEDecoderError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            FSEDecoderError::GetBitsError(source) => Some(source),
            _ => None,
        }
    }
}

impl core::fmt::Display for FSEDecoderError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            FSEDecoderError::GetBitsError(e) => write!(f, "{e:?}"),
            FSEDecoderError::TableIsUninitialized => {
                write!(f, "Tried to use an uninitialized table!")
            }
        }
    }
}

impl From<GetBitsError> for FSEDecoderError {
    fn from(val: GetBitsError) -> Self {
        Self::GetBitsError(val)
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum HuffmanTableError {
    GetBitsError(GetBitsError),
    FSEDecoderError(FSEDecoderError),
    FSETableError(FSETableError),
    SourceIsEmpty,
    NotEnoughBytesForWeights {
        got_bytes: usize,
        expected_bytes: u8,
    },
    ExtraPadding {
        skipped_bits: i32,
    },
    TooManyWeights {
        got: usize,
    },
    MissingWeights,
    LeftoverIsNotAPowerOf2 {
        got: u32,
    },
    NotEnoughBytesToDecompressWeights {
        have: usize,
        need: usize,
    },
    FSETableUsedTooManyBytes {
        used: usize,
        available_bytes: u8,
    },
    NotEnoughBytesInSource {
        got: usize,
        need: usize,
    },
    WeightBiggerThanMaxNumBits {
        got: u8,
    },
    MaxBitsTooHigh {
        got: u8,
    },
}

#[cfg(feature = "std")]
impl StdError for HuffmanTableError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            HuffmanTableError::GetBitsError(source) => Some(source),
            HuffmanTableError::FSEDecoderError(source) => Some(source),
            HuffmanTableError::FSETableError(source) => Some(source),
            _ => None,
        }
    }
}

impl core::fmt::Display for HuffmanTableError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> ::core::fmt::Result {
        match self {
            HuffmanTableError::GetBitsError(e) => write!(f, "{e:?}"),
            HuffmanTableError::FSEDecoderError(e) => write!(f, "{e:?}"),
            HuffmanTableError::FSETableError(e) => write!(f, "{e:?}"),
            HuffmanTableError::SourceIsEmpty => write!(f, "Source needs to have at least one byte"),
            HuffmanTableError::NotEnoughBytesForWeights {
                got_bytes,
                expected_bytes,
            } => {
                write!(f, "Header says there should be {expected_bytes} bytes for the weights but there are only {got_bytes} bytes in the stream")
            }
            HuffmanTableError::ExtraPadding { skipped_bits } => {
                write!(f,
                    "Padding at the end of the sequence_section was more than a byte long: {skipped_bits} bits. Probably caused by data corruption",
                )
            }
            HuffmanTableError::TooManyWeights { got } => {
                write!(
                    f,
                    "More than 255 weights decoded (got {got} weights). Stream is probably corrupted",
                )
            }
            HuffmanTableError::MissingWeights => {
                write!(f, "Can\'t build huffman table without any weights")
            }
            HuffmanTableError::LeftoverIsNotAPowerOf2 { got } => {
                write!(f, "Leftover must be power of two but is: {got}")
            }
            HuffmanTableError::NotEnoughBytesToDecompressWeights { have, need } => {
                write!(
                    f,
                    "Not enough bytes in stream to decompress weights. Is: {have}, Should be: {need}",
                )
            }
            HuffmanTableError::FSETableUsedTooManyBytes {
                used,
                available_bytes,
            } => {
                write!(f,
                    "FSE table used more bytes: {used} than were meant to be used for the whole stream of huffman weights ({available_bytes})",
                )
            }
            HuffmanTableError::NotEnoughBytesInSource { got, need } => {
                write!(f, "Source needs to have at least {need} bytes, got: {got}",)
            }
            HuffmanTableError::WeightBiggerThanMaxNumBits { got } => {
                write!(
                    f,
                    "Cant have weight: {} bigger than max_num_bits: {}",
                    got,
                    crate::huff0::MAX_MAX_NUM_BITS,
                )
            }
            HuffmanTableError::MaxBitsTooHigh { got } => {
                write!(
                    f,
                    "max_bits derived from weights is: {} should be lower than: {}",
                    got,
                    crate::huff0::MAX_MAX_NUM_BITS,
                )
            }
        }
    }
}

impl From<GetBitsError> for HuffmanTableError {
    fn from(val: GetBitsError) -> Self {
        Self::GetBitsError(val)
    }
}

impl From<FSEDecoderError> for HuffmanTableError {
    fn from(val: FSEDecoderError) -> Self {
        Self::FSEDecoderError(val)
    }
}

impl From<FSETableError> for HuffmanTableError {
    fn from(val: FSETableError) -> Self {
        Self::FSETableError(val)
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum HuffmanDecoderError {
    GetBitsError(GetBitsError),
}

impl core::fmt::Display for HuffmanDecoderError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            HuffmanDecoderError::GetBitsError(e) => write!(f, "{e:?}"),
        }
    }
}

#[cfg(feature = "std")]
impl StdError for HuffmanDecoderError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            HuffmanDecoderError::GetBitsError(source) => Some(source),
        }
    }
}

impl From<GetBitsError> for HuffmanDecoderError {
    fn from(val: GetBitsError) -> Self {
        Self::GetBitsError(val)
    }
}
