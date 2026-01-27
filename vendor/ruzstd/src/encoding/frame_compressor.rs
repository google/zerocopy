//! Utilities and interfaces for encoding an entire frame. Allows reusing resources

use alloc::vec::Vec;
use core::convert::TryInto;
#[cfg(feature = "hash")]
use twox_hash::XxHash64;

#[cfg(feature = "hash")]
use core::hash::Hasher;

use super::{
    block_header::BlockHeader, frame_header::FrameHeader, levels::*,
    match_generator::MatchGeneratorDriver, CompressionLevel, Matcher,
};
use crate::fse::fse_encoder::{default_ll_table, default_ml_table, default_of_table, FSETable};

use crate::io::{Read, Write};

/// An interface for compressing arbitrary data with the ZStandard compression algorithm.
///
/// `FrameCompressor` will generally be used by:
/// 1. Initializing a compressor by providing a buffer of data using `FrameCompressor::new()`
/// 2. Starting compression and writing that compression into a vec using `FrameCompressor::begin`
///
/// # Examples
/// ```
/// use ruzstd::encoding::{FrameCompressor, CompressionLevel};
/// let mock_data: &[_] = &[0x1, 0x2, 0x3, 0x4];
/// let mut output = std::vec::Vec::new();
/// // Initialize a compressor.
/// let mut compressor = FrameCompressor::new(CompressionLevel::Uncompressed);
/// compressor.set_source(mock_data);
/// compressor.set_drain(&mut output);
///
/// // `compress` writes the compressed output into the provided buffer.
/// compressor.compress();
/// ```
pub struct FrameCompressor<R: Read, W: Write, M: Matcher> {
    uncompressed_data: Option<R>,
    compressed_data: Option<W>,
    compression_level: CompressionLevel,
    state: CompressState<M>,
    #[cfg(feature = "hash")]
    hasher: XxHash64,
}

pub(crate) struct FseTables {
    pub(crate) ll_default: FSETable,
    pub(crate) ll_previous: Option<FSETable>,
    pub(crate) ml_default: FSETable,
    pub(crate) ml_previous: Option<FSETable>,
    pub(crate) of_default: FSETable,
    pub(crate) of_previous: Option<FSETable>,
}

impl FseTables {
    pub fn new() -> Self {
        Self {
            ll_default: default_ll_table(),
            ll_previous: None,
            ml_default: default_ml_table(),
            ml_previous: None,
            of_default: default_of_table(),
            of_previous: None,
        }
    }
}

pub(crate) struct CompressState<M: Matcher> {
    pub(crate) matcher: M,
    pub(crate) last_huff_table: Option<crate::huff0::huff0_encoder::HuffmanTable>,
    pub(crate) fse_tables: FseTables,
}

impl<R: Read, W: Write> FrameCompressor<R, W, MatchGeneratorDriver> {
    /// Create a new `FrameCompressor`
    pub fn new(compression_level: CompressionLevel) -> Self {
        Self {
            uncompressed_data: None,
            compressed_data: None,
            compression_level,
            state: CompressState {
                matcher: MatchGeneratorDriver::new(1024 * 128, 1),
                last_huff_table: None,
                fse_tables: FseTables::new(),
            },
            #[cfg(feature = "hash")]
            hasher: XxHash64::with_seed(0),
        }
    }
}

impl<R: Read, W: Write, M: Matcher> FrameCompressor<R, W, M> {
    /// Create a new `FrameCompressor` with a custom matching algorithm implementation
    pub fn new_with_matcher(matcher: M, compression_level: CompressionLevel) -> Self {
        Self {
            uncompressed_data: None,
            compressed_data: None,
            state: CompressState {
                matcher,
                last_huff_table: None,
                fse_tables: FseTables::new(),
            },
            compression_level,
            #[cfg(feature = "hash")]
            hasher: XxHash64::with_seed(0),
        }
    }

    /// Before calling [FrameCompressor::compress] you need to set the source.
    ///
    /// This is the data that is compressed and written into the drain.
    pub fn set_source(&mut self, uncompressed_data: R) -> Option<R> {
        self.uncompressed_data.replace(uncompressed_data)
    }

    /// Before calling [FrameCompressor::compress] you need to set the drain.
    ///
    /// As the compressor compresses data, the drain serves as a place for the output to be writte.
    pub fn set_drain(&mut self, compressed_data: W) -> Option<W> {
        self.compressed_data.replace(compressed_data)
    }

    /// Compress the uncompressed data from the provided source as one Zstd frame and write it to the provided drain
    ///
    /// This will repeatedly call [Read::read] on the source to fill up blocks until the source returns 0 on the read call.
    /// Also [Write::write_all] will be called on the drain after each block has been encoded.
    ///
    /// To avoid endlessly encoding from a potentially endless source (like a network socket) you can use the
    /// [Read::take] function
    pub fn compress(&mut self) {
        // Clearing buffers to allow re-using of the compressor
        self.state.matcher.reset(self.compression_level);
        self.state.last_huff_table = None;
        let source = self.uncompressed_data.as_mut().unwrap();
        let drain = self.compressed_data.as_mut().unwrap();
        // As the frame is compressed, it's stored here
        let output: &mut Vec<u8> = &mut Vec::with_capacity(1024 * 130);
        // First write the frame header
        let header = FrameHeader {
            frame_content_size: None,
            single_segment: false,
            content_checksum: cfg!(feature = "hash"),
            dictionary_id: None,
            window_size: Some(self.state.matcher.window_size()),
        };
        header.serialize(output);
        // Now compress block by block
        loop {
            // Read a single block's worth of uncompressed data from the input
            let mut uncompressed_data = self.state.matcher.get_next_space();
            let mut read_bytes = 0;
            let last_block;
            'read_loop: loop {
                let new_bytes = source.read(&mut uncompressed_data[read_bytes..]).unwrap();
                if new_bytes == 0 {
                    last_block = true;
                    break 'read_loop;
                }
                read_bytes += new_bytes;
                if read_bytes == uncompressed_data.len() {
                    last_block = false;
                    break 'read_loop;
                }
            }
            uncompressed_data.resize(read_bytes, 0);
            // As we read, hash that data too
            #[cfg(feature = "hash")]
            self.hasher.write(&uncompressed_data);
            // Special handling is needed for compression of a totally empty file (why you'd want to do that, I don't know)
            if uncompressed_data.is_empty() {
                let header = BlockHeader {
                    last_block: true,
                    block_type: crate::blocks::block::BlockType::Raw,
                    block_size: 0,
                };
                // Write the header, then the block
                header.serialize(output);
                drain.write_all(output).unwrap();
                output.clear();
                break;
            }

            match self.compression_level {
                CompressionLevel::Uncompressed => {
                    let header = BlockHeader {
                        last_block,
                        block_type: crate::blocks::block::BlockType::Raw,
                        block_size: read_bytes.try_into().unwrap(),
                    };
                    // Write the header, then the block
                    header.serialize(output);
                    output.extend_from_slice(&uncompressed_data);
                }
                CompressionLevel::Fastest => {
                    compress_fastest(&mut self.state, last_block, uncompressed_data, output)
                }
                _ => {
                    unimplemented!();
                }
            }
            drain.write_all(output).unwrap();
            output.clear();
            if last_block {
                break;
            }
        }

        // If the `hash` feature is enabled, then `content_checksum` is set to true in the header
        // and a 32 bit hash is written at the end of the data.
        #[cfg(feature = "hash")]
        {
            // Because we only have the data as a reader, we need to read all of it to calculate the checksum
            // Possible TODO: create a wrapper around self.uncompressed data that hashes the data as it's read?
            let content_checksum = self.hasher.finish();
            drain
                .write_all(&(content_checksum as u32).to_le_bytes())
                .unwrap();
        }
    }

    /// Get a mutable reference to the source
    pub fn source_mut(&mut self) -> Option<&mut R> {
        self.uncompressed_data.as_mut()
    }

    /// Get a mutable reference to the drain
    pub fn drain_mut(&mut self) -> Option<&mut W> {
        self.compressed_data.as_mut()
    }

    /// Get a reference to the source
    pub fn source(&self) -> Option<&R> {
        self.uncompressed_data.as_ref()
    }

    /// Get a reference to the drain
    pub fn drain(&self) -> Option<&W> {
        self.compressed_data.as_ref()
    }

    /// Retrieve the source
    pub fn take_source(&mut self) -> Option<R> {
        self.uncompressed_data.take()
    }

    /// Retrieve the drain
    pub fn take_drain(&mut self) -> Option<W> {
        self.compressed_data.take()
    }

    /// Before calling [FrameCompressor::compress] you can replace the matcher
    pub fn replace_matcher(&mut self, mut match_generator: M) -> M {
        core::mem::swap(&mut match_generator, &mut self.state.matcher);
        match_generator
    }

    /// Before calling [FrameCompressor::compress] you can replace the compression level
    pub fn set_compression_level(
        &mut self,
        compression_level: CompressionLevel,
    ) -> CompressionLevel {
        let old = self.compression_level;
        self.compression_level = compression_level;
        old
    }

    /// Get the current compression level
    pub fn compression_level(&self) -> CompressionLevel {
        self.compression_level
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use super::FrameCompressor;
    use crate::common::MAGIC_NUM;
    use crate::decoding::FrameDecoder;
    use alloc::vec::Vec;

    #[test]
    fn frame_starts_with_magic_num() {
        let mock_data = [1_u8, 2, 3].as_slice();
        let mut output: Vec<u8> = Vec::new();
        let mut compressor = FrameCompressor::new(super::CompressionLevel::Uncompressed);
        compressor.set_source(mock_data);
        compressor.set_drain(&mut output);

        compressor.compress();
        assert!(output.starts_with(&MAGIC_NUM.to_le_bytes()));
    }

    #[test]
    fn very_simple_raw_compress() {
        let mock_data = [1_u8, 2, 3].as_slice();
        let mut output: Vec<u8> = Vec::new();
        let mut compressor = FrameCompressor::new(super::CompressionLevel::Uncompressed);
        compressor.set_source(mock_data);
        compressor.set_drain(&mut output);

        compressor.compress();
    }

    #[test]
    fn very_simple_compress() {
        let mut mock_data = vec![0; 1 << 17];
        mock_data.extend(vec![1; (1 << 17) - 1]);
        mock_data.extend(vec![2; (1 << 18) - 1]);
        mock_data.extend(vec![2; 1 << 17]);
        mock_data.extend(vec![3; (1 << 17) - 1]);
        let mut output: Vec<u8> = Vec::new();
        let mut compressor = FrameCompressor::new(super::CompressionLevel::Uncompressed);
        compressor.set_source(mock_data.as_slice());
        compressor.set_drain(&mut output);

        compressor.compress();

        let mut decoder = FrameDecoder::new();
        let mut decoded = Vec::with_capacity(mock_data.len());
        decoder.decode_all_to_vec(&output, &mut decoded).unwrap();
        assert_eq!(mock_data, decoded);

        let mut decoded = Vec::new();
        zstd::stream::copy_decode(output.as_slice(), &mut decoded).unwrap();
        assert_eq!(mock_data, decoded);
    }

    #[test]
    fn rle_compress() {
        let mock_data = vec![0; 1 << 19];
        let mut output: Vec<u8> = Vec::new();
        let mut compressor = FrameCompressor::new(super::CompressionLevel::Uncompressed);
        compressor.set_source(mock_data.as_slice());
        compressor.set_drain(&mut output);

        compressor.compress();

        let mut decoder = FrameDecoder::new();
        let mut decoded = Vec::with_capacity(mock_data.len());
        decoder.decode_all_to_vec(&output, &mut decoded).unwrap();
        assert_eq!(mock_data, decoded);
    }

    #[test]
    fn aaa_compress() {
        let mock_data = vec![0, 1, 3, 4, 5];
        let mut output: Vec<u8> = Vec::new();
        let mut compressor = FrameCompressor::new(super::CompressionLevel::Uncompressed);
        compressor.set_source(mock_data.as_slice());
        compressor.set_drain(&mut output);

        compressor.compress();

        let mut decoder = FrameDecoder::new();
        let mut decoded = Vec::with_capacity(mock_data.len());
        decoder.decode_all_to_vec(&output, &mut decoded).unwrap();
        assert_eq!(mock_data, decoded);

        let mut decoded = Vec::new();
        zstd::stream::copy_decode(output.as_slice(), &mut decoded).unwrap();
        assert_eq!(mock_data, decoded);
    }

    #[cfg(feature = "std")]
    #[test]
    fn fuzz_targets() {
        use std::io::Read;
        fn decode_ruzstd(data: &mut dyn std::io::Read) -> Vec<u8> {
            let mut decoder = crate::decoding::StreamingDecoder::new(data).unwrap();
            let mut result: Vec<u8> = Vec::new();
            decoder.read_to_end(&mut result).expect("Decoding failed");
            result
        }

        fn decode_ruzstd_writer(mut data: impl Read) -> Vec<u8> {
            let mut decoder = crate::decoding::FrameDecoder::new();
            decoder.reset(&mut data).unwrap();
            let mut result = vec![];
            while !decoder.is_finished() || decoder.can_collect() > 0 {
                decoder
                    .decode_blocks(
                        &mut data,
                        crate::decoding::BlockDecodingStrategy::UptoBytes(1024 * 1024),
                    )
                    .unwrap();
                decoder.collect_to_writer(&mut result).unwrap();
            }
            result
        }

        fn encode_zstd(data: &[u8]) -> Result<Vec<u8>, std::io::Error> {
            zstd::stream::encode_all(std::io::Cursor::new(data), 3)
        }

        fn encode_ruzstd_uncompressed(data: &mut dyn std::io::Read) -> Vec<u8> {
            let mut input = Vec::new();
            data.read_to_end(&mut input).unwrap();

            crate::encoding::compress_to_vec(
                input.as_slice(),
                crate::encoding::CompressionLevel::Uncompressed,
            )
        }

        fn encode_ruzstd_compressed(data: &mut dyn std::io::Read) -> Vec<u8> {
            let mut input = Vec::new();
            data.read_to_end(&mut input).unwrap();

            crate::encoding::compress_to_vec(
                input.as_slice(),
                crate::encoding::CompressionLevel::Fastest,
            )
        }

        fn decode_zstd(data: &[u8]) -> Result<Vec<u8>, std::io::Error> {
            let mut output = Vec::new();
            zstd::stream::copy_decode(data, &mut output)?;
            Ok(output)
        }
        if std::fs::exists("fuzz/artifacts/interop").unwrap_or(false) {
            for file in std::fs::read_dir("fuzz/artifacts/interop").unwrap() {
                if file.as_ref().unwrap().file_type().unwrap().is_file() {
                    let data = std::fs::read(file.unwrap().path()).unwrap();
                    let data = data.as_slice();
                    // Decoding
                    let compressed = encode_zstd(data).unwrap();
                    let decoded = decode_ruzstd(&mut compressed.as_slice());
                    let decoded2 = decode_ruzstd_writer(&mut compressed.as_slice());
                    assert!(
                        decoded == data,
                        "Decoded data did not match the original input during decompression"
                    );
                    assert_eq!(
                        decoded2, data,
                        "Decoded data did not match the original input during decompression"
                    );

                    // Encoding
                    // Uncompressed encoding
                    let mut input = data;
                    let compressed = encode_ruzstd_uncompressed(&mut input);
                    let decoded = decode_zstd(&compressed).unwrap();
                    assert_eq!(
                        decoded, data,
                        "Decoded data did not match the original input during compression"
                    );
                    // Compressed encoding
                    let mut input = data;
                    let compressed = encode_ruzstd_compressed(&mut input);
                    let decoded = decode_zstd(&compressed).unwrap();
                    assert_eq!(
                        decoded, data,
                        "Decoded data did not match the original input during compression"
                    );
                }
            }
        }
    }
}
