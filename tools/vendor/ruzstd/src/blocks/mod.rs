//! In a Zstandard frame, there's a frame header, followed by one or more *blocks*.
//!
//! A block contains data, and a header describing how that data is encoded, as well
//! as other misc metadata.
//!
//! <https://github.com/facebook/zstd/blob/dev/doc/zstd_compression_format.md#blocks>

pub mod block;
pub mod literals_section;
pub mod sequence_section;
