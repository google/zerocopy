//! Structures and utilities used for decoding zstd formatted data

pub mod errors;
mod frame_decoder;
mod streaming_decoder;

pub use frame_decoder::{BlockDecodingStrategy, FrameDecoder};
pub use streaming_decoder::StreamingDecoder;

pub(crate) mod block_decoder;
pub(crate) mod decode_buffer;
pub(crate) mod dictionary;
pub(crate) mod frame;
pub(crate) mod literals_section_decoder;
mod ringbuffer;
#[allow(dead_code)]
pub(crate) mod scratch;
pub(crate) mod sequence_execution;
pub(crate) mod sequence_section_decoder;
