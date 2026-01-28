//! Values and interfaces shared between the encoding side
//! and the decoding side.

// --- FRAMES ---
/// This magic number is included at the start of a single Zstandard frame
pub const MAGIC_NUM: u32 = 0xFD2F_B528;
/// Window size refers to the minimum amount of memory needed to decode any given frame.
///
/// The minimum window size is defined as 1 KB
pub const MIN_WINDOW_SIZE: u64 = 1024;
/// Window size refers to the minimum amount of memory needed to decode any given frame.
///
/// The maximum window size allowed by the spec is 3.75TB
pub const MAX_WINDOW_SIZE: u64 = (1 << 41) + 7 * (1 << 38);

// --- BLOCKS ---
/// While the spec limits block size to 128KB, the implementation uses
/// 128kibibytes
///
/// <https://github.com/facebook/zstd/blob/eca205fc7849a61ab287492931a04960ac58e031/doc/educational_decoder/zstd_decompress.c#L28-L29>
pub const MAX_BLOCK_SIZE: u32 = 128 * 1024;
