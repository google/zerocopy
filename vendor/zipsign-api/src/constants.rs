// "\x0c\x04\x01" -- form feed, end of text, start of header
// "ed25519ph" -- used algorithm
// "\x00\x00" -- version number in network byte order
/// Bytes preceding signatures
pub(crate) const MAGIC_HEADER: &[u8; 14] = b"\x0c\x04\x01ed25519ph\x00\x00";

/// Total number of bytes in a [`MAGIC_HEADER`] + [`SignatureCountLeInt`]
pub(crate) const HEADER_SIZE: usize = 16;

/// Integer type to tell the number of signatures in a signed file, stored in little endian
pub(crate) type SignatureCountLeInt = u16;

/// Prefix of the signature block in a signed .tar.gz file
///
/// Followed by base64 encoded signatures string, the current stream position before this block
/// encoded as zero-padded 16 bytes hexadecimal string, and [`GZIP_END`]
/// [`GZIP_END`]
#[cfg(any(feature = "sign-tar", feature = "unsign-tar", feature = "verify-tar"))]
pub(crate) const GZIP_START: &[u8; 10] = {
    const EPOCH: u32 = 978_307_200; // 2001-01-01 00:00:00 Z

    let [m1, m2, m3, m4] = EPOCH.to_le_bytes();
    &[
        0x1f, 0x8b, // gzip: magic number
        0x08, // gzip: compression method (deflate)
        0x10, // gzip: flags (binary, no checksum, no extra fields, no name, has comment)
        m1, m2, m3, m4,   // gzip: modification time
        0x00, // gzip: extra flags (unset)
        0xff, // gzip: Operating system ID: unknown
    ]
};

/// Suffix of the signature block in a signed .tar.gz file
#[cfg(any(feature = "sign-tar", feature = "unsign-tar", feature = "verify-tar"))]
pub(crate) const GZIP_END: &[u8; 14] = &[
    0x00, // deflate: NUL terminator, end of comments
    0x01, // deflate: block header (final block, uncompressed)
    0x00, 0x00, // deflate: length
    0xff, 0xff, // deflate: negated length
    0, 0, 0, 0, // gzip: crc32 of uncompressed data
    0, 0, 0, 0, // gzip: total uncompressed size
];

/// Total overhead the signature block in a signed .tar.gz file excluding signature data
#[cfg(feature = "sign-tar")]
pub(crate) const GZIP_EXTRA: usize = GZIP_START.len() + GZIP_END.len() + u64::BITS as usize / 4;

/// Maximum number of bytes the encoded signatures may have
///
/// This number equates to 1022 signatures in a `.zip` file, and 767 signatures in `.tar.gz` file.
pub(crate) const BUF_LIMIT: usize = 1 << 16;
