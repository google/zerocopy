// Copyright 2026 The Fuchsia Authors
// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT

//! Borrowed wire headers for Tyr's Mali CSF firmware format.

use core::ops::Range;

use zerocopy::{
    byteorder::{LittleEndian, U16, U32},
    FromBytes, Immutable, IntoBytes, KnownLayout, Project, Unaligned,
};

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    Truncated,
    Magic,
    Version,
    Reserved,
    HeaderBounds,
    Range,
    Alignment,
}

/// The exact 20-byte header read by Tyr's FirmwareHeader::new.
#[derive(FromBytes, IntoBytes, Immutable, KnownLayout, Unaligned, Project)]
#[repr(C)]
pub struct WireHeader {
    magic: U32<LittleEndian>,
    minor: u8,
    major: u8,
    padding1: U16<LittleEndian>,
    version_hash: U32<LittleEndian>,
    padding2: U32<LittleEndian>,
    size: U32<LittleEndian>,
}

pub struct Header<'a>(&'a WireHeader);

impl<'a> Header<'a> {
    /// Parses an immutable kernel-owned snapshot, not concurrently changing I/O.
    pub fn parse(image: &'a [u8]) -> Result<(Self, &'a [u8]), Error> {
        let (wire, rest) = WireHeader::ref_from_prefix(image).map_err(|_| Error::Truncated)?;
        let magic = zerocopy::Ptr::from_ref(wire)
            .project::<zerocopy::project_clients::ProjectDerive, _, { zerocopy::STRUCT_VARIANT_ID }, { zerocopy::ident_id!(magic) }>()
            .unwrap()
            .read::<zerocopy::BecauseImmutable>()
            .get();
        if magic != 0xc3f13a6e {
            return Err(Error::Magic);
        }
        if wire.major != 0 {
            return Err(Error::Version);
        }
        if wire.padding1.get() != 0 || wire.padding2.get() != 0 {
            return Err(Error::Reserved);
        }
        let header_end = wire.size.get() as usize;
        if header_end < core::mem::size_of::<WireHeader>() || header_end > image.len() {
            return Err(Error::HeaderBounds);
        }
        Ok((Self(wire), rest))
    }

    pub fn version(&self) -> (u8, u8) {
        (self.0.major, self.0.minor)
    }

    pub fn version_hash(&self) -> u32 {
        self.0.version_hash.get()
    }

    pub fn header_end(&self) -> usize {
        self.0.size.get() as usize
    }
}

#[derive(FromBytes, IntoBytes, Immutable, KnownLayout, Unaligned)]
#[repr(C)]
struct WireSection {
    flags: U32<LittleEndian>,
    va_start: U32<LittleEndian>,
    va_end: U32<LittleEndian>,
    data_start: U32<LittleEndian>,
    data_end: U32<LittleEndian>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Section {
    pub flags: u32,
    pub va: Range<u32>,
    pub data: Range<u32>,
}

/// Decodes the section header and retains Tyr's range and page checks.
/// The caller still interprets flags, including protected/cache/shared modes.
pub fn section(bytes: &[u8], firmware_len: usize) -> Result<(Section, &[u8]), Error> {
    let (wire, rest) = WireSection::ref_from_prefix(bytes).map_err(|_| Error::Truncated)?;
    let va = wire.va_start.get()..wire.va_end.get();
    let data = wire.data_start.get()..wire.data_end.get();
    if va.end < va.start || data.end < data.start || data.end as usize > firmware_len {
        return Err(Error::Range);
    }
    if va.start % 4096 != 0 || va.end % 4096 != 0 {
        return Err(Error::Alignment);
    }
    Ok((Section { flags: wire.flags.get(), va, data }, rest))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn image() -> [u8; 24] {
        let mut bytes = [0; 24];
        bytes[..4].copy_from_slice(&0xc3f13a6e_u32.to_le_bytes());
        bytes[4] = 7;
        bytes[8..12].copy_from_slice(&0x12345678_u32.to_le_bytes());
        bytes[16..20].copy_from_slice(&24_u32.to_le_bytes());
        bytes
    }

    #[test]
    fn decodes_unaligned_little_endian_header_without_copy() {
        let mut storage = [0xff; 25];
        storage[1..].copy_from_slice(&image());
        let source = &storage[1..];
        let (header, rest) = Header::parse(source).unwrap();
        assert_eq!(header.version(), (0, 7));
        assert_eq!(header.version_hash(), 0x12345678);
        assert_eq!(header.header_end(), 24);
        assert_eq!(rest, &source[20..]);
        assert_eq!(core::ptr::from_ref(header.0).cast::<u8>(), source.as_ptr());
    }

    #[test]
    fn rejects_truncation_reserved_bytes_and_bad_versions() {
        let bytes = image();
        for len in 0..20 {
            assert!(matches!(Header::parse(&bytes[..len]), Err(Error::Truncated)));
        }
        for (offset, error) in
            [(0, Error::Magic), (5, Error::Version), (6, Error::Reserved), (12, Error::Reserved)]
        {
            let mut bad = image();
            bad[offset] ^= 1;
            assert_eq!(Header::parse(&bad).err(), Some(error));
        }
        for size in [0_u32, 19, 25, u32::MAX] {
            let mut bad = image();
            bad[16..20].copy_from_slice(&size.to_le_bytes());
            assert_eq!(Header::parse(&bad).err(), Some(Error::HeaderBounds));
        }
    }

    #[test]
    fn section_checks_bounds_and_alignment() {
        let mut bytes = [0; 20];
        bytes[8..12].copy_from_slice(&4096_u32.to_le_bytes());
        bytes[16..20].copy_from_slice(&24_u32.to_le_bytes());
        assert_eq!(section(&bytes, 24).unwrap().0.data, 0..24);
        assert_eq!(section(&bytes, 23).err(), Some(Error::Range));
        bytes[4] = 1;
        assert_eq!(section(&bytes, 24).err(), Some(Error::Alignment));
        bytes[4..8].copy_from_slice(&8192_u32.to_le_bytes());
        assert_eq!(section(&bytes, 24).err(), Some(Error::Range));
    }
}
