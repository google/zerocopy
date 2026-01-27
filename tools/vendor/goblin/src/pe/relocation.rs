use core::iter::FusedIterator;

use scroll::{IOread, IOwrite, Pread, Pwrite, SizeWith};

use crate::error;
use crate::pe::data_directories;
use crate::pe::options;
use crate::pe::section_table;
use crate::pe::utils;

/// Size of a single COFF relocation.
pub const COFF_RELOCATION_SIZE: usize = 10;

// x86 relocations.

/// The relocation is ignored.
pub const IMAGE_REL_I386_ABSOLUTE: u16 = 0x0000;
/// Not supported.
pub const IMAGE_REL_I386_DIR16: u16 = 0x0001;
/// Not supported.
pub const IMAGE_REL_I386_REL16: u16 = 0x0002;
/// The target's 32-bit VA.
pub const IMAGE_REL_I386_DIR32: u16 = 0x0006;
/// The target's 32-bit RVA.
pub const IMAGE_REL_I386_DIR32NB: u16 = 0x0007;
/// Not supported.
pub const IMAGE_REL_I386_SEG12: u16 = 0x0009;
/// The 16-bit section index of the section that contains the target.
///
/// This is used to support debugging information.
pub const IMAGE_REL_I386_SECTION: u16 = 0x000A;
/// The 32-bit offset of the target from the beginning of its section.
///
/// This is used to support debugging information and static thread local storage.
pub const IMAGE_REL_I386_SECREL: u16 = 0x000B;
/// The CLR token.
pub const IMAGE_REL_I386_TOKEN: u16 = 0x000C;
/// A 7-bit offset from the base of the section that contains the target.
pub const IMAGE_REL_I386_SECREL7: u16 = 0x000D;
/// The 32-bit relative displacement to the target.
///
/// This supports the x86 relative branch and call instructions.
pub const IMAGE_REL_I386_REL32: u16 = 0x0014;

// x86-64 relocations.

/// The relocation is ignored.
pub const IMAGE_REL_AMD64_ABSOLUTE: u16 = 0x0000;
/// The 64-bit VA of the relocation target.
pub const IMAGE_REL_AMD64_ADDR64: u16 = 0x0001;
/// The 32-bit VA of the relocation target.
pub const IMAGE_REL_AMD64_ADDR32: u16 = 0x0002;
/// The 32-bit address without an image base (RVA).
pub const IMAGE_REL_AMD64_ADDR32NB: u16 = 0x0003;
/// The 32-bit relative address from the byte following the relocation.
pub const IMAGE_REL_AMD64_REL32: u16 = 0x0004;
/// The 32-bit address relative to byte distance 1 from the relocation.
pub const IMAGE_REL_AMD64_REL32_1: u16 = 0x0005;
/// The 32-bit address relative to byte distance 2 from the relocation.
pub const IMAGE_REL_AMD64_REL32_2: u16 = 0x0006;
/// The 32-bit address relative to byte distance 3 from the relocation.
pub const IMAGE_REL_AMD64_REL32_3: u16 = 0x0007;
/// The 32-bit address relative to byte distance 4 from the relocation.
pub const IMAGE_REL_AMD64_REL32_4: u16 = 0x0008;
/// The 32-bit address relative to byte distance 5 from the relocation.
pub const IMAGE_REL_AMD64_REL32_5: u16 = 0x0009;
/// The 16-bit section index of the section that contains the target.
///
/// This is used to support debugging information.
pub const IMAGE_REL_AMD64_SECTION: u16 = 0x000A;
/// The 32-bit offset of the target from the beginning of its section.
///
/// This is used to support debugging information and static thread local storage.
pub const IMAGE_REL_AMD64_SECREL: u16 = 0x000B;
/// A 7-bit unsigned offset from the base of the section that contains the target.
pub const IMAGE_REL_AMD64_SECREL7: u16 = 0x000C;
/// CLR tokens.
pub const IMAGE_REL_AMD64_TOKEN: u16 = 0x000D;
/// A 32-bit signed span-dependent value emitted into the object.
pub const IMAGE_REL_AMD64_SREL32: u16 = 0x000E;
/// A pair that must immediately follow every span-dependent value.
pub const IMAGE_REL_AMD64_PAIR: u16 = 0x000F;
/// A 32-bit signed span-dependent value that is applied at link time.
pub const IMAGE_REL_AMD64_SSPAN32: u16 = 0x0010;

// ARM relocation.

/// The relocation is ignored.
pub const IMAGE_REL_ARM_ABSOLUTE: u16 = 0x0000;
/// 32-bit address
pub const IMAGE_REL_ARM_ADDR: u16 = 0x0001;
/// 32-bit address without an image base
pub const IMAGE_REL_ARM_ADDR32NB: u16 = 0x0002;
/// 24-bit branch
pub const IMAGE_REL_ARM_BRANCH24: u16 = 0x0003;
/// 11-bit branch
pub const IMAGE_REL_ARM_BRANCH11: u16 = 0x0004;
/// CLR token
pub const IMAGE_REL_ARM_TOKEN: u16 = 0x0005;
/// 12-bit GP-relative addressing
pub const IMAGE_REL_ARM_GPREL12: u16 = 0x0006;
/// 7-bit GP-relative addressing
pub const IMAGE_REL_ARM_GPREL7: u16 = 0x0007;
/// 24-bit BLX (branch with link and exchange)
pub const IMAGE_REL_ARM_BLX24: u16 = 0x0008;
/// 11-bit BLX
pub const IMAGE_REL_ARM_BLX11: u16 = 0x0009;
/// Section index
pub const IMAGE_REL_ARM_SECTION: u16 = 0x000E;
/// 32-bit offset from section base
pub const IMAGE_REL_ARM_SECREL: u16 = 0x000F;
/// MOVW/MOVT (immediate load for addresses)
pub const IMAGE_REL_ARM_MOV32A: u16 = 0x0010;
/// MOVW/MOVT (thumb mode immediate load)
pub const IMAGE_REL_ARM_MOV32T: u16 = 0x0011;
/// Thumb mode 20-bit branch
pub const IMAGE_REL_ARM_BRANCH20T: u16 = 0x0012;
/// Thumb mode 24-bit branch
pub const IMAGE_REL_ARM_BRANCH24T: u16 = 0x0014;
/// Thumb mode 23-bit BLX
pub const IMAGE_REL_ARM_BLX23T: u16 = 0x0015;

// ARM64 relocation.

/// The relocation is ignored.
pub const IMAGE_REL_ARM64_ABSOLUTE: u16 = 0x0000;
/// 32-bit address
pub const IMAGE_REL_ARM64_ADDR32: u16 = 0x0001;
/// 32-bit address without an image base
pub const IMAGE_REL_ARM64_ADDR32NB: u16 = 0x0002;
/// 26-bit branch
pub const IMAGE_REL_ARM64_BRANCH26: u16 = 0x0003;
/// Page-relative 21-bit offset
pub const IMAGE_REL_ARM64_PAGEBASE_REL21: u16 = 0x0004;
/// 21-bit offset from page base
pub const IMAGE_REL_ARM64_REL21: u16 = 0x0005;
/// 12-bit absolute page offset (addend)
pub const IMAGE_REL_ARM64_PAGEOFFSET_12A: u16 = 0x0006;
/// 12-bit absolute page offset (logical)
pub const IMAGE_REL_ARM64_PAGEOFFSET_12L: u16 = 0x0007;
/// 32-bit offset from section base
pub const IMAGE_REL_ARM64_SECREL: u16 = 0x0008;
/// Low 12 bits of section-relative address (addend)
pub const IMAGE_REL_ARM64_SECREL_LOW12A: u16 = 0x0009;
/// High 12 bits of section-relative address (addend)
pub const IMAGE_REL_ARM64_SECREL_HIGH12A: u16 = 0x000A;
/// Low 12 bits of section-relative address (logical)
pub const IMAGE_REL_ARM64_SECREL_LOW12L: u16 = 0x000B;
/// CLR token
pub const IMAGE_REL_ARM64_TOKEN: u16 = 0x000C;
/// Section index
pub const IMAGE_REL_ARM64_SECTION: u16 = 0x000D;
/// 64-bit address
pub const IMAGE_REL_ARM64_ADDR64: u16 = 0x000E;
/// 19-bit branch
pub const IMAGE_REL_ARM64_BRANCH19: u16 = 0x000F;

// IA64 relocation.

/// The relocation is ignored.
pub const IMAGE_REL_IA64_ABSOLUTE: u16 = 0x0000;
/// Immediate 14-bit offset
pub const IMAGE_REL_IA64_IMM14: u16 = 0x0001;
/// Immediate 22-bit offset
pub const IMAGE_REL_IA64_IMM22: u16 = 0x0002;
/// Immediate 64-bit offset
pub const IMAGE_REL_IA64_IMM64: u16 = 0x0003;
/// Direct 32-bit address
pub const IMAGE_REL_IA64_DIR: u16 = 0x0004;
/// Direct 64-bit address
pub const IMAGE_REL_IA64_DIR64: u16 = 0x0005;
/// PC-relative 21-bit branch (bundle format)
pub const IMAGE_REL_IA64_PCREL21B: u16 = 0x0006;
/// PC-relative 21-bit branch (mixed format)
pub const IMAGE_REL_IA64_PCREL21M: u16 = 0x0007;
/// PC-relative 21-bit branch (full format)
pub const IMAGE_REL_IA64_PCREL21F: u16 = 0x0008;
/// GP-relative 22-bit offset
pub const IMAGE_REL_IA64_GPREL22: u16 = 0x0009;
/// 22-bit offset from GP-relative label
pub const IMAGE_REL_IA64_LTOFF22: u16 = 0x000A;
/// Section index
pub const IMAGE_REL_IA64_SECTION: u16 = 0x000B;
/// Section-relative 22-bit offset
pub const IMAGE_REL_IA64_SECREL22: u16 = 0x000C;
/// Section-relative 64-bit offset with immediate
pub const IMAGE_REL_IA64_SECREL64I: u16 = 0x000D;
/// Section-relative offset
pub const IMAGE_REL_IA64_SECREL: u16 = 0x000E;
/// GP-relative 64-bit offset
pub const IMAGE_REL_IA64_LTOFF64: u16 = 0x000F;
/// 32-bit address without an image base
pub const IMAGE_REL_IA64_DIR32NB: u16 = 0x0010;
/// 14-bit section-relative offset
pub const IMAGE_REL_IA64_SREL14: u16 = 0x0011;
/// 22-bit section-relative offset
pub const IMAGE_REL_IA64_SREL22: u16 = 0x0012;
/// 32-bit section-relative offset
pub const IMAGE_REL_IA64_SREL32: u16 = 0x0013;
/// 32-bit user-defined offset
pub const IMAGE_REL_IA64_UREL32: u16 = 0x0014;
/// PC-relative 60-bit offset (extension format)
pub const IMAGE_REL_IA64_PCREL60X: u16 = 0x0015;
/// PC-relative 60-bit offset (bundle format)
pub const IMAGE_REL_IA64_PCREL60B: u16 = 0x0016;
/// PC-relative 60-bit offset (full format)
pub const IMAGE_REL_IA64_PCREL60F: u16 = 0x0017;
/// PC-relative 60-bit offset (immediate format)
pub const IMAGE_REL_IA64_PCREL60I: u16 = 0x0018;
/// PC-relative 60-bit offset (mixed format)
pub const IMAGE_REL_IA64_PCREL60M: u16 = 0x0019;
/// GP-relative 64-bit immediate offset
pub const IMAGE_REL_IA64_IMMGPREL64: u16 = 0x001A;
/// CLR token
pub const IMAGE_REL_IA64_TOKEN: u16 = 0x001B;
/// 32-bit GP-relative offset
pub const IMAGE_REL_IA64_GPREL32: u16 = 0x001C;
/// Offset with an addend
pub const IMAGE_REL_IA64_ADDEND: u16 = 0x001F;

// base relocation.

/// Absolute relocation. No modification is necessary.
pub const IMAGE_REL_BASED_ABSOLUTE: u16 = 0;
/// Relocation based on the high 16 bits of the address.
pub const IMAGE_REL_BASED_HIGH: u16 = 1;
/// Relocation based on the low 16 bits of the address.
pub const IMAGE_REL_BASED_LOW: u16 = 2;
/// Relocation based on the entire 32-bit address.
pub const IMAGE_REL_BASED_HIGHLOW: u16 = 3;
/// Relocation based on the adjusted high 16 bits of the address.
pub const IMAGE_REL_BASED_HIGHADJ: u16 = 4;
/// MIPS jump address relocation.
pub const IMAGE_REL_BASED_MIPS_JMPADDR: u16 = 5;
/// ARM MOV32A relocation (shares the same value as MIPS_JMPADDR).
pub const IMAGE_REL_BASED_ARM_MOV32A: u16 = 5;
/// ARM MOV32 relocation (shares the same value as MIPS_JMPADDR).
pub const IMAGE_REL_BASED_ARM_MOV32: u16 = 5;
/// Relocation based on the section.
pub const IMAGE_REL_BASED_SECTION: u16 = 6;
/// Relocation relative to the base.
pub const IMAGE_REL_BASED_REL: u16 = 7;
/// ARM MOV32T relocation (shares the same value as REL).
pub const IMAGE_REL_BASED_ARM_MOV32T: u16 = 7;
/// Thumb MOV32 relocation (shares the same value as REL).
pub const IMAGE_REL_BASED_THUMB_MOV32: u16 = 7;
/// MIPS 16-bit jump address relocation.
pub const IMAGE_REL_BASED_MIPS_JMPADDR16: u16 = 9;
/// IA64 immediate 64-bit relocation (shares the same value as MIPS_JMPADDR16).
pub const IMAGE_REL_BASED_IA64_IMM64: u16 = 9;
/// Relocation based on a 64-bit address.
pub const IMAGE_REL_BASED_DIR64: u16 = 10;
/// Relocation based on the top 16 bits of a 48-bit address.
pub const IMAGE_REL_BASED_HIGH3ADJ: u16 = 11;

/// A COFF relocation.
#[repr(C)]
#[derive(Debug, Copy, Clone, PartialEq, Default, Pread, Pwrite, IOread, IOwrite, SizeWith)]
pub struct Relocation {
    /// The address of the item to which relocation is applied.
    ///
    /// This is the offset from the beginning of the section, plus the
    /// value of the section's `virtual_address` field.
    pub virtual_address: u32,
    /// A zero-based index into the symbol table.
    ///
    /// This symbol gives the address that is to be used for the relocation. If the specified
    /// symbol has section storage class, then the symbol's address is the address with the
    /// first section of the same name.
    pub symbol_table_index: u32,
    /// A value that indicates the kind of relocation that should be performed.
    ///
    /// Valid relocation types depend on machine type.
    pub typ: u16,
}

/// An iterator for COFF relocations.
#[derive(Default)]
pub struct Relocations<'a> {
    offset: usize,
    relocations: &'a [u8],
}

impl<'a> Relocations<'a> {
    /// Parse a COFF relocation table at the given offset.
    ///
    /// The offset and number of relocations should be from the COFF section header.
    pub fn parse(bytes: &'a [u8], offset: usize, number: usize) -> error::Result<Relocations<'a>> {
        let relocations = bytes.pread_with(offset, number * COFF_RELOCATION_SIZE)?;
        Ok(Relocations {
            offset: 0,
            relocations,
        })
    }
}

impl<'a> Iterator for Relocations<'a> {
    type Item = Relocation;
    fn next(&mut self) -> Option<Self::Item> {
        if self.offset >= self.relocations.len() {
            None
        } else {
            Some(
                self.relocations
                    .gread_with(&mut self.offset, scroll::LE)
                    .unwrap(),
            )
        }
    }
}

/// Represents a PE base relocation directory data.
#[derive(Debug, PartialEq, Clone, Default)]
pub struct RelocationData<'a> {
    /// Raw bytes covering the entire bytes of the base relocation directory.
    bytes: &'a [u8],
}

impl<'a> RelocationData<'a> {
    pub fn parse(
        bytes: &'a [u8],
        dd: data_directories::DataDirectory,
        sections: &[section_table::SectionTable],
        file_alignment: u32,
    ) -> error::Result<Self> {
        Self::parse_with_opts(
            bytes,
            dd,
            sections,
            file_alignment,
            &options::ParseOptions::default(),
        )
    }

    pub fn parse_with_opts(
        bytes: &'a [u8],
        dd: data_directories::DataDirectory,
        sections: &[section_table::SectionTable],
        file_alignment: u32,
        opts: &options::ParseOptions,
    ) -> error::Result<Self> {
        let offset =
            match utils::find_offset(dd.virtual_address as usize, sections, file_alignment, opts) {
                Some(offset) => offset,
                None => {
                    return Err(error::Error::Malformed(format!(
                        "Cannot map base reloc rva {:#x} into offset",
                        dd.virtual_address
                    )));
                }
            };

        let available_size = if offset + (dd.size as usize) <= bytes.len() {
            dd.size as usize
        } else {
            return Err(error::Error::Malformed(format!(
                "base reloc offset {:#x} and size {:#x} exceeds the bounds of the bytes size {:#x}",
                offset,
                dd.size,
                bytes.len()
            )));
        };

        if offset >= bytes.len() {
            return Err(error::Error::Malformed(format!(
                "Relocation offset {:#x} is beyond file bounds (file size: {:#x})",
                offset,
                bytes.len()
            )));
        }

        // Ensure we don't try to read more bytes than are actually available
        let remaining_bytes = bytes.len() - offset;
        let safe_available_size = available_size.min(remaining_bytes);

        if safe_available_size != available_size {
            return Err(error::Error::Malformed(format!(
                "Relocation size {:#x} at offset {:#x} exceeds remaining file data ({:#x} bytes)",
                available_size, offset, remaining_bytes
            )));
        }

        let bytes = bytes
            .pread_with::<&[u8]>(offset, safe_available_size)
            .map_err(|_| {
                error::Error::Malformed(format!(
                    "base reloc offset {:#x} and size {:#x} exceeds the bounds of the bytes size {:#x}",
                    offset,
                    safe_available_size,
                    bytes.len()
                ))
            })?;

        Ok(Self { bytes })
    }

    /// Returns iterator for [`RelocationBlock`]
    pub fn blocks(&self) -> RelocationBlockIterator<'a> {
        RelocationBlockIterator {
            bytes: &self.bytes,
            offset: 0,
        }
    }
}

/// Represents a PE (Portable Executable) base relocation block.
///
/// In the PE format, base relocations are organized into blocks, where each block corresponds
/// to a contiguous range of memory that needs to be relocated. The relocations within a block
/// specify offsets relative to the block's starting address.
///
/// Unlike COFF (Common Object File Format), PE base relocations are separated by blocks.
/// Each block begins with a [`RelocationBlock`] structure that provides information about the
/// relocation block, including its starting RVA (Relative Virtual Address) and size in bytes.
///
/// Each block ends with an "absolute" relocation entry, which acts as a marker to indicate
/// the end of the block. This entry has no actual relocation effect.
#[derive(Debug, Copy, Clone, PartialEq, Default)]
pub struct RelocationBlock<'a> {
    /// The starting RVA for the relocation block.
    pub rva: u32,
    /// The total size of the relocation block, in bytes.
    pub size: u32,
    /// The bytes of [`RelocationWord`] data within this block.
    pub bytes: &'a [u8],
}

impl RelocationBlock<'_> {
    /// Returns iterator for [`RelocationWord`]
    pub fn words(&self) -> RelocationWordIterator<'_> {
        RelocationWordIterator {
            bytes: &self.bytes,
            offset: 0,
        }
    }
}

/// Raw size of [`RelocationBlock`]
pub const RELOCATION_BLOCK_SIZE: usize = 8;

impl<'a> scroll::ctx::TryFromCtx<'a, scroll::Endian> for RelocationBlock<'a> {
    type Error = crate::error::Error;

    fn try_from_ctx(bytes: &'a [u8], ctx: scroll::Endian) -> Result<(Self, usize), Self::Error> {
        let mut offset = 0;
        let rva = bytes.gread_with::<u32>(&mut offset, ctx)?;
        let size = bytes.gread_with::<u32>(&mut offset, ctx)?;
        if (size as usize) < RELOCATION_BLOCK_SIZE {
            return Err(error::Error::Malformed(format!(
                "base reloc size {size} is less than a block {RELOCATION_BLOCK_SIZE}"
            )));
        }
        let word_size = size as usize - RELOCATION_BLOCK_SIZE;
        let word_data = bytes.gread_with::<&[u8]>(&mut offset, word_size).map_err(|_| error::Error::Malformed(format!(
                "base reloc block offset {:#x} and size {:#x} exceeds the bounds of the bytes size {:#x}",
                offset,
                word_size,
                bytes.len()
            )))?;
        Ok((
            Self {
                rva,
                size,
                bytes: word_data,
            },
            offset,
        ))
    }
}

#[derive(Clone, Copy, Debug)]
pub struct RelocationBlockIterator<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Iterator for RelocationBlockIterator<'a> {
    type Item = error::Result<RelocationBlock<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.offset >= self.bytes.len() {
            return None;
        }

        Some(
            match self
                .bytes
                .gread_with::<RelocationBlock>(&mut self.offset, scroll::LE)
            {
                Ok(block) => Ok(block),
                Err(error) => {
                    self.bytes = &[];
                    Err(error.into())
                }
            },
        )
    }
}

impl FusedIterator for RelocationBlockIterator<'_> {}

/// Represents a single relocation entry within a PE base relocation block.
///
/// Each relocation entry is stored as a 16-bit value ([`u16`]), referred to as a "relocation word."
/// The value is divided into two components:
///
/// * The upper 4 bits specify the relocation type, which determines how the relocation
///   should be applied.
/// * The remaining 12 bits specify the offset from the block's starting RVA where the
///   relocation should be applied.
#[derive(Debug, Copy, Clone, PartialEq, Default, Pread, Pwrite, IOread, IOwrite, SizeWith)]
pub struct RelocationWord {
    /// A 16-bit value encoding the relocation type and offset.
    ///
    /// - Upper 4 bits: relocation type.
    /// - Lower 12 bits: offset from the base RVA.
    pub value: u16,
}

impl RelocationWord {
    /// Returns the relocation type from the upper 4 bits of [Self::value].
    pub fn reloc_type(&self) -> u8 {
        (self.value >> 12) as u8
    }

    /// Returns the relocation offset from the lower 16 bits of [Self::value].
    pub fn offset(&self) -> u16 {
        (self.value & 0xFFF) as u16
    }
}

#[derive(Clone, Copy, Debug)]
pub struct RelocationWordIterator<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl Iterator for RelocationWordIterator<'_> {
    type Item = error::Result<RelocationWord>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.offset >= self.bytes.len() {
            return None;
        }

        Some(match self.bytes.gread_with(&mut self.offset, scroll::LE) {
            Ok(word) => Ok(word),
            Err(error) => {
                self.bytes = &[];
                Err(error.into())
            }
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let count = self.bytes.len() / core::mem::size_of::<RelocationWord>();
        (count, Some(count))
    }
}

impl FusedIterator for RelocationWordIterator<'_> {}

#[cfg(test)]
mod tests {
    use super::*;

    static BASERELOC_DATA1: &[u8; 1360] = &[
        0x00, 0xD0, 0x11, 0x00, 0x34, 0x02, 0x00, 0x00, 0x08, 0xA0, 0x18, 0xA0, 0x28, 0xA0, 0x38,
        0xA0, 0x48, 0xA0, 0x58, 0xA0, 0x68, 0xA0, 0x78, 0xA0, 0x88, 0xA0, 0x98, 0xA0, 0xA8, 0xA0,
        0xB8, 0xA0, 0xC8, 0xA0, 0xD8, 0xA0, 0xE0, 0xA0, 0xE8, 0xA0, 0xF0, 0xA0, 0xF8, 0xA0, 0x00,
        0xA1, 0x08, 0xA1, 0x10, 0xA1, 0x18, 0xA1, 0x20, 0xA1, 0x28, 0xA1, 0x30, 0xA1, 0x38, 0xA1,
        0x48, 0xA1, 0x50, 0xA1, 0x58, 0xA1, 0x60, 0xA1, 0x68, 0xA1, 0x70, 0xA1, 0x78, 0xA1, 0x80,
        0xA1, 0x88, 0xA1, 0x98, 0xA1, 0xA0, 0xA1, 0xA8, 0xA1, 0xB8, 0xA1, 0xC0, 0xA1, 0xC8, 0xA1,
        0xD0, 0xA1, 0xD8, 0xA1, 0xE8, 0xA1, 0xF8, 0xA1, 0x08, 0xA2, 0x18, 0xA2, 0x28, 0xA2, 0x38,
        0xA2, 0x48, 0xA2, 0x58, 0xA2, 0x68, 0xA2, 0x78, 0xA2, 0x88, 0xA2, 0x98, 0xA2, 0xA8, 0xA2,
        0xB8, 0xA2, 0xC8, 0xA2, 0xD8, 0xA2, 0xE8, 0xA2, 0x08, 0xA3, 0x28, 0xA3, 0x48, 0xA3, 0x68,
        0xA3, 0x88, 0xA3, 0x98, 0xA3, 0xA8, 0xA3, 0xB8, 0xA3, 0xC8, 0xA3, 0xD8, 0xA3, 0xE8, 0xA3,
        0xF8, 0xA3, 0x08, 0xA4, 0x18, 0xA4, 0x28, 0xA4, 0x38, 0xA4, 0x48, 0xA4, 0x58, 0xA4, 0x70,
        0xA4, 0xA0, 0xA4, 0xA8, 0xA6, 0xB8, 0xA6, 0xC8, 0xA6, 0xD8, 0xA6, 0xE8, 0xA6, 0xF8, 0xA6,
        0x00, 0xA7, 0x08, 0xA7, 0x30, 0xA7, 0x60, 0xA7, 0x88, 0xA7, 0x98, 0xA7, 0xA8, 0xA7, 0xB8,
        0xA7, 0xC8, 0xA7, 0xD0, 0xA7, 0xD8, 0xA7, 0xE0, 0xA7, 0xF8, 0xA7, 0x00, 0xA8, 0x08, 0xA8,
        0x10, 0xA8, 0x28, 0xA8, 0x38, 0xA8, 0x50, 0xA8, 0x70, 0xA8, 0x78, 0xA8, 0x80, 0xA8, 0x88,
        0xA8, 0x90, 0xA8, 0x98, 0xA8, 0xA0, 0xA8, 0xA8, 0xA8, 0xB0, 0xA8, 0xB8, 0xA8, 0xC0, 0xA8,
        0xC8, 0xA8, 0xD0, 0xA8, 0xD8, 0xA8, 0xE0, 0xA8, 0xE8, 0xA8, 0xF0, 0xA8, 0xF8, 0xA8, 0x00,
        0xA9, 0x08, 0xA9, 0x10, 0xA9, 0x18, 0xA9, 0x20, 0xA9, 0x28, 0xA9, 0x30, 0xA9, 0x38, 0xA9,
        0x40, 0xA9, 0x48, 0xA9, 0x50, 0xA9, 0x58, 0xA9, 0x60, 0xA9, 0x68, 0xA9, 0x70, 0xA9, 0x78,
        0xA9, 0x80, 0xA9, 0x88, 0xA9, 0x90, 0xA9, 0x98, 0xA9, 0xA0, 0xA9, 0xA8, 0xA9, 0xB0, 0xA9,
        0xB8, 0xA9, 0xC0, 0xA9, 0xC8, 0xA9, 0xD0, 0xA9, 0xD8, 0xA9, 0xE0, 0xA9, 0xE8, 0xA9, 0xF0,
        0xA9, 0xF8, 0xA9, 0x00, 0xAA, 0x08, 0xAA, 0x10, 0xAA, 0x18, 0xAA, 0x20, 0xAA, 0x28, 0xAA,
        0x30, 0xAA, 0x38, 0xAA, 0x40, 0xAA, 0x48, 0xAA, 0x50, 0xAA, 0x58, 0xAA, 0x70, 0xAA, 0x80,
        0xAA, 0x88, 0xAA, 0x98, 0xAA, 0xB0, 0xAA, 0xC8, 0xAA, 0xE0, 0xAA, 0xF8, 0xAA, 0x08, 0xAB,
        0x18, 0xAB, 0x28, 0xAB, 0x38, 0xAB, 0x48, 0xAB, 0x58, 0xAB, 0x68, 0xAB, 0x78, 0xAB, 0xD8,
        0xAB, 0xF0, 0xAB, 0xF8, 0xAB, 0x00, 0xAC, 0x88, 0xAC, 0xA0, 0xAC, 0xA8, 0xAC, 0xB0, 0xAC,
        0xB8, 0xAC, 0xC0, 0xAC, 0xC8, 0xAC, 0xD0, 0xAC, 0xD8, 0xAC, 0xE0, 0xAC, 0xE8, 0xAC, 0xF8,
        0xAC, 0x00, 0xAD, 0x08, 0xAD, 0x10, 0xAD, 0x18, 0xAD, 0x20, 0xAD, 0x28, 0xAD, 0x30, 0xAD,
        0x38, 0xAD, 0x48, 0xAD, 0x50, 0xAD, 0x58, 0xAD, 0x60, 0xAD, 0x70, 0xAD, 0x78, 0xAD, 0x80,
        0xAD, 0x88, 0xAD, 0x98, 0xAD, 0xA0, 0xAD, 0xA8, 0xAD, 0xB0, 0xAD, 0xC8, 0xAD, 0xD0, 0xAD,
        0xD8, 0xAD, 0xF0, 0xAD, 0xF8, 0xAD, 0x00, 0xAE, 0x18, 0xAE, 0x20, 0xAE, 0x28, 0xAE, 0x30,
        0xAE, 0x38, 0xAE, 0x40, 0xAE, 0x48, 0xAE, 0x50, 0xAE, 0x58, 0xAE, 0x60, 0xAE, 0x68, 0xAE,
        0x70, 0xAE, 0x78, 0xAE, 0x80, 0xAE, 0x88, 0xAE, 0x98, 0xAE, 0xA8, 0xAE, 0xB8, 0xAE, 0xC8,
        0xAE, 0xD8, 0xAE, 0xE8, 0xAE, 0xF8, 0xAE, 0x08, 0xAF, 0x18, 0xAF, 0x20, 0xAF, 0x28, 0xAF,
        0x30, 0xAF, 0x38, 0xAF, 0x40, 0xAF, 0x48, 0xAF, 0x50, 0xAF, 0x58, 0xAF, 0x60, 0xAF, 0x68,
        0xAF, 0x70, 0xAF, 0x78, 0xAF, 0x80, 0xAF, 0x88, 0xAF, 0x90, 0xAF, 0x98, 0xAF, 0xA0, 0xAF,
        0xA8, 0xAF, 0xB0, 0xAF, 0xB8, 0xAF, 0xC0, 0xAF, 0xC8, 0xAF, 0xD0, 0xAF, 0xD8, 0xAF, 0xE0,
        0xAF, 0xE8, 0xAF, 0xF0, 0xAF, 0xF8, 0xAF, 0x00, 0x00, 0x00, 0xE0, 0x11, 0x00, 0x58, 0x01,
        0x00, 0x00, 0x00, 0xA0, 0x08, 0xA0, 0x10, 0xA0, 0x18, 0xA0, 0x20, 0xA0, 0x30, 0xA0, 0x40,
        0xA0, 0x48, 0xA0, 0x50, 0xA0, 0x58, 0xA0, 0x60, 0xA0, 0x68, 0xA0, 0x70, 0xA0, 0x78, 0xA0,
        0x80, 0xA0, 0x88, 0xA0, 0x90, 0xA0, 0x98, 0xA0, 0xA0, 0xA0, 0xA8, 0xA0, 0xB0, 0xA0, 0xB8,
        0xA0, 0xC0, 0xA0, 0xC8, 0xA0, 0xD0, 0xA0, 0xD8, 0xA0, 0xE0, 0xA0, 0xE8, 0xA0, 0xF0, 0xA0,
        0xF8, 0xA0, 0x00, 0xA1, 0x08, 0xA1, 0x10, 0xA1, 0x18, 0xA1, 0x20, 0xA1, 0x28, 0xA1, 0x30,
        0xA1, 0x38, 0xA1, 0x40, 0xA1, 0x48, 0xA1, 0x50, 0xA1, 0x58, 0xA1, 0x60, 0xA1, 0x68, 0xA1,
        0x70, 0xA1, 0x78, 0xA1, 0x80, 0xA1, 0x88, 0xA1, 0x90, 0xA1, 0x98, 0xA1, 0xA0, 0xA1, 0xA8,
        0xA1, 0xB0, 0xA1, 0xB8, 0xA1, 0xC0, 0xA1, 0xC8, 0xA1, 0xD0, 0xA1, 0xD8, 0xA1, 0xE0, 0xA1,
        0xF0, 0xA1, 0x08, 0xA2, 0x10, 0xA2, 0x20, 0xA2, 0x30, 0xA2, 0x48, 0xA2, 0x50, 0xA2, 0x58,
        0xA2, 0x60, 0xA2, 0x68, 0xA2, 0x70, 0xA2, 0x78, 0xA2, 0x88, 0xA2, 0x90, 0xA2, 0xA0, 0xA2,
        0xA8, 0xA2, 0xB8, 0xA2, 0xC0, 0xA2, 0xD0, 0xA2, 0xD8, 0xA2, 0xE8, 0xA2, 0xF0, 0xA2, 0x08,
        0xA3, 0x18, 0xA3, 0x28, 0xA3, 0x38, 0xA3, 0x48, 0xA3, 0x58, 0xA3, 0x68, 0xA3, 0x78, 0xA3,
        0x80, 0xA3, 0x88, 0xA3, 0x90, 0xA3, 0x98, 0xA3, 0xA0, 0xA3, 0xA8, 0xA3, 0xB8, 0xA3, 0xC8,
        0xA3, 0xD8, 0xA3, 0xF0, 0xA3, 0x18, 0xA4, 0x20, 0xA4, 0x30, 0xA4, 0x40, 0xA4, 0x50, 0xA4,
        0x60, 0xA4, 0x70, 0xA4, 0x80, 0xA4, 0x90, 0xA4, 0xA0, 0xA4, 0xB0, 0xA4, 0xC0, 0xA4, 0xD0,
        0xA4, 0xE0, 0xA4, 0xF0, 0xA4, 0x00, 0xA5, 0x10, 0xA5, 0x28, 0xA5, 0x50, 0xA5, 0x60, 0xA5,
        0x70, 0xA5, 0x80, 0xA5, 0x90, 0xA5, 0xA0, 0xA5, 0xB0, 0xA5, 0xC0, 0xA5, 0xD0, 0xA5, 0xE0,
        0xA5, 0xF0, 0xA5, 0x00, 0xA6, 0x10, 0xA6, 0x20, 0xA6, 0x28, 0xA6, 0x30, 0xA6, 0x38, 0xA6,
        0x50, 0xA6, 0x68, 0xA6, 0x78, 0xA6, 0x88, 0xA6, 0x98, 0xA6, 0xA8, 0xA6, 0xB8, 0xA6, 0xC8,
        0xA6, 0xD8, 0xA6, 0xE8, 0xA6, 0xF8, 0xA6, 0x08, 0xA7, 0x18, 0xA7, 0x28, 0xA7, 0x38, 0xA7,
        0x48, 0xA7, 0x58, 0xA7, 0x68, 0xA7, 0x78, 0xA7, 0x88, 0xA7, 0x98, 0xA7, 0xA8, 0xA7, 0xB8,
        0xA7, 0xC8, 0xA7, 0xD8, 0xA7, 0xE8, 0xA7, 0xF8, 0xA7, 0x08, 0xA8, 0x18, 0xA8, 0x28, 0xA8,
        0x38, 0xA8, 0x58, 0xA8, 0x68, 0xA8, 0x80, 0xA8, 0x00, 0x60, 0x12, 0x00, 0x1C, 0x00, 0x00,
        0x00, 0xA0, 0xA9, 0xA8, 0xA9, 0xB0, 0xA9, 0xB8, 0xA9, 0xC0, 0xA9, 0xC8, 0xA9, 0xD0, 0xA9,
        0xD8, 0xA9, 0xE0, 0xA9, 0x00, 0x00, 0x00, 0x20, 0x15, 0x00, 0x28, 0x00, 0x00, 0x00, 0xE8,
        0xA0, 0xF0, 0xA0, 0xF8, 0xA0, 0x08, 0xA1, 0x10, 0xA1, 0x18, 0xA1, 0x20, 0xA1, 0x38, 0xA1,
        0x40, 0xA1, 0x48, 0xA1, 0x58, 0xA1, 0x60, 0xA1, 0x68, 0xA1, 0x70, 0xA1, 0x90, 0xA1, 0x00,
        0x00, 0x00, 0x60, 0x16, 0x00, 0xE8, 0x00, 0x00, 0x00, 0x00, 0xA0, 0x08, 0xA0, 0x78, 0xA0,
        0x98, 0xA0, 0xB8, 0xA0, 0xD8, 0xA0, 0xF8, 0xA0, 0x38, 0xA1, 0x50, 0xA1, 0x58, 0xA1, 0x60,
        0xA1, 0x78, 0xA1, 0x88, 0xA1, 0x98, 0xA1, 0xA8, 0xA1, 0xB8, 0xA1, 0xC8, 0xA1, 0xD8, 0xA1,
        0xE8, 0xA1, 0xF8, 0xA1, 0x08, 0xA2, 0x18, 0xA2, 0x28, 0xA2, 0x38, 0xA2, 0x48, 0xA2, 0x58,
        0xA2, 0x68, 0xA2, 0x78, 0xA2, 0x88, 0xA2, 0x98, 0xA2, 0xA8, 0xA2, 0xB8, 0xA2, 0xC8, 0xA2,
        0xD8, 0xA2, 0xE8, 0xA2, 0xF8, 0xA2, 0x08, 0xA3, 0x18, 0xA3, 0x28, 0xA3, 0x38, 0xA3, 0x40,
        0xA3, 0x48, 0xA3, 0x50, 0xA3, 0x58, 0xA3, 0x60, 0xA3, 0x68, 0xA3, 0x70, 0xA3, 0x78, 0xA3,
        0x80, 0xA3, 0x88, 0xA3, 0x98, 0xA3, 0xA0, 0xA3, 0xA8, 0xA3, 0xB0, 0xA3, 0xB8, 0xA3, 0xC0,
        0xA3, 0xC8, 0xA3, 0xD0, 0xA3, 0xE0, 0xA3, 0xA8, 0xA4, 0xB0, 0xA4, 0xC0, 0xA4, 0xF0, 0xA4,
        0x28, 0xA5, 0x60, 0xA5, 0x98, 0xA5, 0xC8, 0xA5, 0xF0, 0xA5, 0xF8, 0xA5, 0x10, 0xA6, 0x30,
        0xA6, 0x38, 0xA6, 0x40, 0xA6, 0x48, 0xA6, 0x50, 0xA6, 0x58, 0xA6, 0x68, 0xA6, 0xA0, 0xA6,
        0xD0, 0xA6, 0xD8, 0xA6, 0xE0, 0xA6, 0xE8, 0xA6, 0xF8, 0xA6, 0x00, 0xA7, 0x08, 0xA7, 0x10,
        0xA7, 0x48, 0xA7, 0x50, 0xA7, 0x60, 0xA7, 0xC8, 0xA7, 0xD0, 0xA7, 0xE0, 0xA7, 0x48, 0xA8,
        0x50, 0xA8, 0x60, 0xA8, 0xD0, 0xA8, 0xD8, 0xA8, 0xE0, 0xA8, 0x18, 0xA9, 0x20, 0xA9, 0x30,
        0xA9, 0x98, 0xA9, 0xA0, 0xA9, 0xB0, 0xA9, 0x20, 0xAA, 0x50, 0xAA, 0x78, 0xAA, 0x80, 0xAA,
        0x88, 0xAA, 0x98, 0xAA, 0xA0, 0xAA, 0xA8, 0xAA, 0x00, 0x10, 0x18, 0x00, 0x8C, 0x00, 0x00,
        0x00, 0x00, 0xA0, 0x08, 0xA0, 0x10, 0xA0, 0x18, 0xA0, 0x20, 0xA0, 0x28, 0xA0, 0x30, 0xA0,
        0x38, 0xA0, 0x40, 0xA0, 0x48, 0xA0, 0x50, 0xA0, 0x58, 0xA0, 0x60, 0xA0, 0x68, 0xA0, 0x70,
        0xA0, 0x78, 0xA0, 0x80, 0xA0, 0x88, 0xA0, 0x90, 0xA0, 0x98, 0xA0, 0xA0, 0xA0, 0xA8, 0xA0,
        0xB0, 0xA0, 0xB8, 0xA0, 0xC0, 0xA0, 0xC8, 0xA0, 0xD0, 0xA0, 0xD8, 0xA0, 0xE0, 0xA0, 0xE8,
        0xA0, 0xF0, 0xA0, 0xF8, 0xA0, 0x00, 0xA1, 0x08, 0xA1, 0x10, 0xA1, 0x18, 0xA1, 0x20, 0xA1,
        0x28, 0xA1, 0x30, 0xA1, 0x38, 0xA1, 0x40, 0xA1, 0x48, 0xA1, 0x50, 0xA1, 0x58, 0xA1, 0x60,
        0xA1, 0x68, 0xA1, 0x70, 0xA1, 0x78, 0xA1, 0x80, 0xA1, 0x88, 0xA1, 0x90, 0xA1, 0x98, 0xA1,
        0xA0, 0xA1, 0xA8, 0xA1, 0xB0, 0xA1, 0xB8, 0xA1, 0xC0, 0xA1, 0xC8, 0xA1, 0xD0, 0xA1, 0xE0,
        0xA1, 0xF0, 0xA3, 0xF8, 0xA3, 0x00, 0xA4, 0x08, 0xA4, 0x10, 0xA4, 0x18, 0xA4, 0x00, 0x50,
        0x18, 0x00, 0x0C, 0x00, 0x00, 0x00, 0x00, 0xA0, 0x00, 0x00,
    ];

    #[test]
    fn parse_baserelocs() {
        let it = RelocationBlockIterator {
            bytes: BASERELOC_DATA1,
            offset: 0,
        };
        let blocks = it
            .collect::<crate::error::Result<Vec<RelocationBlock>>>()
            .unwrap();
        assert_eq!(blocks.len(), 7);

        const RELOC_ANY_ABSOLUTE: u8 = 0;
        let ends_with_absrel = |block: &RelocationBlock| {
            block
                .words()
                .last()
                .transpose()
                .unwrap()
                .map(|x| x.reloc_type() == RELOC_ANY_ABSOLUTE)
                .unwrap_or(false)
        };

        assert_eq!(blocks[0].rva, 0x0011D000);
        assert_eq!(blocks[0].size, 0x234);
        assert_eq!(ends_with_absrel(&blocks[0]), true);
        assert_eq!(blocks[1].rva, 0x0011E000);
        assert_eq!(blocks[1].size, 0x158);
        assert_eq!(ends_with_absrel(&blocks[1]), false);
        assert_eq!(blocks[2].rva, 0x00126000);
        assert_eq!(blocks[2].size, 0x1C);
        assert_eq!(ends_with_absrel(&blocks[2]), true);
        assert_eq!(blocks[3].rva, 0x00152000);
        assert_eq!(blocks[3].size, 0x28);
        assert_eq!(ends_with_absrel(&blocks[3]), true);
        assert_eq!(blocks[4].rva, 0x00166000);
        assert_eq!(blocks[4].size, 0xE8);
        assert_eq!(ends_with_absrel(&blocks[4]), false);
        assert_eq!(blocks[5].rva, 0x00181000);
        assert_eq!(blocks[5].size, 0x8C);
        assert_eq!(ends_with_absrel(&blocks[5]), false);
        assert_eq!(blocks[6].rva, 0x00185000);
        assert_eq!(blocks[6].size, 0xC);
        assert_eq!(ends_with_absrel(&blocks[6]), true);

        let words = blocks
            .iter()
            .flat_map(|b| b.words())
            .collect::<crate::error::Result<Vec<RelocationWord>>>()
            .unwrap();
        assert_eq!(words.len(), 652);
    }
}
