use core::iter::FusedIterator;

use crate::error;
use crate::options::Permissive;
use log::debug;
use scroll::{Pread, Pwrite, SizeWith};

use crate::pe::data_directories;
use crate::pe::options;
use crate::pe::section_table;
use crate::pe::utils;

/// Size of [`ImageDebugDirectory`]
pub const IMAGE_DEBUG_DIRECTORY_SIZE: usize = 0x1C;

/// Iterator over debug directory entries in [`DebugData`].
#[derive(Debug, Copy, Clone)]
pub struct ImageDebugDirectoryIterator<'a> {
    /// Raw data reference that scoped to the next element if appropriate
    data: &'a [u8],
    /// Fixup RVA offset used for TE fixups
    ///
    /// - **When zero**: no fixup is performed
    /// - **When non-zero**: fixup is performed
    rva_offset: u32,
}

impl Iterator for ImageDebugDirectoryIterator<'_> {
    type Item = error::Result<ImageDebugDirectory>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.data.is_empty() {
            return None;
        }

        Some(
            match self.data.pread_with::<ImageDebugDirectory>(0, scroll::LE) {
                Ok(func) => {
                    self.data = &self.data[IMAGE_DEBUG_DIRECTORY_SIZE..];

                    // Adjust all addresses in the TE binary debug data if fixup is specified
                    let idd = ImageDebugDirectory {
                        address_of_raw_data: func.address_of_raw_data.wrapping_sub(self.rva_offset),
                        pointer_to_raw_data: func.pointer_to_raw_data.wrapping_sub(self.rva_offset),
                        ..func
                    };

                    debug!(
                        "ImageDebugDirectory address of raw data fixed up from: 0x{:X} to 0x{:X}",
                        idd.address_of_raw_data.wrapping_add(self.rva_offset),
                        idd.address_of_raw_data,
                    );

                    debug!(
                        "ImageDebugDirectory pointer to raw data fixed up from: 0x{:X} to 0x{:X}",
                        idd.pointer_to_raw_data.wrapping_add(self.rva_offset),
                        idd.pointer_to_raw_data,
                    );

                    Ok(idd)
                }
                Err(error) => {
                    self.data = &[];
                    Err(error.into())
                }
            },
        )
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.data.len() / IMAGE_DEBUG_DIRECTORY_SIZE;
        (len, Some(len))
    }
}

impl FusedIterator for ImageDebugDirectoryIterator<'_> {}
impl ExactSizeIterator for ImageDebugDirectoryIterator<'_> {}

impl<'a> ImageDebugDirectoryIterator<'a> {
    /// Find a specific debug type in the debug data.
    pub fn find_type(&self, data_type: u32) -> Option<ImageDebugDirectory> {
        self.filter_map(Result::ok)
            .find(|idd| idd.data_type == data_type)
    }
}

/// Represents debug data extracted from a PE (Portable Executable) or TE (Terse Executable) file.
#[derive(Debug, PartialEq, Clone, Default)]
pub struct DebugData<'a> {
    /// Raw data covering bytes of entire [`ImageDebugDirectory`]
    data: &'a [u8],
    /// Fixup RVA offset used for TE fixups
    ///
    /// - **When zero**: no fixup is performed
    /// - **When non-zero**: fixup is performed
    rva_offset: u32,
    /// Parsed CodeView PDB 7.0 (RSDS) debug information, if available.
    ///
    /// CodeView PDB 7.0 contains a GUID, an age value, and the path to the PDB file.
    /// This is commonly used in modern PDB files.
    ///
    /// [`IMAGE_DEBUG_TYPE_CODEVIEW`]
    pub codeview_pdb70_debug_info: Option<CodeviewPDB70DebugInfo<'a>>,
    /// Parsed CodeView PDB 2.0 (NB10) debug information, if available.
    ///
    /// CodeView PDB 2.0 includes a signature, an age value, and the path to the PDB file.
    /// It is used in older PDB formats.
    ///
    /// [`IMAGE_DEBUG_TYPE_CODEVIEW`]
    pub codeview_pdb20_debug_info: Option<CodeviewPDB20DebugInfo<'a>>,
    /// Visual C++ feature data, if available.
    ///
    /// This includes information about specific features or optimizations enabled
    /// in Visual C++ builds.
    ///
    /// [`IMAGE_DEBUG_TYPE_VC_FEATURE`]
    pub vcfeature_info: Option<VCFeatureInfo>,
    /// Extended DLL characteristics information, if available.
    ///
    /// This data includes extended properties of the DLL that may affect
    /// how the operating system handles the DLL, such as security features.
    ///
    /// [`IMAGE_DEBUG_TYPE_EX_DLLCHARACTERISTICS`]
    pub ex_dll_characteristics_info: Option<ExDllCharacteristicsInfo>,
    /// Reproducible build (Repro) information, if available.
    ///
    /// - **MSVC builds**: Contains a 32-byte hash stored directly in the raw data.
    /// - **Clang builds**: Uses the [`ImageDebugDirectory::time_date_stamp`] as a hash,
    ///   with no dedicated raw data.
    ///
    /// [`IMAGE_DEBUG_TYPE_REPRO`]
    pub repro_info: Option<ReproInfo<'a>>,
    /// Profile-guided optimization (POGO aka PGO) data, if available.
    ///
    /// This data provides information relevant to Profile-Guided Optimization
    /// (POGO) processes, including function and data block optimizations.
    ///
    /// [`IMAGE_DEBUG_TYPE_POGO`]
    ///
    /// Reference: <https://devblogs.microsoft.com/cppblog/pogo>
    pub pogo_info: Option<POGOInfo<'a>>,
}

impl<'a> DebugData<'a> {
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
        Self::parse_with_opts_and_fixup(bytes, dd, sections, file_alignment, opts, 0)
    }

    pub fn parse_with_opts_and_fixup(
        bytes: &'a [u8],
        dd: data_directories::DataDirectory,
        sections: &[section_table::SectionTable],
        file_alignment: u32,
        opts: &options::ParseOptions,
        rva_offset: u32,
    ) -> error::Result<Self> {
        let offset =
            match utils::find_offset(dd.virtual_address as usize, sections, file_alignment, opts) {
                Some(offset) => offset,
                None => {
                    return Err(error::Error::Malformed(format!(
                        "Cannot map ImageDebugDirectory rva {:#x} into offset",
                        dd.virtual_address
                    )))?;
                }
            };

        // Ensure that the offset and size do not exceed the length of the bytes slice
        let available_size = if offset + dd.size as usize > bytes.len() {
            let remaining_bytes = bytes.len().saturating_sub(offset);
            Err(error::Error::Malformed(format!(
                "ImageDebugDirectory offset {:#x} and size {:#x} exceeds the bounds of the bytes size {:#x}. \
                This may indicate a packed binary.",
                offset,
                dd.size,
                bytes.len()
            )))
            .or_permissive_and_value(
                opts.parse_mode.is_permissive(),
                "ImageDebugDirectory exceeds bounds; truncating",
                remaining_bytes,
            )?
        } else {
            dd.size as usize
        };

        let data = if available_size > 0 {
            bytes.pread_with::<&[u8]>(offset, available_size)?
        } else {
            &[]
        };
        let it = ImageDebugDirectoryIterator { data, rva_offset };

        let mut codeview_pdb70_debug_info = None;
        let mut codeview_pdb20_debug_info = None;
        let mut vcfeature_info = None;
        let mut ex_dll_characteristics_info = None;
        let mut repro_info = None;
        let mut pogo_info = None;

        if let Some(idd) = &it.find_type(IMAGE_DEBUG_TYPE_CODEVIEW) {
            codeview_pdb70_debug_info = CodeviewPDB70DebugInfo::parse_with_opts(bytes, idd, opts)?;
            codeview_pdb20_debug_info = CodeviewPDB20DebugInfo::parse_with_opts(bytes, idd, opts)?;
        }
        if let Some(idd) = &it.find_type(IMAGE_DEBUG_TYPE_VC_FEATURE) {
            vcfeature_info = Some(VCFeatureInfo::parse_with_opts(bytes, idd, opts)?);
        }
        if let Some(idd) = &it.find_type(IMAGE_DEBUG_TYPE_EX_DLLCHARACTERISTICS) {
            ex_dll_characteristics_info =
                Some(ExDllCharacteristicsInfo::parse_with_opts(bytes, idd, opts)?);
        }
        if let Some(idd) = &it.find_type(IMAGE_DEBUG_TYPE_REPRO) {
            repro_info = Some(ReproInfo::parse_with_opts(bytes, idd, opts)?);
        }
        if let Some(idd) = &it.find_type(IMAGE_DEBUG_TYPE_POGO) {
            pogo_info = POGOInfo::parse_with_opts(bytes, idd, opts)?;
        }

        Ok(DebugData {
            data,
            rva_offset,
            codeview_pdb70_debug_info,
            codeview_pdb20_debug_info,
            vcfeature_info,
            ex_dll_characteristics_info,
            repro_info,
            pogo_info,
        })
    }

    /// Return this executable's debugging GUID, suitable for matching against a PDB file.
    pub fn guid(&self) -> Option<[u8; 16]> {
        self.codeview_pdb70_debug_info.map(|pdb70| pdb70.signature)
    }

    /// Find a specific debug type in the debug data.
    pub fn find_type(&self, data_type: u32) -> Option<ImageDebugDirectory> {
        self.entries().find_type(data_type)
    }

    /// Returns iterator for [`ImageDebugDirectory`]
    pub fn entries(&self) -> ImageDebugDirectoryIterator<'a> {
        ImageDebugDirectoryIterator {
            data: &self.data,
            rva_offset: self.rva_offset,
        }
    }
}

/// Represents the IMAGE_DEBUG_DIRECTORY structure in a Portable Executable (PE) file.
///
/// This structure holds information about the debug data in a PE file. It is used
/// to locate debug information such as PDB files or other types of debugging data.
/// The fields correspond to the Windows-specific IMAGE_DEBUG_DIRECTORY structure.
///
/// For more details, see the [Microsoft documentation](https://learn.microsoft.com/en-us/windows/win32/debug/pe-format#image-debug_directory).
///
/// <https://msdn.microsoft.com/en-us/library/windows/desktop/ms680307(v=vs.85).aspx>
#[repr(C)]
#[derive(Debug, PartialEq, Copy, Clone, Default, Pread, Pwrite, SizeWith)]
pub struct ImageDebugDirectory {
    /// The characteristics of the debug data, reserved for future use.
    pub characteristics: u32,
    /// The time and date when the debug data was created, represented as a Unix timestamp.
    pub time_date_stamp: u32,
    /// The major version number of the debug data format.
    pub major_version: u16,
    /// The minor version number of the debug data format.
    pub minor_version: u16,
    /// The type of debug data, such as codeview or coff.
    pub data_type: u32,
    /// The size of the debug data in bytes.
    pub size_of_data: u32,
    /// The address of the debug data when loaded into memory.
    pub address_of_raw_data: u32,
    /// The file pointer to the debug data within the PE file.
    pub pointer_to_raw_data: u32,
}

/// Represents an unknown debug data type.
pub const IMAGE_DEBUG_TYPE_UNKNOWN: u32 = 0;
/// Represents COFF (Common Object File Format) debug information.
pub const IMAGE_DEBUG_TYPE_COFF: u32 = 1;
/// Represents CodeView debug information, often used for PDB (Program Database) files.
pub const IMAGE_DEBUG_TYPE_CODEVIEW: u32 = 2;
/// Represents FPO (Frame Pointer Omission) information.
pub const IMAGE_DEBUG_TYPE_FPO: u32 = 3;
/// Represents miscellaneous debug information.
pub const IMAGE_DEBUG_TYPE_MISC: u32 = 4;
/// Represents exception handling information.
pub const IMAGE_DEBUG_TYPE_EXCEPTION: u32 = 5;
/// Represents fixup information, used for relocation.
pub const IMAGE_DEBUG_TYPE_FIXUP: u32 = 6;
/// Represents OMAP (Optimized Map) information from source to compiled addresses.
pub const IMAGE_DEBUG_TYPE_OMAP_TO_SRC: u32 = 7;
/// Represents OMAP information from compiled addresses to source.
pub const IMAGE_DEBUG_TYPE_OMAP_FROM_SRC: u32 = 8;
/// Represents Borland-specific debug information.
pub const IMAGE_DEBUG_TYPE_BORLAND: u32 = 9;
/// Reserved debug data type (value 10).
pub const IMAGE_DEBUG_TYPE_RESERVED10: u32 = 10;
/// Represents BBT (Basic Block Transfer) information, an alias for reserved type 10.
pub const IMAGE_DEBUG_TYPE_BBT: u32 = IMAGE_DEBUG_TYPE_RESERVED10;
/// Represents a CLSID (Class ID) associated with the debug data.
pub const IMAGE_DEBUG_TYPE_CLSID: u32 = 11;
/// Represents Visual C++ feature data.
pub const IMAGE_DEBUG_TYPE_VC_FEATURE: u32 = 12;
/// Represents POGO (Profile Guided Optimization) information.
pub const IMAGE_DEBUG_TYPE_POGO: u32 = 13;
/// Represents ILTCG (Incremental Link Time Code Generation) optimization data.
pub const IMAGE_DEBUG_TYPE_ILTCG: u32 = 14;
/// Represents MPX (Memory Protection Extensions) related debug information.
pub const IMAGE_DEBUG_TYPE_MPX: u32 = 15;
/// Represents repro information, typically used for reproducible builds.
pub const IMAGE_DEBUG_TYPE_REPRO: u32 = 16;
/// Represents an embedded Portable PDB, a .NET-specific debug information format.
pub const IMAGE_DEBUG_TYPE_EMBEDDEDPORTABLEPDB: u32 = 17;
/// Represents SPGO (Static Profile Guided Optimization) information.
pub const IMAGE_DEBUG_TYPE_SPGO: u32 = 18;
/// Represents a checksum for the PDB file.
pub const IMAGE_DEBUG_TYPE_PDBCHECKSUM: u32 = 19;
/// Represents extended DLL characteristics for debugging.
pub const IMAGE_DEBUG_TYPE_EX_DLLCHARACTERISTICS: u32 = 20;
/// Represents a performance map for profiling.
pub const IMAGE_DEBUG_TYPE_PERFMAP: u32 = 21;

/// Magic number for CodeView PDB 7.0 signature (`'SDSR'`).
pub const CODEVIEW_PDB70_MAGIC: u32 = 0x5344_5352;
/// Magic number for CodeView PDB 2.0 signature (`'01BN'`).
pub const CODEVIEW_PDB20_MAGIC: u32 = 0x3031_424e;
/// Magic number for CodeView CV 5.0 signature (`'11BN'`).
pub const CODEVIEW_CV50_MAGIC: u32 = 0x3131_424e;
/// Magic number for CodeView CV 4.1 signature (`'90BN'`).
pub const CODEVIEW_CV41_MAGIC: u32 = 0x3930_424e;

// http://llvm.org/doxygen/CVDebugRecord_8h_source.html
#[repr(C)]
#[derive(Debug, PartialEq, Copy, Clone, Default)]
pub struct CodeviewPDB70DebugInfo<'a> {
    pub codeview_signature: u32,
    pub signature: [u8; 16],
    pub age: u32,
    pub filename: &'a [u8],
}

impl<'a> CodeviewPDB70DebugInfo<'a> {
    pub fn parse(bytes: &'a [u8], idd: &ImageDebugDirectory) -> error::Result<Option<Self>> {
        Self::parse_with_opts(bytes, idd, &options::ParseOptions::default())
    }

    pub fn parse_with_opts(
        bytes: &'a [u8],
        idd: &ImageDebugDirectory,
        opts: &options::ParseOptions,
    ) -> error::Result<Option<Self>> {
        // ImageDebugDirectory.pointer_to_raw_data stores a raw offset -- not a virtual offset -- which we can use directly
        let mut offset: usize = match opts.resolve_rva {
            true => idd.pointer_to_raw_data as usize,
            false => idd.address_of_raw_data as usize,
        };

        // calculate how long the eventual filename will be, which doubles as a check of the record size
        let filename_length = idd.size_of_data as isize - 24;
        if filename_length < 0 {
            // the record is too short to be plausible
            return Err(error::Error::Malformed(format!(
                "ImageDebugDirectory size of data seems wrong: {:?}",
                idd.size_of_data
            )))
            .or_permissive_and_default(
                opts.parse_mode.is_permissive(),
                "ImageDebugDirectory size of data seems wrong",
            );
        }
        let filename_length = filename_length as usize;

        // check the codeview signature
        let codeview_signature: u32 = bytes.gread_with(&mut offset, scroll::LE)?;
        if codeview_signature != CODEVIEW_PDB70_MAGIC {
            return Ok(None);
        }

        // read the rest
        let mut signature: [u8; 16] = [0; 16];
        signature.copy_from_slice(bytes.gread_with(&mut offset, 16)?);
        let age: u32 = bytes.gread_with(&mut offset, scroll::LE)?;
        if let Some(filename) = bytes.get(offset..offset + filename_length) {
            Ok(Some(CodeviewPDB70DebugInfo {
                codeview_signature,
                signature,
                age,
                filename,
            }))
        } else {
            Err(error::Error::Malformed(format!(
                "ImageDebugDirectory seems corrupted: {:?}",
                idd
            )))
        }
    }
}

/// Represents the `IMAGE_DEBUG_VC_FEATURE_ENTRY` structure
#[repr(C)]
#[derive(Debug, PartialEq, Copy, Clone, Default)]
pub struct VCFeatureInfo {
    /// The count of pre-VC++
    pub pre_vc_plusplus_count: u32,
    /// The count of C and C++
    pub c_and_cplusplus_count: u32,
    /// The count of guard stack
    pub guard_stack_count: u32,
    /// The count of SDL
    pub sdl_count: u32,
    /// The count of guard
    pub guard_count: u32,
}

impl<'a> VCFeatureInfo {
    pub fn parse(bytes: &'a [u8], idd: &ImageDebugDirectory) -> error::Result<Self> {
        Self::parse_with_opts(bytes, idd, &options::ParseOptions::default())
    }

    pub fn parse_with_opts(
        bytes: &'a [u8],
        idd: &ImageDebugDirectory,
        opts: &options::ParseOptions,
    ) -> error::Result<Self> {
        let mut offset: usize = match opts.resolve_rva {
            true => idd.pointer_to_raw_data as usize,
            false => idd.address_of_raw_data as usize,
        };

        let pre_vc_plusplus_count: u32 = bytes.gread_with(&mut offset, scroll::LE)?;
        let c_and_cplusplus_count: u32 = bytes.gread_with(&mut offset, scroll::LE)?;
        let guard_stack_count: u32 = bytes.gread_with(&mut offset, scroll::LE)?;
        let sdl_count: u32 = bytes.gread_with(&mut offset, scroll::LE)?;
        let guard_count: u32 = bytes.gread_with(&mut offset, scroll::LE)?;

        Ok(VCFeatureInfo {
            pre_vc_plusplus_count,
            c_and_cplusplus_count,
            guard_stack_count,
            sdl_count,
            guard_count,
        })
    }
}

// http://llvm.org/doxygen/CVDebugRecord_8h_source.html
#[repr(C)]
#[derive(Debug, PartialEq, Copy, Clone, Default)]
pub struct CodeviewPDB20DebugInfo<'a> {
    pub codeview_signature: u32,
    pub codeview_offset: u32,
    pub signature: u32,
    pub age: u32,
    pub filename: &'a [u8],
}

impl<'a> CodeviewPDB20DebugInfo<'a> {
    pub fn parse(bytes: &'a [u8], idd: &ImageDebugDirectory) -> error::Result<Option<Self>> {
        Self::parse_with_opts(bytes, idd, &options::ParseOptions::default())
    }

    pub fn parse_with_opts(
        bytes: &'a [u8],
        idd: &ImageDebugDirectory,
        opts: &options::ParseOptions,
    ) -> error::Result<Option<Self>> {
        // ImageDebugDirectory.pointer_to_raw_data stores a raw offset -- not a virtual offset -- which we can use directly
        let mut offset: usize = match opts.resolve_rva {
            true => idd.pointer_to_raw_data as usize,
            false => idd.address_of_raw_data as usize,
        };

        // calculate how long the eventual filename will be, which doubles as a check of the record size
        let filename_length = idd.size_of_data as isize - 16;
        if filename_length < 0 {
            // the record is too short to be plausible
            return Err(error::Error::Malformed(format!(
                "ImageDebugDirectory size of data seems wrong: {:?}",
                idd.size_of_data
            )))
            .or_permissive_and_default(
                opts.parse_mode.is_permissive(),
                "ImageDebugDirectory size of data seems wrong",
            );
        }
        let filename_length = filename_length as usize;

        // check the codeview signature
        let codeview_signature: u32 = bytes.gread_with(&mut offset, scroll::LE)?;
        if codeview_signature != CODEVIEW_PDB20_MAGIC {
            return Ok(None);
        }
        let codeview_offset: u32 = bytes.gread_with(&mut offset, scroll::LE)?;

        // read the rest
        let signature: u32 = bytes.gread_with(&mut offset, scroll::LE)?;
        let age: u32 = bytes.gread_with(&mut offset, scroll::LE)?;
        if let Some(filename) = bytes.get(offset..offset + filename_length) {
            Ok(Some(CodeviewPDB20DebugInfo {
                codeview_signature,
                codeview_offset,
                signature,
                age,
                filename,
            }))
        } else {
            Err(error::Error::Malformed(format!(
                "ImageDebugDirectory seems corrupted: {:?}",
                idd
            )))
        }
    }
}

/// Represents the reproducible build (Repro) information extracted from a PE (Portable Executable) file.
///
/// The Repro information differs based on the compiler used to build the executable:
/// - For MSVC (Microsoft Visual C++), the Repro information is written directly into the raw data as a 32-byte hash.
/// - For Clang/(correctly, LLD linker), there is no dedicated raw data for the Repro information. Instead, the [`ImageDebugDirectory::time_date_stamp`]
///   field functions as a hash, providing a unique identifier for the reproducible build.
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum ReproInfo<'a> {
    /// Represents a hash stored in the [`ImageDebugDirectory::time_date_stamp`] field.
    ///
    /// This variant is used primarily for executables built with Clang/LLD, where the
    /// [`ImageDebugDirectory::time_date_stamp`] acts as the Repro hash.
    TimeDateStamp(u32),
    /// Represents a buffer containing the 32-byte Repro hash.
    ///
    /// This variant is used for MSVC-built executables, where the Repro hash is directly
    /// stored as raw data in the debug directory.
    Buffer {
        /// The length of the buffer containing the Repro data. For MSVC, this is typically 32 bytes long.
        length: u32,
        /// A reference to the buffer containing the Repro hash data.
        buffer: &'a [u8],
    },
}

impl<'a> ReproInfo<'a> {
    pub fn parse(bytes: &'a [u8], idd: &ImageDebugDirectory) -> error::Result<Self> {
        Self::parse_with_opts(bytes, idd, &options::ParseOptions::default())
    }

    pub fn parse_with_opts(
        bytes: &'a [u8],
        idd: &ImageDebugDirectory,
        opts: &options::ParseOptions,
    ) -> error::Result<Self> {
        let mut offset: usize = match opts.resolve_rva {
            true => idd.pointer_to_raw_data as usize,
            false => idd.address_of_raw_data as usize,
        };

        // Clang(LLD) produces no data, uses timestamp field instead
        // MSVC(link.exe) produces 32-byte data
        if idd.size_of_data > 0 {
            let length: u32 = bytes.gread_with(&mut offset, scroll::LE)?;
            if let Some(buffer) = bytes.get(offset..offset + length as usize) {
                Ok(Self::Buffer { length, buffer })
            } else {
                Err(error::Error::Malformed(format!(
                    "ImageDebugDirectory seems corrupted: {:?}",
                    idd
                )))
            }
        } else {
            Ok(Self::TimeDateStamp(idd.time_date_stamp))
        }
    }
}

/// Represents extended DLL characteristics information.
///
/// This structure holds additional characteristics of a DLL that may influence
/// how the operating system loads or manages the DLL, especially in terms of
/// security features and optimizations. These characteristics can include
/// settings related to Intel CET (Control-flow Enforcement Technology) and other
/// security-relevant attributes.
#[repr(C)]
#[derive(Debug, PartialEq, Copy, Clone, Default)]
pub struct ExDllCharacteristicsInfo {
    /// The extended characteristics of the DLL.
    ///
    /// This field is a bitmask of flags that define various security and performance
    /// properties of the DLL. The specific flags are defined by the PE format specification.
    ///
    /// This field contains one or more bitflags of:
    ///
    /// - [`IMAGE_DLLCHARACTERISTICS_EX_CET_COMPAT`]
    /// - [`IMAGE_DLLCHARACTERISTICS_EX_CET_COMPAT_STRICT_MODE`]
    /// - [`IMAGE_DLLCHARACTERISTICS_EX_CET_SET_CONTEXT_IP_VALIDATION_RELAXED_MODE`]
    /// - [`IMAGE_DLLCHARACTERISTICS_EX_CET_DYNAMIC_APIS_ALLOW_IN_PROC_ONLY`]
    /// - [`IMAGE_DLLCHARACTERISTICS_EX_CET_RESERVED_1`]
    /// - [`IMAGE_DLLCHARACTERISTICS_EX_CET_RESERVED_2`]
    /// - [`IMAGE_DLLCHARACTERISTICS_EX_FORWARD_CFI_COMPAT`]
    /// - [`IMAGE_DLLCHARACTERISTICS_EX_HOTPATCH_COMPATIBLE`]
    pub characteristics_ex: u32,
}

/// Indicates that Control Flow Enforcement Technology (CET) is enabled for the DLL,
/// enhancing security via control-flow integrity.
pub const IMAGE_DLLCHARACTERISTICS_EX_CET_COMPAT: u32 = 0x1;
/// Indicates that CET is enforced in strict mode, increasing security measures against
/// control-flow attacks but may impact compatibility.
pub const IMAGE_DLLCHARACTERISTICS_EX_CET_COMPAT_STRICT_MODE: u32 = 0x2;
/// Indicates that relaxed mode for Context IP Validation under CET is allowed,
/// providing a balance between security and performance.
pub const IMAGE_DLLCHARACTERISTICS_EX_CET_SET_CONTEXT_IP_VALIDATION_RELAXED_MODE: u32 = 0x4;
/// Indicates that the use of dynamic APIs is restricted to processes only,
/// enhancing security by limiting external API calls under CET.
pub const IMAGE_DLLCHARACTERISTICS_EX_CET_DYNAMIC_APIS_ALLOW_IN_PROC_ONLY: u32 = 0x8;
/// Reserved for future.
pub const IMAGE_DLLCHARACTERISTICS_EX_CET_RESERVED_1: u32 = 0x10;
/// Reserved for future.
pub const IMAGE_DLLCHARACTERISTICS_EX_CET_RESERVED_2: u32 = 0x20;
/// Indicates that the DLL is compatible with Forward Control Flow Integrity (CFI).
///
/// This flag signifies that the DLL is designed to support forward CFI, a security
/// feature that helps prevent certain types of control flow attacks by ensuring
/// that control flow transfers occur only to valid targets.
pub const IMAGE_DLLCHARACTERISTICS_EX_FORWARD_CFI_COMPAT: u32 = 0x40;
/// Indicates that the DLL is hotpatch-compatible.
///
/// This flag indicates that the DLL can be modified while in use (hotpatching),
/// allowing updates or fixes to be applied without needing to restart the application
/// or service that is using the DLL. This can be useful for maintaining uptime and
/// applying critical patches in a live environment.
pub const IMAGE_DLLCHARACTERISTICS_EX_HOTPATCH_COMPATIBLE: u32 = 0x80;

impl<'a> ExDllCharacteristicsInfo {
    pub fn parse(bytes: &'a [u8], idd: &ImageDebugDirectory) -> error::Result<Self> {
        Self::parse_with_opts(bytes, idd, &options::ParseOptions::default())
    }

    pub fn parse_with_opts(
        bytes: &'a [u8],
        idd: &ImageDebugDirectory,
        opts: &options::ParseOptions,
    ) -> error::Result<Self> {
        // ImageDebugDirectory.pointer_to_raw_data stores a raw offset -- not a virtual offset -- which we can use directly
        let mut offset: usize = match opts.resolve_rva {
            true => idd.pointer_to_raw_data as usize,
            false => idd.address_of_raw_data as usize,
        };

        let characteristics_ex: u32 = bytes.gread_with(&mut offset, scroll::LE)?;

        Ok(ExDllCharacteristicsInfo { characteristics_ex })
    }
}

/// Represents the POGO info structure, which provides information
/// about Profile-Guided Optimization (POGO aka PGO) data within a PE file.
///
/// PGO is a compiler optimization technique that uses data collected from program
/// execution to optimize code layout and improve runtime performance. This structure
/// contains details such as the relative virtual address (RVA), size, and the associated
/// name of the function or data block for which PGO data is provided.
///
/// <https://devblogs.microsoft.com/cppblog/pogo>
#[repr(C)]
#[derive(Debug, PartialEq, Copy, Clone, Default)]
pub struct POGOInfo<'a> {
    /// The signature of POGO debug directory entry is always first 4-bytes
    ///
    /// Either one of:
    ///
    /// - [`IMAGE_DEBUG_POGO_SIGNATURE_LTCG`]
    /// - [`IMAGE_DEBUG_POGO_SIGNATURE_PGU`]
    pub signature: u32,
    /// Raw bytes of POGO debug entry, without first 4-bytes signatures field
    pub data: &'a [u8],
}

/// Represents the `IMAGE_DEBUG_POGO_ENTRY` structure
#[derive(Debug, PartialEq, Copy, Clone, Default)]
pub struct POGOInfoEntry<'a> {
    /// The relative virtual address (RVA) of the PGO data.
    pub rva: u32,
    /// The size of the PGO data block.
    pub size: u32,
    /// The name of the function or data block associated with the PGO data as a byte slice.
    ///
    /// This may contain a null-terminated string that represents the function or block
    /// name for which PGO optimization data is provided.
    pub name: &'a [u8],
}

/// Iterator over POGO entries in [`POGOInfo`].
#[derive(Debug, Copy, Clone)]
pub struct POGOEntryIterator<'a> {
    /// The raw data of [`POGOInfo::data`] without the signature field
    data: &'a [u8],
}

/// Indicates the PGO signature for Link-Time Code Generation (LTCG) (`u32` hex representation of `'LTCG'`).
///
/// This constant is used in the `IMAGE_DEBUG_DIRECTORY` to identify sections of
/// PGO data generated specifically for LTCG optimizations.
pub const IMAGE_DEBUG_POGO_SIGNATURE_LTCG: u32 = 0x4C544347;
/// Indicates the PGO signature for Profile-Guided Optimization (PGO) updates (PGU) (`u32` hex representation of `'PGU\0'`).
///
/// This constant is used to signify sections of PGO data associated with PGO updates,
/// which are incremental optimizations based on profiling data collected over time.
pub const IMAGE_DEBUG_POGO_SIGNATURE_PGU: u32 = 0x50475500;
/// Size of [`IMAGE_DEBUG_POGO_SIGNATURE_LTCG`] or [`IMAGE_DEBUG_POGO_SIGNATURE_PGU`]
pub const POGO_SIGNATURE_SIZE: usize = core::mem::size_of::<u32>();

impl<'a> POGOInfo<'a> {
    pub fn parse(bytes: &'a [u8], idd: &ImageDebugDirectory) -> error::Result<Option<Self>> {
        Self::parse_with_opts(bytes, idd, &options::ParseOptions::default())
    }

    pub fn parse_with_opts(
        bytes: &'a [u8],
        idd: &ImageDebugDirectory,
        opts: &options::ParseOptions,
    ) -> error::Result<Option<Self>> {
        // ImageDebugDirectory.pointer_to_raw_data stores a raw offset -- not a virtual offset -- which we can use directly
        let mut offset: usize = match opts.resolve_rva {
            true => idd.pointer_to_raw_data as usize,
            false => idd.address_of_raw_data as usize,
        };

        let signature = bytes.gread_with::<u32>(&mut offset, scroll::LE)?;
        if signature != IMAGE_DEBUG_POGO_SIGNATURE_LTCG
            && signature != IMAGE_DEBUG_POGO_SIGNATURE_PGU
        {
            // This is not something we support
            return Ok(None);
        }

        if idd.size_of_data as usize <= POGO_SIGNATURE_SIZE {
            return Err(error::Error::Malformed(format!(
                "ImageDebugDirectory size_of_data {:#x} is smaller or equal to POGO_SIGNATURE_SIZE {:#x}",
                idd.size_of_data, POGO_SIGNATURE_SIZE
            )));
        }

        let offset_end = offset
            .checked_add(idd.size_of_data as usize - POGO_SIGNATURE_SIZE)
            .ok_or_else(|| {
                error::Error::Malformed(format!(
                    "ImageDebugDirectory offset ({:#x}) and size ({:#x}) cause an integer overflow",
                    offset,
                    idd.size_of_data as usize - POGO_SIGNATURE_SIZE
                ))
            })?;

        if offset > bytes.len() || offset_end > bytes.len() {
            return Err(error::Error::Malformed(format!(
                "ImageDebugDirectory offset_start {:#x} or offset_end {:#x} exceed the bounds of the bytes size {:#x}",
                offset,
                offset_end,
                bytes.len()
            )));
        }

        let data = &bytes[offset..offset_end];
        Ok(Some(POGOInfo { signature, data }))
    }

    /// Returns iterator for [`POGOInfoEntry`]
    pub fn entries(&self) -> POGOEntryIterator<'a> {
        POGOEntryIterator { data: &self.data }
    }
}

impl<'a> Iterator for POGOEntryIterator<'a> {
    type Item = error::Result<POGOInfoEntry<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.data.is_empty() {
            return None;
        }

        let mut offset = 0;
        let rva = match self.data.gread_with::<u32>(&mut offset, scroll::LE) {
            Ok(rva) => rva,
            Err(error) => return Some(Err(error.into())),
        };
        let size = match self.data.gread_with::<u32>(&mut offset, scroll::LE) {
            Ok(size) => size,
            Err(error) => return Some(Err(error.into())),
        };

        // Use >= to avoid empty slice, that we want to emit an error early here for
        // malformed name in a POGO entry.
        if offset >= self.data.len() {
            return Some(Err(error::Error::Malformed(format!(
                "Offset {offset:#x} is too big for containing name field of POGO entry (rva {rva:#x} and size {size:#X})",
            ))));
        }
        let name = match self.data[offset..].iter().position(|&b| b == 0) {
            Some(pos) => {
                // + 1 nul
                let Some(name) = self.data.gread_with::<&[u8]>(&mut offset, pos + 1).ok() else {
                    return Some(Err(error::Error::Malformed(format!(
                        "Null-terminator for POGO entry (rva {rva:#x} and size {size:#X}) found but exceeds iterator buffer",
                    ))));
                };
                // Round up to the nearest multiple of 4
                offset = (offset + 3) & !3;
                name
            }
            None => {
                return Some(Err(error::Error::Malformed(format!(
                    "Cannot find null-terminator for POGO entry (rva {rva:#x} and size {size:#X})",
                ))
                .into()));
            }
        };

        if offset > self.data.len() {
            return Some(Err(error::Error::Malformed(format!(
                "Offset {offset:#x} exceeds buffer length {:#x}",
                self.data.len()
            ))));
        }
        self.data = &self.data[offset..];
        Some(Ok(POGOInfoEntry { rva, size, name }))
    }
}

impl FusedIterator for POGOEntryIterator<'_> {}

#[cfg(test)]
mod tests {
    use super::{
        CODEVIEW_PDB70_MAGIC, ExDllCharacteristicsInfo, IMAGE_DEBUG_POGO_SIGNATURE_LTCG,
        IMAGE_DEBUG_TYPE_CODEVIEW, IMAGE_DEBUG_TYPE_EX_DLLCHARACTERISTICS, IMAGE_DEBUG_TYPE_ILTCG,
        IMAGE_DEBUG_TYPE_POGO, IMAGE_DEBUG_TYPE_REPRO, IMAGE_DEBUG_TYPE_VC_FEATURE,
        IMAGE_DLLCHARACTERISTICS_EX_CET_COMPAT, IMAGE_DLLCHARACTERISTICS_EX_CET_COMPAT_STRICT_MODE,
        ImageDebugDirectory, POGO_SIGNATURE_SIZE, POGOEntryIterator, POGOInfoEntry, ReproInfo,
        VCFeatureInfo,
    };

    const NO_DEBUG_DIRECTORIES_BIN: &[u8] =
        include_bytes!("../../tests/bins/pe/no_debug_directories.exe.bin");
    const DEBUG_DIRECTORIES_TEST_MSVC_BIN: &[u8] =
        include_bytes!("../../tests/bins/pe/debug_directories-msvc.exe.bin");
    const DEBUG_DIRECTORIES_TEST_CLANG_LLD_BIN: &[u8] =
        include_bytes!("../../tests/bins/pe/debug_directories-clang_lld.exe.bin");

    fn ffi_to_string(bytes: &[u8]) -> String {
        unsafe { std::ffi::CStr::from_bytes_with_nul_unchecked(bytes) }
            .to_string_lossy()
            .to_string()
    }

    #[test]
    fn parse_no_debug_directories() {
        let binary =
            crate::pe::PE::parse(NO_DEBUG_DIRECTORIES_BIN).expect("Unable to parse binary");
        assert_eq!(binary.debug_data.is_none(), true);
    }

    #[test]
    fn parse_debug_entries_iterator() {
        let binary =
            crate::pe::PE::parse(DEBUG_DIRECTORIES_TEST_MSVC_BIN).expect("Unable to parse binary");
        assert_eq!(binary.debug_data.is_some(), true);
        let debug_data = binary.debug_data.unwrap();
        let entries = debug_data.entries().collect::<Result<Vec<_>, _>>();
        assert_eq!(entries.is_ok(), true);
        let entries = entries.unwrap();
        let entries_expect = vec![
            ImageDebugDirectory {
                characteristics: 0x0,
                time_date_stamp: 0x80AC7661,
                major_version: 0x0,
                minor_version: 0x0,
                data_type: IMAGE_DEBUG_TYPE_CODEVIEW,
                size_of_data: 0x38,
                address_of_raw_data: 0x20c0,
                pointer_to_raw_data: 0x4c0,
            },
            ImageDebugDirectory {
                characteristics: 0x0,
                time_date_stamp: 0x80AC7661,
                major_version: 0x0,
                minor_version: 0x0,
                data_type: IMAGE_DEBUG_TYPE_VC_FEATURE,
                size_of_data: 0x14,
                address_of_raw_data: 0x20f8,
                pointer_to_raw_data: 0x4f8,
            },
            ImageDebugDirectory {
                characteristics: 0x0,
                time_date_stamp: 0x80AC7661,
                major_version: 0x0,
                minor_version: 0x0,
                data_type: IMAGE_DEBUG_TYPE_POGO,
                size_of_data: 0x58,
                address_of_raw_data: 0x210c,
                pointer_to_raw_data: 0x50c,
            },
            ImageDebugDirectory {
                characteristics: 0x0,
                time_date_stamp: 0x80AC7661,
                major_version: 0x0,
                minor_version: 0x0,
                data_type: IMAGE_DEBUG_TYPE_ILTCG,
                size_of_data: 0x0,
                address_of_raw_data: 0x0,
                pointer_to_raw_data: 0x0,
            },
            ImageDebugDirectory {
                characteristics: 0x0,
                time_date_stamp: 0x80AC7661,
                major_version: 0x0,
                minor_version: 0x0,
                data_type: IMAGE_DEBUG_TYPE_REPRO,
                size_of_data: 0x24,
                address_of_raw_data: 0x2164,
                pointer_to_raw_data: 0x564,
            },
            ImageDebugDirectory {
                characteristics: 0x0,
                time_date_stamp: 0x80AC7661,
                major_version: 0x0,
                minor_version: 0x0,
                data_type: IMAGE_DEBUG_TYPE_EX_DLLCHARACTERISTICS,
                size_of_data: 0x4,
                address_of_raw_data: 0x2188,
                pointer_to_raw_data: 0x588,
            },
        ];
        assert_eq!(entries, entries_expect);
    }

    #[test]
    fn parse_debug_codeview_pdb70_msvc() {
        let binary =
            crate::pe::PE::parse(DEBUG_DIRECTORIES_TEST_MSVC_BIN).expect("Unable to parse binary");
        assert_eq!(binary.debug_data.is_some(), true);
        let debug_data = binary.debug_data.unwrap();
        assert_eq!(debug_data.codeview_pdb70_debug_info.is_some(), true);
        let codeview_pdb70_debug_info = debug_data.codeview_pdb70_debug_info.unwrap();
        let filename = ffi_to_string(codeview_pdb70_debug_info.filename);
        assert_eq!(filename, String::from("THIS-IS-BINARY-FOR-GOBLIN-TESTS"));
        assert_eq!(codeview_pdb70_debug_info.age, 3);
        assert_eq!(
            codeview_pdb70_debug_info.codeview_signature,
            CODEVIEW_PDB70_MAGIC
        );
        assert_eq!(
            codeview_pdb70_debug_info.signature,
            [
                0x1F, 0x4F, 0x58, 0x9C, 0x3C, 0xEA, 0x00, 0x83, 0x3F, 0x57, 0x00, 0xCC, 0x36, 0xA7,
                0x84, 0xDF,
            ]
        );
    }

    #[test]
    fn parse_debug_codeview_pdb70_clang() {
        let binary = crate::pe::PE::parse(DEBUG_DIRECTORIES_TEST_CLANG_LLD_BIN)
            .expect("Unable to parse binary");
        assert_eq!(binary.debug_data.is_some(), true);
        let debug_data = binary.debug_data.unwrap();
        assert_eq!(debug_data.codeview_pdb70_debug_info.is_some(), true);
        let codeview_pdb70_debug_info = debug_data.codeview_pdb70_debug_info.unwrap();
        let filename = ffi_to_string(codeview_pdb70_debug_info.filename);
        assert_eq!(filename, String::from("THIS-IS-BINARY-FOR-GOBLIN-TESTS"));
        assert_eq!(codeview_pdb70_debug_info.age, 1);
        assert_eq!(
            codeview_pdb70_debug_info.codeview_signature,
            CODEVIEW_PDB70_MAGIC
        );
        assert_eq!(
            codeview_pdb70_debug_info.signature,
            [
                0xC8, 0xBA, 0xF6, 0xAB, 0xB2, 0x98, 0xD1, 0x9E, 0x4C, 0x4C, 0x44, 0x20, 0x50, 0x44,
                0x42, 0x2E,
            ]
        );
    }

    #[test]
    fn parse_debug_vcfeature() {
        let binary =
            crate::pe::PE::parse(DEBUG_DIRECTORIES_TEST_MSVC_BIN).expect("Unable to parse binary");
        assert_eq!(binary.debug_data.is_some(), true);
        let debug_data = binary.debug_data.unwrap();
        assert_eq!(debug_data.vcfeature_info.is_some(), true);
        let vcfeature_info = debug_data.vcfeature_info.unwrap();
        let vcfeature_info_expect = VCFeatureInfo {
            pre_vc_plusplus_count: 0,
            c_and_cplusplus_count: 1,
            guard_stack_count: 0,
            sdl_count: 0,
            guard_count: 0,
        };
        assert_eq!(vcfeature_info, vcfeature_info_expect);
    }

    #[test]
    fn parse_debug_repro_msvc() {
        let binary =
            crate::pe::PE::parse(DEBUG_DIRECTORIES_TEST_MSVC_BIN).expect("Unable to parse binary");
        assert_eq!(binary.debug_data.is_some(), true);
        let debug_data = binary.debug_data.unwrap();
        assert_eq!(debug_data.repro_info.is_some(), true);
        let repro_info = debug_data.repro_info.unwrap();
        let repro_info_expect = ReproInfo::Buffer {
            length: 32,
            buffer: &[
                0x1F, 0x4F, 0x58, 0x9C, 0x3C, 0xEA, 0x00, 0x83, 0x3F, 0x57, 0x00, 0xCC, 0x36, 0xA7,
                0x84, 0xDF, 0xF7, 0x7C, 0x70, 0xE0, 0xEF, 0x7A, 0xBA, 0x08, 0xD0, 0xA6, 0x8B, 0x7F,
                0x61, 0x76, 0xAC, 0x80,
            ],
        };
        assert_eq!(repro_info, repro_info_expect);
    }

    #[test]
    fn parse_debug_repro_clang_lld() {
        let binary = crate::pe::PE::parse(DEBUG_DIRECTORIES_TEST_CLANG_LLD_BIN)
            .expect("Unable to parse binary");
        assert_eq!(binary.debug_data.is_some(), true);
        let debug_data = binary.debug_data.unwrap();
        assert_eq!(debug_data.repro_info.is_some(), true);
        let repro_info = debug_data.repro_info.unwrap();
        let repro_info_expect = ReproInfo::TimeDateStamp(0xDB2F3908);
        assert_eq!(repro_info, repro_info_expect);
    }

    #[test]
    fn parse_debug_exdllcharacteristics() {
        let binary =
            crate::pe::PE::parse(DEBUG_DIRECTORIES_TEST_MSVC_BIN).expect("Unable to parse binary");
        assert_eq!(binary.debug_data.is_some(), true);
        let debug_data = binary.debug_data.unwrap();
        assert_eq!(debug_data.ex_dll_characteristics_info.is_some(), true);
        let ex_dll_characteristics_info = debug_data.ex_dll_characteristics_info.unwrap();
        let ex_dll_characteristics_info_expect = ExDllCharacteristicsInfo {
            characteristics_ex: IMAGE_DLLCHARACTERISTICS_EX_CET_COMPAT
                | IMAGE_DLLCHARACTERISTICS_EX_CET_COMPAT_STRICT_MODE,
        };
        assert_eq!(
            ex_dll_characteristics_info,
            ex_dll_characteristics_info_expect
        );
    }

    #[test]
    fn parse_debug_pogo() {
        let binary =
            crate::pe::PE::parse(DEBUG_DIRECTORIES_TEST_MSVC_BIN).expect("Unable to parse binary");
        assert_eq!(binary.debug_data.is_some(), true);
        let debug_data = binary.debug_data.unwrap();
        assert_eq!(debug_data.pogo_info.is_some(), true);
        let pogo_info = debug_data.pogo_info.unwrap();
        assert_eq!(pogo_info.signature, IMAGE_DEBUG_POGO_SIGNATURE_LTCG);
        assert_eq!(pogo_info.data.len(), 88 - POGO_SIGNATURE_SIZE);
        let entries = pogo_info.entries().collect::<Result<Vec<_>, _>>().unwrap();
        let entries_expect = vec![
            POGOInfoEntry {
                rva: 0x1000,
                size: 0x3,
                name: b".text$mn\0",
            },
            POGOInfoEntry {
                rva: 0x2000,
                size: 0xA8,
                name: b".rdata\0",
            },
            POGOInfoEntry {
                rva: 0x20A8,
                size: 0x18,
                name: b".rdata$voltmd\0",
            },
            POGOInfoEntry {
                rva: 0x20C0,
                size: 0xCC,
                name: b".rdata$zzzdbg\0",
            },
        ];
        assert_eq!(entries, entries_expect);
    }

    #[rustfmt::skip]
    const MALFORMED_POGO_NAME: &[u8; 83] = &[
        // Entry 1: .text$mn
        0x00, 0x10, 0x00, 0x00, // RVA: 0x00001000
        0x03, 0x00, 0x00, 0x00, // Size: 0x00000003
        0x2e, 0x74, 0x65, 0x78, // Name: ".text$mn\0"
        0x74, 0x24, 0x6d, 0x6e,
        0x00, 0x00, 0x00, 0x00,
        // Entry 2: .rdata
        0x00, 0x20, 0x00, 0x00, // RVA: 0x00002000
        0xa8, 0x00, 0x00, 0x00, // Size: 0x000000A8
        0x2e, 0x72, 0x64, 0x61, // Name: ".rdata\0"
        0x74, 0x61, 0x00, 0x00,
        // Entry 3: .rdata$voltmd
        0xa8, 0x20, 0x00, 0x00, // RVA: 0x000020A8
        0x18, 0x00, 0x00, 0x00, // Size: 0x00000018
        0x2e, 0x72, 0x64, 0x61, // Name: ".rdata$voltmd\0"
        0x74, 0x61, 0x24, 0x76,
        0x6f, 0x6c, 0x74, 0x6d,
        0x64, 0x00, 0x00, 0x00,
        // Entry 4: .rdata$zzzdbg
        0xc0, 0x20, 0x00, 0x00, // RVA: 0x000020C0
        0xcc, 0x00, 0x00, 0x00, // Size: 0x000000CC
        0x2e, 0x72, 0x64, 0x61, // Name: ".rdata$zzzdbg\0"
        0x74, 0x61, 0x24, 0x7a,
        0x7a, 0x7a, 0x64, 0x62,
        0x67, 0x00, 0x00, /* truncated 0x00 */
    ];

    #[test]
    #[should_panic = "Malformed(\"Offset 0x18 exceeds buffer length 0x17\")"]
    fn parse_debug_pogo_malformed_name() {
        let entries = POGOEntryIterator {
            data: MALFORMED_POGO_NAME,
        };
        let _ = entries.collect::<Result<Vec<_>, _>>().unwrap();
    }
}
