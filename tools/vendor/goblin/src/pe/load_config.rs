use scroll::ctx;
use scroll::{Pread, Pwrite, SizeWith};

use crate::container::{Container, Ctx};
use crate::error;
use crate::pe::data_directories;
use crate::pe::options;
use crate::pe::section_table;
use crate::pe::utils;
use log;

// GuardFlags: bitflags for LoadConfigDirectory::guard_flags.

/// Indicate that the module performs control flow integrity checks using system-supplied support.
pub const IMAGE_GUARD_CF_INSTRUMENTED: u32 = 0x0000_0100;
/// Indicate that the module performs control flow and write integrity checks.
pub const IMAGE_GUARD_CFW_INSTRUMENTED: u32 = 0x0000_0200;
/// Indicate that the module contains valid control flow target metadata.
pub const IMAGE_GUARD_CF_FUNCTION_TABLE_PRESENT: u32 = 0x0000_0400;
/// Indicate that the module does not make use of the /GS security cookie.
pub const IMAGE_GUARD_SECURITY_COOKIE_UNUSED: u32 = 0x0000_0800;
/// Indicate that the module supports read-only delay load IAT.
pub const IMAGE_GUARD_PROTECT_DELAYLOAD_IAT: u32 = 0x0000_1000;
/// Indicate that the delay-load import table is in its own .didat section that can be freely reprotected.
pub const IMAGE_GUARD_DELAYLOAD_IAT_IN_ITS_OWN_SECTION: u32 = 0x0000_2000;
/// Indicate that the module contains suppressed export information and the address-taken IAT table is present.
pub const IMAGE_GUARD_CF_EXPORT_SUPPRESSION_INFO_PRESENT: u32 = 0x0000_4000;
/// Indicate that the module enables suppression of exports.
pub const IMAGE_GUARD_CF_ENABLE_EXPORT_SUPPRESSION: u32 = 0x0000_8000;
/// Indicate that the module contains longjmp target information.
pub const IMAGE_GUARD_CF_LONGJUMP_TABLE_PRESENT: u32 = 0x0001_0000;
/// Indicate that the module contains return flow instrumentation and metadata.
pub const IMAGE_GUARD_RF_INSTRUMENTED: u32 = 0x0002_0000;
/// Indicate that the module requests the OS to enable return flow protection.
pub const IMAGE_GUARD_RF_ENABLE: u32 = 0x0004_0000;
/// Indicate that the module requests the OS to enable return flow protection in strict mode.
pub const IMAGE_GUARD_RF_STRICT: u32 = 0x0008_0000;
/// Indicate that the module was built with retpoline support.
pub const IMAGE_GUARD_RETPOLINE_PRESENT: u32 = 0x0010_0000;
/// Indicate that the module contains EH continuation target information.
pub const IMAGE_GUARD_EH_CONTINUATION_TABLE_PRESENT: u32 = 0x0040_0000;
/// Indicate that the module was built with XFG (Cross Function Guard), now deprecated.
pub const IMAGE_GUARD_XFG_ENABLED: u32 = 0x0080_0000;
/// Indicate that the module has CastGuard instrumentation present.
pub const IMAGE_GUARD_CASTGUARD_PRESENT: u32 = 0x0100_0000;
/// Indicate that the module has Guarded Memcpy instrumentation present.
pub const IMAGE_GUARD_MEMCPY_PRESENT: u32 = 0x0200_0000;

// DependentLoadFlags: bitflags for LoadConfigDirectory::dependent_load_flags.

/// Indicate that the system does not resolve DLL references for the loaded module.
pub const DONT_RESOLVE_DLL_REFERENCES: u32 = 0x0000_0001;
/// Indicate that the DLL is loaded as a data file.
pub const LOAD_LIBRARY_AS_DATAFILE: u32 = 0x0000_0002;
/// Indicate that the DLL is loaded as a packaged library.
pub const LOAD_PACKAGED_LIBRARY: u32 = 0x0000_0004;
/// Indicate that the DLL is loaded with an altered search path.
pub const LOAD_WITH_ALTERED_SEARCH_PATH: u32 = 0x0000_0008;
/// Indicate that the system ignores the code authorization level.
pub const LOAD_IGNORE_CODE_AUTHZ_LEVEL: u32 = 0x0000_0010;
/// Indicate that the DLL is loaded as an image resource.
pub const LOAD_LIBRARY_AS_IMAGE_RESOURCE: u32 = 0x0000_0020;
/// Indicate that the DLL is loaded as a data file and cannot be loaded again as an executable.
pub const LOAD_LIBRARY_AS_DATAFILE_EXCLUSIVE: u32 = 0x0000_0040;
/// Indicate that the DLL target must be signed.
pub const LOAD_LIBRARY_REQUIRE_SIGNED_TARGET: u32 = 0x0000_0080;
/// Indicate that the system searches the directory that contains the DLL being loaded.
pub const LOAD_LIBRARY_SEARCH_DLL_LOAD_DIR: u32 = 0x0000_0100;
/// Indicate that the system searches the application directory.
pub const LOAD_LIBRARY_SEARCH_APPLICATION_DIR: u32 = 0x0000_0200;
/// Indicate that the system searches directories added with `AddDllDirectory`.
pub const LOAD_LIBRARY_SEARCH_USER_DIRS: u32 = 0x0000_0400;
/// Indicate that the system searches the System32 directory.
pub const LOAD_LIBRARY_SEARCH_SYSTEM32: u32 = 0x0000_0800;
/// Indicate that the system uses the default DLL search directories.
pub const LOAD_LIBRARY_SEARCH_DEFAULT_DIRS: u32 = 0x0000_1000;
/// Indicate that the current directory is searched only when it is safe to do so.
pub const LOAD_LIBRARY_SAFE_CURRENT_DIRS: u32 = 0x0000_2000;
/// Indicate that the system searches System32 without resolving forwarded exports.
///
/// This value may not be supported on older versions of Windows.
pub const LOAD_LIBRARY_SEARCH_SYSTEM32_NO_FORWARDER: u32 = 0x0000_4000;
/// Indicate that the system uses OS integrity continuity policies when loading the DLL.
pub const LOAD_LIBRARY_OS_INTEGRITY_CONTINUITY: u32 = 0x0000_8000;

/// Represents the 32/64-bit Load Configuration directory structure of a PE file.
///
/// This structure contains information related to the loading configuration
/// of a PE (Portable Executable) file. It provides details for various
/// configuration settings that the operating system loader may use when loading
/// the PE file into memory. This structure is marked as non_exhaustive, meaning
/// that future versions of the PE format may include additional fields that are
/// not present in the current version of this structure.
///
/// # Notes
///
/// This structure may grow in future versions of the PE format, so be cautious
/// when working with it, as some fields may not be available or relevant for
/// all versions of PE files.
#[non_exhaustive]
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct LoadConfigDirectory {
    /// The size of the structure.
    pub size: u32,
    /// The date and time stamp value.
    ///
    /// The value is represented in the number of seconds elapsed since midnight
    /// (00:00:00), January 1, 1970, Universal Coordinated Time, according to the
    /// system clock.
    pub time_stamp: Option<u32>,
    /// The major version number.
    pub major_version: Option<u16>,
    /// The minor version number.
    pub minor_version: Option<u16>,
    /// Global flags to clear.
    pub global_flags_clear: Option<u32>,
    /// Global flags to set.
    pub global_flags_set: Option<u32>,
    /// Default timeout value for critical sections.
    pub critical_section_default_timeout: Option<u32>,
    /// Threshold for decommitting free blocks.
    pub de_commit_free_block_threshold: Option<u64>,
    /// Total threshold for decommitting memory.
    pub de_commit_total_free_threshold: Option<u64>,
    /// Virtual address of the lock prefix table.
    pub lock_prefix_table: Option<u64>,
    /// Maximum allocation size allowed.
    pub maximum_allocation_size: Option<u64>,
    /// Threshold for allocating virtual memory.
    pub virtual_memory_threshold: Option<u64>,
    /// Process affinity mask.
    pub process_affinity_mask: Option<u64>,
    /// Heap flags for the process.
    pub process_heap_flags: Option<u32>,
    /// Service pack version (CSD Version).
    pub csd_version: Option<u16>,
    /// Dependent load flags.
    pub dependent_load_flags: Option<u16>,
    /// Virtual address of the edit list.
    pub edit_list: Option<u64>,
    /// Virtual address of the security cookie.
    pub security_cookie: Option<u64>,
    /// Virtual address of the SE handler table.
    pub se_handler_table: Option<u64>,
    /// Count of SE handlers.
    pub se_handler_count: Option<u64>,
    /// Virtual address of the Guard CF check function pointer.
    pub guard_cf_check_function_pointer: Option<u64>,
    /// Virtual address of the Guard CF dispatch function pointer.
    pub guard_cf_dispatch_function_pointer: Option<u64>,
    /// Virtual address of the Guard CF function table.
    pub guard_cf_function_table: Option<u64>,
    /// Count of Guard CF functions.
    pub guard_cf_function_count: Option<u64>,
    /// Flags related to Control Flow Guard (CFG).
    pub guard_flags: Option<u32>,
    /// Code integrity configuration.
    pub code_integrity: Option<LoadConfigCodeIntegrity>,
    /// Virtual address of the Guard address-taken IAT entry table.
    pub guard_address_taken_iat_entry_table: Option<u64>,
    /// Count of Guard address-taken IAT entries.
    pub guard_address_taken_iat_entry_count: Option<u64>,
    /// Virtual address of the Guard long jump target table.
    pub guard_long_jump_target_table: Option<u64>,
    /// Count of Guard long jump targets.
    pub guard_long_jump_target_count: Option<u64>,
    /// Virtual address of the dynamic value relocation table.
    pub dynamic_value_reloc_table: Option<u64>,
    /// Virtual address of the CHPE metadata.
    pub chpe_metadata_pointer: Option<u64>,
    /// Virtual address of the Guard RF failure routine.
    pub guard_rf_failure_routine: Option<u64>,
    /// Virtual address of the Guard RF failure routine function pointer.
    pub guard_rf_failure_routine_function_pointer: Option<u64>,
    /// Offset of the dynamic value relocation table.
    pub dynamic_value_reloc_table_offset: Option<u32>,
    /// Section index of the dynamic value relocation table.
    pub dynamic_value_reloc_table_section: Option<u16>,
    /// Reserved field.
    pub reserved2: Option<u16>,
    /// Virtual address of the Guard RF verify stack pointer function pointer.
    pub guard_rf_verify_stack_pointer_function_pointer: Option<u64>,
    /// Offset to the hot patch table.
    pub hot_patch_table_offset: Option<u32>,
    /// Reserved field.
    pub reserved3: Option<u32>,
    /// Virtual address of the enclave configuration pointer.
    pub enclave_configuration_pointer: Option<u64>,
    /// Virtual address of the volatile metadata pointer.
    pub volatile_metadata_pointer: Option<u64>,
    /// Virtual address of the Guard EH continuation table.
    pub guard_eh_continuation_table: Option<u64>,
    /// Count of Guard EH continuations.
    pub guard_eh_continuation_count: Option<u64>,
    /// Virtual address of the Guard XFG check function pointer.
    pub guard_xfg_check_function_pointer: Option<u64>,
    /// Virtual address of the Guard XFG dispatch function pointer.
    pub guard_xfg_dispatch_function_pointer: Option<u64>,
    /// Virtual address of the Guard XFG table dispatch function pointer.
    pub guard_xfg_table_dispatch_function_pointer: Option<u64>,
    /// Virtual address of the CASTGuard OS-determined failure mode handler.
    pub cast_guard_os_determined_failure_mode: Option<u64>,
    /// Virtual address of the Guard memcpy function pointer.
    pub guard_memcpy_function_pointer: Option<u64>,
}

impl<'a> ctx::TryFromCtx<'a, Ctx> for LoadConfigDirectory {
    type Error = crate::error::Error;
    fn try_from_ctx(bytes: &'a [u8], ctx: Ctx) -> error::Result<(Self, usize)> {
        // `size` field must be present
        if bytes.len() < 4 {
            return Err(error::Error::Malformed(format!("Too small")));
        }

        let is_64 = ctx.is_big();
        let mut offset = 0;

        let read_arch_dependent_u64 = |offset: &mut usize| {
            if is_64 {
                bytes.gread_with(offset, scroll::LE).ok()
            } else {
                bytes
                    .gread_with::<u32>(offset, scroll::LE)
                    .map(Into::into)
                    .ok()
            }
        };

        let out = Self {
            size: bytes.gread_with(&mut offset, scroll::LE)?,
            time_stamp: bytes.gread_with(&mut offset, scroll::LE).ok(),
            major_version: bytes.gread_with(&mut offset, scroll::LE).ok(),
            minor_version: bytes.gread_with(&mut offset, scroll::LE).ok(),
            global_flags_clear: bytes.gread_with(&mut offset, scroll::LE).ok(),
            global_flags_set: bytes.gread_with(&mut offset, scroll::LE).ok(),
            critical_section_default_timeout: bytes.gread_with(&mut offset, scroll::LE).ok(),
            de_commit_free_block_threshold: read_arch_dependent_u64(&mut offset),
            de_commit_total_free_threshold: read_arch_dependent_u64(&mut offset),
            lock_prefix_table: read_arch_dependent_u64(&mut offset),
            maximum_allocation_size: read_arch_dependent_u64(&mut offset),
            virtual_memory_threshold: read_arch_dependent_u64(&mut offset),
            process_affinity_mask: read_arch_dependent_u64(&mut offset),
            process_heap_flags: bytes.gread_with(&mut offset, scroll::LE).ok(),
            csd_version: bytes.gread_with(&mut offset, scroll::LE).ok(),
            dependent_load_flags: bytes.gread_with(&mut offset, scroll::LE).ok(),
            edit_list: read_arch_dependent_u64(&mut offset),
            security_cookie: read_arch_dependent_u64(&mut offset),
            se_handler_table: read_arch_dependent_u64(&mut offset),
            se_handler_count: read_arch_dependent_u64(&mut offset),
            guard_cf_check_function_pointer: read_arch_dependent_u64(&mut offset),
            guard_cf_dispatch_function_pointer: read_arch_dependent_u64(&mut offset),
            guard_cf_function_table: read_arch_dependent_u64(&mut offset),
            guard_cf_function_count: read_arch_dependent_u64(&mut offset),
            guard_flags: bytes.gread_with(&mut offset, scroll::LE).ok(),
            code_integrity: bytes.gread_with(&mut offset, scroll::LE).ok(),
            guard_address_taken_iat_entry_table: read_arch_dependent_u64(&mut offset),
            guard_address_taken_iat_entry_count: read_arch_dependent_u64(&mut offset),
            guard_long_jump_target_table: read_arch_dependent_u64(&mut offset),
            guard_long_jump_target_count: read_arch_dependent_u64(&mut offset),
            dynamic_value_reloc_table: read_arch_dependent_u64(&mut offset),
            chpe_metadata_pointer: read_arch_dependent_u64(&mut offset),
            guard_rf_failure_routine: read_arch_dependent_u64(&mut offset),
            guard_rf_failure_routine_function_pointer: read_arch_dependent_u64(&mut offset),
            dynamic_value_reloc_table_offset: bytes.gread_with(&mut offset, scroll::LE).ok(),
            dynamic_value_reloc_table_section: bytes.gread_with(&mut offset, scroll::LE).ok(),
            reserved2: bytes.gread_with(&mut offset, scroll::LE).ok(),
            guard_rf_verify_stack_pointer_function_pointer: read_arch_dependent_u64(&mut offset),
            hot_patch_table_offset: bytes.gread_with(&mut offset, scroll::LE).ok(),
            reserved3: bytes.gread_with(&mut offset, scroll::LE).ok(),
            enclave_configuration_pointer: read_arch_dependent_u64(&mut offset),
            volatile_metadata_pointer: read_arch_dependent_u64(&mut offset),
            guard_eh_continuation_table: read_arch_dependent_u64(&mut offset),
            guard_eh_continuation_count: read_arch_dependent_u64(&mut offset),
            guard_xfg_check_function_pointer: read_arch_dependent_u64(&mut offset),
            guard_xfg_dispatch_function_pointer: read_arch_dependent_u64(&mut offset),
            guard_xfg_table_dispatch_function_pointer: read_arch_dependent_u64(&mut offset),
            cast_guard_os_determined_failure_mode: read_arch_dependent_u64(&mut offset),
            guard_memcpy_function_pointer: read_arch_dependent_u64(&mut offset),
        };

        Ok((out, offset))
    }
}

/// Represents the code integrity configuration used in load configuration.
#[repr(C)]
#[derive(Debug, Clone, Pread, Pwrite, SizeWith, Eq, PartialEq)]
pub struct LoadConfigCodeIntegrity {
    /// Flags indicating code integrity options.
    pub flags: u16,
    /// Catalog index.
    pub catalog: u16,
    /// Offset to the catalog.
    pub catalog_offset: u32,
    /// Reserved field.
    pub reserved: u32,
}

/// Represents a PE load config directory data.
#[derive(Debug, PartialEq, Clone, Default)]
pub struct LoadConfigData {
    /// Parsed load config directory.
    pub directory: LoadConfigDirectory,
}

impl LoadConfigData {
    pub fn parse(
        bytes: &[u8],
        dd: data_directories::DataDirectory,
        sections: &[section_table::SectionTable],
        file_alignment: u32,
        is_64: bool,
    ) -> error::Result<Self> {
        Self::parse_with_opts(
            bytes,
            dd,
            sections,
            file_alignment,
            &options::ParseOptions::default(),
            is_64,
        )
    }

    pub fn parse_with_opts(
        bytes: &[u8],
        dd: data_directories::DataDirectory,
        sections: &[section_table::SectionTable],
        file_alignment: u32,
        opts: &options::ParseOptions,
        is_64: bool,
    ) -> error::Result<Self> {
        let offset =
            utils::find_offset(dd.virtual_address as usize, sections, file_alignment, opts)
                .ok_or_else(|| {
                    error::Error::Malformed(format!(
                        "Cannot map load config rva {:#x} into offset",
                        dd.virtual_address
                    ))
                })?;

        log::debug!(
            "LoadConfig parsing: offset={:#x}, dd.size={:#x}, total_bytes_len={:#x}, remaining_bytes_from_offset={:#x}",
            offset,
            dd.size,
            bytes.len(),
            bytes.len().saturating_sub(offset)
        );
        let bytes = bytes
            .pread_with::<&[u8]>(offset, dd.size as usize)
            .map_err(|_| {
                error::Error::Malformed(format!(
                    "load config offset {:#x} and size {:#x} exceeds the bounds of the bytes size {:#x}",
                    offset,
                    dd.size,
                    bytes.len()
                ))
            })?;
        log::debug!(
            "LoadConfig bytes slice created successfully, length={}",
            bytes.len()
        );

        let ctx = Ctx::new(
            if is_64 {
                Container::Big
            } else {
                Container::Little
            },
            scroll::LE,
        );
        let directory = bytes.pread_with(0, ctx)?;

        Ok(Self { directory })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const LOADCONFIG64_DATA0: &[u8; 320] = &[
        0x40, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x98, 0x45,
        0x1E, 0x80, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x18, 0x12, 0x1E, 0x80, 0x01, 0x00, 0x00, 0x00,
        0x00, 0x50, 0x1E, 0x80, 0x01, 0x00, 0x00, 0x00, 0xA0, 0x02, 0x17, 0x80, 0x01, 0x00, 0x00,
        0x00, 0x87, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x75, 0x41, 0x10, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xA0,
        0x06, 0x00, 0x00, 0x0F, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x38, 0xFF, 0x16, 0x80, 0x01, 0x00,
        0x00, 0x00, 0xAE, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x08, 0x50, 0x1E, 0x80, 0x01,
        0x00, 0x00, 0x00, 0x10, 0x50, 0x1E, 0x80, 0x01, 0x00, 0x00, 0x00, 0x18, 0x50, 0x1E, 0x80,
        0x01, 0x00, 0x00, 0x00, 0x20, 0x50, 0x1E, 0x80, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00,
    ];

    const LOADCONFIG32_DATA0: &[u8; 192] = &[
        0xBC, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x08, 0xD0, 0x41, 0x00, 0xD4, 0xB6, 0x41, 0x00, 0x10, 0x00, 0x00, 0x00, 0x70, 0x51, 0x41,
        0x00, 0x00, 0x00, 0x00, 0x00, 0xBC, 0x51, 0x41, 0x00, 0x3F, 0x00, 0x00, 0x00, 0x00, 0x75,
        0x01, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0xD4, 0xDC, 0x41, 0x00, 0x00, 0x00, 0x00, 0x00,
    ];

    #[test]
    fn parse_loadconfig64_data0() {
        let ctx = Ctx::new(crate::container::Container::Big, scroll::LE);
        let data = LOADCONFIG64_DATA0
            .pread_with::<LoadConfigDirectory>(0, ctx)
            .unwrap();

        assert_eq!(data.size, 320);
        assert_eq!(data.time_stamp, Some(0));
        assert_eq!(data.major_version, Some(0));
        assert_eq!(data.minor_version, Some(0));
        assert_eq!(data.global_flags_clear, Some(0));
        assert_eq!(data.global_flags_set, Some(0));
        assert_eq!(data.critical_section_default_timeout, Some(0));
        assert_eq!(data.de_commit_free_block_threshold, Some(0));
        assert_eq!(data.de_commit_total_free_threshold, Some(0));
        assert_eq!(data.lock_prefix_table, Some(0));
        assert_eq!(data.maximum_allocation_size, Some(0));
        assert_eq!(data.virtual_memory_threshold, Some(0));
        assert_eq!(data.process_affinity_mask, Some(0));
        assert_eq!(data.process_heap_flags, Some(0));
        assert_eq!(data.csd_version, Some(0));
        assert_eq!(
            data.dependent_load_flags,
            Some(LOAD_LIBRARY_SEARCH_SYSTEM32 as u16)
        );
        assert_eq!(data.edit_list, Some(0));
        assert_eq!(data.security_cookie, Some(0x1801e4598));
        assert_eq!(data.se_handler_table, Some(0));
        assert_eq!(data.se_handler_count, Some(0));
        assert_eq!(data.guard_cf_check_function_pointer, Some(0x1801e1218));
        assert_eq!(data.guard_cf_dispatch_function_pointer, Some(0x1801e5000));
        assert_eq!(data.guard_cf_function_table, Some(0x1801702a0));
        assert_eq!(data.guard_cf_function_count, Some(2183));
        // Instrumented, Function table, Delay-load IAT protected, Delay-load private section,
        // Export information suppression, Longjump table, EH continuation table
        assert_eq!(data.guard_flags, Some(0x10417500));
        const FLAGS: u32 = IMAGE_GUARD_CF_INSTRUMENTED
            | IMAGE_GUARD_CF_FUNCTION_TABLE_PRESENT
            | IMAGE_GUARD_PROTECT_DELAYLOAD_IAT
            | IMAGE_GUARD_DELAYLOAD_IAT_IN_ITS_OWN_SECTION
            | IMAGE_GUARD_CF_EXPORT_SUPPRESSION_INFO_PRESENT
            | IMAGE_GUARD_CF_LONGJUMP_TABLE_PRESENT
            | IMAGE_GUARD_EH_CONTINUATION_TABLE_PRESENT;
        assert_eq!(data.guard_flags.map(|x| x & FLAGS), Some(FLAGS));
        assert_eq!(
            data.code_integrity,
            Some(LoadConfigCodeIntegrity {
                flags: 0,
                catalog: 0,
                catalog_offset: 0,
                reserved: 0
            })
        );
        assert_eq!(data.guard_address_taken_iat_entry_table, Some(0));
        assert_eq!(data.guard_address_taken_iat_entry_count, Some(0));
        assert_eq!(data.guard_long_jump_target_table, Some(0));
        assert_eq!(data.guard_long_jump_target_count, Some(0));
        assert_eq!(data.dynamic_value_reloc_table, Some(0));
        assert_eq!(data.chpe_metadata_pointer, Some(0));
        assert_eq!(data.guard_rf_failure_routine, Some(0));
        assert_eq!(data.guard_rf_failure_routine_function_pointer, Some(0));
        assert_eq!(data.dynamic_value_reloc_table_offset, Some(0x6a0));
        assert_eq!(data.dynamic_value_reloc_table_section, Some(15));
        assert_eq!(data.reserved2, Some(0));
        assert_eq!(data.guard_rf_verify_stack_pointer_function_pointer, Some(0));
        assert_eq!(data.hot_patch_table_offset, Some(0));
        assert_eq!(data.reserved3, Some(0));
        assert_eq!(data.enclave_configuration_pointer, Some(0));
        assert_eq!(data.volatile_metadata_pointer, Some(0));
        assert_eq!(data.guard_eh_continuation_table, Some(0x18016ff38));
        assert_eq!(data.guard_eh_continuation_count, Some(174));
        assert_eq!(data.guard_xfg_check_function_pointer, Some(0x1801e5008));
        assert_eq!(data.guard_xfg_dispatch_function_pointer, Some(0x1801e5010));
        assert_eq!(
            data.guard_xfg_table_dispatch_function_pointer,
            Some(0x1801e5018)
        );
        assert_eq!(
            data.cast_guard_os_determined_failure_mode,
            Some(0x1801e5020)
        );
        assert_eq!(data.guard_memcpy_function_pointer, Some(0));
    }

    #[test]
    fn parse_loadconfig32_data0() {
        let ctx = Ctx::new(crate::container::Container::Little, scroll::LE);
        let data = LOADCONFIG32_DATA0
            .pread_with::<LoadConfigDirectory>(0, ctx)
            .unwrap();

        assert_eq!(data.size, 188);
        assert_eq!(data.time_stamp, Some(0));
        assert_eq!(data.major_version, Some(0));
        assert_eq!(data.minor_version, Some(0));
        assert_eq!(data.global_flags_clear, Some(0));
        assert_eq!(data.global_flags_set, Some(0));
        assert_eq!(data.critical_section_default_timeout, Some(0));
        assert_eq!(data.de_commit_free_block_threshold, Some(0));
        assert_eq!(data.de_commit_total_free_threshold, Some(0));
        assert_eq!(data.lock_prefix_table, Some(0));
        assert_eq!(data.maximum_allocation_size, Some(0));
        assert_eq!(data.virtual_memory_threshold, Some(0));
        assert_eq!(data.process_affinity_mask, Some(0));
        assert_eq!(data.process_heap_flags, Some(0));
        assert_eq!(data.csd_version, Some(0));
        assert_eq!(data.dependent_load_flags, Some(0));
        assert_eq!(data.edit_list, Some(0));
        assert_eq!(data.security_cookie, Some(0x41d008));
        assert_eq!(data.se_handler_table, Some(0x41b6d4));
        assert_eq!(data.se_handler_count, Some(16));
        assert_eq!(data.guard_cf_check_function_pointer, Some(0x415170));
        assert_eq!(data.guard_cf_dispatch_function_pointer, Some(0));
        assert_eq!(data.guard_cf_function_table, Some(0x4151bc));
        assert_eq!(data.guard_cf_function_count, Some(63));
        // Instrumented, Function table, Delay-load IAT protected, Delay-load private section,
        // Export information suppression, Longjump table
        assert_eq!(data.guard_flags, Some(0x10017500));
        const FLAGS: u32 = IMAGE_GUARD_CF_INSTRUMENTED
            | IMAGE_GUARD_CF_FUNCTION_TABLE_PRESENT
            | IMAGE_GUARD_PROTECT_DELAYLOAD_IAT
            | IMAGE_GUARD_DELAYLOAD_IAT_IN_ITS_OWN_SECTION
            | IMAGE_GUARD_CF_EXPORT_SUPPRESSION_INFO_PRESENT
            | IMAGE_GUARD_CF_LONGJUMP_TABLE_PRESENT;
        assert_eq!(data.guard_flags.map(|x| x & FLAGS), Some(FLAGS));
        assert_eq!(
            data.code_integrity,
            Some(LoadConfigCodeIntegrity {
                flags: 0,
                catalog: 0,
                catalog_offset: 0,
                reserved: 0
            })
        );
        assert_eq!(data.guard_address_taken_iat_entry_table, Some(0));
        assert_eq!(data.guard_address_taken_iat_entry_count, Some(0));
        assert_eq!(data.guard_long_jump_target_table, Some(0));
        assert_eq!(data.guard_long_jump_target_count, Some(0));
        assert_eq!(data.dynamic_value_reloc_table, Some(0));
        assert_eq!(data.chpe_metadata_pointer, Some(0));
        assert_eq!(data.guard_rf_failure_routine, Some(0));
        assert_eq!(data.guard_rf_failure_routine_function_pointer, Some(0));
        assert_eq!(data.dynamic_value_reloc_table_offset, Some(0));
        assert_eq!(data.dynamic_value_reloc_table_section, Some(0));
        assert_eq!(data.reserved2, Some(0));
        assert_eq!(data.guard_rf_verify_stack_pointer_function_pointer, Some(0));
        assert_eq!(data.hot_patch_table_offset, Some(0));
        assert_eq!(data.reserved3, Some(0));
        assert_eq!(data.enclave_configuration_pointer, Some(0));
        assert_eq!(data.volatile_metadata_pointer, Some(0));
        assert_eq!(data.guard_eh_continuation_table, Some(0));
        assert_eq!(data.guard_eh_continuation_count, Some(0));
        assert_eq!(data.guard_xfg_check_function_pointer, Some(0));
        assert_eq!(data.guard_xfg_dispatch_function_pointer, Some(0));
        assert_eq!(data.guard_xfg_table_dispatch_function_pointer, Some(0));
        assert_eq!(data.cast_guard_os_determined_failure_mode, Some(0x41dcd4));
        assert_eq!(data.guard_memcpy_function_pointer, Some(0));
    }
}
