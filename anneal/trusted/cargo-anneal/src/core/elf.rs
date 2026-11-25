// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pure ELF64 little-endian `PT_INTERP` metadata parsing and dynamic-linker
//! environment variable sanitization rules.

use std::collections::BTreeMap;

use crate::core::error::Failure;

/// Dynamic-linker environment variable prefixes forbidden inside sandboxed
/// child `extra_env` maps.
pub const FORBIDDEN_LOADER_ENV_PREFIXES: &[&str] = &["LD_", "DYLD_"];

/// Refuse any dynamic-linker environment variable (`LD_*`, `DYLD_*`) in a
/// sandboxed child `extra_env` map before spawning a child process.
pub fn reject_forbidden_loader_env(extra_env: &BTreeMap<String, String>) -> Result<(), Failure> {
    for key in extra_env.keys() {
        if FORBIDDEN_LOADER_ENV_PREFIXES.iter().any(|prefix| key.starts_with(prefix)) {
            return Err(Failure::operational(
                "sandbox",
                format!("refusing dynamic linker environment variable {key} in sandbox extra_env"),
            ));
        }
    }
    Ok(())
}

/// Validated ELF64 program-header table coordinates extracted from an ELF64
/// header.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Elf64PhdrTable {
    /// Byte offset of the program header table within the ELF binary.
    pub e_phoff: u64,
    /// Size in bytes of each program header entry (`>= 56`).
    pub e_phentsize: usize,
    /// Number of program header entries (`>= 1`).
    pub e_phnum: usize,
    /// Total byte length of the program header table (`<= 4 MiB`).
    pub table_bytes: usize,
}

/// Parse and bounds-check an ELF64 little-endian header to locate its program
/// header table (`Ok(None)` when `e_phnum == 0`).
pub fn parse_elf64_ehdr(
    ehdr: &[u8; 64],
    file_len: u64,
    label: &str,
) -> Result<Option<Elf64PhdrTable>, String> {
    if &ehdr[0..4] != b"\x7fELF" {
        return Err(format!("{label} is not an ELF binary"));
    }
    if ehdr[4] != 2 || ehdr[5] != 1 {
        return Err(format!(
            "{label} is not little-endian ELF64 (class={}, data={})",
            ehdr[4], ehdr[5]
        ));
    }
    let e_phoff = u64::from_le_bytes([
        ehdr[32], ehdr[33], ehdr[34], ehdr[35], ehdr[36], ehdr[37], ehdr[38], ehdr[39],
    ]);
    let e_phentsize = u16::from_le_bytes([ehdr[54], ehdr[55]]) as u64;
    let e_phnum = u16::from_le_bytes([ehdr[56], ehdr[57]]) as u64;
    if e_phnum == 0 {
        return Ok(None);
    }
    if e_phentsize < 56 {
        return Err(format!("invalid ELF64 e_phentsize {e_phentsize} in {label}"));
    }
    let ph_table_bytes = e_phentsize
        .checked_mul(e_phnum)
        .ok_or_else(|| "ELF64 program header table size overflow".to_string())?;
    let ph_end = e_phoff
        .checked_add(ph_table_bytes)
        .ok_or_else(|| "ELF64 program header table end overflow".to_string())?;
    if ph_end > file_len || ph_table_bytes > 4 * 1024 * 1024 {
        return Err(format!("ELF64 program header table out of bounds in {label}"));
    }
    Ok(Some(Elf64PhdrTable {
        e_phoff,
        e_phentsize: e_phentsize as usize,
        e_phnum: e_phnum as usize,
        table_bytes: ph_table_bytes as usize,
    }))
}

/// Locate the `(p_offset, p_filesz)` byte range of the first `PT_INTERP`
/// entry in `table`, enforcing bounds against `file_len` and `<= 4096` bytes.
pub fn find_elf64_pt_interp(
    table: &[u8],
    info: Elf64PhdrTable,
    file_len: u64,
) -> Result<Option<(u64, usize)>, String> {
    const PT_INTERP: u32 = 3;
    if info.e_phentsize < 56 {
        return Err(format!("invalid ELF64 e_phentsize {}", info.e_phentsize));
    }
    let required_bytes = info
        .e_phnum
        .checked_mul(info.e_phentsize)
        .ok_or_else(|| "ELF64 program header table size overflow".to_string())?;
    if info.table_bytes < required_bytes || table.len() < required_bytes {
        return Err("truncated ELF64 program header table".to_string());
    }
    for i in 0..info.e_phnum {
        let base = i * info.e_phentsize;
        let entry = table
            .get(base..base + 40)
            .ok_or_else(|| "truncated ELF64 program header table".to_string())?;
        let p_type = u32::from_le_bytes([entry[0], entry[1], entry[2], entry[3]]);
        if p_type == PT_INTERP {
            let p_offset = u64::from_le_bytes([
                entry[8], entry[9], entry[10], entry[11], entry[12], entry[13], entry[14],
                entry[15],
            ]);
            let p_filesz = u64::from_le_bytes([
                entry[32], entry[33], entry[34], entry[35], entry[36], entry[37], entry[38],
                entry[39],
            ]);
            if p_filesz == 0 || p_filesz > 4096 {
                return Err(format!("invalid PT_INTERP size {p_filesz}"));
            }
            let end = p_offset
                .checked_add(p_filesz)
                .ok_or_else(|| "PT_INTERP offset overflow".to_string())?;
            if end > file_len {
                return Err("PT_INTERP extends past EOF".to_string());
            }
            return Ok(Some((p_offset, p_filesz as usize)));
        }
    }
    Ok(None)
}

/// Decode a NUL-terminated UTF-8 `PT_INTERP` payload.
pub fn decode_pt_interp_cstr(raw: &[u8]) -> Result<String, String> {
    let nul_pos = raw.iter().position(|&b| b == 0).unwrap_or(raw.len());
    let s =
        std::str::from_utf8(&raw[..nul_pos]).map_err(|e| format!("non-UTF-8 PT_INTERP: {e}"))?;
    if s.is_empty() {
        return Err("empty PT_INTERP".to_string());
    }
    Ok(s.to_owned())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn find_elf64_pt_interp_rejects_inconsistent_phdr_table_without_panicking() {
        let inconsistent =
            Elf64PhdrTable { e_phoff: 64, e_phentsize: 56, e_phnum: 4, table_bytes: 0 };
        assert!(find_elf64_pt_interp(&[], inconsistent, 4096).is_err());

        let small_phentsize =
            Elf64PhdrTable { e_phoff: 64, e_phentsize: 32, e_phnum: 1, table_bytes: 32 };
        assert!(find_elf64_pt_interp(&[0u8; 64], small_phentsize, 4096).is_err());
    }
}
