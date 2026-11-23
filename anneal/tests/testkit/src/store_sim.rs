// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Hermetic Nix/CAS split-store and ELF `DT_RUNPATH` simulation helpers.
//!
//! Tests split C/toolchain runtimes (`PT_INTERP`, `DT_RUNPATH` vs. `DT_RPATH`,
//! symlinked DSOs, and cross-package Nix `symlinkJoin` Lean stdlib trees)
//! under `<root>/store/` without mutating or requiring host `/nix/store`.

use std::collections::BTreeSet;
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};

use crate::TestResult;
use crate::process::{Invocation, ProcessOutcome};
use crate::workspace::{Building, StagedWorkspace, WorkspaceBuilder};

/// Parsed subset of ELF64 little-endian headers used to validate split-store
/// fixtures against `anneal-rustc-capture` and `glibc` dynamic-loader rules.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Elf64Info {
    pub is_executable_or_dyn: bool,
    pub pt_interp: Option<String>,
    pub dt_needed: Vec<String>,
    pub dt_runpath: Option<String>,
    pub dt_rpath: Option<String>,
}

/// Specification for generating a minimal valid ELF64 little-endian image
/// carrying exact `PT_LOAD`, `PT_INTERP`, and `PT_DYNAMIC` metadata.
#[derive(Clone, Debug, Default)]
pub struct Elf64Spec {
    pub is_shared_object: bool,
    pub pt_interp: Option<String>,
    pub dt_needed: Vec<String>,
    pub dt_runpath: Option<String>,
    pub dt_rpath: Option<String>,
}

/// Synthesize a minimal, header-valid ELF64 little-endian executable or shared
/// object containing `PT_LOAD`, optional `PT_INTERP`, and `PT_DYNAMIC`
/// (`DT_STRTAB`, `DT_STRSZ`, `DT_NEEDED`, `DT_RUNPATH`, `DT_RPATH`, `DT_NULL`).
pub fn build_elf64_image(spec: &Elf64Spec) -> Vec<u8> {
    const EHDR_SIZE: usize = 64;
    const PHDR_SIZE: usize = 56;
    const VADDR_BASE: u64 = 0x0040_0000;

    let mut strtab = vec![0u8];
    let mut push_str = |s: &str| -> u64 {
        let off = strtab.len() as u64;
        strtab.extend_from_slice(s.as_bytes());
        strtab.push(0);
        off
    };

    let mut dyn_entries: Vec<(i64, u64)> = Vec::new();
    for needed in &spec.dt_needed {
        let off = push_str(needed);
        dyn_entries.push((1, off)); // DT_NEEDED
    }
    if let Some(runpath) = &spec.dt_runpath {
        let off = push_str(runpath);
        dyn_entries.push((29, off)); // DT_RUNPATH
    }
    if let Some(rpath) = &spec.dt_rpath {
        let off = push_str(rpath);
        dyn_entries.push((15, off)); // DT_RPATH
    }

    let phnum = 2 + usize::from(spec.pt_interp.is_some()); // PT_LOAD + PT_DYNAMIC [+ PT_INTERP]
    let ph_end = EHDR_SIZE + phnum * PHDR_SIZE;
    let interp_bytes = spec.pt_interp.as_ref().map(|s| {
        let mut b = s.as_bytes().to_vec();
        b.push(0);
        b
    });
    let interp_off = ph_end;
    let interp_len = interp_bytes.as_ref().map_or(0, Vec::len);
    let dyn_off = align8(interp_off + interp_len);

    // Reserve slots for DT_STRTAB, DT_STRSZ, and DT_NULL.
    let dyn_count = dyn_entries.len() + 3;
    let dyn_sz = dyn_count * 16;
    let strtab_off = dyn_off + dyn_sz;
    let total_len = strtab_off + strtab.len();

    let mut buf = vec![0u8; total_len];
    // ELF64 header
    buf[0..4].copy_from_slice(b"\x7fELF");
    buf[4] = 2; // ELFCLASS64
    buf[5] = 1; // ELFDATA2LSB
    buf[6] = 1; // EV_CURRENT
    let e_type: u16 = if spec.is_shared_object { 3 } else { 2 };
    buf[16..18].copy_from_slice(&e_type.to_le_bytes());
    buf[18..20].copy_from_slice(&62u16.to_le_bytes()); // EM_X86_64
    buf[20..24].copy_from_slice(&1u32.to_le_bytes()); // e_version
    buf[24..32].copy_from_slice(&VADDR_BASE.to_le_bytes()); // e_entry
    buf[32..40].copy_from_slice(&(EHDR_SIZE as u64).to_le_bytes()); // e_phoff
    buf[52..54].copy_from_slice(&(EHDR_SIZE as u16).to_le_bytes()); // e_ehsize
    buf[54..56].copy_from_slice(&(PHDR_SIZE as u16).to_le_bytes()); // e_phentsize
    buf[56..58].copy_from_slice(&(phnum as u16).to_le_bytes()); // e_phnum

    fn write_phdr(
        buf: &mut [u8],
        idx: usize,
        p_type: u32,
        p_flags: u32,
        off: usize,
        sz: usize,
    ) {
        let base = EHDR_SIZE + idx * PHDR_SIZE;
        let vaddr = VADDR_BASE + off as u64;
        buf[base..base + 4].copy_from_slice(&p_type.to_le_bytes());
        buf[base + 4..base + 8].copy_from_slice(&p_flags.to_le_bytes());
        buf[base + 8..base + 16].copy_from_slice(&(off as u64).to_le_bytes());
        buf[base + 16..base + 24].copy_from_slice(&vaddr.to_le_bytes());
        buf[base + 24..base + 32].copy_from_slice(&vaddr.to_le_bytes());
        buf[base + 32..base + 40].copy_from_slice(&(sz as u64).to_le_bytes());
        buf[base + 40..base + 48].copy_from_slice(&(sz as u64).to_le_bytes());
        buf[base + 48..base + 56].copy_from_slice(&0x1000u64.to_le_bytes());
    }

    // PT_LOAD covering the image so vaddr -> offset translation succeeds.
    write_phdr(&mut buf, 0, 1, 5, 0, total_len);
    let mut next_ph = 1;
    if let Some(interp) = &interp_bytes {
        buf[interp_off..interp_off + interp.len()].copy_from_slice(interp);
        write_phdr(&mut buf, next_ph, 3, 4, interp_off, interp.len()); // PT_INTERP
        next_ph += 1;
    }
    write_phdr(&mut buf, next_ph, 2, 6, dyn_off, dyn_sz); // PT_DYNAMIC

    dyn_entries.push((5, VADDR_BASE + strtab_off as u64)); // DT_STRTAB
    dyn_entries.push((10, strtab.len() as u64)); // DT_STRSZ
    dyn_entries.push((0, 0)); // DT_NULL

    for (i, (tag, val)) in dyn_entries.into_iter().enumerate() {
        let off = dyn_off + i * 16;
        buf[off..off + 8].copy_from_slice(&tag.to_le_bytes());
        buf[off + 8..off + 16].copy_from_slice(&val.to_le_bytes());
    }
    buf[strtab_off..strtab_off + strtab.len()].copy_from_slice(&strtab);
    buf
}

fn align8(n: usize) -> usize {
    (n + 7) & !7
}

/// Inspect an ELF64 little-endian binary or DSO from disk.
pub fn inspect_elf64(path: &Path) -> TestResult<Elf64Info> {
    let bytes =
        fs::read(path).map_err(|error| format!("read ELF {}: {error}", path.display()))?;
    if bytes.len() < 64 || &bytes[0..4] != b"\x7fELF" || bytes[4] != 2 || bytes[5] != 1 {
        return Err(format!("not a valid ELF64-LE binary: {}", path.display()));
    }
    let e_type = u16::from_le_bytes(bytes[16..18].try_into().unwrap());
    let e_phoff = u64::from_le_bytes(bytes[32..40].try_into().unwrap()) as usize;
    let e_phentsize = u16::from_le_bytes(bytes[54..56].try_into().unwrap()) as usize;
    let e_phnum = u16::from_le_bytes(bytes[56..58].try_into().unwrap()) as usize;
    let ph_end = e_phoff
        .checked_add(e_phentsize.saturating_mul(e_phnum))
        .ok_or_else(|| "ELF program header overflow".to_string())?;
    if e_phentsize < 56 || ph_end > bytes.len() {
        return Err(format!("truncated ELF program headers in {}", path.display()));
    }

    let mut loads: Vec<(u64, u64, u64)> = Vec::new();
    let mut pt_interp = None;
    let mut dynamic_seg = None;
    for i in 0..e_phnum {
        let base = e_phoff + i * e_phentsize;
        let p_type = u32::from_le_bytes(bytes[base..base + 4].try_into().unwrap());
        let p_offset = u64::from_le_bytes(bytes[base + 8..base + 16].try_into().unwrap());
        let p_vaddr = u64::from_le_bytes(bytes[base + 16..base + 24].try_into().unwrap());
        let p_filesz = u64::from_le_bytes(bytes[base + 32..base + 40].try_into().unwrap());
        match p_type {
            1 => loads.push((p_vaddr, p_offset, p_filesz)),
            2 => dynamic_seg = Some((p_offset as usize, p_filesz as usize)),
            3 if pt_interp.is_none() => {
                let start = p_offset as usize;
                let end = start.saturating_add(p_filesz as usize);
                if end <= bytes.len() {
                    let raw = &bytes[start..end];
                    let nul = raw.iter().position(|&b| b == 0).unwrap_or(raw.len());
                    pt_interp = std::str::from_utf8(&raw[..nul]).ok().map(str::to_owned);
                }
            }
            _ => {}
        }
    }

    let mut dt_needed = Vec::new();
    let mut dt_runpath = None;
    let mut dt_rpath = None;
    if let Some((dyn_off, dyn_sz)) = dynamic_seg
        && dyn_off.saturating_add(dyn_sz) <= bytes.len()
    {
        let mut strtab_vaddr = None;
        let mut strsz = None;
        let mut needed_offs = Vec::new();
        let mut rpath_off = None;
        let mut runpath_off = None;
        for chunk in bytes[dyn_off..dyn_off + dyn_sz].as_chunks::<16>().0 {
            let tag = i64::from_le_bytes(chunk[0..8].try_into().unwrap());
            let val = u64::from_le_bytes(chunk[8..16].try_into().unwrap());
            match tag {
                0 => break,
                1 => needed_offs.push(val),
                5 => strtab_vaddr = Some(val),
                10 => strsz = Some(val),
                15 => rpath_off = Some(val),
                29 => runpath_off = Some(val),
                _ => {}
            }
        }
        if let (Some(sv), Some(ss)) = (strtab_vaddr, strsz)
            && let Some(strtab_off) = vaddr_to_offset(&loads, sv, ss)
            && let Some(end) = usize::try_from(ss).ok().and_then(|n| strtab_off.checked_add(n))
            && let Some(strtab) = bytes.get(strtab_off..end)
        {
            let read_cstr = |off: u64| -> Option<String> {
                let tail = strtab.get(off as usize..)?;
                let nul = tail.iter().position(|&b| b == 0).unwrap_or(tail.len());
                std::str::from_utf8(&tail[..nul]).ok().map(str::to_owned)
            };
            for off in needed_offs {
                if let Some(s) = read_cstr(off) {
                    dt_needed.push(s);
                }
            }
            dt_runpath = runpath_off.and_then(read_cstr);
            dt_rpath = rpath_off.and_then(read_cstr);
        }
    }

    Ok(Elf64Info {
        is_executable_or_dyn: e_type == 2 || e_type == 3,
        pt_interp,
        dt_needed,
        dt_runpath,
        dt_rpath,
    })
}

fn vaddr_to_offset(loads: &[(u64, u64, u64)], vaddr: u64, len: u64) -> Option<usize> {
    for &(pv, po, pfs) in loads {
        let Some(rel) = vaddr.checked_sub(pv) else {
            continue;
        };
        if let Some(end) = rel.checked_add(len)
            && end <= pfs
            && let Some(off) = po.checked_add(rel).and_then(|v| usize::try_from(v).ok())
        {
            return Some(off);
        }
    }
    None
}

/// Identifier for each of the five ELF `DT_RUNPATH` / `DT_RPATH` / `DT_NEEDED`
/// test cells materialized by [`ElfStoreBuilder`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ElfStoreCell {
    Cell1NonTransitiveRunpathFailure,
    Cell2AncestorRpathSuppressedByRunpath,
    Cell3AncestorRpathFallback,
    Cell4PreloadedDtNeeded,
    Cell5OriginRelativeAndDedupSymlink,
}

/// Paths produced by [`ElfStoreBuilder::build_five_cell_layout`].
#[derive(Clone, Debug)]
pub struct FiveCellElfLayout {
    pub glibc_dir: PathBuf,
    pub loader_path: PathBuf,
    pub gcc_lib_dir: PathBuf,
    pub zlib_dir: PathBuf,
    pub sysroot_dir: PathBuf,
    pub cell_consumers: [(ElfStoreCell, PathBuf); 5],
}

/// Materializes Nix/CAS split-output ELF stores under `<root>/store/` backed
/// by `ReadOnlyTreeGuard` (`0o555` dirs / read-only files).
pub struct ElfStoreBuilder<'w> {
    ws: &'w mut WorkspaceBuilder<Building>,
    freeze_read_only: bool,
}

impl<'w> ElfStoreBuilder<'w> {
    /// Create a split-store builder targeting `ws`. When `freeze_read_only` is
    /// `true`, created store packages are frozen with `0o555` directories and
    /// `0o444`/`0o555` files under `ReadOnlyTreeGuard`.
    pub fn new(ws: &'w mut WorkspaceBuilder<Building>, freeze_read_only: bool) -> Self {
        Self {
            ws,
            freeze_read_only,
        }
    }

    /// Build the five-cell split C/toolchain runtime layout in `<root>/store/`:
    /// - `0001-glibc/lib/ld-linux-x86-64.so.2`
    /// - `0002-gcc-lib/lib/libgcc_s.so.1` symlinked to
    ///   `../../0003-gcc-libgcc/lib/libgcc_s.so.1`
    /// - `0003-gcc-libgcc/lib/libgcc_s.so.1`
    /// - `0004-zlib/lib/libz.so.1`
    /// - `0005-rust-sysroot/` (`bin/rustc`, `lib/librustc_driver-test.so`,
    ///   `lib/libLLVM-21.so`, `lib/rustlib/x86_64-unknown-linux-gnu/lib/...`)
    /// - `0006-elf-cells/...` holding Cell 1-5 executables and DSOs.
    pub fn build_five_cell_layout(&mut self) -> TestResult<FiveCellElfLayout> {
        let store_dir = self.ws.store_dir().to_path_buf();
        let glibc_dir = self
            .ws
            .add_store_package("0001-glibc", self.freeze_read_only, |pkg| {
                let lib = pkg.join("lib");
                fs::create_dir_all(&lib).map_err(|e| e.to_string())?;
                write_exec(
                    &lib.join("ld-linux-x86-64.so.2"),
                    &build_elf64_image(&Elf64Spec {
                        is_shared_object: true,
                        ..Default::default()
                    }),
                )
            })?;
        let loader_path = glibc_dir.join("lib/ld-linux-x86-64.so.2");

        let _gcc_real = self
            .ws
            .add_store_package("0003-gcc-libgcc", self.freeze_read_only, |pkg| {
                let lib = pkg.join("lib");
                fs::create_dir_all(&lib).map_err(|e| e.to_string())?;
                write_exec(
                    &lib.join("libgcc_s.so.1"),
                    &build_elf64_image(&Elf64Spec {
                        is_shared_object: true,
                        ..Default::default()
                    }),
                )
            })?;

        let gcc_lib_dir = self
            .ws
            .add_store_package("0002-gcc-lib", self.freeze_read_only, |pkg| {
                let lib = pkg.join("lib");
                fs::create_dir_all(&lib).map_err(|e| e.to_string())?;
                #[cfg(unix)]
                std::os::unix::fs::symlink(
                    "../../0003-gcc-libgcc/lib/libgcc_s.so.1",
                    lib.join("libgcc_s.so.1"),
                )
                .map_err(|e| e.to_string())?;
                Ok(())
            })?;

        let zlib_dir = self
            .ws
            .add_store_package("0004-zlib", self.freeze_read_only, |pkg| {
                let lib = pkg.join("lib");
                fs::create_dir_all(&lib).map_err(|e| e.to_string())?;
                write_exec(
                    &lib.join("libz.so.1"),
                    &build_elf64_image(&Elf64Spec {
                        is_shared_object: true,
                        ..Default::default()
                    }),
                )
            })?;

        let zlib_lib = store_dir.join("0004-zlib/lib");
        let sysroot_dir = self
            .ws
            .add_store_package("0005-rust-sysroot", self.freeze_read_only, |pkg| {
                let bin = pkg.join("bin");
                let lib = pkg.join("lib");
                let rustlib = lib.join("rustlib/x86_64-unknown-linux-gnu/lib");
                fs::create_dir_all(&bin).map_err(|e| e.to_string())?;
                fs::create_dir_all(&rustlib).map_err(|e| e.to_string())?;
                write_exec(
                    &bin.join("rustc"),
                    &build_elf64_image(&Elf64Spec {
                        pt_interp: Some(loader_path.to_string_lossy().into_owned()),
                        dt_needed: vec!["librustc_driver-test.so".into()],
                        dt_runpath: Some("$ORIGIN/../lib".into()),
                        ..Default::default()
                    }),
                )?;
                write_exec(
                    &lib.join("librustc_driver-test.so"),
                    &build_elf64_image(&Elf64Spec {
                        is_shared_object: true,
                        dt_needed: vec!["libLLVM-21.so".into(), "libgcc_s.so.1".into()],
                        dt_runpath: Some(format!(
                            "$ORIGIN:{}",
                            gcc_lib_dir.join("lib").display()
                        )),
                        ..Default::default()
                    }),
                )?;
                write_exec(
                    &lib.join("libLLVM-21.so"),
                    &build_elf64_image(&Elf64Spec {
                        is_shared_object: true,
                        dt_needed: vec!["libz.so.1".into()],
                        dt_runpath: Some(zlib_lib.to_string_lossy().into_owned()),
                        ..Default::default()
                    }),
                )?;
                #[cfg(unix)]
                std::os::unix::fs::symlink(
                    "../../../libLLVM-21.so",
                    rustlib.join("libLLVM-21.so"),
                )
                .map_err(|e| e.to_string())?;
                Ok(())
            })?;

        let cells_dir = self
            .ws
            .add_store_package("0006-elf-cells", self.freeze_read_only, |pkg| {
                let bin = pkg.join("bin");
                let mid = pkg.join("mid");
                let omni_lib = pkg.join("lib");
                fs::create_dir_all(&bin).map_err(|e| e.to_string())?;
                fs::create_dir_all(&mid).map_err(|e| e.to_string())?;
                fs::create_dir_all(&omni_lib).map_err(|e| e.to_string())?;

                // Shared local `libz.so.1` inside omnibus `lib/` for Cell 5.
                write_exec(
                    &omni_lib.join("libz.so.1"),
                    &build_elf64_image(&Elf64Spec {
                        is_shared_object: true,
                        ..Default::default()
                    }),
                )?;

                // Cell 1: Consumer has `DT_RUNPATH = mid:zlib_lib` and
                // `DT_NEEDED libmid_runpath.so`, while `libmid_runpath.so`
                // needs `libz.so.1` with empty `DT_RUNPATH`. Under ELF
                // `DT_RUNPATH` non-transitivity, `libz.so.1` is NOT found via
                // the consumer's `DT_RUNPATH`.
                write_exec(
                    &mid.join("libmid_runpath.so"),
                    &build_elf64_image(&Elf64Spec {
                        is_shared_object: true,
                        dt_needed: vec!["libz.so.1".into()],
                        ..Default::default()
                    }),
                )?;
                write_exec(
                    &bin.join("cell1-consumer"),
                    &build_elf64_image(&Elf64Spec {
                        pt_interp: Some(loader_path.to_string_lossy().into_owned()),
                        dt_needed: vec!["libmid_runpath.so".into()],
                        dt_runpath: Some(format!("{}:{}", mid.display(), zlib_lib.display())),
                        ..Default::default()
                    }),
                )?;

                // Cell 2: Consumer sets legacy `DT_RPATH = mid:zlib_lib`, while
                // `libmid_with_runpath.so` sets `DT_RUNPATH = mid` and needs
                // `libz.so.1`: non-empty `DT_RUNPATH` suppresses ancestor
                // `DT_RPATH` (`glibc` `elf/dl-load.c`).
                write_exec(
                    &mid.join("libmid_with_runpath.so"),
                    &build_elf64_image(&Elf64Spec {
                        is_shared_object: true,
                        dt_needed: vec!["libz.so.1".into()],
                        dt_runpath: Some(mid.to_string_lossy().into_owned()),
                        ..Default::default()
                    }),
                )?;
                write_exec(
                    &bin.join("cell2-consumer"),
                    &build_elf64_image(&Elf64Spec {
                        pt_interp: Some(loader_path.to_string_lossy().into_owned()),
                        dt_needed: vec!["libmid_with_runpath.so".into()],
                        dt_rpath: Some(format!("{}:{}", mid.display(), zlib_lib.display())),
                        ..Default::default()
                    }),
                )?;

                // Cell 3: Consumer sets `DT_RPATH = mid:zlib_lib` and leaf has
                // NO `DT_RUNPATH`: ancestor `DT_RPATH` resolves `libz.so.1`.
                write_exec(
                    &bin.join("cell3-consumer"),
                    &build_elf64_image(&Elf64Spec {
                        pt_interp: Some(loader_path.to_string_lossy().into_owned()),
                        dt_needed: vec!["libmid_runpath.so".into()],
                        dt_rpath: Some(format!("{}:{}", mid.display(), zlib_lib.display())),
                        ..Default::default()
                    }),
                )?;

                // Cell 4: Consumer preloads `DT_NEEDED libz.so.1` alongside
                // `libmid_runpath.so` (`patchelf --add-needed libz.so.1`) so
                // leaf `libmid_runpath.so` reuses already-loaded `libz.so.1`.
                write_exec(
                    &bin.join("cell4-consumer"),
                    &build_elf64_image(&Elf64Spec {
                        pt_interp: Some(loader_path.to_string_lossy().into_owned()),
                        dt_needed: vec!["libz.so.1".into(), "libmid_runpath.so".into()],
                        dt_runpath: Some(format!("{}:{}", mid.display(), zlib_lib.display())),
                        ..Default::default()
                    }),
                )?;

                // Cell 5: Co-located omnibus `$ORIGIN/../lib` `DT_RUNPATH`
                // directly resolves `libz.so.1`.
                write_exec(
                    &bin.join("cell5-consumer"),
                    &build_elf64_image(&Elf64Spec {
                        pt_interp: Some(loader_path.to_string_lossy().into_owned()),
                        dt_needed: vec!["libz.so.1".into()],
                        dt_runpath: Some("$ORIGIN/../lib".into()),
                        ..Default::default()
                    }),
                )?;
                Ok(())
            })?;

        Ok(FiveCellElfLayout {
            glibc_dir,
            loader_path,
            gcc_lib_dir,
            zlib_dir,
            sysroot_dir,
            cell_consumers: [
                (
                    ElfStoreCell::Cell1NonTransitiveRunpathFailure,
                    cells_dir.join("bin/cell1-consumer"),
                ),
                (
                    ElfStoreCell::Cell2AncestorRpathSuppressedByRunpath,
                    cells_dir.join("bin/cell2-consumer"),
                ),
                (
                    ElfStoreCell::Cell3AncestorRpathFallback,
                    cells_dir.join("bin/cell3-consumer"),
                ),
                (
                    ElfStoreCell::Cell4PreloadedDtNeeded,
                    cells_dir.join("bin/cell4-consumer"),
                ),
                (
                    ElfStoreCell::Cell5OriginRelativeAndDedupSymlink,
                    cells_dir.join("bin/cell5-consumer"),
                ),
            ],
        })
    }
}

/// Simulate glibc `elf/dl-load.c` `DT_RUNPATH` / `DT_RPATH` / `DT_NEEDED`
/// transitive dependency resolution for an ELF64 root executable inside a
/// split store (with zero ambient `/lib` fallback).
pub fn resolve_elf64_dependency_closure(root_exe: &Path) -> TestResult<Vec<PathBuf>> {
    let mut loaded_names: BTreeSet<String> = BTreeSet::new();
    let mut loaded_paths: Vec<PathBuf> = Vec::new();
    resolve_recursive(root_exe, &[], &mut loaded_names, &mut loaded_paths)?;
    Ok(loaded_paths)
}

fn expand_origin(raw: &str, obj_path: &Path) -> Vec<PathBuf> {
    let origin = obj_path.parent().unwrap_or_else(|| Path::new("/"));
    raw.split(':')
        .filter(|s| !s.is_empty())
        .map(|entry| {
            let expanded = entry
                .replace("${ORIGIN}", &origin.to_string_lossy())
                .replace("$ORIGIN", &origin.to_string_lossy());
            PathBuf::from(expanded)
        })
        .collect()
}

fn resolve_recursive(
    obj_path: &Path,
    ancestor_rpaths: &[PathBuf],
    loaded_names: &mut BTreeSet<String>,
    loaded_paths: &mut Vec<PathBuf>,
) -> TestResult {
    let info = inspect_elf64(obj_path)?;
    // Per glibc `elf/dl-load.c`: `DT_RPATH` of an object is searched only when
    // that object has `DT_RUNPATH == NULL`; otherwise `DT_RUNPATH` supersedes
    // both its own and ancestor `DT_RPATH` entries for its direct `DT_NEEDED`.
    let has_runpath = info.dt_runpath.is_some();
    let own_runpath = info
        .dt_runpath
        .as_deref()
        .map(|s| expand_origin(s, obj_path))
        .unwrap_or_default();
    let own_rpath = info
        .dt_rpath
        .as_deref()
        .map(|s| expand_origin(s, obj_path))
        .unwrap_or_default();

    let mut search_dirs: Vec<PathBuf> = Vec::new();
    let mut next_ancestor_rpaths: Vec<PathBuf> = Vec::new();
    if !has_runpath {
        search_dirs.extend(own_rpath.iter().cloned());
        search_dirs.extend(ancestor_rpaths.iter().cloned());
        next_ancestor_rpaths.extend(own_rpath);
        next_ancestor_rpaths.extend(ancestor_rpaths.iter().cloned());
    } else {
        search_dirs.extend(own_runpath);
    }

    let mut direct_children = Vec::new();
    for needed in &info.dt_needed {
        if loaded_names.contains(needed) {
            continue;
        }
        let found = search_dirs
            .iter()
            .map(|dir| dir.join(needed))
            .find(|cand| cand.is_file())
            .ok_or_else(|| {
                format!(
                    "ELF loader could not resolve {needed} for {} (search_dirs={search_dirs:?})",
                    obj_path.display()
                )
            })?;
        loaded_names.insert(needed.clone());
        loaded_paths.push(found.clone());
        direct_children.push(found);
    }

    for child in direct_children {
        resolve_recursive(&child, &next_ancestor_rpaths, loaded_names, loaded_paths)?;
    }
    Ok(())
}

/// Configuration for running an executable inside an unprivileged Linux `bwrap`
/// namespace with `<store_dir>` bound read-only at `/nix/store`.
#[derive(Clone, Debug)]
pub struct SimulatedStoreConfig {
    pub extra_ro_binds: Vec<(PathBuf, PathBuf)>,
    pub environment: Vec<(String, String)>,
}

impl Default for SimulatedStoreConfig {
    fn default() -> Self {
        Self {
            extra_ro_binds: Vec::new(),
            environment: vec![("PATH".into(), "/usr/bin:/bin".into())],
        }
    }
}

/// Execute `exe` with `args` inside an unprivileged Linux `bubblewrap` mount
/// namespace binding `staged.store_dir()` read-only at `/nix/store` and
/// `staged.work_dir()` writable at `/work`.
///
/// If `exe` resides outside `/usr`, `/bin`, `/lib`, `/lib64`, or `/nix/store`,
/// it is also read-only mounted at its canonical path inside the namespace so
/// workspace-compiled test binaries can run as the simulated child target.
pub fn run_in_simulated_nix_store(
    staged: &StagedWorkspace,
    exe: &Path,
    args: &[&OsStr],
    config: &SimulatedStoreConfig,
) -> TestResult<ProcessOutcome> {
    #[cfg(not(target_os = "linux"))]
    {
        let _ = (staged, exe, args, config);
        return Err(
            "run_in_simulated_nix_store requires Linux bubblewrap user/mount namespaces".into(),
        );
    }
    #[cfg(target_os = "linux")]
    {
        let bwrap = Path::new("/usr/bin/bwrap");
        if !bwrap.is_file() {
            return Err("bubblewrap (/usr/bin/bwrap) is required for simulated /nix/store".into());
        }
        let canon_store = fs::canonicalize(staged.store_dir())
            .map_err(|e| format!("canonicalize store_dir: {e}"))?;
        let canon_work = fs::canonicalize(staged.work_dir())
            .map_err(|e| format!("canonicalize work_dir: {e}"))?;
        // Allow callers to invoke binaries staged directly under `/nix/store/`
        // without host canonicalization so `/nix/store`-relative `$ORIGIN` is
        // preserved inside the mount namespace.
        let (exec_in_sandbox, bind_host_exe) = if let Ok(rel) = exe.strip_prefix("/nix/store") {
            if rel.as_os_str().is_empty()
                || rel
                    .components()
                    .any(|c| matches!(c, std::path::Component::ParentDir))
            {
                return Err(format!(
                    "simulated /nix/store executable path must be clean: {}",
                    exe.display()
                ));
            }
            let host_target = canon_store.join(rel);
            let canon_target = fs::canonicalize(&host_target).map_err(|e| {
                format!("canonicalize staged store executable {}: {e}", exe.display())
            })?;
            if !canon_target.starts_with(&canon_store) {
                return Err(format!(
                    "staged store executable escapes store_dir: {}",
                    exe.display()
                ));
            }
            (exe.to_path_buf(), None)
        } else {
            let canon_exe = fs::canonicalize(exe)
                .map_err(|e| format!("canonicalize target executable {}: {e}", exe.display()))?;
            let already_mounted = ["/usr", "/bin", "/lib", "/lib64", "/nix/store"]
                .into_iter()
                .any(|prefix| canon_exe.starts_with(prefix));
            let extra_bind = (!already_mounted).then(|| canon_exe.clone());
            (canon_exe, extra_bind)
        };

        let mut inv = Invocation::new(
            bwrap,
            &[
                "--unshare-all",
                "--die-with-parent",
                "--new-session",
                "--clearenv",
                "--cap-drop",
                "ALL",
                "--tmpfs",
                "/",
                "--dev",
                "/dev",
                "--proc",
                "/proc",
                "--ro-bind",
                "/usr",
                "/usr",
                "--ro-bind-try",
                "/bin",
                "/bin",
                "--ro-bind-try",
                "/lib",
                "/lib",
                "--ro-bind-try",
                "/lib64",
                "/lib64",
                "--ro-bind-try",
                "/etc/ld.so.cache",
                "/etc/ld.so.cache",
            ],
        );
        inv = inv
            .arg("--ro-bind")
            .arg(&canon_store)
            .arg("/nix/store")
            .arg("--dir")
            .arg("/work")
            .arg("--bind")
            .arg(&canon_work)
            .arg("/work")
            .arg("--chdir")
            .arg("/work");

        if let Some(host_exe) = &bind_host_exe {
            inv = inv.arg("--ro-bind").arg(host_exe).arg(host_exe);
        }
        for (src, dst) in &config.extra_ro_binds {
            inv = inv.arg("--ro-bind").arg(src).arg(dst);
        }
        for (k, v) in &config.environment {
            inv = inv.arg("--setenv").arg(k).arg(v);
        }
        inv = inv.arg("--").arg(&exec_in_sandbox);
        for arg in args {
            inv = inv.arg(arg);
        }

        let log_dir = staged.next_command_log_dir();
        staged
            .supervisor()
            .run(&inv, staged.work_dir(), &log_dir, staged.root_dir())
    }
}

fn write_exec(path: &Path, bytes: &[u8]) -> TestResult {
    fs::write(path, bytes).map_err(|e| format!("write {}: {e}", path.display()))?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(path, fs::Permissions::from_mode(0o755))
            .map_err(|e| format!("chmod {}: {e}", path.display()))?;
    }
    Ok(())
}

#[cfg(all(test, target_os = "linux"))]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn five_cell_elf_store_matches_runpath_rpath_rules_and_cleans_up() {
        let mut ws = WorkspaceBuilder::new("anneal-elf-5cell-", Duration::from_secs(5)).unwrap();
        let root_path = ws.root_dir().to_path_buf();
        let layout = ElfStoreBuilder::new(&mut ws, true)
            .build_five_cell_layout()
            .unwrap();

        // Check `rustc`, `librustc_driver` metadata, and `rustlib` symlink.
        let rustc_info = inspect_elf64(&layout.sysroot_dir.join("bin/rustc")).unwrap();
        assert_eq!(
            rustc_info.pt_interp.as_deref(),
            Some(layout.loader_path.to_str().unwrap())
        );
        assert_eq!(rustc_info.dt_runpath.as_deref(), Some("$ORIGIN/../lib"));
        assert!(layout
            .sysroot_dir
            .join("lib/rustlib/x86_64-unknown-linux-gnu/lib/libLLVM-21.so")
            .symlink_metadata()
            .unwrap()
            .file_type()
            .is_symlink());
        assert!(layout
            .gcc_lib_dir
            .join("lib/libgcc_s.so.1")
            .symlink_metadata()
            .unwrap()
            .file_type()
            .is_symlink());

        // Exercise all 5 cells under dynamic resolution rules.
        for (cell, consumer) in &layout.cell_consumers {
            let res = resolve_elf64_dependency_closure(consumer);
            match cell {
                ElfStoreCell::Cell1NonTransitiveRunpathFailure => {
                    assert!(res.is_err(), "Cell 1 must fail non-transitive DT_RUNPATH");
                }
                ElfStoreCell::Cell2AncestorRpathSuppressedByRunpath => {
                    assert!(
                        res.is_err(),
                        "Cell 2 must reject when intermediate DT_RUNPATH suppresses ancestor DT_RPATH"
                    );
                }
                ElfStoreCell::Cell3AncestorRpathFallback => {
                    let closure = res.expect("Cell 3 ancestor DT_RPATH must resolve leaf libz.so.1");
                    assert!(closure.iter().any(|p| p.ends_with("libz.so.1")));
                }
                ElfStoreCell::Cell4PreloadedDtNeeded => {
                    let closure = res.expect("Cell 4 preloaded DT_NEEDED must satisfy leaf");
                    assert!(closure.iter().any(|p| p.ends_with("libz.so.1")));
                }
                ElfStoreCell::Cell5OriginRelativeAndDedupSymlink => {
                    let closure = res.expect("Cell 5 $ORIGIN/../lib must resolve colocated libz.so.1");
                    assert!(closure.iter().any(|p| p.ends_with("libz.so.1")));
                }
            }
        }

        // Verify store/work disjointness and 0o555 store drop cleanup.
        let staged = ws.stage().unwrap();
        assert!(!staged.work_dir().starts_with(&layout.sysroot_dir));
        assert!(!staged.work_dir().starts_with(&layout.glibc_dir));
        staged.finish_with_options(Ok(()), false, None).unwrap();
        assert!(!root_path.exists());
    }

    #[test]
    fn simulated_nix_store_resolves_cross_package_lean_symlink_join_trees() {
        let mut ws = WorkspaceBuilder::new("anneal-nix-sim-", Duration::from_secs(10)).unwrap();
        let root_path = ws.root_dir().to_path_buf();

        ws.add_store_package("0001-lean-unwrapped", true, |pkg| {
            let init_dir = pkg.join("lib/lean");
            fs::create_dir_all(&init_dir).unwrap();
            fs::write(init_dir.join("Init.olean"), b"init-olean").unwrap();
            fs::write(init_dir.join("Init.olean.server"), b"init-server").unwrap();
            fs::write(init_dir.join("Init.olean.private"), b"init-private").unwrap();
            Ok(())
        })
        .unwrap();

        ws.add_store_package("0002-lean-joined", true, |pkg| {
            let joined_dir = pkg.join("lib/lean");
            fs::create_dir_all(&joined_dir).unwrap();
            for suffix in ["olean", "olean.server", "olean.private"] {
                std::os::unix::fs::symlink(
                    format!("../../../0001-lean-unwrapped/lib/lean/Init.{suffix}"),
                    joined_dir.join(format!("Init.{suffix}")),
                )
                .unwrap();
            }
            Ok(())
        })
        .unwrap();

        let staged = ws.stage().unwrap();
        let probe_script = r#"
import os, pathlib
joined = pathlib.Path('/nix/store/0002-lean-joined/lib/lean')
canon_root = pathlib.Path(os.path.realpath(joined))
assert str(canon_root).startswith('/nix/store/'), f'unexpected canon_root: {canon_root}'
for suffix, expected in [('olean', b'init-olean'), ('olean.server', b'init-server'), ('olean.private', b'init-private')]:
    p = joined / f'Init.{suffix}'
    target = pathlib.Path(os.path.realpath(p))
    assert str(target).startswith('/nix/store/0001-lean-unwrapped/'), f'bad target {target}'
    assert p.read_bytes() == expected
try:
    (joined / 'mutate').write_bytes(b'x')
    raise AssertionError('expected read-only /nix/store failure')
except OSError:
    pass
pathlib.Path('/work/probe-ok.txt').write_text('verified-nix-sim')
print('NIX_SIM_OK')
"#;
        let outcome = run_in_simulated_nix_store(
            &staged,
            Path::new("/usr/bin/python3"),
            &[OsStr::new("-c"), OsStr::new(probe_script)],
            &SimulatedStoreConfig::default(),
        )
        .unwrap();
        outcome.expect_code(0).unwrap();
        assert_eq!(String::from_utf8_lossy(&outcome.stdout).trim(), "NIX_SIM_OK");
        assert_eq!(
            fs::read_to_string(staged.work_dir().join("probe-ok.txt")).unwrap(),
            "verified-nix-sim"
        );

        staged.finish_with_options(Ok(()), false, None).unwrap();
        assert!(!root_path.exists());
    }

    #[test]
    fn elf_inspector_handles_multi_load_and_oob_strtab_and_nix_store_exe() {
        // Multi-segment lookup: first PT_LOAD starts above target vaddr, second
        // segment covers it.
        let loads = [(0x50_0000, 0x1000, 0x1000), (0x40_0000, 0x0, 0x2000)];
        assert_eq!(vaddr_to_offset(&loads, 0x40_0200, 0x40), Some(0x200));

        // Malformed ELF with oversized p_filesz/DT_STRSZ must not panic.
        let mut raw = build_elf64_image(&Elf64Spec {
            dt_needed: vec!["libz.so.1".into()],
            ..Default::default()
        });
        // Inflate PT_LOAD p_filesz and truncate tail to simulate an OOB slice.
        raw[64 + 32..64 + 40].copy_from_slice(&0xFFFFu64.to_le_bytes());
        raw.truncate(raw.len().saturating_sub(4));
        let malformed_dir = tempfile::tempdir().unwrap();
        let malformed_path = malformed_dir.path().join("malformed.elf");
        fs::write(&malformed_path, &raw).unwrap();
        let parsed = inspect_elf64(&malformed_path).unwrap();
        assert!(parsed.is_executable_or_dyn);

        // Execute a binary directly at `/nix/store/<pkg>/bin/...` inside bwrap.
        if !Path::new("/usr/bin/bwrap").is_file() {
            return;
        }
        let mut ws = WorkspaceBuilder::new("anneal-testkit-nixexe-", Duration::from_secs(10)).unwrap();
        ws.add_store_package("0009-tool", true, |pkg| {
            let bin = pkg.join("bin");
            fs::create_dir_all(&bin).map_err(|e| e.to_string())?;
            let script = bin.join("echo-argv0");
            write_exec(&script, b"#!/bin/sh\necho \"$0\"\n")
        })
        .unwrap();
        let staged = ws.stage().unwrap();
        let outcome = run_in_simulated_nix_store(
            &staged,
            Path::new("/nix/store/0009-tool/bin/echo-argv0"),
            &[],
            &SimulatedStoreConfig::default(),
        )
        .unwrap();
        outcome.expect_code(0).unwrap();
        assert_eq!(
            String::from_utf8_lossy(&outcome.stdout).trim(),
            "/nix/store/0009-tool/bin/echo-argv0"
        );
    }
}
