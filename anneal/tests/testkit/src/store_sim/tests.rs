// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Tests for the split-store and ELF simulation helpers.

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
