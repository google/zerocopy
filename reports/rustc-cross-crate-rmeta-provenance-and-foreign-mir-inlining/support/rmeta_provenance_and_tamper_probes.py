#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Reproducible probe suite for cross-crate .rmeta/.rlib provenance and tampering."""

import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


PROVENANCE_DRIVER_RS = r'''#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::CrateNum;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::{InstanceKind, TyCtxt};
use std::fs;
use std::os::unix::fs::MetadataExt;
use std::path::Path;

fn file_stat_json(p: &Path) -> String {
    match fs::metadata(p) {
        Ok(m) => format!(
            "{{\"path\":{:?},\"dev\":{},\"ino\":{},\"size\":{},\"mtime_nsec\":{}}}",
            p.display().to_string(),
            m.dev(),
            m.ino(),
            m.len(),
            m.mtime_nsec()
        ),
        Err(e) => format!("{{\"path\":{:?},\"error\":{:?}}}", p.display().to_string(), e.to_string()),
    }
}

fn collect_source_files(tcx: TyCtxt<'_>, filter_cnum: Option<CrateNum>) -> Vec<String> {
    let sm = tcx.sess.source_map();
    let files = sm.files();
    let mut out = Vec::new();
    for sf in files.iter() {
        if let Some(c) = filter_cnum {
            if sf.cnum != c {
                continue;
            }
        }
        let name = format!("{:?}", sf.name);
        let src_present = sf.src.is_some();
        let ext_present = sf.external_src.borrow().get_source().is_some();
        let src_hash = format!("{}", sf.src_hash);
        let checksum_hash = match sf.checksum_hash {
            Some(h) => format!("{:?}", format!("{}", h)),
            None => "null".to_string(),
        };
        out.push(format!(
            "{{\"cnum\":{},\"crate_name\":{:?},\"name\":{:?},\"src_present\":{},\"ext_src_loaded\":{},\"src_hash\":{:?},\"checksum_hash\":{}}}",
            sf.cnum.as_u32(),
            tcx.crate_name(sf.cnum).as_str(),
            name,
            src_present,
            ext_present,
            src_hash,
            checksum_hash
        ));
    }
    out
}

struct ProvenanceCallbacks;

impl Callbacks for ProvenanceCallbacks {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        // Optional hook to simulate mid-compilation rename swap of an rmeta/rlib file
        if let Ok(swap_spec) = std::env::var("SIMULATE_SWAP_BEFORE_AFTER_ANALYSIS") {
            let parts: Vec<&str> = swap_spec.split("::").collect();
            if parts.len() == 2 {
                let _ = fs::copy(parts[0], parts[1]);
            }
        }
        if let Ok(rename_spec) = std::env::var("SIMULATE_RENAME_BEFORE_AFTER_ANALYSIS") {
            let parts: Vec<&str> = rename_spec.split("::").collect();
            if parts.len() == 2 {
                let _ = fs::rename(parts[0], parts[1]);
            }
        }

        let target_crate = std::env::var("TARGET_CRATE").unwrap_or_else(|_| "upstream_mod".to_string());

        let mut target_cnum: Option<CrateNum> = None;
        let mut crates_json = Vec::new();

        for &cnum in tcx.crates(()) {
            let cname = tcx.crate_name(cnum).as_str().to_string();
            if cname == target_crate {
                target_cnum = Some(cnum);
            }
            let svh = tcx.crate_hash(cnum).to_hex();
            let stable_id = format!("{:?}", tcx.stable_crate_id(cnum));
            let src = tcx.used_crate_source(cnum);
            let rmeta_json = match &src.rmeta {
                Some(p) => file_stat_json(p),
                None => "null".to_string(),
            };
            let rlib_json = match &src.rlib {
                Some(p) => file_stat_json(p),
                None => "null".to_string(),
            };
            let dylib_json = match &src.dylib {
                Some(p) => file_stat_json(p),
                None => "null".to_string(),
            };
            crates_json.push(format!(
                "{{\"cnum\":{},\"name\":{:?},\"svh\":{:?},\"stable_crate_id\":{:?},\"rmeta\":{},\"rlib\":{},\"dylib\":{}}}",
                cnum.as_u32(),
                cname,
                svh,
                stable_id,
                rmeta_json,
                rlib_json,
                dylib_json
            ));
        }

        let before_import = collect_source_files(tcx, target_cnum);

        // Now force import_source_files for target_cnum (if found)
        if let Some(cnum) = target_cnum {
            tcx.import_source_files(cnum);
        }

        let after_import = collect_source_files(tcx, target_cnum);

        // Also inspect exported functions in target_cnum if any
        let mut fn_items_json = Vec::new();
        if let Some(cnum) = target_cnum {
            for child in tcx.module_children(cnum.as_def_id()) {
                if let Some(did) = child.res.opt_def_id() {
                    if matches!(tcx.def_kind(did), DefKind::Fn) {
                        let dpath = tcx.def_path_str(did);
                        let dhash = format!("{:?}", tcx.def_path_hash(did));
                        let mir_avail = tcx.is_mir_available(did);
                        let mut body_items = Vec::new();
                        if mir_avail {
                            let body = tcx.instance_mir(InstanceKind::Item(did));
                            for bb in body.basic_blocks.iter() {
                                for stmt in &bb.statements {
                                    body_items.push(format!("stmt:{:?}", stmt.kind));
                                }
                                if let Some(term) = &bb.terminator {
                                    body_items.push(format!("term:{:?}", term.kind));
                                }
                            }
                        }
                        let stmts_s: Vec<String> = body_items.iter().map(|s| format!("{:?}", s)).collect();
                        fn_items_json.push(format!(
                            "{{\"path\":{:?},\"def_path_hash\":{:?},\"is_mir_available\":{},\"mir_items\":[{}]}}",
                            dpath,
                            dhash,
                            mir_avail,
                            stmts_s.join(",")
                        ));
                    }
                }
            }
        }

        println!(
            "PROVENANCE_JSON:{{\"loaded_crates\":[{}],\"target_files_before_import\":[{}],\"target_files_after_import\":[{}],\"target_fns\":[{}]}}",
            crates_json.join(","),
            before_import.join(","),
            after_import.join(","),
            fn_items_json.join(",")
        );

        Compilation::Stop
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut callbacks = ProvenanceCallbacks;
    rustc_driver::compiler_entrypoint(&args, &mut callbacks);
}
'''


def get_toolchain_env():
    sysroot = subprocess.check_output(["rustc", "--print", "sysroot"], text=True).strip()
    env = os.environ.copy()
    lib_dir = os.path.join(sysroot, "lib")
    existing = env.get("LD_LIBRARY_PATH", "")
    env["LD_LIBRARY_PATH"] = f"{lib_dir}:{existing}" if existing else lib_dir
    return env, sysroot


def extract_json(stdout: str):
    for line in stdout.splitlines():
        if line.startswith("PROVENANCE_JSON:"):
            return json.loads(line[len("PROVENANCE_JSON:"):])
    raise RuntimeError(f"No PROVENANCE_JSON in output:\n{stdout}")


def sha256_file(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def md5_file(p: Path) -> str:
    return hashlib.md5(p.read_bytes()).hexdigest()


def scrub_temp_paths(obj, tmp_str: str, sysroot_str: str, cwd_str: str):
    if isinstance(obj, dict):
        return {k: scrub_temp_paths(v, tmp_str, sysroot_str, cwd_str) for k, v in obj.items()}
    elif isinstance(obj, list):
        return [scrub_temp_paths(x, tmp_str, sysroot_str, cwd_str) for x in obj]
    elif isinstance(obj, str):
        return (
            obj.replace(tmp_str, "<SCRATCH>")
            .replace(sysroot_str, "<SYSROOT>")
            .replace(cwd_str, "<WORKDIR>")
        )
    return obj


def main():
    env, sysroot = get_toolchain_env()
    rustc_v = subprocess.check_output(["rustc", "-vV"], text=True).strip()

    with tempfile.TemporaryDirectory(prefix="anneal_rmeta_probe_") as tmp:
        tmp_path = Path(tmp)
        driver_src = tmp_path / "provenance_driver.rs"
        driver_bin = tmp_path / "provenance_driver"
        driver_src.write_text(PROVENANCE_DRIVER_RS)

        subprocess.run(
            ["rustc", "--edition=2021", "-O", str(driver_src), "-o", str(driver_bin)],
            check=True,
            env=env,
        )

        # =====================================================================
        # Experiment 1: Selective encode_source_map & Lazy vs. Eager imported_source_files
        # =====================================================================
        exp1_dir = tmp_path / "exp1"
        exp1_src = exp1_dir / "src"
        exp1_src.mkdir(parents=True)

        (exp1_src / "lib.rs").write_text(
            "#![no_std]\n"
            "pub mod submodule;\n"
            "#[inline]\n"
            "pub fn used_in_downstream(x: u64) -> u64 { x.wrapping_add(1) }\n"
        )
        (exp1_src / "submodule.rs").write_text(
            "pub const DATA_STR: &str = include_str!(\"data.txt\");\n"
            "include!(\"included_fragment.rs\");\n"
            "pub fn unused_by_downstream(x: u64) -> u64 { x.wrapping_add(10) }\n"
        )
        (exp1_src / "data.txt").write_text("payload_from_include_str\n")
        (exp1_src / "included_fragment.rs").write_text(
            "pub fn from_included_fragment(x: u64) -> u64 { x.wrapping_add(20) }\n"
        )

        exp1_rlib = exp1_dir / "libupstream_mod.rlib"
        subprocess.run(
            [
                "rustc",
                "--crate-name=upstream_mod",
                "--crate-type=rlib",
                "--edition=2021",
                "-Z",
                "checksum-hash-algorithm=blake3",
                "-o",
                str(exp1_rlib),
                str(exp1_src / "lib.rs"),
            ],
            check=True,
            env=env,
        )

        downstream1 = exp1_dir / "downstream.rs"
        # Downstream only calls `used_in_downstream`, never referencing `submodule`
        downstream1.write_text(
            "#![no_std]\n"
            "extern crate upstream_mod;\n"
            "pub fn entry(x: u64) -> u64 { upstream_mod::used_in_downstream(x) }\n"
        )

        run_env = env.copy()
        run_env["TARGET_CRATE"] = "upstream_mod"
        proc1 = subprocess.run(
            [
                str(driver_bin),
                "--sysroot",
                sysroot,
                "--crate-type=rlib",
                "--edition=2021",
                "--extern",
                f"upstream_mod={exp1_rlib}",
                str(downstream1),
            ],
            capture_output=True,
            text=True,
            check=True,
            env=run_env,
        )
        exp1_res = extract_json(proc1.stdout)

        # =====================================================================
        # Experiment 2: Post-.rmeta Upstream .rs Tampering Without Rebuilding .rmeta
        # =====================================================================
        orig_lib_md5 = f"md5={md5_file(exp1_src / 'lib.rs')}"
        orig_sub_md5 = f"md5={md5_file(exp1_src / 'submodule.rs')}"

        # Tamper with both lib.rs and submodule.rs on disk without rebuilding libupstream_mod.rlib
        (exp1_src / "lib.rs").write_text(
            "#![no_std]\n"
            "pub mod submodule;\n"
            "#[inline]\n"
            "pub fn used_in_downstream(x: u64) -> u64 { x.wrapping_add(999999) }\n"
        )
        (exp1_src / "submodule.rs").write_text(
            "pub const DATA_STR: &str = \"tampered\";\n"
            "pub fn unused_by_downstream(x: u64) -> u64 { 0 }\n"
        )
        tampered_lib_md5 = f"md5={md5_file(exp1_src / 'lib.rs')}"
        tampered_sub_md5 = f"md5={md5_file(exp1_src / 'submodule.rs')}"

        # Standard rustc compilation succeeds silently with 0 errors
        std_rustc_proc = subprocess.run(
            [
                "rustc",
                "--crate-type=rlib",
                "--edition=2021",
                "--extern",
                f"upstream_mod={exp1_rlib}",
                "-o",
                str(exp1_dir / "libdownstream.rlib"),
                str(downstream1),
            ],
            capture_output=True,
            text=True,
            env=env,
        )

        proc2 = subprocess.run(
            [
                str(driver_bin),
                "--sysroot",
                sysroot,
                "--crate-type=rlib",
                "--edition=2021",
                "--extern",
                f"upstream_mod={exp1_rlib}",
                str(downstream1),
            ],
            capture_output=True,
            text=True,
            check=True,
            env=run_env,
        )
        exp2_res = extract_json(proc2.stdout)

        # =====================================================================
        # Experiment 3: Trojan .rmeta/.rlib Substitution (Same StableCrateId vs. SVH)
        # =====================================================================
        exp3_dir = tmp_path / "exp3"
        exp3_v1_dir = exp3_dir / "v1"
        exp3_v2_dir = exp3_dir / "v2"
        exp3_mid_dir = exp3_dir / "mid"
        exp3_v1_dir.mkdir(parents=True)
        exp3_v2_dir.mkdir(parents=True)
        exp3_mid_dir.mkdir(parents=True)

        v1_src = exp3_v1_dir / "upstream.rs"
        v2_src = exp3_v2_dir / "upstream.rs"
        v1_src.write_text("#![no_std]\npub fn compute(x: u64) -> u64 { x.wrapping_add(1) }\n")
        v2_src.write_text("#![no_std]\npub fn compute(x: u64) -> u64 { x.wrapping_add(999) }\n")

        v1_rlib = exp3_v1_dir / "libupstream.rlib"
        v2_rlib = exp3_v2_dir / "libupstream.rlib"

        for src, out_rlib in [(v1_src, v1_rlib), (v2_src, v2_rlib)]:
            subprocess.run(
                [
                    "rustc",
                    "--crate-name=upstream",
                    "--crate-type=rlib",
                    "--edition=2021",
                    "-C",
                    "metadata=fixed_seed_123",
                    "-Z",
                    "always-encode-mir=yes",
                    "-o",
                    str(out_rlib),
                    str(src),
                ],
                check=True,
                env=env,
            )

        # Build middle crate `mid` against v1
        mid_src = exp3_mid_dir / "mid.rs"
        mid_src.write_text(
            "#![no_std]\n"
            "extern crate upstream;\n"
            "pub fn mid_call(x: u64) -> u64 { upstream::compute(x) }\n"
        )
        mid_rlib = exp3_mid_dir / "libmid.rlib"
        subprocess.run(
            [
                "rustc",
                "--crate-name=mid",
                "--crate-type=rlib",
                "--edition=2021",
                "--extern",
                f"upstream={v1_rlib}",
                "-o",
                str(mid_rlib),
                str(mid_src),
            ],
            check=True,
            env=env,
        )

        # Inspect direct downstream compilation against v1 vs. swapped v2
        down3_src = exp3_dir / "down3.rs"
        down3_src.write_text(
            "#![no_std]\n"
            "extern crate upstream;\n"
            "pub fn run(x: u64) -> u64 { upstream::compute(x) }\n"
        )
        env3 = env.copy()
        env3["TARGET_CRATE"] = "upstream"

        proc3_v1 = subprocess.run(
            [
                str(driver_bin),
                "--sysroot",
                sysroot,
                "--crate-type=rlib",
                "--edition=2021",
                "--extern",
                f"upstream={v1_rlib}",
                str(down3_src),
            ],
            capture_output=True,
            text=True,
            check=True,
            env=env3,
        )
        proc3_v2 = subprocess.run(
            [
                str(driver_bin),
                "--sysroot",
                sysroot,
                "--crate-type=rlib",
                "--edition=2021",
                "--extern",
                f"upstream={v2_rlib}",
                str(down3_src),
            ],
            capture_output=True,
            text=True,
            check=True,
            env=env3,
        )

        # Diamond dependency: downstream -> mid (built against v1) + -L pointing to v2
        down3_diamond_src = exp3_dir / "down3_diamond.rs"
        down3_diamond_src.write_text(
            "#![no_std]\n"
            "extern crate mid;\n"
            "pub fn run(x: u64) -> u64 { mid::mid_call(x) }\n"
        )
        proc3_diamond_swap = subprocess.run(
            [
                "rustc",
                "--crate-type=rlib",
                "--edition=2021",
                "--extern",
                f"mid={mid_rlib}",
                "-L",
                f"dependency={exp3_v2_dir}",
                "-o",
                str(exp3_dir / "libdown3_diamond.rlib"),
                str(down3_diamond_src),
            ],
            capture_output=True,
            text=True,
            env=env,
        )

        # Case 3C: Forge CrateHeader.hash (SVH) inside v2_rlib by overwriting the 16-byte LE Fingerprint
        v1_json = extract_json(proc3_v1.stdout)
        v2_json = extract_json(proc3_v2.stdout)
        svh_v1_hex = [c["svh"] for c in v1_json["loaded_crates"] if c["name"] == "upstream"][0]
        svh_v2_hex = [c["svh"] for c in v2_json["loaded_crates"] if c["name"] == "upstream"][0]
        svh_v1_le = int(svh_v1_hex, 16).to_bytes(16, "little")
        svh_v2_le = int(svh_v2_hex, 16).to_bytes(16, "little")

        exp3_forged_dir = exp3_dir / "v2_forged_svh"
        exp3_forged_dir.mkdir(parents=True)
        forged_rlib = exp3_forged_dir / "libupstream.rlib"
        raw_v2 = v2_rlib.read_bytes()
        svh_occurrences = raw_v2.count(svh_v2_le)
        forged_bytes = raw_v2.replace(svh_v2_le, svh_v1_le)
        forged_rlib.write_bytes(forged_bytes)

        proc3_diamond_forged = subprocess.run(
            [
                str(driver_bin),
                "--sysroot",
                sysroot,
                "--crate-type=rlib",
                "--edition=2021",
                "--extern",
                f"mid={mid_rlib}",
                "-L",
                f"dependency={exp3_forged_dir}",
                str(down3_diamond_src),
            ],
            capture_output=True,
            text=True,
            check=True,
            env=env3,
        )
        forged_json = extract_json(proc3_diamond_forged.stdout)

        # =====================================================================
        # Experiment 4: .rmeta vs .rlib Priority Ambiguity & Mmap Unlinked-Inode TOCTOU
        # =====================================================================
        exp4_dir = tmp_path / "exp4"
        exp4_dir.mkdir(parents=True)

        # Place BOTH libupstream.rmeta and libupstream.rlib in exp4_dir
        # Case 4A: Emit both from same build and check which one CrateLocator opens for rlib vs bin
        subprocess.run(
            [
                "rustc",
                "--crate-name=upstream",
                "--crate-type=rlib",
                "--emit=metadata,link",
                "--edition=2021",
                "-C",
                "metadata=fixed_seed_123",
                "-Z",
                "always-encode-mir=yes",
                "--out-dir",
                str(exp4_dir),
                str(v1_src),
            ],
            check=True,
            env=env,
        )

        proc4_rlib_mode = subprocess.run(
            [
                str(driver_bin),
                "--sysroot",
                sysroot,
                "--crate-type=rlib",
                "--edition=2021",
                "-L",
                str(exp4_dir),
                str(down3_src),
            ],
            capture_output=True,
            text=True,
            check=True,
            env=env3,
        )

        down4_bin_src = exp4_dir / "down4_bin.rs"
        down4_bin_src.write_text(
            "extern crate upstream;\n"
            "fn main() { let _ = upstream::compute(1); }\n"
        )
        proc4_bin_mode = subprocess.run(
            [
                str(driver_bin),
                "--sysroot",
                sysroot,
                "--crate-type=bin",
                "--edition=2021",
                "-L",
                str(exp4_dir),
                str(down4_bin_src),
            ],
            capture_output=True,
            text=True,
            check=True,
            env=env3,
        )

        # Case 4B: Simulate atomic rename(2) swap of libupstream.rmeta while rustc_driver is active
        rmeta_live = exp4_dir / "libupstream.rmeta"
        rmeta_v2_stage = exp4_dir / "libupstream_v2.rmeta.stage"
        subprocess.run(
            [
                "rustc",
                "--crate-name=upstream",
                "--crate-type=rlib",
                "--emit=metadata",
                "--edition=2021",
                "-C",
                "metadata=fixed_seed_123",
                "-Z",
                "always-encode-mir=yes",
                "-o",
                str(rmeta_v2_stage),
                str(v2_src),
            ],
            check=True,
            env=env,
        )

        pre_stat = os.stat(rmeta_live)
        pre_sha256 = sha256_file(rmeta_live)

        env4_swap = env3.copy()
        env4_swap["SIMULATE_RENAME_BEFORE_AFTER_ANALYSIS"] = f"{rmeta_v2_stage}::{rmeta_live}"
        proc4_toctou = subprocess.run(
            [
                str(driver_bin),
                "--sysroot",
                sysroot,
                "--crate-type=rlib",
                "--edition=2021",
                "--extern",
                f"upstream={rmeta_live}",
                str(down3_src),
            ],
            capture_output=True,
            text=True,
            check=True,
            env=env4_swap,
        )
        post_stat = os.stat(rmeta_live)
        post_sha256 = sha256_file(rmeta_live)
        toctou_json = extract_json(proc4_toctou.stdout)

        summary = {
            "rustc_version": rustc_v,
            "experiment_1_selective_and_lazy_source_map": {
                "files_in_source_map_before_explicit_import": exp1_res["target_files_before_import"],
                "files_in_source_map_after_explicit_import": exp1_res["target_files_after_import"],
                "include_str_data_txt_encoded_in_rmeta": any(
                    "data.txt" in f["name"] for f in exp1_res["target_files_after_import"]
                ),
                "include_rs_fragment_encoded_in_rmeta": any(
                    "included_fragment.rs" in f["name"] for f in exp1_res["target_files_after_import"]
                ),
                "unreferenced_submodule_encoded_in_rmeta": any(
                    "submodule.rs" in f["name"] for f in exp1_res["target_files_after_import"]
                ),
            },
            "experiment_2_post_rmeta_source_tampering": {
                "standard_rustc_exit_code": std_rustc_proc.returncode,
                "standard_rustc_stderr": std_rustc_proc.stderr,
                "original_disk_hashes": {"lib.rs": orig_lib_md5, "submodule.rs": orig_sub_md5},
                "tampered_disk_hashes": {"lib.rs": tampered_lib_md5, "submodule.rs": tampered_sub_md5},
                "rmeta_imported_source_files": exp2_res["target_files_after_import"],
            },
            "experiment_3_trojan_rmeta_and_svh": {
                "v1_direct_load": v1_json,
                "v2_trojan_direct_load": v2_json,
                "diamond_swap_exit_code": proc3_diamond_swap.returncode,
                "diamond_swap_stderr": proc3_diamond_swap.stderr.strip(),
                "forged_svh_in_v2_rlib": {
                    "svh_v2_le_occurrences_replaced": svh_occurrences,
                    "diamond_compile_with_forged_svh_succeeded": proc3_diamond_forged.returncode == 0,
                    "v1_rlib_sha256": sha256_file(v1_rlib),
                    "forged_v2_rlib_sha256": sha256_file(forged_rlib),
                    "loaded_state": forged_json,
                },
            },
            "experiment_4_rmeta_rlib_priority_and_mmap_toctou": {
                "dual_candidate_rlib_crate_type_used_source": [
                    c for c in extract_json(proc4_rlib_mode.stdout)["loaded_crates"] if c["name"] == "upstream"
                ],
                "dual_candidate_dylib_crate_type_used_source": [
                    c for c in extract_json(proc4_bin_mode.stdout)["loaded_crates"] if c["name"] == "upstream"
                ],
                "mmap_rename_toctou": {
                    "pre_run_stat": {
                        "dev": pre_stat.st_dev,
                        "ino": pre_stat.st_ino,
                        "size": pre_stat.st_size,
                        "sha256": pre_sha256,
                    },
                    "post_run_stat_on_same_path": {
                        "dev": post_stat.st_dev,
                        "ino": post_stat.st_ino,
                        "size": post_stat.st_size,
                        "sha256": post_sha256,
                    },
                    "compiler_decoded_during_after_analysis": toctou_json,
                },
            },
        }

        summary = scrub_temp_paths(summary, str(tmp_path), sysroot, os.getcwd())

        if len(sys.argv) > 1:
            Path(sys.argv[1]).write_text(json.dumps(summary, indent=2) + "\n")
        else:
            print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
