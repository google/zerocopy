// Self-contained probe verifying the `rustc` (`1.101.0-nightly`) query,
// monomorphization, and ELF/linker mechanics documented in `REPORT.md`:
//
// 1. `tcx.def_path_str(def_id)` -> `trimmed_def_paths` -> `DiagCtxtInner::drop`
//    ICE when compilation completes without diagnostics (and why `--emit=mir`
//    masks it, while `with_no_trimmed_paths!(tcx.def_path_str(def_id))` and
//    `tcx.def_path_debug_str(def_id)` avoid it).
// 2. `tcx.item_name(def_id)` ICE on `DefKind::Closure` versus
//    `tcx.opt_item_name(def_id)` + `mono_item.symbol_name(tcx).name`.
// 3. Polymorphic `tcx.instance_mir(instance.def)` bodies, two-argument
//    `ty::EarlyBinder::bind(tcx, value)`,
//    `instance.instantiate_mir_and_normalize_erasing_regions`, and
//    `!has_non_region_param()` guards on `layout_of` / `Instance::try_resolve`.
// 4. `CrateType::Dylib` facade-crate (`librustc_driver.so`) archive-member
//    dropping in `rust-lld -flavor gnu -m elf64lriscv -shared` without
//    `--whole-archive`, versus retaining all `.rlib` members with
//    `--whole-archive ... --no-whole-archive`, and cross-CGU `STB_LOCAL` vs.
//    `STB_GLOBAL` symbol resolution.

#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_interface::interface;
use rustc_middle::mono::MonoItem;
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};

const SAMPLE_CRATE_SRC: &str = r#"
#![allow(dead_code)]

#[inline(never)]
pub fn poly_size_add<T: Copy>(x: T, acc: u64) -> u64 {
    let _keep = x;
    acc.wrapping_add(core::mem::size_of::<T>() as u64)
}

pub fn run_sample(seed: u64) -> u64 {
    let bump = |v: u64| v.wrapping_add(seed);
    let a = poly_size_add([0u64; 4], bump(10));
    let b = poly_size_add(7u32, a);
    b
}

fn main() {
    let out = run_sample(5);
    if out == 0 {
        core::hint::black_box(out);
    }
}
"#;

struct SafeCodegenProbeCallbacks;

impl Callbacks for SafeCodegenProbeCallbacks {
    fn config(&mut self, config: &mut interface::Config) {
        // Mirror `TimePassesCallbacks::config` (`rustc_driver_impl/src/lib.rs:161-168`),
        // which sets `config.opts.trimmed_def_paths = true` in standard `rustc` invocations.
        config.opts.trimmed_def_paths = true;
    }

    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        let crate_name = tcx.crate_name(LOCAL_CRATE);
        let cgus = tcx.collect_and_partition_mono_items(()).codegen_units;
        let mut closure_count = 0usize;
        let mut poly_fn_checked = false;

        for cgu in cgus {
            for (mono_item, _data) in cgu.items() {
                if let MonoItem::Fn(instance) = *mono_item {
                    let did = instance.def_id();
                    let sym = mono_item.symbol_name(tcx).name;

                    // Safe diagnostic-independent path formatting:
                    let no_trim_path = with_no_trimmed_paths!(tcx.def_path_str(did));
                    let debug_path = tcx.def_path_debug_str(did);
                    assert!(!no_trim_path.is_empty() && !debug_path.is_empty());

                    // Closure DefIds have no item_name (`opt_item_name` returns `None`).
                    let opt_name = tcx.opt_item_name(did);
                    if matches!(tcx.def_kind(did), DefKind::Closure) {
                        assert!(
                            opt_name.is_none(),
                            "DefKind::Closure must return None from opt_item_name"
                        );
                        closure_count += 1;
                    }

                    // Check polymorphic `instance_mir` vs. `instantiate_mir_and_normalize_erasing_regions`.
                    if no_trim_path.contains("poly_size_add") && !instance.args.is_empty() {
                        let raw_body = tcx.instance_mir(instance.def);
                        // Local _1 (`x: T`) in the uninstantiated `instance_mir` still has `TyKind::Param`.
                        let raw_arg_ty = raw_body.local_decls[rustc_middle::mir::Local::from_usize(1)].ty;
                        assert!(
                            raw_arg_ty.has_non_region_param(),
                            "uninstantiated instance_mir local _1 must still have a type parameter"
                        );

                        // Querying layout_of on the uninstantiated `raw_arg_ty` under
                        // `TypingEnv::fully_monomorphized()` fails with `LayoutError::TooGeneric`.
                        let raw_layout = tcx.layout_of(
                            ty::TypingEnv::fully_monomorphized().as_query_input(raw_arg_ty),
                        );
                        assert!(
                            raw_layout.is_err(),
                            "layout_of on uninstantiated TyKind::Param must fail"
                        );

                        // Substituting via 2-argument `ty::EarlyBinder::bind(tcx, raw_arg_ty)`
                        // produces a concrete type with known layout.
                        let inst_arg_ty = instance.instantiate_mir_and_normalize_erasing_regions(
                            tcx,
                            ty::TypingEnv::fully_monomorphized(),
                            ty::EarlyBinder::bind(tcx, raw_arg_ty),
                        );
                        assert!(
                            !inst_arg_ty.has_non_region_param(),
                            "instantiated type must not contain non-region parameters"
                        );
                        let inst_layout = tcx
                            .layout_of(
                                ty::TypingEnv::fully_monomorphized().as_query_input(inst_arg_ty),
                            )
                            .expect("layout_of on substituted concrete type must succeed");
                        println!(
                            "[probe:poly] symbol={} raw_ty={:?} inst_ty={:?} size_bytes={}",
                            sym,
                            raw_arg_ty,
                            inst_arg_ty,
                            inst_layout.size.bytes()
                        );
                        poly_fn_checked = true;
                    }
                }
            }
        }

        assert!(closure_count >= 1, "expected at least one monomorphized closure");
        assert!(poly_fn_checked, "expected to inspect polymorphic poly_size_add instance");
        println!(
            "[probe:safe_path] crate={} cgus={} closures_verified={} must_produce_diag=false",
            crate_name,
            cgus.len(),
            closure_count
        );
        Compilation::Stop
    }
}

struct UnwrappedDefPathStrCallbacks;

impl Callbacks for UnwrappedDefPathStrCallbacks {
    fn config(&mut self, config: &mut interface::Config) {
        config.opts.trimmed_def_paths = true;
    }

    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        let cgus = tcx.collect_and_partition_mono_items(()).codegen_units;
        for cgu in cgus {
            for (mono_item, _data) in cgu.items() {
                if let MonoItem::Fn(instance) = *mono_item {
                    // Unwrapped `tcx.def_path_str` during normal compilation (without
                    // `--emit=mir`) invokes `tcx.trimmed_def_paths(())` ->
                    // `tcx.sess.record_trimmed_def_paths()` ->
                    // `tcx.dcx().set_must_produce_diag()`.
                    let _s = tcx.def_path_str(instance.def_id());
                }
            }
        }
        Compilation::Stop
    }
}

struct ClosureItemNameCallbacks;

impl Callbacks for ClosureItemNameCallbacks {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        let cgus = tcx.collect_and_partition_mono_items(()).codegen_units;
        for cgu in cgus {
            for (mono_item, _data) in cgu.items() {
                if let MonoItem::Fn(instance) = *mono_item {
                    let did = instance.def_id();
                    if matches!(tcx.def_kind(did), DefKind::Closure) {
                        let _ = tcx.item_name(did);
                    }
                }
            }
        }
        Compilation::Stop
    }
}

fn find_sysroot() -> String {
    let out = Command::new("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .expect("rustc --print sysroot");
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

/// Emit a minimal 64-bit little-endian RISC-V (`EM_RISCV = 243`, `EF_RISCV_RVC |
/// EF_RISCV_FLOAT_ABI_DOUBLE = 0x5`) relocatable object (`.o`) with a single
/// symbol in `.text` (`jalr x0, x1, 0` = `0x00008067`) and an optional undefined
/// external symbol reference.
fn write_minimal_rv64_elf_o(
    path: &Path,
    defined_sym: &str,
    defined_is_global: bool,
    undef_sym: Option<&str>,
) {
    // `.text`: `addi a0, zero, 42` (`0x02a00513`), `ret` (`0x00008067`)
    let text_bytes: [u8; 8] = [0x13, 0x05, 0xa0, 0x02, 0x67, 0x80, 0x00, 0x00];

    let mut shstrtab = Vec::new();
    shstrtab.push(0u8);
    let sh_name_text = shstrtab.len() as u32;
    shstrtab.extend_from_slice(b".text\0");
    let sh_name_symtab = shstrtab.len() as u32;
    shstrtab.extend_from_slice(b".symtab\0");
    let sh_name_strtab = shstrtab.len() as u32;
    shstrtab.extend_from_slice(b".strtab\0");
    let sh_name_shstrtab = shstrtab.len() as u32;
    shstrtab.extend_from_slice(b".shstrtab\0");
    let sh_name_rela_text = shstrtab.len() as u32;
    if undef_sym.is_some() {
        shstrtab.extend_from_slice(b".rela.text\0");
    }
    while shstrtab.len() % 8 != 0 {
        shstrtab.push(0);
    }

    let mut strtab = Vec::new();
    strtab.push(0u8);
    let st_name_def = strtab.len() as u32;
    strtab.extend_from_slice(defined_sym.as_bytes());
    strtab.push(0);
    let st_name_undef = if let Some(u) = undef_sym {
        let off = strtab.len() as u32;
        strtab.extend_from_slice(u.as_bytes());
        strtab.push(0);
        off
    } else {
        0
    };
    while strtab.len() % 8 != 0 {
        strtab.push(0);
    }

    // Build `.symtab`:
    // Notice ELF rule: all STB_LOCAL symbols must precede STB_GLOBAL symbols,
    // and `sh_info` on `.symtab` is the index of the first non-local symbol.
    let mut symtab = Vec::new();
    let push_sym = |buf: &mut Vec<u8>,
                    st_name: u32,
                    st_info: u8,
                    st_other: u8,
                    st_shndx: u16,
                    st_value: u64,
                    st_size: u64| {
        buf.extend_from_slice(&st_name.to_le_bytes());
        buf.push(st_info);
        buf.push(st_other);
        buf.extend_from_slice(&st_shndx.to_le_bytes());
        buf.extend_from_slice(&st_value.to_le_bytes());
        buf.extend_from_slice(&st_size.to_le_bytes());
    };
    // [0] null symbol
    push_sym(&mut symtab, 0, 0, 0, 0, 0, 0);

    let first_global_idx: u32;
    let undef_sym_idx: u32;
    if defined_is_global {
        first_global_idx = 1;
        // [1] defined global function (`STB_GLOBAL = 1`, `STT_FUNC = 2` -> `0x12`)
        push_sym(&mut symtab, st_name_def, 0x12, 0, 1, 0, 8);
        if undef_sym.is_some() {
            undef_sym_idx = 2;
            push_sym(&mut symtab, st_name_undef, 0x10, 0, 0, 0, 0);
        } else {
            undef_sym_idx = 0;
        }
    } else {
        // [1] defined local function (`STB_LOCAL = 0`, `STT_FUNC = 2` -> `0x02`)
        push_sym(&mut symtab, st_name_def, 0x02, 0, 1, 0, 8);
        first_global_idx = 2;
        if undef_sym.is_some() {
            undef_sym_idx = 2;
            push_sym(&mut symtab, st_name_undef, 0x10, 0, 0, 0, 0);
        } else {
            undef_sym_idx = 0;
        }
    }

    let mut rela_bytes = Vec::new();
    if undef_sym.is_some() {
        // `R_RISCV_CALL_PLT = 19` at offset 0 referencing `undef_sym_idx`
        let r_offset: u64 = 0;
        let r_info: u64 = ((undef_sym_idx as u64) << 32) | 19u64;
        let r_addend: i64 = 0;
        rela_bytes.extend_from_slice(&r_offset.to_le_bytes());
        rela_bytes.extend_from_slice(&r_info.to_le_bytes());
        rela_bytes.extend_from_slice(&r_addend.to_le_bytes());
    }

    let num_sections: u16 = if undef_sym.is_some() { 6 } else { 5 };
    let text_off: u64 = 64;
    let symtab_off: u64 = text_off + text_bytes.len() as u64;
    let strtab_off: u64 = symtab_off + symtab.len() as u64;
    let shstrtab_off: u64 = strtab_off + strtab.len() as u64;
    let rela_off: u64 = shstrtab_off + shstrtab.len() as u64;
    let shoff: u64 = rela_off + rela_bytes.len() as u64;

    let mut elf = Vec::new();
    // ELF64 header
    elf.extend_from_slice(&[
        0x7f, b'E', b'L', b'F', 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ]);
    elf.extend_from_slice(&1u16.to_le_bytes()); // ET_REL
    elf.extend_from_slice(&243u16.to_le_bytes()); // EM_RISCV
    elf.extend_from_slice(&1u32.to_le_bytes()); // EV_CURRENT
    elf.extend_from_slice(&0u64.to_le_bytes()); // e_entry
    elf.extend_from_slice(&0u64.to_le_bytes()); // e_phoff
    elf.extend_from_slice(&shoff.to_le_bytes()); // e_shoff
    elf.extend_from_slice(&0x5u32.to_le_bytes()); // e_flags: RVC | double-float ABI
    elf.extend_from_slice(&64u16.to_le_bytes()); // e_ehsize
    elf.extend_from_slice(&0u16.to_le_bytes()); // e_phentsize
    elf.extend_from_slice(&0u16.to_le_bytes()); // e_phnum
    elf.extend_from_slice(&64u16.to_le_bytes()); // e_shentsize
    elf.extend_from_slice(&num_sections.to_le_bytes()); // e_shnum
    elf.extend_from_slice(&4u16.to_le_bytes()); // e_shstrndx = 4

    elf.extend_from_slice(&text_bytes);
    elf.extend_from_slice(&symtab);
    elf.extend_from_slice(&strtab);
    elf.extend_from_slice(&shstrtab);
    elf.extend_from_slice(&rela_bytes);

    let push_shdr = |buf: &mut Vec<u8>,
                     sh_name: u32,
                     sh_type: u32,
                     sh_flags: u64,
                     sh_offset: u64,
                     sh_size: u64,
                     sh_link: u32,
                     sh_info: u32,
                     sh_addralign: u64,
                     sh_entsize: u64| {
        buf.extend_from_slice(&sh_name.to_le_bytes());
        buf.extend_from_slice(&sh_type.to_le_bytes());
        buf.extend_from_slice(&sh_flags.to_le_bytes());
        buf.extend_from_slice(&0u64.to_le_bytes()); // sh_addr
        buf.extend_from_slice(&sh_offset.to_le_bytes());
        buf.extend_from_slice(&sh_size.to_le_bytes());
        buf.extend_from_slice(&sh_link.to_le_bytes());
        buf.extend_from_slice(&sh_info.to_le_bytes());
        buf.extend_from_slice(&sh_addralign.to_le_bytes());
        buf.extend_from_slice(&sh_entsize.to_le_bytes());
    };

    // [0] NULL
    push_shdr(&mut elf, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    // [1] .text (SHT_PROGBITS = 1, SHF_ALLOC | SHF_EXECINSTR = 6)
    push_shdr(
        &mut elf,
        sh_name_text,
        1,
        6,
        text_off,
        text_bytes.len() as u64,
        0,
        0,
        4,
        0,
    );
    // [2] .symtab (SHT_SYMTAB = 2, link = 3 (.strtab), info = first_global_idx)
    push_shdr(
        &mut elf,
        sh_name_symtab,
        2,
        0,
        symtab_off,
        symtab.len() as u64,
        3,
        first_global_idx,
        8,
        24,
    );
    // [3] .strtab (SHT_STRTAB = 3)
    push_shdr(
        &mut elf,
        sh_name_strtab,
        3,
        0,
        strtab_off,
        strtab.len() as u64,
        0,
        0,
        1,
        0,
    );
    // [4] .shstrtab (SHT_STRTAB = 3)
    push_shdr(
        &mut elf,
        sh_name_shstrtab,
        3,
        0,
        shstrtab_off,
        shstrtab.len() as u64,
        0,
        0,
        1,
        0,
    );
    // [5] optional .rela.text (SHT_RELA = 4, SHF_INFO_LINK = 0x40, link = 2, info = 1)
    if undef_sym.is_some() {
        push_shdr(
            &mut elf,
            sh_name_rela_text,
            4,
            0x40,
            rela_off,
            rela_bytes.len() as u64,
            2,
            1,
            8,
            24,
        );
    }

    fs::write(path, elf).expect("write minimal RV64 ELF .o");
}

fn verify_dylib_whole_archive_and_cgu_binding(sysroot: &str, workdir: &Path) {
    let rust_lld = PathBuf::from(sysroot).join("lib/rustlib/x86_64-unknown-linux-gnu/bin/rust-lld");
    assert!(rust_lld.exists(), "rust-lld must exist in sysroot");

    let rmeta_o = workdir.join("rmeta.o");
    let impl_cgu0_o = workdir.join("impl_cgu0.o");
    let impl_cgu1_local_o = workdir.join("impl_cgu1_local.o");
    let impl_cgu1_global_o = workdir.join("impl_cgu1_global.o");
    let rlib_local = workdir.join("librustc_driver_impl_local.rlib");
    let rlib_global = workdir.join("librustc_driver_impl_global.rlib");
    let so_no_whole = workdir.join("librustc_driver_no_whole.so");
    let so_whole_local = workdir.join("librustc_driver_whole_local.so");
    let so_whole_global = workdir.join("librustc_driver_whole_global.so");

    // `rmeta.o` represents `rustc_driver`'s metadata wrapper object (0 references to
    // `rustc_driver_impl`).
    write_minimal_rv64_elf_o(&rmeta_o, "rustc_metadata_sym", true, None);
    // `impl_cgu0.o` defines `rustc_driver_impl_main` (global) and references
    // `cgu1_internal_helper` in `impl_cgu1.o`.
    write_minimal_rv64_elf_o(
        &impl_cgu0_o,
        "rustc_driver_impl_main",
        true,
        Some("cgu1_internal_helper"),
    );
    // `impl_cgu1_local.o` defines `cgu1_internal_helper` as STB_LOCAL (`is_global = false`).
    write_minimal_rv64_elf_o(&impl_cgu1_local_o, "cgu1_internal_helper", false, None);
    // `impl_cgu1_global.o` defines `cgu1_internal_helper` as STB_GLOBAL (`is_global = true`).
    write_minimal_rv64_elf_o(&impl_cgu1_global_o, "cgu1_internal_helper", true, None);

    let _ = fs::remove_file(&rlib_local);
    let _ = fs::remove_file(&rlib_global);
    assert!(
        Command::new("ar")
            .arg("crs")
            .arg(&rlib_local)
            .arg(&impl_cgu0_o)
            .arg(&impl_cgu1_local_o)
            .status()
            .unwrap()
            .success()
    );
    assert!(
        Command::new("ar")
            .arg("crs")
            .arg(&rlib_global)
            .arg(&impl_cgu0_o)
            .arg(&impl_cgu1_global_o)
            .status()
            .unwrap()
            .success()
    );

    // Case A: Link `CrateType::Dylib` (`librustc_driver.so`) WITHOUT `--whole-archive`.
    // Because `rmeta.o` has no undefined reference to `rustc_driver_impl_main`,
    // `rust-lld` drops all members of `librustc_driver_impl_global.rlib`!
    assert!(
        Command::new(&rust_lld)
            .args(["-flavor", "gnu", "-m", "elf64lriscv", "-shared"])
            .arg(&rmeta_o)
            .arg(&rlib_global)
            .arg("-o")
            .arg(&so_no_whole)
            .status()
            .unwrap()
            .success()
    );
    let dynsym_no_whole = String::from_utf8(
        Command::new("readelf")
            .args(["--dyn-syms", "-W"])
            .arg(&so_no_whole)
            .output()
            .unwrap()
            .stdout,
    )
    .unwrap();
    assert!(
        !dynsym_no_whole.contains("rustc_driver_impl_main"),
        "without --whole-archive, unreferenced .rlib archive members are dropped from Dylib"
    );
    println!(
        "[probe:link_case_a] without --whole-archive: rustc_driver_impl_main present_in_dynsym=false"
    );

    // Case B: Link WITH `--whole-archive --no-undefined`, when `cgu1_internal_helper`
    // is `STB_LOCAL` in CGU 1. Cross-CGU reference from `impl_cgu0.o` to
    // `impl_cgu1_local.o` fails with `undefined symbol: cgu1_internal_helper`
    // (or leaves an unresolved `UND` entry in `.dynsym` if `--no-undefined` is omitted).
    let out_local = Command::new(&rust_lld)
        .args([
            "-flavor",
            "gnu",
            "-m",
            "elf64lriscv",
            "-shared",
            "--no-undefined",
        ])
        .arg(&rmeta_o)
        .arg("--whole-archive")
        .arg(&rlib_local)
        .arg("--no-whole-archive")
        .arg("-o")
        .arg(&so_whole_local)
        .output()
        .unwrap();
    let stderr_local = String::from_utf8_lossy(&out_local.stderr);
    assert!(
        !out_local.status.success()
            && stderr_local.contains("undefined symbol: cgu1_internal_helper"),
        "STB_LOCAL symbol in CGU 1 must fail cross-CGU resolution from CGU 0, got: {}",
        stderr_local
    );
    println!(
        "[probe:link_case_b] with --whole-archive + STB_LOCAL across CGUs: failed as expected (undefined symbol: cgu1_internal_helper)"
    );

    // Case C: Link WITH `--whole-archive --no-undefined` AND `STB_GLOBAL` across CGUs.
    // Both `rustc_driver_impl_main` and `cgu1_internal_helper` resolve and appear in `.dynsym`.
    let out_global = Command::new(&rust_lld)
        .args([
            "-flavor",
            "gnu",
            "-m",
            "elf64lriscv",
            "-shared",
            "--no-undefined",
        ])
        .arg(&rmeta_o)
        .arg("--whole-archive")
        .arg(&rlib_global)
        .arg("--no-whole-archive")
        .arg("-o")
        .arg(&so_whole_global)
        .output()
        .unwrap();
    assert!(
        out_global.status.success(),
        "rust-lld with --whole-archive and STB_GLOBAL must succeed"
    );
    let dynsym_whole = String::from_utf8(
        Command::new("readelf")
            .args(["--dyn-syms", "-W"])
            .arg(&so_whole_global)
            .output()
            .unwrap()
            .stdout,
    )
    .unwrap();
    assert!(
        dynsym_whole.contains("rustc_driver_impl_main")
            && dynsym_whole.contains("cgu1_internal_helper"),
        "with --whole-archive and STB_GLOBAL, both CGU symbols are retained in .dynsym"
    );
    println!(
        "[probe:link_case_c] with --whole-archive + STB_GLOBAL across CGUs: rustc_driver_impl_main present_in_dynsym=true"
    );
}

fn main() {
    let sysroot = find_sysroot();
    let workdir = std::env::temp_dir().join(format!("rustc_cg_probe_{}", std::process::id()));
    fs::create_dir_all(&workdir).expect("create temp probe dir");
    let src_path = workdir.join("sample_probe_crate.rs");
    fs::write(&src_path, SAMPLE_CRATE_SRC).expect("write sample crate");

    // If invoked with `--child-trigger-trimmed-ice`, run the unwrapped `def_path_str`
    // callbacks without `--emit=mir` so the parent process can observe the exact
    // `DiagCtxtInner::drop` ICE message.
    if std::env::args().any(|a| a == "--child-trigger-trimmed-ice") {
        let args = vec![
            "rustc".to_string(),
            src_path.display().to_string(),
            "--crate-type=bin".to_string(),
            "--sysroot".to_string(),
            sysroot,
            "-C".to_string(),
            "panic=abort".to_string(),
            "-o".to_string(),
            workdir.join("unused_out").display().to_string(),
        ];
        let mut cb = UnwrappedDefPathStrCallbacks;
        rustc_driver::compiler_entrypoint(&args, &mut cb);
        return;
    }

    if std::env::args().any(|a| a == "--child-trigger-closure-item-name-ice") {
        let args = vec![
            "rustc".to_string(),
            src_path.display().to_string(),
            "--crate-type=bin".to_string(),
            "--sysroot".to_string(),
            sysroot,
            "-C".to_string(),
            "panic=abort".to_string(),
            "-o".to_string(),
            workdir.join("unused_out").display().to_string(),
        ];
        let mut cb = ClosureItemNameCallbacks;
        rustc_driver::compiler_entrypoint(&args, &mut cb);
        return;
    }

    // 1. Run the safe callbacks (`with_no_trimmed_paths!`, `opt_item_name`, 2-arg `EarlyBinder::bind`).
    let safe_args = vec![
        "rustc".to_string(),
        src_path.display().to_string(),
        "--crate-type=bin".to_string(),
        "--sysroot".to_string(),
        sysroot.clone(),
        "-C".to_string(),
        "panic=abort".to_string(),
        "-o".to_string(),
        workdir.join("sample_out").display().to_string(),
    ];
    let mut safe_cb = SafeCodegenProbeCallbacks;
    rustc_driver::compiler_entrypoint(&safe_args, &mut safe_cb);

    // 2. Run child process with unwrapped `tcx.def_path_str(def_id)` and verify that
    // `DiagCtxtInner::drop` panics with the exact `trimmed_def_paths` ICE when no
    // diagnostics are emitted and `--emit=mir` is absent.
    let current_exe = std::env::current_exe().expect("current_exe");
    let child_out = Command::new(&current_exe)
        .arg("--child-trigger-trimmed-ice")
        .env_remove("RUSTC_LOG")
        .output()
        .expect("spawn child for trimmed_def_paths ICE verification");
    let child_stderr = String::from_utf8_lossy(&child_out.stderr);
    assert!(
        !child_out.status.success()
            && child_stderr.contains(
                "`trimmed_def_paths` called, diagnostics were expected but none were emitted. Use `with_no_trimmed_paths` for debugging."
            ),
        "expected DiagCtxtInner::drop panic in child, got stderr:\n{}",
        child_stderr
    );
    println!(
        "[probe:trimmed_ice] verified DiagCtxtInner::drop ICE on unwrapped tcx.def_path_str: \"`trimmed_def_paths` called, diagnostics were expected but none were emitted. Use `with_no_trimmed_paths` for debugging.\""
    );

    // 3. Run child process calling `tcx.item_name(closure_def_id)` and verify that it
    // panics with `item_name: no name for DefPath { ... data: Closure }`.
    let closure_child_out = Command::new(&current_exe)
        .arg("--child-trigger-closure-item-name-ice")
        .env_remove("RUSTC_LOG")
        .output()
        .expect("spawn child for closure item_name ICE verification");
    let closure_stderr = String::from_utf8_lossy(&closure_child_out.stderr);
    assert!(
        !closure_child_out.status.success() && closure_stderr.contains("item_name: no name for"),
        "expected item_name ICE in child, got stderr:\n{}",
        closure_stderr
    );
    println!(
        "[probe:closure_item_name_ice] verified tcx.item_name(closure_def_id) ICE: \"item_name: no name for DefPath {{ ... data: Closure }}\""
    );

    // 3. Verify `CrateType::Dylib` (`librustc_driver.so`) `--whole-archive` and
    // cross-CGU `STB_LOCAL` vs. `STB_GLOBAL` linking with `rust-lld`.
    verify_dylib_whole_archive_and_cgu_binding(&sysroot, &workdir);

    let _ = fs::remove_dir_all(&workdir);
}
