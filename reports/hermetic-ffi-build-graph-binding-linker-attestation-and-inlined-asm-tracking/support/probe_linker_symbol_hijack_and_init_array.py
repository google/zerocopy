#!/usr/bin/env python3
"""Executable probes for ELF linker symbol resolution hazards:
- 2A: Archive link-order symbol shadowing (rust-lld vs GNU ld.bfd)
- 2B: Weak symbol (STB_WEAK) overridden by strong symbol (STB_GLOBAL) across .o and .a orders
- 2C: #[link_name] unintended binding and ambient libc symbol collision
- 2D: Dynamic symbol interposition (LD_PRELOAD) across Rust cdylib (assume_dso_local),
      extern "C" foreign imports, and C shared libraries (default vs -Bsymbolic vs STV_HIDDEN)
- 2E: --whole-archive (+whole-archive) pulling unreferenced .o members with .init_array
      constructors, same-member .init_array piggybacking, and .note.gnu.property CET drop.
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import subprocess
import tempfile


def run(cmd: list[str], cwd: pathlib.Path | None = None, env: dict[str, str] | None = None, check: bool = True) -> subprocess.CompletedProcess[str]:
    merged_env = os.environ.copy()
    if env:
        merged_env.update(env)
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=merged_env,
        text=True,
        capture_output=True,
        check=check,
    )


def build_archive(c_files: dict[str, str], lib_name: str, out_dir: pathlib.Path, extra_cflags: list[str] | None = None) -> pathlib.Path:
    objs = []
    cflags = ["-O2", "-fPIC"] + (extra_cflags or [])
    for stem, src in c_files.items():
        c_p = out_dir / f"{lib_name}_{stem}.c"
        o_p = out_dir / f"{stem}.o"
        c_p.write_text(src)
        run(["gcc", *cflags, "-c", str(c_p), "-o", str(o_p)])
        objs.append(str(o_p))
    a_p = out_dir / f"lib{lib_name}.a"
    if a_p.exists():
        a_p.unlink()
    run(["ar", "rcs", str(a_p), *objs])
    return a_p


def probe_2a_archive_order_shadowing(toolchain: str) -> dict:
    with tempfile.TemporaryDirectory(prefix="probe2a_") as td:
        root = pathlib.Path(td)
        build_archive({"good": "int crypto_verify(int x) { return x + 100; }\n"}, "good", root)
        build_archive({"evil": "int crypto_verify(int x) { return -1; }\n"}, "evil", root)

        rs = root / "app.rs"
        rs.write_text(
            'extern "C" { fn crypto_verify(x: i32) -> i32; }\n'
            'fn main() { println!("{}", unsafe { crypto_verify(5) }); }\n'
        )
        results = {}
        for linker_label, extra_link in [("rust_lld", []), ("ld_bfd", ["-C", "link-arg=-fuse-ld=bfd"])]:
            for order_label, l_flags in [
                ("good_then_evil", ["-l", "static=good", "-l", "static=evil"]),
                ("evil_then_good", ["-l", "static=evil", "-l", "static=good"]),
            ]:
                exe = root / f"app_{linker_label}_{order_label}"
                p = run([
                    "rustc", f"+{toolchain}", "-O",
                    "-L", f"native={root}",
                    *l_flags,
                    *extra_link,
                    str(rs), "-o", str(exe),
                ])
                val = run([str(exe)]).stdout.strip()
                results[f"{linker_label}__{order_label}"] = {
                    "exit_code": p.returncode,
                    "warnings_emitted": bool(p.stderr.strip()),
                    "runtime_output": val,
                }
        return results


def probe_2b_weak_override(toolchain: str) -> dict:
    with tempfile.TemporaryDirectory(prefix="probe2b_") as td:
        root = pathlib.Path(td)
        build_archive(
            {"base": '__attribute__((weak)) int auth_gate(void) { return 1; }\n'},
            "verified_weak",
            root,
        )
        build_archive(
            {"strong": 'int auth_gate(void) { return 0; }\nint unrelated_sibling(void) { return 7; }\n'},
            "override_strong",
            root,
        )
        # Also build a standalone strong .o
        strong_c = root / "standalone_strong.c"
        strong_o = root / "standalone_strong.o"
        strong_c.write_text("int auth_gate(void) { return 0; }\n")
        run(["gcc", "-O2", "-fPIC", "-c", str(strong_c), "-o", str(strong_o)])

        rs = root / "app.rs"
        rs.write_text(
            'extern "C" { fn auth_gate() -> i32; }\n'
            'fn main() { println!("{}", unsafe { auth_gate() }); }\n'
        )
        rs_sibling = root / "app_sibling.rs"
        rs_sibling.write_text(
            'extern "C" { fn auth_gate() -> i32; fn unrelated_sibling() -> i32; }\n'
            'fn main() { println!("{}", unsafe { auth_gate() + 0 * unrelated_sibling() }); }\n'
        )

        cases = [
            ("weak_only", rs, ["-l", "static=verified_weak"]),
            ("weak_then_strong_obj", rs, ["-l", "static=verified_weak", "-C", f"link-arg={strong_o}"]),
            ("weak_then_strong_archive", rs, ["-l", "static=verified_weak", "-l", "static=override_strong"]),
            ("weak_then_strong_archive_pulled_by_sibling", rs_sibling, ["-l", "static=verified_weak", "-l", "static=override_strong"]),
            ("strong_archive_then_weak", rs, ["-l", "static=override_strong", "-l", "static=verified_weak"]),
            ("weak_then_strong_whole_archive", rs, ["-l", "static=verified_weak", "-l", "static:+whole-archive=override_strong"]),
        ]
        results = {}
        for linker_label, extra_link in [("rust_lld", []), ("ld_bfd", ["-C", "link-arg=-fuse-ld=bfd"])]:
            for cname, src_rs, flags in cases:
                exe = root / f"app_{linker_label}_{cname}"
                p = run([
                    "rustc", f"+{toolchain}", "-O",
                    "-L", f"native={root}",
                    *flags,
                    *extra_link,
                    str(src_rs), "-o", str(exe),
                ])
                val = run([str(exe)]).stdout.strip()
                results[f"{linker_label}__{cname}"] = {
                    "runtime_output": val,
                    "strong_overrode_weak": val == "0",
                }
        return results


def probe_2c_link_name_binding(toolchain: str) -> dict:
    with tempfile.TemporaryDirectory(prefix="probe2c_") as td:
        root = pathlib.Path(td)
        build_archive(
            {
                "targets": (
                    "int verified_mac(int x) { return x ^ 0x55; }\n"
                    "int unverified_trap(int x) { return -999; }\n"
                )
            },
            "mac",
            root,
        )
        rs = root / "app.rs"
        rs.write_text(
            'extern "C" {\n'
            '    #[link_name = "unverified_trap"]\n'
            '    fn verified_mac(x: i32) -> i32;\n'
            '    #[link_name = "getpid"]\n'
            '    fn ambient_libc_collision() -> i32;\n'
            '}\n'
            '#[no_mangle] pub extern "C" fn call_site(x: i32) -> i32 {\n'
            '    unsafe { verified_mac(x) }\n'
            '}\n'
            'fn main() {\n'
            '    let r = call_site(10);\n'
            '    let pid = unsafe { ambient_libc_collision() };\n'
            '    println!("MAC={r} PID_POSITIVE={}", pid > 0);\n'
            '}\n'
        )
        obj = root / "app.o"
        run(["rustc", f"+{toolchain}", "-O", "--emit=obj", str(rs), "-o", str(obj)])
        relocs = run(["readelf", "-rW", str(obj)]).stdout
        exe = root / "app"
        run(["rustc", f"+{toolchain}", "-O", "-L", f"native={root}", "-l", "static=mac", str(rs), "-o", str(exe)])
        out = run([str(exe)]).stdout.strip()
        return {
            "obj_has_verified_mac_reloc": "verified_mac" in relocs,
            "obj_has_unverified_trap_reloc": "unverified_trap" in relocs,
            "obj_has_getpid_reloc": "getpid" in relocs,
            "runtime_output": out,
        }


def probe_2d_dynamic_interposition(toolchain: str) -> dict:
    with tempfile.TemporaryDirectory(prefix="probe2d_") as td:
        root = pathlib.Path(td)

        # 1. External shared library providing ext_provider() -> 20
        ext_c = root / "ext.c"
        ext_so = root / "libext.so"
        ext_c.write_text("int ext_provider(void) { return 20; }\n")
        run(["gcc", "-O2", "-fPIC", "-shared", str(ext_c), "-o", str(ext_so)])

        # 2. Rust cdylib exporting shared_inner(), rust_call_inner(), rust_call_ext()
        rcdy_rs = root / "rcdy.rs"
        rcdy_rs.write_text(
            'extern "C" { fn ext_provider() -> i32; }\n'
            '#[no_mangle] #[inline(never)]\n'
            'pub extern "C" fn shared_inner() -> i32 { 10 }\n'
            '#[no_mangle] #[inline(never)]\n'
            'pub extern "C" fn rust_call_inner() -> i32 { shared_inner() }\n'
            '#[no_mangle] #[inline(never)]\n'
            'pub extern "C" fn rust_call_ext() -> i32 { unsafe { ext_provider() } }\n'
        )
        rcdy_so = root / "librcdy.so"
        run([
            "rustc", f"+{toolchain}", "-O", "--crate-type=cdylib",
            "-L", f"native={root}", "-l", "dylib=ext",
            "-C", f"link-arg=-Wl,-rpath,{root}",
            str(rcdy_rs), "-o", str(rcdy_so),
        ])

        # 3. C shared libraries: default -fPIC, -Wl,-Bsymbolic, and STV_HIDDEN
        c_def_src = (
            "__attribute__((noinline)) int c_inner_def(void) { return 10; }\n"
            "int c_call_def(void) { return c_inner_def(); }\n"
        )
        c_bsym_src = (
            "__attribute__((noinline)) int c_inner_bsym(void) { return 10; }\n"
            "int c_call_bsym(void) { return c_inner_bsym(); }\n"
        )
        c_hid_src = (
            '__attribute__((noinline, visibility("hidden"))) int c_inner_hid(void) { return 10; }\n'
            "int c_call_hid(void) { return c_inner_hid(); }\n"
        )
        (root / "c_def.c").write_text(c_def_src)
        (root / "c_bsym.c").write_text(c_bsym_src)
        (root / "c_hid.c").write_text(c_hid_src)
        run(["gcc", "-O2", "-fPIC", "-shared", str(root / "c_def.c"), "-o", str(root / "libc_def.so")])
        run(["gcc", "-O2", "-fPIC", "-shared", "-Wl,-Bsymbolic", str(root / "c_bsym.c"), "-o", str(root / "libc_bsym.so")])
        run(["gcc", "-O2", "-fPIC", "-shared", str(root / "c_hid.c"), "-o", str(root / "libc_hid.so")])

        # 4. LD_PRELOAD interposer overriding all exported symbols
        hijack_c = root / "hijack.c"
        hijack_so = root / "libhijack.so"
        hijack_c.write_text(
            "int shared_inner(void) { return 999; }\n"
            "int ext_provider(void) { return 888; }\n"
            "int c_inner_def(void) { return 999; }\n"
            "int c_inner_bsym(void) { return 999; }\n"
            "int c_inner_hid(void) { return 999; }\n"
        )
        run(["gcc", "-O2", "-fPIC", "-shared", str(hijack_c), "-o", str(hijack_so)])

        # 5. Driver calling all 5 paths
        drv_c = root / "driver.c"
        drv_exe = root / "driver"
        drv_c.write_text(
            "#include <stdio.h>\n"
            "int rust_call_inner(void);\n"
            "int rust_call_ext(void);\n"
            "int c_call_def(void);\n"
            "int c_call_bsym(void);\n"
            "int c_call_hid(void);\n"
            "int main(void) {\n"
            '  printf("rust_inner=%d rust_ext=%d c_def=%d c_bsym=%d c_hid=%d\\n",\n'
            "         rust_call_inner(), rust_call_ext(), c_call_def(), c_call_bsym(), c_call_hid());\n"
            "  return 0;\n"
            "}\n"
        )
        run([
            "gcc", "-O2", str(drv_c),
            f"-L{root}", "-lrcdy", "-lext", "-lc_def", "-lc_bsym", "-lc_hid",
            f"-Wl,-rpath,{root}",
            "-o", str(drv_exe),
        ])

        normal = run([str(drv_exe)]).stdout.strip()
        preloaded = run([str(drv_exe)], env={"LD_PRELOAD": str(hijack_so)}).stdout.strip()

        # Check DT_SYMBOLIC / DF_SYMBOLIC in libc_bsym.so and relocs in librcdy.so
        bsym_dyn = run(["readelf", "-d", str(root / "libc_bsym.so")]).stdout
        rcdy_rel = run(["readelf", "-rW", str(rcdy_so)]).stdout
        cdef_rel = run(["readelf", "-rW", str(root / "libc_def.so")]).stdout

        return {
            "without_ld_preload": normal,
            "with_ld_preload": preloaded,
            "librcdy_has_shared_inner_dyn_reloc": "shared_inner" in rcdy_rel,
            "librcdy_has_ext_provider_dyn_reloc": "ext_provider" in rcdy_rel,
            "libc_def_has_c_inner_def_dyn_reloc": "c_inner_def" in cdef_rel,
            "libc_bsym_has_SYMBOLIC_flag": ("SYMBOLIC" in bsym_dyn),
        }


def probe_2e_whole_archive_init_array_and_cet(toolchain: str) -> dict:
    with tempfile.TemporaryDirectory(prefix="probe2e_") as td:
        root = pathlib.Path(td)

        # Archive 1: separate unreferenced member with __attribute__((constructor))
        build_archive(
            {
                "used": "int g_ctor_state = 0;\nint helper_add(int a, int b) { return a + b + g_ctor_state; }\n",
                "evil_ctor": (
                    "extern int g_ctor_state;\n"
                    "__attribute__((constructor)) static void sneaky_init(void) {\n"
                    "    g_ctor_state = 1000;\n"
                    "}\n"
                ),
            },
            "splitplug",
            root,
        )

        # Archive 2: constructor piggybacked inside the SAME .o member as helper_add
        build_archive(
            {
                "piggy": (
                    "int g_ctor_state = 0;\n"
                    "__attribute__((constructor)) static void piggy_init(void) {\n"
                    "    g_ctor_state = 2000;\n"
                    "}\n"
                    "int helper_add(int a, int b) { return a + b + g_ctor_state; }\n"
                ),
            },
            "piggyplug",
            root,
        )

        rs = root / "app.rs"
        rs.write_text(
            'extern "C" { fn helper_add(a: i32, b: i32) -> i32; }\n'
            'fn main() { println!("SUM={}", unsafe { helper_add(2, 3) }); }\n'
        )

        def init_array_entries(exe: pathlib.Path) -> int:
            out = run(["readelf", "-SW", str(exe)]).stdout
            for line in out.splitlines():
                if ".init_array" in line and "INIT_ARRAY" in line:
                    # Columns: [Nr] Name Type Addr Off Size ...
                    m = re.search(r"INIT_ARRAY\s+[0-9a-fA-F]+\s+[0-9a-fA-F]+\s+([0-9a-fA-F]+)", line)
                    if m:
                        return int(m.group(1), 16) // 8
            return 0

        cases = {}
        for label, link_spec in [
            ("split_default_no_whole_archive", "static=splitplug"),
            ("split_with_whole_archive", "static:+whole-archive=splitplug"),
            ("same_object_piggyback_no_whole_archive", "static=piggyplug"),
        ]:
            exe = root / f"exe_{label}"
            run([
                "rustc", f"+{toolchain}", "-O",
                "-L", f"native={root}", "-l", link_spec,
                str(rs), "-o", str(exe),
            ])
            cases[label] = {
                "runtime_output": run([str(exe)]).stdout.strip(),
                "init_array_entry_count": init_array_entries(exe),
            }

        # CET-IBT .note.gnu.property bitwise-AND drop check:
        # (a) Pure #![no_std] direct link (isolating C input object CET drop)
        # (b) Standard std link (exposing prebuilt libstd.rlib CET absence)
        sysroot = pathlib.Path(run(["rustc", f"+{toolchain}", "--print", "sysroot"]).stdout.strip())
        rust_lld = sysroot / "lib/rustlib/x86_64-unknown-linux-gnu/bin/rust-lld"
        nostd_rs = root / "nostd_cet.rs"
        nostd_rs.write_text(
            '#![no_std]\n#![no_main]\n'
            '#[panic_handler] fn p(_: &core::panic::PanicInfo) -> ! { loop {} }\n'
            'extern "C" { fn helper_add(a: i32, b: i32) -> i32; }\n'
            '#[no_mangle] pub extern "C" fn _start() -> i32 { unsafe { helper_add(2, 3) } }\n'
        )
        nostd_o = root / "nostd_cet.o"
        run(
            ["rustc", f"+{toolchain}", "-O", "-C", "panic=abort", "-Z", "cf-protection=full", "--emit=obj", str(nostd_rs), "-o", str(nostd_o)],
            env={"RUSTC_BOOTSTRAP": "1"},
        )
        cet_results = {}
        for c_flag, label in [("-fcf-protection=full", "c_with_cet"), ("-fcf-protection=none", "c_without_cet")]:
            c_dir = root / label
            c_dir.mkdir()
            c_src = c_dir / "c.c"
            c_o = c_dir / "c.o"
            c_src.write_text("int helper_add(int a, int b) { return a + b; }\n")
            run(["gcc", "-O2", "-fPIC", c_flag, "-c", str(c_src), "-o", str(c_o)])
            elf_nostd = c_dir / "nostd.elf"
            run([str(rust_lld), "-flavor", "gnu", str(nostd_o), str(c_o), "-o", str(elf_nostd)])
            notes_nostd = run(["readelf", "-n", str(elf_nostd)]).stdout

            build_archive({"c": "int helper_add(int a, int b) { return a + b; }\n"}, "cettest", c_dir, extra_cflags=[c_flag])
            exe_std = c_dir / "app_cet_std"
            run(
                [
                    "rustc", f"+{toolchain}", "-O",
                    "-Z", "cf-protection=full",
                    "-L", f"native={c_dir}", "-l", "static=cettest",
                    str(rs), "-o", str(exe_std),
                ],
                env={"RUSTC_BOOTSTRAP": "1"},
            )
            notes_std = run(["readelf", "-n", str(exe_std)]).stdout
            cet_results[label] = {
                "nostd_has_ibt": "IBT" in notes_nostd,
                "nostd_has_shstk": "SHSTK" in notes_nostd,
                "nostd_note_lines": [ln.strip() for ln in notes_nostd.splitlines() if "x86 feature:" in ln],
                "std_without_build_std_has_ibt": "IBT" in notes_std,
                "std_without_build_std_has_shstk": "SHSTK" in notes_std,
            }

        return {"init_array_cases": cases, "cet_gnu_property_cases": cet_results}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--toolchains", nargs="+", default=["1.99.1", "nightly-2026-06-01"])
    parser.add_argument("--json-out", type=pathlib.Path)
    args = parser.parse_args()

    out = {}
    for tc in args.toolchains:
        out[tc] = {
            "probe_2a_archive_order_shadowing": probe_2a_archive_order_shadowing(tc),
            "probe_2b_weak_override": probe_2b_weak_override(tc),
            "probe_2c_link_name_binding": probe_2c_link_name_binding(tc),
            "probe_2d_dynamic_interposition": probe_2d_dynamic_interposition(tc),
            "probe_2e_whole_archive_init_array_and_cet": probe_2e_whole_archive_init_array_and_cet(tc),
        }

    rendered = json.dumps(out, indent=2)
    if args.json_out:
        args.json_out.write_text(rendered + "\n")
    print(rendered)


if __name__ == "__main__":
    main()
