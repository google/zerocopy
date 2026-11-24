#!/usr/bin/env python3
"""Reproducible rustc + zerocopy probe for coinductive auto traits,
PhantomData<UnsafeCell<u32>> four-way asymmetry, async coroutine Send leaks,
and zerocopy::Immutable soundness.
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile
from typing import Any


def parse_rustc_version(version_verbose: str) -> tuple[int, int, int]:
    m = re.search(r"rustc\s+(\d+)\.(\d+)\.(\d+)", version_verbose)
    if not m:
        raise RuntimeError(f"cannot parse rustc version from:\n{version_verbose}")
    return (int(m.group(1)), int(m.group(2)), int(m.group(3)))


def scrub_text(text: str, td: pathlib.Path, zc_dir: pathlib.Path | None = None) -> str:
    """Remove local filesystem paths and user/host identifiers."""
    home = str(pathlib.Path.home())
    user = os.environ.get("USER", "")
    text = re.sub(
        r"/[^\s:]+/\.rustup/toolchains/[^\s/]+/",
        "<sysroot>/",
        text,
    )
    text = re.sub(
        r"/[^\s:]+/\.cargo/registry/src/[^/]+/",
        "<cargo_registry>/",
        text,
    )
    if zc_dir is not None:
        text = text.replace(str(zc_dir) + os.sep, "<zerocopy_src>/")
        text = text.replace(str(zc_dir), "<zerocopy_src>")
    text = text.replace(str(td) + os.sep, "<tmp>/")
    text = text.replace(str(td), "<tmp>")
    text = re.sub(r"/(?:home|Users)/[^/\s]+/Projects/[^/\s]+/zerocopy/zerocopy\b", "<zerocopy_src>", text)
    if home:
        text = text.replace(home, "<home>")
    if user:
        text = re.sub(rf"/home/{re.escape(user)}\b", "<home>", text)
        text = re.sub(rf"/Users/{re.escape(user)}\b", "<home>", text)
    return text.strip()


def run_rustc_case(
    name: str,
    code: str,
    td: pathlib.Path,
    *,
    zc_dir: pathlib.Path | None = None,
    edition: str = "2024",
    extra_args: list[str] | None = None,
    expect_compile_rc: int,
    run_binary: bool = False,
) -> dict[str, Any]:
    src = td / f"{name}.rs"
    out = td / f"{name}_bin"
    src.write_text(code, encoding="utf-8")
    cmd = ["rustc", f"--edition={edition}"]
    if extra_args:
        cmd.extend(extra_args)
    cmd.extend([str(src), "-o", str(out)])
    proc = subprocess.run(cmd, capture_output=True, text=True)
    result: dict[str, Any] = {
        "edition": edition,
        "extra_args": [scrub_text(a, td, zc_dir) for a in (extra_args or [])],
        "compile_returncode": proc.returncode,
        "compile_stdout": scrub_text(proc.stdout, td, zc_dir),
        "compile_stderr": scrub_text(proc.stderr, td, zc_dir),
    }
    if proc.returncode != expect_compile_rc:
        raise RuntimeError(
            f"case {name!r}: expected compile_rc={expect_compile_rc}, got {proc.returncode}\n"
            f"stderr:\n{proc.stderr}"
        )
    if run_binary and proc.returncode == 0:
        run_proc = subprocess.run([str(out)], capture_output=True, text=True)
        result["run_returncode"] = run_proc.returncode
        result["run_stdout"] = scrub_text(run_proc.stdout, td, zc_dir)
        result["run_stderr"] = scrub_text(run_proc.stderr, td, zc_dir)
        if run_proc.returncode != 0:
            raise RuntimeError(f"case {name!r}: binary failed with rc={run_proc.returncode}")
    return result


def discover_zerocopy_dir(explicit: str | None) -> pathlib.Path:
    candidates: list[pathlib.Path] = []
    if explicit:
        candidates.append(pathlib.Path(explicit))
    env_src = os.environ.get("ZEROCOPY_SRC")
    if env_src:
        candidates.append(pathlib.Path(env_src))
    here = pathlib.Path(__file__).resolve()
    for parent in [pathlib.Path.cwd(), *here.parents]:
        candidates.append(parent / "zerocopy")
        candidates.append(parent)
    proj_root = pathlib.Path.home() / "Projects"
    if proj_root.is_dir():
        for user_dir in sorted(proj_root.iterdir()):
            candidates.append(user_dir / "zerocopy" / "zerocopy")
    cargo_reg = pathlib.Path(os.environ.get("CARGO_HOME", pathlib.Path.home() / ".cargo")) / "registry" / "src"
    if cargo_reg.is_dir():
        for idx_dir in sorted(cargo_reg.iterdir()):
            for zc in sorted(idx_dir.glob("zerocopy-*"), reverse=True):
                if not zc.name.startswith("zerocopy-derive-"):
                    candidates.append(zc)
    for c in candidates:
        if (c / "Cargo.toml").is_file() and (c / "src" / "lib.rs").is_file():
            # Verify Cargo.toml actually defines package name = "zerocopy"
            cargo_txt = (c / "Cargo.toml").read_text(encoding="utf-8", errors="ignore")
            if 'name = "zerocopy"' in cargo_txt:
                return c.resolve()
    raise FileNotFoundError(
        "Could not locate zerocopy crate directory; pass --zerocopy-src <path/to/zerocopy>."
    )


def parse_zerocopy_cargo_metadata(cargo_toml: pathlib.Path, rustc_ver: tuple[int, int, int]) -> tuple[str, list[str]]:
    txt = cargo_toml.read_text(encoding="utf-8")
    ver_m = re.search(r'^version\s*=\s*"([^"]+)"', txt, re.MULTILINE)
    pkg_version = ver_m.group(1) if ver_m else "0.8.64"
    cfgs: list[str] = []
    in_meta = False
    for line in txt.splitlines():
        s = line.strip()
        if s.startswith("["):
            in_meta = (s == "[package.metadata.build-rs]")
            continue
        if in_meta and "=" in s and not s.startswith("#"):
            k, v = [p.strip() for p in s.split("=", 1)]
            vm = re.match(r'"(\d+)\.(\d+)\.(\d+)"', v)
            if vm:
                req = (int(vm.group(1)), int(vm.group(2)), int(vm.group(3)))
                if rustc_ver < req:
                    cfgs.append(k.replace("-", "_"))
    return pkg_version, cfgs


def build_zerocopy_derive_optional(td: pathlib.Path, zc_dir: pathlib.Path) -> pathlib.Path | None:
    zcd_lib = zc_dir / "zerocopy-derive" / "src" / "lib.rs"
    if not zcd_lib.is_file():
        return None
    cargo_reg = pathlib.Path(os.environ.get("CARGO_HOME", pathlib.Path.home() / ".cargo")) / "registry" / "src"
    if not cargo_reg.is_dir():
        return None
    ui = pm2 = qt = sy = None
    for idx_dir in sorted(cargo_reg.iterdir()):
        ui_hits = sorted(idx_dir.glob("unicode-ident-*"))
        pm2_hits = sorted(idx_dir.glob("proc-macro2-*"))
        qt_hits = sorted(idx_dir.glob("quote-*"))
        sy_hits = sorted(idx_dir.glob("syn-2.*"))
        if ui_hits and pm2_hits and qt_hits and sy_hits:
            ui = ui_hits[-1] / "src" / "lib.rs"
            pm2 = pm2_hits[-1] / "src" / "lib.rs"
            qt = qt_hits[-1] / "src" / "lib.rs"
            sy = sy_hits[-1] / "src" / "lib.rs"
            break
    if not (ui and pm2 and qt and sy):
        return None

    steps = [
        ["rustc", "--edition=2018", "--crate-type=lib", "--crate-name=unicode_ident",
         str(ui), "-o", str(td / "libunicode_ident.rlib")],
        ["rustc", "--edition=2021", "--crate-type=lib", "--crate-name=proc_macro2",
         "--cfg", 'feature="proc-macro"', "--cfg", "wrap_proc_macro",
         "-L", f"dependency={td}",
         "--extern", f"unicode_ident={td / 'libunicode_ident.rlib'}",
         str(pm2), "-o", str(td / "libproc_macro2.rlib")],
        ["rustc", "--edition=2018", "--crate-type=lib", "--crate-name=quote",
         "--cfg", 'feature="proc-macro"', "-L", f"dependency={td}",
         "--extern", f"proc_macro2={td / 'libproc_macro2.rlib'}",
         str(qt), "-o", str(td / "libquote.rlib")],
        ["rustc", "--edition=2021", "--crate-type=lib", "--crate-name=syn",
         "--cfg", 'feature="full"', "--cfg", 'feature="parsing"', "--cfg", 'feature="printing"',
         "--cfg", 'feature="proc-macro"', "--cfg", 'feature="derive"', "--cfg", 'feature="clone-impls"',
         "-L", f"dependency={td}",
         "--extern", f"unicode_ident={td / 'libunicode_ident.rlib'}",
         "--extern", f"proc_macro2={td / 'libproc_macro2.rlib'}",
         "--extern", f"quote={td / 'libquote.rlib'}",
         str(sy), "-o", str(td / "libsyn.rlib")],
        ["rustc", "--edition=2021", "--crate-type=proc-macro", "--crate-name=zerocopy_derive",
         "--extern", "proc_macro", "-L", f"dependency={td}",
         "--extern", f"proc_macro2={td / 'libproc_macro2.rlib'}",
         "--extern", f"quote={td / 'libquote.rlib'}",
         "--extern", f"syn={td / 'libsyn.rlib'}",
         str(zcd_lib), "-o", str(td / "libzerocopy_derive.so")],
    ]
    for cmd in steps:
        proc = subprocess.run(cmd, capture_output=True, text=True)
        if proc.returncode != 0:
            return None
    return td / "libzerocopy_derive.so"


def run_all_probes(zerocopy_src: str | None) -> dict[str, Any]:
    rv = subprocess.run(["rustc", "-Vv"], capture_output=True, text=True, check=True).stdout.strip()
    rustc_ver = parse_rustc_version(rv)
    zc_dir = discover_zerocopy_dir(zerocopy_src)
    pkg_version, no_cfgs = parse_zerocopy_cargo_metadata(zc_dir / "Cargo.toml", rustc_ver)

    with tempfile.TemporaryDirectory() as td_str:
        td = pathlib.Path(td_str)

        part_a: dict[str, Any] = {}
        part_a["coinductive_node_has_cell_and_phantom_cell_ok"] = run_rustc_case(
            "coinductive_ok",
            """#![feature(freeze)]
use core::cell::UnsafeCell;
use core::marker::{Freeze, PhantomData};

#[allow(dead_code)]
struct Node {
    val: u32,
    next: Option<Box<Node>>,
}

#[allow(dead_code)]
struct CycleA(Option<Box<CycleB>>);
#[allow(dead_code)]
struct CycleB(Option<Box<CycleA>>);

#[allow(dead_code)]
struct HasRaw(*const u8);
#[allow(dead_code)]
struct HasCell(UnsafeCell<u32>);
#[allow(dead_code)]
struct HasPhantomCell(PhantomData<UnsafeCell<u32>>);
#[allow(dead_code)]
struct HasPhantomRaw(PhantomData<*const u8>);

fn assert_send<T: Send>() {}
fn assert_sync<T: Sync>() {}
fn assert_unpin<T: Unpin>() {}
fn assert_freeze<T: Freeze>() {}

fn main() {
    assert_send::<Node>();
    assert_sync::<Node>();
    assert_unpin::<Node>();
    assert_freeze::<Node>();

    assert_send::<CycleA>();
    assert_sync::<CycleA>();
    assert_freeze::<CycleA>();

    assert_unpin::<HasRaw>();
    assert_freeze::<HasRaw>();

    assert_send::<HasCell>();
    assert_unpin::<HasCell>();

    assert_send::<HasPhantomCell>();
    assert_unpin::<HasPhantomCell>();
    assert_freeze::<HasPhantomCell>();

    assert_unpin::<HasPhantomRaw>();
    assert_freeze::<HasPhantomRaw>();
    println!("AUTO_OK=1");
}
""",
            td,
            expect_compile_rc=0,
            run_binary=True,
        )

        # Verify coinductive cycle + PhantomData<UnsafeCell> also pass under -Znext-solver
        part_a["next_solver_coinductive_and_phantom_freeze_ok"] = run_rustc_case(
            "next_solver_ok",
            part_a_src := (td / "coinductive_ok.rs").read_text(encoding="utf-8"),
            td,
            extra_args=["-Znext-solver"],
            expect_compile_rc=0,
            run_binary=True,
        )
        del part_a_src

        part_a["coinductive_node_with_raw_ptr_rejected_send_e0277"] = run_rustc_case(
            "bad_node_raw_send",
            """#[allow(dead_code)]
struct BadNode {
    val: u32,
    next: Option<Box<BadNode>>,
    raw: *const u8,
}
fn assert_send<T: Send>() {}
fn main() {
    assert_send::<BadNode>();
}
""",
            td,
            expect_compile_rc=1,
        )

        part_a["coinductive_node_with_cell_rejected_sync_e0277"] = run_rustc_case(
            "cell_node_sync",
            """use core::cell::UnsafeCell;
#[allow(dead_code)]
struct CellNode {
    val: UnsafeCell<u32>,
    next: Option<Box<CellNode>>,
}
fn assert_sync<T: Sync>() {}
fn main() {
    assert_sync::<CellNode>();
}
""",
            td,
            expect_compile_rc=1,
        )

        part_a["has_raw_ptr_not_send_rejected_e0277"] = run_rustc_case(
            "has_raw_not_send",
            """#[allow(dead_code)]
struct HasRaw(*const u8);
fn assert_send<T: Send>() {}
fn main() {
    assert_send::<HasRaw>();
}
""",
            td,
            expect_compile_rc=1,
        )

        part_a["has_raw_ptr_not_sync_rejected_e0277"] = run_rustc_case(
            "has_raw_not_sync",
            """#[allow(dead_code)]
struct HasRaw(*const u8);
fn assert_sync<T: Sync>() {}
fn main() {
    assert_sync::<HasRaw>();
}
""",
            td,
            expect_compile_rc=1,
        )

        part_a["has_cell_not_sync_rejected_e0277"] = run_rustc_case(
            "has_cell_not_sync",
            """use core::cell::UnsafeCell;
#[allow(dead_code)]
struct HasCell(UnsafeCell<u32>);
fn assert_sync<T: Sync>() {}
fn main() {
    assert_sync::<HasCell>();
}
""",
            td,
            expect_compile_rc=1,
        )

        part_a["has_cell_not_freeze_rejected_e0277"] = run_rustc_case(
            "has_cell_not_freeze",
            """#![feature(freeze)]
use core::cell::UnsafeCell;
use core::marker::Freeze;
#[allow(dead_code)]
struct HasCell(UnsafeCell<u32>);
fn assert_freeze<T: Freeze>() {}
fn main() {
    assert_freeze::<HasCell>();
}
""",
            td,
            expect_compile_rc=1,
        )

        part_a["has_phantom_cell_not_sync_rejected_e0277"] = run_rustc_case(
            "has_phantom_cell_not_sync",
            """use core::cell::UnsafeCell;
use core::marker::PhantomData;
#[allow(dead_code)]
struct HasPhantomCell(PhantomData<UnsafeCell<u32>>);
fn assert_sync<T: Sync>() {}
fn main() {
    assert_sync::<HasPhantomCell>();
}
""",
            td,
            expect_compile_rc=1,
        )

        part_a["has_phantom_raw_not_send_rejected_e0277"] = run_rustc_case(
            "has_phantom_raw_not_send",
            """use core::marker::PhantomData;
#[allow(dead_code)]
struct HasPhantomRaw(PhantomData<*const u8>);
fn assert_send<T: Send>() {}
fn main() {
    assert_send::<HasPhantomRaw>();
}
""",
            td,
            expect_compile_rc=1,
        )

        part_a["unsafe_field_blocks_send_allows_unpin"] = run_rustc_case(
            "unsafe_field_unpin_only",
            """#![feature(unsafe_fields)]
#[allow(dead_code)]
struct WithUnsafeField {
    unsafe secret: u32,
}
fn assert_unpin<T: Unpin>() {}
fn main() {
    assert_unpin::<WithUnsafeField>();
    println!("UNSAFE_FIELD_UNPIN_OK=1");
}
""",
            td,
            expect_compile_rc=0,
            run_binary=True,
        )

        part_a["unsafe_field_blocks_send_rejected_e0277"] = run_rustc_case(
            "unsafe_field_not_send",
            """#![feature(unsafe_fields)]
#[allow(dead_code)]
struct WithUnsafeField {
    unsafe secret: u32,
}
fn assert_send<T: Send>() {}
fn main() {
    assert_send::<WithUnsafeField>();
}
""",
            td,
            expect_compile_rc=1,
        )

        # Part B: zerocopy::Immutable & #[derive(Immutable)]
        part_b: dict[str, Any] = {
            "zerocopy_crate_version": pkg_version,
            "zerocopy_no_cfgs_applied": no_cfgs,
        }
        derive_so = build_zerocopy_derive_optional(td, zc_dir)
        zc_cmd = [
            "rustc", "--edition=2021", "--crate-type=lib", "--crate-name=zerocopy",
            "--cfg", 'feature="alloc"',
        ]
        for cfg_name in no_cfgs:
            zc_cmd.extend(["--cfg", cfg_name])
        if derive_so is not None:
            zc_cmd.extend([
                "--cfg", 'feature="derive"',
                "--extern", f"zerocopy_derive={derive_so}",
                "-L", f"dependency={td}",
            ])
        zc_rlib = td / "libzerocopy.rlib"
        zc_cmd.extend([str(zc_dir / "src" / "lib.rs"), "-o", str(zc_rlib)])
        zc_env = dict(os.environ, CARGO_PKG_VERSION=pkg_version)
        zc_build = subprocess.run(zc_cmd, capture_output=True, text=True, env=zc_env)
        part_b["zerocopy_derive_built"] = derive_so is not None
        part_b["zerocopy_lib_compile_returncode"] = zc_build.returncode
        part_b["zerocopy_lib_compile_stderr"] = scrub_text(zc_build.stderr, td, zc_dir)
        if zc_build.returncode != 0:
            raise RuntimeError(f"failed to compile zerocopy:\n{zc_build.stderr}")

        ext_args = ["-L", f"dependency={td}", "--extern", f"zerocopy={zc_rlib}"]

        part_b["zerocopy_phantom_unsafecell_implements_immutable_ok"] = run_rustc_case(
            "zc_phantom_cell_ok",
            """#![feature(freeze)]
use core::cell::UnsafeCell;
use core::marker::{Freeze, PhantomData};
use core::mem::{ManuallyDrop, MaybeUninit};
use core::num::Wrapping;
use zerocopy::Immutable;

fn assert_imm<T: Immutable>() {}
fn assert_send<T: Send>() {}
fn assert_freeze<T: Freeze>() {}

fn main() {
    assert_imm::<PhantomData<UnsafeCell<u32>>>();
    assert_send::<PhantomData<UnsafeCell<u32>>>();
    assert_freeze::<PhantomData<UnsafeCell<u32>>>();

    assert_imm::<[PhantomData<UnsafeCell<u32>>; 4]>();
    assert_imm::<Option<PhantomData<UnsafeCell<u32>>>>();
    assert_imm::<Box<UnsafeCell<u32>>>();
    assert_imm::<*const UnsafeCell<u32>>();
    assert_imm::<&UnsafeCell<u32>>();
    assert_imm::<ManuallyDrop<u32>>();
    assert_imm::<Wrapping<u32>>();
    assert_imm::<MaybeUninit<u32>>();
    println!("ZC_PHANTOM_CELL_IMMUTABLE_OK=1");
}
""",
            td,
            zc_dir=zc_dir,
            extra_args=ext_args,
            expect_compile_rc=0,
            run_binary=True,
        )

        part_b["zerocopy_unsafecell_rejected_immutable_e0277"] = run_rustc_case(
            "zc_unsafecell_err",
            """use core::cell::UnsafeCell;
use zerocopy::Immutable;
fn assert_immutable<T: Immutable>() {}
fn main() {
    assert_immutable::<UnsafeCell<u32>>();
}
""",
            td,
            zc_dir=zc_dir,
            extra_args=ext_args,
            expect_compile_rc=1,
        )

        part_b["zerocopy_cell_rejected_immutable_e0277"] = run_rustc_case(
            "zc_cell_err",
            """use core::cell::Cell;
use zerocopy::Immutable;
fn assert_immutable<T: Immutable>() {}
fn main() {
    assert_immutable::<Cell<u32>>();
}
""",
            td,
            zc_dir=zc_dir,
            extra_args=ext_args,
            expect_compile_rc=1,
        )

        part_b["zerocopy_manually_drop_unsafecell_rejected_immutable_e0277"] = run_rustc_case(
            "zc_md_unsafecell_err",
            """use core::cell::UnsafeCell;
use core::mem::ManuallyDrop;
use zerocopy::Immutable;
fn assert_immutable<T: Immutable>() {}
fn main() {
    assert_immutable::<ManuallyDrop<UnsafeCell<u32>>>();
}
""",
            td,
            zc_dir=zc_dir,
            extra_args=ext_args,
            expect_compile_rc=1,
        )

        part_b["zerocopy_box_slice_unsafecell_rejected_immutable_e0277"] = run_rustc_case(
            "zc_box_slice_err",
            """use core::cell::UnsafeCell;
use zerocopy::Immutable;
fn assert_immutable<T: ?Sized + Immutable>() {}
fn main() {
    assert_immutable::<Box<[UnsafeCell<u32>]>>();
}
""",
            td,
            zc_dir=zc_dir,
            extra_args=ext_args,
            expect_compile_rc=1,
        )

        if derive_so is not None:
            part_b["zerocopy_derive_phantom_and_recursive_node_ok"] = run_rustc_case(
                "zc_derive_ok",
                """#![feature(freeze)]
use core::cell::UnsafeCell;
use core::marker::{Freeze, PhantomData};
use zerocopy::Immutable;

#[derive(Immutable)]
#[allow(dead_code)]
struct HasPhantomCell {
    val: u32,
    _marker: PhantomData<UnsafeCell<u32>>,
}

#[derive(Immutable)]
#[allow(dead_code)]
struct RecImmNode {
    val: u32,
    next: Option<Box<RecImmNode>>,
}

fn assert_all<T: Send + Freeze + Immutable>() {}
fn assert_sync<T: Sync>() {}

fn main() {
    assert_all::<HasPhantomCell>();
    assert_all::<RecImmNode>();
    assert_sync::<RecImmNode>();
    println!("ZC_DERIVE_IMMUTABLE_OK=1");
}
""",
                td,
                zc_dir=zc_dir,
            extra_args=ext_args,
                expect_compile_rc=0,
                run_binary=True,
            )

            part_b["zerocopy_derive_struct_with_unsafecell_rejected_e0277"] = run_rustc_case(
                "zc_derive_err",
                """use core::cell::UnsafeCell;
use zerocopy::Immutable;

#[derive(Immutable)]
#[allow(dead_code)]
struct BadDerivedCell {
    val: u32,
    cell: UnsafeCell<u8>,
}

fn main() {}
""",
                td,
                zc_dir=zc_dir,
            extra_args=ext_args,
                expect_compile_rc=1,
            )

            part_b["zerocopy_derive_phantom_cell_rejected_sync_e0277"] = run_rustc_case(
                "zc_derive_phantom_sync_err",
                """use core::cell::UnsafeCell;
use core::marker::PhantomData;
use zerocopy::Immutable;

#[derive(Immutable)]
#[allow(dead_code)]
struct HasPhantomCell {
    val: u32,
    _marker: PhantomData<UnsafeCell<u32>>,
}

fn assert_sync<T: Sync>() {}
fn main() {
    assert_sync::<HasPhantomCell>();
}
""",
                td,
                zc_dir=zc_dir,
            extra_args=ext_args,
                expect_compile_rc=1,
            )

        # Part C: Async coroutine cross-.await Send leaks and static Unpin
        part_c: dict[str, Any] = {}
        async_harness = """use core::future::Future;
use core::pin::Pin;
use core::task::{Context, Poll};

struct YieldOnce(bool);
impl Future for YieldOnce {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
        if self.0 {
            Poll::Ready(())
        } else {
            self.0 = true;
            Poll::Pending
        }
    }
}
fn yield_now() -> YieldOnce { YieldOnce(false) }
fn require_send<F: Future + Send>(_fut: F) {}
"""

        part_c["rc_held_across_await_rejected_not_send"] = run_rustc_case(
            "async_rc_across_err",
            async_harness + """use std::rc::Rc;
async fn bad() {
    let rc = Rc::new(1u32);
    yield_now().await;
    drop(rc);
}
fn main() {
    require_send(bad());
}
""",
            td,
            expect_compile_rc=1,
        )

        part_c["rc_dropped_before_await_send_ok"] = run_rustc_case(
            "async_rc_before_ok",
            async_harness + """use std::rc::Rc;
async fn good() {
    {
        let rc = Rc::new(1u32);
        let _v = *rc;
    }
    yield_now().await;
}
fn main() {
    require_send(good());
    println!("ASYNC_SEND_OK=1");
}
""",
            td,
            expect_compile_rc=0,
            run_binary=True,
        )

        part_c["unsafecell_by_value_and_phantom_across_await_send_ok"] = run_rustc_case(
            "async_cell_val_ok",
            async_harness + """use core::cell::UnsafeCell;
use core::marker::PhantomData;
async fn cell_by_val() {
    let c = UnsafeCell::new(1u32);
    let p: PhantomData<UnsafeCell<u32>> = PhantomData;
    yield_now().await;
    drop((c, p));
}
fn main() {
    require_send(cell_by_val());
    println!("ASYNC_CELL_VAL_SEND_OK=1");
}
""",
            td,
            expect_compile_rc=0,
            run_binary=True,
        )

        part_c["ref_unsafecell_across_await_rejected_not_send"] = run_rustc_case(
            "async_ref_cell_err",
            async_harness + """use core::cell::UnsafeCell;
async fn ref_cell_across() {
    let c = UnsafeCell::new(1u32);
    let r = &c;
    yield_now().await;
    let _ = r;
}
fn main() {
    require_send(ref_cell_across());
}
""",
            td,
            expect_compile_rc=1,
        )

        part_c["ref_phantom_unsafecell_across_await_rejected_not_send"] = run_rustc_case(
            "async_ref_phantom_err",
            async_harness + """use core::cell::UnsafeCell;
use core::marker::PhantomData;
async fn ref_phantom_across() {
    let p: PhantomData<UnsafeCell<u32>> = PhantomData;
    let r = &p;
    yield_now().await;
    let _ = r;
}
fn main() {
    require_send(ref_phantom_across());
}
""",
            td,
            expect_compile_rc=1,
        )

        part_c["async_static_coroutine_not_unpin_e0277"] = run_rustc_case(
            "async_not_unpin",
            async_harness + """async fn triv() {
    yield_now().await;
}
fn require_unpin<T: Unpin>(_x: T) {}
fn main() {
    require_unpin(triv());
}
""",
            td,
            expect_compile_rc=1,
        )

    return {
        "rustc_version": rv,
        "experiments": {
            "a_coinductive_auto_traits_and_asymmetry": part_a,
            "b_zerocopy_immutable_and_derive": part_b,
            "c_async_coroutine_cross_await_send": part_c,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--zerocopy-src",
        default=None,
        help="Path to the zerocopy crate directory (containing Cargo.toml and src/lib.rs)",
    )
    parser.add_argument(
        "--out",
        default=None,
        help="Optional output JSON path (defaults to stdout if omitted)",
    )
    args = parser.parse_args()
    results = run_all_probes(args.zerocopy_src)
    payload = json.dumps(results, indent=2, ensure_ascii=True) + "\n"
    if args.out:
        pathlib.Path(args.out).write_text(payload, encoding="utf-8")
    else:
        sys.stdout.write(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
