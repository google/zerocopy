#!/usr/bin/env python3
"""Live rustc multi-crate probes for rustc_privacy visibility lattice, EffectiveVisibilities,
RFC 2145 lints (private_bounds, private_interfaces, unnameable_types), unreachable_pub,
sealed-trait enforcement (and re-export escape), and real google/zerocopy sealing.

Uses only the Python 3.10+ standard library and executes all builds inside
tempfile.TemporaryDirectory(). Temporary paths, host usernames, and local repo prefixes
are scrubbed before emitting JSON.
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

SLUG = "rustc-privacy-visibility-lattice-rfc2145-sealed-traits-and-zerocopy-sealing"
DEFAULT_OUT = Path(__file__).resolve().with_name("probe_results.json")
RUSTC_PATH_BIN = os.environ.get("RUSTC", "rustc")

ERROR_CODE_RE = re.compile(r"error\[(E\d{4})\]")


def resolve_rustc() -> str:
    candidate = Path.home() / ".cargo" / "bin" / "rustc"
    if RUSTC_PATH_BIN == "rustc" and candidate.is_file():
        return str(candidate)
    return RUSTC_PATH_BIN


def find_zerocopy_src(explicit: str | None) -> Path | None:
    candidates: list[Path] = []
    if explicit:
        candidates.append(Path(explicit))
    env_zc = os.environ.get("ZEROCOPY_SRC")
    if env_zc:
        candidates.append(Path(env_zc))
    here = Path(__file__).resolve()
    for parent in here.parents:
        candidates.append(parent / "zerocopy" / "src" / "lib.rs")
        candidates.append(parent / "src" / "lib.rs")
    home = Path.home()
    for rel in (
        "zerocopy/zerocopy/src/lib.rs",
        "workspace/zerocopy/zerocopy/src/lib.rs",
        "Projects/zerocopy/zerocopy/src/lib.rs",
    ):
        candidates.append(home / rel)
    for c in candidates:
        if c.is_file() and c.name == "lib.rs" and (c.parent / "byteorder.rs").is_file():
            return c.resolve()
    return None


def scrub_text(text: str, tmpdir: Path, zc_root: Path | None) -> str:
    if not text:
        return text
    out = text
    if zc_root is not None:
        zc_str = str(zc_root).rstrip("/") + "/"
        out = out.replace(zc_str, "google/zerocopy:")
    tmp_str = str(tmpdir).rstrip("/") + "/"
    out = out.replace(tmp_str, "<tmp>/")
    out = out.replace(str(tmpdir), "<tmp>")
    sys_tmp = tempfile.gettempdir().rstrip("/")
    if sys_tmp and sys_tmp != "/tmp":
        out = out.replace(sys_tmp, "<tmp>")
    home = Path.home()
    home_str = str(home).rstrip("/")
    out = out.replace(home_str, "<home>")
    out = re.sub(rf"{re.escape(str(home.parent))}/[^/\s:]+", "<home>", out)
    out = re.sub(r"[0-9a-f]{40}", lambda m: "<sha>" if f"/{m.group(0)}/" in out else m.group(0), out)
    return out


def extract_error_codes(stderr: str) -> list[str]:
    seen: list[str] = []
    for code in ERROR_CODE_RE.findall(stderr):
        if code not in seen:
            seen.append(code)
    return seen


def run_rustc(
    rustc: str,
    args: list[str],
    tmpdir: Path,
    zc_root: Path | None,
    env_extra: dict[str, str] | None = None,
) -> dict[str, Any]:
    env = dict(os.environ)
    if env_extra:
        env.update(env_extra)
    proc = subprocess.run([rustc, *args], capture_output=True, text=True, env=env, check=False)
    stderr = scrub_text(proc.stderr, tmpdir, zc_root)
    stdout = scrub_text(proc.stdout, tmpdir, zc_root)
    return {
        "returncode": proc.returncode,
        "stdout": stdout.strip(),
        "stderr": stderr.strip(),
        "error_codes": extract_error_codes(stderr),
    }


def compile_and_maybe_run(
    rustc: str,
    src_path: Path,
    out_path: Path,
    tmpdir: Path,
    zc_root: Path | None,
    *,
    edition: str = "2024",
    crate_type: str = "bin",
    crate_name: str | None = None,
    externs: list[tuple[str, Path]] | None = None,
    extra_args: list[str] | None = None,
    run_binary: bool = False,
) -> dict[str, Any]:
    cmd = [f"--edition={edition}", f"--crate-type={crate_type}"]
    if crate_name:
        cmd.extend(["--crate-name", crate_name])
    if externs:
        for name, path in externs:
            cmd.extend(["--extern", f"{name}={path}"])
    if extra_args:
        cmd.extend(extra_args)
    cmd.extend([str(src_path), "-o", str(out_path)])
    comp = run_rustc(rustc, cmd, tmpdir, zc_root)
    result: dict[str, Any] = {
        "edition": edition,
        "crate_type": crate_type,
        "extra_args": extra_args or [],
        "compile_returncode": comp["returncode"],
        "compile_stdout": comp["stdout"],
        "compile_stderr": comp["stderr"],
        "error_codes": comp["error_codes"],
    }
    if run_binary and comp["returncode"] == 0:
        run_proc = subprocess.run([str(out_path)], capture_output=True, text=True, check=False)
        result["run_returncode"] = run_proc.returncode
        result["run_stdout"] = scrub_text(run_proc.stdout, tmpdir, zc_root).strip()
        result["run_stderr"] = scrub_text(run_proc.stderr, tmpdir, zc_root).strip()
    return result


def parse_effective_visibilities(stderr: str) -> list[dict[str, str]]:
    items: list[dict[str, str]] = []
    lines = stderr.splitlines()
    for idx, line in enumerate(lines):
        if line.startswith("error: Direct: ") or line.startswith("error: not in the table"):
            msg = line[len("error: ") :].strip()
            snippet = ""
            for j in range(idx + 1, min(idx + 6, len(lines))):
                if "|" in lines[j] and ("pub" in lines[j] or "fn " in lines[j] or "struct " in lines[j] or "trait " in lines[j]):
                    snippet = lines[j].split("|", 1)[1].strip()
                    break
            items.append({"item": snippet, "effective_visibility": msg})
    return items


def run_probes(zc_src_arg: str | None) -> dict[str, Any]:
    rustc = resolve_rustc()
    ver_v = subprocess.run([rustc, "--version", "--verbose"], capture_output=True, text=True, check=True)
    zc_lib = find_zerocopy_src(zc_src_arg)
    zc_root = zc_lib.parents[2] if zc_lib is not None else None

    results: dict[str, Any] = {
        "probe_suite": "rustc_privacy_visibility_lattice_rfc2145_sealed_traits_zerocopy",
        "rustc_version": ver_v.stdout.strip(),
        "host_machine": platform.machine(),
        "zerocopy_detected": zc_lib is not None,
        "experiments": {},
    }

    with tempfile.TemporaryDirectory() as tmp_str:
        tmp = Path(tmp_str)

        # ------------------------------------------------------------------
        # Part A: Visibility Lattice (pub, pub(crate), pub(super), pub(in path), pub(self))
        # ------------------------------------------------------------------
        part_a: dict[str, Any] = {}

        a01 = tmp / "a01.rs"
        a01.write_text(
            """mod a {
    pub(in crate::a) fn in_a() -> u32 { 41 }
    pub(super) fn sup() -> u32 { 10 }
    pub(crate) fn krate() -> u32 { 49 }

    pub mod sub {
        pub(super) fn call_a() -> u32 {
            super::in_a() + super::sup() + super::krate()
        }
    }

    pub fn entry() -> u32 {
        sub::call_a()
    }
}

mod b {
    pub fn from_sibling() -> u32 {
        crate::a::krate()
    }
}

fn main() {
    let total = a::entry() + b::from_sibling();
    println!("VIS_OK={}", total);
}
""",
            encoding="utf-8",
        )
        part_a["a01_descendant_and_crate_access_ok"] = compile_and_maybe_run(
            rustc, a01, tmp / "a01_bin", tmp, zc_root, run_binary=True
        )

        a02 = tmp / "a02.rs"
        a02.write_text(
            """mod a {
    pub(in crate::a) fn in_a() -> u32 { 7 }
}

mod b {
    pub fn call_sibling() -> u32 {
        crate::a::in_a()
    }
}

fn main() {
    let _ = b::call_sibling();
}
""",
            encoding="utf-8",
        )
        part_a["a02_sibling_pub_in_crate_a_rejected_e0603"] = compile_and_maybe_run(
            rustc, a02, tmp / "a02_bin", tmp, zc_root
        )

        a03 = tmp / "a03.rs"
        a03.write_text(
            """mod outer {
    mod inner {
        pub(self) fn secret() -> u32 { 1 }
    }
    pub fn poke() -> u32 {
        inner::secret()
    }
}

fn main() {
    let _ = outer::poke();
}
""",
            encoding="utf-8",
        )
        part_a["a03_parent_access_pub_self_rejected_e0603"] = compile_and_maybe_run(
            rustc, a03, tmp / "a03_bin", tmp, zc_root
        )

        a04 = tmp / "a04.rs"
        a04.write_text(
            """mod a {
    mod b {
        pub(in crate::other) fn bad_vis() {}
    }
}
mod other {}
fn main() {}
""",
            encoding="utf-8",
        )
        part_a["a04_pub_in_non_ancestor_path_rejected_e0742"] = compile_and_maybe_run(
            rustc, a04, tmp / "a04_bin", tmp, zc_root
        )

        a05_lib = tmp / "a05_lib.rs"
        a05_lib.write_text(
            """mod priv_outer {
    pub fn f() -> u32 { 11 }
    pub fn g() -> u32 { 22 }
}
pub use priv_outer::g;
""",
            encoding="utf-8",
        )
        a05_rlib = tmp / "liba05_lib.rlib"
        part_a["a05_lib_compile"] = compile_and_maybe_run(
            rustc, a05_lib, a05_rlib, tmp, zc_root, crate_type="lib", crate_name="a05_lib"
        )

        a05_reexp_ok = tmp / "a05_reexp_ok.rs"
        a05_reexp_ok.write_text(
            """fn main() {
    println!("REEXP_OK={}", a05_lib::g());
}
""",
            encoding="utf-8",
        )
        part_a["a05a_reexport_short_circuit_ok"] = compile_and_maybe_run(
            rustc,
            a05_reexp_ok,
            tmp / "a05a_bin",
            tmp,
            zc_root,
            externs=[("a05_lib", a05_rlib)],
            run_binary=True,
        )

        a05_direct_err = tmp / "a05_direct_err.rs"
        a05_direct_err.write_text(
            """fn main() {
    let _ = a05_lib::priv_outer::f();
}
""",
            encoding="utf-8",
        )
        part_a["a05b_ancestor_bottleneck_rejected_e0603"] = compile_and_maybe_run(
            rustc,
            a05_direct_err,
            tmp / "a05b_bin",
            tmp,
            zc_root,
            externs=[("a05_lib", a05_rlib)],
        )

        a06a = tmp / "a06a.rs"
        a06a.write_text(
            """mod m {
    pub struct S {
        pub x: u32,
        y: u32,
    }
    impl S {
        pub fn new() -> Self { S { x: 1, y: 2 } }
    }
}
fn main() {
    let s = m::S::new();
    let _ = s.y;
}
""",
            encoding="utf-8",
        )
        part_a["a06a_private_struct_field_e0616"] = compile_and_maybe_run(
            rustc, a06a, tmp / "a06a_bin", tmp, zc_root
        )

        a06b = tmp / "a06b.rs"
        a06b.write_text(
            """mod m {
    pub struct S {
        pub x: u32,
        y: u32,
    }
}
fn main() {
    let _ = m::S { x: 1, y: 2 };
}
""",
            encoding="utf-8",
        )
        part_a["a06b_private_struct_ctor_field_e0451"] = compile_and_maybe_run(
            rustc, a06b, tmp / "a06b_bin", tmp, zc_root
        )

        a07 = tmp / "a07.rs"
        a07.write_text(
            """#![allow(private_interfaces)]
mod m {
    struct Priv(u32);
    pub type Alias = Priv;
    pub fn mk() -> Priv { Priv(9) }
}
fn main() {
    let _: m::Alias = m::mk();
}
""",
            encoding="utf-8",
        )
        part_a["a07_type_privacy_alias_and_inferred_ret_item_is_private"] = compile_and_maybe_run(
            rustc, a07, tmp / "a07_bin", tmp, zc_root
        )

        results["experiments"]["a_visibility_lattice_and_privacy_checks"] = part_a

        # ------------------------------------------------------------------
        # Part B: EffectiveVisibilities & RFC 2145 Lints + unreachable_pub
        # ------------------------------------------------------------------
        part_b: dict[str, Any] = {}

        b01 = tmp / "b01.rs"
        b01.write_text(
            """#![feature(rustc_attrs)]
#![crate_type = "lib"]
#![allow(dead_code, private_interfaces)]

#[rustc_effective_visibility]
pub struct DirectPub;

mod hidden {
    #[rustc_effective_visibility]
    pub struct ReexportedItem;

    #[rustc_effective_visibility]
    pub trait Sealed {}

    #[rustc_effective_visibility]
    pub trait UnusedPub {}

    #[rustc_effective_visibility]
    pub trait RpitTrait {}

    #[rustc_effective_visibility]
    pub struct RpitHidden;

    impl RpitTrait for RpitHidden {}
}

#[rustc_effective_visibility]
pub use hidden::ReexportedItem;

#[rustc_effective_visibility]
pub trait PublicSealed: hidden::Sealed {}

#[rustc_effective_visibility]
pub fn leak_rpit() -> impl hidden::RpitTrait {
    hidden::RpitHidden
}

#[rustc_effective_visibility]
pub(crate) fn crate_fn_rpit() -> impl hidden::RpitTrait {
    hidden::RpitHidden
}
""",
            encoding="utf-8",
        )
        b01_res = compile_and_maybe_run(
            rustc, b01, tmp / "libb01.rmeta", tmp, zc_root, crate_type="lib", extra_args=["--emit=metadata"]
        )
        b01_res["parsed_effective_visibilities"] = parse_effective_visibilities(b01_res["compile_stderr"])
        part_b["b01_rustc_effective_visibility_inspection"] = b01_res

        b02 = tmp / "b02.rs"
        b02.write_text(
            """#![crate_type = "lib"]
#![deny(private_bounds, private_interfaces, unreachable_pub)]

mod private {
    pub trait Sealed {}
    impl Sealed for super::Token {}
}

pub struct Token;

pub trait PublicSealed: private::Sealed {
    fn id(&self) -> u32;
}

impl PublicSealed for Token {
    fn id(&self) -> u32 { 1 }
}
""",
            encoding="utf-8",
        )
        part_b["b02_sealed_trait_passes_deny_private_bounds_interfaces_unreachable_pub"] = compile_and_maybe_run(
            rustc, b02, tmp / "libb02.rlib", tmp, zc_root, crate_type="lib"
        )

        b03 = tmp / "b03.rs"
        b03.write_text(
            """#![crate_type = "lib"]
#![deny(unnameable_types)]

mod private {
    pub trait Sealed {}
}

pub trait PublicSealed: private::Sealed {}
""",
            encoding="utf-8",
        )
        part_b["b03_sealed_trait_flagged_by_deny_unnameable_types"] = compile_and_maybe_run(
            rustc, b03, tmp / "libb03.rlib", tmp, zc_root, crate_type="lib"
        )

        b04 = tmp / "b04.rs"
        b04.write_text(
            """#![crate_type = "lib"]
#![deny(unreachable_pub)]

mod private {
    pub trait UnusedSealed {}
}
""",
            encoding="utf-8",
        )
        part_b["b04_unused_pub_in_private_mod_triggers_unreachable_pub"] = compile_and_maybe_run(
            rustc, b04, tmp / "libb04.rlib", tmp, zc_root, crate_type="lib"
        )

        b05 = tmp / "b05.rs"
        b05.write_text(
            """#![crate_type = "lib"]
#![deny(private_bounds)]

mod inner {
    trait HiddenTrait {}
}
trait CrateTrait {}
pub trait BadSuper: CrateTrait {}
pub fn bad_generic<T: CrateTrait>(_x: T) {}
""",
            encoding="utf-8",
        )
        part_b["b05_private_bounds_rejects_crate_trait_bound"] = compile_and_maybe_run(
            rustc, b05, tmp / "libb05.rlib", tmp, zc_root, crate_type="lib"
        )

        b06 = tmp / "b06.rs"
        b06.write_text(
            """#![crate_type = "lib"]
#![deny(private_interfaces)]

struct PrivateType(u32);
pub fn leak_iface() -> PrivateType { PrivateType(7) }
""",
            encoding="utf-8",
        )
        part_b["b06_private_interfaces_rejects_pub_fn_private_type"] = compile_and_maybe_run(
            rustc, b06, tmp / "libb06.rlib", tmp, zc_root, crate_type="lib"
        )

        b07 = tmp / "b07.rs"
        b07.write_text(
            """#![crate_type = "lib"]
#![deny(unnameable_types)]

mod outer {
    mod inner {
        pub struct InnerUnnameable(pub u32);
    }
    pub(in crate::outer) fn crate_internal_leak() -> inner::InnerUnnameable {
        inner::InnerUnnameable(5)
    }
}
""",
            encoding="utf-8",
        )
        part_b["b07_unnameable_types_silent_when_not_crate_public"] = compile_and_maybe_run(
            rustc, b07, tmp / "libb07.rlib", tmp, zc_root, crate_type="lib"
        )

        b08 = tmp / "b08.rs"
        b08.write_text(
            """#![crate_type = "lib"]
#![allow(private_interfaces, private_bounds, dead_code)]

pub trait Tr {
    type Assoc;
}
pub struct Pub;
struct Priv;
impl Tr for Pub {
    type Assoc = Priv;
}
""",
            encoding="utf-8",
        )
        part_b["b08_assoc_type_hard_error_e0446_ignores_allow_lints"] = compile_and_maybe_run(
            rustc, b08, tmp / "libb08.rlib", tmp, zc_root, crate_type="lib"
        )

        results["experiments"]["b_effective_visibilities_and_rfc2145"] = part_b

        # ------------------------------------------------------------------
        # Part C: Multi-Crate Sealed Trait Enforcement & Escape Counterexamples
        # ------------------------------------------------------------------
        part_c: dict[str, Any] = {}

        up_rs = tmp / "up.rs"
        up_rs.write_text(
            """#![crate_type = "lib"]
#![deny(private_bounds, private_interfaces, unreachable_pub)]

mod private {
    pub trait Sealed {}
    impl Sealed for super::Token {}

    pub trait LeakySealed {}
    impl LeakySealed for super::Token {}

    pub struct Witness;
}

pub struct Token(pub u32);

pub trait PublicSealed: private::Sealed {
    fn value(&self) -> u32;
}

impl PublicSealed for Token {
    fn value(&self) -> u32 { self.0 }
}

pub fn consume<T: PublicSealed>(x: &T) -> u32 {
    x.value()
}

pub fn make_dyn(x: &Token) -> &dyn PublicSealed {
    x
}

pub(crate) fn crate_only() -> u32 {
    99
}

// Re-export escape: exposing LeakySealed breaks sealing of PublicFromLeaky.
pub use private::LeakySealed;
pub trait PublicFromLeaky: private::LeakySealed {
    fn tag(&self) -> &'static str;
}
impl PublicFromLeaky for Token {
    fn tag(&self) -> &'static str { "up_token" }
}

// #[doc(hidden)] pub mod does NOT seal against downstream impls.
#[doc(hidden)]
pub mod doc_hidden {
    pub trait NotSealed {}
}
pub trait DocHiddenSuper: doc_hidden::NotSealed {
    fn kind(&self) -> &'static str;
}

// Method-signature privacy witness (RFC 2145 allows with #[allow(private_interfaces)] or pub Witness in priv mod).
#[allow(private_interfaces, unreachable_pub)]
pub trait MethodSigHidden {
    fn secret(&self, _w: private::Witness) -> u32;
}
""",
            encoding="utf-8",
        )
        up_rlib = tmp / "libup.rlib"
        part_c["c00_upstream_lib_compile"] = compile_and_maybe_run(
            rustc, up_rs, up_rlib, tmp, zc_root, crate_type="lib", crate_name="up"
        )

        c01 = tmp / "c01.rs"
        c01.write_text(
            """fn read_val<T: up::PublicSealed>(x: &T) -> u32 {
    x.value() + up::consume(x)
}

fn main() {
    let t = up::Token(21);
    let d: &dyn up::PublicSealed = up::make_dyn(&t);
    println!("SEALED_CALL_OK={},dyn={}", read_val(&t), d.value());
}
""",
            encoding="utf-8",
        )
        part_c["c01_downstream_bound_method_and_dyn_ok"] = compile_and_maybe_run(
            rustc, c01, tmp / "c01_bin", tmp, zc_root, externs=[("up", up_rlib)], run_binary=True
        )

        c02 = tmp / "c02.rs"
        c02.write_text(
            """struct Local;
impl up::PublicSealed for Local {
    fn value(&self) -> u32 { 0 }
}
fn main() {}
""",
            encoding="utf-8",
        )
        part_c["c02_downstream_impl_public_sealed_rejected_e0277"] = compile_and_maybe_run(
            rustc, c02, tmp / "c02_bin", tmp, zc_root, externs=[("up", up_rlib)]
        )

        c03 = tmp / "c03.rs"
        c03.write_text(
            """struct Local;
impl up::private::Sealed for Local {}
fn main() {}
""",
            encoding="utf-8",
        )
        part_c["c03_downstream_impl_private_sealed_rejected_e0603"] = compile_and_maybe_run(
            rustc, c03, tmp / "c03_bin", tmp, zc_root, externs=[("up", up_rlib)]
        )

        c04 = tmp / "c04.rs"
        c04.write_text(
            """fn main() {
    let _ = up::crate_only();
}
""",
            encoding="utf-8",
        )
        part_c["c04_downstream_pub_crate_rejected_e0603"] = compile_and_maybe_run(
            rustc, c04, tmp / "c04_bin", tmp, zc_root, externs=[("up", up_rlib)]
        )

        c05 = tmp / "c05.rs"
        c05.write_text(
            """struct Local;
impl up::LeakySealed for Local {}
impl up::PublicFromLeaky for Local {
    fn tag(&self) -> &'static str { "ESCAPE_OK" }
}
fn main() {
    let x = Local;
    println!("{}", <Local as up::PublicFromLeaky>::tag(&x));
}
""",
            encoding="utf-8",
        )
        part_c["c05_reexport_escape_breaks_sealing_ok"] = compile_and_maybe_run(
            rustc, c05, tmp / "c05_bin", tmp, zc_root, externs=[("up", up_rlib)], run_binary=True
        )

        c06 = tmp / "c06.rs"
        c06.write_text(
            """struct Local;
impl up::doc_hidden::NotSealed for Local {}
impl up::DocHiddenSuper for Local {
    fn kind(&self) -> &'static str { "DOC_HIDDEN_NOT_SEALED" }
}
fn main() {
    println!("{}", <Local as up::DocHiddenSuper>::kind(&Local));
}
""",
            encoding="utf-8",
        )
        part_c["c06_doc_hidden_mod_does_not_seal_ok"] = compile_and_maybe_run(
            rustc, c06, tmp / "c06_bin", tmp, zc_root, externs=[("up", up_rlib)], run_binary=True
        )

        c07 = tmp / "c07.rs"
        c07.write_text(
            """struct Local;
impl up::MethodSigHidden for Local {
    fn secret(&self, _w: _) -> u32 { 0 }
}
fn main() {}
""",
            encoding="utf-8",
        )
        part_c["c07_method_sig_unnameable_witness_placeholder_rejected_e0121"] = compile_and_maybe_run(
            rustc, c07, tmp / "c07_bin", tmp, zc_root, externs=[("up", up_rlib)]
        )

        results["experiments"]["c_multicrate_sealed_traits_and_escape"] = part_c

        # ------------------------------------------------------------------
        # Part D: Real google/zerocopy ByteOrder & pointer::invariant Sealing
        # ------------------------------------------------------------------
        part_d: dict[str, Any] = {}
        if zc_lib is not None:
            zc_rlib = tmp / "libzerocopy.rlib"
            zc_comp = run_rustc(
                rustc,
                [
                    "--edition=2021",
                    "--crate-type=lib",
                    "--crate-name=zerocopy",
                    "--cfg",
                    "no_zerocopy_allocator_api_1_100_0",
                    str(zc_lib),
                    "-o",
                    str(zc_rlib),
                ],
                tmp,
                zc_root,
                env_extra={"CARGO_PKG_VERSION": "0.8.64"},
            )
            part_d["d01_zerocopy_lib_compile"] = zc_comp

            if zc_comp["returncode"] == 0:
                d02 = tmp / "d02.rs"
                d02.write_text(
                    """use zerocopy::byteorder::{BigEndian, ByteOrder, LittleEndian, Order, U32};
use zerocopy::pointer::invariant::{Aligned, Alignment, Exclusive, Invariants, Reference, Safe, Shared, Unaligned};

fn order_tag<B: ByteOrder>() -> &'static str {
    match B::ORDER {
        Order::BigEndian => "BE",
        Order::LittleEndian => "LE",
    }
}

fn check_invariant<A: Alignment, R: Reference, I: Invariants<Alignment = A, Aliasing = R, Validity = Safe>>() -> bool {
    R::IS_EXCLUSIVE
}

fn main() {
    let v = U32::<BigEndian>::new(0x1234_5678);
    let _le = U32::<LittleEndian>::new(v.get());
    let shared_ex = check_invariant::<Aligned, Shared, (Shared, Aligned, Safe)>();
    let excl_ex = check_invariant::<Unaligned, Exclusive, (Exclusive, Unaligned, Safe)>();
    println!(
        "ZC_SEALED_OK={},be={},le={},shared_ex={},excl_ex={}",
        v.get() == 0x1234_5678,
        order_tag::<BigEndian>(),
        order_tag::<LittleEndian>(),
        shared_ex,
        excl_ex
    );
}
""",
                    encoding="utf-8",
                )
                part_d["d02_zerocopy_downstream_usage_ok"] = compile_and_maybe_run(
                    rustc,
                    d02,
                    tmp / "d02_bin",
                    tmp,
                    zc_root,
                    externs=[("zerocopy", zc_rlib)],
                    run_binary=True,
                )

                d03 = tmp / "d03.rs"
                d03.write_text(
                    """#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct LocalOrder;
impl std::fmt::Display for LocalOrder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { f.write_str("local") }
}
impl zerocopy::byteorder::ByteOrder for LocalOrder {
    const ORDER: zerocopy::byteorder::Order = zerocopy::byteorder::Order::LittleEndian;
}
fn main() {}
""",
                    encoding="utf-8",
                )
                part_d["d03_zerocopy_impl_byteorder_rejected_e0277"] = compile_and_maybe_run(
                    rustc, d03, tmp / "d03_bin", tmp, zc_root, externs=[("zerocopy", zc_rlib)]
                )

                d04 = tmp / "d04.rs"
                d04.write_text(
                    """struct LocalAlign;
impl zerocopy::pointer::invariant::Alignment for LocalAlign {}
fn main() {}
""",
                    encoding="utf-8",
                )
                part_d["d04_zerocopy_impl_alignment_rejected_e0277"] = compile_and_maybe_run(
                    rustc, d04, tmp / "d04_bin", tmp, zc_root, externs=[("zerocopy", zc_rlib)]
                )

                d05 = tmp / "d05.rs"
                d05.write_text(
                    """use zerocopy::pointer::invariant::{Validity, ValidityKind};
struct LocalValidity;
unsafe impl Validity for LocalValidity {
    const KIND: ValidityKind = ValidityKind::Safe;
}
fn main() {}
""",
                    encoding="utf-8",
                )
                part_d["d05_zerocopy_unsafe_impl_validity_rejected_e0277"] = compile_and_maybe_run(
                    rustc, d05, tmp / "d05_bin", tmp, zc_root, externs=[("zerocopy", zc_rlib)]
                )

                d06 = tmp / "d06.rs"
                d06.write_text(
                    """use zerocopy::pointer::invariant::{Aliasing, Invariants, Reference, Aligned, Safe};
struct LocalAlias;
impl Aliasing for LocalAlias { const IS_EXCLUSIVE: bool = false; }
impl Reference for LocalAlias {}
struct LocalInv;
impl Invariants for LocalInv {
    type Aliasing = LocalAlias;
    type Alignment = Aligned;
    type Validity = Safe;
}
fn main() {}
""",
                    encoding="utf-8",
                )
                part_d["d06_zerocopy_impl_aliasing_reference_invariants_rejected_e0277"] = compile_and_maybe_run(
                    rustc, d06, tmp / "d06_bin", tmp, zc_root, externs=[("zerocopy", zc_rlib)]
                )

                d07 = tmp / "d07.rs"
                d07.write_text(
                    """use zerocopy::pointer::invariant::{Read, Shared};
struct LocalTy;
struct LocalReason;
impl Read<Shared, LocalReason> for LocalTy {}
fn main() {
    println!("READ_UNSEALED_OK=true");
}
""",
                    encoding="utf-8",
                )
                part_d["d07_zerocopy_read_trait_unsealed_contrast_ok"] = compile_and_maybe_run(
                    rustc,
                    d07,
                    tmp / "d07_bin",
                    tmp,
                    zc_root,
                    externs=[("zerocopy", zc_rlib)],
                    run_binary=True,
                )

        results["experiments"]["d_zerocopy_sealing_enforcement"] = part_d

    return results


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", default=str(DEFAULT_OUT), help="Output JSON path")
    parser.add_argument("--zerocopy-src", default=None, help="Path to zerocopy/src/lib.rs")
    args = parser.parse_args(argv)

    data = run_probes(args.zerocopy_src)
    serialized = json.dumps(data, indent=2, ensure_ascii=True) + "\n"
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(serialized, encoding="utf-8")

    # Summary counts
    total = 0
    passed_rc0 = 0
    for group in data["experiments"].values():
        for name, entry in group.items():
            if isinstance(entry, dict) and "compile_returncode" in entry:
                total += 1
                if entry["compile_returncode"] == 0:
                    passed_rc0 += 1
            elif isinstance(entry, dict) and "returncode" in entry:
                total += 1
                if entry["returncode"] == 0:
                    passed_rc0 += 1
    print(f"wrote {out_path} ({total} probe runs; {passed_rc0} rc=0)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
