#!/usr/bin/env python3
"""Live differential rustc and Miri probe suite for TAIT, ATPIT, RTN, and -Znext-solver.

Compiles and runs 22 test cases covering:
  - Explicit #[define_opaque(...)] defining-scope rules and unconstrained checks
  - Bijective generic-parameter requirements, duplicate parameters, lifetime-equality
    exceptions, and non-defining uses coexisting with defining uses
  - Three-phase visibility: user-facing opacity, auto-trait leakage, and post-analysis
    CTFE/MIR/codegen layout & ABI transparency (including cross-crate rlib boundaries)
  - Self-referential opaque cycles under -Znext-solver=globally vs -Znext-solver=no
  - impl_trait_in_assoc_type (ATPIT) and return_type_notation (RTN) lowering/bounds

Every case is compiled under BOTH `-Znext-solver=globally` and `-Znext-solver=no`.
Runnable passing cases are executed both natively and under Miri (`-Zmiri-tree-borrows`)
in both solver modes.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

ERROR_CODE_RE = re.compile(r"error\[(E\d{4})\]")


def sanitize_output(text: str, tmpdir: str) -> str:
    """Replace ephemeral temporary paths so recorded outputs remain portable."""
    text = text.replace(tmpdir, "<tmp>")
    # Strip any remaining home/worktree paths if rustc prints sysroot paths
    home = os.path.expanduser("~")
    if home and home != "/":
        text = text.replace(home, "<home>")
    return text


def extract_error_codes(stderr: str) -> list[str]:
    seen: list[str] = []
    for m in ERROR_CODE_RE.finditer(stderr):
        code = m.group(1)
        if code not in seen:
            seen.append(code)
    return seen


def run_cmd(
    cmd: list[str],
    cwd: Path,
    env: dict[str, str] | None = None,
    timeout: int = 120,
) -> tuple[int, str, str]:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd),
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
    )
    return proc.returncode, proc.stdout, proc.stderr


# 22 concrete single-crate and multi-crate cases.
# The first 14 preserve exact names and semantics from the 1.102.0-nightly baseline
# so cross-version comparisons (1.98.0-nightly vs 1.102.0-nightly) are direct 1:1.
SINGLE_CRATE_CASES: list[dict[str, Any]] = [
    {
        "name": "tait_01_valid_define_opaque_and_nondefining_size",
        "crate_type": "bin",
        "run_native": True,
        "run_miri": True,
        "code": """\
#![feature(type_alias_impl_trait)]
use std::mem::{align_of, size_of};

pub type Hidden = impl Copy + PartialEq;

#[define_opaque(Hidden)]
pub fn make_hidden(x: u32) -> Hidden {
    x
}

fn require_send<T: Send>() -> bool { true }

const HIDDEN_SIZE: usize = size_of::<Hidden>();
const HIDDEN_ALIGN: usize = align_of::<Hidden>();

fn main() {
    let a = make_hidden(42);
    let b = make_hidden(42);
    let eq = a == b;
    let send = require_send::<Hidden>();
    println!("EQ={eq} SIZE={HIDDEN_SIZE} ALIGN={HIDDEN_ALIGN} SEND={send}");
}
""",
    },
    {
        "name": "tait_02_missing_define_opaque_rejected",
        "crate_type": "lib",
        "run_native": False,
        "run_miri": False,
        "code": """\
#![feature(type_alias_impl_trait)]
pub type Hidden = impl Copy;
pub fn unmarked_definer() -> Hidden { 42u32 }
""",
    },
    {
        "name": "tait_03_unconstrained_define_opaque_rejected",
        "crate_type": "lib",
        "run_native": False,
        "run_miri": False,
        "code": """\
#![feature(type_alias_impl_trait)]
pub type Hidden = impl Copy;
#[define_opaque(Hidden)]
pub fn claims_to_define_but_does_not() -> u32 { 7 }
""",
    },
    {
        "name": "tait_04_conflicting_concrete_witnesses_rejected",
        "crate_type": "lib",
        "run_native": False,
        "run_miri": False,
        "code": """\
#![feature(type_alias_impl_trait)]
pub type Hidden = impl Copy;
#[define_opaque(Hidden)]
pub fn def_u32() -> Hidden { 1u32 }
#[define_opaque(Hidden)]
pub fn def_u64() -> Hidden { 2u64 }
""",
    },
    {
        "name": "tait_05_non_send_rc_auto_trait_leak_rejected",
        "crate_type": "lib",
        "run_native": False,
        "run_miri": False,
        "code": """\
#![feature(type_alias_impl_trait)]
mod m {
    use std::rc::Rc;
    pub type OpaqueRc = impl Clone;
    #[define_opaque(OpaqueRc)]
    pub fn make() -> OpaqueRc { Rc::new(1u32) }
}
fn require_send<T: Send>() {}
pub fn check() { require_send::<m::OpaqueRc>(); }
""",
    },
    {
        "name": "tait_06_send_u64_auto_trait_leak_accepted",
        "crate_type": "lib",
        "run_native": False,
        "run_miri": False,
        "code": """\
#![feature(type_alias_impl_trait)]
mod m {
    pub type OpaqueU64 = impl Copy;
    #[define_opaque(OpaqueU64)]
    pub fn make() -> OpaqueU64 { 99u64 }
}
fn require_send<T: Send + Sync + Unpin>() {}
pub fn check() { require_send::<m::OpaqueU64>(); }
""",
    },
    {
        "name": "tait_07_nondefining_concrete_equality_probe",
        "crate_type": "lib",
        "run_native": False,
        "run_miri": False,
        "code": """\
#![feature(type_alias_impl_trait)]
pub type Hidden = impl Copy;
#[define_opaque(Hidden)]
pub fn make() -> Hidden { 1u32 }
pub fn nondefining_add(h: Hidden) -> u32 {
    h + 1u32
}
""",
    },
    {
        "name": "tait_08_Defining_self_cycle_in_box",
        "crate_type": "lib",
        "run_native": False,
        "run_miri": False,
        "code": """\
#![feature(type_alias_impl_trait)]
pub type Rec = impl Sized;
#[define_opaque(Rec)]
pub fn make_rec(b: Option<Box<Rec>>) -> Rec {
    (1u32, b)
}
""",
    },
    {
        "name": "tait_09_generic_lifetime_unused_in_witness",
        "crate_type": "bin",
        "run_native": True,
        "run_miri": True,
        "code": """\
#![feature(type_alias_impl_trait)]
pub type WithLt<'a> = impl Copy + use<'a>;
#[define_opaque(WithLt)]
pub fn make<'a>(_x: &'a u8) -> WithLt<'a> {
    123u32
}
fn main() {
    let local = 9u8;
    let v = make(&local);
    println!("WITH_LT_SIZE={}", std::mem::size_of_val(&v));
}
""",
    },
    {
        "name": "tait_10_generic_type_non_param_instantiation_rejected",
        "crate_type": "lib",
        "run_native": False,
        "run_miri": False,
        "code": """\
#![feature(type_alias_impl_trait)]
pub type GenOpaque<T> = impl Copy;
#[define_opaque(GenOpaque)]
pub fn bad_inst() -> GenOpaque<u32> {
    42u32
}
""",
    },
    {
        "name": "atpit_01_impl_trait_in_assoc_type_and_send_leak",
        "crate_type": "bin",
        "run_native": True,
        "run_miri": True,
        "code": """\
#![feature(impl_trait_in_assoc_type)]
trait Producer {
    type Iter: Iterator<Item = u32>;
    fn produce(&self) -> Self::Iter;
}
struct Counter(u32);
impl Producer for Counter {
    type Iter = impl Iterator<Item = u32>;
    fn produce(&self) -> Self::Iter {
        [self.0, self.0 + 1, self.0 + 2].into_iter()
    }
}
fn require_send<T: Send>() -> bool { true }
fn main() {
    let s: u32 = Counter(3).produce().sum();
    let send = require_send::<<Counter as Producer>::Iter>();
    println!("ATPIT_SUM={s} SEND={send}");
}
""",
    },
    {
        "name": "rtn_01_async_fn_in_trait_send_bound",
        "crate_type": "bin",
        "run_native": True,
        "run_miri": True,
        "code": """\
#![feature(return_type_notation)]
use std::future::Future;
use std::task::{Context, Poll, Waker};

trait Worker {
    async fn run(&self) -> u32;
}
struct PureWorker(u32);
impl Worker for PureWorker {
    async fn run(&self) -> u32 {
        std::future::ready(self.0).await
    }
}
fn poll_send_worker<W: Worker<run(..): Send>>(w: &W) -> u32 {
    let mut fut = std::pin::pin!(w.run());
    let waker = Waker::noop();
    let mut cx = Context::from_waker(waker);
    match fut.as_mut().poll(&mut cx) {
        Poll::Ready(v) => v,
        Poll::Pending => panic!("unexpected pending"),
    }
}
fn main() {
    let v = poll_send_worker(&PureWorker(42));
    println!("RTN_READY={v}");
}
""",
    },
    {
        "name": "rtn_02_non_send_local_rc_across_await_rejected",
        "crate_type": "lib",
        "run_native": False,
        "run_miri": False,
        "code": """\
#![feature(return_type_notation)]
use std::rc::Rc;

trait Worker {
    async fn run(&self) -> u32;
}
struct RcWorker;
impl Worker for RcWorker {
    async fn run(&self) -> u32 {
        let rc = Rc::new(7u32);
        std::future::ready(()).await;
        *rc
    }
}

pub fn require_rtn_send<W: Worker<run(..): Send>>(_: W) {}
pub fn trigger() { require_rtn_send(RcWorker); }
""",
    },
    {
        "name": "rtn_03_type_qualified_syntax_probe",
        "crate_type": "bin",
        "run_native": True,
        "run_miri": True,
        "code": """\
#![feature(return_type_notation)]
use std::future::Future;
use std::task::{Context, Poll, Waker};

trait Worker {
    async fn run(&self) -> u32;
}
struct PureWorker(u32);
impl Worker for PureWorker {
    async fn run(&self) -> u32 {
        self.0
    }
}
fn check_where<W>(w: &W) -> u32
where
    W: Worker,
    W::run(..): Send,
{
    let mut fut = std::pin::pin!(w.run());
    let waker = Waker::noop();
    let mut cx = Context::from_waker(waker);
    match fut.as_mut().poll(&mut cx) {
        Poll::Ready(v) => v,
        Poll::Pending => panic!("unexpected pending"),
    }
}
fn main() {
    println!("RTN_WHERE_READY={}", check_where(&PureWorker(77)));
}
""",
    },
    # --- Extended primary-source discriminating cases (15..21) ---
    {
        "name": "tait_11_duplicate_generic_param_rejected",
        "crate_type": "lib",
        "run_native": False,
        "run_miri": False,
        "code": """\
#![feature(type_alias_impl_trait)]
pub type GenPair<A, B> = impl Copy;
#[define_opaque(GenPair)]
pub fn dup_param<T: Copy>(x: T) -> GenPair<T, T> {
    (x, x)
}
""",
    },
    {
        "name": "tait_12_nondefining_alongside_defining_in_same_scope",
        "crate_type": "bin",
        "run_native": True,
        "run_miri": True,
        "code": """\
#![feature(type_alias_impl_trait)]
pub type GenOpaque<T: Copy> = impl Copy;
#[define_opaque(GenOpaque)]
pub fn define_and_reuse<T: Copy>(x: T) -> (GenOpaque<T>, GenOpaque<u32>) {
    (x, 7u32)
}
fn main() {
    let (a, b) = define_and_reuse(9u16);
    println!("SIZES={},{}", std::mem::size_of_val(&a), std::mem::size_of_val(&b));
}
""",
    },
    {
        "name": "tait_14_lifetime_equality_exception_accepted",
        "crate_type": "bin",
        "run_native": True,
        "run_miri": True,
        "code": """\
#![feature(type_alias_impl_trait)]
pub type EqLt<'a: 'b, 'b: 'a> = impl Copy + use<'a, 'b>;
#[define_opaque(EqLt)]
pub fn make_eq<'x>(r: &'x u32) -> EqLt<'x, 'x> {
    r
}
fn main() {
    let n = 55u32;
    let h = make_eq(&n);
    println!("EQLT_SIZE={}", std::mem::size_of_val(&h));
}
""",
    },
    {
        "name": "atpit_02_non_send_atpit_auto_trait_rejected",
        "crate_type": "lib",
        "run_native": False,
        "run_miri": False,
        "code": """\
#![feature(impl_trait_in_assoc_type)]
use std::rc::Rc;
trait Holder {
    type Item: Clone;
    fn get(&self) -> Self::Item;
}
struct Local;
impl Holder for Local {
    type Item = impl Clone;
    fn get(&self) -> Self::Item {
        Rc::new(5u32)
    }
}
fn require_send<T: Send>() {}
pub fn check() { require_send::<<Local as Holder>::Item>(); }
""",
    },
    {
        "name": "rtn_04_equality_bound_rejected",
        "crate_type": "lib",
        "run_native": False,
        "run_miri": False,
        "code": """\
#![feature(return_type_notation)]
trait Worker {
    async fn run(&self) -> u32;
}
pub fn bad<W: Worker<run(..) = ()>>(_: W) {}
""",
    },
    {
        "name": "rtn_05_non_rpitit_method_rejected",
        "crate_type": "lib",
        "run_native": False,
        "run_miri": False,
        "code": """\
#![feature(return_type_notation)]
trait Plain {
    fn sync_fn(&self) -> u32;
}
pub fn bad<W: Plain<sync_fn(..): Send>>(_: W) {}
""",
    },
    {
        "name": "rtn_06_method_type_param_rejected",
        "crate_type": "lib",
        "run_native": False,
        "run_miri": False,
        "code": """\
#![feature(return_type_notation)]
trait Bad {
    async fn f<T>(&self, x: T) -> u32;
}
pub fn bad<W: Bad<f(..): Send>>(_: W) {}
""",
    },
]

# Case 22: Cross-crate rlib boundary test for Reveal::UserFacing vs Auto-Trait vs Reveal::All layout/ABI.
CROSS_CRATE_DEP_SRC = """\
#![feature(type_alias_impl_trait)]
pub type Secret = impl Copy + PartialEq;

#[define_opaque(Secret)]
pub fn make_secret(a: u64, b: u64, c: u64) -> Secret {
    [a, b, c]
}
"""

CROSS_CRATE_BIN_SRC = """\
use std::mem::{align_of, size_of};

const SECRET_SIZE: usize = size_of::<dep::Secret>();
const SECRET_ALIGN: usize = align_of::<dep::Secret>();

fn require_auto<T: Send + Sync + Unpin>() -> bool { true }

fn main() {
    let x = dep::make_secret(10, 20, 30);
    let y = dep::make_secret(10, 20, 30);
    let eq = x == y;
    let auto_ok = require_auto::<dep::Secret>();
    println!("XC_EQ={eq} XC_SIZE={SECRET_SIZE} XC_ALIGN={SECRET_ALIGN} XC_AUTO={auto_ok}");
}
"""

CROSS_CRATE_REJECT_OP_SRC = """\
pub fn try_index(s: dep::Secret) -> u64 {
    s[0]
}
"""


def run_miri_case(
    miri_cache_dir: Path,
    case_name: str,
    code: str,
    solver_flag: str,
    base_env: dict[str, str],
) -> dict[str, Any]:
    """Run a single-crate binary under cargo miri with -Zmiri-tree-borrows."""
    mode_tag = "next" if "globally" in solver_flag else "old"
    with tempfile.TemporaryDirectory(prefix=f"miri_{case_name}_") as td:
        pkg = Path(td)
        (pkg / "src").mkdir()
        (pkg / "Cargo.toml").write_text(
            f'[package]\nname = "probe_{case_name}_{mode_tag}"\nversion = "0.1.0"\nedition = "2024"\n',
            encoding="utf-8",
        )
        (pkg / "src" / "main.rs").write_text(code, encoding="utf-8")
        env = dict(base_env)
        env["CARGO_TARGET_DIR"] = str(pkg / "target")
        env["MIRI_SYSROOT"] = str(miri_cache_dir / "sysroot")
        env["RUSTFLAGS"] = solver_flag
        env["MIRIFLAGS"] = "-Zmiri-tree-borrows"
        rc, stdout, stderr = run_cmd(
            ["cargo", "miri", "run", "--offline", "--quiet"],
            cwd=pkg,
            env=env,
            timeout=180,
        )
        return {
            "rc": rc,
            "stdout": stdout.strip(),
            "stderr_head": sanitize_output(stderr[:600], td).strip(),
        }


def run_miri_cross_crate(
    miri_cache_dir: Path,
    solver_flag: str,
    base_env: dict[str, str],
) -> dict[str, Any]:
    """Run the two-crate dep + consumer workspace under cargo miri with -Zmiri-tree-borrows."""
    with tempfile.TemporaryDirectory(prefix="miri_xc_") as td:
        ws = Path(td)
        dep_dir = ws / "dep"
        app_dir = ws / "app"
        (dep_dir / "src").mkdir(parents=True)
        (app_dir / "src").mkdir(parents=True)
        (ws / "Cargo.toml").write_text(
            '[workspace]\nmembers = ["dep", "app"]\nresolver = "2"\n',
            encoding="utf-8",
        )
        (dep_dir / "Cargo.toml").write_text(
            '[package]\nname = "dep"\nversion = "0.1.0"\nedition = "2024"\n',
            encoding="utf-8",
        )
        (dep_dir / "src" / "lib.rs").write_text(CROSS_CRATE_DEP_SRC, encoding="utf-8")
        (app_dir / "Cargo.toml").write_text(
            '[package]\nname = "app"\nversion = "0.1.0"\nedition = "2024"\n\n[dependencies]\ndep = { path = "../dep" }\n',
            encoding="utf-8",
        )
        (app_dir / "src" / "main.rs").write_text(CROSS_CRATE_BIN_SRC, encoding="utf-8")
        env = dict(base_env)
        env["CARGO_TARGET_DIR"] = str(ws / "target")
        env["MIRI_SYSROOT"] = str(miri_cache_dir / "sysroot")
        env["RUSTFLAGS"] = solver_flag
        env["MIRIFLAGS"] = "-Zmiri-tree-borrows"
        rc, stdout, stderr = run_cmd(
            ["cargo", "miri", "run", "--offline", "--quiet", "-p", "app"],
            cwd=ws,
            env=env,
            timeout=180,
        )
        return {
            "rc": rc,
            "stdout": stdout.strip(),
            "stderr_head": sanitize_output(stderr[:600], td).strip(),
        }


def run_cross_crate_case(
    tmpdir: Path,
    solver_flag: str,
    base_env: dict[str, str],
) -> dict[str, Any]:
    """Compile dep rlib, positive consumer bin, and negative concrete-op lib."""
    cdir = tmpdir / f"xc_{solver_flag.replace('=', '_').replace('-', '')}"
    cdir.mkdir(parents=True, exist_ok=True)
    dep_rs = cdir / "dep.rs"
    dep_rlib = cdir / "libdep.rlib"
    bin_rs = cdir / "main.rs"
    bin_out = cdir / "main_bin"
    neg_rs = cdir / "neg.rs"
    neg_rlib = cdir / "libneg.rlib"

    dep_rs.write_text(CROSS_CRATE_DEP_SRC, encoding="utf-8")
    bin_rs.write_text(CROSS_CRATE_BIN_SRC, encoding="utf-8")
    neg_rs.write_text(CROSS_CRATE_REJECT_OP_SRC, encoding="utf-8")

    rc_dep, _, err_dep = run_cmd(
        [
            "rustc",
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=dep",
            solver_flag,
            str(dep_rs),
            "-o",
            str(dep_rlib),
        ],
        cwd=cdir,
        env=base_env,
    )
    res: dict[str, Any] = {
        "flags": [solver_flag],
        "dep_rc": rc_dep,
        "dep_error_codes": extract_error_codes(err_dep),
    }
    if rc_dep != 0:
        res["dep_stderr_head"] = sanitize_output(err_dep[:800], str(tmpdir))
        return res

    rc_bin, _, err_bin = run_cmd(
        [
            "rustc",
            "--edition=2024",
            "--crate-type=bin",
            "--crate-name=consumer",
            solver_flag,
            "--extern",
            f"dep={dep_rlib}",
            str(bin_rs),
            "-o",
            str(bin_out),
        ],
        cwd=cdir,
        env=base_env,
    )
    res["consumer_rc"] = rc_bin
    res["consumer_error_codes"] = extract_error_codes(err_bin)
    if rc_bin == 0:
        run_rc, run_out, run_err = run_cmd([str(bin_out)], cwd=cdir, env=base_env)
        res["run_rc"] = run_rc
        res["run_stdout"] = run_out.strip()
        if run_err.strip():
            res["run_stderr"] = sanitize_output(run_err[:400], str(tmpdir))
    else:
        res["consumer_stderr_head"] = sanitize_output(err_bin[:800], str(tmpdir))

    rc_neg, _, err_neg = run_cmd(
        [
            "rustc",
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=neg",
            solver_flag,
            "--extern",
            f"dep={dep_rlib}",
            str(neg_rs),
            "-o",
            str(neg_rlib),
        ],
        cwd=cdir,
        env=base_env,
    )
    res["neg_concrete_op_rc"] = rc_neg
    res["neg_concrete_op_error_codes"] = extract_error_codes(err_neg)
    res["neg_concrete_op_stderr_head"] = sanitize_output(err_neg[:800], str(tmpdir))
    return res


def main() -> int:
    out_path = Path(sys.argv[1]) if len(sys.argv) > 1 else None
    env = dict(os.environ)
    cargo_bin = os.path.expanduser("~/.cargo/bin")
    if cargo_bin not in env.get("PATH", ""):
        env["PATH"] = f"{cargo_bin}:{env.get('PATH', '')}"

    _, rustc_ver, _ = run_cmd(["rustc", "--version", "--verbose"], cwd=Path("."), env=env)
    miri_rc, miri_ver, _ = run_cmd(["cargo", "miri", "--version"], cwd=Path("."), env=env)

    solver_modes = {
        "next_solver_globally": "-Znext-solver=globally",
        "next_solver_no": "-Znext-solver=no",
    }

    results: dict[str, Any] = {
        "rustc_version": rustc_ver.strip(),
        "miri_version": miri_ver.strip() if miri_rc == 0 else "unavailable",
        "case_count": len(SINGLE_CRATE_CASES) + 1,
        "solver_divergences": [],
        "cases": {},
    }

    with tempfile.TemporaryDirectory(prefix="tait_probe_") as td:
        tmpdir = Path(td)
        miri_cache = tmpdir / "miri_cache"
        miri_cache.mkdir()

        # Pre-setup Miri sysroot once so per-case Miri invocations are fast and offline.
        miri_ready = False
        if miri_rc == 0:
            setup_env = dict(env)
            setup_env["MIRI_SYSROOT"] = str(miri_cache / "sysroot")
            rc_setup, _, err_setup = run_cmd(
                ["cargo", "miri", "setup", "--quiet"],
                cwd=tmpdir,
                env=setup_env,
                timeout=240,
            )
            miri_ready = rc_setup == 0
            results["miri_setup_rc"] = rc_setup
            if not miri_ready:
                results["miri_setup_stderr"] = sanitize_output(err_setup[:600], td)

        for spec in SINGLE_CRATE_CASES:
            name = spec["name"]
            case_out: dict[str, Any] = {}
            for mode_key, solver_flag in solver_modes.items():
                src_file = tmpdir / f"{name}_{mode_key}.rs"
                out_file = tmpdir / f"{name}_{mode_key}.out"
                src_file.write_text(spec["code"], encoding="utf-8")
                cmd = [
                    "rustc",
                    "--edition=2024",
                    f"--crate-type={spec['crate_type']}",
                    "--crate-name=probe",
                    solver_flag,
                    str(src_file),
                    "-o",
                    str(out_file),
                ]
                rc, _, stderr = run_cmd(cmd, cwd=tmpdir, env=env)
                sanitized_err = sanitize_output(stderr, td)
                entry: dict[str, Any] = {
                    "flags": [solver_flag],
                    "rc": rc,
                    "stderr_head": sanitized_err[:2200],
                    "error_codes": extract_error_codes(sanitized_err),
                }
                if rc == 0 and spec["run_native"]:
                    run_rc, run_stdout, run_stderr = run_cmd([str(out_file)], cwd=tmpdir, env=env)
                    entry["run_rc"] = run_rc
                    entry["run_stdout"] = run_stdout.strip()
                    if run_stderr.strip():
                        entry["run_stderr"] = sanitize_output(run_stderr[:400], td)
                if rc == 0 and spec["run_miri"] and miri_ready:
                    entry["miri"] = run_miri_case(miri_cache, name, spec["code"], solver_flag, env)
                case_out[mode_key] = entry

            g = case_out["next_solver_globally"]
            n = case_out["next_solver_no"]
            g_err_headline = next(
                (ln for ln in g["stderr_head"].splitlines() if ln.startswith("error")), ""
            )
            n_err_headline = next(
                (ln for ln in n["stderr_head"].splitlines() if ln.startswith("error")), ""
            )
            parity = (
                g["rc"] == n["rc"]
                and g["error_codes"] == n["error_codes"]
                and g_err_headline == n_err_headline
                and g.get("run_stdout") == n.get("run_stdout")
            )
            case_out["exit_code_parity"] = g["rc"] == n["rc"]
            case_out["solver_parity"] = parity
            if not parity:
                results["solver_divergences"].append(name)
            results["cases"][name] = case_out

        # Case 22: Cross-crate rlib boundary
        xc_name = "tait_13_cross_crate_reveal_all_layout_and_abi"
        xc_out: dict[str, Any] = {}
        for mode_key, solver_flag in solver_modes.items():
            xc_entry = run_cross_crate_case(tmpdir, solver_flag, env)
            if miri_ready and xc_entry.get("consumer_rc") == 0:
                xc_entry["miri"] = run_miri_cross_crate(miri_cache, solver_flag, env)
            xc_out[mode_key] = xc_entry
        g = xc_out["next_solver_globally"]
        n = xc_out["next_solver_no"]
        xc_parity = (
            g.get("dep_rc") == n.get("dep_rc")
            and g.get("consumer_rc") == n.get("consumer_rc")
            and g.get("run_stdout") == n.get("run_stdout")
            and g.get("neg_concrete_op_rc") == n.get("neg_concrete_op_rc")
            and g.get("neg_concrete_op_error_codes") == n.get("neg_concrete_op_error_codes")
        )
        xc_out["solver_parity"] = xc_parity
        if not xc_parity:
            results["solver_divergences"].append(xc_name)
        results["cases"][xc_name] = xc_out

    rendered = json.dumps(results, indent=2) + "\n"
    if out_path is not None:
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
