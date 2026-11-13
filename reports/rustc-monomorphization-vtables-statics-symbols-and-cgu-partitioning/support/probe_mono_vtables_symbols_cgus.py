#!/usr/bin/env python3
"""Reproducible probe for R1-R5: mono-item dumps, vtable/shim/static lowering, symbol mangling, and CGU stability."""
import argparse
import json
import os
import subprocess
import tempfile
from pathlib import Path

MONO_PROBE_SRC = """#![crate_type = "lib"]
#![crate_name = "mono_probe"]

pub trait Speak {
    fn speak(&self) -> u32;
    fn id(&self) -> u32 { 42 }
}

pub trait LoudSpeak: Speak {
    fn loud(&self) -> u32;
}

pub struct Dog {
    pub tag: String,
    pub age: u32,
}

impl Speak for Dog {
    fn speak(&self) -> u32 { self.age }
}

impl LoudSpeak for Dog {
    fn loud(&self) -> u32 { self.age * 10 }
}

#[inline]
pub fn generic_inline<T: Speak>(x: &T) -> u32 {
    x.speak() + 1
}

pub fn generic_non_inline<T: Speak>(x: &T) -> u32 {
    x.speak() + 2
}

#[track_caller]
pub fn tracked_callee(x: u32) -> u32 {
    assert!(x > 0, "x must be positive");
    x + 1
}

pub static GLOBAL_ARRAY: [u32; 4] = [10, 20, 30, 40];
pub static REF_TO_GLOBAL: &[u32; 4] = &GLOBAL_ARRAY;

pub fn exercise_all(d: Dog) -> u32 {
    let f_ptr: fn(u32) -> u32 = tracked_callee;
    let c = |y: u32| d.age + y;
    let c_once: Box<dyn FnOnce(u32) -> u32> = Box::new(move |y| {
        let _keep = d.tag;
        y + 99
    });
    let dog2 = Dog { tag: String::new(), age: 7 };
    let dyn_loud: &dyn LoudSpeak = &dog2;
    let dyn_speak: &dyn Speak = dyn_loud;
    let promoted_slice: &[u32] = &[100, 200];
    generic_inline(&dog2) + generic_non_inline(&dog2) + f_ptr(5) + c(3) + dyn_speak.speak() + c_once(1) + promoted_slice[0]
}
"""

CGU_BASE_SRC = """#![crate_type = "lib"]
#![crate_name = "cgu_probe"]

pub mod mod_a {
    #[inline]
    pub fn inlined_helper(x: u32) -> u32 { x + 10 }
    pub fn fa(x: u32) -> u32 { x + 1 }
    pub fn generic_shared<T: Copy>(v: T) -> T { v }
}

pub mod mod_b {
    pub fn fb(x: u32) -> u32 { super::mod_a::generic_shared(x) + super::mod_a::inlined_helper(x) + 2 }
}

pub mod mod_c {
    pub fn fc(x: u32) -> u32 { super::mod_a::generic_shared(x) + 3 }
}
"""


def run_rustc_mono(wdir: Path, toolchain: str, src_name: str, extra_flags: list[str]) -> list[str]:
    env = os.environ.copy()
    env["RUSTC_BOOTSTRAP"] = "1"
    res = subprocess.run(
        [
            "rustup",
            "run",
            toolchain,
            "rustc",
            "--edition=2024",
            "-Zprint-mono-items=yes",
            "-Copt-level=0",
            src_name,
        ]
        + extra_flags,
        cwd=str(wdir),
        env=env,
        capture_output=True,
        text=True,
        check=True,
    )
    return sorted(line.strip() for line in res.stdout.splitlines() if line.startswith("MONO_ITEM"))


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--toolchain", default="1.99.1-x86_64-unknown-linux-gnu")
    ap.add_argument("--out", required=True, type=Path)
    args = ap.parse_args()

    with tempfile.TemporaryDirectory() as td:
        wdir = Path(td)
        (wdir / "mono_probe.rs").write_text(MONO_PROBE_SRC, encoding="utf-8")
        mono_lazy = run_rustc_mono(wdir, args.toolchain, "mono_probe.rs", ["-Ccodegen-units=1"])
        mono_link_dead = run_rustc_mono(
            wdir, args.toolchain, "mono_probe.rs", ["-Ccodegen-units=1", "-Clink-dead-code=yes"]
        )

        # CGU partitioning: non-incremental vs incremental across 3 edits
        (wdir / "cgu_probe.rs").write_text(CGU_BASE_SRC, encoding="utf-8")
        incr_dir = wdir / "incr_cache"
        non_incr_v1 = run_rustc_mono(wdir, args.toolchain, "cgu_probe.rs", ["-Ccodegen-units=16"])
        incr_v1 = run_rustc_mono(
            wdir, args.toolchain, "cgu_probe.rs", ["-Ccodegen-units=16", f"-Cincremental={incr_dir}"]
        )

        # Edit 1: body-only change in mod_b::fb
        (wdir / "cgu_probe.rs").write_text(CGU_BASE_SRC.replace("+ 2", "+ 200"), encoding="utf-8")
        non_incr_v2 = run_rustc_mono(wdir, args.toolchain, "cgu_probe.rs", ["-Ccodegen-units=16"])
        incr_v2 = run_rustc_mono(
            wdir, args.toolchain, "cgu_probe.rs", ["-Ccodegen-units=16", f"-Cincremental={incr_dir}"]
        )

        # Edit 2: add new generic instantiation generic_shared::<u64> in mod_c::fc
        (wdir / "cgu_probe.rs").write_text(
            CGU_BASE_SRC.replace("+ 3", "+ super::mod_a::generic_shared(3u64) as u32"), encoding="utf-8"
        )
        non_incr_v3 = run_rustc_mono(wdir, args.toolchain, "cgu_probe.rs", ["-Ccodegen-units=16"])
        incr_v3 = run_rustc_mono(
            wdir, args.toolchain, "cgu_probe.rs", ["-Ccodegen-units=16", f"-Cincremental={incr_dir}"]
        )

        out = {
            "toolchain": args.toolchain,
            "mono_probe_lazy_items": mono_lazy,
            "mono_probe_link_dead_code_items": mono_link_dead,
            "cgu_non_incremental": {
                "v1_baseline": non_incr_v1,
                "v2_body_edit_in_mod_b": non_incr_v2,
                "v3_new_generic_inst_in_mod_c": non_incr_v3,
            },
            "cgu_incremental": {
                "v1_baseline": incr_v1,
                "v2_body_edit_in_mod_b": incr_v2,
                "v3_new_generic_inst_in_mod_c": incr_v3,
            },
        }
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
