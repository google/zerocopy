#!/usr/bin/env python3
"""Reproducible rustc, MIR, LLVM IR, and Miri (-Zmiri-tree-borrows) probe for
#![feature(loop_match)] and #[const_continue].

Exercises:
  1. DFA MIR/LLVM CFG comparison (built MIR FalseEdge + dual DropTrees,
     post-borrowck/optimized MIR, LLVM IR at -O0 and -O2) and lexical LIFO
     drop order under both native execution and Miri Tree Borrows.
  2. Structural-equality gate rejecting manual PartialEq on fieldless enums.
  3. IEEE-754 float dispatch (-0.0f32, +0.0f32, NaN, +/-inf, open ranges) and
     Or-pattern sub_branch rebinding (x @ 0 | x @ 2, x @ (0 | 2), 0 | 2),
     plus the nested binding-wrapped Or-pattern ICE ((x @ (0 | 1)) | x @ 2).
  4. Compile-time rejection gates (arm guards, payload enums, projected places,
     const params, const blocks, bad labels, mismatched state update).
  5. Drop-implementing fieldless enum state overwrite divergence between
     #[loop_match] (both #[const_continue] and normal break) vs plain loop.
  6. Unwind cleanup ordering when an inner Drop panics during #[const_continue].
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def _env() -> dict[str, str]:
    env = os.environ.copy()
    cargo_bin = str(Path.home() / ".cargo" / "bin")
    if cargo_bin not in env.get("PATH", "").split(":"):
        env["PATH"] = f"{cargo_bin}:{env.get('PATH', '')}"
    env["RUSTC_ICE"] = "0"
    return env


def _run(
    cmd: list[str],
    cwd: Path | None = None,
    extra_env: dict[str, str] | None = None,
    timeout: int = 120,
) -> subprocess.CompletedProcess[str]:
    env = _env()
    if extra_env:
        env.update(extra_env)
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=env,
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def _parse_llvm_fn_cfg(ll_text: str, fn_substrings: list[str]) -> dict[str, dict[str, int]]:
    results: dict[str, dict[str, int]] = {}
    current_key: str | None = None
    in_fn = False
    for line in ll_text.splitlines():
        if line.startswith("define "):
            current_key = None
            for sub in fn_substrings:
                if f"@{sub}(" in line or re.search(rf"@[^\s(]*{re.escape(sub)}[^\s(]*\(", line):
                    current_key = sub
                    in_fn = True
                    results.setdefault(sub, {"switch": 0, "br": 0, "bb_labels": 1})
                    break
            continue
        if in_fn and line.strip() == "}":
            in_fn = False
            current_key = None
            continue
        if in_fn and current_key is not None:
            stripped = line.strip()
            if stripped.startswith("switch "):
                results[current_key]["switch"] += 1
            elif stripped.startswith("br "):
                results[current_key]["br"] += 1
            elif re.match(r"^[A-Za-z0-9_$.-]+:\s*(;.*)?$", line):
                results[current_key]["bb_labels"] += 1
    return results


def _summarize_mir_file(path: Path) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8")
    return {
        "file": path.name,
        "basic_blocks": len(re.findall(r"^\s+bb\d+\b.*:\s*\{", text, re.MULTILINE)),
        "switch_int": len(re.findall(r"\bswitchInt\(", text)),
        "false_edge": len(re.findall(r"\bfalseEdge\s*->", text)),
        "false_unwind": len(re.findall(r"\bfalseUnwind\s*->", text)),
        "discriminant_rvalue": len(re.findall(r"=\s*discriminant\(", text)),
        "drop_terminators": len(re.findall(r"\bdrop\(_\d+\)\s*->", text)),
        "goto_terminators": len(re.findall(r"\bgoto\s*->\s*bb\d+", text)),
    }


C1_SRC = r"""#![feature(loop_match)]
#![allow(incomplete_features)]

use std::cell::RefCell;

thread_local! {
    static DROPS: RefCell<Vec<&'static str>> = const { RefCell::new(Vec::new()) };
}

struct Guard(&'static str);
impl Drop for Guard {
    fn drop(&mut self) {
        DROPS.with(|d| d.borrow_mut().push(self.0));
    }
}

#[derive(Copy, Clone)]
enum State {
    S0,
    S1,
    S2,
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn step_loop_match(mut s: u8, mut acc: u32) -> u32 {
    #[loop_match]
    'outer: loop {
        s = 'blk: {
            match s {
                0 => {
                    acc = acc.wrapping_mul(3).wrapping_add(1);
                    #[const_continue]
                    break 'blk 1;
                }
                1 => {
                    acc = acc.wrapping_mul(5).wrapping_add(2);
                    #[const_continue]
                    break 'blk 2;
                }
                2 => {
                    acc = acc.wrapping_mul(7).wrapping_add(3);
                    break 'outer acc;
                }
                _ => break 'outer acc,
            }
        };
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn step_plain_loop(mut s: u8, mut acc: u32) -> u32 {
    'outer: loop {
        s = 'blk: {
            match s {
                0 => {
                    acc = acc.wrapping_mul(3).wrapping_add(1);
                    break 'blk 1;
                }
                1 => {
                    acc = acc.wrapping_mul(5).wrapping_add(2);
                    break 'blk 2;
                }
                2 => {
                    acc = acc.wrapping_mul(7).wrapping_add(3);
                    break 'outer acc;
                }
                _ => break 'outer acc,
            }
        };
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn dfa_stream_loop_match(input: &[u8]) -> u32 {
    let mut s = State::S0;
    let mut i = 0usize;
    let mut acc = 0u32;
    #[loop_match]
    'outer: loop {
        s = 'blk: {
            match s {
                State::S0 => {
                    if i >= input.len() {
                        break 'outer acc;
                    }
                    let b = input[i];
                    i += 1;
                    acc = acc.wrapping_add(b as u32);
                    if b & 1 == 0 {
                        #[const_continue]
                        break 'blk State::S1;
                    } else {
                        #[const_continue]
                        break 'blk State::S2;
                    }
                }
                State::S1 => {
                    if i >= input.len() {
                        break 'outer acc ^ 0x11;
                    }
                    let b = input[i];
                    i += 1;
                    acc = acc.wrapping_mul(3).wrapping_add(b as u32);
                    if b & 2 == 0 {
                        #[const_continue]
                        break 'blk State::S2;
                    } else {
                        #[const_continue]
                        break 'blk State::S0;
                    }
                }
                State::S2 => {
                    if i >= input.len() {
                        break 'outer acc ^ 0x22;
                    }
                    let b = input[i];
                    i += 1;
                    acc = acc.wrapping_add((b as u32) << 1);
                    #[const_continue]
                    break 'blk State::S0;
                }
            }
        };
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn dfa_stream_plain_loop(input: &[u8]) -> u32 {
    let mut s = State::S0;
    let mut i = 0usize;
    let mut acc = 0u32;
    'outer: loop {
        s = 'blk: {
            match s {
                State::S0 => {
                    if i >= input.len() {
                        break 'outer acc;
                    }
                    let b = input[i];
                    i += 1;
                    acc = acc.wrapping_add(b as u32);
                    if b & 1 == 0 {
                        break 'blk State::S1;
                    } else {
                        break 'blk State::S2;
                    }
                }
                State::S1 => {
                    if i >= input.len() {
                        break 'outer acc ^ 0x11;
                    }
                    let b = input[i];
                    i += 1;
                    acc = acc.wrapping_mul(3).wrapping_add(b as u32);
                    if b & 2 == 0 {
                        break 'blk State::S2;
                    } else {
                        break 'blk State::S0;
                    }
                }
                State::S2 => {
                    if i >= input.len() {
                        break 'outer acc ^ 0x22;
                    }
                    let b = input[i];
                    i += 1;
                    acc = acc.wrapping_add((b as u32) << 1);
                    break 'blk State::S0;
                }
            }
        };
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn drop_order_loop_match() -> Vec<&'static str> {
    DROPS.with(|d| d.borrow_mut().clear());
    let mut s = 0u8;
    #[loop_match]
    'outer: loop {
        s = 'blk: {
            match s {
                0 => {
                    let _outer = Guard("arm0_outer");
                    {
                        let _inner = Guard("arm0_inner");
                        #[const_continue]
                        break 'blk 1;
                    }
                }
                1 => {
                    let _g1 = Guard("arm1");
                    break 'outer;
                }
                _ => break 'outer,
            }
        };
    }
    DROPS.with(|d| d.borrow().clone())
}

fn main() {
    let dfa_lm = step_loop_match(0, 1);
    let dfa_pl = step_plain_loop(0, 1);
    assert_eq!(dfa_lm, dfa_pl);
    let stream = [0u8, 2, 5, 3, 4, 1, 6, 7];
    let s_lm = dfa_stream_loop_match(&stream);
    let s_pl = dfa_stream_plain_loop(&stream);
    assert_eq!(s_lm, s_pl);
    let drops = drop_order_loop_match();
    println!("DFA={} STREAM={} DROPS={:?}", dfa_lm, s_lm, drops);
}
"""


C2_SRC = r"""#![feature(loop_match)]
#![feature(stmt_expr_attributes)]
#![allow(incomplete_features)]

enum CustomEq { A, B }
impl PartialEq for CustomEq {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

const PAT_A: CustomEq = CustomEq::A;

fn main() {
    let mut s = CustomEq::B;
    let mut res = "";
    #[loop_match]
    'outer: loop {
        s = 'blk: {
            match s {
                PAT_A => {
                    res = "matched_PAT_A";
                    break 'outer;
                }
                _ => {
                    #[const_continue]
                    break 'blk CustomEq::A;
                }
            }
        };
    }
    println!("{}", res);
}
"""


C3_SRC = r"""#![feature(loop_match)]
#![allow(incomplete_features)]

const NEG_ZERO: f32 = -0.0;
const POS_ZERO: f32 = 0.0;
const NAN_VAL: f32 = f32::NAN;
const POS_INF: f32 = f32::INFINITY;
const NEG_INF: f32 = f32::NEG_INFINITY;

fn float_loop_match(start: f32) -> (&'static str, u32) {
    let mut s = start;
    #[loop_match]
    'outer: loop {
        s = 'blk: {
            match s {
                1.0 => {
                    #[const_continue]
                    break 'blk NEG_ZERO;
                }
                2.0 => {
                    #[const_continue]
                    break 'blk NAN_VAL;
                }
                3.0 => {
                    #[const_continue]
                    break 'blk POS_INF;
                }
                4.0 => {
                    #[const_continue]
                    break 'blk NEG_INF;
                }
                x @ 0.0 => break 'outer ("zero_arm", x.to_bits()),
                5.0.. => break 'outer ("ge5_or_pos_inf", s.to_bits()),
                ..0.0 => break 'outer ("lt0_or_neg_inf", s.to_bits()),
                _ => break 'outer ("nan_wildcard", s.to_bits()),
            }
        };
    }
}

fn float_plain_loop(start: f32) -> (&'static str, u32) {
    let mut s = start;
    'outer: loop {
        s = 'blk: {
            match s {
                1.0 => break 'blk NEG_ZERO,
                2.0 => break 'blk NAN_VAL,
                3.0 => break 'blk POS_INF,
                4.0 => break 'blk NEG_INF,
                x @ 0.0 => break 'outer ("zero_arm", x.to_bits()),
                5.0.. => break 'outer ("ge5_or_pos_inf", s.to_bits()),
                ..0.0 => break 'outer ("lt0_or_neg_inf", s.to_bits()),
                _ => break 'outer ("nan_wildcard", s.to_bits()),
            }
        };
    }
}

fn float_open_range_neg_zero(use_const_continue: bool) -> (&'static str, u32) {
    let mut s: f32 = 1.0;
    if use_const_continue {
        #[loop_match]
        'outer: loop {
            s = 'blk: {
                match s {
                    1.0 => {
                        #[const_continue]
                        break 'blk NEG_ZERO;
                    }
                    ..0.0 => break 'outer ("strictly_lt_zero", s.to_bits()),
                    0.0.. => break 'outer ("ge_zero_open_range", s.to_bits()),
                    _ => break 'outer ("nan", s.to_bits()),
                }
            };
        }
    } else {
        'outer: loop {
            s = 'blk: {
                match s {
                    1.0 => break 'blk NEG_ZERO,
                    ..0.0 => break 'outer ("strictly_lt_zero", s.to_bits()),
                    0.0.. => break 'outer ("ge_zero_open_range", s.to_bits()),
                    _ => break 'outer ("nan", s.to_bits()),
                }
            };
        }
    }
}

fn or_bind_separate_loop_match() -> u32 {
    let mut s: u32 = 0;
    let mut acc: u32 = 0;
    #[loop_match]
    'outer: loop {
        s = 'blk: {
            match s {
                x @ 0 | x @ 2 => {
                    acc += x;
                    if x == 0 {
                        acc += 20;
                        #[const_continue]
                        break 'blk 2;
                    } else {
                        break 'outer acc;
                    }
                }
                _ => break 'outer 999,
            }
        };
    }
}

fn or_bind_outer_loop_match() -> u32 {
    let mut s: u32 = 0;
    let mut acc: u32 = 0;
    #[loop_match]
    'outer: loop {
        s = 'blk: {
            match s {
                x @ (0 | 2) => {
                    acc += x;
                    if x == 0 {
                        acc += 20;
                        #[const_continue]
                        break 'blk 2;
                    } else {
                        break 'outer acc;
                    }
                }
                _ => break 'outer 999,
            }
        };
    }
}

fn or_no_bind_loop_match() -> u32 {
    let mut s: u32 = 0;
    let mut steps: u32 = 0;
    #[loop_match]
    'outer: loop {
        s = 'blk: {
            match s {
                0 | 2 => {
                    steps += 1;
                    if steps == 1 {
                        #[const_continue]
                        break 'blk 2;
                    } else {
                        break 'outer s + 100;
                    }
                }
                _ => break 'outer 999,
            }
        };
    }
}

fn main() {
    for start in [1.0f32, 2.0, 3.0, 4.0, POS_ZERO] {
        let lm = float_loop_match(start);
        let pl = float_plain_loop(start);
        assert_eq!(lm.0, pl.0, "arm mismatch for {start}");
        if !f32::from_bits(lm.1).is_nan() {
            assert_eq!(lm.1, pl.1, "bit mismatch for {start}");
        }
    }
    let nz = float_loop_match(1.0);
    let nan = float_loop_match(2.0);
    let pinf = float_loop_match(3.0);
    let ninf = float_loop_match(4.0);
    let open_lm = float_open_range_neg_zero(true);
    let open_pl = float_open_range_neg_zero(false);
    assert_eq!(open_lm, open_pl);
    let ob_sep = or_bind_separate_loop_match();
    let ob_out = or_bind_outer_loop_match();
    let ob_none = or_no_bind_loop_match();
    assert_eq!(ob_sep, 22);
    assert_eq!(ob_out, 22);
    assert_eq!(ob_none, 102);
    println!(
        "NEG_ZERO={:?} NAN={} PINF={:?} NINF={:?} OPEN_NZ={:?} OR_BIND={} OR_OUTER={} OR_NOBIND={}",
        nz, nan.0, pinf, ninf, open_lm, ob_sep, ob_out, ob_none
    );
}
"""


C3_NESTED_OR_ICE_SRC = r"""#![feature(loop_match)]
#![allow(incomplete_features)]

fn nested_binding_or(mut s: u8) -> u8 {
    #[loop_match]
    'outer: loop {
        s = 'blk: {
            match s {
                (x @ (0 | 1)) | x @ 2 => {
                    if x == 0 {
                        #[const_continue]
                        break 'blk 2;
                    }
                    break 'outer x + 10;
                }
                _ => break 'outer 99,
            }
        };
    }
}

fn main() {
    println!("{}", nested_binding_or(0));
}
"""


C4_GATES: dict[str, str] = {
    "c4a_reject_arm_guard": r"""#![feature(loop_match)]
fn main() {
    let mut s = 0u8;
    #[loop_match]
    'outer: loop {
        s = 'blk: {
            match s {
                0 if true => { #[const_continue] break 'blk 1; }
                _ => break 'outer,
            }
        };
    }
}
""",
    "c4b_reject_payload_enum": r"""#![feature(loop_match)]
enum E { A(u8), B }
fn main() {
    let mut s = E::A(0);
    #[loop_match]
    'outer: loop {
        s = 'blk: {
            match s {
                E::A(_) => { #[const_continue] break 'blk E::B; }
                E::B => break 'outer,
            }
        };
    }
}
""",
    "c4c_reject_projected_place": r"""#![feature(loop_match)]
struct Holder { s: u8 }
fn main() {
    let mut h = Holder { s: 0 };
    #[loop_match]
    'outer: loop {
        h.s = 'blk: {
            match h.s {
                0 => { #[const_continue] break 'blk 1; }
                _ => break 'outer,
            }
        };
    }
}
""",
    "c4d_reject_const_param": r"""#![feature(loop_match)]
fn generic<const NEXT: u8>(mut s: u8) {
    #[loop_match]
    'outer: loop {
        s = 'blk: {
            match s {
                0 => { #[const_continue] break 'blk NEXT; }
                _ => break 'outer,
            }
        };
    }
}
fn main() { generic::<1>(0); }
""",
    "c4e_reject_const_block": r"""#![feature(loop_match)]
fn main() {
    let mut s = 0u8;
    #[loop_match]
    'outer: loop {
        s = 'blk: {
            match s {
                0 => { #[const_continue] break 'blk const { 1 }; }
                _ => break 'outer,
            }
        };
    }
}
""",
    "c4f_reject_bad_label": r"""#![feature(loop_match)]
fn main() {
    let mut s = 0u8;
    #[loop_match]
    'outer: loop {
        s = 'blk: {
            match s {
                0 => { #[const_continue] break 'outer; }
                _ => break 'outer,
            }
        };
    }
}
""",
    "c4g_reject_mismatched_update": r"""#![feature(loop_match)]
fn main() {
    let s1 = 0u8;
    let mut s2 = 0u8;
    #[loop_match]
    'outer: loop {
        s2 = 'blk: {
            match s1 {
                0 => { #[const_continue] break 'blk 1; }
                _ => break 'outer,
            }
        };
    }
    let _ = s2;
}
""",
}


C5_DROP_ENUM_SRC = r"""#![feature(loop_match)]
#![allow(incomplete_features)]

use std::cell::RefCell;

thread_local! {
    static LOG: RefCell<Vec<&'static str>> = const { RefCell::new(Vec::new()) };
}

enum DropState { A, B }
impl Drop for DropState {
    fn drop(&mut self) {
        LOG.with(|l| l.borrow_mut().push(match self {
            DropState::A => "drop_S::A",
            DropState::B => "drop_S::B",
        }));
    }
}

struct Guard(&'static str);
impl Drop for Guard {
    fn drop(&mut self) {
        LOG.with(|l| l.borrow_mut().push(self.0));
    }
}

fn run_lm_const_continue() -> Vec<&'static str> {
    LOG.with(|l| l.borrow_mut().clear());
    let mut s = DropState::A;
    #[loop_match]
    'outer: loop {
        s = 'blk: {
            match s {
                DropState::A => {
                    let _o = Guard("armA_outer");
                    {
                        let _i = Guard("armA_inner");
                        #[const_continue]
                        break 'blk DropState::B;
                    }
                }
                DropState::B => {
                    let _b = Guard("armB");
                    break 'outer;
                }
            }
        };
    }
    drop(s);
    LOG.with(|l| l.borrow().clone())
}

fn run_lm_normal_break() -> Vec<&'static str> {
    LOG.with(|l| l.borrow_mut().clear());
    let mut s = DropState::A;
    #[loop_match]
    'outer: loop {
        s = 'blk: {
            match s {
                DropState::A => {
                    let _o = Guard("armA_outer");
                    {
                        let _i = Guard("armA_inner");
                        break 'blk DropState::B;
                    }
                }
                DropState::B => {
                    let _b = Guard("armB");
                    break 'outer;
                }
            }
        };
    }
    drop(s);
    LOG.with(|l| l.borrow().clone())
}

fn run_plain_loop() -> Vec<&'static str> {
    LOG.with(|l| l.borrow_mut().clear());
    let mut s = DropState::A;
    'outer: loop {
        s = 'blk: {
            match s {
                DropState::A => {
                    let _o = Guard("armA_outer");
                    {
                        let _i = Guard("armA_inner");
                        break 'blk DropState::B;
                    }
                }
                DropState::B => {
                    let _b = Guard("armB");
                    break 'outer;
                }
            }
        };
    }
    drop(s);
    LOG.with(|l| l.borrow().clone())
}

fn main() {
    println!("LM_CONST_CONTINUE={:?}", run_lm_const_continue());
    println!("LM_NORMAL_BREAK={:?}", run_lm_normal_break());
    println!("PLAIN_LOOP={:?}", run_plain_loop());
}
"""


C6_UNWIND_SRC = r"""#![feature(loop_match)]
#![allow(incomplete_features)]

use std::cell::RefCell;

thread_local! {
    static LOG: RefCell<Vec<&'static str>> = const { RefCell::new(Vec::new()) };
}

struct Guard(&'static str, bool);
impl Drop for Guard {
    fn drop(&mut self) {
        LOG.with(|l| l.borrow_mut().push(self.0));
        if self.1 {
            panic!("intentional_drop_panic");
        }
    }
}

fn main() {
    let res = std::panic::catch_unwind(|| {
        let mut s = 0u8;
        #[loop_match]
        'outer: loop {
            s = 'blk: {
                match s {
                    0 => {
                        let _outer = Guard("arm0_outer", false);
                        {
                            let _inner = Guard("arm0_inner_panics", true);
                            #[const_continue]
                            break 'blk 1;
                        }
                    }
                    1 => {
                        LOG.with(|l| l.borrow_mut().push("UNREACHABLE_ARM1"));
                        break 'outer;
                    }
                    _ => break 'outer,
                }
            };
        }
    });
    assert!(res.is_err());
    let log = LOG.with(|l| l.borrow().clone());
    println!("UNWIND_CAUGHT={} LOG={:?}", res.is_err(), log);
}
"""


def _prepare_miri_sysroot(work: Path) -> tuple[Path, Path]:
    """Ensure a usable Miri sysroot exists, preferring MIRI_SYSROOT if already built,
    otherwise building offline from the active toolchain's rust-src vendor directory."""
    sysroot_cp = _run(["rustc", "--print", "sysroot"])
    rustc_sysroot = Path(sysroot_cp.stdout.strip())
    miri_bin = rustc_sysroot / "bin" / "miri"

    existing = os.environ.get("MIRI_SYSROOT")
    if existing and (Path(existing) / "lib" / "rustlib").is_dir():
        return miri_bin, Path(existing)

    vendor = rustc_sysroot / "lib" / "rustlib" / "src" / "rust" / "library" / "vendor"
    miri_home = work / "miri_home"
    miri_cargo = miri_home / ".cargo"
    miri_sysroot = work / "miri_sysroot"
    miri_cargo.mkdir(parents=True, exist_ok=True)
    miri_sysroot.mkdir(parents=True, exist_ok=True)
    if vendor.is_dir():
        (miri_cargo / "config.toml").write_text(
            f'[net]\noffline = true\n\n'
            f'[source.crates-io]\nreplace-with = "vendored-sources"\n\n'
            f'[source.vendored-sources]\ndirectory = "{vendor}"\n',
            encoding="utf-8",
        )
    orig_home = Path.home()
    extra = {
        "HOME": str(miri_home),
        "RUSTUP_HOME": os.environ.get("RUSTUP_HOME", str(orig_home / ".rustup")),
        "CARGO_HOME": str(miri_cargo),
        "MIRI_SYSROOT": str(miri_sysroot),
    }
    cargo_miri = rustc_sysroot / "bin" / "cargo-miri"
    setup_cmd = [str(cargo_miri), "miri", "setup"] if cargo_miri.exists() else ["cargo", "miri", "setup"]
    setup = _run(setup_cmd, cwd=miri_home, extra_env=extra, timeout=300)
    if setup.returncode != 0:
        raise RuntimeError(f"miri setup failed ({setup.returncode}): {setup.stderr[:1000]}")
    return miri_bin, miri_sysroot


def run_miri_case(miri_bin: Path, miri_sysroot: Path, src: str, work: Path, case_name: str) -> dict[str, Any]:
    rs_path = work / f"miri_{case_name}.rs"
    rs_path.write_text(src, encoding="utf-8")
    proc = _run(
        [
            str(miri_bin),
            "--edition=2024",
            "--sysroot", str(miri_sysroot),
            "-Zmiri-tree-borrows",
            str(rs_path),
        ],
        cwd=work,
        timeout=180,
    )
    return {
        "miri_rc": proc.returncode,
        "stdout": proc.stdout.strip(),
        "stderr_head": proc.stderr[:1200],
    }


def run_probe() -> dict[str, Any]:
    rustc_v = _run(["rustc", "--version", "--verbose"])
    miri_v = _run(["cargo", "miri", "--version"])
    out: dict[str, Any] = {
        "rustc_version": rustc_v.stdout.strip(),
        "miri_version": miri_v.stdout.strip(),
        "cases": {},
    }

    with tempfile.TemporaryDirectory(prefix="probe_loop_match_") as td:
        work = Path(td)

        # Case 1: DFA at -O0 and -O2 + MIR dump + LLVM IR + Miri
        c1_rs = work / "c1.rs"
        c1_rs.write_text(C1_SRC, encoding="utf-8")
        fn_names = [
            "step_loop_match",
            "step_plain_loop",
            "dfa_stream_loop_match",
            "dfa_stream_plain_loop",
            "drop_order_loop_match",
        ]

        for opt_label, opt_flag in [("c1_dfa_opt0", "0"), ("c1_dfa_opt2", "2")]:
            bin_path = work / f"c1_O{opt_flag}"
            ll_path = work / f"c1_O{opt_flag}.ll"
            mir_dir = work / f"mir_O{opt_flag}"
            mir_dir.mkdir()

            cp_bin = _run([
                "rustc",
                f"-C", f"opt-level={opt_flag}",
                "--edition=2024",
                "-Z", "dump-mir=step_loop_match|step_plain_loop|dfa_stream_loop_match|dfa_stream_plain_loop|drop_order_loop_match",
                "-Z", f"dump-mir-dir={mir_dir}",
                str(c1_rs),
                "-o", str(bin_path),
            ])
            cp_ll = _run([
                "rustc",
                f"-C", f"opt-level={opt_flag}",
                "--edition=2024",
                "--emit=llvm-ir",
                str(c1_rs),
                "-o", str(ll_path),
            ])
            run_bin = _run([str(bin_path)]) if cp_bin.returncode == 0 else None
            ll_cfg = (
                _parse_llvm_fn_cfg(ll_path.read_text(encoding="utf-8"), fn_names)
                if cp_ll.returncode == 0 and ll_path.exists()
                else {}
            )

            mir_stats: dict[str, dict[str, Any]] = {}
            for fn in fn_names:
                mir_stats[fn] = {}
                for stage in ("built.after", "CleanupPostBorrowck.after", "ElaborateDrops.after", "runtime-optimized.after"):
                    matches = sorted(mir_dir.glob(f"*.{fn}.*.{stage}.mir"))
                    if matches:
                        mir_stats[fn][stage] = _summarize_mir_file(matches[0])

            out["cases"][opt_label] = {
                "compile_rc": cp_bin.returncode,
                "run_rc": run_bin.returncode if run_bin else None,
                "stdout": run_bin.stdout.strip() if run_bin else "",
                "llvm_fn_cfg": ll_cfg,
                "mir_stats": mir_stats,
            }

        miri_bin, miri_sysroot = _prepare_miri_sysroot(work)

        out["cases"]["c1_miri_tree_borrows"] = run_miri_case(miri_bin, miri_sysroot, C1_SRC, work, "c1_dfa")

        # Case 2: manual PartialEq rejection
        c2_rs = work / "c2.rs"
        c2_rs.write_text(C2_SRC, encoding="utf-8")
        c2_cp = _run(["rustc", "--edition=2024", str(c2_rs), "-o", str(work / "c2_bin")])
        out["cases"]["c2_opaque_manual_partial_eq_rejection"] = {
            "compile_rc": c2_cp.returncode,
            "stderr_head": c2_cp.stderr[:1500],
        }

        # Case 3: IEEE-754 float ranges and Or-pattern rebinding + Miri + nested-or ICE
        c3_rs = work / "c3.rs"
        c3_rs.write_text(C3_SRC, encoding="utf-8")
        c3_bin = work / "c3_bin"
        c3_cp = _run(["rustc", "--edition=2024", str(c3_rs), "-o", str(c3_bin)])
        c3_run = _run([str(c3_bin)]) if c3_cp.returncode == 0 else None
        out["cases"]["c3_ieee754_float_and_or_bindings"] = {
            "compile_rc": c3_cp.returncode,
            "run_rc": c3_run.returncode if c3_run else None,
            "stdout": c3_run.stdout.strip() if c3_run else "",
            "stderr_head": c3_cp.stderr[:1000],
        }
        out["cases"]["c3_miri_tree_borrows"] = run_miri_case(miri_bin, miri_sysroot, C3_SRC, work, "c3_float_or")

        c3_ice_rs = work / "c3_ice.rs"
        c3_ice_rs.write_text(C3_NESTED_OR_ICE_SRC, encoding="utf-8")
        c3_ice_cp = _run(["rustc", "--edition=2024", str(c3_ice_rs), "-o", str(work / "c3_ice_bin")])
        out["cases"]["c3_nested_binding_or_ice"] = {
            "compile_rc": c3_ice_cp.returncode,
            "stderr_head": c3_ice_cp.stderr[:1200],
        }

        # Case 4: Compile-time rejection gates
        for gate_name, gate_src in C4_GATES.items():
            g_rs = work / f"{gate_name}.rs"
            g_rs.write_text(gate_src, encoding="utf-8")
            g_cp = _run(["rustc", "--edition=2024", str(g_rs), "-o", str(work / f"{gate_name}_bin")])
            out["cases"][gate_name] = {
                "compile_rc": g_cp.returncode,
                "stderr_head": g_cp.stderr[:1200],
            }

        # Case 5: Drop-implementing fieldless enum state overwrite divergence
        c5_rs = work / "c5.rs"
        c5_rs.write_text(C5_DROP_ENUM_SRC, encoding="utf-8")
        c5_bin = work / "c5_bin"
        c5_cp = _run(["rustc", "--edition=2024", str(c5_rs), "-o", str(c5_bin)])
        c5_run = _run([str(c5_bin)]) if c5_cp.returncode == 0 else None
        out["cases"]["c5_drop_fieldless_enum_divergence"] = {
            "compile_rc": c5_cp.returncode,
            "run_rc": c5_run.returncode if c5_run else None,
            "stdout": c5_run.stdout.strip() if c5_run else "",
        }
        out["cases"]["c5_miri_tree_borrows"] = run_miri_case(miri_bin, miri_sysroot, C5_DROP_ENUM_SRC, work, "c5_drop_enum")

        # Case 6: Unwind through #[const_continue] DropTree
        c6_rs = work / "c6.rs"
        c6_rs.write_text(C6_UNWIND_SRC, encoding="utf-8")
        c6_bin = work / "c6_bin"
        c6_cp = _run(["rustc", "--edition=2024", str(c6_rs), "-o", str(c6_bin)])
        c6_run = _run([str(c6_bin)]) if c6_cp.returncode == 0 else None
        out["cases"]["c6_unwind_through_const_continue_drops"] = {
            "compile_rc": c6_cp.returncode,
            "run_rc": c6_run.returncode if c6_run else None,
            "stdout": c6_run.stdout.strip() if c6_run else "",
        }
        out["cases"]["c6_miri_tree_borrows"] = run_miri_case(miri_bin, miri_sysroot, C6_UNWIND_SRC, work, "c6_unwind")

    return out


def main() -> int:
    result = run_probe()
    out_path = Path(sys.argv[1]) if len(sys.argv) > 1 else None
    rendered = json.dumps(result, indent=2, sort_keys=False) + "\n"
    if out_path is not None:
        out_path.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
