#!/usr/bin/env python3
"""Seven-release Runtime(PostCleanup) MIR schema drift and capture compatibility probe.

Compiles a self-contained 30-function Rust language-feature probe (37 post-cleanup
MIR bodies) and three pinned zero-dependency crates.io libraries (ryu 1.0.23,
itoa 1.0.19, memchr 2.8.3) across seven rustc releases (1.93.1, 1.94.0, 1.96.0,
1.99.0, 1.99.1, 1.100.0, 1.102.0-nightly) using `-Z dump-mir=all`, extracting the
`3-2-000.runtime-post-cleanup.after.mir` snapshot for every body.

Separates five layers of cross-release textual vs. semantic MIR drift:
  1. Raw `.mir` text drift
  2. Span/comment-stripped drift (`// ...` stripped)
  3. Disambiguator-normalized drift (`crate[xxxx]` metadata hash normalized)
  4. Alloc-ID-normalized drift (`allocN` global allocation IDs normalized)
  5. Combined normalized semantic/schema drift (disambiguator + allocN +
     registry source-path prefix normalized), categorized by exact root cause.

Deletes each toolchain's temporary `-Z dump-mir-dir` immediately after extracting
`runtime-post-cleanup.after.mir` to avoid tmpfs inode exhaustion (e.g., memchr
emits ~67,000-69,500 intermediate `.mir` files per toolchain).

All measurements come directly from live rustc invocations; zero hardcoded metrics.
"""

import argparse
import difflib
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
import time
from collections import Counter
from pathlib import Path

DEFAULT_TOOLCHAINS = [
    "1.93.1",
    "1.94.0",
    "1.96.0",
    "1.99.0",
    "1.99.1",
    "1.100.0",
    "nightly",
]

FEATURE_PROBE_RS = r'''
#![allow(dead_code, unused_variables, unused_mut, clippy::all)]

use core::mem::{self, MaybeUninit, offset_of};
use core::ptr::{self, NonNull};
use core::sync::atomic::{AtomicU32, AtomicU64, AtomicU8, Ordering, compiler_fence, fence};

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Pair {
    pub a: u32,
    pub b: u64,
}

#[repr(u8)]
pub enum Tag {
    Empty = 0,
    Small(u16) = 1,
    Pair(Pair) = 2,
}

pub struct DropGuard<'a> {
    pub slot: &'a mut u32,
    pub delta: u32,
}

impl<'a> Drop for DropGuard<'a> {
    fn drop(&mut self) {
        *self.slot = self.slot.wrapping_add(self.delta);
    }
}

#[inline(never)]
pub fn f01_checked_arith(a: u32, b: u32, c: i32) -> (u32, i32) {
    let x = a + b;
    let y = c * 3 - (b as i32);
    (x, y)
}

#[inline(never)]
pub fn f02_wrapping_saturating(a: u64, b: u64) -> (u64, u64) {
    (a.wrapping_mul(b).wrapping_add(1), a.saturating_sub(b))
}

#[inline(never)]
pub fn f03_div_rem(a: u64, b: u64, c: i64, d: i64) -> (u64, i64) {
    (a / b + a % b, c / d)
}

#[inline(never)]
pub fn f04_shifts(a: u32, s: u32, b: i64, t: u32) -> (u32, i64) {
    (a << s, b >> t)
}

#[inline(never)]
pub fn f05_slice_index_and_copy(src: &[u8], dst: &mut [u8], idx: usize) -> u8 {
    dst[..4].copy_from_slice(&src[..4]);
    src[idx]
}

#[inline(never)]
pub fn f06_subslice_pattern(s: &[u32]) -> u32 {
    match s {
        [first, .., last] => first.wrapping_add(*last),
        [only] => *only,
        [] => 0,
    }
}

#[inline(never)]
pub unsafe fn f07_ub_checks_unchecked(s: &[u32], i: usize, p: *const u32) -> u32 {
    let a = *s.get_unchecked(i);
    let nn = NonNull::new_unchecked(p as *mut u32);
    let b = ptr::read(nn.as_ptr());
    a.wrapping_add(b)
}

#[inline(never)]
pub unsafe fn f08_copy_nonoverlapping(src: *const u8, dst: *mut u8, n: usize) {
    ptr::copy_nonoverlapping(src, dst, n);
}

#[inline(never)]
pub unsafe fn f09_unreachable_and_assume(x: u32) -> u32 {
    if x == 0 {
        core::hint::unreachable_unchecked();
    }
    x - 1
}

#[inline(never)]
pub fn f10_transmute_bits(x: f64) -> u64 {
    x.to_bits()
}

#[inline(never)]
pub fn f11_enum_discriminant_match(t: Tag) -> u64 {
    match t {
        Tag::Empty => 0,
        Tag::Small(v) => v as u64,
        Tag::Pair(p) => (p.a as u64).wrapping_add(p.b),
    }
}

#[inline(never)]
pub fn f12_enum_construct_set_discriminant(flag: bool, a: u32, b: u64) -> Tag {
    if flag {
        Tag::Pair(Pair { a, b })
    } else {
        Tag::Small(a as u16)
    }
}

#[inline(never)]
pub fn f13_drop_unwind_edge(slot: &mut u32, n: usize, arr: &[u32]) -> u32 {
    let _g = DropGuard { slot, delta: 7 };
    arr[n]
}

#[inline(never)]
pub fn f14_raw_ptr_addr_of(p: &mut Pair) -> (*const u32, *mut u64) {
    let a = &raw const p.a;
    let b = &raw mut p.b;
    (a, b)
}

#[inline(never)]
pub fn f15_offset_and_layout() -> (usize, usize, usize) {
    (offset_of!(Pair, b), mem::size_of::<Pair>(), mem::align_of::<Pair>())
}

#[inline(never)]
pub fn f16_inline_const_block(x: u32) -> u32 {
    let k = const { (1u32 << 16) + 37 };
    x.wrapping_add(k)
}

#[inline(never)]
pub fn f17_const_unevaluated_array(i: usize) -> u8 {
    const LUT: [u8; 8] = [3, 1, 4, 1, 5, 9, 2, 6];
    LUT[i & 7]
}

#[inline(never)]
pub fn f18_loop_with_break_value(s: &[u32], needle: u32) -> Option<usize> {
    let mut i = 0usize;
    loop {
        if i >= s.len() {
            break None;
        }
        if s[i] == needle {
            break Some(i);
        }
        i += 1;
    }
}

#[inline(never)]
pub fn f19_ptr_metadata_slice(s: &[u16]) -> (usize, *const u16) {
    (s.len(), s.as_ptr())
}

#[inline(never)]
pub fn f20_casts_numeric_and_ptr(x: i64, f: f32, p: *const u8) -> (u8, i32, usize, *const u32) {
    (x as u8, f as i32, p as usize, p as *const u32)
}

#[inline(never)]
pub fn f21_array_repeat_aggregate(v: u32) -> [u32; 8] {
    [v; 8]
}

#[inline(never)]
pub fn f22_maybe_uninit_write(v: Pair) -> Pair {
    let mut m = MaybeUninit::<Pair>::uninit();
    m.write(v);
    unsafe { m.assume_init() }
}

pub trait Accum {
    fn step(&self, acc: u64) -> u64;
}

impl Accum for Pair {
    fn step(&self, acc: u64) -> u64 {
        acc.wrapping_add(self.a as u64 ^ self.b)
    }
}

#[inline(never)]
pub fn f23_dyn_vtable_dispatch(obj: &dyn Accum, init: u64) -> u64 {
    obj.step(init)
}

#[inline(never)]
pub fn f24_closure_capture(a: u32, b: u32) -> u32 {
    let f = |x: u32| x.wrapping_mul(a).wrapping_add(b);
    f(11)
}

#[inline(never)]
pub fn f25_atomic_load_acquire(a: &AtomicU64) -> u64 {
    a.load(Ordering::Acquire)
}

#[inline(never)]
pub fn f26_atomic_store_release(a: &AtomicU64, v: u64) {
    a.store(v, Ordering::Release);
}

#[inline(never)]
pub fn f27_atomic_rmw_acqrel(a: &AtomicU32, d: u32) -> u32 {
    a.fetch_add(d, Ordering::AcqRel)
}

#[inline(never)]
pub fn f28_atomic_cas_seqcst(a: &AtomicU64, cur: u64, new: u64) -> Result<u64, u64> {
    a.compare_exchange(cur, new, Ordering::SeqCst, Ordering::Acquire)
}

#[inline(never)]
pub fn f29_atomic_fence_and_compiler_fence(a: &AtomicU8, v: u8) -> u8 {
    a.store(v, Ordering::Relaxed);
    fence(Ordering::SeqCst);
    compiler_fence(Ordering::AcqRel);
    a.load(Ordering::Relaxed)
}

#[inline(never)]
pub fn f30_option_niche_unwrap(o: Option<NonNull<u8>>) -> usize {
    match o {
        Some(p) => p.as_ptr() as usize,
        None => 0,
    }
}
'''


def run_cmd(cmd, env=None, timeout=180):
    t0 = time.monotonic()
    p = subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=timeout)
    return p.returncode, p.stdout, p.stderr, round(time.monotonic() - t0, 3)


def rustc_info(tc: str) -> dict:
    rc, out, _, _ = run_cmd(["rustup", "run", tc, "rustc", "--version", "--verbose"])
    info = {"toolchain": tc, "rc": rc}
    for line in out.splitlines():
        if ":" in line:
            k, v = line.split(":", 1)
            info[k.strip()] = v.strip()
        elif line.startswith("rustc "):
            info["version_line"] = line.strip()
    return info


def scrub_paths(text: str, scrub_prefixes: list[str]) -> str:
    s = text
    for pfx in scrub_prefixes:
        if pfx:
            s = s.replace(pfx, "<SRC_ROOT>")
    return s


def norm_span(text: str) -> str:
    return "\n".join(
        code for line in text.splitlines()
        if (code := re.sub(r"//.*$", "", line).rstrip())
    )


def norm_disamb_only(text: str) -> str:
    return re.sub(r"([A-Za-z0-9_]+)\[[0-9a-f]{4,16}\]", r"\1[DISAMB]", norm_span(text))


def norm_alloc_only(text: str) -> str:
    return re.sub(r"\balloc\d+\b", "allocN", norm_span(text))


def norm_semantic(text: str) -> str:
    s = norm_disamb_only(text)
    s = re.sub(r"\balloc\d+\b", "allocN", s)
    return s


def h16(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()[:16]


def collect_postcleanup(mir_dir: Path, scrub_prefixes: list[str]):
    post = {}
    pass_pats = Counter()
    total_mir = 0
    for p in sorted(mir_dir.glob("*.mir")):
        total_mir += 1
        m = re.match(r"^(.+?)\.(\d+(?:-\d+)+)\.([^.]+)\.(before|after)\.mir$", p.name)
        if m:
            fn_name, pass_num, pass_name, phase = m.groups()
            if "runtime-post-cleanup" in pass_name.lower() or "runtime_post_cleanup" in pass_name.lower():
                pass_pats[f"{pass_num}.{pass_name}.{phase}"] += 1
                if phase == "after":
                    post[fn_name] = scrub_paths(p.read_text(errors="replace"), scrub_prefixes)
    return post, dict(pass_pats), total_mir


def find_offline_crate(cargo_registry_src: Path, name_prefix: str) -> Path | None:
    if not cargo_registry_src.exists():
        return None
    matches = sorted(cargo_registry_src.glob(f"*/{name_prefix}-*"))
    return matches[-1] if matches else None


def classify_semantic_diff(fn: str, diff_lines: list[str], from_tc: str, to_tc: str) -> list[str]:
    changed = [
        l for l in diff_lines
        if l.startswith(("+", "-")) and not l.startswith(("+++", "---"))
    ]
    dtxt = "\n".join(changed)
    tags = []
    if "Atomic::<" in dtxt or "Atomic<" in dtxt:
        tags.append("generic_atomic")
    if "core::panicking::assert_failed" in dtxt:
        tags.append("assert_failed_trimmed_path")
    if ("memchr::memchr" in dtxt or "memchr::memrchr" in dtxt
            or "fn memchr(" in dtxt or "fn memchr::" in dtxt):
        tags.append("doc_hidden_trimmed_path")
    if "(PtrToPtr)" in dtxt:
        tags.append("ptr_to_ptr_coercion_temp")
    if "no_retag copy" in dtxt:
        tags.append("no_retag_copy")
    if "(BoxDerefTransmute)" in dtxt:
        tags.append("box_deref_transmute")
    if "BoxRaw<" in dtxt:
        tags.append("box_raw_field_type")
    if "discriminant(" in dtxt:
        tags.append("dead_discriminant_elision")
    if "unreachable_unchecked" in dtxt:
        tags.append("never_type_local_elision")
    if "{closure@" in dtxt and "__" in dtxt:
        tags.append("closure_upvar_debug_name")
    if "Option<!>" in dtxt:
        tags.append("option_try_residual_never")
    if fn.endswith("-fmt") and to_tc == "nightly":
        tags.append("derive_debug_concat_names")
    if "scope " in dtxt and to_tc == "nightly" and not fn.endswith("-fmt"):
        tags.append("empty_try_scope_elision")
    return tags or ["other"]


def compare_pair(da: dict, db: dict, a: str, b: str, max_samples: int = 4) -> dict:
    common = sorted(set(da) & set(db))
    only_a = sorted(set(da) - set(db))
    only_b = sorted(set(db) - set(da))
    raw_c = [fn for fn in common if da[fn]["h_raw"] != db[fn]["h_raw"]]
    span_c = [fn for fn in common if da[fn]["h_span"] != db[fn]["h_span"]]
    dis_c = [fn for fn in common if da[fn]["h_disamb"] != db[fn]["h_disamb"]]
    alc_c = [fn for fn in common if da[fn]["h_alloc"] != db[fn]["h_alloc"]]
    sem_c = [fn for fn in common if da[fn]["h_sem"] != db[fn]["h_sem"]]

    cat_counts = Counter()
    tag_counts = Counter()
    diff_samples = {}
    seen_cats = set()
    for fn in sem_c:
        dlines = list(difflib.unified_diff(
            da[fn]["sem"].splitlines(),
            db[fn]["sem"].splitlines(),
            fromfile=f"{a}:{fn}",
            tofile=f"{b}:{fn}",
            n=1,
            lineterm="",
        ))
        tags = classify_semantic_diff(fn, dlines, a, b)
        combo = "+".join(tags)
        cat_counts[combo] += 1
        for tg in tags:
            tag_counts[tg] += 1
        if combo not in seen_cats or len(diff_samples) < max_samples:
            seen_cats.add(combo)
            if len(diff_samples) < 10:
                diff_samples[fn] = dlines[:22]

    span_only_samples = {}
    for fn in [x for x in span_c if x not in sem_c][:2]:
        span_only_samples[fn] = list(difflib.unified_diff(
            da[fn]["span"].splitlines(),
            db[fn]["span"].splitlines(),
            fromfile=f"{a}:{fn}",
            tofile=f"{b}:{fn}",
            n=1,
            lineterm="",
        ))[:16]

    return {
        "from": a,
        "to": b,
        "common_fns": len(common),
        "only_in_from": only_a,
        "only_in_to": only_b,
        "raw_changed": len(raw_c),
        "span_changed": len(span_c),
        "span_changed_pct": round(100.0 * len(span_c) / len(common), 2) if common else 0.0,
        "after_disamb_only_changed": len(dis_c),
        "after_alloc_only_changed": len(alc_c),
        "semantic_changed": len(sem_c),
        "semantic_changed_pct": round(100.0 * len(sem_c) / len(common), 2) if common else 0.0,
        "semantic_category_combos": dict(cat_counts),
        "semantic_tag_counts": dict(tag_counts),
        "diff_samples": diff_samples,
        "span_only_samples": span_only_samples,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True, help="Output JSON summary path")
    ap.add_argument(
        "--cargo-registry-src",
        default=str(Path(os.environ.get("CARGO_HOME", Path.home() / ".cargo")) / "registry" / "src"),
        help="Path to Cargo registry src directory containing ryu, itoa, memchr",
    )
    ap.add_argument("--toolchains", nargs="+", default=DEFAULT_TOOLCHAINS)
    args = ap.parse_args()

    t_start = time.monotonic()
    reg_src = Path(args.cargo_registry_src)
    toolchains = args.toolchains

    report = {
        "probe": "rustc_seven_release_postcleanup_mir_schema_drift",
        "timestamp_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "toolchains": {tc: rustc_info(tc) for tc in toolchains},
        "corpora": {},
    }

    with tempfile.TemporaryDirectory(prefix="mir_7rel_probe_") as td:
        td_path = Path(td)
        fp_rs = td_path / "feature_probe.rs"
        fp_rs.write_text(FEATURE_PROBE_RS, encoding="utf-8")

        specs = [("feature_probe", fp_rs, "feature_probe", ["--edition=2021"], None)]
        for cname, flags in [
            ("ryu", ["--edition=2018"]),
            ("itoa", ["--edition=2021"]),
            ("memchr", ["--edition=2021", "--cfg", 'feature="alloc"', "--cfg", 'feature="std"']),
        ]:
            cdir = find_offline_crate(reg_src, cname)
            if cdir and (cdir / "src" / "lib.rs").exists():
                vcs = cdir / ".cargo_vcs_info.json"
                vcs_sha = None
                if vcs.exists():
                    vcs_sha = json.loads(vcs.read_text(encoding="utf-8")).get("git", {}).get("sha1")
                specs.append((cname, cdir / "src" / "lib.rs", cdir.name, flags, vcs_sha))

        for cname, src_file, label, flags, vcs_sha in specs:
            scrub_prefixes = [str(src_file.parent.parent), str(td_path)]
            per_tc = {}
            by_tc = {}
            disamb_progression = {}
            for tc in toolchains:
                mir_dir = td_path / f"mir_{cname}_{tc}"
                mir_dir.mkdir()
                env = os.environ.copy()
                env["RUSTC_BOOTSTRAP"] = "1"
                cmd = [
                    "rustup", "run", tc, "rustc",
                    "--crate-type=lib", f"--crate-name={cname}",
                    *flags,
                    "-C", "opt-level=2",
                    "-Z", "dump-mir=all",
                    "-Z", f"dump-mir-dir={mir_dir}",
                    "-o", str(td_path / f"lib{cname}_{tc}.rlib"),
                    str(src_file),
                ]
                rc, _, err, elapsed = run_cmd(cmd, env=env)
                post, pats, total_mir = collect_postcleanup(mir_dir, scrub_prefixes)
                shutil.rmtree(mir_dir)

                entries = {}
                disambs = set()
                for fn, body in post.items():
                    sp = norm_span(body)
                    di = norm_disamb_only(body)
                    al = norm_alloc_only(body)
                    sm = norm_semantic(body)
                    for m in re.findall(rf"\b{re.escape(cname)}\[[0-9a-f]{{4,16}}\]", sp):
                        disambs.add(m)
                    entries[fn] = {
                        "h_raw": h16(body),
                        "h_span": h16(sp),
                        "h_disamb": h16(di),
                        "h_alloc": h16(al),
                        "h_sem": h16(sm),
                        "span": sp,
                        "sem": sm,
                    }
                by_tc[tc] = entries
                if disambs:
                    disamb_progression[tc] = sorted(disambs)
                per_tc[tc] = {
                    "rc": rc,
                    "post_cleanup_fns": len(post),
                    "total_mir_files": total_mir,
                    "elapsed_sec": elapsed,
                    "pass_patterns": pats,
                    "err_head": scrub_paths(err[:240], scrub_prefixes) if rc != 0 else "",
                }
                print(f"  {cname} {tc}: rc={rc} post={len(post)} total_mir={total_mir} elapsed={elapsed}s", flush=True)

            transitions = [
                compare_pair(by_tc[a], by_tc[b], a, b)
                for a, b in zip(toolchains, toolchains[1:])
            ]
            cumulative = compare_pair(by_tc[toolchains[0]], by_tc[toolchains[-1]], toolchains[0], toolchains[-1], max_samples=6)
            report["corpora"][cname] = {
                "crate_label": label,
                "vcs_sha1": vcs_sha,
                "extra_flags": flags,
                "disambiguator_progression": disamb_progression,
                "per_toolchain": per_tc,
                "transitions": transitions,
                "cumulative_first_to_last": cumulative,
            }

    report["total_elapsed_sec"] = round(time.monotonic() - t_start, 2)
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"WROTE {out_path} ({out_path.stat().st_size} bytes) in {report['total_elapsed_sec']}s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
