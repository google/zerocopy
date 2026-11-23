#!/usr/bin/env python3
"""Standalone revalidation and kernel-profiling suite for size-pressure,
proof-compression, Pass-1 helper refactoring, and deterministic MIR scaffolding.

Pure Python 3.10+ standard library when run with `--check-static` (plus optional
`--zerocopy-dir`, `--run-whnf-probe --lean <bin>`, and `--run-blockcfg-probe`).
Never hardcodes host-specific paths or mutates source repositories.
"""

from __future__ import annotations

import argparse
import glob
import json
import os
import re
import statistics
import subprocess
import tempfile
import time
from pathlib import Path

# ---------------------------------------------------------------------------
# 1. Lean Theorem-Length & Non-Blank Code Scanner (pure Python stdlib)
# ---------------------------------------------------------------------------

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque|example)\b"
)


def strip_lean_comments(lines: list[str]) -> list[str]:
    """Return non-empty Lean code lines with nested `/- ... -/` and `--` comments stripped."""
    out: list[str] = []
    block_depth = 0
    for s in lines:
        i = 0
        chars: list[str] = []
        n = len(s)
        while i < n:
            if block_depth > 0:
                if s[i : i + 2] == "/-":
                    block_depth += 1
                    i += 2
                elif s[i : i + 2] == "-/":
                    block_depth -= 1
                    i += 2
                else:
                    i += 1
            else:
                if s[i : i + 2] == "/-":
                    block_depth += 1
                    i += 2
                elif s[i : i + 2] == "--":
                    break
                else:
                    chars.append(s[i])
                    i += 1
        joined = "".join(chars).strip()
        if joined:
            out.append(joined)
    return out


def scan_lean_files(paths: list[Path], base_dir: Path | None = None) -> dict:
    """Measure non-blank LOC and theorem length quantiles across a set of `.lean` files."""
    total_files = 0
    total_nonblank = 0
    thm_lengths: list[int] = []
    long_thms: list[tuple[int, str, str]] = []

    for path in sorted(paths):
        total_files += 1
        raw_lines = path.read_text(encoding="utf-8").splitlines()
        total_nonblank += len(strip_lean_comments(raw_lines))

        decls: list[tuple[int, str, str]] = []
        in_comment = 0
        for idx, raw in enumerate(raw_lines):
            s = raw.strip()
            if "/-" in s and "-/" not in s:
                in_comment += s.count("/-") - s.count("-/")
            elif "-/" in s and in_comment > 0:
                in_comment = max(0, in_comment - s.count("-/"))
                continue
            if in_comment > 0 or not s or s.startswith("--"):
                continue
            m = DECL_RE.match(s)
            if m:
                decls.append((idx, m.group(1), s[:80]))

        for di, (start, kind, sig) in enumerate(decls):
            if kind not in ("theorem", "lemma"):
                continue
            end = decls[di + 1][0] if di + 1 < len(decls) else len(raw_lines)
            n = len(strip_lean_comments(raw_lines[start:end]))
            thm_lengths.append(n)
            if n > 60:
                rel = str(path.relative_to(base_dir)) if base_dir else str(path)
                long_thms.append((n, f"{rel}:{start + 1}", sig))

    thm_sorted = sorted(thm_lengths)
    k = len(thm_sorted)

    def pct(p: float) -> int:
        if not k:
            return 0
        return thm_sorted[min(k - 1, int(round(p * (k - 1))))]

    return {
        "files": total_files,
        "nonblank_lines": total_nonblank,
        "theorems": k,
        "median": statistics.median(thm_sorted) if k else 0,
        "mean": round(statistics.mean(thm_sorted), 2) if k else 0.0,
        "p90": pct(0.90),
        "p99": pct(0.99),
        "max": max(thm_sorted) if k else 0,
        "pct_le_5": round(100.0 * sum(1 for x in thm_sorted if x <= 5) / k, 1) if k else 0.0,
        "pct_le_15": round(100.0 * sum(1 for x in thm_sorted if x <= 15) / k, 1) if k else 0.0,
        "gt_60_count": sum(1 for x in thm_sorted if x > 60),
        "pct_gt_60": round(100.0 * sum(1 for x in thm_sorted if x > 60) / k, 1) if k else 0.0,
        "top_long": sorted(long_thms, reverse=True)[:5],
    }


# ---------------------------------------------------------------------------
# 2. Identity-Keyed Symbolic Straight-Line MIR Stepper (AutoScaffold v3 core)
# ---------------------------------------------------------------------------

def identity_slug(identity: str) -> str:
    s = identity.removeprefix("rust-path-v1::")
    return re.sub(r"[^A-Za-z0-9_]+", "_", s).strip("_")


def _is_u64_ty(ty: dict) -> bool:
    return ty == {"kind": "int", "width": "i64", "signed": False}


def _resolve_u64(op: dict, slots: list[tuple[str, str]]) -> str | None:
    kind = op.get("kind")
    if kind in ("copy", "move"):
        loc = op["local"]
        sk, expr = slots[loc]
        if sk != "u64":
            return None
        if kind == "move":
            slots[loc] = ("none", "")
        return expr
    if kind == "constant" and _is_u64_ty(op.get("ty", {})):
        lit = op.get("lit", {})
        if lit.get("kind") == "scalar":
            return f"(BitVec.ofNat 64 {lit['bits']})"
    return None


def analyze_u64_straight_line(body: dict) -> tuple[list[str], str, str, list[tuple]] | None:
    """Symbolically lower a 1-block `u64`/`bool` MIR body to an explicit step trace."""
    blocks = body.get("blocks", [])
    if len(blocks) != 1:
        return None
    bb = blocks[0]
    if bb.get("terminator", {}).get("kind") != "ret":
        return None
    arg_count = body.get("arg_count", 0)
    tys = body.get("local_tys", [])
    if len(tys) < 1 + arg_count:
        return None
    if tys[0] == {"kind": "bool"}:
        ret_kind = "bool"
    elif _is_u64_ty(tys[0]):
        ret_kind = "u64"
    else:
        return None
    if any(not _is_u64_ty(tys[i]) for i in range(1, 1 + arg_count)):
        return None

    arg_names = [f"a{i}" for i in range(arg_count)]
    slots: list[tuple[str, str]] = (
        [("none", "")]
        + [("u64", a) for a in arg_names]
        + [("dead", "")] * (len(tys) - 1 - arg_count)
    )
    trace: list[tuple] = []
    for step_idx, st in enumerate(bb.get("statements", []), 1):
        sk = st.get("kind")
        if sk == "storage_live":
            slots[st["local"]] = ("none", "")
            trace.append(("rfl", step_idx, list(slots)))
        elif sk == "storage_dead":
            slots[st["local"]] = ("dead", "")
            trace.append(("rfl", step_idx, list(slots)))
        elif sk == "assign":
            dst = st["local"]
            val = st.get("value", {})
            vk = val.get("kind")
            if vk == "use":
                expr = _resolve_u64(val.get("operand", {}), slots)
                if expr is None:
                    return None
                slots[dst] = ("u64", expr)
                trace.append(("u64_use", step_idx, expr, list(slots)))
            elif vk == "unary" and val.get("op") == "not":
                expr = _resolve_u64(val.get("operand", {}), slots)
                if expr is None:
                    return None
                res = f"~~~({expr})"
                slots[dst] = ("u64", res)
                trace.append(("u64_not", step_idx, expr, res, list(slots)))
            elif vk == "binary" and val.get("op") == "bit_and":
                lx = _resolve_u64(val.get("left", {}), slots)
                rx = _resolve_u64(val.get("right", {}), slots)
                if lx is None or rx is None:
                    return None
                res = f"({lx}) &&& ({rx})"
                slots[dst] = ("u64", res)
                trace.append(("u64_and", step_idx, lx, rx, list(slots)))
            elif vk == "binary" and val.get("op") == "eq":
                right = val.get("right", {})
                if right.get("kind") != "constant":
                    return None
                lx = _resolve_u64(val.get("left", {}), slots)
                rx = _resolve_u64(right, slots)
                if lx is None or rx is None:
                    return None
                bits = int(right["lit"]["bits"])
                res = f"({lx}) == ({rx})"
                slots[dst] = ("bool", res)
                trace.append(("u64_eq_const", step_idx, lx, bits, list(slots)))
            else:
                return None
        else:
            return None

    if slots[0][0] != ret_kind:
        return None
    return arg_names, ret_kind, slots[0][1], trace


def build_identity_index(bodies: list[dict]) -> dict[str, tuple[int, tuple]]:
    """Map semantic body identities to `(idx, trace)` independently of declaration order."""
    out: dict[str, tuple[int, tuple]] = {}
    for idx, body in enumerate(bodies):
        slug = identity_slug(body["identity"])
        tr = analyze_u64_straight_line(body)
        if tr is None:
            raise AssertionError(f"failed to symbolically lower {slug}")
        out[slug] = (idx, tr)
    return out


def run_static_selftest() -> None:
    sample_lean = [
        "/- header",
        "   /- nested comment theorem fake : True := trivial -/ -/",
        "@[simp] private theorem short_thm : True := by",
        "  trivial -- trailing comment",
        "",
        "theorem second_thm : Nat.succ 0 = 1 := rfl",
    ]
    stats = scan_lean_files_from_strings([sample_lean])
    assert stats["theorems"] == 2 and stats["median"] == 1.5, stats

    u64 = {"kind": "int", "width": "i64", "signed": False}
    b_align_mask = {
        "identity": "rust-path-v1::align_down_mask",
        "arg_count": 2,
        "local_tys": [u64, u64, u64, u64, u64, u64],
        "blocks": [{
            "statements": [
                {"kind": "storage_live", "local": 3},
                {"kind": "assign", "local": 3, "value": {"kind": "use", "operand": {"kind": "copy", "local": 1}}},
                {"kind": "storage_live", "local": 4},
                {"kind": "storage_live", "local": 5},
                {"kind": "assign", "local": 5, "value": {"kind": "use", "operand": {"kind": "copy", "local": 2}}},
                {"kind": "assign", "local": 4, "value": {"kind": "unary", "op": "not", "operand": {"kind": "move", "local": 5}}},
                {"kind": "storage_dead", "local": 5},
                {"kind": "assign", "local": 0, "value": {"kind": "binary", "op": "bit_and", "left": {"kind": "move", "local": 3}, "right": {"kind": "move", "local": 4}}},
                {"kind": "storage_dead", "local": 4},
                {"kind": "storage_dead", "local": 3},
            ],
            "terminator": {"kind": "ret"},
        }],
    }
    b_is_aligned = {
        "identity": "rust-path-v1::is_aligned_mask",
        "arg_count": 2,
        "local_tys": [{"kind": "bool"}, u64, u64, u64, u64, u64],
        "blocks": [{
            "statements": [
                {"kind": "storage_live", "local": 3},
                {"kind": "storage_live", "local": 4},
                {"kind": "assign", "local": 4, "value": {"kind": "use", "operand": {"kind": "copy", "local": 1}}},
                {"kind": "storage_live", "local": 5},
                {"kind": "assign", "local": 5, "value": {"kind": "use", "operand": {"kind": "copy", "local": 2}}},
                {"kind": "assign", "local": 3, "value": {"kind": "binary", "op": "bit_and", "left": {"kind": "move", "local": 4}, "right": {"kind": "move", "local": 5}}},
                {"kind": "storage_dead", "local": 5},
                {"kind": "storage_dead", "local": 4},
                {"kind": "assign", "local": 0, "value": {"kind": "binary", "op": "eq", "left": {"kind": "move", "local": 3}, "right": {"kind": "constant", "ty": u64, "lit": {"kind": "scalar", "bits": "0"}}}},
                {"kind": "storage_dead", "local": 3},
            ],
            "terminator": {"kind": "ret"},
        }],
    }
    # P3 perturbation: introduce explicit `let inv = !mask; addr & inv` local
    b_align_mask_p3 = {
        "identity": "rust-path-v1::align_down_mask",
        "arg_count": 2,
        "local_tys": [u64, u64, u64, u64, u64, u64, u64],
        "blocks": [{
            "statements": [
                {"kind": "storage_live", "local": 3},
                {"kind": "storage_live", "local": 6},
                {"kind": "assign", "local": 6, "value": {"kind": "use", "operand": {"kind": "copy", "local": 2}}},
                {"kind": "assign", "local": 3, "value": {"kind": "unary", "op": "not", "operand": {"kind": "move", "local": 6}}},
                {"kind": "storage_dead", "local": 6},
                {"kind": "storage_live", "local": 4},
                {"kind": "assign", "local": 4, "value": {"kind": "use", "operand": {"kind": "copy", "local": 1}}},
                {"kind": "storage_live", "local": 5},
                {"kind": "assign", "local": 5, "value": {"kind": "use", "operand": {"kind": "copy", "local": 3}}},
                {"kind": "assign", "local": 0, "value": {"kind": "binary", "op": "bit_and", "left": {"kind": "move", "local": 4}, "right": {"kind": "move", "local": 5}}},
                {"kind": "storage_dead", "local": 5},
                {"kind": "storage_dead", "local": 4},
                {"kind": "storage_dead", "local": 3},
            ],
            "terminator": {"kind": "ret"},
        }],
    }

    idx_base = build_identity_index([b_align_mask, b_is_aligned])
    idx_p2 = build_identity_index([b_is_aligned, b_align_mask])
    idx_p3 = build_identity_index([b_align_mask_p3, b_is_aligned])

    assert idx_base["align_down_mask"][0] == 0 and idx_p2["align_down_mask"][0] == 1
    assert idx_base["align_down_mask"][1][:3] == (["a0", "a1"], "u64", "(a0) &&& (~~~(a1))")
    assert idx_p3["align_down_mask"][1][:3] == (["a0", "a1"], "u64", "(a0) &&& (~~~(a1))")
    assert len(idx_p3["align_down_mask"][1][3]) == 13
    assert idx_base["is_aligned_mask"][1][:3] == (["a0", "a1"], "bool", "((a0) &&& (a1)) == ((BitVec.ofNat 64 0))")
    print("STATIC_SELFTEST_OK: comment/theorem parser + identity-keyed MIR P2/P3 lowering verified.")


def scan_lean_files_from_strings(docs: list[list[str]]) -> dict:
    with tempfile.TemporaryDirectory(prefix="sp_scan_") as td:
        paths = []
        for idx, lines in enumerate(docs):
            p = Path(td) / f"M{idx}.lean"
            p.write_text("\n".join(lines) + "\n", encoding="utf-8")
            paths.append(p)
        return scan_lean_files(paths, Path(td))


# ---------------------------------------------------------------------------
# 3. Module-Exact Kernel Profiler (Public + `_private.*` via `moduleData`)
# ---------------------------------------------------------------------------

PROFILER_LEAN = r"""import Lean
import Lean.Replay

open Lean

structure ExprStats where
  dagNodes  : Nat
  treeNodes : Nat
  maxDepth  : Nat

partial def measureExpr (root : Expr) : ExprStats :=
  let cap := 100000000
  let rec go (e : Expr) : StateM (Std.HashMap Expr (Nat × Nat)) (Nat × Nat) := do
    if let some cached := (← get).get? e then
      return cached
    let res ← match e with
      | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => pure (1, 1)
      | .mdata _ b | .proj _ _ b => do
        let (t, d) ← go b
        pure (Nat.min cap (1 + t), 1 + d)
      | .app f a => do
        let (tf, df) ← go f
        let (ta, da) ← go a
        pure (Nat.min cap (1 + tf + ta), 1 + Nat.max df da)
      | .lam _ ty body _ | .forallE _ ty body _ => do
        let (tt, dt) ← go ty
        let (tb, db) ← go body
        pure (Nat.min cap (1 + tt + tb), 1 + Nat.max dt db)
      | .letE _ ty val body _ => do
        let (tt, dt) ← go ty
        let (tv, dv) ← go val
        let (tb, db) ← go body
        pure (Nat.min cap (1 + tt + tv + tb), 1 + Nat.max dt (Nat.max dv db))
    modify (·.insert e res)
    return res
  let ((treeN, depth), vis) := (go root).run {}
  { dagNodes := vis.size, treeNodes := treeN, maxDepth := depth }

def main (args : List String) : IO Unit := do
  let [modStr] := args | throw (IO.userError "expected <moduleName>")
  let targetMod := modStr.toName
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := targetMod }] {} 0
  let mut modIdx? : Option Nat := none
  for i in Array.range env.header.modules.size do
    if env.header.modules[i]!.module == targetMod then
      modIdx? := some i
  let some modIdx := modIdx? | throw (IO.userError s!"module {targetMod} not found")
  let data := env.header.moduleData[modIdx]!
  let mut sumValTree : Nat := 0
  let mut declCount : Nat := 0
  let mut modConsts : Std.HashMap Name ConstantInfo := {}
  let mut visited : Std.HashSet Expr := {}
  for i in Array.range data.constNames.size do
    let name := data.constNames[i]!
    let ci := data.constants[i]!
    modConsts := modConsts.insert name ci
    let val? : Option Expr := match ci with
      | .defnInfo v => some v.value
      | .thmInfo v  => some v.value
      | _           => none
    let vs := match val? with
      | some v => measureExpr v
      | none   => { dagNodes := 0, treeNodes := 0, maxDepth := 0 }
    let rec walk (e : Expr) : StateM (Std.HashSet Expr) Unit := do
      if (← get).contains e then return
      modify (·.insert e)
      match e with
      | .mdata _ b | .proj _ _ b => walk b
      | .app f a => walk f; walk a
      | .lam _ t b _ | .forallE _ t b _ => walk t; walk b
      | .letE _ t v b _ => walk t; walk v; walk b
      | _ => pure ()
    let (_, visited') := (walk ci.type).run visited
    visited := visited'
    if let some v := val? then
      let (_, visited'') := (walk v).run visited
      visited := visited''
    declCount := declCount + 1
    sumValTree := sumValTree + vs.treeNodes
  let mut imports : Array Import := #[]
  for imp in data.imports do
    imports := imports.push imp
  let mut replayTimes : Array Float := #[]
  for _ in Array.range 3 do
    let baseEnv ← importModules imports {} 0
    let t0 ← IO.monoNanosNow
    let _ ← Lean.Kernel.Environment.replay modConsts baseEnv.toKernelEnv
    let t1 ← IO.monoNanosNow
    replayTimes := replayTimes.push ((t1 - t0).toFloat / 1000000.0)
  IO.println <| Json.compress <| Json.mkObj [
    ("decl_count", toJson declCount),
    ("module_union_dag", toJson visited.size),
    ("sum_val_tree", toJson sumValTree),
    ("kernel_replay_runs_ms", toJson replayTimes)
  ]
"""


def profile_lean_module(lean_bin: Path, lean_paths: list[Path], mod_name: str) -> dict:
    stdlib = lean_bin.resolve().parent.parent / "lib" / "lean"
    full_paths = list(lean_paths) + ([stdlib] if stdlib not in lean_paths else [])
    env = os.environ.copy()
    env["LEAN_PATH"] = ":".join(str(p) for p in full_paths)
    with tempfile.TemporaryDirectory(prefix="sp_kprof_") as td:
        prof = Path(td) / "Profile.lean"
        prof.write_text(PROFILER_LEAN, encoding="utf-8")
        p = subprocess.run(
            [str(lean_bin), "--run", str(prof), mod_name],
            env=env, capture_output=True, text=True, check=True,
        )
        return json.loads(p.stdout.strip().splitlines()[-1])


# ---------------------------------------------------------------------------
# 4. Probe R2-A: WHNF / `by rfl` Goodhart Trap Reproduction
# ---------------------------------------------------------------------------

GRID_DEFS = """prelude
import Init.Data.Nat.Basic

def okPair (r c : Nat) : Bool := (r + c + 1) - 1 == r + c

def checkRow (r : Nat) : Nat → Bool
  | 0 => true
  | c + 1 => okPair r c && checkRow r c

def checkGrid (cols : Nat) : Nat → Bool
  | 0 => true
  | r + 1 => checkRow r cols && checkGrid cols r
"""

GRID_RFL = GRID_DEFS + "\ntheorem check_grid_rfl : checkGrid {COLS} {ROWS} = true := by rfl\n"

GRID_STRUCT = GRID_DEFS + """
private theorem okPair_true (r c : Nat) : okPair r c = true :=
  beq_iff_eq.mpr (Nat.add_sub_cancel (r + c) 1)

private theorem checkRow_true (r : Nat) : ∀ cols, checkRow r cols = true
  | 0 => rfl
  | c + 1 => by dsimp [checkRow]; rw [okPair_true, checkRow_true r c]; rfl

theorem checkGrid_true (cols : Nat) : ∀ rows, checkGrid cols rows = true
  | 0 => rfl
  | r + 1 => by dsimp [checkGrid]; rw [checkRow_true, checkGrid_true cols r]; rfl

theorem check_grid_struct : checkGrid {COLS} {ROWS} = true := checkGrid_true {COLS} {ROWS}
"""


def run_whnf_probe(lean_bin: Path) -> list[dict]:
    cases = [
        ("grid_rfl_2x80", GRID_RFL.format(COLS=80, ROWS=2), 0),
        ("grid_rfl_8x80", GRID_RFL.format(COLS=80, ROWS=8), 0),
        ("grid_rfl_32x80", GRID_RFL.format(COLS=80, ROWS=32), 0),
        ("grid_rfl_64x80", GRID_RFL.format(COLS=80, ROWS=64), 0),
        ("grid_rfl_128x80", GRID_RFL.format(COLS=80, ROWS=128), 1),
        ("grid_struct_64x80", GRID_STRUCT.format(COLS=80, ROWS=64), 0),
        ("grid_struct_100000x80", GRID_STRUCT.format(COLS=80, ROWS=100000), 0),
    ]
    stdlib = lean_bin.resolve().parent.parent / "lib" / "lean"
    results = []
    for name, src, exp_rc in cases:
        with tempfile.TemporaryDirectory(prefix=f"sp_whnf_{name}_") as td:
            d = Path(td)
            f, ol = d / "M.lean", d / "M.olean"
            f.write_text(src, encoding="utf-8")
            env = dict(os.environ, LEAN_PATH=f"{d}:{stdlib}")
            cold = []
            rc = 0
            err = ""
            for _ in range(3 if exp_rc == 0 else 1):
                if ol.exists():
                    ol.unlink()
                t0 = time.monotonic()
                p = subprocess.run(
                    [str(lean_bin), "-Ddebug.skipKernelTC=false", "-o", str(ol), str(f)],
                    cwd=str(d), env=env, capture_output=True, text=True,
                )
                cold.append(round((time.monotonic() - t0) * 1000, 1))
                rc = p.returncode
                if rc != 0:
                    err = (p.stdout + p.stderr).splitlines()[0]
                    break
            assert rc == exp_rc, f"{name}: got rc={rc}, expected {exp_rc}: {err}"
            row = {"name": name, "rc": rc, "loc": len([l for l in src.splitlines() if l.strip()])}
            if rc == 0:
                kp = profile_lean_module(lean_bin, [d], "M")
                row.update({
                    "olean_bytes": ol.stat().st_size,
                    "cold_med_ms": round(statistics.median(cold), 1),
                    "replay_med_ms": round(statistics.median(kp["kernel_replay_runs_ms"]), 3),
                    "decl_count": kp["decl_count"],
                    "module_union_dag": kp["module_union_dag"],
                    "sum_val_tree": kp["sum_val_tree"],
                })
            else:
                row["err"] = err
            results.append(row)
    return results


def main() -> None:
    ap = argparse.ArgumentParser(description="Revalidate size-pressure and scaffolding probes.")
    ap.add_argument("--check-static", action="store_true", help="Run zero-dep Python stdlib probes.")
    ap.add_argument("--zerocopy-dir", type=Path, help="Optional google/zerocopy checkout to census.")
    ap.add_argument("--run-whnf-probe", action="store_true", help="Run live Lean WHNF Goodhart probe.")
    ap.add_argument("--lean", type=Path, help="Path to pinned Lean v4.34.1 binary.")
    args = ap.parse_args()

    if args.check_static or (not args.run_whnf_probe and not args.zerocopy_dir):
        run_static_selftest()
    if args.zerocopy_dir:
        zc = args.zerocopy_dir.resolve()
        census = {
            "anneal_theory": scan_lean_files(
                [Path(p) for p in glob.glob(str(zc / "anneal/theory/**/*.lean"), recursive=True)], zc
            ),
            "anneal_correspondence": scan_lean_files(
                [Path(p) for p in glob.glob(str(zc / "anneal/correspondence/**/*.lean"), recursive=True)], zc
            ),
            "zerocopy_proofs": scan_lean_files(
                [Path(p) for p in glob.glob(str(zc / "zerocopy/proofs/*/Proof.lean"))], zc
            ),
        }
        print(json.dumps({"census": census}, indent=2))
    if args.run_whnf_probe:
        if not args.lean:
            ap.error("--run-whnf-probe requires --lean")
        print(json.dumps({"whnf_probe": run_whnf_probe(args.lean)}, indent=2))


if __name__ == "__main__":
    main()
