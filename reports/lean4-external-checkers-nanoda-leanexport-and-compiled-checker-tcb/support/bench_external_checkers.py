#!/usr/bin/env python3
"""Parameterized reproduction harness for Lean 4.35.0 vs lean4lean vs leanexport + nanoda_bin."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

GMP_HEADER = """namespace VrustcHonestGmpBench

structure RegFact where
  np : Bool
  lo : Nat
  hi : Nat
  deriving DecidableEq

structure RegFile where
  r0 : RegFact
  r1 : RegFact
  r2 : RegFact
  r3 : RegFact
  r4 : RegFact
  r5 : RegFact
  r6 : RegFact
  r7 : RegFact

def topFact : RegFact := { np := false, lo := 0, hi := 18446744073709551615 }

def initFile : RegFile :=
  { r0 := topFact, r1 := topFact, r2 := topFact, r3 := topFact,
    r4 := topFact, r5 := topFact, r6 := topFact, r7 := topFact }

def getR (f : RegFile) : Nat → RegFact
  | 0 => f.r0 | 1 => f.r1 | 2 => f.r2 | 3 => f.r3
  | 4 => f.r4 | 5 => f.r5 | 6 => f.r6 | _ => f.r7

def setR (f : RegFile) (r : Nat) (v : RegFact) : RegFile :=
  match f with
  | ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ =>
    match r with
    | 0 => ⟨v, r1, r2, r3, r4, r5, r6, r7⟩
    | 1 => ⟨r0, v, r2, r3, r4, r5, r6, r7⟩
    | 2 => ⟨r0, r1, v, r3, r4, r5, r6, r7⟩
    | 3 => ⟨r0, r1, r2, v, r4, r5, r6, r7⟩
    | 4 => ⟨r0, r1, r2, r3, v, r5, r6, r7⟩
    | 5 => ⟨r0, r1, r2, r3, r4, v, r6, r7⟩
    | 6 => ⟨r0, r1, r2, r3, r4, r5, v, r7⟩
    | _ => ⟨r0, r1, r2, r3, r4, r5, r6, v⟩

def MAX64 : Nat := 18446744073709551615

def stepOne (f : RegFile) (word : Nat) : Option RegFile :=
  let op   := word % 8
  let dst  := (word / 8) % 8
  let srcA := (word / 64) % 8
  let srcB := (word / 512) % 8
  let imm  := word / 4096
  match op with
  | 0 => some (setR f dst { np := true, lo := imm, hi := imm })
  | 1 =>
    let fa := getR f srcA
    let fb := getR f srcB
    if fa.np && fb.np && (fa.hi + fb.hi <= MAX64) then
      some (setR f dst { np := true, lo := fa.lo + fb.lo, hi := fa.hi + fb.hi })
    else none
  | 2 =>
    let fa := getR f srcA
    let fb := getR f srcB
    if fa.np && fb.np && (fb.hi <= fa.lo) then
      some (setR f dst { np := true, lo := fa.lo - fb.hi, hi := fa.hi - fb.lo })
    else none
  | 3 =>
    let fa := getR f srcA
    if fa.np then some (setR f dst { np := true, lo := 0, hi := if fa.hi < imm then fa.hi else imm })
    else none
  | 4 =>
    let fi := getR f srcA
    let fl := getR f srcB
    if fi.np && fl.np && (fi.hi < fl.lo) then some f else none
  | 5 =>
    let fa := getR f srcA
    some (setR f dst { np := true, lo := if fa.np then fa.lo else 0, hi := if fa.np then fa.hi else MAX64 })
  | _ => none

inductive ChunkTree where
  | leaf (count : Nat) (packed : Nat)
  | node (l r : ChunkTree)

def checkChunk : Nat → RegFile → Nat → Option RegFile
  | 0, f, _ => some f
  | n + 1, f, packed =>
    let word := packed % 4294967296
    let rest := packed / 4294967296
    match stepOne f word with
    | some f' => checkChunk n f' rest
    | none => none

def checkTree (f : RegFile) : ChunkTree → Option RegFile
  | .leaf cnt packed => checkChunk cnt f packed
  | .node l r =>
    match checkTree f l with
    | some f' => checkTree f' r
    | none => none
"""


def pack_word(op: int, dst: int, src_a: int, src_b: int, imm: int) -> int:
    return (op & 7) | ((dst & 7) << 3) | ((src_a & 7) << 6) | ((src_b & 7) << 9) | (imm << 12)


def build_words(n: int) -> list[int]:
    words = [pack_word(0, 0, 0, 0, 1024), pack_word(0, 1, 0, 0, 10), pack_word(0, 2, 0, 0, 1)]
    while len(words) < n:
        r = len(words) % 5
        if r == 0:
            words.append(pack_word(0, 1, 0, 0, (len(words) % 32) + 1))
        elif r == 1:
            words.append(pack_word(1, 3, 1, 2, 0))
        elif r == 2:
            words.append(pack_word(3, 4, 3, 0, 255))
        elif r == 3:
            words.append(pack_word(4, 0, 4, 0, 0))
        else:
            words.append(pack_word(5, 5, 4, 0, 0))
    return words[:n]


def build_tree_expr(words: list[int], leaf_sz: int = 16) -> str:
    if len(words) <= leaf_sz:
        packed = 0
        for idx, w in enumerate(words):
            packed |= (w << (32 * idx))
        return f"(ChunkTree.leaf {len(words)} {packed})"
    mid = len(words) // 2
    return f"(ChunkTree.node {build_tree_expr(words[:mid], leaf_sz)} {build_tree_expr(words[mid:], leaf_sz)})"


def run_timed(cmd: list[str], env: dict[str, str], cwd: Path, timeout: int = 300) -> dict:
    t0 = time.monotonic()
    p = subprocess.run(["/usr/bin/time", "-v", *cmd], env=env, capture_output=True, text=True, timeout=timeout, cwd=str(cwd))
    dt = round(time.monotonic() - t0, 4)
    rss_kb = int(m.group(1)) if (m := re.search(r"Maximum resident set size \(kbytes\):\s+(\d+)", p.stderr)) else 0
    return {"rc": p.returncode, "wall_sec": dt, "rss_mb": round(rss_kb / 1024.0, 2), "stdout": p.stdout[-400:]}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--toolchain-dir", required=True)
    ap.add_argument("--f1-proof", default="")
    ap.add_argument("--out-json", required=True)
    args = ap.parse_args()

    tc = Path(args.toolchain_dir)
    tc_bin, tc_lib = tc / "bin", tc / "lib/lean"
    with tempfile.TemporaryDirectory(prefix="lean_ext_check_") as td:
        work = Path(td)
        env = os.environ.copy()
        env["LEAN_PATH"] = f"{work}:{tc_lib}"
        env["PATH"] = f"{tc_bin}:{env.get('PATH', '')}"

        out = {"lean_version": subprocess.check_output([str(tc_bin / "lean"), "--version"], text=True).strip(), "scales": {}}
        for n in (100, 500, 1000, 4000):
            mod = f"HonestGmp_{n}"
            src = work / f"{mod}.lean"
            src.write_text(
                GMP_HEADER + f"\ndef tree_{n} : ChunkTree := {build_tree_expr(build_words(n))}\n"
                f"theorem cert_valid_gmp_{n} : (checkTree initFile tree_{n}).isSome = true := rfl\n"
                "end VrustcHonestGmpBench\n",
                encoding="utf-8",
            )
            olean, exp, cfg = work / f"{mod}.olean", work / f"{mod}.ndjson", work / f"{mod}.json"
            k = run_timed([str(tc_bin / "lean"), "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-o", str(olean), str(src)], env, work)
            with open(exp, "wb") as ef:
                t0 = time.monotonic()
                ep = subprocess.run([str(tc_bin / "leanexport"), mod, "--", f"VrustcHonestGmpBench.cert_valid_gmp_{n}"], env=env, stdout=ef, stderr=subprocess.PIPE, cwd=str(work))
                exp_s = round(time.monotonic() - t0, 4)
            cfg.write_text(json.dumps({
                "export_file_path": str(exp), "use_stdin": False, "permitted_axioms": [],
                "unpermitted_axiom_hard_error": False, "nat_extension": True, "string_extension": True,
                "print_success_message": True,
            }), encoding="utf-8")
            nan = run_timed([str(tc_bin / "nanoda_bin"), str(cfg)], env, work)
            out["scales"][str(n)] = {"lean_kernel": k, "leanexport_sec": exp_s, "export_bytes": exp.stat().st_size, "nanoda_bin": nan}
        Path(args.out_json).write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
