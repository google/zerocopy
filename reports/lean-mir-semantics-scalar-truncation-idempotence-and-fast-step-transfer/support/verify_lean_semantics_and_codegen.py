#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Verification driver for Package 3 (`lean-mir-semantics-scalar-truncation-idempotence-and-fast-step-transfer`).

Verifies:
1. `ScalarMirFastStepProbe.lean` under `leanprover/lean4:v4.34.1` (`exit 0`,
   zero output, all `#guard_msgs` WHNF timeouts, mismatches, and axiom receipts).
2. `LeanCodegenAndWfProbe.lean` under BOTH `leanprover/lean4:v4.34.1` and
   `v4.35.0-rc2`:
   - `LCNF.elimDeadVars` (`benchDeadLet`), `LCNF.cse` (`pureChecksum4x`);
   - `LCNF.floatLetIn` sinking `l_pureChecksum` past `t1` in `v4.34.1` while
     retaining `[t0, l_pureChecksum, t1]` order in `v4.35.0-rc2`;
   - `@[noinline] ... IO` barrier (`doChecksumBarrier`) preserving `[t0, bar, t1]`;
   - Perceus `@&` self-alias `lean_inc_ref` emission vs. single-owned FFI;
   - `leanc -nostdinc` freestanding header isolation, `-O0` `optnone` vs.
     `-O2 -DNDEBUG` LTO attributes, and `ld.lld` `-plugin-opt=O3`;
   - Deterministic `whnf` timeout on inlined `WF.Fix` bit-shifted match
     scrutinees (`w >>> 16`) vs. millisecond `Subtype` + `@[inline]` cure;
   - Compiled binary timing assertions for both `v4.34.1` and `v4.35.0-rc2`.
"""

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent


def lean_wrap(cmd: list[str]) -> list[str]:
    if shutil.which("anneal-lean-run"):
        return ["anneal-lean-run", "--mode", "file", "--concurrency", "1", "--", *cmd]
    return cmd


def run_cmd(cmd: list[str], check: bool = True, env=None) -> subprocess.CompletedProcess:
    merged = os.environ.copy()
    home = str(Path.home())
    merged["PATH"] = f"{home}/.elan/bin:{home}/.local/bin:" + merged.get("PATH", "")
    if env:
        merged.update(env)
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, env=merged)
    if check and p.returncode != 0:
        raise RuntimeError(f"Command failed ({p.returncode}): {' '.join(cmd)}\n{p.stdout}")
    return p


def extract_c_func(c_src: str, func_name: str) -> str:
    m = re.search(rf"LEAN_EXPORT [^\n]*\b{re.escape(func_name)}\([^\n]*\{{\n_start:\n\{{(.*?)\n\}}\n\}}", c_src, re.S)
    if not m:
        raise AssertionError(f"Missing C function {func_name}")
    return m.group(1)


def main() -> int:
    # 1. ScalarMirFastStepProbe.lean on v4.34.1
    t0 = time.monotonic()
    scalar_res = run_cmd(lean_wrap(["elan", "run", "leanprover/lean4:v4.34.1", "lean", str(HERE / "ScalarMirFastStepProbe.lean")]))
    scalar_s = round(time.monotonic() - t0, 3)
    assert scalar_res.stdout.strip() == "", f"Unexpected output:\n{scalar_res.stdout}"

    summary = {"status": "PASS", "scalar_probe_sec": scalar_s, "toolchains": {}}

    with tempfile.TemporaryDirectory(prefix="pkg3_lean_codegen_") as td:
        tmp = Path(td)
        probe_src = (HERE / "LeanCodegenAndWfProbe.lean").read_text()
        (tmp / "LeanCodegenAndWfProbe.lean").write_text(probe_src)
        shutil.copy2(HERE / "copy_within_ffi.c", tmp / "copy_within_ffi.c")

        for tc in ("leanprover/lean4:v4.34.1", "leanprover/lean4:v4.35.0-rc2"):
            tag = tc.split(":")[1]
            c_out = tmp / f"probe_{tag}.c"
            olean_out = tmp / "LeanCodegenAndWfProbe.olean"
            t1 = time.monotonic()
            comp = run_cmd(lean_wrap([
                "elan", "run", tc, "lean", f"--root={tmp}", f"--c={c_out}", f"--o={olean_out}", str(tmp / "LeanCodegenAndWfProbe.lean")
            ]))
            assert "warning:" not in comp.stdout and "error:" not in comp.stdout, comp.stdout
            elab_ms = round((time.monotonic() - t1) * 1000.0, 1)

            c_txt = c_out.read_text()
            dead_loop = extract_c_func(
                c_txt,
                "l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00benchDeadLet_spec__0___redArg",
            )
            assert "l_pureChecksum(" not in dead_loop and dead_loop.count("lean_io_mono_nanos_now()") == 2
            cse_fn = extract_c_func(c_txt, "l_pureChecksum4x")
            assert cse_fn.count("l_pureChecksum(") == 1

            sunk_fn = extract_c_func(
                c_txt,
                "l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00benchPureLetSunk_spec__0___redArg",
            )
            p_t0 = sunk_fn.find("lean_io_mono_nanos_now()")
            p_t1 = sunk_fn.find("lean_io_mono_nanos_now()", p_t0 + 1)
            p_cs = sunk_fn.find("l_pureChecksum(")
            if "4.34" in tag:
                assert 0 <= p_t0 < p_t1 < p_cs, "Expected floatLetIn clock sinking in v4.34.1"
                float_mode = "sunk_past_t1"
            else:
                assert 0 <= p_t0 < p_cs < p_t1, "Expected pureChecksum inside [t0, t1] in v4.35.0-rc2"
                float_mode = "ordered_inside_t0_t1"

            bar_fn = extract_c_func(
                c_txt,
                "l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00benchNoinlineIOBarrier_spec__0___redArg",
            )
            b0 = bar_fn.find("lean_io_mono_nanos_now()")
            bc = bar_fn.find("l_doChecksumBarrier(")
            b1 = bar_fn.find("lean_io_mono_nanos_now()", b0 + 1)
            assert 0 <= b0 < bc < b1

            step_al = extract_c_func(c_txt, "l_stepAliased")
            step_ow = extract_c_func(c_txt, "l_stepOwned")
            assert "lean_inc_ref(" in step_al and "lean_byte_array_copy_slice(" in step_al
            assert "lean_inc_ref(" not in step_ow and "probe_byte_array_copy_within(" in step_ow

            ffi_o = tmp / f"ffi_{tag}.o"
            bin_p = tmp / f"bin_{tag}"
            run_cmd(lean_wrap(["elan", "run", tc, "leanc", "-O2", "-DNDEBUG", "-c", str(tmp / "copy_within_ffi.c"), "-o", str(ffi_o)]))
            run_cmd(lean_wrap(["elan", "run", tc, "leanc", "-O3", "-DNDEBUG", str(c_out), str(ffi_o), "-o", str(bin_p)]))
            run_p = run_cmd([str(bin_p)])
            m1 = re.search(r"dead_ns=(\d+).*pure_sunk_ns=(\d+).*inline_io_sunk_ns=(\d+).*barrier_ns=(\d+)", run_p.stdout)
            m2 = re.search(r"steps=4000: sz=256064/256064 aliased_ns=(\d+) owned_ns=(\d+)", run_p.stdout)
            assert m1 and m2 and "eq=true (2830096295)" in run_p.stdout, run_p.stdout
            dead_ns, pure_ns, inline_ns, bar_ns = map(int, m1.groups())
            al_ns, ow_ns = map(int, m2.groups())
            assert al_ns > 20 * ow_ns
            if "4.34" in tag:
                assert bar_ns > 50 * pure_ns and bar_ns > 50 * inline_ns and bar_ns > 50 * dead_ns
            else:
                assert bar_ns > 50 * dead_ns and pure_ns > 50 * dead_ns and inline_ns > 50 * dead_ns

            summary["toolchains"][tag] = {
                "elab_ms": elab_ms,
                "floatLetIn_pureLet": float_mode,
                "dead_ns": dead_ns,
                "pure_let_ns": pure_ns,
                "inline_io_ns": inline_ns,
                "barrier_ns": bar_ns,
                "perceus_4000_speedup": round(al_ns / ow_ns, 1),
            }

        # Check -nostdinc, optnone, lld -plugin-opt=O3, and WF WHNF timeout on v4.34.1
        nostdinc_c = tmp / "nostdinc.c"
        nostdinc_c.write_text("#include <lean/lean.h>\n#include <string.h>\n")
        nr = run_cmd(lean_wrap(["elan", "run", "leanprover/lean4:v4.34.1", "leanc", "-c", str(nostdinc_c), "-o", str(tmp / "n.o")]), check=False)
        assert nr.returncode != 0 and "'string.h' file" in nr.stdout

        opt_c = tmp / "opt.c"
        opt_c.write_text("#include <lean/lean.h>\nLEAN_EXPORT uint32_t u32le(b_lean_obj_arg a, size_t i) { uint32_t v; __builtin_memcpy(&v, lean_sarray_cptr(a) + i, 4); return v; }\n")
        ll0, ll2 = tmp / "o0.ll", tmp / "o2.ll"
        run_cmd(lean_wrap(["elan", "run", "leanprover/lean4:v4.34.1", "leanc", "-S", "-emit-llvm", str(opt_c), "-o", str(ll0)]))
        run_cmd(lean_wrap(["elan", "run", "leanprover/lean4:v4.34.1", "leanc", "-O2", "-DNDEBUG", "-S", "-emit-llvm", str(opt_c), "-o", str(ll2)]))
        assert "optnone" in ll0.read_text() and "noinline" in ll0.read_text()
        assert "optnone" not in ll2.read_text() and "local_unnamed_addr" in ll2.read_text()
        lld_r = run_cmd(["elan", "run", "leanprover/lean4:v4.34.1", "leanc", "-###", "-flto", "-fno-semantic-interposition", "-O3", str(ll2), "-o", "/dev/null"], check=False)
        assert "-plugin-opt=O3" in lld_r.stdout

        # Re-elaborate v4.34.1 olean cleanly for WF import
        run_cmd(lean_wrap(["elan", "run", "leanprover/lean4:v4.34.1", "lean", f"--root={tmp}", f"--o={tmp / 'LeanCodegenAndWfProbe.olean'}", str(tmp / "LeanCodegenAndWfProbe.lean")]))
        slow_lean = tmp / "wf_slow.lean"
        slow_lean.write_text(
            "import LeanCodegenAndWfProbe\n"
            "set_option maxHeartbeats 15000 in\n"
            "def tokenFreqsP_Slow (tokens : Array UInt32) : Array Nat × Array Nat :=\n"
            "  go tokens ((Array.replicate 286 0).set! 256 1) (Array.replicate 30 0)\n"
            "    (by rw [Array.size_set!, Array.size_replicate]) (by rw [Array.size_replicate]) 0\n"
            "where\n"
            "  go (tokens : Array UInt32) (litLenFreqs distFreqs : Array Nat)\n"
            "      (hlit : litLenFreqs.size = 286) (hdist : distFreqs.size = 30) (i : Nat) : Array Nat × Array Nat :=\n"
            "    if h : i < tokens.size then\n"
            "      let w := tokens[i]\n"
            "      if w &&& ((1 : UInt32) <<< 31) = 0 then\n"
            "        let idx := w.toUInt8.toNat\n"
            "        have hidx : idx < litLenFreqs.size := by have := UInt8.toNat_lt w.toUInt8; omega\n"
            "        go tokens (litLenFreqs.set! idx (litLenFreqs[idx] + 1)) distFreqs\n"
            "          (by rw [Array.size_set!]; exact hlit) hdist (i + 1)\n"
            "      else\n"
            "        match hflc : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) with\n"
            "        | none => go tokens litLenFreqs distFreqs hlit hdist (i + 1)\n"
            "        | some (lIdx, _, _) =>\n"
            "          have hsym : lIdx + 257 < litLenFreqs.size := by have := findLengthCode_idx_lt hflc; omega\n"
            "          let litLenFreqs' := litLenFreqs.set! (lIdx + 257) (litLenFreqs[lIdx + 257] + 1)\n"
            "          have hlit' : litLenFreqs'.size = 286 := by show (litLenFreqs.set! _ _).size = 286; rw [Array.size_set!]; exact hlit\n"
            "          match hfdc : findDistCode ((w &&& 0xFFFF).toNat) with\n"
            "          | none => go tokens litLenFreqs' distFreqs hlit' hdist (i + 1)\n"
            "          | some (dIdx, _, _) =>\n"
            "            have hd : dIdx < distFreqs.size := by have := findDistCode_idx_lt hfdc; omega\n"
            "            go tokens litLenFreqs' (distFreqs.set! dIdx (distFreqs[dIdx] + 1)) hlit'\n"
            "              (by show (distFreqs.set! _ _).size = 30; rw [Array.size_set!]; exact hdist) (i + 1)\n"
            "    else (litLenFreqs, distFreqs)\n"
            "  termination_by tokens.size - i\n"
        )
        res_slow = run_cmd(lean_wrap(["elan", "run", "leanprover/lean4:v4.34.1", "lean", f"--root={tmp}", str(slow_lean)]), check=False, env={"LEAN_PATH": str(tmp)})
        assert res_slow.returncode != 0 and "(deterministic) timeout at `whnf`" in res_slow.stdout, res_slow.stdout
        summary["wf_slow_whnf_timeout"] = True
        summary["leanc_nostdinc_and_optnone_verified"] = True

    print(json.dumps(summary, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
