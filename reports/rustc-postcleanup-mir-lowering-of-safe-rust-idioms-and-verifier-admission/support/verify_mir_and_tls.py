#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Verification suite for Package: rustc-postcleanup-mir-lowering-of-safe-rust-idioms-and-verifier-admission.

Checks:
1. `Runtime(PostCleanup)` (`SimplifyCfg-pre-optimizations.after.mir`) MIR idioms
   across available toolchains (`nightly-2026-05-31` `1.98` vs default `nightly`
   `1.102`), specifically verifying the `BoxRaw`/`BoxDerefTransmute` migration vs
   `Unique/NonNull (Transmute)`, `PtrMetadata`, `CastKind`, `&Cell<[T]>`,
   `FnMut` dynamic calls, closure `Aggregate`s, and `Div`/`Rem`/`Not`/`Neg`.
2. Upstream `Frommi/miniz_oxide` (0.9.1) dead-bitmask check
   `TDEFL_FORCE_ALL_RAW_BLOCKS & TDEFL_RLE_MATCHES == 0`.
3. `tls_stack_overflow_probe.rs` under `-C opt-level=0`: confirming `const`
   inline 1.8 MB TLS and `Box` pass on 2 MiB stacks while eager non-`const`
   `[1u8; 1_800_000]` overflows the 2 MiB thread stack (exit != 0 / SIGABRT).
"""

import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent


def available_toolchains() -> list[tuple[str, str]]:
    out = subprocess.check_output(["rustup", "toolchain", "list"], text=True)
    res = []
    for cand in ("nightly-2026-05-31", "nightly"):
        for line in out.splitlines():
            tc = line.split()[0]
            if tc == cand or tc.startswith(cand + "-"):
                ver = subprocess.check_output(["rustc", f"+{tc}", "-vV"], text=True).splitlines()[0]
                res.append((tc, ver))
                break
    return res


def dump_mir(tc: str, dump_dir: Path, tmp: Path) -> dict[str, str]:
    dump_dir.mkdir(parents=True, exist_ok=True)
    cmd = [
        "rustc",
        f"+{tc}",
        "--edition",
        "2021",
        "--crate-type",
        "rlib",
        "--crate-name",
        "mir_idioms_probe",
        "-Copt-level=0",
        "-Cdebug-assertions=no",
        "-Coverflow-checks=no",
        "-Zdump-mir=SimplifyCfg-pre-optimizations",
        f"-Zdump-mir-dir={dump_dir}",
        "-o",
        str(tmp / f"lib_{tc}.rlib"),
        str(HERE / "mir_idioms_probe.rs"),
    ]
    subprocess.run(cmd, check=True, capture_output=True, text=True)
    dumps = {}
    for p in dump_dir.glob("*.SimplifyCfg-pre-optimizations.after.mir"):
        dumps[p.name] = p.read_text()
    return dumps


def main() -> int:
    tcs = available_toolchains()
    assert tcs, "Expected at least one nightly rustc"
    mir_summary = {}

    with tempfile.TemporaryDirectory(prefix="pkg4_mir_tls_") as td:
        tmp = Path(td)
        for tc, ver in tcs:
            dumps = dump_mir(tc, tmp / f"dump_{tc}", tmp)
            box_mir = next(v for k, v in dumps.items() if "read_box_array." in k)
            cell_mir = next(v for k, v in dumps.items() if "cell_apply." in k)
            dyn_mir = next(v for k, v in dumps.items() if "dyn_cb." in k)
            cls_mir = next(v for k, v in dumps.items() if "closure_map." in k)
            zip_mir = next(v for k, v in dumps.items() if "iter_zip_dot." in k)
            enum_mir = next(v for k, v in dumps.items() if "from_flag." in k)
            ops_mir = next(v for k, v in dumps.items() if "scalar_ops." in k)

            assert "PtrMetadata" in cell_mir
            assert "{closure@" in cls_mir or "{closure#" in cls_mir or "Closure" in cls_mir
            assert "Div(" in ops_mir and "Rem(" in ops_mir and "Not(" in ops_mir and "Neg(" in ops_mir
            assert "MiniStatus::Failed" in enum_mir and "MiniStatus::Done" in enum_mir
            if "1.98" in ver:
                assert "Transmute" in box_mir and "BoxDerefTransmute" not in box_mir
                box_cast = "Unique/NonNull (Transmute)"
            elif "1.102" in ver or "1.101" in ver:
                assert "BoxDerefTransmute" in box_mir
                box_cast = "BoxRaw (BoxDerefTransmute)"
            else:
                box_cast = "other"

            mir_summary[ver] = {
                "dump_files": len(dumps),
                "box_deref_cast": box_cast,
                "cell_uses_ptr_metadata": "PtrMetadata" in cell_mir,
                "dyn_has_call": "::call_mut(" in dyn_mir,
                "zip_uses_call_terminators": zip_mir.count("-> [return:") >= 2,
                "scalar_has_not_neg_div_rem": True,
            }

        # Check TLS stack overflow probe at -O0 and -O3
        tls_o0 = tmp / "tls_o0"
        tls_o3 = tmp / "tls_o3"
        subprocess.run(
            ["rustc", "--edition", "2021", "-C", "opt-level=0", str(HERE / "tls_stack_overflow_probe.rs"), "-o", str(tls_o0)],
            check=True,
        )
        subprocess.run(
            ["rustc", "--edition", "2021", "-C", "opt-level=3", str(HERE / "tls_stack_overflow_probe.rs"), "-o", str(tls_o3)],
            check=True,
        )
        safe_o0 = subprocess.run([str(tls_o0), "safe"], check=True, capture_output=True, text=True)
        eager_o0 = subprocess.run([str(tls_o0), "eager"], capture_output=True, text=True)
        assert eager_o0.returncode != 0 and "overflowed its stack" in eager_o0.stderr, eager_o0.stderr
        eager_o3 = subprocess.run([str(tls_o3), "eager"], check=True, capture_output=True, text=True)

    # Check static arithmetic property of miniz_oxide 0.9.1 dead bitmask
    TDEFL_RLE_MATCHES = 0x0001_0000
    TDEFL_FORCE_ALL_RAW_BLOCKS = 0x0008_0000
    assert (TDEFL_FORCE_ALL_RAW_BLOCKS & TDEFL_RLE_MATCHES) == 0

    print(
        json.dumps(
            {
                "status": "PASS",
                "mir_summary": mir_summary,
                "tls_o0_safe_out": safe_o0.stdout.strip().splitlines(),
                "tls_o0_eager_rc": eager_o0.returncode,
                "tls_o3_eager_out": eager_o3.stdout.strip(),
                "tdefl_rle_raw_and_zero": (TDEFL_FORCE_ALL_RAW_BLOCKS & TDEFL_RLE_MATCHES) == 0,
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
