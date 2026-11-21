#!/usr/bin/env python3
"""Does a Lean 4 binary refuse a `.olean` written by a different Lean build?

Usage:
    python3 olean_header_githash_probe.py --lean <path to bin/lean> [--wrap "<command prefix>"]

The probe compiles a one-line module `A` to `A.olean`, imports it from a second
file, and then repeats the import after editing one field of the `.olean`
header in place:

  * one character of the 40-byte build githash (header bytes 40..79);
  * separately, the Lean version string (header bytes 7..39), githash intact.

Header layout, from `struct olean_header` in `src/library/module.cpp` of
leanprover/lean4 (revision 5045d0056413266e57c625dcd7c365b10e377c52, lines
107-144): 5-byte marker `olean`, 1-byte version, 1-byte flags, 33-byte Lean
version string, 40-byte githash, then the base address. The reader's check is
at lines 490-495 of the same file; the githash comparison there is compiled
only under `LEAN_CHECK_OLEAN_VERSION`, a CMake option that defaults to OFF
(`src/CMakeLists.txt:118`), so whether a given binary enforces it has to be
observed.

`--wrap` optionally prefixes every `lean` invocation (for example with a
resource-limiting launcher); it is not recorded. Everything reported is
observed on the given binary; nothing is hardcoded.
"""

import argparse
import json
import os
import shlex
import subprocess
import sys
import tempfile


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean", required=True)
    ap.add_argument("--wrap", default="")
    args = ap.parse_args()
    lean = os.path.realpath(args.lean)
    wrap = shlex.split(args.wrap)

    def run(argv, cwd, env=None):
        r = subprocess.run(wrap + [lean] + argv, cwd=cwd, env=env, capture_output=True, text=True)
        text = (r.stdout + r.stderr).strip().splitlines()
        return {"exit_code": r.returncode, "first_output_line": text[0] if text else ""}

    out = {"lean_version": subprocess.run([lean, "--version"], capture_output=True, text=True).stdout.strip()}
    with tempfile.TemporaryDirectory() as d:
        open(os.path.join(d, "A.lean"), "w").write("def answer : Nat := 42\n")
        open(os.path.join(d, "B.lean"), "w").write("import A\n#eval answer\n")
        env = dict(os.environ, LEAN_PATH=".")
        out["compile_A"] = run(["-o", "A.olean", "A.lean"], d)
        olean = os.path.join(d, "A.olean")
        original = open(olean, "rb").read()
        out["header"] = {
            "marker": original[0:5].decode("ascii", "replace"),
            "version": original[5],
            "flags": original[6],
            "lean_version": original[7:40].rstrip(b"\0").decode("ascii", "replace"),
            "githash": original[40:80].rstrip(b"\0").decode("ascii", "replace"),
        }
        out["import_unmodified"] = run(["B.lean"], d, env)

        patched = bytearray(original)
        patched[40] = ord("0") if patched[40] != ord("0") else ord("1")
        open(olean, "wb").write(patched)
        out["import_githash_one_character_changed"] = dict(
            run(["B.lean"], d, env), githash_in_file=bytes(patched[40:80]).decode("ascii", "replace")
        )

        patched = bytearray(original)
        patched[7:12] = b"9.99."
        open(olean, "wb").write(patched)
        out["import_version_string_changed"] = dict(
            run(["B.lean"], d, env),
            lean_version_in_file=bytes(patched[7:40]).rstrip(b"\0").decode("ascii", "replace"),
        )

        open(olean, "wb").write(original)
        out["import_restored"] = run(["B.lean"], d, env)

    out["githash_mismatch_rejected"] = out["import_githash_one_character_changed"]["exit_code"] != 0
    out["version_string_mismatch_rejected"] = out["import_version_string_changed"]["exit_code"] != 0
    json.dump(out, sys.stdout, indent=2, sort_keys=True)
    print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
