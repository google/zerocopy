#!/usr/bin/env python3
"""Finite differential check. Requires existing Kraken build and AArch64 rustc/host.
No dependency install, network, upstream build, pointer access, or privileged asm.
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import time

MASK = (1 << 64) - 1
EDGES = [0, 1, 2, 255, 256, (1 << 31)-1, 1 << 31, (1 << 32)-1,
         1 << 32, (1 << 63)-1, 1 << 63, MASK-1, MASK,
         0x0123456789abcdef, 0x80ff007e11223344]
COUNTS = [0, 1, 7, 31, 32, 33, 63, 64, 65, 127, 128, MASK]

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def cases():
    rows = []
    for op in ["adds64", "adcs64", "add32"]:
        for a in EDGES:
            for b in EDGES:
                for c in ([0, 1] if op == "adcs64" else [0]):
                    rows.append((str(len(rows)), op, a, b, c))
    for op in ["lslv64", "lslv32"]:
        for a in EDGES:
            for b in COUNTS:
                rows.append((str(len(rows)), op, a, b, 0))
    for op in ["rev64", "rev32"]:
        for a in EDGES:
            rows.append((str(len(rows)), op, a, 0, 0))
    return rows

def oracle(row):
    _, op, a, b, carry = row
    if op in ("adds64", "adcs64"):
        cin = carry if op == "adcs64" else 0
        total = a + b + cin
        result = total & MASK
        signed = lambda n: n if n < 1 << 63 else n - (1 << 64)
        signed_total = signed(a) + signed(b) + cin
        overflow = not (-(1 << 63) <= signed_total < (1 << 63))
        nzcv = ((result >> 63) << 3) | ((result == 0) << 2) | ((total > MASK) << 1) | overflow
    elif op == "add32":
        result = (a + b) % (1 << 32)
        nzcv = 6
    elif op in ("lslv64", "lslv32"):
        width = 64 if op == "lslv64" else 32
        result = ((a % (1 << width)) << (b % width)) % (1 << width)
        nzcv = 6
    elif op in ("rev64", "rev32"):
        size = 8 if op == "rev64" else 4
        result = int.from_bytes((a % (1 << (8*size))).to_bytes(size, "little"), "big")
        nzcv = 6
    else:
        raise ValueError(op)
    return (result, nzcv)

def decode(text):
    out = {}
    for line in text.splitlines():
        fields = line.split("\t")
        if len(fields) != 3 or fields[0] in out:
            raise ValueError("malformed or duplicate result: " + line)
        out[fields[0]] = tuple(map(int, fields[1:]))
    return out

def compare(rows, observed, expected, route):
    if set(observed) != set(expected):
        raise RuntimeError(route + " produced a different set of case IDs")
    for row in rows:
        if observed[row[0]] != expected[row[0]]:
            raise RuntimeError(json.dumps({"REAL_DISAGREEMENT": route, "case": row,
                "observed": observed[row[0]], "oracle": expected[row[0]]}))

def negative_controls(rows, expected):
    witnesses = {}
    def keep(name, row, mutant):
        right = expected[row[0]]
        if mutant != right and name not in witnesses:
            witnesses[name] = {"case": row, "correct": right, "mutant": mutant}
    for row in rows:
        _, op, a, b, c = row
        result, flags = expected[row[0]]
        if op == "adcs64" and c == 1:
            keep("ignore_input_carry", row, oracle((row[0], "adds64", a, b, 0)))
        if op == "adds64":
            keep("clear_output_carry", row, (result, flags & ~2))
            keep("clear_signed_overflow", row, (result, flags & ~1))
        if op in ("add32", "lslv32", "rev32"):
            keep("preserve_old_destination_upper32", row, (result | 0xffffffff00000000, flags))
        if op.startswith("lslv"):
            width = 64 if op == "lslv64" else 32
            if b >= width:
                # A conventional unmasked fixed-width shift returns zero once count >= width.
                keep("unmasked_shift_"+str(width), row, (0, flags))
        if op.startswith("rev"):
            width = 64 if op == "rev64" else 32
            bit_reverse = int(format(a % (1 << width), "0"+str(width)+"b")[::-1], 2)
            keep("reverse_bits_instead_of_bytes_"+str(width), row, (bit_reverse, flags))
    required = {"ignore_input_carry", "clear_output_carry", "clear_signed_overflow",
        "preserve_old_destination_upper32", "unmasked_shift_64", "unmasked_shift_32",
        "reverse_bits_instead_of_bytes_64", "reverse_bits_instead_of_bytes_32"}
    if set(witnesses) != required:
        raise RuntimeError("negative control coverage incomplete")
    return witnesses

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lean", required=True)
    ap.add_argument("--kraken-lib", required=True)
    ap.add_argument("--rustc", default="rustc")
    ap.add_argument("--artifact-dir", required=True, help="owned scratch for unshipped native executables/assembly")
    args = ap.parse_args()
    root = Path(__file__).resolve().parent
    os.chdir(root)
    artifacts = Path(args.artifact_dir).resolve()
    artifacts.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=str(Path(args.kraken_lib).resolve()))
    records = []
    results = {"status": "running", "observation_date": "2026-10-14", "commands": records}
    def run(argv, labels, log, use_lean=False):
        start = time.monotonic()
        p = subprocess.run(argv, text=True, capture_output=True, env=env if use_lean else None)
        (root/log).write_text(p.stdout + p.stderr)
        rec = {"argv": labels, "cwd": ".", "exit": p.returncode,
            "elapsed_seconds": time.monotonic()-start, "log": log,
            "log_sha256": digest(root/log)}
        if use_lean: rec["LEAN_PATH"] = "<pinned Kraken build library>"
        records.append(rec)
        if p.returncode != 0 or re.search(r"\bpanic(?:ked)?\b|assertion failed", p.stdout+p.stderr, re.I):
            raise RuntimeError("stop and diagnose failed command: " + " ".join(labels))
        return p.stdout
    try:
        if platform.machine() != "arm64":
            raise RuntimeError("native corpus requires arm64 host")
        lean_identity = run([args.lean, "--version"], ["lean", "--version"], "lean-version.log")
        rustc_identity = run([args.rustc, "--version", "--verbose"], ["rustc", "--version", "--verbose"], "rustc-version.log")
        run([args.lean, "--run", "InstructionEval.lean", "--describe"],
            ["lean", "--run", "InstructionEval.lean", "--describe"], "parsed-programs.log", True)
        rows = cases()
        (root/"cases.tsv").write_text("".join("\t".join(map(str, row))+"\n" for row in rows))
        expected = {r[0]: oracle(r) for r in rows}
        (root/"oracle.tsv").write_text("".join(f"{r[0]}\t{expected[r[0]][0]}\t{expected[r[0]][1]}\n" for r in rows))
        observed = decode(run([args.lean, "--run", "InstructionEval.lean", "cases.tsv"],
            ["lean", "--run", "InstructionEval.lean", "cases.tsv"], "kraken.tsv", True))
        compare(rows, observed, expected, "Kraken")
        results["kraken_compared_before_native"] = True
        builds = []
        for opt in (0, 3):
            binary = artifacts/f"native-O{opt}"
            assembly = artifacts/f"native-O{opt}.s"
            label_emit = f"asm=<artifact-dir>/native-O{opt}.s,link=<artifact-dir>/native-O{opt}"
            run([args.rustc, "--edition=2024", "-C", f"opt-level={opt}", "--emit", f"asm={assembly},link={binary}", "native.rs"],
                ["rustc", "--edition=2024", "-C", f"opt-level={opt}", "--emit", label_emit, "native.rs"], f"native-O{opt}-build.log")
            # Inspect emitted asm block contents before executing this fresh binary.
            source = assembly.read_text()
            blocks = re.findall(r"; InlineAsm Start\n(.*?); InlineAsm End", source, re.S)
            blocks = [block for block in blocks if re.search(r"\bmrs\b.*\bNZCV\b", block)]
            if len(blocks) != 7:
                raise RuntimeError("unexpected native asm-block count")
            (root/f"native-O{opt}-asm-blocks.s").write_text("\n".join(blocks))
            native = decode(run([str(binary), "cases.tsv"], [f"<artifact-dir>/native-O{opt}", "cases.tsv"], f"native-O{opt}.tsv"))
            compare(rows, native, expected, f"native O{opt}")
            builds.append({"opt_level": opt, "binary_sha256": digest(binary),
                "assembly_sha256": digest(assembly), "asm_blocks": len(blocks),
                "case_count": len(rows), "all_equal_oracle_and_kraken": True})
        witnesses = negative_controls(rows, expected)
        (root/"negative-controls.json").write_text(json.dumps(witnesses, indent=2)+"\n")
        nzcv = defaultdict(set)
        for row in rows: nzcv[row[1]].add(expected[row[0]][1])
        results.update(status="passed", case_count=len(rows), per_op=dict(Counter(r[1] for r in rows)),
            nzcv_values={k: sorted(v) for k,v in nzcv.items()},
            native_builds=builds, negative_control_count=len(witnesses),
            input_edges=EDGES, shift_counts=COUNTS,
            cases_sha256=digest(root/"cases.tsv"), oracle_sha256=digest(root/"oracle.tsv"),
            frame_check="Kraken equality to initial full data with only X0/status replacements; PC4/one exec[0,4)",
            environment={"host":platform.machine(), "platform":platform.platform(),
                "lean":lean_identity.strip(), "rustc":rustc_identity.strip()},
            owned_sources={n:digest(root/n) for n in ("InstructionEval.lean","native.rs","validate.py")})
    except Exception as exc:
        results.update(status="STOPPED_FOR_DIAGNOSIS", error=str(exc))
        (root/"results.json").write_text(json.dumps(results,indent=2)+"\n")
        print(str(exc), file=sys.stderr)
        return 1
    (root/"results.json").write_text(json.dumps(results,indent=2)+"\n")
    print(json.dumps({"status":results["status"], "cases_per_route":len(rows), "native_opts":[0,3], "negative_controls":len(witnesses)}))
    return 0

if __name__ == "__main__":
    sys.exit(main())
