#!/usr/bin/env python3
"""Record what a nightly rustc (and Miri) does with `pin_ergonomics` / `#[pin_v2]` programs.

The probe programs live next to this script in `probes/`. The script copies them to a
temporary directory, compiles each one, runs the runnable ones natively and under Miri
(Stacked Borrows and Tree Borrows), and writes a JSON record of the observed outcomes.
It asserts nothing by itself; `--check GOLDEN` compares the outcome with a stored record.

    python3 probe_pin_ergonomics_pin_v2_and_ice.py --out observed.json
    python3 probe_pin_ergonomics_pin_v2_and_ice.py --check results/<golden>.json

Options:
    --rustc PATH         compiler to probe (default: `rustc` found on PATH)
    --miri PATH          Miri driver (default: `miri` next to the real rustc binary)
    --miri-sysroot DIR   Miri sysroot (default: $MIRI_SYSROOT, else ~/.cache/miri)
    --skip-miri          do not run Miri
    --out FILE           write the full JSON record to FILE
    --check FILE         compare the stable part of the record with FILE; exit 1 on difference

Only the Python standard library is used. Every probe is `#![forbid(unsafe_code)]`.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

SCHEMA = "pin-ergonomics-probe/1"
EDITION = "2024"
TIMEOUT_SEC = 180

# name -> one-line statement of what the probe discriminates.
COMPILE_PROBES = {
    "b01_explicit_pattern_on_non_pin_v2_struct": "explicit `&pin mut` projection through a struct that is not `#[pin_v2]`",
    "b02_implicit_pattern_on_non_pin_v2_struct": "match-ergonomics projection through a struct that is not `#[pin_v2]`",
    "b03_ref_mut_binding_of_non_unpin_field": "`ref mut` binding of a `!Unpin` field below `&pin mut`",
    "b04_ref_mut_binding_of_unpin_field_ok": "control: `ref mut` binding of an `Unpin` field below `&pin mut`",
    "b05_pin_v2_with_drop_only": "`#[pin_v2]` type implementing `Drop::drop(&mut self)`",
    "b06_pin_v2_with_pin_drop_only": "control: `#[pin_v2]` type implementing only `Drop::pin_drop`",
    "b07_pin_v2_with_both_drop_and_pin_drop": "`#[pin_v2]` type implementing both `drop` and `pin_drop`",
    "b08_non_pin_v2_with_both_drop_and_pin_drop": "unmarked type implementing both `drop` and `pin_drop`",
    "b09_non_pin_v2_with_pin_drop_only": "control: unmarked type implementing only `pin_drop`",
    "b10_pin_v2_repr_packed": "`#[pin_v2]` on `#[repr(packed)]`",
    "b11_pin_v2_repr_packed_2": "`#[pin_v2]` on `#[repr(C, packed(2))]`",
    "b12_manual_unpin_impl_on_pin_v2": "explicit `Unpin` impl for a `#[pin_v2]` type",
    "b13_explicit_pin_drop_call": "explicit call of `Drop::pin_drop`",
    "b14_reference_to_underaligned_packed_field": "control (no feature gate): reference to an under-aligned packed field",
    "b15_pin_v2_without_feature_gate": "control: `#[pin_v2]` and `&pin mut` without the feature gate",
    "c01_fn_item_explicit_pin_mut_pattern": "control: explicit `&pin mut` pattern in a fn body",
    "c02_closure_explicit_pin_mut_pattern": "explicit `&pin mut` pattern in a closure body",
    "c03_closure_explicit_pin_const_pattern": "explicit `&pin const` pattern in a closure body",
    "c04_closure_implicit_pattern": "control: match-ergonomics projection in a closure body",
    "c05_fn_item_pinned_reborrow": "control: implicit pinned reborrow in a fn body",
    "c06_closure_pinned_reborrow": "implicit pinned reborrow in a closure body",
    "c07_closure_pin_method_call": "`Pin<&mut Self>` method call in a closure body",
    "c08_async_fn_await": "`.await` in an `async fn`",
    "c09_async_fn_explicit_pin_mut_pattern": "explicit `&pin mut` pattern in an `async fn` body",
    "c10_closure_upvar_explicit_pin_mut_pattern": "explicit `&pin mut` pattern on a captured variable",
    "c11_closure_upvar_pinned_reborrow": "implicit pinned reborrow of a captured variable",
    "c12_closure_explicit_pattern_plus_type_error": "c02 plus an unrelated type error",
    "c13_closure_pin_method_call_without_feature": "control: c07 without the feature gate",
    "c14_fn_param_pin_patterns": "`&pin` patterns in fn parameters",
    "c15_closure_upvar_poll_fn": "captured `Pin<&mut T>` polled in a `poll_fn` closure",
    "c16_fn_item_overlapping_pinned_reborrows": "two overlapping pinned reborrows in a fn body",
    "e01_pin_borrow_expression_then_use": "`&pin mut place` borrow expression, then a use of the place",
}
# Compiled with lints enabled (no `--cap-lints allow`); warnings are recorded.
LINT_PROBES = {
    "d01_pin_mut_self_unused_mut_lint": "`unused_mut` warning on the `&pin mut self` receiver sugar",
}
RUN_PROBES = {
    "a1_structural_projection_reborrow_drop": "type identity, structural projection, pinned reborrow, `pin_drop`",
    "a2_packed_pinned_field_moved_on_drop": "pinned field of a `#[pin_v2] #[repr(packed)]` struct at drop",
    "a3_plain_packed_drop_moves_field": "packed drop glue moves an under-aligned field (no structural pinning)",
}
A4_MAIN = "a4_unmarked_projection_uaf"
A4_HELPER = "a4_selfref_future"
A5 = "a5_drop_glue_forwarding"

# Fields compared by --check. `native_stdout` of a4 is excluded: when the program is accepted
# it reads freed memory natively, so the printed value is not reproducible.
STABLE_KEYS = (
    "verdict",
    "rc",
    "first_error",
    "delayed_at",
    "warnings",
    "native_rc",
    "native_stdout",
    "miri_sb_verdict",
    "miri_sb_stdout",
    "miri_sb_first_error",
    "miri_tb_verdict",
    "miri_tb_stdout",
    "miri_tb_first_error",
    "glue_calls_trait_drop",
    "trait_drop_calls_pin_drop",
)
UNSTABLE_NATIVE_STDOUT = {A4_MAIN}

ERROR_LINE = re.compile(r"^error(\[E\d+\])?:.*$", re.MULTILINE)
WARNING_LINE = re.compile(r"^warning:.*$", re.MULTILINE)
DELAYED_AT = re.compile(r"delayed at (\S+)")


class Runner:
    def __init__(self, rustc: str, miri: str | None, miri_sysroot: str | None, work: Path):
        self.rustc = rustc
        self.miri = miri
        self.miri_sysroot = miri_sysroot
        self.work = work
        self.env = dict(os.environ)
        self.env["RUSTC_ICE"] = "0"  # do not write rustc-ice-*.txt dump files
        self.env["LC_ALL"] = "C"
        self.env["RUST_BACKTRACE"] = "0"  # keep ICE output free of process-specific backtraces
        self.env.pop("RUSTFLAGS", None)
        self.env.pop("MIRIFLAGS", None)

    def sanitize(self, text: str) -> str:
        text = text.replace(str(self.work), "<TMP>")
        home = os.path.expanduser("~")
        if home and home != "/":
            text = text.replace(home, "<HOME>")
        return text.replace("\r\n", "\n")

    def run(self, cmd: list[str], extra_env: dict[str, str] | None = None):
        env = dict(self.env)
        if extra_env:
            env.update(extra_env)
        try:
            proc = subprocess.run(
                cmd,
                cwd=self.work,
                env=env,
                stdin=subprocess.DEVNULL,
                capture_output=True,
                timeout=TIMEOUT_SEC,
            )
        except subprocess.TimeoutExpired:
            return 124, "", f"<timeout after {TIMEOUT_SEC}s>"
        out = self.sanitize(proc.stdout.decode("utf-8", "replace"))
        err = self.sanitize(proc.stderr.decode("utf-8", "replace"))
        return proc.returncode, out, err

    # -- rustc -----------------------------------------------------------------------------

    def rustc_cmd(self, *args: str, cap_lints: bool = True) -> list[str]:
        cmd = [self.rustc, "--edition", EDITION]
        if cap_lints:
            cmd += ["--cap-lints", "allow"]
        return cmd + list(args)

    @staticmethod
    def classify(rc: int, stderr: str) -> str:
        if rc == 0:
            return "accepted"
        if rc == 101 or "internal compiler error" in stderr:
            return "ice"
        return "rejected"

    def compile_record(self, rc: int, stderr: str) -> dict:
        first = ERROR_LINE.search(stderr)
        delayed = DELAYED_AT.search(stderr)
        return {
            "verdict": self.classify(rc, stderr),
            "rc": rc,
            "first_error": first.group(0) if first else None,
            "delayed_at": delayed.group(1) if delayed else None,
            "stderr": stderr[:6000],
        }

    def compile_only(self, name: str, cap_lints: bool = True) -> dict:
        rc, _, err = self.run(
            self.rustc_cmd(f"{name}.rs", "--emit=metadata", "-o", f"{name}.rmeta", cap_lints=cap_lints)
        )
        rec = self.compile_record(rc, err)
        if not cap_lints:
            rec["warnings"] = WARNING_LINE.findall(err)
        return rec

    # -- Miri ------------------------------------------------------------------------------

    def miri_available(self) -> bool:
        return bool(self.miri and self.miri_sysroot and Path(self.miri).exists() and Path(self.miri_sysroot).is_dir())

    def miri_cmd(self, tree_borrows: bool, *args: str) -> list[str]:
        cmd = [self.miri, "--sysroot", self.miri_sysroot]
        if tree_borrows:
            cmd.append("-Zmiri-tree-borrows")
        return cmd + ["--edition", EDITION, "--cap-lints", "allow"] + list(args)

    def miri_record(self, prefix: str, rc: int, out: str, err: str) -> dict:
        first = ERROR_LINE.search(err)
        if rc == 0:
            verdict = "ok"
        elif "Undefined Behavior" in err:
            verdict = "undefined-behavior"
        else:
            verdict = "error"
        return {
            f"{prefix}_verdict": verdict,
            f"{prefix}_rc": rc,
            f"{prefix}_stdout": out.strip(),
            f"{prefix}_first_error": first.group(0) if first else None,
            f"{prefix}_stderr": err[:4000],
        }

    def run_under_miri(self, rec: dict, *args: str) -> None:
        if not self.miri_available():
            rec["miri"] = "unavailable"
            return
        for prefix, tree in (("miri_sb", False), ("miri_tb", True)):
            rc, out, err = self.run(self.miri_cmd(tree, *args))
            rec.update(self.miri_record(prefix, rc, out, err))

    # -- probe kinds -----------------------------------------------------------------------

    def run_probe(self, name: str) -> dict:
        rc, _, err = self.run(self.rustc_cmd(f"{name}.rs", "-o", f"{name}.bin"))
        rec = self.compile_record(rc, err)
        if rc != 0:
            return rec
        nrc, nout, nerr = self.run([str(self.work / f"{name}.bin")])
        rec.update({"native_rc": nrc, "native_stdout": nout.strip(), "native_stderr": nerr[:2000]})
        self.run_under_miri(rec, f"{name}.rs")
        return rec

    def a4(self) -> dict:
        helper = self.rustc_cmd(
            "--crate-type", "rlib", "--crate-name", A4_HELPER, f"{A4_HELPER}.rs", "-o", f"native/lib{A4_HELPER}.rlib"
        )
        (self.work / "native").mkdir(exist_ok=True)
        hrc, _, herr = self.run(helper)
        if hrc != 0:
            return {"verdict": "helper-failed", "rc": hrc, "stderr": herr[:4000]}
        rc, _, err = self.run(
            self.rustc_cmd(f"{A4_MAIN}.rs", "--extern", f"{A4_HELPER}=native/lib{A4_HELPER}.rlib", "-o", f"{A4_MAIN}.bin")
        )
        rec = self.compile_record(rc, err)
        if rc != 0:
            return rec
        nrc, nout, nerr = self.run([str(self.work / f"{A4_MAIN}.bin")])
        rec.update({"native_rc": nrc, "native_stdout": nout.strip(), "native_stderr": nerr[:2000]})
        if not self.miri_available():
            rec["miri"] = "unavailable"
            return rec
        (self.work / "miri").mkdir(exist_ok=True)
        # Build the helper with MIR available to the interpreter (what `cargo miri` does).
        mrc, _, merr = self.run(
            [
                self.miri, "--sysroot", self.miri_sysroot, "--edition", EDITION, "--cap-lints", "allow",
                "--crate-type", "rlib", "--crate-name", A4_HELPER, f"{A4_HELPER}.rs",
                "-o", f"miri/lib{A4_HELPER}.rlib",
            ],
            extra_env={"MIRI_BE_RUSTC": "target"},
        )
        if mrc != 0:
            rec["miri"] = "helper-failed"
            rec["miri_helper_stderr"] = merr[:4000]
            return rec
        self.run_under_miri(rec, f"{A4_MAIN}.rs", "--extern", f"{A4_HELPER}=miri/lib{A4_HELPER}.rlib")
        return rec

    def a5(self) -> dict:
        rc, _, err = self.run(
            self.rustc_cmd(
                f"{A5}.rs", "-C", "opt-level=0", "-C", "no-prepopulate-passes", "--emit=llvm-ir", "-o", f"{A5}.ll"
            )
        )
        rec = self.compile_record(rc, err)
        if rc != 0:
            return rec
        ir = (self.work / f"{A5}.ll").read_text(encoding="utf-8", errors="replace")
        ty = f"{A5}::OnlyPinDrop"
        calls = [line.strip() for line in ir.splitlines() if line.startswith("; call ")]
        rec["glue_calls_trait_drop"] = f"; call <{ty} as core::ops::drop::Drop>::drop" in calls
        rec["trait_drop_calls_pin_drop"] = f"; call <{ty} as core::ops::drop::Drop>::pin_drop" in calls
        rec["call_comments"] = [c for c in calls if "drop" in c]
        return rec


def real_rustc(rustc: str, env: dict) -> Path | None:
    """Resolve the toolchain's `bin/` directory through `rustc --print sysroot`."""
    try:
        out = subprocess.run(
            [rustc, "--print", "sysroot"], capture_output=True, env=env, stdin=subprocess.DEVNULL, timeout=60
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if out.returncode != 0:
        return None
    return Path(out.stdout.decode().strip()) / "bin"


def stable_view(record: dict) -> dict:
    view = {}
    for name, rec in sorted(record["probes"].items()):
        keys = [k for k in STABLE_KEYS if k in rec]
        if name in UNSTABLE_NATIVE_STDOUT:
            keys = [k for k in keys if k != "native_stdout"]
        view[name] = {k: rec[k] for k in keys}
    return view


def detail(rec: dict) -> str:
    parts = []
    if rec.get("first_error"):
        parts.append(rec["first_error"][:110])
    if "native_stdout" in rec:
        parts.append(f"native: {rec['native_stdout']}")
    for prefix in ("miri_sb", "miri_tb"):
        if f"{prefix}_verdict" in rec:
            parts.append(f"{prefix}: {rec[f'{prefix}_verdict']}")
    if "glue_calls_trait_drop" in rec:
        parts.append(
            f"glue->Drop::drop={rec['glue_calls_trait_drop']} Drop::drop->pin_drop={rec['trait_drop_calls_pin_drop']}"
        )
    if rec.get("warnings"):
        parts.append(rec["warnings"][0])
    return " | ".join(parts)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--rustc", default="rustc")
    parser.add_argument("--miri", default=None)
    parser.add_argument("--miri-sysroot", default=None)
    parser.add_argument("--skip-miri", action="store_true")
    parser.add_argument("--out", default=None)
    parser.add_argument("--check", default=None)
    args = parser.parse_args(argv)

    probes_dir = Path(__file__).resolve().parent / "probes"
    if not probes_dir.is_dir():
        print(f"missing probe directory: {probes_dir}", file=sys.stderr)
        return 2

    version = subprocess.run([args.rustc, "-vV"], capture_output=True, stdin=subprocess.DEVNULL)
    if version.returncode != 0:
        print(f"cannot run `{args.rustc} -vV`", file=sys.stderr)
        return 2
    rustc_vv = version.stdout.decode().strip()
    commit = re.search(r"^commit-hash: (\S+)$", rustc_vv, re.MULTILINE)

    miri = None
    miri_sysroot = None
    miri_version = None
    if not args.skip_miri:
        miri = args.miri
        if miri is None:
            bindir = real_rustc(args.rustc, dict(os.environ))
            if bindir is not None and (bindir / "miri").exists():
                miri = str(bindir / "miri")
        miri_sysroot = args.miri_sysroot or os.environ.get("MIRI_SYSROOT") or os.path.expanduser("~/.cache/miri")
        if miri is not None:
            mv = subprocess.run([miri, "--version"], capture_output=True, stdin=subprocess.DEVNULL)
            miri_version = mv.stdout.decode().strip() if mv.returncode == 0 else None

    record: dict = {
        "schema": SCHEMA,
        "toolchain": {
            "rustc_vV": rustc_vv,
            "commit_hash": commit.group(1) if commit else None,
            "miri_version": miri_version,
        },
        "invocation": {
            "edition": EDITION,
            "compile_only": "rustc --edition 2024 --cap-lints allow <probe>.rs --emit=metadata",
            "run": "rustc --edition 2024 --cap-lints allow <probe>.rs; ./<probe>",
            "miri_sb": "miri --sysroot <miri-sysroot> --edition 2024 --cap-lints allow <probe>.rs",
            "miri_tb": "miri --sysroot <miri-sysroot> -Zmiri-tree-borrows --edition 2024 --cap-lints allow <probe>.rs",
        },
        "probes": {},
    }

    with tempfile.TemporaryDirectory(prefix="pin_ergonomics_probe_") as tmp:
        work = Path(tmp)
        for src in sorted(probes_dir.glob("*.rs")):
            shutil.copy(src, work / src.name)
        runner = Runner(args.rustc, miri, miri_sysroot, work)
        if not args.skip_miri and not runner.miri_available():
            print("note: Miri driver or sysroot not found; Miri runs are skipped", file=sys.stderr)

        for name, what in RUN_PROBES.items():
            record["probes"][name] = {"what": what, **runner.run_probe(name)}
        record["probes"][A4_MAIN] = {
            "what": "explicit projection through an unmarked `Unpin` wrapper around a self-referential future",
            **runner.a4(),
        }
        record["probes"][A5] = {"what": "functions called by the drop glue of a `pin_drop`-only type", **runner.a5()}
        for name, what in COMPILE_PROBES.items():
            record["probes"][name] = {"what": what, **runner.compile_only(name)}
        for name, what in LINT_PROBES.items():
            record["probes"][name] = {"what": what, **runner.compile_only(name, cap_lints=False)}

    print(f"toolchain: {rustc_vv.splitlines()[0]}  (miri: {miri_version or 'not run'})")
    for name, rec in sorted(record["probes"].items()):
        print(f"{name:48} {rec['verdict']:9} {detail(rec)}")

    if args.out:
        Path(args.out).write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"wrote {args.out}")

    if args.check:
        golden = json.loads(Path(args.check).read_text(encoding="utf-8"))
        golden_commit = golden.get("toolchain", {}).get("commit_hash")
        if golden_commit != record["toolchain"]["commit_hash"]:
            print(
                f"note: golden record is for rustc commit {golden_commit}, "
                f"this run used {record['toolchain']['commit_hash']}; differences are expected",
                file=sys.stderr,
            )
        want, got = stable_view(golden), stable_view(record)
        differences = 0
        for name in sorted(set(want) | set(got)):
            if want.get(name) == got.get(name):
                continue
            differences += 1
            print(f"DIFF {name}", file=sys.stderr)
            keys = sorted(set(want.get(name, {})) | set(got.get(name, {})))
            for key in keys:
                a, b = want.get(name, {}).get(key), got.get(name, {}).get(key)
                if a != b:
                    print(f"    {key}: golden={a!r} observed={b!r}", file=sys.stderr)
        if differences:
            print(f"check failed: {differences} probe(s) differ from {args.check}", file=sys.stderr)
            return 1
        print(f"check passed: all {len(got)} probes match {args.check}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
