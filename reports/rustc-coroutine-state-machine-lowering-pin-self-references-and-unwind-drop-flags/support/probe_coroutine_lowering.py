#!/usr/bin/env python3
"""Live rustc MIR + LLVM IR + runtime probe and Lean kernel audit for coroutine lowering."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import resource
import shutil
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Any


SUPPORT_DIR = Path(__file__).resolve().parent
SPECIMENS_RS = SUPPORT_DIR / "coroutine_specimens.rs"
LEAN_FILE = SUPPORT_DIR / "CoroutineStateTransformRefinement.lean"
OUT_JSON = SUPPORT_DIR / "probe_coroutine_results.json"

COROUTINE_FILTER_TARGETS = (
    "make_movable_two_yield_coro",
    "async_non_self_ref_two_await",
    "async_self_ref_two_await",
    "async_nested_drop_and_unwind",
    "inner_guarded_step",
)


def _augmented_env() -> dict[str, str]:
    env = os.environ.copy()
    home = str(Path.home())
    extra_bins = [
        f"{home}/.cargo/bin",
        f"{home}/.elan/bin",
        f"{home}/.local/bin",
    ]
    cur = env.get("PATH", "")
    env["PATH"] = ":".join(extra_bins + ([cur] if cur else []))
    return env


def _sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _run_cmd(
    cmd: list[str],
    env: dict[str, str],
    cwd: Path | None = None,
) -> tuple[int, str, str, float, int]:
    t0 = time.monotonic()
    usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    proc = subprocess.run(
        cmd,
        env=env,
        cwd=str(cwd) if cwd else None,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    elapsed_s = time.monotonic() - t0
    peak_rss_kb = max(0, int(usage_after.ru_maxrss))
    if peak_rss_kb == int(usage_before.ru_maxrss):
        # On Linux RUSAGE_CHILDREN holds cumulative max across all children; keep as reported max.
        peak_rss_kb = int(usage_after.ru_maxrss)
    return proc.returncode, proc.stdout, proc.stderr, elapsed_s, peak_rss_kb


def _parse_rustc_version(env: dict[str, str]) -> dict[str, str]:
    rc, out, err, _, _ = _run_cmd(["rustc", "--version", "-v"], env)
    if rc != 0:
        raise RuntimeError(f"rustc --version -v failed: {err}")
    info: dict[str, str] = {}
    lines = [ln.strip() for ln in out.splitlines() if ln.strip()]
    if lines:
        info["banner"] = lines[0]
    for ln in lines[1:]:
        if ":" in ln:
            k, v = ln.split(":", 1)
            info[k.strip()] = v.strip()
    return info


def _parse_mir_body(text: str) -> dict[str, Any]:
    lines = text.splitlines()
    signature = ""
    for ln in lines:
        if ln.startswith("fn "):
            signature = ln.strip()
            break

    layout_fields: list[str] = []
    variant_fields: dict[str, list[str]] = {}
    storage_conflicts: list[str] = []
    in_layout = False
    in_variants = False
    for ln in lines:
        s = ln.strip()
        if s == "coroutine layout {":
            in_layout = True
            continue
        if in_layout:
            if s == "}":
                in_layout = False
                in_variants = False
                continue
            if s == "variant_fields = {":
                in_variants = True
                continue
            if in_variants:
                if s == "}":
                    in_variants = False
                    continue
                m = re.match(r"^([A-Za-z0-9_]+)\s*\((\d+)\):\s*\[(.*)\],?$", s)
                if m:
                    name, idx, flds = m.group(1), m.group(2), m.group(3).strip()
                    items = [x.strip() for x in flds.split(",") if x.strip()]
                    variant_fields[f"{name}({idx})"] = items
            elif s.startswith("field "):
                layout_fields.append(s.rstrip(";"))
            elif s.startswith("storage_conflicts ="):
                m_conf = re.findall(r"\(_s\d+,\s*_s\d+\)", s)
                storage_conflicts = m_conf

    bb_headers = re.findall(r"^\s+bb(\d+)(?:\s+\(cleanup\))?:\s*\{", text, re.MULTILINE)
    cleanup_bbs = len(re.findall(r"^\s+bb\d+\s+\(cleanup\):", text, re.MULTILINE))
    storage_live_locals = re.findall(r"StorageLive\((_[0-9]+)\)", text)
    storage_dead_locals = re.findall(r"StorageDead\((_[0-9]+)\)", text)
    storage_live_remapped = len(re.findall(r"StorageLive\(\(\*", text))
    storage_dead_remapped = len(re.findall(r"StorageDead\(\(\*", text))
    set_discr = [int(x) for x in re.findall(r"discriminant\(\(\*_[0-9]+\)\)\s*=\s*(\d+);", text)]
    read_discr = len(re.findall(r"=\s*discriminant\(\(\*_[0-9]+\)\);", text))
    yield_count = len(re.findall(r"=\s*yield\(", text))
    coro_drop_count = len(re.findall(r"\bcoroutine_drop;", text))
    no_retag_copy_count = len(re.findall(r"\bno_retag copy\b", text))
    bool_drop_flags = len(
        re.findall(r"^\s+let(?: mut)? _\d+:\s*bool;\s*$", text, re.MULTILINE)
    )

    switch_on_entry: dict[str, str] = {}
    for ln in lines:
        m_sw = re.match(r"^\s*switchInt\(move _\d+\)\s*->\s*\[(.*)\];", ln)
        if m_sw and not switch_on_entry:
            for pair in m_sw.group(1).split(","):
                pair = pair.strip()
                if ":" in pair:
                    k, v = pair.split(":", 1)
                    switch_on_entry[k.strip()] = v.strip()

    assert_msgs = re.findall(r'assert\(const false,\s*"([^"]+)"', text)

    return {
        "signature": signature,
        "basic_blocks": len(bb_headers),
        "cleanup_bbs": cleanup_bbs,
        "layout_fields": layout_fields,
        "variant_fields": variant_fields,
        "storage_conflict_pairs": len(storage_conflicts),
        "storage_live_total": len(storage_live_locals) + storage_live_remapped,
        "storage_dead_total": len(storage_dead_locals) + storage_dead_remapped,
        "storage_live_remapped_fields": storage_live_remapped,
        "storage_dead_remapped_fields": storage_dead_remapped,
        "set_discriminant_values": sorted(set_discr),
        "set_discriminant_occurrences": set_discr,
        "read_discriminant_sites": read_discr,
        "yield_terminators": yield_count,
        "coroutine_drop_terminators": coro_drop_count,
        "no_retag_copy_sites": no_retag_copy_count,
        "local_bool_decls": bool_drop_flags,
        "entry_switch_targets": switch_on_entry,
        "panic_assert_messages": assert_msgs,
    }


def _find_mir_file(mir_dir: Path, fn_fragment: str, stage_fragment: str) -> Path | None:
    matches = sorted(
        p
        for p in mir_dir.iterdir()
        if p.is_file()
        and fn_fragment in p.name
        and stage_fragment in p.name
        and not p.name.startswith("core.")
    )
    return matches[0] if matches else None


def _parse_llvm_defines(ll_text: str) -> dict[str, Any]:
    defines: list[dict[str, Any]] = []
    # Note: on Linux `core::panic::panic_any` / `str` panic payload in `catch_unwind`
    # downcasts `&'static str` or `String` when panicked via panic!(...).
    # In `coroutine_specimens.rs`, panic_message formats `err.downcast_ref::<&'static str>()`,
    # wait: `panic!("{}", ...)` uses `String`, while `panic!("literal")` in Rust 2024
    # uses `&'static str`! Wait why did panic_message return "<non-string panic>"?
    # Let's inspect in coroutine_specimens.rs!
    # Also pass `-Z inline-mir=no` for an extra LLVM IR snapshot so internal closure
    # poll functions are not inlined away before we inspect them at O2/O3!
    fn_blocks: dict[str, dict[str, Any]] = {}

    lines = ll_text.splitlines()
    cur_role: str | None = None

    def _split_top_level_params(params_str: str) -> list[str]:
        parts: list[str] = []
        depth = 0
        start = 0
        for idx, ch in enumerate(params_str):
            if ch == "(":
                depth += 1
            elif ch == ")" and depth > 0:
                depth -= 1
            elif ch == "," and depth == 0:
                parts.append(params_str[start:idx].strip())
                start = idx + 1
        tail_piece = params_str[start:].strip()
        if tail_piece:
            parts.append(tail_piece)
        return parts

    def _classify(symbol: str) -> str:
        if "ManualUnpinTwoStepFuture" in symbol and "poll" in symbol:
            return "manual_unpin_fut_poll"
        if "drive_manual_unpin" in symbol:
            return "drive_manual_unpin"
        if "drive_generic_future" in symbol and "async_non_self_ref_two_await" in symbol:
            return "drive_async_non_self_ref"
        if "drive_generic_future" in symbol and "async_self_ref_two_await" in symbol:
            return "drive_async_self_ref"
        if "drive_generic_future" in symbol and "async_nested_drop_and_unwind" in symbol:
            return "drive_async_nested_drop"
        if "drive_generic_coro" in symbol and "make_movable_two_yield_coro" in symbol:
            return "drive_movable_coro"
        if "drop_generic_future" in symbol and "async_nested_drop_and_unwind" in symbol:
            return "drop_generic_async_nested"
        if "drop_glue" in symbol and "async_nested_drop_and_unwind" in symbol:
            return "drop_glue_async_nested"
        if "drop_glue" in symbol and "async_self_ref_two_await" in symbol:
            return "drop_glue_async_self_ref"
        if "drop_glue" in symbol and "async_non_self_ref_two_await" in symbol:
            return "drop_glue_async_non_self_ref"
        if "drop_glue" in symbol and "make_movable_two_yield_coro" in symbol:
            return "drop_glue_movable_coro"
        if "drop_glue" in symbol and "inner_guarded_step" in symbol:
            return "drop_glue_inner_guarded_step"
        if "async_non_self_ref_two_await" in symbol and "0B3_" in symbol:
            return "coro_async_non_self_ref_poll"
        if "async_self_ref_two_await" in symbol and "0B3_" in symbol:
            return "coro_async_self_ref_poll"
        if "async_nested_drop_and_unwind" in symbol and "0B3_" in symbol:
            return "coro_async_nested_drop_poll"
        if "inner_guarded_step" in symbol and "0B3_" in symbol:
            return "coro_inner_guarded_step_poll"
        if "make_movable_two_yield_coro" in symbol and "0B3_" in symbol:
            return "coro_movable_resume"
        return symbol

    for ln in lines:
        # Match `define ... @name(params) tail` where `tail` starts after the outer `)`.
        # Use non-greedy params or scan balanced parentheses from `@name(`.
        at_idx = ln.find("@") if ln.startswith("define ") else -1
        if at_idx != -1:
            paren_open = ln.find("(", at_idx)
            if paren_open != -1:
                depth = 0
                paren_close = -1
                for idx in range(paren_open, len(ln)):
                    if ln[idx] == "(":
                        depth += 1
                    elif ln[idx] == ")":
                        depth -= 1
                        if depth == 0:
                            paren_close = idx
                            break
                if paren_close != -1:
                    ret_ty = ln[len("define "):at_idx].strip()
                    if ret_ty.startswith("internal "):
                        ret_ty = ret_ty[len("internal "):].strip()
                    cur_name = ln[at_idx + 1:paren_open]
                    params_raw = ln[paren_open + 1:paren_close]
                    tail = ln[paren_close + 1:].strip()
                    params = _split_top_level_params(params_raw)
                    first_param = params[0] if params else ""
                    role = _classify(cur_name)
                    cur_role = role
                    attrs_first = {
                        "raw": first_param,
                        "has_noalias": bool(re.search(r"\bnoalias\b", first_param)),
                        "has_nofree": bool(re.search(r"\bnofree\b", first_param)),
                        "has_nonnull": bool(re.search(r"\bnonnull\b", first_param)),
                        "has_noundef": bool(re.search(r"\bnoundef\b", first_param)),
                        "has_dereferenceable": bool(re.search(r"\bdereferenceable\(", first_param)),
                        "dereferenceable_bytes": (
                            int(m_d.group(1))
                            if (m_d := re.search(r"\bdereferenceable\((\d+)\)", first_param))
                            else None
                        ),
                        "has_captures_none": "captures(none)" in first_param,
                        "align_bytes": (
                            int(m_a.group(1))
                            if (m_a := re.search(r"\balign (\d+)", first_param))
                            else None
                        ),
                        "has_dead_on_return": "dead_on_return" in first_param,
                    }
                    fn_blocks[role] = {
                        "symbol": cur_name,
                        "return_type": ret_ty,
                        "param_count": len(params),
                        "first_param_attrs": attrs_first,
                        "has_personality": "personality ptr" in tail,
                        "switch_count": 0,
                        "invoke_count": 0,
                        "landingpad_count": 0,
                        "lifetime_start_count": 0,
                        "lifetime_end_count": 0,
                    }
                    defines.append(fn_blocks[role])
                    continue
        elif cur_role is not None:
            rec = fn_blocks[cur_role]
            stripped = ln.strip()
            if stripped.startswith("switch "):
                rec["switch_count"] += 1
            if re.search(r"\binvoke\b", stripped):
                rec["invoke_count"] += 1
            if "landingpad" in stripped:
                rec["landingpad_count"] += 1
            if "@llvm.lifetime.start" in stripped:
                rec["lifetime_start_count"] += 1
            if "@llvm.lifetime.end" in stripped:
                rec["lifetime_end_count"] += 1
            if stripped == "}":
                cur_role = None

    return {
        "total_defined_functions": len(defines),
        "by_role": fn_blocks,
    }


def run_rustc_probe(env: dict[str, str]) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="coro_probe_") as tmp:
        tmp_path = Path(tmp)
        mir_dir = tmp_path / "mir_dump"
        mir_dir.mkdir(parents=True, exist_ok=True)
        rlib_out = tmp_path / "libspecimens.rlib"

        # 1. Dump MIR across StateTransform stages & Runtime(PostCleanup).
        t0 = time.monotonic()
        rc, _, err, mir_elapsed, _ = _run_cmd(
            [
                "rustc",
                "--edition=2024",
                "--crate-type=lib",
                "-C",
                "opt-level=2",
                "-Z",
                "dump-mir=coroutine_before|coroutine_resume|coroutine_drop|runtime-post-cleanup",
                "-Z",
                f"dump-mir-dir={mir_dir}",
                str(SPECIMENS_RS),
                "-o",
                str(rlib_out),
            ],
            env,
        )
        if rc != 0:
            raise RuntimeError(f"rustc MIR dump failed:\n{err}")

        mir_summaries: dict[str, Any] = {}
        for target in COROUTINE_FILTER_TARGETS:
            entry: dict[str, Any] = {}
            for stage in (
                "coroutine_before",
                "coroutine_resume",
                "coroutine_drop",
                "runtime-post-cleanup",
            ):
                p = _find_mir_file(mir_dir, target, stage)
                if p is not None:
                    entry[stage] = _parse_mir_body(p.read_text(encoding="utf-8"))
                else:
                    entry[stage] = None
            mir_summaries[target] = entry

        # Capture exact drop_glue MIR for async_nested_drop_and_unwind if emitted.
        drop_glue_matches = sorted(
            p
            for p in mir_dir.iterdir()
            if "drop_glue" in p.name
            and "async_nested_drop_and_unwind" in p.name
            and "runtime-optimized" in p.name
        )
        nested_drop_glue_mir = (
            _parse_mir_body(drop_glue_matches[0].read_text(encoding="utf-8"))
            if drop_glue_matches
            else None
        )

        # 2. Emit LLVM IR across pre-opt frontend, -O2, -O2 (-Z inline-mir=no), and -O3.
        llvm_profiles: dict[str, Any] = {}
        for prof_name, flags in (
            ("o2_no_prepopulate", ["-C", "opt-level=2", "-C", "no-prepopulate-passes"]),
            ("o2", ["-C", "opt-level=2"]),
            ("o2_no_mir_inline", ["-C", "opt-level=2", "-Z", "inline-mir=no"]),
            ("o3", ["-C", "opt-level=3"]),
        ):
            ll_path = tmp_path / f"specimens_{prof_name}.ll"
            rc, _, err, ll_elapsed, _ = _run_cmd(
                [
                    "rustc",
                    "--edition=2024",
                    "--crate-type=lib",
                    "--emit=llvm-ir",
                    *flags,
                    str(SPECIMENS_RS),
                    "-o",
                    str(ll_path),
                ],
                env,
            )
            if rc != 0:
                raise RuntimeError(f"rustc --emit=llvm-ir ({prof_name}) failed:\n{err}")
            parsed_ll = _parse_llvm_defines(ll_path.read_text(encoding="utf-8"))
            parsed_ll["compile_elapsed_s"] = round(ll_elapsed, 4)
            llvm_profiles[prof_name] = parsed_ll

        # 3. Compile and execute standalone binary at -O3 for lifecycle & latency proof.
        bin_path = tmp_path / "specimens_bin"
        rc, _, err, bin_compile_s, _ = _run_cmd(
            [
                "rustc",
                "--edition=2024",
                "--crate-type=bin",
                "-C",
                "opt-level=3",
                str(SPECIMENS_RS),
                "-o",
                str(bin_path),
            ],
            env,
        )
        if rc != 0:
            raise RuntimeError(f"rustc bin compile failed:\n{err}")
        bin_size_bytes = bin_path.stat().st_size

        rc, run_out, run_err, bin_run_s, _ = _run_cmd([str(bin_path)], env)
        if rc != 0:
            raise RuntimeError(f"specimens_bin exited with {rc}:\n{run_err}\n{run_out}")
        runtime_json = json.loads(run_out)
        total_probe_s = time.monotonic() - t0

    return {
        "mir_dump_compile_s": round(mir_elapsed, 4),
        "bin_compile_s": round(bin_compile_s, 4),
        "bin_run_s": round(bin_run_s, 4),
        "bin_size_bytes": bin_size_bytes,
        "rustc_probe_total_s": round(total_probe_s, 4),
        "mir_summaries": mir_summaries,
        "nested_drop_glue_post_cleanup_mir": nested_drop_glue_mir,
        "llvm_ir": llvm_profiles,
        "runtime_verification": runtime_json,
    }


def run_lean_audit(env: dict[str, str]) -> dict[str, Any]:
    if not LEAN_FILE.exists():
        return {"status": "missing_lean_file"}

    lean_text = LEAN_FILE.read_text(encoding="utf-8")
    lean_lines = len(lean_text.splitlines())
    theorem_decls = re.findall(r"^\s*(?:private\s+)?theorem\s+([A-Za-z0-9_']+)", lean_text, re.MULTILINE)
    def_decls = re.findall(
        r"^\s*(?:private\s+)?(?:def|inductive|structure|abbrev)\s+([A-Za-z0-9_']+)",
        lean_text,
        re.MULTILINE,
    )

    forbidden_tokens = [
        "sorry",
        "Classical.choice",
        "omega",
        "bv_decide",
        "native_decide",
        "Lean.ofReduceBool",
        "partial def",
        "._unsafe_rec",
        "namespace Trusted",
    ]
    token_hits = {
        tok: len(re.findall(r"(?<![A-Za-z0-9_])" + re.escape(tok) + r"(?![A-Za-z0-9_])", lean_text))
        for tok in forbidden_tokens
    }

    wrapper = Path.home() / ".local" / "bin" / "anneal-lean-run"
    if wrapper.exists():
        cmd = [str(wrapper), "--", "lean", "-DElab.async=false", "-Ddebug.skipKernelTC=false", str(LEAN_FILE)]
    else:
        cmd = ["lean", "-DElab.async=false", "-Ddebug.skipKernelTC=false", str(LEAN_FILE)]

    t0 = time.monotonic()
    rc, out, err, _, _ = _run_cmd(cmd, env)
    elapsed_s = time.monotonic() - t0
    if rc != 0:
        raise RuntimeError(f"Lean check failed (rc={rc}):\n{out}\n{err}")

    rc_ver, ver_out, _, _, _ = _run_cmd(["lean", "--version"], env)
    lean_version = ver_out.strip() if rc_ver == 0 else "unknown"

    combined_output = (out + "\n" + err).strip()
    axiom_lines = [
        ln.strip()
        for ln in combined_output.splitlines()
        if "depends on axioms:" in ln or "does not depend on any axioms" in ln
    ]
    uses_classical = "Classical.choice" in combined_output
    uses_sorry_ax = "sorryAx" in combined_output
    uses_reduce_bool = "Lean.ofReduceBool" in combined_output

    return {
        "lean_version": lean_version,
        "file_name": LEAN_FILE.name,
        "sha256": _sha256_file(LEAN_FILE),
        "loc": lean_lines,
        "theorem_count": len(theorem_decls),
        "def_and_type_count": len(def_decls),
        "theorems": theorem_decls,
        "kernel_check_elapsed_s": round(elapsed_s, 4),
        "exit_code": rc,
        "forbidden_source_token_hits": token_hits,
        "axiom_audit": {
            "lines": axiom_lines,
            "uses_classical_choice": uses_classical,
            "uses_sorry_ax": uses_sorry_ax,
            "uses_reduce_bool": uses_reduce_bool,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-lean", action="store_true", help="Skip Lean kernel check")
    args = parser.parse_args()

    env = _augmented_env()
    rustc_meta = _parse_rustc_version(env)
    rustc_probe = run_rustc_probe(env)
    lean_audit = {"status": "skipped"} if args.skip_lean else run_lean_audit(env)

    payload = {
        "schema": "coroutine-lowering-probe/1",
        "rustc_toolchain": rustc_meta,
        "specimens_file": {
            "name": SPECIMENS_RS.name,
            "sha256": _sha256_file(SPECIMENS_RS),
            "loc": len(SPECIMENS_RS.read_text(encoding="utf-8").splitlines()),
        },
        "rustc_probe": rustc_probe,
        "lean_audit": lean_audit,
    }
    OUT_JSON.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # Compact console summary for verification runs.
    o2_roles = rustc_probe["llvm_ir"]["o2_no_prepopulate"]["by_role"]
    o3_roles = rustc_probe["llvm_ir"]["o3"]["by_role"]
    print(f"rustc: {rustc_meta.get('banner', 'unknown')} (commit {rustc_meta.get('commit-hash', 'unknown')})")
    print("LLVM IR first-param attributes (o2_no_prepopulate -> o3):")
    for role in (
        "manual_unpin_fut_poll",
        "drive_manual_unpin",
        "drive_movable_coro",
        "coro_movable_resume",
        "drive_async_non_self_ref",
        "coro_async_non_self_ref_poll",
        "drive_async_self_ref",
        "coro_async_self_ref_poll",
        "drive_async_nested_drop",
        "coro_async_nested_drop_poll",
    ):
        a2 = o2_roles.get(role, {}).get("first_param_attrs", {})
        a3 = o3_roles.get(role, {}).get("first_param_attrs", {})
        print(
            f"  {role}: preopt(noalias={a2.get('has_noalias')}, deref={a2.get('dereferenceable_bytes')}, cap_none={a2.get('has_captures_none')})"
            f" | o3(noalias={a3.get('has_noalias')}, deref={a3.get('dereferenceable_bytes')}, cap_none={a3.get('has_captures_none')})"
        )
    print(f"Runtime sizes: {rustc_probe['runtime_verification']['sizes_bytes']}")
    print(f"Lifecycle drops: {rustc_probe['runtime_verification']['lifecycle_drop_counts']}")
    print(f"Wrote {OUT_JSON.name} ({OUT_JSON.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
