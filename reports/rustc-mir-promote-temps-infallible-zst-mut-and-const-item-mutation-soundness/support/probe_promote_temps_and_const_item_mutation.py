#!/usr/bin/env python3
"""Run live rustc and Miri differential probes for PromoteTemps and CheckConstItemMutation.

Executes standalone Rust specimens under default `rustc` and `cargo miri`,
captures sanitized MIR dumps for key cases, compares overlapping cases against
`baseline_1_102_3ef0c22cd.json`, and writes `probe_results.json`.
"""

from __future__ import annotations

import datetime
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPECIMENS = HERE / "specimens"
MIR_DUMPS = HERE / "mir_dumps"
BASELINE_PATH = HERE / "baseline_1_102_3ef0c22cd.json"


def build_env() -> dict[str, str]:
    env = dict(os.environ)
    extra = [str(Path.home() / ".cargo" / "bin"), str(Path.home() / ".local" / "bin")]
    env["PATH"] = ":".join(extra + [env.get("PATH", "")])
    return env


def sanitize_text(text: str, tmp_dir: Path | None = None) -> str:
    home = str(Path.home())
    out = text
    if tmp_dir is not None:
        out = out.replace(str(tmp_dir), "$TMP")
    out = re.sub(r"/home/[^/\s]+/\.rustup/toolchains/[^/\s]+", "$SYSROOT", out)
    out = re.sub(r"/home/[^/\s]+", "$HOME", out)
    out = re.sub(r"/" + r"rustc-dev/[0-9a-f]+", "$RUSTC_DEV", out)
    out = re.sub(r"/" + r"rustc/[0-9a-f]+", "$RUSTC_SRC", out)
    out = out.replace(home, "$HOME")
    return out


def run_rustc_case(
    name: str,
    code: str,
    rustc: str,
    env: dict[str, str],
    crate_type: str = "lib",
    extra_args: list[str] | None = None,
    dump_pass: str | None = None,
    run_bin: bool = False,
) -> dict:
    extra_args = list(extra_args or [])
    with tempfile.TemporaryDirectory(prefix=f"probe_{name}_") as td:
        td_path = Path(td)
        src_path = td_path / f"{name}.rs"
        src_path.write_text(code, encoding="utf-8")
        out_path = td_path / (f"{name}.out" if crate_type == "bin" else f"lib{name}.rlib")
        mir_dir = td_path / "mir"
        cmd = [rustc, "--edition=2021", f"--crate-type={crate_type}", "-o", str(out_path)] + extra_args
        if dump_pass is not None:
            mir_dir.mkdir()
            cmd.extend(["-Z", f"dump-mir={dump_pass}", f"-Zdump-mir-dir={mir_dir}"])
        cmd.append(str(src_path))
        proc = subprocess.run(cmd, env=env, cwd=td_path, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        stderr_clean = sanitize_text(proc.stderr, td_path)
        warnings = []
        for m in re.finditer(r"warning: ([^\n]+)\n\s*--> [^:\n]+:(\d+):\d+", proc.stderr):
            warnings.append({"line": int(m.group(2)), "msg": m.group(1).strip()})
        first_err = next((l.strip() for l in stderr_clean.splitlines() if l.strip().startswith("error")), "")

        promoted_counts = {}
        dump_files = {}
        if mir_dir.exists():
            for mf in sorted(mir_dir.glob("*.mir")):
                txt = sanitize_text(mf.read_text(encoding="utf-8", errors="replace"), td_path)
                promoted_counts[mf.name] = len(re.findall(r"promoted\[\d+\]", txt))
                dump_files[mf.name] = txt

        run_rc = None
        run_stdout = None
        if run_bin and proc.returncode == 0 and out_path.exists():
            r = subprocess.run([str(out_path)], env=env, cwd=td_path, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            run_rc = r.returncode
            run_stdout = sanitize_text(r.stdout.strip(), td_path)

        return {
            "compile_rc": proc.returncode,
            "stderr_first": first_err,
            "stderr": stderr_clean,
            "warnings": warnings,
            "run_rc": run_rc,
            "run_stdout": run_stdout,
            "promoted_counts": promoted_counts,
            "dump_files": dump_files,
        }


def run_miri_case(name: str, src_file: Path, env: dict[str, str], miriflags: str = "") -> dict:
    with tempfile.TemporaryDirectory(prefix=f"miri_{name}_") as td:
        td_path = Path(td)
        (td_path / "Cargo.toml").write_text(
            f'[package]\nname = "{name}"\nversion = "0.1.0"\nedition = "2021"\n',
            encoding="utf-8",
        )
        (td_path / "src").mkdir()
        shutil.copy2(src_file, td_path / "src" / "main.rs")
        run_env = dict(env)
        if miriflags:
            run_env["MIRIFLAGS"] = miriflags
        else:
            run_env.pop("MIRIFLAGS", None)
        proc = subprocess.run(
            ["cargo", "miri", "run", "--quiet"],
            env=run_env,
            cwd=td_path,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        return {
            "rc": proc.returncode,
            "stdout": sanitize_text(proc.stdout.strip(), td_path),
            "stderr_tail": sanitize_text("\n".join(proc.stderr.splitlines()[-8:]), td_path),
        }


def save_dump(subdir: str, filename: str, content: str) -> str:
    dest = MIR_DUMPS / subdir / filename
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(content, encoding="utf-8")
    return f"support/mir_dumps/{subdir}/{filename}"


def main() -> int:
    env = build_env()
    rustc = shutil.which("rustc", path=env["PATH"]) or "rustc"
    rustc_v = subprocess.run([rustc, "-vV"], env=env, capture_output=True, text=True, check=True).stdout.strip()
    miri_v = subprocess.run(["cargo", "miri", "--version"], env=env, capture_output=True, text=True, check=True).stdout.strip()

    MIR_DUMPS.mkdir(parents=True, exist_ok=True)
    baseline = json.loads(BASELINE_PATH.read_text(encoding="utf-8"))

    results: dict[str, dict] = {}
    saved_mir: list[str] = []

    # 1. ZST mutable borrow & rvalue promotion (native + MIR + Miri SB + Miri TB)
    zst_src = (SPECIMENS / "zst_mut_and_rvalue_promotion.rs").read_text(encoding="utf-8")
    zst_res = run_rustc_case(
        "zst_mut_and_rvalue_promotion",
        zst_src,
        rustc,
        env,
        crate_type="bin",
        dump_pass="PromoteTemps",
        run_bin=True,
    )
    miri_sb = run_miri_case("zst_mut_sb", SPECIMENS / "zst_mut_and_rvalue_promotion.rs", env)
    miri_tb = run_miri_case("zst_mut_tb", SPECIMENS / "zst_mut_and_rvalue_promotion.rs", env, "-Zmiri-tree-borrows")
    probe_three_after = [k for k in zst_res["promoted_counts"] if "probe_three_promoteds" in k and "PromoteTemps.after.mir" in k]
    promoted_count_after = zst_res["promoted_counts"][probe_three_after[0]] if probe_three_after else 0
    for fn, content in zst_res["dump_files"].items():
        if "probe_three_promoteds" in fn or "dual_protected_zst_mut" in fn:
            saved_mir.append(save_dump("zst_mut_and_rvalue_promotion", fn, content))
    results["zst_mut_and_rvalue_promotion"] = {
        "compile_rc": zst_res["compile_rc"],
        "native_rc": zst_res["run_rc"],
        "native_stdout": zst_res["run_stdout"],
        "miri_sb_rc": miri_sb["rc"],
        "miri_tb_rc": miri_tb["rc"],
        "miri_stdout": miri_sb["stdout"],
        "miri_tb_stdout": miri_tb["stdout"],
        "promoted_count_after": promoted_count_after,
    }

    # 2. Miri OOB write through promoted &'static mut [u32] must be rejected under SB & TB
    oob_sb = run_miri_case("zst_oob_sb", SPECIMENS / "miri_zst_mut_oob_write_rejected.rs", env)
    oob_tb = run_miri_case("zst_oob_tb", SPECIMENS / "miri_zst_mut_oob_write_rejected.rs", env, "-Zmiri-tree-borrows")
    results["miri_zst_mut_oob_write_rejected"] = {
        "miri_sb_rc": oob_sb["rc"],
        "miri_tb_rc": oob_tb["rc"],
        "miri_sb_stderr_tail": oob_sb["stderr_tail"],
        "miri_tb_stderr_tail": oob_tb["stderr_tail"],
    }

    # 3. Single-file lib probes covering RFC 3027 infallibility, ZST mut, UnsafeCell, and const blocks
    lib_cases = [
        ("div_by_zero_not_promoted", "#![allow(unconditional_panic)]\npub fn f() -> &'static u32 { &(1u32 / 0u32) }\n", [], "PromoteTemps"),
        ("rem_by_zero_not_promoted", "#![allow(unconditional_panic)]\npub fn f() -> &'static u32 { &(1u32 % 0u32) }\n", [], "PromoteTemps"),
        ("signed_min_div_neg1_not_promoted", "#![allow(arithmetic_overflow)]\npub fn f() -> &'static i32 { &(i32::MIN / -1i32) }\n", [], "PromoteTemps"),
        ("signed_nonmin_div_neg1_promoted", "pub fn f() -> &'static i32 { &((-5i32) / -1i32) }\n", [], "PromoteTemps"),
        ("overflow_add_in_dead_branch_promoted", "#![allow(arithmetic_overflow)]\npub fn f() -> Option<&'static u8> {\n    if false { Some(&(200u8 + 200u8)) } else { None }\n}\n", ["-C", "overflow-checks=on"], "PromoteTemps"),
        ("place_index_oob_base_promoted", "#![allow(unconditional_panic)]\npub fn f() -> &'static u32 { &([10u32, 20u32][2]) }\n", [], "PromoteTemps"),
        ("value_index_oob_not_promoted", "#![allow(unconditional_panic)]\npub fn f() -> &'static u32 { &({ [10u32, 20u32][2] }) }\n", [], "PromoteTemps"),
        ("value_arith_index_oob_not_promoted", "#![allow(unconditional_panic)]\npub fn f() -> &'static u32 { &(1u32 + [10u32, 20u32][2]) }\n", [], "PromoteTemps"),
        ("value_index_inbounds_promoted", "pub fn f() -> &'static u32 { &({ [10u32, 20u32][1] }) }\n", [], "PromoteTemps"),
        ("plain_const_fn_not_promoted", "const fn cf() -> u32 { 42 }\npub fn f() -> &'static u32 { &cf() }\n", [], "PromoteTemps"),
        ("promotable_std_const_fn_promoted", "pub fn f() -> &'static usize { &core::mem::size_of::<u64>() }\n", [], "PromoteTemps"),
        ("const_item_safe_block_const_fn_promoted", "const fn cf() -> u32 { 42 }\npub const C_SAFE: &'static u32 = core::convert::identity(&cf());\n", [], "PromoteTemps"),
        ("const_item_dead_branch_nonext_rejected", "const fn cf_panic() -> u32 { panic!(\"dead\") }\npub const C_DEAD: Option<&'static u32> = if false { Some(core::convert::identity(&cf_panic())) } else { None };\n", [], "PromoteTemps"),
        ("const_item_dead_branch_ext_unpromoted_ok", "const fn cf_panic() -> u32 { panic!(\"dead\") }\npub const C_DEAD_EXT: Option<&'static u32> = if false { Some(&cf_panic()) } else { None };\n", [], "PromoteTemps"),
        ("const_item_safe_block_panic_e0080", "const fn cf_panic() -> u32 { panic!(\"live\") }\npub const C_LIVE_PANIC: &'static u32 = core::convert::identity(&cf_panic());\n", [], "PromoteTemps"),
        ("inline_const_block_allows_plain_const_fn", "const fn cf() -> u32 { 42 }\npub fn f() -> &'static u32 { &const { cf() } }\n", [], "PromoteTemps"),
        ("inline_const_pme_dead_branch_obj_rejected", "pub fn f() -> Option<&'static u32> {\n    if false { Some(&const { 1u32 / 0u32 }) } else { None }\n}\n", ["--emit=obj"], "PromoteTemps"),
        ("inline_const_pme_dead_branch_metadata_skipped", "pub fn f() -> Option<&'static u32> {\n    if false { Some(&const { 1u32 / 0u32 }) } else { None }\n}\n", ["--emit=metadata"], None),
        ("mut_non_zst_not_promoted", "pub fn f() -> &'static mut [u32; 1] { &mut [0] }\n", [], "PromoteTemps"),
        ("mut_unit_zst_not_promoted", "pub fn f() -> &'static mut () { &mut () }\n", [], "PromoteTemps"),
        ("unsafecell_u32_not_promoted", "use core::cell::UnsafeCell;\npub fn f() -> &'static UnsafeCell<u32> { &UnsafeCell::new(0) }\n", [], "PromoteTemps"),
        ("unsafecell_zst_not_promoted", "use core::cell::UnsafeCell;\npub fn f() -> &'static UnsafeCell<()> { &UnsafeCell::new(()) }\n", [], "PromoteTemps"),
        ("unsafecell_zst_const_temp_not_promoted", "use core::cell::UnsafeCell;\nconst UC: UnsafeCell<()> = UnsafeCell::new(());\npub fn f() -> &'static UnsafeCell<()> { &UC }\n", [], "PromoteTemps"),
        ("none_unsafecell_zst_promoted", "use core::cell::UnsafeCell;\npub fn f() -> &'static Option<UnsafeCell<()>> { &None }\n", [], "PromoteTemps"),
        ("some_unsafecell_zst_not_promoted", "use core::cell::UnsafeCell;\nconst UC: UnsafeCell<()> = UnsafeCell::new(());\npub fn f() -> &'static Option<UnsafeCell<()>> { &Some(UC) }\n", [], "PromoteTemps"),
    ]
    keep_dumps = {
        "overflow_add_in_dead_branch_promoted",
        "place_index_oob_base_promoted",
        "value_index_oob_not_promoted",
        "inline_const_block_allows_plain_const_fn",
        "inline_const_pme_dead_branch_obj_rejected",
    }
    for cname, code, flags, dump_pass in lib_cases:
        res = run_rustc_case(cname, code, rustc, env, crate_type="lib", extra_args=flags, dump_pass=dump_pass)
        after_sum = sum(v for k, v in res["promoted_counts"].items() if "PromoteTemps.after.mir" in k)
        results[cname] = {
            "rc": res["compile_rc"],
            "stderr_first": res["stderr_first"],
            "promoted_count_after": after_sum,
        }
        if cname in keep_dumps:
            for fn, content in res["dump_files"].items():
                if ".f." in fn or ".PromoteTemps." in fn:
                    saved_mir.append(save_dump(cname, fn, content))

    # 4. CheckConstItemMutation asymmetry & nested Drop differential
    ccim_src = (SPECIMENS / "check_const_item_mutation_asymmetry.rs").read_text(encoding="utf-8")
    ccim_res = run_rustc_case(
        "check_const_item_mutation_asymmetry",
        ccim_src,
        rustc,
        env,
        crate_type="bin",
        dump_pass="built",
        run_bin=True,
    )
    for fn, content in ccim_res["dump_files"].items():
        if "demo_const_mutation_paths" in fn:
            saved_mir.append(save_dump("check_const_item_mutation_asymmetry", fn, content))
    results["check_const_item_mutation_asymmetry"] = {
        "compile_rc": ccim_res["compile_rc"],
        "run_rc": ccim_res["run_rc"],
        "run_stdout": ccim_res["run_stdout"],
        "warnings": ccim_res["warnings"],
    }

    explicit_mut_ref_src = """use std::sync::atomic::{AtomicU32, Ordering};
static EXPLICIT_DROPS: AtomicU32 = AtomicU32::new(0);
struct D { val: u32 }
impl Drop for D {
    fn drop(&mut self) { EXPLICIT_DROPS.fetch_add(self.val, Ordering::SeqCst); }
}
const C: D = D { val: 0 };
fn main() {
    { let r = &mut C; r.val = 50; }
    unsafe {
        let mut x = 1u32;
        struct P(*mut u32);
        const CP: P = P(core::ptr::null_mut());
        let mut p = CP;
        p.0 = &mut x as *mut u32;
        *p.0 = 7;
    }
    println!("EXPLICIT_DROPS={}", EXPLICIT_DROPS.load(Ordering::SeqCst));
}
"""
    explicit_res = run_rustc_case(
        "check_const_item_mutation_explicit_mut_ref",
        explicit_mut_ref_src,
        rustc,
        env,
        crate_type="bin",
        run_bin=True,
    )
    results["check_const_item_mutation_explicit_mut_ref"] = {
        "compile_rc": explicit_res["compile_rc"],
        "run_rc": explicit_res["run_rc"],
        "run_stdout": explicit_res["run_stdout"],
        "warnings": explicit_res["warnings"],
    }

    nested_src = (SPECIMENS / "check_const_item_mutation_nested_drop.rs").read_text(encoding="utf-8")
    nested_res = run_rustc_case(
        "check_const_item_mutation_nested_drop",
        nested_src,
        rustc,
        env,
        crate_type="bin",
        run_bin=True,
    )
    results["check_const_item_mutation_nested_drop"] = {
        "compile_rc": nested_res["compile_rc"],
        "run_rc": nested_res["run_rc"],
        "run_stdout": nested_res["run_stdout"],
        "warnings": nested_res["warnings"],
    }

    # Differential check against baseline_1_102_3ef0c22cd.json
    diff_summary = {}
    b_cases = baseline["cases"]
    for key in [
        "zst_mut_and_rvalue_promotion",
        "div_by_zero_not_promoted",
        "plain_const_fn_not_promoted",
        "unsafecell_u32_not_promoted",
        "unsafecell_zst_not_promoted",
        "mut_non_zst_not_promoted",
        "inline_const_block_allows_plain_const_fn",
        "check_const_item_mutation_asymmetry",
    ]:
        b = b_cases[key]
        cur = results[key]
        if key == "zst_mut_and_rvalue_promotion":
            parity = (
                b["compile_rc"] == cur["compile_rc"]
                and b["native_rc"] == cur["native_rc"]
                and b["native_stdout"] == cur["native_stdout"]
                and b["miri_sb_rc"] == cur["miri_sb_rc"]
                and b["miri_tb_rc"] == cur["miri_tb_rc"]
                and b["miri_stdout"] == cur["miri_stdout"]
                and b["miri_stdout"] == cur["miri_tb_stdout"]
                and b["promoted_count_after"] == cur["promoted_count_after"]
            )
        elif key == "check_const_item_mutation_asymmetry":
            b_msgs = [w["msg"] for w in b["warnings"]]
            c_msgs = [w["msg"] for w in cur["warnings"]]
            parity = (
                b["compile_rc"] == cur["compile_rc"]
                and cur["run_stdout"].startswith(b["run_stdout"])
                and b_msgs == c_msgs
            )
        else:
            parity = b["rc"] == cur["rc"] and b["stderr_first"] == cur["stderr_first"]
        diff_summary[key] = parity

    # Hard assertions so probe exits nonzero if any ground-truth expectation regresses
    assert all(diff_summary.values()), f"baseline parity mismatch: {diff_summary}"
    assert results["miri_zst_mut_oob_write_rejected"]["miri_sb_rc"] != 0
    assert results["miri_zst_mut_oob_write_rejected"]["miri_tb_rc"] != 0
    assert results["rem_by_zero_not_promoted"]["rc"] == 1
    assert results["signed_min_div_neg1_not_promoted"]["rc"] == 1
    assert results["signed_nonmin_div_neg1_promoted"]["rc"] == 0
    assert results["overflow_add_in_dead_branch_promoted"]["rc"] == 0
    assert results["place_index_oob_base_promoted"]["rc"] == 0
    assert results["value_index_oob_not_promoted"]["rc"] == 1
    assert results["value_arith_index_oob_not_promoted"]["rc"] == 1
    assert results["value_index_inbounds_promoted"]["rc"] == 0
    assert results["promotable_std_const_fn_promoted"]["rc"] == 0
    assert results["const_item_safe_block_const_fn_promoted"]["rc"] == 0
    assert results["const_item_safe_block_const_fn_promoted"]["promoted_count_after"] == 1
    assert results["const_item_dead_branch_nonext_rejected"]["rc"] == 1
    assert results["const_item_dead_branch_nonext_rejected"]["promoted_count_after"] == 0
    assert results["const_item_dead_branch_ext_unpromoted_ok"]["rc"] == 0
    assert results["const_item_dead_branch_ext_unpromoted_ok"]["promoted_count_after"] == 0
    assert results["const_item_safe_block_panic_e0080"]["rc"] == 1
    assert results["const_item_safe_block_panic_e0080"]["promoted_count_after"] == 1
    assert results["inline_const_pme_dead_branch_obj_rejected"]["rc"] == 1
    assert results["inline_const_pme_dead_branch_metadata_skipped"]["rc"] == 0
    assert results["mut_unit_zst_not_promoted"]["rc"] == 1
    assert results["unsafecell_zst_const_temp_not_promoted"]["rc"] == 1
    assert results["none_unsafecell_zst_promoted"]["rc"] == 0
    assert results["some_unsafecell_zst_not_promoted"]["rc"] == 1
    assert results["check_const_item_mutation_nested_drop"]["run_stdout"] == "NESTED_DROPS=43"
    assert len(results["check_const_item_mutation_nested_drop"]["warnings"]) == 2

    payload = {
        "schema": "promote-temps-probe-results/1",
        "generated_on": datetime.date.today().isoformat(),
        "rustc_version": rustc_v,
        "miri_version": miri_v,
        "baseline_1_102_version": baseline["rustc_version"],
        "baseline_parity": diff_summary,
        "saved_mir_dumps": saved_mir,
        "cases": results,
    }
    (HERE / "probe_results.json").write_text(json.dumps(payload, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    print("ALL_PROBES_PASSED", len(results), "cases,", len(saved_mir), "mir dumps saved")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
