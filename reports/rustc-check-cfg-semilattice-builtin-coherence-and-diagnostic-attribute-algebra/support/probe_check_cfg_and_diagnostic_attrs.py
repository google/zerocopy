#!/usr/bin/env python3
"""Real-`rustc` probe for check-cfg accumulation, builtin-cfg coherence,
atomic cfg emission, cfg predicates and the `#[diagnostic::*]` attributes.

Every observation recorded by this script comes from a `rustc` subprocess (or
from running a binary that `rustc` just produced).  The only non-subprocess
logic is (1) classification of structured JSON diagnostics and (2) a small
reference model of `--check-cfg` accumulation used for differential testing
against the compiler; model predictions are stored next to, never instead of,
the compiler's verdicts.

Usage:
    python3 probe_check_cfg_and_diagnostic_attrs.py [--rustc PATH] [--out FILE]
                                                   [--skip-census]

Requirements: Python 3.10+ (standard library only) and a nightly `rustc`
(parts B, C and D use `-Z` flags and `#![feature(..)]`).  Sources and build
products live in a temporary directory that is removed on exit.  The exit
status is 0 iff every check listed under `invariant_checks` holds.
"""

import argparse
import datetime
import itertools
import json
import os
import random
import subprocess
import sys
import tempfile

TIMEOUT = 120


class Probe:
    def __init__(self, rustc, tmp):
        self.rustc = rustc
        self.tmp = tmp
        self.sysroot = self.raw(["--print", "sysroot"])[1].strip()
        self.home = os.path.expanduser("~")
        self.subprocess_calls = 0

    # ---- subprocess helpers -------------------------------------------------
    def raw(self, args, env=None):
        full_env = dict(os.environ)
        full_env.pop("RUSTFLAGS", None)
        full_env.pop("RUSTC_BOOTSTRAP", None)
        if env:
            full_env.update(env)
        proc = subprocess.run(
            [self.rustc] + list(args),
            capture_output=True,
            text=True,
            timeout=TIMEOUT,
            cwd=self.tmp,
            env=full_env,
        )
        self.subprocess_calls = getattr(self, "subprocess_calls", 0) + 1
        return proc.returncode, proc.stdout, proc.stderr

    def scrub(self, text):
        for needle, repl in ((self.tmp, "<TMP>"), (self.sysroot, "<SYSROOT>"), (self.home, "<HOME>")):
            if needle:
                text = text.replace(needle, repl)
        return text

    def write(self, name, source):
        path = os.path.join(self.tmp, name)
        with open(path, "w", encoding="utf-8") as handle:
            handle.write(source)
        return name

    def diag(self, src, extra=(), env=None, emit_metadata=True, out=None):
        """Compile `src` and return rc plus structured diagnostics."""
        args = ["--edition", "2024", "--error-format=json"]
        if emit_metadata:
            args += ["--emit=metadata", "-o", "probe_out.rmeta"]
        elif out:
            args += ["-o", out]
        args += [src] + list(extra)
        rc, _stdout, stderr = self.raw(args, env=env)
        diags = []
        for line in stderr.splitlines():
            if not line.startswith("{"):
                continue
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                continue
            if obj.get("$message_type") != "diagnostic":
                continue
            code = (obj.get("code") or {}).get("code")
            spans = obj.get("spans", [])
            diags.append(
                {
                    "level": obj.get("level"),
                    "code": code,
                    "message": self.scrub(obj.get("message", "")),
                    "primary_lines": [s.get("line_start") for s in spans if s.get("is_primary")],
                    "primary_labels": [self.scrub(s.get("label") or "") for s in spans if s.get("is_primary")],
                    "secondary_labels": [
                        self.scrub(s.get("label") or "") for s in spans if not s.get("is_primary") and s.get("label")
                    ],
                    "children": [
                        {"level": c.get("level"), "message": self.scrub(c.get("message", ""))}
                        for c in obj.get("children", [])
                    ],
                }
            )
        argv = ["rustc"] + [self.scrub(a) for a in args]
        record = {"argv": argv, "rc": rc, "diagnostics": diags}
        if env:
            record["env"] = dict(env)
        return record

    def print_cfg(self, extra=(), env=None):
        rc, stdout, stderr = self.raw(["--print", "cfg"] + list(extra), env=env)
        errors = [self.scrub(l) for l in stderr.splitlines() if l.startswith("error")]
        return {
            "argv": ["rustc", "--print", "cfg"] + list(extra),
            "rc": rc,
            "lines": sorted(l for l in stdout.splitlines() if l),
            "errors": errors,
            **({"env": dict(env)} if env else {}),
        }

    def build_and_run(self, src, extra=(), env=None, binary="probe_bin"):
        rec = self.diag(src, extra=extra, env=env, emit_metadata=False, out=binary)
        rec["stdout"] = None
        if rec["rc"] == 0:
            proc = subprocess.run(
                [os.path.join(self.tmp, binary)], capture_output=True, text=True, timeout=TIMEOUT, cwd=self.tmp
            )
            self.subprocess_calls += 1
            rec["run_rc"] = proc.returncode
            rec["stdout"] = self.scrub(proc.stdout.strip())
            rec["kv"] = dict(tok.split("=", 1) for tok in proc.stdout.split() if "=" in tok)
        return rec


def lints(rec, code):
    return [d for d in rec["diagnostics"] if d["code"] == code]


def errors(rec):
    return [d for d in rec["diagnostics"] if d["level"] == "error" and d["code"]]


def first_with_code(rec, code):
    for d in rec["diagnostics"]:
        if d["code"] == code:
            return d
    return None


def notes(diagnostic):
    return [c["message"] for c in diagnostic["children"] if c["level"] == "note"]


# ----------------------------------------------------------------------------
# Part A: --check-cfg accumulation
# ----------------------------------------------------------------------------

# One predicate per source line; the lint verdict for each line is recovered
# from the primary span line of `unexpected_cfgs` diagnostics.
MODE_PREDICATES = [
    ("mode", "alpha"),
    ("mode", "beta"),
    ("mode", None),
    ("lvl", "x"),
    ("lvl", "y"),
    ("lvl", None),
    ("other", None),
]


def mode_source():
    lines = ['#![crate_type = "lib"]']
    for i, (name, value) in enumerate(MODE_PREDICATES):
        pred = name if value is None else '%s = "%s"' % (name, value)
        lines.append("#[cfg(%s)] pub fn f%d() {}" % (pred, i))
    return "\n".join(lines) + "\n"


def render_spec(spec):
    """spec: {'names': [...], 'values': [..]|'any'|None} or {'any_names': True}."""
    if spec.get("any_names"):
        return "cfg(any())"
    parts = list(spec["names"])
    values = spec.get("values")
    if values == "any":
        parts.append("values(any())")
    elif values is not None:
        parts.append("values(%s)" % ", ".join("none()" if v is None else '"%s"' % v for v in values))
    return "cfg(%s)" % ", ".join(parts)


def model_verdicts(specs):
    """Reference model of `parse_check_cfg` + the `unexpected_cfgs` decision.

    Mirrors the Lean definitions `parseCheckCfg` / `lint` shipped with this
    probe: per name the state is absent | Some(set) | Any; a spec joins into
    the state (`Some ∪ Some`, anything with `Any` is `Any`); `cfg(any())`
    switches name checking off; no spec at all switches the lint off.
    """
    if not specs:
        return ["ok"] * len(MODE_PREDICATES)
    exhaustive_names = True
    table = {}
    for spec in specs:
        if spec.get("any_names"):
            exhaustive_names = False
            continue
        values = spec.get("values")
        new = "any" if values == "any" else set([None] if values is None else values)
        for name in spec["names"]:
            old = table.get(name)
            if old is None:
                table[name] = "any" if new == "any" else set(new)
            elif old == "any" or new == "any":
                table[name] = "any"
            else:
                table[name] = old | new
    out = []
    for name, value in MODE_PREDICATES:
        entry = table.get(name)
        if entry is None:
            out.append("unexpected_name" if exhaustive_names else "ok")
        elif entry == "any" or value in entry:
            out.append("ok")
        else:
            out.append("unexpected_value")
    return out


def observed_verdicts(rec):
    verdict = ["ok"] * len(MODE_PREDICATES)
    for d in lints(rec, "unexpected_cfgs"):
        kind = "unexpected_name" if "condition name" in d["message"] else "unexpected_value"
        for line in d["primary_lines"]:
            verdict[line - 2] = kind  # line 1 is the crate attribute
    return verdict


def part_a(p):
    out = {}
    src = p.write("mode_probe.rs", mode_source())
    out["predicates"] = [n if v is None else '%s="%s"' % (n, v) for n, v in MODE_PREDICATES]

    def run_specs(specs, extra=()):
        args = []
        for spec in specs:
            args += ["--check-cfg", render_spec(spec)]
        rec = p.diag(src, extra=args + list(extra))
        return {
            "check_cfg": [render_spec(s) for s in specs],
            "rc": rec["rc"],
            "observed": observed_verdicts(rec),
            "model": model_verdicts(specs),
        }

    A = lambda names, values=None: {"names": names, "values": values}
    named = {
        "no_check_cfg": [],
        "empty_cfg": [{"names": [], "values": None, "empty": True}],
        "any_names": [{"any_names": True}],
        "only_alpha": [A(["mode"], ["alpha"])],
        "none_and_alpha": [A(["mode"], [None, "alpha"])],
        "bare_name_is_values_none": [A(["mode"])],
        "empty_values": [A(["mode"], [])],
        "union_two_flags": [A(["mode"], ["alpha"]), A(["mode"], ["beta", None])],
        "some_then_any": [A(["mode"], ["alpha"]), A(["mode"], "any")],
        "any_then_some": [A(["mode"], "any"), A(["mode"], ["alpha"])],
        "multi_name": [A(["mode", "lvl"], ["x"])],
        "any_names_plus_values": [{"any_names": True}, A(["mode"], ["alpha"])],
    }
    cases = {}
    for key, specs in named.items():
        if key == "empty_cfg":
            rec = p.diag(src, extra=["--check-cfg", "cfg()"])
            cases[key] = {
                "check_cfg": ["cfg()"],
                "rc": rec["rc"],
                "observed": observed_verdicts(rec),
                "model": ["unexpected_name"] * len(MODE_PREDICATES),
            }
        else:
            cases[key] = run_specs(specs)
    out["named_cases"] = cases

    # Permutation invariance: all orders of five specs touching two names.
    base = [
        A(["mode"], ["alpha"]),
        A(["mode"], ["beta"]),
        A(["lvl"], "any"),
        A(["lvl"], ["x"]),
        A(["mode"]),
    ]
    seen = {}
    disagreements = 0
    count = 0
    for perm in itertools.permutations(base):
        res = run_specs(list(perm))
        count += 1
        seen.setdefault(tuple(res["observed"]), 0)
        seen[tuple(res["observed"])] += 1
        if res["observed"] != res["model"]:
            disagreements += 1
    out["permutation_invariance"] = {
        "specs": [render_spec(s) for s in base],
        "orders_run": count,
        "distinct_verdict_vectors": len(seen),
        "verdict_vector": list(next(iter(seen))) if len(seen) == 1 else [list(k) for k in seen],
        "model_disagreements": disagreements,
    }

    # Seeded random differential test of the reference model against rustc.
    rng = random.Random(20261122)
    names = ["mode", "lvl", "other"]
    values = [None, "alpha", "beta", "x", "y"]
    trials = 80
    mismatches = []
    for _ in range(trials):
        specs = []
        for _ in range(rng.randint(1, 4)):
            roll = rng.random()
            if roll < 0.08:
                specs.append({"any_names": True})
                continue
            chosen = rng.sample(names, rng.randint(1, 2))
            if roll < 0.25:
                specs.append(A(chosen, "any"))
            elif roll < 0.35:
                specs.append(A(chosen))
            else:
                specs.append(A(chosen, rng.sample(values, rng.randint(0, 3))))
        res = run_specs(specs)
        if res["observed"] != res["model"]:
            mismatches.append(res)
    out["random_differential"] = {"seed": 20261122, "trials": trials, "mismatches": mismatches}

    # Well-known names under `--check-cfg=cfg()`.
    wk_names = [
        "miri", "clippy", "doc", "doctest", "rustfmt", "rust_analyzer", "test",
        "unix", "windows", "debug_assertions", "proc_macro", "target_has_atomic", "panic", "feature",
    ]
    wk_src = '#![crate_type = "lib"]\n' + "".join("#[cfg(%s)] pub fn w%d() {}\n" % (n, i) for i, n in enumerate(wk_names))
    wk = p.write("well_known.rs", wk_src)

    def per_name(rec):
        verdict = {n: "ok" for n in wk_names}
        for d in lints(rec, "unexpected_cfgs"):
            kind = "unexpected_name" if "condition name" in d["message"] else "unexpected_value"
            for line in d["primary_lines"]:
                verdict[wk_names[line - 2]] = kind
        return verdict

    rec = p.diag(wk, extra=["--check-cfg", "cfg()"])
    out["well_known_under_empty_cfg"] = {"rc": rec["rc"], "verdicts": per_name(rec)}
    rec = p.diag(wk)
    out["well_known_without_check_cfg"] = {"rc": rec["rc"], "verdicts": per_name(rec)}
    rec = p.diag(wk, extra=["--check-cfg", "cfg()", "-D", "unexpected_cfgs"])
    out["deny_unexpected_cfgs"] = {"rc": rec["rc"], "error_count": len([d for d in rec["diagnostics"] if d["code"] == "unexpected_cfgs" and d["level"] == "error"])}

    # A user spec for a well-known name: shadowing vs. union.
    shadow_preds = ["unix", "debug_assertions", 'panic = "abort"', 'panic = "zzz"', 'target_os = "linux"', 'target_os = "myos"']
    sh_src = '#![crate_type = "lib"]\n' + "".join("#[cfg(%s)] pub fn s%d() {}\n" % (pr, i) for i, pr in enumerate(shadow_preds))
    sh = p.write("shadow.rs", sh_src)

    def shadow_run(specs):
        args = []
        for s in specs:
            args += ["--check-cfg", s]
        rec = p.diag(sh, extra=args)
        verdict = {pr: "ok" for pr in shadow_preds}
        detail = {}
        for d in lints(rec, "unexpected_cfgs"):
            kind = "unexpected_name" if "condition name" in d["message"] else "unexpected_value"
            for line in d["primary_lines"]:
                verdict[shadow_preds[line - 2]] = kind
                if not shadow_preds[line - 2].startswith("target_os"):
                    detail[shadow_preds[line - 2]] = [m for m in notes(d) if m.startswith("expected values")]
        return {"check_cfg": specs, "rc": rec["rc"], "verdicts": verdict, "expected_values_notes": detail}

    out["well_known_user_interaction"] = {
        "baseline_empty_cfg": shadow_run(["cfg()"]),
        "user_values_on_bare_well_known_unix": shadow_run(['cfg(unix, values("x"))']),
        "user_values_on_bare_well_known_debug_assertions": shadow_run(['cfg(debug_assertions, values("x"))']),
        "user_values_on_valued_well_known_panic": shadow_run(['cfg(panic, values("zzz"))']),
        "user_values_on_valued_well_known_target_os": shadow_run(['cfg(target_os, values("myos"))']),
        "user_any_on_valued_well_known_panic": shadow_run(["cfg(panic, values(any()))"]),
    }
    return out


# ----------------------------------------------------------------------------
# Part B: builtin cfgs on the command line
# ----------------------------------------------------------------------------

CLI_CFGS = [
    "ub_checks", "overflow_checks", "contract_checks", "debug_assertions",
    'sanitize="address"', 'panic="abort"', 'panic="unwind"', 'panic="immediate-abort"',
    "unix", "windows", "proc_macro", 'target_feature="avx2"', 'target_os="linux"',
    'target_arch="x86_64"', 'target_family="unix"', 'target_pointer_width="64"',
    'target_has_atomic="128"', 'target_has_atomic_load_store="8"',
    'target_has_atomic_primitive_alignment="8"', "target_thread_local",
    'relocation_model="pic"', 'fmt_debug="full"',
    # not matched by the gate:
    "test", "miri", "clippy", "doc", "doctest", "rustfmt", "rust_analyzer",
    "panic", 'panic="zzz"', "target_os", "target_arch", "target_has_atomic",
    "target_has_atomic_load_store", 'overflow_checks="x"', 'feature="x"', "anneal_driver_test",
]

COHERENCE_SRC = """#![feature(cfg_ub_checks, core_intrinsics, cfg_overflow_checks)]
#![allow(internal_features)]
fn main() {
    let cfg_ub = cfg!(ub_checks);
    let intrinsic_ub = core::intrinsics::ub_checks();
    let cfg_overflow = cfg!(overflow_checks);
    let cfg_debug = cfg!(debug_assertions);
    let x: u8 = std::hint::black_box(255);
    std::panic::set_hook(Box::new(|_| {}));
    let add_panicked = std::panic::catch_unwind(|| x + std::hint::black_box(1)).is_err();
    println!(
        "cfg_ub_checks={cfg_ub} intrinsic_ub_checks={intrinsic_ub} cfg_overflow_checks={cfg_overflow} \\
         overflow_add_panicked={add_panicked} cfg_debug_assertions={cfg_debug}"
    );
}
"""


def part_b(p):
    out = {}
    empty = p.write("empty_lib.rs", '#![crate_type = "lib"]\npub fn f() {}\n')
    matrix = {}
    for cfg in CLI_CFGS:
        rec = p.diag(empty, extra=["--cfg", cfg])
        hit = first_with_code(rec, "explicit_builtin_cfgs_in_flags")
        matrix[cfg] = {
            "rc": rec["rc"],
            "message": hit["message"] if hit else None,
            "level": hit["level"] if hit else None,
            "controlled_by": next((m for m in notes(hit) if "controlled by" in m), None) if hit else None,
        }
    out["cli_cfg_matrix"] = matrix
    hit = first_with_code(p.diag(empty, extra=["--cfg", "ub_checks"]), "explicit_builtin_cfgs_in_flags")
    out["gate_diagnostic_children"] = hit["children"] if hit else None

    coh = p.write("coherence.rs", COHERENCE_SRC)
    off = ["-Zub-checks=no", "-Coverflow-checks=off", "-Cdebug-assertions=off"]
    spoof = ["--cfg", "ub_checks", "--cfg", "overflow_checks", "--cfg", "debug_assertions"]
    coh_allow = p.write(
        "coherence_allow.rs",
        COHERENCE_SRC.replace(
            "#![allow(internal_features)]", "#![allow(internal_features, explicit_builtin_cfgs_in_flags)]"
        ),
    )
    configs = {
        "baseline_default_flags": (coh, []),
        "baseline_all_checks_off": (coh, off),
        "baseline_all_checks_on": (coh, ["-Zub-checks=yes", "-Coverflow-checks=on", "-Cdebug-assertions=on"]),
        "spoof_at_default_lint_level": (coh, off + spoof),
        "spoof_with_A_lint": (coh, off + spoof + ["-A", "explicit_builtin_cfgs_in_flags"]),
        "spoof_with_W_lint": (coh, off + spoof + ["-W", "explicit_builtin_cfgs_in_flags"]),
        "spoof_with_cap_lints_allow": (coh, off + spoof + ["--cap-lints", "allow"]),
        "spoof_with_cap_lints_warn": (coh, off + spoof + ["--cap-lints", "warn"]),
        "spoof_with_in_source_allow": (coh_allow, off + spoof),
    }
    bypass = {}
    for key, (src, args) in configs.items():
        rec = p.build_and_run(src, extra=args)
        gate = lints(rec, "explicit_builtin_cfgs_in_flags")
        bypass[key] = {
            "argv": rec["argv"],
            "rc": rec["rc"],
            "gate_diagnostic_levels": sorted(set(d["level"] for d in gate)),
            "gate_diagnostic_count": len(gate),
            "program_output": rec.get("kv"),
        }
    out["lint_level_bypass"] = bypass

    pc = {}
    pc["panic_unwind"] = p.print_cfg(["-Cpanic=unwind"])
    pc["panic_abort"] = p.print_cfg(["-Cpanic=abort"])
    pc["panic_immediate_abort_without_unstable_options"] = p.print_cfg(["-Cpanic=immediate-abort"])
    pc["panic_immediate_abort"] = p.print_cfg(["-Zunstable-options", "-Cpanic=immediate-abort"])
    pc["sanitizer_address"] = p.print_cfg(["-Zsanitizer=address"])
    pc["sanitizer_address_leak"] = p.print_cfg(["-Zsanitizer=address,leak"])
    pc["sanitizer_kernel_address_x86_64_unknown_none"] = p.print_cfg(
        ["-Zsanitizer=kernel-address", "--target", "x86_64-unknown-none"]
    )
    pc["sanitizer_kernel_address_on_unsupported_host_target"] = p.print_cfg(["-Zsanitizer=kernel-address"])
    pc["sanitizer_hwaddress_aarch64_linux"] = p.print_cfg(
        ["-Zsanitizer=hwaddress", "--target", "aarch64-unknown-linux-gnu"]
    )
    pc["sanitizer_kernel_hwaddress_aarch64_none"] = p.print_cfg(
        ["-Zsanitizer=kernel-hwaddress", "--target", "aarch64-unknown-none"]
    )
    pc["ub_checks_off_in_print_mode"] = p.print_cfg(["-Zub-checks=no"])
    pc["spoofed_ub_checks_in_print_mode"] = p.print_cfg(["-Zub-checks=no", "--cfg", "ub_checks"])
    pc["bare_target_has_atomic_on_thumbv6m"] = p.print_cfg(["--target", "thumbv6m-none-eabi"])
    pc["bare_target_has_atomic_on_thumbv6m_spoofed"] = p.print_cfg(
        ["--target", "thumbv6m-none-eabi", "--cfg", "target_has_atomic"]
    )
    keep = ("panic", "sanitize", "ub_checks", "debug_assertions", "overflow_checks")
    bare = ("target_has_atomic", "target_has_atomic_load_store")
    for key, rec in pc.items():
        if key.startswith("bare_target_has_atomic"):
            rec["lines"] = [l for l in rec["lines"] if l in bare]
        else:
            rec["lines"] = [l for l in rec["lines"] if l.startswith(keep)]
    out["print_cfg"] = pc
    return out


# ----------------------------------------------------------------------------
# Part C: atomic cfgs and cfg predicates
# ----------------------------------------------------------------------------

ATOMIC_TARGETS = {
    "x86_64_unknown_linux_gnu": ["--target", "x86_64-unknown-linux-gnu"],
    "x86_64_unknown_linux_gnu_target_cpu_x86_64_v3": ["--target", "x86_64-unknown-linux-gnu", "-Ctarget-cpu=x86-64-v3"],
    "x86_64_unknown_linux_gnu_target_feature_cmpxchg16b": [
        "--target", "x86_64-unknown-linux-gnu", "-Ctarget-feature=+cmpxchg16b"
    ],
    "x86_64_apple_darwin": ["--target", "x86_64-apple-darwin"],
    "x86_64_pc_windows_msvc": ["--target", "x86_64-pc-windows-msvc"],
    "i686_unknown_linux_gnu": ["--target", "i686-unknown-linux-gnu"],
    "aarch64_unknown_linux_gnu": ["--target", "aarch64-unknown-linux-gnu"],
    "thumbv6m_none_eabi": ["--target", "thumbv6m-none-eabi"],
    "riscv32imc_unknown_none_elf": ["--target", "riscv32imc-unknown-none-elf"],
    "m68k_unknown_linux_gnu": ["--target", "m68k-unknown-linux-gnu"],
    "s390x_unknown_linux_gnu": ["--target", "s390x-unknown-linux-gnu"],
    "bpfel_unknown_none": ["--target", "bpfel-unknown-none"],
    "bpfel_unknown_none_target_cpu_v4": ["--target", "bpfel-unknown-none", "-Ctarget-cpu=v4"],
}

PREDICATE_SRC = """#![feature(cfg_target_compact, cfg_version, cfg_accessible)]
#[cfg_accessible(core::mem::size_of)]
const ACC_SIZE_OF: bool = true;
#[cfg_accessible(core::mem::no_such_item_zzz)]
compile_error!("cfg_accessible should have removed this item");
fn main() {
    let sel = core::cfg_select! {
        target_pointer_width = "64" => { "p64" }
        target_pointer_width = "32" => { "p32" }
        _ => { "other" }
    };
    let first = cfg_select! { true => { "first" } true => { "second" } _ => { "fallback" } };
    let compact = cfg!(target(os = "linux", arch = "x86_64"));
    let compact_neg = cfg!(target(os = "linux", arch = "aarch64"));
    let v_low = cfg!(version("1.90"));
    let v_high = cfg!(version("1.250"));
    let v_bogus = cfg!(version("not.a.version"));
    println!(
        "CFG_SELECT={sel} CFG_SELECT_FIRST_MATCH={first} COMPACT_TARGET={compact} COMPACT_TARGET_NEG={compact_neg} \\
         VERSION_1_90={v_low} VERSION_1_250={v_high} VERSION_BOGUS={v_bogus} ACCESSIBLE_SIZE_OF={ACC_SIZE_OF}"
    );
}
"""


def atomic_sets(lines):
    def vals(prefix):
        return sorted(l.split('"')[1] for l in lines if l.startswith(prefix + "="))

    return {
        "target_has_atomic": vals("target_has_atomic"),
        "target_has_atomic_load_store": vals("target_has_atomic_load_store"),
        "target_has_atomic_primitive_alignment": vals("target_has_atomic_primitive_alignment"),
        "bare_target_has_atomic": "target_has_atomic" in lines,
        "bare_target_has_atomic_load_store": "target_has_atomic_load_store" in lines,
        "target_feature_cmpxchg16b": 'target_feature="cmpxchg16b"' in lines,
    }


def part_c(p, skip_census):
    out = {}
    matrix = {}
    for key, args in ATOMIC_TARGETS.items():
        rec = p.print_cfg(args)
        matrix[key] = {"argv": rec["argv"], "rc": rec["rc"], "errors": rec["errors"], **atomic_sets(rec["lines"])}
    out["atomic_matrix"] = matrix

    nightly = p.print_cfg([])
    stable = p.print_cfg([], env={"RUSTC_BOOTSTRAP": "-1"})
    out["host_print_cfg_nightly_vs_forced_stable"] = {
        "env_for_forced_stable": {"RUSTC_BOOTSTRAP": "-1"},
        "rc": [nightly["rc"], stable["rc"]],
        "only_on_nightly": sorted(set(nightly["lines"]) - set(stable["lines"])),
        "only_on_forced_stable": sorted(set(stable["lines"]) - set(nightly["lines"])),
    }

    if not skip_census:
        rc, stdout, _ = p.raw(["--print", "target-list"])
        targets = stdout.split()
        census = {
            "targets": len(targets),
            "print_cfg_failures": [],
            "has_atomic_128": [],
            "cas_without_primitive_alignment": {},
            "load_store_without_cas": [],
            "no_atomics": [],
            "cas_superset_violations": [],
        }
        for target in targets:
            rec = p.print_cfg(["--target", target])
            if rec["rc"] != 0:
                census["print_cfg_failures"].append(target)
                continue
            s = atomic_sets(rec["lines"])
            cas, ls, pa = set(s["target_has_atomic"]), set(s["target_has_atomic_load_store"]), set(
                s["target_has_atomic_primitive_alignment"]
            )
            if "128" in cas:
                census["has_atomic_128"].append(target)
            for width in sorted(cas - pa):
                census["cas_without_primitive_alignment"].setdefault(width, []).append(target)
            if ls and not cas:
                census["load_store_without_cas"].append(target)
            if not ls:
                census["no_atomics"].append(target)
            if not (cas <= ls and pa <= ls):
                census["cas_superset_violations"].append(target)
        out["all_builtin_targets_census"] = census

    src = p.write("predicates.rs", PREDICATE_SRC)
    rec = p.build_and_run(src, binary="predicates_bin")
    out["predicates_with_feature_gates"] = {
        "rc": rec["rc"],
        "warnings": sorted(set(d["message"] for d in rec["diagnostics"] if d["level"] == "warning" and d["code"] is None and "emitted" not in d["message"]) | set(d["message"] for d in rec["diagnostics"] if d["level"] == "warning" and d["code"])),
        "program_output": rec.get("kv"),
    }
    nofeat = p.write("predicates_nofeature.rs", PREDICATE_SRC.split("\n", 1)[1])
    rec = p.diag(nofeat)
    by_msg = {}
    for d in rec["diagnostics"]:
        if d["code"] == "E0658":
            by_msg[d["message"]] = by_msg.get(d["message"], 0) + 1
    out["predicates_without_feature_gates"] = {"rc": rec["rc"], "E0658_messages": by_msg}

    sel = p.write(
        "cfg_select_only.rs",
        'fn main() { let s = cfg_select! { unix => { "unix" } _ => { "other" } }; println!("SELECTED={s}"); }\n',
    )
    rec_n = p.build_and_run(sel, binary="sel_n")
    rec_s = p.build_and_run(sel, env={"RUSTC_BOOTSTRAP": "-1"}, binary="sel_s")
    out["cfg_select_without_feature"] = {
        "nightly": {"rc": rec_n["rc"], "program_output": rec_n.get("kv")},
        "forced_stable": {"rc": rec_s["rc"], "program_output": rec_s.get("kv"), "env": {"RUSTC_BOOTSTRAP": "-1"}},
    }
    sel_lint = p.write(
        "cfg_select_lint.rs",
        '#![crate_type = "lib"]\npub const S: &str = cfg_select! { zzz_unknown => { "a" } _ => { "b" } };\n',
    )
    rec = p.diag(sel_lint, extra=["--check-cfg", "cfg()"])
    out["cfg_select_arms_are_check_cfg_linted"] = {
        "rc": rec["rc"],
        "unexpected_cfgs": [d["message"] for d in lints(rec, "unexpected_cfgs")],
    }
    return out


# ----------------------------------------------------------------------------
# Part D: #[diagnostic::*]
# ----------------------------------------------------------------------------

UNKNOWN_SRC = """#![crate_type = "lib"]
#[diagnostic::future_attr(anything = "goes")]
pub struct S;
#[diagnostic::on_move(message = "moved")]
pub struct M;
#[diagnostic::on_unimplemented(bogus_option = "x", message = "ok")]
pub trait T {}
#[diagnostic::do_not_recommend(with_args)]
impl T for S {}
#[diagnostic::do_not_recommend]
pub fn not_an_impl() {}
"""


def stacked_src(attrs):
    return (
        '#![crate_type = "lib"]\n'
        + "".join("#[diagnostic::on_unimplemented(%s)]\n" % a for a in attrs)
        + "pub trait Tr {}\npub fn need<T: Tr>(_: T) {}\npub fn call() { need(1u8); }\n"
    )


def e0277_summary(rec):
    d = first_with_code(rec, "E0277")
    if d is None:
        return None
    return {
        "message": d["message"],
        "primary_labels": d["primary_labels"],
        "notes": [m for m in notes(d) if not m.startswith("required by a bound")],
        "ignored_option_warnings": sorted(
            w["message"] for w in lints(rec, "malformed_diagnostic_attributes") if "is ignored due to previous definition" in w["message"]
        ),
    }


def dnr_src(dnr_inner, dnr_outer):
    mark = "#[diagnostic::do_not_recommend]\n"
    return (
        '#![crate_type = "lib"]\npub trait A {}\npub trait B {}\npub trait C {}\n'
        + (mark if dnr_inner else "")
        + "impl<T: A> B for T {}\n"
        + (mark if dnr_outer else "")
        + "impl<T: B> C for T {}\npub fn need_c<T: C>(_: T) {}\npub fn call() { need_c(1u8); }\n"
    )


ON_MOVE_SRC = """#![crate_type = "lib"]
#![feature(diagnostic_on_move)]
#[diagnostic::on_move(
    message = "MOVE_MSG Self=`{Self}` This=`{This}` this=`{this}` G=`{G}` Bad=`{BadArg}`",
    label = "MOVE_LBL",
    note = "MOVE_NOTE_1",
    note = "MOVE_NOTE_2"
)]
pub struct LinearToken<G>(pub G);
pub fn use_twice(tok: LinearToken<u32>) -> (LinearToken<u32>, LinearToken<u32>) {
    let a = tok;
    let b = tok;
    (a, b)
}
"""


def part_d(p):
    out = {}
    unk = p.write("unknown_attrs.rs", UNKNOWN_SRC)

    def lint_summary(rec):
        return sorted(
            "%s[%s]: %s" % (d["level"], d["code"], d["message"])
            for d in rec["diagnostics"]
            if d["code"] and d["code"].endswith("diagnostic_attributes")
        )

    rec = p.diag(unk)
    out["unknown_and_malformed_default_levels"] = {
        "rc": rec["rc"],
        "diagnostics": lint_summary(rec),
        "hard_errors": [d["code"] for d in errors(rec)],
        "feature_help": sorted(
            c["message"] for d in rec["diagnostics"] for c in d["children"] if c["level"] == "help" and "feature" in c["message"]
        ),
    }
    rec = p.diag(unk, env={"RUSTC_BOOTSTRAP": "-1"})
    out["unknown_and_malformed_forced_stable"] = {
        "env": {"RUSTC_BOOTSTRAP": "-1"},
        "rc": rec["rc"],
        "diagnostics": lint_summary(rec),
        "feature_help": sorted(
            c["message"] for d in rec["diagnostics"] for c in d["children"] if c["level"] == "help" and "feature" in c["message"]
        ),
    }
    rec = p.diag(unk, extra=["-D", "warnings"])
    out["unknown_and_malformed_deny_warnings"] = {"rc": rec["rc"], "diagnostics": lint_summary(rec)}
    rec = p.diag(unk, extra=["-A", "unknown_or_malformed_diagnostic_attributes"])
    out["unknown_and_malformed_allow_group"] = {"rc": rec["rc"], "diagnostics": lint_summary(rec)}

    first = 'message = "FIRST_MSG for `{Self}`", label = "FIRST_LBL", note = "NOTE_ONE"'
    second = 'message = "SECOND_MSG", label = "SECOND_LBL", note = "NOTE_TWO"'
    third = 'note = "NOTE_THREE"'
    stacked = {}
    orders = {
        "first_then_second": [first, second],
        "second_then_first": [second, first],
        "first_second_third": [first, second, third],
        "third_first_second": [third, first, second],
        "identical_note_twice": ['note = "SAME_NOTE"', 'note = "SAME_NOTE"'],
        "label_filled_by_later_attribute": ['note = "N0"', 'label = "LATER_LBL"', 'message = "LATER_MSG"'],
        "duplicates_inside_one_attribute": ['note = "N1", note = "N2", message = "M_A", message = "M_B"'],
        "only_malformed_option_then_real": ['bogus = "x"', first],
    }
    for key, attrs in orders.items():
        rec = p.diag(p.write("stacked_%s.rs" % key, stacked_src(attrs)))
        stacked[key] = {"attributes": attrs, "rc": rec["rc"], "E0277": e0277_summary(rec)}
    out["stacked_on_unimplemented"] = stacked

    alias = p.write(
        "trait_alias.rs",
        '#![crate_type = "lib"]\n#![feature(trait_alias)]\npub trait Base {}\n'
        '#[diagnostic::on_unimplemented(message = "ALIAS_CUSTOM_MSG", note = "ALIAS_NOTE")]\n'
        "pub trait MyAlias = Base;\npub fn need_alias<T: MyAlias>(_: T) {}\npub fn call_alias() { need_alias(7_u8); }\n",
    )
    rec = p.diag(alias)
    d = first_with_code(rec, "E0277")
    out["trait_alias_on_unimplemented"] = {
        "rc": rec["rc"],
        "misplaced_warnings": [w["message"] for w in lints(rec, "misplaced_diagnostic_attributes")],
        "E0277_message": d["message"] if d else None,
        "E0277_notes": notes(d) if d else None,
        "custom_text_used_in_E0277": bool(d) and ("ALIAS_CUSTOM_MSG" in d["message"] or "ALIAS_NOTE" in notes(d)),
    }

    dnr = {}
    for inner in (False, True):
        for outer in (False, True):
            src = p.write("dnr_%d%d.rs" % (inner, outer), dnr_src(inner, outer))
            entry = {"do_not_recommend_on_impl_B_for_A": inner, "do_not_recommend_on_impl_C_for_B": outer}
            for solver, extra in (("current_solver", []), ("next_solver", ["-Znext-solver"])):
                rec = p.diag(src, extra=extra)
                d = first_with_code(rec, "E0277")
                entry[solver] = {
                    "rc": rec["rc"],
                    "message": d["message"] if d else None,
                    "primary_labels": d["primary_labels"] if d else None,
                    "required_for_notes": [m for m in notes(d) if m.startswith("required for")] if d else None,
                }
            dnr["inner_%s_outer_%s" % (str(inner).lower(), str(outer).lower())] = entry
    out["do_not_recommend_chain"] = dnr

    mv = p.write("on_move.rs", ON_MOVE_SRC)
    rec = p.diag(mv)
    d = first_with_code(rec, "E0382")
    out["on_move_with_feature"] = {
        "rc": rec["rc"],
        "E0382_message": d["message"] if d else None,
        "primary_labels": d["primary_labels"] if d else None,
        "secondary_labels": d["secondary_labels"] if d else None,
        "notes": [m for m in notes(d) if m.startswith("MOVE_")] if d else None,
        "format_warnings": sorted(w["message"] for w in lints(rec, "malformed_diagnostic_format_literals")),
        "format_warning_help": sorted(
            set(c["message"] for w in lints(rec, "malformed_diagnostic_format_literals") for c in w["children"] if c["level"] == "help")
        ),
    }
    mv2 = p.write("on_move_ungated.rs", ON_MOVE_SRC.replace("#![feature(diagnostic_on_move)]\n", ""))
    rec = p.diag(mv2)
    d = first_with_code(rec, "E0382")
    out["on_move_without_feature"] = {
        "rc": rec["rc"],
        "E0382_message": d["message"] if d else None,
        "hard_error_codes": sorted(set(e["code"] for e in errors(rec))),
        "unknown_attribute_warnings": [w["message"] for w in lints(rec, "unknown_diagnostic_attributes")],
    }
    return out


# ----------------------------------------------------------------------------
# Checks
# ----------------------------------------------------------------------------

def build_checks(r):
    a, b, c, d = (r["part_a_check_cfg"], r["part_b_builtin_cfgs_on_cli"], r["part_c_atomics_and_predicates"], r["part_d_diagnostic_attributes"])
    inv = []

    def check(name, ok):
        inv.append({"check": name, "holds": bool(ok)})

    nc = a["named_cases"]
    check("A1 model == rustc on every named check-cfg case", all(v["observed"] == v["model"] for v in nc.values()))
    check("A2 values(any()) absorbs in both orders", nc["some_then_any"]["observed"] == nc["any_then_some"]["observed"] and nc["some_then_any"]["observed"][:3] == ["ok"] * 3)
    check("A3 two --check-cfg flags union their values", nc["union_two_flags"]["observed"][:3] == ["ok"] * 3)
    check("A4 cfg(name) alone expects only the bare form", nc["bare_name_is_values_none"]["observed"][:3] == ["unexpected_value", "unexpected_value", "ok"])
    check("A5 120 orders of five specs give one verdict vector", a["permutation_invariance"]["orders_run"] == 120 and a["permutation_invariance"]["distinct_verdict_vectors"] == 1 and a["permutation_invariance"]["model_disagreements"] == 0)
    check("A6 seeded random differential test has no mismatch", not a["random_differential"]["mismatches"])
    wk = a["well_known_under_empty_cfg"]["verdicts"]
    check("A7 tool cfgs miri/clippy/doc/doctest/rustfmt are well-known", all(wk[n] == "ok" for n in ("miri", "clippy", "doc", "doctest", "rustfmt")))
    check("A8 `test` is not well-known under --check-cfg=cfg()", wk["test"] == "unexpected_name")
    check("A9 no --check-cfg flag means no unexpected_cfgs lint", all(v == "ok" for v in a["well_known_without_check_cfg"]["verdicts"].values()))
    wu = a["well_known_user_interaction"]
    check("A10 user values on bare well-known name shadow the implicit none()", wu["user_values_on_bare_well_known_unix"]["verdicts"]["unix"] == "unexpected_value" and wu["baseline_empty_cfg"]["verdicts"]["unix"] == "ok")
    check("A11 user values on valued well-known name are unioned", wu["user_values_on_valued_well_known_panic"]["verdicts"]['panic = "zzz"'] == "ok" and wu["user_values_on_valued_well_known_panic"]["verdicts"]['panic = "abort"'] == "ok" and wu["baseline_empty_cfg"]["verdicts"]['panic = "zzz"'] == "unexpected_value")

    m = b["cli_cfg_matrix"]
    rejected = ["ub_checks", "overflow_checks", "contract_checks", "debug_assertions", 'sanitize="address"', 'panic="abort"', "unix", "windows", "proc_macro", 'target_feature="avx2"', 'target_has_atomic="128"']
    accepted = ["test", "miri", "clippy", "doc", "doctest", "rustfmt", "panic", 'panic="zzz"', "target_has_atomic", "target_has_atomic_load_store", 'overflow_checks="x"', 'feature="x"']
    check("B1 gated builtin cfgs are rejected at the default lint level", all(m[k]["rc"] != 0 and m[k]["level"] == "error" for k in rejected))
    check("B2 test, tool cfgs and unmatched shapes are accepted", all(m[k]["rc"] == 0 and m[k]["message"] is None for k in accepted))
    lb = b["lint_level_bypass"]
    for key in ("baseline_default_flags", "baseline_all_checks_off", "baseline_all_checks_on"):
        o = lb[key]["program_output"] or {}
        check("B3 %s: cfg view equals codegen view" % key, lb[key]["rc"] == 0 and o.get("cfg_ub_checks") == o.get("intrinsic_ub_checks") and o.get("cfg_overflow_checks") == o.get("overflow_add_panicked"))
    check("B4 spoof rejected at default level", lb["spoof_at_default_lint_level"]["rc"] != 0)
    for key in ("spoof_with_A_lint", "spoof_with_W_lint", "spoof_with_cap_lints_allow", "spoof_with_cap_lints_warn", "spoof_with_in_source_allow"):
        o = lb[key]["program_output"] or {}
        check("B5 %s: accepted and cfg(ub_checks) diverges from intrinsic" % key, lb[key]["rc"] == 0 and o.get("cfg_ub_checks") == "true" and o.get("intrinsic_ub_checks") == "false")
    pc = b["print_cfg"]
    check("B6 immediate-abort prints both panic values", pc["panic_immediate_abort"]["rc"] == 0 and {'panic="abort"', 'panic="immediate-abort"'} <= set(pc["panic_immediate_abort"]["lines"]))
    check("B7 kernel-address prints sanitize=\"address\"", pc["sanitizer_kernel_address_x86_64_unknown_none"]["rc"] == 0 and [l for l in pc["sanitizer_kernel_address_x86_64_unknown_none"]["lines"] if l.startswith("sanitize")] == ['sanitize="address"'])
    check("B9 --print cfg shows a spoofed ub_checks and reports nothing", pc["spoofed_ub_checks_in_print_mode"]["rc"] == 0 and "ub_checks" in pc["spoofed_ub_checks_in_print_mode"]["lines"] and not pc["spoofed_ub_checks_in_print_mode"]["errors"] and pc["ub_checks_off_in_print_mode"]["rc"] == 0 and "ub_checks" not in pc["ub_checks_off_in_print_mode"]["lines"])
    check("B8 bare target_has_atomic can be injected on a no-CAS target", "target_has_atomic" not in pc["bare_target_has_atomic_on_thumbv6m"]["lines"] and "target_has_atomic" in pc["bare_target_has_atomic_on_thumbv6m_spoofed"]["lines"])

    am = c["atomic_matrix"]
    check("C1 i686: CAS at 64 without primitive alignment at 64", "64" in am["i686_unknown_linux_gnu"]["target_has_atomic"] and "64" not in am["i686_unknown_linux_gnu"]["target_has_atomic_primitive_alignment"])
    for key in ("thumbv6m_none_eabi", "riscv32imc_unknown_none_elf"):
        check("C2 %s: load/store without CAS" % key, am[key]["target_has_atomic"] == [] and am[key]["target_has_atomic_load_store"] != [])
    for key in ("x86_64_unknown_linux_gnu", "x86_64_unknown_linux_gnu_target_cpu_x86_64_v3", "x86_64_unknown_linux_gnu_target_feature_cmpxchg16b"):
        check("C3 %s: no 128-bit atomic cfg" % key, "128" not in am[key]["target_has_atomic"])
    check("C4 x86-64-v3 enables cmpxchg16b without enabling atomic 128", am["x86_64_unknown_linux_gnu_target_cpu_x86_64_v3"]["target_feature_cmpxchg16b"])
    for key in ("x86_64_apple_darwin", "x86_64_pc_windows_msvc"):
        check("C5 %s: 128-bit atomic cfg present" % key, "128" in am[key]["target_has_atomic"])
    if "all_builtin_targets_census" in c:
        check("C6 census: CAS and primitive-alignment sets are subsets of load/store set", not c["all_builtin_targets_census"]["cas_superset_violations"] and not c["all_builtin_targets_census"]["print_cfg_failures"])
    po = c["predicates_with_feature_gates"]["program_output"] or {}
    check("C7 cfg_select!, cfg(target()), cfg(version()), cfg_accessible evaluate as expected", po == {"CFG_SELECT": po.get("CFG_SELECT"), "CFG_SELECT_FIRST_MATCH": "first", "COMPACT_TARGET": po.get("COMPACT_TARGET"), "COMPACT_TARGET_NEG": "false", "VERSION_1_90": "true", "VERSION_1_250": "false", "VERSION_BOGUS": "false", "ACCESSIBLE_SIZE_OF": "true"})
    check("C8 cfg_select! needs no feature gate, also in forced-stable mode", c["cfg_select_without_feature"]["nightly"]["rc"] == 0 and c["cfg_select_without_feature"]["forced_stable"]["rc"] == 0)
    check("C9 target(..), version(..), cfg_accessible are E0658 without their gates", c["predicates_without_feature_gates"]["rc"] != 0 and len(c["predicates_without_feature_gates"]["E0658_messages"]) == 3)

    u = d["unknown_and_malformed_default_levels"]
    check("D1 unknown/un-gated/malformed/misplaced diagnostic attributes compile with warnings only", u["rc"] == 0 and not u["hard_errors"] and len(u["diagnostics"]) == 5)
    check("D2 the same crate fails under -D warnings", d["unknown_and_malformed_deny_warnings"]["rc"] != 0)
    st = d["stacked_on_unimplemented"]
    check("D3 first attribute wins message and label; notes concatenate in order", st["first_then_second"]["E0277"]["message"] == "FIRST_MSG for `u8`" and st["first_then_second"]["E0277"]["primary_labels"] == ["FIRST_LBL"] and [n for n in st["first_then_second"]["E0277"]["notes"] if n.startswith("NOTE_")] == ["NOTE_ONE", "NOTE_TWO"])
    check("D4 swapping the attributes changes message, label and note order", st["second_then_first"]["E0277"]["message"] == "SECOND_MSG" and [n for n in st["second_then_first"]["E0277"]["notes"] if n.startswith("NOTE_")] == ["NOTE_TWO", "NOTE_ONE"])
    check("D5 identical notes are emitted twice", st["identical_note_twice"]["E0277"]["notes"].count("SAME_NOTE") == 2)
    check("D6 later attributes fill options the earlier ones left unset", st["label_filled_by_later_attribute"]["E0277"]["message"] == "LATER_MSG" and st["label_filled_by_later_attribute"]["E0277"]["primary_labels"] == ["LATER_LBL"])
    check("D7 on_unimplemented on a trait alias is ignored", d["trait_alias_on_unimplemented"]["custom_text_used_in_E0277"] is False and len(d["trait_alias_on_unimplemented"]["misplaced_warnings"]) == 1)
    ch = d["do_not_recommend_chain"]
    want = {
        "inner_false_outer_false": "the trait `A` is not implemented for `u8`",
        "inner_true_outer_false": "the trait `B` is not implemented for `u8`",
        "inner_false_outer_true": "the trait `C` is not implemented for `u8`",
        "inner_true_outer_true": "the trait `C` is not implemented for `u8`",
    }
    for solver in ("current_solver", "next_solver"):
        check("D8 %s: reported predicate is the head of the outermost do_not_recommend impl" % solver, all(ch[k][solver]["primary_labels"] == [v] for k, v in want.items()))
    mv = d["on_move_with_feature"]
    check("D9 on_move: {Self} is the bare item name and {G} the instantiated argument", mv["E0382_message"] is not None and "Self=`LinearToken`" in mv["E0382_message"] and "G=`u32`" in mv["E0382_message"] and mv["notes"] == ["MOVE_NOTE_1", "MOVE_NOTE_2"])
    check("D10 un-gated on_move is a warning, never E0658", d["on_move_without_feature"]["hard_error_codes"] == ["E0382"] and len(d["on_move_without_feature"]["unknown_attribute_warnings"]) == 1)

    disc = {
        "rust_analyzer_is_well_known": wk["rust_analyzer"] == "ok",
        "on_move_uppercase_This_is_substituted": mv["E0382_message"] is not None and "This=`LinearToken`" in mv["E0382_message"],
        "on_move_lowercase_this_is_substituted": mv["E0382_message"] is not None and "this=`LinearToken`" in mv["E0382_message"],
        "bpfel_default_cpu_load_store_widths": am["bpfel_unknown_none"]["target_has_atomic_load_store"],
        "bpfel_cpu_v4_load_store_widths": am["bpfel_unknown_none_target_cpu_v4"]["target_has_atomic_load_store"],
        "host_nightly_prints_emscripten_wasm_eh": "emscripten_wasm_eh" in c["host_print_cfg_nightly_vs_forced_stable"]["only_on_nightly"],
        "host_prints_target_has_threads": None,
    }
    return inv, disc


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--rustc", default=os.environ.get("RUSTC", "rustc"))
    ap.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "probe_results.json"))
    ap.add_argument("--skip-census", action="store_true", help="skip `--print cfg` over every builtin target")
    opts = ap.parse_args()

    with tempfile.TemporaryDirectory(prefix="check_cfg_probe_") as tmp:
        p = Probe(opts.rustc, tmp)
        rc, version, _ = p.raw(["-vV"])
        if rc != 0:
            print("cannot run rustc -vV", file=sys.stderr)
            return 2
        results = {
            "probe": "probe_check_cfg_and_diagnostic_attrs.py",
            "observed_at_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "rustc_version_verbose": version.strip().splitlines(),
            "part_a_check_cfg": part_a(p),
            "part_b_builtin_cfgs_on_cli": part_b(p),
            "part_c_atomics_and_predicates": part_c(p, opts.skip_census),
            "part_d_diagnostic_attributes": part_d(p),
        }
        nightly_lines = p.print_cfg([])["lines"]
        inv, disc = build_checks(results)
        disc["host_prints_target_has_threads"] = "target_has_threads" in nightly_lines
        results["invariant_checks"] = inv
        results["version_discriminators"] = disc
        results["subprocess_calls"] = p.subprocess_calls
        text = json.dumps(results, indent=1, sort_keys=True, ensure_ascii=False) + "\n"
        leaks = [needle for needle in (tmp, p.home, p.sysroot) if needle and needle in text]
    if leaks:
        print("refusing to write results containing local paths", file=sys.stderr)
        return 3
    with open(opts.out, "w", encoding="utf-8") as handle:
        handle.write(text)
    failed = [c["check"] for c in inv if not c["holds"]]
    print("%d subprocess calls; %d/%d invariant checks hold" % (results["subprocess_calls"], len(inv) - len(failed), len(inv)))
    for name in failed:
        print("FAILED: " + name)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
