#!/usr/bin/env python3
import os
import re
import json
import gzip
from collections import Counter, defaultdict

S1991 = "/tmp/rust-s1991"
OUT_DIR = "/tmp/run-probe"

def read_text(rel):
    with open(os.path.join(S1991, rel), "r", encoding="utf-8", errors="replace") as f:
        return f.read()

# Map suites to their CompiletestMode from bootstrap test.rs
SUITE_MODES = {
    "ui": "ui",
    "ui-fulldeps": "ui",
    "codegen-llvm": "codegen",
    "codegen-units": "codegen-units",
    "mir-opt": "mir-opt",
    "assembly-llvm": "assembly",
    "incremental": "incremental",
    "debuginfo": "debuginfo",
    "coverage": "coverage-map+coverage-run",
    "coverage-run-rustdoc": "coverage-run-rustdoc",
    "crashes": "crashes",
    "pretty": "pretty",
    "run-make": "run-make",
    "run-make-cargo": "run-make",
    "build-std": "run-make",
    "rustdoc-html": "rustdoc-html",
    "rustdoc-json": "rustdoc-json",
    "rustdoc-js": "rustdoc-js",
    "rustdoc-js-std": "rustdoc-js",
    "rustdoc-ui": "ui",
    "rustdoc-gui": "rustdoc-gui",
}

# Load GCC exclusion lists
gcc_excl_by_file = {}
for fn in [
    "failing-ui-tests.txt",
    "failing-ui-tests12.txt",
    "failing-ui-tests-without-128bit-integers.txt",
    "failing-run-make-tests.txt",
    "failing-lto-tests.txt",
    "failing-ice-tests.txt",
]:
    rel = f"compiler/rustc_codegen_gcc/tests/{fn}"
    for line in read_text(rel).splitlines():
        ls = line.strip()
        if ls and not ls.startswith("#"):
            gcc_excl_by_file.setdefault(ls, []).append(fn)

# Load Cranelift explicit rm exclusions
clif_sh = read_text("compiler/rustc_codegen_cranelift/scripts/test_rustc_tests.sh")
clif_rm_exact = {}
clif_rm_prefixes = []
curr_cat = "general"
for line in clif_sh.splitlines():
    ls = line.strip()
    if ls.startswith("# ") and not ls.startswith("# =="):
        curr_cat = ls[2:].strip()
    m = re.match(r"^rm\s+(-r\s+)?(tests/\S+)(?:\s+#\s*(.*))?$", ls)
    if m:
        is_dir, pat, comment = bool(m.group(1)), m.group(2).rstrip("/"), m.group(3) or ""
        if "*" in pat or is_dir or not pat.endswith(".rs"):
            clif_rm_prefixes.append((pat, curr_cat, comment))
        else:
            clif_rm_exact[pat] = (curr_cat, comment)

# Directive regex: //@ [rev] name: value  OR //@ name
DIRECTIVE_RE = re.compile(r"^\s*//@\s*(?:\[([^\]]+)\]\s*)?([a-zA-Z0-9_-]+)(?:\s*:\s*(.*)|\s+(.*))?$")
ERROR_ANNOT_RE = re.compile(r"//(?:\[[^\]]+\])?~")

suite_stats = {}
all_records = []
directive_freq = Counter()
only_freq = Counter()
ignore_freq = Counter()
needs_freq = Counter()
llvm_component_freq = Counter()

tests_root = os.path.join(S1991, "tests")
for suite in sorted(SUITE_MODES.keys()):
    sdir = os.path.join(tests_root, suite)
    if not os.path.isdir(sdir):
        continue
    test_files = []
    if suite in ("run-make", "run-make-cargo", "build-std"):
        # Each test directory contains rmake.rs or Makefile
        for root, dirs, files in os.walk(sdir):
            if "rmake.rs" in files or "Makefile" in files:
                entry = "rmake.rs" if "rmake.rs" in files else "Makefile"
                test_files.append(os.path.join(root, entry))
                dirs[:] = []  # don't recurse into subdirs of a run-make test
    else:
        for root, dirs, files in os.walk(sdir):
            # Skip auxiliary directories and subdirs marked with compiletest-ignore-dir
            dirs[:] = [d for d in sorted(dirs) if d != "auxiliary"]
            for fn in sorted(files):
                if suite == "rustdoc-gui":
                    if fn.endswith(".goml"):
                        test_files.append(os.path.join(root, fn))
                else:
                    if fn.endswith(".rs"):
                        test_files.append(os.path.join(root, fn))

    st = Counter()
    for tf in test_files:
        rel_path = os.path.relpath(tf, S1991)
        parent_dir = os.path.dirname(tf)
        stem = os.path.splitext(os.path.basename(tf))[0]
        try:
            with open(tf, "r", encoding="utf-8", errors="replace") as f:
                content = f.read()
        except Exception:
            content = ""

        lines = content.splitlines()
        directives = []
        revisions = []
        only_conds = []
        ignore_conds = []
        needs_conds = []
        compile_flags = []
        pass_mode = None
        fail_mode = None
        has_error_annots = bool(ERROR_ANNOT_RE.search(content))
        has_error_pattern = False
        has_should_fail = False
        has_llvm_args = "-Cllvm-args" in content or "-C llvm-args" in content
        has_lto = any(x in content for x in ["-Clto", "-C lto", "-Clinker-plugin-lto"])

        for line in lines:
            m = DIRECTIVE_RE.match(line)
            if m:
                rev, dname, colon_val, space_val = m.groups()
                val = (colon_val if colon_val is not None else space_val or "").strip()
                directives.append(dname)
                directive_freq[dname] += 1
                if dname == "revisions":
                    revisions.extend(val.split())
                elif dname.startswith("only-"):
                    only_conds.append(dname[5:] if not val else f"{dname[5:]}:{val}")
                    only_freq[dname] += 1
                elif dname.startswith("ignore-"):
                    ignore_conds.append(dname[7:] if not val else f"{dname[7:]}:{val}")
                    ignore_freq[dname] += 1
                elif dname.startswith("needs-"):
                    needs_conds.append(dname[6:] if not val else f"{dname[6:]}:{val}")
                    needs_freq[dname] += 1
                    if dname == "needs-llvm-components":
                        for comp in val.split():
                            llvm_component_freq[comp] += 1
                elif dname == "compile-flags":
                    compile_flags.append(val)
                elif dname in ("check-pass", "build-pass", "run-pass", "force-host"):
                    pass_mode = dname
                elif dname in ("check-fail", "build-fail", "run-fail", "run-crash"):
                    fail_mode = dname
                elif dname == "error-pattern":
                    has_error_pattern = True
                elif dname == "should-fail":
                    has_should_fail = True

        # Check companion files in same directory (for ui/mir-opt/incremental/etc.)
        has_stderr = False
        has_stdout = False
        has_fixed = False
        has_mir_dump = False
        if suite not in ("run-make", "run-make-cargo", "build-std"):
            try:
                siblings = os.listdir(parent_dir)
                for s in siblings:
                    if s == stem + ".stderr" or (s.startswith(stem + ".") and s.endswith(".stderr")):
                        has_stderr = True
                    elif s == stem + ".stdout" or (s.startswith(stem + ".") and s.endswith(".stdout")):
                        has_stdout = True
                    elif s == stem + ".fixed" or (s.startswith(stem + ".") and s.endswith(".fixed")):
                        has_fixed = True
                    elif s.startswith(stem + ".") and (".mir" in s or s.endswith(".diff")):
                        has_mir_dump = True
            except Exception:
                pass

        # Determine what the test observes and its pipeline classification
        observes = []
        if has_stderr or has_error_annots or has_error_pattern:
            observes.append("diagnostics")
        if has_fixed:
            observes.append("rustfix")
        if pass_mode == "run-pass" or fail_mode in ("run-fail", "run-crash") or has_stdout:
            observes.append("run-execution")
        if suite == "codegen-llvm":
            observes.append("llvm-ir-filecheck")
        elif suite == "assembly-llvm":
            observes.append("assembly-filecheck")
        elif suite == "mir-opt":
            observes.append("mir-dump")
        elif suite == "debuginfo":
            observes.append("debugger-output")
        elif suite == "incremental":
            observes.append("incremental-reuse")
        elif suite in ("coverage", "coverage-run-rustdoc"):
            observes.append("llvm-coverage")
        elif suite in ("run-make", "run-make-cargo", "build-std"):
            observes.append("custom-recipe")
        elif suite.startswith("rustdoc"):
            observes.append("rustdoc-output")
        elif suite == "codegen-units":
            observes.append("cgu-partitioning")
        elif suite == "pretty":
            observes.append("pretty-printer")
        elif suite == "crashes":
            observes.append("ice-reproducer")

        # Pipeline tier:
        # 1. "frontend-only": check-pass, or UI diagnostic/check-fail test that does not reach codegen (no build-pass/run-pass/build-fail/run-fail)
        # 2. "mir-only": mir-opt without codegen
        # 3. "llvm-specific": codegen-llvm, assembly-llvm (uses llvm-args/llvm-components), coverage, or explicitly requires -Cllvm-args / needs-llvm-components / LTO linker plugin
        # 4. "backend-codegen": exercises codegen/linking/execution across any backend (run-pass, build-pass, build-fail, run-fail, debuginfo, incremental, codegen-units, run-make not tied to LLVM)
        # 5. "rustdoc": rustdoc-* suites
        if suite.startswith("rustdoc"):
            tier = "rustdoc"
        elif suite == "mir-opt":
            tier = "mir-only"
        elif suite in ("codegen-llvm", "coverage", "coverage-run-rustdoc") or has_llvm_args or "needs-llvm-components" in directives:
            tier = "llvm-specific"
        elif suite == "assembly-llvm":
            tier = "llvm-or-asm-specific"
        elif suite in ("ui", "ui-fulldeps"):
            if pass_mode in ("run-pass", "build-pass") or fail_mode in ("build-fail", "run-fail", "run-crash"):
                tier = "backend-codegen"
            elif pass_mode == "check-pass" or has_error_annots or has_error_pattern or has_stderr:
                tier = "frontend-only"
            else:
                # Default in UI when no pass/fail directive and no //~ ERROR is build-pass!
                tier = "backend-codegen"
        elif suite in ("pretty",):
            tier = "frontend-only"
        elif suite == "crashes":
            if any("codegen" in cf or "-Z" in cf or "-C" in cf for cf in compile_flags):
                tier = "backend-or-frontend-ice"
            else:
                tier = "backend-or-frontend-ice"
        elif suite in ("run-make", "run-make-cargo", "build-std"):
            if any(k in content for k in ["llvm_", "llvm-", "FileCheck", "clang", "-Clto", "linker-plugin-lto"]):
                tier = "llvm-specific"
            else:
                tier = "backend-codegen"
        else:
            tier = "backend-codegen"

        # Check Cranelift exclusion
        clif_excl = None
        if rel_path in clif_rm_exact:
            clif_excl = f"explicit:{clif_rm_exact[rel_path][0]}"
        else:
            test_dir_rel = os.path.dirname(rel_path) if suite in ("run-make", "run-make-cargo", "build-std") else rel_path
            for pat, cat, _ in clif_rm_prefixes:
                if pat.endswith("*"):
                    if test_dir_rel.startswith(pat[:-1]):
                        clif_excl = f"explicit:{cat}"
                        break
                elif test_dir_rel == pat or test_dir_rel.startswith(pat + "/"):
                    clif_excl = f"explicit:{cat}"
                    break
        if not clif_excl:
            if has_should_fail and suite in ("codegen-units", "ui", "incremental"):
                clif_excl = "regex:should-fail"
            elif suite == "ui" and (has_error_annots or has_error_pattern or fail_mode in ("build-fail", "run-fail") or has_llvm_args):
                clif_excl = "regex:ui-error-or-fail-or-llvm-args"
            elif has_lto and suite in ("codegen-units", "ui", "incremental"):
                clif_excl = "regex:lto"
            elif any(c.startswith("backends:cranelift") or "cranelift" in c for c in ignore_conds):
                clif_excl = "directive:ignore-backends-cranelift"
            elif suite not in ("codegen-units", "run-make", "run-make-cargo", "ui", "incremental"):
                clif_excl = "suite-not-run-by-clif"

        # Check GCC exclusion
        gcc_excl = None
        test_key = os.path.dirname(rel_path) if suite in ("run-make", "run-make-cargo") else rel_path
        if test_key in gcc_excl_by_file:
            gcc_excl = ",".join(gcc_excl_by_file[test_key])
        elif suite == "ui":
            parts = rel_path.split("/")
            if len(parts) > 2 and parts[2] in ("abi", "extern", "proc-macro", "threads-sendsync"):
                gcc_excl = f"dir-excluded:{parts[2]}"
            elif has_lto and "-Clto=thin" not in content:
                gcc_excl = "filter:lto"
        elif suite not in ("ui", "run-make", "run-make-cargo"):
            gcc_excl = "suite-not-run-by-gcc"

        st["total"] += 1
        st[f"tier:{tier}"] += 1
        if pass_mode:
            st[f"pass:{pass_mode}"] += 1
        if fail_mode:
            st[f"fail:{fail_mode}"] += 1
        if revisions:
            st["has_revisions"] += 1
        if only_conds:
            st["has_only"] += 1
        if ignore_conds:
            st["has_ignore"] += 1
        if needs_conds:
            st["has_needs"] += 1
        if clif_excl:
            st[f"clif_excl:{clif_excl}"] += 1
        else:
            st["clif_kept"] += 1
        if gcc_excl:
            st[f"gcc_excl:{gcc_excl}"] += 1
        else:
            st["gcc_kept"] += 1

        all_records.append({
            "path": rel_path,
            "suite": suite,
            "mode": SUITE_MODES[suite],
            "tier": tier,
            "pass_mode": pass_mode,
            "fail_mode": fail_mode,
            "revisions": revisions,
            "observes": observes,
            "only": only_conds,
            "ignore": ignore_conds,
            "needs": needs_conds,
            "clif_status": clif_excl or "active",
            "gcc_status": gcc_excl or "active",
        })

    suite_stats[suite] = dict(st)
    print(f"Suite {suite:22s}: total={st['total']:5d} | frontend={st['tier:frontend-only']:5d} | backend={st['tier:backend-codegen']:5d} | llvm={st['tier:llvm-specific']+st['tier:llvm-or-asm-specific']:4d} | mir={st['tier:mir-only']:4d} | clif_kept={st['clif_kept']:5d} | gcc_kept={st['gcc_kept']:5d}")

print(f"\nTotal classified test files across 21 suites: {len(all_records)}")
with open(os.path.join(OUT_DIR, "test_classification_summary.json"), "w") as f:
    json.dump({
        "total_tests": len(all_records),
        "suite_stats": suite_stats,
        "top_directives": directive_freq.most_common(100),
        "top_only": only_freq.most_common(60),
        "top_ignore": ignore_freq.most_common(60),
        "top_needs": needs_freq.most_common(60),
        "llvm_components": llvm_component_freq.most_common(40),
    }, f, indent=2)
with gzip.open(os.path.join(OUT_DIR, "test_catalog.jsonl.gz"), "wt", encoding="utf-8") as gz:
    for r in all_records:
        gz.write(json.dumps(r, separators=(",", ":")) + "\n")
print("Saved test_classification_summary.json and test_catalog.jsonl.gz")
