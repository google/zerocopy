# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for the two-phase tripwire CI policy checker."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_phase0_tripwires as checker  # noqa: E402


CI_DIR = Path(__file__).resolve().parent
ANNEAL_ROOT = CI_DIR.parent
REPO_ROOT = ANNEAL_ROOT.parent
SCRIPT_PATH = CI_DIR / "check_phase0_tripwires.py"

BASE_TRIPWIRES_RS = """\
// Header placeholder
struct Phase0Tripwire {
    pub bug_id: &'static str,
}
macro_rules! PHASE0_TRIPWIRE {
    ($($t:tt)*) => {};
}

pub(crate) const SYNTHETIC_DEMO_TRIPWIRE: Phase0Tripwire = PHASE0_TRIPWIRE! {
    bug_id: "ITREE-DEMO-000000000001",
    issue: "selftest",
    owner: "anneal-maintainers",
    added_date: "2026-11-26",
    scope: "Synthetic selftest hook",
    rationale: "Proves fail-closed capture refusal without production impact",
    regression_test: "anneal/tests/rustc-capture/tests/phase0_demo.rs::demo_selftest",
    activation: TripwireActivation::SyntheticSelftestOnly { env_key: "K", env_value: "V" },
    predicate: TripwirePredicate::AnyBody,
};

// === PHASE 0 MUTABLE REGISTRY START ===
pub(crate) const ACTIVE_PHASE0_TRIPWIRES: &[Phase0Tripwire] = &[];
// === PHASE 0 MUTABLE REGISTRY END ===

#[cfg(test)]
mod tests {
    // Unit-test fixture block should not register as active production code.
    fn local_fixture() {
        let _x = PHASE0_TRIPWIRE! {
            bug_id: "ITREE-TEST-000000000002",
            issue: "https://github.com/google/zerocopy/issues/4095",
            owner: "tester",
            added_date: "2026-11-26",
            scope: "unit test",
            rationale: "unit test",
            regression_test: "anneal/tests/rustc-capture/tests/phase0_demo.rs::missing",
            activation: TripwireActivation::Always,
            predicate: TripwirePredicate::AnyBody,
        };
    }
}
"""

DEMO_TEST_RS = """\
#[test]
fn demo_selftest() {
    let (out, reason) = run_capture();
    assert_eq!(out.status.code(), Some(1));
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-DEMO-000000000001]"));
}
"""


def _git(cwd: Path, *args: str) -> str:
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env["GIT_CONFIG_GLOBAL"] = os.devnull
    env["GIT_CONFIG_SYSTEM"] = os.devnull
    env["GIT_CONFIG_NOSYSTEM"] = "1"
    env["GIT_TERMINAL_PROMPT"] = "0"
    env["LC_ALL"] = "C"
    res = subprocess.run(
        ["git", "-C", str(cwd), "-c", "commit.gpgsign=false", *args],
        capture_output=True,
        text=True,
        env=env,
        check=True,
    )
    return res.stdout.strip()


def _init_fixture_repo(root: Path) -> str:
    _git(root, "init", "-q")
    _git(root, "config", "user.name", "Fixture User")
    _git(root, "config", "user.email", "fixture@example.invalid")
    (root / "anneal/trusted/rustc-capture/src").mkdir(parents=True)
    (root / "anneal/trusted/audit/src").mkdir(parents=True)
    (root / "anneal/trusted/lean/Trusted/MirSemantics").mkdir(parents=True)
    (root / "anneal/tests/rustc-capture/tests").mkdir(parents=True)
    (root / "anneal/tests/itree_diff/tests").mkdir(parents=True)
    (root / "anneal/tests/audit/tests").mkdir(parents=True)
    (root / "anneal/ci").mkdir(parents=True)
    (root / "anneal/Cargo.toml").write_text(
        """\
[workspace]
resolver = "2"
members = [
    "trusted/audit",
    "trusted/rustc-capture",
    "tests/audit",
    "tests/itree_diff",
    "tests/rustc-capture",
]
""",
        encoding="utf-8",
    )
    for crate_rel, pkg_name in (
        ("anneal/tests/audit", "anneal-audit-tests"),
        ("anneal/tests/itree_diff", "anneal-itree-diff"),
        ("anneal/tests/rustc-capture", "anneal-rustc-capture-tests"),
    ):
        (root / crate_rel / "Cargo.toml").write_text(
            f'[package]\nname = "{pkg_name}"\nversion = "0.1.0"\nedition = "2024"\npublish = false\n',
            encoding="utf-8",
        )
    (root / checker.TRIPWIRES_REL).write_text(
        BASE_TRIPWIRES_RS, encoding="utf-8"
    )
    (root / "anneal/tests/rustc-capture/tests/phase0_demo.rs").write_text(
        DEMO_TEST_RS, encoding="utf-8"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "base")
    return _git(root, "rev-parse", "HEAD")


def _with_active_entries(entries_src: str) -> str:
    return BASE_TRIPWIRES_RS.replace(
        "pub(crate) const ACTIVE_PHASE0_TRIPWIRES: &[Phase0Tripwire] = &[];",
        "pub(crate) const ACTIVE_PHASE0_TRIPWIRES: &[Phase0Tripwire] = &[\n"
        f"{entries_src}\n];",
    )


class CheckPhase0TripwiresTests(unittest.TestCase):
    def test_live_repo_tree_passes_policy_checks(self):
        rep = checker.check_tree(REPO_ROOT)
        self.assertTrue(rep.ok, rep.errors)
        self.assertIsInstance(rep.active_production_tripwires, tuple)
        self.assertIn(
            "ITREE-DEMO-000000000001", rep.synthetic_selftest_tripwires
        )

    def test_valid_unified_namespaces_raw_strings_and_negative_tests(self):
        with tempfile.TemporaryDirectory(prefix="phase0-valid-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)
            rust_src = _with_active_entries(
                r"""    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-CAST-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4095",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: r#"Guard "raw" cast width"#,
        rationale: "Fail closed until Phase 1",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_reg.rs::refuse_cast",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::Body(|_, _, _| '"' == '"' && true),
    },
    PHASE0_TRIPWIRE! {
        bug_id: "DIFF-BORROW-abcdef012345",
        issue: "https://github.com/google/zerocopy/issues/4096",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Borrow aliasing guard",
        rationale: "Fail closed until Phase 1",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_reg.rs::refuse_diff",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "LMIRI-CAST-001122334455",
        issue: "https://github.com/google/zerocopy/issues/4098",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Lean-Miri correspondence cast gap",
        rationale: "Hold cast form fail-closed pending correspondence update",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_reg.rs::refuse_lmiri",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "MINIRUST-MOVE-aabbccddeeff",
        issue: "https://github.com/google/zerocopy/issues/4099",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "MiniRust operational edge guard",
        rationale: "Hold move variant fail-closed — pending MiniRust witness",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_reg.rs::refuse_minirust",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                """\
// PHASE0_TRIPWIRE(bug_id="RT-CODE_AND_PROOF_HACK-deadbeef1234", issue="https://github.com/google/zerocopy/issues/4097", owner="fixture-owner", added_date="2026-11-26", scope="Red-team PoC closure", rationale="Block unsound vector", regression_test="anneal/ci/test_phase0_rt.py::test_refuse_rt")
pub fn audit_stub() {}
""",
                encoding="utf-8",
            )
            (root / checker.TRIPWIRES_REL).write_text(rust_src, encoding="utf-8")
            parsed_entries, parsed_errs = checker.parse_rust_tripwires(rust_src)
            self.assertEqual(parsed_errs, [])
            minirust_entry = next(
                e
                for e in parsed_entries
                if e.bug_id == "MINIRUST-MOVE-aabbccddeeff"
            )
            self.assertIn("—", minirust_entry.rationale)
            (root / "anneal/tests/rustc-capture/tests/phase0_reg.rs").write_text(
                """\
#[test]
fn refuse_cast() {
    let (status, reason) = run_capture();
    assert_eq!(status, "unsupported");
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-CAST-0123456789ab]"));
}
#[test]
fn refuse_diff() {
    let (out, reason) = run_capture();
    assert_eq!(out.status.code(), Some(1));
    assert!(reason.contains("[PHASE0_TRIPWIRE:DIFF-BORROW-abcdef012345]"));
}
#[test]
fn refuse_lmiri() {
    let (res, msg) = run_capture();
    assert!(res.is_err());
    assert!(msg.contains("[PHASE0_TRIPWIRE:LMIRI-CAST-001122334455]"));
}
#[test]
fn refuse_minirust() {
    let (res, msg) = run_capture();
    assert!(res.is_err());
    assert!(msg.contains("[PHASE0_TRIPWIRE:MINIRUST-MOVE-aabbccddeeff]"));
}
""",
                encoding="utf-8",
            )
            (
                root / "anneal/ci/test_phase0_rt.py"
            ).write_text(
                """\
import unittest

class RegTests(unittest.TestCase):
    def test_refuse_rt(self):
        status, err = run_probe()
        self.assertIn(
            "[PHASE0_TRIPWIRE:RT-CODE_AND_PROOF_HACK-deadbeef1234]", err
        )
        self.assertEqual(status, "unsupported")
""",
                encoding="utf-8",
            )
            rep = checker.check_tree(root)
            self.assertTrue(rep.ok, rep.errors)
            self.assertEqual(
                set(rep.active_production_tripwires),
                {
                    "ITREE-CAST-0123456789ab",
                    "DIFF-BORROW-abcdef012345",
                    "RT-CODE_AND_PROOF_HACK-deadbeef1234",
                    "LMIRI-CAST-001122334455",
                    "MINIRUST-MOVE-aabbccddeeff",
                },
            )

    def test_malformed_metadata_missing_issue_and_stubs_fail_closed(self):
        with tempfile.TemporaryDirectory(prefix="phase0-bad-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)
            bad_src = _with_active_entries(
                """    // PHASE0_TRIPWIRE(bug_id="ITREE-STUB-000000000099") stub
    PHASE0_TRIPWIRE! {
        bug_id: "CORR-D17",
        issue: "invalid-issue-ref",
        owner: "",
        added_date: "2026-02-30",
        scope: "",
        rationale: "",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_demo.rs::missing_fn",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
            )
            (root / checker.TRIPWIRES_REL).write_text(bad_src, encoding="utf-8")
            rep = checker.check_tree(root)
            self.assertFalse(rep.ok)
            joined = "\n".join(rep.errors)
            self.assertIn("commented-out tripwire stub", joined)
            self.assertIn("invalid Phase-0 bug_id", joined)
            self.assertIn("public GitHub issue URL", joined)
            self.assertIn("missing owner", joined)
            self.assertIn("invalid calendar added_date", joined)
            self.assertIn("missing scope", joined)
            self.assertIn("missing rationale", joined)
            self.assertIn("missing Rust #[test] function `missing_fn`", joined)

    def test_rust_lexer_and_cfg_test_hardening_blocks_bypasses(self):
        with tempfile.TemporaryDirectory(prefix="phase0-spoof-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)

            # 1. Decoy #[cfg(test)] block before production code -> FAIL.
            decoy_cfg = BASE_TRIPWIRES_RS.replace(
                "// Header placeholder",
                "#[cfg(test)]\nmod decoy {}\n// Header placeholder",
            )
            (root / checker.TRIPWIRES_REL).write_text(
                decoy_cfg, encoding="utf-8"
            )
            rep_cfg = checker.check_tree(root)
            self.assertFalse(rep_cfg.ok)
            self.assertIn("multiple #[cfg(test)]", "\n".join(rep_cfg.errors))

            # 1b. Production items after a single #[cfg(test)] block -> FAIL.
            trailing_cfg = BASE_TRIPWIRES_RS + (
                "\npub(crate) const LATE: &[Phase0Tripwire] = &[];\n"
            )
            (root / checker.TRIPWIRES_REL).write_text(
                trailing_cfg, encoding="utf-8"
            )
            rep_trail = checker.check_tree(root)
            self.assertFalse(rep_trail.ok)
            self.assertIn(
                "production items cannot appear after #[cfg(test)]",
                "\n".join(rep_trail.errors),
            )

            # 2. Direct Phase0Tripwire struct literal -> FAIL.
            raw_struct = _with_active_entries(
                """    Phase0Tripwire {
        bug_id: "ITREE-RAW-0123456789ab",
    },"""
            )
            (root / checker.TRIPWIRES_REL).write_text(
                raw_struct, encoding="utf-8"
            )
            rep_raw = checker.check_tree(root)
            self.assertFalse(rep_raw.ok)
            self.assertIn(
                "direct Phase0Tripwire struct literal forbidden",
                "\n".join(rep_raw.errors),
            )

            # 2b. Second macro_rules! PHASE0_TRIPWIRE definition (brace or
            # bracket) -> FAIL.
            dup_macro = BASE_TRIPWIRES_RS + (
                "\nmacro_rules! PHASE0_TRIPWIRE [ ($($t:tt)*) => { "
                "Phase0Tripwire { bug_id: \"\" } }; ]\n"
            )
            (root / checker.TRIPWIRES_REL).write_text(
                dup_macro, encoding="utf-8"
            )
            rep_macro = checker.check_tree(root)
            self.assertFalse(rep_macro.ok)
            self.assertIn(
                "multiple macro_rules! PHASE0_TRIPWIRE",
                "\n".join(rep_macro.errors),
            )

            # 3. Ignored / should_panic / cfg-disabled / dead / docstring
            # / skipTest bypass attempts -> FAIL.
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-IGN-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4100",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard cfg_attr ignore spoof",
        rationale: "Ensure negative test is live",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_spoof.rs::ignored_rs",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-CFG-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4103",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard cfg(not(test)) spoof",
        rationale: "Ensure test cannot be disabled via cfg",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_spoof.rs::cfg_disabled_rs",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-PANIC-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4106",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard should_panic spoof",
        rationale: "Ensure should_panic cannot short-circuit test",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_spoof.rs::should_panic_rs",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-MODCFG-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4107",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard disabled mod spoof",
        rationale: "Ensure enclosing mod cfg cannot disable test",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_spoof.rs::mod_cfg_rs",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-FILECFG-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4108",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard file-level cfg(any()) spoof",
        rationale: "Ensure file cfg(any()) fails closed",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_filecfg.rs::file_cfg_rs",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "DIFF-CMT-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4102",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard unasserted string spoof",
        rationale: "Dead strings must not satisfy negative test check",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_spoof.rs::dead_string_rs",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
                ),
                encoding="utf-8",
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                """\
// PHASE0_TRIPWIRE(bug_id="RT-SKIP-0123456789ab", issue="https://github.com/google/zerocopy/issues/4101", owner="fixture-owner", added_date="2026-11-26", scope="skip py", rationale="live py test", regression_test="anneal/ci/test_phase0_skip.py::test_skipped_py")
// PHASE0_TRIPWIRE(bug_id="RT-SKIPCALL-0123456789ab", issue="https://github.com/google/zerocopy/issues/4109", owner="fixture-owner", added_date="2026-11-26", scope="skip call", rationale="no skipTest", regression_test="anneal/ci/test_phase0_skip.py::test_skip_call")
// PHASE0_TRIPWIRE(bug_id="RT-DOC-0123456789ab", issue="https://github.com/google/zerocopy/issues/4104", owner="fixture-owner", added_date="2026-11-26", scope="doc spoof", rationale="no docstrings", regression_test="anneal/ci/test_phase0_skip.py::test_docstring_only")
""",
                encoding="utf-8",
            )
            (
                root / "anneal/tests/rustc-capture/tests/phase0_spoof.rs"
            ).write_text(
                """\
#[test]
#[cfg_attr(all(), ignore)]
fn ignored_rs() {
    assert_eq!(status, "unsupported");
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-IGN-0123456789ab]"));
}

#[test]
#[cfg(not(test))]
fn cfg_disabled_rs() {
    assert_eq!(status, "unsupported");
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-CFG-0123456789ab]"));
}

#[test]
#[should_panic]
fn should_panic_rs() {
    assert_eq!(status, "unsupported");
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-PANIC-0123456789ab]"));
}

#[cfg(feature = "never_enabled")]
mod hidden {
    #[test]
    fn mod_cfg_rs() {
        assert_eq!(status, "unsupported");
        assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-MODCFG-0123456789ab]"));
    }
}

#[test]
fn dead_string_rs() {
    let _ = "[PHASE0_TRIPWIRE:DIFF-CMT-0123456789ab] unsupported";
    assert!(true);
}
""",
                encoding="utf-8",
            )
            (
                root / "anneal/tests/rustc-capture/tests/phase0_filecfg.rs"
            ).write_text(
                """\
#![cfg(any())]
#[test]
fn file_cfg_rs() {
    assert_eq!(status, "unsupported");
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-FILECFG-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            (
                root / "anneal/ci/test_phase0_skip.py"
            ).write_text(
                '''\
import unittest

class SkipTests(unittest.TestCase):
    @unittest.skip("bypass attempt")
    def test_skipped_py(self):
        self.assertIn("[PHASE0_TRIPWIRE:RT-SKIP-0123456789ab]", err)
        self.assertEqual(status, "unsupported")

    def test_skip_call(self):
        self.skipTest("runtime skip")
        self.assertIn("[PHASE0_TRIPWIRE:RT-SKIPCALL-0123456789ab]", err)
        self.assertEqual(status, "unsupported")

    def test_docstring_only(self):
        """[PHASE0_TRIPWIRE:RT-DOC-0123456789ab] assertIn unsupported"""
        _ = "[PHASE0_TRIPWIRE:RT-DOC-0123456789ab] unsupported"
        self.assertTrue(True)
''',
                encoding="utf-8",
            )
            rep_spoof = checker.check_tree(root)
            self.assertFalse(rep_spoof.ok)
            spoof_err = "\n".join(rep_spoof.errors)
            self.assertIn("carries ignore/cfg_attr ignore", spoof_err)
            self.assertIn("carries conditional #[cfg(not(test))]", spoof_err)
            self.assertIn("carries #[should_panic]", spoof_err)
            self.assertIn("enclosing module disabled via", spoof_err)
            self.assertIn("file disabled via #![cfg(any())]", spoof_err)
            self.assertIn("must not be skipped", spoof_err)
            self.assertIn("must not call skipTest", spoof_err)
            self.assertIn("RT-DOC-0123456789ab", spoof_err)
            self.assertIn("DIFF-CMT-0123456789ab", spoof_err)

    def test_phase0_diff_isolation_reads_git_revs_and_rejects_core_or_scope_tamper(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-diff-") as tmp:
            root = Path(tmp)
            base = _init_fixture_repo(root)

            # Add an active tripwire + dedicated test cleanly.
            phase0_rs = _with_active_entries(
                """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-MEM-112233445566",
        issue: "https://github.com/google/zerocopy/issues/4095",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard unaligned write",
        rationale: "Refuse until Step fix lands",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_mem.rs::refuse_mem_bug",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
            )
            (root / checker.TRIPWIRES_REL).write_text(
                phase0_rs, encoding="utf-8"
            )
            (
                root / "anneal/tests/rustc-capture/tests/phase0_mem.rs"
            ).write_text(
                """\
#[test]
fn refuse_mem_bug() {
    let (out, failure, reason) = run_capture();
    assert_eq!(out.status.code(), Some(1));
    assert_eq!(failure["status"], "unsupported");
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-MEM-112233445566]"));
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "phase0")
            head = _git(root, "rev-parse", "HEAD")

            # Uncommitted working tree edits must not mask Git rev checks.
            (root / "anneal/trusted/rustc-capture/src/extract.rs").write_text(
                "// dirty working tree edit\n", encoding="utf-8"
            )
            rep_ok = checker.check_phase0_diff(root, base=base, head=head)
            self.assertTrue(rep_ok.ok, rep_ok.errors)
            self.assertTrue(rep_ok.isolated_tripwire_surface)
            self.assertFalse(rep_ok.requires_full_semantic_review)

            # Committing extract.rs change breaks isolation fail-closed.
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "tcb tamper")
            bad_tcb = _git(root, "rev-parse", "HEAD")
            rep_tcb = checker.check_phase0_diff(root, base=base, head=bad_tcb)
            self.assertFalse(rep_tcb.ok)
            self.assertIn("outside isolated Phase-0", "\n".join(rep_tcb.errors))

            # Reverting extract.rs and tampering with immutable tripwires.rs
            # core -> FAIL.
            (root / "anneal/trusted/rustc-capture/src/extract.rs").unlink()
            (root / checker.TRIPWIRES_REL).write_text(
                phase0_rs.replace("// Header placeholder", "// Mutated core!"),
                encoding="utf-8",
            )
            _git(root, "add", "-A")
            _git(root, "commit", "-q", "-m", "core tamper")
            bad_core = _git(root, "rev-parse", "HEAD")
            rep_core = checker.check_phase0_diff(root, base=base, head=bad_core)
            self.assertFalse(rep_core.ok)
            self.assertIn(
                "immutable harness code above", "\n".join(rep_core.errors)
            )

            # Deleting mutable-registry marker -> FAIL.
            (root / checker.TRIPWIRES_REL).write_text(
                phase0_rs.replace(checker.MUTABLE_START_MARKER, "// removed"),
                encoding="utf-8",
            )
            _git(root, "add", "-A")
            _git(root, "commit", "-q", "-m", "marker tamper")
            bad_marker = _git(root, "rev-parse", "HEAD")
            rep_marker = checker.check_phase0_diff(
                root, base=base, head=bad_marker
            )
            self.assertFalse(rep_marker.ok)
            self.assertIn(
                "missing or malformed mutable-registry markers",
                "\n".join(rep_marker.errors),
            )

            # Pointing regression_test to boundary_audit.rs -> FAIL.
            (root / checker.TRIPWIRES_REL).write_text(
                phase0_rs.replace(
                    "anneal/tests/rustc-capture/tests/phase0_mem.rs::refuse_mem_bug",
                    "anneal/tests/audit/tests/boundary_audit.rs::hijack",
                ),
                encoding="utf-8",
            )
            (root / "anneal/tests/audit/tests/boundary_audit.rs").write_text(
                """\
#[test]
fn hijack() {
    assert_eq!(status, "unsupported");
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-MEM-112233445566]"));
}
""",
                encoding="utf-8",
            )
            _git(root, "add", "-A")
            _git(root, "commit", "-q", "-m", "audit hijack")
            bad_scope = _git(root, "rev-parse", "HEAD")
            rep_scope = checker.check_phase0_diff(
                root, base=base, head=bad_scope
            )
            self.assertFalse(rep_scope.ok)
            self.assertIn(
                "dedicated *phase0*/*tripwire* file", "\n".join(rep_scope.errors)
            )

    def test_phase0_runtime_lean_fallback_requires_opt_in_and_semantic_review(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-lean-") as tmp:
            root = Path(tmp)
            base = _init_fixture_repo(root)
            step_path = (
                root / "anneal/trusted/lean/Trusted/MirSemantics/Step.lean"
            )
            step_path.write_text(
                """\
namespace Trusted.MirSemantics
-- PHASE0_TRIPWIRE(bug_id="LMIRI-OPS-aabbccddeeff", issue="https://github.com/google/zerocopy/issues/4105", owner="fixture-owner", added_date="2026-11-26", scope="runtime guard", rationale="Static overapprox too broad", regression_test="anneal/tests/itree_diff/tests/phase0_rt.rs::rt_guard")
def guard := StepResult.fault .unsupported
def evalStep := guard
end Trusted.MirSemantics
""",
                encoding="utf-8",
            )
            (root / "anneal/tests/itree_diff/tests/phase0_rt.rs").write_text(
                """\
#[test]
fn rt_guard() {
    // FaultKind.unsupported has no string payload; tag bug ID in assert.
    let step_fault = run_lean_step();
    assert_eq!(
        step_fault,
        Some(FaultKind::Unsupported),
        "expected Runbook B Phase-0 refusal for LMIRI-OPS-aabbccddeeff"
    );
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "lean runtime tripwire")
            head = _git(root, "rev-parse", "HEAD")

            # Advance base on an unrelated commit to test merge-base diff.
            _git(root, "checkout", "-q", "-b", "main-adv", base)
            (root / "anneal/README.md").write_text("# advanced\n", encoding="utf-8")
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "main advanced")
            adv_base = _git(root, "rev-parse", "HEAD")
            _git(root, "checkout", "-q", head)

            rep_strict = checker.check_phase0_diff(
                root, base=adv_base, head=head
            )
            self.assertFalse(rep_strict.ok)

            rep_opt = checker.check_phase0_diff(
                root,
                base=adv_base,
                head=head,
                allow_runtime_semantics_fallback=True,
            )
            self.assertTrue(rep_opt.ok, rep_opt.errors)
            self.assertFalse(rep_opt.isolated_tripwire_surface)
            self.assertTrue(rep_opt.requires_full_semantic_review)

            # Phase-1 removal of runtime fallback must flip off Unsupported.
            step_path.write_text("-- fixed operational rule\n", encoding="utf-8")
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "bad runtime phase1")
            bad_rt_p1 = _git(root, "rev-parse", "HEAD")
            rep_rt_unflipped = checker.check_phase1_cleanup(
                root, base=head, head=bad_rt_p1
            )
            self.assertFalse(rep_rt_unflipped.ok)
            self.assertIn(
                "must flip from unsupported-fault refusal",
                "\n".join(rep_rt_unflipped.errors),
            )

            (root / "anneal/tests/itree_diff/tests/phase0_rt.rs").write_text(
                """\
#[test]
fn rt_guard() {
    assert!(matches_miri_fault_ub("LMIRI-OPS-aabbccddeeff"));
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "good runtime phase1")
            good_rt_p1 = _git(root, "rev-parse", "HEAD")
            rep_rt_good = checker.check_phase1_cleanup(
                root, base=head, head=good_rt_p1
            )
            self.assertTrue(rep_rt_good.ok, rep_rt_good.errors)

    def test_phase1_cleanup_enforces_recursive_deletion_and_flipped_test(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase1-clean-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)
            phase0_rs = _with_active_entries(
                """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-MEM-112233445566",
        issue: "https://github.com/google/zerocopy/issues/4095",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard unaligned write",
        rationale: "Refuse until Step fix lands",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_mem.rs::refuse_mem_bug",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
            )
            test_file = root / "anneal/tests/rustc-capture/tests/phase0_mem.rs"
            test_file.write_text(
                """\
#[test]
fn refuse_mem_bug() {
    let (out, reason) = run_capture();
    assert_eq!(out.status.code(), Some(1));
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-MEM-112233445566]"));
}
""",
                encoding="utf-8",
            )
            (root / checker.TRIPWIRES_REL).write_text(
                phase0_rs, encoding="utf-8"
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "phase0")
            phase0_sha = _git(root, "rev-parse", "HEAD")

            # Remove tripwire WITHOUT flipping test -> FAIL.
            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS, encoding="utf-8"
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "incomplete phase1")
            bad_p1 = _git(root, "rev-parse", "HEAD")
            rep_unflipped = checker.check_phase1_cleanup(
                root, base=phase0_sha, head=bad_p1
            )
            self.assertFalse(rep_unflipped.ok)
            self.assertIn("must flip", "\n".join(rep_unflipped.errors))

            # Flip regression test to positive / FaultUb parity -> PASS.
            test_file.write_text(
                """\
#[test]
fn refuse_mem_bug() {
    assert!(captures_cleanly_and_matches_miri_fault_ub());
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "complete phase1")
            good_p1 = _git(root, "rev-parse", "HEAD")
            rep_good = checker.check_phase1_cleanup(
                root, base=phase0_sha, head=good_p1
            )
            self.assertTrue(rep_good.ok, rep_good.errors)

            # Residual bug ID committed inside another trusted crate -> FAIL.
            (root / "anneal/trusted/audit/src/guard.rs").write_text(
                "// leftover ITREE-MEM-112233445566 reference\n",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "leftover trusted ref")
            residual_p1 = _git(root, "rev-parse", "HEAD")
            rep_stub = checker.check_phase1_cleanup(
                root, base=phase0_sha, head=residual_p1
            )
            self.assertFalse(rep_stub.ok)
            self.assertIn(
                "residual reference remains in anneal/trusted/audit/src/guard.rs",
                "\n".join(rep_stub.errors),
            )

    def test_known_bugs_alignment_validates_mitigated_phase0_and_fixed(self):
        with tempfile.TemporaryDirectory(prefix="phase0-bugs-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)
            bugs_json = root / "known_bugs.json"
            bugs_json.write_text(
                json.dumps(
                    [
                        {
                            "bug_id": "RT-CODE_AND_PROOF_HACK-001122334455",
                            "status": "needs_human_review",
                        },
                        {
                            "bug_id": "LMIRI-CAST-0123456789ab",
                            "status": "mitigated_phase0",
                        },
                        {
                            "bug_id": "MINIRUST-MOVE-abcdef012345",
                            "status": "fixed",
                            "fixed_sha": "deadbeef12345678",
                        },
                    ]
                ),
                encoding="utf-8",
            )
            rep_warn = checker.check_tree(root, known_bugs_path=bugs_json)
            self.assertTrue(rep_warn.ok, rep_warn.errors)
            self.assertTrue(
                any("mitigated_phase0" in w for w in rep_warn.warnings)
            )

            rep_strict = checker.check_tree(
                root, known_bugs_path=bugs_json, strict_mitigated_link=True
            )
            self.assertFalse(rep_strict.ok)

            # fixed without fixed_sha must fail closed.
            bugs_json.write_text(
                json.dumps(
                    [
                        {
                            "bug_id": "RT-PROOF_HACK-abcdef012345",
                            "status": "fixed",
                        }
                    ]
                ),
                encoding="utf-8",
            )
            rep_bad_fix = checker.check_tree(root, known_bugs_path=bugs_json)
            self.assertFalse(rep_bad_fix.ok)
            self.assertIn("fixed_sha", "\n".join(rep_bad_fix.errors))

            # Both 1-record and multi-record JSONL files parse cleanly.
            bugs_jsonl = root / "known_bugs.jsonl"
            bugs_jsonl.write_text(
                json.dumps(
                    {
                        "bug_id": "LMIRI-CAST-0123456789ab",
                        "status": "mitigated_phase0",
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            rep_single_jsonl = checker.check_tree(
                root, known_bugs_path=bugs_jsonl
            )
            self.assertTrue(rep_single_jsonl.ok, rep_single_jsonl.errors)
            self.assertTrue(
                any("mitigated_phase0" in w for w in rep_single_jsonl.warnings)
            )

            # A single-record JSONL resolved row must drive phase1-cleanup.
            resolved_jsonl = root / "resolved_single.jsonl"
            resolved_jsonl.write_text(
                json.dumps(
                    {
                        "bug_id": "RT-PROOF_HACK-abcdef012345",
                        "status": "fixed",
                        "fixed_sha": "deadbeef12345678",
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            rep_single_jsonl_p1 = checker.check_phase1_cleanup(
                root, known_bugs_path=resolved_jsonl
            )
            self.assertFalse(rep_single_jsonl_p1.ok)
            self.assertIn(
                "RT-PROOF_HACK-abcdef012345",
                "\n".join(rep_single_jsonl_p1.errors),
            )

            # Empty JSONL summary works; malformed envelope fails.
            bugs_jsonl.write_text(
                json.dumps({"known_bugs": []}) + "\n", encoding="utf-8"
            )
            rep_empty_env = checker.check_tree(root, known_bugs_path=bugs_jsonl)
            self.assertTrue(rep_empty_env.ok, rep_empty_env.errors)

            bugs_jsonl.write_text(
                json.dumps({"known_bugs": "bad"}) + "\n", encoding="utf-8"
            )
            rep_bad_env = checker.check_tree(root, known_bugs_path=bugs_jsonl)
            self.assertFalse(rep_bad_env.ok)

            # Multi-record JSONL parses all lines as well.
            bugs_jsonl.write_text(
                "\n".join(
                    [
                        json.dumps(
                            {
                                "bug_id": "LMIRI-CAST-0123456789ab",
                                "status": "mitigated_phase0",
                            }
                        ),
                        json.dumps(
                            {
                                "bug_id": "MINIRUST-MOVE-abcdef012345",
                                "status": "fixed",
                                "fixed_sha": "deadbeef12345678",
                            }
                        ),
                    ]
                )
                + "\n",
                encoding="utf-8",
            )
            rep_multi_jsonl = checker.check_tree(
                root, known_bugs_path=bugs_jsonl
            )
            self.assertTrue(rep_multi_jsonl.ok, rep_multi_jsonl.errors)

    def test_rejects_unused_standalone_tripwire_and_dead_test_assertions(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-dead-ast-") as tmp:
            root = Path(tmp)
            base = _init_fixture_repo(root)

            # 1. Unused standalone constant outside slice -> FAIL.
            unused_const_rs = BASE_TRIPWIRES_RS.replace(
                "// === PHASE 0 MUTABLE REGISTRY START ===",
                """pub(crate) const UNUSED_BYPASS: Phase0Tripwire = PHASE0_TRIPWIRE! {
    bug_id: "ITREE-UNUSED-0123456789ab",
    issue: "https://github.com/google/zerocopy/issues/4095",
    owner: "fixture-owner",
    added_date: "2026-11-26",
    scope: "Never wired into ACTIVE_PHASE0_TRIPWIRES",
    rationale: "Unused standalone constant bypass test",
    regression_test: "anneal/tests/rustc-capture/tests/phase0_demo.rs::demo_selftest",
    activation: TripwireActivation::Always,
    predicate: TripwirePredicate::AnyBody,
};

// === PHASE 0 MUTABLE REGISTRY START ===""",
            )
            (root / checker.TRIPWIRES_REL).write_text(
                unused_const_rs, encoding="utf-8"
            )
            rep_unused = checker.check_tree(root)
            self.assertFalse(rep_unused.ok)
            self.assertIn(
                "outside ACTIVE_PHASE0_TRIPWIRES is forbidden",
                "\n".join(rep_unused.errors),
            )

            # 2. Assertions inside dead `if False:`, nested Python helper, or
            # dead Rust `if false` / local `macro_rules!` / nested `fn` -> FAIL.
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-DEADRS-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4112",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard unreachable Rust if false/macro/helper",
        rationale: "Unreached Rust assertions must fail closed",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_dead.rs::dead_rust_assertions",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
                ),
                encoding="utf-8",
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                """\
// PHASE0_TRIPWIRE(bug_id="RT-DEADPY-0123456789ab", issue="https://github.com/google/zerocopy/issues/4110", owner="fixture-owner", added_date="2026-11-26", scope="dead branch", rationale="dead branch fails", regression_test="anneal/ci/test_phase0_dead.py::test_dead_branch_py")
// PHASE0_TRIPWIRE(bug_id="RT-NESTPY-0123456789ab", issue="https://github.com/google/zerocopy/issues/4111", owner="fixture-owner", added_date="2026-11-26", scope="nested def", rationale="nested helper fails", regression_test="anneal/ci/test_phase0_dead.py::test_uncalled_helper_py")
""",
                encoding="utf-8",
            )
            (
                root / "anneal/ci/test_phase0_dead.py"
            ).write_text(
                """\
import unittest

class DeadPyTests(unittest.TestCase):
    def test_dead_branch_py(self):
        status, err = run_probe()
        if False:
            self.assertIn("[PHASE0_TRIPWIRE:RT-DEADPY-0123456789ab]", err)
            self.assertEqual(status, "unsupported")
        self.assertTrue(True)

    def test_uncalled_helper_py(self):
        status, err = run_probe()
        def _unused_helper():
            self.assertIn("[PHASE0_TRIPWIRE:RT-NESTPY-0123456789ab]", err)
            self.assertEqual(status, "unsupported")
        self.assertTrue(True)
""",
                encoding="utf-8",
            )
            (root / "anneal/tests/rustc-capture/tests/phase0_dead.rs").write_text(
                """\
#[test]
fn dead_rust_assertions() {
    let (status, reason) = run_capture();
    if false {
        assert_eq!(status, "unsupported");
        assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-DEADRS-0123456789ab]"));
    }
    macro_rules! _unused_assert {
        () => {
            assert_eq!(status, "unsupported");
            assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-DEADRS-0123456789ab]"));
        };
    }
    fn _uncalled_helper(reason: &str, status: &str) {
        assert_eq!(status, "unsupported");
        assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-DEADRS-0123456789ab]"));
    }
    assert!(true);
}
""",
                encoding="utf-8",
            )
            rep_dead = checker.check_tree(root)
            self.assertFalse(rep_dead.ok)
            dead_err = "\n".join(rep_dead.errors)
            self.assertIn("RT-DEADPY-0123456789ab", dead_err)
            self.assertIn("RT-NESTPY-0123456789ab", dead_err)
            self.assertIn("ITREE-DEADRS-0123456789ab", dead_err)

            # Live `else` branch after `if false` remains valid.
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                "pub fn audit_stub() {}\n", encoding="utf-8"
            )
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-LIVEELSE-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4113",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Live else branch passes",
        rationale: "Valid else branch remains active",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_dead.rs::live_else_ok",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
                ),
                encoding="utf-8",
            )
            (root / "anneal/tests/rustc-capture/tests/phase0_dead.rs").write_text(
                """\
#[test]
fn live_else_ok() {
    let (status, reason) = run_capture();
    if false {
        assert!(false);
    } else {
        assert_eq!(status, "unsupported");
        assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-LIVEELSE-0123456789ab]"));
    }
}
""",
                encoding="utf-8",
            )
            rep_live = checker.check_tree(root)
            self.assertTrue(rep_live.ok, rep_live.errors)

            # 3. phase0-diff rejects weakening an existing rule or helper.
            _ = base
            weak_base_rs = BASE_TRIPWIRES_RS.replace(
                "// === PHASE 0 MUTABLE REGISTRY END ===",
                "fn pred_existing() -> bool { true }\n// === PHASE 0 MUTABLE REGISTRY END ===",
            ).replace(
                "pub(crate) const ACTIVE_PHASE0_TRIPWIRES: &[Phase0Tripwire] = &[];",
                """pub(crate) const ACTIVE_PHASE0_TRIPWIRES: &[Phase0Tripwire] = &[
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-OLD-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4095",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Existing guard",
        rationale: "Must not weaken",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_demo.rs::demo_old",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
];""",
            )
            (root / "anneal/tests/rustc-capture/tests/phase0_demo.rs").write_text(
                DEMO_TEST_RS
                + """
#[test]
fn demo_old() {
    assert_eq!(status, "unsupported");
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-OLD-0123456789ab]"));
}
#[test]
fn demo_new() {
    assert_eq!(status, "unsupported");
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-NEW-abcdef012345]"));
}
""",
                encoding="utf-8",
            )
            (root / checker.TRIPWIRES_REL).write_text(
                weak_base_rs, encoding="utf-8"
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "existing phase0 with helper")
            existing_base = _git(root, "rev-parse", "HEAD")

            # Mutate existing tripwire's predicate during addition -> FAIL.
            weak_head_rs = weak_base_rs.replace(
                "predicate: TripwirePredicate::AnyBody,\n    },",
                """predicate: TripwirePredicate::Crate(|_| false),
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-NEW-abcdef012345",
        issue: "https://github.com/google/zerocopy/issues/4096",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "New guard",
        rationale: "Smuggle weaken alongside add",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_demo.rs::demo_new",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },""",
            )
            (root / checker.TRIPWIRES_REL).write_text(
                weak_head_rs, encoding="utf-8"
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "weaken existing entry")
            bad_weaken = _git(root, "rev-parse", "HEAD")
            rep_weaken = checker.check_phase0_diff(
                root, base=existing_base, head=bad_weaken
            )
            self.assertFalse(rep_weaken.ok)
            self.assertIn(
                "must not be deleted or weakened", "\n".join(rep_weaken.errors)
            )

            # Mutate existing helper predicate inside mutable registry -> FAIL.
            weak_helper_rs = weak_base_rs.replace(
                "fn pred_existing() -> bool { true }",
                "fn pred_existing() -> bool { false }",
            ).replace(
                "    },\n];",
                """    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-NEW-abcdef012345",
        issue: "https://github.com/google/zerocopy/issues/4096",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "New guard",
        rationale: "Smuggle helper edit alongside add",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_demo.rs::demo_new",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
];""",
            )
            (root / checker.TRIPWIRES_REL).write_text(
                weak_helper_rs, encoding="utf-8"
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "weaken helper")
            bad_helper = _git(root, "rev-parse", "HEAD")
            rep_helper = checker.check_phase0_diff(
                root, base=existing_base, head=bad_helper
            )
            self.assertFalse(rep_helper.ok)
            self.assertIn(
                "existing predicate helpers inside mutable registry",
                "\n".join(rep_helper.errors),
            )

            # 4. phase1-cleanup rejects residual bug_id inside #[cfg(test)].
            cleaned_rs = BASE_TRIPWIRES_RS + (
                "// note inside #[cfg(test)]\n"
            )
            cleaned_cfg_rs = BASE_TRIPWIRES_RS.replace(
                "fn local_fixture() {",
                "// stale ITREE-OLD-0123456789ab in cfg(test)\n    fn local_fixture() {",
            )
            _ = cleaned_rs
            (root / checker.TRIPWIRES_REL).write_text(
                cleaned_cfg_rs, encoding="utf-8"
            )
            (root / "anneal/tests/rustc-capture/tests/phase0_demo.rs").write_text(
                DEMO_TEST_RS
                + """
#[test]
fn demo_old() {
    assert!(positive_oracle_matches_miri());
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "cfg test residual ref")
            cfg_residual = _git(root, "rev-parse", "HEAD")
            rep_cfg_res = checker.check_phase1_cleanup(
                root, base=existing_base, head=cfg_residual
            )
            self.assertFalse(rep_cfg_res.ok)
            self.assertIn(
                "residual reference remains in",
                "\n".join(rep_cfg_res.errors),
            )

    def test_rejects_unexecuted_test_paths_cfg_allowlist_and_enclosing_blocks(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-exec-paths-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)

            # 1. Python test under anneal/tests/ (not discovered by CI) -> FAIL.
            # 2. Unregistered Cargo crate dir or nested subdir/*.rs -> FAIL.
            # 3. #![cfg(windows)], const cfg(false), # [ignore] -> FAIL.
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    """    PHASE0_TRIPWIRE! {
        bug_id: "RT-UNRUN-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4201",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard unexecuted py path",
        rationale: "Ensure test lives under anneal/ci/",
        regression_test: "anneal/tests/rustc-capture/tests/test_phase0_unrun.py::test_unrun",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-UNREG-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4202",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard unregistered dir",
        rationale: "Ensure Cargo discovers test",
        regression_test: "anneal/tests/unregistered_dir/fake.rs::t_unreg",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-SUBDIR-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4203",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard nested tests subdir",
        rationale: "Cargo skips nested tests/subdir/file.rs",
        regression_test: "anneal/tests/rustc-capture/tests/subdir/phase0_nested.rs::t_sub",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-WINCFG-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4204",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard cfg(windows) allowlist bypass",
        rationale: "Linux CI never compiles cfg(windows)",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_wincfg.rs::t_win",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-CONSTCFG-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4205",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard enclosing const item cfg",
        rationale: "Non-mod enclosing cfg(false) must fail closed",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_g2probes.rs::t_const",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-SPACEIGN-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4206",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard whitespace between # and [",
        rationale: "# [ignore] must still fail closed",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_g2probes.rs::t_sp2",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
                ),
                encoding="utf-8",
            )
            (
                root / "anneal/tests/rustc-capture/tests/test_phase0_unrun.py"
            ).write_text(
                """\
import unittest
class UnrunTests(unittest.TestCase):
    def test_unrun(self):
        self.assertIn("[PHASE0_TRIPWIRE:RT-UNRUN-0123456789ab]", err)
        self.assertEqual(status, "unsupported")
""",
                encoding="utf-8",
            )
            (root / "anneal/tests/unregistered_dir").mkdir(parents=True)
            (root / "anneal/tests/unregistered_dir/fake.rs").write_text(
                """\
#[test]
fn t_unreg() {
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-UNREG-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            (root / "anneal/tests/rustc-capture/tests/subdir").mkdir(
                parents=True
            )
            (
                root
                / "anneal/tests/rustc-capture/tests/subdir/phase0_nested.rs"
            ).write_text(
                """\
#[test]
fn t_sub() {
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-SUBDIR-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            (
                root / "anneal/tests/rustc-capture/tests/phase0_wincfg.rs"
            ).write_text(
                """\
#![cfg(windows)]
#[test]
fn t_win() {
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-WINCFG-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            (
                root / "anneal/tests/rustc-capture/tests/phase0_g2probes.rs"
            ).write_text(
                """\
#[cfg(false)]
const _: () = {
    #[test]
    fn t_const() {
        assert_eq!(status, "unsupported");
        assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-CONSTCFG-0123456789ab]"));
    }
};

# [ignore]
#[test]
fn t_sp2() {
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-SPACEIGN-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            rep = checker.check_tree(root)
            self.assertFalse(rep.ok)
            joined = "\n".join(rep.errors)
            self.assertIn("RT-UNRUN-0123456789ab", joined)
            self.assertIn("anneal/ci/test_<file>.py", joined)
            self.assertIn("[workspace].members", joined)
            self.assertIn("not a Cargo-discovered integration test", joined)
            self.assertIn("file disabled via #![cfg(windows)]", joined)
            self.assertIn("enclosing block disabled via #[cfg(false)]", joined)
            self.assertIn("carries ignore/cfg_attr ignore", joined)

            # Host-mismatch target_os="windows" must fail, while
            # _validate_test_target_executed rejects anneal/tests/*.py directly.
            self.assertIn(
                "not discovered by run_anneal_check.sh",
                checker._validate_test_target_executed(
                    checker.FilesystemRepoView(root),
                    "anneal/tests/rustc-capture/tests/test_phase0_unrun.py",
                )
                or "",
            )
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-OSWIN-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4207",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard wrong OS target string",
        rationale: "Non-linux target_os cfg must fail closed",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_wincfg.rs::t_win_str",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
                ),
                encoding="utf-8",
            )
            (
                root / "anneal/tests/rustc-capture/tests/phase0_wincfg.rs"
            ).write_text(
                """\
#![cfg(all(target_os = "windows", target_arch = "x86_64"))]
#[test]
fn t_win_str() {
    let (status, r) = run_capture();
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-OSWIN-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            rep_winstr = checker.check_tree(root)
            self.assertFalse(rep_winstr.ok)
            winstr_err = "\n".join(rep_winstr.errors)
            self.assertIn("ITREE-OSWIN-0123456789ab", winstr_err)
            self.assertIn("file disabled via", winstr_err)

    def test_blocks_cfg_splits_slice_truncation_activation_and_raw_spoofs(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-cfg-slice-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)

            # 1. #[cfg(all(test))] / #[cfg(not(test))] in tripwires.rs -> FAIL.
            cfg_split_rs = BASE_TRIPWIRES_RS.replace(
                "pub(crate) const ACTIVE_PHASE0_TRIPWIRES: &[Phase0Tripwire] = &[];",
                """#[cfg(not(test))]
pub(crate) const ACTIVE_PHASE0_TRIPWIRES: &[Phase0Tripwire] = &[];
#[cfg(all(test))]
mod extra_decoy {}""",
            )
            (root / checker.TRIPWIRES_REL).write_text(
                cfg_split_rs, encoding="utf-8"
            )
            rep_cfg = checker.check_tree(root)
            self.assertFalse(rep_cfg.ok)
            self.assertIn("conditional attribute", "\n".join(rep_cfg.errors))

            # 2. Selftest inside slice, wrapper `disable(...)`, raw-string
            # spoof, and `];` inside predicate -> catch all spoofs.
            spoof_rs = _with_active_entries(
                r"""    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-SELFSPOOF-0123456789ab",
        issue: "selftest",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Smuggle selftest inside active slice",
        rationale: "Must fail closed",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_demo.rs::ok_spoof",
        activation: TripwireActivation::SyntheticSelftestOnly { env_key: "K", env_value: "V" },
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-WRAPACT-0123456789ab",
        issue: r#"https://github.com/google/zerocopy/issues/4210"#,
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: r##"spoof issue: r#"https://github.com/google/zerocopy/issues/4095"#"##,
        rationale: "Must fail closed on wrapper activation",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_demo.rs::ok_spoof",
        activation: disable(TripwireActivation::Always),
        predicate: TripwirePredicate::Body(|_, _, _| { let _arr = [1, 2]; let _s = "];"; true }),
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-RAWSPOOF-0123456789ab",
        issue: "NOT-A-VALID-URL",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: r##"spoof issue: r#"https://github.com/google/zerocopy/issues/4095"#"##,
        rationale: "Raw string inside scope must not forge issue field",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_demo.rs::ok_spoof",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    UNCHECKED_NON_MACRO_ELEMENT"""
            )
            (root / checker.TRIPWIRES_REL).write_text(
                spoof_rs, encoding="utf-8"
            )
            (root / "anneal/tests/rustc-capture/tests/phase0_demo.rs").write_text(
                DEMO_TEST_RS
                + """
#[test]
fn ok_spoof() {
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-SELFSPOOF-0123456789ab]"));
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-WRAPACT-0123456789ab]"));
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-RAWSPOOF-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            rep_spoof = checker.check_tree(root)
            self.assertFalse(rep_spoof.ok)
            err_s = "\n".join(rep_spoof.errors)
            self.assertIn("SyntheticSelftestOnly tripwire must not live inside ACTIVE_PHASE0_TRIPWIRES", err_s)
            self.assertIn("unrecognized or non-literal TripwireActivation", err_s)
            self.assertIn("NOT-A-VALID-URL", err_s)
            self.assertIn("element in ACTIVE_PHASE0_TRIPWIRES must invoke PHASE0_TRIPWIRE!", err_s)

            # 3. Valid predicate with `[1, 2];` and `"];"` -> PASSES cleanly!
            ok_arr_rs = _with_active_entries(
                r"""    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-ARR-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4211",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard predicate with brackets and semicolons",
        rationale: "Balanced bracket matcher handles [1, 2];",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_demo.rs::ok_arr",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::Body(|_, _, _| { let _arr = [1, 2]; let _s = "];"; true }),
    },"""
            )
            (root / checker.TRIPWIRES_REL).write_text(
                ok_arr_rs, encoding="utf-8"
            )
            (root / "anneal/tests/rustc-capture/tests/phase0_demo.rs").write_text(
                DEMO_TEST_RS
                + """
#[test]
fn ok_arr() {
    let (status, r) = run_capture();
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-ARR-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            rep_arr = checker.check_tree(root)
            self.assertTrue(rep_arr.ok, rep_arr.errors)

    def test_multiline_parens_array_cfg_test_head_rev_and_layer_handling(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-history-") as tmp:
            root = Path(tmp)
            base = _init_fixture_repo(root)

            # 1. Multiline Lean comment with `(v2)`, embargoed issue, and
            # pre-existing trusted/audit RT-* entry -> PASS.
            step_path = (
                root / "anneal/trusted/lean/Trusted/MirSemantics/Step.lean"
            )
            step_path.write_text(
                """\
namespace Trusted.MirSemantics
-- PHASE0_TRIPWIRE(
--   bug_id="LMIRI-OPS-aabbccddeeff",
--   issue="https://github.com/google/zerocopy/issues/4105",
--   owner="fixture-owner",
--   added_date="2026-11-26",
--   scope="guard (v2) width overflow",
--   rationale="Neutral fail-closed runtime guard",
--   regression_test="anneal/tests/itree_diff/tests/phase0_rt.rs::rt_guard"
-- )
def guard := StepResult.fault .unsupported
def evalStep := guard
end Trusted.MirSemantics
""",
                encoding="utf-8",
            )
            (root / "anneal/tests/itree_diff/tests/phase0_rt.rs").write_text(
                """\
#[test]
fn rt_guard() {
    let step_fault = run_lean_step();
    assert_eq!(step_fault, Some(FaultKind::Unsupported), "LMIRI-OPS-aabbccddeeff");
}
""",
                encoding="utf-8",
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                """\
// PHASE0_TRIPWIRE(bug_id="RT-AUDIT-112233445566", issue="embargoed", owner="sec-maintainers", added_date="2026-11-26", scope="Neutral fail-closed admission check", rationale="Blocks unvetted boundary pattern fail-closed", regression_test="anneal/tests/audit/tests/boundary_audit.rs::rt_embargoed")

#[cfg(test)]
fn helper() -> [u8; 4] {
    // Doc fixture mention: ITREE-DUMMY-deadbeef0001
    let _x = "PHASE0_TRIPWIRE(bug_id=\"BAD\")";
    [0; 4]
}
""",
                encoding="utf-8",
            )
            (root / "anneal/tests/audit/tests/boundary_audit.rs").write_text(
                """\
#[test]
fn rt_embargoed() {
    let res = run_audit();
    assert!(res.is_err(), "RT-AUDIT-112233445566");
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "preexisting lean and audit")
            pre_base = _git(root, "rev-parse", "HEAD")

            rep_pre = checker.check_tree(root)
            self.assertTrue(rep_pre.ok, rep_pre.errors)

            # 2. No-op comment edit in tripwires.rs while Lean rule already
            # exists in `pre_base` must FAIL (added set is empty).
            noop_rs = BASE_TRIPWIRES_RS.replace(
                "// === PHASE 0 MUTABLE REGISTRY END ===",
                "// no-op comment\n// === PHASE 0 MUTABLE REGISTRY END ===",
            )
            (root / checker.TRIPWIRES_REL).write_text(noop_rs, encoding="utf-8")
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "noop comment edit")
            noop_rev = _git(root, "rev-parse", "HEAD")
            rep_noop = checker.check_phase0_diff(
                root, base=pre_base, head=noop_rev
            )
            self.assertFalse(rep_noop.ok)
            self.assertIn(
                "must introduce at least one new active PHASE0_TRIPWIRE",
                "\n".join(rep_noop.errors),
            )

            # 3. Valid embargoed Runbook A addition alongside pre-existing
            # Lean/audit rules -> PASS without touching boundary_audit.rs.
            add_embargoed_rs = _with_active_entries(
                """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-EMB-0123456789ab",
        issue: "embargoed",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Neutral fail-closed capture guard",
        rationale: "Hold pattern fail-closed under coordinated disclosure",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_demo.rs::embargoed_test",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
            )
            (root / checker.TRIPWIRES_REL).write_text(
                add_embargoed_rs, encoding="utf-8"
            )
            (root / "anneal/tests/rustc-capture/tests/phase0_demo.rs").write_text(
                DEMO_TEST_RS
                + """
#[test]
fn embargoed_test() {
    let (status, r) = run_capture();
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-EMB-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "add embargoed runbook A")
            emb_rev = _git(root, "rev-parse", "HEAD")
            rep_emb = checker.check_phase0_diff(
                root, base=pre_base, head=emb_rev
            )
            self.assertTrue(rep_emb.ok, rep_emb.errors)

            # 4. Deleting Lean rule with runtime fallback flag -> FAIL.
            step_path.write_text("-- deleted unexpectedly\n", encoding="utf-8")
            (root / "anneal/trusted/lean/Trusted/MirSemantics/Extra.lean").write_text(
                """\
-- PHASE0_TRIPWIRE(bug_id="LMIRI-EXTRA-0123456789ab", issue="https://github.com/google/zerocopy/issues/4106", owner="fixture-owner", added_date="2026-11-26", scope="extra guard", rationale="new rule", regression_test="anneal/tests/itree_diff/tests/phase0_rt.rs::rt_extra")
def extraGuard := StepResult.fault .unsupported
""",
                encoding="utf-8",
            )
            (root / "anneal/tests/itree_diff/tests/phase0_rt.rs").write_text(
                """\
#[test]
fn rt_guard() {
    let step_fault = run_lean_step();
    assert_eq!(step_fault, Some(FaultKind::Unsupported), "LMIRI-OPS-aabbccddeeff");
}
#[test]
fn rt_extra() {
    let step_fault = run_lean_step();
    assert_eq!(step_fault, Some(FaultKind::Unsupported), "LMIRI-EXTRA-0123456789ab");
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "delete lean rule")
            del_lean_rev = _git(root, "rev-parse", "HEAD")
            rep_del_lean = checker.check_phase0_diff(
                root,
                base=emb_rev,
                head=del_lean_rev,
                allow_runtime_semantics_fallback=True,
            )
            self.assertFalse(rep_del_lean.ok)
            self.assertIn(
                "must not delete existing tripwires",
                "\n".join(rep_del_lean.errors),
            )

            # 5. Phase-1 cleanup of `LMIRI-OPS-aabbccddeeff` honoring `--head`
            # against dirty working tree, `--resolved-bug` preserving `--base`
            # runtime layer, and `--known-bugs` layer check.
            step_path.write_text("-- fixed operational rule\n", encoding="utf-8")
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "unflipped phase1")
            unflipped_rev = _git(root, "rev-parse", "HEAD")

            # Dirty working tree looks fixed while `unflipped_rev` stays bad.
            (root / "anneal/tests/itree_diff/tests/phase0_rt.rs").write_text(
                """\
#[test]
fn rt_guard() {
    assert!(matches_miri_fault_ub("LMIRI-OPS-aabbccddeeff"));
}
""",
                encoding="utf-8",
            )

            # --resolved-bug + --base checks `unflipped_rev` and keeps
            # runtime_semantics layer from --base.
            rep_p1_base = checker.check_phase1_cleanup(
                root,
                base=pre_base,
                head=unflipped_rev,
                resolved_bugs=["LMIRI-OPS-aabbccddeeff"],
            )
            self.assertFalse(rep_p1_base.ok)
            self.assertIn(
                "must flip from unsupported-fault refusal",
                "\n".join(rep_p1_base.errors),
            )

            # Omitting --base with --head + --known-bugs still reads Git
            # `unflipped_rev` and rejects Unsupported!
            bugs_rt_json = root / "bugs_rt.json"
            bugs_rt_json.write_text(
                json.dumps(
                    [
                        {
                            "bug_id": "LMIRI-OPS-aabbccddeeff",
                            "status": "fixed",
                            "fixed_sha": unflipped_rev,
                            "layer": "runtime_semantics",
                            "regression_test": "anneal/tests/itree_diff/tests/phase0_rt.rs::rt_guard",
                        }
                    ]
                ),
                encoding="utf-8",
            )
            rep_kb_head = checker.check_phase1_cleanup(
                root, head=unflipped_rev, known_bugs_path=bugs_rt_json
            )
            self.assertFalse(rep_kb_head.ok)
            self.assertIn(
                "must flip from unsupported-fault refusal",
                "\n".join(rep_kb_head.errors),
            )

            # Omitting --base with --diff-files MUST fail closed; passing
            # --base with --head + --diff-files still inspects Git rev.
            rep_no_base = checker.check_phase0_diff(
                root,
                head=base,
                diff_files=["anneal/ci/test_phase0_x.py"],
            )
            self.assertFalse(rep_no_base.ok)
            self.assertIn("requires --base", "\n".join(rep_no_base.errors))

            rep_head_only = checker.check_phase0_diff(
                root,
                base=pre_base,
                head=base,
                diff_files=["anneal/ci/unrelated.py"],
            )
            self.assertFalse(rep_head_only.ok)
            self.assertIn("outside isolated Phase-0", "\n".join(rep_head_only.errors))

    def test_blocks_field_cfg_macro_delims_lean_char_cargo_flags_and_vacuous(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-hardening-") as tmp:
            root = Path(tmp)
            base = _init_fixture_repo(root)

            # 1. #[cfg(test)] struct/literal field with trailing comma must not
            # swallow subsequent production `impl Drop` tokens.
            (root / "anneal/trusted/audit/src/stage_like.rs").write_text(
                """\
struct S {
    #[cfg(test)]
    test_only: BTreeMap<String, Option<Vec<u8>>>,
    real: u32,
}
impl Drop for S {
    fn drop(&mut self) {
        // PHASE0_TRIPWIRE(bug_id="BAD-ID", issue="BAD")
    }
}
""",
                encoding="utf-8",
            )
            rep_field = checker.check_tree(root)
            self.assertFalse(rep_field.ok)
            self.assertIn("invalid Phase-0 bug_id 'BAD-ID'", "\n".join(rep_field.errors))

            # Verify valid stage_like without comment passes cleanly (incl.
            # BTreeMap<K, V> generic comma and struct literal field).
            (root / "anneal/trusted/audit/src/stage_like.rs").write_text(
                """\
struct S {
    #[cfg(test)]
    test_only: BTreeMap<String, Vec<u8>>,
    real: u32,
}
fn mk() -> S {
    S {
        #[cfg(test)]
        test_only: None,
        real: 0,
    }
}
""",
                encoding="utf-8",
            )
            self.assertTrue(checker.check_tree(root).ok)

            # 2. Lean character literal `'\"'` must not break string masking.
            lean_step = (
                root / "anneal/trusted/lean/Trusted/MirSemantics/Step.lean"
            )
            lean_step.write_text(
                """\
def q : Char := '\"'
-- PHASE0_TRIPWIRE(bug_id="BAD-CHAR-MASK", issue="BAD")
""",
                encoding="utf-8",
            )
            rep_char = checker.check_tree(root)
            self.assertFalse(rep_char.ok)
            self.assertIn("BAD-CHAR-MASK", "\n".join(rep_char.errors))
            lean_step.unlink()

            # 3. Missing mutable-registry fence markers must fail `--mode tree`.
            no_fence = checker.check_tree(root)
            self.assertTrue(no_fence.ok)
            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS.replace(checker.MUTABLE_START_MARKER, "// gone"),
                encoding="utf-8",
            )
            rep_nofence = checker.check_tree(root)
            self.assertFalse(rep_nofence.ok)
            self.assertIn("PHASE 0 MUTABLE REGISTRY START", "\n".join(rep_nofence.errors))

            # 4. Reject uninvoked macro_rules!(...), non-module blocks, async
            # def, non-TestCase classes, and `if True: raise SkipTest(...)`,
            # while keeping live statement #[cfg(target_os = "linux")] intact.
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-MACPAREN-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4301",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard paren macro_rules test",
        rationale: "Uninvoked macro_rules! must fail",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_hardened.rs::dead_macro_paren",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-SWALLOW-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4302",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard swallow macro block",
        rationale: "Macro-swallowed #[test] must fail",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_hardened.rs::swallowed_test",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-CONSTBLK-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4303",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard const _: () = { #[test] }",
        rationale: "const block #[test] never runs in rustc --test",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_hardened.rs::dead_const_test",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-LINUXBLK-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4304",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Valid statement-level linux cfg block",
        rationale: "Must keep #[cfg(target_os = linux)] body live",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_hardened.rs::linux_stmt_ok",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
                ),
                encoding="utf-8",
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                """\
// PHASE0_TRIPWIRE(bug_id="RT-NONTC-0123456789ab", issue="https://github.com/google/zerocopy/issues/4305", owner="fixture-owner", added_date="2026-11-26", scope="non-TestCase", rationale="FakeSuite fails", regression_test="anneal/ci/test_phase0_hardened.py::test_fake_suite")
// PHASE0_TRIPWIRE(bug_id="RT-ASYNC-0123456789ab", issue="https://github.com/google/zerocopy/issues/4306", owner="fixture-owner", added_date="2026-11-26", scope="async method", rationale="async def fails", regression_test="anneal/ci/test_phase0_hardened.py::test_async_skip")
// PHASE0_TRIPWIRE(bug_id="RT-RAISESKIP-0123456789ab", issue="https://github.com/google/zerocopy/issues/4307", owner="fixture-owner", added_date="2026-11-26", scope="raise SkipTest", rationale="raise SkipTest fails", regression_test="anneal/ci/test_phase0_hardened.py::test_raise_skip")
""",
                encoding="utf-8",
            )
            (root / "anneal/tests/rustc-capture/tests/phase0_hardened.rs").write_text(
                """\
macro_rules! never_invoked (
    (a) => {};
    (b) => {
        #[test]
        fn dead_macro_paren() {
            let (status, r) = run_capture();
            assert_eq!(status, "unsupported");
            assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-MACPAREN-0123456789ab]"));
        }
    };
);
macro_rules! swallow { ($($t:tt)*) => {}; }
swallow! {
    #[test]
    fn swallowed_test() {
        let (status, r) = run_capture();
        assert_eq!(status, "unsupported");
        assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-SWALLOW-0123456789ab]"));
    }
}
const _: () = {
    #[test]
    fn dead_const_test() {
        let (status, r) = run_capture();
        assert_eq!(status, "unsupported");
        assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-CONSTBLK-0123456789ab]"));
    }
};
#[test]
fn linux_stmt_ok() {
    let (status, r) = run_capture();
    #[cfg(target_os = "linux")]
    {
        assert_eq!(status, "unsupported");
        assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-LINUXBLK-0123456789ab]"));
    }
}
""",
                encoding="utf-8",
            )
            (root / "anneal/ci/test_phase0_hardened.py").write_text(
                """\
import unittest

class FakeSuite:
    def test_fake_suite(self):
        status, err = run_probe()
        self.assertIn("[PHASE0_TRIPWIRE:RT-NONTC-0123456789ab]", err)
        self.assertEqual(status, "unsupported")

class RealSuite(unittest.TestCase):
    async def test_async_skip(self):
        status, err = run_probe()
        self.assertIn("[PHASE0_TRIPWIRE:RT-ASYNC-0123456789ab]", err)
        self.assertEqual(status, "unsupported")

    def test_raise_skip(self):
        status, err = run_probe()
        if True:
            raise unittest.SkipTest("bypass")
        self.assertIn("[PHASE0_TRIPWIRE:RT-RAISESKIP-0123456789ab]", err)
        self.assertEqual(status, "unsupported")
""",
                encoding="utf-8",
            )
            rep_enc = checker.check_tree(root)
            self.assertFalse(rep_enc.ok)
            err_enc = "\n".join(rep_enc.errors)
            self.assertIn("ITREE-MACPAREN-0123456789ab", err_enc)
            self.assertIn("ITREE-SWALLOW-0123456789ab", err_enc)
            self.assertIn("ITREE-CONSTBLK-0123456789ab", err_enc)
            self.assertIn("nested inside non-module delimiter", err_enc)
            self.assertIn("nested inside non-module enclosing block", err_enc)
            self.assertNotIn("ITREE-LINUXBLK-0123456789ab", err_enc)
            self.assertIn("must inherit from unittest.TestCase", err_enc)
            self.assertIn("must be a synchronous def", err_enc)
            self.assertIn("must not call skipTest", err_enc)

            # 5. Reject Cargo `test = false` / `harness = false` / non-default
            # required-features.
            rc_toml = root / "anneal/tests/rustc-capture/Cargo.toml"
            orig_toml = rc_toml.read_text(encoding="utf-8")
            for bad_flags, frag in (
                ('test = false\n', "test = false"),
                ('harness = false\n', "harness = false"),
                ('required-features = ["unmet"]\n', "non-default Cargo feature"),
            ):
                rc_toml.write_text(
                    orig_toml
                    + f'\n[[test]]\nname = "phase0_hardened"\n{bad_flags}',
                    encoding="utf-8",
                )
                cargo_err = checker._validate_test_target_executed(
                    checker.FilesystemRepoView(root),
                    "anneal/tests/rustc-capture/tests/phase0_hardened.rs",
                )
                self.assertIn(frag, cargo_err or "")
            rc_toml.write_text(orig_toml, encoding="utf-8")

            # 6. Helper literal whitespace change must fail phase0-diff.
            helper_base_rs = BASE_TRIPWIRES_RS.replace(
                "// === PHASE 0 MUTABLE REGISTRY END ===",
                'fn h_env(v: &str) -> bool { v == "two  spaces" }\n'
                "// === PHASE 0 MUTABLE REGISTRY END ===",
            )
            (root / checker.TRIPWIRES_REL).write_text(
                helper_base_rs, encoding="utf-8"
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "helper literal spaces base")
            h_base = _git(root, "rev-parse", "HEAD")

            helper_head_rs = (
                helper_base_rs.replace("two  spaces", "two spaces")
                .replace(
                    "pub(crate) const ACTIVE_PHASE0_TRIPWIRES: &[Phase0Tripwire] = &[];",
                    """pub(crate) const ACTIVE_PHASE0_TRIPWIRES: &[Phase0Tripwire] = &[
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-LINUXBLK-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4304",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard helper edit",
        rationale: "Test literal space preservation",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_hardened.rs::linux_stmt_ok",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
];""",
                )
            )
            (root / checker.TRIPWIRES_REL).write_text(
                helper_head_rs, encoding="utf-8"
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "weaken helper string space")
            h_head = _git(root, "rev-parse", "HEAD")
            rep_ws = checker.check_phase0_diff(root, base=h_base, head=h_head)
            self.assertFalse(rep_ws.ok)
            self.assertIn(
                "existing predicate helpers inside mutable registry",
                "\n".join(rep_ws.errors),
            )

            # 7. Editing pre-existing annotated Step.lean without a NEW bug ID
            # must FAIL under --allow-runtime-semantics-fallback.
            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS, encoding="utf-8"
            )
            lean_step.write_text(
                """\
-- PHASE0_TRIPWIRE(bug_id="LMIRI-PRE-0123456789ab", issue="https://github.com/google/zerocopy/issues/4308", owner="fixture-owner", added_date="2026-11-26", scope="pre", rationale="existing", regression_test="anneal/tests/itree_diff/tests/phase0_hardened_lean.rs::pre_ok")
def guard := StepResult.fault .unsupported
""",
                encoding="utf-8",
            )
            (root / "anneal/tests/itree_diff/tests/phase0_hardened_lean.rs").write_text(
                """\
#[test]
fn pre_ok() {
    assert_eq!(f, Some(FaultKind::Unsupported), "LMIRI-PRE-0123456789ab");
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "preexisting lean rule")
            lean_base = _git(root, "rev-parse", "HEAD")

            lean_step.write_text(
                """\
-- PHASE0_TRIPWIRE(bug_id="LMIRI-PRE-0123456789ab", issue="https://github.com/google/zerocopy/issues/4308", owner="fixture-owner", added_date="2026-11-26", scope="pre", rationale="existing", regression_test="anneal/tests/itree_diff/tests/phase0_hardened_lean.rs::pre_ok")
def guard := StepResult.ok
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "sneak lean edit without new id")
            lean_head = _git(root, "rev-parse", "HEAD")
            rep_sneak = checker.check_phase0_diff(
                root,
                base=lean_base,
                head=lean_head,
                allow_runtime_semantics_fallback=True,
            )
            self.assertFalse(rep_sneak.ok)
            self.assertIn(
                "must introduce at least one new active PHASE0_TRIPWIRE",
                "\n".join(rep_sneak.errors),
            )

            # 8. Hollowed-out empty or tautological Phase-1 test body -> FAIL.
            lean_step.write_text("-- fixed\n", encoding="utf-8")
            for bad_body in ("", "assert!(true);", "assert_eq!(1, 1);"):
                (
                    root / "anneal/tests/itree_diff/tests/phase0_hardened_lean.rs"
                ).write_text(
                    f"#[test]\nfn pre_ok() {{\n    {bad_body}\n}}\n",
                    encoding="utf-8",
                )
                _git(root, "add", ".")
                _git(root, "commit", "-q", "-m", "vacuous phase1")
                vac_head = _git(root, "rev-parse", "HEAD")
                rep_vac = checker.check_phase1_cleanup(
                    root, base=lean_base, head=vac_head
                )
                self.assertFalse(rep_vac.ok)
                self.assertIn("non-vacuous", "\n".join(rep_vac.errors))
            for vac_py in (
                "",
                "assert True",
                "self.assertEqual(1, 1)",
                "self.assertTrue(True, msg=err)",
            ):
                self.assertFalse(checker._has_meaningful_phase1_assertion(vac_py))
            self.assertTrue(
                checker._has_meaningful_phase1_assertion(
                    "self.assertEqual(out.returncode, 0)"
                )
            )
            self.assertTrue(
                checker._has_meaningful_phase1_assertion("assert!(res.is_ok());")
            )
            _ = base

    def test_blocks_early_return_closures_cfg_comments_and_phase0_tautologies(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-codex-hardening-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)

            # 1. Early `return;`, `if true { return; }`, closures, and Phase-0
            # tautologies must FAIL; `.iter().any(|l| ...)` & match-`|` pass.
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-RET-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4401",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard early return bypass",
        rationale: "Assertions after unconditional return never run",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_hardened.rs::dead_after_return",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-IFRET-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4402",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard if true return bypass",
        rationale: "Assertions after if true return never run",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_hardened.rs::dead_after_if_true_ret",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-CLOSBLK-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4403",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard uncalled block closure",
        rationale: "Assertions in closure body may never run",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_hardened.rs::dead_closure_block",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-CLOSEXP-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4404",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard uncalled expr closure",
        rationale: "Assertions in expr closure may never run",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_hardened.rs::dead_closure_expr",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-TAUT-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4405",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard Phase-0 tautologies",
        rationale: "Constant equality checks do not test capture",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_hardened.rs::phase0_tautologies",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-LIVEOK-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4406",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Allow real iter().any(|l| ...) and leading match |",
        rationale: "Valid assertions outside closures stay live",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_hardened.rs::live_iter_and_match",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
                ),
                encoding="utf-8",
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                """\
// PHASE0_TRIPWIRE(bug_id="RT-TAUTPY-0123456789ab", issue="https://github.com/google/zerocopy/issues/4407", owner="fixture-owner", added_date="2026-11-26", scope="py taut", rationale="tautology fails", regression_test="anneal/ci/test_phase0_taut.py::test_py_tautology")
""",
                encoding="utf-8",
            )
            (root / "anneal/tests/rustc-capture/tests/phase0_hardened.rs").write_text(
                """\
#[test]
fn dead_after_return() {
    let (status, r) = run_capture();
    if false { return; }
    return;
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-RET-0123456789ab]"));
}
#[test]
fn dead_after_if_true_ret() {
    let (status, r) = run_capture();
    if true {
        return;
    }
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-IFRET-0123456789ab]"));
}
#[test]
fn dead_closure_block() {
    let (status, r) = run_capture();
    let _f = || {
        assert_eq!(status, "unsupported");
        assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-CLOSBLK-0123456789ab]"));
    };
}
#[test]
fn dead_closure_expr() {
    let (status, r) = run_capture();
    let _f = move |_x: u8| (
        assert_eq!(status, "unsupported"),
        assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-CLOSEXP-0123456789ab]")),
    );
}
#[test]
fn phase0_tautologies() {
    let (out, reason) = run_capture();
    assert_eq!(Some(1), Some(1));
    assert_eq!(
        "[PHASE0_TRIPWIRE:ITREE-TAUT-0123456789ab]",
        "[PHASE0_TRIPWIRE:ITREE-TAUT-0123456789ab]",
    );
    assert!(
        true
            || (out.status.code() == Some(1)
                && reason.contains(
                    "[PHASE0_TRIPWIRE:ITREE-TAUT-0123456789ab]"
                ))
    );
}
#[test]
fn live_iter_and_match() {
    let (failure, lines) = run_capture();
    if maybe_skip() {
        panic!("unexpected skip");
    }
    match kind {
        | Kind::A
        | Kind::B => {
            assert_eq!(failure["status"], "unsupported");
            assert!(lines.iter().any(|l| l.contains("[PHASE0_TRIPWIRE:ITREE-LIVEOK-0123456789ab]")));
        }
    }
}
""",
                encoding="utf-8",
            )
            (root / "anneal/ci/test_phase0_taut.py").write_text(
                """\
import unittest

class PyTautTests(unittest.TestCase):
    def test_py_tautology(self):
        self.assertEqual("[PHASE0_TRIPWIRE:RT-TAUTPY-0123456789ab]", "[PHASE0_TRIPWIRE:RT-TAUTPY-0123456789ab]")
        self.assertEqual("unsupported", "unsupported")
""",
                encoding="utf-8",
            )
            rep_dead = checker.check_tree(root)
            self.assertFalse(rep_dead.ok)
            err_dead = "\n".join(rep_dead.errors)
            for bad_id in (
                "ITREE-RET-0123456789ab",
                "ITREE-IFRET-0123456789ab",
                "ITREE-CLOSBLK-0123456789ab",
                "ITREE-CLOSEXP-0123456789ab",
                "ITREE-TAUT-0123456789ab",
                "RT-TAUTPY-0123456789ab",
            ):
                self.assertIn(bad_id, err_dead)
            self.assertNotIn("ITREE-LIVEOK-0123456789ab", err_dead)

            # 2. Trusted Rust comment tripwires under #[cfg(any())],
            # #![cfg(any())], or #![cfg(test)] must FAIL; plain #[cfg(unix)]
            # on normal code without comment tripwires continues to pass.
            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS, encoding="utf-8"
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                "pub fn audit_stub() {}\n", encoding="utf-8"
            )
            (root / "anneal/trusted/audit/src/unix_ok.rs").write_text(
                "#[cfg(unix)]\npub fn platform_ok() {}\n", encoding="utf-8"
            )
            self.assertTrue(checker.check_tree(root).ok)

            for bad_attr in (
                "#[cfg(any())]\npub fn d() {\n",
                "#![cfg(any())]\npub fn d() {\n",
                "#![cfg(test)]\npub fn d() {\n",
            ):
                (root / "anneal/trusted/audit/src/cfg_bad.rs").write_text(
                    bad_attr
                    + '// PHASE0_TRIPWIRE(bug_id="RT-CFGCMT-0123456789ab", issue="https://github.com/google/zerocopy/issues/4408", owner="fixture-owner", added_date="2026-11-26", scope="guard", rationale="guard", regression_test="anneal/tests/rustc-capture/tests/phase0_hardened.rs::live_iter_and_match")\n}\n',
                    encoding="utf-8",
                )
                rep_cfg_cmt = checker.check_tree(root)
                self.assertFalse(rep_cfg_cmt.ok)
                self.assertIn(
                    "trusted comment PHASE0_TRIPWIRE inside",
                    "\n".join(rep_cfg_cmt.errors),
                )
            (root / "anneal/trusted/audit/src/cfg_bad.rs").unlink()

            # 3. Phase-1 cleanup on static_capture must reject tests that keep
            # expecting refusal (`"unsupported"` or exit `Some(1)` / non-zero).
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-STATICP1-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4409",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard static Phase-1 unflipped refusal",
        rationale: "Refuse until fixed",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_static_p1.rs::static_test",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
                ),
                encoding="utf-8",
            )
            p1_file = (
                root / "anneal/tests/rustc-capture/tests/phase0_static_p1.rs"
            )
            p1_file.write_text(
                """\
#[test]
fn static_test() {
    let (out, failure, reason) = run_capture();
    assert_eq!(out.status.code(), Some(1));
    assert_eq!(failure["status"], "unsupported");
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-STATICP1-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "static phase0 base")
            p1_base = _git(root, "rev-parse", "HEAD")

            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS, encoding="utf-8"
            )
            for still_refuses in (
                'assert_eq!(failure["status"], "unsupported");\nassert!(out.status.success());',
                'assert_eq!(out.status.code(), Some(1));',
                'assert!(!out.status.success());',
            ):
                p1_file.write_text(
                    f"#[test]\nfn static_test() {{\n    {still_refuses}\n}}\n",
                    encoding="utf-8",
                )
                _git(root, "add", ".")
                _git(root, "commit", "-q", "-m", "static still refuses")
                bad_p1 = _git(root, "rev-parse", "HEAD")
                rep_bad_p1 = checker.check_phase1_cleanup(
                    root, base=p1_base, head=bad_p1
                )
                self.assertFalse(rep_bad_p1.ok)
                self.assertIn(
                    "must flip from unsupported-fault refusal",
                    "\n".join(rep_bad_p1.errors),
                )

            p1_file.write_text(
                """\
#[test]
fn static_test() {
    let (out, out_status) = run_capture();
    assert!(out.status.success());
    assert_eq!(out_status["status"], "captured");
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "static cleanly flips")
            good_p1 = _git(root, "rev-parse", "HEAD")
            rep_good_p1 = checker.check_phase1_cleanup(
                root, base=p1_base, head=good_p1
            )
            self.assertTrue(rep_good_p1.ok, rep_good_p1.errors)

    def test_rejects_macro_brackets_dir_tests_inner_cfg_and_negated_polarity(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-g2r3-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)

            # 1. PHASE0_TRIPWIRE![...] square-bracket invocations outside
            # ACTIVE_PHASE0_TRIPWIRES or inside other trusted files must FAIL.
            bracket_rs = BASE_TRIPWIRES_RS.replace(
                "// === PHASE 0 MUTABLE REGISTRY END ===",
                'pub(crate) const SNEAKY: Phase0Tripwire = PHASE0_TRIPWIRE![\n'
                '    bug_id: "BAD-ID", issue: "BAD",\n'
                '];\n// === PHASE 0 MUTABLE REGISTRY END ===',
            )
            (root / checker.TRIPWIRES_REL).write_text(
                bracket_rs, encoding="utf-8"
            )
            rep_br = checker.check_tree(root)
            self.assertFalse(rep_br.ok)
            self.assertIn(
                "production PHASE0_TRIPWIRE! outside", "\n".join(rep_br.errors)
            )
            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS, encoding="utf-8"
            )
            (root / "anneal/trusted/rustc-capture/src/other.rs").write_text(
                'pub const X: Phase0Tripwire = PHASE0_TRIPWIRE![bug_id: "BAD"];\n',
                encoding="utf-8",
            )
            rep_other_br = checker.check_tree(root)
            self.assertFalse(rep_other_br.ok)
            self.assertIn(
                "declarations are permitted only inside",
                "\n".join(rep_other_br.errors),
            )
            (root / "anneal/trusted/rustc-capture/src/other.rs").unlink()

            # 2. Directory-form Cargo [[test]] name="<name>" without path must
            # honor test=false, harness=false, and unmet required-features.
            rc_toml = root / "anneal/tests/rustc-capture/Cargo.toml"
            orig_toml = rc_toml.read_text(encoding="utf-8")
            dir_main = (
                root / "anneal/tests/rustc-capture/tests/phase0_dir/main.rs"
            )
            dir_main.parent.mkdir(parents=True, exist_ok=True)
            dir_main.write_text("#[test]\nfn dir_ok() {}\n", encoding="utf-8")
            self.assertIsNone(
                checker._validate_test_target_executed(
                    checker.FilesystemRepoView(root),
                    "anneal/tests/rustc-capture/tests/phase0_dir/main.rs",
                )
            )
            for bad_flag, msg_frag in (
                ("test = false\n", "test = false"),
                ("harness = false\n", "harness = false"),
                ('required-features = ["opt"]\n', "non-default Cargo feature"),
            ):
                rc_toml.write_text(
                    orig_toml + f'\n[[test]]\nname = "phase0_dir"\n{bad_flag}',
                    encoding="utf-8",
                )
                err = checker._validate_test_target_executed(
                    checker.FilesystemRepoView(root),
                    "anneal/tests/rustc-capture/tests/phase0_dir/main.rs",
                )
                self.assertIn(msg_frag, err or "")
            rc_toml.write_text(orig_toml, encoding="utf-8")

            # 3. Allowlisted file/mod inner #![cfg(target_os = "linux")] probes
            # A1/A2/A3 must PASS, while #![cfg(windows)] must FAIL.
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-A1-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4501",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Allowlisted file inner cfg",
        rationale: "Probe A1 passes",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_a1.rs::t_a1",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-A2-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4502",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Allowlisted file inner cfg over mod",
        rationale: "Probe A2 passes",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_a2.rs::t_a2",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-A3-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4503",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Allowlisted inner cfg inside mod",
        rationale: "Probe A3 passes",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_a3.rs::t_a3",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
                ),
                encoding="utf-8",
            )
            (root / "anneal/tests/rustc-capture/tests/phase0_a1.rs").write_text(
                """\
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn t_a1() {
    let (status, r) = run_capture();
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-A1-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            (root / "anneal/tests/rustc-capture/tests/phase0_a2.rs").write_text(
                """\
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
mod tests {
    #[test]
    fn t_a2() {
        let (status, r) = run_capture();
        assert_eq!(status, "unsupported");
        assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-A2-0123456789ab]"));
    }
}
""",
                encoding="utf-8",
            )
            (root / "anneal/tests/rustc-capture/tests/phase0_a3.rs").write_text(
                """\
mod tests {
    #![cfg(target_os = "linux")]
    #[test]
    fn t_a3() {
        let (status, r) = run_capture();
        assert_eq!(status, "unsupported");
        assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-A3-0123456789ab]"));
    }
}
""",
                encoding="utf-8",
            )
            rep_a = checker.check_tree(root)
            self.assertTrue(rep_a.ok, rep_a.errors)

            (root / "anneal/tests/rustc-capture/tests/phase0_a3.rs").write_text(
                """\
mod tests {
    #![cfg(windows)]
    #[test]
    fn t_a3() {
        let (status, r) = run_capture();
        assert_eq!(status, "unsupported");
        assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-A3-0123456789ab]"));
    }
}
""",
                encoding="utf-8",
            )
            rep_a_bad = checker.check_tree(root)
            self.assertFalse(rep_a_bad.ok)
            self.assertIn("ITREE-A3-0123456789ab", "\n".join(rep_a_bad.errors))

            # 4. Reject negated polarity (F1/F2) and static_capture->py binding.
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-NEGTAG-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4504",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard negated contains tag",
        rationale: "F1 negative polarity must fail",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_neg.rs::f1_neg_tag",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-NEGSUCC-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4505",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard status.success with unsupported message",
        rationale: "F2 must fail",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_neg.rs::f2_success",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-NEGREF-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4506",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard assert_ne against unsupported",
        rationale: "Negated refusal must fail",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_neg.rs::neg_refusal",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-STATICPY-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4507",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Reject python test on static_capture",
        rationale: "static_capture requires Cargo rs integration test",
        regression_test: "anneal/ci/test_phase0_neg.py::test_py_neg",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
                ),
                encoding="utf-8",
            )
            (root / "anneal/tests/rustc-capture/tests/phase0_neg.rs").write_text(
                """\
#[test]
fn f1_neg_tag() {
    let (failure, reason) = run_capture();
    assert!(!reason.contains("[PHASE0_TRIPWIRE:ITREE-NEGTAG-0123456789ab]"));
    assert_eq!(failure["status"], "unsupported");
}
#[test]
fn f2_success() {
    let out = run_capture();
    assert!(out.status.success(), "[PHASE0_TRIPWIRE:ITREE-NEGSUCC-0123456789ab] must stay unsupported");
}
#[test]
fn neg_refusal() {
    let (failure, reason) = run_capture();
    assert_ne!(failure["status"], "unsupported");
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-NEGREF-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            (root / "anneal/ci/test_phase0_neg.py").write_text(
                """\
import unittest

class NegPyTests(unittest.TestCase):
    def test_py_neg(self):
        status, err = run_probe()
        self.assertIn("[PHASE0_TRIPWIRE:ITREE-STATICPY-0123456789ab]", err)
        self.assertEqual(status, "unsupported")

    def test_py_notin(self):
        status, err = run_probe()
        self.assertNotIn("RT-NEGIN-0123456789ab", err)
        self.assertNotEqual(status, "unsupported")
""",
                encoding="utf-8",
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                """\
// PHASE0_TRIPWIRE(bug_id="RT-NEGIN-0123456789ab", issue="https://github.com/google/zerocopy/issues/4508", owner="fixture-owner", added_date="2026-11-26", scope="neg py", rationale="neg py fails", regression_test="anneal/ci/test_phase0_neg.py::test_py_notin")
""",
                encoding="utf-8",
            )
            rep_neg = checker.check_tree(root)
            self.assertFalse(rep_neg.ok)
            err_neg = "\n".join(rep_neg.errors)
            for bid in (
                "ITREE-NEGTAG-0123456789ab",
                "ITREE-NEGSUCC-0123456789ab",
                "phase0_neg.rs::neg_refusal",
                "ITREE-STATICPY-0123456789ab",
                "RT-NEGIN-0123456789ab",
            ):
                self.assertIn(bid, err_neg)
            self.assertIn("must bind a Cargo .rs integration test", err_neg)

    def test_dataflow_numeric_rebind_shadow_base_and_lean_block(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-codex-r4-") as tmp:
            root = Path(tmp)
            base = _init_fixture_repo(root)

            # 1. Numeric-false Python (`if 0:`, `while 0:`, `if "":`, `if None:`
            # `if []:`), rebound TestCase method, constant-bound locals (Python
            # and Rust), mixed observed+const conjunction, and shadowed Rust
            # assertion macros MUST fail closed.
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-CBOUND-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4510",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard constant-bound Rust locals",
        rationale: "Constant local reason/status fails provenance",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_r4.rs::const_bound_rs",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-MIXAND-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4511",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard observed&&const-tag mixed clause",
        rationale: "Constant tag clause inside observed assert fails",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_r4.rs::mixed_clause_rs",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-SHADMAC-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4512",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard shadowed assert macro",
        rationale: "macro_rules! assert shadowing fails",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_shad.rs::shadowed_assert",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-SHADUSE-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4513",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard shadowed assert use alias",
        rationale: "use noop as assert_eq fails",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_shaduse.rs::shadowed_use",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
                ),
                encoding="utf-8",
            )
            (root / "anneal/tests/rustc-capture/tests/phase0_r4.rs").write_text(
                """\
#[test]
fn const_bound_rs() {
    let _unused = run_capture();
    let status = "unsupported".to_string();
    let reason = format!("[PHASE0_TRIPWIRE:{}]", "ITREE-CBOUND-0123456789ab");
    assert_eq!(status, "unsupported");
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-CBOUND-0123456789ab]"));
}
#[test]
fn mixed_clause_rs() {
    let out = run_capture();
    assert!(
        out.status.code() == Some(1)
            && "[PHASE0_TRIPWIRE:ITREE-MIXAND-0123456789ab]".contains("[PHASE0_TRIPWIRE:ITREE-MIXAND-0123456789ab]")
    );
    assert_eq!(out.status_str, "unsupported");
}
""",
                encoding="utf-8",
            )
            (root / "anneal/tests/rustc-capture/tests/phase0_shad.rs").write_text(
                """\
macro_rules! assert {
    ($($tt:tt)*) => {};
}
#[test]
fn shadowed_assert() {
    let (out, reason) = run_capture();
    assert!(out.status.code() == Some(1));
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-SHADMAC-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            (root / "anneal/tests/rustc-capture/tests/phase0_shaduse.rs").write_text(
                """\
use helper::noop as assert_eq;
#[test]
fn shadowed_use() {
    let (status, reason) = run_capture();
    assert_eq!(status, "unsupported");
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-SHADUSE-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                """\
// PHASE0_TRIPWIRE(bug_id="RT-NUMZERO-0123456789ab", issue="https://github.com/google/zerocopy/issues/4514", owner="fixture-owner", added_date="2026-11-26", scope="num0", rationale="if 0 must fail", regression_test="anneal/ci/test_phase0_r4.py::test_num_zero")
// PHASE0_TRIPWIRE(bug_id="RT-WHILEZERO-0123456789ab", issue="https://github.com/google/zerocopy/issues/4515", owner="fixture-owner", added_date="2026-11-26", scope="w0", rationale="while 0 must fail", regression_test="anneal/ci/test_phase0_r4.py::test_while_zero")
// PHASE0_TRIPWIRE(bug_id="RT-REBIND-0123456789ab", issue="https://github.com/google/zerocopy/issues/4516", owner="fixture-owner", added_date="2026-11-26", scope="rebind", rationale="rebind method fails", regression_test="anneal/ci/test_phase0_r4.py::test_rebound")
// PHASE0_TRIPWIRE(bug_id="RT-CONSTPY-0123456789ab", issue="https://github.com/google/zerocopy/issues/4517", owner="fixture-owner", added_date="2026-11-26", scope="constpy", rationale="const local fails", regression_test="anneal/ci/test_phase0_r4.py::test_const_locals")
""",
                encoding="utf-8",
            )
            (root / "anneal/ci/test_phase0_r4.py").write_text(
                """\
import unittest

class R4PyTests(unittest.TestCase):
    def test_num_zero(self):
        status, err = run_probe()
        if 0:
            self.assertIn("RT-NUMZERO-0123456789ab", err)
            self.assertEqual(status, "unsupported")

    def test_while_zero(self):
        status, err = run_probe()
        while "":
            self.assertIn("RT-WHILEZERO-0123456789ab", err)
            self.assertEqual(status, "unsupported")

    def test_rebound(self):
        status, err = run_probe()
        self.assertIn("RT-REBIND-0123456789ab", err)
        self.assertEqual(status, "unsupported")
    test_rebound = None

    def test_const_locals(self):
        _unused = run_probe()
        err = "[PHASE0_TRIPWIRE:RT-CONSTPY-0123456789ab]"
        status = "unsupported"
        self.assertIn("RT-CONSTPY-0123456789ab", err)
        self.assertEqual(status, "unsupported")
""",
                encoding="utf-8",
            )
            rep_r4 = checker.check_tree(root)
            self.assertFalse(rep_r4.ok)
            err_r4 = "\n".join(rep_r4.errors)
            for bid in (
                "ITREE-CBOUND-0123456789ab",
                "ITREE-MIXAND-0123456789ab",
                "ITREE-SHADMAC-0123456789ab",
                "ITREE-SHADUSE-0123456789ab",
                "RT-NUMZERO-0123456789ab",
                "RT-WHILEZERO-0123456789ab",
                "RT-REBIND-0123456789ab",
                "RT-CONSTPY-0123456789ab",
            ):
                self.assertIn(bid, err_r4)

            # 2. Lean `-- PHASE0_TRIPWIRE(...)` inside `/- ... -/` block comment
            # (including nested `/- /- ... -/ -/`) MUST be ignored completely!
            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS, encoding="utf-8"
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                "pub fn audit_stub() {}\n", encoding="utf-8"
            )
            (
                root / "anneal/trusted/lean/Trusted/MirSemantics/BlockCmt.lean"
            ).write_text(
                """\
/- outer comment
-- PHASE0_TRIPWIRE(bug_id="NOT-EVEN-PARSED", issue="BAD")
/- nested block
-- PHASE0_TRIPWIRE(bug_id="LMIRI-INERT-0123456789ab", issue="BAD")
-/
-/
def ok : Nat := 0
""",
                encoding="utf-8",
            )
            rep_blk = checker.check_tree(root)
            self.assertTrue(rep_blk.ok, rep_blk.errors)
            self.assertEqual(rep_blk.active_production_tripwires, ())

            # 3. Phase-1 cleanup also rejects constant-bound positive checks.
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "r4 clean baseline")
            clean_sha = _git(root, "rev-parse", "HEAD")
            (root / "anneal/tests/rustc-capture/tests/phase0_r4p1.rs").write_text(
                """\
#[test]
fn const_p1() {
    let ok = true;
    assert!(ok);
}
""",
                encoding="utf-8",
            )
            rep_p1_const = checker.check_phase1_cleanup(
                root,
                base=base,
                resolved_bugs=["ITREE-CONSTP1-0123456789ab"],
                test_refs={
                    "ITREE-CONSTP1-0123456789ab": "anneal/tests/rustc-capture/tests/phase0_r4p1.rs::const_p1"
                },
            )
            self.assertFalse(rep_p1_const.ok)
            self.assertIn("non-vacuous", "\n".join(rep_p1_const.errors))

    def test_unwrap_err_exit_blocks_pascal_and_phase1_layers(self):
        with tempfile.TemporaryDirectory(prefix="phase0-unwrap-layers-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)

            # 1. Idiomatic standalone .unwrap_err() / .expect_err(...) PASS,
            # while standalone unused .is_err() and negated !.is_err() FAIL.
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-ERRU-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4520",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard standalone unwrap_err acceptance",
        rationale: "Idiomatic unwrap_err should pass",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_g2r4.rs::ok_unwrap_err",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
                ),
                encoding="utf-8",
            )
            (root / "anneal/trusted/lean/Trusted/MirSemantics/Step.lean").write_text(
                """\
namespace Trusted.MirSemantics
-- PHASE0_TRIPWIRE(
--   bug_id="LMIRI-ERRE-0123456789ab",
--   issue="https://github.com/google/zerocopy/issues/4521",
--   owner="fixture-owner",
--   added_date="2026-11-26",
--   scope="Guard standalone expect_err",
--   rationale="Idiomatic expect_err should pass",
--   regression_test="anneal/tests/rustc-capture/tests/phase0_g2r4.rs::ok_expect_err"
-- )
def g := StepResult.fault .unsupported
def evalStep := g
end Trusted.MirSemantics
""",
                encoding="utf-8",
            )
            (root / "anneal/tests/rustc-capture/tests/phase0_g2r4.rs").write_text(
                """\
#[test]
fn ok_unwrap_err() {
    let err = run_capture().unwrap_err();
    assert!(err.contains("[PHASE0_TRIPWIRE:ITREE-ERRU-0123456789ab]"));
}
#[test]
fn ok_expect_err() {
    let err = run_lean_step().expect_err("expected unsupported fault");
    assert_eq!(err, FaultKind::Unsupported, "LMIRI-ERRE-0123456789ab");
}
""",
                encoding="utf-8",
            )
            rep_err_ok = checker.check_tree(root)
            self.assertTrue(rep_err_ok.ok, rep_err_ok.errors)

            # 2. Early-exit blocks, PascalCase constructors, and is_err fail.
            (root / "anneal/trusted/lean/Trusted/MirSemantics/Step.lean").unlink()
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-NOSEMI-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4522",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard if true return no semicolon",
        rationale: "Unreachable assert fails",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_g2r4_bad.rs::if_true_nosemi",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-BAREBLK-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4523",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard bare return block",
        rationale: "Unreachable after bare block fails",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_g2r4_bad.rs::bare_ret_block",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-ELSEIF-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4524",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard if true else if chain",
        rationale: "Dead else if branch stripped",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_g2r4_bad.rs::dead_else_if",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-PASCAL-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4525",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard PascalCase constructor tautology",
        rationale: "Some/FaultKind tautologies fail",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_g2r4_bad.rs::pascal_taut",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },
    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-NEGISERR-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4526",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard negated is_err",
        rationale: "Negated is_err fails",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_g2r4_bad.rs::neg_is_err",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
                ),
                encoding="utf-8",
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                '// PHASE0_TRIPWIRE(bug_id="RT-PASCAL-0123456789ab", issue="https://github.com/google/zerocopy/issues/4527", owner="fixture-owner", added_date="2026-11-26", scope="Pascal FaultKind taut", rationale="Taut fails", regression_test="anneal/tests/rustc-capture/tests/phase0_g2r4_bad.rs::pascal_rt")\n',
                encoding="utf-8",
            )
            (root / "anneal/tests/rustc-capture/tests/phase0_g2r4_bad.rs").write_text(
                """\
#[test]
fn if_true_nosemi() {
    let (status, reason) = run_capture();
    if true { return }
    assert_eq!(status, "unsupported");
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-NOSEMI-0123456789ab]"));
}
#[test]
fn bare_ret_block() {
    let (status, reason) = run_capture();
    unsafe { { return; } }
    assert_eq!(status, "unsupported");
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-BAREBLK-0123456789ab]"));
}
#[test]
fn dead_else_if() {
    let (status, reason) = run_capture();
    if true {
        let _x = 1;
    } else if flag() {
        assert_eq!(status, "unsupported");
        assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-ELSEIF-0123456789ab]"));
    }
}
#[test]
fn pascal_taut() {
    assert_eq!(Some("[PHASE0_TRIPWIRE:ITREE-PASCAL-0123456789ab]"), Some("[PHASE0_TRIPWIRE:ITREE-PASCAL-0123456789ab]"));
    assert_eq!(Some(1), Some(1));
}
#[test]
fn pascal_rt() {
    assert_eq!(FaultKind::Unsupported, FaultKind::Unsupported, "RT-PASCAL-0123456789ab");
}
#[test]
fn neg_is_err() {
    let (res, reason) = run_capture();
    assert!(!res.is_err());
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-NEGISERR-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            rep_bad = checker.check_tree(root)
            self.assertFalse(rep_bad.ok)
            err_bad = "\n".join(rep_bad.errors)
            for bid in (
                "ITREE-NOSEMI-0123456789ab",
                "ITREE-BAREBLK-0123456789ab",
                "ITREE-ELSEIF-0123456789ab",
                "ITREE-PASCAL-0123456789ab",
                "phase0_g2r4_bad.rs::neg_is_err",
                "RT-PASCAL-0123456789ab",
            ):
                self.assertIn(bid, err_bad)
            self.assertFalse(checker._rust_expr_has_observed_value("Some(1)"))
            self.assertFalse(
                checker._rust_expr_has_observed_value("FaultKind::Unsupported")
            )
            self.assertFalse(
                checker._has_meaningful_phase1_assertion(
                    "assert_eq!(Some(0), Some(0));"
                )
            )

            # 3. Phase 1 rejects unflipped .is_err() and Some(0) on
            # static_capture, while allowing RT-* permanent Err/exit refusal
            # and negated assert_ne!(..., "unsupported").
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-ISERRP1-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4528",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard unflipped is_err in Phase 1",
        rationale: "Refuse until fixed",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_p1_layers.rs::static_is_err",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
                ),
                encoding="utf-8",
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                '// PHASE0_TRIPWIRE(bug_id="RT-AUDITP1-0123456789ab", issue="https://github.com/google/zerocopy/issues/4529", owner="fixture-owner", added_date="2026-11-26", scope="Guard RT Phase 1", rationale="Permanent audit reject", regression_test="anneal/tests/audit/tests/boundary_audit.rs::rt_perm")\n',
                encoding="utf-8",
            )
            (root / "anneal/tests/rustc-capture/tests/phase0_p1_layers.rs").write_text(
                """\
#[test]
fn static_is_err() {
    let err = run_capture().unwrap_err();
    assert!(err.contains("[PHASE0_TRIPWIRE:ITREE-ISERRP1-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            (root / "anneal/tests/audit/tests/boundary_audit.rs").write_text(
                """\
#[test]
fn rt_perm() {
    let res = run_audit();
    assert!(res.is_err(), "RT-AUDITP1-0123456789ab");
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "g2r4 phase0 base")
            p0_base = _git(root, "rev-parse", "HEAD")

            # Remove both tripwires; keep static assert!(res.is_err()) -> FAIL.
            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS, encoding="utf-8"
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                "pub fn perm_audit_guard() {}\n", encoding="utf-8"
            )
            (root / "anneal/tests/rustc-capture/tests/phase0_p1_layers.rs").write_text(
                """\
#[test]
fn static_is_err() {
    let res = run_capture();
    assert!(res.is_err());
}
""",
                encoding="utf-8",
            )
            (root / "anneal/tests/audit/tests/boundary_audit.rs").write_text(
                """\
#[test]
fn rt_perm() {
    let res = run_audit();
    assert!(res.is_err(), "RT-AUDITP1-0123456789ab");
}
""",
                encoding="utf-8",
            )
            rep_iserr = checker.check_phase1_cleanup(root, base=p0_base)
            self.assertFalse(rep_iserr.ok)
            err_iserr = "\n".join(rep_iserr.errors)
            self.assertIn("static_is_err", err_iserr)
            self.assertNotIn("rt_perm", err_iserr)

            # Tautological Some(0) in Phase 1 -> FAIL.
            (root / "anneal/tests/rustc-capture/tests/phase0_p1_layers.rs").write_text(
                """\
#[test]
fn static_is_err() {
    assert_eq!(Some(0), Some(0));
}
""",
                encoding="utf-8",
            )
            rep_some0 = checker.check_phase1_cleanup(root, base=p0_base)
            self.assertFalse(rep_some0.ok)
            self.assertIn("non-vacuous", "\n".join(rep_some0.errors))

            # Negated assert_ne!(out.status_str, "unsupported") + RT -> PASS!
            (root / "anneal/tests/rustc-capture/tests/phase0_p1_layers.rs").write_text(
                """\
#[test]
fn static_is_err() {
    let out = run_capture();
    assert_ne!(out.status_str, "unsupported");
    assert!(out.status.success());
}
""",
                encoding="utf-8",
            )
            rep_clean = checker.check_phase1_cleanup(root, base=p0_base)
            self.assertTrue(rep_clean.ok, rep_clean.errors)

            # Trusted-comment (`RT-*`) permanent exit-code refusal forms (Rust
            # and Python) must be preserved when `keep_permanent_rejection`
            # applies, while `static_capture` rejects permanent exit refusal
            # and `trusted_comment` rejects vacuous status checks.
            for rt_body in (
                'let out = run_audit();\n    assert_eq!(out.status.code(), Some(1), "RT-AUDITP1-0123456789ab");',
                'let out = run_audit();\n    assert_eq!(out.status.code(), Some(2), "RT-AUDITP1-0123456789ab");',
                'let out = run_audit();\n    assert_ne!(out.status.code(), Some(0), "RT-AUDITP1-0123456789ab");',
                'let out = run_audit();\n    assert_eq!(out.status.success(), false, "RT-AUDITP1-0123456789ab");',
                'let out = run_audit();\n    assert!(out.status.code() == Some(1), "RT-AUDITP1-0123456789ab");',
                'let out = run_audit();\n    assert!(out.status.code() != Some(0), "RT-AUDITP1-0123456789ab");',
            ):
                (root / "anneal/tests/audit/tests/boundary_audit.rs").write_text(
                    f"#[test]\nfn rt_perm() {{\n    {rt_body}\n}}\n",
                    encoding="utf-8",
                )
                rep_rt = checker.check_phase1_cleanup(root, base=p0_base)
                self.assertTrue(rep_rt.ok, f"failed for {rt_body!r}: {rep_rt.errors}")

            # Non-trusted_comment `static_capture` MUST reject permanent exit
            # refusal.
            (root / "anneal/tests/rustc-capture/tests/phase0_p1_layers.rs").write_text(
                """\
#[test]
fn static_is_err() {
    let out = run_capture();
    assert_eq!(out.status.code(), Some(1));
}
""",
                encoding="utf-8",
            )
            rep_static_perm = checker.check_phase1_cleanup(root, base=p0_base)
            self.assertFalse(rep_static_perm.ok)
            self.assertIn("static_is_err", "\n".join(rep_static_perm.errors))

            # Vacuous `code().is_some()` on `trusted_comment` MUST still fail.
            (root / "anneal/tests/rustc-capture/tests/phase0_p1_layers.rs").write_text(
                """\
#[test]
fn static_is_err() {
    let out = run_capture();
    assert!(out.status.success());
}
""",
                encoding="utf-8",
            )
            (root / "anneal/tests/audit/tests/boundary_audit.rs").write_text(
                """\
#[test]
fn rt_perm() {
    let out = run_audit();
    assert_eq!(out.status.code().is_some(), true, "RT-AUDITP1-0123456789ab");
}
""",
                encoding="utf-8",
            )
            rep_rt_vac = checker.check_phase1_cleanup(root, base=p0_base)
            self.assertFalse(rep_rt_vac.ok)
            self.assertIn("rt_perm", "\n".join(rep_rt_vac.errors))

        # Python `trusted_comment` permanent returncode refusal forms.
        with tempfile.TemporaryDirectory() as tmpdir_py:
            root = Path(tmpdir_py)
            _init_fixture_repo(root)
            py_audit = root / "anneal/ci/test_rt_perm.py"
            py_audit.write_text(
                """\
import unittest
class RtTests(unittest.TestCase):
    def test_rt_py_perm(self):
        res = run_audit()
        self.assertEqual(res.returncode, 1, "RT-AUDITPY1-0123456789ab")
""",
                encoding="utf-8",
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                '// PHASE0_TRIPWIRE(bug_id="RT-AUDITPY1-0123456789ab", issue="https://github.com/google/zerocopy/issues/1", owner="fixture-owner", added_date="2026-11-26", scope="Guard Py RT", rationale="Permanent audit reject", regression_test="anneal/ci/test_rt_perm.py::test_rt_py_perm")\npub fn py_perm_guard() {}\n',
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "py rt phase0 base")
            py_base = _git(root, "rev-parse", "HEAD")

            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                "pub fn py_perm_guard() {}\n", encoding="utf-8"
            )
            for py_stmt in (
                'self.assertEqual(res.returncode, 1, "RT-AUDITPY1-0123456789ab")',
                'self.assertEqual(res.returncode, 2, "RT-AUDITPY1-0123456789ab")',
                'self.assertNotEqual(res.returncode, 0, "RT-AUDITPY1-0123456789ab")',
                'assert res.returncode == 1, "RT-AUDITPY1-0123456789ab"',
                'assert res.returncode != 0, "RT-AUDITPY1-0123456789ab"',
            ):
                py_audit.write_text(
                    f"""\
import unittest
class RtTests(unittest.TestCase):
    def test_rt_py_perm(self):
        res = run_audit()
        {py_stmt}
""",
                    encoding="utf-8",
                )
                rep_py = checker.check_phase1_cleanup(root, base=py_base)
                self.assertTrue(rep_py.ok, f"failed for {py_stmt!r}: {rep_py.errors}")

            # Non-zero `!= 1` or `assertIsNotNone(res.returncode)` still fails!
            for bad_stmt in (
                'self.assertNotEqual(res.returncode, 1, "RT-AUDITPY1-0123456789ab")',
                'self.assertIsNotNone(res.returncode, "RT-AUDITPY1-0123456789ab")',
                'assert res.returncode >= 0, "RT-AUDITPY1-0123456789ab"',
                (
                    "self.assertGreaterEqual("
                    'res.returncode, 0, "RT-AUDITPY1-0123456789ab")'
                ),
            ):
                py_audit.write_text(
                    f"""\
import unittest
class RtTests(unittest.TestCase):
    def test_rt_py_perm(self):
        res = run_audit()
        {bad_stmt}
""",
                    encoding="utf-8",
                )
                rep_bad = checker.check_phase1_cleanup(root, base=py_base)
                self.assertFalse(rep_bad.ok, f"expected fail for {bad_stmt!r}")

        # Ordering Python returncode checks and exhaustive Rust matches! checks
        # MUST fail in static_capture / non-permanent Phase-1 cleanup too.
        with tempfile.TemporaryDirectory() as tmpdir_ord:
            root = Path(tmpdir_ord)
            _init_fixture_repo(root)
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-MATCHEX-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4530",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard exhaustive matches in Phase 1",
        rationale: "Refuse until fixed",
        regression_test: "anneal/tests/rustc-capture/tests/p1_ex.rs::ex_match",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
                ),
                encoding="utf-8",
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                "// PHASE0_TRIPWIRE(\n"
                '//   bug_id="RT-ORDPY-0123456789ab",\n'
                '//   issue="https://github.com/google/zerocopy/issues/4531",\n'
                '//   owner="fixture-owner", added_date="2026-11-26",\n'
                '//   scope="Guard py ord", rationale="Refuse until fixed",\n'
                '//   regression_test="anneal/ci/test_py_ord.py::test_ord"\n'
                "// )\n"
                "pub fn guard_fn() {}\n",
                encoding="utf-8",
            )
            (root / "anneal/tests/rustc-capture/tests/p1_ex.rs").write_text(
                """\
#[test]
fn ex_match() {
    let err = run_capture().unwrap_err();
    assert!(err.contains("[PHASE0_TRIPWIRE:ITREE-MATCHEX-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            py_ord = root / "anneal/ci/test_py_ord.py"
            py_ord.write_text(
                """\
import unittest
class OrdTests(unittest.TestCase):
    def test_ord(self):
        output = run_audit()
        assert output.returncode != 0, "RT-ORDPY-0123456789ab"
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "ord and matches phase0")
            ord_base = _git(root, "rev-parse", "HEAD")

            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS, encoding="utf-8"
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                "pub fn guard_fn() {}\n", encoding="utf-8"
            )
            for bad_rust in (
                "matches!(output.status.code(), None | Some(_))",
                "matches!(output.status.code(), Some(_) | None)",
                "matches!(output.status.code(), _)",
                "matches!(output.status.exit_ok(), Ok(_) | Err(_))",
                "matches!(output.status.success(), true | false)",
                "matches!(output.status.code(), Some(code))",
                (
                    "output.status.code() == Some(0)\n"
                    "        || matches!(output.status.code(), None | Some(_))"
                ),
            ):
                (root / "anneal/tests/rustc-capture/tests/p1_ex.rs").write_text(
                    "#[test]\nfn ex_match() {\n"
                    "    let output = run_capture();\n"
                    f"    assert!({bad_rust});\n"
                    "}\n",
                    encoding="utf-8",
                )
                for bad_py in (
                    "assert output.returncode >= 0",
                    "assert 0 <= output.returncode",
                    "assert output.returncode <= 0",
                    "assert output.returncode in (0, 1)",
                    "self.assertTrue(output.returncode >= 0)",
                    "self.assertGreaterEqual(output.returncode, 0)",
                    "self.assertFalse(output.returncode < 0)",
                ):
                    py_ord.write_text(
                        f"""\
import unittest
class OrdTests(unittest.TestCase):
    def test_ord(self):
        output = run_audit()
        {bad_py}
""",
                        encoding="utf-8",
                    )
                    rep_fail = checker.check_phase1_cleanup(root, base=ord_base)
                    self.assertFalse(rep_fail.ok)
                    joined_err = "\n".join(rep_fail.errors)
                    self.assertIn("ex_match", joined_err, f"for {bad_rust!r}")
                    self.assertIn("test_ord", joined_err, f"for {bad_py!r}")

            (root / "anneal/tests/rustc-capture/tests/p1_ex.rs").write_text(
                "#[test]\nfn ex_match() {\n"
                "    let output = run_capture();\n"
                "    assert_matches!(output.status.code(), None | Some(_));\n"
                "}\n",
                encoding="utf-8",
            )
            rep_am = checker.check_phase1_cleanup(root, base=ord_base)
            self.assertFalse(rep_am.ok)
            self.assertIn("ex_match", "\n".join(rep_am.errors))

            (root / "anneal/tests/rustc-capture/tests/p1_ex.rs").write_text(
                """\
#[test]
fn ex_match() {
    let output = run_capture();
    assert!(matches!(output.status.code(), Some(0)));
}
""",
                encoding="utf-8",
            )
            py_ord.write_text(
                """\
import unittest
class OrdTests(unittest.TestCase):
    def test_ord(self):
        output = run_audit()
        assert output.returncode == 0
""",
                encoding="utf-8",
            )
            rep_pass = checker.check_phase1_cleanup(root, base=ord_base)
            self.assertTrue(rep_pass.ok, rep_pass.errors)

    def test_cli_runs_isolated_against_live_repo_and_emits_json(self):
        res = subprocess.run(
            [
                sys.executable,
                "-I",
                "-B",
                str(SCRIPT_PATH),
                "--repo-root",
                str(REPO_ROOT),
                "--mode",
                "tree",
                "--json",
            ],
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        payload = json.loads(res.stdout)
        self.assertTrue(payload["ok"])
        self.assertEqual(payload["mode"], "tree")
        self.assertIsInstance(payload["active_production_tripwires"], list)
        self.assertIn(
            "ITREE-DEMO-000000000001", payload["synthetic_selftest_tripwires"]
        )
        self.assertIn(
            "ITREE-DEMO_CRATE-000000000001",
            payload["synthetic_selftest_tripwires"],
        )


    def test_rejects_post_exhaustive_match_ifelse_loop_and_diverging_macros(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-match-exit-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)
            mexit_rel = "anneal/tests/rustc-capture/tests/phase0_mexit.rs"
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    f"""    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-MUNIT-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4601",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard exhaustive unit match early return",
        rationale: "Post-match assertions never execute",
        regression_test: "{mexit_rel}::unit_match_ret",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},
    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-MBOOL-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4602",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard exhaustive bool match diverging arms",
        rationale: "return and panic arms never fall through",
        regression_test: "{mexit_rel}::bool_match_div",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},
    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-MOPT-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4603",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard Option match with unreachable and todo",
        rationale: "Diverging std macros never fall through",
        regression_test: "{mexit_rel}::opt_match_macros",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},
    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-LETM-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4604",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard let-bound diverging match",
        rationale: "Eager let RHS match exits before assertions",
        regression_test: "{mexit_rel}::let_match_ret",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},
    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-IFELSE-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4605",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard complete if-else early exit",
        rationale: "Both branches exit before assertions",
        regression_test: "{mexit_rel}::if_else_exit",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},
    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-LOOP-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4606",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard infinite loop without break",
        rationale: "Post-loop assertions never execute",
        regression_test: "{mexit_rel}::loop_no_break",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},
    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-MGOK-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4607",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Allow guarded return arm with live fallback",
        rationale: "Reachable post-match assertions must pass",
        regression_test: "{mexit_rel}::guarded_match_live",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
                ),
                encoding="utf-8",
            )
            (root / mexit_rel).write_text(
                """\
#[test]
fn unit_match_ret() {
    let (status, r) = run_capture();
    match () { () => return }
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-MUNIT-0123456789ab]"));
}
#[test]
fn bool_match_div() {
    let (status, r) = run_capture();
    match cond() {
        true => { return; }
        false => panic!("abort early"),
    }
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-MBOOL-0123456789ab]"));
}
#[test]
fn opt_match_macros() {
    let (status, r) = run_capture();
    match maybe_val() {
        Some(_) => unreachable!(),
        None => todo!(),
    }
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-MOPT-0123456789ab]"));
}
#[test]
fn let_match_ret() {
    let (status, r) = run_capture();
    let _ = match () { () => return };
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-LETM-0123456789ab]"));
}
#[test]
fn if_else_exit() {
    let (status, r) = run_capture();
    if cond() {
        return;
    } else {
        std::process::abort();
    }
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-IFELSE-0123456789ab]"));
}
#[test]
fn loop_no_break() {
    let (status, r) = run_capture();
    loop {
        let _spin = 1;
    }
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-LOOP-0123456789ab]"));
}
#[test]
fn guarded_match_live() {
    let (status, r) = run_capture();
    match maybe_val() {
        Some(x) if x == 99 => panic!("unexpected branch"),
        _ => {}
    }
    loop {
        match cond() {
            true => break,
            false => continue,
        }
    }
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-MGOK-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            rep = checker.check_tree(root)
            self.assertFalse(rep.ok)
            err = "\n".join(rep.errors)
            for bad_id in (
                "ITREE-MUNIT-0123456789ab",
                "ITREE-MBOOL-0123456789ab",
                "ITREE-MOPT-0123456789ab",
                "ITREE-LETM-0123456789ab",
                "ITREE-IFELSE-0123456789ab",
                "ITREE-LOOP-0123456789ab",
            ):
                self.assertIn(bad_id, err)
            self.assertNotIn("ITREE-MGOK-0123456789ab", err)

    def test_requires_rust_observations_to_originate_from_capture_under_test(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-cap-origin-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)
            orig_rel = "anneal/tests/rustc-capture/tests/phase0_origin.rs"
            spoof_rel = "anneal/tests/rustc-capture/tests/phase0_spoof_fn.rs"
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    f"""    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-BBOX-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4610",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Reject black_box constant laundering",
        rationale: "black_box does not invoke capture",
        regression_test: "{orig_rel}::launder_black_box",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},
    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-EXTFN-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4611",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Reject unrecognized associated/external calls",
        rationale: "External helper cannot launder static string",
        regression_test: "{orig_rel}::launder_external",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},
    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-ECHO-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4612",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Reject non-capture Command::new(echo)",
        rationale: "Echo command does not invoke capture",
        regression_test: "{orig_rel}::launder_echo_cmd",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},
    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-FAKELOC-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4613",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Reject locally spoofed run_capture fn",
        rationale: "Local stub without capture call is pure",
        regression_test: "{spoof_rel}::spoof_local_runner",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},
    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-WRONGLAY-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4614",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Reject audit runner on static_capture tripwire",
        rationale: "static_capture requires capture origin",
        regression_test: "{orig_rel}::wrong_driver_layer",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},
    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-REALCAP-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4615",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Accept helper invoking real capture binary",
        rationale: "Transitive local capture helper is valid",
        regression_test: "{orig_rel}::real_capture_helper_ok",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
                ),
                encoding="utf-8",
            )
            (root / orig_rel).write_text(
                """\
use std::process::{Command, Output};

fn build_cap_cmd() -> Command {
    Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"))
}

fn run_via_helper() -> Output {
    build_cap_cmd().arg("capture").output().unwrap()
}

fn decode_reason(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

#[test]
fn launder_black_box() {
    let _unused = run_via_helper();
    let msg = std::hint::black_box(
        "[PHASE0_TRIPWIRE:ITREE-BBOX-0123456789ab] unsupported"
    );
    assert!(msg.contains("[PHASE0_TRIPWIRE:ITREE-BBOX-0123456789ab]"));
    assert!(msg.contains("unsupported"));
}

#[test]
fn launder_external() {
    let msg = external_mod::passthrough(
        "[PHASE0_TRIPWIRE:ITREE-EXTFN-0123456789ab] unsupported"
    );
    assert!(msg.contains("[PHASE0_TRIPWIRE:ITREE-EXTFN-0123456789ab]"));
    assert!(msg.contains("unsupported"));
}

#[test]
fn launder_echo_cmd() {
    let out = Command::new("echo")
        .arg("[PHASE0_TRIPWIRE:ITREE-ECHO-0123456789ab] unsupported")
        .output()
        .unwrap();
    let s = decode_reason(&out);
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-ECHO-0123456789ab]"));
    assert!(s.contains("unsupported"));
}

#[test]
fn wrong_driver_layer() {
    let (status, r) = run_audit();
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-WRONGLAY-0123456789ab]"));
}

#[test]
fn real_capture_helper_ok() {
    let out = run_via_helper();
    let reason = decode_reason(&out);
    assert_eq!(out.status.code(), Some(1));
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-REALCAP-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            (
                root / "anneal/tests/rustc-capture/tests/phase0_spoof_fn.rs"
            ).write_text(
                """\
fn run_capture() -> (&'static str, &'static str) {
    ("unsupported", "[PHASE0_TRIPWIRE:ITREE-FAKELOC-0123456789ab]")
}

#[test]
fn spoof_local_runner() {
    let (status, r) = run_capture();
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-FAKELOC-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            rep = checker.check_tree(root)
            self.assertFalse(rep.ok)
            err = "\n".join(rep.errors)
            for bad_id in (
                "ITREE-BBOX-0123456789ab",
                "ITREE-EXTFN-0123456789ab",
                "ITREE-ECHO-0123456789ab",
                "ITREE-FAKELOC-0123456789ab",
                "ITREE-WRONGLAY-0123456789ab",
            ):
                self.assertIn(bad_id, err)
            self.assertNotIn("ITREE-REALCAP-0123456789ab", err)
            self.assertFalse(
                checker._rust_expr_has_observed_value(
                    'std::hint::black_box("[PHASE0_TRIPWIRE:ID] unsupported")'
                )
            )

    def test_phase0_diff_crosschecks_explicit_diff_files_against_git_diff(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-difffiles-") as tmp:
            root = Path(tmp)
            base = _init_fixture_repo(root)
            test_rel = "anneal/tests/rustc-capture/tests/phase0_dchk.rs"
            phase0_rs = _with_active_entries(
                f"""    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-DCHK-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4620",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Cross-check explicit diff-files against Git",
        rationale: "Prevent hiding TCB edits outside --diff-files",
        regression_test: "{test_rel}::refuse_dchk",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
            )
            (root / checker.TRIPWIRES_REL).write_text(
                phase0_rs, encoding="utf-8"
            )
            (root / test_rel).write_text(
                """\
#[test]
fn refuse_dchk() {
    let (status, r) = run_capture();
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-DCHK-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "clean phase0 commit")
            clean_head = _git(root, "rev-parse", "HEAD")

            # Exact matching --diff-files passes cleanly.
            rep_exact = checker.check_phase0_diff(
                root,
                base=base,
                head=clean_head,
                diff_files=[checker.TRIPWIRES_REL, test_rel],
            )
            self.assertTrue(rep_exact.ok, rep_exact.errors)

            # Extra non-changed path in --diff-files fails closed.
            rep_extra = checker.check_phase0_diff(
                root,
                base=base,
                head=clean_head,
                diff_files=[
                    checker.TRIPWIRES_REL,
                    test_rel,
                    "anneal/tests/rustc-capture/tests/phase0_ghost.rs",
                ],
            )
            self.assertFalse(rep_extra.ok)
            self.assertIn(
                "--diff-files lists path(s) absent from Git diff",
                "\n".join(rep_extra.errors),
            )

            # Unauthorized trusted edit omitted from --diff-files fails closed
            # both in --head mode and in working-tree mode.
            tcb_rel = "anneal/trusted/rustc-capture/src/extract.rs"
            (root / tcb_rel).write_text("// unauthorized\n", encoding="utf-8")
            rep_wt_partial = checker.check_phase0_diff(
                root,
                base=base,
                diff_files=[checker.TRIPWIRES_REL, test_rel],
            )
            self.assertFalse(rep_wt_partial.ok)
            wt_err = "\n".join(rep_wt_partial.errors)
            self.assertIn("--diff-files omits Git-changed path(s)", wt_err)
            self.assertIn("outside isolated Phase-0", wt_err)

            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "smuggled tcb edit")
            tampered_head = _git(root, "rev-parse", "HEAD")
            rep_partial = checker.check_phase0_diff(
                root,
                base=base,
                head=tampered_head,
                diff_files=[checker.TRIPWIRES_REL, test_rel],
            )
            self.assertFalse(rep_partial.ok)
            p_err = "\n".join(rep_partial.errors)
            self.assertIn("--diff-files omits Git-changed path(s)", p_err)
            self.assertIn(tcb_rel, p_err)
            self.assertIn("outside isolated Phase-0", p_err)

    def test_rejects_monkey_patched_python_testcase_assertions_and_decorators(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-py-monkey-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)
            def _cmt(bid: str, num: int, ref: str) -> str:
                url = f"https://github.com/google/zerocopy/issues/{num}"
                return (
                    f'// PHASE0_TRIPWIRE(\n'
                    f'//   bug_id="{bid}",\n'
                    f'//   issue="{url}",\n'
                    f'//   owner="fixture-owner", added_date="2026-11-26",\n'
                    f'//   scope="monkey guard", rationale="guard",\n'
                    f'//   regression_test="{ref}"\n'
                    f'// )\n'
                )

            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                "".join(
                    [
                        _cmt(
                            "RT-MPTOP-0123456789ab",
                            4631,
                            "anneal/ci/test_phase0_mp1.py::test_top_monkey",
                        ),
                        _cmt(
                            "RT-MPHLP-0123456789ab",
                            4632,
                            "anneal/ci/test_phase0_mp2.py::test_helper_monkey",
                        ),
                        _cmt(
                            "RT-MPSET-0123456789ab",
                            4633,
                            "anneal/ci/test_phase0_mp3.py::test_setattr_monkey",
                        ),
                        _cmt(
                            "RT-MPBASE-0123456789ab",
                            4634,
                            "anneal/ci/test_phase0_mp4.py::test_base_shadow",
                        ),
                        _cmt(
                            "RT-MPDEC-0123456789ab",
                            4635,
                            "anneal/ci/test_phase0_mp5.py::test_wrapped_dec",
                        ),
                        _cmt(
                            "RT-MPOK-0123456789ab",
                            4636,
                            "anneal/ci/test_phase0_mp_ok.py::test_clean_py",
                        ),
                    ]
                ),
                encoding="utf-8",
            )
            (root / "anneal/ci/test_phase0_mp1.py").write_text(
                """\
import unittest

unittest.TestCase.assertIn = lambda *args: None

class Mp1Tests(unittest.TestCase):
    def test_top_monkey(self):
        status, err = run_probe()
        self.assertIn("RT-MPTOP-0123456789ab", err)
        self.assertEqual(status, "unsupported")
""",
                encoding="utf-8",
            )
            (root / "anneal/ci/test_phase0_mp2.py").write_text(
                """\
from unittest import TestCase

def _mute():
    TestCase.assertEqual = lambda *args: None

class Mp2Tests(TestCase):
    def test_helper_monkey(self):
        _mute()
        status, err = run_probe()
        self.assertIn("RT-MPHLP-0123456789ab", err)
        self.assertEqual(status, "unsupported")
""",
                encoding="utf-8",
            )
            (root / "anneal/ci/test_phase0_mp3.py").write_text(
                """\
import unittest

class Mp3Tests(unittest.TestCase):
    def test_setattr_monkey(self):
        setattr(unittest.TestCase, "assertIn", lambda *a: None)
        status, err = run_probe()
        self.assertIn("RT-MPSET-0123456789ab", err)
        self.assertEqual(status, "unsupported")
""",
                encoding="utf-8",
            )
            (root / "anneal/ci/test_phase0_mp4.py").write_text(
                """\
import unittest

class BaseMuted(unittest.TestCase):
    def assertIn(self, *args):
        return None

class Mp4Tests(BaseMuted):
    def test_base_shadow(self):
        status, err = run_probe()
        self.assertIn("RT-MPBASE-0123456789ab", err)
        self.assertEqual(status, "unsupported")
""",
                encoding="utf-8",
            )
            (root / "anneal/ci/test_phase0_mp5.py").write_text(
                """\
import unittest

def swallow(fn):
    return lambda self: None

class Mp5Tests(unittest.TestCase):
    @swallow
    def test_wrapped_dec(self):
        status, err = run_probe()
        self.assertIn("RT-MPDEC-0123456789ab", err)
        self.assertEqual(status, "unsupported")
""",
                encoding="utf-8",
            )
            (root / "anneal/ci/test_phase0_mp_ok.py").write_text(
                """\
import unittest

def normalize_err(text):
    return text.strip()

class MpOkTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.banner = "ready"

    def test_clean_py(self):
        status, raw_err = run_probe()
        err = normalize_err(raw_err)
        self.assertIn("RT-MPOK-0123456789ab", err)
        self.assertEqual(status, "unsupported")
""",
                encoding="utf-8",
            )
            rep = checker.check_tree(root)
            self.assertFalse(rep.ok)
            err = "\n".join(rep.errors)
            for bad_id in (
                "RT-MPTOP-0123456789ab",
                "RT-MPHLP-0123456789ab",
                "RT-MPSET-0123456789ab",
                "RT-MPBASE-0123456789ab",
                "RT-MPDEC-0123456789ab",
            ):
                self.assertIn(bad_id, err)
            self.assertNotIn("RT-MPOK-0123456789ab", err)

    def test_phase1_cleanup_preserves_original_failing_regression_witness(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase1-witness-") as tmp:
            root = Path(tmp)
            base_init = _init_fixture_repo(root)
            witness_src = (
                "pub fn bad_ptr_cast(p: *const u8) -> *const u32 "
                "{ p as *const u32 }\n"
            )
            witness_sha = hashlib.sha256(
                witness_src.encode("utf-8")
            ).hexdigest()

            fixture_dir = root / "anneal/tests/rustc-capture/tests/fixtures"
            fixture_dir.mkdir(parents=True)
            ext_fixture = fixture_dir / "ext_witness.rs"
            ext_fixture.write_text(
                "pub fn ext_bad() -> u32 { 42 }\n", encoding="utf-8"
            )

            wit_rel = "anneal/tests/rustc-capture/tests/phase0_wit.rs"
            phase0_rs = _with_active_entries(
                f"""    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-WIT-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4640",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard bad_ptr_cast witness",
        rationale: "Refuse until Phase 1 fix",
        regression_test: "{wit_rel}::refuse_bad_cast",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},
    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-EXTW-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4641",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard external file witness",
        rationale: "Refuse until Phase 1 fix",
        regression_test: "{wit_rel}::refuse_ext_file",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
            )
            (root / checker.TRIPWIRES_REL).write_text(
                phase0_rs, encoding="utf-8"
            )
            wit_test = root / wit_rel
            wit_test.write_text(
                f"""\
#[test]
fn refuse_bad_cast() {{
    let source = b"{witness_src.strip()}\\n";
    let (out, reason) = run_capture(source, "--select=bad_ptr_cast");
    assert_eq!(out.status.code(), Some(1));
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-WIT-0123456789ab]"));
}}

#[test]
fn refuse_ext_file() {{
    let ext_src = include_str!("fixtures/ext_witness.rs");
    let (out, reason) = run_capture(ext_src, "--select=ext_bad");
    assert_eq!(out.status.code(), Some(1));
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-EXTW-0123456789ab]"));
}}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "phase0 with witnesses")
            p0_sha = _git(root, "rev-parse", "HEAD")
            self.assertTrue(checker.check_tree(root).ok)

            # 1. Replacing failing witness with trivial crate in Phase 1 FAILS.
            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS, encoding="utf-8"
            )
            wit_test.write_text(
                """\
#[test]
fn refuse_bad_cast() {
    let source = b"pub fn trivial() {}\\n";
    let (out, status_json) = run_capture(source, "--select=trivial");
    assert!(out.status.success());
    assert_eq!(status_json["status"], "captured");
}

#[test]
fn refuse_ext_file() {
    let ext_src = include_str!("fixtures/ext_witness.rs");
    let (out, status_json) = run_capture(ext_src, "--select=ext_bad");
    assert!(out.status.success());
    assert_eq!(status_json["status"], "captured");
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "phase1 swapped witness")
            swapped_sha = _git(root, "rev-parse", "HEAD")
            rep_swap = checker.check_phase1_cleanup(
                root, base=p0_sha, head=swapped_sha
            )
            self.assertFalse(rep_swap.ok)
            self.assertIn(
                "must preserve original Phase-0 failing witness input",
                "\n".join(rep_swap.errors),
            )

            # 2. Keeping old witness only in an unused `let _old = ...` FAILS.
            wit_test.write_text(
                f"""\
#[test]
fn refuse_bad_cast() {{
    let _old = b"{witness_src.strip()}\\n";
    let source = b"pub fn trivial() {{}}\\n";
    let (out, status_json) = run_capture(source, "--select=bad_ptr_cast");
    assert!(out.status.success());
    assert_eq!(status_json["status"], "captured");
}}

#[test]
fn refuse_ext_file() {{
    let ext_src = include_str!("fixtures/ext_witness.rs");
    let (out, status_json) = run_capture(ext_src, "--select=ext_bad");
    assert!(out.status.success());
    assert_eq!(status_json["status"], "captured");
}}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "phase1 dead witness local")
            dead_wit_sha = _git(root, "rev-parse", "HEAD")
            rep_dead_wit = checker.check_phase1_cleanup(
                root, base=p0_sha, head=dead_wit_sha
            )
            self.assertFalse(rep_dead_wit.ok)
            self.assertIn(
                "must preserve original Phase-0 failing witness input",
                "\n".join(rep_dead_wit.errors),
            )

            # 3. Mutating external witness fixture file in Phase 1 FAILS.
            ext_fixture.write_text("pub fn trivial() {}\n", encoding="utf-8")
            wit_test.write_text(
                f"""\
#[test]
fn refuse_bad_cast() {{
    let source = b"{witness_src.strip()}\\n";
    let (out, status_json) = run_capture(source, "--select=bad_ptr_cast");
    assert!(out.status.success());
    assert_eq!(status_json["status"], "captured");
}}

#[test]
fn refuse_ext_file() {{
    let ext_src = include_str!("fixtures/ext_witness.rs");
    let (out, status_json) = run_capture(ext_src, "--select=ext_bad");
    assert!(out.status.success());
    assert_eq!(status_json["status"], "captured");
}}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "phase1 tampered ext fixture")
            ext_bad_sha = _git(root, "rev-parse", "HEAD")
            rep_ext_bad = checker.check_phase1_cleanup(
                root, base=p0_sha, head=ext_bad_sha
            )
            self.assertFalse(rep_ext_bad.ok)
            self.assertIn(
                "modified or dropped Phase-0 witness fixture file",
                "\n".join(rep_ext_bad.errors),
            )

            # 4. Restoring original external + inline witnesses PASSES cleanly,
            # and also works without --base ONLY when witness_sha256 is bound.
            ext_fixture.write_text(
                "pub fn ext_bad() -> u32 { 42 }\n", encoding="utf-8"
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "phase1 preserved witnesses")
            good_p1_sha = _git(root, "rev-parse", "HEAD")
            rep_good = checker.check_phase1_cleanup(
                root, base=p0_sha, head=good_p1_sha
            )
            self.assertTrue(rep_good.ok, rep_good.errors)

            # Without --base (or against pre-Phase-0 base_init) and no hash ->
            # FAIL; with matching --witness-sha256 -> PASS!
            rep_no_prov = checker.check_phase1_cleanup(
                root,
                base=base_init,
                head=good_p1_sha,
                resolved_bugs=["ITREE-WIT-0123456789ab"],
                test_refs={
                    "ITREE-WIT-0123456789ab": (
                        "anneal/tests/rustc-capture/tests/"
                        "phase0_wit.rs::refuse_bad_cast"
                    )
                },
            )
            self.assertFalse(rep_no_prov.ok)
            self.assertIn(
                "requires Phase-0 provenance", "\n".join(rep_no_prov.errors)
            )

            rep_hash_ok = checker.check_phase1_cleanup(
                root,
                head=good_p1_sha,
                resolved_bugs=["ITREE-WIT-0123456789ab"],
                test_refs={
                    "ITREE-WIT-0123456789ab": (
                        "anneal/tests/rustc-capture/tests/"
                        "phase0_wit.rs::refuse_bad_cast"
                    )
                },
                witness_hashes={"ITREE-WIT-0123456789ab": witness_sha},
            )
            self.assertTrue(rep_hash_ok.ok, rep_hash_ok.errors)

    def test_ignores_rust_line_markers_nested_inside_block_comments(self):
        with tempfile.TemporaryDirectory(prefix="phase0-rs-blkcmt-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)

            # 1. Nested `/* ... // PHASE0_TRIPWIRE(...) ... */` inside trusted
            # Rust files outside tripwires.rs is ignored as an active marker.
            audit_rs = root / "anneal/trusted/audit/src/lib.rs"
            audit_rs.write_text(
                """\
/* outer Rust block comment
// PHASE0_TRIPWIRE(bug_id="NOT-A-REAL-MARKER", issue="BAD")
/* nested Rust block comment
// PHASE0_TRIPWIRE(bug_id="RT-NESTBLK-0123456789ab", issue="BAD")
*/
*/
pub fn audit_ok() {}
""",
                encoding="utf-8",
            )
            rep_ignored = checker.check_tree(root)
            self.assertTrue(rep_ignored.ok, rep_ignored.errors)
            self.assertEqual(rep_ignored.active_production_tripwires, ())

            # 2. Top-level `// PHASE0_TRIPWIRE(...)` after closing `*/` IS
            # parsed and validated normally.
            audit_rs.write_text(
                """\
/* harmless block comment */
// PHASE0_TRIPWIRE(
//   bug_id="RT-AFTERBLK-0123456789ab",
//   issue="https://github.com/google/zerocopy/issues/4650",
//   owner="fixture-owner", added_date="2026-11-26",
//   scope="post-block line marker", rationale="active guard",
//   regression_test="anneal/tests/audit/tests/boundary_audit.rs::rt_after_blk"
// )
pub fn audit_guarded() {}
""",
                encoding="utf-8",
            )
            (root / "anneal/tests/audit/tests/boundary_audit.rs").write_text(
                """\
#[test]
fn rt_after_blk() {
    let res = run_audit();
    assert!(res.is_err(), "RT-AFTERBLK-0123456789ab");
}
""",
                encoding="utf-8",
            )
            rep_after = checker.check_tree(root)
            self.assertTrue(rep_after.ok, rep_after.errors)
            self.assertEqual(
                rep_after.active_production_tripwires,
                ("RT-AFTERBLK-0123456789ab",),
            )

            # 3. Inside tripwires.rs, `/* // PHASE0_TRIPWIRE(...) */` remains
            # forbidden as a commented-out production stub.
            stub_cmt = (
                "/*\n"
                '// PHASE0_TRIPWIRE(bug_id="ITREE-BLKSTUB-0123456789ab")\n'
                "*/"
            )
            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS.replace("// Header placeholder", stub_cmt),
                encoding="utf-8",
            )
            rep_stub = checker.check_tree(root)
            self.assertFalse(rep_stub.ok)
            self.assertIn(
                "commented-out PHASE0_TRIPWIRE stub",
                "\n".join(rep_stub.errors),
            )

    def test_non_doc_comment_lexing_and_preceding_cfg_comment_guards(self):
        with tempfile.TemporaryDirectory(prefix="phase0-lex-cfg-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)

            # 1. `////` (4+ slashes) and `/***` / `/**/` are non-doc comments
            # per Rust lexing rules and must trigger stub-ban checks.
            for bad_cmt in (
                '//// PHASE0_TRIPWIRE! { bug_id: "ITREE-FOURSL-0123456789ab" }',
                (
                    "/***\n"
                    'PHASE0_TRIPWIRE(bug_id="ITREE-THREEST-0123456789ab")\n'
                    "*/"
                ),
            ):
                (root / checker.TRIPWIRES_REL).write_text(
                    BASE_TRIPWIRES_RS.replace("// Header placeholder", bad_cmt),
                    encoding="utf-8",
                )
                rep_bad = checker.check_tree(root)
                self.assertFalse(rep_bad.ok)
                self.assertIn(
                    "commented-out PHASE0_TRIPWIRE stub",
                    "\n".join(rep_bad.errors),
                )

            # Genuine `///` and `/** ... */` doc comments remain doc comments.
            doc_cmt = (
                "/// Doc example: PHASE0_TRIPWIRE! { ... }\n"
                "/** Block doc example: PHASE0_TRIPWIRE(...) */"
            )
            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS.replace("// Header placeholder", doc_cmt),
                encoding="utf-8",
            )
            rep_doc = checker.check_tree(root)
            self.assertTrue(rep_doc.ok, rep_doc.errors)
            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS, encoding="utf-8"
            )

            # 2. `// PHASE0_TRIPWIRE(...)` immediately preceding an outer
            # `#[cfg(...)]` item (Runbook B placement) must be rejected when
            # guarded by `#[cfg(any())]` or `#[cfg(test)]`.
            (root / "anneal/tests/audit/tests/boundary_audit.rs").write_text(
                """\
#[test]
fn rt_pre_cfg() {
    let res = run_audit();
    assert!(res.is_err(), "RT-PRECFG-0123456789ab");
}
""",
                encoding="utf-8",
            )
            marker = (
                "// PHASE0_TRIPWIRE(\n"
                '//   bug_id="RT-PRECFG-0123456789ab",\n'
                '//   issue="https://github.com/google/zerocopy/issues/4701",\n'
                '//   owner="fixture-owner", added_date="2026-11-26",\n'
                '//   scope="preceding cfg guard",\n'
                '//   rationale="fail closed",\n'
                '//   regression_test='
                '"anneal/tests/audit/tests/boundary_audit.rs::rt_pre_cfg"\n'
                "// )\n"
            )
            for cfg_prefix in (
                "#[cfg(any())]\npub fn dead_guard() {}\n",
                "#[allow(dead_code)]\n#[cfg(test)]\npub fn test_guard() {}\n",
            ):
                (root / "anneal/trusted/audit/src/lib.rs").write_text(
                    marker + cfg_prefix, encoding="utf-8"
                )
                rep_pre = checker.check_tree(root)
                self.assertFalse(rep_pre.ok)
                self.assertIn(
                    "trusted comment PHASE0_TRIPWIRE inside",
                    "\n".join(rep_pre.errors),
                )

            # Marker on an unconditional item followed by a later
            # `#[cfg(any())]` helper in the same file must pass cleanly.
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                marker
                + "pub fn live_guard() {}\n\n"
                + "#[cfg(any())]\nfn unrelated_dead_helper() {}\n",
                encoding="utf-8",
            )
            rep_live = checker.check_tree(root)
            self.assertTrue(rep_live.ok, rep_live.errors)

    def test_assert_matches_and_match_arm_scrutinee_provenance(self):
        with tempfile.TemporaryDirectory(prefix="phase0-match-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)

            # 1. `assert_matches!` recognized in Phase-0 tree mode and in
            # Phase-1 cleanup mode (rejecting unflipped Unsupported pattern).
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                "// PHASE0_TRIPWIRE(\n"
                '//   bug_id="LMIRI-MATCHES-0123456789ab",\n'
                '//   issue="https://github.com/google/zerocopy/issues/4702",\n'
                '//   owner="fixture-owner", added_date="2026-11-26",\n'
                '//   scope="assert_matches support",\n'
                '//   rationale="hold unsupported fault",\n'
                '//   regression_test='
                '"anneal/tests/itree_diff/tests/m.rs::check_matches"\n'
                "// )\n"
                "pub fn guard_fn() {}\n",
                encoding="utf-8",
            )
            m_rs = root / "anneal/tests/itree_diff/tests/m.rs"
            m_rs.write_text(
                """\
#[test]
fn check_matches() {
    let step_fault = run_mir_eval();
    assert_matches!(
        step_fault,
        Some(FaultKind::Unsupported),
        "LMIRI-MATCHES-0123456789ab"
    );
}
""",
                encoding="utf-8",
            )
            rep_m0 = checker.check_tree(root)
            self.assertTrue(rep_m0.ok, rep_m0.errors)
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "assert_matches phase0")
            m_base = _git(root, "rev-parse", "HEAD")

            # Remove tripwire without flipping `Some(FaultKind::Unsupported)` ->
            # Phase-1 cleanup must reject.
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                "pub fn guard_fn() {}\n", encoding="utf-8"
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "remove tripwire unflipped")
            m_bad = _git(root, "rev-parse", "HEAD")
            rep_m_bad = checker.check_phase1_cleanup(
                root, base=m_base, head=m_bad
            )
            self.assertFalse(rep_m_bad.ok)
            self.assertIn(
                "must flip from unsupported-fault refusal",
                "\n".join(rep_m_bad.errors),
            )

            # Flipping pattern to `Some(FaultKind::Ub)` passes Phase-1 cleanup.
            m_rs.write_text(
                """\
#[test]
fn check_matches() {
    let step_fault = run_mir_eval();
    assert_matches!(step_fault, Some(FaultKind::Ub));
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "flip assert_matches to Ub")
            m_good = _git(root, "rev-parse", "HEAD")
            rep_m_good = checker.check_phase1_cleanup(
                root, base=m_base, head=m_good
            )
            self.assertTrue(rep_m_good.ok, rep_m_good.errors)

            # 2. Rust & Python `match` arm pattern bindings inherit scrutinee
            # provenance (and constant scrutinees still fail closed).
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-MARM-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4703",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Match arm pattern binding",
        rationale: "Fail closed until Phase 1",
        regression_test: "anneal/tests/rustc-capture/tests/m_arm.rs::arm_test",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
                ),
                encoding="utf-8",
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                "// PHASE0_TRIPWIRE(\n"
                '//   bug_id="RT-PYMATCH-0123456789ab",\n'
                '//   issue="https://github.com/google/zerocopy/issues/4704",\n'
                '//   owner="fixture-owner", added_date="2026-11-26",\n'
                '//   scope="Python match case binding",\n'
                '//   rationale="Fail closed",\n'
                '//   regression_test='
                '"anneal/ci/test_py_match.py::test_match_case"\n'
                "// )\n"
                "pub fn guard_fn() {}\n",
                encoding="utf-8",
            )
            arm_rs = root / "anneal/tests/rustc-capture/tests/m_arm.rs"
            arm_rs.write_text(
                """\
#[test]
fn arm_test() {
    let res = run_capture();
    match res {
        Ok(_) => panic!("expected capture refusal"),
        Err((status, reason)) => {
            assert_eq!(status, "unsupported");
            assert!(
                reason.contains("[PHASE0_TRIPWIRE:ITREE-MARM-0123456789ab]")
            );
        }
    }
}
""",
                encoding="utf-8",
            )
            py_m = root / "anneal/ci/test_py_match.py"
            py_m.write_text(
                """\
import unittest

class PyMatchTests(unittest.TestCase):
    def test_match_case(self):
        match run_probe():
            case (status, err):
                self.assertEqual(status, "unsupported")
                self.assertIn("RT-PYMATCH-0123456789ab", err)
            case other:
                self.fail(f"unexpected probe output: {other!r}")
""",
                encoding="utf-8",
            )
            rep_arms_ok = checker.check_tree(root)
            self.assertTrue(rep_arms_ok.ok, rep_arms_ok.errors)

            # Constant scrutinee in Rust `match` must fail closed.
            arm_rs.write_text(
                """\
#[test]
fn arm_test() {
    let _unused = run_capture();
    let fake: Result<(), (&str, &str)> = Err((
        "unsupported",
        "[PHASE0_TRIPWIRE:ITREE-MARM-0123456789ab]",
    ));
    match fake {
        Ok(_) => panic!("unexpected"),
        Err((status, reason)) => {
            assert_eq!(status, "unsupported");
            assert!(
                reason.contains("[PHASE0_TRIPWIRE:ITREE-MARM-0123456789ab]")
            );
        }
    }
}
""",
                encoding="utf-8",
            )
            rep_arm_const = checker.check_tree(root)
            self.assertFalse(rep_arm_const.ok)

    def test_python_setup_hooks_swallowed_assertions_and_self_receivers(self):
        with tempfile.TemporaryDirectory(prefix="phase0-py-hooks-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                "// PHASE0_TRIPWIRE(\n"
                '//   bug_id="RT-PYHOOK-0123456789ab",\n'
                '//   issue="https://github.com/google/zerocopy/issues/4705",\n'
                '//   owner="fixture-owner", added_date="2026-11-26",\n'
                '//   scope="Python hook and handler hardening",\n'
                '//   rationale="Fail closed",\n'
                '//   regression_test='
                '"anneal/ci/test_py_hooks.py::test_refuse"\n'
                "// )\n"
                "pub fn guard_fn() {}\n",
                encoding="utf-8",
            )
            py_f = root / "anneal/ci/test_py_hooks.py"

            bad_cases = [
                # setUp skipping test
                """\
import unittest

class HookTests(unittest.TestCase):
    def setUp(self):
        self.skipTest("disabled in setUp")
    def test_refuse(self):
        status, err = run_probe()
        self.assertEqual(status, "unsupported")
        self.assertIn("RT-PYHOOK-0123456789ab", err)
""",
                # setUpClass skipping test
                """\
import unittest

class HookTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        raise unittest.SkipTest("disabled in setUpClass")
    def test_refuse(self):
        status, err = run_probe()
        self.assertEqual(status, "unsupported")
        self.assertIn("RT-PYHOOK-0123456789ab", err)
""",
                # setUpModule skipping module
                """\
import unittest

def setUpModule():
    raise unittest.SkipTest("disabled in setUpModule")

class HookTests(unittest.TestCase):
    def test_refuse(self):
        status, err = run_probe()
        self.assertEqual(status, "unsupported")
        self.assertIn("RT-PYHOOK-0123456789ab", err)
""",
                # load_tests protocol
                """\
import unittest

def load_tests(loader, tests, pattern):
    return unittest.TestSuite()

class HookTests(unittest.TestCase):
    def test_refuse(self):
        status, err = run_probe()
        self.assertEqual(status, "unsupported")
        self.assertIn("RT-PYHOOK-0123456789ab", err)
""",
                # try / except AssertionError swallowing failure
                """\
import unittest

class HookTests(unittest.TestCase):
    def test_refuse(self):
        status, err = run_probe()
        try:
            self.assertEqual(status, "unsupported")
            self.assertIn("RT-PYHOOK-0123456789ab", err)
        except AssertionError:
            pass
""",
                # try / bare except swallowing failure
                """\
import unittest

class HookTests(unittest.TestCase):
    def test_refuse(self):
        status, err = run_probe()
        try:
            self.assertEqual(status, "unsupported")
            self.assertIn("RT-PYHOOK-0123456789ab", err)
        except:
            pass
""",
                # with self.assertRaises(AssertionError) inverting assertion
                """\
import unittest

class HookTests(unittest.TestCase):
    def test_refuse(self):
        status, err = run_probe()
        with self.assertRaises(AssertionError):
            self.assertEqual(status, "unsupported")
            self.assertIn("RT-PYHOOK-0123456789ab", err)
""",
                # non-self receiver (`fake.assertIn`) and free `assert_equal`
                """\
import unittest

def assert_equal(a, b):
    return True

class FakeHelper:
    def assertIn(self, a, b):
        return True

class HookTests(unittest.TestCase):
    def test_refuse(self):
        status, err = run_probe()
        fake = FakeHelper()
        assert_equal(status, "unsupported")
        fake.assertIn("RT-PYHOOK-0123456789ab", err)
""",
                # rebinding `self` inside test method
                """\
import unittest

class FakeSelf:
    def assertEqual(self, a, b):
        pass
    def assertIn(self, a, b):
        pass

class HookTests(unittest.TestCase):
    def test_refuse(self):
        status, err = run_probe()
        self = FakeSelf()
        self.assertEqual(status, "unsupported")
        self.assertIn("RT-PYHOOK-0123456789ab", err)
""",
            ]
            for idx, src in enumerate(bad_cases):
                py_f.write_text(src, encoding="utf-8")
                rep_bad = checker.check_tree(root)
                self.assertFalse(rep_bad.ok, f"case {idx} unexpectedly passed")

            # Re-raising `except AssertionError: raise` and `super().assert*`
            # remain accepted.
            py_f.write_text(
                """\
import unittest

class HookTests(unittest.TestCase):
    def setUp(self):
        self.ready = True
    def test_refuse(self):
        status, err = run_probe()
        try:
            super().assertEqual(status, "unsupported")
            self.assertIn("RT-PYHOOK-0123456789ab", err)
        except AssertionError:
            raise
""",
                encoding="utf-8",
            )
            rep_ok = checker.check_tree(root)
            self.assertTrue(rep_ok.ok, rep_ok.errors)

    def test_empty_for_loops_and_disjunction_branch_polarity(self):
        with tempfile.TemporaryDirectory(prefix="phase0-loop-or-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-LOOPOR-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4706",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Empty loop and disjunction checks",
        rationale: "Fail closed until Phase 1",
        regression_test: "anneal/tests/rustc-capture/tests/lo.rs::lo_test",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
                ),
                encoding="utf-8",
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                "// PHASE0_TRIPWIRE(\n"
                '//   bug_id="RT-PYLOOPOR-0123456789ab",\n'
                '//   issue="https://github.com/google/zerocopy/issues/4707",\n'
                '//   owner="fixture-owner", added_date="2026-11-26",\n'
                '//   scope="Python empty loop and disjunction",\n'
                '//   rationale="Fail closed",\n'
                '//   regression_test="anneal/ci/test_py_lo.py::test_py_lo"\n'
                "// )\n"
                "pub fn guard_fn() {}\n",
                encoding="utf-8",
            )
            lo_rs = root / "anneal/tests/rustc-capture/tests/lo.rs"
            py_lo = root / "anneal/ci/test_py_lo.py"

            valid_py = """\
import unittest

class PyLoTests(unittest.TestCase):
    def test_py_lo(self):
        for _ in range(1):
            status, err = run_probe()
            assert (status == "unsupported" or "unsupported" in err)
            self.assertIn("RT-PYLOOPOR-0123456789ab", err)
"""
            valid_rs = """\
#[test]
fn lo_test() {
    for _ in 0..=0 {
        let (out, reason, alt) = run_capture();
        assert!(
            out.status.code() == Some(1) || alt == "unsupported"
        );
        assert!(
            reason.contains("[PHASE0_TRIPWIRE:ITREE-LOOPOR-0123456789ab]")
                || alt.contains("[PHASE0_TRIPWIRE:ITREE-LOOPOR-0123456789ab]")
        );
    }
}
"""
            lo_rs.write_text(valid_rs, encoding="utf-8")
            py_lo.write_text(valid_py, encoding="utf-8")
            rep_valid = checker.check_tree(root)
            self.assertTrue(rep_valid.ok, rep_valid.errors)

            # Dead Rust `for` loops and one-sided `||` disjunctions must fail.
            for bad_rs_body in (
                "for _ in 0..0 {\n"
                "    assert_eq!(out.status.code(), Some(1));\n"
                '    assert!(reason.contains("[PHASE0_TRIPWIRE:'
                'ITREE-LOOPOR-0123456789ab]"));\n'
                "}",
                "for _ in 5..2 {\n"
                "    assert_eq!(out.status.code(), Some(1));\n"
                '    assert!(reason.contains("[PHASE0_TRIPWIRE:'
                'ITREE-LOOPOR-0123456789ab]"));\n'
                "}",
                "for _ in &[] {\n"
                "    assert_eq!(out.status.code(), Some(1));\n"
                '    assert!(reason.contains("[PHASE0_TRIPWIRE:'
                'ITREE-LOOPOR-0123456789ab]"));\n'
                "}",
                "assert!(true || (out.status.code() == Some(1) &&\n"
                '    reason.contains("[PHASE0_TRIPWIRE:'
                'ITREE-LOOPOR-0123456789ab]")));',
                "assert!(out.status.success() ||\n"
                '    (out.status.code() == Some(1) && reason.contains(\n'
                '        "[PHASE0_TRIPWIRE:ITREE-LOOPOR-0123456789ab]")));',
            ):
                lo_rs.write_text(
                    "#[test]\nfn lo_test() {\n"
                    "    let (out, reason) = run_capture();\n"
                    f"    {bad_rs_body}\n}}\n",
                    encoding="utf-8",
                )
                rep_bad_rs = checker.check_tree(root)
                self.assertFalse(rep_bad_rs.ok, bad_rs_body)

            lo_rs.write_text(valid_rs, encoding="utf-8")

            # Dead Python `for` loops and `True or (...)` / `or` fallback fail.
            for bad_py_body in (
                '        for _ in []:\n'
                '            self.assertEqual(status, "unsupported")\n'
                '            self.assertIn("RT-PYLOOPOR-0123456789ab", err)\n',
                '        for _ in range(5, 2):\n'
                '            self.assertEqual(status, "unsupported")\n'
                '            self.assertIn("RT-PYLOOPOR-0123456789ab", err)\n',
                '        assert True or (\n'
                '            status == "unsupported"\n'
                '            and "RT-PYLOOPOR-0123456789ab" in err\n'
                '        )\n',
                '        self.assertTrue(\n'
                '            True or status == "unsupported",\n'
                '            "RT-PYLOOPOR-0123456789ab",\n'
                '        )\n',
                '        self.assertEqual(\n'
                '            status or "unsupported", "unsupported"\n'
                '        )\n'
                '        self.assertIn(\n'
                '            "RT-PYLOOPOR-0123456789ab",\n'
                '            err or "RT-PYLOOPOR-0123456789ab",\n'
                '        )\n',
            ):
                py_lo.write_text(
                    "import unittest\n\n"
                    "class PyLoTests(unittest.TestCase):\n"
                    "    def test_py_lo(self):\n"
                    "        status, err = run_probe()\n"
                    + bad_py_body,
                    encoding="utf-8",
                )
                rep_bad_py = checker.check_tree(root)
                self.assertFalse(rep_bad_py.ok, bad_py_body)

    def test_if_chain_preserves_cmd_capture_and_rejects_inverted_equality_polarity(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-r7-if-eq-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-MIR-000000000002",
        issue: "https://github.com/google/zerocopy/issues/4710",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "If-chain cmd_capture preservation and equality polarity",
        rationale: "Fail closed until Phase 1",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_r7_eq.rs::eq_probe",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
                ),
                encoding="utf-8",
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                "// PHASE0_TRIPWIRE(\n"
                '//   bug_id="RT-MIR-000000000007",\n'
                '//   issue="https://github.com/google/zerocopy/issues/4711",\n'
                '//   owner="fixture-owner", added_date="2026-11-26",\n'
                '//   scope="Runtime assert_eq false check",\n'
                '//   rationale="Fail closed",\n'
                '//   regression_test="anneal/tests/rustc-capture/tests/phase0_r7_eq.rs::rt_eq_probe"\n'
                "// )\n"
                "// PHASE0_TRIPWIRE(\n"
                '//   bug_id="RT-PYEQ-0123456789ab",\n'
                '//   issue="https://github.com/google/zerocopy/issues/4712",\n'
                '//   owner="fixture-owner", added_date="2026-11-26",\n'
                '//   scope="Python assertEqual False check",\n'
                '//   rationale="Fail closed",\n'
                '//   regression_test="anneal/ci/test_r7_eq.py::test_py_eq"\n'
                "// )\n"
                "pub fn audit_guard() {}\n",
                encoding="utf-8",
            )
            rs_path = root / "anneal/tests/rustc-capture/tests/phase0_r7_eq.rs"
            py_path = root / "anneal/ci/test_r7_eq.py"

            valid_rs = """\
#[test]
fn eq_probe() {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"));
    if cfg!(unix) {
        cmd.arg("--scope=crate");
    }
    let out = cmd.output().unwrap();
    assert_eq!(out.stderr.contains("[PHASE0_TRIPWIRE:ITREE-MIR-000000000002]"), true);
    assert_eq!((out.status.success(), out.stderr.contains("unsupported")), (false, true));
}

#[test]
fn rt_eq_probe() {
    let res = run_audit();
    assert!(res.is_err(), "RT-MIR-000000000007 unsupported");
}
"""
            valid_py = """\
import unittest

class R7EqTests(unittest.TestCase):
    def test_py_eq(self):
        status, err = run_probe()
        self.assertEqual(status, "unsupported")
        self.assertIn("RT-PYEQ-0123456789ab", err)
"""
            rs_path.write_text(valid_rs, encoding="utf-8")
            py_path.write_text(valid_py, encoding="utf-8")
            rep_ok = checker.check_tree(root)
            self.assertTrue(rep_ok.ok, rep_ok.errors)

            # Reassigning cmd to non-capture inside an `if` branch still fails.
            rs_path.write_text(
                valid_rs.replace(
                    'cmd.arg("--scope=crate");',
                    'cmd = Command::new("echo");',
                ),
                encoding="utf-8",
            )
            self.assertFalse(checker.check_tree(root).ok)

            # Inverted polarity & self-equality Rust assertions must fail.
            for bad_eq in (
                'assert_eq!(false, !out.status.success() && out.stderr.contains("[PHASE0_TRIPWIRE:ITREE-MIR-000000000002]") && out.stderr.contains("unsupported"));',
                'assert_eq!(out.stderr.contains("[PHASE0_TRIPWIRE:ITREE-MIR-000000000002]"), false); assert_eq!(out.stderr.contains("unsupported"), false);',
                'assert_eq!((!out.status.success(), out.stderr.contains("[PHASE0_TRIPWIRE:ITREE-MIR-000000000002]"), out.stderr.contains("unsupported")), (!out.status.success(), out.stderr.contains("[PHASE0_TRIPWIRE:ITREE-MIR-000000000002]"), out.stderr.contains("unsupported")));',
                'assert_eq!((out.stderr.contains("[PHASE0_TRIPWIRE:ITREE-MIR-000000000002]"), out.stderr.contains("unsupported")), (false, false));',
                'assert!(out.stderr.contains("[PHASE0_TRIPWIRE:ITREE-MIR-000000000002]") == out.stderr.contains("[PHASE0_TRIPWIRE:ITREE-MIR-000000000002]")); assert_eq!(out.status.code(), Some(0));',
            ):
                rs_path.write_text(
                    "#[test]\nfn eq_probe() {\n"
                    '    let mut cmd = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"));\n'
                    "    let out = cmd.output().unwrap();\n"
                    f"    {bad_eq}\n}}\n"
                    "#[test]\nfn rt_eq_probe() {\n"
                    "    let res = run_audit();\n"
                    '    assert!(res.is_err(), "RT-MIR-000000000007 unsupported");\n'
                    "}\n",
                    encoding="utf-8",
                )
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, bad_eq)

            # Runtime `assert_eq!(res.is_err(), false, "RT-... ...")` fails.
            rs_path.write_text(
                valid_rs.replace(
                    'assert!(res.is_err(), "RT-MIR-000000000007 unsupported");',
                    'assert_eq!(res.is_err(), false, "RT-MIR-000000000007 unsupported");',
                ),
                encoding="utf-8",
            )
            self.assertFalse(checker.check_tree(root).ok)
            rs_path.write_text(valid_rs, encoding="utf-8")

            # Python inverted polarity & self-equality must fail.
            for bad_py in (
                '        self.assertEqual(False, "RT-PYEQ-0123456789ab" in err)\n'
                '        self.assertEqual("unsupported" in err, False)\n',
                '        expected = False\n'
                '        self.assertEqual(expected, "RT-PYEQ-0123456789ab" in err)\n'
                '        self.assertEqual("unsupported" in err, expected)\n',
                '        self.assertEqual((status == "unsupported", "RT-PYEQ-0123456789ab" in err), (status == "unsupported", "RT-PYEQ-0123456789ab" in err))\n',
                '        assert ("RT-PYEQ-0123456789ab" in err) is False\n'
                '        assert ("unsupported" in err) == False\n',
            ):
                py_path.write_text(
                    "import unittest\n\n"
                    "class R7EqTests(unittest.TestCase):\n"
                    "    def test_py_eq(self):\n"
                    "        status, err = run_probe()\n"
                    + bad_py,
                    encoding="utf-8",
                )
                rep_py = checker.check_tree(root)
                self.assertFalse(rep_py.ok, bad_py)

    def test_strips_dead_if_not_false_paren_false_and_inner_outer_cfg_blocks(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-r7-cfg-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-DEAD-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4713",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Dead branch and inner/outer cfg stripping",
        rationale: "Fail closed until Phase 1",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_r7_dead.rs::dead_probe",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
                ),
                encoding="utf-8",
            )
            rs_path = root / "anneal/tests/rustc-capture/tests/phase0_r7_dead.rs"
            for bad_fn in (
                '#[test]\nfn dead_probe() {\n    let (out, reason) = run_capture();\n    if !false {} else {\n        assert_eq!(out.status.code(), Some(1));\n        assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-DEAD-0123456789ab]"));\n    }\n}\n',
                '#[test]\nfn dead_probe() {\n    let (out, reason) = run_capture();\n    if (false) {\n        assert_eq!(out.status.code(), Some(1));\n        assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-DEAD-0123456789ab]"));\n    }\n}\n',
                '#[test]\nfn dead_probe() {\n    let (out, reason) = run_capture();\n    while (false) {\n        assert_eq!(out.status.code(), Some(1));\n        assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-DEAD-0123456789ab]"));\n    }\n}\n',
                '#[test]\nfn dead_probe() {\n    let (out, reason) = run_capture();\n    if (true) { return; }\n    assert_eq!(out.status.code(), Some(1));\n    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-DEAD-0123456789ab]"));\n}\n',
                '#[test]\nfn dead_probe() {\n    let (out, reason) = run_capture();\n    {\n        #![cfg(false)]\n        let _dead = 0;\n        assert_eq!(out.status.code(), Some(1));\n        assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-DEAD-0123456789ab]"));\n    }\n}\n',
                '#[test]\nfn dead_probe() {\n    #![cfg(any())]\n    let _ = ();\n    let (out, reason) = run_capture();\n    assert_eq!(out.status.code(), Some(1));\n    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-DEAD-0123456789ab]"));\n}\n',
                '#[test]\nfn dead_probe() {\n    let (out, reason) = run_capture();\n    #[cfg(any())]\n    if true {\n        let _ = ();\n    } else {\n        assert_eq!(out.status.code(), Some(1));\n        assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-DEAD-0123456789ab]"));\n    }\n}\n',
            ):
                rs_path.write_text(bad_fn, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, bad_fn)

            # Trusted comment inside `#[cfg(any())] if true {} else {}` fails.
            rs_path.write_text(
                '#[test]\nfn dead_probe() {\n    let (out, reason) = run_capture();\n    assert_eq!(out.status.code(), Some(1));\n    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-DEAD-0123456789ab]"));\n}\n',
                encoding="utf-8",
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                "pub fn f() {\n"
                "    #[cfg(any())]\n"
                "    if true {\n"
                "        let _ = ();\n"
                "    } else {\n"
                '        // PHASE0_TRIPWIRE(bug_id="RT-CFGIF-0123456789ab", issue="https://github.com/google/zerocopy/issues/4714", owner="fixture-owner", added_date="2026-11-26", scope="cfg if-else", rationale="blocked", regression_test="anneal/tests/rustc-capture/tests/phase0_r7_dead.rs::dead_probe")\n'
                "        let _ = 1;\n"
                "    }\n"
                "}\n",
                encoding="utf-8",
            )
            rep_tc = checker.check_tree(root)
            self.assertFalse(rep_tc.ok)
            self.assertIn("trusted comment PHASE0_TRIPWIRE inside", "\n".join(rep_tc.errors))

    def test_rust_scope_qualified_helpers_local_closures_structs_and_use_aliases(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-r7-prov-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    """    PHASE0_TRIPWIRE! {
        bug_id: "ITREE-PROV-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4715",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Capture provenance scoping and alias resolution",
        rationale: "Fail closed until Phase 1",
        regression_test: "anneal/tests/rustc-capture/tests/phase0_r7_prov.rs::prov_probe",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    },"""
                ),
                encoding="utf-8",
            )
            rs_path = root / "anneal/tests/rustc-capture/tests/phase0_r7_prov.rs"

            # 1. Method collision: Dummy::execute cannot spoof RealHarness.
            rs_path.write_text(
                """\
struct RealHarness;
impl RealHarness {
    fn execute(&self) -> String {
        anneal_rustc_capture::capture()
    }
}
struct Dummy { msg: &'static str }
impl Dummy {
    fn execute(&self) -> String {
        self.msg.to_string()
    }
}
#[test]
fn prov_probe() {
    let out = Dummy { msg: "[PHASE0_TRIPWIRE:ITREE-PROV-0123456789ab] unsupported" }.execute();
    assert!(out.contains("[PHASE0_TRIPWIRE:ITREE-PROV-0123456789ab]"));
    assert!(out.contains("unsupported"));
}
""",
                encoding="utf-8",
            )
            self.assertFalse(checker.check_tree(root).ok)

            # Calling RealHarness.execute() in the same file PASSES.
            rs_path.write_text(
                rs_path.read_text(encoding="utf-8").replace(
                    'Dummy { msg: "[PHASE0_TRIPWIRE:ITREE-PROV-0123456789ab] unsupported" }.execute()',
                    "RealHarness.execute()",
                ),
                encoding="utf-8",
            )
            rep_real = checker.check_tree(root)
            self.assertTrue(rep_real.ok, rep_real.errors)

            # 2. Local closure binding `let run_capture = || ...` fails closed.
            rs_path.write_text(
                """\
#[test]
fn prov_probe() {
    let run_capture = || "[PHASE0_TRIPWIRE:ITREE-PROV-0123456789ab] unsupported";
    let out = run_capture();
    assert!(out.contains("[PHASE0_TRIPWIRE:ITREE-PROV-0123456789ab]"));
    assert!(out.contains("unsupported"));
}
""",
                encoding="utf-8",
            )
            self.assertFalse(checker.check_tree(root).ok)

            # 3. Local `struct LeanTraceSession` shadowing fails closed.
            rs_path.write_text(
                """\
struct LeanTraceSession;
impl LeanTraceSession {
    fn run() -> &'static str {
        "[PHASE0_TRIPWIRE:ITREE-PROV-0123456789ab] unsupported"
    }
}
#[test]
fn prov_probe() {
    let out = LeanTraceSession::run();
    assert!(out.contains("[PHASE0_TRIPWIRE:ITREE-PROV-0123456789ab]"));
    assert!(out.contains("unsupported"));
}
""",
                encoding="utf-8",
            )
            self.assertFalse(checker.check_tree(root).ok)

            # 4. Import aliases `use std::convert::identity as run_capture;`
            # and `use std::convert as anneal_rustc_capture;` fail closed.
            for bad_alias in (
                'use std::convert::identity as run_capture;\n#[test]\nfn prov_probe() {\n    let out = run_capture("[PHASE0_TRIPWIRE:ITREE-PROV-0123456789ab] unsupported");\n    assert!(out.contains("[PHASE0_TRIPWIRE:ITREE-PROV-0123456789ab]"));\n    assert!(out.contains("unsupported"));\n}\n',
                'use std::convert as anneal_rustc_capture;\n#[test]\nfn prov_probe() {\n    let out = anneal_rustc_capture::identity("[PHASE0_TRIPWIRE:ITREE-PROV-0123456789ab] unsupported");\n    assert!(out.contains("[PHASE0_TRIPWIRE:ITREE-PROV-0123456789ab]"));\n    assert!(out.contains("unsupported"));\n}\n',
                '#[test]\nfn prov_probe() {\n    use std::convert::identity as run_capture;\n    let out = run_capture("[PHASE0_TRIPWIRE:ITREE-PROV-0123456789ab] unsupported");\n    assert!(out.contains("[PHASE0_TRIPWIRE:ITREE-PROV-0123456789ab]"));\n    assert!(out.contains("unsupported"));\n}\n',
            ):
                rs_path.write_text(bad_alias, encoding="utf-8")
                self.assertFalse(checker.check_tree(root).ok, bad_alias)

            # Valid alias `use anneal_rustc_capture::capture as ...` PASSES.
            rs_path.write_text(
                'use anneal_rustc_capture::capture as run_capture;\n'
                "#[test]\nfn prov_probe() {\n"
                "    let out = run_capture();\n"
                '    assert!(out.contains("[PHASE0_TRIPWIRE:ITREE-PROV-0123456789ab]"));\n'
                '    assert!(out.contains("unsupported"));\n'
                "}\n",
                encoding="utf-8",
            )
            rep_alias_ok = checker.check_tree(root)
            self.assertTrue(rep_alias_ok.ok, rep_alias_ok.errors)

    def test_python_finally_abort_in_else_except_and_assigned_setup_module(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-r7-py-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                "// PHASE0_TRIPWIRE(\n"
                '//   bug_id="RT-PYFIN-0123456789ab",\n'
                '//   issue="https://github.com/google/zerocopy/issues/4716",\n'
                '//   owner="fixture-owner", added_date="2026-11-26",\n'
                '//   scope="Python finally abort and setUpModule assignment",\n'
                '//   rationale="Fail closed",\n'
                '//   regression_test="anneal/ci/test_r7_py.py::test_py_fin"\n'
                "// )\n"
                "pub fn audit_guard() {}\n",
                encoding="utf-8",
            )
            py_path = root / "anneal/ci/test_r7_py.py"
            for bad_src in (
                # finally: return suppresses else assertions (except raises)
                "import unittest\n\nclass T(unittest.TestCase):\n    def test_py_fin(self):\n        try:\n            res = run_probe()\n        except ValueError:\n            raise\n        else:\n            self.assertIn('RT-PYFIN-0123456789ab', res)\n            self.assertIn('unsupported', res)\n        finally:\n            return\n",
                # finally: return suppresses both try and except assertions
                "import unittest\n\nclass T(unittest.TestCase):\n    def test_py_fin(self):\n        try:\n            res = run_probe()\n            self.assertIn('RT-PYFIN-0123456789ab', res)\n            self.assertIn('unsupported', res)\n        except ValueError:\n            res = run_probe()\n            self.assertIn('RT-PYFIN-0123456789ab', res)\n            self.assertIn('unsupported', res)\n        finally:\n            return\n",
                # finally: break suppresses else assertions in loop
                "import unittest\n\nclass T(unittest.TestCase):\n    def test_py_fin(self):\n        for _ in range(1):\n            try:\n                res = run_probe()\n            except ValueError:\n                raise\n            else:\n                self.assertIn('RT-PYFIN-0123456789ab', res)\n                self.assertIn('unsupported', res)\n            finally:\n                break\n",
                # finally: continue suppresses else assertions in loop
                "import unittest\n\nclass T(unittest.TestCase):\n    def test_py_fin(self):\n        for _ in range(1):\n            try:\n                res = run_probe()\n            except ValueError:\n                raise\n            else:\n                self.assertIn('RT-PYFIN-0123456789ab', res)\n                self.assertIn('unsupported', res)\n            finally:\n                continue\n",
                # setUpModule = helper skips entire module
                "import unittest\n\ndef helper():\n    raise unittest.SkipTest('skip')\n\nsetUpModule = helper\n\nclass T(unittest.TestCase):\n    def test_py_fin(self):\n        res = run_probe()\n        self.assertIn('RT-PYFIN-0123456789ab', res)\n        self.assertIn('unsupported', res)\n",
                # def setUpModule() calling helper that raises SkipTest
                "import unittest\n\ndef helper():\n    raise unittest.SkipTest('skip')\n\ndef setUpModule():\n    helper()\n\nclass T(unittest.TestCase):\n    def test_py_fin(self):\n        res = run_probe()\n        self.assertIn('RT-PYFIN-0123456789ab', res)\n        self.assertIn('unsupported', res)\n",
            ):
                py_path.write_text(bad_src, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, bad_src)
                self.assertIn("RT-PYFIN-0123456789ab", "\n".join(rep.errors), bad_src)

            # Clean try/else/finally without abort passes.
            py_path.write_text(
                "import unittest\n\n"
                "class T(unittest.TestCase):\n"
                "    def test_py_fin(self):\n"
                "        try:\n"
                "            res = run_probe()\n"
                "        except ValueError:\n"
                "            raise\n"
                "        else:\n"
                "            self.assertIn('RT-PYFIN-0123456789ab', res)\n"
                "            self.assertIn('unsupported', res)\n"
                "        finally:\n"
                "            pass\n",
                encoding="utf-8",
            )
            rep_ok = checker.check_tree(root)
            self.assertTrue(rep_ok.ok, rep_ok.errors)

    def test_lean_runtime_tripwire_requires_adjacent_unsupported_guard(self):
        with tempfile.TemporaryDirectory(prefix="phase0-r7-lean-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)
            step_path = (
                root / "anneal/trusted/lean/Trusted/MirSemantics/Step.lean"
            )
            step_path.write_text(
                "namespace Trusted.MirSemantics\n"
                "def existingBranch := StepResult.fault .unsupported\n"
                "def evalStep := existingBranch\n"
                "end Trusted.MirSemantics\n",
                encoding="utf-8",
            )
            (root / "anneal/tests/itree_diff/tests/phase0_rt_guard.rs").write_text(
                """\
#[test]
fn rt_guard() {
    let step_fault = run_lean_step();
    assert_eq!(step_fault, Some(FaultKind::Unsupported), "LMIRI-GUARD-0123456789ab");
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "base with preexisting unsupported")
            base_sha = _git(root, "rev-parse", "HEAD")

            marker = (
                '-- PHASE0_TRIPWIRE(bug_id="LMIRI-GUARD-0123456789ab", '
                'issue="https://github.com/google/zerocopy/issues/4717", '
                'owner="fixture-owner", added_date="2026-11-26", '
                'scope="Bind guard", rationale="Fail closed", '
                'regression_test="anneal/tests/itree_diff/tests/phase0_rt_guard.rs::rt_guard")\n'
            )

            # 1. Marker above unrelated def, string, comment, or blank -> FAIL.
            for bad_lean in (
                "namespace Trusted.MirSemantics\n" + marker + "def evalStep := 42\nend Trusted.MirSemantics\n",
                "namespace Trusted.MirSemantics\n" + marker + 'def evalStep := ".fault .unsupported"\nend Trusted.MirSemantics\n',
                "namespace Trusted.MirSemantics\n" + marker + "-- .fault .unsupported\ndef evalStep := 42\nend Trusted.MirSemantics\n",
                "namespace Trusted.MirSemantics\n" + marker + "\ndef evalStep := StepResult.fault .unsupported\nend Trusted.MirSemantics\n",
                "namespace Trusted.MirSemantics\n" + marker + "theorem thm : True := trivial\nend Trusted.MirSemantics\n",
            ):
                step_path.write_text(bad_lean, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, bad_lean)

            # 2. Marker above PRE-EXISTING guard in phase0-diff -> FAIL.
            step_path.write_text(
                "namespace Trusted.MirSemantics\n"
                + marker
                + "def existingBranch := StepResult.fault .unsupported\n"
                + "def evalStep := existingBranch\n"
                + "end Trusted.MirSemantics\n",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "marker only on existing branch")
            marker_only_sha = _git(root, "rev-parse", "HEAD")
            rep_reused = checker.check_phase0_diff(
                root,
                base=base_sha,
                head=marker_only_sha,
                allow_runtime_semantics_fallback=True,
            )
            self.assertFalse(rep_reused.ok)
            self.assertIn(
                "must add a new reachable fail-closed",
                "\n".join(rep_reused.errors),
            )

            # 3. Adding a new reachable `.error .unsupported` arm -> PASS.
            step_path.write_text(
                "namespace Trusted.MirSemantics\n"
                "def existingBranch := StepResult.fault .unsupported\n"
                "def stepOp (x : Nat) : Except FaultKind Nat :=\n"
                "  match x with\n"
                "  " + marker + "  | 0 => .error .unsupported\n"
                "  | n => .ok n\n"
                "def evalStep (x : Nat) := (existingBranch, stepOp x)\n"
                "end Trusted.MirSemantics\n",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "real new lean runtime guard")
            real_guard_sha = _git(root, "rev-parse", "HEAD")
            rep_real = checker.check_phase0_diff(
                root,
                base=base_sha,
                head=real_guard_sha,
                allow_runtime_semantics_fallback=True,
            )
            self.assertTrue(rep_real.ok, rep_real.errors)

    def test_phase1_rt_without_base_fail_closed_provenance_exit_and_witness_dataflow(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-r7-p1-") as tmp:
            root = Path(tmp)
            pre_p0_sha = _init_fixture_repo(root)
            witness_src = (
                "pub fn bad_r7_witness(p: *const u8) -> *const u32 "
                "{ p as *const u32 }\n"
            )
            witness_sha = hashlib.sha256(
                witness_src.encode("utf-8")
            ).hexdigest()
            wit_rel = "anneal/tests/rustc-capture/tests/phase0_r7_p1.rs"
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    f"""    PHASE0_TRIPWIRE! {{
        bug_id: "RT-MIR-000000000099",
        issue: "https://github.com/google/zerocopy/issues/4718",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard Phase-1 RT layer/witness/exit checks",
        rationale: "Refuse until Phase 1",
        regression_test: "{wit_rel}::refuse_r7_p1",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
                ),
                encoding="utf-8",
            )
            wit_path = root / wit_rel
            wit_path.write_text(
                f"""\
const OLD_WITNESS: &[u8] = b"{witness_src.strip()}\\n";

#[test]
fn refuse_r7_p1() {{
    let (out, reason) = run_capture(OLD_WITNESS, "--select=bad_r7_witness");
    assert_eq!(out.status.code(), Some(1));
    assert!(reason.contains("[PHASE0_TRIPWIRE:RT-MIR-000000000099]"));
}}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "r7 phase0")
            p0_sha = _git(root, "rev-parse", "HEAD")
            self.assertTrue(checker.check_tree(root).ok)

            # Remove tripwire for Phase-1 tests.
            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS, encoding="utf-8"
            )

            # 1. RT-* without --base or layer MUST reject unflipped
            # `assert!(res.is_err())` AND non-capture `run_audit()`.
            wit_path.write_text(
                f"""\
const OLD_WITNESS: &[u8] = b"{witness_src.strip()}\\n";

#[test]
fn refuse_r7_p1() {{
    let res = run_capture(OLD_WITNESS, "--select=bad_r7_witness");
    assert!(res.is_err());
}}
""",
                encoding="utf-8",
            )
            rep_rt_err = checker.check_phase1_cleanup(
                root,
                resolved_bugs=["RT-MIR-000000000099"],
                test_refs={"RT-MIR-000000000099": f"{wit_rel}::refuse_r7_p1"},
                witness_hashes={"RT-MIR-000000000099": witness_sha},
            )
            self.assertFalse(rep_rt_err.ok)
            self.assertIn("must flip", "\n".join(rep_rt_err.errors))

            wit_path.write_text(
                f"""\
const OLD_WITNESS: &[u8] = b"{witness_src.strip()}\\n";

#[test]
fn refuse_r7_p1() {{
    let res = run_audit(OLD_WITNESS, "--select=bad_r7_witness");
    assert!(res.is_ok());
}}
""",
                encoding="utf-8",
            )
            rep_rt_noncap = checker.check_phase1_cleanup(
                root,
                resolved_bugs=["RT-MIR-000000000099"],
                test_refs={"RT-MIR-000000000099": f"{wit_rel}::refuse_r7_p1"},
                witness_hashes={"RT-MIR-000000000099": witness_sha},
            )
            self.assertFalse(rep_rt_noncap.ok)
            self.assertIn("non-vacuous", "\n".join(rep_rt_noncap.errors))

            # 2. Standalone `!status.success()`, `assert_eq!(..., false)`,
            # and `!res.is_ok()` FAIL Phase-1 cleanup.
            for bad_exit in (
                'let status = run_capture(OLD_WITNESS, "--select=bad_r7_witness").status;\n    assert!(!status.success());',
                'let status = run_capture(OLD_WITNESS, "--select=bad_r7_witness").status;\n    assert_eq!(status.success(), false);',
                'let res = run_capture(OLD_WITNESS, "--select=bad_r7_witness");\n    assert!(!res.is_ok());',
            ):
                wit_path.write_text(
                    f'const OLD_WITNESS: &[u8] = b"{witness_src.strip()}\\n";\n'
                    f"#[test]\nfn refuse_r7_p1() {{\n    {bad_exit}\n}}\n",
                    encoding="utf-8",
                )
                rep_ex = checker.check_phase1_cleanup(root, base=p0_sha)
                self.assertFalse(rep_ex.ok, bad_exit)
                self.assertIn("must flip", "\n".join(rep_ex.errors))

            # 3. `black_box(OLD_WITNESS)` decoys, unasserted capture calls,
            # unused helper params, and `&& !old.is_empty()` FAIL.
            for bad_decoy in (
                'std::hint::black_box(OLD_WITNESS);\n    let (out, status) = run_capture(b"pub fn trivial() {}\\n", "--select=trivial");\n    assert!(out.status.success());\n    assert_eq!(status["status"], "captured");',
                'let _unused = run_capture(OLD_WITNESS, "--select=bad_r7_witness");\n    let (out, status) = run_capture(b"pub fn trivial() {}\\n", "--select=trivial");\n    assert!(out.status.success());\n    assert_eq!(status["status"], "captured");',
                'let old = OLD_WITNESS;\n    let (out, status) = run_capture(b"pub fn trivial() {}\\n", "--select=trivial");\n    assert!(out.status.success() && !old.is_empty());\n    assert_eq!(status["status"], "captured");',
            ):
                wit_path.write_text(
                    f'const OLD_WITNESS: &[u8] = b"{witness_src.strip()}\\n";\n'
                    f"#[test]\nfn refuse_r7_p1() {{\n    {bad_decoy}\n}}\n",
                    encoding="utf-8",
                )
                rep_dec = checker.check_phase1_cleanup(root, base=p0_sha)
                self.assertFalse(rep_dec.ok, bad_decoy)
                self.assertIn(
                    "must preserve original Phase-0 failing witness input",
                    "\n".join(rep_dec.errors),
                )

            # Helper ignoring decoy parameter via `black_box(decoy)` fails.
            wit_path.write_text(
                f"""\
const OLD_WITNESS: &[u8] = b"{witness_src.strip()}\\n";

fn wrap_capture(decoy: &[u8], real: &[u8]) -> Output {{
    std::hint::black_box(decoy);
    run_capture(real, "--select=trivial")
}}

#[test]
fn refuse_r7_p1() {{
    let out = wrap_capture(OLD_WITNESS, b"pub fn trivial() {{}}\\n");
    assert!(out.status.success());
}}
""",
                encoding="utf-8",
            )
            rep_wrap = checker.check_phase1_cleanup(root, base=p0_sha)
            self.assertFalse(rep_wrap.ok)
            self.assertIn(
                "must preserve original Phase-0 failing witness input",
                "\n".join(rep_wrap.errors),
            )

            # 4. `known_bugs` `phase0_sha` pointing to commit lacking the
            # tripwire MUST fail closed (even on substituted witness).
            wit_path.write_text(
                """\
#[test]
fn refuse_r7_p1() {
    let (out, status) = run_capture(b"pub fn trivial() {}\\n", "--select=trivial");
    assert!(out.status.success());
    assert_eq!(status["status"], "captured");
}
""",
                encoding="utf-8",
            )
            bad_kb = root / "bad_p0_sha.json"
            bad_kb.write_text(
                json.dumps(
                    [
                        {
                            "bug_id": "RT-MIR-000000000099",
                            "status": "fixed",
                            "fixed_sha": p0_sha,
                            "phase0_sha": pre_p0_sha,
                            "layer": "static_capture",
                            "regression_test": f"{wit_rel}::refuse_r7_p1",
                        }
                    ]
                ),
                encoding="utf-8",
            )
            rep_bad_p0 = checker.check_phase1_cleanup(
                root, known_bugs_path=bad_kb
            )
            self.assertFalse(rep_bad_p0.ok)
            self.assertIn(
                "does not contain an active PHASE0_TRIPWIRE",
                "\n".join(rep_bad_p0.errors),
            )

            # 4b. If `_extract_test_witness_bundle` returns None at Phase-0
            # provenance rev, fail closed instead of skipping comparison.
            missing_src_errs = checker._verify_phase1_witness_preservation(
                root,
                checker.FilesystemRepoView(root),
                "RT-MIR-000000000099",
                f"{wit_rel}::refuse_r7_p1",
                base_view=checker.GitRevRepoView(root, pre_p0_sha),
                base_test_ref=f"{wit_rel}::refuse_r7_p1",
            )
            self.assertTrue(
                any(
                    "unable to extract Phase-0 witness bundle" in e
                    for e in missing_src_errs
                ),
                missing_src_errs,
            )

            # 5. Restoring genuine witness dataflow (direct and via fs::write)
            # into observed capture PASSES!
            wit_path.write_text(
                f"""\
const OLD_WITNESS: &[u8] = b"{witness_src.strip()}\\n";

#[test]
fn refuse_r7_p1() {{
    let (out, status) = run_capture(OLD_WITNESS, "--select=bad_r7_witness");
    assert!(out.status.success());
    assert_eq!(status["status"], "captured");
}}
""",
                encoding="utf-8",
            )
            rep_good_p1 = checker.check_phase1_cleanup(root, base=p0_sha)
            self.assertTrue(rep_good_p1.ok, rep_good_p1.errors)

            wit_path.write_text(
                f"""\
const OLD_WITNESS: &[u8] = b"{witness_src.strip()}\\n";

#[test]
fn refuse_r7_p1() {{
    let dir = tempfile::tempdir().unwrap();
    let src = dir.path().join("input.rs");
    std::fs::write(&src, OLD_WITNESS).unwrap();
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"));
    cmd.arg("--source-file").arg(&src).arg("--select=bad_r7_witness");
    let out = cmd.output().unwrap();
    assert!(out.status.success());
}}
""",
                encoding="utf-8",
            )
            rep_fs_p1 = checker.check_phase1_cleanup(root, base=p0_sha)
            self.assertTrue(rep_fs_p1.ok, rep_fs_p1.errors)

            # 6. Python Phase-1 returncode refusal & witness decoys fail.
            for py_span, expected_refusal in (
                ("assert returncode != 0", True),
                ("self.assertNotEqual(0, res.returncode)", True),
                ("self.assertEqual(1, res.returncode)", True),
                ("self.assertFalse(res.returncode == 0)", True),
                ("assert res.returncode == 0", False),
                ("self.assertEqual(res.returncode, 0)", False),
            ):
                item = checker._AssertionItem(
                    full_span=py_span,
                    tested_expr=py_span,
                    is_observed=True,
                )
                self.assertEqual(
                    checker._phase1_item_refuses_exit(item, is_python=True),
                    expected_refusal,
                    py_span,
                )

            py_decoy_rel = "anneal/ci/test_r7_py_wit.py"
            (root / py_decoy_rel).write_text(
                'import unittest\n\n'
                'OLD_WIT = "pub fn py_bad_witness() {}"\n\n'
                'class PyWitTests(unittest.TestCase):\n'
                '    def test_wit(self):\n'
                '        repr(OLD_WIT)\n'
                '        res = run_probe("pub fn trivial() {}")\n'
                '        self.assertEqual(res, "ok")\n',
                encoding="utf-8",
            )
            py_bundle = checker._extract_test_witness_bundle(
                checker.FilesystemRepoView(root),
                f"{py_decoy_rel}::test_wit",
                "RT-PYWIT-0123456789ab",
            )
            self.assertIsNotNone(py_bundle)
            assert py_bundle is not None
            self.assertNotIn(
                "pub fn py_bad_witness() {}", py_bundle.witness_literals
            )
            self.assertIn("pub fn trivial() {}", py_bundle.witness_literals)

    def test_path_dominance_and_phase1_conditional_assertion_guards(self):
        with tempfile.TemporaryDirectory(prefix="phase0-r8-cfg-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)
            rs_rel = "anneal/tests/rustc-capture/tests/phase0_r8_cfg.rs"
            py_rel = "anneal/ci/test_r8_cfg.py"

            # 1. Rust split-branch tag/refusal, early return, let-else return,
            # short-circuit &&, and let-if assertions must FAIL; full dominance
            # across all normal-exit paths must PASS.
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    f"""    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-CFG-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4801",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard path dominance",
        rationale: "Every live exit path must assert tag and refusal",
        regression_test: "{rs_rel}::dom_test",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
                ),
                encoding="utf-8",
            )
            bad_rust_bodies = (
                # Split across if/else: neither path checks both.
                """\
#[test]
fn dom_test() {
    let (status, r) = run_capture();
    if cond() {
        assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-CFG-0123456789ab]"));
    } else {
        assert_eq!(status, "unsupported");
    }
}
""",
                # Early return skips assertions on one branch.
                """\
#[test]
fn dom_test() {
    let (status, r) = run_capture();
    if !cond() {
        return;
    }
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-CFG-0123456789ab]"));
}
""",
                # let ... else { return; } skips assertions on divergence.
                """\
#[test]
fn dom_test() {
    let Ok((status, r)) = run_capture() else {
        return;
    };
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-CFG-0123456789ab]"));
}
""",
                # Short-circuit && makes nested block assertion conditional.
                """\
#[test]
fn dom_test() {
    let (status, r) = run_capture();
    let _ = cond() && {
        assert_eq!(status, "unsupported");
        assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-CFG-0123456789ab]"));
        true
    };
}
""",
                # `let _ = if cond { ... };` without else skips assertions.
                """\
#[test]
fn dom_test() {
    let (status, r) = run_capture();
    let _ = if cond() {
        assert_eq!(status, "unsupported");
        assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-CFG-0123456789ab]"));
    };
}
""",
                # Match arms split tag vs refusal across branches.
                """\
#[test]
fn dom_test() {
    let (status, r) = run_capture();
    match kind() {
        Kind::A => assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-CFG-0123456789ab]")),
        Kind::B => assert_eq!(status, "unsupported"),
    }
}
""",
            )
            for idx, body in enumerate(bad_rust_bodies):
                (root / rs_rel).write_text(body, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, f"case {idx} unexpectedly passed")

            # Valid: else branch panics (failing exit) or checks both.
            good_rust_bodies = (
                """\
#[test]
fn dom_test() {
    let (status, r) = run_capture();
    if cond() {
        assert_eq!(status, "unsupported");
        assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-CFG-0123456789ab]"));
    } else {
        panic!("expected refusal");
    }
}
""",
                """\
#[test]
fn dom_test() {
    let (status, r) = run_capture();
    if cond() {
        assert_eq!(status, "unsupported");
        assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-CFG-0123456789ab]"));
    } else {
        assert!(r.contains("unsupported") && r.contains("[PHASE0_TRIPWIRE:ITREE-CFG-0123456789ab]"));
    }
}
""",
            )
            for idx, body in enumerate(good_rust_bodies):
                (root / rs_rel).write_text(body, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertTrue(rep.ok, f"good case {idx}: {rep.errors}")

            # 2. Python split-branch, early return, non-exhaustive match, and
            # short-circuit `and` must FAIL; `else: self.fail(...)` PASSES.
            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS, encoding="utf-8"
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                '// PHASE0_TRIPWIRE(bug_id="RT-PYCFG-0123456789ab", '
                'issue="https://github.com/google/zerocopy/issues/4802", '
                'owner="fixture-owner", added_date="2026-11-26", '
                'scope="Python path dominance", rationale="Dominate exits", '
                f'regression_test="{py_rel}::test_dom")\n',
                encoding="utf-8",
            )
            bad_py_bodies = (
                """\
import unittest
class DomTests(unittest.TestCase):
    def test_dom(self):
        status, err = run_probe()
        if cond():
            self.assertIn("RT-PYCFG-0123456789ab", err)
        else:
            self.assertEqual(status, "unsupported")
""",
                """\
import unittest
class DomTests(unittest.TestCase):
    def test_dom(self):
        status, err = run_probe()
        if not cond():
            return
        self.assertEqual(status, "unsupported")
        self.assertIn("RT-PYCFG-0123456789ab", err)
""",
                """\
import unittest
class DomTests(unittest.TestCase):
    def test_dom(self):
        match run_probe():
            case (status, err):
                self.assertEqual(status, "unsupported")
                self.assertIn("RT-PYCFG-0123456789ab", err)
""",
                """\
import unittest
class DomTests(unittest.TestCase):
    def test_dom(self):
        status, err = run_probe()
        cond() and (self.assertEqual(status, "unsupported") or self.assertIn("RT-PYCFG-0123456789ab", err))
""",
            )
            for idx, body in enumerate(bad_py_bodies):
                (root / py_rel).write_text(body, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, f"py bad case {idx} passed")

            (root / py_rel).write_text(
                """\
import unittest
class DomTests(unittest.TestCase):
    def test_dom(self):
        status, err = run_probe()
        if cond():
            self.assertEqual(status, "unsupported")
            self.assertIn("RT-PYCFG-0123456789ab", err)
        else:
            self.fail("unexpected non-refusal")
""",
                encoding="utf-8",
            )
            rep_py_ok = checker.check_tree(root)
            self.assertTrue(rep_py_ok.ok, rep_py_ok.errors)

            # 3. Phase-1 cleanup must reject conditional/tautological checks
            # (`if output.status.success() { assert!(output.status.success()); }`,
            # early return, self-equality, `p || !p`, Python `if success:`).
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                "pub fn ok() {}\n", encoding="utf-8"
            )
            (root / py_rel).unlink()
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    f"""    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-P1COND-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4803",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard Phase-1 conditional assert",
        rationale: "Phase-1 must assert on every successful path",
        regression_test: "{rs_rel}::p1_flip",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
                ),
                encoding="utf-8",
            )
            (root / rs_rel).write_text(
                """\
#[test]
fn p1_flip() {
    let out = run_capture("pub fn witness_p1() {}");
    assert_eq!(out.status.code(), Some(1));
    assert!(out.stderr.contains("[PHASE0_TRIPWIRE:ITREE-P1COND-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "phase0 for p1 cond")
            p0_sha = _git(root, "rev-parse", "HEAD")

            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS, encoding="utf-8"
            )
            bad_p1_rust = (
                """\
#[test]
fn p1_flip() {
    let output = run_capture("pub fn witness_p1() {}");
    if output.status.success() {
        assert!(output.status.success());
    }
}
""",
                """\
#[test]
fn p1_flip() {
    let res = run_capture("pub fn witness_p1() {}");
    if res.is_ok() {
        assert!(res.is_ok());
    }
}
""",
                """\
#[test]
fn p1_flip() {
    let output = run_capture("pub fn witness_p1() {}");
    if !output.status.success() {
        return;
    }
    assert!(output.status.success());
}
""",
                """\
#[test]
fn p1_flip() {
    let out = run_capture("pub fn witness_p1() {}");
    assert_eq!(out.status.success(), out.status.success());
}
""",
                """\
#[test]
fn p1_flip() {
    let out = run_capture("pub fn witness_p1() {}");
    assert!(out.status.success() || !out.status.success());
}
""",
            )
            for idx, body in enumerate(bad_p1_rust):
                (root / rs_rel).write_text(body, encoding="utf-8")
                rep_p1 = checker.check_phase1_cleanup(root, base=p0_sha)
                self.assertFalse(rep_p1.ok, f"bad p1 case {idx} passed")

            for idx, body in enumerate(
                (
                    """\
#[test]
fn p1_flip() {
    let output = run_capture("pub fn witness_p1() {}");
    assert!(output.status.success());
}
""",
                    """\
#[test]
fn p1_flip() {
    let output = run_capture("pub fn witness_p1() {}");
    if output.status.success() {
        assert!(output.status.success());
    } else {
        panic!("capture failed");
    }
}
""",
                )
            ):
                (root / rs_rel).write_text(body, encoding="utf-8")
                rep_p1_ok = checker.check_phase1_cleanup(root, base=p0_sha)
                self.assertTrue(
                    rep_p1_ok.ok, f"good p1 case {idx}: {rep_p1_ok.errors}"
                )

            # Python Phase-1 `if success: self.assertTrue(success)` -> FAIL.
            py_p1_src = (
                "import unittest\n"
                "class P1Tests(unittest.TestCase):\n"
                "    def test_p1(self):\n"
                "        res = run_probe('pub fn w() {}')\n"
                "        if res.returncode == 0:\n"
                "            self.assertEqual(res.returncode, 0)\n"
            )
            _r, py_items, py_cfg, py_err = (
                checker._extract_python_test_assertion_items_with_cfg(
                    py_p1_src, "anneal/ci/test_p1.py", "test_p1"
                )
            )
            self.assertIsNone(py_err)
            assert py_items is not None
            py_p1_errs = checker._validate_phase1_flipped_items(
                "RT-P1PY-0123456789ab",
                "anneal/ci/test_p1.py::test_p1",
                py_items,
                is_python=True,
                layer="trusted_comment",
                cfg=py_cfg,
            )
            self.assertTrue(py_p1_errs)

    def test_lean_reachability_and_tripwires_unreferenced_helpers(self):
        with tempfile.TemporaryDirectory(prefix="phase0-reach-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)

            # 1. Lean runtime semantics reachability: dead defs, dead cycles,
            # theorem-only refs, CanaryFixtures refs, unused `let _`/`where`,
            # `if false`, unimported files, and dead-def diff inflation FAIL.
            step_path = (
                root / "anneal/trusted/lean/Trusted/MirSemantics/Step.lean"
            )
            root_lean = root / "anneal/trusted/lean/Trusted/MirSemantics.lean"
            extra_lean = (
                root / "anneal/trusted/lean/Trusted/MirSemantics/Extra.lean"
            )
            canary_lean = (
                root
                / "anneal/trusted/lean/Trusted/MirSemantics/CanaryFixtures.lean"
            )
            rt_test = root / "anneal/tests/itree_diff/tests/phase0_r8_lean.rs"
            rt_test.write_text(
                """\
#[test]
fn rt_reach() {
    let fault = run_lean_step();
    assert_eq!(fault, Some(FaultKind::Unsupported), "LMIRI-RCH-0123456789ab");
}
""",
                encoding="utf-8",
            )
            marker = (
                '-- PHASE0_TRIPWIRE(bug_id="LMIRI-RCH-0123456789ab", '
                'issue="https://github.com/google/zerocopy/issues/4810", '
                'owner="fixture-owner", added_date="2026-11-26", '
                'scope="Guard Lean reachability", rationale="Must run", '
                'regression_test="anneal/tests/itree_diff/tests/phase0_r8_lean.rs::rt_reach")\n'
            )
            root_lean.write_text(
                "import Trusted.MirSemantics.Step\n", encoding="utf-8"
            )
            canary_lean.write_text(
                "def canaryRun := phase0Guard\n", encoding="utf-8"
            )
            dead_lean_cases = (
                # Dead standalone def (even referenced by CanaryFixtures).
                "namespace Trusted.MirSemantics\n"
                + marker
                + "def phase0Guard := StepResult.fault .unsupported\n"
                + "def evalStep := StepResult.ok\n"
                + "end Trusted.MirSemantics\n",
                # Dead mutual/helper chain not called from evalStep.
                "namespace Trusted.MirSemantics\n"
                + "def deadA := deadB\n"
                + marker
                + "def deadB := StepResult.fault .unsupported\n"
                + "def evalStep := StepResult.ok\n"
                + "end Trusted.MirSemantics\n",
                # Referenced only by a theorem.
                "namespace Trusted.MirSemantics\n"
                + marker
                + "def thmOnly := StepResult.fault .unsupported\n"
                + "theorem t : thmOnly = thmOnly := rfl\n"
                + "def evalStep := StepResult.ok\n"
                + "end Trusted.MirSemantics\n",
                # Discarded via `let _ := phase0Guard`.
                "namespace Trusted.MirSemantics\n"
                + marker
                + "def phase0Guard := StepResult.fault .unsupported\n"
                + "def evalStep :=\n"
                + "  let _ := phase0Guard\n"
                + "  StepResult.ok\n"
                + "end Trusted.MirSemantics\n",
                # Guard under `if false then ...`.
                "namespace Trusted.MirSemantics\n"
                + "def evalStep :=\n"
                + "  "
                + marker
                + "  if false then StepResult.fault .unsupported else StepResult.ok\n"
                + "end Trusted.MirSemantics\n",
                # Unused local `where` helper.
                "namespace Trusted.MirSemantics\n"
                + "def evalStep := StepResult.ok\n"
                + "where\n"
                + "  "
                + marker
                + "  unusedHelper := StepResult.fault .unsupported\n"
                + "end Trusted.MirSemantics\n",
            )
            for idx, src in enumerate(dead_lean_cases):
                step_path.write_text(src, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, f"dead lean case {idx} passed")

            # Unimported submodule fails when MirSemantics.lean exists.
            step_path.write_text(
                "namespace Trusted.MirSemantics\n"
                "def evalStep := extraGuard\n"
                "end Trusted.MirSemantics\n",
                encoding="utf-8",
            )
            extra_lean.write_text(
                "namespace Trusted.MirSemantics\n"
                + marker
                + "def extraGuard := StepResult.fault .unsupported\n"
                + "end Trusted.MirSemantics\n",
                encoding="utf-8",
            )
            rep_unimp = checker.check_tree(root)
            self.assertFalse(rep_unimp.ok)

            # Importing Extra.lean makes evalStep -> extraGuard reachable.
            root_lean.write_text(
                "import Trusted.MirSemantics.Extra\n"
                "import Trusted.MirSemantics.Step\n",
                encoding="utf-8",
            )
            rep_imp = checker.check_tree(root)
            self.assertTrue(rep_imp.ok, rep_imp.errors)

            # Phase-0 diff: dead-def guard inflation must not count as new.
            extra_lean.unlink()
            root_lean.write_text(
                "import Trusted.MirSemantics.Step\n", encoding="utf-8"
            )
            step_path.write_text(
                "namespace Trusted.MirSemantics\n"
                "def existingBranch := StepResult.fault .unsupported\n"
                "def evalStep := existingBranch\n"
                "end Trusted.MirSemantics\n",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "lean reach base")
            lean_base = _git(root, "rev-parse", "HEAD")

            step_path.write_text(
                "namespace Trusted.MirSemantics\n"
                + marker
                + "def existingBranch := StepResult.fault .unsupported\n"
                + "def deadNew := StepResult.fault .unsupported\n"
                + "def evalStep := existingBranch\n"
                + "end Trusted.MirSemantics\n",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "dead lean inflation")
            lean_inflate = _git(root, "rev-parse", "HEAD")
            rep_inf = checker.check_phase0_diff(
                root,
                base=lean_base,
                head=lean_inflate,
                allow_runtime_semantics_fallback=True,
            )
            self.assertFalse(rep_inf.ok)

            # 2. Unreferenced non-test helpers in tripwires.rs must fail in both
            # --mode tree and --mode phase1-cleanup, while active shared helpers
            # and #[cfg(test)] helpers pass.
            step_path.unlink()
            root_lean.unlink()
            canary_lean.unlink()
            stale_helper_rs = BASE_TRIPWIRES_RS.replace(
                "// === PHASE 0 MUTABLE REGISTRY END ===",
                "fn stale_leftover_pred(_ctx: &TripwireContext) -> bool { true }\n"
                "// === PHASE 0 MUTABLE REGISTRY END ===",
            )
            (root / checker.TRIPWIRES_REL).write_text(
                stale_helper_rs, encoding="utf-8"
            )
            rep_stale = checker.check_tree(root)
            self.assertFalse(rep_stale.ok)
            self.assertIn("unreferenced", "\n".join(rep_stale.errors))

            # Dead helper referenced only from #[cfg(test)] still FAILS.
            test_only_ref_rs = stale_helper_rs.replace(
                "    fn local_fixture() {",
                "    #[test]\n    fn ref_stale() { let _ = super::stale_leftover_pred; }\n    fn local_fixture() {",
            )
            (root / checker.TRIPWIRES_REL).write_text(
                test_only_ref_rs, encoding="utf-8"
            )
            rep_test_ref = checker.check_tree(root)
            self.assertFalse(rep_test_ref.ok)
            self.assertIn("unreferenced", "\n".join(rep_test_ref.errors))

            # Dead mutually recursive helper cycle still FAILS.
            cycle_rs = BASE_TRIPWIRES_RS.replace(
                "// === PHASE 0 MUTABLE REGISTRY END ===",
                "fn cycle_a() -> bool { cycle_b() }\n"
                "fn cycle_b() -> bool { cycle_a() }\n"
                "// === PHASE 0 MUTABLE REGISTRY END ===",
            )
            (root / checker.TRIPWIRES_REL).write_text(cycle_rs, encoding="utf-8")
            rep_cyc = checker.check_tree(root)
            self.assertFalse(rep_cyc.ok)
            self.assertIn("unreferenced", "\n".join(rep_cyc.errors))

            # Shared helper + transitive sub-helper used by active entry PASSES,
            # and leaving it behind after Phase-1 deletion FAILS phase1-cleanup.
            rs_h = "anneal/tests/rustc-capture/tests/phase0_r8_helper.rs"
            (root / rs_h).write_text(
                """\
#[test]
fn helper_refuse() {
    let (status, r) = run_capture("pub fn hwit() {}");
    assert_eq!(status, "unsupported");
    assert!(r.contains("[PHASE0_TRIPWIRE:ITREE-HLP-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            active_with_helper_rs = _with_active_entries(
                f"""    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-HLP-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4811",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard with helper",
        rationale: "Helper used by active entry",
        regression_test: "{rs_h}::helper_refuse",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::Body(active_pred),
    }},"""
            ).replace(
                "// === PHASE 0 MUTABLE REGISTRY END ===",
                "fn sub_pred() -> bool { true }\n"
                "fn active_pred(_ctx: &TripwireContext) -> bool { sub_pred() }\n"
                "// === PHASE 0 MUTABLE REGISTRY END ===",
            ).replace(
                "    fn local_fixture() {",
                "    fn test_only_helper() {}\n    fn local_fixture() {",
            )
            (root / checker.TRIPWIRES_REL).write_text(
                active_with_helper_rs, encoding="utf-8"
            )
            rep_hlp_ok = checker.check_tree(root)
            self.assertTrue(rep_hlp_ok.ok, rep_hlp_ok.errors)
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "phase0 with helper")
            hlp_p0 = _git(root, "rev-parse", "HEAD")

            # Phase-1 deletes entry and flips test, leaving `active_pred`.
            (root / rs_h).write_text(
                """\
#[test]
fn helper_refuse() {
    let out = run_capture("pub fn hwit() {}");
    assert!(out.status.success());
}
""",
                encoding="utf-8",
            )
            (root / checker.TRIPWIRES_REL).write_text(
                stale_helper_rs, encoding="utf-8"
            )
            rep_p1_dead = checker.check_phase1_cleanup(root, base=hlp_p0)
            self.assertFalse(rep_p1_dead.ok)
            self.assertIn("unreferenced", "\n".join(rep_p1_dead.errors))

    def test_python_provenance_doc_stubs_expect_err_unittest_and_taint(self):
        with tempfile.TemporaryDirectory(prefix="phase0-prov-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)

            # 1. Fail-closed Python observation provenance.
            py_prov = "anneal/ci/test_r8_prov.py"
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                '// PHASE0_TRIPWIRE(bug_id="RT-PROV-0123456789ab", '
                'issue="https://github.com/google/zerocopy/issues/4820", '
                'owner="fixture-owner", added_date="2026-11-26", '
                'scope="Python provenance", rationale="Reject spoofed calls", '
                f'regression_test="{py_prov}::test_prov")\n',
                encoding="utf-8",
            )
            bad_py_provs = (
                # Unrecognized stdlib call `copy.copy`.
                """\
import copy, unittest
class ProvTests(unittest.TestCase):
    def test_prov(self):
        err = copy.copy("RT-PROV-0123456789ab unsupported")
        self.assertIn("RT-PROV-0123456789ab", err)
        self.assertIn("unsupported", err)
""",
                # Aliasing `copy.copy` as `run_probe`.
                """\
import unittest
from copy import copy as run_probe
class ProvTests(unittest.TestCase):
    def test_prov(self):
        err = run_probe("RT-PROV-0123456789ab unsupported")
        self.assertIn("RT-PROV-0123456789ab", err)
        self.assertIn("unsupported", err)
""",
                # Local constant helper named `run_probe`.
                """\
import unittest
def run_probe():
    return "RT-PROV-0123456789ab unsupported"
class ProvTests(unittest.TestCase):
    def test_prov(self):
        err = run_probe()
        self.assertIn("RT-PROV-0123456789ab", err)
        self.assertIn("unsupported", err)
""",
                # Subprocess shell/echo/python -c spoofs.
                """\
import subprocess, unittest
class ProvTests(unittest.TestCase):
    def test_prov(self):
        res = subprocess.run(["echo", "RT-PROV-0123456789ab unsupported"], capture_output=True, text=True)
        self.assertIn("RT-PROV-0123456789ab", res.stdout)
        self.assertIn("unsupported", res.stdout)
""",
                """\
import subprocess, sys, unittest
class ProvTests(unittest.TestCase):
    def test_prov(self):
        res = subprocess.run([sys.executable, "-c", "print('RT-PROV-0123456789ab unsupported')"], capture_output=True, text=True)
        self.assertIn("RT-PROV-0123456789ab", res.stdout)
        self.assertIn("unsupported", res.stdout)
""",
                """\
import subprocess, unittest
class ProvTests(unittest.TestCase):
    def test_prov(self):
        res = subprocess.run("echo RT-PROV-0123456789ab unsupported", shell=True, capture_output=True, text=True)
        self.assertIn("RT-PROV-0123456789ab", res.stdout)
        self.assertIn("unsupported", res.stdout)
""",
                # Unittest internal skip / expected-failure flags.
                """\
import unittest
class ProvTests(unittest.TestCase):
    __unittest_skip__ = True
    def test_prov(self):
        err = run_probe()
        self.assertIn("RT-PROV-0123456789ab", err)
        self.assertIn("unsupported", err)
""",
                """\
import unittest
class ProvTests(unittest.TestCase):
    __unittest_expecting_failure__ = True
    def test_prov(self):
        err = run_probe()
        self.assertIn("RT-PROV-0123456789ab", err)
        self.assertIn("unsupported", err)
""",
                """\
import unittest
class ProvTests(unittest.TestCase):
    if True:
        __unittest_skip__ = True
    def test_prov(self):
        err = run_probe()
        self.assertIn("RT-PROV-0123456789ab", err)
        self.assertIn("unsupported", err)
""",
                # Python tuple, f-string, and const-side equality spoofs.
                """\
import unittest
class ProvTests(unittest.TestCase):
    def test_prov(self):
        err = run_probe()
        self.assertIn("RT-PROV-0123456789ab unsupported", (err, "RT-PROV-0123456789ab unsupported"))
""",
                """\
import unittest
class ProvTests(unittest.TestCase):
    def test_prov(self):
        err = run_probe()
        self.assertIn("RT-PROV-0123456789ab unsupported", f"{err} RT-PROV-0123456789ab unsupported")
""",
                """\
import unittest
class ProvTests(unittest.TestCase):
    def test_prov(self):
        out = run_probe()
        fake = "RT-PROV-0123456789ab unsupported"
        self.assertEqual(out == "clean", "RT-PROV-0123456789ab unsupported" in fake)
""",
                """\
import unittest
class ProvTests(unittest.TestCase):
    def test_prov(self):
        out = run_probe()
        fake = "RT-PROV-0123456789ab unsupported"
        assert (out == "clean") == ("RT-PROV-0123456789ab unsupported" in fake)
""",
            )
            for idx, src in enumerate(bad_py_provs):
                (root / py_prov).write_text(src, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, f"bad py case {idx} passed")

            # Approved subprocess & imported anneal checker calls PASS.
            for idx, src in enumerate(
                (
                    """\
import subprocess, sys, unittest
def _run_tool():
    return subprocess.run([sys.executable, "anneal/ci/check_phase0_tripwires.py"], capture_output=True, text=True)
class ProvTests(unittest.TestCase):
    def test_prov(self):
        res = _run_tool()
        self.assertIn("RT-PROV-0123456789ab", res.stderr)
        self.assertIn("unsupported", res.stderr)
""",
                    """\
import unittest
import check_phase0_tripwires as chk
class ProvTests(unittest.TestCase):
    def test_prov(self):
        rep = chk.check_tree(self.repo_root)
        self.assertIn("RT-PROV-0123456789ab", rep.errors[0])
        self.assertIn("unsupported", rep.errors[0])
""",
                )
            ):
                (root / py_prov).write_text(src, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertTrue(rep.ok, f"good py case {idx}: {rep.errors}")

            # 2. Multi-line `/** ... */` doc-comment stubs inside and outside
            # ACTIVE_PHASE0_TRIPWIRES, and `#[doc = "..."]` must FAIL.
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                "pub fn ok() {}\n", encoding="utf-8"
            )
            (root / py_prov).unlink()
            for idx, bad_doc_rs in enumerate(
                (
                    _with_active_entries(
                        "    /**\n"
                        '     * PHASE0_TRIPWIRE! { bug_id: "ITREE-DOC-123456789abc", issue: "invalid" }\n'
                        "     */"
                    ),
                    BASE_TRIPWIRES_RS.replace(
                        "// Header placeholder",
                        "/**\n"
                        ' * PHASE0_TRIPWIRE! { bug_id: "ITREE-DOC-123456789abc", issue: "invalid" }\n'
                        " */",
                    ),
                    BASE_TRIPWIRES_RS.replace(
                        "// Header placeholder",
                        '#[doc = "PHASE0_TRIPWIRE! { bug_id: ITREE-DOC-123456789abc }"]',
                    ),
                )
            ):
                (root / checker.TRIPWIRES_REL).write_text(
                    bad_doc_rs, encoding="utf-8"
                )
                self.assertFalse(
                    checker.check_tree(root).ok, f"bad doc case {idx} passed"
                )

            # 3. Rust `.expect_err(...)` panic string spoofs, receiver literal
            # spoofs, const-side equality, container literal, and `format!`
            # needle injection must FAIL.
            rs_spoof = "anneal/tests/rustc-capture/tests/phase0_r8_spoof.rs"
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    f"""    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-SPF-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4821",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Guard expect_err and eq taint",
        rationale: "Block panic-msg and const-side spoofs",
        regression_test: "{rs_spoof}::spoof_test",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
                ),
                encoding="utf-8",
            )
            bad_rust_spoofs = (
                # expect_err panic message carries tag + unsupported.
                """\
#[test]
fn spoof_test() {
    let _ = run_capture().expect_err("[PHASE0_TRIPWIRE:ITREE-SPF-0123456789ab] unsupported");
}
""",
                # Receiver string literal carries tag.
                """\
#[test]
fn spoof_test() {
    let _ = run_capture("[PHASE0_TRIPWIRE:ITREE-SPF-0123456789ab]").unwrap_err();
}
""",
                # assert_eq! with observed bool LHS and const predicate RHS.
                """\
#[test]
fn spoof_test() {
    let out = run_capture();
    let fake = "[PHASE0_TRIPWIRE:ITREE-SPF-0123456789ab] unsupported";
    assert_eq!(out == "clean", fake.contains("[PHASE0_TRIPWIRE:ITREE-SPF-0123456789ab] unsupported"));
}
""",
                # assert!((out == "clean") == fake.contains(...)).
                """\
#[test]
fn spoof_test() {
    let out = run_capture();
    let fake = "[PHASE0_TRIPWIRE:ITREE-SPF-0123456789ab] unsupported";
    assert!((out == "clean") == fake.contains("[PHASE0_TRIPWIRE:ITREE-SPF-0123456789ab] unsupported"));
}
""",
                # Array literal mixing observed err and constant needle.
                """\
#[test]
fn spoof_test() {
    let err = run_capture();
    assert!([err, "[PHASE0_TRIPWIRE:ITREE-SPF-0123456789ab] unsupported"].contains(&"[PHASE0_TRIPWIRE:ITREE-SPF-0123456789ab] unsupported"));
}
""",
                # format! injecting needle into observed value.
                """\
#[test]
fn spoof_test() {
    let out = run_capture();
    assert!(format!("{out} [PHASE0_TRIPWIRE:ITREE-SPF-0123456789ab] unsupported").contains("[PHASE0_TRIPWIRE:ITREE-SPF-0123456789ab]"));
}
""",
                # Paired tuple with unobserved needle element.
                """\
#[test]
fn spoof_test() {
    let out = run_capture();
    let fake = "[PHASE0_TRIPWIRE:ITREE-SPF-0123456789ab] unsupported";
    assert_eq!((out, fake.contains("[PHASE0_TRIPWIRE:ITREE-SPF-0123456789ab] unsupported")), ("clean", true));
}
""",
            )
            for idx, body in enumerate(bad_rust_spoofs):
                (root / rs_spoof).write_text(body, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, f"rust spoof {idx} passed")

            # Genuine expect_err + err inspection and genuine tuple/eq PASS.
            for idx, body in enumerate(
                (
                    """\
#[test]
fn spoof_test() {
    let err = run_capture().expect_err("expected Phase-0 refusal");
    assert!(err.contains("[PHASE0_TRIPWIRE:ITREE-SPF-0123456789ab]"));
}
""",
                    """\
#[test]
fn spoof_test() {
    let (status, err) = run_capture();
    assert_eq!((status, err), ("unsupported", "[PHASE0_TRIPWIRE:ITREE-SPF-0123456789ab]"));
}
""",
                    """\
#[test]
fn spoof_test() {
    let err = run_capture();
    assert_eq!(err.contains("[PHASE0_TRIPWIRE:ITREE-SPF-0123456789ab] unsupported"), true);
}
""",
                )
            ):
                (root / rs_spoof).write_text(body, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertTrue(rep.ok, f"rust valid {idx}: {rep.errors}")

            # 4. Invalid Git revisions return structured PolicyReport(ok=False)
            # instead of an uncaught RuntimeError.
            rep_bad_tree = checker.check_tree(root, rev="deadbeefdeadbeef")
            self.assertFalse(rep_bad_tree.ok)
            self.assertTrue(rep_bad_tree.errors)
            rep_bad_diff = checker.check_phase0_diff(
                root, base="deadbeefdeadbeef"
            )
            self.assertFalse(rep_bad_diff.ok)
            self.assertTrue(rep_bad_diff.errors)
            rep_bad_p1 = checker.check_phase1_cleanup(
                root, base="deadbeefdeadbeef"
            )
            self.assertFalse(rep_bad_p1.ok)
            self.assertTrue(rep_bad_p1.errors)

    def test_capture_binary_resolution_rejects_arbitrary_paths(self):
        with tempfile.TemporaryDirectory(prefix="phase0-r9-bin-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)
            rs_rel = "anneal/tests/rustc-capture/tests/phase0_r9_bin.rs"
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    f"""    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-BIN-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4901",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Require authenticated capture binary resolution",
        rationale: "Block fake temp binaries matching basename",
        regression_test: "{rs_rel}::bin_test",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
                ),
                encoding="utf-8",
            )
            bad_bin_cases = (
                # Direct /tmp fake binary matching basename.
                """\
use std::process::Command;
#[test]
fn bin_test() {
    let out = Command::new("/tmp/anneal-rustc-capture-fake").output().unwrap();
    let s = String::from_utf8_lossy(&out.stdout);
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-BIN-0123456789ab]"));
    assert!(s.contains("unsupported"));
}
""",
                # TempDir join matching exact binary name.
                """\
use std::process::Command;
#[test]
fn bin_test() {
    let dir = tempfile::tempdir().unwrap();
    let fake = dir.path().join("anneal-rustc-capture");
    let out = Command::new(&fake).output().unwrap();
    let s = String::from_utf8_lossy(&out.stdout);
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-BIN-0123456789ab]"));
    assert!(s.contains("unsupported"));
}
""",
                # Passing CARGO_BIN_EXE_ as an argument to `echo`.
                """\
use std::process::Command;
#[test]
fn bin_test() {
    let out = Command::new("echo")
        .arg(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"))
        .arg("[PHASE0_TRIPWIRE:ITREE-BIN-0123456789ab] unsupported")
        .output()
        .unwrap();
    let s = String::from_utf8_lossy(&out.stdout);
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-BIN-0123456789ab]"));
    assert!(s.contains("unsupported"));
}
""",
                # Mutating CARGO_BIN_EXE_ via `format!` or `.with_file_name`.
                """\
use std::process::Command;
#[test]
fn bin_test() {
    let fake = format!("{}-fake", env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"));
    let out = Command::new(fake).output().unwrap();
    let s = String::from_utf8_lossy(&out.stdout);
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-BIN-0123456789ab]"));
    assert!(s.contains("unsupported"));
}
""",
                """\
use std::{path::Path, process::Command};
#[test]
fn bin_test() {
    let fake = Path::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"))
        .with_file_name("anneal-rustc-capture-fake");
    let out = Command::new(fake).output().unwrap();
    let s = String::from_utf8_lossy(&out.stdout);
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-BIN-0123456789ab]"));
    assert!(s.contains("unsupported"));
}
""",
                # Runtime `std::env::var` spoofable via `set_var`.
                """\
use std::process::Command;
#[test]
fn bin_test() {
    let bin = std::env::var("CARGO_BIN_EXE_anneal-rustc-capture-test-bin").unwrap();
    let out = Command::new(bin).output().unwrap();
    let s = String::from_utf8_lossy(&out.stdout);
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-BIN-0123456789ab]"));
    assert!(s.contains("unsupported"));
}
""",
                # Helper smuggling decoy `Command::new` before returning fake.
                """\
use std::process::Command;
fn build_cmd() -> Command {
    let _decoy = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"));
    Command::new("/tmp/anneal-rustc-capture-fake")
}
#[test]
fn bin_test() {
    let out = build_cmd().output().unwrap();
    let s = String::from_utf8_lossy(&out.stdout);
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-BIN-0123456789ab]"));
    assert!(s.contains("unsupported"));
}
""",
                # Shadowing `env!` macro or `Command` struct locally.
                """\
macro_rules! env { ($k:expr) => { "/tmp/fake" }; }
use std::process::Command;
#[test]
fn bin_test() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    let s = String::from_utf8_lossy(&out.stdout);
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-BIN-0123456789ab]"));
    assert!(s.contains("unsupported"));
}
""",
                """\
struct Command;
impl Command {
    fn new(_: &str) -> Self { Self }
    fn output(&self) -> Result<String, ()> { Ok("[PHASE0_TRIPWIRE:ITREE-BIN-0123456789ab] unsupported".into()) }
}
#[test]
fn bin_test() {
    let s = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-BIN-0123456789ab]"));
    assert!(s.contains("unsupported"));
}
""",
                """\
use std::{path::PathBuf, process::Command};
#[test]
fn bin_test() {
    let mut bin = PathBuf::from(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"));
    bin.set_file_name("fake");
    let out = Command::new(&bin).output().unwrap();
    let s = String::from_utf8_lossy(&out.stdout);
    assert_eq!(out.status.code(), Some(1));
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-BIN-0123456789ab]"));
}
""",
                """\
use std::process::Command;
struct PathBuf;
impl PathBuf {
    fn from(_: &str) -> &'static str { "/tmp/fake" }
}
#[test]
fn bin_test() {
    let out = Command::new(PathBuf::from(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"))).output().unwrap();
    let s = String::from_utf8_lossy(&out.stdout);
    assert_eq!(out.status.code(), Some(1));
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-BIN-0123456789ab]"));
}
""",
            )
            for idx, body in enumerate(bad_bin_cases):
                (root / rs_rel).write_text(body, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, f"bad bin case {idx} passed")

            # Authenticated Cargo bindings (const, PathBuf, passthrough) PASS.
            good_bin_cases = (
                """\
use std::{path::PathBuf, process::Command};
const CAP_BIN: &str = env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin");
#[test]
fn bin_test() {
    let bin = PathBuf::from(CAP_BIN);
    let out = Command::new(&bin).output().unwrap();
    let s = String::from_utf8_lossy(&out.stdout);
    assert_eq!(out.status.code(), Some(1));
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-BIN-0123456789ab]"));
}
""",
                """\
use std::{ffi::OsStr, process::Command};
struct Harness;
impl Harness {
    fn command_for(&self, exe: impl AsRef<OsStr>) -> Command {
        Command::new(exe)
    }
    fn command(&self) -> Command {
        self.command_for(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"))
    }
}
#[test]
fn bin_test() {
    let h = Harness;
    let out = h.command().output().unwrap();
    let s = String::from_utf8_lossy(&out.stdout);
    assert_eq!(out.status.code(), Some(1));
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-BIN-0123456789ab]"));
}
""",
            )
            for idx, body in enumerate(good_bin_cases):
                (root / rs_rel).write_text(body, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertTrue(rep.ok, f"good bin case {idx}: {rep.errors}")

            # Python subprocess must also reject /tmp fake executables/scripts.
            py_rel = "anneal/ci/test_r9_py_bin.py"
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                '// PHASE0_TRIPWIRE(bug_id="RT-PYBIN-0123456789ab", '
                'issue="https://github.com/google/zerocopy/issues/4902", '
                'owner="fixture-owner", added_date="2026-11-26", '
                'scope="Reject tmp python subprocess binary", '
                f'rationale="No arbitrary /tmp exec", regression_test="{py_rel}::test_bin")\n',
                encoding="utf-8",
            )
            for bad_py in (
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_bin(self):
        r = subprocess.run(["/tmp/anneal-rustc-capture-fake"], capture_output=True, text=True)
        self.assertIn("RT-PYBIN-0123456789ab", r.stdout)
        self.assertIn("unsupported", r.stdout)
""",
                """\
import subprocess, sys, unittest
class T(unittest.TestCase):
    def test_bin(self):
        r = subprocess.run([sys.executable, "/tmp/fake_check.py"], capture_output=True, text=True)
        self.assertIn("RT-PYBIN-0123456789ab", r.stdout)
        self.assertIn("unsupported", r.stdout)
""",
            ):
                (root / py_rel).write_text(bad_py, encoding="utf-8")
                self.assertFalse(checker.check_tree(root).ok)

    def test_lean_roots_require_fully_qualified_declaration_identity(self):
        with tempfile.TemporaryDirectory(prefix="phase0-r9-lean-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)
            root_lean = root / "anneal/trusted/lean/Trusted/MirSemantics.lean"
            step_lean = root / "anneal/trusted/lean/Trusted/MirSemantics/Step.lean"
            rt_test = root / "anneal/tests/itree_diff/tests/phase0_r9_lean.rs"
            root_lean.write_text(
                "import Trusted.MirSemantics.Step\n", encoding="utf-8"
            )
            rt_test.write_text(
                """\
#[test]
fn rt_qual() {
    let fault = run_lean_step();
    assert_eq!(fault, Some(FaultKind::Unsupported), "LMIRI-QUAL-0123456789ab");
}
""",
                encoding="utf-8",
            )
            marker = (
                '-- PHASE0_TRIPWIRE(bug_id="LMIRI-QUAL-0123456789ab", '
                'issue="https://github.com/google/zerocopy/issues/4903", '
                'owner="fixture-owner", added_date="2026-11-26", '
                'scope="Qualified Lean root identity", rationale="Reject decoy namespaces", '
                'regression_test="anneal/tests/itree_diff/tests/phase0_r9_lean.rs::rt_qual")\n'
            )

            decoy_cases = (
                # Single-line `;`-separated decoy `namespace Decoy`.
                "namespace Trusted.MirSemantics\n"
                "def evalStep := StepResult.ok\n"
                + marker
                + "namespace Decoy; def evalStep := StepResult.fault .unsupported; end Decoy\n"
                "end Trusted.MirSemantics\n",
                # Multi-line nested `namespace Decoy` with marker on `evalStep`.
                "namespace Trusted.MirSemantics\n"
                "def evalStep := StepResult.ok\n"
                "namespace Decoy\n"
                + marker
                + "def evalStep := StepResult.fault .unsupported\n"
                "end Decoy\n"
                "end Trusted.MirSemantics\n",
                # Dotted decoy declaration `def Decoy.evalStep`.
                "namespace Trusted.MirSemantics\n"
                "def evalStep := StepResult.ok\n"
                + marker
                + "def Decoy.evalStep := StepResult.fault .unsupported\n"
                "end Trusted.MirSemantics\n",
                # Private `evalStep` not exported by runtime interface.
                "namespace Trusted.MirSemantics\n"
                + marker
                + "private def evalStep := StepResult.fault .unsupported\n"
                "end Trusted.MirSemantics\n",
                # Un-namespaced `def evalStep` outside `Trusted.MirSemantics`.
                "namespace Trusted.MirSemantics\n"
                "def evalStep := StepResult.ok\n"
                "end Trusted.MirSemantics\n"
                + marker
                + "def evalStep := StepResult.fault .unsupported\n",
                # Decoy helper with same short name as a real called helper.
                "namespace Trusted.MirSemantics\n"
                "def realHelper := StepResult.ok\n"
                "def evalStep := realHelper\n"
                "namespace Decoy\n"
                + marker
                + "def realHelper := StepResult.fault .unsupported\n"
                "end Decoy\n"
                "end Trusted.MirSemantics\n",
            )
            for idx, src in enumerate(decoy_cases):
                step_lean.write_text(src, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, f"lean decoy case {idx} passed")

            # Decoy namespace must not inflate guard count in `phase0-diff`.
            step_lean.write_text(
                "namespace Trusted.MirSemantics\n"
                "def existingBranch := StepResult.fault .unsupported\n"
                "def evalStep := existingBranch\n"
                "end Trusted.MirSemantics\n",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "qualified lean base")
            qual_base = _git(root, "rev-parse", "HEAD")

            step_lean.write_text(
                "namespace Trusted.MirSemantics\n"
                + marker
                + "def existingBranch := StepResult.fault .unsupported\n"
                "namespace Decoy; def evalStep := StepResult.fault .unsupported; end Decoy\n"
                "def evalStep := existingBranch\n"
                "end Trusted.MirSemantics\n",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "decoy evalStep inflation")
            qual_head = _git(root, "rev-parse", "HEAD")
            rep_diff = checker.check_phase0_diff(
                root,
                base=qual_base,
                head=qual_head,
                allow_runtime_semantics_fallback=True,
            )
            self.assertFalse(rep_diff.ok)

            # Genuine `Trusted.MirSemantics.evalStep` + real dot-proj PASSES.
            step_lean.write_text(
                "namespace Trusted.MirSemantics\n"
                "inductive Val where | unit\n"
                "namespace Val\n"
                + marker
                + "def checkVal := StepResult.fault .unsupported\n"
                "end Val\n"
                "def evalStep (v : Val) := v.checkVal\n"
                "end Trusted.MirSemantics\n",
                encoding="utf-8",
            )
            rep_ok = checker.check_tree(root)
            self.assertTrue(rep_ok.ok, rep_ok.errors)

    def test_rejects_user_defined_partial_eq_and_wrapper_spoofing(self):
        with tempfile.TemporaryDirectory(prefix="phase0-r9-eq-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)
            rs_rel = "anneal/tests/rustc-capture/tests/phase0_r9_eq.rs"
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    f"""    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-PEQ-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4904",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Reject custom PartialEq wrappers in assertions",
        rationale: "Require concrete trusted output/string projections",
        regression_test: "{rs_rel}::eq_spoof",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
                ),
                encoding="utf-8",
            )
            bad_eq_cases = (
                # Direct `assert_eq!(Evil(&output), ...)` custom `PartialEq`.
                """\
use std::process::{Command, Output};
#[derive(Debug)]
struct Evil<'a>(&'a Output);
impl PartialEq<&str> for Evil<'_> { fn eq(&self, _: &&str) -> bool { true } }
#[test]
fn eq_spoof() {
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    assert_eq!(Evil(&output), "[PHASE0_TRIPWIRE:ITREE-PEQ-0123456789ab]");
    assert_eq!(Evil(&output), "unsupported");
}
""",
                # Reversed operands and `assert!(Evil(&output) == ...)`.
                """\
use std::process::{Command, Output};
struct Evil<'a>(&'a Output);
impl PartialEq<Evil<'_>> for &str { fn eq(&self, _: &Evil<'_>) -> bool { true } }
#[test]
fn eq_spoof() {
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    assert!("[PHASE0_TRIPWIRE:ITREE-PEQ-0123456789ab]" == Evil(&output));
    assert!("unsupported" == Evil(&output));
}
""",
                # Bound via `let wrapped = Evil(&output)` and tuple.
                """\
use std::process::{Command, Output};
#[derive(Debug)]
struct Evil<'a>(&'a Output);
impl PartialEq<&str> for Evil<'_> { fn eq(&self, _: &&str) -> bool { true } }
#[test]
fn eq_spoof() {
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    let wrapped = Evil(&output);
    let (a, _) = (wrapped, 0);
    assert_eq!(a, "[PHASE0_TRIPWIRE:ITREE-PEQ-0123456789ab]");
    assert_eq!(a, "unsupported");
}
""",
                # Opaque helper returning `impl PartialEq<&str>` or `Evil`.
                """\
use std::process::{Command, Output};
#[derive(Debug)]
struct Evil<'a>(&'a Output);
impl PartialEq<&str> for Evil<'_> { fn eq(&self, _: &&str) -> bool { true } }
fn disguise(o: &Output) -> impl PartialEq<&str> + std::fmt::Debug + '_ { Evil(o) }
#[test]
fn eq_spoof() {
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    assert_eq!(disguise(&output), "[PHASE0_TRIPWIRE:ITREE-PEQ-0123456789ab]");
    assert_eq!(disguise(&output), "unsupported");
}
""",
                # Needle-side custom PartialEq type `FakeStr("...")`.
                """\
use std::process::Command;
#[derive(Debug)]
struct FakeStr(&'static str);
impl PartialEq<FakeStr> for String { fn eq(&self, _: &FakeStr) -> bool { true } }
#[test]
fn eq_spoof() {
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    let s = String::from_utf8_lossy(&output.stdout).into_owned();
    assert_eq!(s, FakeStr("[PHASE0_TRIPWIRE:ITREE-PEQ-0123456789ab]"));
    assert_eq!(s, FakeStr("unsupported"));
}
""",
                # Extension trait overriding `.contains()` on `Output`.
                """\
use std::process::{Command, Output};
trait Lie { fn contains(&self, s: &str) -> bool; }
impl Lie for Output { fn contains(&self, _: &str) -> bool { true } }
#[test]
fn eq_spoof() {
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    assert!(output.contains("[PHASE0_TRIPWIRE:ITREE-PEQ-0123456789ab]"));
    assert!(output.contains("unsupported"));
}
""",
                # Custom `impl PartialEq` defined inside the test body itself.
                """\
use std::process::{Command, Output};
#[test]
fn eq_spoof() {
    #[derive(Debug)]
    struct LocalEvil<'a>(&'a Output);
    impl PartialEq<&str> for LocalEvil<'_> { fn eq(&self, _: &&str) -> bool { true } }
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    assert_eq!(LocalEvil(&output), "[PHASE0_TRIPWIRE:ITREE-PEQ-0123456789ab]");
    assert_eq!(LocalEvil(&output), "unsupported");
}
""",
                # External untrusted wrapper constructor or `.into()`.
                """\
use std::process::Command;
#[test]
fn eq_spoof() {
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    assert_eq!(other_mod::Evil(&output), "[PHASE0_TRIPWIRE:ITREE-PEQ-0123456789ab]");
    assert_eq!(other_mod::Evil(&output), "unsupported");
}
""",
            )
            for idx, body in enumerate(bad_eq_cases):
                (root / rs_rel).write_text(body, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, f"bad eq case {idx} passed")

            # Concrete trusted projections PASS.
            (root / rs_rel).write_text(
                """\
use std::process::{Command, Output};
fn decode_stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}
#[test]
fn eq_spoof() {
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    let err = decode_stderr(&output);
    assert_eq!(output.status.code(), Some(1));
    assert!(err.contains("[PHASE0_TRIPWIRE:ITREE-PEQ-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            rep_ok = checker.check_tree(root)
            self.assertTrue(rep_ok.ok, rep_ok.errors)

            # Python custom `__eq__` / `__contains__` wrapper spoofing FAILS.
            py_rel = "anneal/ci/test_r9_py_eq.py"
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                '// PHASE0_TRIPWIRE(bug_id="RT-PYEQW-0123456789ab", '
                'issue="https://github.com/google/zerocopy/issues/4905", '
                'owner="fixture-owner", added_date="2026-11-26", '
                'scope="Reject Python custom __eq__ wrappers", '
                f'rationale="No custom eq spoofs", regression_test="{py_rel}::test_eq")\n',
                encoding="utf-8",
            )
            (root / py_rel).write_text(
                """\
import unittest
class Evil:
    def __init__(self, x):
        self.x = x
    def __eq__(self, other):
        return True
class T(unittest.TestCase):
    def test_eq(self):
        out = run_probe()
        self.assertEqual(Evil(out), "RT-PYEQW-0123456789ab")
        self.assertEqual(Evil(out), "unsupported")
""",
                encoding="utf-8",
            )
            self.assertFalse(checker.check_tree(root).ok)

    def test_propagates_successful_process_exit_through_local_helpers(self):
        with tempfile.TemporaryDirectory(prefix="phase0-r9-exit-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)
            rs_rel = "anneal/tests/rustc-capture/tests/phase0_r9_exit.rs"
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    f"""    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-EXIT-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4906",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Propagate process::exit(0) through local helpers",
        rationale: "Assertions must dominate test-process exit",
        regression_test: "{rs_rel}::exit_helper_test",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
                ),
                encoding="utf-8",
            )
            bad_exit_cases = (
                # Direct local helper executing `std::process::exit(0)`.
                """\
use std::process::Command;
fn bail() { std::process::exit(0); }
#[test]
fn exit_helper_test() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    bail();
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).contains("[PHASE0_TRIPWIRE:ITREE-EXIT-0123456789ab]"));
}
""",
                # Transitive helper chain `a() -> b() -> std::process::exit(0)`.
                """\
use std::process::Command;
fn leaf() { std::process::exit(0); }
fn mid() { leaf(); }
#[test]
fn exit_helper_test() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    mid();
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).contains("[PHASE0_TRIPWIRE:ITREE-EXIT-0123456789ab]"));
}
""",
                # Conditional exit helper (`if success() { exit(0); }`).
                """\
use std::process::{Command, Output};
fn maybe_bail(out: &Output) {
    if out.status.success() {
        std::process::exit(0);
    }
}
#[test]
fn exit_helper_test() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    maybe_bail(&out);
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).contains("[PHASE0_TRIPWIRE:ITREE-EXIT-0123456789ab]"));
}
""",
                # Aliased `use std::process::exit as quit;` inside helper.
                """\
use std::process::{Command, exit as quit};
fn bail() { quit(0); }
#[test]
fn exit_helper_test() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    bail();
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).contains("[PHASE0_TRIPWIRE:ITREE-EXIT-0123456789ab]"));
}
""",
                # Method helper and module-scoped helper calling exit(0).
                """\
use std::process::Command;
struct Guard;
impl Guard { fn finish(&self) { std::process::exit(0); } }
#[test]
fn exit_helper_test() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    let g = Guard;
    g.finish();
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).contains("[PHASE0_TRIPWIRE:ITREE-EXIT-0123456789ab]"));
}
""",
                # Nested `fn` inside test body calling `std::process::exit(0)`.
                """\
use std::process::Command;
#[test]
fn exit_helper_test() {
    fn inner_bail() { std::process::exit(0); }
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    inner_bail();
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).contains("[PHASE0_TRIPWIRE:ITREE-EXIT-0123456789ab]"));
}
""",
                # Closure / IIFE / fn-pointer calling `std::process::exit(0)`.
                """\
use std::process::Command;
#[test]
fn exit_helper_test() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    let f = || std::process::exit(0);
    f();
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).contains("[PHASE0_TRIPWIRE:ITREE-EXIT-0123456789ab]"));
}
""",
                """\
use std::process::Command;
#[test]
fn exit_helper_test() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    (|| std::process::exit(0))();
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).contains("[PHASE0_TRIPWIRE:ITREE-EXIT-0123456789ab]"));
}
""",
                # Drop bomb exiting 0 when dropped before assertions.
                """\
use std::process::Command;
struct Bomb;
impl Drop for Bomb { fn drop(&mut self) { std::process::exit(0); } }
#[test]
fn exit_helper_test() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    { let _b = Bomb; }
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).contains("[PHASE0_TRIPWIRE:ITREE-EXIT-0123456789ab]"));
}
""",
                # Exit helper invoked inside the assertion expression itself.
                """\
use std::process::Command;
fn bail_str(s: &str) -> &str { std::process::exit(0); }
#[test]
fn exit_helper_test() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    let s = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(1));
    assert!(bail_str(&s).contains("[PHASE0_TRIPWIRE:ITREE-EXIT-0123456789ab]"));
}
""",
                # Post-assertion `process::exit(0)` STILL exits the whole
                # test binary and masks sibling/remaining tests.
                """\
use std::process::Command;
fn done() { std::process::exit(0); }
#[test]
fn exit_helper_test() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).contains("[PHASE0_TRIPWIRE:ITREE-EXIT-0123456789ab]"));
    done();
}
""",
            )
            for idx, body in enumerate(bad_exit_cases):
                (root / rs_rel).write_text(body, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, f"bad exit case {idx} passed")

            # Nonzero failing `exit(1)` PASSES.
            for idx, body in enumerate(
                (
                    """\
use std::process::Command;
fn fail_hard() -> ! { std::process::exit(1); }
#[test]
fn exit_helper_test() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    if out.status.success() { fail_hard(); }
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).contains("[PHASE0_TRIPWIRE:ITREE-EXIT-0123456789ab]"));
}
""",
                )
            ):
                (root / rs_rel).write_text(body, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertTrue(rep.ok, f"good exit case {idx}: {rep.errors}")

            # Python transitive helper `sys.exit(0)` and `self.skipTest` FAIL.
            py_rel = "anneal/ci/test_r9_py_exit.py"
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                '// PHASE0_TRIPWIRE(bug_id="RT-PYEX-0123456789ab", '
                'issue="https://github.com/google/zerocopy/issues/4907", '
                'owner="fixture-owner", added_date="2026-11-26", '
                'scope="Propagate Python helper exit(0) and skipTest", '
                f'rationale="Must not skip assertions", regression_test="{py_rel}::test_ex")\n',
                encoding="utf-8",
            )
            for bad_py in (
                """\
import sys, unittest
def bail():
    sys.exit(0)
class T(unittest.TestCase):
    def test_ex(self):
        err = run_probe()
        bail()
        self.assertIn("RT-PYEX-0123456789ab", err)
        self.assertIn("unsupported", err)
""",
                """\
import unittest
class T(unittest.TestCase):
    def _skip_me(self):
        self.skipTest("bye")
    def test_ex(self):
        err = run_probe()
        self._skip_me()
        self.assertIn("RT-PYEX-0123456789ab", err)
        self.assertIn("unsupported", err)
""",
            ):
                (root / py_rel).write_text(bad_py, encoding="utf-8")
                self.assertFalse(checker.check_tree(root).ok)

    def test_blocks_compound_rhs_inline_return_paren_shortcircuit_and_py_ast(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-g2r8-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)
            rs_rel = "anneal/tests/rustc-capture/tests/phase0_compound_cfg.rs"
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    f"""    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-CMP-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4910",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Block compound RHS laundering, inline returns, and short-circuit",
        rationale: "Every path must observe the capture binary before exiting",
        regression_test: "{rs_rel}::cmp_test",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
                ),
                encoding="utf-8",
            )
            bad_rs_cases = (
                # `Command::new("sh")` passing capture name as an argument.
                """\
use std::process::Command;
#[test]
fn cmp_test() {
    let out = Command::new("sh")
        .args(["-c", "echo '[PHASE0_TRIPWIRE:ITREE-CMP-0123456789ab] unsupported'; exit 1", "anneal-rustc-capture"])
        .output()
        .unwrap();
    let s = String::from_utf8_lossy(&out.stdout);
    assert_eq!(out.status.code(), Some(1));
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-CMP-0123456789ab]"));
}
""",
                # Dummy `.output(&cmd)` passing verified Command as an arg.
                """\
use std::process::Command;
struct Dummy;
impl Dummy {
    fn output(&self, _: &Command) -> String { "[PHASE0_TRIPWIRE:ITREE-CMP-0123456789ab] unsupported".into() }
}
#[test]
fn cmp_test() {
    let cmd = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"));
    let s = Dummy.output(&cmd);
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-CMP-0123456789ab]"));
    assert!(s.contains("unsupported"));
}
""",
                # Block RHS smuggling decoy `env!` before `echo`.
                """\
use std::process::Command;
#[test]
fn cmp_test() {
    let out = {
        let _decoy = env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin");
        Command::new("echo")
            .arg("[PHASE0_TRIPWIRE:ITREE-CMP-0123456789ab] unsupported")
            .output()
            .unwrap()
    };
    let s = String::from_utf8_lossy(&out.stdout);
    assert_eq!(out.status.code(), Some(1));
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-CMP-0123456789ab]"));
}
""",
                # Conditional `if`/`else` RHS mixing `echo` and capture binary.
                """\
use std::process::Command;
#[test]
fn cmp_test() {
    let out = if std::env::var("X").is_ok() {
        Command::new("echo").arg("ok").output().unwrap()
    } else {
        Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap()
    };
    let s = String::from_utf8_lossy(&out.stdout);
    assert_eq!(out.status.code(), Some(1));
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-CMP-0123456789ab]"));
}
""",
                # `match` RHS mixing `echo` and capture binary.
                """\
use std::process::Command;
#[test]
fn cmp_test() {
    let out = match std::env::var("X").is_ok() {
        true => Command::new("echo").arg("ok").output().unwrap(),
        false => Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap(),
    };
    let s = String::from_utf8_lossy(&out.stdout);
    assert_eq!(out.status.code(), Some(1));
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-CMP-0123456789ab]"));
}
""",
                # Fallback `unwrap_or_else` laundering `Command::new("echo")`.
                """\
use std::process::Command;
#[test]
fn cmp_test() {
    let out = Command::new("echo")
        .arg("[PHASE0_TRIPWIRE:ITREE-CMP-0123456789ab] unsupported")
        .output()
        .unwrap_or_else(|_| Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap());
    let s = String::from_utf8_lossy(&out.stdout);
    assert_eq!(out.status.code(), Some(1));
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-CMP-0123456789ab]"));
}
""",
                # Tuple element `.0` discarding observed capture in `.1`.
                """\
use std::process::Command;
#[test]
fn cmp_test() {
    let out = (
        Command::new("echo").arg("x").output().unwrap(),
        Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap(),
    ).0;
    let s = String::from_utf8_lossy(&out.stdout);
    assert_eq!(out.status.code(), Some(1));
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-CMP-0123456789ab]"));
}
""",
                # Single-statement inline `if cond { return; }` before asserts.
                """\
use std::process::Command;
#[test]
fn cmp_test() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    let s = String::from_utf8_lossy(&out.stderr);
    let _ = (
        (),
        if std::env::var("X").is_ok() { return; },
        assert_eq!(out.status.code(), Some(1)),
        assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-CMP-0123456789ab]")),
    );
}
""",
                # Parenthesized short-circuit `false && (assert!(...), ...)`.
                """\
use std::process::Command;
#[test]
fn cmp_test() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    let s = String::from_utf8_lossy(&out.stderr);
    let _ = (
        false
            && (
                assert_eq!(out.status.code(), Some(1)),
                assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-CMP-0123456789ab]")),
                true
            )
            .2
    );
}
""",
            )
            for idx, body in enumerate(bad_rs_cases):
                (root / rs_rel).write_text(body, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, f"bad compound/cfg case {idx} passed")

            # Legitimate compound RHS blocks and plain tuples PASS.
            good_rs_cases = (
                """\
use std::process::Command;
#[test]
fn cmp_test() {
    let out = {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"));
        cmd.arg("--flag");
        cmd.output().unwrap()
    };
    let s = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(1));
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-CMP-0123456789ab]"));
}
""",
                """\
use std::process::Command;
#[test]
fn cmp_test() {
    let out = if std::env::var("X").is_ok() {
        Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap()
    } else {
        Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap()
    };
    let s = String::from_utf8_lossy(&out.stderr);
    let _ = (
        true && false,
        assert_eq!(out.status.code(), Some(1)),
        assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-CMP-0123456789ab]")),
    );
}
""",
            )
            for idx, body in enumerate(good_rs_cases):
                (root / rs_rel).write_text(body, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertTrue(rep.ok, f"good compound/cfg case {idx}: {rep.errors}")

            # Python local class spoof, nested `def` in `with`, and AST spoofs.
            py_rel = "anneal/ci/test_py_ast_prov.py"
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                '// PHASE0_TRIPWIRE(bug_id="RT-PYAST-0123456789ab", '
                'issue="https://github.com/google/zerocopy/issues/4911", '
                'owner="fixture-owner", added_date="2026-11-26", '
                'scope="Fail-closed Python local classes, nested defs, and AST", '
                f'rationale="No unexecuted provenance", regression_test="{py_rel}::test_ast")\n',
                encoding="utf-8",
            )
            bad_py_cases = (
                # Local class matching `anneal_*` module prefix without import.
                """\
import unittest
class anneal_fake:
    @staticmethod
    def run():
        return "RT-PYAST-0123456789ab unsupported"
class T(unittest.TestCase):
    def test_ast(self):
        err = anneal_fake.run()
        self.assertIn("RT-PYAST-0123456789ab", err)
        self.assertIn("unsupported", err)
""",
                # Nested `def run_audit` inside `with` block.
                """\
import tempfile, unittest
class T(unittest.TestCase):
    def test_ast(self):
        with tempfile.TemporaryDirectory():
            def run_audit():
                return "RT-PYAST-0123456789ab unsupported"
            err = run_audit()
            self.assertIn("RT-PYAST-0123456789ab", err)
            self.assertIn("unsupported", err)
""",
                # Ternary `IfExp` mixing driver call with `echo`.
                """\
import os, subprocess, unittest
class T(unittest.TestCase):
    def test_ast(self):
        r = (
            subprocess.run(["cargo", "test"], capture_output=True, text=True)
            if os.environ.get("REAL")
            else subprocess.run(["echo", "RT-PYAST-0123456789ab unsupported"], capture_output=True, text=True)
        )
        self.assertIn("RT-PYAST-0123456789ab", r.stdout)
        self.assertIn("unsupported", r.stdout)
""",
                # `BoolOp` `or` short-circuiting past driver call.
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_ast(self):
        r = (
            subprocess.run(["echo", "RT-PYAST-0123456789ab unsupported"], capture_output=True, text=True)
            or subprocess.run(["cargo", "test"], capture_output=True, text=True)
        )
        self.assertIn("RT-PYAST-0123456789ab", r.stdout)
        self.assertIn("unsupported", r.stdout)
""",
                # List subscript `[echo, driver][0]`.
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_ast(self):
        r = [
            subprocess.run(["echo", "RT-PYAST-0123456789ab unsupported"], capture_output=True, text=True),
            subprocess.run(["cargo", "test"], capture_output=True, text=True),
        ][0]
        self.assertIn("RT-PYAST-0123456789ab", r.stdout)
        self.assertIn("unsupported", r.stdout)
""",
                # Tuple subscript `(echo, driver)[0]`.
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_ast(self):
        r = (
            subprocess.run(["echo", "RT-PYAST-0123456789ab unsupported"], capture_output=True, text=True),
            subprocess.run(["cargo", "test"], capture_output=True, text=True),
        )[0]
        self.assertIn("RT-PYAST-0123456789ab", r.stdout)
        self.assertIn("unsupported", r.stdout)
""",
                # Tuple destructuring `a, b = echo, driver` asserting on `a`.
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_ast(self):
        a, _b = (
            subprocess.run(["echo", "RT-PYAST-0123456789ab unsupported"], capture_output=True, text=True),
            subprocess.run(["cargo", "test"], capture_output=True, text=True),
        )
        self.assertIn("RT-PYAST-0123456789ab", a.stdout)
        self.assertIn("unsupported", a.stdout)
""",
            )
            for idx, bad_py in enumerate(bad_py_cases):
                (root / py_rel).write_text(bad_py, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, f"bad py ast case {idx} passed")

            # Legitimate `res.stderr or ""` and `stdout + "\n" + stderr` PASS.
            (root / py_rel).write_text(
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_ast(self):
        r = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        err = (r.stderr or "") + "\\n" + (r.stdout or "")
        self.assertIn("RT-PYAST-0123456789ab", err)
        self.assertIn("unsupported", err)
""",
                encoding="utf-8",
            )
            rep_py_ok = checker.check_tree(root)
            self.assertTrue(rep_py_ok.ok, rep_py_ok.errors)

    def test_unittest_keyword_args_and_phase1_cleanup(self):
        with tempfile.TemporaryDirectory(prefix="phase0-kw-") as tmp:
            root = Path(tmp)
            base = _init_fixture_repo(root)
            py_rel = "anneal/ci/test_kw_tripwire.py"
            py_target = f"{py_rel}::test_kw"
            bid = "RT-KWARG-0123456789ab"

            def _write_case(body: str) -> None:
                (root / "anneal/trusted/audit/src/lib.rs").write_text(
                    f'// PHASE0_TRIPWIRE(bug_id="{bid}", '
                    'issue="https://github.com/google/zerocopy/issues/4901", '
                    'owner="fixture-owner", added_date="2026-11-26", '
                    'scope="Fixture refusal check", '
                    'rationale="Ensure unittest keyword assertions resolve cleanly.", '
                    f'regression_test="{py_target}")\n'
                    "pub fn audit_stub() {}\n",
                    encoding="utf-8",
                )
                (root / py_rel).write_text(body, encoding="utf-8")

            # Valid keyword order (`container=...`, `member=...`,
            # `expected_regex=...`, `text=...`, `expr=...`) PASSES.
            for good in (
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_kw(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertIn(container=out.stderr, member="RT-KWARG-0123456789ab")
        self.assertIn(container=out.stderr, member="unsupported")
""",
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_kw(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertRegex(expected_regex="RT-KWARG-0123456789ab", text=out.stderr)
        self.assertRegex(expected_regex="unsupported", text=out.stderr)
""",
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_kw(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertTrue(expr=("RT-KWARG-0123456789ab" in out.stderr))
        self.assertTrue(expr=("unsupported" in out.stderr))
""",
            ):
                _write_case(good)
                rep = checker.check_tree(root)
                self.assertTrue(rep.ok, rep.errors)

            # Vacuous/inverted keyword order and `assertTrue(expr=...)`
            # bypasses MUST fail closed.
            for bad in (
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_kw(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertIn(container="RT-KWARG-0123456789ab unsupported", member=out.stderr)
""",
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_kw(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertRegex(expected_regex=out.stderr, text="RT-KWARG-0123456789ab unsupported")
""",
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_kw(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertTrue(expr=("RT-KWARG-0123456789ab" in f"{out.stderr} RT-KWARG-0123456789ab unsupported"))
""",
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_kw(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertTrue(expr=("RT-KWARG-0123456789ab" in out.stderr))
        self.assertTrue(expr=(out.returncode == 0 or "unsupported" in out.stderr))
""",
            ):
                _write_case(bad)
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, f"bad kw case passed: {bad}")

            # Phase-1 cleanup (on `runtime_semantics` layer `Step.lean`) must
            # reject unflipped and tautological keyword-argument assertions.
            lean_kw_rel = "anneal/trusted/lean/Trusted/MirSemantics/Step.lean"
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                "pub fn audit_stub() {}\n", encoding="utf-8"
            )
            (root / lean_kw_rel).write_text(
                "namespace Trusted.MirSemantics\n"
                f'-- PHASE0_TRIPWIRE(bug_id="{bid}", '
                'issue="https://github.com/google/zerocopy/issues/4901", '
                'owner="fixture-owner", added_date="2026-11-26", '
                'scope="Fixture refusal check", '
                'rationale="Ensure unittest keyword assertions resolve cleanly.", '
                f'regression_test="{py_target}")\n'
                "def guard := StepResult.fault .unsupported\n"
                "def evalStep := guard\n"
                "end Trusted.MirSemantics\n",
                encoding="utf-8",
            )
            (root / py_rel).write_text(
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_kw(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertIn(container=out.stderr, member="RT-KWARG-0123456789ab")
        self.assertIn(container=out.stderr, member="unsupported")
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "add kw tripwire")
            base_with_tw = _git(root, "rev-parse", "HEAD")

            for bad_p1 in (
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_kw(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertNotEqual(first=out.returncode, second=0)
""",
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_kw(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertEqual(first=out.returncode, second=1)
""",
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_kw(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertTrue(expr=out.returncode != 0)
""",
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_kw(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertEqual(first=out.returncode, second=out.returncode)
""",
            ):
                (root / lean_kw_rel).write_text(
                    "namespace Trusted.MirSemantics\n"
                    "def evalStep := StepResult.ok ()\n"
                    "end Trusted.MirSemantics\n",
                    encoding="utf-8",
                )
                (root / py_rel).write_text(bad_p1, encoding="utf-8")
                _git(root, "add", ".")
                _git(root, "commit", "-q", "-m", "phase1 bad kw")
                head_bad = _git(root, "rev-parse", "HEAD")
                rep_p1 = checker.check_phase1_cleanup(
                    root, base=base_with_tw, head=head_bad
                )
                self.assertFalse(rep_p1.ok, f"phase1 accepted bad kw: {bad_p1}")
                _git(root, "reset", "--hard", base_with_tw)
            _git(root, "reset", "--hard", base)

    def test_capture_refused_matches_phase0_and_blocks_phase1(self):
        with tempfile.TemporaryDirectory(prefix="phase0-capref-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)

            # Both `static_capture` (`tripwires.rs`) and `runtime_semantics`
            # (Lean `Step.lean`) tripwires using `CaptureRefused` pass Phase 0.
            static_test = "anneal/tests/rustc-capture/tests/cap_refused.rs"
            static_target = f"{static_test}::static_capture_refused"
            lean_rel = "anneal/trusted/lean/Trusted/MirSemantics/Step.lean"
            itree_test = "anneal/tests/itree_diff/tests/cap_refused.rs"
            itree_target = f"{itree_test}::itree_capture_refused"
            static_bid = "DIFF-CAPREF-0123456789ab"
            lean_bid = "ITREE-CAPREF-abcdef012345"

            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    f"""    PHASE0_TRIPWIRE! {{
        bug_id: "{static_bid}",
        issue: "https://github.com/google/zerocopy/issues/4902",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "Fixture static_capture CaptureRefused refusal check",
        rationale: "Verify CaptureRefused works in Phase 0 and Phase 1.",
        regression_test: "{static_target}",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
                ),
                encoding="utf-8",
            )
            (root / static_test).write_text(
                f"""\
#[test]
fn static_capture_refused() {{
    let res = run_capture();
    assert!(matches!(res.outcome, TerminalOutcome::CaptureRefused {{ .. }}));
    assert!(res.detail.contains("[PHASE0_TRIPWIRE:{static_bid}]"));
}}
""",
                encoding="utf-8",
            )
            (root / lean_rel).write_text(
                "namespace Trusted.MirSemantics\n"
                f'-- PHASE0_TRIPWIRE(bug_id="{lean_bid}", '
                'issue="https://github.com/google/zerocopy/issues/4903", '
                'owner="fixture-owner", added_date="2026-11-26", '
                'scope="runtime CaptureRefused guard", '
                'rationale="Block unsound step pending Phase 1", '
                f'regression_test="{itree_target}")\n'
                "def guard := StepResult.fault .unsupported\n"
                "def evalStep := guard\n"
                "end Trusted.MirSemantics\n",
                encoding="utf-8",
            )
            (root / itree_test).write_text(
                f"""\
#[test]
fn itree_capture_refused() {{
    let res = run_lean_step();
    assert!(
        matches!(res.outcome, TerminalOutcome::CaptureRefused {{ .. }}),
        "expected Runbook B Phase-0 refusal for {lean_bid}"
    );
}}
""",
                encoding="utf-8",
            )
            rep = checker.check_tree(root)
            self.assertTrue(rep.ok, rep.errors)

            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "active CaptureRefused tripwires")
            tw_head = _git(root, "rev-parse", "HEAD")

            # Phase-1 deletion of each layer individually with an unflipped
            # `CaptureRefused` assertion MUST fail `check_phase1_cleanup`.
            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS, encoding="utf-8"
            )
            (root / static_test).write_text(
                """\
#[test]
fn static_capture_refused() {
    let res = run_capture();
    assert!(matches!(res.outcome, TerminalOutcome::CaptureRefused { .. }));
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "phase1 unflipped static CaptureRefused")
            p1_static = _git(root, "rev-parse", "HEAD")
            rep_s = checker.check_phase1_cleanup(
                root, base=tw_head, head=p1_static
            )
            self.assertFalse(rep_s.ok, "phase1 accepted unflipped static CaptureRefused")
            self.assertIn("cap_refused.rs::static_capture_refused", "\n".join(rep_s.errors))

            _git(root, "reset", "--hard", tw_head)
            (root / lean_rel).write_text(
                "namespace Trusted.MirSemantics\n"
                "def evalStep := StepResult.ok ()\n"
                "end Trusted.MirSemantics\n",
                encoding="utf-8",
            )
            (root / itree_test).write_text(
                """\
#[test]
fn itree_capture_refused() {
    let res = run_lean_step();
    assert!(matches!(res.outcome, TerminalOutcome::CaptureRefused { .. }));
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "phase1 unflipped lean CaptureRefused")
            p1_lean = _git(root, "rev-parse", "HEAD")
            rep_l = checker.check_phase1_cleanup(root, base=tw_head, head=p1_lean)
            self.assertFalse(rep_l.ok, "phase1 accepted unflipped lean CaptureRefused")
            self.assertIn("cap_refused.rs::itree_capture_refused", "\n".join(rep_l.errors))

    def test_git_helpers_hermetic_against_ambient_git_env(self):
        with tempfile.TemporaryDirectory(prefix="phase0-git-env-") as tmp:
            tmp_path = Path(tmp)
            sentinel = tmp_path / "sentinel"
            sentinel.mkdir()
            _git(sentinel, "init", "-q")
            _git(sentinel, "config", "user.name", "Real Dev")
            _git(sentinel, "config", "user.email", "real@example.invalid")
            (sentinel / "hello.txt").write_text("hi\n", encoding="utf-8")
            _git(sentinel, "add", "hello.txt")
            _git(sentinel, "commit", "-q", "-m", "sentinel base")
            sentinel_head = _git(sentinel, "rev-parse", "HEAD")

            fixture = tmp_path / "fixture"
            fixture.mkdir()
            with mock.patch.dict(
                os.environ,
                {
                    "GIT_DIR": str(sentinel / ".git"),
                    "GIT_WORK_TREE": str(sentinel),
                    "GIT_INDEX_FILE": str(sentinel / ".git/index"),
                },
            ):
                base = _init_fixture_repo(fixture)
                tw_test = "anneal/tests/rustc-capture/tests/phase0_env_guard.rs"
                (fixture / checker.TRIPWIRES_REL).write_text(
                    _with_active_entries(
                        f"""    PHASE0_TRIPWIRE! {{
        bug_id: "DIFF-ENV-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4904",
        owner: "fixture-owner",
        added_date: "2026-11-26",
        scope: "ambient env guard",
        rationale: "Ensure git helpers stay hermetic under ambient GIT_DIR.",
        regression_test: "{tw_test}::test_ok",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
                    ),
                    encoding="utf-8",
                )
                (fixture / tw_test).write_text(
                    """\
#[test]
fn test_ok() {
    let (out, reason) = run_capture();
    assert_eq!(out.status.code(), Some(1));
    assert!(reason.contains("[PHASE0_TRIPWIRE:DIFF-ENV-0123456789ab]"));
}
""",
                    encoding="utf-8",
                )
                _git(fixture, "add", ".")
                _git(fixture, "commit", "-q", "-m", "add phase0 under ambient env")
                rep_tree = checker.check_tree(fixture, rev="HEAD")
                self.assertTrue(rep_tree.ok, rep_tree.errors)
                rep_p0 = checker.check_phase0_diff(
                    fixture, base=base, head="HEAD"
                )
                self.assertTrue(rep_p0.ok, rep_p0.errors)
                tw_rev = _git(fixture, "rev-parse", "HEAD")
                (fixture / checker.TRIPWIRES_REL).write_text(
                    BASE_TRIPWIRES_RS, encoding="utf-8"
                )
                (fixture / tw_test).write_text(
                    """\
#[test]
fn test_ok() {
    let out = run_capture_ok();
    assert_eq!(out.status.code(), Some(0));
}
""",
                    encoding="utf-8",
                )
                _git(fixture, "add", ".")
                _git(fixture, "commit", "-q", "-m", "phase1 under ambient env")
                rep_p1 = checker.check_phase1_cleanup(
                    fixture, base=tw_rev, head="HEAD"
                )
                self.assertTrue(rep_p1.ok, rep_p1.errors)
                with self.assertRaises(RuntimeError):
                    checker._git_merge_base(fixture, "--output=pwn", "HEAD")

            self.assertTrue((fixture / ".git").is_dir())
            self.assertEqual(_git(sentinel, "rev-parse", "HEAD"), sentinel_head)
            self.assertEqual(_git(sentinel, "config", "user.name"), "Real Dev")

    def test_except_binding_tag_refusal_and_proc_exit_guards(self):
        with tempfile.TemporaryDirectory(prefix="phase0-proc-exit-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)

            # 1. `except ... as e:` is observed only when `try:` invokes an
            # approved runtime/driver observation call.
            py_rel = "anneal/ci/test_try_exit.py"
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                '// PHASE0_TRIPWIRE(bug_id="RT-EXCTRY-0123456789ab", '
                'issue="https://github.com/google/zerocopy/issues/4911", '
                'owner="fixture-owner", added_date="2026-11-27", '
                'scope="Require try body observation for except handler binding", '
                'rationale="Block self-raised exception laundering", '
                f'regression_test="{py_rel}::test_exc")\n',
                encoding="utf-8",
            )
            for bad_try in (
                """\
import unittest
class T(unittest.TestCase):
    def test_exc(self):
        try:
            raise RuntimeError("RT-EXCTRY-0123456789ab unsupported")
        except RuntimeError as e:
            self.assertIn("RT-EXCTRY-0123456789ab", str(e))
            self.assertIn("unsupported", str(e))
""",
                """\
import unittest
def fake_raise():
    raise RuntimeError("RT-EXCTRY-0123456789ab unsupported")
class T(unittest.TestCase):
    def test_exc(self):
        try:
            fake_raise()
            self.fail("expected error")
        except Exception as e:
            self.assertIn("RT-EXCTRY-0123456789ab", str(e))
            self.assertIn("unsupported", str(e))
""",
                """\
import unittest
class T(unittest.TestCase):
    def test_exc(self):
        try:
            if False:
                run_probe()
            raise RuntimeError("RT-EXCTRY-0123456789ab unsupported")
        except RuntimeError as e:
            self.assertIn("RT-EXCTRY-0123456789ab", str(e))
            self.assertIn("unsupported", str(e))
""",
            ):
                (root / py_rel).write_text(bad_try, encoding="utf-8")
                self.assertFalse(checker.check_tree(root).ok, bad_try)

            (root / py_rel).write_text(
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_exc(self):
        try:
            subprocess.check_output(["cargo", "test"], text=True)
            self.fail("expected non-zero refusal")
        except subprocess.CalledProcessError as e:
            self.assertIn("RT-EXCTRY-0123456789ab", e.output)
            self.assertIn("unsupported", e.output)
""",
                encoding="utf-8",
            )
            rep_try = checker.check_tree(root)
            self.assertTrue(rep_try.ok, rep_try.errors)

            # 2. Python non-static checks reject `msg=` bug IDs, vacuous
            # `assertNotEqual(out.stderr, "")`, and `returncode != 42`.
            for bad_py_refusal in (
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_exc(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertNotEqual(out.stderr, "", msg="RT-EXCTRY-0123456789ab")
""",
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_exc(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertNotEqual(out.returncode, 0, msg="RT-EXCTRY-0123456789ab")
""",
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_exc(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertNotEqual(out.returncode, 42)
        self.assertIn("RT-EXCTRY-0123456789ab", out.stderr)
""",
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_exc(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        assert (out.returncode != 0 or True)
        self.assertIn("RT-EXCTRY-0123456789ab", out.stderr)
""",
            ):
                (root / py_rel).write_text(bad_py_refusal, encoding="utf-8")
                self.assertFalse(checker.check_tree(root).ok, bad_py_refusal)

            (root / py_rel).write_text(
                """\
import subprocess, unittest
class T(unittest.TestCase):
    def test_exc(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertNotEqual(out.returncode, 0)
        self.assertIn("RT-EXCTRY-0123456789ab", out.stderr)
""",
                encoding="utf-8",
            )
            rep_py_ok = checker.check_tree(root)
            self.assertTrue(rep_py_ok.ok, rep_py_ok.errors)

            # 3. Python forbids `os._exit(0)` across test, sibling, setup/
            # teardown hooks, and module top level (`if __name__` exempted).
            for bad_py_exit in (
                """\
import os, subprocess, unittest
class T(unittest.TestCase):
    def test_exc(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertNotEqual(out.returncode, 0)
        self.assertIn("RT-EXCTRY-0123456789ab", out.stderr)
        os._exit(0)
""",
                """\
import os, subprocess, unittest
def done():
    os._exit(0)
class T(unittest.TestCase):
    def test_exc(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertNotEqual(out.returncode, 0)
        self.assertIn("RT-EXCTRY-0123456789ab", out.stderr)
    def test_sibling(self):
        done()
""",
                """\
import subprocess, unittest
from os import *
_exit(0)
class T(unittest.TestCase):
    def test_exc(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertNotEqual(out.returncode, 0)
        self.assertIn("RT-EXCTRY-0123456789ab", out.stderr)
""",
                """\
import os, subprocess, unittest
class T(unittest.TestCase):
    def tearDown(self):
        os._exit(0)
    def test_exc(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertNotEqual(out.returncode, 0)
        self.assertIn("RT-EXCTRY-0123456789ab", out.stderr)
""",
            ):
                (root / py_rel).write_text(bad_py_exit, encoding="utf-8")
                self.assertFalse(checker.check_tree(root).ok, bad_py_exit)

            (root / py_rel).write_text(
                """\
import os, subprocess, unittest
class T(unittest.TestCase):
    def test_exc(self):
        out = subprocess.run(["cargo", "test"], capture_output=True, text=True)
        self.assertNotEqual(out.returncode, 0)
        self.assertIn("RT-EXCTRY-0123456789ab", out.stderr)
    def test_sibling_nonzero(self):
        if False:
            os._exit(0)
        self.assertTrue(True)
if __name__ == "__main__":
    unittest.main()
""",
                encoding="utf-8",
            )
            rep_py_exit_ok = checker.check_tree(root)
            self.assertTrue(rep_py_exit_ok.ok, rep_py_exit_ok.errors)

            # 4. Rust non-static exit refusal and sibling `exit(0)` checks:
            rs_rel = "anneal/tests/itree_diff/tests/phase0_proc_exit.rs"
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                '// PHASE0_TRIPWIRE(bug_id="ITREE-EXRS-0123456789ab", '
                'issue="https://github.com/google/zerocopy/issues/4912", '
                'owner="fixture-owner", added_date="2026-11-27", '
                'scope="Strict non-static exit refusal and sibling exit0 guard", '
                'rationale="Reject vacuous status.code() checks and sibling exit(0)", '
                f'regression_test="{rs_rel}::rt_guard")\n',
                encoding="utf-8",
            )
            for bad_rs in (
                """\
use std::process::Command;
#[test]
fn rt_guard() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-audit")).output().unwrap();
    assert!(out.status.code().is_some(), "ITREE-EXRS-0123456789ab");
}
""",
                """\
use std::process::Command;
#[test]
fn rt_guard() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-audit")).output().unwrap();
    assert_eq!(out.status.code(), Some(1), "ITREE-EXRS-0123456789ab");
}
""",
                """\
use std::process::Command;
#[test]
fn rt_guard() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-audit")).output().unwrap();
    assert_ne!(out.status.code(), Some(42));
    assert!(String::from_utf8_lossy(&out.stderr).contains("ITREE-EXRS-0123456789ab"));
}
""",
                """\
use std::process::Command;
#[test]
fn rt_guard() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-audit")).output().unwrap();
    assert!(out.status.code() != Some(42));
    assert!(String::from_utf8_lossy(&out.stderr).contains("ITREE-EXRS-0123456789ab"));
}
""",
                """\
use std::process::Command;
#[test]
fn rt_guard() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-audit")).output().unwrap();
    assert!(matches!(out.status.code(), Some(_)));
    assert!(String::from_utf8_lossy(&out.stderr).contains("ITREE-EXRS-0123456789ab"));
}
""",
                """\
use std::process::*;
#[test]
fn rt_guard() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-audit")).output().unwrap();
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).contains("ITREE-EXRS-0123456789ab"));
    exit(0);
}
""",
                """\
use std::process::Command;
#[test]
fn rt_guard() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-audit")).output().unwrap();
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).contains("ITREE-EXRS-0123456789ab"));
}
#[test]
fn sibling_masked() {
    std::process::exit(0);
}
""",
                """\
use std::process::Command;
#[test]
fn rt_guard() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-audit")).output().unwrap();
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).contains("ITREE-EXRS-0123456789ab"));
}
mod nested {
    fn bye() { std::process::exit(0); }
    #[test]
    fn sib() { bye(); }
}
""",
            ):
                (root / rs_rel).write_text(bad_rs, encoding="utf-8")
                self.assertFalse(checker.check_tree(root).ok, bad_rs)

            for good_rs in (
                """\
use std::process::Command;
#[test]
fn rt_guard() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-audit")).output().unwrap();
    assert!(matches!(out.status.code(), Some(c) if c != 0));
    assert!(String::from_utf8_lossy(&out.stderr).contains("ITREE-EXRS-0123456789ab"));
}
#[cfg(any())]
#[test]
fn disabled_sib() {
    std::process::exit(0);
}
""",
                """\
use std::process::Command;
#[test]
fn rt_guard() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-audit")).output().unwrap();
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("ITREE-EXRS-0123456789ab"));
}
""",
                """\
#[test]
fn rt_guard() {
    let res = run_audit();
    assert!(res.is_err(), "ITREE-EXRS-0123456789ab");
}
""",
            ):
                (root / rs_rel).write_text(good_rs, encoding="utf-8")
                rep_rs_ok = checker.check_tree(root)
                self.assertTrue(rep_rs_ok.ok, f"{good_rs}: {rep_rs_ok.errors}")

    def test_lean_public_modifiers_mir_ast_submodules_and_itree_diff_types(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _init_fixture_repo(root)

            # 1. `MirAst` import-only barrel + `Trusted/MirAst/*.lean` submodule
            #    type, plus Lean 4 `public def`, `@[expose] public def`, and
            #    `else if` branch alignment.
            ast_barrel = root / "anneal/trusted/lean/Trusted/MirAst.lean"
            ast_sub_dir = root / "anneal/trusted/lean/Trusted/MirAst"
            ast_sub_dir.mkdir(parents=True, exist_ok=True)
            ast_barrel.write_text(
                "module\npublic import Trusted.MirAst.Types\n",
                encoding="utf-8",
            )
            (ast_sub_dir / "Types.lean").write_text(
                "@[expose] public section\n"
                "namespace Trusted.MirAst\n"
                "inductive MirSubTy | unit | scalar\n"
                "end Trusted.MirAst\n"
                "end\n",
                encoding="utf-8",
            )

            ops_rel = "anneal/trusted/lean/Trusted/MirSemantics/Ops.lean"
            step_rel = "anneal/trusted/lean/Trusted/MirSemantics/Step.lean"
            itree_rel = "anneal/tests/itree_diff/tests/phase0_r12.rs"
            itree_target = f"{itree_rel}::rt_r12"
            bid_pub = "ITREE-PUBM-0123456789ab"
            bid_dot = "ITREE-MAST-abcdef012345"

            (root / "anneal/trusted/lean/Trusted/MirSemantics.lean").write_text(
                "import Trusted.MirSemantics.Ops\n"
                "import Trusted.MirSemantics.Step\n",
                encoding="utf-8",
            )
            (root / ops_rel).write_text(
                "module\n"
                "namespace Trusted.MirAst\n"
                f'-- PHASE0_TRIPWIRE(bug_id="{bid_dot}", '
                'issue="https://github.com/google/zerocopy/issues/4950", '
                'owner="fixture-owner", added_date="2026-11-27", '
                'scope="dot-proj MirAst submodule", '
                'rationale="Submodule type method", '
                f'regression_test="{itree_target}")\n'
                "@[expose] public noncomputable def MirSubTy.guardOp "
                "(t : MirSubTy) : StepResult :=\n"
                "  StepResult.fault .unsupported\n"
                "end Trusted.MirAst\n",
                encoding="utf-8",
            )
            (root / step_rel).write_text(
                "module\n"
                "namespace Trusted.MirSemantics\n"
                "open Trusted.MirAst\n"
                "public def evalBranch (b : Bool) : StepResult :=\n"
                "  if b then StepResult.ok\n"
                f'  -- PHASE0_TRIPWIRE(bug_id="{bid_pub}", '
                'issue="https://github.com/google/zerocopy/issues/4951", '
                'owner="fixture-owner", added_date="2026-11-27", '
                'scope="else if lean guard", '
                'rationale="Module public + else-if branch", '
                f'regression_test="{itree_target}")\n'
                "  else if !b\n"
                "  then StepResult.fault .unsupported\n"
                "  else StepResult.ok\n"
                "@[expose] public def evalExposedSync : StepResult :=\n"
                "  evalBranch false\n"
                "public def evalStep (t : MirSubTy) : StepResult :=\n"
                "  match t.guardOp with\n"
                "  | _ => evalExposedSync\n"
                "end Trusted.MirSemantics\n",
                encoding="utf-8",
            )
            (root / itree_rel).write_text(
                f"""\
use anneal_itree_diff::{{
    CaseReport, DifferentialConfig, DifferentialEngine, DifferentialReport,
    TerminalOutcome, TraceVal, UbFaultClass,
}};
#[test]
fn rt_r12() {{
    let cfg = DifferentialConfig::for_workspace(std::path::PathBuf::from("."));
    let eng = DifferentialEngine::prepare(cfg).unwrap();
    let rep: CaseReport = eng.run_case(&Default::default());
    let _ub = UbFaultClass::PointerOrMemoryAccess;
    let _val = TraceVal::u32(1);
    let _kind: Option<DifferentialReport> = None;
    assert!(
        matches!(rep.outcome, TerminalOutcome::CaptureRefused {{ .. }}),
        "{bid_dot}"
    );
    assert_eq!(
        rep.outcome,
        TerminalOutcome::CaptureRefused {{ reason: String::from("unsupported") }},
        "{bid_pub}"
    );
}}
#[test]
fn rt_r12_decoy() {{
    let cfg = DifferentialConfig::for_workspace(std::path::PathBuf::from("."));
    let eng = DifferentialEngine::prepare(cfg).unwrap();
    let rep: CaseReport = eng.run_case(&Default::default());
    assert_eq!(
        rep.outcome,
        TerminalOutcome::CaptureRefused {{ reason: String::from("unsupported") }},
        "ITREE-DECOY-999999999999"
    );
}}
""",
                encoding="utf-8",
            )
            rep_ok = checker.check_tree(root)
            self.assertTrue(rep_ok.ok, rep_ok.errors)

            # Uncalled `@[expose] public def decoyGuard` placed inside
            # `Trusted.MirSemantics` immediately after `evalStep` (before
            # `end Trusted.MirSemantics`) MUST NOT inherit reachability.
            decoy_target = f"{itree_rel}::rt_r12_decoy"
            saved_step = (root / step_rel).read_text(encoding="utf-8")
            decoy_decl = (
                "-- PHASE0_TRIPWIRE(bug_id=\"ITREE-DECOY-999999999999\", "
                'issue="https://github.com/google/zerocopy/issues/4952", '
                'owner="fixture-owner", added_date="2026-11-27", '
                'scope="dead expose public decoy", '
                'rationale="Must be caught as unreachable", '
                f'regression_test="{decoy_target}")\n'
                "@[expose] public def decoyGuard : StepResult :=\n"
                "  StepResult.fault .unsupported\n"
                "end Trusted.MirSemantics\n"
            )
            self.assertIn("end Trusted.MirSemantics\n", saved_step)
            decoy_text = saved_step.replace("end Trusted.MirSemantics\n", decoy_decl)
            (root / step_rel).write_text(decoy_text, encoding="utf-8")
            rep_decoy = checker.check_tree(root)
            self.assertFalse(rep_decoy.ok)
            decoy_err = "\n".join(rep_decoy.errors)
            self.assertIn("ITREE-DECOY-999999999999", decoy_err)
            self.assertIn(
                "guard in `Trusted.MirSemantics.decoyGuard` is unreachable from MirSemantics runtime semantics entrypoints",
                decoy_err,
            )
            self.assertNotIn("must positively bind", decoy_err)
            (root / step_rel).write_text(saved_step, encoding="utf-8")

            # 2. Phase-1 deletion requires flipping `CaptureRefused` assertions
            #    using `CaseReport`, `TerminalOutcome::FaultUb`, and
            #    `TerminalOutcome::Returned { ret: TraceVal::u32(1), .. }`.
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "phase0 r12 valid fixtures")
            base_sha = _git(root, "rev-parse", "HEAD")

            (root / ops_rel).write_text(
                "module\nnamespace Trusted.MirAst\n"
                "@[expose] public noncomputable def MirSubTy.guardOp "
                "(t : MirSubTy) : StepResult := StepResult.ok\n"
                "end Trusted.MirAst\n",
                encoding="utf-8",
            )
            (root / step_rel).write_text(
                "module\nnamespace Trusted.MirSemantics\n"
                "open Trusted.MirAst\n"
                "public def evalBranch (b : Bool) : StepResult := StepResult.ok\n"
                "public def evalStep (t : MirSubTy) : StepResult :=\n"
                "  match t.guardOp with\n"
                "  | _ => evalBranch false\n"
                "end Trusted.MirSemantics\n",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "phase1 unflipped")
            unflipped_sha = _git(root, "rev-parse", "HEAD")
            self.assertFalse(
                checker.check_phase1_cleanup(
                    root, base=base_sha, head=unflipped_sha
                ).ok
            )

            (root / itree_rel).write_text(
                """\
use anneal_itree_diff::{CaseReport, DifferentialConfig, DifferentialEngine, TerminalOutcome, TraceVal};
#[test]
fn rt_r12() {
    let cfg = DifferentialConfig::for_workspace(std::path::PathBuf::from("."));
    let eng = DifferentialEngine::prepare(cfg).unwrap();
    let rep: CaseReport = eng.run_case(&Default::default());
    assert!(matches!(rep.outcome, TerminalOutcome::FaultUb { .. }));
    assert_eq!(
        rep.outcome,
        TerminalOutcome::Returned {
            ret: TraceVal::u32(1),
            mem_digest: String::from("ok"),
        }
    );
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "phase1 flipped")
            flipped_sha = _git(root, "rev-parse", "HEAD")
            rep_p1 = checker.check_phase1_cleanup(
                root, base=base_sha, head=flipped_sha
            )
            self.assertTrue(rep_p1.ok, rep_p1.errors)

    def test_g2_r13_cfg_labels_while_generator_none_and_rel_fixture(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _init_fixture_repo(root)

            rs_rel = "anneal/tests/rustc-capture/tests/phase0_g2r13.rs"
            py_rel = "anneal/ci/test_phase0_g2r13.py"
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    f"""    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-R13RS-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4960",
        owner: "fixture-owner",
        added_date: "2026-11-27",
        scope: "cfg!, loop labels, and None tag polarity",
        rationale: "Must reject unreachable assertions and absent-tag assertions",
        regression_test: "{rs_rel}::g2_r13_rs",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
                ),
                encoding="utf-8",
            )
            (root / "anneal/trusted/audit/src/lib.rs").write_text(
                '// PHASE0_TRIPWIRE(bug_id="RT-R13PY-0123456789ab", '
                'issue="https://github.com/google/zerocopy/issues/4961", '
                'owner="fixture-owner", added_date="2026-11-27", '
                'scope="Python mutating while cond and generator yield", '
                f'rationale="Must reject unexecuted generators and dynamic while loops", regression_test="{py_rel}::test_py_r13")\n',
                encoding="utf-8",
            )

            valid_rs = """\
use std::process::Command;
#[test]
fn g2_r13_rs() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    let reason = String::from_utf8_lossy(&out.stderr);
    'outer: loop {
        'inner: for l in reason.lines() {
            if l.is_empty() { break 'inner; }
        }
        assert_eq!(out.status.code(), Some(1));
        assert!(reason.find("[PHASE0_TRIPWIRE:ITREE-R13RS-0123456789ab]").is_some());
        break 'outer;
    }
}
"""
            valid_py = """\
import unittest

class R13PyTests(unittest.TestCase):
    def test_py_r13(self):
        status, err = run_probe()
        self.assertEqual(status, "unsupported")
        self.assertIn("RT-R13PY-0123456789ab", err)
"""
            (root / rs_rel).write_text(valid_rs, encoding="utf-8")
            (root / py_rel).write_text(valid_py, encoding="utf-8")
            rep_base = checker.check_tree(root)
            self.assertTrue(rep_base.ok, rep_base.errors)

            # 1-3, 5: Rust cfg!(), stmt #[cfg], labels, and None polarity.
            bad_rs_variants = (
                """\
use std::process::Command;
#[test]
fn g2_r13_rs() {
    if cfg!(debug_assertions) { return; }
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    let reason = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(1));
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-R13RS-0123456789ab]"));
}
""",
                """\
use std::process::Command;
#[test]
fn g2_r13_rs() {
    if cfg!(not(feature = "x")) { return; }
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    let reason = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(1));
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-R13RS-0123456789ab]"));
}
""",
                """\
use std::process::Command;
#[test]
fn g2_r13_rs() {
    if !cfg!(debug_assertions) {
        let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
        let reason = String::from_utf8_lossy(&out.stderr);
        assert_eq!(out.status.code(), Some(1));
        assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-R13RS-0123456789ab]"));
    }
}
""",
                """\
use std::process::Command;
#[test]
fn g2_r13_rs() {
    if cfg!(target_os = "linux") { return; }
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    let reason = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(1));
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-R13RS-0123456789ab]"));
}
""",
                """\
use std::process::Command;
#[test]
fn g2_r13_rs() {
    #[cfg(debug_assertions)]
    return;
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    let reason = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(1));
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-R13RS-0123456789ab]"));
}
""",
                """\
use std::process::Command;
#[test]
fn g2_r13_rs() {
    'outer: loop {
        let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
        let reason = String::from_utf8_lossy(&out.stderr);
        for l in reason.lines() {
            if l.is_empty() { break 'outer; }
        }
        assert_eq!(out.status.code(), Some(1));
        assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-R13RS-0123456789ab]"));
        break;
    }
}
""",
                """\
use std::process::Command;
#[test]
fn g2_r13_rs() {
    'outer: for _ in 0..2 {
        let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
        let reason = String::from_utf8_lossy(&out.stderr);
        for l in reason.lines() {
            if l.is_empty() { continue 'outer; }
        }
        assert_eq!(out.status.code(), Some(1));
        assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-R13RS-0123456789ab]"));
    }
}
""",
                """\
use std::process::Command;
#[test]
fn g2_r13_rs() {
    'blk: {
        let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
        let reason = String::from_utf8_lossy(&out.stderr);
        for l in reason.lines() {
            if l.is_empty() { break 'blk; }
        }
        assert_eq!(out.status.code(), Some(1));
        assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-R13RS-0123456789ab]"));
    }
}
""",
                """\
use std::process::Command;
#[test]
fn g2_r13_rs() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    let reason = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(1));
    assert_eq!(reason.find("[PHASE0_TRIPWIRE:ITREE-R13RS-0123456789ab]"), None);
}
""",
                """\
use std::process::Command;
#[test]
fn g2_r13_rs() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    let reason = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(1));
    assert!(reason.find("[PHASE0_TRIPWIRE:ITREE-R13RS-0123456789ab]") == None);
}
""",
                """\
use std::process::Command;
#[test]
fn g2_r13_rs() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    let reason = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(1));
    assert!(None == reason.rfind("[PHASE0_TRIPWIRE:ITREE-R13RS-0123456789ab]"));
}
""",
                """\
use std::process::Command;
#[test]
fn g2_r13_rs() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).output().unwrap();
    let reason = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(1));
    assert_matches!(reason.strip_prefix("[PHASE0_TRIPWIRE:ITREE-R13RS-0123456789ab]"), Option::None);
}
""",
            )
            for idx, bad_rs in enumerate(bad_rs_variants):
                (root / rs_rel).write_text(bad_rs, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, f"variant {idx} should fail:\n{bad_rs}")
            (root / rs_rel).write_text(valid_rs, encoding="utf-8")

            # 4 & 3: Python mutating-flag while loop and generator yield.
            for idx, bad_py in enumerate(
                (
                    """\
import unittest

class R13PyTests(unittest.TestCase):
    def test_py_r13(self):
        retry = True
        while retry:
            status, err = run_probe()
            retry = False
            if "RT-R13PY-0123456789ab" in err:
                self.assertEqual(status, "unsupported")
                self.assertIn("RT-R13PY-0123456789ab", err)
                return
""",
                    """\
import unittest

class R13PyTests(unittest.TestCase):
    def test_py_r13(self):
        status, err = run_probe()
        self.assertEqual(status, "unsupported")
        self.assertIn("RT-R13PY-0123456789ab", err)
        yield
""",
                    """\
import unittest

class R13PyTests(unittest.TestCase):
    def test_py_r13(self):
        status, err = run_probe()
        self.assertEqual(status, "unsupported")
        self.assertIn("RT-R13PY-0123456789ab", err)
        yield from ()
""",
                )
            ):
                (root / py_rel).write_text(bad_py, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, f"py variant {idx} should fail:\n{bad_py}")

            # 6: `..`-relative `include_str!` witness in phase1-cleanup.
            (root / py_rel).write_text(valid_py, encoding="utf-8")
            (root / "anneal/tests/corpora").mkdir(parents=True, exist_ok=True)
            corpus_rel = "anneal/tests/corpora/r13_witness.rs"
            (root / corpus_rel).write_text("pub fn bad_witness() {}\n", encoding="utf-8")
            (root / rs_rel).write_text(
                """\
use std::process::Command;
const W: &str = include_str!("../../corpora/r13_witness.rs");
#[test]
fn g2_r13_rs() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).arg(W).output().unwrap();
    let reason = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(1));
    assert!(reason.contains("[PHASE0_TRIPWIRE:ITREE-R13RS-0123456789ab]"));
}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "r13 phase0 relative witness")
            p0_sha = _git(root, "rev-parse", "HEAD")

            # Mutate the relative external witness in Phase 1 -> MUST FAIL.
            (root / checker.TRIPWIRES_REL).write_text(BASE_TRIPWIRES_RS, encoding="utf-8")
            (root / rs_rel).write_text(
                """\
use std::process::Command;
const W: &str = include_str!("../../corpora/r13_witness.rs");
#[test]
fn g2_r13_rs() {
    let out = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin")).arg(W).output().unwrap();
    assert_eq!(out.status.code(), Some(0));
}
""",
                encoding="utf-8",
            )
            (root / corpus_rel).write_text("pub fn benign_witness() {}\n", encoding="utf-8")
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "r13 phase1 mutated relative witness")
            mut_sha = _git(root, "rev-parse", "HEAD")
            rep_mut = checker.check_phase1_cleanup(root, base=p0_sha, head=mut_sha)
            self.assertFalse(rep_mut.ok)
            self.assertIn("modified or dropped Phase-0 witness fixture file", "\n".join(rep_mut.errors))

            # Restoring the relative external witness -> PASSES.
            (root / corpus_rel).write_text("pub fn bad_witness() {}\n", encoding="utf-8")
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "r13 phase1 restored relative witness")
            ok_sha = _git(root, "rev-parse", "HEAD")
            rep_ok = checker.check_phase1_cleanup(root, base=p0_sha, head=ok_sha)
            self.assertTrue(rep_ok.ok, rep_ok.errors)

    def test_mir_semantics_root_and_needle_injection_tracking(self):
        with tempfile.TemporaryDirectory(prefix="phase0-root-inj-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)

            # Trusted/MirSemantics.lean must be enforced identically to
            # Trusted/MirSemantics/*.lean in check_tree and check_phase0_diff.
            root_lean = root / "anneal/trusted/lean/Trusted/MirSemantics.lean"
            rt_test = root / "anneal/tests/itree_diff/tests/phase0_r14_lean.rs"
            rt_test.write_text(
                """\
#[test]
fn rt_root_reach() {
    let fault = run_lean_step();
    assert_eq!(fault, Some(FaultKind::Unsupported), "LMIRI-ROOT-0123456789ab");
}
""",
                encoding="utf-8",
            )
            marker = (
                '-- PHASE0_TRIPWIRE(bug_id="LMIRI-ROOT-0123456789ab", '
                'issue="https://github.com/google/zerocopy/issues/4890", '
                'owner="fixture-owner", added_date="2026-11-27", '
                'scope="Guard root MirSemantics.lean", rationale="Root fallback", '
                'regression_test="anneal/tests/itree_diff/tests/phase0_r14_lean.rs::rt_root_reach")\n'
            )
            root_lean.write_text(
                "namespace Trusted.MirSemantics\n"
                "def evalStep := StepResult.ok\n"
                "end Trusted.MirSemantics\n",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "root lean base")
            base_sha = _git(root, "rev-parse", "HEAD")

            # Unguarded marker in root MirSemantics.lean fails check_tree.
            root_lean.write_text(
                "namespace Trusted.MirSemantics\n"
                + marker
                + "def evalStep := StepResult.ok\n"
                + "end Trusted.MirSemantics\n",
                encoding="utf-8",
            )
            rep_bad_root = checker.check_tree(root)
            self.assertFalse(rep_bad_root.ok)

            # Editing Trusted/MirSemantics.lean fails check_phase0_diff unless
            # allow_runtime_semantics_fallback is set and the marker reaches
            # `.fault .unsupported`, in which case both checks pass.
            root_lean.write_text(
                "namespace Trusted.MirSemantics\n"
                + marker
                + "def evalStep := StepResult.fault .unsupported\n"
                + "end Trusted.MirSemantics\n",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "root lean fallback")
            head_sha = _git(root, "rev-parse", "HEAD")
            self.assertTrue(checker.check_tree(root).ok, checker.check_tree(root).errors)
            self.assertFalse(checker.check_phase0_diff(root, base=base_sha, head=head_sha).ok)
            rep_allow = checker.check_phase0_diff(
                root,
                base=base_sha,
                head=head_sha,
                allow_runtime_semantics_fallback=True,
            )
            self.assertTrue(rep_allow.ok, rep_allow.errors)

            # Variable-bound formatting and string mutation needle injection
            # MUST FAIL in both Rust and Python.
            root_lean.write_text(
                "namespace Trusted.MirSemantics\n"
                "def evalStep := StepResult.ok\n"
                "end Trusted.MirSemantics\n",
                encoding="utf-8",
            )
            rs_rel = "anneal/tests/rustc-capture/tests/phase0_r14_inj.rs"
            py_rel = "anneal/ci/test_phase0_r14_inj.py"
            fw_lean = root / "anneal/trusted/lean/Trusted/Framework.lean"
            fw_lean.write_text(
                f"""\
-- PHASE0_TRIPWIRE(bug_id="RT-R14PY-0123456789ab", issue="https://github.com/google/zerocopy/issues/4892", owner="fixture-owner", added_date="2026-11-27", scope="Guard Python bound/mutated needle injection", rationale="No f-string/.format/+= needle spoofs", regression_test="{py_rel}::test_r14_py")
def fwAnchor := 0
""",
                encoding="utf-8",
            )
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    f"""    PHASE0_TRIPWIRE! {{
        bug_id: "ITREE-R14RS-0123456789ab",
        issue: "https://github.com/google/zerocopy/issues/4891",
        owner: "fixture-owner",
        added_date: "2026-11-27",
        scope: "Guard Rust bound/mutated needle injection",
        rationale: "No bound or push_str needle spoofs",
        regression_test: "{rs_rel}::r14_rs",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
                ),
                encoding="utf-8",
            )
            valid_py = """\
import subprocess, unittest
class TestR14Inj(unittest.TestCase):
    def test_r14_py(self):
        res = subprocess.run(["anneal/tools/anneal-mir-eval", "--probe"], capture_output=True, text=True)
        self.assertNotEqual(res.returncode, 0)
        self.assertIn("RT-R14PY-0123456789ab", res.stderr)
"""
            valid_rs = """\
#[test]
fn r14_rs() {
    let err = run_capture().expect_err("refusal");
    assert!(err.contains("[PHASE0_TRIPWIRE:ITREE-R14RS-0123456789ab]"));
}
"""
            (root / py_rel).write_text(valid_py, encoding="utf-8")
            (root / rs_rel).write_text(valid_rs, encoding="utf-8")
            self.assertTrue(checker.check_tree(root).ok, checker.check_tree(root).errors)

            bad_rust_inj = (
                # Local binding with format!.
                """\
#[test]
fn r14_rs() {
    let err = run_capture().expect_err("refusal");
    let s = format!("{err} [PHASE0_TRIPWIRE:ITREE-R14RS-0123456789ab]");
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-R14RS-0123456789ab]"));
}
""",
                # Local binding via inline `{tag}` const variable in format!.
                """\
#[test]
fn r14_rs() {
    let err = run_capture().expect_err("refusal");
    let tag = "[PHASE0_TRIPWIRE:ITREE-R14RS-0123456789ab]";
    let s = format!("{err} {tag}");
    assert!(s.contains("[PHASE0_TRIPWIRE:ITREE-R14RS-0123456789ab]"));
}
""",
                # In-place push_str mutation on observed variable.
                """\
#[test]
fn r14_rs() {
    let mut err = run_capture().expect_err("refusal");
    err.push_str(" [PHASE0_TRIPWIRE:ITREE-R14RS-0123456789ab]");
    assert!(err.contains("[PHASE0_TRIPWIRE:ITREE-R14RS-0123456789ab]"));
}
""",
                # In-place += and insert_str / write!.
                """\
#[test]
fn r14_rs() {
    let mut err = run_capture().expect_err("refusal");
    err += " [PHASE0_TRIPWIRE:ITREE-R14RS-0123456789ab]";
    assert!(err.trim().contains("[PHASE0_TRIPWIRE:ITREE-R14RS-0123456789ab]"));
}
""",
                """\
use std::fmt::Write;
#[test]
fn r14_rs() {
    let mut err = run_capture().expect_err("refusal");
    writeln!(&mut err, "[PHASE0_TRIPWIRE:ITREE-R14RS-0123456789ab]").unwrap();
    assert!(err.contains("[PHASE0_TRIPWIRE:ITREE-R14RS-0123456789ab]"));
}
""",
                # Conditional branch injecting needle on one path.
                """\
#[test]
fn r14_rs() {
    let mut err = run_capture().expect_err("refusal");
    if std::env::var("X").is_ok() {
        err.insert_str(0, "[PHASE0_TRIPWIRE:ITREE-R14RS-0123456789ab]");
    }
    assert!(err.contains("[PHASE0_TRIPWIRE:ITREE-R14RS-0123456789ab]"));
}
""",
            )
            for idx, bad_rs in enumerate(bad_rust_inj):
                (root / rs_rel).write_text(bad_rs, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, f"bad rust inj {idx} should fail:\n{bad_rs}")

            (root / rs_rel).write_text(valid_rs, encoding="utf-8")
            bad_py_inj = (
                # Bound f-string variable.
                """\
import subprocess, unittest
class TestR14Inj(unittest.TestCase):
    def test_r14_py(self):
        res = subprocess.run(["anneal/tools/anneal-mir-eval", "--probe"], capture_output=True, text=True)
        self.assertNotEqual(res.returncode, 0)
        s = f"{res.stderr} RT-R14PY-0123456789ab"
        self.assertIn("RT-R14PY-0123456789ab", s)
""",
                # Bound .format() variable with observed stderr.
                """\
import subprocess, unittest
class TestR14Inj(unittest.TestCase):
    def test_r14_py(self):
        res = subprocess.run(["anneal/tools/anneal-mir-eval", "--probe"], capture_output=True, text=True)
        self.assertNotEqual(res.returncode, 0)
        s = "{} {}".format(res.stderr, "RT-R14PY-0123456789ab")
        self.assertIn("RT-R14PY-0123456789ab", s.strip())
""",
                # Augmented assignment += on observed stderr.
                """\
import subprocess, unittest
class TestR14Inj(unittest.TestCase):
    def test_r14_py(self):
        res = subprocess.run(["anneal/tools/anneal-mir-eval", "--probe"], capture_output=True, text=True)
        self.assertNotEqual(res.returncode, 0)
        err = res.stderr
        err += " RT-R14PY-0123456789ab"
        self.assertIn("RT-R14PY-0123456789ab", err)
""",
                # List append on observed lines tested via comprehension.
                """\
import subprocess, unittest
class TestR14Inj(unittest.TestCase):
    def test_r14_py(self):
        res = subprocess.run(["anneal/tools/anneal-mir-eval", "--probe"], capture_output=True, text=True)
        self.assertNotEqual(res.returncode, 0)
        lines = [res.stderr]
        lines.append("RT-R14PY-0123456789ab")
        assert any("RT-R14PY-0123456789ab" in l for l in lines)
""",
                # Direct f-string combining observed stderr and needle.
                """\
import subprocess, unittest
class TestR14Inj(unittest.TestCase):
    def test_r14_py(self):
        res = subprocess.run(["anneal/tools/anneal-mir-eval", "--probe"], capture_output=True, text=True)
        self.assertNotEqual(res.returncode, 0)
        self.assertIn("RT-R14PY-0123456789ab", f"{res.stderr + 'RT-R14PY-0123456789ab'}")
""",
            )
            for idx, bad_py in enumerate(bad_py_inj):
                (root / py_rel).write_text(bad_py, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, f"bad py inj {idx} should fail:\n{bad_py}")

    def test_python_isolated_argv_unittest_msg_and_domain_refusal_tag(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory(prefix="phase0-py-msg-") as td:
            root = Path(td)
            _init_fixture_repo(root)
            py_rel = "anneal/ci/test_py_msg.py"
            fw_lean = root / "anneal/trusted/lean/Trusted/Framework.lean"
            fw_lean.write_text(
                (
                    '-- PHASE0_TRIPWIRE(bug_id="RT-PYMSG-0123456789ab", '
                    'issue="https://github.com/google/zerocopy/issues/99", '
                    'owner="fixture-owner", added_date="2026-11-27", '
                    'scope="Python isolated argv and msg refusal tags", '
                    'rationale="Allow -I -B, positional msg, and domain tag", '
                    f'regression_test="{py_rel}::test_m")\n'
                    "def fwAnchor := 0\n"
                ),
                encoding="utf-8",
            )

            ok_cases = (
                """\
import pathlib, subprocess, sys, unittest
SCRIPT_PATH = pathlib.Path("ci/check_bundle_tree.py")
class T(unittest.TestCase):
    def test_m(self):
        out = subprocess.run(
            [sys.executable, "-I", "-B", "ci/check_bundle_tree.py"],
            capture_output=True, text=True,
        )
        self.assertNotEqual(out.returncode, 0, "must exit non-zero")
        self.assertIn("RT-PYMSG-0123456789ab", out.stdout, "missing tag")
""",
                """\
import pathlib, subprocess, sys, unittest
SCRIPT_PATH = pathlib.Path(__file__).resolve().parent / "check_bundle_tree.py"
class T(unittest.TestCase):
    def test_m(self):
        cmd = [sys.executable, "-I", "-B", str(SCRIPT_PATH)]
        out = subprocess.run(cmd, capture_output=True, text=True)
        self.assertEqual(out.returncode, 1, "check exit")
        self.assertIn("unsupported", out.stdout, msg="RT-PYMSG-0123456789ab")
""",
                """\
import subprocess, sys, unittest
class T(unittest.TestCase):
    def test_m(self):
        cmd = [sys.executable, "-I", "-B", "ci/check_bundle_tree.py"]
        out = subprocess.run(cmd, capture_output=True, text=True)
        self.assertTrue(out.returncode != 0, "check")
        self.assertIn("unsupported", out.stdout, "RT-PYMSG-0123456789ab")
""",
                """\
import subprocess, sys, unittest
class T(unittest.TestCase):
    def test_m(self):
        out = subprocess.run(
            [sys.executable, "-I", "-B"] + ["ci/check_bundle_tree.py"],
            capture_output=True, text=True,
        )
        assert ".fault .unsupported" in out.stdout, "RT-PYMSG-0123456789ab"
""",
            )
            for idx, body in enumerate(ok_cases):
                (root / py_rel).write_text(body, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertTrue(rep.ok, f"ok case {idx} failed: {rep.errors}")

            bad_cases = (
                """\
import subprocess, sys, unittest
class T(unittest.TestCase):
    def test_m(self):
        out = subprocess.run(
            [sys.executable, "-I", "-c", "print('RT-PYMSG-0123456789ab unsupported')"],
            capture_output=True, text=True,
        )
        self.assertNotEqual(out.returncode, 0, "check")
        self.assertIn("RT-PYMSG-0123456789ab", out.stdout)
""",
                """\
import subprocess, sys, unittest
class T(unittest.TestCase):
    def test_m(self):
        out = subprocess.run(
            [sys.executable, "-m", "http.server"],
            capture_output=True, text=True,
        )
        self.assertIn("unsupported", out.stdout, msg="RT-PYMSG-0123456789ab")
""",
                """\
import subprocess, sys, unittest
class T(unittest.TestCase):
    def test_m(self):
        out = subprocess.run(
            [sys.executable, "-I", "-B", "/tmp/fake.py"],
            capture_output=True, text=True,
        )
        self.assertIn("unsupported", out.stdout, msg="RT-PYMSG-0123456789ab")
""",
                """\
import subprocess, sys, unittest
class T(unittest.TestCase):
    def test_m(self):
        out = subprocess.run(
            [sys.executable, "-I", "-B", "ci/check_bundle_tree.py"],
            capture_output=True, text=True,
        )
        self.assertNotEqual(out.returncode, 0, msg="RT-PYMSG-0123456789ab")
""",
                """\
import subprocess, sys, unittest
class T(unittest.TestCase):
    def test_m(self):
        out = subprocess.run(
            [sys.executable, "-I", "-B", "ci/check_bundle_tree.py"],
            capture_output=True, text=True,
        )
        self.assertIn("unsupported", "unsupported", msg="RT-PYMSG-0123456789ab")
""",
                """\
import subprocess, sys, unittest
class T(unittest.TestCase):
    def test_m(self):
        out = subprocess.run(
            [sys.executable, "-I", "-B", "ci/check_bundle_tree.py"],
            capture_output=True, text=True,
        )
        self.assertTrue(out.returncode != 0)
        assert True, "unsupported RT-PYMSG-0123456789ab"
""",
            )
            for idx, body in enumerate(bad_cases):
                (root / py_rel).write_text(body, encoding="utf-8")
                rep = checker.check_tree(root)
                self.assertFalse(rep.ok, f"bad case {idx} should fail:\n{body}")

    def test_phase1_cleanup_rejects_fail_on_success_guard_and_metadata_stubs(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory(prefix="phase1-pos-") as td:
            root = Path(td)
            _init_fixture_repo(root)
            bid = "ITREE-POS-0123456789ab"
            wit_rel = "anneal/tests/rustc-capture/tests/phase0_pos.rs"
            wit_src = "pub fn target_stub(x: u32) -> u32 { x }\n"
            (root / wit_rel).write_text(
                f"""\
const OLD_WITNESS: &[u8] = b"{wit_src.strip()}\\n";

#[test]
fn check_pos_bug() {{
    let out = run_capture(OLD_WITNESS, "--select=target_stub");
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).contains("[PHASE0_TRIPWIRE:{bid}]"));
}}
""",
                encoding="utf-8",
            )
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    f"""    PHASE0_TRIPWIRE! {{
        bug_id: "{bid}",
        issue: "https://github.com/google/zerocopy/issues/4999",
        owner: "fixture-owner",
        added_date: "2026-11-27",
        scope: "Require Phase-1 positive capture success",
        rationale: "Block fail-on-success guards and exit-neutral stubs",
        regression_test: "{wit_rel}::check_pos_bug",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
                ),
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "phase0 pos")
            p0_sha = _git(root, "rev-parse", "HEAD")

            # Phase-1 removal of tripwire must fail if test panics on success
            # or asserts only generic status/stream metadata.
            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS, encoding="utf-8"
            )
            bad_bodies = (
                """\
let output = run_capture(OLD_WITNESS, "--select=target_stub");
if output.status.success() {
    panic!("still captured!");
}
assert!(output.status.code().is_some());
""",
                """\
let output = run_capture(OLD_WITNESS, "--select=target_stub");
if output.status.success() {
    panic!("still captured!");
}
let ok_other = run_capture(OLD_WITNESS, "--select=target_stub");
assert!(ok_other.status.success());
""",
                """\
let output = run_capture(OLD_WITNESS, "--select=target_stub");
if !output.status.success() {
    assert!(true);
} else {
    panic!("unexpected success");
}
assert!(output.status.success() || true);
""",
                """\
let output = run_capture(OLD_WITNESS, "--select=target_stub");
match output.status.success() {
    true => panic!("still captured"),
    false => {}
}
assert!(output.status.code().is_some());
""",
                """\
let output = run_capture(OLD_WITNESS, "--select=target_stub");
assert!(output.status.code().is_some());
""",
                """\
let output = run_capture(OLD_WITNESS, "--select=target_stub");
assert_ne!(output.status.code(), None);
""",
                """\
let output = run_capture(OLD_WITNESS, "--select=target_stub");
assert!(!output.stderr.is_empty());
""",
                """\
let output = run_capture(OLD_WITNESS, "--select=target_stub");
assert_eq!(output.status.code().is_some(), !output.status.code().is_none());
""",
                """\
let output = run_capture(OLD_WITNESS, "--select=target_stub");
assert!(output.status.code().is_some() == !output.status.code().is_none());
""",
                """\
let output = run_capture(OLD_WITNESS, "--select=target_stub");
assert_eq!(output.status.code(), Some(1));
""",
                """\
let output = run_capture(OLD_WITNESS, "--select=target_stub");
assert_eq!(output.status.success(), false);
""",
                """\
let output = run_capture(OLD_WITNESS, "--select=target_stub");
assert_eq!(output.status.success(), output.status.code() == Some(0));
""",
                """\
let output = run_capture(OLD_WITNESS, "--select=target_stub");
let a = output.status.code().is_some();
let b = !output.status.code().is_none();
assert_eq!(a, b);
""",
            )
            for idx, b in enumerate(bad_bodies):
                (root / wit_rel).write_text(
                    f'const OLD_WITNESS: &[u8] = b"{wit_src.strip()}\\n";\n'
                    f"#[test]\nfn check_pos_bug() {{\n{b}}}\n",
                    encoding="utf-8",
                )
                rep = checker.check_phase1_cleanup(root, base=p0_sha)
                self.assertFalse(rep.ok, f"bad phase1 body {idx} passed:\n{b}")

            good_bodies = (
                """\
let output = run_capture(OLD_WITNESS, "--select=target_stub");
if !output.status.success() {
    panic!("capture failed!");
}
assert!(output.status.success());
""",
                """\
let output = run_capture(OLD_WITNESS, "--select=target_stub");
assert!(output.status.success() && !output.stdout.is_empty());
""",
                """\
let output = run_capture(OLD_WITNESS, "--select=target_stub");
assert_eq!(output.status.code(), Some(0));
""",
                """\
let output = run_capture(OLD_WITNESS, "--select=target_stub");
assert_eq!(output.status.success(), true);
""",
                """\
let output = run_capture(OLD_WITNESS, "--select=target_stub");
assert!(output.status.code() == Some(0));
""",
                """\
let output = run_capture(OLD_WITNESS, "--select=target_stub");
assert_ne!(output.status.success(), false);
""",
            )
            for idx, g in enumerate(good_bodies):
                (root / wit_rel).write_text(
                    f'const OLD_WITNESS: &[u8] = b"{wit_src.strip()}\\n";\n'
                    f"#[test]\nfn check_pos_bug() {{\n{g}}}\n",
                    encoding="utf-8",
                )
                rep = checker.check_phase1_cleanup(root, base=p0_sha)
                self.assertTrue(
                    rep.ok, f"good phase1 body {idx} failed: {rep.errors}"
                )

            # Python Phase-1 rejects tautological returncode comparisons too.
            py_bid = "ITREE-PYEQ-0123456789ab"
            py_wit_rel = "anneal/ci/test_pyeq_pos.py"
            (root / py_wit_rel).write_text(
                f"""\
import subprocess, unittest
WIT_SRC = {wit_src!r}
class PyEqTests(unittest.TestCase):
    def test_py_eq(self):
        proc = subprocess.run(["cargo", "test", WIT_SRC], capture_output=True)
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("[PHASE0_TRIPWIRE:{py_bid}]", proc.stderr.decode())
""",
                encoding="utf-8",
            )
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    f"""    PHASE0_TRIPWIRE! {{
        bug_id: "{py_bid}",
        issue: "https://github.com/google/zerocopy/issues/4998",
        owner: "fixture-owner",
        added_date: "2026-11-27",
        scope: "Require Phase-1 Python returncode equality to prove zero",
        rationale: "Block tautological returncode comparisons",
        regression_test: "{py_wit_rel}::test_py_eq",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
                ),
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "phase0 py eq")
            py_p0 = _git(root, "rev-parse", "HEAD")

            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS, encoding="utf-8"
            )
            for py_bad in (
                "self.assertEqual(proc.returncode is not None, not (proc.returncode is None))",
                "assert (proc.returncode is not None) == (proc.returncode != None)",
                "self.assertEqual(proc.returncode, 1)",
            ):
                (root / py_wit_rel).write_text(
                    f"""\
import subprocess, unittest
WIT_SRC = {wit_src!r}
class PyEqTests(unittest.TestCase):
    def test_py_eq(self):
        proc = subprocess.run(["cargo", "test", WIT_SRC], capture_output=True)
        {py_bad}
""",
                    encoding="utf-8",
                )
                rep = checker.check_phase1_cleanup(root, base=py_p0)
                self.assertFalse(rep.ok, f"bad py body passed: {py_bad}")

            (root / py_wit_rel).write_text(
                f"""\
import subprocess, unittest
WIT_SRC = {wit_src!r}
class PyEqTests(unittest.TestCase):
    def test_py_eq(self):
        proc = subprocess.run(["cargo", "test", WIT_SRC], capture_output=True)
        self.assertEqual(proc.returncode, 0)
""",
                encoding="utf-8",
            )
            rep_py_ok = checker.check_phase1_cleanup(root, base=py_p0)
            self.assertTrue(rep_py_ok.ok, rep_py_ok.errors)

    def test_independent_oracle_parity_lossless_bytes_test_ref_and_shared_diff(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="phase0-r21-") as tmp:
            root = Path(tmp)
            _init_fixture_repo(root)

            # 1. Parity checks must fail on capture-vs-capture, alias-bound
            #    capture-vs-capture, same-oracle vs same-oracle, and
            #    capture-vs-audit in both Rust and Python; succeed only
            #    against an independent oracle (Miri / mir-eval / Lean).
            bid_par = "ITREE-PAR-0123456789ab"
            wit_src = "pub fn parity_bad() {}"
            rs_rel = "anneal/tests/rustc-capture/tests/phase0_parity.rs"
            (root / rs_rel).write_text(
                f"""\
#[test]
fn test_parity_bug() {{
    let out = run_capture(b"{wit_src}", "--select=parity_bad");
    assert_eq!(out.status.code(), Some(1));
    assert!(out.stderr.contains("[PHASE0_TRIPWIRE:{bid_par}]"));
}}
""",
                encoding="utf-8",
            )
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    f"""    PHASE0_TRIPWIRE! {{
        bug_id: "{bid_par}",
        issue: "https://github.com/google/zerocopy/issues/4998",
        owner: "fixture-owner",
        added_date: "2026-11-27",
        scope: "Oracle parity enforcement",
        rationale: "Block capture-vs-capture equality",
        regression_test: "{rs_rel}::test_parity_bug",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
                ),
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "phase0 parity")
            p0_par = _git(root, "rev-parse", "HEAD")

            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS, encoding="utf-8"
            )
            bad_rs_parity = (
                """\
let first = run_capture(b"pub fn parity_bad() {}", "--select=parity_bad");
let second = run_capture(b"pub fn parity_bad() {}", "--select=parity_bad");
assert_eq!(first.status.success(), second.status.success());
""",
                """\
let first = run_capture(b"pub fn parity_bad() {}", "--select=parity_bad");
let second = run_capture(b"pub fn parity_bad() {}", "--select=parity_bad");
let s1 = first.status.success();
let s2 = second.status.success();
assert_eq!(s1, s2);
""",
                """\
let cap = run_capture(b"pub fn parity_bad() {}", "--select=parity_bad");
let aud = run_audit(b"pub fn parity_bad() {}", "--select=parity_bad");
assert_eq!(cap.status.success(), aud.status.success());
""",
                """\
let m1 = run_miri(b"pub fn parity_bad() {}");
let m2 = run_miri(b"pub fn parity_bad() {}");
assert_eq!(m1.status.success(), m2.status.success());
""",
            )
            for idx, body in enumerate(bad_rs_parity):
                (root / rs_rel).write_text(
                    f"#[test]\nfn test_parity_bug() {{\n{body}}}\n",
                    encoding="utf-8",
                )
                rep = checker.check_phase1_cleanup(root, base=p0_par)
                self.assertFalse(rep.ok, f"bad rust parity {idx} passed")

            good_rs_parity = (
                """\
let cap = run_capture(b"pub fn parity_bad() {}", "--select=parity_bad");
let oracle = run_miri(b"pub fn parity_bad() {}");
assert_eq!(cap.status.success(), oracle.status.success());
""",
                """\
let cap = std::process::Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
    .arg("pub fn parity_bad() {}")
    .arg("--select=parity_bad")
    .output()
    .unwrap();
let oracle = std::process::Command::new(env!("CARGO_BIN_EXE_anneal-mir-eval"))
    .arg("pub fn parity_bad() {}")
    .output()
    .unwrap();
assert_eq!(cap.status.code(), oracle.status.code());
""",
            )
            for idx, body in enumerate(good_rs_parity):
                (root / rs_rel).write_text(
                    f"#[test]\nfn test_parity_bug() {{\n{body}}}\n",
                    encoding="utf-8",
                )
                rep = checker.check_phase1_cleanup(root, base=p0_par)
                self.assertTrue(
                    rep.ok, f"good rust parity {idx} failed: {rep.errors}"
                )

            # 2. Lossless non-UTF-8 Python byte witnesses (`b"\xff"` vs
            #    `b"\xfe"`) and authoritative --test-ref binding protection.
            py_bid = "ITREE-BYTE-0123456789ab"
            py_rel = "anneal/ci/test_phase0_bytes.py"
            wit_ff = b"\xff\x00witness_bad"
            wit_fe = b"\xfe\x00witness_bad"
            ff_sha = hashlib.sha256(wit_ff).hexdigest()
            (root / py_rel).write_text(
                f"""\
import subprocess, unittest
WIT_BYTES = {wit_ff!r}
class ByteWitnessTests(unittest.TestCase):
    def test_refuse_bytes(self):
        proc = subprocess.run(["anneal/target/debug/anneal-rustc-capture", WIT_BYTES], capture_output=True)
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("[PHASE0_TRIPWIRE:{py_bid}]", proc.stderr.decode())
""",
                encoding="utf-8",
            )
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(
                    f"""    PHASE0_TRIPWIRE! {{
        bug_id: "{py_bid}",
        issue: "https://github.com/google/zerocopy/issues/4998",
        owner: "fixture-owner",
        added_date: "2026-11-27",
        scope: "Lossless byte witnesses and authoritative bindings",
        rationale: "Preserve non-UTF8 witnesses",
        regression_test: "{py_rel}::test_refuse_bytes",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
                ),
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "phase0 py bytes")
            py_p0 = _git(root, "rev-parse", "HEAD")

            (root / checker.TRIPWIRES_REL).write_text(
                BASE_TRIPWIRES_RS, encoding="utf-8"
            )
            (root / py_rel).write_text(
                f"""\
import subprocess, unittest
WIT_BYTES = {wit_fe!r}
class ByteWitnessTests(unittest.TestCase):
    def test_refuse_bytes(self):
        first = subprocess.run(["anneal/target/debug/anneal-rustc-capture", WIT_BYTES], capture_output=True)
        second = subprocess.run(["anneal/target/debug/anneal-rustc-capture", WIT_BYTES], capture_output=True)
        self.assertEqual(first.returncode, second.returncode)
""",
                encoding="utf-8",
            )
            rep_sub_fe = checker.check_phase1_cleanup(
                root, base=py_p0, witness_hashes={py_bid: ff_sha}
            )
            self.assertFalse(rep_sub_fe.ok)
            joined_fe = "\n".join(rep_sub_fe.errors)
            self.assertIn("preserve original Phase-0 failing witness", joined_fe)
            self.assertIn("witness_sha256", joined_fe)
            self.assertIn("positive verification", joined_fe)

            # Restore b"\xff..." and pair capture vs independent Miri -> PASS.
            (root / py_rel).write_text(
                f"""\
import subprocess, unittest
WIT_BYTES = {wit_ff!r}
class ByteWitnessTests(unittest.TestCase):
    def test_refuse_bytes(self):
        cap = subprocess.run(["anneal/target/debug/anneal-rustc-capture", WIT_BYTES], capture_output=True)
        oracle = subprocess.run(["cargo", "miri", "run"], capture_output=True)
        self.assertEqual(cap.returncode, oracle.returncode)
""",
                encoding="utf-8",
            )
            rep_py_ok = checker.check_phase1_cleanup(
                root, base=py_p0, witness_hashes={py_bid: ff_sha}
            )
            self.assertTrue(rep_py_ok.ok, rep_py_ok.errors)

            # Passing conflicting --test-ref against authoritative --base fails.
            alt_rel = "anneal/ci/test_phase0_alt.py"
            (root / alt_rel).write_text(
                (root / py_rel).read_text(encoding="utf-8").replace(
                    "test_refuse_bytes", "test_refuse_alt"
                ),
                encoding="utf-8",
            )
            rep_override = checker.check_phase1_cleanup(
                root,
                base=py_p0,
                test_refs={py_bid: f"{alt_rel}::test_refuse_alt"},
                witness_hashes={py_bid: ff_sha},
            )
            self.assertFalse(rep_override.ok)
            self.assertIn(
                "conflicts with authoritative regression_test binding",
                "\n".join(rep_override.errors),
            )

            # 3. `phase0-diff` touching a shared dedicated test file must keep
            #    every pre-existing tripwire's failing witness intact.
            shared_rel = "anneal/tests/rustc-capture/tests/phase0_shared.rs"
            bid_old = "ITREE-OLD-0123456789ab"
            bid_new = "ITREE-NEW-0123456789ab"
            (root / shared_rel).write_text(
                f"""\
#[test]
fn test_old_bug() {{
    let out = run_capture(b"pub fn old_witness() {{}}", "--select=old");
    assert_eq!(out.status.code(), Some(1));
    assert!(out.stderr.contains("[PHASE0_TRIPWIRE:{bid_old}]"));
}}
""",
                encoding="utf-8",
            )
            old_entry_src = f"""    PHASE0_TRIPWIRE! {{
        bug_id: "{bid_old}",
        issue: "https://github.com/google/zerocopy/issues/4998",
        owner: "fixture-owner",
        added_date: "2026-11-27",
        scope: "Pre-existing shared test witness",
        rationale: "Keep pre-existing witness",
        regression_test: "{shared_rel}::test_old_bug",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(old_entry_src), encoding="utf-8"
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "shared base")
            shared_base = _git(root, "rev-parse", "HEAD")

            new_entry_src = f"""{old_entry_src}
    PHASE0_TRIPWIRE! {{
        bug_id: "{bid_new}",
        issue: "https://github.com/google/zerocopy/issues/4998",
        owner: "fixture-owner",
        added_date: "2026-11-27",
        scope: "New shared test witness",
        rationale: "Add second entry in shared file",
        regression_test: "{shared_rel}::test_new_bug",
        activation: TripwireActivation::Always,
        predicate: TripwirePredicate::AnyBody,
    }},"""
            (root / checker.TRIPWIRES_REL).write_text(
                _with_active_entries(new_entry_src), encoding="utf-8"
            )
            # Mutate OLD_BUG's witness while adding NEW_BUG -> FAIL phase0-diff.
            (root / shared_rel).write_text(
                f"""\
#[test]
fn test_old_bug() {{
    let out = run_capture(b"pub fn replaced_witness() {{}}", "--select=old");
    assert_eq!(out.status.code(), Some(1));
    assert!(out.stderr.contains("[PHASE0_TRIPWIRE:{bid_old}]"));
}}

#[test]
fn test_new_bug() {{
    let out = run_capture(b"pub fn new_witness() {{}}", "--select=new");
    assert_eq!(out.status.code(), Some(1));
    assert!(out.stderr.contains("[PHASE0_TRIPWIRE:{bid_new}]"));
}}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "shared bad diff")
            shared_bad = _git(root, "rev-parse", "HEAD")
            rep_shared_bad = checker.check_phase0_diff(
                root, base=shared_base, head=shared_bad
            )
            self.assertFalse(rep_shared_bad.ok)
            self.assertIn(
                "preserve original Phase-0 failing witness",
                "\n".join(rep_shared_bad.errors),
            )

            # Preserving OLD_BUG's witness while adding NEW_BUG -> PASS.
            (root / shared_rel).write_text(
                f"""\
#[test]
fn test_old_bug() {{
    let out = run_capture(b"pub fn old_witness() {{}}", "--select=old");
    assert_eq!(out.status.code(), Some(1));
    assert!(out.stderr.contains("[PHASE0_TRIPWIRE:{bid_old}]"));
}}

#[test]
fn test_new_bug() {{
    let out = run_capture(b"pub fn new_witness() {{}}", "--select=new");
    assert_eq!(out.status.code(), Some(1));
    assert!(out.stderr.contains("[PHASE0_TRIPWIRE:{bid_new}]"));
}}
""",
                encoding="utf-8",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-q", "-m", "shared good diff")
            shared_good = _git(root, "rev-parse", "HEAD")
            rep_shared_good = checker.check_phase0_diff(
                root, base=shared_base, head=shared_good
            )
            self.assertTrue(rep_shared_good.ok, rep_shared_good.errors)


if __name__ == "__main__":
    unittest.main()
