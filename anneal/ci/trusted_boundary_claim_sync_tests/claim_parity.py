# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Trusted-boundary claim sync tests for live claim parity and synthetic parity
failures."""

from .support import (
    assert_claim_parity,
    BOUNDARY_AUDIT,
    extract_fixture_claims_for_file,
    INSTALLED_SMOKE,
    parse_required_mir_wp_claims,
    Path,
    tempfile,
    TRUSTED_BOUNDARY,
)


class ClaimParityCases:
    """`TrustedBoundaryClaimSyncTests` methods for live claim parity and
    synthetic parity failures."""

    def test_live_installed_smoke_and_boundary_audit_match_trusted_boundary(self):
        required = parse_required_mir_wp_claims(
            TRUSTED_BOUNDARY.read_text(encoding="utf-8")
        )
        # Sanity-check baseline count: 2 core WP claims + >=25 canary claims.
        self.assertIn("WpSoundnessClaim", required)
        self.assertIn("WpFaultSoundnessClaim", required)
        self.assertGreaterEqual(len(required), 27)

        for rust_file in (INSTALLED_SMOKE, BOUNDARY_AUDIT):
            self.assertTrue(rust_file.is_file(), f"Missing Rust fixture: {rust_file}")
            label, claims, pairs = extract_fixture_claims_for_file(rust_file)
            assert_claim_parity(required, label, claims, pairs)

    def test_synthetic_missing_claim_fails_cleanly(self):
        tb_src = """
def verifyMirWpCoreTheorems (env : Environment) : IO Unit := do
  requireClaimProof env locals semMod wpMod
    `Trusted.MirSemantics.WpSoundnessClaim
    (some `Anneal.MirWp.wpProg)
    `Anneal.MirWp.wellFormed_and_spec_of_wp
    [`Trusted.MirSemantics.SatisfiesPost]
  requireClaimProof env locals semMod wpMod
    `Trusted.MirSemantics.ExecSoundnessClaimV2
    (some `Anneal.MirWp.execProgV2)
    `Anneal.MirWp.exec_soundness_v2
    [`Trusted.MirSemantics.Behavior]
  for (claimName, proofName, reqConsts) in [
      (`Trusted.MirSemantics.CanaryPositiveAddAnnealClaim,
        `Anneal.MirWp.canary_positive_add_anneal, [posClaim])] do
    requireClaimProof env locals semMod canaryMod claimName none proofName reqConsts

def audit : IO Unit := pure ()
"""
        required = parse_required_mir_wp_claims(tb_src)
        self.assertEqual(
            required,
            {
                "WpSoundnessClaim": "wellFormed_and_spec_of_wp",
                "ExecSoundnessClaimV2": "exec_soundness_v2",
                "CanaryPositiveAddAnnealClaim": "canary_positive_add_anneal",
            },
        )

        with tempfile.TemporaryDirectory(prefix="anneal-claim-sync-") as tmp:
            fixture_rs = Path(tmp) / "installed_smoke.rs"
            fixture_rs.write_text(
                'const SEM: &str = "def WpSoundnessClaim (_f : Nat) : Prop := True\\n";\n'
                'const WP: &str = "theorem wellFormed_and_spec_of_wp : Trusted.MirSemantics.WpSoundnessClaim wpProg := True.intro\\n";\n'
                'const CANARIES: &[(&str, &str)] = &[("CanaryPositiveAddAnnealClaim", "canary_positive_add_anneal")];\n',
                encoding="utf-8",
            )
            label, claims, pairs = extract_fixture_claims_for_file(
                fixture_rs, shared_fixture_path=Path(tmp) / "nonexistent.rs"
            )
            with self.assertRaises(AssertionError) as ctx:
                assert_claim_parity(required, label, claims, pairs)
            self.assertIn("ExecSoundnessClaimV2", str(ctx.exception))
            self.assertIn("exec_soundness_v2", str(ctx.exception))

    def test_swapped_proof_pairings_fail_closed(self):
        tb_src = """
def verifyMirWpCoreTheorems (env : Environment) : IO Unit := do
  requireClaimProof env locals semMod wpMod
    `Trusted.MirSemantics.WpSoundnessClaim
    (some `Anneal.MirWp.wpProg)
    `Anneal.MirWp.wellFormed_and_spec_of_wp
    [`Trusted.MirSemantics.SatisfiesPost]
  requireClaimProof env locals semMod wpMod
    `Trusted.MirSemantics.WpFaultSoundnessClaim
    (some `Anneal.MirWp.wpFaultProg)
    `Anneal.MirWp.reaches_fault_and_exclusive_of_wpFault
    [`Trusted.MirSemantics.WellFormed]

def audit : IO Unit := pure ()
"""
        required = parse_required_mir_wp_claims(tb_src)
        with tempfile.TemporaryDirectory(prefix="anneal-claim-swap-") as tmp:
            swapped_rs = Path(tmp) / "swapped.rs"
            # Exact same claim set and proof set, but proofs are swapped.
            swapped_rs.write_text(
                'const SEM: &str = "def WpSoundnessClaim (_f : Nat) : Prop := True\\n'
                'def WpFaultSoundnessClaim (_f : Nat) : Prop := True\\n";\n'
                'const WP: &str = "theorem reaches_fault_and_exclusive_of_wpFault : Trusted.MirSemantics.WpSoundnessClaim wpProg := True.intro\\n'
                'theorem wellFormed_and_spec_of_wp : Trusted.MirSemantics.WpFaultSoundnessClaim wpFaultProg := True.intro\\n";\n',
                encoding="utf-8",
            )
            label, claims, pairs = extract_fixture_claims_for_file(
                swapped_rs, shared_fixture_path=Path(tmp) / "nonexistent.rs"
            )
            with self.assertRaises(AssertionError) as ctx:
                assert_claim_parity(required, label, claims, pairs)
            self.assertIn("mismatched (claim, proof) pairs", str(ctx.exception))
