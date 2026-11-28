# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Trusted-boundary claim sync tests for delegation to the shared
`mir_wp_fixture`."""

from .support import (
    assert_claim_parity,
    extract_fixture_claims_for_file,
    MIR_WP_FIXTURE,
    parse_required_mir_wp_claims,
    Path,
    tempfile,
    TRUSTED_BOUNDARY,
)


class FixtureDelegationCases:
    """`TrustedBoundaryClaimSyncTests` methods for delegation to the shared
    `mir_wp_fixture`."""

    def test_delegation_to_shared_mir_wp_fixture_works(self):
        tb_src = """
def verifyMirWpCoreTheorems (env : Environment) : IO Unit := do
  requireClaimProof env locals semMod wpMod
    `Trusted.MirSemantics.WpSoundnessClaim
    (some `Anneal.MirWp.wpProg)
    `Anneal.MirWp.wellFormed_and_spec_of_wp
    [`Trusted.MirSemantics.SatisfiesPost]
  for (claimName, proofName, reqConsts) in [
      (`Trusted.MirSemantics.CanaryPositiveAddAnnealClaim,
        `Anneal.MirWp.canary_positive_add_anneal, [posClaim])] do
    requireClaimProof env locals semMod canaryMod claimName none proofName reqConsts

def audit : IO Unit := pure ()
"""
        required = parse_required_mir_wp_claims(tb_src)

        with tempfile.TemporaryDirectory(prefix="anneal-claim-sync-deleg-") as tmp:
            shared = Path(tmp) / "mir_wp_fixture.rs"
            shared.write_text(
                "pub struct Canary { pub claim: &'static str, pub proof: &'static str }\n"
                'pub const CANARIES: &[Canary] = &[Canary { claim: "CanaryPositiveAddAnnealClaim", proof: "canary_positive_add_anneal" }];\n'
                'pub const SEM: &str = "def WpSoundnessClaim (_f : Nat) : Prop := True\\n";\n'
                'pub const WP: &str = "theorem wellFormed_and_spec_of_wp : Trusted.MirSemantics.WpSoundnessClaim wpProg := True.intro\\n";\n',
                encoding="utf-8",
            )
            consumer = Path(tmp) / "installed_smoke.rs"
            consumer.write_text(
                "use anneal_testkit::mir_wp_fixture;\n"
                "fn smoke() { let _ = mir_wp_fixture::MirWpFixture::valid(); }\n",
                encoding="utf-8",
            )
            label, claims, pairs = extract_fixture_claims_for_file(
                consumer, shared_fixture_path=shared
            )
            self.assertIn("mir_wp_fixture.rs", label)
            assert_claim_parity(required, label, claims, pairs)

            # A bare unused `use anneal_testkit::mir_wp_fixture;` must NOT count
            # as delegating.
            unused_import = Path(tmp) / "unused_import.rs"
            unused_import.write_text(
                "use anneal_testkit::mir_wp_fixture;\n"
                "fn smoke() {}\n",
                encoding="utf-8",
            )
            ui_label, ui_claims, ui_pairs = extract_fixture_claims_for_file(
                unused_import, shared_fixture_path=shared
            )
            self.assertEqual(ui_label, "unused_import.rs")
            with self.assertRaises(AssertionError):
                assert_claim_parity(required, ui_label, ui_claims, ui_pairs)

            # A mere comment/string mention of `mir_wp_fixture` must NOT trigger
            # delegation.
            non_delegating = Path(tmp) / "comment_only.rs"
            non_delegating.write_text(
                '// see anneal_testkit::mir_wp_fixture::MirWpFixture\n'
                'const NOTE: &str = "mir_wp_fixture::MirWpFixture";\n'
                'const SEM: &str = "def WpSoundnessClaim (_f : Nat) : Prop := True\\n";\n',
                encoding="utf-8",
            )
            nd_label, nd_claims, _ = extract_fixture_claims_for_file(
                non_delegating, shared_fixture_path=shared
            )
            self.assertEqual(nd_label, "comment_only.rs")
            self.assertEqual(nd_claims, {"WpSoundnessClaim"})

            # Active delegation alongside a partial/diverging local inline
            # fixture must fail closed.
            partial = Path(tmp) / "partial_deleg.rs"
            partial.write_text(
                "use anneal_testkit::mir_wp_fixture;\n"
                "fn smoke() { let _ = mir_wp_fixture::MirWpFixture::valid(); }\n"
                'const SYNTHETIC_CANARIES: &[(&str, &str)] = &[("CanaryPositiveAddAnnealClaim", "canary_positive_add_anneal")];\n',
                encoding="utf-8",
            )
            with self.assertRaises(AssertionError) as ctx:
                extract_fixture_claims_for_file(partial, shared_fixture_path=shared)
            self.assertIn("diverging partial inline MirWp fixture", str(ctx.exception))

    def test_delegation_against_live_mir_wp_fixture_matches_trusted_boundary(self):
        self.assertTrue(
            MIR_WP_FIXTURE.is_file(),
            f"expected live shared fixture at {MIR_WP_FIXTURE}",
        )
        required = parse_required_mir_wp_claims(
            TRUSTED_BOUNDARY.read_text(encoding="utf-8")
        )
        with tempfile.TemporaryDirectory(prefix="anneal-claim-live-deleg-") as tmp:
            consumer = Path(tmp) / "live_delegating_consumer.rs"
            consumer.write_text(
                "use anneal_testkit::mir_wp_fixture;\n"
                "fn smoke() { let _ = mir_wp_fixture::MirWpFixture::valid(); }\n",
                encoding="utf-8",
            )
            label, claims, pairs = extract_fixture_claims_for_file(
                consumer, shared_fixture_path=MIR_WP_FIXTURE
            )
            self.assertIn("mir_wp_fixture.rs", label)
            assert_claim_parity(required, label, claims, pairs)
