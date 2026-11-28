# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Trusted-boundary claim sync tests for the Rust lexer, unrecognized claim
patterns, and diverging inline fixtures."""

from .support import (
    extract_fixture_claims_for_file,
    parse_required_mir_wp_claims,
    Path,
    tempfile,
)


class LexerAndInlineFixtureCases:
    """`TrustedBoundaryClaimSyncTests` methods for the Rust lexer, unrecognized
    claim patterns, and diverging inline fixtures."""

    def test_rust_lexer_handles_raw_strings_and_char_literals(self):
        with tempfile.TemporaryDirectory(prefix="anneal-claim-rust-lex-") as tmp:
            shared = Path(tmp) / "mir_wp_fixture.rs"
            shared.write_text(
                'pub const SEM: &str = "def WpSoundnessClaim (_f : Nat) : Prop := True\\n";\n'
                'pub const WP: &str = "theorem wellFormed_and_spec_of_wp : '
                'Trusted.MirSemantics.WpSoundnessClaim wpProg := True.intro\\n";\n',
                encoding="utf-8",
            )
            # (a) Raw string ending in `\` (`r#"foo\"#`) followed by a `//`
            # comment containing `"` + `mir_wp_fixture::MirWpFixture` must NOT
            # trigger false delegation; (b) `'"'` char literal followed by
            # `// def FakeClaim` must strip the comment; (c) `'}'` and `']'`
            # char literals inside `SYNTHETIC_CANARIES` and `MirWpSyntheticSpec`
            # must NOT terminate balanced block extraction early.
            consumer = Path(tmp) / "boundary_audit.rs"
            consumer.write_text(
                'const RAW_END_BS: &str = r#"foo\\"#; // " mir_wp_fixture::MirWpFixture\n'
                'const C_RAW: &core::ffi::CStr = cr#"bar\\"#; // " mir_wp_fixture::Other\n'
                "const QUOTE_CH: char = '\"'; // def FakeClaim : Prop := True\n"
                "const BYTE_QUOTE: u8 = b'\"'; // def FakeByteClaim : Prop := True\n"
                "const SYNTHETIC_CANARIES: &[(&str, &str, char)] = &[\n"
                '    ("CanaryPositiveAddAnnealClaim", "canary_positive_add_anneal", \']\'),\n'
                "];\n"
                "impl MirWpSyntheticSpec {\n"
                "    fn valid() -> Self {\n"
                "        let _brace_ch: char = '}';\n"
                '        let _sem = "def WpSoundnessClaim (_f : Nat) : Prop := True\\n";\n'
                '        let _wp = "theorem wellFormed_and_spec_of_wp : '
                'Trusted.MirSemantics.WpSoundnessClaim wpProg := True.intro\\n";\n'
                "        Self {}\n"
                "    }\n"
                "}\n",
                encoding="utf-8",
            )
            label, claims, pairs = extract_fixture_claims_for_file(
                consumer, shared_fixture_path=shared
            )
            self.assertEqual(label, "boundary_audit.rs")
            self.assertEqual(
                claims,
                {"WpSoundnessClaim", "CanaryPositiveAddAnnealClaim"},
            )
            self.assertEqual(
                pairs,
                {
                    ("WpSoundnessClaim", "wellFormed_and_spec_of_wp"),
                    ("CanaryPositiveAddAnnealClaim", "canary_positive_add_anneal"),
                },
            )

    def test_unrecognized_claim_pattern_fails_closed(self):
        tb_src = """
def verifyMirWpCoreTheorems (env : Environment) : IO Unit := do
  requireClaimProof env locals semMod wpMod
    `Trusted.MirSemantics.WpSoundnessClaim
    (some `Anneal.MirWp.wpProg)
    `Anneal.MirWp.wellFormed_and_spec_of_wp
    [`Trusted.MirSemantics.SatisfiesPost]
  customHelper `Trusted.MirSemantics.NovelUnparsedClaim

def audit : IO Unit := pure ()
"""
        with self.assertRaises(AssertionError) as ctx:
            parse_required_mir_wp_claims(tb_src)
        self.assertIn("NovelUnparsedClaim", str(ctx.exception))

    def test_delegating_root_rejects_diverging_inline_fixture_in_submodule(self):
        with tempfile.TemporaryDirectory(prefix="anneal-claim-submod-") as tmp:
            shared = Path(tmp) / "mir_wp_fixture.rs"
            shared.write_text(
                'pub const SEM: &str = "def WpSoundnessClaim (_f : Nat) : Prop := True\\n";\n'
                'pub const WP: &str = "theorem wellFormed_and_spec_of_wp : '
                'Trusted.MirSemantics.WpSoundnessClaim wpProg := True.intro\\n";\n',
                encoding="utf-8",
            )
            root = Path(tmp) / "boundary_audit.rs"
            root.write_text(
                "use anneal_testkit::mir_wp_fixture::MirWpFixtureSpec;\n"
                "fn materialize(spec: &MirWpFixtureSpec) {}\n",
                encoding="utf-8",
            )
            sub_dir = Path(tmp) / "boundary_audit"
            sub_dir.mkdir()
            (sub_dir / "gates.rs").write_text(
                "use super::*;\nfn t() { materialize(&MirWpFixtureSpec::valid()); }\n",
                encoding="utf-8",
            )
            label, claims, _ = extract_fixture_claims_for_file(
                root, shared_fixture_path=shared
            )
            self.assertEqual(label, "boundary_audit.rs -> mir_wp_fixture.rs")
            self.assertEqual(claims, {"WpSoundnessClaim"})

            # Any diverging partial inline fixture in a submodule fails closed.
            (sub_dir / "stray.rs").write_text(
                'const SYNTHETIC_CANARIES: &[(&str, &str)] = '
                '&[("CanaryExtraDriftClaim", "canary_extra_drift")];\n',
                encoding="utf-8",
            )
            with self.assertRaises(AssertionError) as ctx:
                extract_fixture_claims_for_file(root, shared_fixture_path=shared)
            self.assertIn("diverging partial inline MirWp fixture", str(ctx.exception))
            self.assertIn("stray.rs", str(ctx.exception))
