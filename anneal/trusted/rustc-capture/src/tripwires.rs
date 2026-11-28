// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Fail-closed Phase-0 containment tripwires for `anneal-rustc-capture`.
//!
//! Each registered rule narrows the set of admitted crates or MIR bodies before
//! proof emission (`Admitted' <= Admitted`) without altering lowering or the
//! operational semantics of any surviving body. Phase-0 emergency patches add
//! entries to [`ACTIVE_PHASE0_TRIPWIRES`] alongside a negative regression test
//! and public tracking issue; Phase-1 fixes delete the entry completely.

use std::collections::BTreeMap;

use rustc_middle::mir;

use crate::ir;

/// Environment key read solely from explicit `--env` CLI bindings to enable the
/// synthetic selftest tripwire without changing production behavior.
pub(crate) const SYNTHETIC_DEMO_ENV_KEY: &str = "ANNEAL_PHASE0_TRIPWIRE_SELFTEST";

/// Expected value for [`SYNTHETIC_DEMO_ENV_KEY`] activating the per-body hook.
pub(crate) const SYNTHETIC_DEMO_ENV_VALUE: &str = "ITREE-DEMO-000000000001";

/// Expected value for [`SYNTHETIC_DEMO_ENV_KEY`] activating the crate hook.
pub(crate) const SYNTHETIC_DEMO_CRATE_ENV_VALUE: &str = "ITREE-DEMO_CRATE-000000000001";

/// Optional `--env` key narrowing [`SYNTHETIC_DEMO_CRATE_TRIPWIRE`] to crates
/// enabling the named unstable feature (consulted only when
/// [`SYNTHETIC_DEMO_CRATE_TRIPWIRE`] is activated via
/// [`SYNTHETIC_DEMO_ENV_KEY`]).
pub(crate) const SYNTHETIC_DEMO_CRATE_FEATURE_ENV_KEY: &str =
    "ANNEAL_PHASE0_TRIPWIRE_SELFTEST_FEATURE";

/// Activation gate controlling when a tripwire rule fires.
#[allow(dead_code)] // `Always` is constructed when Phase-0 entries exist.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TripwireActivation {
    /// Active on every capture until deleted in Phase 1.
    Always,
    /// Inactive unless explicitly requested by test harnesses via `--env`.
    SyntheticSelftestOnly { env_key: &'static str, env_value: &'static str },
}

/// Predicate deciding whether a Phase-0 tripwire refuses a crate or body.
#[allow(dead_code)] // `Crate`/`Body` are constructed when Phase-0 entries exist.
#[derive(Clone, Copy)]
pub(crate) enum TripwirePredicate {
    /// Evaluated once per crate before body enumeration.
    Crate(fn(&CrateFacts<'_>) -> bool),
    /// Evaluated per MIR body prior to extraction.
    Body(fn(&CrateFacts<'_>, &str, &mir::Body<'_>) -> bool),
    /// Matches every visited MIR body whenever its activation gate holds.
    AnyBody,
}

impl std::fmt::Debug for TripwirePredicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Crate(_) => f.write_str("Crate(<fn>)"),
            Self::Body(_) => f.write_str("Body(<fn>)"),
            Self::AnyBody => f.write_str("AnyBody"),
        }
    }
}

/// Structured Phase-0 fail-closed capture refusal entry.
#[allow(dead_code)] // `issue` is inspected by CI policy and human audit.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Phase0Tripwire {
    pub bug_id: &'static str,
    pub issue: &'static str,
    pub owner: &'static str,
    pub added_date: &'static str,
    pub scope: &'static str,
    pub rationale: &'static str,
    pub regression_test: &'static str,
    pub activation: TripwireActivation,
    pub predicate: TripwirePredicate,
}

/// Demarcated macro for Phase-0 tripwire declarations so audits and CI policy
/// checks inspect every active entry cleanly.
macro_rules! PHASE0_TRIPWIRE {
    (
        bug_id: $bug_id:expr,
        issue: $issue:expr,
        owner: $owner:expr,
        added_date: $added_date:expr,
        scope: $scope:expr,
        rationale: $rationale:expr,
        regression_test: $regression_test:expr,
        activation: $activation:expr,
        predicate: $predicate:expr $(,)?
    ) => {
        Phase0Tripwire {
            bug_id: $bug_id,
            issue: $issue,
            owner: $owner,
            added_date: $added_date,
            scope: $scope,
            rationale: $rationale,
            regression_test: $regression_test,
            activation: $activation,
            predicate: $predicate,
        }
    };
}

/// Crate-level context available to Phase-0 tripwires before extraction.
///
/// `observed_unstable_features` contains every enabled gated `#![feature(...)]`
/// name (sorted) across both normal and `--stdlib-crate` captures, even though
/// `ir::Configuration::observed_unstable_features` stays empty for stdlib
/// captures.
#[allow(dead_code)] // Fields are read by crate/body predicate hooks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CrateFacts<'a> {
    pub crate_name: &'a str,
    pub crate_type: ir::CrateType,
    pub panic: ir::PanicStrategy,
    pub overflow_checks: bool,
    pub observed_unstable_features: &'a [String],
    pub declared_env: &'a BTreeMap<String, String>,
}

/// Built-in synthetic selftest tripwire verifying end-to-end capture refusal
/// with zero production impact unless explicitly requested via `--env`.
pub(crate) const SYNTHETIC_DEMO_TRIPWIRE: Phase0Tripwire = PHASE0_TRIPWIRE! {
    bug_id: "ITREE-DEMO-000000000001",
    issue: "selftest",
    owner: "anneal-maintainers",
    added_date: "2026-11-26",
    scope: "Synthetic selftest hook via explicit --env trigger",
    rationale: "Proves fail-closed Phase-0 capture refusal without production impact",
    regression_test: "anneal/tests/rustc-capture/tests/phase0_tripwires.rs::synthetic_demo_tripwire_refuses_only_when_explicitly_enabled",
    activation: TripwireActivation::SyntheticSelftestOnly {
        env_key: SYNTHETIC_DEMO_ENV_KEY,
        env_value: SYNTHETIC_DEMO_ENV_VALUE,
    },
    predicate: TripwirePredicate::AnyBody,
};

fn crate_selftest_matches(facts: &CrateFacts<'_>) -> bool {
    match facts.declared_env.get(SYNTHETIC_DEMO_CRATE_FEATURE_ENV_KEY) {
        Some(required) => facts.observed_unstable_features.iter().any(|feat| feat == required),
        None => true,
    }
}

/// Built-in synthetic crate-level selftest tripwire verifying `check_crate`
/// refusal with zero production impact unless requested via `--env`.
pub(crate) const SYNTHETIC_DEMO_CRATE_TRIPWIRE: Phase0Tripwire = PHASE0_TRIPWIRE! {
    bug_id: "ITREE-DEMO_CRATE-000000000001",
    issue: "selftest",
    owner: "anneal-maintainers",
    added_date: "2026-11-26",
    scope: "Synthetic crate-level selftest hook via explicit --env trigger",
    rationale: "Proves fail-closed Phase-0 crate-hook refusal without production impact",
    regression_test: "anneal/tests/rustc-capture/tests/phase0_tripwires.rs::synthetic_demo_tripwire_refuses_only_when_explicitly_enabled",
    activation: TripwireActivation::SyntheticSelftestOnly {
        env_key: SYNTHETIC_DEMO_ENV_KEY,
        env_value: SYNTHETIC_DEMO_CRATE_ENV_VALUE,
    },
    predicate: TripwirePredicate::Crate(crate_selftest_matches),
};

const SYNTHETIC_DEMO_TRIPWIRES: [Phase0Tripwire; 2] =
    [SYNTHETIC_DEMO_TRIPWIRE, SYNTHETIC_DEMO_CRATE_TRIPWIRE];

fn is_activation_enabled(
    activation: TripwireActivation,
    declared_env: &BTreeMap<String, String>,
) -> bool {
    match activation {
        TripwireActivation::Always => true,
        TripwireActivation::SyntheticSelftestOnly { env_key, env_value } => {
            declared_env.get(env_key).map(String::as_str) == Some(env_value)
        }
    }
}

fn format_refusal(rule: &Phase0Tripwire) -> String {
    format!("[PHASE0_TRIPWIRE:{}] {}: {}", rule.bug_id, rule.scope, rule.rationale)
}

fn evaluate_tripwire_rules<'a>(
    facts: &CrateFacts<'_>,
    rules: impl IntoIterator<Item = &'a Phase0Tripwire>,
    mut predicate_matches: impl FnMut(&TripwirePredicate) -> bool,
) -> Result<(), String> {
    let mut refusals = Vec::new();
    for rule in rules {
        if is_activation_enabled(rule.activation, facts.declared_env)
            && predicate_matches(&rule.predicate)
        {
            refusals.push(format_refusal(rule));
        }
    }
    if refusals.is_empty() { Ok(()) } else { Err(refusals.join("\n")) }
}

pub(crate) fn evaluate_crate_tripwires<'a>(
    facts: &CrateFacts<'_>,
    rules: impl IntoIterator<Item = &'a Phase0Tripwire>,
) -> Result<(), String> {
    evaluate_tripwire_rules(
        facts,
        rules,
        |pred| matches!(pred, TripwirePredicate::Crate(p) if p(facts)),
    )
}

pub(crate) fn evaluate_body_tripwires<'a>(
    facts: &CrateFacts<'_>,
    def_path: &str,
    body: &mir::Body<'_>,
    rules: impl IntoIterator<Item = &'a Phase0Tripwire>,
) -> Result<(), String> {
    evaluate_tripwire_rules(facts, rules, |pred| match pred {
        TripwirePredicate::Body(p) => p(facts, def_path, body),
        TripwirePredicate::AnyBody => true,
        TripwirePredicate::Crate(_) => false,
    })
}

/// Evaluate active crate-level Phase-0 tripwires before body extraction.
pub(crate) fn check_crate(facts: &CrateFacts<'_>) -> Result<(), String> {
    evaluate_crate_tripwires(facts, ACTIVE_PHASE0_TRIPWIRES.iter().chain(&SYNTHETIC_DEMO_TRIPWIRES))
}

/// Evaluate active per-body Phase-0 tripwires before IR translation.
pub(crate) fn check_mir_body(
    facts: &CrateFacts<'_>,
    def_path: &str,
    body: &mir::Body<'_>,
) -> Result<(), String> {
    evaluate_body_tripwires(
        facts,
        def_path,
        body,
        ACTIVE_PHASE0_TRIPWIRES.iter().chain(&SYNTHETIC_DEMO_TRIPWIRES),
    )
}

// === PHASE 0 MUTABLE REGISTRY START ===
// Add emergency Phase-0 rules using `PHASE0_TRIPWIRE!` inside
// `ACTIVE_PHASE0_TRIPWIRES` (with helper predicate functions below if needed),
// and delete resolved entries completely in Phase 1.

/// Active production Phase-0 tripwires. Add entries using `PHASE0_TRIPWIRE!`
/// during Phase 0 containment and delete them completely in Phase 1.
pub(crate) const ACTIVE_PHASE0_TRIPWIRES: &[Phase0Tripwire] = &[];

// === PHASE 0 MUTABLE REGISTRY END ===

#[cfg(test)]
mod tests {
    use super::*;

    fn default_crate_facts<'a>(
        declared_env: &'a BTreeMap<String, String>,
        features: &'a [String],
    ) -> CrateFacts<'a> {
        CrateFacts {
            crate_name: "demo",
            crate_type: ir::CrateType::Lib,
            panic: ir::PanicStrategy::Unwind,
            overflow_checks: false,
            observed_unstable_features: features,
            declared_env,
        }
    }

    fn has_bad_feature(facts: &CrateFacts<'_>) -> bool {
        facts.observed_unstable_features.iter().any(|f| f == "demo_bad_feature")
    }

    fn is_valid_bug_id(bug_id: &str) -> bool {
        let Some(tail) = bug_id
            .strip_prefix("ITREE-")
            .or_else(|| bug_id.strip_prefix("DIFF-"))
            .or_else(|| bug_id.strip_prefix("RT-"))
            .or_else(|| bug_id.strip_prefix("LMIRI-"))
            .or_else(|| bug_id.strip_prefix("MINIRUST-"))
        else {
            return false;
        };
        let Some((category, hex12)) = tail.rsplit_once('-') else {
            return false;
        };
        let mut cat_chars = category.chars();
        let cat_ok = cat_chars.next().is_some_and(|c| c.is_ascii_uppercase())
            && cat_chars.all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_');
        let hex_ok =
            hex12.len() == 12 && hex12.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'));
        cat_ok && hex_ok
    }

    #[test]
    fn active_production_tripwires_and_synthetic_hook_metadata_are_valid() {
        for rule in ACTIVE_PHASE0_TRIPWIRES {
            assert!(is_valid_bug_id(rule.bug_id), "{}", rule.bug_id);
            assert!(
                rule.issue.starts_with("https://github.com/google/zerocopy/issues/")
                    || rule.issue == "embargoed",
                "{}",
                rule.issue
            );
            assert!(!rule.owner.is_empty());
            assert_eq!(rule.added_date.len(), 10);
            assert!(!rule.scope.is_empty());
            assert!(!rule.rationale.is_empty());
            assert!(rule.regression_test.contains("::"));
            assert_eq!(rule.activation, TripwireActivation::Always);
        }
        assert!(is_valid_bug_id(SYNTHETIC_DEMO_TRIPWIRE.bug_id));
        assert!(is_valid_bug_id(SYNTHETIC_DEMO_CRATE_TRIPWIRE.bug_id));
    }

    #[test]
    fn bug_id_validator_accepts_unified_namespaces_and_rejects_malformed() {
        for valid in [
            "ITREE-CAST-0123456789ab",
            "ITREE-DEMO-000000000001",
            "DIFF-BORROW-fedcba987654",
            "RT-PROOF_HACK-deadbeef1234",
            "RT-CODE_AND_PROOF_HACK-001122334455",
            "LMIRI-CAST-001122334455",
            "MINIRUST-MOVE-aabbccddeeff",
        ] {
            assert!(is_valid_bug_id(valid), "expected valid bug ID: {valid}");
        }
        for invalid in [
            "",
            "BUG-123",
            "CORR-D17",
            "CORR-0123456789ab",
            "ITREE-cast-0123456789ab",
            "ITREE-CAST-01234",
            "ITREE-CAST-0123456789AB",
            "RT-PROOF_HACK-0123456789az",
            "LMIRI-bad",
            "MINIRUST-",
        ] {
            assert!(!is_valid_bug_id(invalid), "expected invalid bug ID: {invalid}");
        }
    }

    #[test]
    fn synthetic_tripwire_fires_only_when_explicitly_enabled() {
        let features = Vec::new();

        let empty_env = BTreeMap::new();
        let prod_facts = default_crate_facts(&empty_env, &features);
        assert!(evaluate_crate_tripwires(&prod_facts, &[SYNTHETIC_DEMO_TRIPWIRE]).is_ok());
        assert!(!is_activation_enabled(
            SYNTHETIC_DEMO_TRIPWIRE.activation,
            prod_facts.declared_env
        ));

        let wrong_env = BTreeMap::from([(SYNTHETIC_DEMO_ENV_KEY.to_owned(), "other".to_owned())]);
        let wrong_facts = default_crate_facts(&wrong_env, &features);
        assert!(!is_activation_enabled(
            SYNTHETIC_DEMO_TRIPWIRE.activation,
            wrong_facts.declared_env
        ));

        let enabled_env = BTreeMap::from([(
            SYNTHETIC_DEMO_ENV_KEY.to_owned(),
            SYNTHETIC_DEMO_ENV_VALUE.to_owned(),
        )]);
        let enabled_facts = default_crate_facts(&enabled_env, &features);
        assert!(is_activation_enabled(
            SYNTHETIC_DEMO_TRIPWIRE.activation,
            enabled_facts.declared_env
        ));
        assert!(check_crate(&prod_facts).is_ok());
        assert!(
            format_refusal(&SYNTHETIC_DEMO_TRIPWIRE)
                .starts_with("[PHASE0_TRIPWIRE:ITREE-DEMO-000000000001]")
        );

        let crate_env = BTreeMap::from([(
            SYNTHETIC_DEMO_ENV_KEY.to_owned(),
            SYNTHETIC_DEMO_CRATE_ENV_VALUE.to_owned(),
        )]);
        let crate_facts = default_crate_facts(&crate_env, &features);
        let crate_err = check_crate(&crate_facts).unwrap_err();
        assert!(
            crate_err.starts_with("[PHASE0_TRIPWIRE:ITREE-DEMO_CRATE-000000000001]"),
            "{crate_err}"
        );

        let f16_features = vec!["f16".to_owned()];
        let feature_only_env =
            BTreeMap::from([(SYNTHETIC_DEMO_CRATE_FEATURE_ENV_KEY.to_owned(), "f16".to_owned())]);
        assert!(check_crate(&default_crate_facts(&feature_only_env, &f16_features)).is_ok());

        let filtered_env = BTreeMap::from([
            (SYNTHETIC_DEMO_ENV_KEY.to_owned(), SYNTHETIC_DEMO_CRATE_ENV_VALUE.to_owned()),
            (SYNTHETIC_DEMO_CRATE_FEATURE_ENV_KEY.to_owned(), "f16".to_owned()),
        ]);
        assert!(check_crate(&default_crate_facts(&filtered_env, &features)).is_ok());
        let filtered_err =
            check_crate(&default_crate_facts(&filtered_env, &f16_features)).unwrap_err();
        assert!(
            filtered_err.starts_with("[PHASE0_TRIPWIRE:ITREE-DEMO_CRATE-000000000001]"),
            "{filtered_err}"
        );
    }

    #[test]
    fn active_crate_tripwires_refuse_targets_and_restore_on_removal() {
        let sample_rules = [PHASE0_TRIPWIRE! {
            bug_id: "DIFF-FEATURE-fedcba987654",
            issue: "https://github.com/google/zerocopy/issues/4095",
            owner: "anneal-maintainers",
            added_date: "2026-11-26",
            scope: "Refuse experimental unstable feature flag",
            rationale: "Temporary crate-level Phase-0 containment",
            regression_test: "anneal/tests/rustc-capture/tests/phase0_tripwires.rs::crate_demo",
            activation: TripwireActivation::Always,
            predicate: TripwirePredicate::Crate(has_bad_feature),
        }];

        let empty_env = BTreeMap::new();
        let bad_features = vec!["demo_bad_feature".to_owned()];
        let crate_bad = default_crate_facts(&empty_env, &bad_features);
        let crate_err = evaluate_crate_tripwires(&crate_bad, &sample_rules).unwrap_err();
        assert!(crate_err.contains("[PHASE0_TRIPWIRE:DIFF-FEATURE-fedcba987654]"), "{crate_err}");

        let ok_features = Vec::new();
        let crate_ok = default_crate_facts(&empty_env, &ok_features);
        assert!(evaluate_crate_tripwires(&crate_ok, &sample_rules).is_ok());

        // Deleting all Phase-0 rules restores admission for previously matched
        // targets.
        assert!(evaluate_crate_tripwires(&crate_bad, &[]).is_ok());
    }

    #[test]
    fn overlapping_crate_and_body_tripwires_report_every_matching_rule() {
        let empty_env = BTreeMap::new();
        let bad_features = vec!["demo_bad_feature".to_owned()];
        let crate_bad = default_crate_facts(&empty_env, &bad_features);
        let crate_rules = [
            PHASE0_TRIPWIRE! {
                bug_id: "DIFF-FEATURE-fedcba987654",
                issue: "https://github.com/google/zerocopy/issues/4095",
                owner: "anneal-maintainers",
                added_date: "2026-11-26",
                scope: "First overlapping crate guard",
                rationale: "Check multi-match refusal reporting",
                regression_test: "anneal/tests/rustc-capture/tests/phase0_tripwires.rs::c1",
                activation: TripwireActivation::Always,
                predicate: TripwirePredicate::Crate(has_bad_feature),
            },
            PHASE0_TRIPWIRE! {
                bug_id: "ITREE-CRATE2-0123456789ab",
                issue: "https://github.com/google/zerocopy/issues/4096",
                owner: "anneal-maintainers",
                added_date: "2026-11-26",
                scope: "Second overlapping crate guard",
                rationale: "Check later rule remains observable",
                regression_test: "anneal/tests/rustc-capture/tests/phase0_tripwires.rs::c2",
                activation: TripwireActivation::Always,
                predicate: TripwirePredicate::Crate(has_bad_feature),
            },
        ];
        let crate_err = evaluate_crate_tripwires(&crate_bad, &crate_rules).unwrap_err();
        assert!(crate_err.contains("[PHASE0_TRIPWIRE:DIFF-FEATURE-fedcba987654]"), "{crate_err}");
        assert!(crate_err.contains("[PHASE0_TRIPWIRE:ITREE-CRATE2-0123456789ab]"), "{crate_err}");

        // Overlapping `AnyBody` predicates evaluated through the shared rule
        // evaluator must report every matching tag rather than stopping early.
        let body_rules = [
            PHASE0_TRIPWIRE! {
                bug_id: "ITREE-BODY1-111111111111",
                issue: "https://github.com/google/zerocopy/issues/4097",
                owner: "anneal-maintainers",
                added_date: "2026-11-26",
                scope: "First overlapping body guard",
                rationale: "Check multi-match body refusal reporting",
                regression_test: "anneal/tests/rustc-capture/tests/phase0_tripwires.rs::b1",
                activation: TripwireActivation::Always,
                predicate: TripwirePredicate::AnyBody,
            },
            PHASE0_TRIPWIRE! {
                bug_id: "ITREE-BODY2-222222222222",
                issue: "https://github.com/google/zerocopy/issues/4098",
                owner: "anneal-maintainers",
                added_date: "2026-11-26",
                scope: "Second overlapping body guard",
                rationale: "Check later body rule remains observable",
                regression_test: "anneal/tests/rustc-capture/tests/phase0_tripwires.rs::b2",
                activation: TripwireActivation::Always,
                predicate: TripwirePredicate::AnyBody,
            },
        ];
        let body_err = evaluate_tripwire_rules(&crate_bad, &body_rules, |p| {
            matches!(p, TripwirePredicate::AnyBody)
        })
        .unwrap_err();
        assert!(body_err.contains("[PHASE0_TRIPWIRE:ITREE-BODY1-111111111111]"), "{body_err}");
        assert!(body_err.contains("[PHASE0_TRIPWIRE:ITREE-BODY2-222222222222]"), "{body_err}");
    }
}
