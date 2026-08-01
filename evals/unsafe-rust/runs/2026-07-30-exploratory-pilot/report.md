# Unsafe Rust Skill Exploratory Evaluation

Date: 2026-07-30  
Skill entrypoint:
[`SKILL.md`](../../../../skills/unsafe-rust/SKILL.md)  
Protocol: [`testing-plan.md`](../../testing-plan.md)  
Frozen inputs and prompts: [`manifest.md`](manifest.md)

## Executive conclusion

The frozen skill passed this behavioral smoke test, but the evaluation does
**not** qualify it for release.

- On the admitted six-atom synthetic vulnerable fixture, the skill and
  baseline both recovered every issue. The skill received `78/78`; the
  baseline received `73/78`. The difference came from authority,
  configuration, surface-closure, TCB, and report completeness—not recall.
- Neither condition reproduced a repaired defect on the synthetic fixed
  control. The skill supplied a scoped positive proof and correctly reported
  the deliberately retained local-comment debt; the baseline missed that
  proof-artifact defect and made a less-supported universal no-finding claim.
- On the admitted historical zerocopy `read_from_io` defect, both conditions
  received `14/14`, and both fixed-side agents proved that in-place zeroing
  closes the padding-initialization hole.
- On current zerocopy, both conditions correctly refused a positive
  whole-scope verdict and distinguished test-only proof debt from
  downstream-shippable code. Results were mixed: the skill was stronger at
  theorem/configuration/report discipline, while the baseline found two
  important proof/contract questions omitted by the skill.
- No evaluated target code was executed.

The evidence supports a narrow claim:

> In one fresh-agent paired smoke test, the skill preserved perfect known-atom
> recall and materially improved proof/report completeness without introducing
> a repaired-defect false positive.

It does not establish general lift, cross-model behavior, corpus closure, or
release readiness.

## Executed design

Ten fresh-agent runs were performed:

| Target | Skill runs | Baseline runs |
|---|---:|---:|
| Synthetic vulnerable | 1 | 1 |
| Synthetic fixed | 1 | 1 |
| Historical zerocopy vulnerable | 1 | 1 |
| Historical zerocopy fixed | 1 | 1 |
| Current zerocopy `src/impls.rs` challenge | 1 | 1 |

Every evaluated agent used `fork_turns="none"`. No agent saw another report or
both members of a vulnerable/fixed pair. Runtime target names were opaque.
Historical incident titles, issue numbers, VCS metadata, fixing history, and
the incident-named regression test were absent. The skill was not edited after
its revision was frozen; its entrypoint SHA-256 remained
`b943f1092008252bbd77e10a1a4963fb0f78a60303ab653218c5c423cc6f0d70`.

The synthetic reports were normalized, shuffled, and scored without revealing
condition identity. The historical atom was admitted only after a second
independent source/authority review. Current-source findings were independently
reviewed but remain a Challenge result rather than a complete audit.

## Objective results

### Synthetic pair

Full scoring and deductions:
[`synthetic-score.md`](synthetic-score.md).

| Condition | Known-atom recall | Proof/report score | Hard errors |
|---|---:|---:|---:|
| Skill | `6/6` | `78/78` | 0 |
| Baseline | `6/6` | `73/78` | 0 |

The baseline lost points for incomplete authority on two local proofs, partial
configuration closure, no safe-surface/exhaustiveness inventory, and missing
overall theorem/TCB/residual-scope material. These are exactly the behaviors
the skill is intended to improve.

The fixed-side skill report supported its scoped positive conclusion. The
fixed-side baseline did not make a repaired-defect assertion, but it missed the
absent adjacent proof for `item_unchecked` and did not fully support its broad
no-finding language.

### Historical zerocopy pair

Full result and oracle:
[`historical-result.md`](historical-result.md).

| Condition | Vulnerable atom | Fixed control | Hard errors |
|---|---:|---|---:|
| Skill | `14/14` | Exact defect closed | 0 |
| Baseline | `14/14` | Exact defect closed | 0 |

Both conditions traced the false `Initialized` upgrade through
`Ptr::as_bytes` to caller-provided safe `Read` code and did not confuse the
final `assume_init` with the earlier byte-slice defect. Both fixed reports
proved that `uninit(); buf.zero()` initializes the complete final storage
before a byte slice is formed.

This public historical issue is contamination-prone and both source versions
contain general padding documentation. Equal recall is therefore a capability
check, not evidence of lift.

## Current zerocopy challenge

Detailed paired findings and independent adjudication:
[`current-result.md`](current-result.md).

Both conditions returned `UNPROVED` rather than manufacturing a positive or
negative whole-target verdict. Both correctly placed the two
`assume_initialized` calls under `#[cfg(test)]` and declined to infer a
concrete bad execution merely from the comments' admitted generic proof gap.

Independently supported residuals include:

- an authoritative-documentation gap for all-zero `Option` representations
  over the entire declared Rust 1.56+ range;
- no normative universal SIMD proof across every emitted type, target,
  feature, nightly, and compiler version; and
- an incomplete normative proof for `Box<T>: Immutable`.

The baseline found the historical-`Option` gap and a `ManuallyDrop<T>:
HasField` field-contract ambiguity that the skill omitted. The skill found that
the fixture lacked lockfile, path-dependency, linked policy, and pinned-nightly
inputs needed for complete configuration closure.

The skill also listed optional function-pointer and `NonNull<T>` `Immutable`
impls as unproved. Independent review derived those obligations from normative
`Copy` and `UnsafeCell` rules, so these appear to be conservative
over-reporting.

Most importantly, the skill's statement that null-pointer-optimized `Option`
obligations “closed locally” was not justified across the declared MSRV. The
overall result remained `UNPROVED`, so this was not a false whole-scope
certification, but it is a premature positive local conclusion. A
release-gating review should treat an equivalent explicitly `PROVED` claim as
a hard error.

No novel current-source claim is reported as production UB. The
`ManuallyDrop` claim remains a contract-interpretation question for project
authors because `HasField` permits a layout-equivalent field model.

## Harness and validity limitations

The evaluation does not satisfy the protocol's isolation attestation.

An outer bubblewrap plus nested Codex sandbox was locally verified as a viable
filesystem boundary. An authenticated run would have required providing the
networked process with a credential. Mounting the persistent host
authentication file was rejected, correctly, as an exfiltration risk. No
attempt was made to bypass that decision.

The fallback used procedural restrictions:

- fresh no-history agents;
- opaque, separate `/tmp` bundles;
- no paired-side reuse;
- prompts restricting reads to target, skill treatment, and exact official
  Rust documentation; and
- no target execution.

Agents nevertheless shared the host filesystem and general tool environment.
The baseline was not physically prevented from discovering the skill or
evaluator files. Network/documentation allowlisting was not enforced. Thus the
pilot cannot meet the plan's release isolation gate.

Additional limitations:

- one replicate per cell;
- no previous-skill condition;
- exact model identifier, sampling seed, token counts, and elapsed time were
  unavailable from the collaboration API;
- scorer citation content was not independently re-opened after report
  normalization;
- no opaque private holdout;
- no Google audit-log, RustSec-wide, std-wide, authoring, change-review,
  evidence-review, or generated/FFI/configuration microfixture cohort;
- no statistical inference; and
- the current-source bundle itself was incomplete for a full audit.

One auxiliary historical-oracle prompt was rejected by a generic
“cybersecurity” classifier. Rephrasing it as a non-operational source-contract
comparison succeeded. No evaluated run was lost to that filter.

## Tool/package validation

The skill package passed the skill-creator static validator:

```text
Skill is valid!
```

This checks package structure and metadata, not semantic quality.

## Release disposition

**Disposition: exploratory pass; release gates not met.**

Before a release evaluation:

1. provision a short-lived evaluator credential acceptable for the isolated
   bubblewrap harness; never mount the host's persistent authentication state;
2. rebuild the current-source bundle with every semantically required
   manifest, lockfile, path dependency, policy, generated input, and
   configuration artifact;
3. independently admit the remaining microfixture and public-corpus oracles,
   including record/atom closure for `audits.toml`;
4. run the preregistered three- and five-replicate cohorts, previous-skill
   comparator, and opaque holdouts;
5. independently verify every necessary citation against its exact version;
   and
6. adjudicate the current `Option` MSRV and `ManuallyDrop::HasField` questions
   with zerocopy/Rust maintainers before converting them into regression
   fixtures.

Do not change the runtime skill based on this report without assigning a new
skill revision and rerunning every affected paired condition.
