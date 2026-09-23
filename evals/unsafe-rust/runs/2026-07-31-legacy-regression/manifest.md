# 2026-07-31 Legacy Regression Replay Manifest

> **Evaluator-only material**

## Status

This was a source-only, protocol-equivalent replay of the 2026-07-30
exploratory pilot after the `unsafe-rust` redesign. It was not byte-identical:
the prior run did not preserve its raw prompts, raw historical/current reports,
scorer prompt, or old skill archive. The reconstructed prompts below were
frozen before the first evaluated run.

This remains an exploratory one-replicate experiment. It does not satisfy the
release protocol's hardened filesystem, documentation mirror, model/seed,
replicate-count, previous-skill, or statistical gates.

No target was modified, built, tested, expanded by execution, or otherwise
executed.

## Frozen identities

- Skill package tree digest:
  `d97b9ace50109216614fbb7c975ac9c97508bfa928381d247869699593a2bcdd`
- Skill entrypoint digest:
  `2b063ad7d8c6a3f5051294e3c9ed49c8850397645b46772cd40ec6ae7136531e`
- Synthetic vulnerable bundle:
  `e561c4a3ebf71800857edeedc217227bf152a719845b74b5ded4bac4f77081c3`
- Synthetic fixed bundle:
  `27a820a8a590194916cb25a3b39b38aa3a04cc1556636a1b96cbebee755d3a51`
- Historical vulnerable source: commit
  `49a13ba945954a6127036165499b6242e74bc3c6`; sanitized bundle
  `450562e0515de2e60836b133e2a03a6ef7c3c65976866dde6d99a4b2f4dced25`
- Historical fixed source: commit
  `f99854afb33365e9dada073a166b3047df7109d1`; sanitized bundle
  `62c51935d22fb64d363482e50ce04658e0f674e570324243f48dde1f92448e4f`
- Current source: commit
  `53a3fbfa15d656b25b74688369f7248ff354a021`; bundle
  `3242db7402b801cefb4425fd36c9c117906b1647765006b6533c8fde6b8ffb2b`

Digests use GNU tar with sorted names, timestamp zero, numeric owner/group
zero, and preserved contents/modes. Every duplicate opaque target copy was
verified against the applicable bundle digest before use.

The collaboration API exposed no exact hosted-model identifier, sampling seed,
token count, or effective reasoning setting. Every evaluated run used a fresh
agent with `fork_turns="none"` and inherited the same parent configuration.

## Cells and reports

| Target | Condition | Runtime target | Agent | Raw report | Report SHA-256 |
|---|---|---|---|---|---|
| Synthetic vulnerable | skill | `m7q4` | `q4m7` | [`reports/q4m7.md`](reports/q4m7.md) | `40cc2816b61ded7564165df37c5eb194630bea11bf997bd6201e86a0e229d4cf` |
| Synthetic vulnerable | no-skill | `r2v9` | `v9r2` | [`reports/v9r2.md`](reports/v9r2.md) | `6e0d30258f4fc0a13a66a96479b9979c48188c6ce1d2d9b55f51e8f9feb6197b` |
| Synthetic fixed | skill | `k8d3` | `d3k8` | [`reports/d3k8.md`](reports/d3k8.md) | `e30216795e6de6a932ebc1921a5fb365b4bbae69af5f527df7ebc6cb24858734` |
| Synthetic fixed | no-skill | `x5p1` | `p1x5` | [`reports/p1x5.md`](reports/p1x5.md) | `7c8c39586d8526f24ec8e4a4c490ef7a4a2f427701bd1fe5d713b0b083a2fffa` |
| Historical vulnerable | skill | `a9n6` | `n6a9` | [`reports/n6a9.md`](reports/n6a9.md) | `88688cd9ac71e7aa42759009cbafc09adc187f1bcff457be65bc0334f6950f88` |
| Historical vulnerable | no-skill | `u3c8` | `g2r6` | [`reports/g2r6.md`](reports/g2r6.md) | `47ca6fc15d041131fd758f456d9290851a12d8998f5e054dd9b16c1f8a50342b` |
| Historical fixed | skill | `f4w7` | `w7f4` | [`reports/w7f4.md`](reports/w7f4.md) | `cfcd988d84b4af72dfd19e7c4bd5ad25fd1cc4e87890b9bbdfdd5e8d0a92d995` |
| Historical fixed | no-skill | `h2j5` | `j5h2` | [`reports/j5h2.md`](reports/j5h2.md) | `c58c18020067277d795eb431f94314bddb4289d95dd46c57acbba78f727712a9` |
| Current challenge | skill | `z6b1` | `b1z6` | [`reports/b1z6.md`](reports/b1z6.md) | `733cf5800b5b4f12a01590e656e4227a0e6d6b26bd96f49efa0002af035acd23` |
| Current challenge | no-skill | `c9t4` | `t4c9` | [`reports/t4c9.md`](reports/t4c9.md) | `a707a360c214640270b04ac2da5f38da8ed2da512217320bbddcfdb2e26f2130` |

No agent saw two cells or both members of a vulnerable/fixed pair.

## Frozen prompt protocol

The skill condition began:

```text
Act as a fresh source-audit agent. First read the complete unsafe Rust skill
package rooted at [SKILL]/SKILL.md, including every reference it directs you
to for this task, and follow it as $unsafe-rust.
```

The baseline omitted that sentence and was told not to inspect any unsafe-Rust
skill. Both conditions then received the same target-specific request:

- Synthetic: audit the crate at `[TARGET]`; its support policy is
  `SUPPORT.md`.
- Historical: audit `FromBytes::read_from_io` and every definition, helper,
  contract, and invariant on which its proof depends; Rust 1.84.1, feature
  `std`, `x86_64-unknown-linux-gnu`.
- Current: audit `src/impls.rs`, the public unsafe-trait contracts implemented
  there, invoked macro definitions, and relevant Cargo/build/configuration
  policy.

Every initial prompt ended:

```text
Inspect only that target directory [and, for treatment, the stated skill
directory] and exact versioned official Rust Reference or standard-library
documentation needed to verify claims. Do not inspect sibling directories,
the enclosing repository, version-control history, evaluator material, or
prior reports. Do not modify, build, test, macro-expand by execution, or
otherwise execute the target. Return a complete but reasonably concise
source-audit report in your final response.
```

Long-running cells received only target-neutral steering such as “complete
with your current source-only findings” or “do not widen scope.” No finding,
location, contract, or expected verdict was supplied.

## Isolation and run deviations

The same procedural-isolation limitation as the prior pilot applies: agents
shared a host filesystem and were instructed, not mechanically prevented, from
reading forbidden paths. Network allowlisting and an offline documentation
mirror were unavailable.

Two treatment agents reported that an initial tool invocation ignored its
requested working directory and listed enclosing-workspace filenames. Both
stopped immediately and reported that they opened or used no sibling contents.

The first historical-vulnerable baseline agent found the correct defect but
stalled while waiting for a helper and produced no final report. That attempt
was invalidated. An accidentally over-specific replacement prompt was aborted
before it returned any result and was not scored. The recorded `g2r6` report
came from a new neutral-prompt agent forbidden to spawn helpers.

## Scoring and adjudication

The synthetic reports were copied under labels A–D and scored by a fresh agent
which knew vulnerable versus fixed membership but not condition identity. It
saw no target source, skill, prior results, or condition mapping. The raw score
is [`blind-synthetic-score.md`](blind-synthetic-score.md).

Fresh independent agents compared the historical and current reports with raw
source and applicable official documentation. Their raw conclusions are
[`historical-adjudication.md`](historical-adjudication.md) and
[`current-adjudication.md`](current-adjudication.md). The evaluator corrected
their claim that links to paired opaque copies were snapshot-binding errors:
each report correctly linked its own byte-identical, pre-hashed target copy.

