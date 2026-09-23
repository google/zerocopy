# 2026-07-31 Abstraction-Design V1 Manifest

> **Evaluator-only material. Do not expose this file to evaluated agents.**

## Status and scope

This is a preregistered, source-only, 54-run exploratory evaluation of the
conditional abstraction-design workflow. The full protocol and gates are in
[`../../abstraction-design-plan.md`](../../abstraction-design-plan.md); exact
atoms are in the private
[`../../fixtures/abstraction-design-v1/README.md`](../../fixtures/abstraction-design-v1/README.md).

“Exhaustive” means capability-closure over the nine behaviors named in that
plan, not coverage of every possible unsafe-Rust abstraction.

The skill and comparator were frozen before the first valid evaluated run. No
target may be modified, built, tested, expanded by execution, or otherwise
executed.

## Frozen package identities

- Treatment tree digest:
  `d97b9ace50109216614fbb7c975ac9c97508bfa928381d247869699593a2bcdd`
- Treatment `SKILL.md` digest:
  `2b063ad7d8c6a3f5051294e3c9ed49c8850397645b46772cd40ec6ae7136531e`
- Core-ablation tree digest:
  `7ae4d42abd086720ed97bf1ef8b22f66b1d0ed33a0a5834b17eebfdc245c4d52`
- Core-ablation `SKILL.md` digest:
  `c2f07d263ce89d758985d6ff388ca344e038c1db111f2298cc5ddef051697595`

The treatment is a byte-for-byte copy of `skills/unsafe-rust`. The comparator
removes the abstraction-design reference, its activation/routing paragraphs,
its optional report-template section, and its design-only cross-references;
ordinary proof, API, configuration, authority, TCB, and verdict content is
unchanged. Both packages passed the skill static validator.

## Frozen fixture identities

| Mode | Source directory | Deterministic tree digest |
|---|---|---|
| A | `a_acceptance` | `f3564d5af0704da33cf13e6bb01711677ccf1746f7c2dbc822385573ed1d1f55` |
| R | `b_projection_redesign` | `8f5357f4a57900a8009c9fc9c732b04ed84715adfface9aeae9d072a547cef2c` |
| T | `c_ticket` | `df348015164c68d626b79e9c9a4625a3f7163377b2ad6783baa5f42ff27ec388` |
| P | `d_published_contract` | `0ad42022c041cbd4cc6dd555ae605cafd4e49ffaa6724baeeff142388961ed54` |
| C | `e_configuration_domain` | `5c5cdc7430571e055d7a6b1ddf281c83ed62f6f224872a158dd4ff775d07fdf9` |
| S | `f_sealed_boundary` | `cb45d50017c290dd84bc9485b6e2b33a0259b27d73582d802fd347d8d47ef78a` |
| G | `g_greenfield` | `f7679319733257b582d62744483c263cbbcaaa4b366f408e014caa01169cea30` |
| H | `h_tradeoff` | `06c138336064a80f8069feb9b6e41b92c5eb53623a07c0c1033033cd35f03d59` |
| N | `i_new_snapshot` | `eef6b621a5b74e23613d3c67679470744651a192546eb63fa03986865b275bff` |

Digests use GNU tar streams rooted at `.`, sorted names, timestamp zero,
numeric owner/group zero, and preserved contents/modes. Every opaque runtime
copy was verified against its mode digest before the first run.

## Frozen cells

Each row has three fresh treatment replicates followed by three fresh
core-ablation replicates.

| Mode | Treatment targets | Core-ablation targets |
|---|---|---|
| A | `r001`, `r002`, `r003` | `r004`, `r005`, `r006` |
| R | `r007`, `r008`, `r009` | `r010`, `r011`, `r012` |
| T | `r013`, `r014`, `r015` | `r016`, `r017`, `r018` |
| P | `r019`, `r020`, `r021` | `r022`, `r023`, `r024` |
| C | `r025`, `r026`, `r027` | `r028`, `r029`, `r030` |
| S | `r031`, `r032`, `r033` | `r034`, `r035`, `r036` |
| G | `r037`, `r038`, `r039` | `r040`, `r041`, `r042` |
| H | `r043`, `r044`, `r045` | `r046`, `r047`, `r048` |
| N | `r049`, `r050`, `r051` | `r052`, `r053`, `r054` |

Randomized launch order, fixed before the first run:

```text
r051 r053 r007 r015 r008 r025 r039 r046 r024 r011 r023 r030 r034 r038
r043 r016 r052 r033 r045 r005 r021 r054 r048 r029 r019 r003 r037 r002
r047 r044 r018 r004 r031 r040 r050 r036 r022 r001 r026 r032 r028 r017
r006 r009 r041 r012 r020 r010 r013 r014 r035 r049 r042 r027
```

## Frozen evaluated-agent prompt

The two conditions receive byte-identical text except the resolved opaque
`[PACKAGE]` path; every cell receives its own resolved opaque `[TARGET]` and
`[OUTPUT]` paths.

```text
Act as a fresh source-review and design agent. Read the complete unsafe Rust
skill package rooted at [PACKAGE]/SKILL.md and every reference it directs you
to for this task, then follow it. Read REQUEST.md and the other files in
[TARGET], and complete exactly the requested review/design work.

Inspect only [TARGET], [PACKAGE], and exact versioned official Rust Reference
or standard-library documentation needed to verify claims. Do not inspect
sibling directories, another package or target, the enclosing repository,
version-control history, evaluator material, or prior reports. Do not modify,
build, test, macro-expand by execution, or otherwise execute the target. Do not
spawn helper agents.

Write the report to [OUTPUT] using apply_patch, then return the same report in
your final response. Keep the report focused and no longer than 1,400 words.
This is a focused review/design report, not a persistent whole-crate audit;
provide the equivalent proof material compactly.
```

No substantive steering is permitted. A neutral instruction to finish within
the current source-only scope is permitted and must be recorded.

### Invalidated uncapped warm-up

Before the word-limit clarification above was frozen, `r051` treatment and
`r053` core-ablation warm-ups ran with the same prompt minus its final two
sentences. Each expanded the 23-line target into a persistent-audit-scale
report and took roughly ten minutes. They were invalidated before scoring; no
semantic result motivated any change. Their raw outputs are preserved as
procedural evidence but are excluded from every score and gate. Both cells are
rerun fresh under the exact prompt above, and every other valid cell uses that
prompt from its first attempt.

## Isolation and reproducibility limits

Fresh collaboration agents use `fork_turns="none"`, but share a host
filesystem. Path restrictions are procedural rather than a hardened mount.
The collaboration API exposes neither a fixed seed nor a precise hosted model
identity. A pinned offline Rust-documentation mirror is unavailable. These
limitations make the suite exploratory even if all semantic gates pass.

## Run ledger

Raw reports will be copied byte-for-byte into `reports/rNNN.md` only after all
evaluated runs finish. Agent identity, report digest, deviations, blind score,
and adjudication will then be appended without changing the frozen material
above.

## Collection result

All 54 valid cells completed. Their byte-for-byte reports are in
[`reports/`](reports/); the deterministic report-tree digest is
`5e4adb0ccddb368282c95116278b980b0b1fc859f50116310e440f79a18fb649`.
Reports contain 527–907 words (mean 728.65; total 39,347), so every report
satisfied the frozen 1,400-word cap.

Every valid cell received the same target-neutral reminder after approximately
two minutes: “Complete now within the frozen word limit using only material
already inspected; do not widen scope.” A few slow cells received a semantically
equivalent second request to stop lookup and write from material already
inspected. No finding, contract interpretation, candidate, verdict, or expected
result was supplied.

One `r035` core-ablation agent reported that its first command ignored the
requested temporary working directory and a follow-up `find .` enumerated
enclosing-workspace filenames. It stopped immediately, opened no sibling file,
and used none of the listing. This procedural-isolation deviation is retained
and the report remains valid; the physical-isolation limitation was already
preregistered.

The invalid uncapped warm-up report digests are:

- `r051`: `81380cef54b5d9ba7c202478e9df4db7c1b05e004f313f8a98f2930e84a5e267`
- `r053`: `d54f0e77500ad740f2751f56d73e5e08afa316a268d6d8a6810e9c135f45abc5`

They remain excluded from scoring.

## Blind-scoring map

Before scoring, each mode's reports were randomly copied under labels A–F.
Scorers receive one mode, its exact atoms, and these labels; they receive no
condition identity, source, skill, sibling mode, or map below.

| Mode | A | B | C | D | E | F |
|---|---|---|---|---|---|---|
| Acceptance | `r005` | `r004` | `r001` | `r003` | `r006` | `r002` |
| Projection | `r011` | `r008` | `r009` | `r010` | `r007` | `r012` |
| Ticket | `r017` | `r018` | `r013` | `r015` | `r016` | `r014` |
| Published | `r023` | `r024` | `r021` | `r020` | `r019` | `r022` |
| Configuration | `r029` | `r026` | `r030` | `r027` | `r025` | `r028` |
| Sealing | `r036` | `r034` | `r035` | `r032` | `r033` | `r031` |
| Greenfield | `r040` | `r042` | `r039` | `r041` | `r037` | `r038` |
| Tradeoff | `r047` | `r045` | `r046` | `r048` | `r043` | `r044` |
| New snapshot | `r051` | `r050` | `r049` | `r054` | `r052` | `r053` |

## Scoring and adjudication result

All nine anonymous mode bundles received blind atom-level scores. Raw score
files were preserved unchanged, then independent adjudicators reviewed rubric
granularity and the disputed Rust-1.70 pointer semantics. The resulting
score/adjudication tree is in [`blind-scores/`](blind-scores/) and has
deterministic digest
`a0772c8375ff573c6e571676b63411d2370b735c9a0a17cb431d94852b325240`.

The final condition-level analysis and preregistered gate disposition are in
[`result.md`](result.md). The treatment materially improved the
proposal/new-snapshot firewall but did not pass the complete gate set: two H
treatment reports incorrectly proved an unsound Rust-1.70 pointer loop, and
four treatment atoms fell below the required 2/3 rate after adjudication. No
skill/package file was changed during collection, scoring, or adjudication.
