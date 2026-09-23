# 2026-07-31 Unsafe Rust V2 Forward Evaluation Manifest

> **Evaluator-only material**

## Frozen preregistration

This section, the packages, fixtures, prompt, oracle, schedule, conditions, and
gates were frozen before the first evaluated report. No target may be modified,
built, tested, macro-expanded by execution, or otherwise executed.

The experiment contains ten modes, three conditions, and five fresh replicates
per cell: 150 reports. V2 versus V1 is the primary comparison. The V1 core
ablation is a secondary historical bridge and does not isolate V2's changes.

## Frozen package identities

| Condition | Package tree digest | `SKILL.md` digest | Opaque runtime label |
|---|---|---|---|
| V2 | `40b4171cc9daf7e51ba032aef52157a85a49c4c12cea8696deadb948e0867897` | `a0a75ef8a14497aa78b50b459981097ee99605c57fec95c637cf59aaa20fe766` | `q7m2` |
| V1 | `d97b9ace50109216614fbb7c975ac9c97508bfa928381d247869699593a2bcdd` | `2b063ad7d8c6a3f5051294e3c9ed49c8850397645b46772cd40ec6ae7136531e` | `b4x9` |
| V1 core ablation | `7ae4d42abd086720ed97bf1ef8b22f66b1d0ed33a0a5834b17eebfdc245c4d52` | `c2f07d263ce89d758985d6ff388ca344e038c1db111f2298cc5ddef051697595` | `n8k3` |

All packages passed the skill static validator. The V2 package received a
separate holistic freeze review after the evaluator failures were translated
into three general rules. No package file may change during collection,
scoring, or adjudication.

## Frozen fixture identities

| Mode | Source directory | Tree digest | Opaque runtime label |
|---|---|---|---|
| U | `fixtures/v2-forward/u_behavior` | `ee28003a984072cd3beebbd7f9549f3adbf087b7cd901f7fec889cd100ce8f3a` | `m2q8` |
| D | `fixtures/v2-forward/d_support` | `8196405f5bf3b110bfae84ef5904441e8a5726de338aa8be8d1bf49936a2877a` | `v7c4` |
| V | `fixtures/v2-forward/v_versions` | `636cefc08d1ece6183a208e47080e76f2669ef95c251586b8dc2bb00144cee22` | `h5p9` |
| I | `fixtures/v2-forward/i_producer` | `e213794c96e0fe442fc85747f2851c2da0da548dc031731e2c11b11e43022a1f` | `k3r6` |
| T | `fixtures/abstraction-design-v1/c_ticket` | `df348015164c68d626b79e9c9a4625a3f7163377b2ad6783baa5f42ff27ec388` | `f8w1` |
| C | `fixtures/abstraction-design-v1/e_configuration_domain` | `5c5cdc7430571e055d7a6b1ddf281c83ed62f6f224872a158dd4ff775d07fdf9` | `z4n7` |
| H | `fixtures/abstraction-design-v1/h_tradeoff` | `06c138336064a80f8069feb9b6e41b92c5eb53623a07c0c1033033cd35f03d59` | `a6d2` |
| A | `fixtures/abstraction-design-v1/a_acceptance` | `f3564d5af0704da33cf13e6bb01711677ccf1746f7c2dbc822385573ed1d1f55` | `y9t5` |
| P | `fixtures/abstraction-design-v1/d_published_contract` | `0ad42022c041cbd4cc6dd555ae605cafd4e49ffaa6724baeeff142388961ed54` | `c3g8` |
| N | `fixtures/abstraction-design-v1/i_new_snapshot` | `eef6b621a5b74e23613d3c67679470744651a192546eb63fa03986865b275bff` | `p1j4` |

The legacy fixture directories are byte-for-byte unchanged. Every opaque copy
was verified against its source digest before collection. The semantic atoms,
hard errors, authority review, and release gates are frozen in
[`../../v2-forward-oracle.md`](../../v2-forward-oracle.md).

## Frozen evaluated-agent prompt

Each cell receives byte-identical text except the resolved opaque `[PACKAGE]`,
`[TARGET]`, and unique empty `[OUTPUT]` paths:

```text
Act as a fresh source-review agent. Read the complete unsafe Rust skill package
rooted at [PACKAGE]/SKILL.md and every reference it directs you to for this
task, then follow it. Read REQUEST.md and every other file in [TARGET], and
complete exactly the requested review or design work.

Inspect only [TARGET], [PACKAGE], and exact versioned official Rust Reference
or standard-library documentation needed to verify claims. Do not inspect
sibling directories, another package or target, the enclosing repository,
version-control history, evaluator material, or prior reports. Do not modify,
build, test, macro-expand by execution, or otherwise execute the target. Do not
spawn helper agents.

Write the report to [OUTPUT]/report.md using apply_patch, then return the same
report in your final response. Keep the report focused and no longer than 1,400
words. This is a focused source review, not a persistent whole-crate audit;
provide the equivalent proof material compactly.
```

No substantive steering is permitted. A single target-neutral reminder to
finish within the frozen word limit using already inspected material is
permitted and must be recorded.

## Frozen launch schedule

The following random order was fixed before collection. The final column is a
within-cell replicate identity, not a sampling seed.

```text
r001 P v2 5
r002 U v2 2
r003 P v1 3
r004 D v1 5
r005 I v1 4
r006 C v2 2
r007 N core 4
r008 C v2 3
r009 U v1 2
r010 C v1 5
r011 T v2 1
r012 U v2 3
r013 T v2 2
r014 D core 3
r015 V core 2
r016 P v1 1
r017 T core 2
r018 A v1 3
r019 A v2 4
r020 V core 4
r021 H v2 5
r022 H v1 4
r023 T v1 1
r024 P core 2
r025 T v1 3
r026 D v2 1
r027 P core 5
r028 V v2 4
r029 U v1 4
r030 N core 5
r031 T v1 4
r032 P v2 3
r033 V v2 2
r034 P core 4
r035 D core 1
r036 T v2 4
r037 I core 3
r038 N v1 1
r039 H v1 1
r040 U v1 5
r041 U v1 1
r042 I v1 5
r043 P core 1
r044 U core 1
r045 I core 4
r046 A core 2
r047 H core 2
r048 V v1 3
r049 H v2 4
r050 P v1 5
r051 I v2 5
r052 H core 5
r053 A v1 5
r054 P v2 2
r055 H v1 2
r056 A v2 2
r057 D v1 2
r058 D v2 2
r059 C core 4
r060 C v1 3
r061 A v2 1
r062 U core 4
r063 N v1 4
r064 N v2 4
r065 N v1 5
r066 V v1 2
r067 N v2 5
r068 T v1 5
r069 I v1 2
r070 A core 3
r071 T v1 2
r072 I v1 3
r073 D core 2
r074 D v1 3
r075 H v2 2
r076 P v2 1
r077 H v2 3
r078 C v2 4
r079 H core 3
r080 C core 1
r081 P core 3
r082 U core 3
r083 N core 1
r084 A v1 1
r085 A v2 5
r086 C core 5
r087 U v2 4
r088 T v2 5
r089 C v2 5
r090 U v2 1
r091 P v1 2
r092 N v2 1
r093 D core 5
r094 V v2 1
r095 N v1 2
r096 P v2 4
r097 V core 5
r098 I v2 1
r099 V v1 1
r100 U core 5
r101 V core 1
r102 D core 4
r103 C core 3
r104 I v2 2
r105 C v2 1
r106 H v1 3
r107 T v2 3
r108 N core 3
r109 C v1 4
r110 C v1 1
r111 H core 4
r112 I core 5
r113 N v2 3
r114 V core 3
r115 T core 1
r116 V v2 3
r117 P v1 4
r118 A core 4
r119 U v2 5
r120 N v2 2
r121 U core 2
r122 H core 1
r123 D v2 3
r124 D v2 5
r125 A v1 2
r126 A v2 3
r127 I core 1
r128 T core 3
r129 N v1 3
r130 V v1 5
r131 I v2 3
r132 H v2 1
r133 V v2 5
r134 I v1 1
r135 A core 1
r136 D v1 4
r137 T core 4
r138 C core 2
r139 H v1 5
r140 A v1 4
r141 D v1 1
r142 T core 5
r143 N core 2
r144 V v1 4
r145 I v2 4
r146 A core 5
r147 C v1 2
r148 I core 2
r149 D v2 4
r150 U v1 3
```

## Freshness, isolation, and scoring

Every report uses a new collaboration agent with `fork_turns="none"`; no agent
may see two cells. Agents share a host filesystem, so path isolation is
procedural rather than hardened. The runtime root is
`/tmp/unsafe-rust-v2-eval.9epWDK`; agents receive only their opaque package,
target, and empty output paths. The collaboration API exposes neither a fixed
sampling seed nor a precise hosted-model identity. These limitations make the
study exploratory even if every gate passes.

After all reports finish, copy them byte-for-byte into `reports/rNNN.md`, hash
the report tree, and randomize labels independently per mode. Two fresh blind
scorers per mode receive source, oracle, and anonymous reports, but no package
or condition identity. Resolve semantic disagreements before unblinding;
preserve raw scores and adjudications separately. Do not patch the frozen skill
or oracle after observing outputs.

## Collection ledger

Append only operational facts here after collection: agent identity, output
digest, deviations, reminders, invalid reruns, and aggregate artifact digests.
Do not alter the frozen material above.

## Completed collection, scoring, and adjudication

Collection produced all 150 valid reports. Two blind scores per mode were
preserved, all semantic disagreements were adjudicated before unblinding, and
the canonical matrices were then joined to the frozen condition schedule. The
preregistered V2 gate result is **FAIL**.

See [`operational-ledger.md`](operational-ledger.md) for collection/scoring
events, invalid-attempt handling, byte-for-byte preservation checks, and
artifact digests. See [`results.md`](results.md) for the unblinded per-mode
counts, condition deltas, exact failed cells, hard errors, and gate decisions.
