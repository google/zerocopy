# Typeclass-Insulated `Layer 0` (`OpenCoreMIR`) and Automated Lean 4 Proof Repair (`anneal-proof-repair`)

## Summary

In the prior baseline (`compiler-upgrade-soundness-quarantine-and-proof-invalidation-bounds`),
factoring the Lean 4 compiler verification hierarchy into a 5-layer DAG
(`Layer0_TrustedCore` $\to$ `Layer1_Adapter` $\to$ `Layer2_RuleFamily_01..52`
$\to$ `Layer3_Target` $\to$ `Layer4_CrateTheorem`) bounded adapter, rule-family,
and target ABI perturbations (`P1`–`P3`) to `2.94%`–`4.41%` (`2`–`3 / 68`
modules). However, its `Boundaries` section identified a critical residual
bottleneck: because every `Layer 2` rule family imported a monolithic
`Layer0_TrustedCore.lean` defining a closed `inductive CoreStmt` and a concrete
`structure MachState`, adding a single ghost/runtime state field to `MachState`
or adding a new statement construct to `CoreStmt` invalidated **`100.0%` (`68 /
68`) of `.olean` modules**.

Mechanizing the **Four-Sublayer `OpenCoreMIR` Micro-Kernel Architecture** in
Lean `v4.34.1` ([`support/OpenLayer0.lean`](support/OpenLayer0.lean)) and
benchmarking `.olean` invalidation and diagnostic-driven proof repair across a
live 19-module (`70`-module scaled) Lean `v4.34.1` DAG
([`support/run_k7_perturbation_bench.py`](support/run_k7_perturbation_bench.py),
[`support/anneal_proof_repair.py`](support/anneal_proof_repair.py),
[`support/k7_invalidation_results.json`](support/k7_invalidation_results.json))
establishes three architectural results:

1. **Splitting `Layer 0` into `ValCore`, Lawful Typeclass `StateLenses`,
   Parametric `CoreStmt (Ext : Type)`, and `ConcreteInst` Eliminates `Layer 2`
   `.olean` Coupling:**
   - Instead of importing a concrete `MachState` record or closed `CoreStmt`
     inductive, `Layer2_RuleInterface.lean` and all 52 `Layer2_RuleFamily_*.lean`
     modules import only `Layer0a_ValCore` (`RegId`, `Addr`, `Val`),
     `Layer0b_StateLenses` (`[HasRegLens S]`, `[HasMemLens S]`,
     `[HasBorrowLens S]`, `[MemRegOrthogonal S]`), and `Layer0c_OpenStmt`
     (`CoreStmt (Ext : Type)` with parametric constructor `| extOp (op : Ext)`
     and `[SemanticsExt Ext S]`).
   - All optimization rule families—including algebraic rewrites
     (`rule_assign_add_zero_sound`, `rule_assign_sub_self_sound`), memory-frame
     rewrites (`rule_dead_store_overwrite_const_sound`,
     `rule_store_load_forward_const_sound`), and CFG sequence rewrites
     (`rule_seq_assoc_sound`, `rule_seq_skip_right_sound`)—are proven once
     polymorphically over `{Ext S : Type}`
     ([`support/OpenLayer0.lean:145-210`](support/OpenLayer0.lean#L145-L210),
     checked with `[propext, Quot.sound]` only).
2. **`35x` Reduction in `.olean` Module Invalidation on `MachState` (`P5`) and
   `CoreStmt Ext` (`P6`) Evolutions (`0 / 52` Rule Families Rebuilt):**
   - **Perturbation `P5` (adding `asyncDropEpoch : Nat` and `provenanceGen :
     UInt64` to `ConcreteMachState` in `Layer0d_ConcreteInst.lean`):** Whereas
     `X10`'s monolithic `Layer0_TrustedCore` invalidated `17 / 17` (`100.0%`)
     prototype modules and `68 / 68` (`100.0%`, including all `52 / 52` rule
     families) scaled modules, `OpenCoreMIR` rebuilds only
     `Layer0d_ConcreteInst.lean` and `Layer4_CrateTheorem.lean`—**`2 / 19`
     (`10.53%`) prototype modules and `2 / 70` (`2.86%`) scaled compiler
     modules, with `0 / 52` (`0.0%`) rule-family `.olean` files rebuilt** in
     **`785.16 ms`** (vs. `7,410.27 ms` cold build).
   - **Perturbation `P6` (adding `asyncDropGlue (slot : Nat)` and
     `coroutineYield (bb : Nat)` to `ConcreteExt` in
     `Layer0d_ConcreteInst.lean`):** Because `CoreStmt (Ext : Type)` is
     polymorphic in `Ext`, all `52 / 52` rule families remain 100% `.olean`-valid
     (**`0 / 52` rebuilt**), rebuilding only `2 / 70` (`2.86%`) scaled modules
     in **`768.12 ms`**.
3. **Zero-Touch Automated Proof Repair (`anneal_proof_repair.py`) for
   Non-Insulated Cross-Cutting Interface Migrations (`P7`):**
   - When a genuine cross-cutting migration modifies `Layer2_RuleInterface.lean`
     directly—such as **Perturbation `P7`**, which adds a mandatory
     `quarantineTag : UInt16` field to `structure VerifiedOptRule` and triggers
     `Fields missing: \`quarantineTag\`` errors across all rule-family
     modules—`anneal_proof_repair.py` parses `lean --json` diagnostics,
     synthesizes the deterministic field binding `quarantineTag := 0`, patches
     all `8 / 8` (`100.0%`) broken rule-family modules with **`0` manual edits**
     in `~580 ms`/module, and restores a clean `0`-error, `0`-`sorryAx` build.

## Applicability

This report applies to `Lean 4 v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`), `rustc 1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`), `rustc 1.100.0`
(`0ef1bc386059596dada8fb65b50425aab2ea637a`), and Anneal
(`joshlf/anneal@d4ca2c861f664f200b69cdced9f6af38b5b1175a`) when structuring the
`Layer 0`–`Layer 4` `.olean` module graph and maintaining `Layer 2` rule-family
proofs across Rust edition and MIR evolutions.

It extends three corpus reports:
- `compiler-upgrade-soundness-quarantine-and-proof-invalidation-bounds`
- `lean-environment-identity-imports-and-trust-admissions`
- `compcert-sel4-everest-pass-composition-and-proof-maintenance`

Created: 2026-11-14 · Updated: 2026-11-14

## Findings

### 1. Lean `v4.34.1` Mechanization of `OpenCoreMIR` Lenses and Polymorphic Rule Families

Basis: source + execution

In [`support/OpenLayer0.lean`](support/OpenLayer0.lean), state access is
factored through `[HasRegLens S]`, `[HasMemLens S]`, `[HasBorrowLens S]`, and
`[MemRegOrthogonal S]`, while statement syntax is parameterized by `(Ext : Type)`
with `[SemanticsExt Ext S]`. All eight theorems verify in Lean `v4.34.1` with
zero `sorryAx` and zero `Lean.ofReduceBool`:

| Theorem Name | Lines | Axiom Footprint | Verified Contract |
| :--- | :---: | :---: | :--- |
| `rule_assign_add_zero_sound` | `145-151` | `[propext, Quot.sound]` | Polymorphic register identity `dst := e + 0 ~> dst := e` over any `{Ext S : Type}`. |
| `rule_assign_sub_self_sound` | `154-160` | `[propext, Quot.sound]` | Polymorphic self-cancellation `dst := e - e ~> dst := 0` over any `{Ext S : Type}`. |
| `rule_dead_store_overwrite_const_sound` | `164-171` | `[propext, Quot.sound]` | Polymorphic dead-store elimination `store a e1; store a v2 ~> store a v2` using only `HasMemLens.writeMem_overwrite`. |
| `rule_store_load_forward_const_sound` | `175-182` | `[propext, Quot.sound]` | Polymorphic store-to-load forwarding `store a v; dst := load a ~> store a v; dst := v` using `HasMemLens` + `MemRegOrthogonal`. |
| `rule_seq_assoc_sound` | `186-194` | `[propext, Quot.sound]` | Polymorphic sequence associativity `(s1; s2); s3 ~> s1; (s2; s3)` across arbitrary `.extOp op` statements. |
| `rule_seq_skip_right_sound` | `197-204` | `[propext, Quot.sound]` | Polymorphic trailing `skip` elimination `s; skip ~> s`. |
| `p5_p6_Specialized_store_load_forward` | `297-302` | `[propext, Quot.sound]` | 1-line zero-rebuild specialization of `rule_store_load_forward_const_sound` to `ConcreteMachStateV2` (`P5`) and `ConcreteExtV2` (`P6`). |
| `p5_p6_Specialized_seq_assoc_with_asyncDrop` | `304-309` | `[propext, Quot.sound]` | 1-line specialization of `rule_seq_assoc_sound` across `.extOp (.asyncDropGlue slot)` on `ConcreteMachStateV2`. |

### 2. Multi-Module `.olean` Invalidation & Automated Proof-Repair Benchmark (`P5`–`P7`)

Basis: execution + derived

Table 1 compares `X10`'s monolithic `Layer0_TrustedCore` DAG against `K7_`'s
`OpenCoreMIR` micro-kernel DAG across Perturbations `P5`, `P6`, and `P7`
([`support/run_k7_perturbation_bench.py`](support/run_k7_perturbation_bench.py),
[`support/k7_invalidation_results.json`](support/k7_invalidation_results.json)):

| Perturbation Scenario | `X10` Monolithic `Layer0` Rebuilt (Prototype / Scaled) | `K7_` `OpenCoreMIR` Rebuilt (Prototype `19` Mods) | `K7_` `OpenCoreMIR` Rebuilt (Scaled `70` Mods) | `Layer 2` Rule Families Rebuilt (`X10` vs. `K7_`) | `K7_` Incremental Rebuild / Repair Wall Time |
| :--- | :---: | :---: | :---: | :---: | :---: |
| **`P5`: Add `asyncDropEpoch` & `provenanceGen` to `ConcreteMachState`** | `17 / 17` (`100.0%`) / `68 / 68` (`100.0%`) | **`2 / 19` (`10.53%`)** (`Layer0d`, `Layer4`) | **`2 / 70` (`2.86%`)** | `52 / 52` $\to$ **`0 / 52` (`0.0%`)** | **`785.16 ms`** (vs. `7,410.27 ms` cold) |
| **`P6`: Add `asyncDropGlue` & `coroutineYield` to `ConcreteExt`** | `17 / 17` (`100.0%`) / `68 / 68` (`100.0%`) | **`2 / 19` (`10.53%`)** (`Layer0d`, `Layer4`) | **`2 / 70` (`2.86%`)** | `52 / 52` $\to$ **`0 / 52` (`0.0%`)** | **`768.12 ms`** (`9.65x` speedup over cold) |
| **`P7`: Add mandatory `quarantineTag : UInt16` to `VerifiedOptRule`** | `10 / 17` (`58.8%`) with `8` manual file edits | `11 / 19` (`57.89%`) with **`0` manual edits** (`8 / 8` auto-repaired by `anneal_proof_repair.py`) | `55 / 70` (`78.57%`) with **`0` manual edits** (`52 / 52` auto-repaired) | `52 / 52` auto-patched (`0` human LOC) | **`579 ms`/module** (`8,908.05 ms` total check + patch + `.olean` build) |

## Boundaries

1. **Semantics-Altering Changes to Core Algebraic Value Operations (`Layer0a_ValCore` / `Layer0c_OpenStmt`):**
   - If a change alters the mathematical evaluation of `CoreExpr.add` itself or
     modifies the lens laws in `HasRegLens` / `HasMemLens` (`Layer0b_StateLenses`),
     `Layer0b` or `Layer0c` changes hash and rightly triggers re-verification of
     `Layer 2` rule families (`100%` soundness check). `OpenCoreMIR` insulates
     `Layer 2` specifically against orthogonal state-component extensions (`P5`)
     and statement-constructor extensions (`P6`).
2. **Non-Defaultable Theorem-Obligation Fields in `P7`:**
   - `anneal_proof_repair.py` automatically synthesizes metadata, tag, and
     trivial/canonical proof fields (`rfl`, `decide`, `simp`). When a new field
     in `VerifiedOptRule` requires a non-trivial semantic proof obligation that
     cannot be discharged by `RuleSynthV2` tactics, `anneal_proof_repair.py`
     quarantines that rule family via `X10`'s Soundness Quarantine (`quarantineTag`)
     rather than inserting `sorry`.

## Evidence

1. **Lean `v4.34.1` Mechanization (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`):**
   - [`support/OpenLayer0.lean`](support/OpenLayer0.lean): `HasRegLens`,
     `HasMemLens`, `HasBorrowLens`, `MemRegOrthogonal`, `CoreStmt (Ext : Type)`,
     `SemanticsExt`, polymorphic `Layer 2` theorems, and `ConcreteMachStateV2` /
     `ConcreteExtV2` specializations (zero `sorryAx`, zero `Lean.ofReduceBool`).
2. **Automated Lean 4 Proof-Repair Tool & Live 19-Module Perturbation Suite:**
   - [`support/anneal_proof_repair.py`](support/anneal_proof_repair.py)
   - [`support/run_k7_perturbation_bench.py`](support/run_k7_perturbation_bench.py)
   - [`support/k7_invalidation_results.json`](support/k7_invalidation_results.json)

## Revalidation

```bash
anneal-lean-run --mode file --concurrency 4 -- lean \
  reports/typeclass-insulated-layer0-coremir-and-automated-lean-proof-repair/support/OpenLayer0.lean
python3 reports/typeclass-insulated-layer0-coremir-and-automated-lean-proof-repair/support/run_k7_perturbation_bench.py \
  --out /tmp/k7_invalidation_results.json
```
