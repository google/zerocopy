<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Operational Semantics, Hoare/WP Verification Conditions, Custom Tactic Elaboration, and Property-Based Negative Canaries Across `sf-in-lean`, `cslib`, and `plausible`

## Summary

This report analyzes the operational semantics, Hoare and weakest-precondition
verification condition (VC) generators, mutable-reference store-typing models,
and custom tactic elaborators in `plclub/sf-in-lean` (commit `13e9425b4647` and
PR #449 `0f74845c92a1`), alongside the labeled transition system (LTS)
simulation hierarchy in `leanprover/cslib` (commit `f7ec4db9f911`) and the
property-based random testing and constrained-generation framework in
`leanprover-community/plausible` (`v4.34.0`, commit `118aa17ee846` and PR #56
`f48022651ffa`). Every architectural pattern is evaluated against Anneal's MIR
semantics, verification building blocks, and kernel trust boundary
(`joshlf/anneal` commits `f938c18db56c`, `ebac418ccf7c`, and `f6ec1fc98057`)
using two self-contained runnable Lean `v4.34.1` probes in `support/`.

Six technical findings govern how these mechanisms map to Anneal:

1. **Operational Semantics and Refinement (`HL/Slang.lean`, `HL/Imp.lean`,
   `HL/Equiv.lean`, `TS/Smallstep.lean`, `cslib` vs. Anneal MIR):** `sf-in-lean`
   and `cslib` formalize execution over unbounded syntax trees via relational
   big-step (`CEval : Com → State → State → Prop`) or small-step (`Step :
   Tm × Store → Tm × Store → Prop`, `LTS.Tr`) relations and symmetric
   observational equivalence (`cequiv c1 c2 := ∀ st st', CEval c1 st st' ↔
   CEval c2 st st'`). Anneal's MIR evaluator (`evalBlock`, `evalCall`,
   `evalBody` in `trusted/lean/Anneal/MirSemantics.lean`) is fuel-indexed and
   computational (`Option StepResult`), and its correctness contract is
   asymmetric undefined-behavior (UB) refinement (`StepResult.refines`,
   `Compiler.Verified`), where `none` (`OutOfFuel`) and `.unreachable`
   (`UndefinedBehavior`) are refined by any outcome. Symmetric `cequiv` holds
   only for total intra-CFG expression/statement rewrites
   (`optMirConstPropStmt`); all whole-body and interprocedural transformations
   must target asymmetric `StepResult.refines` (`PassPackage.sound`).
2. **Functional Induction (`fun_induction` / `fun_cases`) vs. Structural
   Induction on AST Passes (`optimizeAExp`, `optMirConstPropStmt`):** On an
   8-constructor recursive AST pass with wildcard fallthroughs (`optimizeAExp`),
   `symm; fun_induction optimizeAExp a <;> simp_all [AExp.eval]` reduces direct
   theorem DAG size by `91.1%` (`1,126` vs. `12,665` `Expr.numObjs` nodes) and
   marginal per-theorem kernel replay time by `66.1%` (`9,270 us` vs.
   `27,315 us`) relative to structural `induction`, while on a non-recursive
   4-level nested pattern match (`optMirConstPropStmt`), `fun_cases` reduces
   direct theorem DAG size by `77.2%` (`290` vs. `1,271` nodes). However,
   `fun_induction` and `fun_cases` pull the equation compiler's `.induct` /
   `.fun_cases` principle and `.match_N.splitter` theorem (`1,744`–`4,003`
   nodes) into the module closure (`21,381` vs. `24,660` total module-closure
   objects on a single theorem), amortizing after `K >= 2` theorems over the
   same function. Furthermore, recursive functions using overlapping wildcard
   match arms in Lean `v4.34.1` compile via well-founded recursion and emit an
   auxiliary `._unsafe_rec` constant in `.olean` stage 1, which
   `TrustedBoundary.lean` rejects inside `Anneal.*` (`trusted/lean/`) but
   permits in untrusted helper modules (`theory/`).
3. **Hoare Logic vs. Sparse Weakest-Precondition VC Generation (`HL/Hoare.lean`,
   `HL/Hoare2.lean`) and Transitive Axiom Closures of `omega`, `lia`, and
   `grind`:** `HL/Hoare2.lean`'s backward weakest-precondition generator
   (`SparseAnnotations.awp` + `verificationConditions`) eliminates intermediate
   assertions at sequential compositions (`seq`) and branches (`ite`), reducing
   proof-term DAG size by `3.2x` on a diamond CFG (`504` vs. `1,620` direct
   nodes) and `3.3x` on an 8-statement straight-line block (`2,535` vs. `8,379`
   direct nodes; `6.2x` faster marginal kernel replay). Crucially, discharging
   VCs via `omega`, `lia`, or `grind` introduces axioms outside
   `TrustedBoundary.lean`'s current two-axiom allowlist (`propext`,
   `Classical.choice`): `omega` on atomic `Nat` linear arithmetic
   (`omega_nat_add`, `omega_nat_sub`, `omega_nat_sub_fn`) depends on
   `#[propext, Quot.sound]` (via `Lean.Omega.combo_sat'` -> `funext` ->
   `Quot.sound`, `0` uses of `Classical.choice`), `omega` on a conjunction goal
   (`omega_nat_conj`) adds `Classical.choice` via `Classical.propDecidable`
   (`#[propext, Quot.sound, Classical.choice]`), and `lia` / `grind`
   unconditionally depend on all three standard axioms `#[propext, Quot.sound,
   Classical.choice]` (`1,388`–`2,673` reachable declarations).
4. **Mutable References and Store Typing (`TS/References.lean`) vs. Anneal's
   Fuel-Bounded Reference Invariants (`MirVal.satisfiesInv`):**
   `TS/References.lean` models mutable heap cells (`Store := List Tm`) via an
   extrinsic store typing context (`StoreTy := List Ty`) and monotonic extension
   (`Extends δ' δ := δ.IsPrefixOf δ'`). Because typing a location
   (`HasType.loc`) inspects `δ[l]? = some τ` without re-traversing `ρ[l]`,
   `STLCRef` proves type preservation for cyclic stores
   (`cyclic_store_well_typed` in `514` direct DAG nodes) via `store_weakening`
   (`180` nodes), `store_well_typed_alloc` (`584` nodes), and
   `assign_pres_store_typing` (`543` nodes). Anneal's
   `MirVal.satisfiesInv : Nat → Memory → MirVal → TyInv → Prop` evaluates
   nested `.ref loc` invariants by structural recursion on `fuel : Nat`;
   combining `StoreTy` (`RegionEnv : Loc → Option TyInv`) with monotonic frame
   extension (`RegionEnv.Extends`) removes the `fuel` bound and supports cyclic
   or long-lived reference graphs while embedding cleanly into `SparseDCom` VCs.
5. **Custom Tactic Elaboration (`LF/CustomTactics.lean`), `sf-in-lean` Issue
   #447 / PR #449, and `TrustedBoundary.lean` Compatibility:** Built-in `cases h`
   fails on dependent inductive predicates whose index is a computed function
   application (`ShiftStep (evalShift raw) out`) because
   `Lean.Meta.Cases.unifyEqs` throws a hard error when `unifyEq?` returns
   `none`, whereas `LF/CustomTactics.lean`'s `inversion` wraps `unifyEq?` in
   `observing?` and retains unsolved index equations (`evalShift raw = 0`) as
   local hypotheses. We diagnose the two-part root cause of `sf-in-lean` Issue
   #447 and PR #449 (`0f74845c`)—right-aligned backwards `renameInaccessibles`
   binding user names to trailing `eq✝`/`heq✝` equations on `main`, versus
   pre-unification `givenNames` consumed by unified-away implicit constructor
   parameters on `NoStutter` in PR #449—and implement a complete fix
   (`inversion_fixed`, `renameInversionFieldsForward`) that renames surviving
   `.fvar` entries in `CasesSubgoal.fields` in forward order after
   `unifyCasesEqs`. We also provide the 14-pattern `TrustedBoundary.lean` +
   `foundation-lock.json` compatibility matrix and identify a 1-character AST
   indexing bug in `TrustedBoundary.lean:366` (`s[1].getArgs.isEmpty` vs.
   `s[1][0].getArgs.isEmpty`) that rejects bare `by decide`.
6. **Property-Based Negative Canaries and Pre-Proof Specification Falsification
   (`plausible` `v4.34.0` + `Chamelean` PR #56):** `plausible` (`v4.34.0`)
   provides an out-of-TCB executable falsification layer that catches semantic
   mutants (`MirBinOp.shlUnchecked` missing UB guard, `MirBinOp.subChecked`
   off-by-one underflow flag) and flawed candidate lemma specifications
   (`alignUpBitwise` missing power-of-two or `UInt8` overflow guards) in
   `0.2`–`1.6 ms` per property. When testing sparse memory-frame invariants
   (`ValidFrame`), `Plausible`'s `@[instance 2000] subtypeVarTestable`
   intercepts `∀ f : MirFrame, ValidFrame f → P f` and dispatches to a
   `Chamelean`-style constrained generator
   (`SampleableExt { f // ValidFrame f }`), finding boundary bugs in `0.27 ms`
   where naive rejection sampling (`decGuardTestable`) gives up after `500`
   discarded samples. Finally, we expose a critical sizing pitfall in
   `Plausible/Arbitrary.lean`: `UInt8`..`UInt64` and `USize` cap random
   generation at `min (← getSize) MAX` (where default `maxSize = 100`), making
   default `plausible` runs completely blind to fixed-width arithmetic overflow
   above `100` unless overridden by a boundary-weighted full-range generator
   (`FullRangeUInt8`).

## Applicability

These findings apply directly to three subsystems in `joshlf/anneal`:

- **Trusted MIR Semantics and Boundary Auditor (`trusted/lean/Anneal/`,
  `trusted/audit/TrustedBoundary.lean`,
  `trusted/cargo-anneal/foundation-lock.json`):** Governs how MIR evaluation
  (`evalStmt`, `evalTerminator`, `evalBlock`, `evalBody`) and refinement
  (`StepResult.refines`, `Compiler.Verified`) are structured, why recursive
  functions with wildcard match arms (`._unsafe_rec`) must remain outside
  `trusted/lean/`, why `TrustedBoundary.lean:15–16` must add `Quot.sound` to
  `allowedAxioms` (and `Init.Omega` / `Init.Grind` / `Init.RCases` to
  `foundation-lock.json`) before generated or manual proofs can use `omega`,
  `lia`, or `grind`, and how to fix `TrustedBoundary.lean:366` so bare
  `by decide` passes source-syntax preflight.
- **Verification Building Blocks and Proof Automation
  (`theory/Anneal/Verification/`):** Guides the evolution of
  `BuildingBlocks.lean` (`BB-1`..`BB-8`) from per-block manual stepping to a
  hybrid `SparseDCom` weakest-precondition VC generator for acyclic basic-block
  sub-DAGs combined with cut-point invariants at loop headers, plus the adoption
  of `fun_induction` / `fun_cases` for MIR pass soundness proofs
  (`optMirConstPropStmt`) and `StoreTy` (`RegionEnv`) + `Extends`
  (`store_weakening`) for mutable-reference invariant preservation.
- **Negative-Canary and Specification-Falsification Test Suite (`tests/` and
  `theory/` development workflows):** Establishes how `plausible` (`v4.34.0`)
  and `Chamelean`-style `SampleableExt { x // P x }` generators can falsify
  semantic mutants (Issue #228 / PR #82) and candidate `theory/Anneal/`
  specifications before investing in Lean kernel proofs or full Cargo/Miri
  differential builds.

## Findings

### Finding 1: Operational Semantics, Program Equivalence (`HL/Slang.lean`, `HL/Imp.lean`, `HL/Equiv.lean`, `TS/Smallstep.lean`), and `leanprover/cslib` (`LTS`, `Simulation`) vs. Anneal's Fuel-Indexed MIR Semantics and Asymmetric Refinement (`StepResult.refines`)

Basis: `source + execution + derived` — `plclub/sf-in-lean` commit
`13e9425b4647` (`HL/Slang.lean:1–252`, `HL/Imp.lean:1–262`,
`HL/Equiv.lean:1–777`, `TS/Smallstep.lean:1–579`), `leanprover/cslib` commit
`f7ec4db9f911` (`Cslib/Foundations/Semantics/LTS/Basic.lean:1–230`,
`Simulation.lean:1–145`, `Bisimulation.lean:1–180`), `joshlf/anneal` commits
`f938c18db56c` and `ebac418ccf7c` (`trusted/lean/Anneal/MirSemantics.lean`,
`theory/Anneal/MirPassProofs.lean`), and
`support/ProbeHoareWpFunIndAndReferences.lean` (`HoareVCProbe`,
`FunInductionProbe`).

#### 1.1 Architectural Comparison Across Semantic Encodings

The three repositories represent operational semantics and behavioral
equivalence along three distinct axes:

| Dimension | `sf-in-lean` (`HL/Slang.lean`, `HL/Imp.lean`, `HL/Equiv.lean`, `TS/Smallstep.lean`) | `leanprover/cslib` (`LTS/Basic.lean`, `Simulation.lean`, `Bisimulation.lean`) | `joshlf/anneal` (`trusted/lean/Anneal/MirSemantics.lean`, `theory/Anneal/MirPassProofs.lean`) |
| :--- | :--- | :--- | :--- |
| **Program Representation** | Deeply embedded inductive ASTs (`Com`: `skip`, `assign`, `seq`, `ite`, `while`; `Tm`: lambda + store operations) | Abstract state type `State` with labeled transition relation `Tr : State → Label → State → Prop` | Deeply embedded CFG (`Body` with indexed `List BasicBlock`, `Stmt`, `Terminator`, `Rvalue`, `Operand`) |
| **Evaluation Mode** | Big-step inductive relation `CEval : Com → State → State → Prop` (`HL/Imp.lean:155–176`) and small-step `Step : (Tm × Store) → (Tm × Store) → Prop` (`TS/References.lean:243–296`) | Relational single-step `LTS.Tr s μ s'` and multi-step `LTS.MTr s μs s'` (trace-indexed transitive closure) | Fuel-indexed total evaluator (`evalStmt`, `evalTerminator`, `evalBlock`, `evalCall`, `evalBody : Nat → ... → Option StepResult`) |
| **Nontermination & Fuel** | Big-step `CEval` omits diverging runs (`while_true_nonterm`, `HL/Equiv.lean:226–242`); small-step uses reflexive-transitive closure `Multi Step` (`TS/Smallstep.lean:180–190`) | Coinductive/relational infinite traces and divergence predicates (`LTS.Diverges`) | Explicit fuel exhaustion `none` (`OutOfFuel`), distinct from `.returned v`, `.diverged` (unwind/abort), and `.unreachable` (`UndefinedBehavior`) |
| **Equivalence / Refinement Contract** | Symmetric big-step equivalence: `cequiv c1 c2 := ∀ st st', CEval c1 st st' ↔ CEval c2 st st'` (`HL/Equiv.lean:45–47`) | Asymmetric `Simulation` (`∀ s₁ s₂ μ s₁', R s₁ s₂ → Tr s₁ μ s₁' → ∃ s₂', Tr s₂ μ s₂' ∧ R s₁' s₂'`) and symmetric `Bisimulation` | Asymmetric UB/fuel refinement: `StepResult.refines tgt src : Option StepResult → Option StepResult → Prop` (`PassPackage.sound`) |

#### 1.2 Why Symmetric `cequiv` Fails for Fuel-Indexed MIR Bodies and How Asymmetric Refinement Resolves It

In `HL/Equiv.lean:45–47`, two `Imp` commands `c1` and `c2` are behaviorally
equivalent when they relate identical initial and final states:

```lean
def cequiv (c1 c2 : Com) : Prop :=
  ∀ (st st' : State), (CEval c1 st st') ↔ (CEval c2 st st')
```

`HL/Equiv.lean` uses `cequiv` to verify recursive AST transformations such as
`fold_constants_com_sound` (`HL/Equiv.lean:511–545`) via congruence lemmas
(`CSeq_congruence`, `CIf_congruence`, `CWhile_congruence`). However, a
symmetric bi-implication `↔` cannot serve as the top-level correctness relation
for Anneal's MIR semantics (`trusted/lean/Anneal/MirSemantics.lean`) for two
fundamental reasons:

1. **Asymmetry of Undefined Behavior (`.unreachable`):** In Rust and MIR, a
   source program execution that triggers Undefined Behavior (represented by
   `some .unreachable` in `StepResult`, or `none` in partial statement helpers
   such as `evalMirStmt` in `support/ProbeHoareWpFunIndAndReferences.lean:642`)
   imposes no constraint on a transformed target program. An optimization pass
   such as dead-branch elimination or unchecked-shift folding may turn a source
   `.unreachable` execution into a defined value `some (.returned v)` without
   allowing the converse (`some (.returned v)` refined into
   `some .unreachable`).
2. **Asymmetry of Fuel Consumption (`none` / `OutOfFuel`):** Because `evalBody`
   decrements `fuel : Nat` across basic-block transitions and recursive calls,
   an optimization that eliminates basic blocks or inlines a call can succeed
   with `some (.returned v)` at fuel `N` where the unoptimized body returned
   `none` (`OutOfFuel`).

Anneal's `StepResult.refines : Option StepResult → Option StepResult → Prop`
(on branch `ebac418ccf7c`, `theory/Anneal/MirPassProofs.lean`) and `cslib`'s
asymmetric `Simulation` (`Cslib/Foundations/Semantics/LTS/Simulation.lean`)
capture this directionality directly:

- When the source evaluation yields `none` (`OutOfFuel`) or
  `some .unreachable` (`UndefinedBehavior`), `StepResult.refines tgt src` holds
  trivially (`True`) for any target outcome `tgt`.
- When the source evaluation yields a defined terminal outcome
  `some (.returned v)` or `some .diverged`, the target must produce the exact
  same defined outcome (`tgt = some (.returned v)` or `tgt = some .diverged`).

Symmetric equality (`evalAExp (optimizeAExp a) st = evalAExp a st` or
`evalMirStmt (optMirConstPropStmt s) env = evalMirStmt s env`) remains the
right local lemma shape for total, fuel-free expression and single-statement
rewrites within a basic block, which then lift into asymmetric
`StepResult.refines` at the basic-block and `Body` layers via monotonic
fuel-refinement congruence lemmas.

---

### Finding 2: Functional Induction (`symm; fun_induction <;> simp_all`) vs. Structural Induction vs. `fun_cases` on Compiler Passes (`optimizeAExp`, `optMirConstPropStmt`), Module-Closure Splitter Amortization, and Equation-Compiler `._unsafe_rec` Interaction with `TrustedBoundary.lean`

Basis: `source + execution + derived` — `plclub/sf-in-lean` commit
`13e9425b4647` (`HL/Slang.lean:51–228`, `HL/Equiv.lean:457–545`),
`joshlf/anneal` commits `f938c18db56c` and `ebac418ccf7c`
(`trusted/audit/TrustedBoundary.lean:178–202`,
`theory/Anneal/MirPassProofs.lean`), and
`support/ProbeHoareWpFunIndAndReferences.lean` (`FunInductionProbe`, lines
509–979).

#### 2.1 The Quadratic Wildcard Explosion in `HL/Slang.lean` vs. Lean 4's `fun_induction` and `fun_cases`

When an AST optimization pass matches specific multi-level constructor patterns
and falls through to a wildcard arm (`| _ => ...`), structural `induction` or
nested `cases` on the syntax tree must manually re-split every sub-expression
to prove that the wildcard arm does not overlap the specialized arms. In
`HL/Slang.lean`, `Slang` defines a 3-constructor expression AST (`num`, `id`,
`plus`) and a constant-folding pass `optimize_0plus`. Even for 3 constructors,
the manual `cases`-based proof `optimize_0plus_sound` (`HL/Slang.lean:77–139`)
requires 62 lines of nested `cases e1 <;> cases e2` splits, which
`HL/Slang.lean:216–228` replaces with a 5-line `fun_induction` script:

```lean
theorem optimize_0plus_sound'' (st : State) (e : Exp) :
    eval st (optimize_0plus e) = eval st e := by
  symm
  fun_induction optimize_0plus e <;> simp_all [eval]
```

Note the critical `symm` before `fun_induction`: in Lean 4, when an induction
hypothesis `ih1 : eval st e1 = eval st (optimize_0plus e1)` is oriented with
the unoptimized term on the left-hand side, `simp_all [eval]` rewrites
`eval st (optimize_0plus e1)` in the goal only when the goal is oriented so the
unfolded recursive call appears without creating a self-rewriting loop.

To quantify how this scales to realistic compiler ASTs, `FunInductionProbe` in
`support/ProbeHoareWpFunIndAndReferences.lean:509–979` benchmarks two passes:

1. **Recursive 8-Constructor Arithmetic Optimizer (`optimizeAExp`):** Over an
   8-constructor `AExp` (`num`, `var`, `add`, `sub`, `mul`, `shl`, `bitAnd`,
   `ite`) with three nested constant-folding match arms (`0 + e2`, `e1 + 0`,
   `1 * e2`, `e1 * 1`, `0 * e2`, `e1 * 0`, and wildcard fallthroughs),
   comparing:
   - `optimizeAExp_sound_structural`: manual structural `induction a` with
     exhaustive 8-way sub-case splits (`351` lines of proof script),
   - `optimizeAExp_sound_fun_ind_simp`: `symm; fun_induction optimizeAExp a <;>
     simp_all [AExp.eval]` (`4` lines of proof script), and
   - `optimizeAExp_sound_fun_ind_grind`: `fun_induction optimizeAExp a <;>
     grind [AExp.eval]` (`3` lines of proof script).
2. **Non-Recursive 4-Level MIR Constant-Propagation Pass
   (`optMirConstPropStmt`):** Modeling Anneal's `MirPassProofs.lean`
   (`ebac418ccf7c`), which inspects a statement
   `Stmt.assign dst (.binaryOp op (.const (.int c1)) (.const (.int c2)))` across
   4 nested ADT layers (`MirStmt` -> `MirRvalue` -> `MirOperand` -> `MirConst`)
   with a wildcard fallthrough `| s => s`, comparing:
   - `evalMirStmt_optMirConstPropStmt_structural`: 4-level nested `cases` with
     `rfl` on all 18 resulting branches (`42` lines), and
   - `evalMirStmt_optMirConstPropStmt_fun_cases`: `fun_cases optMirConstPropStmt
     s <;> rfl` (`2` lines).

#### 2.2 Direct Proof-Term Size vs. Module-Closure Splitter Overhead

Running `lean --run support/ProbeHoareWpFunIndAndReferences.lean` yields the
exact DAG object counts (`Expr.numObjs` after maximal DAG sharing), auxiliary
constant counts, and 10-iteration average `Lean.Kernel.Environment.replay`
times:

| Theorem | Proof Strategy | Script Lines | Direct Proof `Expr.numObjs` | Marginal Theorem Closure (`Expr.numObjs`) | Transitive Module Closure (`Expr.numObjs`) | Module Closure Decls | `.eq_N` / `.induct` / `.match_N` / `._proof_N` | Marginal Kernel Replay (`us`) | Full Closure Kernel Replay (`us`) | Transitive Axioms |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | :---: | ---: | ---: | :--- |
| `optimizeAExp_sound_structural` | Structural `induction` + 8-way `cases` | 351 | `12,665` | `12,665` | `24,660` | 30 | `11 / 0 / 4 / 0` | `27,315` | `64,675` | `#[propext]` |
| `optimizeAExp_sound_fun_ind_simp` | `symm; fun_induction <;> simp_all` | 4 | `1,126` | `1,126` | `21,381` | 40 | `11 / 1 / 7 / 0` | `9,270` | `64,840` | `#[propext]` |
| `optimizeAExp_sound_fun_ind_grind` | `fun_induction <;> grind` | 3 | `650` | `4,884` | `25,139` | 57 | `11 / 1 / 7 / 17` | `13,865` | `72,068` | `#[propext, Quot.sound, Classical.choice]` |
| `evalMirStmt_optMirConstPropStmt_structural` | 4-level nested `cases <;> rfl` | 42 | `1,271` | `1,271` | `4,581` | 15 | `1 / 0 / 2 / 0` | `3,005` | `6,466` | `#[]` |
| `evalMirStmt_optMirConstPropStmt_fun_cases` | `fun_cases <;> rfl` | 2 | `290` | `290` | `16,751` | 32 | `5 / 1 / 4 / 0` | `516` | `12,670` | `#[propext]` |

Three structural laws emerge from these measurements:

1. **Direct and Marginal Theorem Compression (`11.2x` on `optimizeAExp`, `4.4x`
   on `optMirConstPropStmt`):** `fun_induction` and `fun_cases` delegate
   wildcard disjointness to the equation compiler's pre-generated `.induct` /
   `.fun_cases` principle (`optimizeAExp.induct = 1,452` objects;
   `optMirConstPropStmt.fun_cases = 212` objects). Consequently, the theorem's
   own proof term shrinks from `12,665` to `1,126` DAG objects (`-91.1%`) on
   `optimizeAExp` and from `1,271` to `290` DAG objects (`-77.2%`) on
   `optMirConstPropStmt`, cutting marginal per-theorem kernel replay time by
   `66.1%` (`9,270 us` vs. `27,315 us`) and `82.8%` (`516 us` vs. `3,005 us`),
   respectively.
2. **Splitter Amortization Threshold ($K \ge 2$):** On a non-recursive
   function like `optMirConstPropStmt`, structural `cases <;> rfl` uses only
   `optMirConstPropStmt.eq_def` (`210` objects) and never references the
   equation compiler's `.match_1.splitter` (`1,744` objects) or `.match_1.eq_4`
   (`4,003` objects, which encodes the negated pattern assumptions of the
   wildcard branch). Calling `fun_cases` pulls `optMirConstPropStmt.fun_cases`,
   `.match_1.splitter`, and `.match_1.eq_1`..`.eq_4` (`12,170` objects of shared
   machinery) into the transitive module closure. Thus, for a single theorem
   ($K = 1$) over a non-recursive pass, nested `cases` has a smaller total
   module closure (`4,581` vs. `16,751` objects), whereas for $K \ge 2$
   theorems over the same pass—or even $K = 1$ theorem over a recursive
   multi-arm pass like `optimizeAExp` (`21,381` vs. `24,660` objects)—the
   shared `.induct`/`.fun_cases` principle amortizes and wins in both marginal
   and total DAG size.
3. **Equation-Compiler `._unsafe_rec` Emission and `TrustedBoundary.lean`:**
   In Lean `v4.34.1`, when a recursive function such as `optimizeAExp` (or
   `FullDCom.verificationConditions` / `SparseDCom.awp`) contains overlapping
   wildcard arms or mutual recursion that Lean compiles via well-founded
   recursion (`_unary`), the equation compiler also emits an auxiliary stage-1
   constant `optimizeAExp._unsafe_rec` (`ci.isUnsafe = true`). Even though the
   kernel-checked theorem `optimizeAExp_sound_fun_ind_simp` never references
   `optimizeAExp._unsafe_rec` in its proof DAG, `TrustedBoundary.lean:178–202`
   (`checkConstantInfo`) scans every constant whose name begins with `Anneal.`
   in `.olean` stage 1 and rejects any constant with `ci.isUnsafe` or
   `ci.isPartial`. Therefore:
   - Functions defined inside `trusted/lean/Anneal/` (`Anneal.*`) must use pure
     structural recursion (`fuel : Nat` or direct structural recursion without
     well-founded `_unary` compilation) so Lean never emits
     `Anneal.*._unsafe_rec`.
   - Complex recursive AST passes and VC generators should live outside
     `trusted/` in `theory/`, or if placed in `Anneal.*`, `TrustedBoundary.lean`
     must trace reachability from `Trusted.CrateTheorem` rather than rejecting
     unreferenced compiler-generated `._unsafe_rec` stage-1 siblings.

---

### Finding 3: Hoare Logic and Weakest-Precondition VC Generation (`HL/Hoare.lean`, `HL/Hoare2.lean` `FullDCom` vs. `SparseAnnotations.awp` vs. `BuildingBlocks.lean` `BB-1`..`BB-8`), and Exact Transitive Axiom Closures of `omega`, `lia`, and `grind` in Lean `v4.34.1`

Basis: `source + execution + derived` — `plclub/sf-in-lean` commit
`13e9425b4647` (`HL/Hoare.lean:1–777`, `HL/Hoare2.lean:1–660`), `joshlf/anneal`
commit `f938c18db56c` (`theory/Anneal/Verification/BuildingBlocks.lean`,
`trusted/audit/TrustedBoundary.lean:15–16`), and
`support/ProbeHoareWpFunIndAndReferences.lean` (`HoareVCProbe`, lines 53–507;
`AxiomClosureProbe`, lines 1267–1310).

#### 3.1 Comparing Three VC Architectures Across Diamond, 8-Statement Chain, and Loop Programs

`HL/Hoare.lean` and `HL/Hoare2.lean` implement three progressively more compact
verification architectures over `Imp`:

1. **Step-by-Step Hoare Rule Application (`HL/Hoare.lean:136–395`):** Every
   sequential composition (`hoare_seq`), conditional (`hoare_if`), loop
   (`hoare_while`), and assertion strengthening (`hoare_consequence_pre`,
   `hoare_consequence_post`) is applied explicitly in the proof script. This
   mirrors Anneal's current `BuildingBlocks.lean` (`BB-1`..`BB-8`, such as
   `evalBlock_step`, `evalBlock_goto`, `evalBlock_switchInt_true`, and
   `evalBlocks_while`), where proof authors step through basic blocks one
   statement and terminator at a time.
2. **Full Decorated Programs (`HL/Hoare2.lean:168–361`, `FullDCom`):** Every
   command node in `FullDCom` carries an explicit postcondition `Assertion`
   (`skip (Q)`, `assign x a (Q)`, `seq d1 d2`, `ite b P1 d1 P2 d2 (Q)`,
   `while b Pbody d (Qpost)`). A single meta-theorem `full_verification_correct`
   (`HL/Hoare2.lean:321–361`) proves `∀ P d, verificationConditions P d →
   HoareTriple P (erase d) (post d)`. However, for an $N$-statement basic block,
   `FullDCom` generates $N$ intermediate postcondition assertions and $N$
   implication VCs `(P_i → P_{i+1}[x ↦ a])`, growing both the AST and VC tree
   linearly with redundancy at every assignment.
3. **Sparse Annotations with Weakest Liberal Preconditions
   (`HL/Hoare2.lean:514–660`, `SparseAnnotations.SparseDCom` + `awp`):**
   `SparseDCom` removes all assertions from `skip`, `assign`, `seq`, and `ite`,
   requiring user annotations only at loop headers (`while b (Pinv : Assertion)
   (body : SparseDCom)`) and at the function's entry precondition and exit
   postcondition. The backward transformer `awp : SparseDCom → Assertion →
   Assertion` computes weakest preconditions syntactically:
   - `awp .skip Q = Q`
   - `awp (.assign x a) Q = Q[x ↦ a]` (state substitution `assn_sub`)
   - `awp (.seq d1 d2) Q = awp d1 (awp d2 Q)`
   - `awp (.ite b d1 d2) Q = fun st => (BExp.eval b st = true → awp d1 Q st) ∧
     (BExp.eval b st = false → awp d2 Q st)`
   - `awp (.while _ Pinv _) _ = Pinv`
   while `verificationConditions : Assertion → SparseDCom → Assertion → Prop`
   emits `True` on loop-free code (beyond the single entry implication
   `∀ st, P st → awp d Q st`) and emits only loop-body preservation and
   loop-exit obligations at `while` nodes.

`HoareVCProbe` in `support/ProbeHoareWpFunIndAndReferences.lean:53–507`
evaluates all three encodings on three benchmark programs:

- `diamondProg`: 2-branch conditional computing `z := (x + y) + 1` or
  `z := (x + x) + 1`, proved to satisfy `z = x + y + 1`.
- `chain8Prog`: 8-assignment straight-line basic block accumulating linear
  offsets into registers `r0`..`r3`, proved to satisfy `r3 = 2 * r0_init + 22`.
- `loopProg`: `while 0 < r0 do (r0 := r0 - 1; r2 := r2 + 1)`, proved to satisfy
  `r0 = 0 ∧ r2 = r0_init + r2_init` under invariant
  `r0 + r2 = r0_init + r2_init`.

| Benchmark Theorem | VC Architecture | Direct Proof `Expr.numObjs` | Marginal Closure (`Expr.numObjs`) | Transitive Module Closure (`Expr.numObjs`) | Marginal Kernel Replay (`us`) | Full Closure Kernel Replay (`us`) | Transitive Axioms |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | :--- |
| `diamond_verified_hoare_rules` | Step-by-step `hoare_seq` / `hoare_if` | `1,620` | `3,128` | `4,292` | `1,920` | `4,884` | `#[propext, Quot.sound]` |
| `diamond_verified_full_dcom` | `FullDCom` (`full_verification_correct`) | `1,608` | `3,116` | `10,331` | `4,009` | `16,581` | `#[propext, Quot.sound]` |
| `diamond_verified_sparse_awp` | `SparseDCom` (`awp` + `sparse_verification_correct`) | `504` | `504` | `6,881` | `789` | `10,137` | `#[propext]` |
| `chain8_verified_hoare_rules` | Step-by-step `hoare_seq` (8 steps) | `8,379` | `9,887` | `11,051` | `4,839` | `7,940` | `#[propext, Quot.sound]` |
| `chain8_verified_full_dcom` | `FullDCom` (8 intermediate postconditions) | `10,956` | `12,464` | `19,679` | `9,367` | `21,984` | `#[propext, Quot.sound]` |
| `chain8_verified_sparse_awp` | `SparseDCom` (`awp`, 1 entry VC) | `2,535` | `2,535` | `8,912` | `775` | `10,160` | `#[propext]` |
| `loop_verified_hoare_rules` | `hoare_while` + `omega` | `583` | `985` | `2,175` | `1,546` | `4,462` | `#[propext, Quot.sound]` |
| `loop_verified_sparse_awp` | `SparseDCom` (`awp`) + `omega` on conjunction VC | `539` | `985` | `7,362` | `2,068` | `11,431` | `#[propext, Quot.sound, Classical.choice]` |
| `loop_verified_sparse_awp_constructive` | `SparseDCom` (`awp`) + `And.intro` + `Nat` lemmas | `299` | `299` | `6,676` | `901` | `10,192` | `#[propext]` |

Key engineering conclusions for Anneal's `BuildingBlocks.lean`:

1. **Loop-Free Basic-Block Sub-DAGs Collapse to a Single `awp` Obligation:**
   On both `diamondProg` and `chain8Prog`, `SparseDCom.awp` reduces the entire
   control-flow graph to a single entry implication over substituted states,
   discharged by `omega` or `simp` without `Quot.sound` or `Classical.choice`
   when simplified via `State.update` (`#[propext]`). Direct proof-term size
   drops by `3.2x` (`504` vs. `1,620` nodes on `diamondProg`) and `3.3x`
   (`2,535` vs. `8,379` nodes on `chain8Prog`), while marginal kernel replay
   time drops by `6.2x` (`775 us` vs. `4,839 us`).
2. **Amortizing `sparse_verification_correct`:** Proving the generic soundness
   theorem `sparse_verification_correct` once in `theory/Anneal/Verification/`
   adds `~6,377` shared module-closure objects (`~9.3 ms` one-time kernel
   replay). Because `chain8_verified_hoare_rules` already consumes `11,051`
   module-closure objects on a single 8-statement block (`8,912` for
   `chain8_verified_sparse_awp`), `SparseDCom` wins on total module closure
   from the very first 8-statement function ($K = 1$) and saves `~7.3k` DAG
   nodes on every subsequent function.
3. **Fuel-Accounting Extension for Anneal MIR:** Unlike relational `CEval`,
   Anneal's `evalBlocks fuel body bbIdx frames` decrements `fuel` on every
   basic-block transition (`goto`, `switchInt`, `call`, `return`). A
   `SparseDCom`-style backward WP transformer for Anneal basic-block DAGs
   therefore threads a minimum fuel requirement `reqFuel : SparseDCom → Nat`:
   - `reqFuel (.block stmts) = 1`
   - `reqFuel (.seqGoto d1 d2) = reqFuel d1 + reqFuel d2`
   - `reqFuel (.switchInt cond dTrue dFalse) =`
     `1 + max (reqFuel dTrue) (reqFuel dFalse)`
   - `reqFuel (.loop k inv body) = k * (reqFuel body + 1) + 1`
   This preserves `SparseDCom`'s elimination of intermediate state assertions
   while guaranteeing
   `fuel >= reqFuel d → evalBlocks fuel ... = some (.returned v)`.

#### 3.2 Exact Transitive Axiom Closures of `omega`, `lia`, and `grind` vs. `TrustedBoundary.lean`

In `joshlf/anneal` commit `f938c18db56c`,
`trusted/audit/TrustedBoundary.lean:15–16` defines the kernel axiom allowlist
for `Trusted.CrateTheorem` as:

```lean
def allowedAxioms : Array Name :=
  #[`propext, `Classical.choice]
```

Wait: why did `diamond_verified_hoare_rules` and `loop_verified_hoare_rules`
pull in `Quot.sound`, and why did `loop_verified_sparse_awp` pull in
`Classical.choice` while `loop_verified_hoare_rules` did not?
`AxiomClosureProbe` in `support/ProbeHoareWpFunIndAndReferences.lean:1267–1310`
isolates 8 atomic arithmetic and propositional goals in Lean `v4.34.1` and
traces their exact transitive axiom closures and shortest dependency paths in
`Kernel.Environment`:

| Probe Theorem | Goal Shape | Tactic | Transitive Axioms | Reachable Kernel Decls | Shortest Path to `Classical.choice` | Shortest Path to `Quot.sound` |
| :--- | :--- | :--- | :--- | ---: | :--- | :--- |
| `omega_nat_add` | `a < 100 → b < 100 → a + b < 200` | `omega` | `#[propext, Quot.sound]` | `1,437` | *(none — `0` uses)* | `7` hops via `Lean.Omega.combo_sat'` $\to$ `Coeffs.combo_eq_smul_add_smul` $\to$ `IntList.combo_eq_smul_add_smul` $\to$ `funext` $\to$ `Quot.sound` |
| `omega_nat_sub` | `a + b = k ∧ 0 < a → (a - 1) + (b + 1) = k` | `omega` | `#[propext, Quot.sound]` | `1,467` | *(none — `0` uses)* | `7` hops via `Lean.Omega.combo_sat'` $\to \dots \to$ `funext` $\to$ `Quot.sound` |
| `omega_nat_sub_fn` | `st 0 + st 2 = st 3 → 0 < st 0 → (st 0 - 1) + (st 2 + 1) = st 3` | `omega` | `#[propext, Quot.sound]` | `1,467` | *(none — `0` uses)* | `7` hops via `Lean.Omega.combo_sat'` $\to \dots \to$ `funext` $\to$ `Quot.sound` |
| `omega_nat_conj` | `st 0 + st 2 = st 3 → st 0 = 0 → st 0 = 0 ∧ st 2 = st 3` | `omega` | `#[propext, Quot.sound, Classical.choice]` | `1,447` | `4` hops via `omega_nat_conj._proof_1` $\to$ `Classical.propDecidable` $\to$ `Classical.choice` | `7` hops via `Classical.propDecidable` $\to$ `Classical.em` $\to$ `funext` $\to$ `Quot.sound` |
| `lia_nat_add` | `a < 100 → b < 100 → a + b < 200` | `lia` | `#[propext, Quot.sound, Classical.choice]` | `1,388` | `5` hops via `lia_nat_add._proof_1` $\to$ `Classical.byContradiction` $\to$ `Classical.propDecidable` $\to$ `Classical.choice` | `5` hops via `Int.Internal.Linear.le_unsat` $\to$ `funext` $\to$ `Quot.sound` |
| `lia_nat_sub` | `a + b = k ∧ 0 < a → (a - 1) + (b + 1) = k` | `lia` | `#[propext, Quot.sound, Classical.choice]` | `2,083` | `5` hops via `Classical.byContradiction` $\to$ `Classical.propDecidable` $\to$ `Classical.choice` | `5` hops via `Int.Internal.Linear.le_unsat` $\to$ `funext` $\to$ `Quot.sound` |
| `grind_nat_add` | `a < 101 → b < 101 → a + b < 202` | `grind` | `#[propext, Quot.sound, Classical.choice]` | `1,388` | `5` hops via `Classical.byContradiction` $\to$ `Classical.propDecidable` $\to$ `Classical.choice` | `5` hops via `Int.Internal.Linear.le_unsat` $\to$ `funext` $\to$ `Quot.sound` |
| `grind_nat_sub` | `a + b = k ∧ 1 < a → (a - 2) + (b + 2) = k` | `grind` | `#[propext, Quot.sound, Classical.choice]` | `2,673` | `5` hops via `Classical.byContradiction` $\to$ `Classical.propDecidable` $\to$ `Classical.choice` | `6` hops via `Lean.Grind.CommRing.le_norm_expr` $\to$ `Expr.denote_toPoly` $\to$ `funext` $\to$ `Quot.sound` |

This resolves three subtle audit questions for Anneal:

1. **Every `omega`, `lia`, and `grind` Proof Depends on `Quot.sound`:** Even on
   pure `Nat` addition (`omega_nat_add`), `omega`'s linear certificate checker
   (`Lean.Omega.combo_sat'`) proves linear combination equality via `funext`,
   which in Lean 4 is derived from quotient soundness (`Quot.sound`). Similarly,
   `lia` and `grind` invoke `Int.Internal.Linear.le_unsat` or
   `Lean.Grind.CommRing.le_norm_expr`, both of which depend on `funext` $\to$
   `Quot.sound`. Because `TrustedBoundary.lean:15–16` currently allows only
   `#[`propext, `Classical.choice]`, any theorem proved by `omega`, `lia`, or
   `grind`—or by `funext`—will fail the boundary audit until `` `Quot.sound ``
   is added to `allowedAxioms` (as Lean's third standard mathematical axiom; see
   also `loop_verified_sparse_awp_constructive` in
   `support/ProbeHoareWpFunIndAndReferences.lean:489–505` for how explicit
   `Nat.sub_add_cancel` / `Nat.add_assoc` lemmas avoid both `Quot.sound` and
   `Classical.choice`).
2. **Why `omega` Uses `Classical.choice` Only on Non-Atomic Propositional
   Goals:** On atomic linear arithmetic goals (`omega_nat_add`, `omega_nat_sub`,
   `omega_nat_sub_fn`), `omega` uses `Decidable.byContradiction` over decidable
   `Int` inequalities and never touches `Classical.choice`. However, when
   `omega` is invoked directly on a conjunction goal `P ∧ Q` (`omega_nat_conj`,
   as emitted by `SparseDCom.verificationConditions` on `loopProg`), `omega`'s
   front-end clausifier splits `¬ (P ∧ Q)` using `Classical.propDecidable` $\to$
   `Classical.choice`. Splitting the conjunction via `refine ⟨?_, ?_⟩` before
   calling `omega` eliminates `Classical.choice` completely.
3. **Why `lia` and `grind` Always Use `Classical.choice`:** Both `lia` and
   `grind` wrap their core refutation goal in `Classical.byContradiction`
   (5 hops to `Classical.choice`), regardless of whether the goal is an atomic
   `Nat` inequality or a propositional compound.

---

### Finding 4: Mutable References, Store Typing (`StoreTy`), and Store Extension Monotonicity (`Extends`, `store_weakening`) in `TS/References.lean` (`STLCRef`) vs. Fuel-Bounded Reference Invariants in Anneal (`MirVal.satisfiesInv`)

Basis: `source + execution + derived` — `plclub/sf-in-lean` commit
`13e9425b4647` (`TS/References.lean:1–777`, `TS/Stlc.lean:1–320`,
`TS/StlcProp.lean:1–450`), `joshlf/anneal` commit `ebac418ccf7c`
(`theory/Anneal/MirValInv.lean`), and
`support/ProbeHoareWpFunIndAndReferences.lean` (`ReferencesProbe`, lines
981–1265).

#### 4.1 Why Naive Store-Indexed Typing Fails and How `StoreTy` + `Extends` Resolves It

When formalizing mutable references (`ref e`, `!e`, `e1 := e2`), a natural
first attempt is to parameterize value typing directly by the concrete runtime
store `ρ : Store := List Tm`, recursively checking that location `.loc l` has
type `.ref τ` whenever the stored value `ρ[l]` has type `τ`. As
`TS/References.lean:331–380` explains, this naive design fails for two reasons:

1. **Every Store Mutation Invalidates Existing Typing Derivations:** Writing to
   location `l'` (`ρ.set l' v`) changes the concrete store `ρ`, requiring every
   sub-term typing derivation in the program context to be rebuilt from scratch.
2. **Cyclic Reference Graphs Diverge:** If cell `0` contains a term referencing
   cell `1` and cell `1` contains a term referencing cell `0` (as in doubly
   linked lists, intrusive queues, or closures stored in mutable cells),
   re-typechecking `ρ[l]` at every `.loc l` lookup has no finite derivation
   without an artificial step-index fuel bound.

`TS/References.lean:383–762` resolves both problems via an extrinsic store
typing `StoreTy := List Ty` (`δ`) that assigns a fixed intended type `δ[l]?` to
each allocated cell `l : Nat`, decoupled from the cell's current runtime value:

1. **Constant-Time Location Lookup (`HasType.loc`):** `.loc l` has type `.ref τ`
   under `δ` whenever `δ[l]? = some τ`, without inspecting `ρ[l]`.
2. **Global Store Well-Typedness (`StoreWellTyped δ ρ`):** Holds when
   `δ.length = ρ.length` and every cell `l < ρ.length` satisfies
   `HasType δ ρ[l] δ[l]`.
3. **Monotonic Store Extension (`Extends δ' δ := δ.IsPrefixOf δ'`):** Because
   `STLCRef` stores are append-only on allocation (`ρ ++ [v]`) and
   type-invariant on mutation (`ρ.set l v`), `δ` only grows by appending new
   cell types (`δ ++ [τ]`).

`ReferencesProbe` in `support/ProbeHoareWpFunIndAndReferences.lean:981–1265`
mechanizes the complete `STLCRef` preservation chain and a 2-cell cyclic heap
witness (`cyclic_store_well_typed`, where cell `0` holds `!(loc 1); unit` and
cell `1` holds `!(loc 0); unit`):

| Theorem (`ReferencesProbe`) | Role in Store-Typing Architecture | Direct Proof `Expr.numObjs` | Marginal Closure (`Expr.numObjs`) | Transitive Module Closure (`Expr.numObjs`) | Marginal Kernel Replay (`us`) | Full Closure Kernel Replay (`us`) | Transitive Axioms |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | :--- |
| `store_weakening` | `Extends δ' δ → HasType δ t τ → HasType δ' t τ` | `180` | `180` | `2,243` | `1,303` | `6,464` | `#[propext]` |
| `store_well_typed_alloc` | Allocation `ρ ++ [v]` preserves `StoreWellTyped (δ ++ [τ])` | `584` | `584` | `3,389` | `1,375` | `8,389` | `#[propext]` |
| `assign_pres_store_typing` | In-place mutation `ρ.set l v` preserves `StoreWellTyped δ` | `543` | `543` | `3,336` | `825` | `7,682` | `#[propext]` |
| `preservation` | Full small-step type + store preservation across 9 `Step` rules | `6,114` | `6,114` | `17,746` | `13,734` | `40,101` | `#[propext]` |
| `cyclic_store_well_typed` | Finite well-typedness proof for 2-cell mutually referential store | `514` | `514` | `861` | `1,664` | `3,363` | `#[propext]` |

#### 4.2 Mapping `StoreTy` and `Extends` to Anneal's `MirVal.satisfiesInv`

In Anneal (`ebac418ccf7c`, `theory/Anneal/MirValInv.lean`), value invariants for
MIR references (`MirVal.ref loc`) are currently defined by recursion on a step
counter `fuel : Nat`:

```lean
def MirVal.satisfiesInv : Nat → Memory → MirVal → TyInv → Prop
  | 0, _, _, _ => False
  | fuel + 1, mem, .ref loc, .ref pointeeInv =>
      ∃ v, mem.lookup loc = some v ∧ MirVal.satisfiesInv fuel mem v pointeeInv
```

This `fuel`-indexed formulation forces every function call, loop iteration, and
dereference chain in a proof to decrement `fuel`, and cannot express cyclic
reference invariants at all. Adopting `TS/References.lean`'s `StoreTy` pattern
in `theory/Anneal/` replaces `fuel` with a region typing environment
`RegionEnv := Loc → Option TyInv` (`Δ`):

1. **Fuel-Free Value Invariant (`MirVal.satisfiesInv Δ v τ`):** For `.ref loc`
   and `.ref pointeeInv`, `MirVal.satisfiesInv Δ (.ref loc) (.ref pointeeInv)`
   Simply asserts `Δ loc = some pointeeInv` (zero `Memory` lookup, zero `fuel`
   parameter).
2. **Global Memory Well-Typedness (`Memory.WellTyped Δ mem`):** Asserts that for
   every `loc` and `inv` with `Δ loc = some inv`, there exists `v` such that
   `mem.lookup loc = some v ∧ MirVal.satisfiesInv Δ v inv`.
3. **Monotonic Allocation (`RegionEnv.Extends Δ' Δ`):** When a new stack slot or
   heap allocation is created at fresh location `loc`, `Δ' := Δ.insert loc inv`
   extends `Δ`. By the direct analogue of `store_weakening` (`180` DAG nodes),
   all existing local-variable invariants `MirVal.satisfiesInv Δ v τ` lift
   automatically to `Δ'` without re-inspecting `mem`, and in-place mutation of
   an existing `loc` with a value satisfying `Δ loc` preserves `Δ` identically
   (`assign_pres_store_typing`, `543` DAG nodes).

---

### Finding 5: Metaprogramming Architecture of `LF/CustomTactics.lean` (`inversion`, `apply ... at ...`), Two-Part Root Cause and Fix (`inversion_fixed`) for `sf-in-lean` Issue #447 / PR #449, and the 14-Pattern `TrustedBoundary.lean` + `foundation-lock.json` Tactic Compatibility Matrix

Basis: `source + execution + derived` — `plclub/sf-in-lean` commit
`13e9425b4647` (`LF/CustomTactics.lean:1–435`, `TS/AttributeDecls.lean:1–25`)
and PR #449 commit `0f74845c92a1`, `joshlf/anneal` commit `f938c18db56c`
(`trusted/audit/TrustedBoundary.lean:1–420`,
`trusted/cargo-anneal/foundation-lock.json`), and
`support/ProbeInversionBoundaryAndPlausible.lean` (`CustomTactics`,
`InversionProbe`, `BoundaryAuditProbe`, lines 52–875).

#### 5.1 Why Built-In `cases` Fails on Computed Index Expressions While `LF/CustomTactics.lean`'s `inversion` Succeeds

In Lean 4 (`Lean/Meta/Tactic/Cases.lean:160–277`), when `cases h` is invoked on
a hypothesis `h : I idx_1 ... idx_k` whose type is an indexed inductive family
with non-independent indices (`!hasIndepIndices ctx`), `MVarId.cases` executes:

1. `generalizeIndices goal h`: replaces each non-variable index `idx_i` with a
   fresh free variable `x_i` and introduces equality hypotheses `x_i = idx_i`
   plus `h ≍ h'`.
2. `inductionCasesOn`: eliminates `h'` into one `CasesSubgoal` per constructor.
3. `Lean.Meta.Cases.unifyCasesEqs`: calls `Lean.Meta.Cases.unifyEqs` to solve
   the index equations `ctor_idx_i = idx_i` in each constructor branch.

Crucially, `Lean.Meta.Cases.unifyEqs` calls `unifyEq?` and—if `unifyEq?` returns
`none` because one side is a non-constructor function application such as
`evalShift raw = 0`—**immediately throws a hard exception**:

```text
error: Dependent elimination failed: Failed to solve equation
  evalShift raw = 0
```

`LF/CustomTactics.lean:166–224` replaces `Lean.Meta.Cases.unifyEqs` with a
custom `Lean.Meta.unifyEqs`
(`support/ProbeInversionBoundaryAndPlausible.lean:183–194`) that wraps
`unifyEq?` in `observing?`:

```lean
let some { mvarId, subst, numNewEqs } ←
    Option.join <$> (observing? $ unifyEq? mvarId eq subst MVarId.acyclic caseName?)
  | unifyEqs eqs mvarId subst caseName?
```

When `unifyEq?` fails on `evalShift raw = 0`, `observing?` catches the failure,
leaves the unsolved index equation `heq : evalShift raw = 0` as a hypothesis in
the local context of the `zeroShift` subgoal, and continues unifying the
remaining equations (`out = x`). In `InversionProbe`
(`support/ProbeInversionBoundaryAndPlausible.lean:472–506`), `#guard_msgs`
verifies that built-in `cases h` fails on `ShiftStep (evalShift raw) out`,
whereas both `inversion +clear h` (`268` DAG nodes) and the
foundation-compatible idiom
`generalize hexp : evalShift raw = idx at h; cases h` (`313` DAG nodes)
succeed.

#### 5.2 Complete Two-Part Diagnosis and Fix (`inversion_fixed`) for `sf-in-lean` Issue #447 and PR #449 (`0f74845c`)

In `sf-in-lean` Issue #447 and open PR #449 (commit `0f74845c92a1`), users
reported that `inversion h with | ctor x y => ...` binds user-supplied variable
names to the wrong hypotheses or rejects `@ctor` syntax when constructors have
implicit parameters or unsolved index equations. By inspecting both `main`
(`13e9425b4647`) and PR #449 (`0f74845c92a1`), we identify two distinct bugs:

1. **Bug 1 on `sf-in-lean` `main` (`13e9425b4647`,
   `LF/CustomTactics.lean:245–272`):**
   - `evalInvAlt` matches only
     `` `(inductionAlt| | $tag:ident $vars* => $tactics) ``, rejecting explicit
     `@tag` patterns (`issue447_at_syntax_rejected` in
     `support/ProbeInversionBoundaryAndPlausible.lean:528–534`).
   - More importantly, `trySolveGoal` renames hypotheses by calling
     `Lean.Elab.Tactic.renameInaccessibles goal vars`. In Lean 4 core
     (`Lean/Elab/Tactic/RenameInaccessibles.lean`), `renameInaccessibles` walks
     `mvarDecl.lctx.decls.toList.reverse` **backwards from the end of the local
     context** and collects the **last** `vars.size` inaccessible hypotheses!
     When `inversion` leaves $k$ unsolved index/heterogeneous equations (`eq✝`,
     `heq✝`) at the end of `lctx` after the constructor fields (`f✝`, `hd✝`,
     `tl✝`), and a user writes `| cons a b =>` supplying fewer names than total
     inaccessibles, `renameInaccessibles` binds `a` and `b` to the **trailing
     equations** (`a : w ≍ IndexedWec.cons _ _ _`, `b : n + 1 = _`) instead of
     the first two constructor fields
     (`issue447_reverse_renaming_binds_trailing_eqs`, lines 539–547)!
2. **Bug 2 Introduced in PR #449 (`0f74845c92a1`):**
   - PR #449 attempted to fix Issue #447 by extracting `givenNames : Array
     AltVarNames` from the user's `inductionAlt` syntax and passing `givenNames`
     directly into `inductionCasesOn newGoal newTarget givenNames ctx`
     **before** `unifyCasesEqs` runs.
   - However, `inductionCasesOn` assigns user names to constructor fields
     **before index unification (`unifyCasesEqs`) eliminates fields determined
     by concrete indices**. On `NoStutter [3, 1, 1, 4]` where constructor
     `NoStutter.cons` has type `∀ {x y : Nat} {l : List Nat}, x ≠ y → NoStutter
     (y :: l) → NoStutter (x :: y :: l)`, the three implicit fields `{x y l}`
     are immediately unified with `3`, `1`, and `[1, 4]` and cleared by
     `unifyCasesEqs`. Passing `givenNames` to `inductionCasesOn` in `@cons` mode
     consumes the user's first three names on `{x, y, l}` before `unifyCasesEqs`
     deletes them from the context!

Our fix `inversion_fixed` (`renameInversionFieldsForward` in
`support/ProbeInversionBoundaryAndPlausible.lean:350–395`) solves both bugs:

- It runs **after** `unifyCasesEqs` and inspects `subgoal.fields`, where
  `unifyCasesEqs` has already applied `subst.apply`
  (`s.fields.map (subst.apply ·)`). Constructor fields that were unified with
  concrete terms (`3`, `1`, `[1, 4]`) are no longer `.fvar` expressions; only
  **surviving** constructor fields remain `.fvar`s in `subgoal.fields`.
- In default (`| tag vars* =>`) mode, it filters out surviving constructor
  fields whose constructor `BinderInfo` is non-explicit (`!bi.isExplicit`),
  while in explicit (`| @tag vars* =>`) mode it includes surviving implicit
  fields.
- Starting at the local-context index of the first surviving constructor field,
  it collects inaccessible hypotheses in **forward (left-to-right) order**,
  binding constructor fields first and trailing unsolved index equations
  afterward. Theorems `issue447_fixed_noStutter`,
  `issue447_fixed_indexedWec_forward_binding`, and
  `issue447_fixed_indexedWec_at_syntax` (lines 553–577) verify all three cases.

#### 5.3 The 14-Pattern `TrustedBoundary.lean` Preflight and `foundation-lock.json` Elaboration Matrix

Anneal enforces two orthogonal gates on Lean files:

1. **Source-Syntax Preflight (`trusted/audit/TrustedBoundary.lean`):** Applied
   only to files in the `Anneal.*` module hierarchy (`trusted/lean/`). It
   restricts top-level commands to `commandKinds`, restricts attributes to
   `allowedAttributeNames` (`simp`, `reducible`, `inline`, `specialize`), bans
   metaprogramming escape hatches (`by_elab`, `run_tac`, `eval_expr`) via
   `forbiddenSyntaxKinds`, and bans `decide +kernel` / `decide +native` via
   `inspectSyntax`.
2. **Import Closure Lock (`trusted/cargo-anneal/foundation-lock.json`):** Locks
   the transitive `.olean` module graph of `Anneal.Trusted` to 65 core `Init.*`
   modules rooted at `Init.NotationExtra` (which excludes `Init.Omega`,
   `Init.Grind`, and `Init.RCases`).

`BoundaryAuditProbe` (`support/ProbeInversionBoundaryAndPlausible.lean:625–874`)
tests 14 tactic and command snippets against both `TrustedBoundary.lean`'s
preflight parser and live elaboration under `Init.NotationExtra` vs.
`+Init.Omega/Grind/RCases`:

| # | Pattern / Tactic | `TrustedBoundary.lean` Preflight (Stock `f938c18db`) | `TrustedBoundary.lean` Preflight (With `s[1][0]` Fix) | Elaborates Under `Init.NotationExtra` (`foundation-lock.json`) | Elaborates Under `+Init.Omega/Grind/RCases` | Recommended Anneal Equivalent |
| :- | :--- | :---: | :---: | :---: | :---: | :--- |
| 1 | Custom `syntax` + `elab` (`inversion`, `apply ... at ...`) | **FAIL** (`unsupported command syntax`) | **FAIL** | PASS (if `Lean` imported) | PASS | Prohibited in `Anneal.*`; use `generalize + cases` or `replace h := f ... h` |
| 2 | Custom `macro` / `macro_rules` | **FAIL** (`unsupported command macro`) | **FAIL** | PASS | PASS | Prohibited in `Anneal.*`; expand macros in Rust generator or `theory/` |
| 3 | `register_label_attr` (`TS/AttributeDecls.lean`) | **FAIL** (`unexpected identifier`) | **FAIL** | **FAIL** (requires `Lean.LabelAttribute`) | **FAIL** | Pass explicit lemma lists: `apply_rules [lem1, lem2]` |
| 4 | Custom `@[SimpleArith]` attribute | **FAIL** (`unsupported attribute`) | **FAIL** | **FAIL** | **FAIL** | Use `@[simp]` or explicit lemma lists `[lem1, lem2]` |
| 5 | `by_elab` / `run_tac` inside `by ...` | **FAIL** (`forbidden syntax kind runTac`) | **FAIL** | **FAIL** | **FAIL** | Prohibited everywhere in Anneal |
| 6a | `native_decide` / `decide +kernel` inside `by ...` | **FAIL** (`forbidden decide configuration '+kernel'`) | **FAIL** | PASS | PASS | Prohibited (`Lean.ofReduceBool` / `Lean.trustCompiler`) |
| 6b | **Bare `by decide`** (no config flags) | **FAIL** (`forbidden decide configuration ''`) | **PASS** | **PASS** | **PASS** | Fix `TrustedBoundary.lean:366` (`s[1][0].getArgs.isEmpty`) |
| 7 | `cases` + `generalize` + `injections` + `subst_vars` | **PASS** | **PASS** | **PASS** | **PASS** | Direct drop-in replacement for `inversion` (`313` vs. `268` DAG nodes) |
| 8 | `apply_rules [lem1, lem2]` (explicit list) | **PASS** | **PASS** | **PASS** | **PASS** | Built into `Init.Tactics`; `30` DAG nodes on `EvenInd 8` |
| 9 | `solve_by_elim [lem1, lem2]` (explicit list) | **PASS** | **PASS** | **PASS** | **PASS** | Built into `Init.Tactics`; `30` DAG nodes on `EvenInd 8` |
| 10 | `fun_induction` / `fun_cases` inside `by ...` | **PASS** | **PASS** | **PASS** | **PASS** | Built into `Init.Tactics`; use in `theory/` (`#[propext]`) |
| 11 | `omega` inside `by ...` | **PASS** | **PASS** | **FAIL** (`Unknown constant Lean.Omega...`) | **PASS** | Add `Init.Omega` to imports + `` `Quot.sound `` to `allowedAxioms` |
| 12 | `lia` / `grind` inside `by ...` | **PASS** | **PASS** | **FAIL** (`Unknown constant Lean.Grind.ToInt`) | **PASS** | Add `Init.Grind` to imports + `` `Quot.sound `` to `allowedAxioms` |
| 13 | `rcases` / `obtain` inside `by ...` | **FAIL** (`unknown tactic` under `Init.NotationExtra` parser) | **FAIL** | **FAIL** | **PASS** | Use Lean 4 built-in `rcases`-free `cases` / `obtain`-free `have ⟨x, hx⟩ := h` or import `Init.RCases` |

**Diagnosis of the Bare `by decide` Bug in `TrustedBoundary.lean:366`
(Snippet 6b):** In `trusted/audit/TrustedBoundary.lean:364–367`, the auditor
checks whether `decide` or `decide!` was passed configuration flags (`+kernel`
or `+native`) by inspecting `s[1].getArgs.isEmpty`:

```lean
if (k == ``Lean.Parser.Tactic.decide || k == ``Lean.Parser.Tactic.decide!) &&
    !s[1].getArgs.isEmpty then
  throw s!"forbidden decide configuration '{s[1].reprint.getD ""}' in {modName}"
```

In Lean `v4.34.1`, `s[1]` is a `Lean.Parser.Tactic.optConfig` node whose child
array is `#[nullNode]` (size `1`), where the inner `nullNode` (`s[1][0]`) holds
the actual `configItem` arguments. Consequently, on bare `by decide`,
`s[1].getArgs.isEmpty` evaluates to `false` (because
`#[mkNullNode #[]].size == 1`), falsely rejecting every bare `by decide` with
`forbidden decide configuration ''`! Changing `!s[1].getArgs.isEmpty` to
`!s[1][0].getArgs.isEmpty` (verified in
`support/ProbeInversionBoundaryAndPlausible.lean:725–727`) accepts bare
`by decide` while continuing to reject `decide +kernel` and `decide +native`.

---

### Finding 6: Property-Based Negative Canaries and Pre-Proof Specification Falsification with `leanprover-community/plausible` (`v4.34.0`) + `Chamelean` (PR #56), `subtypeVarTestable` Priority-2000 Constrained Sampling, and the `UInt*` / `BitVec` `maxSize = 100` Capping Pitfall

Basis: `source + execution + derived` — `leanprover-community/plausible`
`v4.34.0` commit `118aa17ee846` (`Plausible/Testable.lean:1–510`,
`Plausible/Sampleable.lean:1–180`, `Plausible/Arbitrary.lean:1–160`,
`Plausible/DeriveArbitrary.lean`) and PR #56 commit `f48022651ffa`
(`Plausible/Chamelean/`), `joshlf/anneal` commit `f6ec1fc98057` (Issue #228 /
PR #82 Miri differential testing), and
`support/ProbeInversionBoundaryAndPlausible.lean` (`PlausibleCanaryProbe`,
lines 876–1350).

#### 6.1 `Plausible` (`v4.34.0`) Architecture and `@[instance 2000] subtypeVarTestable`

`leanprover-community/plausible` (`v4.34.0`) separates random generation and
shrinking (`Arbitrary α`, `Shrinkable α`, bundled via `SampleableExt α` with an
explicit `proxy : Type` and `interp : proxy → α` for non-computable or dependent
types) from proposition evaluation (`Testable (p : Prop)`). When testing a
universally quantified implication `∀ x : α, p x → q x`,
`Plausible/Testable.lean` provides two competing typeclass instances:

1. **Naive Rejection Sampling (`decGuardTestable` at priority `500` +
   `varTestable` at priority `1000`):** Generates an unconstrained `x : α` via
   `SampleableExt α`, evaluates `decide (p x)`, and if `p x` is false, returns
   `TestResult.gaveUp 1` (retrying up to `cfg.numRetries := 10` times per
   instance).
2. **Constrained Subtype Sampling (`subtypeVarTestable` at `@[instance 2000]`,
   `Plausible/Testable.lean:448–457`):** Whenever a constrained generator
   instance `SampleableExt { x : α // p x }` (or `Arbitrary { x : α // p x }`)
   is in scope, `subtypeVarTestable` overrides `varTestable + decGuardTestable`
   at priority `2000`, rewriting `∀ x : α, p x → q x` into
   `∀ s : { x : α // p x }, q s.val`. Every sample satisfies `p x` by
   construction with zero rejected draws!

In `plausible` PR #56 (commit `f48022651ffa`), `Plausible/Chamelean/` adds
`derive_generator` and `derive_checker` macros that automatically synthesize
constrained `Arbitrary { x : α // P x }` generators and `DecOpt` checkers for
inductive relations `P x`, plugging directly into `subtypeVarTestable`.

#### 6.2 Empirical Evaluation: Negative Canaries, Sparse Preconditions, and the `UInt*` Size-Capping Pitfall

`PlausibleCanaryProbe`
(`support/ProbeInversionBoundaryAndPlausible.lean:876–1350`) runs 8 benchmarks
across three Anneal verification scenarios:

1. **Semantic Mutant Canaries (Issue #228 / PR #82 Style):** Testing a mutated
   MIR binary operator evaluator against reference semantics
   (`evalMirBinOpRef`):
   - *Canary 1a (`MirBinOp.shlUnchecked` missing `rhs >= 8` UB guard):*
     Falsified in `1.59 ms` and shrunk in `6` steps to the minimal
     counterexample `[op := .shlUnchecked, lhs := 0, rhs := 8]`.
   - *Canary 1b (`MirBinOp.subChecked` off-by-one `lhs <= rhs` underflow flag):*
     Falsified in `0.21 ms` at `[op := .subChecked, lhs := 0, rhs := 0]`.
2. **Sparse Memory-Frame Well-Formedness (`ValidFrame`) — Rejection Sampling vs.
   Constrained Subtype Generation:** Testing an off-by-one dereference-bounds
   mutant (`offset + accessLen < allocSize` instead of `≤`) under a sparse
   alignment + tight-allocation invariant (`alignExp = 4 ∧ offset % 16 = 0 ∧
   offset + accessLen = allocSize`):
   - *Canary 2a (Naive rejection sampling via `decGuardTestable`):* `GAVE UP`
     after `500` consecutive discarded precondition failures (`2.47 ms`),
     failing to test a single valid frame!
   - *Canary 2b (`Chamelean`-style constrained `Arbitrary { f : MirFrame //
     ValidFrame f }` via `subtypeVarTestable` at priority `2000`):* Falsified in
     `0.27 ms` with zero discarded samples at
     `{ allocSize := 4, alignExp := 4, offset := 0, accessLen := 4 }`.
3. **Pre-Proof Specification Falsification and the `UInt8.Arbitrary` `maxSize`
   Pitfall:** Consider a candidate alignment helper in `theory/Anneal/`:
   `alignUpBitwise (addr align : UInt8) : UInt8 :=`
   `(addr + (align - 1)) &&& ~~~(align - 1)`.
   - *Spec Falsification 3a (Missing `isPowerOfTwoU8 align` precondition on
     `align > 0 → alignUpBitwise addr align % align = 0`):* Falsified in
     `1.12 ms` and shrunk in `1` step to `[addr := 1, align := 3]`.
   - *Spec Falsification 3b-default (Testing `isPowerOfTwoU8 align = true →
     alignUpBitwise addr align >= addr` at default `maxSize := 50` or `100`):*
     **Falsely reports `SUCCESS` (`3.31 ms`)!** Why? Because in
     `Plausible/Arbitrary.lean:94–129`, the stock `Arbitrary` instances for
     `UInt8`, `UInt16`, `UInt32`, `UInt64`, and `USize` are implemented as:

     ```lean
     instance : Arbitrary UInt8 where
       arbitrary := do
         let d ← Gen.choose Nat 0 (min (← Gen.getSize) UInt8.size)
         return UInt8.ofNat d
     ```

     Because `Gen.getSize` is bounded by `cfg.maxSize` (default `100`), stock
     `Plausible` **never generates `UInt8` values above `100`** (or `UInt32` /
     `UInt64` / `USize` values above `100`)! Consequently, any bug or missing
     precondition triggered by fixed-width arithmetic wrapping (`addr + align -
     1 >= 256` on `UInt8`, or `>= 2^32` on `UInt32`) is completely invisible to
     default `plausible` configurations.
   - *Spec Falsification 3b-full (Overriding with boundary-weighted
     `FullRangeUInt8` that mixes corner values `#[0, 1, 127, 128, 254, 255]`
     with uniform `0..255` regardless of `maxSize`):* Falsifies the missing
     overflow guard in `0.39 ms` at `[addr := 165, align := 128]` (where
     `165 + 127 = 292 ≡ 36 (mod 256) < 165`).
   - *Spec Verification 3c (Corrected specification adding `addr.toNat +
     align.toNat - 1 < 256` with `FullRangeUInt8`):* Passes `200/200` instances
     in `8.73 ms`.

| Benchmark Case (`PlausibleCanaryProbe`) | Generator / `Testable` Path | Execution Time | Shrinking Steps | Outcome & Counterexample |
| :--- | :--- | ---: | ---: | :--- |
| **Canary 1a:** `MirBinOp.shlUnchecked` missing `rhs >= 8` UB guard | Derived `Arbitrary` + `varTestable` | `1.59 ms` | `6` | **FAILURE:** `[op := .shlUnchecked, lhs := 0, rhs := 8]` |
| **Canary 1b:** `MirBinOp.subChecked` off-by-one `lhs <= rhs` flag | Derived `Arbitrary` + `varTestable` | `0.21 ms` | `0` | **FAILURE:** `[op := .subChecked, lhs := 0, rhs := 0]` |
| **Canary 2a:** Sparse `ValidFrame` under naive rejection sampling | `decGuardTestable` (priority `500`) | `2.47 ms` | — | **GAVE UP** after `500` discarded precondition failures |
| **Canary 2b:** Sparse `ValidFrame` under constrained subtype generator | `subtypeVarTestable` (priority `2000`) | `0.27 ms` | `0` | **FAILURE:** `[{ allocSize := 4, alignExp := 4, offset := 0, accessLen := 4 }]` |
| **Spec 3a:** `alignUpBitwise` without `isPowerOfTwoU8 align` | Stock `UInt8.Arbitrary` | `1.12 ms` | `1` | **FAILURE:** `[addr := 1, align := 3]` |
| **Spec 3b-default:** `alignUpBitwise` without overflow guard (`maxSize := 50`) | Stock `UInt8.Arbitrary` (`min size 256`) | `3.31 ms` | — | **FALSE SUCCESS** (blind to `addr + align - 1 >= 256` due to `getSize` cap) |
| **Spec 3b-full:** `alignUpBitwise` without overflow guard (`FullRangeUInt8`) | Boundary-weighted `FullRangeUInt8` | `0.39 ms` | `0` | **FAILURE:** `[addr := 165, align := 128]` |
| **Spec 3c:** Corrected `alignUpBitwise` spec (`FullRangeUInt8`) | Boundary-weighted `FullRangeUInt8` | `8.73 ms` | — | **SUCCESS** (`200/200` instances passed) |

**Trust Boundary Placement for `Plausible` in Anneal:** `Plausible`'s
`plausible` tactic closes goals with `sorryAx` after random testing passes, and
its runner uses `IO` and `StdGen`. Therefore, `Plausible` must **never** be
imported into `trusted/lean/` (`Anneal.*`) or `theory/Anneal/` production proof
modules. Instead, it belongs in a dedicated non-TCB test target (e.g.,
`tests/lean-canaries/`) that imports `Anneal.MirSemantics` and `theory/Anneal/`
definitions alongside boundary-weighted `FullRangeUInt*` / `BitVec` generators
and `SampleableExt { x // Valid* x }` instances.

## Boundaries

The conclusions and measurements in this report are bounded by the following
scope conditions:

1. **Toolchain and Repository Versions:** All `.olean` DAG object counts
   (`Expr.numObjs`), kernel replay timings (`Lean.Kernel.Environment.replay`),
   and transitive axiom closures were measured on Lean `v4.34.1` (commit
   `5045d0056413`). Future Lean releases may alter the equation compiler's
   splitter generation, `AuxDeclCache` deduplication, or `omega`/`grind` proof
   terms.
2. **Loop-Free vs. Loop-Heavy Control Flow for `SparseDCom.awp`:** Backward
   weakest-precondition substitution (`awp`) achieves `3.2x`–`3.3x` DAG
   reductions on straight-line and moderate diamond CFGs, but nests
   exponentially on sequences of $D$ back-to-back diamond branches without
   intermediate cut-points ($O(2^D)$ duplication of the postcondition). In
   Anneal's MIR verification pipeline, join blocks shared by multiple branches
   should therefore carry cut-point assertions (hybrid `SparseDCom`) whenever a
   join block's continuation exceeds a small AST size threshold.
3. **First-Order Data vs. Higher-Order Stored Closures in `StoreTy`:**
   `TS/References.lean`'s extrinsic `StoreTy` (`RegionEnv`) eliminates fuel
   indexing for arbitrary cyclic graphs of first-order mutable references (the
   fragment relevant to safe and unsafe Rust data structures without mutable
   function-pointer/trait-object self-application through the heap).
   Higher-order self-referential code pointers stored in mutable memory
   (Landin's knot) still require step-indexed logical relations if termination
   is proved, though type and invariant safety (`StoreWellTyped`) remains
   fuel-free.
4. **`Chamelean` Generator Synthesis Scope (`plausible` PR #56):** Automated
   `derive_generator` synthesis in `Plausible/Chamelean/` currently targets
   inductive relations whose mode constraints decompose into constructor
   unification and recursive sub-generators; arithmetic bit-vector and alignment
   relations (`ValidFrame`) require either handwritten `Arbitrary { x // P x }`
   instances (12 lines in
   `support/ProbeInversionBoundaryAndPlausible.lean:1197–1211`) or SMT/interval
   combinators.

## Evidence

All claims in this report are backed by pinned upstream source files and two
self-contained runnable Lean `v4.34.1` support probes in this package:

- **Support Probes in `support/`:**
  - `support/ProbeHoareWpFunIndAndReferences.lean` (SHA-256:
    `aa086a55e108e6e6853dc5e65deda05ccd7f72219b16ac8dc822c37cd2e78065`):
    Mechanizes `HoareVCProbe` (`diamondProg`, `chain8Prog`, `loopProg` across
    Hoare rules, `FullDCom`, and `SparseDCom.awp`), `FunInductionProbe`
    (`optimizeAExp` and `optMirConstPropStmt` across structural
    `induction`/`cases`, `fun_induction`, and `fun_cases`), `ReferencesProbe`
    (`STLCRef` `Store`, `StoreTy`, `Extends`, `store_weakening`,
    `store_well_typed_alloc`, `assign_pres_store_typing`, `preservation`,
    `cyclic_store_well_typed`), `AxiomClosureProbe` (`omega_nat_add`,
    `omega_nat_sub`, `omega_nat_sub_fn`, `omega_nat_conj`, `lia_nat_add`,
    `lia_nat_sub`, `grind_nat_add`, `grind_nat_sub`), and the `ProbeHarness`
    measurement and kernel replay driver.
  - `support/ProbeInversionBoundaryAndPlausible.lean` (SHA-256:
    `b8078e5e1503c87961468156fd30e099ebe0fb4177cb4a0606eeeb001a917f14`):
    Mechanizes `CustomTactics` (`inversion`, `inversion_fixed` with
    `renameInversionFieldsForward`, `apply ... at ...`), `InversionProbe`
    (`ShiftStep`, `NoStutter`, `IndexedWec`, `#guard_msgs` proofs of Issue #447
    and PR #449 failure modes and fixes, and `Expr.numObjs` + `Kernel.check`
    comparisons), `BoundaryAuditProbe` (14-snippet `TrustedBoundary.lean`
    preflight + `s[1][0].getArgs.isEmpty` fix + `Init.NotationExtra` vs.
    `+Init.Omega/Grind/RCases` elaboration matrix), and `PlausibleCanaryProbe`
    (self-contained `Plausible` `v4.34.0` engine and 8 MIR negative-canary and
    specification-falsification benchmarks).
- **Upstream Source Code Examined:**
  - `plclub/sf-in-lean` (`13e9425b4647402a09316c1d39fa555e9bc3c257` and PR #449
    `0f74845c92a17fc896ab5893106ce2c0e3fbba3b`): `LF/CustomTactics.lean`,
    `HL/Slang.lean`, `HL/Imp.lean`, `HL/Equiv.lean`, `HL/Hoare.lean`,
    `HL/Hoare2.lean`, `TS/Smallstep.lean`, `TS/Stlc.lean`, `TS/StlcProp.lean`,
    `TS/References.lean`, `TS/AttributeDecls.lean`.
  - `leanprover-community/plausible`
    (`118aa17ee84656b8bd727fef7c458ee8c833385c`, `v4.34.0`, and PR #56
    `f48022651ffaa28b272b7328d07bf9450947c97a`): `Plausible/Testable.lean`,
    `Plausible/Sampleable.lean`, `Plausible/Arbitrary.lean`,
    `Plausible/DeriveArbitrary.lean`, `Plausible/Attr.lean`,
    `Plausible/Chamelean/`.
  - `leanprover/cslib` (`f7ec4db9f911a26c8c331fd48d1d464efde9e2a4`):
    `Cslib/Foundations/Semantics/LTS/Basic.lean`, `Simulation.lean`,
    `Bisimulation.lean`.
  - `joshlf/anneal` (`f938c18db56c49e82dde95506894a9b58b76b227`,
    `ebac418ccf7c234ae402cf76a491c903bff3be4f`, and
    `f6ec1fc98057607437bef9bb4ecdad3aaa7623e5`):
    `trusted/audit/TrustedBoundary.lean`,
    `trusted/cargo-anneal/foundation-lock.json`,
    `theory/Anneal/Verification/BuildingBlocks.lean`,
    `trusted/lean/Anneal/MirSemantics.lean`, `theory/Anneal/MirPassProofs.lean`,
    `theory/Anneal/MirValInv.lean`.

## Revalidation

To reproduce every measurement, proof check, `#guard_msgs` assertion, boundary
audit table, and negative-canary benchmark in this report from a clean
checkout, run the two self-contained support probes with Lean `v4.34.1`:

```bash
# 1. Verify SHA-256 checksums of the support probes
sha256sum \
  reports/sf-in-lean-semantics-hoare-vc-custom-tactics-and-plausible-2026/support/ProbeHoareWpFunIndAndReferences.lean \
  reports/sf-in-lean-semantics-hoare-vc-custom-tactics-and-plausible-2026/support/ProbeInversionBoundaryAndPlausible.lean

# 2. Run Probe 1: Hoare/WP VCs, fun_induction/fun_cases, STLCRef store typing,
#    kernel replay benchmarks, and omega/lia/grind transitive axiom closures
~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean --run \
  reports/sf-in-lean-semantics-hoare-vc-custom-tactics-and-plausible-2026/support/ProbeHoareWpFunIndAndReferences.lean

# 3. Run Probe 2: LF/CustomTactics.lean (inversion, Issue #447 / PR #449 fix),
#    14-snippet TrustedBoundary.lean preflight & foundation elaboration matrix,
#    and Plausible v4.34.0 negative canaries & spec falsification
~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean --run \
  reports/sf-in-lean-semantics-hoare-vc-custom-tactics-and-plausible-2026/support/ProbeInversionBoundaryAndPlausible.lean
```

Revalidate this report when:

- Anneal upgrades its pinned Lean toolchain beyond `v4.34.1` or modifies
  `trusted/audit/TrustedBoundary.lean` or
  `trusted/cargo-anneal/foundation-lock.json`.
- `plclub/sf-in-lean` merges PR #449 or updates `LF/CustomTactics.lean` or
  `HL/Hoare2.lean`.
- `leanprover-community/plausible` merges PR #56 (`Chamelean`) or changes the
  default `Arbitrary` instances for `UInt8`..`UInt64`, `USize`, or `BitVec` in
  `Plausible/Arbitrary.lean`.
