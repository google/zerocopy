<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Fuel, Step-Indexing, Clocks, and Recursion Budgets in Program Semantics and Verification TCBs: Polarity Hazards, Structural Decomposition, and Literature Survey

## Summary

Interactive theorem provers (Lean 4, Rocq/Coq, Isabelle/HOL, HOL4, Agda) enforce
logical consistency by requiring every function and inductive predicate in the
kernel to be total and terminating (or guarded/productive). When modeling
potentially non-terminating operational semantics, cyclic environment tables, or
heap/stack reference graphs—especially inside a minimal `prelude`-only Trusted
Computing Base (TCB) such as Anneal's `trusted/lean/Trusted/`—engineers
frequently reach for **fuel** (an explicit `Nat` step counter, clock, or
recursion budget).

Combining a code-level audit and Lean 4.34.1 mechanization of Anneal's TCB
(`Trusted/{Refinement,StepResult,MirAst,MirSemantics}.lean`) and proof engine
(`theory/Anneal/{Lowering,MirLemmas}.lean`) with a cross-system survey of the
programming-languages and verification literature establishes eight primary
findings:

- **F-01 (Why `prelude`-Only TCBs Cannot Use `WellFounded.fix` or
  `partial_fixpoint`):** Lean 4's `WellFounded.fix` (`Init/WF.lean:212-227`)
  Pulls `Init.Grind.Tactics` and `Init.Data.Nat.Basic` into the TCB and blocks
  kernel `whnf`/`isDefEq` reduction on symbolic terms behind opaque `Acc` proofs
  in `Prop` (`Lean/Elab/PreDefinition/WF/Main.lean:62-69`). Lean 4's
  `partial_fixpoint` (`Init/Internal/Order/Basic.lean:105-106`) defines
  chain-complete supremums (`CCPO.csup`) via `Classical.choose`, injecting
  `Classical.choice` into the `.olean` axiom cone. Under `prelude`, every TCB
  definition must therefore use either direct structural recursion or explicit
  `Nat` fuel/step indexing.
- **F-02 (The Polarity Law of Fuel-Bounded Predicates and the Contravariant
  Vacuity Exploit in `AdmissibleAdtInv`):** A fuel-bounded predicate
  $P_{\text{fuel}}(k)$ with $P_{\text{fuel}}(0) = \text{False}$ is an
  **under-approximation** of its unbounded limit
  ($\forall k, P_{\text{fuel}}(k) \implies \exists n, P_{\text{fuel}}(n)$). In
  **positive (covariant)** positions (`EnsuresRetLibInv`, `NonVacuousOn`,
  `returnRefsOk`), fuel exhaustion fails closed. In **negative (contravariant)**
  positions (`initEntryState`, `AdmissibleAdtInv`), fuel exhaustion fails open.
  While `Language.Verified` (`Trusted/Refinement.lean:155-160`) guards function
  entry via `NonVacuousOn`, `AdmissibleAdtInv`
  (`Trusted/MirSemantics.lean:1120-1126`) places
  `inner.valid adts defaultAdtInv s 0 payload` in an **unguarded negative
  position**. If a single-layer `validFuelCoupled` decrements fuel on both
  `.adt` and `.ref` (with `fuel := adts.length + 2`), then for a public safe
  struct `pub struct WrapRef3(pub &&&usize)` (`adts.length = 1`, `fuel = 3`),
  `validCoupled` exhausts its fuel on the three `.ref` constructors and
  evaluates to `False` for every state `s` and value `inner`. Consequently,
  `AdmissibleAdtInvCoupled` holds **vacuously** for `fun _ _ => False` (and any
  arbitrary `badInv`), allowing `unsafe` code to assume `False` on a safe
  public struct (`admissibleAdtInvCoupled_vacuous_arbitrary` in
  `support/AnnealFuelPolarityAndRecursionProbe.lean`).
- **F-03 (Two-Layer Structural/Fuel Decomposition Eliminates Coupled Fuel
  Exhaustion):** Separating `validStep` and `tySizeStep` (which recurse
  **structurally** on `ty : MirTy` and consume **0 fuel** on `.ref inner`) from
  `validFuel` and `tySizeFuel` (which consume 1 unit of fuel **only** when
  unfolding `.adt id` via `adts : List AdtDecl`) makes `adts.length + 1` an
  exact pigeonhole bound for any acyclic `adts` table regardless of reference
  nesting depth (`validFuel_refChain_fuel_irrelevant` and
  `not_admissibleAdtInv_false` in
  `support/AnnealFuelPolarityAndRecursionProbe.lean`).
- **F-04 (Five-Way Taxonomy of Recursion Spines in `Trusted/MirSemantics.lean`):**
  Every recursive function in `Trusted/MirSemantics.lean` falls into one of five
  distinct structural or fuel-bounded patterns:
  1. *Structural on `s.stack : List StackFrame`* (`resolveRef`, 0 fuel—making a
     `s.stack.length + 1` fuel bound completely redundant, proved in
     `findFrameFueled_eq_listFind`);
  2. *Structural on `v : MirVal`* (`MirVal.isFullyInit`, `extractTransmuteBits`,
     0 fuel);
  3. *Structural on `p.projection : List PlaceElem`* despite heap/stack
     dereferences (`evalProj`, `evalRefProj`, 0 fuel);
  4. *Two-layer `MirTy`-structural + `adts`-fuel* (`tySizeStep`/`tySizeFuel`,
     `validStep`/`validFuel`, `constructTransmuteVal`, fuel = `adts.length + 1`
     on `.adt` only); and
  5. *Two-layer `MirVal`-structural + `.ref`-hop fuel*
     (`returnRefsStep`/`returnRefsFuel`, 0 fuel on `.adt` via
     `returnRefsFuel_adt_depth_invariant`, fuel = `5` on untyped `.ref` hops in
     positive terminator position where `false` fails closed to `.failed`).
- **F-05 (AST Indirection via `BodyId` Eliminates Fuel from Decidable Equality
  and Substitution):** Embedding recursive callee `MirBody` trees inside
  `Terminator.call1` and `MirBody.requiredConsts` (at
  `5a48fba09794839a06cee0bc4fa56f98f1fbb38e`) forced `beqMirBodyFuel 8` in
  `theory/Anneal/MirLemmas.lean:3549-3609`, which violates reflexivity
  (`beqMirBody b b = false`) whenever call depth reaches the fuel bound
  (`beqMirBodyFuel_not_refl`). Replacing embedded `MirBody` with `BodyId`
  indirection into `Crate.bodies : List BodyDecl` (at
  `4a7bcfdcc0f50274edd5874ba9b204cc2dac7032`) makes `MirBody` non-recursive and
  restores fuel-free, unconditionally reflexive `beqMirBody` and
  `MirBody.subst` (`beqMirBodyFlat_refl`, `beqMirBodyFlat_eq_iff`).
- **F-06 (Lean 4 Kernel `whnf` / `isDefEq` Reduction Asymmetry: `adts.length + k`
  vs. `k + adts.length`):** Because `Nat.add` (`Init/Prelude.lean:1773-1775`) is
  defined by structural recursion on its **second** argument, `adts.length + 1`
  is definitionally equal (`rfl`) to `Nat.succ adts.length` even when `adts` is
  a free symbolic variable, allowing `tySize adts tySizes .usize = some 8` and
  `tySize adts tySizes (.ref inner) = some 8` to reduce by `rfl`
  (`tySize_usize_symbolic_rfl`, `tySize_ref_chain_symbolic_rfl`). By contrast,
  `1 + adts.length` (`Nat.add 1 adts.length`) is stuck in Weak Head Normal Form
  (WHNF) when `adts` is symbolic and requires an inductive rewrite before
  `tySizeFuel` can unfold.
- **F-07 (Relational Step-Indexing `ReachesPrefix` in the TCB vs. Inductive
  Omnisemantics `ExecNormal` in Stage 3 Lowering):** Anneal's TCB uses
  relational step-indexed prefixes (`ReachesPrefix`, `Trusted/StepResult.lean:89-108`)
  and trajectory witnesses (`eventualBehaviorOf`, `StepResult.lean:119-149`) to
  express all-prefix safety, infinite-loop safety (`loop {}`), propositional
  demonic choice (`StepResult.choice`), and productive reactivity without
  coinductive types (`silentLoop_safe_and_diverges`, `demonicStep_reaches_failed`
  in `support/SemanticsFuelOmnisemanticsComparisonProbe.lean`). However, for
  Stage 3 compiler lowering (`lowerBody_simulates`,
  `theory/Anneal/Lowering.lean:535-605`), where `goto`-chain coalescing
  contracts two small steps into one, step-indexed `ReachesPrefix` suffers from
  step-count mismatch (`n` lowered steps correspond to `n' ≥ n` source steps).
  Anneal solves this by proving simulation over `ExecNormal`
  (`Lowering.lean:34-44`)—a fuel-free inductive big-step omnisemantics—and
  bridging back to `ReachesPrefix` once via `execNormal_safeAndEnsures`
  (`MirLemmas.lean:583-617`; mechanized in `coalesceGoto_simulates_execNormal`
  and `coalesceGoto_simulates_reachesPrefix_dilated`).
- **F-08 (Cross-System Synthesis Across the Literature):** A comparative analysis
  of (1) Step-Indexed Logical Relations & Iris, (2) CakeML Functional Big-Step
  Clocks, (3) Definitional Interpreters with Fuel, (4) Coinductive `ITree` /
  `CTree` / Delay Monads, (5) Charguéraud Inductive Omnisemantics, and
  (6) Theorem-Prover Recursion Compilers establishes a sharp architectural split:
  use **relational step-indexed prefixes** in a `prelude` TCB that must govern
  divergence, reactivity, and demonic choice; use **two-layer structural +
  pigeonhole-fueled helpers** for finite cyclic environment tables (with positive
  inhabitation guards wherever used negatively); and use **fuel-free inductive
  omnisemantics (`ExecNormal` / `OmniSem`)** in the proof layer for terminating
  symbolic execution and step-contracting compiler simulations.

## Applicability

- `joshlf/anneal` at `4a7bcfdcc0f50274edd5874ba9b204cc2dac7032`
  (`simplify-trusted` branch: `trusted/lean/Trusted/{Refinement,StepResult,MirAst,MirSemantics}.lean`,
  `theory/Anneal/{Lowering,MirLemmas}.lean`)
- `joshlf/anneal` at `5a48fba09794839a06cee0bc4fa56f98f1fbb38e` (recursive
  `MirBody` and `beqMirBodyFuel 8` baseline)
- `joshlf/anneal` at `ebac418ccf7c234ae402cf76a491c903bff3be4f` (`@Nat.rec` and
  `@MirVal.rec` TCB recursion baseline)
- `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`,
  `src/lean/Init/{Prelude,Core,WF,WFComputable,WFExtrinsicFix}.lean`,
  `src/lean/Init/Internal/Order/Basic.lean`,
  `src/lean/Lean/Elab/PreDefinition/WF/{Main,Fix}.lean`)

## Findings

### F-01: Why `prelude`-Only TCBs Cannot Use `WellFounded.fix` or `partial_fixpoint`

Every file in Anneal's Lean TCB (`trusted/lean/Trusted/*.lean`) begins with the
`prelude` directive and imports only `Init.NotationExtra` and `Init.Core` (locked
by `trusted/lean/foundation-lock.json` and audited by `trusted/audit/`). In
standard Lean 4, non-structural recursion is compiled by one of three mechanisms,
each of which is incompatible with a minimal, auditable `prelude` TCB:

1. **Well-Founded Recursion (`WellFounded.fix`, `Init/WF.lean:212-227`):**
   - *Import footprint:* `Init.WF` transitively imports `Init.Grind.Tactics`,
     `Init.Data.Nat.Basic`, and `Init.SizeOf`, adding thousands of lines of
     tactic and arithmetic definitions to the TCB environment.
   - *Kernel reduction blockage:* `WellFounded.fix` recurses via `Acc.rec` on an
     accessibility proof `a : Acc r x` living in `Prop`. Although Lean 4's kernel
     permits singleton elimination from `Acc` into `Sort u`, unfolding
     `WellFounded.fixF` on a symbolic term requires constructing and reducing the
     accessibility proof term (`Nat.lt_wfRel`). As documented in the Lean 4
     elaborator (`src/lean/Lean/Elab/PreDefinition/WF/Main.lean:62-69` at
     `5045d0056413266e57c625dcd7c365b10e377c52`), definitions compiled via
     `WellFounded.fix` are marked `irreducible` by default (unless reduced by
     `WellFounded.Nat.fix` in `Init.WFComputable`) because unfolding the `Acc`
     proof term during kernel `isDefEq` triggers exponential blowups.
2. **Monadic Extrinsic Fixpoints (`extrinsicFix`, `Init/WFExtrinsicFix.lean:51-78`):**
   Introduced in recent Lean 4 releases to avoid `Acc` proof terms during
   computation, `extrinsicFix` still depends on `Init.WF` and `Classical.em` /
   propositional termination witnesses to extract pure values.
3. **Domain-Theoretic Partial Fixpoints (`partial_fixpoint`,
   `Init/Internal/Order/Basic.lean:105-106`):**
   Lean 4's `partial_fixpoint` mechanism compiles tail-recursive and monadic
   functions as least fixpoints over a chain-complete partial order (`CCPO`).
   However, `CCPO.csup` is defined in `Init/Internal/Order/Basic.lean:105-106`
   using `Classical.choose`:
   ```lean
   noncomputable def csup {α : Type u} [CCPO α] (c : Set α) (hc : Directed (· ≤ ·) c) : α :=
     Classical.choose (CCPO.has_csup hc)
   ```
   Using `partial_fixpoint` therefore injects `Classical.choice` into the
   declaration's `.olean` axiom cone and marks the function `noncomputable`,
   preventing both `decide`/`rfl` kernel evaluation and `.olean` TCB boundary
   verification when `Classical.choice` is disallowed.

Consequently, a `prelude`-only TCB has exactly two kernel-native recursion
mechanisms:
- **Structural recursion** (compiled via `T.rec` or `T.brecOn` using only
  `Init.Prelude` and `Init.Core`), and
- **Explicit `Nat` fuel / step counters** (structural recursion on `Nat`, via
  `Nat.rec`).

---

### F-02: The Polarity Law of Fuel-Bounded Predicates and the Contravariant Vacuity Exploit in `AdmissibleAdtInv`

When a recursive predicate $P : \alpha \to \text{Prop}$ over a potentially
cyclic environment is approximated by a fuel-indexed family
$P_{\text{fuel}} : \mathbb{N} \to \alpha \to \text{Prop}$ with base case
$P_{\text{fuel}}(0, x) = \text{False}$ and monotone step
$P_{\text{fuel}}(k, x) \implies P_{\text{fuel}}(k+1, x)$, every finite fuel
level $k$ is an **under-approximation** of the true semantic predicate
$P_{\infty}(x) \triangleq \exists n, P_{\text{fuel}}(n, x)$:

$$\forall k\, x,\quad P_{\text{fuel}}(k, x) \implies P_{\infty}(x)$$

Whether this under-approximation is **sound (fail-closed)** or **unsound
(fail-open)** in a verification TCB depends strictly on the **logical polarity**
of the occurrence of $P_{\text{fuel}}(k, x)$ inside the top-level theorem
(`CrateTheorem`, `Trusted/MirSemantics.lean:1225-1232`):

| Occurrence in `Trusted/MirSemantics.lean` | Logical Polarity in `CrateTheorem` | Behavior on Fuel Exhaustion ($P_{\text{fuel}}(k, x) = \text{False}$) | Soundness Status |
| :--- | :--- | :--- | :--- |
| `EnsuresRetLibInv` (`MirSemantics.lean:1131-1136`): `r.value.valid adts adtInv ...` | **Positive (covariant)** (postcondition of `SpecOn`) | Obligation reduces to `False`; proof of `EnsuresRetLibInv` becomes impossible. | **Fail-closed (sound)** (`fuel_positive_sound`) |
| `MirVal.returnRefsOk` (`MirSemantics.lean:352-354`): `returnRefsFuel s localCount 5 v` | **Positive (covariant)** (`false` steps to `StepResult.failed` at `Terminator.return_`) | Execution reaches `.failed`, violating ` out.isSafe`. | **Fail-closed (sound)** |
| `ConstSucceeds` / `ConstUnwinds` (`MirSemantics.lean:1036-1054`): `∃ n, ReachesPrefix ... n ...` | **Positive** in `MonoAdmitted`, **guarded negative** in `initMirState` | Empties `initMirState`, which causes `NonVacuousOn` to become `False`. | **Fail-closed via `NonVacuousOn`** (`nonVacuous_blocks_total_exhaustion`) |
| `initEntryState` / `argsMatchInv` (`MirSemantics.lean:468-496`): `v.valid adts adtInv ...` | **Negative** in `SpecOn` / `ProductiveOn`, **positive** in `NonVacuousOn` | Would make `SpecOn` vacuous, **except** `Verified` requires `NonVacuousOn (L.dom prog) pre` (`∃ s, dom s ∧ pre s`). | **Fail-closed via `NonVacuousOn`** (unless fuel is only partially exhausted on a subtype) |
| `AdmissibleAdtInv` (`MirSemantics.lean:1120-1126`): `∀ decl ∈ adts, ... → inner.valid adts defaultAdtInv s 0 payload → adtInv decl.id inner` | **Unguarded Negative (contravariant antecedent)** | Antecedent `inner.valid ...` becomes `False` for all `s, inner`, making `AdmissibleAdtInv` **vacuously `True`** for *every* `adtInv`! | **FAIL-OPEN (UNSOUND)** if `valid` can exhaust fuel on any valid payload type! |

#### Concrete Mechanized Exploit (`AdmissibleAdtInvCoupled`)

Look closely at `AdmissibleAdtInv` (`Trusted/MirSemantics.lean:1120-1126`):
```lean
def AdmissibleAdtInv (adts : List AdtDecl) (adtInv : AdtInv) : Prop :=
  NoDupIds (adts.map AdtDecl.id) ∧
  ∀ decl, decl ∈ adts → decl.allFieldsPubSafe = true →
    ∀ (s : MirState) (payload : MirTy) (inner : MirVal),
      decl.payloadTy = some payload →
      inner.valid adts defaultAdtInv s 0 payload →
      adtInv decl.id inner
```
As its doc comment (`MirSemantics.lean:1116-1119`) notes, `AdmissibleAdtInv`
deliberately omits a per-struct inhabitation requirement (`∃ s inner, inner.valid ...`)
so that unmodeled or uninhabited struct declarations in a crate do not block
verifying unrelated functions.

However, suppose `MirVal.valid` is implemented with a single coupled fuel
parameter `fuel : Nat` that decrements on **both** `.adt` and `.ref` (for
example, `fuel := adts.length + 2`, modeled as `validCoupled` in
`support/AnnealFuelPolarityAndRecursionProbe.lean:236-240`):

1. Consider a crate with a single public, all-safe-fields wrapper struct
   `pub struct WrapRef3<'a>(pub &'a &'a &'a usize)` (`pubRef3Adt`, where
   `adts = [pubRef3Adt]`, `adts.length = 1`, and `fuel = adts.length + 2 = 3`).
2. When `AdmissibleAdtInvCoupled` checks `pubRef3Adt`, it evaluates
   `validCoupled [pubRef3Adt] defaultAdtInv s 0 (.ref (.ref (.ref .usize))) inner`.
3. Traversing the three `.ref` constructors consumes all 3 units of fuel
   ($3 \to 2 \to 1 \to 0$) before reaching `.usize`, where `validFuelCoupled 0`
   is definitionally `False` (`validCoupled_ref3_always_false`,
   `AnnealFuelPolarityAndRecursionProbe.lean:261-308`).
4. Because `validCoupled` is `False` for every state `s` and value `inner`,
   `AdmissibleAdtInvCoupled [pubRef3Adt] badInv` holds **vacuously** for
   **every** `badInv : AdtInv`—including `fun _ _ => False`
   (`admissibleAdtInvCoupled_vacuous_arbitrary` and
   `admissibleAdtInvCoupled_accepts_false`,
   `AnnealFuelPolarityAndRecursionProbe.lean:314-331`).
5. Meanwhile, another function in the crate whose signature has shallower
   reference depth (e.g., `pub fn f(x: usize) -> usize`) easily passes
   `NonVacuousOn` (`partial_exhaustion_bypasses_nonvacuity`,
   `AnnealFuelPolarityAndRecursionProbe.lean:94-101`).

---

### F-03: Separating Structural Recursion on `MirTy` from Fuel-Bounded `.adt` Lookup

Why did `validCoupled` run out of fuel on `&&&usize` when `&&&usize` contains
zero recursive struct unfoldings? Because `validCoupled` conflated two
fundamentally different recursion edges:

1. **Unfolding `.ref inner`:** In `validStep` (`Trusted/MirSemantics.lean:413-419`),
   matching `.ref inner` against `.ref frameId gen loc` resolves `pointee` in
   `s` (`resolveRef s frameId gen loc`). Although `pointee : MirVal` is **not**
   a structural subterm of `.ref frameId gen loc` (and in an arbitrary state `s`,
   local `0` could hold `.ref 0 0 0`, forming a cycle in `MirVal`), the type
   `inner : MirTy` **is** a strict structural subterm of `.ref inner : MirTy`!
2. **Unfolding `.adt id`:** Matching `.adt id` against `.adt vId inner` looks up
   `decl.payloadTy` in the flat environment table `adts : List AdtDecl`. Here
   `payload : MirTy` is **not** a subterm of `.adt id`, so structural recursion
   on `MirTy` stops and must delegate to the outer fuel counter.

In `Trusted/MirSemantics.lean:395-456` (and `tySizeStep`/`tySizeFuel` at
`MirSemantics.lean:253-281`) at `4a7bcfdcc0f50274edd5874ba9b204cc2dac7032`,
Anneal factors both functions into a two-layer nested recursion:

```lean
-- Layer 1: Structural recursion on `ty : MirTy` (0 fuel consumed on `.ref inner`)
noncomputable def validStep (adts : List AdtDecl) (adtInv : AdtInv)
    (s : MirState) (callerBase : Nat)
    (unfold : MirTy → MirVal → Prop) : MirTy → MirVal → Prop
  | .usize, .usize _ => True
  ...
  | .adt id, .adt vId inner =>
    vId = id ∧ adtInv id inner ∧
    match (findAdtDecl adts id).bind AdtDecl.payloadTy with
    | some payload => unfold payload inner
    | none => False
  | .ref inner, .ref frameId gen loc =>
    frameId = 0 ∧ callerBase ≤ loc.index ∧
    match resolveRef s frameId gen loc with
    | some pointee => validStep adts adtInv s callerBase unfold inner pointee
    | none => False
  ...

-- Layer 2: Structural recursion on `fuel : Nat` (1 fuel consumed per `.adt` unfolding)
noncomputable def MirVal.validFuel (adts : List AdtDecl) (adtInv : AdtInv)
    (s : MirState) (callerBase : Nat) : Nat → MirTy → MirVal → Prop
  | 0, _, _ => False
  | fuel + 1, ty, v =>
    validStep adts adtInv s callerBase
      (MirVal.validFuel adts adtInv s callerBase fuel) ty v
```

In `support/AnnealFuelPolarityAndRecursionProbe.lean:346-463`, we prove three
mechanized theorems about this two-layer split:
- `valid_ref3_holds` (`AnnealFuelPolarityAndRecursionProbe.lean:402-407`):
  `sampleRef3Val` is valid at `ref3Usize = &&&usize` under `[pubRef3Adt]`.
- `not_admissibleAdtInv_false` (`AnnealFuelPolarityAndRecursionProbe.lean:412-416`):
  `AdmissibleAdtInv [pubRef3Adt] (fun _ _ => False)` is **refuted**, closing the
  contravariant vacuity exploit.
- `validFuel_refChain_fuel_irrelevant`
  (`AnnealFuelPolarityAndRecursionProbe.lean:454-462`): for any `n`-deep chain
  of shared references `refChain n .usize`, `validFuel ... (fuel + 1)` is
  propositionally identical to `validFuel ... 1` for every `n : Nat` and
  `fuel : Nat`.

#### Exactness of the Pigeonhole Bound `adts.length + 1`

Because only `.adt id` invokes `unfold` (consuming 1 unit of fuel), and every
leaf check (`.usize`, `.bool`, `.unit`, `.param`, or a `.adt` with no further
`.adt` payload) requires 1 initial `fuel + 1` step to enter `validStep` /
`tySizeStep`, any chain of nested `.adt` unfoldings of depth $d \le |\text{adts}|$
visits at most $|\text{adts}|$ distinct `AdtDecl` entries before either reaching
a non-ADT leaf or repeating an `AdtId` (which indicates a cyclic type
declaration). Thus `fuel := adts.length + 1` is **exact** (both sound and
complete) for all acyclic `adts` tables with distinct `AdtId`s (`NoDupIds`).

---

### F-04: Five-Way Taxonomy of Recursion Spines in `Trusted/MirSemantics.lean`

Auditing every recursive helper in `Trusted/MirSemantics.lean` at
`4a7bcfdcc0f50274edd5874ba9b204cc2dac7032` reveals five distinct structural and
fuel-bounded recursion patterns:

| TCB Function (`Trusted/MirSemantics.lean`) | Primary Recursion Spine | Fuel Used | Why Fuel Is / Is Not Needed |
| :--- | :--- | :--- | :--- |
| `resolveRef` (`304-319`), `findAdtDecl` (`133-134`), `findBody` (`137-138`) | `s.stack : List StackFrame` / `adts : List AdtDecl` / `bodies : List BodyDecl` (via `List.find?`) | **0 fuel** | Linear scan of a finite inductive `List` (`Init/Data/List/Basic.lean:1617-1621` compiles `List.find?` via `List.brecOn`). Passing `s.stack.length + 1` fuel is redundant (`findFrameFueled_eq_listFind`). |
| `MirVal.isFullyInit` (`292-295`), `extractTransmuteBits` (`741-749`) | `v : MirVal` | **0 fuel** | `.adt _ inner` unpacks a strict structural subterm `inner` of `v : MirVal`; `.ref` is not dereferenced. |
| `evalProj` (`522-530`), `evalRefProj` (`580-590`) | `proj : List PlaceElem` | **0 fuel** | Even though `.deref` replaces `v` with `pointee` from `resolveRef s` (which is not a subterm of `v`), every step strips one head element from `proj : List PlaceElem`. |
| `tySizeStep`/`tySizeFuel` (`253-267`), `validStep`/`validFuel` (`395-428`), `constructTransmuteVal` (`768-783`) | Layer 1: `ty : MirTy` (0 fuel on `.ref`)<br>Layer 2: `fuel : Nat` on `.adt` | `adts.length + 1` | `.ref inner` shrinks `MirTy` structurally; `.adt id` jumps to `decl.payloadTy` in `adts`, bounded by pigeonhole `adts.length + 1`. |
| `returnRefsStep`/`returnRefsFuel` (`334-354`) | Layer 1: `v : MirVal` (0 fuel on `.adt`)<br>Layer 2: `fuel : Nat` on `.ref` hops | `5` (up to 4 pointer hops) | At `Terminator.return_`, no `MirTy` or `List PlaceElem` spine is threaded, and `s.locals` could syntactically contain a reference cycle. `.adt _ inner` shrinks `v : MirVal` structurally (`returnRefsFuel_adt_depth_invariant`), while `.ref` consumes 1 fuel per dereference hop and fails closed (`false` $\mapsto$ `.failed`) in positive position. |

*Design observation on `returnRefsOk`:* Because `active.retTy : MirTy` is
available on `active : MirBody` at `evalMirTerminator`
(`MirSemantics.lean:903-926`), `returnRefsOk` could also be parameterized by
`active.retTy : MirTy` (recursing structurally on `MirTy` for `.ref inner` and
using `adts.length + 1` fuel on `.adt id`, identically to `validStep`/`validFuel`),
which would eliminate the fixed 4-hop reference limit (`fuel = 5`) at
`Terminator.return_` as well.

---

### F-05: AST Indirection (`BodyId`) Eliminates Fuel from Decidable Equality and Substitution

At revision `5a48fba09794839a06cee0bc4fa56f98f1fbb38e`, `MirBody` was a
mutually/nested recursive inductive type that embedded callee `MirBody` records
directly inside `Terminator.call1` and `MirBody.requiredConsts`:

```lean
-- At 5a48fba09794839a06cee0bc4fa56f98f1fbb38e:
inductive Terminator where
  ...
  | call1 (dst : Place) (callee : MirBody) (arg : Operand)
      (target : BlockId) (typeArgs : List MirTy)

structure MirBody where
  ...
  blocks : List BasicBlock
  requiredConsts : List (MirBody × List MirTy)
```

Because `MirBody` occurred nested inside `List BasicBlock` (via `Terminator.call1`)
and `List (MirBody × List MirTy)`, Lean 4 could not derive a flat structural
`BEq` instance for `MirBody`, and `theory/Anneal/MirLemmas.lean:3549-3609` had
to define a fuel-bounded equality checker `beqMirBodyFuel` hardcoded to
`fuel := 8`:

```lean
-- theory/Anneal/MirLemmas.lean:3608-3609 at 5a48fba09794839a06cee0bc4fa56f98f1fbb38e:
def beqMirBody (b1 b2 : MirBody) : Bool :=
  beqMirBodyFuel 8 b1 b2
```

As proved in `beqMirBodyFuel_not_refl`
(`support/AnnealFuelPolarityAndRecursionProbe.lean:544-550`), any fuel-bounded
Boolean equality `beqMirBodyFuel fuel` violates reflexivity
(`beqMirBodyFuel fuel b b = false`) as soon as the call graph depth reaches
`fuel`.

At revision `4a7bcfdcc0f50274edd5874ba9b204cc2dac7032`
(`Trusted/MirAst.lean:154-206`), replacing embedded `MirBody` values with a
flat `BodyId` index into `Crate.bodies : List BodyDecl` broke the recursive
cycle in `MirBody`:
- `Terminator.call1` carries `(callee : BodyId)` instead of `(callee : MirBody)`;
- `MirBody.requiredConsts` carries `List (BodyId × List MirTy)`;
- `MirBody.subst` (`Trusted/MirSemantics.lean:196-208`) and `beqMirBody`
  (`theory/Anneal/MirLemmas.lean:3763-3770`) are now **non-recursive**,
  total, and unconditionally reflexive (`beqMirBodyFlat_refl` and
  `beqMirBodyFlat_eq_iff`,
  `AnnealFuelPolarityAndRecursionProbe.lean:566-573`).

---

### F-06: Lean 4 Kernel `whnf` / `isDefEq` Reduction Asymmetry (`n + k` vs. `k + n`) and Pattern Matching vs. `@Nat.rec`

In Lean 4's `Init/Prelude.lean:1773-1775`
(`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`), natural number
addition is defined by structural recursion on its **second** argument:

```lean
protected def Nat.add : (@& Nat) → (@& Nat) → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)
```

This creates a fundamental kernel reduction asymmetry whenever a fuel expression
combines a symbolic list length (`adts.length`) with a constant offset (`+ 1` or
`+ 2`):

1. **Right-Addition (`adts.length + 1`, `adts.length + 2`):**
   By the second equation of `Nat.add`, `n + 1` is definitionally equal (`isDefEq`)
   in the Lean 4 kernel to `Nat.succ n`, and `n + 2` is definitionally equal to
   `Nat.succ (Nat.succ n)` (`right_add_two_defeq_succ_succ`,
   `AnnealFuelPolarityAndRecursionProbe.lean:628-630`). Consequently, when
   `evalTyByteSize adts tySizes ty` (`tySizeFuel adts tySizes (adts.length + 1) ty`)
   is applied to `.usize`, `.bool`, `.unit`, `.param idx`, or `.ref inner`, the
   outer `fuel + 1` pattern match in `tySizeFuel` reduces immediately in WHNF
   **even when `adts : List AdtDecl` is a universally quantified symbolic
   variable** (`tySize_usize_symbolic_rfl` and `tySize_ref_chain_symbolic_rfl`,
   `AnnealFuelPolarityAndRecursionProbe.lean:614-622`).
2. **Left-Addition (`1 + adts.length`, `2 + adts.length`):**
   Because the second argument `adts.length` is not a constructor application
   `Nat.succ _` when `adts` is symbolic, `1 + adts.length` (`Nat.add 1 adts.length`)
   is **stuck in WHNF**. Neither `rfl` nor `dsimp` can unfold `tySizeFuel` on a
   symbolic `adts` without first rewriting by `Nat.one_add` / `Nat.add_comm`
   (`tySizeLeftAdd_eq_tySize`,
   `AnnealFuelPolarityAndRecursionProbe.lean:635-646`).

#### Evolution from Raw `@Nat.rec` (`ebac418cc`) to Two-Layer Equation Compiler Definitions (`4a7bcfdcc`)

At an earlier TCB milestone (`ebac418ccf7c234ae402cf76a491c903bff3be4f`,
`Trusted/MirSemantics.lean:106-127` and `259-318`), Anneal wrote recursive TCB
functions using raw eliminators (`@Nat.rec`, `@MirVal.rec`, `@MirTy.rec`) to
ensure zero dependence on equation-compiler elaboration helpers. While both raw
`@Nat.rec` and equation-compiler pattern matching elaborate to the exact same
kernel `Nat.rec` / `MirTy.brecOn` primitives under `prelude`, the two-layer
pattern-matched formulation (`tySizeStep`/`tySizeFuel` and
`validStep`/`validFuel` at `4a7bcfdcc0f50274edd5874ba9b204cc2dac7032`) has two
decisive advantages:
- It automatically generates clean equational unfolding lemmas for `simp`/`dsimp`;
  and
- At `ebac418ccf7c234ae402cf76a491c903bff3be4f` (`MirSemantics.lean:150-154`),
  avoiding `MirTy` recursion in `MirTy.wfInAdts` led to checking `.ref` only one
  level deep (`| .ref (.adt id) => ... | .ref (.ref _) => true`), whereas
  `tySizeStep` at `4a7bcfdcc0f50274edd5874ba9b204cc2dac7032` checks `.ref inner`
  to arbitrary depth without spending fuel.

---

### F-07: Relational Step-Indexing (`ReachesPrefix`) in the TCB vs. Inductive Omnisemantics (`ExecNormal`) in Stage 3 Lowering

Anneal deliberately uses **two different semantic representations** on the two
sides of its trust boundary (`support/SemanticsFuelOmnisemanticsComparisonProbe.lean`):

#### 1. Inside `trusted/lean/Trusted/`: Relational Step-Indexed Prefixes (`ReachesPrefix`)

In `Trusted/StepResult.lean:89-149`, Anneal defines program execution via an
inductive finite-prefix relation indexed by `steps : Nat`:
- `ReachesPrefix step prog (steps : Nat) init trace out`
- `eventualBehaviorOf step prog init out`, which classifies infinite executions
  without coinductive types using trajectory functions `traj : Nat → State`:
  - **All-prefix safety (`out.isSafe`):** A program faults (`.failed`) iff
    `∃ steps trace, ReachesPrefix step prog steps init trace .failed`. Therefore,
    proving safety (`∀ out, eventualBehaviorOf ... out → out.isSafe`) reduces to
    plain mathematical induction on `steps : Nat` (`silentLoop_reaches_running`
    and `silentLoop_safe_and_diverges`,
    `SemanticsFuelOmnisemanticsComparisonProbe.lean:152-194`).
  - **Silent divergence (`EventualOut.diverges trace`):** Witnessed by a
    trajectory `traj : Nat → State` that reaches `traj 0` with `trace` and steps
    silently from `traj k` to `traj (k + 1)` in `n + 1` steps for every `k`.
  - **Productive reactivity (`EventualOut.reacts infTrace`):** Witnessed by
    `traj : Nat → State`, `segSteps : Nat → Nat`, and `segEvent : Nat → Event`
    emitting one event per non-empty segment.
  - **Demonic non-determinism (`StepResult.choice (branches : State → Prop)`):**
    Because `ReachesPrefix.choice` existentially selects any `s'` satisfying
    `branches s'`, universal quantification over `eventualBehaviorOf` in
    `SpecOn` (`∀ s out, pre s → sem prog s out → post s out`) is **demonic**:
    every reachable branch must be safe and satisfy `post`
    (`demonicStep_reaches_failed`,
    `SemanticsFuelOmnisemanticsComparisonProbe.lean:202-215`).

#### 2. Inside `theory/Anneal/`: Fuel-Free Inductive Omnisemantics (`ExecNormal`)

Why does `theory/Anneal/Lowering.lean:34-44` introduce a second execution
relation `ExecNormal` without a `steps : Nat` parameter?

```lean
-- theory/Anneal/Lowering.lean:34-44 at 4a7bcfdcc0f50274edd5874ba9b204cc2dac7032:
inductive ExecNormal (adts : List AdtDecl) (bodies : List BodyDecl)
    (body : MirBody) : MirState → MirReturn → Prop where
  | term {s : MirState} {r : MirReturn} :
      evalMirStep adts bodies body s = .terminated (.normal r) →
      ExecNormal adts bodies body s r
  | step {s s' : MirState} {r : MirReturn} :
      evalMirStep adts bodies body s = .step [] s' →
      ExecNormal adts bodies body s' r →
      ExecNormal adts bodies body s r
```

Consider Stage 3 compiler lowering (`lowerBody` in
`theory/Anneal/Lowering.lean:300-605`), which coalesces `goto` chains (`bb0`
jumping to an empty `bb1` that jumps to `bb2` is rewritten so `bb0` jumps
directly to `bb2`) and fuses local copy chains.
- In `ReachesPrefix`, coalescing `bb0 -> bb1 -> bb2` into `bb0 -> bb2`
  **changes the step index `n`**: a 1-step transition in `lowerBody body`
  corresponds to 2 (or $k$) steps in `body`. Carrying `n : Nat` through backward
  simulation requires existential step-dilation arithmetic
  ($\forall n, \text{ReachesPrefix}(\text{lowered}, n) \implies \exists n' \ge n, \text{ReachesPrefix}(\text{orig}, n')$)
  at every inductive step.
- In `ExecNormal`, step counts are erased into the inductive derivation tree.
  Backward simulation (`lowerBody_simulates`, `Lowering.lean:535-605`; mechanized
  in `coalesceGoto_simulates_execNormal`,
  `SemanticsFuelOmnisemanticsComparisonProbe.lean:602-662`) replaces one
  lowered `ExecNormal.step` with two uncoalesced `ExecNormal.step` constructors
  (`ExecNormal.step hcode (ExecNormal.step hmid ih)`) with **zero arithmetic on
  `Nat`**.
- Once `ExecNormal` is established for the lowered body, a single bridge theorem
  (`execNormal_safeAndEnsures` and `execNormal_reaches` in
  `theory/Anneal/MirLemmas.lean:583-617`; mechanized in
  `execNormal_iff_exists_reachesPrefix` and
  `coalesceGoto_simulates_reachesPrefix_dilated`,
  `SemanticsFuelOmnisemanticsComparisonProbe.lean:546-573, 670-681`) existentializes
  the step count $n'$ once at the boundary to discharge `MirSem`.

---

### F-08: Broad Literature and Systems Survey

#### 1. Step-Indexed Operational Semantics and Logical Relations

- **Foundational PCC & Recursive Types (Appel & McAllester, TOPLAS 2001; Ahmed,
  ESOP 2006; Appel, Melliès, Richards, Vouillon, POPL 2007):**
  Introduced step-indexed logical relations $\mathcal{V}_k\llbracket \tau \rrbracket$
  indexed by remaining operational steps $k \in \mathbb{N}$ to break the
  negative-occurrence cardinality paradox of recursive types ($\mu \alpha.\, \alpha \to \tau$)
  and mutable references without domain theory. The ** Gödel-Löb modality
  ($\triangleright P$)** ("later $P$", holding at index $k$ iff $k = 0 \lor P(k-1)$)
  turns contravariant recursive occurrences into contractive fixpoints.
- **Biorthogonality & Relational Step-Indexing (Benton & Hur, ICFP 2009; Dreyer,
  Neis, Birkedal, ICFP 2010):**
  Extended step-indexing to binary compiler correctness relations between source
  and target languages. A notorious proof-engineering hazard in explicit
  step-indexed binary relations is **step-index misalignment (stuttering)**:
  when one target step corresponds to zero or multiple source steps, arithmetic
  bookkeeping on indices $(k, j)$ pollutes every lemma unless hidden behind an
  abstract modal logic or simulation game.
- **Iris, RustBelt, Caesium, and RefinedRust (Jung et al., JFP 2018; Jung et al.,
  POPL 2018; Sammler et al., PLDI 2021; Gäher et al., PLDI 2024):**
  Iris internalizes step-indexing inside higher-order ghost state and the
  `later` modality ($\triangleright$), hiding explicit `Nat` arithmetic from
  users. However, for **liveness and total correctness**, finite $\mathbb{N}$
  step-indexing is insufficient when unbounded nondeterminism is present; Spies
  et al. (*Transfinite Iris*, POPL 2021) showed that proving termination under
  unbounded demonic choice requires **ordinal ($\text{Ord}$) step-indexing**.

#### 2. Functional Big-Step Semantics (Clocked Evaluators — CakeML / HOL4)

- **Owens, Myreen, Kumar, and Tan (ESOP 2016):**
  Replaced relational small-step and relational big-step semantics in the CakeML
  verified compiler with **Functional Big-Step Semantics**: a total recursive
  function ` evaluate (ck : num) (env : env) (s : state) (e : exp) : state # result`
  that carries a natural-number clock `ck` decremented on recursive calls and
  `while` loops, returning `Rerr (Rabort Rtimeout_error)` when `ck = 0`.
- **Two Core Metatheorems (Mechanized in
  `support/SemanticsFuelOmnisemanticsComparisonProbe.lean:333-490`):**
  1. *Clock Monotonicity (`evalClocked_mono`):* If `evalClocked ck stmt s = out`
     and `out ≠ .timeout`, then for all `extra : Nat`,
     `evalClocked (ck + extra) stmt s = out`.
  2. *Divergence as Universal Timeout (`whileSkip_diverges_all_clocks`):* For
     deterministic programs, silent divergence is characterized by
     $\forall \text{ck},\, \text{evalClocked}(\text{ck}, e, s) = \text{timeout}$,
     avoiding coinductive big-step predicates entirely.
- **Subtle Termination Constraint in `prelude`:**
  As demonstrated in Section 3 of `SemanticsFuelOmnisemanticsComparisonProbe.lean`,
  a single-function clocked big-step interpreter `evalClocked ck stmt s` is
  **lexicographically** recursive on `(ck, sizeOf stmt)` (since `.seq s1 s2`
  preserves `ck` while shrinking `stmt`, whereas `.whileNonZero body` shrinks
  `ck` while preserving `.whileNonZero body`). In a `prelude` TCB without
  lexicographic `WellFounded.fix`, decomposing clocked evaluation into
  `evalStmtStep` (structural on `Stmt`) and `evalClocked` (structural on
  `ck : Nat`) restores pure structural recursion.
- **Limitation:** Functional big-step clocks are tailored to **deterministic**
  languages (or angelic oracle threads); they cannot directly express demonic
  propositional choice (`StepResult.choice (branches : State → Prop)`).

#### 3. Definitional Interpreters with Fuel

- **Amin & Rompf (POPL 2017); Siek (2013); Berghofer & Nipkow (2000); CompCert
  `Cexec` vs. `Clight` (Leroy, JAR 2009); Vellvm; `lean-mlir` / `riscv-lean`:**
  Amin & Rompf showed that type soundness for expressive type systems ($F_{<:}$,
  DOT) can be proved directly on a fuel-indexed definitional interpreter
  `eval (n : Nat) (e : Exp) : Result` by showing that for every $n$,
  `eval n e ≠ Stuck` (`Timeout` is treated as safe).
- **CompCert's Dual-Semantics Pattern:**
  CompCert uses **relational small-step semantics** (`Smallstep.v`, `Clight.v`)
  as its authoritative specification TCB (to support pointer/allocation
  non-determinism and C evaluation-order non-determinism), and provides a
  separate **executable fuel-driven reference interpreter** (`Cexec.v`) proved
  sound against the relational semantics for testing and `decide`-style symbolic
  evaluation.

#### 4. Coinductive and Free-Monad Semantics (`ITree`, `CTree`, Delay Monad)

- **Capretta (LMCS 2005) Delay Monad; Leroy & Grall (IC 2009) Coinductive
  Big-Step; Xia et al. (POPL 2020) Interaction Trees (`ITree`); Chappe et al.
  (POPL 2023) Choice Trees (`CTree`):**
  Coinductive trees (`itree E R := Ret r | Tau t | Vis e k`) represent
  divergent and interactive computations compositionally as values without a
  `Nat` step counter, supporting monadic `bind` and equational reasoning up to
  weak bisimulation (`eutt`).
- **Trade-offs for Lean 4 Verification TCBs:**
  1. Lean 4's kernel has **no native `coinductive` primitive** (unlike Rocq's
     `CoInductive` or Isabelle's `codatatype`); coinductive types in Lean 4 must
     be constructed as quotients of polynomial functors (`QPF`) or indexed
     approximations, pulling heavy library machinery and `Classical.choice` into
     the TCB.
  2. As Leroy & Grall (2009) proved, naive coinductive big-step semantics fails
     to propagate crashes inside divergent loops unless augmented with a separate
     coinductive divergence relation (`evalinf`).
  3. Aeneas (`Aeneas.Std.Result`) models pure Rust loops in Lean 4 using a finite
     sum `Result α := ok α | fail Error | div`, where `div` is synthesized via
     classical `WellFounded`/domain-theoretic fixpoints outside a `prelude` TCB.

#### 5. Inductive Omnisemantics and Predicate-Transformer Semantics

- **Charguéraud, Campbell, Ligtvoet, and collaborators (TOPLAS 2023); Schäfer et
  al. (2016); Nipkow:**
  Omnisemantics defines a single **inductive** big-step judgment
  $\text{OmniSem}(e, s, Q)$ asserting that starting from $(e, s)$, **every**
  nondeterministic execution path terminates safely in a state/value satisfying
  the postcondition set $Q : \text{State} \to \text{Val} \to \text{Prop}$
  (`OmniSem` in `SemanticsFuelOmnisemanticsComparisonProbe.lean:503-521`).
- **Why Omnisemantics Excels for Terminating Verification:**
  - *Zero fuel / zero step counters:* Proofs proceed by direct structural
    induction on the derivation tree of `OmniSem` (`ExecNormal`).
  - *Single derivation covers demonic non-determinism:* Unlike standard big-step
    semantics (which requires two separate judgments—one for reachability and
    one for safety), a single `OmniSem` derivation guarantees both that no
    branch gets stuck/faults and that every branch satisfies $Q$.
  - *Step-contracting & step-dilating simulations:* Compiler passes that change
    the number of steps (`lowerBody_simulates` in `theory/Anneal/Lowering.lean`)
    require zero step-counter arithmetic.
- **Boundary of Inductive Omnisemantics:**
  Because `OmniSem` is an **inductive** (least) fixpoint, any program with an
  infinite loop (`loop {}`) has **no finite derivation tree**, so `OmniSem`
  cannot distinguish safe silent divergence (`loop {}`) from undefined behavior
  (`.failed`). Consequently, `OmniSem`/`ExecNormal` belongs in `theory/` (for
  proving terminating functions and compiler lowering passes), whereas the TCB
  must retain `ReachesPrefix` + `eventualBehaviorOf` so safe infinite loops and
  reactive event loops remain verifiable.

#### 6. General Recursion Support Across Interactive Theorem Provers

| System | Primary Recursion Mechanisms | Kernel Primitive | TCB / Reduction Trade-offs |
| :--- | :--- | :--- | :--- |
| **Lean 4** (`v4.34.1`) | Structural (`brecOn`), `WellFounded.fix` / `WellFounded.Nat.fix`, `extrinsicFix`, `partial_fixpoint` (`CCPO`) | Only `Inductive.rec` is in the kernel; all others elaborate to `rec` + `Prop`/`Classical.choice` | `prelude` has only `rec`/`brecOn`; `WellFounded.fix` blocks symbolic kernel `whnf` unless `isNatLtWF`; `partial_fixpoint` uses `Classical.choose`. |
| **Rocq / Coq** | Structural `Fix` (kernel guard condition), `Function`, `Program Fixpoint`, `Equations` (Sozeau & Mangin, ICFP 2019), `CoFix` | Kernel `Fix` (syntactic subterm guard) and `CoFix` (productivity guard) | Kernel `Fix` unfolds on constructor arguments; `WellFounded` (`Fix_sub`) blocks `vm_compute`/`reflexivity` unless fuel or `Acc` generator tricks (`2^n` fuel) are used. |
| **Isabelle/HOL** | `primrec`, Krauss `function` package (inductive domain graph `f_dom`), Krauss `partial_function` (flat/tail-recursive `option`/`ccpo`) | Pure HOL definitions via Hilbert choice (`Eps`) and inductive sets | No kernel reduction (`simp` uses proved equational theorems `f.simps`); `partial_function (tailrec)` requires no fuel for tail-recursive interpreters. |
| **HOL4** | Slind `Hol_defn` (`Define` + `tgoal`), CakeML clocked `Define` | Well-founded recursion theorem (`WFrec`) over HOL relations | Clocked definitions (`ck : num`) discharge termination automatically in `Define` and yield unconditional `.simps` equations. |
| **Agda** | Structural termination matrix (Foetus), **Sized Types** (`Size`, `↑ i`, `∞`, Abel 2010) | Type-level `Size` indices on inductive/coinductive types | Sized types track structural depth in types without runtime `Nat` fuel, though Agda's `∞` size typing has historically required careful soundness restrictions. |

#### Master Comparison Matrix of Semantic Representations

| Criterion | Relational Step-Indexed (`ReachesPrefix`, Anneal TCB) | Functional Fuel (`evalFuel`) | Clocked Big-Step (`evalClocked`, CakeML) | Coinductive / `ITree` / `CTree` | Inductive Omnisemantics (`OmniSem` / `ExecNormal`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`prelude`-Only Lean 4 Kernel Compatibility** | **Yes** (`Nat` + inductive `Prop`) | **Yes** (`Nat` + function) | **Yes** (requires 2-layer `Stmt` + `ck` split in `prelude`) | **No** (requires QPF quotients + `Classical.choice`) | **Yes** (inductive `Prop`, **0 fuel**) |
| **Proving Safety of Infinite Loops (`loop {}`)** | **Yes** (induction on `steps : Nat` + `traj` witness) | **Yes** (induction on `fuel : Nat`) | **Yes** ($\forall \text{ck},\, \text{eval}(\text{ck}) = \text{timeout}$) | **Yes** (coinduction / bisimulation) | **No** (inductive derivation requires termination) |
| **Propositional Demonic Choice (`StepResult.choice`)** | **Yes** (native `branches : State → Prop`) | **No** (deterministic only) | **No** (deterministic / oracle only) | Requires `CTree` (`brD` nodes) | **Yes** (native `∀ s', branches s' → OmniSem s'`) |
| **Step-Contracting Lowering Simulation (`lowerBody_simulates`)** | Requires existential step dilation ($\exists n'$) | Requires fuel dilation ($\exists k'$) | Preserves loop clock if only straight-line `goto`s contract | Up-to-tau bisimulation (`eutt`) | **Exact structural induction (0 step arithmetic)** |
| **Symbolic Evaluation via `decide` / `rfl`** | Via `evalFuel` / `ExecNormal` bridge | **Direct** (`rfl` / `decide`) | **Direct** (`rfl` / `decide`) | Blocked by quotient / coinduction | Via deterministic step unfolding (`execStep`) |

## Boundaries

1. **`AdmissibleAdtInv` Negative-Position Invariant:** Anneal's current
   `AdmissibleAdtInv` (`Trusted/MirSemantics.lean:1120-1126` at
   `4a7bcfdcc0f50274edd5874ba9b204cc2dac7032`) is sound for arbitrary `.ref`
   nesting depths **because** `validStep` recurses structurally on `MirTy` for
   `.ref inner` and only `validFuel` consumes fuel (`adts.length + 1`) on
   `.adt id` unfoldings. If any future extension to `MirTy` adds a type
   constructor (such as tuples, arrays, or slices) to `validStep`, that
   constructor **must** recurse via `validStep` (structural on `MirTy`, 0 fuel),
   **never** via `unfold` (`validFuel`), or else deep nesting of that
   constructor inside a `pub` safe struct will re-introduce the contravariant
   vacuity exploit proved in `admissibleAdtInvCoupled_vacuous_arbitrary`.
2. **`returnRefsOk` Hop Bound (`fuel = 5`):** `MirVal.returnRefsOk`
   (`Trusted/MirSemantics.lean:352-354`) uses `returnRefsFuel s localCount 5 v`,
   which is structural on `.adt` wrappers (`0` fuel) and allows up to 4 nested
   `.ref` dereference hops at `Terminator.return_`. Because `returnRefsOk` sits
   exclusively in a positive operational position (returning `false` transitions
   to `StepResult.failed`), this bound cannot cause soundness vacuity, but a
   function returning a $\ge 5$-deep reference (`&&&&&T`) will fail verification
   unless `returnRefsOk` is refactored to recurse structurally on `active.retTy : MirTy`.
3. **Scope of `ExecNormal`:** `ExecNormal` (`theory/Anneal/Lowering.lean:34-44`)
   intentionally models only deterministic, silent (`ev = []`), normally
   terminating executions; functions that unwind (`.unwind`), diverge silently
   (`.diverges`), or emit reactive traces (`.reacts`) must use `ReachesPrefix`
   and `eventualBehaviorOf` directly (or an extended omnisemantics with unwind
   postconditions).

## Evidence

- **Self-Contained Lean 4.34.1 Mechanized Probes (`support/`):**
  - `support/AnnealFuelPolarityAndRecursionProbe.lean` (kernel-checked under
    `prelude` with `elan run leanprover/lean4:v4.34.1 lean`):
    - `fuel_positive_sound`, `fuel_negative_weakens`,
      `fuel_exhaustion_vacuous_antecedent`, `nonVacuous_blocks_total_exhaustion`,
      `partial_exhaustion_bypasses_nonvacuity` (Lines 35-101)
    - `findFrameFueled_eq_listFind` (Lines 193-199)
    - `validCoupled_ref3_always_false`, `admissibleAdtInvCoupled_vacuous_arbitrary`,
      `admissibleAdtInvCoupled_accepts_false` (Lines 261-331)
    - `valid_ref3_holds`, `not_admissibleAdtInv_false`,
      `validStep_refChain_next_irrelevant`, `validFuel_refChain_fuel_irrelevant`
      (Lines 402-462)
    - `returnRefsFuel_adt_depth_invariant` (Lines 524-532)
    - `beqMirBodyFuel_not_refl`, `beqMirBodyFlat_refl`, `beqMirBodyFlat_eq_iff`
      (Lines 555-583)
    - `tySize_usize_symbolic_rfl`, `tySize_ref_chain_symbolic_rfl`,
      `right_add_two_defeq_succ_succ`, `tySizeLeftAdd_eq_tySize` (Lines 624-656)
  - `support/SemanticsFuelOmnisemanticsComparisonProbe.lean` (kernel-checked
    under `prelude` with `elan run leanprover/lean4:v4.34.1 lean`):
    - `silentLoop_reaches_running`, `silentLoop_safe_and_diverges`,
      `demonicStep_reaches_failed` (Lines 154-224)
    - `evalFuel_to_reachesPrefix`, `reachesPrefix_to_evalFuel` (Lines 255-320)
    - `evalStmtStep_mono`, `evalClocked_mono`, `whileSkip_diverges_all_clocks`
      (Lines 385-483)
    - `OmniSem`, `ExecNormal`, `evalFuel_to_execNormal`,
      `execNormal_iff_exists_reachesPrefix` (Lines 503-582)
    - `coalesceGoto_simulates_execNormal`,
      `coalesceGoto_simulates_reachesPrefix_dilated` (Lines 613-695)
- **Anneal Source Citations (`joshlf/anneal`):**
  - `trusted/lean/Trusted/Refinement.lean:51-195` (`Language.Verified`,
    `SpecOn`, `NonVacuousOn`, `ProductiveOn`) at
    `4a7bcfdcc0f50274edd5874ba9b204cc2dac7032`
  - `trusted/lean/Trusted/StepResult.lean:33-164` (`StepResult`, `ReachesPrefix`,
    `EventualOut`, `eventualBehaviorOf`) at
    `4a7bcfdcc0f50274edd5874ba9b204cc2dac7032`
  - `trusted/lean/Trusted/MirAst.lean:38-328` (`MirTy`, `AdtDecl`, `BodyId`,
    `MirBody`, `BodyDecl`, `Crate`) at
    `4a7bcfdcc0f50274edd5874ba9b204cc2dac7032`
  - `trusted/lean/Trusted/MirSemantics.lean:151-1234` (`MirBody.subst`,
    `tySizeStep`, `tySizeFuel`, `evalTyByteSize`, `MirVal.isFullyInit`,
    `resolveRef`, `returnRefsStep`, `returnRefsFuel`, `validStep`,
    `MirVal.validFuel`, `MirVal.valid`, `evalProj`, `extractTransmuteBits`,
    `constructTransmuteVal`, `AdmissibleAdtInv`, `EnsuresRetLibInv`,
    `CrateTheorem`) at `4a7bcfdcc0f50274edd5874ba9b204cc2dac7032`
  - `theory/Anneal/Lowering.lean:34-605` (`ExecNormal`, `lowerBody_simulates`)
    and `theory/Anneal/MirLemmas.lean:583-617, 3763-3770`
    (`execNormal_safeAndEnsures`, `beqMirBody`) at
    `4a7bcfdcc0f50274edd5874ba9b204cc2dac7032`
  - Historical baselines: `5a48fba09794839a06cee0bc4fa56f98f1fbb38e`
    (`theory/Anneal/MirLemmas.lean:3549-3609`, `beqMirBodyFuel 8`) and
    `ebac418ccf7c234ae402cf76a491c903bff3be4f`
    (`trusted/lean/Trusted/MirSemantics.lean:106-175, 259-318`, `@Nat.rec` and
    `@MirVal.rec`)
- **Lean 4 Toolchain Citations (`leanprover/lean4` at
  `5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):**
  - `src/lean/Init/Prelude.lean:1773-1775` (`Nat.add` right-recursion)
  - `src/lean/Init/Data/List/Basic.lean:1617-1621` (`List.find?`)
  - `src/lean/Init/WF.lean:14-240` (`Acc`, `WellFounded.fix`, `Nat.lt_wfRel`)
  - `src/lean/Init/WFComputable.lean:1-98` (`Acc.recC`, `WellFounded.Nat.fix`)
  - `src/lean/Init/Internal/Order/Basic.lean:105-106` (`CCPO.csup` via
    `Classical.choose`)
  - `src/lean/Lean/Elab/PreDefinition/WF/Main.lean:62-69` (`WellFounded.fix`
    irreducibility policy)

## Revalidation

Run the self-contained Lean 4.34.1 kernel probes from the package root:

```bash
anneal-lean-run --mode file --concurrency 1 -- \
  elan run leanprover/lean4:v4.34.1 lean \
  reports/fuel-step-indexing-clocks-and-tcb-recursion-2026/support/AnnealFuelPolarityAndRecursionProbe.lean

anneal-lean-run --mode file --concurrency 1 -- \
  elan run leanprover/lean4:v4.34.1 lean \
  reports/fuel-step-indexing-clocks-and-tcb-recursion-2026/support/SemanticsFuelOmnisemanticsComparisonProbe.lean
```

Both commands must exit with status `0` and produce zero warnings or errors.
