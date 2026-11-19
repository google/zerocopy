# Lean 4 Std.Do Conjunctive Weakest Preconditions and Pure Init.* Distillation

## Summary

Lean 4 `v4.34.1` (`leanprover/lean4` commit `5045d0056413266e57c625dcd7c365b10e377c52`) ships two monadic weakest-precondition frameworks descended from `sgraf812/mpl` (`1dbf6bc75ff5398f59b77ae320f1f0a0781b721e`): public `Std.Do` (curried `SPred σs := SVal σs (ULift Prop)`, `PostShape`, `PredTrans.Conjunctive`, `Triple.mp`, and experimental `mvcgen`) and redesigned `Std.Internal.Do` (`CompleteLattice` flat `Pred`/`EPred`, per-program `WPConjunctive`, `WP.Frames`, frame-free `isConjunctiveInPosts`, `vcgen`, and `requires`/`ensures` elaboration). Importing either into Anneal `theory/` (`joshlf/anneal` commit `c131b320eeeb26ef692e5afd5ec8db49ee518613`) fails Pass 1 (`TrustedBoundary.lean`): `theory/` is locked to 51 `Init.*` modules (`foundation-lock.json`), forbidding `Std.*`, `Lean.*`, `Init.Internal.Order`, `module`/`public import`, metaprogramming syntax (`scoped syntax`, `macro_rules`, `do`), `@[expose]`/`@[ext]`/`@[spec]`/`@[grind =]`, `grind`/`conv`/`simpa`/`solve_by_elim`, and `CCPO.csup`'s `Classical.choice`. Moreover, `Std.Do.SPred`'s curried `SVal`/`ULift Prop` forces `@[reducible]` unrolling, lacks working `@[simp]` congruence over `entails_cons`, and relies on manual semi-reducibility wrappers (`PredTrans.apply`) plus elaboration postponement tricks (`post⟨...⟩`).

Distilling the algebraic core of both stacks into pure `Init.Core` + `Init.Data.Nat.Basic` yields a zero-axiom, zero-`ULift`, zero-macro conjunctive weakest-precondition layer (`wpOutcome` / `wlpOutcome`) compatible with `Anneal.MirWp.wpOutcomeState`. Its key payoff is **Two-Pass Demonic Modus Ponens** (`wpOutcome_mp_wlp` and `wpOutcome_mp_max`): under demonic choice (`∀ c, validChoice s c → ...`), weakest preconditions preserve conjunction (`wpOutcome_and_iff`). An automated **Pass A** can thus prove total UB-freedom, all-path termination, and bounds invariants (`wpOutcome sys Q₁ (fun _ => False) f₁ s`), while a decoupled **Pass B** proves only conditional functional postconditions (`wlpOutcome sys (fun o => Q₁ o → Q₂ o) (fun _ => True) f₂ s` at `f₁ ≤ f₂`) without re-proving choice inhabitedness (`∃ c₀, validChoice s c₀`) or overflow guards. Because `wpOutcome` (`0 ↦ False`) is covariant in fuel whereas `wlpOutcome` (`0 ↦ True`) is contravariant, dropping `f₁ ≤ f₂` is unsound (`doneOneSys`), and switching to angelic choice (`∃ c`) breaks conjunctivity (`angelicTwoSys`).

## Applicability

This report relates three pinned upstream artifacts to define how `Std.Do` / `Std.Internal.Do` algebra transfers into Anneal's Pass 1 `theory/` layer:

- **`leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** Source for `src/Std/Do/*`, `src/Std/Internal/Do/*`, `src/Lean/Elab/Tactic/Do/*`, and `src/Init/Internal/Order/Basic.lean`; covers `v4.34.1` (internal experimental `Std.Internal.Do` APIs may shift across releases).
- **`sgraf812/mpl` (`1dbf6bc75ff5398f59b77ae320f1f0a0781b721e`):** Prototype extracted into Lean 4 core (`Std/Do/*.lean` carries Sebastian Graf / Lean FRO authorship; `Lean.Elab.Tactic.Do.Spec` preserves 2022 `SPred` combinators by Lars König and Mario Carneiro).
- **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Authority for Pass 1 checks (`trusted/audit/TrustedBoundary.lean`, `trusted/lean/foundation-lock.json`, `lean-toolchain` pinning `v4.34.1`), operational semantics (`trusted/lean/Trusted/MirSemantics.lean`), and MIR WP (`theory/Anneal/MirWp.lean`).

Cross-corpus scope: kernel replay throughput, GMP scaling, Lean metaprogramming isolation, Aeneas `ITree` tactics, and fuel-free `PureLift` borrowing are covered in `aeneas-lean-backend-generated-signatures-and-wp-proof-tools`, `anneal-fuel-free-mir-lifting-and-alias-erasure`, `lean-elaboration-metaprogramming-import-isolation-and-kernel-audit`, and `lean-kernel-derivation-scale-checking-and-reflection-throughput`. Designs are evaluated on: **(T1)** 0-TCB statement-origin separation from `Anneal.*`; **(P1)** spec auditability; **(P2)** Pass A / Pass B locality; **(P3)** Lean `v4.34.1` kernel / `<50ms` LSP scaling; **(P4)** composability across `MirWp`, deterministic `c = 0`, demonic choice, and faults; **(P5)** failure legibility; and **(C1–C2)** conceptual minimality with refutation counterexamples.

## Findings

### 1. Dual Program-Logic Stacks in Lean 4 `v4.34.1` (`Std.Do` vs. `Std.Internal.Do`)

Basis: source + documentation

Lean 4 `v4.34.1` maintains two parallel monadic WP frameworks under `src/Std/Do/` and `src/Std/Internal/Do/`:

1. **Public `Std.Do` (`SVal`/`SPred` + `PostShape` + `PredTrans` + `mvcgen`):**
   - `Std.Do.SVal` (`SPred/SVal.lean` L30–32) curries predicates by structural recursion over `σs : List (Type u)`, paired with `StateTuple`/`curry`/`uncurry`/`GetTy` (L43–89); `Std.Do.SPred` (`SPred/SPred.lean` L34) wraps `ULift Prop`:
     ```lean
     abbrev SVal (σs : List (Type u)) (α : Type u) : Type u := match σs with
       | [] => α
       | σ :: σs => σ → SVal σs α
     abbrev SPred (σs : List (Type u)) : Type u := SVal σs (ULift Prop)
     ```
     Every connective (`pure`, `entails`, `bientails`, `and`, `or`, `not`, `imp`, `iff`, `exists`, `forall`, `conjunction`, `SPred.lean` L52–155) recurses on `σs` and strips/applies `ULift`.
   - `Std.Do.PostShape` (`PostCond.lean` L54–66) indexes monad stacks (`.pure | .arg σ PostShape | .except ε PostShape`), with `Assertion ps := SPred (PostShape.args ps)` (L75–94) and `PostCond α ps` pairing `(α → Assertion ps)` with `ExceptConds ps` (L107–110, L317–318), plus pointwise `⊢ₚ`/`∧ₚ`/`→ₚ` (L365–423).
   - `Std.Do.PredTrans` (`PredTrans.lean` L41–79) pairs `trans : PostCond α ps → Assertion ps` with `conjunctiveRaw : ∀ Q₁ Q₂, trans (Q₁ ∧ₚ Q₂) ⊣⊢ₛ trans Q₁ ∧ trans Q₂`, deriving `PredTrans.Conjunctive.mono` (L52–56) from conjunctivity. `WP`/`WPMonad` (`WP/Basic.lean` L54–56, `WP/Monad.lean` L36–41) mandate strict equations (`wp (pure a) = pure a`, `wp (x >>= f) = wp x >>= fun a => wp (f a)`).
   - `Std.Do.Triple` (`Triple/Basic.lean` L37–128) defines `Triple x P Q := P ⊢ₛ wp⟦x⟧ Q` alongside `Triple.and` (L101–102), `Triple.mp` (L110–111, combining `P₁ ⊢ₛ wp⟦x⟧ Q₁` and `P₂ ⊢ₛ wp⟦x⟧ (Q₁ →ₚ Q₂)` via `(wp x).conjunctive` + `PostCond.and_imp`), and `Triple.observe` (L119–128). Note `mvcgen` warns at runtime (`VCGen.lean` L455–456: `"The \`mvcgen\` tactic is experimental and still under development. Avoid using it in production projects."`).

2. **Redesigned `Std.Internal.Do` (`CompleteLattice` + `WPConjunctive` + `WP.Frames` + `vcgen`):**
   - Drops `SVal`, `SPred`, `ULift Prop`, and baked-in conjunctivity: `Assertion Pred` requires `Lean.Order.CompleteLattice Pred` (`Internal/Do/Assertion.lean` L31; `Init.Internal.Order.Basic`), and `PredTrans Pred EPred α` (`Internal/Do/PredTrans.lean` L44–46) is an unbundled mapping `apply : (α → Pred) → EPred → Pred`.
   - `WP` moves monotonicity to `WP.wp_trans_monotone` (`Internal/Do/WP/Basic.lean` L62–67), and `WPMonad` relaxes strict equations (`=`) to lattice inequalities (`post x ⊑ wp (pure x) post epost` and `wp x (fun a => wp (f a) post epost) epost ⊑ wp (x >>= f) post epost`, L79–90).
   - Conjunctivity becomes per-program `WPConjunctive x` (`Internal/Do/WP/Conjunctive.lean` L23–110): `wp x Q₁ E₁ ⊓ wp x Q₂ E₂ ⊑ wp x (Q₁ ⊓ Q₂) (E₁ ⊓ E₂)` lifted across `StateT`/`ReaderT`/`OptionT`/`ExceptT`.
   - `WP.Frames` (`Internal/Do/WP/Frame.lean` L31–85) internalizes framing via `WP.Frames.of_conjunctive`: invariant preservation (`∀ E, F ⊑ wp x (fun _ => F) E`) implies automatic framing of `(F ⊓ ·)`. In tactics, `isConjunctiveInPosts` (`ConjunctivePre.lean` L15–155) syntactically checks when spec preconditions use `Q` strictly under conjunctive positions (`wp`, `⊓`, `∧`, `⨅`, `⇨` consequent, `EPost.Cons.head`, `λ`) to bypass manual frame inference in `vcgen`.

| Aspect | Public `Std.Do` (`mvcgen`) | `Std.Internal.Do` (`vcgen`) | Pure `Init.*` Distillation (`theory/`) |
| :--- | :--- | :--- | :--- |
| Carrier | Curried `SVal σs (ULift Prop)` | `CompleteLattice Pred` (`Prop`, `σ → Prop`) | Flat `State → Prop` (`Nat`-indexed fuel) |
| Exits | `PostShape` + `ExceptConds` | `EPost.Cons` (`EPred`) | Direct `(onDone : Out → Prop)` & `(onFault : Fault → Prop)` |
| Conjunctivity | Baked in `PredTrans.conjunctiveRaw` (`⊣⊢ₛ`) | Typeclass `WPConjunctive` (`⊓`/`⊑`) | Standalone `wpOutcome_and_iff` & `wpOutcome_mp_wlp` |
| Monad / step laws | Strict `=` (`@ext` + `funext`) | Lattice inequalities (`⊑`) | Recursive `@Nat.rec` structural unfolding |
| Framing | `HasFrame` search + `mTryFrame` | `WP.Frames` + `isConjunctiveInPosts` | `wpOutcome_frame_of_inv` + `@[irreducible]` cut walls |
| Syntax / macros | `mvcgen`, `spred(...)`, `post⟨...⟩` | `vcgen`, `requires`/`ensures` | Zero macros/elabs; pure Pass 1 kernel terms |

### 2. Kernel Reduction & Elaboration Pathology of Curried `ULift Prop` (`SPred σs`)

Basis: source + derived

Direct inspection identifies five concrete bottlenecks in `SPred σs := SVal σs (ULift Prop)`:
1. **Mandatory `@[reducible]` Unfolding (`SVal.lean` L30–38):** Lifting `Prop` via `ULift.{u}` and matching on `σs : List (Type u)` forces `SVal` to stay `abbrev`: `SVal.lean` L35–38 documents `"We need SVal to be reducible, otherwise type inference fails for Triple. This is tracked in #8074. There is a fix in #9015, but it regresses Mathlib."` Every unification step therefore expands `PostShape.args` and `SVal`.
2. **Broken `@[simp]` Normal Forms (`SPred.lean` L73–74):** `entails_cons` cannot simplify under `@[simp]`, forcing fixed-arity duplicates `entails_1`..`entails_5` and quadratic `HasFrame`/`SimpAnd` typeclass searches (`DerivedLaws.lean` L292–338).
3. **Manual Semi-Reducible Wrappers & Postponement (`PredTrans.lean` L77–79, `PostCond.lean` L321–324, `Spec.lean` L192–235):** Unfolding `PredTrans.trans` bloated kernel `isDefEq`, requiring a semi-reducible `PredTrans.apply` wrapper, `by exact ⟨...⟩` postponement in `post⟨...⟩`, and `.syntheticOpaque` MVars unified via `fullApproxDefEq` in `mSpec`.
4. **`elimLets` Delayed-Assignment Bug (`VCGen.lean` L481–483):** Running `elimLets` after VC generation breaks delayed MVars in `mkFreshPair_triple`, forcing `mvcgen` to preserve join-point `let` bindings.
5. **Curried Closures & `funext`/`propext`:** Each `SPred.and` allocates $k$ nested lambdas around `ULift.up`, and `Triple.mp` invokes `bientails.to_eq` (`funext` × $k$ + `propext`, `SPred/Laws.lean` L73–77). Flat `State → Prop` eliminates currying, `ULift`, and `funext` while matching `Anneal.MirWp.wpOutcomeState` directly.

### 3. Complete Pass 1 Rejection Matrix Against `TrustedBoundary.lean` and `foundation-lock.json`

Basis: normative + source

Anneal's Pass 1 checker (`TrustedBoundary.lean`) enforces pure `Init.*` theory isolation (`trustLevel := 0`) via parser whitelists (`L437–995`) and `.olean` / axiom / replay validation (`audit`, `L1522–1558`), unlike Pass 2 (`correspondence/`), which admits `.sysrootFoundation` inside `bwrap` (`L1560–1576`). Both Lean stacks violate every Pass 1 gate:

| Pass 1 Gate (`TrustedBoundary.lean`) | Requirement | Violation in `Std.Do` / `Std.Internal.Do` | Primary Anchors |
| :--- | :--- | :--- | :--- |
| **Foundation Imports** (`L442`, `foundation-lock.json`) | 51 locked `Init.*` modules only. | Uses `Std.*`, `Lean.*`, `Init.Internal.Order`, `Init.Ext`, `Init.Control.Lawful`, `Init.Data.List.TakeDrop`. | `foundation-lock.json` L22–1335; `PredTrans.lean` L9–10; `Internal/Do/Assertion.lean` L9 |
| **Header Syntax** (`L442`, `L658–660`, `L984–986`) | `prelude` + plain `import` (`isExported=true`, non-`meta`). | Uses `module`, `public import`, `meta import`, `import all`, `@[expose] public section`. | `PredTrans.lean` L6–12; `SPred/Notation.lean` L9; `Internal/Do/WP/Basic.lean` L6–11 |
| **Command Syntax** (`L448–453`) | Pure decls, `namespace`/`section`/`open`/`variable`/`attribute`/`mutual`. | Uses `set_option`, `scoped syntax`, `macro_rules`, `builtin_initialize`, `open scoped`. | `PredTrans.lean` L14; `Triple/Basic.lean` L41, L47; `Contract.lean` L140 |
| **Term Syntax** (`L493–517`) | No `do`, syntax quotations, or `byElab`. | Uses quotations, `do`, and `meta def` unexpanders. | `Triple/Basic.lean` L47–50; `PostCond.lean` L321–350 |
| **Tactic Allowlist** (`L536–557`) | Closed 22-tactic set (`apply`, `cases`, `change`, `dsimp`, `exact`, `funext`, `induction`, `injection`, `intro`, `refine`, `rw`, `simp`, `subst`, `unfold`, etc.). | Uses `grind`, `conv`, `simpa`, `simp_all`, `solve_by_elim`, `obtain`, `split`, `exists`, `calc`, `mvcgen`, `vcgen`. | `PredTrans.lean` L120, L247; `Internal/Do/WP/Basic.lean` L137, L413; `DerivedLaws.lean` L270 |
| **Attributes** (`L594–595`, `L680–693`) | Bare `@[simp]`, `@[instance]`, `@[reducible]`, `@[semireducible]`, `@[irreducible]`. | Uses `@[expose]`, `@[ext]`, `@[refl]`, `@[grind =]`, `@[spec]`, `@[app_unexpander]`, `(priority := ...)`. | `PredTrans.lean` L91, L140; `Internal/Do/PredTrans.lean` L226; `WP/Basic.lean` L211 |
| **Axioms & `noncomputable`** (`L1136–1153`) | Only `{propext, Quot.sound, Classical.choice}`; zero `partial`/`unsafe`/`._unsafe_rec`. | `Init.Internal.Order.CCPO.csup` and `Internal.Do.Order` invoke `Classical.choose` unconditionally on `Prop`. | `Init/Internal/Order/Basic.lean` L105–109; `Internal/Do/Order/Basic.lean` L31–89 |

### 4. Pure `Init.*` 0-Axiom Distillation: Conjunctive WP, Two-Pass Modus Ponens, and Implicit Framing

Basis: source + derived

`Anneal.MirWp.wpOutcomeState` (`theory/Anneal/MirWp.lean` L69–80) already uses structural `@Nat.rec (fun _ => State → Prop)` to avoid `._unsafe_rec` and `ULift Prop`, quantifying universally over `ValidChoice p st c` while requiring `(∃ c₀ : Choice, ValidChoice p st c₀)`. However, `MirWp.lean` (`c131b320eeeb`) currently contains only strong `wpOutcomeState` (`0 ↦ False`), deterministic `execOutcomeState` (L112–121), monotonicity (`wpOutcomeState_mono` L243–276, `wpOutcomeState_fuel_mono` L280–313), and `wellFormed_and_spec_of_wp` (L429–455); it lacks liberal `wlpOutcome`, conjunction distribution, two-pass modus ponens, and implicit invariant framing.

The complete self-contained Pass-1 distillation below imports only `Init.Core` and `Init.Data.Nat.Basic`, uses zero axioms (`propext`-free, `Classical.choice`-free), obeys `allowedTheoryTacticKinds`, and includes concrete counterexamples calibrating fuel variance and choice quantifiers:

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic

namespace Pass1ConjunctiveWpProbe

inductive StepResult (State Out Fault : Type) where
  | step (next : State) | done (out : Out) | fault (err : Fault)

structure TransitionSystem (State Choice Out Fault : Type) where
  validChoice : State → Choice → Prop
  evalStep : Choice → State → StepResult State Out Fault

/-- Strong total-correctness transformer (`0 ↦ False`), matching `Anneal.MirWp.wpOutcomeState`. -/
def wpOutcome {State Choice Out Fault : Type}
    (sys : TransitionSystem State Choice Out Fault)
    (onDone : Out → Prop) (onFault : Fault → Prop)
    (fuel : Nat) (s : State) : Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun _ => False)
    (fun _ ih st =>
      (Exists fun c0 : Choice => sys.validChoice st c0) ∧
      ∀ c : Choice, sys.validChoice st c →
        match sys.evalStep c st with
        | .step st' => ih st' | .done out => onDone out | .fault err => onFault err)
    fuel s

/-- Weakest liberal precondition (`0 ↦ True`, omitting repeated choice inhabitedness). -/
def wlpOutcome {State Choice Out Fault : Type}
    (sys : TransitionSystem State Choice Out Fault)
    (onDone : Out → Prop) (onFault : Fault → Prop)
    (fuel : Nat) (s : State) : Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun _ => True)
    (fun _ ih st =>
      ∀ c : Choice, sys.validChoice st c →
        match sys.evalStep c st with
        | .step st' => ih st' | .done out => onDone out | .fault err => onFault err)
    fuel s

theorem wpOutcome_mono {State Choice Out Fault : Type}
    {sys : TransitionSystem State Choice Out Fault}
    {onDone1 onDone2 : Out → Prop} {onFault1 onFault2 : Fault → Prop}
    (hDone : ∀ o, onDone1 o → onDone2 o) (hFault : ∀ k, onFault1 k → onFault2 k) :
    ∀ {fuel : Nat} {s : State},
      wpOutcome sys onDone1 onFault1 fuel s → wpOutcome sys onDone2 onFault2 fuel s
  | 0, _, h => False.elim h
  | fuel + 1, s, h => by
    change ((Exists fun c0 => sys.validChoice s c0) ∧ ∀ c, sys.validChoice s c →
      match sys.evalStep c s with | .step st' => wpOutcome sys onDone1 onFault1 fuel st' | .done o => onDone1 o | .fault k => onFault1 k) at h
    change ((Exists fun c0 => sys.validChoice s c0) ∧ ∀ c, sys.validChoice s c →
      match sys.evalStep c s with | .step st' => wpOutcome sys onDone2 onFault2 fuel st' | .done o => onDone2 o | .fault k => onFault2 k)
    refine ⟨h.1, fun c hc => ?_⟩; have hc' := h.2 c hc
    cases hStep : sys.evalStep c s with
    | step st' => rw [hStep] at hc'; exact wpOutcome_mono hDone hFault hc'
    | done o => rw [hStep] at hc'; exact hDone o hc'
    | fault k => rw [hStep] at hc'; exact hFault k hc'

theorem wpOutcome_fuel_mono {State Choice Out Fault : Type}
    {sys : TransitionSystem State Choice Out Fault}
    {onDone : Out → Prop} {onFault : Fault → Prop} :
    ∀ {f1 f2 : Nat} {s : State},
      f1 ≤ f2 → wpOutcome sys onDone onFault f1 s → wpOutcome sys onDone onFault f2 s
  | 0, _, _, _, h => False.elim h
  | f1 + 1, 0, _, hLe, _ => False.elim (Nat.not_succ_le_zero f1 hLe)
  | f1 + 1, f2 + 1, s, hLe, h => by
    have hLe' := Nat.le_of_succ_le_succ hLe
    change ((Exists fun c0 => sys.validChoice s c0) ∧ ∀ c, sys.validChoice s c →
      match sys.evalStep c s with | .step st' => wpOutcome sys onDone onFault f1 st' | .done o => onDone o | .fault k => onFault k) at h
    change ((Exists fun c0 => sys.validChoice s c0) ∧ ∀ c, sys.validChoice s c →
      match sys.evalStep c s with | .step st' => wpOutcome sys onDone onFault f2 st' | .done o => onDone o | .fault k => onFault k)
    refine ⟨h.1, fun c hc => ?_⟩; have hc' := h.2 c hc
    cases hStep : sys.evalStep c s with
    | step st' => rw [hStep] at hc'; exact wpOutcome_fuel_mono hLe' hc'
    | done o => rw [hStep] at hc'; exact hc'
    | fault k => rw [hStep] at hc'; exact hc'

theorem wlpOutcome_fuel_anti {State Choice Out Fault : Type}
    {sys : TransitionSystem State Choice Out Fault}
    {onDone : Out → Prop} {onFault : Fault → Prop} :
    ∀ {f1 f2 : Nat} {s : State},
      f1 ≤ f2 → wlpOutcome sys onDone onFault f2 s → wlpOutcome sys onDone onFault f1 s
  | 0, _, _, _, _ => trivial
  | f1 + 1, 0, _, hLe, _ => False.elim (Nat.not_succ_le_zero f1 hLe)
  | f1 + 1, f2 + 1, s, hLe, h => by
    have hLe' := Nat.le_of_succ_le_succ hLe
    change (∀ c, sys.validChoice s c →
      match sys.evalStep c s with | .step st' => wlpOutcome sys onDone onFault f2 st' | .done o => onDone o | .fault k => onFault k) at h
    change (∀ c, sys.validChoice s c →
      match sys.evalStep c s with | .step st' => wlpOutcome sys onDone onFault f1 st' | .done o => onDone o | .fault k => onFault k)
    intro c hc; have hc' := h c hc
    cases hStep : sys.evalStep c s with
    | step st' => rw [hStep] at hc'; exact wlpOutcome_fuel_anti hLe' hc'
    | done o => rw [hStep] at hc'; exact hc'
    | fault k => rw [hStep] at hc'; exact hc'

theorem wpOutcome_and_iff {State Choice Out Fault : Type}
    {sys : TransitionSystem State Choice Out Fault}
    {Q1 Q2 : Out → Prop} {F1 F2 : Fault → Prop} :
    ∀ {fuel : Nat} {s : State},
      wpOutcome sys (fun o => Q1 o ∧ Q2 o) (fun k => F1 k ∧ F2 k) fuel s ↔
      (wpOutcome sys Q1 F1 fuel s ∧ wpOutcome sys Q2 F2 fuel s)
  | 0, _ => ⟨fun h => False.elim h, fun h => False.elim h.1⟩
  | fuel + 1, s => by
    constructor
    · intro h
      exact ⟨wpOutcome_mono (fun _ hq => hq.1) (fun _ hf => hf.1) h,
             wpOutcome_mono (fun _ hq => hq.2) (fun _ hf => hf.2) h⟩
    · intro h; have h1 := h.1; have h2 := h.2
      change ((Exists fun c0 => sys.validChoice s c0) ∧ ∀ c, sys.validChoice s c →
        match sys.evalStep c s with | .step st' => wpOutcome sys Q1 F1 fuel st' | .done o => Q1 o | .fault k => F1 k) at h1
      change ((Exists fun c0 => sys.validChoice s c0) ∧ ∀ c, sys.validChoice s c →
        match sys.evalStep c s with | .step st' => wpOutcome sys Q2 F2 fuel st' | .done o => Q2 o | .fault k => F2 k) at h2
      change ((Exists fun c0 => sys.validChoice s c0) ∧ ∀ c, sys.validChoice s c →
        match sys.evalStep c s with | .step st' => wpOutcome sys (fun o => Q1 o ∧ Q2 o) (fun k => F1 k ∧ F2 k) fuel st' | .done o => Q1 o ∧ Q2 o | .fault k => F1 k ∧ F2 k)
      refine ⟨h1.1, fun c hc => ?_⟩; have b1 := h1.2 c hc; have b2 := h2.2 c hc
      cases hStep : sys.evalStep c s with
      | step st' => rw [hStep] at b1 b2; exact (wpOutcome_and_iff).mpr ⟨b1, b2⟩
      | done o => rw [hStep] at b1 b2; exact ⟨b1, b2⟩
      | fault k => rw [hStep] at b1 b2; exact ⟨b1, b2⟩

/-- Asymmetric Two-Pass Modus Ponens (`f1 ≤ f2` required). -/
theorem wpOutcome_mp_wlp {State Choice Out Fault : Type}
    {sys : TransitionSystem State Choice Out Fault}
    {Q1 Q2 : Out → Prop} {F1 F2 : Fault → Prop} :
    ∀ {f1 f2 : Nat} {s : State},
      f1 ≤ f2 →
      wpOutcome sys Q1 F1 f1 s →
      wlpOutcome sys (fun o => Q1 o → Q2 o) (fun k => F1 k → F2 k) f2 s →
      wpOutcome sys (fun o => Q1 o ∧ Q2 o) (fun k => F1 k ∧ F2 k) f1 s
  | 0, _, _, _, h1, _ => False.elim h1
  | f1 + 1, 0, _, hLe, _, _ => False.elim (Nat.not_succ_le_zero f1 hLe)
  | f1 + 1, f2 + 1, s, hLe, h1, h2 => by
    have hLe' := Nat.le_of_succ_le_succ hLe
    change ((Exists fun c0 => sys.validChoice s c0) ∧ ∀ c, sys.validChoice s c →
      match sys.evalStep c s with | .step st' => wpOutcome sys Q1 F1 f1 st' | .done o => Q1 o | .fault k => F1 k) at h1
    change (∀ c, sys.validChoice s c →
      match sys.evalStep c s with | .step st' => wlpOutcome sys (fun o => Q1 o → Q2 o) (fun k => F1 k → F2 k) f2 st' | .done o => Q1 o → Q2 o | .fault k => F1 k → F2 k) at h2
    change ((Exists fun c0 => sys.validChoice s c0) ∧ ∀ c, sys.validChoice s c →
      match sys.evalStep c s with | .step st' => wpOutcome sys (fun o => Q1 o ∧ Q2 o) (fun k => F1 k ∧ F2 k) f1 st' | .done o => Q1 o ∧ Q2 o | .fault k => F1 k ∧ F2 k)
    refine ⟨h1.1, fun c hc => ?_⟩; have b1 := h1.2 c hc; have b2 := h2 c hc
    cases hStep : sys.evalStep c s with
    | step st' => rw [hStep] at b1 b2; exact wpOutcome_mp_wlp hLe' b1 b2
    | done o => rw [hStep] at b1 b2; exact ⟨b1, b2 b1⟩
    | fault k => rw [hStep] at b1 b2; exact ⟨b1, b2 b1⟩

theorem wpOutcome_mp_max {State Choice Out Fault : Type}
    {sys : TransitionSystem State Choice Out Fault}
    {Q1 Q2 : Out → Prop} {F1 F2 : Fault → Prop} {f1 f2 : Nat} {s : State}
    (h1 : wpOutcome sys Q1 F1 f1 s)
    (h2 : wpOutcome sys (fun o => Q1 o → Q2 o) (fun k => F1 k → F2 k) f2 s) :
    wpOutcome sys (fun o => Q1 o ∧ Q2 o) (fun k => F1 k ∧ F2 k) (Nat.max f1 f2) s :=
  wpOutcome_mono (fun _ hq => ⟨hq.1, hq.2 hq.1⟩) (fun _ hf => ⟨hf.1, hf.2 hf.1⟩)
    (wpOutcome_and_iff.mpr ⟨wpOutcome_fuel_mono (Nat.le_max_left f1 f2) h1,
                            wpOutcome_fuel_mono (Nat.le_max_right f1 f2) h2⟩)

theorem wpOutcome_frame_of_inv {State Choice Out Fault : Type}
    {sys : TransitionSystem State Choice Out Fault}
    {F : Prop} {Q : Out → Prop} {K : Fault → Prop} {f1 f2 : Nat} {s : State}
    (hInv : F → wpOutcome sys (fun _ => F) K f1 s)
    (hBody : wpOutcome sys Q K f2 s) (hPre : F) :
    wpOutcome sys (fun o => F ∧ Q o) K (Nat.max f1 f2) s :=
  wpOutcome_mono (fun _ hq => hq) (fun _ hf => hf.1)
    (wpOutcome_and_iff.mpr ⟨wpOutcome_fuel_mono (Nat.le_max_left f1 f2) (hInv hPre),
                            wpOutcome_fuel_mono (Nat.le_max_right f1 f2) hBody⟩)

def doneOneSys : TransitionSystem Unit Unit Nat Unit where
  validChoice _ _ := True
  evalStep _ _ := .done 1

theorem counterexample_wlp_short_fuel :
    wpOutcome doneOneSys (fun o => o = 1) (fun _ => False) 1 () ∧
    wlpOutcome doneOneSys (fun o => o = 1 → o = 2) (fun _ => False) 0 () ∧
    ¬ wpOutcome doneOneSys (fun o => o = 1 ∧ o = 2) (fun _ => False) 1 () := by
  refine ⟨⟨⟨(), trivial⟩, fun _ _ => rfl⟩, trivial, ?_⟩
  intro hBad; cases (hBad.2 () trivial).2

def angelicTwoSys : TransitionSystem Unit Nat Nat Unit where
  validChoice _ _ := True
  evalStep c _ := .done c

def wpAngelic {State Choice Out Fault : Type}
    (sys : TransitionSystem State Choice Out Fault) (onDone : Out → Prop) (s : State) : Prop :=
  Exists fun c : Choice => sys.validChoice s c ∧
    match sys.evalStep c s with | .done out => onDone out | _ => False

theorem counterexample_angelic_non_conjunctive :
    wpAngelic angelicTwoSys (fun o => o = 0) () ∧
    wpAngelic angelicTwoSys (fun o => o = 1) () ∧
    ¬ wpAngelic angelicTwoSys (fun o => o = 0 ∧ o = 1) () := by
  refine ⟨⟨0, trivial, rfl⟩, ⟨1, trivial, rfl⟩, ?_⟩
  intro hBad; cases hBad with
  | intro c hc => have h0 : c = 0 := hc.2.1; have h1 : c = 1 := hc.2.2; rw [h0] at h1; cases h1

end Pass1ConjunctiveWpProbe
```

**Integration into `Anneal.MirWp`:** Adding `wlpOutcomeState`, `wlpProg`, and `wpOutcomeState_mp_wlp` drops directly into `theory/Anneal/MirWp.lean` with zero changes to `Trusted.MirSemantics`: Pass A proves UB-free termination + bounds `Q₁` (`onFault := fun _ => False`), Pass B proves `wlpProg p f₂ q (fun out => Q₁ out → Q₂ out)` with `onFault := fun _ => True` (discharging fault branches via `trivial` since `False → True`), and `wellFormed_and_spec_of_wp` (`MirWp.lean` L429–455) certifies `WellFormed`, `¬ Diverges`, and `SatisfiesPost` for `Q₁ ∧ Q₂` under 100% statement-origin separation. Shielding Pass A obligations behind an `@[irreducible]` wrapper (`TrustedBoundary.lean` L595) prevents Lean's kernel `whnf`/`isDefEq` from unfolding Pass A terms during Pass B transformation.

### 5. Fuel Variance Asymmetry and Nondeterminism Counterexamples (`C2` Calibration)

Basis: derived

Three sharp semantic distinctions refute premature unification of `wpOutcome`, `wlpOutcome`, and angelic choice:
1. **Opposite Fuel Variance:** `wpOutcome` maps `0 ↦ False`, so more fuel weakens the obligation (`f₁ ≤ f₂ → wp ... f₁ → wp ... f₂`, `wpOutcome_fuel_mono`). Conversely, `wlpOutcome` maps `0 ↦ True`, so more fuel forces checking *more* steps before reaching `True`, strengthening the obligation (`f₁ ≤ f₂ → wlp ... f₂ → wlp ... f₁`, `wlpOutcome_fuel_anti`). Dropping `f₁ ≤ f₂` in `wpOutcome_mp_wlp` would fuse `wpOutcome ... 1 ()` (`o = 1`) with vacuous `wlpOutcome ... 0 ()` (`o = 1 → o = 2`) into `False` (`doneOneSys`).
2. **Demonic vs. Angelic Choice:** Conjunctivity distributes over `∀ c` (`wpOutcome_and_iff`), matching `Trusted.MirSemantics.WellFormed` and `SatisfiesPost` (`MirSemantics.lean` L1646–1676), but fails on `∃ c`: `angelicTwoSys` satisfies `o = 0` (`c = 0`) and `o = 1` (`c = 1`) separately, never `o = 0 ∧ o = 1`.
3. **Asymmetric Inhabitedness:** Choice inhabitedness `(∃ c₀, validChoice st c₀)` cannot be dropped from `wpOutcome` (empty choice sets would be vacuously valid), yet Pass B `wlpOutcome` omits it because `wpOutcome_mp_wlp` carries `h₁.1` across from Pass A up to depth `f₁`.

### 6. Evaluation Against Anneal `theory/` Rubric `(T1, P1–P5, C1–C2)`

Basis: derived

| Option | (T1) 0-TCB | (P1) Auditability | (P2) Locality | (P3) Kernel / LSP | (P4) Composability | (P5) Failure Clarity | (C1–C2) Minimality | Verdict |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Direct `Std.Do` (`mvcgen`)** | Fail (`Std.*`, `@[spec]`, `meta`, `grind`) | Med (`do`-centric, not MIR CFG) | Low (`mvcgen` experimental; `elimLets` bug) | Low (`SVal`/`ULift`, `leanprover/lean4#8074`, `HasFrame`) | Med (rigid `PostShape`) | Med (breaks on MIR states) | Low (`ULift` duplicates `State → Prop`) | **Reject** |
| **Direct `Std.Internal.Do` (`vcgen`)** | Fail (`Init.Internal.Order`, `CCPO` choice) | High (`requires`/`ensures`) | High (`WPConjunctive`, `ConjunctivePre`) | Med-High (flat `Pred`, noncomputable `iInf`) | High (`EPost.Cons`) | High (`pre ⊑ wp x ...`) | Med (over-axiomatizes lattice on `Prop`) | **Extract algebra only** |
| **Monolithic `MirWp.wpProg` (`c131b320`)** | Pass (Pass-1 verified) | Med-High (`WellFormed` / `SatisfiesPost`) | Low-Med (couples UB, choices, spec) | Med (guard bloat) | Med (lacks `wlp` split) | Low-Med (mixed UB/spec goals) | High (single carrier, couples passes) | **Keep as Pass A carrier** |
| **Distilled Pure-`Init.*` `wpOutcome` + `wlpOutcome` + `wpOutcome_mp_wlp`** | **Pass** (`Init.Core`+`Nat`, 0 axioms, 0-TCB) | **High** (clean Pass B postconditions) | **Very High** (decoupled Pass A / Pass B) | **Very High** (flat `Prop`, `@Nat.rec`, `@[irreducible]`) | **Very High** (`exec`, demonic, fault/unwind) | **Very High** (splits UB/fuel vs. spec delta) | **Very High** (minimal dual variance pair) | **Adopt** |

## Boundaries

- **Direct `Std.Do` / `Std.Internal.Do` / `mvcgen` / `vcgen` in Pass 1 `theory/` (`unsupported`):** Excluded by `TrustedBoundary.lean` and the 51-module `foundation-lock.json`; Pass 2 (`correspondence/`) admits `.sysrootFoundation` in `bwrap` (`L1566–1576`), but cannot export those dependencies into Pass 1 `theory/`.
- **Angelic Nondeterminism (`known not to apply`):** `wpOutcome_and_iff` and `wpOutcome_mp_wlp` fail under existential choice (`counterexample_angelic_non_conjunctive`).
- **Short-Fuel Pass B (`f₂ < f₁`) in `wpOutcome_mp_wlp` (`known not to apply`):** Unsound when `f₂ < f₁` due to `wlpOutcome` contravariance (`counterexample_wlp_short_fuel`).
- **Live Lean `v4.34.1` Execution of `Pass1ConjunctiveWpProbe` (`not examined` dynamically on host):** Running `anneal-lean-run ... lean -DwarningAsError=true` on the extracted probe exited with `124` (`BUILD_SLOT_TIMEOUT: Timed out after 180.0s waiting for 1 of 1 host build slot(s)`) because an external host test process held the single slot (`lean_diagnostics` returned `LSP_DEFERRED_BUILD_ACTIVE`). Probe well-typedness and Pass-1 admissibility are therefore `derived` by source inspection against `MirWp.lean` and `TrustedBoundary.lean`, not `execution`-verified in this turn.
- **Unbounded Coinductive `CCPO` Correspondence (`not examined`):** Relation between `Std.Internal.Do`'s `CCPO` fixpoints and coinductive `Trusted.MirSemantics.Diverges` (`MirSemantics.lean` L1665–1670) was not examined because finite-fuel `wpProg` proves `¬ Diverges` constructively (`MirWp.lean` L406–413).
- **Post-`v4.34.1` `Std.Do` Evolution (`unknown`):** Whether future Lean releases promote `Std.Internal.Do` or merge `leanprover/lean4#9015` is unknown at `5045d005`.

## Evidence

| Subject / Revision | File Paths & Exact Inspected Lines | Key Verified Details |
| :--- | :--- | :--- |
| `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`) | `src/Std/Do/SPred/{SVal,SPred,Laws,Notation,DerivedLaws}.lean` (`SVal` L30–90, `SPred` L34–157, `DerivedLaws` L30–120, L250–345) | `SPred := SVal σs (ULift Prop)`, `leanprover/lean4#8074`/`#9015` reducibility comments, `HasFrame`/`SimpAnd` |
| `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`) | `src/Std/Do/{PostCond,PredTrans,WP/Basic,WP/Monad,Triple/Basic,Triple/SpecLemmas}.lean` | `Conjunctive` -> `mono` (`PredTrans.lean` L52–56), `apply` wrapper (L77–79), `Triple.and`/`mp`/`observe` |
| `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`) | `src/Std/Internal/Do/{Assertion,PredTrans,WP/Basic,WP/Conjunctive,WP/Frame,Triple/Basic,Order/Basic,Order/Instances}.lean`; `src/Init/Internal/Order/Basic.lean` L105–109 | `CompleteLattice`, `WPConjunctive`, `WP.Frames.of_conjunctive`, `CCPO.csup` (`Classical.choose`) |
| `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`) | `src/Lean/Elab/Tactic/Do/{VCGen,Spec,ConjunctivePre,Contract,Attr,ProofMode/Basic}.lean` | `mvcgen` experimental warning (`L456`), `elimLets` bug (`L481`), `isConjunctiveInPosts` (`ConjunctivePre.lean` L15–155) |
| `sgraf812/mpl` (`1dbf6bc75ff5398f59b77ae320f1f0a0781b721e`) | GitHub API commit verification | Upstream `mpl` prototype extracted into `Std.Do` |
| `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) | `trusted/audit/TrustedBoundary.lean` L1–140, L437–1580; `foundation-lock.json` (51 modules); `MirSemantics.lean` L1646–1809; `theory/Anneal/MirWp.lean` L65–125, L400–455 | Pass 1 parser/axiom/replay gates; `@Nat.rec` `wpOutcomeState`, `execOutcomeState`, `wellFormed_and_spec_of_wp` |

- **Host Probe Attempt (`2026-11-19`):** Running `$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -DwarningAsError=true` on the extracted `Pass1ConjunctiveWpProbe` file under `anneal-lean-run` exited `124` (`BUILD_SLOT_TIMEOUT: Timed out after 180.0s waiting for 1 of 1 host build slot(s)`); `lean_diagnostics` returned `LSP_DEFERRED_BUILD_ACTIVE`.

## Revalidation

1. **Verify `foundation-lock.json` Exclusions:** Inside a clean `joshlf/anneal` checkout, confirm `Std.*`, `Init.Omega`, and `Init.Internal.Order` remain excluded:
   ```bash
   python3 -c 'import json; mods=set(json.load(open("trusted/lean/foundation-lock.json"))["graph"]); print(any(m.startswith("Std.") for m in mods), "Init.Omega" in mods, any("Internal.Order" in m for m in mods))'
   ```
   Expected output: `False False False`.
2. **Track Lean Core Changes Above `5045d005`:** Diff `src/Std/Do/SPred/{SVal,SPred}.lean`, `src/Std/Internal/Do/WP/Conjunctive.lean`, and `src/Lean/Elab/Tactic/Do/ConjunctivePre.lean`.
3. **Compile and Check Zero-Axiom Status of `Pass1ConjunctiveWpProbe` (`<2s` once build slot is idle):** Write the fenced `Pass1ConjunctiveWpProbe` code from Findings §4 to `/tmp/pass1_conjunctive_wp_probe.lean`, check `#print axioms` on `wpOutcome_mp_wlp`, `wpOutcome_mp_max`, `wpOutcome_frame_of_inv`, `counterexample_wlp_short_fuel`, and `counterexample_angelic_non_conjunctive` in a separate `/tmp/check_axioms.lean` wrapper, and run `~/.local/bin/anneal-lean-run lean -DwarningAsError=true /tmp/pass1_conjunctive_wp_probe.lean`. Confirm exit `0` and empty axiom dependencies.
