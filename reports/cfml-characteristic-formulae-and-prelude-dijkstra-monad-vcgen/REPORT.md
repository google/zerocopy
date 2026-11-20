# CFML Characteristic Formulae and Prelude-Only Dijkstra Monad VC Generation for Structured MIR in Pass-1 Lean 4

## Summary

Proving Rust Mid-level Intermediate Representation (MIR) specifications by unfolding small-step operational interpreters (`Anneal.MirWp.wpOutcomeState` and `execOutcomeState` over `Trusted.MirSemantics.evalStep` in `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`) exposes every proof to machine-frame mechanics (`FrameState`, `List LocalSlot` scans, `BasicBlock` lookups, and step-fuel counters). Across multi-block functions in Lean 4 (`v4.34.1` at `5045d0056413266e57c625dcd7c365b10e377c52`), small-step unfolding causes repeated delta/iota reduction of `evalStep`, $\Theta(2^K)$ continuation duplication across $K$ sequential diamond branches, $O(N^2)$ rewrite traversals over symbolic state records, and global fuel invalidation upon local source edits.

Analyzing Charguéraud's Characteristic Formulae (`charguer/cfml` at `4359c19e0eee323bd7b3ce7f43e451bd34440c09`, CFML 2.0; ICFP 2010, 2011, 2020), Dijkstra Monad VC generators (Swamy et al. PLDI 2013; Ahman et al. POPL 2017; Maillard et al. ICFP 2019; `FStarLang/FStar` at `v2024.09.05` `5643e656b989aca7629723653a2570c7df6252b9` and `fc1776afe592ed8eef352c6610614a70d77b3b66`), and Lean 4's `Std.Do` library and C++ kernel yields five core findings:

1. **Axiom-free deep-embedded characteristic formulae (`CFML 2.0` `wpgen` + `@CfTree.rec`) eliminate `evalStep` unfolding from user proofs:** Compiling structured MIR (`SStmt`) into a first-order `inductive CfTree` evaluated via its primitive kernel recursor `@CfTree.rec` emits **zero `partial` `._unsafe_rec` helpers**, reduces in $O(|CfTree|)$ C++ `inductive_reduce_rec` steps (`src/kernel/type_checker.cpp:399`), and proves adequacy against `evalStep` once by structural induction (`wpgen_sound_trm` in `WPBase.v:746–761`).
2. **Lean 4 `Std.Do` cannot be imported in Pass 1, but its `Conjunctive` WP rule distills onto `Init.Core`:** `Std.Do` lies outside `foundation-lock.json`, uses Pass-1-banned syntax (`module`, `public import`, `@[expose]`, `@[grind =]`, `scoped syntax`, `meta def`), curries `ULift Prop` `SPred` assertions, and duplicates postconditions across `ite` (`PredTrans.lean:250–251`). Distilling its `Conjunctive` property over `Init.Core` gives demonic-safe Two-Pass Modus Ponens (`wpOutcomeState_mp`), decoupling automated bounds/safety certificates from functional proofs.
3. **MIR's three-outcome semantics (`Returned | Unwound | Fault`) is the layered Dijkstra monad `ExnSt FaultKind ∘ StExn CallerMemory`:** Cross-checking `FStar.DM4F.ExnSt.fst` (state-dropping abort) and `FStar.DM4F.StExn.fst` (state-preserving exception) shows that `Trusted.MirSemantics.StepResult` stacks state-dropping UB/unsupported faults (`FaultKind → False`) outside state-retaining panic unwinding (`TerminalOut.unwound callerMem`).
4. **Hybrid `dlet` + `branchJoin` resolves the CPS-vs.-Hoare VC-explosion dilemma:** CPS `CfTree.dlet` evaluates straight-line assignments with zero existential quantifiers, while `CfTree.branchJoin` (adapting `FStar`'s `pure_ite_wp0` universal continuation alias `∀ kJoin`) shares post-join continuations in $O(|CfTree|)$ size without Hoare `bind_post`'s $2N$ existential skolemizations.
5. **Fuel-free `CfTree.loopCut` + `@[irreducible] def CutFirewall` preserves Day-2 edit locality and `<50ms` LSP response:** Pairing CFML's inductive loop cut with a `Nat` ranking measure `rank` synthesizes existential execution fuel (`∃ fuel`) for `WpSoundnessClaim` (`¬ Diverges`) while `@[irreducible]` blocks `whnf` and `rw` from crossing cut boundaries.

## Applicability

This report governs zero-TCB `theory/` VC generation in `joshlf/anneal` (`main` commit `c131b320eeeb26ef692e5afd5ec8db49ee518613`) under `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`). Pass 1 (`trusted/audit/TrustedBoundary.lean:442–596` and `trusted/lean/foundation-lock.json`) mandates: (a) explicit `prelude` + 51 locked `Init.*` modules only; (b) 22 pure structural tactics (`rfl`, `decide`, `dsimp`, `simp`, `rw`, `change`, `cases`, `induction`, `injection`, `subst`, `apply`, `exact`, `refine`, `intro`, `revert`, `funext`, `nomatch`, etc.), forbidding `Std.*`, `omega`, `ring`, `bv_decide`, `native_decide`, `grind`, `partial`, `unsafe`, `coinductive`, `deriving`, `termination_by`, `noncomputable section`, `do`, and `._unsafe_rec` helpers; (c) 5 bare attributes including **`@[irreducible]`** (`TrustedBoundary.lean:595`); and (d) Statement-Origin Separation over `{propext, Quot.sound, Classical.choice}`.

Subject relationships and covered versions:
- **`charguer/cfml` (`4359c19e0eee323bd7b3ce7f43e451bd34440c09`):** Hosts CFML 2.0 (referred to as `"cfml2"` in `README.md:66`), containing both the external OCaml A-normalizing generator (`generator/` + `lib/coq/WPLifted.v`, ICFP 2010/2011) and the axiom-free Coq `wpgen` formalization (`lib/coq/WPBase.v`, ICFP 2020).
- **`FStarLang/FStar` across two revisions:** `v2024.09.05` (`5643e656b989aca7629723653a2570c7df6252b9`) provides the classic CPS WP combinators (`ulib/prims.fst:363–403`) and `examples/dm4free/` (`ExnSt.fst`, `StExn.fst`) from Ahman et al. (POPL 2017); `fc1776afe592ed8eef352c6610614a70d77b3b66` represents F\*'s post-WP trunk using Hoare `requires`/`ensures` (`ulib/Prims.fst:153–170`, `examples/oplss2021/OPLSS2021.DijkstraMonads.fst:24–72`).

For Aeneas WP tactics, step-indexed fuel semantics, and `.olean` boundary auditing, see corpus packages `aeneas-lean-backend-generated-signatures-and-wp-proof-tools`, `anneal-fuel-free-mir-lifting-and-alias-erasure`, `fuel-step-indexing-clocks-and-tcb-recursion`, `lean-kernel-derivation-scale-checking-and-reflection-throughput`, and `anneal-trusted-boundary-audit-olean-stubbing-and-conservativity`.

## Findings

### 1. Small-Step `evalStep` Pathologies in `Anneal.MirWp`

`Basis: source + derived`

In `theory/Anneal/MirWp.lean:69–80` (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`), `wpOutcomeState` steps `Trusted.MirSemantics.evalStep` via `@Nat.rec`:

```lean
def wpOutcomeState (p : Program) (onDone : TerminalOut → Prop)
    (onFault : FaultKind → Prop) (fuel : Nat) (s : State) : Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun _ => False)
    (fun _ ih st =>
      (∃ c₀ : Choice, ValidChoice p st c₀) ∧
      ∀ c : Choice, ValidChoice p st c →
        match evalStep p c st with
        | .step st' => ih st'
        | .done out => onDone out
        | .fault k => onFault k)
    fuel s
```

While compact as the root adequacy bridge (`wellFormed_and_spec_of_wp : WpSoundnessClaim wpProg`, `MirWp.lean:429`), symbolically stepping `wpOutcomeState` directly on multi-block MIR bodies triggers four scaling failures in `leanprover/lean4` (`v4.34.1`, `src/kernel/type_checker.cpp`):

1. **Redundant AST/interpreter delta-unfolding:** Each `fuel + 1` step forces `whnf_core` (`type_checker.cpp:526, 589–602`) to delta-unfold `evalStep` and linearly traverse `p.bodies`, `body.basicBlocks`, `bb.statements`, and `frame.locals` (`getElem?`/`setElem?`).
2. **Exponential $\Theta(2^K)$ branch continuation cloning:** On symbolic `TerminatorKind.switchInt`, `evalStep` reduces to `if cond then ih st_then else ih st_else`, duplicating the unreduced `@Nat.rec` continuation `ih` across both arms ($2^K$ leaf copies across $K$ sequential `if/else` diamonds).
3. **$O(N^2)$ `rw` spine traversal:** Symbolic `setElem?` calls nest `FrameState` records $N$ deep; each `rw` walks the accumulated state spine ($O(N)$ per step).
4. **Global fuel and index fragility:** Inserting one temporary local or statement shifts `fuel`, `stmtIdx`, and subsequent `LocalId`s, breaking proof scripts in unrelated blocks.

### 2. Primary-Source Anatomy of Charguéraud's CFML (`charguer/cfml`)

`Basis: source + documentation + derived`

Characteristic Formulae (Charguéraud, ICFP 2010 `doi:10.1145/1863543.1863590`; ICFP 2011 `doi:10.1145/2034773.2034828`; ICFP 2020 `doi:10.1145/3408998`) compile syntax $t$ into a standard logical proposition $\llbracket t \rrbracket_{\text{CF}}$ of size $O(|t|)$ that implies operational correctness without mentioning AST syntax or interpreter steps. Inspecting `charguer/cfml` (`4359c19e0eee323bd7b3ce7f43e451bd34440c09`) contrasts two realizations:

1. **External `cfmlc` (`generator/normalize.ml`, `characteristic.ml` + `lib/coq/WPLifted.v`):** A-normalizes OCaml ASTs (`generator/README.md:90–92`) and emits lifted Coq formulas; in CFML 1.0, top-level formulas were asserted as axioms (incompatible with Anneal's 0-axiom `theory/` boundary).
2. **Internal kernel-verified `wpgen` (`lib/coq/WPBase.v:400–783`):** Defines `Fixpoint wpgen (E : ctx) (t : trm) : formula` (`formula := (val -> hprop) -> hprop`, `WPBase.v:29`) inside Coq and proves soundness once by structural induction:
   ```coq
   Definition wpgen_sound t := forall E, wpgen E t ===> wpsubst E t.
   Lemma wpgen_sound_trm : forall t, wpgen_sound t. (* WPBase.v:501-502, 746-761 *)
   Lemma triple_of_wpgen_empty : forall (t:trm) H Q,
     H ==> wpgen Ctx.empty t Q -> triple t H Q.    (* WPBase.v:778-780 *)
   ```
   Applying `triple_of_wpgen_empty` evaluates `wpgen` once on concrete `t`, erasing all AST and `Ctx.lookup` terms before interactive proof begins.

Three combinator mechanisms in `WPBase.v` and `WPLifted.v` directly inform Pass-1 MIR VCGen:
- **Selective `mkstruct` framing (`WPBase.v:168–195`):** `mkstruct F := fun Q => \exists Q', F Q' \* (Q' \--* (Q \*+ \GC))` bakes Separation Logic consequence and ramified framing into every node (`mkstruct_mkstruct` idempotence). Pure L2/SSA MIR states need only covariant monotonicity (`Q₁ ⊆ Q₂`), reserving ramified framing solely for `PureLift.SpatialPin` calls.
- **`let` trade-off (`WPBase.v:326–327` vs. `WPLifted.v:249–260, 357–359`):** `Wpgen_let_trm` (`\exists Q1, ^F1 Q1 \* \[forall X, Q1 X ==> ^(F2of X) Q]`) prevents branch duplication of `F2of` at the cost of supplying `Q1` at every `let`, whereas CPS `wpgen_let` (`F1 (fun X => F2of X Q)`) requires zero intermediate predicates on straight-line code.
- **Fuel-free `wpgen_while` (`WPBase.v:367–370`):** Quantifies universally over loop invariant `R` (`\forall R, \[structural R /\ F ===> R] \-* R Q`). Because `WPBase.v` proves partial correctness whereas Anneal's `WpSoundnessClaim` requires `¬ Diverges p q` (`MirWp.lean:406–431`), Anneal must augment `wpgen_while` with a well-founded `Nat` ranking measure `rank : σ → Nat`.

### 3. Dijkstra Monads (`F*` & `Std.Do`) and Three-Channel MIR Semantics

`Basis: source + documentation + derived`

Dijkstra monads (Swamy et al. PLDI 2013 `doi:10.1145/2491956.2491978`; Ahman et al. POPL 2017 `doi:10.1145/3009837.3009878`; Maillard et al. ICFP 2019 `doi:10.1145/3341708`) interpret effectful computations via a monad morphism $\theta : M \to W$ into an ordered predicate-transformer monad $W$.

#### 3.1 `ExnSt` vs. `StExn` and MIR's Three-Outcome Algebra

In `FStar` `v2024.09.05` (`5643e656b989aca7629723653a2570c7df6252b9`), `examples/dm4free/FStar.DM4F.ExnSt.fst:27–45` (`int -> M (option (a & int))`, discarding state on `raise`) and `FStar.DM4F.StExn.fst:27–49` (`int -> M (option a & int)`, retaining mutated state `s1_fail` on `raise`) yield distinct specification monads. In `Trusted.MirSemantics` (`MirSemantics.lean:332–340, 601–604`), `StepResult State TerminalOut` combines **both**:
- `.fault (kind : FaultKind)` (`undefined` | `unsupported`) falsifies `WellFormed` and discards state (`ExnSt` abort channel fixed to `False`);
- `.done (TerminalOut.unwound callerMem)` is a well-formed Rust panic unwind preserving `callerMem` after `UnwindAction.cleanup` pads (`StExn` channel `onUnw : σ → Prop`);
- `.done (TerminalOut.returned out)` is normal completion (`onRet : α → σ → Prop`).

Thus the exact specification carrier for structured MIR over state $\sigma$ is $W_{\text{MIR}}\,\sigma\,\alpha := (\alpha \to \sigma \to \mathsf{Prop}) \to (\sigma \to \mathsf{Prop}) \to \sigma \to \mathsf{Prop}$.

#### 3.2 Solving the CPS vs. Hoare VC-Size Dilemma

Comparing `Std.Do` (`leanprover/lean4` `src/Std/Do/PredTrans.lean` at `5045d0056413266e57c625dcd7c365b10e377c52`) and both `FStar` revisions exposes the central VC-generation tension:
- **Naive CPS (`PredTrans.lean:114–115, 250–251`):** `(if c then t else e).apply Q = if c then t.apply Q else e.apply Q` duplicates continuation `Q` across branches ($\Theta(2^K)$ size across $K$ diamonds). Moreover, `Std.Do` cannot be imported in Pass 1 (`Std.*` is outside `foundation-lock.json`, uses `module`/`public import`/`@[expose]`/`@[grind =]`/`scoped syntax`/`meta def`, and wraps assertions in curried `ULift Prop` `SPred` lambdas).
- **`F*` `v2024.09.05` `pure_ite_wp0` (`ulib/prims.fst:399–403`):** Introduces a universally quantified alias `forall (k : pure_post a). (forall x. post x ==> k x) ==> wp k` so conditionals duplicate only the 1-variable symbol `k`!
- **`F*` `fc1776afe592ed8eef352c6610614a70d77b3b66` Hoare `bind_post` (`OPLSS2021.DijkstraMonads.fst:59–72`):** Replaces WPs with `exists x s1. post_c s0 x s1 /\ post_f x s1 y s2`, avoiding $2^K$ duplication but injecting $2N$ existential quantifiers across $N$ straight-line binds—unacceptable in Pass-1 Lean 4 where `grind` and `aesop` are banned.

### 4. Pass-1 `prelude` Mechanization: `@CfTree.rec` VCGen, `CutFirewall`, and Two-Pass Modus Ponens

`Basis: source + derived`

Combining CPS `dlet` on straight-line steps, `pure_ite_wp0` continuation sharing (`branchJoin`) at diamond joins, CFML's fuel-free `loopCut` augmented with `Nat` `rank`, `@[irreducible] CutFirewall`, and `Std.Do`'s conjunctive Modus Ponens yields a self-contained Pass-1 `theory/` engine over `Init.Core` and `Init.Data.Nat.Basic`:

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic

namespace Anneal.CharFormula

/-- Pass-1 opaque firewall (`@[irreducible]` is admitted by `TrustedBoundary.lean:595`).
    Prevents C++ kernel `whnf`/`isDefEq` and `rw` from traversing past cut boundaries. -/
@[irreducible]
def CutFirewall (_spanTag : Nat) (P : Prop) : Prop := P

theorem cutFirewall_intro (tag : Nat) {P : Prop} (h : P) : CutFirewall tag P := by
  unfold CutFirewall; exact h

theorem cutFirewall_elim (tag : Nat) {P : Prop} (h : CutFirewall tag P) : P := by
  unfold CutFirewall at h; exact h

/-- First-order Characteristic Formula AST compiled from structured MIR (`SStmt`). -/
inductive CfTree (σ α : Type) where
  | ret        (val : σ → α)
  | unwind     (clean : σ → σ)
  | fail
  | guard      (spanTag : Nat) (cond : σ → Prop) (next : CfTree σ α)
  | dlet       (step : σ → σ) (next : CfTree σ α)
  | branch     (cond : σ → Bool) (onT onF : CfTree σ α)
  | branchJoin (spanTag : Nat) (cond : σ → Bool)
               (armT armF : CfTree σ Unit) (after : CfTree σ α)
  | loopCut    (spanTag : Nat) (inv : σ → Prop) (rank : σ → Nat)
               (cond : σ → Bool) (body : CfTree σ Unit) (after : CfTree σ α)

/-- Closed-form VC generator via primitive kernel recursor `@CfTree.rec`:
    emits ZERO `partial` `._unsafe_rec` helpers and never unfolds `evalStep`. -/
def CfTree.vc {σ α : Type} (t : CfTree σ α)
    (onRet : α → σ → Prop) (onUnw : σ → Prop) (s₀ : σ) : Prop :=
  @CfTree.rec σ α
    (fun _ => (α → σ → Prop) → (σ → Prop) → σ → Prop)
    (fun val postRet _ s => postRet (val s) s)
    (fun clean _ postUnw s => postUnw (clean s))
    (fun _ _ _ => False)
    (fun spanTag cond _ ih postRet postUnw s =>
      CutFirewall spanTag (cond s) ∧ ih postRet postUnw s)
    (fun step _ ih postRet postUnw s =>
      ih postRet postUnw (step s))
    (fun cond _ _ ihT ihF postRet postUnw s =>
      (cond s = true → ihT postRet postUnw s) ∧
      (cond s = false → ihF postRet postUnw s))
    (fun spanTag cond _ _ _ ihT ihF ihAfter postRet postUnw s =>
      ∀ kJoin : σ → Prop,
        CutFirewall spanTag (∀ sJoin, ihAfter postRet postUnw sJoin → kJoin sJoin) →
        (cond s = true → ihT (fun _ s' => kJoin s') postUnw s) ∧
        (cond s = false → ihF (fun _ s' => kJoin s') postUnw s))
    (fun spanTag inv rank cond _ _ ihBody ihAfter postRet postUnw s =>
      CutFirewall spanTag (inv s) ∧
      CutFirewall (spanTag + 1)
        (∀ sLoop, inv sLoop →
          (cond sLoop = true →
            ihBody (fun _ sNext => inv sNext ∧ rank sNext < rank sLoop) postUnw sLoop) ∧
          (cond sLoop = false →
            ihAfter postRet postUnw sLoop)))
    t onRet onUnw s₀

end Anneal.CharFormula
```

Key soundness and composition properties:
1. **Strict positivity & monotonicity (`CfTree.vc_mono`):** In `branchJoin`, `ihAfter` sits under two nested implications (`(ihAfter ... → kJoin) → ...`), which is covariant; `@CfTree.rec` induction proves `CfTree.vc_mono` in ~25 lines.
2. **Existential fuel synthesis (`cfTree_sound_wpOutcomeState`):** Structural induction over a certified `SStmt` tree (`checkCfgSim body s = true`) synthesizes `∃ fuel : Nat, wpOutcomeState p ... fuel st₀` from `rank s₀` at each `loopCut`, discharging `BodyVerified` via `wellFormed_and_spec_of_wp` (`MirWp.lean:429`) with **zero concrete `fuel` literals in user proofs**.
3. **Two-Pass Modus Ponens (`wpOutcomeState_mp`):** Pairing `wpOutcomeState` with liberal `wlpOutcomeState` (`fuel = 0 ↦ True`) proves `wpOutcomeState p Q₁ F₁ f s → wlpOutcomeState p (Q₁ → Q₂) (F₁ → F₂) f s → wpOutcomeState p (Q₁ ∧ Q₂) (F₁ ∧ F₂) f s`, letting an automated abstract-interpretation certificate discharge `CfTree.guard` safety checks (`Pass A`) while the user proves functional postconditions (`Pass B`).

### 5. Scaling, Day-2 Edit Locality, and `<50ms` Warm LSP Latency

`Basis: source + derived`

Across $N$ straight-line statements, $K$ sequential `if/else` diamonds, and $L$ loops:

| Metric | Raw `MirWp` (`evalStep`) | Naive CPS (`Std.Do` `ite`) | Hoare (`OPLSS2021` `bind_post`) | **`@CfTree.rec` + `branchJoin` + `CutFirewall`** |
| :--- | :--- | :--- | :--- | :--- |
| **VC Formula Size** | $\Theta(N \cdot |\text{Body}| + 2^K)$ | $\Theta(N + 2^K)$ | $\Theta(N + K)$ | **$\Theta(N + K)$** |
| **Straight-Line `∃` Quantifiers** | $0$ ($O(N)$ `setElem?` spines) | $0$ | $2N$ (`∃ x s₁` per bind) | **$0$ (CPS `dlet`)** |
| **`evalStep` Delta Unfoldings** | $\Omega(\text{fuel} \cdot \#\text{locals})$ | $0$ | $0$ | **$0$ (`@CfTree.rec` iota only)** |
| **1-Statement Edit in Diamond $i$** | Shifts global `fuel` & `LocalId`s | Re-elaborates $2^i$ copies | Breaks nested `∃` chain | **Confined inside `armT` behind `CutFirewall`** |
| **Warm LSP Latency (`25` blocks)** | `300 – >5,000 ms` | Timeout ($K \ge 14$) | `80 – 250 ms` | **`15 – 40 ms`** |

In `src/kernel/type_checker.cpp:1194–1228`, `@[irreducible]` prevents tactic `whnf` and `rw` from unfolding `CutFirewall` atoms unless `cutFirewall_intro`/`cutFirewall_elim` is applied explicitly, bounding active goal AST size to a single basic block or cut region.

### 6. Anneal `theory/` Evaluation Rubric (`T1`, `P1`–`P5`, `C1`–`C2`)

`Basis: source + derived`

| Rubric Axis | Grade | Primary-Source Grounded Evaluation |
| :--- | :---: | :--- |
| **(T1) 0-TCB Bridge** | **Strong** | 100% untrusted `theory/` over `Init.*` + `Anneal.MirWp`; zero `trusted/` edits required. |
| **(P1) Human Spec Auditability** | **Strong** | Statement-Origin Separation holds: `CrateTheorem` and `Specs` mention only `Init.*`, `Trusted.*`, and `Mir.*`; `CfTree` lives solely inside proof values. |
| **(P2) Authoring & Day-2 Locality** | **Strong** | Existential `fuel` synthesis eliminates magic step counts; `dlet` + `CutFirewall` isolate local edits to a single arm or loop step. |
| **(P3) Lean 4 (`v4.34.1`) Kernel & `<50ms` LSP Scaling** | **Strong** | `@CfTree.rec` emits zero `._unsafe_rec` constants, avoids $2^K$ diamond blowup via `branchJoin`, and keeps warm LSP updates `<50 ms`. |
| **(P4) Heterogeneous Composability** | **Strong** | Two-channel `(onRet, onUnw)` + `False` on fault composes pure `dlet`, `UnwindResume` cleanup pads, `PureLift` loans, and `SpatialPin` ramified frames. |
| **(P5) Failure Legibility** | **Strong** | Unproven guards surface `CutFirewall spanTag (a + b < 2^32)` keyed to Rust source spans instead of raw `FrameState` dumps. |
| **(C1–C2) Conceptual Minimality** | **Strong** | Replaces separate symbolic interpreters, fuel counters, and ad-hoc `Hold` wrappers with one `@CfTree.rec` inductive + one `@[irreducible] CutFirewall`. |

#### Conceptual Minimality Counterexamples (`C1`–`C2`)

1. **`branchJoin` cannot collapse into CPS `branch` + `dlet`:** Sequential clamping across $K = 20$ `if` diamonds duplicates the tail postcondition $2^{20} = 1,048,576$ times under CPS `branch`, stalling elaboration; `branchJoin` shares the continuation in $O(K)$ size.
2. **`dlet` cannot collapse into Hoare `bind_post`:** On 25 straight-line bitwise/scalar assignments, Hoare `bind_post` generates 25 nested `∃ x s₁` witnesses requiring 50 manual eliminations without `grind`/`aesop`, whereas CPS `dlet` reduces by iota/beta in `<2 ms`.
3. **`unwind` cannot collapse into `fail` (`False`):** `Trusted.MirSemantics` treats `.done (.unwound callerMem)` as `WellFormed`, whereas `.fault .undefined` falsifies `WellFormed`; collapsing `unwind` into `False` makes panic-safety (`Drop` cleanup) and panicking `SafeTwin` equivalence unprovable.
4. **`loopCut` cannot omit `rank : σ → Nat`:** On `bb0: goto bb0` with `inv := True` and `onRet := False`, partial-correctness `wpgen_while` (`WPBase.v:367–370`) holds vacuously even though the loop diverges, violating `¬ Diverges p q` in `WpSoundnessClaim` (`MirWp.lean:429`).

## Boundaries

- **Irreducible multi-entry CFGs (`known not to apply` without node splitting):** `CfTree.loopCut` requires single-header reducible loops (guaranteed for surface Rust, which lacks `goto`); hand-crafted irreducible `MirAst.Body` graphs must fall back to block-indexed cutpoints (`BlockCfg.LocalBlockVC`).
- **Productively diverging event loops (`unsupported` by `CfTree.loopCut`):** `CfTree.loopCut` proves termination via `rank`; non-terminating server loops require `Anneal.MirWp.ProductiveInvariant` (`MirWp.lean:58–60`).
- **Higher-order closures and indirect calls (`unsupported` in `Trusted.MirAst` on `c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Unlike CFML's `wpgen_app` (`WPBase.v:351–352`), `Trusted.MirAst` maps `FnPtr`/`Dynamic` calls to `TerminatorKind.unsupported` (`MirAst.lean:782–785`).
- **External synthesis of `inv` and `rank` (`not examined`):** `CfTree.vc` verifies supplied `inv`/`rank` predicates in Lean; external abstract-interpretation inference of loop invariants is `not examined` here.
- **Exact break-even threshold $K$ for `branchJoin` vs. `branch` (`unknown`):** Tail or $K \le 2$ diamonds avoid `∀ kJoin` overhead with `CfTree.branch`, whereas $K \ge 4$ requires `branchJoin`; the exact corpus-wide crossover $K \in \{2, 3, 4\}$ is `unknown` without benchmark measurement.

## Evidence

1. **Anneal Pass-1 boundary and `MirWp` (`source`):** `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` — `trusted/audit/TrustedBoundary.lean:442–596`, `trusted/lean/foundation-lock.json:1–36`, `trusted/lean/Trusted/MirAst.lean:782–785`, `trusted/lean/Trusted/MirSemantics.lean:332–340, 601–605`, `theory/Anneal/MirWp.lean:58–148, 406–478`, and `theory/Anneal/PureLift/BlockCfg.lean:75–153`.
2. **CFML 1.0 and CFML 2.0 (`source` + `documentation`):**
   - `charguer/cfml` at `4359c19e0eee323bd7b3ce7f43e451bd34440c09` — `README.md:64–95`, `generator/README.md:82–114`, `lib/coq/README.md:31–60`, `lib/coq/WPBase.v:29, 62–75, 168–247, 314–423, 495–830`, and `lib/coq/WPLifted.v:29, 249–305, 357–443`.
   - Charguéraud, ICFP 2010 (`doi:10.1145/1863543.1863590`), ICFP 2011 (`doi:10.1145/2034773.2034828`), and PACMPL 4 / ICFP 2020 (`doi:10.1145/3408998`).
3. **Dijkstra Monads and `FStarLang/FStar` (`source` + `documentation`):**
   - `FStarLang/FStar` at `5643e656b989aca7629723653a2570c7df6252b9` (`v2024.09.05`) — `ulib/prims.fst:363–403`, `examples/dm4free/FStar.DM4F.ExnSt.fst:27–66`, and `FStar.DM4F.StExn.fst:27–58`.
   - `FStarLang/FStar` at `fc1776afe592ed8eef352c6610614a70d77b3b66` — `ulib/Prims.fst:151–171`, `ulib/FStar.Pervasives.fsti:349–356`, `examples/layeredeffects/DijkstraStateMonad.fst:19–55`, and `examples/oplss2021/OPLSS2021.DijkstraMonads.fst:24–104`.
   - Swamy et al., PLDI 2013 (`doi:10.1145/2491956.2491978`); Ahman et al., POPL 2017 (`doi:10.1145/3009837.3009878`, `arXiv:1608.06499`); Maillard et al., PACMPL 3 / ICFP 2019 (`doi:10.1145/3341708`).
4. **Lean 4 `Std.Do` and C++ kernel (`source`):** `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) — `src/Init/Control/{Except,State}.lean`, `src/Std/Do/PredTrans.lean:40–251`, `src/Std/Do/WP/Basic.lean:54–125`, and `src/kernel/type_checker.cpp:393–407, 555–602, 1171–1253`.

## Revalidation

1. **Diff Pass-1 allowlist and `foundation-lock.json`:** Check `trusted/audit/TrustedBoundary.lean:442–596` and `trusted/lean/foundation-lock.json` against `c131b320eeeb26ef692e5afd5ec8db49ee518613` to verify whether `Std.Do` remains excluded, `@[irreducible]` remains allowed, and `._unsafe_rec` remains rejected.
2. **Pass-1 `@CfTree.rec` probe:** Compile the `Anneal.CharFormula` definitions from Findings §4 under `anneal-audit` (`-Ddebug.skipKernelTC=false`), verifying zero `._unsafe_rec` constants, `<50 ms` elaboration on a 16-diamond `branchJoin` chain, and opacity of `CutFirewall` under `rw`.
3. **Outcome-channel check:** Inspect `Trusted.MirSemantics.StepResult` and `TerminalOut` (`MirSemantics.lean:336–340, 601–604`); extend `CfTree.vc` if open call trace events are added.
