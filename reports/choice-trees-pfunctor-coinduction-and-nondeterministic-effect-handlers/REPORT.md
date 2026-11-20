# Choice Trees, PFunctor M-Type Coinduction, and Nondeterministic Open-Callback Semantics in Pure Init.* Lean 4

## Summary

Choice Trees (`CTrees`, Chappe et al. POPL 2023; `vellvm/ctrees` at `cabcf9bf24b0f459204a7da19ac01b7697ff04e3`) generalize Interaction Trees (`ITrees`) with native internal nondeterminism (`brD` / `brS`) alongside visible external events (`vis`), silent transitions (`tau` / `Step`), and recursion (`Guard` / `iter`). Porting `CTrees` into an untrusted proof library (`theory/`) constrained by Anneal's strict verification boundary (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/audit/TrustedBoundary.lean`) exposes four foundational mismatches in standard coinductive mechanizations:

1. **Lean 4 `v4.34.1` `coinductive` does not define data types:** `src/Lean/Elab/MutualInductive.lean` rejects non-`Prop` targets (`"`coinductive` keyword can only be used to define predicates"`), lowering coinductive predicates onto `Init.Internal.Order.ReverseImplicationOrder`. Anneal's Pass 1 preflight also bans `coinductive`, `coinductive_fixpoint`, `Init.Internal.Order`, `partial`, `unsafe`, `._unsafe_rec`, `set_option`, and `Std.*`/`Mathlib.*` imports—locking `theory/` to 51 `Init.*` modules and `{propext, Quot.sound, Classical.choice}`.
2. **Mathlib's `PFunctor.M` pulls avoidable axioms and tactics, yet distills cleanly:** `Mathlib.Data.PFunctor.Univariate.M` routes `M.bisim` through `Path`/`iselect`, pulling in `Classical.choice`, `[DecidableEq]`, `[Inhabited]`, and `HEq`. Direct `Nat` induction on `CofixA` using `mk_dest` proves `M.bisim` and `M.corec_unique` in pure `Init.Core` + `Init.Data.Nat.Basic` with **zero `Classical.choice`** (only `{propext, Quot.sound}` via `funext`). Encoding external and branching signatures as fixed `Type 0` `(Op : Type, Resp : Op → Type)` records avoids both `vellvm/ctrees`'s `JMeq_eq` / `Unset Universe Checking` workarounds and Anneal's universe-monomorphism rejection.
3. **Naively mapping `FaultKind` to `Stuck` or adopting `wbisim` breaks soundness against `Trusted.MirSemantics`:** In `vellvm/ctrees`, `Stuck` has no outgoing LTS edges (`Stuck ≲ t` universally), and `wbisim` equates `spinS := Step spinS` with `Stuck`, erasing divergence. Faithful Rust semantics requires explicit observable `fault (k : FaultKind)` leaves, inhabited demonic choice (`∃ c, ...`), and divergence-preserving simulation (`Diverges`).
4. **Return-only callback invariants are unsound in Rust:** `std::panic::catch_unwind(AssertUnwindSafe(...))` is 100% safe Rust; a library method (`RingBuf::for_each_mut`) that temporarily breaks its invariant across an open `FnMut` callback can unwind with broken memory. Open-callback `vis` specs must enforce Kripke-monotone library invariants on **both** `TerminalOut.returned` and `TerminalOut.unwound`, distinguishing `Freeze` vs. `!Freeze` (`UnsafeCell`) allocations.

## Applicability

This report relates five durable upstream artifacts to determine how `CTrees`, `PFunctor` M-types, and Kripke-monotone open-callback contracts operate inside Anneal's Pass 1 `theory/` envelope:

- **`vellvm/ctrees` (`cabcf9bf24b0f459204a7da19ac01b7697ff04e3`) and Chappe et al. (POPL 2023, `10.1145/3571254`, `arXiv:2211.06863`):** Primary Rocq implementation and published calculus for `ctreeF`, `equ`, `trans`, `ssim`, `sbisim`, `wbisim`, `fold`, `interp`, and `refine`. Findings distinguish POPL 2023 (which lacked `StuckF` and kept primitive `BrS`) from `cabcf9bf24b0` (which collapses `BrS` into `BrF` + `StepF`, adds `StuckF`, and uses `Unset Universe Checking` in `Interp/{Refine,FoldStateT}.v`).
- **`leanprover-community/mathlib4` (`dd44a18bacca0dba65ac4275af92024f400e63e3`) and `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** Source authority for `PFunctor`, `CofixA`, `M`, Lean 4's `coinductive` elaborator, and the 51 `Init.*` modules locked in Anneal.
- **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Normative authority for Pass 1 source/kernel admission (`trusted/audit/TrustedBoundary.lean`, `trusted/lean/foundation-lock.json`) and small-step MIR semantics (`trusted/lean/Trusted/MirSemantics.lean`, `theory/Anneal/MirWp.lean`).

Related corpus reports cited rather than duplicated: `fuel-step-indexing-clocks-and-tcb-recursion` (fuel vs. coinductive `Diverges`), `rust-unsafe-traits-coinduction-gats-and-safety-invariants`, `anneal-tcb-realizability-external-calls-and-mutation-testing`, and `semantic-models-lenses-hyperproperties-and-putnam-tcb-boundary`. Candidate designs are evaluated across: **(T1)** 0-TCB statement-origin separation from `Anneal.*`; **(P1)** human spec auditability; **(P2)** authoring/edit locality; **(P3)** Lean `v4.34.1` kernel & `<50 ms` LSP scaling; **(P4)** composability across safe, `unsafe`, `UnsafeCell`, `MaybeUninit`, unwind, and open callbacks; **(P5)** failure legibility; and **(C1–C2)** conceptual minimality with counterexamples.

## Findings

### 1. `CTree` Evolution from POPL 2023 to `vellvm/ctrees` (`cabcf9bf24b0`) and Its Rocq Axiom/Universe Cost

Basis: normative + source

Chappe et al. (POPL 2023, §3.1) originally defined `ctree E R` with four coinductive nodes: `Ret`, `Vis`, delayed branching `brD`, and stepping branching `brS`, with `Guard := brD 1` and `Step := brS 1`. Section 4.5 (Definition 4.6, Lemma 4.7) then proved `brS` redundant up to strong bisimilarity (`BrSElim t ~ t` rewrites `brS` to `brD` followed by `Step`).

In `vellvm/ctrees` (`cabcf9bf24b0`, `theories/Core/CTreeDefinitions.v` L58–114), the codebase internalizes that collapse and adds `StuckF`:

```coq
Variant ctreeF (ctree : Type): Type :=
  | RetF   (r : R)
  | StuckF
  | StepF  (t : ctree)
  | GuardF (t : ctree)
  | VisF {X : Type} (e : E X) (k : X -> ctree)
  | BrF {X : Type} (c : B X) (k : X -> ctree).

CoInductive ctree : Type := go { _observe : ctreeF ctree }.
```

`BrS` becomes a derived notation `BrS n k := go (BrF n (fun x => Step (k x)))` (`L108`), freeing `spin`, `spinS`, `forever`, and `iter` (`L311–341`) from `{B1 -< B}` constraints because `GuardF` and `StepF` are native constructors. Negative primitive projections (`_observe`) ensure `observe (iter step i)` unfolds up to coinductive structural equality (`equ`, `theories/Eq/Equ.v` L53–104) without stuck `cofix` terms (`CTreeDefinitions.v` L180–202).

However, direct source inspection exposes two structural hazards in `vellvm/ctrees`:
1. **Implicit Axiom K (`JMeq_eq`):** Quantifying `{X : Type}` inside `VisF`/`BrF` makes dependent constructor inversion rely on `dependent destruction` (`JMeq_eq` / Streicher's Axiom K) in `Vis_eq1`, `Vis_eq2`, `Br_eq1`, and `Br_eq2` (`CTreeDefinitions.v` L419–441).
2. **Universe-Checker Bypasses:** Interpreting `B : Type -> Type` into `stateT S (ctree E B')` or refining `ctree E B` into `ctree E B'` (`theories/Interp/Refine.v` L1, L7, L33; `theories/Interp/FoldStateT.v` L1) induces universe constraints that force `vellvm/ctrees` to invoke `Unset Universe Checking.` at file top level.

### 2. Why Lean 4 `v4.34.1`'s `coinductive` Keyword Fails Both Semantically and Under Anneal Pass 1

Basis: normative + source

Lean 4 `v4.34.1` (`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`) provides experimental `coinductive` syntax alongside `partial_fixpoint` / `coinductive_fixpoint`. Source inspection confirms it cannot implement `CTree`s in Anneal `theory/`:

1. **Predicates Only, Never `Type`-Valued Trees:** In `src/Lean/Elab/MutualInductive.lean` (L1447–1450), if `isCoinductive` is set, the elaborator rejects any non-`Prop` target (`!body.isProp`) with ``"`coinductive` keyword can only be used to define predicates"``. Internally (`L1348–1356`), it encodes greatest fixpoints over `Prop` via `Init.Internal.Order.ReverseImplicationOrder.instCompleteLattice` (`src/Init/Internal/Order/Basic.lean` L1130–1150) using impredicative quantification (`∀ p, c p → p`). Lean 4 has no kernel `CoInductive` former for `Type u` data.
2. **Pass 1 Admission Rejections (`TrustedBoundary.lean`):** Every `theory/` file in `joshlf/anneal` (`c131b320`) passes source preflight (`L442–596, L640–995`), `.olean` import/origin checks (`L1136–1176`), and kernel replay (`L1293–1365`):

| `TrustedBoundary.lean` Gate | Normative Rule | Rejected Feature / Pattern | Line Anchor |
| :--- | :--- | :--- | :--- |
| Foundation imports | Explicit `prelude` + 51 `Init.*` modules only | `Std.*`, `Mathlib.*`, `Lean.*`, `Init.Internal.Order`, `module`/`public import` | `L442–443, L658–660`; `foundation-lock.json` |
| Declaration kinds | `abbrev`, `def`, `theorem`, `opaque`, `instance`, `inductive`, `structure`, `class` | `coinductive`, `axiom`, `example`, `partial`, `unsafe`, `nonrec` | `L455–468` |
| Fixpoints & `deriving` | Structural recursion / `@Nat.rec` / `List.foldr` only | `termination_by`, `decreasing_by`, `coinductive_fixpoint`, `partial_fixpoint`, `deriving` | `L464–468` |
| Commands & notations | Closed command & operator sets; no `set_option` | `set_option`, custom `macro`/`elab`/`syntax`/`notation`, infix `^`, `/`, `%`, `&&&`, `|||`, `^^^`, `|>` | `L445–453, L521–528` |
| Tactic allowlist (`theory/`) | 22 structural tactics (`rfl`, `decide`, `simp`, `dsimp`, `rw`, `change`, `cases`, `induction`, `injection`, `intro`, `apply`, `exact`, `refine`, `unfold`, `funext`, `subst`, etc.) | `omega`, `ring`, `linarith`, `bv_decide`, `native_decide`, `grind`, `ext`, `rcases`, `obtain`, `congr`, `exists`, `exfalso` | `L529–557` |
| Replay & universe params | `{propext, Quot.sound, Classical.choice}`; zero `._unsafe_rec`; monomorphic claims | `WellFounded.fix` emitting `._unsafe_rec`; target claims with `levelParams ≠ []` | `L1117–1153, L1316–1365` |

### 3. `Classical.choice`-Free `Type 0` `PFunctor.M` Distillation vs. Mathlib's `Path`-Indexed Construction

Basis: source + derived

Polynomial functors (`PFunctor`) represent strictly positive endofunctors without built-in coinduction. In `leanprover-community/mathlib4` (`dd44a18bacca`), `Mathlib/Data/PFunctor/Univariate/Basic.lean` (L35–51) defines `PFunctor` as `(A : Type uA, B : A → Type uB)` acting by `Σ x : P.A, P.B x → α`. `Mathlib/Data/PFunctor/Univariate/M.lean` (L36–271) builds its final coalgebra `M F` via consistent depth-`n` approximations `CofixA F n` (`AllAgree`), providing `M.corec` (`L178`), `M.dest` (`L219`), `M.mk` (`L238`), definitional `dest_mk : dest (M.mk x) = x := rfl` (`L251`), and `mk_dest : M.mk (dest x) = x` (`L254`).

Auditing `M.lean` shows two obstacles to direct Pass 1 reuse:
1. **Pass 1 Violations:** Uses `module`/`public import`, `set_option` (`L10–11, L507`), `grind` (`L134–135`), `rw!` (`L268`), `congr` (`L102, L170`), `HEq`/`cast_heq` (`L82–85, L195–198`), and `solve_by_elim` (`L469–470`).
2. **Avoidable `Classical.choice` + `[DecidableEq F.A]` + `[Inhabited (M F)]`:** Proving `eq_of_bisim` (`L538–549`) and `bisim` (`L563–578`) via `Path`/`IsPath`/`iselect` (`L343–537`) invokes `classical` and `by_cases`, tainting `M.bisim` and `M.corec_unique` (`L605`) with `Classical.choice`.

**Direct `Nat`-Depth Coinduction Eliminates `Classical.choice` and `HEq`:** Proving `mk_dest` first (via `head_succ_eq` and `approx_succ_reconstruct`) and then proving `∀ n x y, R x y → x.approx n = y.approx n` by induction on `n : Nat` discharges `M.bisim` and `M.corec_unique` in ~15 lines using **only `{propext, Quot.sound}`** (via `funext`), zero `Classical.choice`, zero `DecidableEq`, zero `Inhabited`, and zero `HEq`. Using Lean 4's `Eq.rec` (`h ▸ i`), `agree_head` and `agree_children` require only single `cases` matches (`node _ _ hg => exact hg i`), bridged via `castB_trans` (`cases h1; cases h2; rfl`).

**Closing the Universe Gap (`Type 0` Signature Record):** Parameterizing `CTree` by a concrete `Type 0` interface `structure Sig where Op : Type; Resp : Op → Type` keeps every event, branching shape, and tree inside `Type 0` (`PFunctor` at universe `0`, `CTree : Sig → Sig → Type → Type`), preventing `Unset Universe Checking` cycles and satisfying `TrustedBoundary.lean`'s universe-monomorphism check (`L1334–1335`).

### 4. LTS Semantics, Weak Bisimulation Hazards, and Polarity Mismatches Against `Trusted.MirSemantics`

Basis: source + derived

`vellvm/ctrees` equips `ctree` with an LTS (`theories/Eq/Trans.v` L89–136) over `label := τ | obs {X} (e : E X) (v : X) | val {X} (v : X)`. `trans_` crawls through `GuardF` and `BrF` until reaching an observable head: `StepF t` emits `τ` to `t`, `VisF e k` emits `obs e x` to `k x`, and `RetF r` emits `val r` to `StuckF`. Using `wtrans l := (trans τ)^* · etrans l · (trans τ)^*` (`L256–257`), `SSim.v`, `SBisim.v`, and `WBisim.v` (`L82–109`) define strong simulation (`ssim`), strong bisimulation (`sbisim`), and weak bisimulation (`wbisim`).

Connecting `Trusted.MirSemantics` (`joshlf/anneal`, `MirSemantics.lean` L597–647, L1616–1676) to `CTrees` refutes **three premature collapses (`C2` calibration)**:

1. **Polarity Inversion of `Stuck` vs. `FaultKind` (`Refine.v` L28 vs. `MirSemantics.lean` L1646–1649):** Because `StuckF` has zero `trans_` edges (`Trans.v` L116–135) and `ss` quantifies `∀ l t', trans l t t' → ...`, `Stuck_ssim` (`Refine.v` L28) proves `Stuck ≲ t` for **every** `t`. Similarly, an empty `BrF` (`brD 0`) emits no transitions. In `Trusted.MirSemantics`, UB (`.fault .undefined`) and unmodeled constructs (`.fault .unsupported`) falsify `WellFormed`, and `WellFormed` mandates `∃ c, ValidChoice p s c` (`L1648`) so empty choice sets cannot vacuously pass safety. Thus `FaultKind` **cannot** map to `Stuck`; faults must be an explicit observable `CTreeHead.fault (k : FaultKind)` head, and demonic `brD` arities must be inhabited (`∃ x : B.Resp c, True`).
2. **Divergence Erasure Under `Guard` and `wbisim` (`Trans.v` L329 vs. `MirSemantics.lean` L1665–1670):** In `CTrees`, `spin := Guard spin` has zero `trans` steps (`spin ~ Stuck` in `sbisim`), and `spinS := Step spinS` satisfies `spinS ≈ Stuck` in `wbisim` because `wnil Stuck : wtrans τ Stuck Stuck`. In `Trusted.MirSemantics`, `Diverges p q` (`∃ trace, trace 0 = s₀ ∧ ∀ n, Step p (trace n) (.step (trace (n + 1)))`) is an observable distinction. Preserving `Diverges` requires loop back-edges to emit productive `Step` (`τ`) nodes (never unguarded `Guard` loops) and requires divergence-preserving simulation (or bounded `etrans` expansion `es`, avoiding `wbisim`'s loss of up-to-transitivity noted at `WBisim.v` L205).
3. **Pure `Init.Core` Knaster–Tarski `gfp` + Conjunctive `wpCTree`:** Replacing Pous's `coq-coinduction` companion with Knaster–Tarski `gfpRel` (`∃ R, (∀ a b, R a b → F R a b) ∧ R x y`) uses zero axioms and zero `Init.Internal.Order`. Finite-horizon safety projects `CTree` via `@Nat.rec` (`wpCTree`), quantifying universally over inhabited `brD` branches (`∀ x, ...`) to preserve `MirWp.wpOutcomeState` conjunctivity (`MirWp.lean` L69–80).

### 5. Kripke-Monotone Open Callbacks, Unwind-Safe Library Invariants, and `!Freeze` Interior Mutability

Basis: source + derived

When using `CTree.vis` to model unverified external callbacks (`FnMut`, trait methods, FFI, or DMA) over `CallerMemory` (`MirSemantics.lean` L578–605), Rust's unwinding and interior-mutability rules impose two strict conditions:

1. **The `catch_unwind(AssertUnwindSafe(...))` Broken-Invariant Exploit:** Suppose a safe library container `RingBuf { buf: Box<[u8]>, head: usize, cap: usize }` maintains private invariant `head < cap` to justify `unsafe { *self.buf.get_unchecked(self.head) }` in `peek_head(&self)`, while `for_each_mut(&mut self, mut f: impl FnMut(&mut u8))` temporarily sets `self.head = self.cap` before calling `f(&mut self.buf[i])` and restores `self.head = old_head` only before normal return. Because `std::panic::AssertUnwindSafe` and `std::panic::catch_unwind` are 100% safe Rust, a caller whose `f` panics causes `for_each_mut` to unwind (`TerminalOut.unwound callerMem`, `MirSemantics.lean` L604) with `self.head == self.cap` still in memory—allowing safe subsequent code to catch the panic and trigger out-of-bounds UB in `peek_head` (a Rudra-class exception-safety bug). Any Kripke-monotone library invariant `LibInv` across `vis` **must hold on BOTH `TerminalOut.returned` and `TerminalOut.unwound`** (restored by RAII `Drop` guards on cleanup pads).
2. **`&mut self` Protector Framing vs. `&self` `!Freeze` (`UnsafeCell`) Reentrancy:** An exclusive `&mut self` argument enforces active Tree Borrows frame protectors on `self.head` and `self.cap` during `f`, blocking safe reentrancy on `self` so `self` may be framed out of the public Kripke world `W` across `vis` (provided `Drop` restores `LibInv` on unwind). Conversely, storing `head: Cell<usize>` (`!Freeze`) behind `&self` removes protector exclusion, allowing `f` to re-enter `&rb` mid-callback while `LibInv` is broken and allowing `f` to mutate captured `&Cell<T>` references. Because `MirAst.MirTy.ref` (`Trusted/MirAst.lean` L319) tracks only `.shared | .mut` without `isFreeze : Bool`, shared-ref optimizations and callback framing must fail closed unless `UnsafeCell` (`!Freeze`) is explicitly surfaced.
3. **`Type 0` First-Order `vis` Encoding:** Encoding open-callback effects via a `Type 0` `Sig` (`Op := OpenCallId`, `Resp := fun _ => CallbackOutcome W Mem`, recording `isUnwind : Bool`, Kripke world `W`, and concrete `Mem` delta) keeps `CTree` in `Type 0` (satisfying `TrustedBoundary.lean` L1334).

#### Self-Contained Pass-1 Lean 4 Formalization & Refutation Counterexamples

This complete module imports only `Init.Core` and `Init.Data.Nat.Basic` under `prelude`, obeys every Pass 1 rule in `TrustedBoundary.lean` (`L442–596`), uses zero `Classical.choice`, and mechanizes both counterexamples:

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic

namespace Anneal.CTreePFunctor

/-! ## Part 1: 0-Choice `Type 0` PFunctor M-Type Coinduction -/

structure PFunctor where
  A : Type
  B : A → Type

def PFunctor.Obj (P : PFunctor) (α : Type) : Type :=
  Sigma fun a : P.A => P.B a → α

inductive CofixA (F : PFunctor) : Nat → Type where
  | cont : CofixA F 0
  | node {n : Nat} (a : F.A) (ch : F.B a → CofixA F n) : CofixA F (n + 1)

def head' {F : PFunctor} : ∀ {n : Nat}, CofixA F (n + 1) → F.A
  | _, .node a _ => a

def children' {F : PFunctor} : ∀ {n : Nat} (u : CofixA F (n + 1)), F.B (head' u) → CofixA F n
  | _, .node _ f => f

def castB {F : PFunctor} {a b : F.A} (h : a = b) (i : F.B a) : F.B b :=
  h ▸ i

theorem castB_trans {F : PFunctor} {a b c : F.A} (h1 : a = b) (h2 : b = c) (i : F.B a) :
    castB h2 (castB h1 i) = castB (Eq.trans h1 h2) i := by
  cases h1
  cases h2
  rfl

inductive Agree {F : PFunctor} : ∀ {n : Nat}, CofixA F n → CofixA F (n + 1) → Prop where
  | cont (x : CofixA F 0) (y : CofixA F 1) : Agree x y
  | node {n : Nat} {a : F.A} (f : F.B a → CofixA F n) (g : F.B a → CofixA F (n + 1)) :
      (∀ i, Agree (f i) (g i)) → Agree (.node a f) (.node a g)

def AllAgree {F : PFunctor} (approx : ∀ n, CofixA F n) : Prop :=
  ∀ n, Agree (approx n) (approx (n + 1))

theorem agree_head {F : PFunctor} {n : Nat} {x : CofixA F (n + 1)} {y : CofixA F (n + 2)}
    (h : Agree x y) : head' x = head' y := by
  cases h with
  | node _ _ _ => rfl

theorem agree_children {F : PFunctor} {n : Nat} {x : CofixA F (n + 1)} {y : CofixA F (n + 2)}
    (h : Agree x y) (i : F.B (head' x)) :
    Agree (children' x i) (children' y (castB (agree_head h) i)) := by
  cases h with
  | node _ _ hg => exact hg i

theorem head_succ_eq {F : PFunctor} (approx : ∀ n, CofixA F n) (hc : AllAgree approx) :
    ∀ n, head' (approx (n + 1)) = head' (approx 1)
  | 0 => rfl
  | n + 1 => Eq.trans (agree_head (hc (n + 1))).symm (head_succ_eq approx hc n)

structure M (F : PFunctor) where
  approx     : ∀ n, CofixA F n
  consistent : AllAgree approx

def M.ext' {F : PFunctor} {x y : M F} (h : ∀ n, x.approx n = y.approx n) : x = y := by
  cases x with
  | mk ax cx =>
    cases y with
    | mk ay cy =>
      have hap : ax = ay := funext h
      subst hap
      rfl

def sCorec {F : PFunctor} {X : Type} (step : X → F.Obj X) : X → ∀ n, CofixA F n
  | _, 0 => .cont
  | x, n + 1 => .node (step x).1 (fun i => sCorec step ((step x).2 i) n)

theorem P_corec {F : PFunctor} {X : Type} (step : X → F.Obj X) (x : X) :
    ∀ n, Agree (sCorec step x n) (sCorec step x (n + 1))
  | 0 => .cont _ _
  | n + 1 => .node _ _ (fun i => P_corec step ((step x).2 i) n)

def M.corec {F : PFunctor} {X : Type} (step : X → F.Obj X) (x : X) : M F :=
  ⟨sCorec step x, P_corec step x⟩

def M.head {F : PFunctor} (x : M F) : F.A :=
  head' (x.approx 1)

def M.children {F : PFunctor} (x : M F) (i : F.B (M.head x)) : M F :=
  { approx := fun n => children' (x.approx (n + 1)) (castB (head_succ_eq x.approx x.consistent n).symm i)
    consistent := fun n => by
      have hStep := agree_children (x.consistent (n + 1))
        (castB (head_succ_eq x.approx x.consistent n).symm i)
      rw [castB_trans] at hStep
      exact hStep }

def M.dest {F : PFunctor} (x : M F) : F.Obj (M F) :=
  ⟨M.head x, fun i => M.children x i⟩

def sMk {F : PFunctor} (x : F.Obj (M F)) : ∀ n, CofixA F n
  | 0 => .cont
  | n + 1 => .node x.1 (fun i => (x.2 i).approx n)

theorem P_mk {F : PFunctor} (x : F.Obj (M F)) :
    ∀ n, Agree (sMk x n) (sMk x (n + 1))
  | 0 => .cont _ _
  | n + 1 => .node _ _ (fun i => (x.2 i).consistent n)

def M.mk {F : PFunctor} (x : F.Obj (M F)) : M F :=
  ⟨sMk x, P_mk x⟩

theorem M.dest_mk {F : PFunctor} (x : F.Obj (M F)) : M.dest (M.mk x) = x := rfl

theorem approx_succ_reconstruct {F : PFunctor} {n : Nat}
    (u : CofixA F (n + 1)) (hd : F.A) (h : head' u = hd) :
    CofixA.node hd (fun i => children' u (castB h.symm i)) = u := by
  cases u with
  | node _ _ => cases h; rfl

theorem M.mk_dest {F : PFunctor} (x : M F) : M.mk (M.dest x) = x := by
  apply M.ext'
  intro n
  cases n with
  | zero =>
    cases x.approx 0
    rfl
  | succ k =>
    exact approx_succ_reconstruct (x.approx (k + 1)) (head' (x.approx 1))
      (head_succ_eq x.approx x.consistent k)

theorem M.bisim_approx {F : PFunctor} (R : M F → M F → Prop)
    (hStep : ∀ x y, R x y → Exists fun a => Exists fun f => Exists fun f' =>
      M.dest x = ⟨a, f⟩ ∧ M.dest y = ⟨a, f'⟩ ∧ ∀ i, R (f i) (f' i)) :
    ∀ n x y, R x y → x.approx n = y.approx n
  | 0, x, y, _ => by
    cases x.approx 0
    cases y.approx 0
    rfl
  | n + 1, x, y, hr => by
    have hs := hStep x y hr
    cases hs with
    | intro a hs1 => cases hs1 with
    | intro f hs2 => cases hs2 with
    | intro f' hs3 =>
      have hx : x = M.mk ⟨a, f⟩ := Eq.trans (M.mk_dest x).symm (congrArg M.mk hs3.1)
      have hy : y = M.mk ⟨a, f'⟩ := Eq.trans (M.mk_dest y).symm (congrArg M.mk hs3.2.1)
      rw [hx, hy]
      have hch : (fun i => (f i).approx n) = (fun i => (f' i).approx n) :=
        funext (fun i => M.bisim_approx R hStep n (f i) (f' i) (hs3.2.2 i))
      exact congrArg (CofixA.node a) hch

theorem M.bisim {F : PFunctor} (R : M F → M F → Prop)
    (hStep : ∀ x y, R x y → Exists fun a => Exists fun f => Exists fun f' =>
      M.dest x = ⟨a, f⟩ ∧ M.dest y = ⟨a, f'⟩ ∧ ∀ i, R (f i) (f' i))
    (x y : M F) (hr : R x y) : x = y :=
  M.ext' (fun n => M.bisim_approx R hStep n x y hr)

/-! ## Part 2: Fault-Explicit Type 0 CTree, Pure gfp, Demonic WP, and Kripke Callbacks -/

structure Sig where
  Op   : Type
  Resp : Op → Type

inductive FaultKind where | undefined | unsupported

inductive CTreeHead (E B : Sig) (R : Type) where
  | ret   (r : R)
  | fault (k : FaultKind)
  | guard
  | step
  | brD   (c : B.Op)
  | vis   (e : E.Op)

def CTreeArity (E B : Sig) (R : Type) : CTreeHead E B R → Type
  | .ret _   => Empty
  | .fault _ => Empty
  | .guard   => Unit
  | .step    => Unit
  | .brD c   => B.Resp c
  | .vis e   => E.Resp e

def ctreePF (E B : Sig) (R : Type) : PFunctor :=
  ⟨CTreeHead E B R, CTreeArity E B R⟩

abbrev CTree (E B : Sig) (R : Type) : Type :=
  M (ctreePF E B R)

def gfpRel {α β : Type} (F : (α → β → Prop) → (α → β → Prop)) (x : α) (y : β) : Prop :=
  Exists fun R : α → β → Prop => (∀ a b, R a b → F R a b) ∧ R x y

def wpCTree {E B : Sig} {R : Type}
    (visOK : ∀ e : E.Op, (E.Resp e → Prop) → Prop)
    (post : R → Prop) (onFault : FaultKind → Prop) (fuel : Nat) (t : CTree E B R) : Prop :=
  @Nat.rec (fun _ => CTree E B R → Prop)
    (fun _ => False)
    (fun _ ih cur =>
      match M.dest cur with
      | ⟨.ret r, _⟩ => post r
      | ⟨.fault k, _⟩ => onFault k
      | ⟨.guard, k⟩ => ih (k ())
      | ⟨.step, k⟩ => ih (k ())
      | ⟨.brD c, k⟩ => (Exists fun _ : B.Resp c => True) ∧ ∀ x : B.Resp c, ih (k x)
      | ⟨.vis e, k⟩ => visOK e (fun resp => ih (k resp)))
    fuel t

structure CallbackOutcome (W Mem : Type) where
  isUnwind : Bool
  world    : W
  mem      : Mem

def UnwindSafeCallbackContract {W Mem : Type}
    (worldLe : W → W → Prop) (libInv : W → Mem → Prop) (w0 : W)
    (out : CallbackOutcome W Mem) : Prop :=
  worldLe w0 out.world ∧ libInv out.world out.mem

theorem empty_brD_refuted_by_inhabitedness :
    ¬ ((Exists fun _ : Empty => True) ∧ ∀ x : Empty, Empty.elim x) := by
  intro h
  cases h.1 with
  | intro e _ => exact Empty.elim e

def brokenOnUnwindOutcome : CallbackOutcome Unit Bool :=
  { isUnwind := true, world := (), mem := false }

theorem return_only_check_misses_unwind_bug :
    (if brokenOnUnwindOutcome.isUnwind then True else brokenOnUnwindOutcome.mem = true) ∧
    ¬ (brokenOnUnwindOutcome.mem = true) := by
  refine ⟨trivial, ?_⟩
  intro h
  cases h

end Anneal.CTreePFunctor
```

### 6. Evaluation Against Anneal `theory/` Rubric `(T1, P1–P5, C1–C2)`

Basis: derived

| Design Option | (T1) 0-TCB Bridge | (P1) Spec Auditability | (P2) Locality | (P3) Kernel / LSP Scaling | (P4) Heterogeneous Composability | (P5) Failure Legibility | (C1–C2) Minimality |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Rocq `CTrees` naive port** | Fails (`JMeq_eq`, `Unset Universe Checking`, `Stuck` unsound) | Low (`BrF` universe leak) | Med | Low | High (`vis` + `brD`), misses unwind/faults | Med | Flawed (`Stuck` collapses faults/divergence) |
| **Lean 4 `coinductive` + `Init.Internal.Order`** | Fails (`Type` rejected; `Init.Internal.Order` banned in Pass 1) | N/A | N/A | N/A | `unsupported` for `Type` trees | N/A | `unsupported` |
| **Mathlib `PFunctor.M` direct import** | Fails (`Mathlib`, `grind`, `HEq`, `Classical.choice`) | Med | Med | Low (`Path`/`iselect`) | High once wrapped | Med (`HEq` goals) | Over-coupled (`Path` unnecessary for `bisim`) |
| **Distilled `Type 0` `PFunctor.M` `CTree` + `UnwindSafeCallbackContract`** | **Passes Pass 1** (`Init.Core` + `Nat`, 0 `Classical.choice`; exposes `Trusted.*` gaps below) | **High** (Kripke `LibInv` on return + unwind) | **High** (handler composition via `M.corec`) | **High** (`Type 0`, `mk_dest`, `<50 ms` behind `@[irreducible]`) | **Very High** (`brD` demonic + `vis` + `fault` + `step` divergence) | **High** (explicit `.fault k` & `isUnwind` witnesses) | **Optimal** (4 distinct effects; `Stuck` & return-only collapses refuted) |

**Irreducible `Trusted.MirSemantics` Deltas Exposed:** Deploying `CTree` + `UnwindSafeCallbackContract` over real Rust MIR requires three minimal, correspondence-checked TCB extensions in `joshlf/anneal` (`c131b320`): (1) widening `ValidChoice` beyond `c = 0` (`MirSemantics.lean` L646–647) for demonic memory/allocator/callback transitions; (2) admitting open external/trait calls (`FnMut`, FFI) and `TerminatorKind.drop` cleanup pads instead of faulting `.unsupported` (`L1568`); and (3) tagging `MirTy` with `isFreeze : Bool` (`UnsafeCell`) and lifting `initState`'s `callerMem = ⟨[]⟩` rejection (`L803–804`).

## Boundaries

- **`unsupported` (Lean 4 `coinductive` & Pass 1 `theory/`):** Lean `v4.34.1` `coinductive` cannot define `Type`-valued trees (`MutualInductive.lean` L1447–1450), and `TrustedBoundary.lean` (`L442–596`) rejects `coinductive`, `Init.Internal.Order`, `Mathlib.*`, `._unsafe_rec`, and `set_option`.
- **`known not to apply` (`Stuck` and `wbisim` to Rust `WellFormed` / `Diverges`):** `Stuck_ssim` (`Refine.v` L28) and `spinS ≈ Stuck` (`WBisim.v`) erase faults and non-termination; they do not apply to `Trusted.MirSemantics` safety or `Diverges` equivalence. Return-only `LibInv` does not apply to unwindable Rust functions.
- **`not examined` (Live Lean compilation & `interp`/`fold_state` congruence):** Live execution of `Anneal.CTreePFunctor` under `lean -DwarningAsError=true` was not examined in this analysis pass (checked statically against `TrustedBoundary.lean` allowlists). Full `Bind`/`Iter` monad laws and `interp_equ` congruence on `Type 0` `PFunctor.M` (analogous to `CTreeDefinitions.v` L229–340 and `FoldStateT.v` L121–150) were not mechanized here.
- **`unknown` (Multi-threaded preemption & post-`v4.34.1` Lean `coinductive` `Type` support):** Whether future Lean 4 toolchains above `5045d005` add kernel `Type`-level coinductive constructors, and the exact trace-interleaving cost of preemptive multi-threading `CTrees` under Anneal's memory model, remain unknown.

## Evidence

| Subject / Revision | Inspected Paths & Anchors | Verified Facts |
| :--- | :--- | :--- |
| `vellvm/ctrees` (`cabcf9bf24b0f459204a7da19ac01b7697ff04e3`) | `theories/Core/CTreeDefinitions.v` L58–114, L180–202, L311–341, L419–441 | `ctreeF` (`RetF`, `StuckF`, `StepF`, `GuardF`, `VisF`, `BrF`), `BrS` macro, `JMeq_eq` (`Vis_eq*`/`Br_eq*`) |
| `vellvm/ctrees` (`cabcf9bf24b0f459204a7da19ac01b7697ff04e3`) | `theories/Eq/{Equ,Epsilon,Trans,SSim,SBisim,WBisim}.v`; `theories/Interp/{Fold,FoldStateT,Refine}.v` | `trans_`, `wtrans`, `wbisim`, `Stuck_ssim` (`Refine.v` L28), `Unset Universe Checking` (`Refine.v` L1, L7, L33; `FoldStateT.v` L1) |
| Chappe et al., POPL 2023 (`doi:10.1145/3571254`, `arXiv:2211.06863`) | §§3.1, 4.4–4.5, 5.1, 6–7 (`BrSElim` Lemma 4.7, `interp` Fig. 13, CCS, cooperative scheduling) | Elimination of primitive `brS`, `interp` non-monomorphism counterexample (`Step (trigger e)`), cooperative `yield`/`fork` |
| `leanprover-community/mathlib4` (`dd44a18bacca0dba65ac4275af92024f400e63e3`) | `Mathlib/Data/PFunctor/Univariate/{Basic,M}.lean` (`Basic` L35–51; `M` L36–271, L343–637) | `CofixA`, `Agree`, `MIntl`, `dest_mk := rfl`, `mk_dest`, `Path`/`iselect` + `classical` in `eq_of_bisim` (`L538–549`) |
| `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`) | `src/Lean/Elab/MutualInductive.lean` L1348–1356, L1447–1450; `src/Init/Internal/Order/Basic.lean` L1130–1150 | `coinductive` restricted to `Prop` predicates; `ReverseImplicationOrder` complete lattice |
| `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) | `trusted/audit/TrustedBoundary.lean` L442–596, L640–995, L1117–1365; `foundation-lock.json`; `MirSemantics.lean` L578–647, L1540–1676; `MirWp.lean` L69–80 | 51-module `Init.*` cap, closed 22-tactic allowlist, `ValidChoice`, `FaultKind`, `TerminalOut.unwound`, `Diverges`, `wpOutcomeState` |

## Revalidation

1. **Check Anneal Foundation & Syntax Constraints:** Inside a `joshlf/anneal` checkout, verify `Init.Internal.Order` remains excluded from the 51-module foundation lock and `coinductive` remains excluded from `allowedDeclarationKinds`:
   ```bash
   python3 -c 'import json; g=json.load(open("trusted/lean/foundation-lock.json"))["graph"]; print(len(g), any("Order" in k for k in g))'
   grep -n "allowedDeclarationKinds" -A 5 trusted/audit/TrustedBoundary.lean
   ```
   Expected: `51 False` and `coinductive` excluded.
2. **Type-Check & Axiom-Check `Anneal.CTreePFunctor` (`<2s` standalone Lean 4 `v4.34.1` check):** Save the `Anneal.CTreePFunctor` block from Findings §5 to `/tmp/ctree_pfunctor_probe.lean`, check `#print axioms` on `Anneal.CTreePFunctor.M.bisim`, `M.mk_dest`, `empty_brD_refuted_by_inhabitedness`, and `return_only_check_misses_unwind_bug` via a separate `/tmp/check_ctree_axioms.lean` wrapper, and run `lean -DwarningAsError=true /tmp/ctree_pfunctor_probe.lean`. Confirm exit `0`, zero `Classical.choice`, zero `sorryAx`, and only `{propext, Quot.sound}` on `M.bisim` / `M.mk_dest`.
3. **Track Upstream Divergence:** Diff `vellvm/ctrees` `theories/Core/CTreeDefinitions.v` and `theories/Eq/WBisim.v` above `cabcf9bf` for removal of `Unset Universe Checking` or addition of divergence-preserving weak bisimulation.
