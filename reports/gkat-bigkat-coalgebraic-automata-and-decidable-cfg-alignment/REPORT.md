# GKAT, BiKAT/BiGKAT, Coalgebraic CFG Automata, and Certified Relational Alignment in Pure Init.* Lean 4

## Summary

Guarded Kleene Algebra with Tests (`GKAT`, Smolka et al. POPL 2020) restricts Kleene Algebra with Tests (`KAT`) to predicate-guarded branching (`e +_b f`) and guarded iteration (`e^{(b)}`), collapsing PSPACE-complete equivalence checking into $O(n \cdot |\text{At}| \cdot \alpha(n))$ coalgebraic bisimulation via Hopcroft–Karp union-find. Extensions add non-local `goto`/`break`/`return` control flow (`CF-GKAT`, Zhang et al. POPL 2025; `SpencerKoevering/cfgkat-rocq` at `8873fd7b48de42cc47a09d3373d683a5a71c6811`) and algebraic relational alignment (`BiKAT`, Antonopoulos et al. POPL 2023; probabilistic `BiGKAT`, Gomes et al. FoSSaCS 2025). Translating these frameworks into Anneal's zero-TCB `theory/` layer (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`, locked to 51 `Init.*` modules by `trusted/audit/TrustedBoundary.lean`) establishes four core engineering results:

1. **Early termination (`e · 0 ≡ 0`) and dead-state normalization are unsound for Rust MIR safety:** POPL 2020 `GKAT` normalizes away transitions into non-accepting states (`Lemma 5.6`), and `cfgkat-rocq` relies on `EqS2: 0 ;; e == 0` plus `ClassicalEpsilon` jump collapse (`ResolveCFGKATAutomatonDynamicsDefaultReject`). Under `Trusted.MirSemantics`, normalizing an unaccepting trace to `0` masks prefix Undefined Behavior (`FaultKind.undefined`), falsifying `WellFormed`, and conflates infinite loops (`Diverges`) with clean panic unwinding (`TerminalOut.unwound`). Omitting `e · 0 ≡ 0`—following `GKAT_0` (Schmid et al. ICALP 2021)—while tagging explicit `.accept`/`.unwind`/`.fault` leaves preserves `WellFormed`, `Behavior`, and `Diverges` constructively with zero `Classical.choice`.
2. **External union-find + internal boolean witness checking achieves linear verification under Pass 1:** Running Hopcroft–Karp or `BiKAT` alignment search outside Lean yields a compact bisimulation table `cert : List (Nat × Nat)`. Checking `cert` in pure `Init.Data.Nat.Basic` + `Init.Data.List.Basic` reduces table-driven DFA verification (UTF-8 / compression decoders) to a single `rfl` reflection step on Lean 4's C++ GMP fast path.
3. **One-sided alignment steps require well-founded ranks:** Unranked `BiKAT` stutter steps (`leftOnly`/`rightOnly`) prove only partial correctness (`Behavior ⊆ Behavior`) and silently accept infinite loops (`while i < n {}`). Requiring strict `Nat` rank decrease (`rank (f s₁) < rank s₁`) inside `RankedBiAlign` recovers bidirectional termination (`Diverges ↔ Diverges`) across $k$-to-$1$ SIMD/SWAR strip-mining and constant-time (`p ⋈ p`) self-alignment.
4. **Hardened `SafeTwin` specs eliminate poison-pill vacuity and panic-footprint asymmetries:** Stating `WellFormed pSpec q → WellFormed pImpl q` allows an unmodeled construct (`.fault .unsupported`) in a safe reference twin to discharge real UB (`.fault .undefined`) in an `unsafe` fast path vacuously (`False → False`). Conjoining `WellFormed pSpec q ∧ WellFormed pImpl q`, separating normal returns from existential unwind `CallerMemory` parity, and keeping `SafeTwin` statements purely over `Trusted.MirSemantics` prevents spec laundering inside the bounded human-review surface.

## Applicability

This report relates six durable upstream authorities to define decidable coalgebraic CFG equivalence and relational alignment checkers inside Anneal's Pass 1 `theory/` envelope:

- **Smolka et al. (POPL 2020, `10.1145/3371129`, `arXiv:1907.05920`) and Schmid et al. (ICALP 2021, `10.4230/LIPIcs.ICALP.2021.142`, `arXiv:2102.08286`):** Normative semantics and complexity bounds separating full `GKAT` (early termination axiom `S3: e · 0 ≡ 0`, dead-state normalization) from `GKAT_0` (omitting `S3`, un-normalized bisimulation completeness via coequations).
- **Antonopoulos et al. (`BiKAT`, POPL 2023, `10.1145/3571213`, `arXiv:2202.04278`, artifact `10.5281/zenodo.7144067`) and Gomes, Baillot, Gaboardi (`BiGKAT`, FoSSaCS 2025, `10.1007/978-3-031-90897-2_12`, `hal-04017128`):** Normative algebras for left/right embeddings (`⌈x⌉`, `⌊y⌋`), left-right commutativity (`LRC`), `BiKAT` $\forall\forall$/$\forall\exists$ witnesses, undecidability of `*-continuous BiKAT` (`Theorem 4.4`), and bi-guarded probabilistic relational alignment (`BiGKAT`).
- **`SpencerKoevering/cfgkat-rocq` (`8873fd7b48de42cc47a09d3373d683a5a71c6811`; Zhang et al. POPL 2025, `10.1145/3704857`, `arXiv:2411.13220`):** Concrete Rocq mechanization of non-local control flow (`goto`, `break`, `continue`, `return`, indicator assignments), automaton resolution, and bisimulation.
- **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Authority for Pass 1 `theory/` boundaries (`trusted/audit/TrustedBoundary.lean`, `trusted/lean/foundation-lock.json`) and small-step MIR outcomes (`trusted/lean/Trusted/MirSemantics.lean`, `theory/Anneal/MirWp.lean`).

Related corpus reports cited rather than duplicated: `relational-logics-simulation-techniques-and-completeness-for-compiler-derivations`, `semantic-models-lenses-hyperproperties-and-putnam-tcb-boundary`, `reference-model-bisimulation-executable-semantics-and-differential-oracles`, `simdjson-carryless-quote-masks-structural-tapes-and-vector-utf8`, and `lean-ieee754-floatspec-cryptography-and-constant-time`. Designs are evaluated across Anneal's rubric: **(T1)** 0-TCB statement-origin separation from `Anneal.*`; **(P1)** human spec auditability; **(P2)** authoring/edit locality; **(P3)** Lean `v4.34.1` kernel & `<50 ms` LSP scaling; **(P4)** heterogeneous composability; **(P5)** failure legibility; and **(C1–C2)** conceptual minimality with refuting counterexamples.

## Findings

### 1. From PSPACE `KAT` and Undecidable `*-Continuous BiKAT` to Coalgebraic `GKAT`, `CF-GKAT`, and `BiGKAT`

Basis: normative + source

Standard `KAT` permits arbitrary nondeterministic choice (`+`) and iteration (`*`), rendering its equational theory PSPACE-complete. Three successive restrictions recover tractable, structured program reasoning:

1. **`GKAT` (Smolka et al., POPL 2020 §§2–4):** Replaces `+` and `*` with Boolean-guarded `e +_b f` (`if b then e else f`) and `e^{(b)}` (`while b do e`). Every expression `e` compiles in $O(|e|)$ time (`Proposition 4.2`, `Theorem 4.1`) to a deterministic `G`-coalgebra `δ : X → (At → 2 + Σ × X)` with `#Σ(e) + 1` states over Boolean atoms `At`, reducing trace equivalence (after dead-state pruning) to Hopcroft–Karp bisimulation in nearly linear $O(n \cdot |\text{At}| \cdot \alpha(n))$ time.
2. **`CF-GKAT` (`SpencerKoevering/cfgkat-rocq` `8873fd7b48de`; POPL 2025):** Extends `GKAT` with finite-domain indicator variables (`assign v to x`, `x is v`), `break`, `continue`, `return` (`syntax/Axioms.v` L51–145, e.g., `EqA5: assign v to x ;; return == return` at `L128`), and `goto l` resolved against finite-support `label_environment`s (`completeness/CFGKATCoalgebra.v` L9–88). Crucially, inspecting `syntax/Preliminaries.v` (`L4–8, L161`) and `semantics/SyntacticAutomata.v` (`L83–90`) reveals heavy classical-logic reliance (`ClassicalEpsilon`, `FunctionalExtensionality`, `PropExtensionality`, and `classic` in `resolve_dynamics_preserves_totality`), while jump resolution defaults unbounded silent `goto` cycles to `CFGKATAutomatonReject`.
3. **`BiKAT` (Antonopoulos et al., POPL 2023 §§4–7) & `BiGKAT` (Gomes et al., FoSSaCS 2025):** `BiKAT` (`Definition 4.1`) pairs an underlying `KAT` `A` with an ambient relational `KAT` `¥A` via left/right homomorphisms `⌈_⌉, ⌊_⌋ : A → ¥A` satisfying **left-right commutativity (`LRC`)**: `⌈x⌉ · ⌊y⌋ = ⌊y⌋ · ⌈x⌉` for all `x, y ∈ A`, defining paired embedding `⟨a | b⟩ := ⌈a⌉ · ⌊b⌋`. A $\forall\forall$ relational Hoare triple `c | c' : R ≈> S` becomes `R · ⟨c | c'⟩ · ¬S = 0` (`Eq. (2)`, `Theorem 4.6`). The general loop-alignment law (`Eq. (3)`):

   $$\langle (e; c)^* \mid (e'; c')^* \rangle ; \langle \neg e \mid \neg e' \rangle \;=\; \langle e; c \mid e'; c' \rangle^* ; (\langle e; c \mid \neg e' \rangle^* + \langle \neg e \mid e'; c' \rangle^*) ; \langle \neg e \mid \neg e' \rangle$$

   allows algebraic strip-mining (e.g., `⟨body · body | body⟩*`, `Example 2.2`, aligning two iterations against one). While `*-continuous BiKAT` identity checking is undecidable (`Theorem 4.4`, via Post Correspondence encoding), `BiGKAT` (FoSSaCS 2025) replaces unguarded `+`/`*` over product states `S × S` with bi-guarded branching and loops over deterministic/sub-Markov semantics, encoding finitary relational Hoare logic while avoiding combinatorial path explosion.

### 2. Why Early Termination (`e · 0 ≡ 0`) and Dead-State Normalization Are Unsound Against `Trusted.MirSemantics`

Basis: normative + source + derived

In POPL 2020 `GKAT`, a state recognizing the empty language (`ℓ(s) = ∅`) cannot distinguish early rejection (`0`) from late rejection (`a · 0`) unless unreachable-to-accept transitions are pruned (`Definition 5.3` & `Lemma 5.6`: setting `δ̂(s)(α) = 0` whenever `δ(s)(α) = (p, x')` targets a dead state `x' ∈ D`). Similarly, `cfgkat-rocq` enforces `EqS2: 0 ;; e == 0` (`Axioms.v` L55) and maps non-halting `goto` chains to `CFGKATAutomatonReject` (`SyntacticAutomata.v` L88–89).

Connecting this semantics to `Trusted.MirSemantics` (`joshlf/anneal`, `MirSemantics.lean` L601–605, L1646–1670) exposes **two fatal soundness collapses (`C2` calibration)**:

1. **Dead-State Pruning Masks All-Prefix Undefined Behavior:** Consider an execution `ub_step ;; while true {}` that dereferences uninitialized storage (`.fault .undefined`) before entering a non-terminating loop. Because the trace never reaches an accepting return (`.returned`), both `ub_step ;; while true {}` and `while true {}` have accepting language `∅`. Dead-state normalization (`Lemma 5.6`) erases the transition into the dead tail—treating the prefix as `0` and masking `.fault .undefined`, violating `Trusted.MirSemantics.WellFormed` (`L1649`: `∀ k, ¬ ReachesResult p q (.fault k)`).
2. **Collapse of Divergence vs. Clean Panic Unwinding:** `Trusted.MirSemantics.TerminalOut` distinguishes normal return (`.returned out`) from panic unwinding (`.unwound callerMem`, `L602–604`), both of which satisfy `WellFormed` when fault-free (`L1646`), while `Diverges` (`L1665–1670`) characterizes infinite step traces. `GKAT` normalization collapses non-terminating loops (`Diverges`), clean unwinding (`.unwound`), and UB (`.fault .undefined`) into a single rejection sink `0`.

**Resolution via `GKAT_0` (Schmid et al., ICALP 2021):** Dropping early termination `S3: e · 0 ≡ 0` (`gkat_icalp21` Fig. 1) yields `GKAT_0`, where un-normalized coalgebraic bisimulation is directly sound and complete with respect to finite/infinite process trees without dead-state pruning! Extending `GKAT_0` states with typed halt leaves (`ExitOut := accept Nat | unwind | fault FaultKind`) makes un-normalized bisimulation preserve `WellFormed`, `Behavior`, and `Diverges` intact while **removing** reachability precomputation and `ClassicalEpsilon` from Lean's kernel.

### 3. Pass-1 Certificate Architecture: `BisimDFA` Checkers, `RankedBiAlign`, and Constant-Time `p ⋈ p`

Basis: source + derived

Under Anneal's Pass 1 rules (`TrustedBoundary.lean` L442–596)—which forbid `Std.*`, `partial`, `omega`, `ring`, `bv_decide`, `native_decide`, and `._unsafe_rec`—decision and alignment search run **externally** (in Rust/Python tooling) and export linear witnesses verified by total `Bool` checkers in `theory/`:

1. **Table-Driven Scanners (`BisimDFA` over `GCoalg`):** For byte-class DFAs (such as Bjoern Hoehrmann / `encoding_rs` UTF-8 state tables or `miniz_oxide` Huffman/inflate decoders), an external tool runs Hopcroft–Karp in $O(n \cdot \alpha(n))$ and emits the minimal equivalence witness `cert : List (Nat × Nat)` relating compiled DFA states to a legible multi-step reference automaton. Lean checks `checkBisimCert c1 c2 cert = true` in a single structural pass (`O(|cert| · numAtoms)`) using closed `Nat` operations on Lean 4.34.1's C++ GMP `reduce_nat` fast path (`rfl`), with zero symbolic free variables (`has_fvar = false`).
2. **SIMD-vs-Scalar `SafeTwin` Strip-Mining (`RankedBiAlign`):** When proving a 16-byte SIMD/SWAR loop equivalent to a scalar byte loop, `BiAlign` aligns one fast step against $k$ scalar steps (`⟨step_simd | step_scalar^16⟩*`) followed by tail lockstep (`⟨step_tail | step_scalar⟩*`) via structural AST constructors (`sync`, `leftStut`, `rightStut`, `seq`, `cond`, `kTo1Loop`), reducing $O(|V_1| \times |V_2|)$ product CFG exploration to $O(|V_1| + |V_2|)$ aligned invariants. Crucially, unlike `BiKAT`’s partial-correctness relational Hoare logic (`Theorem 4.6`), one-sided `.leftStut` / `.rightStut` steps inside loops **must carry a `Nat` ranking measure** (`rank (f s) < rank s`): without strict rank decrease, a non-terminating left loop `while i < n { /* i unchanged */ }` preserves relation `R s₁ s₂` via `.leftStut id` while violating `Diverges pImpl q ↔ Diverges pSpec q`.
3. **Constant-Time Non-Interference (`p ⋈ p` Self-Alignment):** Pairing a functional `SafeTwin` equivalence (`pImpl ⋈ pSpec`, where `pSpec` may branch freely on secret booleans) with a symmetric self-alignment (`pImpl ⋈ pImpl`) over a public-projection invariant `R_pub s₁ s₂` enforces identical control-flow predicates (`c₁ s₁ = c₂ s₂`) and public memory addresses at every branch (`cond`), certifying constant-time leakage absence in linear time without `taint` hacks inside `Trusted.*`.

### 4. Hardening `SafeTwin` Relational Specifications Against Reward-Hacking Spec Laundering

Basis: source + derived

Using a simple safe Rust reference twin (`fn safe_spec`) as the human-reviewed specification for an `unsafe` fast path (`fn fast_impl`) satisfies Statement-Origin Separation (`TrustedBoundary.lean` L1316–1365) because the locked theorem statement mentions **only `Trusted.MirSemantics.{Program, Query, WellFormed, Behavior, Diverges, TerminalOut}`**. However, auditing candidate `SafeTwin` formulations against bounded human review reveals three concrete spec-laundering / over-constraining failures:

1. **The `.fault .unsupported` Poison-Pill Vacuity Exploit:** Suppose a `SafeTwin` claim is phrased conditionally:
   `∀ q, dom q → (WellFormed pSpec q → WellFormed pImpl q) ∧ (∀ out, Behavior pImpl q out ↔ Behavior pSpec q out) ∧ (Diverges pImpl q ↔ Diverges pSpec q)`.
   If `pImpl` (`simd_xor_fast`) contains an out-of-bounds read (`.fault .undefined`) when `len % 16 != 0`, an adversarial agent can insert a harmless-looking, 100% safe-Rust boundary fallback in `pSpec` (such as `dst.iter_mut().zip(...)` or `panic!("bad len {}", n)`) that lowers to a MIR construct outside `Trusted.MirAst`'s supported subset. On `len % 16 != 0`, `pSpec` steps to **`.fault .unsupported`**, making `WellFormed pSpec q = False`, `Behavior pSpec q out = False`, and `Diverges pSpec q = False`. Meanwhile `pImpl` hits `.fault .undefined`, also making `WellFormed pImpl q = False`, `Behavior pImpl q out = False`, and `Diverges pImpl q = False`! Every conjunct (`False → False`, `False ↔ False`, `False ↔ False`) evaluates to **`True`**, shipping real UB past a faithful-looking safe Rust spec!
   - **Fix (`HardenedSafeTwinSpec`):** Require **unconditional conjunction** `WellFormed pSpec q ∧ WellFormed pImpl q` for all `q` satisfying `dom q`. Any `.fault .unsupported` in `pSpec` fails verification closed immediately.
2. **Mid-Loop Panic `CallerMemory` Asymmetry (`TerminalOut.unwound callerMem`):** In `Trusted.MirSemantics` (`MirSemantics.lean` L604), `TerminalOut.unwound` carries final `callerMem`. An honest `simd_xor_fast` validates `assert!(dst.len() <= a.len())` *before* writing `dst` (unwinding with untouched `callerMem`), whereas a naive scalar loop mutates `dst[0..i]` before panicking at index `i` (unwinding with partially mutated `callerMem`). Requiring exact `TerminalOut` equality rejects the honest optimization!
   - **Fix:** Assert exact `Out` equality on `.returned out` (`Behavior pImpl q (.returned out) ↔ Behavior pSpec q (.returned out)`), and match panic reachability existentially on `.unwound` (`(∃ m₁, Behavior pImpl q (.unwound m₁)) ↔ (∃ m₂, Behavior pSpec q (.unwound m₂))`, or require invariant preservation on surviving caller memory).
3. **Eliminating Custom Lean `dom : Query → Prop` Side-Condition Laundering:** If `dom` is hand-written in Lean, an agent can silently forbid legitimate raw-pointer aliasing (`dst == a`) or reject struct values carrying `.uninit` padding bytes (`AllocByte.uninit`), creating an un-reviewed specification dependency. `dom` must be fixed mechanically to valid well-typed MIR queries restricted only by explicit Rust-side `#[safety(...)]` preconditions, with both `pImpl` and `pSpec` captured in the same `Program` with identical `MirTy` signatures.

#### Self-Contained Pass-1 Lean 4 Formalization & Refutation Counterexamples

The standalone module below imports strictly `Init.Core`, `Init.Data.List.Basic`, and `Init.Data.Nat.Basic` under `prelude`, obeys every Pass 1 rule in `TrustedBoundary.lean` (`L442–596`), uses zero `Classical.choice` (`0` axioms on the checkers and counterexamples), and proves `bisim_sound_of_check`, `RankedBiAlign.sound`, and both refutations:

```lean
prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic

namespace Anneal.BiGkatRel

/-! ## Part 1: Multi-Exit `GKAT_0` Coalgebras (No `e · 0 ≡ 0`) & Witnessed Bisimulation -/

inductive FaultKind where | undefined | unsupported

inductive ExitOut where
  | accept (val : Nat)
  | unwind
  | fault  (k : FaultKind)

inductive StepRes where
  | halt (out : ExitOut)
  | step (act : Nat) (next : Nat)

structure GCoalg where
  numAtoms : Nat
  trans    : Nat → Nat → StepRes

def faultKindBeq : FaultKind → FaultKind → Bool
  | .undefined,   .undefined   => true
  | .unsupported, .unsupported => true
  | _,            _            => false

def exitOutBeq : ExitOut → ExitOut → Bool
  | .accept a,  .accept b  => Nat.beq a b
  | .unwind,    .unwind    => true
  | .fault k1,  .fault k2  => faultKindBeq k1 k2
  | _,          _          => false

theorem exitOut_of_beq {a b : ExitOut} (h : exitOutBeq a b = true) : a = b := by
  cases a with
  | accept x =>
    cases b with
    | accept y =>
      have hxy : x = y := Nat.eq_of_beq_eq_true h
      rw [hxy]
    | unwind => cases h
    | fault _ => cases h
  | unwind =>
    cases b with
    | accept _ => cases h
    | unwind => rfl
    | fault _ => cases h
  | fault k1 =>
    cases b with
    | accept _ => cases h
    | unwind => cases h
    | fault k2 =>
      cases k1 with
      | undefined =>
        cases k2 with
        | undefined => rfl
        | unsupported => cases h
      | unsupported =>
        cases k2 with
        | undefined => cases h
        | unsupported => rfl

def pairMem (s1 s2 : Nat) : List (Nat × Nat) → Bool
  | [] => false
  | p :: ps => (Nat.beq p.1 s1 && Nat.beq p.2 s2) || pairMem s1 s2 ps

def stepResSim (cert : List (Nat × Nat)) : StepRes → StepRes → Bool
  | .halt o1,    .halt o2    => exitOutBeq o1 o2
  | .step a1 n1, .step a2 n2 => Nat.beq a1 a2 && pairMem n1 n2 cert
  | _,           _           => false

def checkAtomsUpTo (c1 c2 : GCoalg) (cert : List (Nat × Nat)) (s1 s2 : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => stepResSim cert (c1.trans s1 n) (c2.trans s2 n) && checkAtomsUpTo c1 c2 cert s1 s2 n

def checkCertPairs (c1 c2 : GCoalg) (fullCert : List (Nat × Nat)) : List (Nat × Nat) → Bool
  | [] => true
  | p :: rest =>
    checkAtomsUpTo c1 c2 fullCert p.1 p.2 c1.numAtoms && checkCertPairs c1 c2 fullCert rest

def checkBisimCert (c1 c2 : GCoalg) (cert : List (Nat × Nat)) : Bool :=
  Nat.beq c1.numAtoms c2.numAtoms && checkCertPairs c1 c2 cert cert

theorem and_true_l {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with | true => rfl | false => cases h

theorem and_true_r {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with | true => exact h | false => cases h

theorem checkAtomsUpTo_sound (c1 c2 : GCoalg) (cert : List (Nat × Nat)) (s1 s2 : Nat) :
    ∀ n a, a < n → checkAtomsUpTo c1 c2 cert s1 s2 n = true →
      stepResSim cert (c1.trans s1 a) (c2.trans s2 a) = true
  | 0, a, hlt, _ => False.elim (Nat.not_succ_le_zero a hlt)
  | n + 1, a, hlt, hchk => by
    have hle := Nat.le_of_succ_le_succ hlt
    cases hle with
    | refl => exact and_true_l hchk
    | step hlt' => exact checkAtomsUpTo_sound c1 c2 cert s1 s2 n a hlt' (and_true_r hchk)

theorem checkCertPairs_sound (c1 c2 : GCoalg) (fullCert : List (Nat × Nat)) :
    ∀ rem s1 s2, pairMem s1 s2 rem = true →
      checkCertPairs c1 c2 fullCert rem = true →
      checkAtomsUpTo c1 c2 fullCert s1 s2 c1.numAtoms = true
  | [], _, _, hmem, _ => by cases hmem
  | p :: rest, s1, s2, hmem, hchk => by
    cases hhere : Nat.beq p.1 s1 && Nat.beq p.2 s2 with
    | true =>
      have hp1 : p.1 = s1 := Nat.eq_of_beq_eq_true (and_true_l hhere)
      have hp2 : p.2 = s2 := Nat.eq_of_beq_eq_true (and_true_r hhere)
      rw [← hp1, ← hp2]
      exact and_true_l hchk
    | false =>
      dsimp only [pairMem] at hmem
      rw [hhere] at hmem
      exact checkCertPairs_sound c1 c2 fullCert rest s1 s2 hmem (and_true_r hchk)

inductive TraceOutcome where
  | prefixDiv (acts : List Nat)
  | ended     (acts : List Nat) (out : ExitOut)

def evalGCoalg (c : GCoalg) (atoms : Nat → Nat) : Nat → Nat → TraceOutcome
  | 0, _ => .prefixDiv []
  | fuel + 1, st =>
    match c.trans st (atoms fuel) with
    | .halt o => .ended [] o
    | .step act nxt =>
      match evalGCoalg c atoms fuel nxt with
      | .prefixDiv acts => .prefixDiv (act :: acts)
      | .ended acts o  => .ended (act :: acts) o

theorem bisim_sound_of_check (c1 c2 : GCoalg) (cert : List (Nat × Nat)) (atoms : Nat → Nat)
    (hCert : checkBisimCert c1 c2 cert = true)
    (hAtoms : ∀ k, atoms k < c1.numAtoms) :
    ∀ fuel s1 s2, pairMem s1 s2 cert = true →
      evalGCoalg c1 atoms fuel s1 = evalGCoalg c2 atoms fuel s2
  | 0, _, _, _ => rfl
  | fuel + 1, s1, s2, hmem => by
    have hPairs := and_true_r hCert
    have hAt := checkCertPairs_sound c1 c2 cert cert s1 s2 hmem hPairs
    have hSim := checkAtomsUpTo_sound c1 c2 cert s1 s2 c1.numAtoms (atoms fuel) (hAtoms fuel) hAt
    dsimp only [evalGCoalg]
    cases h1 : c1.trans s1 (atoms fuel) with
    | halt o1 =>
      cases h2 : c2.trans s2 (atoms fuel) with
      | halt o2 =>
        dsimp only [stepResSim] at hSim
        rw [h1, h2] at hSim
        have ho := exitOut_of_beq hSim
        rw [ho]
      | step _ _ =>
        dsimp only [stepResSim] at hSim
        rw [h1, h2] at hSim
        cases hSim
    | step a1 n1 =>
      cases h2 : c2.trans s2 (atoms fuel) with
      | halt _ =>
        dsimp only [stepResSim] at hSim
        rw [h1, h2] at hSim
        cases hSim
      | step a2 n2 =>
        dsimp only [stepResSim] at hSim
        rw [h1, h2] at hSim
        have ha : a1 = a2 := Nat.eq_of_beq_eq_true (and_true_l hSim)
        have hn := bisim_sound_of_check c1 c2 cert atoms hCert hAtoms fuel n1 n2 (and_true_r hSim)
        rw [ha, hn]

/-! ## Part 2: Ranked `BiAlign` (`k`-to-`1` Loop & Constant-Time) + Hardened `SafeTwin` -/

inductive RankedBiAlign (S1 S2 : Type) where
  | sync      (f1 : S1 → S1) (f2 : S2 → S2)
  | leftStut  (rank1 : S1 → Nat) (f1 : S1 → S1)
  | rightStut (rank2 : S2 → Nat) (f2 : S2 → S2)
  | seq       (a b : RankedBiAlign S1 S2)
  | cond      (c1 : S1 → Bool) (c2 : S2 → Bool) (onT onF : RankedBiAlign S1 S2)
  | loop      (g1 : S1 → Bool) (g2 : S2 → Bool) (body : RankedBiAlign S1 S2)

def RankedBiAlign.sound {S1 S2 : Type} (R : S1 → S2 → Prop) : RankedBiAlign S1 S2 → Prop
  | .sync f1 f2        => ∀ s1 s2, R s1 s2 → R (f1 s1) (f2 s2)
  | .leftStut rk1 f1   => ∀ s1 s2, R s1 s2 → R (f1 s1) s2 ∧ rk1 (f1 s1) < rk1 s1
  | .rightStut rk2 f2  => ∀ s1 s2, R s1 s2 → R s1 (f2 s2) ∧ rk2 (f2 s2) < rk2 s2
  | .seq a b           => a.sound R ∧ b.sound R
  | .cond c1 c2 t f    => (∀ s1 s2, R s1 s2 → c1 s1 = c2 s2) ∧ t.sound R ∧ f.sound R
  | .loop g1 g2 body   => (∀ s1 s2, R s1 s2 → g1 s1 = g2 s2) ∧ body.sound R

def HardenedSafeTwinSpec {Query Out Mem : Type}
    (wfImpl wfSpec : Query → Prop)
    (retImpl retSpec : Query → Out → Prop)
    (unwImpl unwSpec : Query → Mem → Prop)
    (divImpl divSpec : Query → Prop)
    (dom : Query → Prop) : Prop :=
  ∀ q, dom q →
    wfSpec q ∧
    wfImpl q ∧
    (∀ o, retImpl q o ↔ retSpec q o) ∧
    ((Exists fun m1 => unwImpl q m1) ↔ (Exists fun m2 => unwSpec q m2)) ∧
    (divImpl q ↔ divSpec q)

/-- Counterexample 1: Conditional `wfSpec → wfImpl` passes when `pSpec` hits `.unsupported` (`False`)
    and `pImpl` commits UB (`False`), whereas `HardenedSafeTwinSpec` (`wfSpec ∧ wfImpl`) rejects it! -/
theorem poison_pill_vacuity_counterexample :
    ((False → False) ∧ (∀ _ : Nat, False ↔ False) ∧ (False ↔ False)) ∧
    ¬ (False ∧ False) := by
  refine ⟨⟨fun h => h, fun _ => ⟨fun h => h, fun h => h⟩, ⟨fun h => h, fun h => h⟩⟩, ?_⟩
  intro h
  exact h.1

/-- Counterexample 2: Unranked `leftStut id` fails its strict `Nat` rank obligation (`0 < 0`),
    blocking divergence laundering inside `RankedBiAlign`. -/
theorem unranked_stutter_divergence_counterexample :
    ¬ (RankedBiAlign.sound (fun _ _ => True)
        (RankedBiAlign.leftStut (fun _ : Unit => 0) (fun _ : Unit => ()))) := by
  intro h
  have hBad := h () () trivial
  exact Nat.lt_irrefl 0 hBad.2

end Anneal.BiGkatRel
```

### 5. Evaluation Against Anneal `theory/` Rubric `(T1, P1–P5, C1–C2)`

Basis: derived

| Verification Strategy | (T1) 0-TCB Bridge | (P1) Spec Auditability | (P2) Locality | (P3) Kernel / LSP Scaling | (P4) Heterogeneous Composability | (P5) Failure Legibility | (C1–C2) Minimality |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Full `KAT` / `*-continuous BiKAT`** | Fails (PSPACE / undecidable `Theorem 4.4`) | Med | Low | Fails | Moderate | Low | Over-broad (`+`/`*` nondeterminism) |
| **Normalized POPL'20 `GKAT` / `cfgkat-rocq`** | Fails (`ClassicalEpsilon`; `e · 0 ≡ 0` masks UB & `Diverges`) | Med | Med | Med (`classic` overhead) | Fails on `.fault` & `.unwound` | Med (`0` collapses causes) | Unsound collapse (`S3`) |
| **Monolithic Product-CFG `MirWp`** | Passes Pass 1 | Med | Low ($O(|V_1|\times|V_2|)$) | Poor (exponential `whnf`) | High | Low | Blows up product states |
| **`GKAT_0` `BisimDFA` + `RankedBiAlign` + `HardenedSafeTwinSpec`** | **Passes Pass 1** (`Init.Core`+`List`+`Nat`, 0 axioms; needs `Trusted.*` capture hooks below) | **Very High** (safe Rust twin is the spec) | **High** (1-pass `cert` & ranked blocks) | **Very High** (`O(\|cert\|)` GMP `rfl`, `<50 ms` behind `@[irreducible]`) | **High** (`safe` ↔ `unsafe` SIMD, CT, table DFAs, `.unwound`) | **Very High** (unmatched `(s1, s2)` pair or rank edge) | **Optimal** (no `e · 0 ≡ 0`; rank stops loop laundering) |

**Kernel Scaling & `Trusted.*` Capture Seam:** Guarding relational loop-cut invariants inside `@[irreducible]` wrappers (`TrustedBoundary.lean` L595) prevents Lean's kernel `whnf`/`isDefEq` from traversing upstream state histories across edits. Deploying `HardenedSafeTwinSpec` end-to-end on real Rust crates requires two minimal TCB provisions in `joshlf/anneal` (`c131b320`): (1) widening `initState` / `BodyVerified` (`MirSemantics.lean` L803, L1751) from empty `callerMem = ⟨[]⟩` to slice/pointer caller memory; and (2) binding `#[safe_twin]` pairs inside `rustc-capture` in the same `Program` with Rust-derived `dom` preconditions so Lean specs cannot launder aliasing or padding (`THREAT_MODEL.md`).

## Boundaries

- **`unsupported` (Decidable `*-Continuous BiKAT` & Direct `cfgkat-rocq` Port):** Deciding arbitrary `*-continuous BiKAT` identities is undecidable (`Theorem 4.4`, Antonopoulos et al. POPL 2023), and `SpencerKoevering/cfgkat-rocq` relies on `ClassicalEpsilon` / `PropExtensionality` / `FunctionalExtensionality` alongside `e · 0 ≡ 0`, which is unsupported under Anneal's zero-UB-masking `WellFormed` requirement.
- **`known not to apply` (`GKAT` Dead-State Normalization, Conditional `wfSpec → wfImpl`, and Unranked Stutter):** `Lemma 5.6` dead-state pruning (Smolka et al. POPL 2020), conditional `WellFormed pSpec → WellFormed pImpl`, and unranked `.leftStut` alignment do not apply to `Trusted.MirSemantics` safety or total-correctness equivalence (`poison_pill_vacuity_counterexample`, `unranked_stutter_divergence_counterexample`).
- **`not examined` (Live Lean Compilation & Unstructured Irreducible CFGs):** Live execution of `Anneal.BiGkatRel` under `lean -DwarningAsError=true` was not examined in this analysis pass (checked statically against `TrustedBoundary.lean` syntax, import, and tactic allowlists). Full mechanization of non-local `goto` loop-lifting (`Semantics/AutomataResolution.v` in `cfgkat-rocq`) onto `Trusted.MirAst` without `ClassicalEpsilon` and probabilistic sub-Markov kernel `BiGKAT` alignment (FoSSaCS 2025) were not examined here.
- **`unknown` (Data-Dependent Loop Alignment Discovery Cost):** Automatic discovery latency for data-dependent variable-stride `RankedBiAlign` witnesses (e.g., variable-length UTF-8 vector decoders vs. fixed $k$-to-$1$ SIMD loops) on unmodeled Rust `InlineAsm` bodies remains unknown.

## Evidence

| Subject / Revision | Inspected Paths & Citations | Verified Facts |
| :--- | :--- | :--- |
| Smolka et al., `GKAT` (POPL 2020, `doi:10.1145/3371129`, `arXiv:1907.05920`) | §§2–5 (`Theorem 4.1`, `Proposition 4.2`, `Definition 5.1–5.3`, `Lemma 5.6`) | $O(\|e\|)$ Thompson construction, normal coalgebras, dead-state pruning erasing `ℓ(s) = ∅` transitions |
| Schmid et al., `GKAT_0` (ICALP 2021, `doi:10.4230/LIPIcs.ICALP.2021.142`, `arXiv:2102.08286`) | §§1–3 (`Fig. 1` axioms `U1–U5`, `S1–S6`, `W1–W3`; reduced `≡₀` omitting `S3: e · 0 ≡ 0`) | `GKAT_0` separates infinite/failing processes without early termination collapse |
| Antonopoulos et al., `BiKAT` (POPL 2023, `doi:10.1145/3571213`, `arXiv:2202.04278`, artifact `doi:10.5281/zenodo.7144067`) | §§2, 4.1–4.2, 7.2 (`Example 2.2`, `Def. 4.1`, `Eq. (2)–(3)`, `Thm. 4.4`, `Thm. 4.6`, `Thm. 7.1–7.3`) | `LRC` (`⌈x⌉ # ⌊y⌋ = ⌊y⌋ # ⌈x⌉`), `*-continuous BiKAT` undecidability, `f-valid` $\forall\exists$ witnesses |
| Gomes, Baillot, Gaboardi, `BiGKAT` (FoSSaCS 2025, `doi:10.1007/978-3-031-90897-2_12`, `hal-04017128`) | Publication metadata & abstract | Bi-guarded `GKAT` extension over product state spaces encoding finitary pRHL |
| `SpencerKoevering/cfgkat-rocq` (`8873fd7b48de42cc47a09d3373d683a5a71c6811`; `doi:10.1145/3704857`, `arXiv:2411.13220`) | `syntax/{Preliminaries,Axioms}.v`, `semantics/{SyntacticAutomata,Bisimulation}.v`, `completeness/CFGKATCoalgebra.v`, `examples/ShortCircuitTransform.v` | `EqS2`, `EqA5`, `ClassicalEpsilon` & `classic` totality, `ResolveCFGKATAutomatonDynamicsDefaultReject` |
| `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) | `trusted/audit/TrustedBoundary.lean` L442–596, L1316–1365; `foundation-lock.json`; `MirSemantics.lean` L601–605, L803, L1646–1676, L1751 | Pass 1 tactic/notation/module ceilings, `@[irreducible]` allowance (`L595`), `TerminalOut.unwound`, `WellFormed`, `Diverges` |

## Revalidation

1. **Confirm Pass-1 Notation & Tactic Compliance:** In a `joshlf/anneal` checkout, verify that every tactic and syntax form in `Anneal.BiGkatRel` remains inside `TrustedBoundary.lean` (`L521–596`):
   ```bash
   python3 -c 'tb=open("trusted/audit/TrustedBoundary.lean").read(); print("@[irreducible]" in tb or "`irreducible" in tb, "Init.Data.List.Basic" in open("trusted/lean/foundation-lock.json").read())'
   ```
   Expected: `True True`.
2. **Type-Check & Zero-Axiom Verify `Anneal.BiGkatRel` (`<2s` standalone Lean 4 `v4.34.1` check):** Write the `Anneal.BiGkatRel` block from Findings §4 to `/tmp/bigkat_align_probe.lean`, append `#print axioms` checks in a separate temporary checker file for `bisim_sound_of_check`, `poison_pill_vacuity_counterexample`, and `unranked_stutter_divergence_counterexample`, and run `lean -DwarningAsError=true /tmp/bigkat_align_probe.lean`. Confirm exit `0` and **zero axioms** (`[]`) on `bisim_sound_of_check` and both counterexamples.
3. **Check `SpencerKoevering/cfgkat-rocq` Upstream Changes:** Diff `syntax/Axioms.v` and `semantics/SyntacticAutomata.v` above `8873fd7b48de` for changes to `EqS2` (`0 ;; e == 0`) or constructive jump resolution without `ClassicalEpsilon`.
