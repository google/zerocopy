# SafeTwin Observational Equivalence, Unwind Loopholes, Constant-Time Phantom Typing, and Linear BiAlign Alignment

## Summary

Verifying an optimized or `unsafe` Rust routine against an executable safe Rust reference implementation (`SafeTwin`) avoids writing brittle manual postconditions, yet standard return-value equality admits subtle unsound escapes when panics unwind, loops diverge, or secrets flow into branches and memory indices. Grounded in `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), `proofs-rs/lean-miri` (`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`), `rust-lang/rust` (`8144389c895da997dbdecaa635e41d6a50be6ffd`), `hacl-star/hacl-star` (`f557259007db9933442dde10aa995c1b00bd3446`), `GaloisInc/saw-script` (`f290af7bda474779c8e5685ddd30612a7e6f0399`), and `GKAT`/`BiKAT`/`BiGKAT`, four architectural requirements govern `SafeTwin` equivalence in Pass-1 Lean `v4.34.1`:

1. **Statement-origin-separated `TotalSafeTwinEquiv` closes four terminal and vacuity loopholes (`L1`–`L4`):** Expressing `SafeTwin` solely in `Trusted.MirSemantics` primitives (`entryProgForBody`, `BodyStaticAdmitted`, `ValidEntryArgs`, `WellFormed`, `Behavior`, `Diverges`, `TerminalOut`) preserves 100% statement-origin separation (`0-TCB` inside `theory/`). Pairing `WellFormed` (excluding `.fault .undefined` and `.fault .unsupported`) with parity across both `TerminalOut.returned` and `TerminalOut.unwound callerMem` prevents panic-to-UB laundering (`L1`), catches `UnwindAction::Unreachable` UB (`L2`), preserves caller-visible partial mutations made before unwind (`L4`), and prevents silent non-termination (`L3`) via explicit `Diverges` equivalence and uninhabited-argument admission (`BodyStaticAdmitted`).
2. **Phantom `SecScalar` types (`PUB | SEC`) enforce constant-time hygiene inside `theory/`, while explicit `LeakStepObs` traces defeat McLean's Refinement Paradox:** HACL* (`Lib.IntTypes.fsti`) prevents secret values from entering branches, shifts, or divisions via `secrecy_level = PUB | SEC`, constant-time masks (`eq_mask`..`lte_mask`), and `Lib.RawIntTypes` declassification boundaries (`u*_to_UInt*` *"BREAKS secret independence"*). Unfolding phantom wrappers cleanly away from target theorem statements preserves `0-TCB`, yet 2-safety constant-time transfer requires explicit step-level `LeakTrace` parity because functional equivalence refines trace sets across secret-dependent control flow.
3. **`BiAlign` lockstep and tiled unroll certificates bound relational proofs to linear $O(|P|)$ size:** Adapting deterministic guarded alignment (`GKAT`/`BiKAT`/`BiGKAT`) and `SAW`/`Crux-MIR` compositional call overrides aligns a 4-lane SIMD/unsafe loop against four iterations of a safe scalar reference loop (`stepQuad`) plus scalar tail epilogue using one local invariant preservation check (`biAlign_stride4_sound`), avoiding quadratic path-product explosion.
4. **Refuted premature collapses establish four non-negotiable separation lines:** Return-only equality permits panic-to-UB escapes; partial inclusion permits diverging unsafe candidates; single-property observational equivalence fails constant-time 2-safety; and naive lockstep `k = 1` simulation rejects stride-4 SIMD vectorization and unrolled slices.

---

## Applicability

This report governs relational verification contracts between safe reference Rust bodies and unsafe/optimized implementations (`SafeTwin`), examining the nine primary subjects in `REPORT.json`:

| Subject | Pinned Identity | Examined Scope |
| :--- | :--- | :--- |
| Anneal verifier | `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `Trusted/MirSemantics.lean`, `Trusted/Correspondence.lean`, `Trusted/audit/TrustedBoundary.lean` |
| `lean-miri` semantics | `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` | `Miri/Interpreter/ControlFlow.lean:40-90, 125-148` (`unwindToBlock`, `returnFromCurrentFrame`) |
| `rust-lang/rust` MIR | `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` | `compiler/rustc_middle/src/mir/syntax.rs` (`Assert`, `UnwindResume`, `UnwindAction`), `terminator.rs:1-80` |
| `HACL*` integer specs | `hacl-star/hacl-star@f557259007db9933442dde10aa995c1b00bd3446` (`ACM CCS 2017`) | `lib/Lib.IntTypes.fsti`, `lib/Lib.RawIntTypes.fsti` |
| `SAW` / `Crux-MIR` | `GaloisInc/saw-script@f290af7bda474779c8e5685ddd30612a7e6f0399`, `arXiv:2410.18280` | Compositional MIR override specs (`#[crux_spec_for]`, `mir_verify`, `mir_extract`, `CHANGES.md:123-166`) |
| `GKAT` | DOI `10.1145/3371129` (POPL 2020) | Deterministic guarded coalgebraic trace bisimulation |
| `BiKAT` | DOI `10.1145/3571213` (POPL 2023) | Relational product algebra (`\|`) for asynchronous left/right program alignment |
| `BiGKAT` | DOI `10.1007/978-3-031-90897-2_12` (ESOP 2025) | Guarded relational product algebra over deterministic executions |
| Lean 4 toolchain | `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Pass-1 `Init.*` kernel target |

Important baseline scope from `Trusted/MirSemantics.lean:1686-1699` on `joshlf/anneal@c131b320`: entry queries constrain value arguments with empty caller memory (`callerMem = ⟨[]⟩`) while `TerminatorKind.call` returns `.fault .unsupported`; interprocedural `BiAlign` overrides and heap-pointer `callerMem` parity extend identically once multi-frame calls and allocations are enabled in `Trusted.MirSemantics`. General refinement preservation theorems across MIR-to-ISA lowering appear separately in [`observable-behavior-property-transfer-and-anneal-statement-forms`](../observable-behavior-property-transfer-and-anneal-statement-forms/REPORT.md), and simulation completeness proofs in [`relational-logics-simulation-techniques-and-completeness-for-compiler-derivations`](../relational-logics-simulation-techniques-and-completeness-for-compiler-derivations/REPORT.md). All inline Lean 4 probes obey `TrustedBoundary.lean:442-596` Pass-1 constraints and were checked analytically without local `lean` compiler invocation.

---

## Findings

### 1. Statement-Origin-Separated `SafeTwinEquiv` over `Trusted.MirSemantics`

Basis: normative + source (`joshlf/anneal@c131b320`: `Trusted/MirSemantics.lean:332-335, 586-604, 1646-1745`, `Trusted/audit/TrustedBoundary.lean:442-596`).

Under Anneal's Pass-1 boundary checker (`TrustedBoundary.lean:442-596`), locked verification obligations must reference only `Init.*`, `Trusted.*`, and extracted `Mir.*` declarations—never `Anneal.*` proof abstractions from `theory/`. Crucially, `Trusted.MirSemantics` already defines every observable needed to state a complete relational `SafeTwin` contract cleanly outside `Anneal.*`:

```lean
inductive FaultKind where
  | undefined
  | unsupported

structure CallerMemory where
  allocations : List Allocation := []

structure Query where
  args : List Val
  callerMem : CallerMemory := ⟨[]⟩

structure Out where
  ret : Val
  callerMem : CallerMemory := ⟨[]⟩

inductive TerminalOut where
  | returned (out : Out)
  | unwound (callerMem : CallerMemory := ⟨[]⟩)

noncomputable def WellFormed (p : Program) (q : Query) : Prop :=
  (∃ s₀ : State, initState p q = .ok s₀ ∧
    ∀ s : State, Reaches p s₀ s → ∃ c : Choice, ValidChoice p s c) ∧
  (∀ k : FaultKind, ¬ ReachesResult p q (.fault k))

noncomputable def Behavior (p : Program) (q : Query) (out : TerminalOut) : Prop :=
  ReachesResult p q (.done out)

noncomputable def Diverges (p : Program) (q : Query) : Prop :=
  ∃ s₀ : State, initState p q = .ok s₀ ∧
    ∃ trace : Nat → State, trace 0 = s₀ ∧
      ∀ n : Nat, Step p (trace n) (.step (trace (n + 1)))
```

Using `entryProgForBody`, `BodyStaticAdmitted`, and `ValidEntryArgs` (`MirSemantics.lean:1710-1745`), a clean, 100% statement-origin-separated **total reference-twin specification** relating `(pSafe, safeId, bodySafe)` to `(pUnsafe, unsafeId, bodyUnsafe)` under query validity invariant `ArgRel : Query → Prop` takes the canonical form:

- **Static body binding (`BodyStaticAdmitted` parity):** Both `(pSafe, bodySafe)` and `(pUnsafe, bodyUnsafe)` are bound at their declared `DefId`s and pass `BodyStaticAdmitted` (`pointerWidthBits == 64`, `mirProfileVersion == 1`, non-empty unique `identity`, non-empty `basicBlocks`, `argumentCount < locals.length`, in-bounds storage annotations). Notice (`MirSemantics.lean:1728-1744`) this explicitly rejects uninhabited `MirTy.never` parameter stubs that would otherwise render `∀ q, ValidEntryArgs body q.args → ...` vacuously true.
- **Fault-freedom and total outcome/divergence parity (`TotalSafeTwinEquiv`):** For every admitted query `q` satisfying `ValidEntryArgs bodySafe q.args ∧ ValidEntryArgs bodyUnsafe q.args ∧ ArgRel q`:
  1. `WellFormed (entryProgForBody pUnsafe unsafeId) q` (the unsafe candidate is free of `.fault .undefined` UB and `.fault .unsupported` unmodeled constructs, and never reaches a stuck state lacking `ValidChoice`);
  2. `∀ out : TerminalOut, Behavior (entryProgForBody pUnsafe unsafeId) q out ↔ Behavior (entryProgForBody pSafe safeId) q out` (bidirectional exact agreement on both normal `.returned` values/memory AND panic `.unwound callerMem` states);
  3. `Diverges (entryProgForBody pUnsafe unsafeId) q ↔ Diverges (entryProgForBody pSafe safeId) q` (bidirectional parity on infinite executions).

When `pSafe` is itself verified (`WellFormed`) and deterministic, condition (2)+(3) ensures the unsafe twin terminates cleanly iff the safe twin does, panics with identical caller memory iff the safe twin does, and returns identical output otherwise.

---

### 2. Four Relational Loopholes Closed by Full Terminal/Divergence Parity (`L1`–`L4`)

Basis: source + derived (`joshlf/anneal@c131b320`, `proofs-rs/lean-miri@c92d1d97`, `rust-lang/rust@8144389c`).

Inspecting Rust MIR unwind lowering alongside `lean-miri` (`Miri/Interpreter/ControlFlow.lean:40-90`) and `MirSemantics.lean` exposes four distinct soundness loopholes that naive "return-value equivalence" leaves open:

| Loophole | MIR / `lean-miri` Operational Root Cause | How Naive Equivalence Leaks | Exact `TotalSafeTwinEquiv` Defense |
| :--- | :--- | :--- | :--- |
| **`L1` Panic-to-UB laundering** | `Assert { cond, expected, msg, target, unwind }` (`syntax.rs:1011-1025`) unwinds safely on panic (`cleanup` $\to$ `TerminalOut.unwound`), whereas `unsafe` `unreachable_unchecked()` steps directly to `.fault .undefined` | Weak contracts matching `∀ out, Behavior safe q (.returned v) → Behavior unsafe q (.returned v)` or conditioning only on normal return skip `.unwound` inputs, letting UB replace checked bounds panics | `WellFormed` enforces `∀ k, ¬ ReachesResult p q (.fault k)`, and bidirectional `Behavior` parity requires `unsafe` to unwind cleanly whenever `safe` panics |
| **`L2` `UnwindAction::Unreachable`** | `syntax.rs` `UnwindAction::{Continue, Unreachable, Terminate, Cleanup}` and `ControlFlow.lean:46-47`: `.Unreachable => .error (.undefinedBehavior "unwinding past a frame that does not allow unwinding")` | Calling or lowering a panicking sub-operation inside a nounwind boundary (`extern "C"` or corrupt cleanup edge) turns safe unwind into Miri UB while matching non-panicking test paths | `WellFormed` universally quantifies `ReachesResult p q (.fault k)` over all nondeterministic choices `Choice`, rejecting any path reaching `.Unreachable` |
| **`L3` Silent non-termination (`Diverges`)** | `MirSemantics.lean:1695-1699`: `WellFormed` explicitly permits infinite loops (`Diverges` has no `.fault` and produces no `ReachesResult (.done out)`) | A one-directional partial contract `∀ out, Behavior pUnsafe q out → Behavior pSafe q out` is vacuously satisfied by an unsafe infinite loop (`loop {}`) | Bidirectional `Behavior` equivalence PLUS `Diverges pUnsafe q ↔ Diverges pSafe q` closes nondeterministic and deterministic loop hangs equally |
| **`L4` Pre-unwind caller memory corruption** | `ControlFlow.lean:62-90` (`returnFromCurrentFrame`): `unwinding = true` skips copying the return place yet preserves prior memory mutations committed before unwind; `TerminalOut.unwound callerMem` (`MirSemantics.lean:602-604`) surfaces this state | Comparing only termination discriminant (`returned` vs `unwound`) allows an unsafe twin to scribble corrupt partial writes into mutable caller slice buffers before triggering an assertion panic | `Behavior ... (.unwound callerMem)` matches the full `CallerMemory` value inside `.unwound`, rejecting observable tear/corruption on unwind |

Additionally, `Trusted.Correspondence.lean` pins `deinitMovedPlace = true` (`lean-miri` `c92d1d97`) and `rustc` `8144389c` to align move/drop deinitialization behavior, while `lean-miri`'s `returnFromCurrentFrame` (`ControlFlow.lean:76-77`) explicitly flags unwinding past frame 1 as `.undefinedBehavior` unless intercepted cleanly at the call-frame boundary (`TerminalOut.unwound` in `MirSemantics.lean:602-604`).

---

### 3. Constant-Time Secret Isolation: HACL* `SecScalar` and `LeakStepObs` Non-Interference

Basis: normative + source + derived (`hacl-star/hacl-star@f5572590`: `lib/Lib.IntTypes.fsti`, `lib/Lib.RawIntTypes.fsti`, `TrustedBoundary.lean:442-596`).

By McLean's Refinement Paradox (mechanized for Anneal in [`observable-behavior-property-transfer-and-anneal-statement-forms`](../observable-behavior-property-transfer-and-anneal-statement-forms/REPORT.md)), functional behavioral equivalence (`TotalSafeTwinEquiv`) **does not** imply timing or memory-access non-interference: a secret-branching `unsafe` lookup table produces the same `TerminalOut` as a masked constant-time twin (`ctCheckBranch` vs `ctMaskSelect`).

HACL* (`hacl-star/hacl-star@f5572590`) demonstrates a two-part mitigation directly transferable to Pass-1 Lean 4:

1. **Static secrecy discipline in `Lib.IntTypes.fsti`:**
   - Defines `type secrecy_level = | SEC | PUB` (`L132-134`) and keeps `sec_int_t` abstract (`L137`), separating `pub_int_t` (decidable equality/branches) from `sec_int_t` (`int_t t SEC`, `L146-149`).
   - Permits upward promotion via `secret : #t:inttype -> x:int_t t PUB -> y:int_t t SEC{v x == v y}` (`L250`) and level-monotone `cast` (`PUB? l \/ SEC? l'`, `L346`), blocking implicit `SEC -> PUB` declassification.
   - Restricts variable-time division/modulo and branching comparisons (`div`, `mod`, `eq`, `ne`, `lt`, `lte`, `gt`, `gte`, `L878-958`) strictly to `PUB`, while forcing `SEC` code onto constant-time selection masks (`eq_mask`, `neq_mask`, `gte_mask`, `lt_mask`, `gt_mask`, `lte_mask`, `L732-795`) and bitwidth-guarded shift counts (`shiftval t = u:size_t{v u < bits t}`, `L656`).
   - Quarantines explicit declassification into `Lib.RawIntTypes.fsti:8, 24-35`, whose header explicitly warns that `u*_to_UInt*` *"BREAKS secret independence"*, turning every declassification into an auditable boundary.
2. **Pass-1 Anneal `SecScalar` + `LeakStepObs` 2-Safety Coupling:**
   - Inside `theory/`, wrap runtime `Val` values in a zero-cost phantom structure `structure SecScalar (lvl : SecLevel) where raw : Val` and define an inductive micro-architectural trace step `LeakObs ::= branch (b : Bool) | memIdx (addr : Nat) | varLatDiv`.
   - Maintain statement-origin separation (`T1`): strip `SecScalar` wrappers at the `Trusted.CrateTheorem` boundary and emit the public 2-safety statement purely over public-equality relations `PubArgsEq q₁ q₂` and observable `LeakTrace` equality across pairs `(q₁, q₂)` rather than leaking `Anneal.SecScalar` into locked theorem types!

---

### 4. Linear Alignment Certificates (`BiAlign`) via `GKAT`/`BiKAT`/`BiGKAT` and `SAW` Overrides

Basis: normative + source + derived (`10.1145/3371129`, `10.1145/3571213`, `10.1007/978-3-031-90897-2_12`, `GaloisInc/saw-script@f290af7b`).

Proving `TotalSafeTwinEquiv` between a safe scalar loop (1 element per iteration) and an `unsafe` SIMD or 4x-unrolled implementation fails under naive step-by-step lockstep simulation (steps diverge immediately after index 0) and blows up combinatorially ($O(N^2)$) under unconstrained self-composition path products (`P3`). Combining three precedents resolves both walls:

1. **Deterministic Guarded Alignment (`GKAT` POPL '20 `10.1145/3371129`, `BiKAT` POPL '23 `10.1145/3571213`, `BiGKAT` ESOP '25 `10.1007/978-3-031-90897-2_12`):** Unlike full Kleene Algebra with nondeterministic union (`+`), Rust MIR loop headers use deterministic boolean/switch guards (`SwitchTargets`, `terminator.rs:15-60`). `BiKAT` and `BiGKAT` factor relational verification into structured alignment laws `(e₁ | e₂)` separating *bounded left/right warmup or epilogue slices* (`1`-to-`0` / `0`-to-`1` steps) from *lockstep synchronized body tiles* (`4`-to-`1` steps), reducing global product reasoning to local single-tile transition checks (`O(|P|)` linear kernel size).
2. **Modular Call Overrides (`SAW` `1.5` / `Crux-MIR`, `f290af7b`, `arXiv:2410.18280`):** `#[crux_spec_for]` replaces verified helper calls (e.g., complex platform intrinsics or adaptive sorts) with an already-proved scalar model spec in callers. In Anneal `theory/`, a relational `BiAlign` theorem composes via verified callee `SafeTwin` specs without re-inlining inner loops.
3. **Structured `BiAlign` Certificate Shape:** Factor any vectorized loop of length `n = 4 * k + r` (`r < 4`) into:
   - *Aligned Main Tile (`hTile`):* relate `stepQuad stepScalar` (`4` scalar reference steps) to `1` SIMD/unrolled target step under relational invariant `R s t`;
   - *Scalar Tail Epilogue (`hTail`):* relate remaining `r < 4` scalar steps `1`-to-`1`;
   - *Exit Condition Parity (`hExit`):* relate loop exit flags so `TotalSafeTwinEquiv` holds cleanly with zero path explosion and `0-omega` Pass-1 induction.

---

### 5. Self-Contained Pass-1 Lean 4 Probe: Loophole Refutations and Linear `BiAlign` Soundness

Basis: derived (`joshlf/anneal@c131b320`: `TrustedBoundary.lean:442-596`).

The standalone Lean 4 (`v4.34.1`) module below encodes `TotalSafeTwinEquiv` vs. `ReturnOnlyEquiv` and `PartialSafeTwinEquiv`, `SecLevel` constant-time trace equality, and the linear 4-to-1 `BiAlign` tile theorem (`biAlign_stride4_sound`), strictly restricted to Pass-1 allowlisted syntax (`Init.*` prelude only; zero `sorry`, zero `omega`, zero `rcases`, zero `deriving`, zero `partial`, zero `._unsafe_rec`):

```lean
namespace AnnealSafeTwinProbe

inductive TermOut where
  | returned (v : Nat)
  | unwound (callerMem : Nat)

inductive StepOut where
  | ok (out : TermOut)
  | fault
  | diverges

inductive SecLevel where
  | sec
  | pub

structure SecScalar (lvl : SecLevel) where
  raw : Nat

inductive LeakObs where
  | branch (b : Bool)
  | memIdx (i : Nat)

/-- Full operational-semantics-level SafeTwin contract matching `WellFormed`,
    normal return vs unwind `CallerMemory`, and `Diverges` parity. -/
def TotalSafeTwinEquiv (semSafe semUnsafe : Nat → StepOut) (q : Nat) : Prop :=
  (semUnsafe q ≠ .fault ∧ semSafe q ≠ .fault) ∧
  (semUnsafe q = semSafe q)

/-- Weak return-only equivalence ignoring `.fault` and `.unwound`. -/
def ReturnOnlyEquiv (semSafe semUnsafe : Nat → StepOut) : Prop :=
  ∀ q v, semUnsafe q = .ok (.returned v) → semSafe q = .ok (.returned v)

/-- Weak partial equivalence permitting silent divergence when `semUnsafe` hangs. -/
def PartialSafeTwinEquiv (semSafe semUnsafe : Nat → StepOut) (q : Nat) : Prop :=
  semUnsafe q ≠ .fault ∧
  ∀ out, semUnsafe q = .ok out → semSafe q = .ok out

def refSafeUnwind (q : Nat) : StepOut :=
  match q with
  | 0 => .ok (.unwound 42)
  | n + 1 => .ok (.returned (n + 1))

def badUnsafeUnwind (q : Nat) : StepOut :=
  match q with
  | 0 => .fault
  | n + 1 => .ok (.returned (n + 1))

def divergingUnsafe (_q : Nat) : StepOut := .diverges

/-- Refutation 1 (Loophole L1/L2): ReturnOnlyEquiv accepts panic-to-UB laundering. -/
theorem returnOnly_misses_panic_to_ub :
    ReturnOnlyEquiv refSafeUnwind badUnsafeUnwind ∧
    ¬ TotalSafeTwinEquiv refSafeUnwind badUnsafeUnwind 0 := by
  constructor
  · intro q v h
    cases q with
    | zero => cases h
    | succ n => exact h
  · intro h
    cases h with
    | intro hWf _ =>
      exact hWf.1 rfl

/-- Refutation 2 (Loophole L3): Partial implication permits a hanging unsafe twin. -/
theorem partialEquiv_misses_divergence :
    (∀ q, PartialSafeTwinEquiv refSafeUnwind divergingUnsafe q) ∧
    ¬ TotalSafeTwinEquiv refSafeUnwind divergingUnsafe 1 := by
  constructor
  · intro q
    constructor
    · intro h; cases h
    · intro out h; cases h
  · intro h
    cases h with
    | intro _ hEq =>
      cases hEq

/-- Refutation 3 (McLean Paradox): branch on secret violates trace non-interference,
    whereas masked branchless arithmetic preserves identical trace observations. -/
def ctCheckBranch (secCond : Bool) : List LeakObs :=
  if secCond then [LeakObs.branch true, LeakObs.memIdx 1]
  else [LeakObs.branch false, LeakObs.memIdx 0]

def ctMaskSelect (secBit a b : Nat) : Nat × List LeakObs :=
  (a * secBit + b * (1 - secBit), [LeakObs.memIdx 0])

theorem declassified_branch_violates_ct_2safety :
    ctCheckBranch true ≠ ctCheckBranch false ∧
    (ctMaskSelect 1 10 20).2 = (ctMaskSelect 0 10 20).2 := by
  constructor
  · intro h
    cases h
  · rfl

/-- Linear 4-to-1 BiAlign certificate combinator for SIMD / loop unrolling. -/
def iterN {α : Type} (step : α → α) (n : Nat) (x : α) : α :=
  Nat.rec x (fun _ acc => step acc) n

def stepQuad {α : Type} (step : α → α) (x : α) : α :=
  step (step (step (step x)))

def tileSteps (k : Nat) : Nat :=
  Nat.rec 0 (fun _ acc => acc + 4) k

theorem iterN_add {α : Type} (step : α → α) (a b : Nat) (x : α) :
    iterN step (a + b) x = iterN step b (iterN step a x) := by
  induction b with
  | zero => rfl
  | succ k ih =>
    dsimp [iterN]
    rw [ih]

theorem biAlign_stride4_sound {S T : Type} (R : S → T → Prop)
    (stepS : S → S) (stepT : T → T)
    (hTile : ∀ s t, R s t → R (stepQuad stepS s) (stepT t)) :
    ∀ k s t, R s t → R (iterN stepS (tileSteps k) s) (iterN stepT k t) := by
  intro k
  induction k with
  | zero =>
    intro s t h
    exact h
  | succ n ih =>
    intro s t h
    dsimp [tileSteps, iterN]
    rw [iterN_add stepS (tileSteps n) 4 s]
    exact hTile _ _ (ih s t h)

end AnnealSafeTwinProbe
```

---

### 6. Anneal Evaluation `(T1, P1–P5, C1–C2)` and Refutations

Basis: derived.

| Criterion | (A) Return-Only Equivalence | (B) Unconstrained Path-Product 2-Safety | (C) `SecScalar` Type Discipline Alone | (D) Statement-Separated `TotalSafeTwinEquiv` + `SecScalar` + `BiAlign` |
| :--- | :--- | :--- | :--- | :--- |
| **(T1) 0-TCB Bridge** | Clean, but unsound | High kernel blowup | Unfolded `SecScalar` stays `0-TCB` | **Strong**: statement uses `Trusted.MirSemantics` only (`0-TCB` inside `theory/`) |
| **(P1) Human Auditability** | Misleadingly simple (masks UB/hangs) | Poor (exponential alignment conditions) | **High**: Rust/spec secrecy annotations make leakage boundaries self-evident | **High**: reference Rust twin IS the spec; phantom `SecLevel` + `LeakTrace` make assumptions explicit |
| **(P2) Day-2 Locality** | Breaks when compiler inserts panics | Global invalidation on unroll changes | Local to crypto helpers | **High**: tile unroll factor `4` lives inside local `BiAlign` lemma |
| **(P3) Kernel Scaling** | $O(\|P\|)$ | $O(\|P\|^2)$–exponential | $O(\|P\|)$ | **$O(\|P\|)$** linear proof size via `biAlign_stride4_sound` |
| **(P4) Composability** | Fails on unwind & `Diverges` | Fails modular call composition | Fails unless combined with operational trace parity | Handles normal return, `.unwound callerMem`, `Diverges`, branchless CT, and SIMD tiles |
| **(P5) Failure Legibility** | Masks `.fault`/hangs | Cryptic unmet path obligations | Immediate type error on `SEC` $\to$ branch | Pinpoints exact deviating step: `.fault`, `.unwound`, `Diverges`, or `LeakObs` mismatch |
| **(C1–C2) Minimality** | Over-collapses outcomes into `.returned` | Unstructured | Cannot derive binary trace transfer alone | Preserves 4 distinct concepts: UB-free `WellFormed`, terminal `Behavior`+`Diverges`, 2-safety `LeakObs`, and `BiAlign` stride factoring |

Four premature collapses (`C2`) are explicitly refuted:
1. **Collapsing `TerminalOut` into bare return values (`ReturnOnlyEquiv`):** Refuted by `returnOnly_misses_panic_to_ub` (panic-to-UB laundering passes normal return equivalence).
2. **Collapsing `TotalSafeTwinEquiv` into partial implication without `Diverges` parity:** Refuted by `partialEquiv_misses_divergence` (an unsafe loop hanging forever passes all-finite-trace checks vacuously).
3. **Collapsing constant-time 2-safety into 1-safety behavioral equivalence:** Refuted by `declassified_branch_violates_ct_2safety` (secret-dependent branching changes `LeakObs` traces without changing returned scalar outputs).
4. **Collapsing `BiAlign` tiled simulation into strict `1`-to-`1` lockstep alignment:** Fails immediately on 4-lane SIMD and unrolled crypto loops because scalar execution needs 4 logical iterations (`stepQuad`) per 1 vectorized iteration (`biAlign_stride4_sound`).

---

## Boundaries

- **not examined:** Live `lean`/`lake` compilation of the Section 5 `AnnealSafeTwinProbe` Lean module during this inspection; runtime MIR capture behavior of `TerminatorKind.call` on non-`main` development branches beyond the pinned `joshlf/anneal@c131b320` commit; direct source inspection of Rust crates such as `subtle` or Coq `VST`.
- **unknown:** Whether future `Trusted.MirSemantics` call-frame models on `joshlf/anneal` expose interprocedural `TerminalOut.unwound` directly through multi-frame `Step` or require per-call landing-pad summaries inside `theory/`; concrete Lean `v4.34.1` `whnf` millisecond timings for `BiAlign` over vectorized crypto kernels (`curve25519`/`blake2`) once SIMD intrinsics are added to `MirSemantics`.
- **known not to apply:** Functional `TotalSafeTwinEquiv` does **not** automatically confer hardware constant-time guarantees after LLVM backend lowering unless paired with a target-level `CTCompiles` or binary leakage validator; `SecScalar` phantom wrappers in `theory/` do **not** prevent timing channels if `Lib.RawIntTypes`-style declassification escapes occur inside unverified FFI/inline assembly blocks.
- **unsupported:** On `joshlf/anneal@c131b320`, `Trusted.MirSemantics` rejects non-empty `callerMem` at entry (`MirSemantics.lean:1686-1690`) and steps any reachable `TerminatorKind.call` to `.fault .unsupported` (`L1691-1694`), bounding immediate executable `SafeTwin` replay to single-body value/scalar kernels until heap/call extensions land; `TrustedBoundary.lean:442-596` forbids `omega`, `ring`, `bv_decide`, `native_decide`, `rcases`, `deriving`, `partial`, `._unsafe_rec`, `Std.*`, and `Lean.*`.

---

## Evidence

- **Anneal (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
  - `trusted/lean/Trusted/MirSemantics.lean:332-335` (`FaultKind`), `586-604` (`CallerMemory`, `Query`, `Out`, `TerminalOut.returned | .unwound`), `646` (`ValidChoice`), `1618-1676` (`Step`, `Reaches`, `ReachesResult`, `WellFormed`, `Behavior`, `Diverges`, `SatisfiesPost`), `1685-1745` (`callerMem` & `TerminatorKind.call` scoping, `entryProgForBody`, `ValidEntryArgs`, `BodyStaticAdmitted`).
  - `trusted/correspondence/Trusted/Correspondence.lean:1-160` (`CorrespondenceClaim`, `FaultEquivalenceClaim`, `MiriMoveDeinitWiringClaim`, pinned `lean-miri` `c92d1d97`, `rustc` `8144389c`, `deinitMovedPlace = true`).
  - `trusted/audit/TrustedBoundary.lean:442-596` (Pass-1 closed syntax/import/tactic allowlists and Statement-Origin Separation).
- **`lean-miri` (`proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`):**
  - `Miri/Interpreter/ControlFlow.lean:42-90, 125-148` (`unwindToBlock` handling `.Cleanup`, `.Unreachable => .error (.undefinedBehavior ...)`, `.Continue`, `.Terminate`, `returnFromCurrentFrame`, `UnwindResume`, `Assert`).
- **Rust Compiler MIR (`rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`):**
  - `compiler/rustc_middle/src/mir/syntax.rs:710, 854-860, 1011-1025` (`UnwindResume`, `Assert`, `UnwindAction`) and `terminator.rs:1-80` (`SwitchTargets`).
- **HACL* (`hacl-star/hacl-star@f557259007db9933442dde10aa995c1b00bd3446`, ACM CCS 2017):**
  - `lib/Lib.IntTypes.fsti:132-158, 250, 346, 656, 732-795, 878-958` (`secrecy_level`, `sec_int_t`, `secret`, `cast`, `shiftval`, `eq_mask`..`lte_mask`, `PUB`-only `div`/`mod`/`eq`..`gte`).
  - `lib/Lib.RawIntTypes.fsti:1-37` (`u*_to_UInt*` explicit constant-time break warning).
- **SAW / Crux-MIR (`GaloisInc/saw-script@f290af7bda474779c8e5685ddd30612a7e6f0399`, `arXiv:2410.18280`):**
  - `CHANGES.md:123-166` (`mir_field_value`, `mir_field_ref`, `mir_set_exception_context_*`) and `arXiv:2410.18280` (`#[crux_spec_for]`, `mir_verify`, `mir_extract`).
- **Relational Kleene Algebra Literature:**
  - `GKAT`: Smolka et al., POPL 2020, DOI `10.1145/3371129`.
  - `BiKAT`: Antonopoulos et al., POPL 2023, DOI `10.1145/3571213`.
  - `BiGKAT`: ESOP 2025, DOI `10.1007/978-3-031-90897-2_12`.
- **Lean 4 Toolchain:** `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`).

---

## Revalidation

1. **Kernel-check the inline Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) probe:** Extract Section 5's Lean block to `/tmp/AnnealSafeTwinProbe.lean` and run `lean /tmp/AnnealSafeTwinProbe.lean`, verifying exit code `0`, zero `sorry`, standard axioms only, and Pass-1 compliance against `TrustedBoundary.lean`.
2. **Re-verify pinned upstream semantics and constant-time specs:**
   ```bash
   curl --http1.1 -fsSL "https://raw.githubusercontent.com/proofs-rs/lean-miri/c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a/Miri/Interpreter/ControlFlow.lean" | sed -n '42,78p'
   curl --http1.1 -fsSL "https://raw.githubusercontent.com/hacl-star/hacl-star/f557259007db9933442dde10aa995c1b00bd3446/lib/Lib.RawIntTypes.fsti" | sed -n '1,37p'
   ```
   Check `joshlf/anneal`'s `MirSemantics.lean` `WellFormed`, `TerminalOut`, `Diverges`, and `TerminatorKind.call` definitions whenever upgrading past commit `c131b320`.
