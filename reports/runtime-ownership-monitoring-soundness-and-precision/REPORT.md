# Run-time ownership monitoring of separation-logic contracts: soundness, completeness, and precision in a toy Lean 4 model

## Summary

This package is a self-contained Lean 4 model of a run-time ownership monitor for separation-logic
contracts (`owned(p)`-style pre- and postconditions), in the style of Fulminate's ghost-state
instrumentation for CN specifications. It proves, against the declarative (exact) separation-logic
meaning of the contracts, when an accepted run really satisfied every contract (soundness), when every
satisfying run is accepted (completeness), how both depend on the precision of the contracts and on the
monitor's footprint-computation strategy, and what must be assumed about uninstrumented (unannotated)
code. All 20 results below are kernel-checked. Model–system relation: none proved (soundness and completeness relate the model's monitor to the model's own declarative semantics). They are statements about the toy model; they neither establish nor refute the corresponding claims about Fulminate, CN, the `owned` primitive proposed for Rust contracts or its Miri prototype (the modeling-bridge claims B1–B5 under **Findings** argue such connections separately).

* **R1a-greedy-footprints-are-witnesses.** For every contract of the toy assertion language (byte-ownership cells, pure conditions, separating conjunction, and arbitrary, possibly imprecise, disjunction), any footprint the greedy evaluator returns lists allocated bytes of the fragment whose restriction satisfies the contract.
* **R1b-search-footprints-are-witnesses.** The same holds for the first footprint found by exhaustive backtracking search.
* **R1-monitor-soundness.** If the footprint strategy is sound, the monitor performs the leak check, and unannotated callees are checked as if inlined, then every run the monitor accepts satisfies all its contracts, with the monitor's own footprints as the witnesses.
* **R1prime-no-false-alarms-relative-to-own-footprints.** Under any configuration and any strategy, a run that satisfies its contracts with the strategy's own footprints is accepted.
* **R1-trusted-soundness-under-unannot-confinement.** With a sound strategy and the leak check, acceptance also implies satisfaction when unannotated callees are trusted (not instrumented), provided every read and write executed by unannotated code targets an allocated byte of the frame it runs in; annotated callees reached from unannotated code are still monitored.
* **R1-frame-property.** A run that satisfies its contracts in a frame owning exactly the addresses `O` changes no byte outside `O`.
* **R1-footprint-witnesses-separating-conjunction.** If the restriction of a fragment to an address list `F` satisfies `A`, the fragment satisfies `A ∗ R`, where `R` holds of exactly the remainder, with the split exposed.
* **R2-disjPrecise-implies-precise.** An assertion in which every disjunction is precise is precise.
* **R2a-greedy-recovers-every-witness-for-disjPrecise.** If every disjunction in a contract is precise, the greedy evaluator recovers every witness: whenever some sub-fragment satisfies the contract, the greedy footprint carves out exactly that sub-fragment.
* **R2b-search-recovers-every-witness-for-precise.** If a contract is precise, backtracking search recovers every witness.
* **R2-recovers-every-witness-implies-precise.** A contract for which some strategy recovers every witness is necessarily precise (this is built into the definition of witness recovery).
* **R2c-satisfies-implies-satisfiesBy-for-witness-recovering-strategies.** If the strategy recovers every witness of every contract occurring in the program, a run that satisfies its contracts with some (angelically chosen) footprints also satisfies them with the strategy's footprints.
* **R2-greedy-monitor-complete-for-disjPrecise-contracts.** If every disjunction in every contract of the program is precise, the greedy monitor, under any configuration, accepts every run that satisfies its contracts.
* **R2-search-monitor-complete-for-precise-contracts.** If every contract of the program is precise, the backtracking monitor, under any configuration, accepts every run that satisfies its contracts.
* **R2-greedy-characterization.** For programs whose contracts contain only precise disjunctions, the strict greedy monitor (leak check on, unannotated callees checked) accepts a run if and only if the run satisfies its contracts.
* **R2-search-characterization.** For programs whose contracts are all precise, the strict backtracking monitor accepts a run if and only if the run satisfies its contracts.
* **R2-owned0-or-owned1-defeats-every-sound-online-strategy.** For the imprecise contract `owned 0 ∨ owned 1`, two runs from the same heap and ownership (the callee reads byte 0; the callee reads byte 1) both satisfy their contracts, yet no sound strategy, under any monitor configuration, gets both accepted, because the footprint is chosen from the contract and the caller's fragment before the callee runs.
* **CE-precise-not-disjPrecise-greedy-false-alarm.** Precision of a whole contract is not enough for the greedy monitor: for the precise contract `C' = ((owned 0 ∗ owned 1) ∨ owned 0) ∗ owned 1`, whose inner disjunction is imprecise, the strict greedy monitor rejects a satisfying run that the backtracking monitor accepts.
* **R3-trusted-unannotated-callee-breaks-soundness.** If unannotated callees are trusted and not confined, a monitor with a sound strategy and the leak check accepts a run in which an unannotated helper writes a byte its caller kept, violating the contracts.
* **CE-no-leak-check-stale-depth-ownership.** Without the leak check, a byte leaked by one callee stays attributed to call depth 1, and a later sibling callee that was given only another byte reads it and is accepted.

Every result's limits are listed first under **Boundaries** (*Non-claims*). In particular, nothing here is a
theorem about Fulminate, CN, Miri, or any other implementation: each connection to a real system is a
separate `derived (modeling bridge)` claim under **Findings** (*Modeling bridge*).

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

**Model fidelity: toy model.** All definitions are toy definitions in the namespace `Toy.Monitor` (Lean
library `ToyMonitor`, directory `lean/`). They are meant to capture the core of depth-indexed run-time
ownership monitors for separation-logic contracts:

* a byte-addressed heap and exact (linear, non-intuitionistic) separation-logic assertions built from
  single-byte ownership cells with a value predicate (`owned p`, `pointsTo p v`), pure conditions,
  separating conjunction and general disjunction;
* a monitor that records the owning call depth of each byte, transfers the footprint of the precondition
  to the callee at a call and the footprint of the postcondition back at return, optionally checks for
  leaks at return, and checks every access of instrumented code;
* a *footprint strategy* that the monitor uses to turn a contract and the caller's owned fragment into a
  list of bytes; the strategy sees neither the callee's code nor anything after the call (the monitor is
  *online*);
* two policies for calls to unannotated functions: checked as if inlined into the caller, or trusted
  (their own accesses unchecked, annotated functions they call still monitored).

**Known gaps** (also stated as a non-claim of every result): programs are straight-line (no branching,
loops, recursion, allocation, deallocation or concurrency); one address is one byte and stores never change
the heap's domain; contracts have no logical variables, value-binding resource outputs (CN's `take`, the
value returned by `owned` in the Rust proposal), function parameters or return values, existentials,
recursive predicates or iterated separating conjunction; ownership is whole (no fractional or read-only
permissions); there are no allocation-block tokens (`alloc_block`); a single run is judged at a time.
The real systems these definitions are meant to resemble are related to the results only through the
modeling-bridge claims under **Findings**, never by the kernel check.

**Subjects and how they relate.** The Lean 4 toolchain (`leanprover/lean4` release `v4.34.1`, tag commit
`5045d0056413266e57c625dcd7c365b10e377c52`) is the checker of every theorem. The papers listed as subjects
(Fulminate, CN, Nguyen–Kuncak–Chin, O'Hearn–Yang–Reynolds) and the Archive of Formal Proofs entry
Separata are the primary sources for prior art and for the modeling bridges; the formal results do not
depend on them. Other references (an accepted Rust compiler-team proposal and an unmerged Miri prototype
branch among them) are context only and appear under **Evidence** with their exact coordinates.

**Lean version and dependencies.** Lean `leanprover/lean4:v4.34.1`, core Lean only: no Mathlib and no
Lake dependencies (`lean/lakefile.toml` declares one `[[lean_lib]]` and no `[[require]]`). The theorems use
only the axioms `propext`, `Classical.choice` and `Quot.sound` (recorded per declaration under
**Evidence**). The results were checked on 2026-11-20; they are not expected to depend on the toolchain
version beyond ordinary source compatibility, but only `v4.34.1` was checked.

## Findings

**Design question (shared by every result).** Separation-logic ownership contracts (`owned(p)`-style
pre/postconditions) can be monitored at run time by a per-byte ownership map with transfer on call/return.
Which fragment of the contract language has a computational interpretation such that an accepted run really
satisfied every contract as a separation-logic assertion, when is the monitor complete, and what does it
assume about unannotated code? Each result below states which part it informs: (a) soundness, (b)
completeness, or (c) unannotated code.

**Answer in this toy model.**

1. *Soundness needs only a sound footprint computation*: it holds for the entire assertion language,
   including imprecise disjunction, provided the monitor performs the leak check and checks unannotated
   callees as inlined (R1, R1a, R1b). Each of these conditions is necessary (counterexamples).
2. *Completeness needs witness recovery.* The monitor accepts every run satisfying its contracts when its
   strategy recovers every witness of every contract (R2c with R1′). Witness recovery includes uniqueness,
   so it forces precision; exhaustive search recovers every witness of every precise contract (R2b); the
   greedy (committed-choice) evaluator does so when every disjunction is precise (R2a), but not for all
   precise contracts (`C'`), and disjunction-precision is sufficient, not necessary (`CFlip`). For the
   imprecise contract `owned 0 ∨ owned 1` no sound online strategy accepts both of two valid runs
   (impossibility). Weaker notions behave differently: search finds *some* footprint for every assertion,
   and a monitor can be complete for one particular program with imprecise contracts.
3. *Unannotated callees*: checking them as inlined is sound (R1); trusting them is sound under the
   operational confinement assumption `UnannotConfined` (R1-trusted) and unsound without it (R3).

### Model (key definitions unfolded)

The verbatim Lean source of every definition used in a statement is in `lean/ToyMonitor/Basic.lean`,
`Strategy.lean`, `Monitor.lean`, `Examples.lean` (the concrete instances `hTwo`, `hOne`, `C`, `C'`, `runL`,
`runR`, `runP`, `pCallback`, `sBad`, `sAll`), `Results.lean` (the concrete instances `CFlip`, `progNV`,
`progMixed`, `progOr`, `runBad`, `runLeak`, `runStale`, `runTrusted`, `pUnannotRead`) and `Lemmas.lean`
(the ownership-depth invariant `OwnInv`, which occurs in no result statement; among the quoted declarations it
occurs only in the supporting lemma `monitorAux_sound`). The Lean blocks below are copied verbatim from that source
(declaration doc comments omitted); the bullet descriptions restate the remaining definitions clause by
clause. The hash of every statement's full definition closure is recorded under **Evidence**.

**Heaps.** `Addr := Nat`, `Val := Nat` (one address is one byte); `Heap := Addr → Option Val` (a heap or a
fragment; `none` means not part of it).

* `Heap.Disjoint g₁ g₂ := ∀ a, g₁ a = none ∨ g₂ a = none`
* `Heap.union g₁ g₂ a := match g₁ a with | some v => some v | none => g₂ a`
* `Heap.Sub g₁ g := ∀ a v, g₁ a = some v → g a = some v` (sub-fragment)
* `g.restrict F a := if a ∈ F then g a else none`; `g.remove F a := if a ∈ F then none else g a`
* `h.write a v` overwrites an *allocated* byte and leaves the heap unchanged otherwise (the domain never
  changes; there is no allocation).

**Assertions and their exact meaning.**

```lean
-- lean/ToyMonitor/Basic.lean:70-74
inductive Assn where
  | cell (p : Addr) (P : Val → Bool)
  | pure (b : Bool)
  | sep (A B : Assn)
  | or (A B : Assn)

-- lean/ToyMonitor/Basic.lean:77
def Assn.owned (p : Addr) : Assn := .cell p (fun _ => true)

-- lean/ToyMonitor/Basic.lean:80
def Assn.pointsTo (p : Addr) (v : Val) : Assn := .cell p (fun w => w == v)

-- lean/ToyMonitor/Basic.lean:83
def Assn.emp : Assn := .pure true

-- lean/ToyMonitor/Basic.lean:88-93
def sat : Assn → Heap → Prop
  | .cell p P, g => ∃ v, g p = some v ∧ P v = true ∧ ∀ a, a ≠ p → g a = none
  | .pure b, g => b = true ∧ ∀ a, g a = none
  | .sep A B, g => ∃ g₁ g₂, Heap.Disjoint g₁ g₂ ∧ (∀ a, g a = Heap.union g₁ g₂ a) ∧
      sat A g₁ ∧ sat B g₂
  | .or A B, g => sat A g ∨ sat B g

-- lean/ToyMonitor/Basic.lean:97-98
def SepP (P R : Heap → Prop) (g : Heap) : Prop :=
  ∃ g₁ g₂, Heap.Disjoint g₁ g₂ ∧ (∀ a, g a = Heap.union g₁ g₂ a) ∧ P g₁ ∧ R g₂

-- lean/ToyMonitor/Basic.lean:104-105
def IsFootprint (A : Assn) (g : Heap) (F : List Addr) : Prop :=
  (∀ a ∈ F, (g a).isSome = true) ∧ sat A (g.restrict F)

-- lean/ToyMonitor/Basic.lean:109-110
def Precise (A : Assn) : Prop :=
  ∀ g g₁ g₂, Heap.Sub g₁ g → Heap.Sub g₂ g → sat A g₁ → sat A g₂ → g₁ = g₂

-- lean/ToyMonitor/Basic.lean:119-123
def DisjPrecise : Assn → Prop
  | .cell _ _ => True
  | .pure _ => True
  | .sep A B => DisjPrecise A ∧ DisjPrecise B
  | .or A B => Precise (.or A B) ∧ DisjPrecise A ∧ DisjPrecise B
```

**Footprint strategies.** `Strategy := Assn → Heap → Option (List Addr)`, applied to a contract and the
caller's fragment only.

```lean
-- lean/ToyMonitor/Strategy.lean:20-21
def StrategySound (s : Strategy) : Prop :=
  ∀ A g F, s A g = some F → IsFootprint A g F

-- lean/ToyMonitor/Strategy.lean:32-34
def RecoversEveryWitness (s : Strategy) (A : Assn) : Prop :=
  ∀ g g', Heap.Sub g' g → sat A g' →
    ∃ F, s A g = some F ∧ (∀ a ∈ F, (g a).isSome = true) ∧ g.restrict F = g'

-- lean/ToyMonitor/Strategy.lean:39-40
def ExistsFootprintComplete (s : Strategy) (A : Assn) : Prop :=
  ∀ g g', Heap.Sub g' g → sat A g' → ∃ F, s A g = some F ∧ IsFootprint A g F
```

`RecoversEveryWitness` requires the single answer `s A g`, which cannot depend on `g'`, to carve out
*every* witness `g'`; uniqueness is therefore built in. `ExistsFootprintComplete` asks only for *some*
genuine footprint whenever one exists.

* `fpGreedy`: `cell p P` reads the byte (`some [p]` if allocated and `P` holds); `pure b` gives `some []`
  iff `b`; `sep A B` computes `A`'s footprint `F₁`, then `B`'s footprint `F₂` in `g.remove F₁`, and returns
  `F₁ ++ F₂`; `or A B` returns `A`'s footprint if there is one, otherwise `B`'s (committed left-first choice:
  no backtracking into a disjunct that succeeded). `fpGreedyR` is the same with right-first `or`.
* `fpAll` returns all consumption-style footprints (`or`: concatenation; `sep`: all pairs, the second
  computed in the remainder); `fpSearch A g := (fpAll A g).head?` (backtracking search).
* `fpAtom` handles `cell` and `pure` like `fpGreedy` and fails on `sep` and `or`.

**Programs, the monitor, and the meaning of contracts.**

```lean
-- lean/ToyMonitor/Monitor.lean:27-35
inductive Prog where
  | skip
  | read (a : Addr)
  | write (a : Addr) (v : Val)
  | seq (p q : Prog)
  /-- Call to an annotated callee with contract `pre`/`post`; `body` is the callee. -/
  | call (pre post : Assn) (body : Prog)
  /-- Call to an unannotated callee (no contract); `body` is the callee. -/
  | unannot (body : Prog)
```

* `exec : Prog → Heap → Heap` is plain execution: reads do nothing, `write a v` is `h.write a v`, calls run
  their body. `p.contracts` lists every pre- and postcondition occurring in `p`.
* `Own := Addr → Option Nat` (owning frame = call depth); `initOwn O a := if a ∈ O then some 0 else none`;
  `frag h o d a := if o a = some d then h a else none`;
  `transfer F src dst o a := if a ∈ F ∧ o a = some src then some dst else o a`.
* `structure MonCfg where leakCheck : Bool; checkUnannot : Bool`; `MonCfg.strict := ⟨true, true⟩`.

`monitorAux cfg s chk p h o d : Option Own` runs `p` from heap `h` with ownership map `o` in frame `d`;
`chk` says whether the running code is instrumented:

* `read a`, `write a v`: if `chk`, succeed iff `o a = some d` and `h a` is allocated; if not `chk`, succeed;
* `seq p q`: run `p`, then `q` from `exec p h` (same `chk`);
* `call P Q body` (any `chk`): `F ← s P (frag h o d)`; fail unless every `a ∈ F` has `o a = some d`;
  `o₂ ← monitorAux cfg s true body h (transfer F d (d+1) o) (d+1)` (annotated callees are always
  instrumented); `F' ← s Q (frag (exec body h) o₂ (d+1))`; fail unless every `a ∈ F'` has
  `o₂ a = some (d+1)`; let `o₃ := transfer F' (d+1) d o₂`; if `cfg.leakCheck` and some `a ∈ F` has
  `o₃ a = some (d+1)`, fail; otherwise return `o₃`;
* `unannot body`: run `body` in the same frame with `chk := chk && cfg.checkUnannot`.

`monitor cfg s := monitorAux cfg s true`, and
`Accepts cfg s p h O := (monitor cfg s p h (initOwn O) 0).isSome = true` (decidable).

`Satisfies p h O` (the frame owns exactly `O`; footprints chosen angelically):

* `skip`: `True`; `read a`, `write a v`: `a ∈ O ∧ (h a).isSome = true`;
* `seq p q`: `Satisfies p h O ∧ Satisfies q (exec p h) O`; `unannot body`: `Satisfies body h O`;
* `call P Q body`: `∃ F, IsFootprint P (h.restrict O) F ∧ Satisfies body h F ∧
  IsFootprint Q ((exec body h).restrict F) F`.

`SatisfiesBy s p h O` is the same except at `call P Q body`:
`∃ F, s P (h.restrict O) = some F ∧ IsFootprint P (h.restrict O) F ∧ SatisfiesBy s body h F ∧
∃ F', s Q ((exec body h).restrict F) = some F' ∧ (∀ a, a ∈ F' ↔ a ∈ F) ∧
IsFootprint Q ((exec body h).restrict F) F'`.

`UnannotConfined s p h O := UnannotConfinedAux s false p h O`, where `UnannotConfinedAux s u` (`u`: running
inside an unannotated callee) requires: at `read a` / `write a v`, `u = true → a ∈ O ∧ (h a).isSome = true`;
at `seq p q`, both parts (the second from `exec p h`); at `call P _ body`,
`∀ F, s P (h.restrict O) = some F → UnannotConfinedAux s false body h F`; at `unannot body`,
`UnannotConfinedAux s true body h O`; at `skip`, `True`. It constrains only the targets of accesses made by
unannotated code along the concrete run, relative to the frames the strategy computes; it does not mention
`sat`, `Satisfies` or `SatisfiesBy`.

**Ownership-depth invariant (`Lemmas.lean`; used only in proof-internal lemmas, including `monitorAux_sound`).**
`OwnInv o d O := (∀ a, o a = some d ↔ a ∈ O) ∧ (∀ a d', d < d' → o a ≠ some d')`: frame `d` owns exactly
the addresses in `O`, and no byte is owned by a frame deeper than `d`.

**Concrete instances.** `hTwo`: bytes 0 and 1 allocated, both holding 0; `hOne`: byte 0 allocated, holding 0.
`C := owned 0 ∨ owned 1` (imprecise); `C' := ((owned 0 ∗ owned 1) ∨ owned 0) ∗ owned 1` (precise, not
disjunction-precise); `CFlip := (owned 0 ∨ (owned 0 ∗ owned 1)) ∗ owned 1` (the same heap predicate as `C'`
with the inner disjuncts swapped). `runL := call C C (read 0)`, `runR := call C C (read 1)`,
`runP := call C' C' skip`, `progNV := call (owned 0) (pointsTo 0 5) (unannot (write 0 5))`,
`progMixed := call (owned 0) (owned 0) (unannot (seq (write 0 5) (call (owned 0) (pointsTo 0 5) (read 0))))`,
`progOr := call (pointsTo 0 0 ∨ pointsTo 0 1) (pointsTo 0 1) (write 0 1)`,
`runBad := call (pointsTo 0 1) (owned 0) skip`, `runLeak := call (owned 0) emp skip`,
`runStale := seq (call (owned 0) emp skip) (call (owned 1) (owned 1) (read 0))`,
`runTrusted := call (owned 0) (owned 0) (unannot (write 1 7))`,
`pCallback := call (owned 0) (owned 0) (unannot (call (pointsTo 0 1) (owned 0) skip))`,
`pUnannotRead := call (owned 0) (owned 0) (unannot (read 1))`; `sBad := fun _ _ => some [0]`,
`sAll := fun _ _ => some [0, 1]` (both unsound).

**Intended positive and negative examples (all proved, `Examples.lean`).**
`sat`: `sat_pointsTo_single`, `sat_owned0_sep_owned1_hTwo` (+); `not_sat_owned0_sep_owned0` (exclusivity),
`not_sat_owned0_hTwo` (exactness) (−). `SepP`: `sepP_owned0_owned1_hTwo` (+), `not_sepP_owned0_owned0` (−).
`IsFootprint`: `isFootprint_owned0_hTwo` (+); `not_isFootprint_owned0_hTwo_01`, `not_isFootprint_owned2_hTwo`
(−). `Precise`: `precise_owned`, `precise_pointsTo00_or_pointsTo01` (+); `not_precise_C` (−). `DisjPrecise`:
`disjPrecise_pointsTo00_or_pointsTo01` (+); `not_disjPrecise_C`, `not_disjPrecise_C'` (−). `StrategySound`:
`fpAtom_strategySound` (+), `not_strategySound_sBad` (−). `RecoversEveryWitness`:
`fpAtom_recoversEveryWitness_cell` (+); `not_recoversEveryWitness_fpGreedy_C`,
`not_recoversEveryWitness_fpSearch_C` (−). `ExistsFootprintComplete`: `fpAtom_existsFootprintComplete_cell`
(+), `not_existsFootprintComplete_fpAtom_C` (−). `Accepts`: `accepts_strict_fpAtom_write_call`,
`accepts_trusted_unannot_store` (+); `not_accepts_read_unowned`, `not_accepts_callee_reads_kept_byte`,
`not_accepts_strict_leak`, `not_accepts_double_owned_pre`, `not_accepts_trusted_nested_annotated_call` (−).
`Satisfies`: `satisfies_write_call` (+); `not_satisfies_callee_reads_kept_byte`, `not_satisfies_leaky_post`
(−). `SatisfiesBy`: `satisfiesBy_fpAtom_write_call` (+), `not_satisfiesBy_fpGreedy_runR` (−).
`UnannotConfined`: `unannotConfined_inside`, `unannotConfined_annotated_read_unconstrained` (+);
`not_unannotConfined_outside`, `not_unannotConfined_top_read` (−). Computations (unnamed `example`s in
`Examples.lean`, checked by `decide` during the build):
`fpGreedy C hTwo = some [0]`, `fpGreedyR C hTwo = some [1]`, `fpGreedy C' hTwo = none`,
`fpSearch C' hTwo = some [0, 1]`.

### Modeling bridge (claims about real systems)

Each claim below is separate from the kernel-checked theorems. `Basis: derived (modeling bridge)`: it is reasoned from the cited sources and the model's definitions, and its reasoning is stated so that it can be checked. Results refer to these claims by label.

**B1. Fulminate-style depth-indexed monitors.** `Basis: derived (modeling bridge)`. Fulminate [S1, Sec. 2.3, 4.5.3] keeps reified ghost state recording, for each byte, the C stack depth that owns it; at a call the precondition's resources must be owned at the caller's depth and are moved to the callee's depth, postconditions move them back, leak checking is optional, and memory accesses can be instrumented to check ownership at the current depth. `monitorAux` has the same state (`Own := Addr → Option Nat`, owner = call depth) and the same transitions (`transfer` at call and return, optional `leakCheck`, access checks). By this structural correspondence, R1, R1′ and the completeness results describe what such a monitor guarantees *if* its per-contract footprint computation behaves like a `Strategy` that is sound (resp. recovers every witness) for the contract at hand, and if the features absent from the toy model (logical variables and value-binding resource outputs, iterated resources and recursive predicates, allocation and deallocation, C memory semantics) preserve the ownership-depth invariant. Neither condition is established here for Fulminate or any other implementation; Fulminate's Theorem 3.5 and Corollary 3.6 relate two dynamic semantics [S1, Sec. 3.4], not a monitor and a declarative satisfaction relation.

**B2. Restricted disjunction in CN and RefinedC.** `Basis: derived (modeling bridge)`. CN replaces general disjunction by ordered guarded cases and uses a conditional "to avoid backtracking during typechecking" [S2, Sec. 2.9, 4.1]; Fulminate states that CN's restrictions let runtime checking determine "without backtracking" which clause applies, citing RefinedC as precedent [S1, Sec. 2.4.2; S13]. In the toy model the corresponding semantic condition is `DisjPrecise`: when every disjunction is precise, committed left-first evaluation without backtracking recovers every witness (R2a) and the greedy monitor is complete (R2 greedy results), whereas a precise contract with an imprecise inner disjunction can produce a false alarm (CE-precise). This is consistent with, and gives one formal reading of, the stated rationale; it does not formalize CN's guards (which range over logical variables and values) and gives no syntactic criterion for `DisjPrecise`.

**B3. The `owned` primitive proposed for Rust contracts and the Miri prototype.** `Basis: derived (modeling bridge)`. rust-lang/compiler-team issue #942 [S5] proposes an `owned` assertion asserting exclusive ownership of the memory a raw pointer points to, consumed when asserted in a precondition and given back when asserted in a postcondition; run-time ownership tracking is left to interpreters. The toy `owned p` is the one-byte, whole-ownership, non-value-binding case of this, and the toy call/return transfer is its consume/give-back reading. The prototype tracker on the unmerged branch `fulminate` of the fork JoJoDeveloping/miri [S6] treats calls to non-annotated functions "as if they were inlined", with access checks still active; this is the toy `checkUnannot = true` policy covered by R1 and R1-trusted. On frame pop it inserts every remaining entry of the callee frame into the caller frame, with no check there that the popped frame is empty, a return policy the toy model does not have (see CE-no-leak-check-stale-depth-ownership); the results that assume `leakCheck = true` are therefore not claimed for that prototype. Its per-frame maps and dyadic fractions are also not modeled. The branch is not a durable subject; this bridge records what was read at the cited commit.

**B4. Imprecise assertions in an online monitor.** `Basis: derived (modeling bridge)`. O'Hearn, Yang and Reynolds [S4, Sec. 6] observe that with imprecise assertions "different splittings can be chosen at different times". The impossibility result is a monitor-level instance of this. Its argument transfers to a real monitor that (i) admits general disjunction such as `owned 0 ∨ owned 1` in contracts, (ii) commits at call time to one footprint that genuinely satisfies the precondition, (iii) bases that choice only on the contract and the caller's state, and (iv) judges assertions exactly: such a monitor rejects at least one of two valid runs. It does not apply to monitors that use one of the escape hatches listed under **Boundaries** (for example CN's restriction of disjunction, which excludes the imprecise contract).

**B5. Uninstrumented code.** `Basis: derived (modeling bridge)`. Fulminate as published places generated code in a single file and does not discuss uninstrumented or unannotated callees [S1, Sec. 4.6]; boundary checking against unverified code (Agten et al., as summarized by Fulminate [S10]) checks that the untrusted context has not mutated the module's state. In the toy model, leaving unannotated code uninstrumented is sound under a confinement assumption on its reads and writes (R1-trusted) and can be unsound without it (R3); the out-of-frame-read example shows that a before/after heap comparison does not establish that assumption. Any real monitor that leaves some code uninstrumented inherits an assumption of this kind; how to discharge it (static analysis, isolation, or instrumentation) is outside the model.

### Results

Each result below corresponds to one entry (card) of `results.json`; field values are quoted from it. All Lean names are in the namespace `Toy.Monitor`. Statements of the counterexamples, non-vacuity witnesses, positive controls and related theorems named in the cards follow the results.

#### R1a-greedy-footprints-are-witnesses: Greedy footprints are genuine footprints

* **Lean:** `Toy.Monitor.fpGreedy_strategySound` (`lean/ToyMonitor/Results.lean`); kind `theorem`; tier `T1`; depth `shallow`.
* **Plain claim:** For every assertion A (cells, pure conditions, separating conjunction, and arbitrary - possibly imprecise - disjunction) and every heap fragment g, whenever the greedy consumption-style footprint computation returns F, every address of F is allocated in g and the restriction of g to F satisfies A.
* **Tier `T1`:** Computational interpretation of separating conjunction by sequential consumption and of disjunction by committed left-first choice is the evaluation scheme described by Nguyen et al. (colouring) and Fulminate; stated here against the declarative exact semantics. (Novelty search: see **Evidence**.)
* **Lean statement:**

```lean
-- lean/ToyMonitor/Results.lean:128-129
/-- **R1a.** Every footprint the greedy strategy returns is a genuine footprint. -/
theorem fpGreedy_strategySound : StrategySound fpGreedy
```

* **With the key definitions unfolded** (`Fp A g F` abbreviates `IsFootprint A g F`, `Acc` abbreviates `Accepts`, `REW` abbreviates `RecoversEveryWitness`; all are quoted under *Model*):

```lean
∀ A g F, fpGreedy A g = some F → (∀ a ∈ F, (g a).isSome = true) ∧ sat A (g.restrict F)
```

* **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness | Counterexample (all other hypotheses hold, conclusion fails) |
  | --- | --- | --- | --- |
  | `fpGreedy A g = some F (inside StrategySound)` | The footprint must have been computed; failure says nothing. | `harmless` | — |

* **Depth:** `shallow`.
* **Non-vacuity witness:** fpGreedy (sep (owned 0 or owned 1) (owned 1)) hTwo = some [0, 1]. (`fpGreedy_strategySound_nonvacuous`)
* **Related proved statements:** `fpGreedyR_strategySound`, `fpGreedy_rejects_satisfying_run_imprecise_contract`, `fpGreedy_rejects_satisfying_run_precise_not_disjPrecise`.
* **Prior art:** [S3] Nguyen, Kuncak, Chin (VMCAI 2008); [S1] Fulminate (POPL 2025); [S2] CN (POPL 2023); [S14] Smans, Jacobs, Piessens (TOPLAS 2012) (full records under **Evidence**).
* **Design question:** informs part (a), soundness: when acceptance implies that every contract was satisfied (package question at the top of **Findings**).
* `Basis: execution (Lean kernel check)` for the theorem.
* `Basis: derived (modeling bridge)` for any reading of this result about a real system: see B1, B2 above, which state the reasoning and the gaps.
* **Non-claims:** listed under **Boundaries** (*R1a-greedy-footprints-are-witnesses*).

#### R1b-search-footprints-are-witnesses: Search footprints are genuine footprints

* **Lean:** `Toy.Monitor.fpSearch_strategySound` (`lean/ToyMonitor/Results.lean`); kind `theorem`; tier `T1`; depth `shallow`.
* **Plain claim:** For every assertion A and fragment g, the first footprint found by exhaustive consumption-style search (if any) consists of allocated addresses of g and carves out a sub-fragment satisfying A.
* **Tier `T1`:** Exhaustive (backtracking) enumeration of splittings is the naive reading of the separating conjunction. (Novelty search: see **Evidence**.)
* **Lean statement:**

```lean
-- lean/ToyMonitor/Results.lean:230-231
/-- **R1b.** Every footprint the backtracking strategy returns is a genuine footprint. -/
theorem fpSearch_strategySound : StrategySound fpSearch
```

* **With the key definitions unfolded** (`Fp A g F` abbreviates `IsFootprint A g F`, `Acc` abbreviates `Accepts`, `REW` abbreviates `RecoversEveryWitness`; all are quoted under *Model*):

```lean
∀ A g F, (fpAll A g).head? = some F → (∀ a ∈ F, (g a).isSome = true) ∧ sat A (g.restrict F)
```

* **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness | Counterexample (all other hypotheses hold, conclusion fails) |
  | --- | --- | --- | --- |
  | `fpSearch A g = some F (inside StrategySound)` | The footprint must have been found. | `harmless` | — |

* **Depth:** `shallow`.
* **Non-vacuity witness:** fpSearch C' hTwo = some [0, 1] for the precise, not disjunction-precise C'. (`fpSearch_strategySound_nonvacuous`)
* **Related proved statements:** `fpSearch_rejects_satisfying_run_imprecise_contract`.
* **Prior art:** [S3] Nguyen, Kuncak, Chin (VMCAI 2008) (full records under **Evidence**).
* **Design question:** informs part (a), soundness: when acceptance implies that every contract was satisfied (package question at the top of **Findings**).
* `Basis: execution (Lean kernel check)` for the theorem.
* `Basis: derived (modeling bridge)` for any reading of this result about a real system: see B1 above, which states the reasoning and the gaps.
* **Non-claims:** listed under **Boundaries** (*R1b-search-footprints-are-witnesses*).

#### R1-monitor-soundness: Monitor soundness (inline-checked unannotated callees)

* **Lean:** `Toy.Monitor.accepts_imp_satisfiesBy_of_strategySound` (`lean/ToyMonitor/Results.lean`); kind `theorem`; tier `T1`; depth `shallow`.
* **Plain claim:** If the footprint strategy is sound, the monitor performs the leak check, and unannotated callees are checked as inlined, then every run the monitor accepts satisfies all its contracts with the monitor's own footprints as witnesses: at each call the strategy's footprint F lies in the caller's fragment and that fragment restricted to F satisfies the precondition, the callee accesses only F, and at return the strategy's footprint has the same members as F and the callee's final fragment on F satisfies the postcondition.
* **Tier `T1`:** Fulminate proves that its ghost-state instrumentation and a resource-passing semantics bisimulate and fail under the same conditions (Thm 3.5, Cor 3.6) - a relation between two dynamic semantics; the present statement instead relates a depth-indexed monitor, generic in the footprint strategy, to the declarative separation-logic meaning of the contracts, exposing the monitor's footprints as witnesses. (Novelty search: see **Evidence**.)
* **Lean statement:**

```lean
-- lean/ToyMonitor/Results.lean:256-267
/-- **R1 (monitor soundness).** If the strategy is sound, the monitor performs the leak
check, and unannotated callees are checked as inlined, then a run accepted by the
monitor satisfies every contract, with the monitor's own footprints as witnesses: at
each call the strategy's footprint satisfies the precondition inside the caller's
fragment, the callee's accesses stay within it, and at return the strategy's footprint
has the same members and satisfies the postcondition. (The `cfg.checkUnannot = true`
instance of R1-trusted, in which the confinement assumption is vacuous.) -/
theorem accepts_imp_satisfiesBy_of_strategySound
    (s : Strategy) (hs : StrategySound s) (cfg : MonCfg)
    (hleak : cfg.leakCheck = true) (hun : cfg.checkUnannot = true)
    (p : Prog) (h : Heap) (O : List Addr) (hacc : Accepts cfg s p h O) :
    SatisfiesBy s p h O
```

* **With the key definitions unfolded** (`Fp A g F` abbreviates `IsFootprint A g F`, `Acc` abbreviates `Accepts`, `REW` abbreviates `RecoversEveryWitness`; all are quoted under *Model*):

```lean
∀ s, (∀ A g F, s A g = some F → IsFootprint A g F) →
  ∀ cfg, cfg.leakCheck = true → cfg.checkUnannot = true →
  ∀ p h O, (monitorAux cfg s true p h (initOwn O) 0).isSome = true → SatisfiesBy s p h O
-- where SatisfiesBy s demands, at every `call P Q body` run in a frame owning O:
--   ∃ F, s P (h.restrict O) = some F ∧ Fp P (h.restrict O) F ∧ SatisfiesBy s body h F ∧
--     ∃ F', s Q ((exec body h).restrict F) = some F' ∧ (∀ a, a ∈ F' ↔ a ∈ F) ∧
--       Fp Q ((exec body h).restrict F) F'
-- and, at every `read a` / `write a v` (annotated or not) in a frame owning O: a ∈ O ∧ (h a).isSome = true.
```

* **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness | Counterexample (all other hypotheses hold, conclusion fails) |
  | --- | --- | --- | --- |
  | `hs : StrategySound s` | The monitor never evaluates assertions itself; it trusts the strategy's footprint. | `tight` | `unsound_strategy_accepts_contract_violating_run` |
  | `hleak : cfg.leakCheck = true` | Exact postconditions must describe the callee's whole final fragment; without the check leaked bytes also stay attributed to the callee's depth. | `tight` | `noLeakCheck_accepts_leaky_post`, `noLeakCheck_later_callee_inherits_leaked_byte` |
  | `hun : cfg.checkUnannot = true` | Accesses of unannotated callees must be checked against the caller's frame (R1-trusted replaces this by a confinement assumption). | `tight` | `trusted_unannot_write_outside_footprint_accepted` |
  | `hacc : Accepts cfg s p h O` | The premise: the monitor accepted this run. | `tight` | `read_unowned_rejected_and_unsatisfied` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** fpAtom (sound), strict configuration, progNV = call (owned 0) (pointsTo 0 5) (unannot (write 0 5)) from the one-byte heap, accepted. (`accepts_imp_satisfiesBy_of_strategySound_nonvacuous`)
* **Related proved statements:** `monitorAux_sound`.
* **Prior art:** [S1] Fulminate (POPL 2025); [S2] CN (POPL 2023); [S3] Nguyen, Kuncak, Chin (VMCAI 2008); [S4] O'Hearn, Yang, Reynolds (POPL 2004); [S5] rust-lang/compiler-team issue #942; [S7] Ishtiaq and O'Hearn (POPL 2001), Reynolds (LICS 2002); [S8] Gradual verification (VMCAI 2018, OOPSLA 2020, POPL 2024); [S9] Tree Borrows (PLDI 2025), Miri (POPL 2026) (full records under **Evidence**).
* **Design question:** informs part (a), soundness: when acceptance implies that every contract was satisfied (package question at the top of **Findings**).
* `Basis: execution (Lean kernel check)` for the theorem.
* `Basis: derived (modeling bridge)` for any reading of this result about a real system: see B1, B3 above, which state the reasoning and the gaps.
* **Non-claims:** listed under **Boundaries** (*R1-monitor-soundness*).

#### R1prime-no-false-alarms-relative-to-own-footprints: No false alarms relative to the strategy's own footprints

* **Lean:** `Toy.Monitor.satisfiesBy_imp_accepts` (`lean/ToyMonitor/Results.lean`); kind `theorem`; tier `T1`; depth `substantive`.
* **Plain claim:** Under any monitor configuration and any strategy, a run that satisfies its contracts with the strategy's footprints (SatisfiesBy) is accepted by the monitor.
* **Tier `T1`:** Converse direction of the monitor/semantics correspondence (compare Fulminate Cor 3.6, 'fail under the same conditions', for its two operational semantics). (Novelty search: see **Evidence**.)
* **Lean statement:**

```lean
-- lean/ToyMonitor/Results.lean:271-276
/-- **R1′ (no false alarms relative to the monitor's own footprints).** Under any
configuration and any strategy, a run that satisfies its contracts with the strategy's
footprints is accepted. -/
theorem satisfiesBy_imp_accepts (s : Strategy) (cfg : MonCfg)
    (p : Prog) (h : Heap) (O : List Addr) (hsat : SatisfiesBy s p h O) :
    Accepts cfg s p h O
```

* **With the key definitions unfolded** (`Fp A g F` abbreviates `IsFootprint A g F`, `Acc` abbreviates `Accepts`, `REW` abbreviates `RecoversEveryWitness`; all are quoted under *Model*):

```lean
∀ s cfg p h O, SatisfiesBy s p h O → (monitorAux cfg s true p h (initOwn O) 0).isSome = true
```

* **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness | Counterexample (all other hypotheses hold, conclusion fails) |
  | --- | --- | --- | --- |
  | `hsat : SatisfiesBy s p h O` | The premise. | `tight` | `read_unowned_rejected_and_unsatisfied` |

* **Depth:** `substantive`.
* **Non-vacuity witness:** SatisfiesBy fpAtom progNV hOne [0]. (`satisfiesBy_imp_accepts_nonvacuous`)
* **Prior art:** [S1] Fulminate (POPL 2025); [S2] CN (POPL 2023) (full records under **Evidence**).
* **Design question:** informs part (b), completeness: when every satisfying run is accepted (package question at the top of **Findings**).
* `Basis: execution (Lean kernel check)` for the theorem.
* `Basis: derived (modeling bridge)` for any reading of this result about a real system: see B1 above, which states the reasoning and the gaps.
* **Non-claims:** listed under **Boundaries** (*R1prime-no-false-alarms-relative-to-own-footprints*).

#### R1-trusted-soundness-under-unannot-confinement: Soundness with trusted unannotated callees under confinement

* **Lean:** `Toy.Monitor.accepts_imp_satisfiesBy_of_unannotConfined` (`lean/ToyMonitor/Results.lean`); kind `theorem`; tier `T1`; depth `substantive`.
* **Plain claim:** With a sound strategy and the leak check, a run accepted by the monitor satisfies all contracts with the monitor's footprints, under either policy for unannotated callees, provided that - when unannotated callees are trusted (not instrumented) - every read and write they execute targets an allocated byte of the frame they run in (their caller's frame, as attributed by the strategy); annotated callees called from unannotated code are monitored in both policies.
* **Tier `T1`:** Makes explicit, as an operational property of the run, the assumption under which leaving unannotated code uninstrumented is sound; boundary checking against unverified code (Agten et al., as summarized by Fulminate) relies on a related integrity assumption, enforced there by other means. (Novelty search: see **Evidence**.)
* **Lean statement:**

```lean
-- lean/ToyMonitor/Results.lean:241-251
/-- **R1-trusted (soundness under either policy for unannotated callees, assuming
confinement when they are trusted).** If the strategy is sound and the monitor performs
the leak check, then a run accepted by the monitor satisfies every contract with the
monitor's own footprints as witnesses, provided that — when unannotated callees are
trusted (`cfg.checkUnannot = false`) — every read and write executed by an unannotated
callee targets an allocated byte of the frame it runs in (`UnannotConfined`). Annotated
callees called from unannotated code are monitored in both policies. -/
theorem accepts_imp_satisfiesBy_of_unannotConfined
    (s : Strategy) (hs : StrategySound s) (cfg : MonCfg) (hleak : cfg.leakCheck = true)
    (p : Prog) (h : Heap) (O : List Addr) (hacc : Accepts cfg s p h O)
    (hconf : cfg.checkUnannot = false → UnannotConfined s p h O) : SatisfiesBy s p h O
```

* **With the key definitions unfolded** (`Fp A g F` abbreviates `IsFootprint A g F`, `Acc` abbreviates `Accepts`, `REW` abbreviates `RecoversEveryWitness`; all are quoted under *Model*):

```lean
∀ s, (∀ A g F, s A g = some F → IsFootprint A g F) → ∀ cfg, cfg.leakCheck = true →
  ∀ p h O, Accepts cfg s p h O → (cfg.checkUnannot = false → UnannotConfinedAux s false p h O) →
  SatisfiesBy s p h O
-- where UnannotConfinedAux s u (u = "running inside an unannotated callee") requires
--   read a / write a v :  u = true → a ∈ O ∧ (h a).isSome = true
--   call P _ body      :  ∀ F, s P (h.restrict O) = some F → UnannotConfinedAux s false body h F
--   unannot body       :  UnannotConfinedAux s true body h O      (seq: both parts; skip: True)
```

* **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness | Counterexample (all other hypotheses hold, conclusion fails) |
  | --- | --- | --- | --- |
  | `hs : StrategySound s` | As in R1. | `tight` | `unsound_strategy_accepts_contract_violating_run` |
  | `hleak : cfg.leakCheck = true` | As in R1. | `tight` | `noLeakCheck_accepts_leaky_post` |
  | `hacc : Accepts cfg s p h O` | The premise. | `tight` | `read_unowned_rejected_and_unsatisfied` |
  | `hconf : cfg.checkUnannot = false → UnannotConfined s p h O` | The confinement assumption on uninstrumented code. Guarded: when cfg.checkUnannot = true the monitor checks those accesses itself and nothing is assumed. UnannotConfined constrains only access targets along the concrete run (not satisfaction of any contract). | `tight` | `trusted_unannot_write_outside_footprint_accepted` |

* **Depth:** `substantive`.
* **Non-vacuity witness:** fpAtom, configuration (leak check on, unannotated callees trusted), progMixed = call (owned 0) (owned 0) (unannot (seq (write 0 5) (call (owned 0) (pointsTo 0 5) (read 0)))) from the one-byte heap: accepted, and the unannotated helper's unchecked store stays in the callee's footprint [0] while its annotated callee is monitored. (`accepts_imp_satisfiesBy_of_unannotConfined_nonvacuous`)
* **Related proved statements:** `trusted_monitor_checks_nested_annotated_call`, `trusted_unannot_read_outside_footprint_accepted_heap_unchanged`.
* **Prior art:** [S6] Miri prototype, JoJoDeveloping/miri@a33a3c07; [S10] Agten, Jacobs, Piessens (POPL 2015); [S8] Gradual verification (VMCAI 2018, OOPSLA 2020, POPL 2024); [S1] Fulminate (POPL 2025); [S2] CN (POPL 2023) (full records under **Evidence**).
* **Design question:** informs part (c), unannotated code: what the monitor assumes about it (package question at the top of **Findings**).
* `Basis: execution (Lean kernel check)` for the theorem.
* `Basis: derived (modeling bridge)` for any reading of this result about a real system: see B3, B5 above, which state the reasoning and the gaps.
* **Non-claims:** listed under **Boundaries** (*R1-trusted-soundness-under-unannot-confinement*).

#### R1-frame-property: Frame property of contract-satisfying runs

* **Lean:** `Toy.Monitor.satisfies_frame` (`lean/ToyMonitor/Results.lean`); kind `theorem`; tier `T0`; depth `shallow`.
* **Plain claim:** If a run satisfies its contracts in a frame owning exactly the addresses O, it changes no byte outside O; in particular bytes not transferred to a callee are unchanged when the callee returns.
* **Tier `T0`:** The frame property of separation-logic triples (standard), restated for this toy semantics.
* **Lean statement:**

```lean
-- lean/ToyMonitor/Results.lean:307-311
/-- **Frame property.** If a run satisfies its contracts in a frame owning `O`, the run
changes no byte outside `O`. In particular (applied to a callee) bytes not transferred
to a callee are unchanged when it returns. -/
theorem satisfies_frame :
    ∀ (p : Prog) (h : Heap) (O : List Addr), Satisfies p h O → ∀ a, a ∉ O → exec p h a = h a
```

* **With the key definitions unfolded** (`Fp A g F` abbreviates `IsFootprint A g F`, `Acc` abbreviates `Accepts`, `REW` abbreviates `RecoversEveryWitness`; all are quoted under *Model*):

```lean
∀ p h O, Satisfies p h O → ∀ a, a ∉ O → exec p h a = h a
```

* **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness | Counterexample (all other hypotheses hold, conclusion fails) |
  | --- | --- | --- | --- |
  | `Satisfies p h O` | Only contract-respecting runs are confined to their frame. | `tight` | `write_outside_frame_changes_byte` |
  | `a ∉ O` | Bytes in O may change. | `tight` | `satisfies_frame_needs_not_mem` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** Satisfies progNV hOne [0] and 1 ∉ [0]. (`satisfies_frame_nonvacuous`)
* **Prior art:** [S4] O'Hearn, Yang, Reynolds (POPL 2004); [S7] Ishtiaq and O'Hearn (POPL 2001), Reynolds (LICS 2002) (full records under **Evidence**).
* **Design question:** informs part (a), soundness: when acceptance implies that every contract was satisfied (package question at the top of **Findings**).
* `Basis: execution (Lean kernel check)` for the theorem.
* No claim about a real system is made for this result.
* **Non-claims:** listed under **Boundaries** (*R1-frame-property*).

#### R1-footprint-witnesses-separating-conjunction: A footprint witnesses `pre ∗ frame`

* **Lean:** `Toy.Monitor.restrict_witnesses_sep` (`lean/ToyMonitor/Results.lean`); kind `theorem`; tier `T0`; depth `definitional`.
* **Plain claim:** If the restriction of a fragment g to an address list F satisfies A, then g satisfies A * R for the frame R holding of exactly g.remove F, with the split exposed (A-part = g.restrict F, frame = g.remove F).
* **Tier `T0`:** Definitional unfolding of the separating conjunction.
* **Lean statement:**

```lean
-- lean/ToyMonitor/Results.lean:334-341
/-- **Footprints witness the separating conjunction.** If the restriction of `g` to `F`
satisfies `A`, then `g` satisfies `A ∗ R` where `R` holds of exactly the frame
`g.remove F`, with the split exposed: the `A`-part is `g.restrict F` and the frame part
is `g.remove F`. (Applied to the caller's fragment and the monitor's footprint `F`, which
R1 shows satisfies the precondition there, this is the witness for `pre ∗ frame`.) -/
theorem restrict_witnesses_sep (A : Assn) (g : Heap) (F : List Addr)
    (hA : sat A (g.restrict F)) :
    SepP (fun g₁ => g₁ = g.restrict F ∧ sat A g₁) (fun g₂ => g₂ = g.remove F) g
```

* **With the key definitions unfolded** (`Fp A g F` abbreviates `IsFootprint A g F`, `Acc` abbreviates `Accepts`, `REW` abbreviates `RecoversEveryWitness`; all are quoted under *Model*):

```lean
∀ (A : Assn) (g : Heap) (F : List Addr), sat A (g.restrict F) →
  ∃ g₁ g₂, (∀ a, g₁ a = none ∨ g₂ a = none) ∧ (∀ a, g a = Heap.union g₁ g₂ a) ∧
    (g₁ = g.restrict F ∧ sat A g₁) ∧ g₂ = g.remove F
```

* **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness | Counterexample (all other hypotheses hold, conclusion fails) |
  | --- | --- | --- | --- |
  | `hA : sat A (g.restrict F)` | The restricted part must satisfy A. | `tight` | `restrict_witnesses_sep_needs_sat` |

* **Depth:** `definitional`.
* **Non-vacuity witness:** sat (owned 0) (hTwo.restrict [0]). (`restrict_witnesses_sep_nonvacuous`)
* **Related proved statements:** `restrict_witnesses_sep_allows_unallocated_addrs`.
* **Prior art:** [S4] O'Hearn, Yang, Reynolds (POPL 2004) (full records under **Evidence**).
* **Design question:** informs part (a), soundness: when acceptance implies that every contract was satisfied (package question at the top of **Findings**).
* `Basis: execution (Lean kernel check)` for the theorem.
* No claim about a real system is made for this result.
* **Non-claims:** listed under **Boundaries** (*R1-footprint-witnesses-separating-conjunction*).

#### R2-disjPrecise-implies-precise: Disjunction-precise assertions are precise

* **Lean:** `Toy.Monitor.precise_of_disjPrecise` (`lean/ToyMonitor/Results.lean`); kind `theorem`; tier `T0`; depth `shallow`.
* **Plain claim:** Every disjunction-precise assertion (every disjunction occurring in it is precise) is precise in the sense of O'Hearn-Yang-Reynolds.
* **Tier `T0`:** Re-derivation of a known result: cell assertions and pure assertions (which hold only of the empty fragment in this model) are precise, and precision is closed under separating conjunction; the closure lemma is mechanized for separation algebras in Isabelle (Archive of Formal Proofs entry Separata, lemma precise_sep_conj). DisjPrecise puts the precision of each disjunction into its definition, so this statement is that closure property restated for this assertion language.
* **Lean statement:**

```lean
-- lean/ToyMonitor/Results.lean:379-380
/-- Disjunction-precise contracts are precise (precision is closed under `∗`). -/
theorem precise_of_disjPrecise (A : Assn) (hA : DisjPrecise A) : Precise A
```

* **With the key definitions unfolded** (`Fp A g F` abbreviates `IsFootprint A g F`, `Acc` abbreviates `Accepts`, `REW` abbreviates `RecoversEveryWitness`; all are quoted under *Model*):

```lean
∀ A, DisjPrecise A →
  ∀ g g₁ g₂, Heap.Sub g₁ g → Heap.Sub g₂ g → sat A g₁ → sat A g₂ → g₁ = g₂
-- DisjPrecise: cell/pure ↦ True; sep A B ↦ DisjPrecise A ∧ DisjPrecise B;
--              or A B ↦ Precise (or A B) ∧ DisjPrecise A ∧ DisjPrecise B
```

* **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness | Counterexample (all other hypotheses hold, conclusion fails) |
  | --- | --- | --- | --- |
  | `hA : DisjPrecise A` | Imprecise disjunctions can make the whole assertion imprecise; the hypothesis rules them out. | `tight` | `not_precise_C` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** DisjPrecise (pointsTo 0 0 or pointsTo 0 1). (`precise_of_disjPrecise_nonvacuous`)
* **Prior art:** [S4] O'Hearn, Yang, Reynolds (POPL 2004); [S11] Klein, Kolanski, Boyton (ITP 2012); [S12] Separata (Archive of Formal Proofs, 2016) (full records under **Evidence**).
* **Design question:** informs part (b), completeness: when every satisfying run is accepted (package question at the top of **Findings**).
* `Basis: execution (Lean kernel check)` for the theorem.
* No claim about a real system is made for this result.
* **Non-claims:** listed under **Boundaries** (*R2-disjPrecise-implies-precise*).

#### R2a-greedy-recovers-every-witness-for-disjPrecise: Greedy recovers every witness of disjunction-precise contracts

* **Lean:** `Toy.Monitor.fpGreedy_recoversEveryWitness_of_disjPrecise` (`lean/ToyMonitor/Results.lean`); kind `theorem`; tier `T1`; depth `substantive`.
* **Plain claim:** For every disjunction-precise assertion A, whenever some sub-fragment g' of g satisfies A, the greedy strategy returns a footprint of allocated addresses of g that carves out exactly g'.
* **Tier `T1`:** Fulminate observes that CN's restrictions (outputs computable from inputs, if-then-else with guarded clauses instead of disjunction, similar to RefinedC) let runtime checking determine without backtracking which clause applies; this states the corresponding witness-recovery property of a committed-choice evaluator for the semantic class 'every disjunction precise'. (Novelty search: see **Evidence**.)
* **Lean statement:**

```lean
-- lean/ToyMonitor/Results.lean:397-401
/-- **R2a.** The greedy strategy recovers every witness of every disjunction-precise
contract: whenever a sub-fragment of `g` satisfies `A`, the greedy footprint carves out
exactly that sub-fragment. -/
theorem fpGreedy_recoversEveryWitness_of_disjPrecise (A : Assn) (hA : DisjPrecise A) :
    RecoversEveryWitness fpGreedy A
```

* **With the key definitions unfolded** (`Fp A g F` abbreviates `IsFootprint A g F`, `Acc` abbreviates `Accepts`, `REW` abbreviates `RecoversEveryWitness`; all are quoted under *Model*):

```lean
∀ A, DisjPrecise A → ∀ g g', Heap.Sub g' g → sat A g' →
  ∃ F, fpGreedy A g = some F ∧ (∀ a ∈ F, (g a).isSome = true) ∧ g.restrict F = g'
```

* **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness | Counterexample (all other hypotheses hold, conclusion fails) |
  | --- | --- | --- | --- |
  | `hA : DisjPrecise A` | Committed left-first choice can pick a disjunct whose footprint blocks the rest of the assertion or the intended witness. | `tight` | `not_recoversEveryWitness_fpGreedy_C`, `fpGreedy_rejects_satisfying_run_precise_not_disjPrecise` |

* **Depth:** `substantive`.
* **Non-vacuity witness:** A = pointsTo 0 0 or pointsTo 0 1, g = g' = the one-byte heap holding 0. (`fpGreedy_recoversEveryWitness_of_disjPrecise_nonvacuous`)
* **Related proved statements:** `fpGreedy_recoversEveryWitness_CFlip_not_disjPrecise`.
* **Prior art:** [S1] Fulminate (POPL 2025); [S2] CN (POPL 2023); [S3] Nguyen, Kuncak, Chin (VMCAI 2008); [S4] O'Hearn, Yang, Reynolds (POPL 2004); [S13] RefinedC (PLDI 2021) (full records under **Evidence**).
* **Design question:** informs part (b), completeness: when every satisfying run is accepted (package question at the top of **Findings**).
* `Basis: execution (Lean kernel check)` for the theorem.
* `Basis: derived (modeling bridge)` for any reading of this result about a real system: see B2 above, which states the reasoning and the gaps.
* **Non-claims:** listed under **Boundaries** (*R2a-greedy-recovers-every-witness-for-disjPrecise*).

#### R2b-search-recovers-every-witness-for-precise: Search recovers every witness of precise contracts

* **Lean:** `Toy.Monitor.fpSearch_recoversEveryWitness_of_precise` (`lean/ToyMonitor/Results.lean`); kind `theorem`; tier `T1`; depth `shallow`.
* **Plain claim:** For every precise assertion A, whenever some sub-fragment g' of g satisfies A, the backtracking strategy returns a footprint of allocated addresses of g that carves out exactly g'.
* **Tier `T1`:** Precision means at most one witness, so any exhaustive search that returns some witness returns the witness. (Novelty search: see **Evidence**.)
* **Lean statement:**

```lean
-- lean/ToyMonitor/Results.lean:448-451
/-- **R2b.** The backtracking strategy recovers every witness of every precise
contract. -/
theorem fpSearch_recoversEveryWitness_of_precise (A : Assn) (hA : Precise A) :
    RecoversEveryWitness fpSearch A
```

* **With the key definitions unfolded** (`Fp A g F` abbreviates `IsFootprint A g F`, `Acc` abbreviates `Accepts`, `REW` abbreviates `RecoversEveryWitness`; all are quoted under *Model*):

```lean
∀ A, Precise A → ∀ g g', Heap.Sub g' g → sat A g' →
  ∃ F, (fpAll A g).head? = some F ∧ (∀ a ∈ F, (g a).isSome = true) ∧ g.restrict F = g'
```

* **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness | Counterexample (all other hypotheses hold, conclusion fails) |
  | --- | --- | --- | --- |
  | `hA : Precise A` | With two witnesses a single answer cannot carve out both. | `tight` | `not_recoversEveryWitness_fpSearch_C` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** A = C' (precise, not disjunction-precise), g = g' = hTwo. (`fpSearch_recoversEveryWitness_of_precise_nonvacuous`)
* **Related proved statements:** `fpSearch_existsFootprintComplete`, `precise_of_recoversEveryWitness`.
* **Prior art:** [S4] O'Hearn, Yang, Reynolds (POPL 2004); [S3] Nguyen, Kuncak, Chin (VMCAI 2008) (full records under **Evidence**).
* **Design question:** informs part (b), completeness: when every satisfying run is accepted (package question at the top of **Findings**).
* `Basis: execution (Lean kernel check)` for the theorem.
* No claim about a real system is made for this result.
* **Non-claims:** listed under **Boundaries** (*R2b-search-recovers-every-witness-for-precise*).

#### R2-recovers-every-witness-implies-precise: Witness recovery forces precision

* **Lean:** `Toy.Monitor.precise_of_recoversEveryWitness` (`lean/ToyMonitor/Examples.lean`); kind `theorem`; tier `T0`; depth `definitional`.
* **Plain claim:** If some strategy s recovers every witness of an assertion A (its single answer carves out whichever sub-fragment satisfies A), then A is precise.
* **Tier `T0`:** Immediate from the definitions: RecoversEveryWitness asks one answer s A g, which cannot depend on the witness, to carve out every witness, so it builds uniqueness in.
* **Lean statement:**

```lean
-- lean/ToyMonitor/Examples.lean:313-315
/-- Witness recovery (`RecoversEveryWitness`) is only possible for precise contracts
(whatever the strategy): the single answer `s A g` must carve out every witness. -/
theorem precise_of_recoversEveryWitness (s : Strategy) (A : Assn) (hc : RecoversEveryWitness s A) : Precise A
```

* **With the key definitions unfolded** (`Fp A g F` abbreviates `IsFootprint A g F`, `Acc` abbreviates `Accepts`, `REW` abbreviates `RecoversEveryWitness`; all are quoted under *Model*):

```lean
∀ s A, RecoversEveryWitness s A → ∀ g g₁ g₂, Heap.Sub g₁ g → Heap.Sub g₂ g → sat A g₁ → sat A g₂ → g₁ = g₂
```

* **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness | Counterexample (all other hypotheses hold, conclusion fails) |
  | --- | --- | --- | --- |
  | `hc : RecoversEveryWitness s A` | The premise. | `tight` | `not_precise_C` |

* **Depth:** `definitional`.
* **Non-vacuity witness:** RecoversEveryWitness fpAtom (owned 0). (`precise_of_recoversEveryWitness_nonvacuous`)
* **Related proved statements:** `accepts_fpGreedy_call_C_C_skip_of_satisfies`, `existsFootprintComplete_not_imp_precise`.
* **Prior art:** [S4] O'Hearn, Yang, Reynolds (POPL 2004) (full records under **Evidence**).
* **Design question:** informs part (b), completeness: when every satisfying run is accepted (package question at the top of **Findings**).
* `Basis: execution (Lean kernel check)` for the theorem.
* No claim about a real system is made for this result.
* **Non-claims:** listed under **Boundaries** (*R2-recovers-every-witness-implies-precise*).

#### R2c-satisfies-implies-satisfiesBy-for-witness-recovering-strategies: Witness recovery turns angelic satisfaction into strategy satisfaction

* **Lean:** `Toy.Monitor.satisfies_imp_satisfiesBy_of_recoversEveryWitness` (`lean/ToyMonitor/Results.lean`); kind `theorem`; tier `T1`; depth `shallow`.
* **Plain claim:** If a strategy recovers every witness of every contract of the program, then a run that satisfies its contracts with some (angelically chosen) footprints also satisfies them with the strategy's footprints.
* **Tier `T1`:** Recorded search (2026-11-20): web searches for runtime checking of separation logic with ownership monitors, completeness, precise assertions, disjunction, online footprint choice and backtracking, gradual verification, and mechanized separation algebras; reading of Fulminate (full text), Nguyen-Kuncak-Chin (full text), O'Hearn-Yang-Reynolds (full text), compiler-team #942 (full text) and the Miri prototype source. No source examined states this result in this form or mechanizes it; the ideas are standard, hence T1 rather than T3.
* **Lean statement:**

```lean
-- lean/ToyMonitor/Results.lean:461-467
/-- **R2c.** If the strategy recovers every witness of every contract of the program, a run that
satisfies its contracts (angelic footprints) satisfies them with the strategy's
footprints. -/
theorem satisfies_imp_satisfiesBy_of_recoversEveryWitness (s : Strategy)
    (p : Prog) (h : Heap) (O : List Addr)
    (hc : ∀ A ∈ p.contracts, RecoversEveryWitness s A) (hsat : Satisfies p h O) :
    SatisfiesBy s p h O
```

* **With the key definitions unfolded** (`Fp A g F` abbreviates `IsFootprint A g F`, `Acc` abbreviates `Accepts`, `REW` abbreviates `RecoversEveryWitness`; all are quoted under *Model*):

```lean
∀ s p h O, (∀ A ∈ p.contracts, RecoversEveryWitness s A) → Satisfies p h O → SatisfiesBy s p h O
-- p.contracts lists every pre- and postcondition occurring in p, including nested calls;
-- Satisfies is SatisfiesBy with the footprint at each call chosen existentially (any F with
-- Fp P (h.restrict O) F, Satisfies body h F, and Fp Q ((exec body h).restrict F) F).
```

* **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness | Counterexample (all other hypotheses hold, conclusion fails) |
  | --- | --- | --- | --- |
  | `hc : ∀ A ∈ p.contracts, RecoversEveryWitness s A` | Every footprint choice must be the forced one. | `tight` | `fpGreedy_rejects_satisfying_run_imprecise_contract` |
  | `hsat : Satisfies p h O` | The premise. | `tight` | `read_unowned_rejected_and_unsatisfied` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** fpAtom, progNV (atomic contracts, whose witnesses fpAtom recovers), Satisfies progNV hOne [0]. (`satisfies_imp_satisfiesBy_of_recoversEveryWitness_nonvacuous`)
* **Related proved statements:** `accepts_fpGreedy_call_C_C_skip_of_satisfies`.
* **Prior art:** [S1] Fulminate (POPL 2025); [S2] CN (POPL 2023) (full records under **Evidence**).
* **Design question:** informs part (b), completeness: when every satisfying run is accepted (package question at the top of **Findings**).
* `Basis: execution (Lean kernel check)` for the theorem.
* `Basis: derived (modeling bridge)` for any reading of this result about a real system: see B1 above, which states the reasoning and the gaps.
* **Non-claims:** listed under **Boundaries** (*R2c-satisfies-implies-satisfiesBy-for-witness-recovering-strategies*).

#### R2-greedy-monitor-complete-for-disjPrecise-contracts: Greedy monitor completeness for disjunction-precise contracts

* **Lean:** `Toy.Monitor.accepts_fpGreedy_of_satisfies_of_disjPrecise` (`lean/ToyMonitor/Results.lean`); kind `theorem`; tier `T1`; depth `shallow`.
* **Plain claim:** If every contract of the program is disjunction-precise, the greedy monitor, under any configuration, accepts every run that satisfies its contracts.
* **Tier `T1`:** Composition of R2a, R2c and R1prime. (Novelty search: see **Evidence**.)
* **Lean statement:**

```lean
-- lean/ToyMonitor/Results.lean:535-541
/-- **R2 (greedy completeness).** If every contract of the program is
disjunction-precise, the greedy monitor (under any configuration) accepts every run that
satisfies its contracts. -/
theorem accepts_fpGreedy_of_satisfies_of_disjPrecise (cfg : MonCfg)
    (p : Prog) (h : Heap) (O : List Addr)
    (hdp : ∀ A ∈ p.contracts, DisjPrecise A) (hsat : Satisfies p h O) :
    Accepts cfg fpGreedy p h O
```

* **With the key definitions unfolded** (`Fp A g F` abbreviates `IsFootprint A g F`, `Acc` abbreviates `Accepts`, `REW` abbreviates `RecoversEveryWitness`; all are quoted under *Model*):

```lean
∀ cfg p h O, (∀ A ∈ p.contracts, DisjPrecise A) → Satisfies p h O →
  (monitorAux cfg fpGreedy true p h (initOwn O) 0).isSome = true
```

* **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness | Counterexample (all other hypotheses hold, conclusion fails) |
  | --- | --- | --- | --- |
  | `hdp : ∀ A ∈ p.contracts, DisjPrecise A` | Greedy committed choice must not be able to pick a wrong footprint. | `tight` | `fpGreedy_rejects_satisfying_run_imprecise_contract`, `fpGreedy_rejects_satisfying_run_precise_not_disjPrecise` |
  | `hsat : Satisfies p h O` | The premise. | `tight` | `read_unowned_rejected_and_unsatisfied` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** progOr = call (pointsTo 0 0 or pointsTo 0 1) (pointsTo 0 1) (write 0 1) from the one-byte heap holding 0. (`accepts_fpGreedy_of_satisfies_of_disjPrecise_nonvacuous`)
* **Related proved statements:** `accepts_fpGreedy_call_C_C_skip_of_satisfies`.
* **Prior art:** [S1] Fulminate (POPL 2025); [S2] CN (POPL 2023); [S4] O'Hearn, Yang, Reynolds (POPL 2004); [S13] RefinedC (PLDI 2021) (full records under **Evidence**).
* **Design question:** informs part (b), completeness: when every satisfying run is accepted (package question at the top of **Findings**).
* `Basis: execution (Lean kernel check)` for the theorem.
* `Basis: derived (modeling bridge)` for any reading of this result about a real system: see B1, B2 above, which state the reasoning and the gaps.
* **Non-claims:** listed under **Boundaries** (*R2-greedy-monitor-complete-for-disjPrecise-contracts*).

#### R2-search-monitor-complete-for-precise-contracts: Search monitor completeness for precise contracts

* **Lean:** `Toy.Monitor.accepts_fpSearch_of_satisfies_of_precise` (`lean/ToyMonitor/Results.lean`); kind `theorem`; tier `T1`; depth `shallow`.
* **Plain claim:** If every contract of the program is precise, the backtracking monitor, under any configuration, accepts every run that satisfies its contracts.
* **Tier `T1`:** Composition of R2b, R2c and R1prime. (Novelty search: see **Evidence**.)
* **Lean statement:**

```lean
-- lean/ToyMonitor/Results.lean:546-552
/-- **R2 (search completeness).** If every contract of the program is precise, the
backtracking monitor (under any configuration) accepts every run that satisfies its
contracts. -/
theorem accepts_fpSearch_of_satisfies_of_precise (cfg : MonCfg)
    (p : Prog) (h : Heap) (O : List Addr)
    (hp : ∀ A ∈ p.contracts, Precise A) (hsat : Satisfies p h O) :
    Accepts cfg fpSearch p h O
```

* **With the key definitions unfolded** (`Fp A g F` abbreviates `IsFootprint A g F`, `Acc` abbreviates `Accepts`, `REW` abbreviates `RecoversEveryWitness`; all are quoted under *Model*):

```lean
∀ cfg p h O, (∀ A ∈ p.contracts, Precise A) → Satisfies p h O →
  (monitorAux cfg fpSearch true p h (initOwn O) 0).isSome = true
```

* **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness | Counterexample (all other hypotheses hold, conclusion fails) |
  | --- | --- | --- | --- |
  | `hp : ∀ A ∈ p.contracts, Precise A` | With an imprecise contract the single online choice may be wrong. | `tight` | `fpSearch_rejects_satisfying_run_imprecise_contract` |
  | `hsat : Satisfies p h O` | The premise. | `tight` | `read_unowned_rejected_and_unsatisfied` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** runP = call C' C' skip from hTwo owning {0, 1}. (`accepts_fpSearch_of_satisfies_of_precise_nonvacuous`)
* **Related proved statements:** `accepts_strict_fpSearch_iff_satisfies_call_C_C_skip`.
* **Prior art:** [S4] O'Hearn, Yang, Reynolds (POPL 2004); [S3] Nguyen, Kuncak, Chin (VMCAI 2008) (full records under **Evidence**).
* **Design question:** informs part (b), completeness: when every satisfying run is accepted (package question at the top of **Findings**).
* `Basis: execution (Lean kernel check)` for the theorem.
* `Basis: derived (modeling bridge)` for any reading of this result about a real system: see B1 above, which states the reasoning and the gaps.
* **Non-claims:** listed under **Boundaries** (*R2-search-monitor-complete-for-precise-contracts*).

#### R2-greedy-characterization: Strict greedy monitor: acceptance iff satisfaction (disjunction-precise contracts)

* **Lean:** `Toy.Monitor.accepts_strict_fpGreedy_iff_satisfies_of_disjPrecise` (`lean/ToyMonitor/Results.lean`); kind `characterization`; tier `T1`; depth `shallow`.
* **Plain claim:** For programs whose contracts are all disjunction-precise, the strict greedy monitor (leak check on, unannotated callees checked) accepts a run if and only if the run satisfies its contracts.
* **Tier `T1`:** Combines soundness (R1, R1a) and completeness (R2a, R2c, R1prime). (Novelty search: see **Evidence**.)
* **Lean statement:**

```lean
-- lean/ToyMonitor/Results.lean:557-562
/-- **R2 (characterization, greedy).** For programs whose contracts are all
disjunction-precise, the strict greedy monitor accepts a run iff the run satisfies its
contracts. -/
theorem accepts_strict_fpGreedy_iff_satisfies_of_disjPrecise
    (p : Prog) (h : Heap) (O : List Addr) (hdp : ∀ A ∈ p.contracts, DisjPrecise A) :
    Accepts MonCfg.strict fpGreedy p h O ↔ Satisfies p h O
```

* **With the key definitions unfolded** (`Fp A g F` abbreviates `IsFootprint A g F`, `Acc` abbreviates `Accepts`, `REW` abbreviates `RecoversEveryWitness`; all are quoted under *Model*):

```lean
∀ p h O, (∀ A ∈ p.contracts, DisjPrecise A) →
  ((monitorAux ⟨true, true⟩ fpGreedy true p h (initOwn O) 0).isSome = true ↔ Satisfies p h O)
-- MonCfg.strict = ⟨leakCheck := true, checkUnannot := true⟩
```

* **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness | Counterexample (all other hypotheses hold, conclusion fails) |
  | --- | --- | --- | --- |
  | `hdp : ∀ A ∈ p.contracts, DisjPrecise A` | Needed only for the 'if' direction; 'only if' holds for all contracts. | `tight` | `fpGreedy_rejects_satisfying_run_imprecise_contract`, `fpGreedy_rejects_satisfying_run_precise_not_disjPrecise` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** progOr (disjunctive precondition) from the one-byte heap. (`accepts_fpGreedy_of_satisfies_of_disjPrecise_nonvacuous`)
* **Related proved statements:** `accepts_fpGreedy_call_C_C_skip_of_satisfies`.
* **Prior art:** [S1] Fulminate (POPL 2025); [S2] CN (POPL 2023); [S3] Nguyen, Kuncak, Chin (VMCAI 2008); [S4] O'Hearn, Yang, Reynolds (POPL 2004) (full records under **Evidence**).
* **Design question:** informs part (b), completeness: when every satisfying run is accepted (package question at the top of **Findings**).
* `Basis: execution (Lean kernel check)` for the theorem.
* `Basis: derived (modeling bridge)` for any reading of this result about a real system: see B1, B2 above, which state the reasoning and the gaps.
* **Non-claims:** listed under **Boundaries** (*R2-greedy-characterization*).

#### R2-search-characterization: Strict search monitor: acceptance iff satisfaction (precise contracts)

* **Lean:** `Toy.Monitor.accepts_strict_fpSearch_iff_satisfies_of_precise` (`lean/ToyMonitor/Results.lean`); kind `characterization`; tier `T1`; depth `shallow`.
* **Plain claim:** For programs whose contracts are all precise, the strict backtracking monitor accepts a run if and only if the run satisfies its contracts.
* **Tier `T1`:** Combines R1, R1b, R2b, R2c, R1prime. (Novelty search: see **Evidence**.)
* **Lean statement:**

```lean
-- lean/ToyMonitor/Results.lean:568-572
/-- **R2 (characterization, search).** For programs whose contracts are all precise,
the strict backtracking monitor accepts a run iff the run satisfies its contracts. -/
theorem accepts_strict_fpSearch_iff_satisfies_of_precise
    (p : Prog) (h : Heap) (O : List Addr) (hp : ∀ A ∈ p.contracts, Precise A) :
    Accepts MonCfg.strict fpSearch p h O ↔ Satisfies p h O
```

* **With the key definitions unfolded** (`Fp A g F` abbreviates `IsFootprint A g F`, `Acc` abbreviates `Accepts`, `REW` abbreviates `RecoversEveryWitness`; all are quoted under *Model*):

```lean
∀ p h O, (∀ A ∈ p.contracts, Precise A) →
  ((monitorAux ⟨true, true⟩ fpSearch true p h (initOwn O) 0).isSome = true ↔ Satisfies p h O)
```

* **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness | Counterexample (all other hypotheses hold, conclusion fails) |
  | --- | --- | --- | --- |
  | `hp : ∀ A ∈ p.contracts, Precise A` | Needed only for the 'if' direction. | `tight` | `fpSearch_rejects_satisfying_run_imprecise_contract` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** runP from hTwo. (`accepts_fpSearch_of_satisfies_of_precise_nonvacuous`)
* **Related proved statements:** `accepts_strict_fpSearch_iff_satisfies_call_C_C_skip`.
* **Prior art:** [S4] O'Hearn, Yang, Reynolds (POPL 2004); [S3] Nguyen, Kuncak, Chin (VMCAI 2008) (full records under **Evidence**).
* **Design question:** informs part (b), completeness: when every satisfying run is accepted (package question at the top of **Findings**).
* `Basis: execution (Lean kernel check)` for the theorem.
* `Basis: derived (modeling bridge)` for any reading of this result about a real system: see B1 above, which states the reasoning and the gaps.
* **Non-claims:** listed under **Boundaries** (*R2-search-characterization*).

#### R2-owned0-or-owned1-defeats-every-sound-online-strategy: Impossibility: `owned 0 ∨ owned 1` defeats every sound online strategy

* **Lean:** `Toy.Monitor.owned0_or_owned1_no_sound_strategy_accepts_both` (`lean/ToyMonitor/Results.lean`); kind `impossibility`; tier `T1`; depth `shallow`.
* **Plain claim:** For the imprecise contract owned 0 or owned 1, the run whose callee reads byte 0 and the run whose callee reads byte 1 both satisfy their contracts from the same heap and ownership, yet no sound footprint strategy - under any monitor configuration - gets both accepted, because the footprint is chosen at call time from the contract and the caller's fragment alone.
* **Tier `T1`:** Folklore made precise: imprecise assertions let different splittings be chosen at different times (O'Hearn-Yang-Reynolds Sec. 6), and evaluators must undo choices for disjunction (Nguyen et al.). (Novelty search: see **Evidence**.)
* **Lean statement:**

```lean
-- lean/ToyMonitor/Results.lean:588-596
/-- **R2 (impossibility).** For the imprecise contract `owned 0 ∨ owned 1`: the run
whose callee reads byte `0` and the run whose callee reads byte `1` both satisfy their
contracts (from the same heap and ownership), yet no sound strategy — under any monitor
configuration — gets both accepted. The strategy must choose the footprint at call time,
before the callee's accesses are seen. -/
theorem owned0_or_owned1_no_sound_strategy_accepts_both :
    Satisfies runL hTwo [0, 1] ∧ Satisfies runR hTwo [0, 1] ∧
      ∀ (cfg : MonCfg) (s : Strategy), StrategySound s →
        ¬ (Accepts cfg s runL hTwo [0, 1] ∧ Accepts cfg s runR hTwo [0, 1])
```

* **With the key definitions unfolded** (`Fp A g F` abbreviates `IsFootprint A g F`, `Acc` abbreviates `Accepts`, `REW` abbreviates `RecoversEveryWitness`; all are quoted under *Model*):

```lean
-- C = or (owned 0) (owned 1);  runL = call C C (read 0);  runR = call C C (read 1);
-- hTwo = {0 ↦ 0, 1 ↦ 0} (all other addresses unallocated)
Satisfies runL hTwo [0, 1] ∧ Satisfies runR hTwo [0, 1] ∧
  ∀ cfg s, (∀ A g F, s A g = some F → IsFootprint A g F) →
    ¬ (Accepts cfg s runL hTwo [0, 1] ∧ Accepts cfg s runR hTwo [0, 1])
```

* **Hypothesis ledger:**

  | Hypothesis | Why it is needed | Tightness | Counterexample (all other hypotheses hold, conclusion fails) |
  | --- | --- | --- | --- |
  | `StrategySound s` | An unsound strategy can transfer both bytes and accept both runs. | `tight` | `owned0_or_owned1_unsound_strategy_accepts_both` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** fpGreedy is a sound strategy that handles disjunction (it returns [0] for owned 0 or owned 1 here); both runs satisfy their contracts. (`owned0_or_owned1_no_sound_strategy_accepts_both_nonvacuous`)
* **Positive control:** `owned0_or_owned1_each_run_accepted_by_some_strategy`: each of the two runs is accepted by some sound strategy (`fpGreedy` accepts `runL`, `fpGreedyR` accepts `runR`, both under the strict configuration and with their footprints satisfying the contracts), so the conclusion fails once the strategy may depend on the run.
* **Related proved statements:** `accepts_fpGreedy_call_C_C_skip_of_satisfies`, `precise_of_recoversEveryWitness`.
* **Prior art:** [S4] O'Hearn, Yang, Reynolds (POPL 2004); [S3] Nguyen, Kuncak, Chin (VMCAI 2008); [S1] Fulminate (POPL 2025); [S2] CN (POPL 2023); [S13] RefinedC (PLDI 2021) (full records under **Evidence**).
* **Design question:** informs part (b), completeness: when every satisfying run is accepted (package question at the top of **Findings**).
* `Basis: execution (Lean kernel check)` for the theorem.
* `Basis: derived (modeling bridge)` for any reading of this result about a real system: see B4 above, which states the reasoning and the gaps.
* **Non-claims:** listed under **Boundaries** (*R2-owned0-or-owned1-defeats-every-sound-online-strategy*).

#### CE-precise-not-disjPrecise-greedy-false-alarm: Counterexample: precise but not disjunction-precise contract, greedy false alarm

* **Lean:** `Toy.Monitor.fpGreedy_rejects_satisfying_run_precise_not_disjPrecise` (`lean/ToyMonitor/Results.lean`); kind `counterexample`; tier `T1`; depth `shallow`.
* **Plain claim:** The contract C' = ((owned 0 * owned 1) or owned 0) * owned 1 is precise but not disjunction-precise; greedy does not recover its witness, and the strict greedy monitor rejects the run call C' C' skip from two owned bytes although the run satisfies its contracts, while the backtracking monitor accepts it.
* **Tier `T1`:** Committed-choice evaluation without backtracking is known to be incomplete in general; this pins the gap between Precise and DisjPrecise with a concrete contract. (Novelty search: see **Evidence**.)
* **Lean statement:**

```lean
-- lean/ToyMonitor/Results.lean:669-676
/-- **Counterexample (precise but not disjunction-precise, greedy).** `C'` is precise but
has an imprecise inner disjunction. Greedy does not recover every witness of it, and the greedy monitor
rejects a run that satisfies its contracts, while the backtracking monitor accepts it.
So `DisjPrecise` in the greedy results cannot be weakened to `Precise`. -/
theorem fpGreedy_rejects_satisfying_run_precise_not_disjPrecise :
    Precise C' ∧ ¬ DisjPrecise C' ∧ ¬ RecoversEveryWitness fpGreedy C' ∧
      Satisfies runP hTwo [0, 1] ∧ ¬ Accepts MonCfg.strict fpGreedy runP hTwo [0, 1] ∧
      Accepts MonCfg.strict fpSearch runP hTwo [0, 1]
```

* **With the key definitions unfolded** (`Fp A g F` abbreviates `IsFootprint A g F`, `Acc` abbreviates `Accepts`, `REW` abbreviates `RecoversEveryWitness`; all are quoted under *Model*):

```lean
-- C' = sep (or (sep (owned 0) (owned 1)) (owned 0)) (owned 1);  runP = call C' C' skip
Precise C' ∧ ¬ DisjPrecise C' ∧ ¬ RecoversEveryWitness fpGreedy C' ∧ Satisfies runP hTwo [0, 1] ∧
  ¬ Accepts ⟨true, true⟩ fpGreedy runP hTwo [0, 1] ∧ Accepts ⟨true, true⟩ fpSearch runP hTwo [0, 1]
```

* **Hypothesis ledger:** none (a closed statement about a concrete instance).
* **Depth:** `shallow`.
* **Non-vacuity witness:** Closed statement about a concrete instance; it has no hypotheses and is its own witness. (`fpGreedy_rejects_satisfying_run_precise_not_disjPrecise`)
* **Prior art:** [S3] Nguyen, Kuncak, Chin (VMCAI 2008); [S4] O'Hearn, Yang, Reynolds (POPL 2004) (full records under **Evidence**).
* **Design question:** informs part (b), completeness: when every satisfying run is accepted (package question at the top of **Findings**).
* `Basis: execution (Lean kernel check)` for the theorem.
* `Basis: derived (modeling bridge)` for any reading of this result about a real system: see B2 above, which states the reasoning and the gaps.
* **Non-claims:** listed under **Boundaries** (*CE-precise-not-disjPrecise-greedy-false-alarm*).

#### R3-trusted-unannotated-callee-breaks-soundness: Counterexample: trusted, unconfined unannotated callee breaks soundness

* **Lean:** `Toy.Monitor.trusted_unannot_write_outside_footprint_accepted` (`lean/ToyMonitor/Results.lean`); kind `counterexample`; tier `T1`; depth `shallow`.
* **Plain claim:** If unannotated callees are trusted rather than checked, the monitor (with a sound strategy and the leak check) accepts a run in which an unannotated helper of a callee that was given only owned 0 stores to byte 1, which its caller kept: byte 1 changes across a call whose footprint is [0], the confinement assumption fails, the contracts are violated, and the inline-checking monitor rejects the run.
* **Tier `T1`:** Uninstrumented code can invalidate monitor verdicts; the prototype Miri tracker sidesteps this by checking inlined callees' accesses (source comment). (Novelty search: see **Evidence**.)
* **Lean statement:**

```lean
-- lean/ToyMonitor/Results.lean:802-816
/-- **Result 3 (counterexample: trusted unannotated callees).** If unannotated callees
are trusted (not checked), the monitor — with a sound strategy and the leak check —
accepts a run in which an unannotated helper of a callee given only `owned 0` stores to
byte `1`, which the caller kept: the contracts are violated (byte `1` changes across a
call whose footprint is `[0]`), the confinement assumption `UnannotConfined` fails, and
the inline-checking (strict) monitor rejects the run. -/
theorem trusted_unannot_write_outside_footprint_accepted :
    StrategySound fpAtom ∧ (⟨true, false⟩ : MonCfg).leakCheck = true ∧
      Accepts ⟨true, false⟩ fpAtom runTrusted hTwo [0, 1] ∧
      ((⟨true, false⟩ : MonCfg).checkUnannot = false ∧
        ¬ UnannotConfined fpAtom runTrusted hTwo [0, 1]) ∧
      ¬ SatisfiesBy fpAtom runTrusted hTwo [0, 1] ∧ ¬ Satisfies runTrusted hTwo [0, 1] ∧
      (fpAtom (owned 0) (hTwo.restrict [0, 1]) = some [0] ∧ (1 : Addr) ∉ [0] ∧
        exec runTrusted hTwo 1 ≠ hTwo 1) ∧
      ¬ Accepts MonCfg.strict fpAtom runTrusted hTwo [0, 1]
```

* **With the key definitions unfolded** (`Fp A g F` abbreviates `IsFootprint A g F`, `Acc` abbreviates `Accepts`, `REW` abbreviates `RecoversEveryWitness`; all are quoted under *Model*):

```lean
-- runTrusted = call (owned 0) (owned 0) (unannot (write 1 7));  trusted config = ⟨true, false⟩
StrategySound fpAtom ∧ (⟨true, false⟩ : MonCfg).leakCheck = true ∧
  Accepts ⟨true, false⟩ fpAtom runTrusted hTwo [0, 1] ∧
  ((⟨true, false⟩ : MonCfg).checkUnannot = false ∧ ¬ UnannotConfined fpAtom runTrusted hTwo [0, 1]) ∧
  ¬ SatisfiesBy fpAtom runTrusted hTwo [0, 1] ∧ ¬ Satisfies runTrusted hTwo [0, 1] ∧
  (fpAtom (owned 0) (hTwo.restrict [0, 1]) = some [0] ∧ 1 ∉ [0] ∧ exec runTrusted hTwo 1 ≠ hTwo 1) ∧
  ¬ Accepts ⟨true, true⟩ fpAtom runTrusted hTwo [0, 1]
```

* **Hypothesis ledger:** none (a closed statement about a concrete instance).
* **Depth:** `shallow`.
* **Non-vacuity witness:** Closed statement about a concrete instance; it has no hypotheses and is its own witness. (`trusted_unannot_write_outside_footprint_accepted`)
* **Related proved statements:** `trusted_unannot_read_outside_footprint_accepted_heap_unchanged`.
* **Prior art:** [S6] Miri prototype, JoJoDeveloping/miri@a33a3c07; [S10] Agten, Jacobs, Piessens (POPL 2015); [S5] rust-lang/compiler-team issue #942 (full records under **Evidence**).
* **Design question:** informs part (c), unannotated code: what the monitor assumes about it (package question at the top of **Findings**).
* `Basis: execution (Lean kernel check)` for the theorem.
* `Basis: derived (modeling bridge)` for any reading of this result about a real system: see B5 above, which states the reasoning and the gaps.
* **Non-claims:** listed under **Boundaries** (*R3-trusted-unannotated-callee-breaks-soundness*).

#### CE-no-leak-check-stale-depth-ownership: Counterexample: without the leak check, depth-indexed ownership goes stale

* **Lean:** `Toy.Monitor.noLeakCheck_later_callee_inherits_leaked_byte` (`lean/ToyMonitor/Results.lean`); kind `counterexample`; tier `T1`; depth `shallow`.
* **Plain claim:** Without the leak check, in this depth-indexed monitor a byte leaked by one callee stays attributed to depth 1, and a later sibling callee at depth 1 that was given only owned 1 reads the leaked byte 0 and is accepted, although that call does not satisfy its contract even on its own.
* **Tier `T1`:** Consequence of identifying frames by call depth (as Fulminate's ghost state does) when leaks are not checked. (Novelty search: see **Evidence**.)
* **Lean statement:**

```lean
-- lean/ToyMonitor/Results.lean:782-793
/-- **Counterexample (no leak check: stale depth-indexed ownership).** Without the leak
check, a byte leaked by one callee stays attributed to call depth 1, and a later sibling
callee at depth 1 — given only `owned 1` — reads byte `0` and is accepted. The second
call does not satisfy its contract even judged on its own, and the strict monitor rejects
the run. -/
theorem noLeakCheck_later_callee_inherits_leaked_byte :
    StrategySound fpAtom ∧ Accepts ⟨false, true⟩ fpAtom runStale hTwo [0, 1] ∧
      ¬ Satisfies (.call (owned 1) (owned 1) (.read 0))
          (exec (.call (owned 0) .emp .skip) hTwo) [0, 1] ∧
      ¬ Satisfies runStale hTwo [0, 1] ∧ ¬ SatisfiesBy fpAtom runStale hTwo [0, 1] ∧
      UnannotConfined fpAtom runStale hTwo [0, 1] ∧
      ¬ Accepts MonCfg.strict fpAtom runStale hTwo [0, 1]
```

* **With the key definitions unfolded** (`Fp A g F` abbreviates `IsFootprint A g F`, `Acc` abbreviates `Accepts`, `REW` abbreviates `RecoversEveryWitness`; all are quoted under *Model*):

```lean
-- runStale = seq (call (owned 0) emp skip) (call (owned 1) (owned 1) (read 0));  config ⟨false, true⟩
StrategySound fpAtom ∧ Accepts ⟨false, true⟩ fpAtom runStale hTwo [0, 1] ∧
  ¬ Satisfies (call (owned 1) (owned 1) (read 0)) (exec (call (owned 0) emp skip) hTwo) [0, 1] ∧
  ¬ Satisfies runStale hTwo [0, 1] ∧ ¬ SatisfiesBy fpAtom runStale hTwo [0, 1] ∧
  UnannotConfined fpAtom runStale hTwo [0, 1] ∧ ¬ Accepts ⟨true, true⟩ fpAtom runStale hTwo [0, 1]
```

* **Hypothesis ledger:** none (a closed statement about a concrete instance).
* **Depth:** `shallow`.
* **Non-vacuity witness:** Closed statement about a concrete instance; it has no hypotheses and is its own witness. (`noLeakCheck_later_callee_inherits_leaked_byte`)
* **Prior art:** [S1] Fulminate (POPL 2025); [S2] CN (POPL 2023); [S6] Miri prototype, JoJoDeveloping/miri@a33a3c07; [S15] Separation Logic Foundations (full records under **Evidence**).
* **Design question:** informs part (a), soundness: when acceptance implies that every contract was satisfied (package question at the top of **Findings**).
* `Basis: execution (Lean kernel check)` for the theorem.
* `Basis: derived (modeling bridge)` for any reading of this result about a real system: see B1, B3 above, which state the reasoning and the gaps.
* **Non-claims:** listed under **Boundaries** (*CE-no-leak-check-stale-depth-ownership*).

### Statements of counterexamples, witnesses, positive controls and related theorems

Verbatim Lean source of every other name referenced in `results.json` (doc comment and statement).

**`accepts_fpGreedy_call_C_C_skip_of_satisfies`** (`lean/ToyMonitor/Results.lean`; referenced by R2-recovers-every-witness-implies-precise (related); R2c-satisfies-implies-satisfiesBy-for-witness-recovering-strategies (related); R2-greedy-monitor-complete-for-disjPrecise-contracts (related); R2-greedy-characterization (related); R2-owned0-or-owned1-defeats-every-sound-online-strategy (related)):

```lean
-- lean/ToyMonitor/Results.lean:704-711
/-- Whole-program completeness of a monitor for one fixed program does not require
precise contracts: the greedy monitor (under every configuration) accepts every
satisfying run of `call C C skip`, whose contracts are both the imprecise `C`, because
the callee does not distinguish the two witnesses. -/
theorem accepts_fpGreedy_call_C_C_skip_of_satisfies :
    (∀ A ∈ (Prog.call C C .skip).contracts, ¬ Precise A) ∧
      ∀ (cfg : MonCfg) (h : Heap) (O : List Addr),
        Satisfies (.call C C .skip) h O → Accepts cfg fpGreedy (.call C C .skip) h O
```

**`accepts_fpGreedy_of_satisfies_of_disjPrecise_nonvacuous`** (`lean/ToyMonitor/Results.lean`; referenced by R2-greedy-monitor-complete-for-disjPrecise-contracts (non-vacuity); R2-greedy-characterization (non-vacuity)):

```lean
-- lean/ToyMonitor/Results.lean:967-970
/-- Non-vacuity for the greedy completeness and characterization theorems: a program
whose precondition is a (precise) disjunction. -/
theorem accepts_fpGreedy_of_satisfies_of_disjPrecise_nonvacuous :
    (∀ A ∈ progOr.contracts, DisjPrecise A) ∧ Satisfies progOr hOne [0]
```

**`accepts_fpSearch_of_satisfies_of_precise_nonvacuous`** (`lean/ToyMonitor/Results.lean`; referenced by R2-search-monitor-complete-for-precise-contracts (non-vacuity); R2-search-characterization (non-vacuity)):

```lean
-- lean/ToyMonitor/Results.lean:973-975
/-- Non-vacuity for the search completeness and characterization theorems. -/
theorem accepts_fpSearch_of_satisfies_of_precise_nonvacuous :
    (∀ A ∈ runP.contracts, Precise A) ∧ Satisfies runP hTwo [0, 1]
```

**`accepts_imp_satisfiesBy_of_strategySound_nonvacuous`** (`lean/ToyMonitor/Results.lean`; referenced by R1-monitor-soundness (non-vacuity)):

```lean
-- lean/ToyMonitor/Results.lean:883-887
/-- Non-vacuity for R1: all hypotheses hold for `fpAtom`, the strict configuration, and
`progNV` (which contains a call and an unannotated helper). -/
theorem accepts_imp_satisfiesBy_of_strategySound_nonvacuous :
    StrategySound fpAtom ∧ MonCfg.strict.leakCheck = true ∧
      MonCfg.strict.checkUnannot = true ∧ Accepts MonCfg.strict fpAtom progNV hOne [0]
```

**`accepts_imp_satisfiesBy_of_unannotConfined_nonvacuous`** (`lean/ToyMonitor/Results.lean`; referenced by R1-trusted-soundness-under-unannot-confinement (non-vacuity)):

```lean
-- lean/ToyMonitor/Results.lean:899-906
/-- Non-vacuity for R1-trusted: all hypotheses hold with unannotated callees trusted, for
`progMixed`, whose unannotated helper both performs an (unchecked, confined) store and
calls an annotated function (monitored). -/
theorem accepts_imp_satisfiesBy_of_unannotConfined_nonvacuous :
    StrategySound fpAtom ∧ (⟨true, false⟩ : MonCfg).leakCheck = true ∧
      Accepts ⟨true, false⟩ fpAtom progMixed hOne [0] ∧
      ((⟨true, false⟩ : MonCfg).checkUnannot = false →
        UnannotConfined fpAtom progMixed hOne [0])
```

**`accepts_strict_fpSearch_iff_satisfies_call_C_C_skip`** (`lean/ToyMonitor/Results.lean`; referenced by R2-search-monitor-complete-for-precise-contracts (related); R2-search-characterization (related)):

```lean
-- lean/ToyMonitor/Results.lean:1107-1114
/-- **A fixed program can be characterized despite imprecise contracts.** For
`call C C skip`, whose contracts are all imprecise, the strict search monitor accepts a
run if and only if the run satisfies its contracts. -/
theorem accepts_strict_fpSearch_iff_satisfies_call_C_C_skip :
    (∀ A ∈ (Prog.call C C .skip).contracts, ¬ Precise A) ∧
    ∀ (h : Heap) (O : List Addr),
      Accepts MonCfg.strict fpSearch (.call C C .skip) h O ↔
        Satisfies (.call C C .skip) h O
```

**`existsFootprintComplete_not_imp_precise`** (`lean/ToyMonitor/Results.lean`; referenced by R2-recovers-every-witness-implies-precise (related)):

```lean
-- lean/ToyMonitor/Results.lean:698-701
/-- Existential footprint completeness does not imply precision (unlike witness
recovery, `precise_of_recoversEveryWitness`). -/
theorem existsFootprintComplete_not_imp_precise :
    ExistsFootprintComplete fpSearch C ∧ ¬ Precise C
```

**`fpGreedy_recoversEveryWitness_CFlip_not_disjPrecise`** (`lean/ToyMonitor/Results.lean`; referenced by R2a-greedy-recovers-every-witness-for-disjPrecise (related)):

```lean
-- lean/ToyMonitor/Results.lean:1025-1033
/-- **`DisjPrecise` is not necessary for greedy witness recovery.** `CFlip` is
satisfiable and precise but not `DisjPrecise`, and the left-biased `fpGreedy` still
recovers every witness of it, while the right-biased `fpGreedyR` does not. -/
theorem fpGreedy_recoversEveryWitness_CFlip_not_disjPrecise :
    Precise CFlip ∧
    ¬ DisjPrecise CFlip ∧
    sat CFlip hTwo ∧
    RecoversEveryWitness fpGreedy CFlip ∧
    ¬ RecoversEveryWitness fpGreedyR CFlip
```

**`fpGreedy_recoversEveryWitness_of_disjPrecise_nonvacuous`** (`lean/ToyMonitor/Results.lean`; referenced by R2a-greedy-recovers-every-witness-for-disjPrecise (non-vacuity)):

```lean
-- lean/ToyMonitor/Results.lean:932-936
/-- Non-vacuity for R2a: all hypotheses (of the theorem and of the witness-recovery
clause) hold for a disjunctive contract. -/
theorem fpGreedy_recoversEveryWitness_of_disjPrecise_nonvacuous :
    DisjPrecise (.or (pointsTo 0 0) (pointsTo 0 1)) ∧ Heap.Sub hOne hOne ∧
      sat (.or (pointsTo 0 0) (pointsTo 0 1)) hOne
```

**`fpGreedy_rejects_satisfying_run_imprecise_contract`** (`lean/ToyMonitor/Results.lean`; referenced by R1a-greedy-footprints-are-witnesses (related); R2c-satisfies-implies-satisfiesBy-for-witness-recovering-strategies (counterexample to hc); R2-greedy-monitor-complete-for-disjPrecise-contracts (counterexample to hdp); R2-greedy-characterization (counterexample to hdp)):

```lean
-- lean/ToyMonitor/Results.lean:644-651
/-- **Counterexample (imprecise contract, greedy).** `owned 0 ∨ owned 1` is not
disjunction-precise and greedy does not recover every witness of it; the run `runR` satisfies its
contracts, but the greedy footprint (byte `0`) is not the one the callee uses, and the
greedy monitor rejects the run. -/
theorem fpGreedy_rejects_satisfying_run_imprecise_contract :
    ¬ DisjPrecise C ∧ ¬ RecoversEveryWitness fpGreedy C ∧ Satisfies runR hTwo [0, 1] ∧
      ¬ SatisfiesBy fpGreedy runR hTwo [0, 1] ∧
      ¬ Accepts MonCfg.strict fpGreedy runR hTwo [0, 1]
```

**`fpGreedy_strategySound_nonvacuous`** (`lean/ToyMonitor/Results.lean`; referenced by R1a-greedy-footprints-are-witnesses (non-vacuity)):

```lean
-- lean/ToyMonitor/Results.lean:876-878
/-- Non-vacuity for R1a: greedy computes a footprint for a contract mixing `∨` and `∗`. -/
theorem fpGreedy_strategySound_nonvacuous :
    fpGreedy (.sep C (owned 1)) hTwo = some [0, 1]
```

**`fpGreedyR_strategySound`** (`lean/ToyMonitor/Results.lean`; referenced by R1a-greedy-footprints-are-witnesses (related)):

```lean
-- lean/ToyMonitor/Results.lean:179-180
/-- The right-biased greedy strategy is sound as well. -/
theorem fpGreedyR_strategySound : StrategySound fpGreedyR
```

**`fpSearch_existsFootprintComplete`** (`lean/ToyMonitor/Results.lean`; referenced by R2b-search-recovers-every-witness-for-precise (related)):

```lean
-- lean/ToyMonitor/Results.lean:687-690
/-- The backtracking strategy is existentially footprint-complete for *every* assertion,
precise or not: whenever a satisfying sub-fragment exists, it returns some genuine
footprint (not necessarily the intended one). -/
theorem fpSearch_existsFootprintComplete (A : Assn) : ExistsFootprintComplete fpSearch A
```

**`fpSearch_recoversEveryWitness_of_precise_nonvacuous`** (`lean/ToyMonitor/Results.lean`; referenced by R2b-search-recovers-every-witness-for-precise (non-vacuity)):

```lean
-- lean/ToyMonitor/Results.lean:940-942
/-- Non-vacuity for R2b: all hypotheses hold for the precise, not disjunction-precise `C'`. -/
theorem fpSearch_recoversEveryWitness_of_precise_nonvacuous :
    Precise C' ∧ Heap.Sub hTwo hTwo ∧ sat C' hTwo
```

**`fpSearch_rejects_satisfying_run_imprecise_contract`** (`lean/ToyMonitor/Results.lean`; referenced by R1b-search-footprints-are-witnesses (related); R2-search-monitor-complete-for-precise-contracts (counterexample to hp); R2-search-characterization (counterexample to hp)):

```lean
-- lean/ToyMonitor/Results.lean:655-660
/-- **Counterexample (imprecise contract, search).** `owned 0 ∨ owned 1` is not precise;
`runR` satisfies its contracts but the backtracking monitor (first footprint found:
byte `0`) rejects it. -/
theorem fpSearch_rejects_satisfying_run_imprecise_contract :
    ¬ Precise C ∧ Satisfies runR hTwo [0, 1] ∧
      ¬ Accepts MonCfg.strict fpSearch runR hTwo [0, 1]
```

**`fpSearch_strategySound_nonvacuous`** (`lean/ToyMonitor/Results.lean`; referenced by R1b-search-footprints-are-witnesses (non-vacuity)):

```lean
-- lean/ToyMonitor/Results.lean:880-881
/-- Non-vacuity for R1b: search computes a footprint for `C'`. -/
theorem fpSearch_strategySound_nonvacuous : fpSearch C' hTwo = some [0, 1]
```

**`monitorAux_sound`** (`lean/ToyMonitor/Lemmas.lean`; referenced by R1-monitor-soundness (related)):

```lean
-- lean/ToyMonitor/Lemmas.lean:299-311
/-- Soundness of the monitor in both instrumentation modes. If the strategy is sound and
the leak check is on, an accepted run (from a state satisfying the ownership-depth
invariant) satisfies its contracts with the strategy's footprints and restores the
ownership map, provided that uninstrumented code (reachable only when
`cfg.checkUnannot = false`) is confined to its frame. -/
theorem monitorAux_sound (s : Strategy) (hs : StrategySound s) (cfg : MonCfg)
    (hleak : cfg.leakCheck = true)
    (p : Prog) (chk : Bool) (h : Heap) (o o' : Own) (d : Nat) (O : List Addr)
    (hinv : OwnInv o d O)
    (hmon : monitorAux cfg s chk p h o d = some o')
    (hchk : chk = false → cfg.checkUnannot = false)
    (hconf : cfg.checkUnannot = false → UnannotConfinedAux s (!chk) p h O) :
    o' = o ∧ SatisfiesBy s p h O
```

The hypothesis `hinv` uses the ownership-depth invariant `OwnInv` (`lean/ToyMonitor/Lemmas.lean`):

```lean
-- lean/ToyMonitor/Lemmas.lean:210-213
/-- Ownership-depth invariant of the monitor in frame `d`: frame `d` owns exactly the
addresses in `O`, and no byte is owned by a deeper frame. -/
def OwnInv (o : Own) (d : Nat) (O : List Addr) : Prop :=
  (∀ a, o a = some d ↔ a ∈ O) ∧ (∀ a d', d < d' → o a ≠ some d')
```

**`noLeakCheck_accepts_leaky_post`** (`lean/ToyMonitor/Results.lean`; referenced by R1-monitor-soundness (counterexample to hleak); R1-trusted-soundness-under-unannot-confinement (counterexample to hleak)):

```lean
-- lean/ToyMonitor/Results.lean:769-777
/-- **Counterexample (no leak check: exactness).** Without the leak check, the monitor
accepts a callee that receives `owned 0` and returns only `emp`, although the
postcondition does not describe the callee's final fragment. All other hypotheses of R1
and R1-trusted hold. -/
theorem noLeakCheck_accepts_leaky_post :
    StrategySound fpAtom ∧ (⟨false, true⟩ : MonCfg).checkUnannot = true ∧
      Accepts ⟨false, true⟩ fpAtom runLeak hOne [0] ∧
      UnannotConfined fpAtom runLeak hOne [0] ∧
      ¬ SatisfiesBy fpAtom runLeak hOne [0] ∧ ¬ Satisfies runLeak hOne [0]
```

**`not_precise_C`** (`lean/ToyMonitor/Examples.lean`; referenced by R2-disjPrecise-implies-precise (counterexample to hA); R2-recovers-every-witness-implies-precise (counterexample to hc)):

```lean
-- lean/ToyMonitor/Examples.lean:214-216
/-- Negative: `owned 0 ∨ owned 1` is not precise (in `hTwo` both one-cell fragments
are witnesses). -/
theorem not_precise_C : ¬ Precise C
```

**`not_recoversEveryWitness_fpGreedy_C`** (`lean/ToyMonitor/Examples.lean`; referenced by R2a-greedy-recovers-every-witness-for-disjPrecise (counterexample to hA)):

```lean
-- lean/ToyMonitor/Examples.lean:289-291
/-- Negative: `fpGreedy` does not recover every witness of `owned 0 ∨ owned 1` (it commits to
`owned 0` even when the intended witness is the cell at `1`). -/
theorem not_recoversEveryWitness_fpGreedy_C : ¬ RecoversEveryWitness fpGreedy C
```

**`not_recoversEveryWitness_fpSearch_C`** (`lean/ToyMonitor/Examples.lean`; referenced by R2b-search-recovers-every-witness-for-precise (counterexample to hA)):

```lean
-- lean/ToyMonitor/Examples.lean:301-303
/-- Negative: `fpSearch` does not recover every witness of `owned 0 ∨ owned 1` either (its first
footprint is the cell at `0`). -/
theorem not_recoversEveryWitness_fpSearch_C : ¬ RecoversEveryWitness fpSearch C
```

**`owned0_or_owned1_each_run_accepted_by_some_strategy`** (`lean/ToyMonitor/Results.lean`; referenced by R2-owned0-or-owned1-defeats-every-sound-online-strategy (positive control)):

```lean
-- lean/ToyMonitor/Results.lean:615-624
/-- **Positive control for the impossibility.** Swapping the quantifiers makes the
conclusion fail: each of the two runs is accepted by some *sound* strategy (whose choices
on that run are genuine footprints) — the left-biased greedy strategy accepts the first,
the right-biased one the second. So the impossibility is about making one choice before
the callee runs, not about either run being unmonitorable by a sound strategy. -/
theorem owned0_or_owned1_each_run_accepted_by_some_strategy :
    StrategySound fpGreedy ∧ StrategySound fpGreedyR ∧
      Accepts MonCfg.strict fpGreedy runL hTwo [0, 1] ∧ SatisfiesBy fpGreedy runL hTwo [0, 1] ∧
      Accepts MonCfg.strict fpGreedyR runR hTwo [0, 1] ∧
      SatisfiesBy fpGreedyR runR hTwo [0, 1]
```

**`owned0_or_owned1_no_sound_strategy_accepts_both_nonvacuous`** (`lean/ToyMonitor/Results.lean`; referenced by R2-owned0-or-owned1-defeats-every-sound-online-strategy (non-vacuity)):

```lean
-- lean/ToyMonitor/Results.lean:981-986
/-- Non-vacuity for the impossibility: a sound strategy that handles disjunction exists
(so the hypothesis `StrategySound s` is satisfiable by a strategy that is not trivially
rejecting `∨`), and both runs satisfy their contracts. -/
theorem owned0_or_owned1_no_sound_strategy_accepts_both_nonvacuous :
    StrategySound fpGreedy ∧ fpGreedy C (hTwo.restrict [0, 1]) = some [0] ∧
      Satisfies runL hTwo [0, 1] ∧ Satisfies runR hTwo [0, 1]
```

**`owned0_or_owned1_unsound_strategy_accepts_both`** (`lean/ToyMonitor/Results.lean`; referenced by R2-owned0-or-owned1-defeats-every-sound-online-strategy (counterexample to StrategySound s)):

```lean
-- lean/ToyMonitor/Results.lean:635-639
/-- **Tightness of `StrategySound` in the impossibility.** An unsound strategy that
always transfers both bytes gets both runs accepted. -/
theorem owned0_or_owned1_unsound_strategy_accepts_both :
    ¬ StrategySound sAll ∧ Accepts MonCfg.strict sAll runL hTwo [0, 1] ∧
      Accepts MonCfg.strict sAll runR hTwo [0, 1]
```

**`precise_of_disjPrecise_nonvacuous`** (`lean/ToyMonitor/Results.lean`; referenced by R2-disjPrecise-implies-precise (non-vacuity)):

```lean
-- lean/ToyMonitor/Results.lean:928-929
/-- Non-vacuity for `precise_of_disjPrecise`: a disjunctive disjunction-precise contract. -/
theorem precise_of_disjPrecise_nonvacuous : DisjPrecise (.or (pointsTo 0 0) (pointsTo 0 1))
```

**`precise_of_recoversEveryWitness_nonvacuous`** (`lean/ToyMonitor/Results.lean`; referenced by R2-recovers-every-witness-implies-precise (non-vacuity)):

```lean
-- lean/ToyMonitor/Results.lean:924-925
/-- Non-vacuity for `precise_of_recoversEveryWitness`. -/
theorem precise_of_recoversEveryWitness_nonvacuous : RecoversEveryWitness fpAtom (owned 0)
```

**`read_unowned_rejected_and_unsatisfied`** (`lean/ToyMonitor/Results.lean`; referenced by R1-monitor-soundness (counterexample to hacc); R1prime-no-false-alarms-relative-to-own-footprints (counterexample to hsat); R1-trusted-soundness-under-unannot-confinement (counterexample to hacc); R2c-satisfies-implies-satisfiesBy-for-witness-recovering-strategies (counterexample to hsat); R2-greedy-monitor-complete-for-disjPrecise-contracts (counterexample to hsat); R2-search-monitor-complete-for-precise-contracts (counterexample to hsat)):

```lean
-- lean/ToyMonitor/Results.lean:847-857
/-- **Counterexample (acceptance / satisfaction premises).** Reading a byte the frame
does not own is accepted by no monitor and satisfies no contract, while every other
hypothesis of the soundness and completeness results holds: the confinement assumption
holds (the read is not unannotated code), and the program has no contracts (so every
contract-wise hypothesis holds vacuously). -/
theorem read_unowned_rejected_and_unsatisfied :
    (∀ (cfg : MonCfg) (s : Strategy), ¬ Accepts cfg s (.read 1) hTwo [0]) ∧
      (∀ s : Strategy, ¬ SatisfiesBy s (.read 1) hTwo [0] ∧ UnannotConfined s (.read 1) hTwo [0]) ∧
      ¬ Satisfies (.read 1) hTwo [0] ∧
      (∀ (s : Strategy), ∀ A ∈ (Prog.read 1).contracts,
        DisjPrecise A ∧ Precise A ∧ RecoversEveryWitness s A)
```

**`restrict_witnesses_sep_allows_unallocated_addrs`** (`lean/ToyMonitor/Results.lean`; referenced by R1-footprint-witnesses-separating-conjunction (related)):

```lean
-- lean/ToyMonitor/Results.lean:1181-1187
/-- `restrict_witnesses_sep` requires only `sat A (g.restrict F)`, which permits
unallocated addresses in `F` (here `99`), unlike `IsFootprint`. -/
theorem restrict_witnesses_sep_allows_unallocated_addrs :
    sat (owned 0) (hTwo.restrict [0, 99]) ∧
    SepP (fun g₁ => g₁ = hTwo.restrict [0, 99] ∧ sat (owned 0) g₁)
         (fun g₂ => g₂ = hTwo.remove [0, 99]) hTwo ∧
    ¬ IsFootprint (owned 0) hTwo [0, 99]
```

**`restrict_witnesses_sep_needs_sat`** (`lean/ToyMonitor/Results.lean`; referenced by R1-footprint-witnesses-separating-conjunction (counterexample to hA)):

```lean
-- lean/ToyMonitor/Results.lean:354-359
/-- **Counterexample (hypothesis of `restrict_witnesses_sep`).** `[0, 1]` does not carve
an `owned 0` fragment out of `hTwo`, and the split it induces is not a witness. -/
theorem restrict_witnesses_sep_needs_sat :
    ¬ sat (owned 0) (hTwo.restrict [0, 1]) ∧
      ¬ SepP (fun g₁ => g₁ = hTwo.restrict [0, 1] ∧ sat (owned 0) g₁)
          (fun g₂ => g₂ = hTwo.remove [0, 1]) hTwo
```

**`restrict_witnesses_sep_nonvacuous`** (`lean/ToyMonitor/Results.lean`; referenced by R1-footprint-witnesses-separating-conjunction (non-vacuity)):

```lean
-- lean/ToyMonitor/Results.lean:920-921
/-- Non-vacuity for `restrict_witnesses_sep`. -/
theorem restrict_witnesses_sep_nonvacuous : sat (owned 0) (hTwo.restrict [0])
```

**`satisfies_frame_needs_not_mem`** (`lean/ToyMonitor/Results.lean`; referenced by R1-frame-property (counterexample to a ∉ O)):

```lean
-- lean/ToyMonitor/Results.lean:867-871
/-- **Counterexample (`a ∉ O` in the frame property).** A run satisfying its contracts
in frame `[0]` changes byte `0`, which is in the frame. -/
theorem satisfies_frame_needs_not_mem :
    Satisfies (.write 0 5) hOne [0] ∧ ¬ ((0 : Addr) ∉ [0]) ∧
      exec (.write 0 5) hOne 0 ≠ hOne 0
```

**`satisfies_frame_nonvacuous`** (`lean/ToyMonitor/Results.lean`; referenced by R1-frame-property (non-vacuity)):

```lean
-- lean/ToyMonitor/Results.lean:915-917
/-- Non-vacuity for the frame property: the run satisfies its contracts and byte `1` is
outside the frame `[0]`. -/
theorem satisfies_frame_nonvacuous : Satisfies progNV hOne [0] ∧ (1 : Addr) ∉ [0]
```

**`satisfies_imp_satisfiesBy_of_recoversEveryWitness_nonvacuous`** (`lean/ToyMonitor/Results.lean`; referenced by R2c-satisfies-implies-satisfiesBy-for-witness-recovering-strategies (non-vacuity)):

```lean
-- lean/ToyMonitor/Results.lean:946-948
/-- Non-vacuity for R2c. -/
theorem satisfies_imp_satisfiesBy_of_recoversEveryWitness_nonvacuous :
    (∀ A ∈ progNV.contracts, RecoversEveryWitness fpAtom A) ∧ Satisfies progNV hOne [0]
```

**`satisfiesBy_imp_accepts_nonvacuous`** (`lean/ToyMonitor/Results.lean`; referenced by R1prime-no-false-alarms-relative-to-own-footprints (non-vacuity)):

```lean
-- lean/ToyMonitor/Results.lean:895-896
/-- Non-vacuity for R1′. -/
theorem satisfiesBy_imp_accepts_nonvacuous : SatisfiesBy fpAtom progNV hOne [0]
```

**`trusted_monitor_checks_nested_annotated_call`** (`lean/ToyMonitor/Results.lean`; referenced by R1-trusted-soundness-under-unannot-confinement (related)):

```lean
-- lean/ToyMonitor/Results.lean:825-832
/-- **Trusted policy still monitors annotated callees.** An unannotated helper that
performs no access at all but calls an annotated function whose precondition
`pointsTo 0 1` is false: the run violates its contracts, the confinement assumption
holds (there is no uninstrumented access), and the monitor with unannotated callees
trusted rejects the run — consistent with R1-trusted. -/
theorem trusted_monitor_checks_nested_annotated_call :
    UnannotConfined fpAtom pCallback hOne [0] ∧ ¬ Satisfies pCallback hOne [0] ∧
      ¬ Accepts ⟨true, false⟩ fpAtom pCallback hOne [0]
```

**`trusted_unannot_read_outside_footprint_accepted_heap_unchanged`** (`lean/ToyMonitor/Results.lean`; referenced by R1-trusted-soundness-under-unannot-confinement (related); R3-trusted-unannotated-callee-breaks-soundness (related)):

```lean
-- lean/ToyMonitor/Results.lean:1161-1173
/-- **Out-of-frame reads.** The unannotated helper of `pUnannotRead` reads a byte
outside its frame: the heap is unchanged (so a check that only compares the heap before
and after the call would pass), the monitor that trusts unannotated callees accepts the
run, yet the run violates `UnannotConfined` and its contracts, and the strict monitor
rejects it. -/
theorem trusted_unannot_read_outside_footprint_accepted_heap_unchanged :
    StrategySound fpAtom ∧
    (⟨true, false⟩ : MonCfg).leakCheck = true ∧
    Accepts ⟨true, false⟩ fpAtom pUnannotRead hTwo [0, 1] ∧
    exec pUnannotRead hTwo = hTwo ∧
    ¬ UnannotConfined fpAtom pUnannotRead hTwo [0, 1] ∧
    ¬ Satisfies pUnannotRead hTwo [0, 1] ∧
    ¬ Accepts MonCfg.strict fpAtom pUnannotRead hTwo [0, 1]
```

**`unsound_strategy_accepts_contract_violating_run`** (`lean/ToyMonitor/Results.lean`; referenced by R1-monitor-soundness (counterexample to hs); R1-trusted-soundness-under-unannot-confinement (counterexample to hs)):

```lean
-- lean/ToyMonitor/Results.lean:753-760
/-- **Counterexample (unsound strategy).** With a strategy that transfers byte `0`
without checking the precondition `pointsTo 0 1`, the strict monitor accepts a run
whose precondition is false. All other hypotheses of R1 and R1-trusted hold. -/
theorem unsound_strategy_accepts_contract_violating_run :
    ¬ StrategySound sBad ∧ MonCfg.strict.leakCheck = true ∧ MonCfg.strict.checkUnannot = true ∧
      Accepts MonCfg.strict sBad runBad hOne [0] ∧
      UnannotConfined sBad runBad hOne [0] ∧
      ¬ SatisfiesBy sBad runBad hOne [0] ∧ ¬ Satisfies runBad hOne [0]
```

**`write_outside_frame_changes_byte`** (`lean/ToyMonitor/Results.lean`; referenced by R1-frame-property (counterexample to Satisfies p h O)):

```lean
-- lean/ToyMonitor/Results.lean:368-372
/-- **Counterexample (hypothesis of the frame property).** A store to a byte outside
the frame changes that byte, and the run does not satisfy its contracts. -/
theorem write_outside_frame_changes_byte :
    ¬ Satisfies (.write 1 7) hTwo [0] ∧ (1 : Addr) ∉ [0] ∧
      exec (.write 1 7) hTwo 1 ≠ hTwo 1
```

## Boundaries

### Non-claims

Non-claims come first. Two apply to every result:

* **Toy model.** Toy model: straight-line programs (no branching, loops, recursion, allocation, deallocation, concurrency), one address per byte, contracts without logical variables, value-binding resource outputs (CN's take, the let-bound results of owned in compiler-team #942), function parameters or return values, existentials, recursive predicates or iterated separating conjunction; ownership is whole (no fractional or read-only permissions) and there are no allocation-block tokens (alloc_block). These theorems neither establish nor refute the corresponding claims about Fulminate, CN, Miri or any other implementation; any such connection is a separate modeling-bridge claim.
* **What "proved" means.** Every theorem is kernel-checked about the toy definitions quoted under
  **Findings** (`Basis: execution (Lean kernel check)`). It never means "true of a real system"; such
  connections are the separately labeled modeling-bridge claims B1–B5, whose basis is `derived`.

Result-specific non-claims (verbatim from `results.json`; names refer to proved theorems in
`Toy.Monitor`):

#### R1a-greedy-footprints-are-witnesses

* Soundness of one computed footprint only; it does not say greedy finds a footprint whenever one exists (it does not: fpGreedy_rejects_satisfying_run_imprecise_contract, fpGreedy_rejects_satisfying_run_precise_not_disjPrecise).
* Does not say the computed footprint is the one the program intends to transfer.
* The right-biased variant fpGreedyR is sound as well (fpGreedyR_strategySound); the choice of bias matters for completeness, not soundness.
* (and the two non-claims that apply to every result, above)

#### R1b-search-footprints-are-witnesses

* Says nothing about cost: search is exponential in the number of disjunctions in general.
* Search is still an online strategy: for imprecise contracts it can pick the wrong footprint (fpSearch_rejects_satisfying_run_imprecise_contract).
* (and the two non-claims that apply to every result, above)

#### R1-monitor-soundness

* Soundness holds for the whole toy assertion language, including imprecise disjunction; precision matters only for completeness. Do not read this as 'imprecise contracts are unsafe to monitor'.
* It is a statement about the one observed run; acceptance of a run says nothing about other inputs or schedules (testing, not verification).
* Exposes the monitor's footprints as witnesses; it does not say they are the footprints the programmer intended (for imprecise contracts there may be several).
* Frames are identified by call depth and ownership is whole (no fractions); results for per-frame maps or fractional permissions are not stated.
* The leak check here inspects only the bytes transferred to the callee; this is adequate because the monitor starts with no ownership at deeper depths, which is built into Accepts (initOwn).
* Proved as the cfg.checkUnannot = true instance of R1-trusted (whose confinement assumption is then vacuous), hence depth shallow; the substantive content is the shared induction with the ownership-depth invariant (Lemmas: OwnInv, monitorAux_sound), counted under R1-trusted, which also shows the monitor restores the ownership map exactly.
* (and the two non-claims that apply to every result, above)

#### R1prime-no-false-alarms-relative-to-own-footprints

* Relative to the strategy's own footprints only: a run that satisfies its contracts with some other footprints may still be rejected (completeness needs witness recovery; see R2).
* (and the two non-claims that apply to every result, above)

#### R1-trusted-soundness-under-unannot-confinement

* UnannotConfined is a property of the run that the trusted policy does not check; this theorem does not provide a way to establish it (e.g. by a static analysis or hardware isolation).
* The confinement assumption is relative to the frames the strategy computes for enclosing annotated calls; it is not a property of the unannotated code alone.
* Annotated callees called from unannotated code are always monitored here (trusted_monitor_checks_nested_annotated_call); a monitor that skipped them as well would need their contracts as an extra assumption.
* The examined Miri prototype keeps access checks on in unannotated callees (the inline-checking policy, covered by R1); Fulminate as published instruments a single translation unit of annotated C and does not discuss uninstrumented callees. This theorem is about the toy trusted policy only.
* Confinement covers reads as well as writes: an unannotated helper that reads a byte outside its frame leaves the heap unchanged, so a boundary check that only compares the heap before and after the call (such as the integrity check attributed to Agten et al. below) passes, yet the run violates UnannotConfined and its contracts, the monitor trusting unannotated callees accepts it, and the strict monitor rejects it (trusted_unannot_read_outside_footprint_accepted_heap_unchanged).
* (and the two non-claims that apply to every result, above)

#### R1-frame-property

* About the angelic Satisfies; it combines with R1 to give frame preservation for monitor-accepted runs only under R1's hypotheses.
* The heap domain never changes in this model (no allocation); with address-targeted allocation a frame property of this form needs extra side conditions (fresh addresses must avoid the frame), which are not studied here.
* (and the two non-claims that apply to every result, above)

#### R1-footprint-witnesses-separating-conjunction

* Purely definitional; it is the bridge from 'footprint' to 'witness for pre * frame' used to read R1.
* hA does not require the addresses of F to be allocated in g, unlike IsFootprint: for F = [0, 99] on hTwo, the restriction satisfies owned 0 and the conclusion holds, although F is not a footprint of owned 0 (restrict_witnesses_sep_allows_unallocated_addrs). R1 uses the theorem with strategy footprints, which are allocated.
* (and the two non-claims that apply to every result, above)

#### R2-disjPrecise-implies-precise

* The converse is false: C' is precise but not disjunction-precise.
* (and the two non-claims that apply to every result, above)

#### R2a-greedy-recovers-every-witness-for-disjPrecise

* DisjPrecise cannot be weakened to Precise (C' is precise and greedy does not recover its witness).
* DisjPrecise is a semantic condition on each disjunction; this result does not give a syntactic or decidable criterion (CN's if-then-else with pure guards is one sufficient pattern, not formalized here).
* Witness recovery is the uniqueness-including notion defined by RecoversEveryWitness, not mere existence of some footprint (ExistsFootprintComplete).
* DisjPrecise is sufficient, not necessary, for greedy witness recovery: the committed left-first choice is order-sensitive, and fpGreedy recovers every witness of CFlip = (owned 0 or (owned 0 * owned 1)) * owned 1, which is satisfiable and precise but not disjunction-precise, while the right-biased fpGreedyR does not (fpGreedy_recoversEveryWitness_CFlip_not_disjPrecise).
* (and the two non-claims that apply to every result, above)

#### R2b-search-recovers-every-witness-for-precise

* No cost bound: backtracking can be exponential.
* Precision is also necessary for any strategy to recover every witness (precise_of_recoversEveryWitness), so no strategy beats search on this criterion; on the weaker criterion of finding some footprint whenever one exists, search succeeds for every assertion, precise or not (fpSearch_existsFootprintComplete).
* (and the two non-claims that apply to every result, above)

#### R2-recovers-every-witness-implies-precise

* Definitional: the uniqueness is part of the definition of RecoversEveryWitness. It does not say that precision is necessary for weaker notions of completeness.
* Existential footprint completeness (some genuine footprint is returned whenever one exists) does not imply precision: fpSearch has it for every assertion, including the imprecise owned 0 or owned 1 (existsFootprintComplete_not_imp_precise).
* Whole-program completeness of a monitor for one fixed program does not imply that the program's contracts are precise: the greedy monitor accepts every satisfying run of call C C skip although C = owned 0 or owned 1 is imprecise, because the callee cannot tell the witnesses apart (accepts_fpGreedy_call_C_C_skip_of_satisfies).
* Witness recovery is a property of one contract evaluation; whole-run completeness is R2c and its corollaries.
* (and the two non-claims that apply to every result, above)

#### R2c-satisfies-implies-satisfiesBy-for-witness-recovering-strategies

* Requires witness recovery for every contract occurring in the program, postconditions included.
* Sufficient, not necessary: call C C skip is handled by the greedy monitor although greedy does not recover every witness of C (accepts_fpGreedy_call_C_C_skip_of_satisfies).
* (and the two non-claims that apply to every result, above)

#### R2-greedy-monitor-complete-for-disjPrecise-contracts

* Precision of the whole contract is not enough (C').
* Sufficient, not necessary, for a fixed program (accepts_fpGreedy_call_C_C_skip_of_satisfies).
* (and the two non-claims that apply to every result, above)

#### R2-search-monitor-complete-for-precise-contracts

* No cost bound.
* Sufficient, not necessary, for a fixed program: call C C skip has only imprecise contracts, yet the strict search monitor accepts exactly its satisfying runs (accepts_strict_fpSearch_iff_satisfies_call_C_C_skip).
* (and the two non-claims that apply to every result, above)

#### R2-greedy-characterization

* The equivalence is per run; it is not a statement that the program is correct on all inputs.
* DisjPrecise cannot be weakened to Precise: runP's contracts are the precise but not disjunction-precise C', runP satisfies them, and the strict greedy monitor rejects it (fpGreedy_rejects_satisfying_run_precise_not_disjPrecise).
* Sufficient, not necessary, for a fixed program: call C C skip has only imprecise contracts, yet the greedy monitor accepts every satisfying run of it (accepts_fpGreedy_call_C_C_skip_of_satisfies) and, by R1, accepts only satisfying runs.
* (and the two non-claims that apply to every result, above)

#### R2-search-characterization

* The equivalence is per run.
* Sufficient, not necessary, for a fixed program: call C C skip has only imprecise contracts, yet the strict search monitor accepts a run of it if and only if the run satisfies its contracts (accepts_strict_fpSearch_iff_satisfies_call_C_C_skip).
* (and the two non-claims that apply to every result, above)

#### R2-owned0-or-owned1-defeats-every-sound-online-strategy

* Shown for one concrete contract and one pair of runs; the general statement 'every imprecise contract defeats every sound strategy on some pair of runs' is not stated and is false at the level of single programs: the greedy monitor accepts every satisfying run of call C C skip (accepts_fpGreedy_call_C_C_skip_of_satisfies). Only the per-evaluation analogue precise_of_recoversEveryWitness is general.
* Positive control: swapping the quantifiers makes the conclusion fail - each run alone is accepted by some sound strategy (fpGreedy for the first, fpGreedyR for the second).
* Escape hatches (each defeats the impossibility; none is formalized here): (1) restrict contracts to a precise fragment, e.g. guarded if-then-else clauses as in CN/RefinedC (R2a/R2b then give completeness); (2) let the strategy see more than the contract and the caller's fragment - the callee's code, a call-site or static annotation naming the intended witness, or lookahead; (3) defer the choice: transfer lazily on first access, or backtrack over executions (re-run the callee with the other footprint, in the spirit of Nguyen et al.'s undo of disjunct colouring); (4) weaken satisfaction from exact to intuitionistic/affine, where transferring both bytes satisfies owned 0 or owned 1 at the cost of the caller temporarily losing the unused byte.
* Because both runs start from the same state with the call as first event, a strategy that also looked at the history before the call would not escape it.
* Rejection is a false alarm, not unsoundness: by R1 nothing unsound is accepted.
* (and the two non-claims that apply to every result, above)

#### CE-precise-not-disjPrecise-greedy-false-alarm

* Does not show greedy fails for every precise contract outside DisjPrecise.
* (and the two non-claims that apply to every result, above)

#### R3-trusted-unannotated-callee-breaks-soundness

* The inline-checking policy is sound (R1), and the trusted policy is sound under the confinement assumption (R1-trusted); this counterexample is only about trusting unconfined unannotated code.
* Does not model unannotated code that is outside the instrumented program entirely (e.g. foreign code), beyond its heap effect.
* Out-of-frame reads break the trusted policy too, not only out-of-frame writes such as the one here: an unannotated helper that reads a byte outside its frame leaves the heap unchanged, so a boundary check that only compares the heap before and after the call (such as the integrity check attributed to Agten et al. below) passes, yet the run violates UnannotConfined and its contracts, the monitor trusting unannotated callees accepts it, and the strict monitor rejects it (trusted_unannot_read_outside_footprint_accepted_heap_unchanged).
* (and the two non-claims that apply to every result, above)

#### CE-no-leak-check-stale-depth-ownership

* Specific to depth-indexed attribution without a leak check. Three return policies should be distinguished: (i) exact postconditions with a leak check (this model; required for the exact Satisfies); (ii) affine postconditions, where unmentioned callee resources may be discarded and are then inaccessible to everyone (as in affine separation logic, e.g. the \GC predicate of Separation Logic Foundations); (iii) the examined Miri prototype, which on frame pop inserts every remaining entry of the callee frame into the caller frame - the caller then holds ownership the postcondition did not state. Policies (ii) and (iii) are not modeled.
* Not examined whether any implementation exhibits this.
* (and the two non-claims that apply to every result, above)

### Attractive stronger conclusions that are not established

* *"Imprecise contracts are unsafe to monitor."* False in this model: soundness (R1, R1-trusted) holds for
  every assertion, including imprecise disjunction. Imprecision causes false alarms (rejected satisfying
  runs), never accepted violations.
* *"Precision is necessary for a complete monitor."* Precision is necessary only for witness recovery of a
  single contract evaluation (`precise_of_recoversEveryWitness`). For a fixed program, a monitor can be
  complete with imprecise contracts (`accepts_fpGreedy_call_C_C_skip_of_satisfies`,
  `accepts_strict_fpSearch_iff_satisfies_call_C_C_skip`), and search finds *some* footprint for every
  assertion (`fpSearch_existsFootprintComplete`).
* *"`DisjPrecise` characterizes the contracts the greedy monitor handles."* It is sufficient, not
  necessary (`fpGreedy_recoversEveryWitness_CFlip_not_disjPrecise`), and greedy is order-sensitive.
* *"Every imprecise contract defeats every sound strategy."* Shown for one contract (`owned 0 ∨ owned 1`)
  and one pair of runs only; false at the level of single programs.
* *"An accepted run shows that the program meets its contracts."* Every monitor result is about one
  observed run; nothing is said about other inputs.
* *"These results hold for Fulminate, CN, the Miri prototype, or Rust contracts."* Not established; see the
  modeling bridges, which are `derived` and list the gaps.
* *"Any ownership monitor needs a leak check."* Shown only for exact postconditions with depth-indexed
  ownership; affine postconditions and the prototype's merge-on-pop policy are not modeled.

### Escape hatches for the impossibility result

The impossibility (`owned0_or_owned1_no_sound_strategy_accepts_both`) depends on each of the following;
dropping or weakening any one defeats it.

* **A sound strategy.** An unsound strategy that transfers both bytes gets both runs accepted
  (`owned0_or_owned1_unsound_strategy_accepts_both`; formal).
* **One choice for both runs (online choice from the contract and the caller's fragment).** Each run alone
  is accepted by some sound strategy (`owned0_or_owned1_each_run_accepted_by_some_strategy`, the positive
  control; formal). Informally, the choice can be informed by more than the contract and the caller's
  fragment (the callee's code, a call-site or static annotation naming the intended witness, or lookahead),
  or deferred (transfer lazily on first access, or backtrack over executions by re-running the callee with
  the other footprint, in the spirit of Nguyen et al.'s undoing of disjunct colouring). History before the
  call does not help: both runs start from the same state with the call as the first event. Not
  formalized.
* **General (imprecise) disjunction in contracts.** Restricting contracts to a precise fragment, for example
  guarded if-then-else clauses as in CN and RefinedC, restores completeness (R2a, R2b and their monitor
  corollaries; formal for `DisjPrecise` and `Precise` contracts).
* **Exact satisfaction.** Under an intuitionistic or affine reading, transferring both bytes satisfies
  `owned 0 ∨ owned 1`, at the cost of the caller temporarily losing the unused byte. Not formalized.

### Hypotheses whose tightness is unknown

None. Every hypothesis of every result is either `tight`, with a proved counterexample in which all other
hypotheses hold and the conclusion fails, or `harmless`. The two `harmless` entries are the output
equations `fpGreedy A g = some F` and `fpSearch A g = some F` inside `StrategySound` (R1a, R1b): they only
name the returned footprint, and a strategy that fails says nothing.

### Disproved or dropped statements

None. All 20 stated results are proved exactly as stated, together with every counterexample,
non-vacuity witness and positive control they name; no statement was weakened, disproved or removed.

### Not examined

* The behavior of Fulminate, CN, the Miri prototype, or any implementation of the proposed Rust `owned`
  primitive (beyond the source reading summarized in the modeling bridges).
* Running time or space of the strategies (search is exponential in the number of disjunctions in general;
  no bound is proved for any strategy).
* Programs with branching, loops, recursion, allocation, deallocation or concurrency; logical variables and
  value-binding resource outputs; fractional or read-only permissions; allocation-block tokens.
* Intuitionistic or affine assertion semantics; per-frame ownership maps; the merge-on-pop return policy.
* Lean toolchains other than `v4.34.1`.

## Evidence

### Kernel-check record

`Basis: execution (Lean kernel check)`, observed 2026-11-20.

* **Toolchain:** `leanprover/lean4` release `v4.34.1` (lightweight tag `refs/tags/v4.34.1` → commit
  `5045d0056413266e57c625dcd7c365b10e377c52`, checked via the GitHub API on 2026-11-20; `lean --version`
  in `lean/` reports `4.34.1 ... commit 5045d0056413266e57c625dcd7c365b10e377c52`). Core Lean only; no
  Mathlib; no Lake dependencies.
* **Build:** `lake build` in `lean/` succeeds with no `sorry` warnings. The sources contain no `sorry`,
  `admit`, `native_decide`, `axiom` or `opaque` declarations, `implemented_by`, `extern`, `unsafe`,
  `debug.skipKernelTC` or `#exit`.
* **Axioms:** all 392 non-internal declarations of the `ToyMonitor` modules were audited with
  `Lean.collectAxioms`; each depends only on a subset of `propext`, `Classical.choice`, `Quot.sound`. The
  per-declaration list is `audit/axioms.json`.
* **Statement hashes:** for every Lean name referenced by `results.json` (results, related theorems,
  counterexamples, non-vacuity witnesses, positive controls), `audit/statements.json` records
  `statement_sha256` (SHA-256 of the UTF-8 text of Lean's `repr` of the declaration's type),
  `closure_sha256` (SHA-256 of the newline-joined, sorted list of entries `c : repr(type)`, followed by
  ` := repr(value)` when `c` is not a theorem, for every constant of a `ToyMonitor` module reachable from
  the statement through types, definition bodies and inductive constructors; theorem bodies are not
  followed), and `closure_size` (the number of entries). Any change to a statement or to any definition
  it depends on changes these hashes.

The table lists every hashed name, the cards that reference it (by result id and role), its axioms, and
its hashes (closure size in parentheses).

| Name (`Toy.Monitor.`) | Referenced by | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| --- | --- | --- | --- | --- |
| `fpGreedy_strategySound` | R1a-greedy-footprints-are-witnesses (result) | `Quot.sound`, `propext` | `fa630bb01a6b4f6c1f5224d11c4372210ec89fc13636b6b9b3817cd995610394` | `b8b789bcffe3685c82d7f93fa203e038f816e53451d9f6ae64c7100622e59b06` (30) |
| `fpSearch_strategySound` | R1b-search-footprints-are-witnesses (result) | `Quot.sound`, `propext` | `2d466184c6f723645241af939bf146a27a5137579861c4e6939bf255614dc3e7` | `9ef3a3a46a8431f7d459a751d6e9a9f3dad2ff2099aef5faeb0985067221f5a5` (29) |
| `accepts_imp_satisfiesBy_of_strategySound` | R1-monitor-soundness (result) | `Quot.sound`, `propext` | `e0b7f1532a8e34b1adc10a49ac105300f27445d039925108ace199d6c35b3b99` | `70828e3d98a7feca57bc4d1d4af9f0b7e10f5dd9ae1fc1d0a3acee6665a76567` (57) |
| `satisfiesBy_imp_accepts` | R1prime-no-false-alarms-relative-to-own-footprints (result) | `Quot.sound`, `propext` | `576c12a51d6b6e6b8cf4e71e981c354bc0d2b09c0ba3fa67f83f5eb66340e79a` | `d8c32c8ed4fe804351f6547c10e42682046ce2c31e2d0e208c866100de86b973` (56) |
| `accepts_imp_satisfiesBy_of_unannotConfined` | R1-trusted-soundness-under-unannot-confinement (result) | `Quot.sound`, `propext` | `732275400e0c023d2632bb115890e019c4919e8ad63d26ac9cad2ff6f7d4934e` | `fc9cb863ab31f7d62b39b0dbe98b1b2f160815a3ac5ac3b8d61ad6c79c0a49e4` (61) |
| `satisfies_frame` | R1-frame-property (result) | `Quot.sound`, `propext` | `86b04b949ac0f5ed0a63801a8f7ecc74114e58ed9948b5a6a77e7e3139496bad` | `9e6f46a32093a787b4a292ca10bf0af043cf010c59581144950305312e9810bd` (40) |
| `restrict_witnesses_sep` | R1-footprint-witnesses-separating-conjunction (result) | `Quot.sound`, `propext` | `835eeab5d0e48374bf3456151cec181e1586866d998aef994f0474bd62f618ec` | `73adae930a153dc61de82d2f1d5a3199f7bdc4877160cf8347dd5628abade3ae` (22) |
| `precise_of_disjPrecise` | R2-disjPrecise-implies-precise (result) | `Quot.sound`, `propext` | `051e9a918b9c39ad4977b8cdfd87e0859807946d8b6a00c948ac2846bdaf3602` | `3f31f9ae5efb982d5cb51aebe7cc74cb8f415f38228aa4fe5a41f71f9518f929` (24) |
| `fpGreedy_recoversEveryWitness_of_disjPrecise` | R2a-greedy-recovers-every-witness-for-disjPrecise (result) | `Quot.sound`, `propext` | `ca7747a958352edae00fa7d826c2767625dc7db2eeb8933a8c068b21f8c4d1a4` | `45b73b64f85d02181fb3b0d71898976682f382ebf5c028bb48a42f73dd916944` (34) |
| `fpSearch_recoversEveryWitness_of_precise` | R2b-search-recovers-every-witness-for-precise (result) | `Quot.sound`, `propext` | `24ec9704ddc99988161da0b63afb0a265651641fa88886a5a55ac2f8f2e023b8` | `a80b2b8c3b157993617de73aaebeaa41362e6eb31bbd6c500448638be7e73b21` (30) |
| `precise_of_recoversEveryWitness` | R2b-search-recovers-every-witness-for-precise (related); R2-recovers-every-witness-implies-precise (result); R2-owned0-or-owned1-defeats-every-sound-online-strategy (related) | `Quot.sound`, `propext` | `93f03ce52aab8ea86762e6dcb630d72518b9e924f95f25dfcff8c1dba820df7e` | `4343927f93d2d452d5dcb5066969f84f5505c695cefe7d18becabf4cdccd6aec` (24) |
| `satisfies_imp_satisfiesBy_of_recoversEveryWitness` | R2c-satisfies-implies-satisfiesBy-for-witness-recovering-strategies (result) | `Quot.sound`, `propext` | `8d1cb38380b94fdf6ea1e8069f544546adb4e251559706f9acc7bf0642868f6f` | `47d7e5eea822863df87f8bc768956742dc2ec635272e062dd5f7e0d25e231a91` (48) |
| `accepts_fpGreedy_of_satisfies_of_disjPrecise` | R2-greedy-monitor-complete-for-disjPrecise-contracts (result) | `Quot.sound`, `propext` | `10fb5434645c585f748f9607fab3cf12d1d490d686966bf367554323e6a4a492` | `45a1f215795884c8817a70bea93200d74eb9d05dccc4f8e4ac2c585b140273d0` (71) |
| `accepts_fpSearch_of_satisfies_of_precise` | R2-search-monitor-complete-for-precise-contracts (result) | `Quot.sound`, `propext` | `7d0ba5387fdc1b1b2de88317516fbf2927adfa711845bdb9d8dd63aba14ae559` | `a7b8f134fa970d8312f2ec4a4e0976e5156515191bae26e44b447f804d56cd25` (67) |
| `accepts_strict_fpGreedy_iff_satisfies_of_disjPrecise` | R2-greedy-characterization (result) | `Quot.sound`, `propext` | `e32e624c30476d2330e5234180c060e417950d06b6235a9e663b408049a5f486` | `f2cdae018515e87c9b41e8463a35481579cac48ef6d734d02936b77a4a9d12cb` (72) |
| `accepts_strict_fpSearch_iff_satisfies_of_precise` | R2-search-characterization (result) | `Quot.sound`, `propext` | `3f5f55da2d5163927ea2935927f8f5b7947a010b17b2b67faa372cedb30f28cb` | `f5e7d631306b78e572c214d7f0ad14f199cb162c41bc15fad814534e2bec93e2` (68) |
| `owned0_or_owned1_no_sound_strategy_accepts_both` | R2-owned0-or-owned1-defeats-every-sound-online-strategy (result) | `Quot.sound`, `propext` | `1be24ca2666d59841c016d4c96e200cac32ad16e4151fc8d986bba906b4a115b` | `0eaed439c8c26123f58df7d5abfbc7bf502bcd9c941855cfc75239932ad6956f` (63) |
| `fpGreedy_rejects_satisfying_run_precise_not_disjPrecise` | R1a-greedy-footprints-are-witnesses (related); R2a-greedy-recovers-every-witness-for-disjPrecise (counterexample to hA); R2-greedy-monitor-complete-for-disjPrecise-contracts (counterexample to hdp); R2-greedy-characterization (counterexample to hdp); CE-precise-not-disjPrecise-greedy-false-alarm (result) | `Quot.sound`, `propext` | `4655c46c510594482f75f658e36fd66b55136b18d02f98d4530f24f43c6c1a77` | `3dd5c3bdd01b2268983125596a6e66d82f71e3b91c862d8c7dea33c4e37c76c5` (78) |
| `trusted_unannot_write_outside_footprint_accepted` | R1-monitor-soundness (counterexample to hun); R1-trusted-soundness-under-unannot-confinement (counterexample to hconf); R3-trusted-unannotated-callee-breaks-soundness (result) | `Quot.sound`, `propext` | `2455aec1fefea90e8234a6c0e5273d39723986daef9bc143fdd7a572925bb6f1` | `56f4ecdaf3fc806cb3435e65a6a3b4b4a4ffd1d7ebd766ea35f661b5f84543c8` (71) |
| `noLeakCheck_later_callee_inherits_leaked_byte` | R1-monitor-soundness (counterexample to hleak); CE-no-leak-check-stale-depth-ownership (result) | `Quot.sound`, `propext` | `ed0f63999573ad0cbd4231cf54edec54da10c7153b2923bfa5d5ce42220f137b` | `0cd96d4d93f11c5b7a604dbe2c51f5ed09dddad9639875ae4142ad6629e537dc` (72) |
| `accepts_fpGreedy_call_C_C_skip_of_satisfies` | R2-recovers-every-witness-implies-precise (related); R2c-satisfies-implies-satisfiesBy-for-witness-recovering-strategies (related); R2-greedy-monitor-complete-for-disjPrecise-contracts (related); R2-greedy-characterization (related); R2-owned0-or-owned1-defeats-every-sound-online-strategy (related) | `Quot.sound`, `propext` | `0b277bd90186c60b39128d717a5b088b378a7621e7007dcaea82284c576560c8` | `8b205e6f8681d255a9fa58313a6b8d9ce2ed7fcabd7896054f471d1b5ac20b43` (70) |
| `accepts_fpGreedy_of_satisfies_of_disjPrecise_nonvacuous` | R2-greedy-monitor-complete-for-disjPrecise-contracts (non-vacuity); R2-greedy-characterization (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `6c2dfcef1e1b868c117932614c601fca35a8cccbe9a54d4c5de7e88ca101f3cb` | `8d5bf17dd4ccb4aa22adad57f7d30a790965151c2f137657ff554c382b1a1c93` (52) |
| `accepts_fpSearch_of_satisfies_of_precise_nonvacuous` | R2-search-monitor-complete-for-precise-contracts (non-vacuity); R2-search-characterization (non-vacuity) | `Quot.sound`, `propext` | `b55a17c138fb6cd8468a2659b0a04f62f5cd293b29384aaac6d40fdd35f07b99` | `d4ec476f052a23dc21e1d99c3be6b92f64ca29f0f94fef27021a04abf3dd7cf3` (50) |
| `accepts_imp_satisfiesBy_of_strategySound_nonvacuous` | R1-monitor-soundness (non-vacuity) | `Quot.sound`, `propext` | `0983d712167d38be05269ec473718dfd022d4e7d3dd82db752560264b5078032` | `f619e55128b3622c8272d175ab37c6005ea4f33293016439532c1f89660879cf` (63) |
| `accepts_imp_satisfiesBy_of_unannotConfined_nonvacuous` | R1-trusted-soundness-under-unannot-confinement (non-vacuity) | `Quot.sound`, `propext` | `7a15366dd36b6958694246875e07d643af762de15f887212493e6538281c25ff` | `550ef0f6f00bab82c39a3152654c47ddb46c8442c853060ee5d4f1e88d3e625b` (66) |
| `accepts_strict_fpSearch_iff_satisfies_call_C_C_skip` | R2-search-monitor-complete-for-precise-contracts (related); R2-search-characterization (related) | `Quot.sound`, `propext` | `e207275c8c3336a4e5a239203966f82a72b832d076347f575306bdba55ad4163` | `11cf7129d8a6743a7f6ee5b06d9fe923ffc1d58a53f2310af0834844d7e8e40a` (70) |
| `existsFootprintComplete_not_imp_precise` | R2-recovers-every-witness-implies-precise (related) | `Quot.sound`, `propext` | `85371af628d71f9cb3f1f8c3cb6bd66303869d8d171555a0327aea8502d97865` | `23ea285d35c30b919b25f31b731ed202601348e02766d18135d5028888b37fc5` (33) |
| `fpGreedy_recoversEveryWitness_CFlip_not_disjPrecise` | R2a-greedy-recovers-every-witness-for-disjPrecise (related) | `Quot.sound`, `propext` | `851b042f24dca3d9929bfd5fd3a9c62835d96e47635ec7a8497342d0698f374b` | `6bcfcd5d70ab89aa56328be39a90140df268bb39e210619d9cb49ba3849c04e4` (40) |
| `fpGreedy_recoversEveryWitness_of_disjPrecise_nonvacuous` | R2a-greedy-recovers-every-witness-for-disjPrecise (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `fa0548f7631931d9391b76c8c1bbc3a785384c7cad93fa93c45bf4952d0d2a60` | `568ce1e4f814075f57be371dd0c3a75a29ef55eaea90cf2fae5afc710da0e1a0` (27) |
| `fpGreedy_rejects_satisfying_run_imprecise_contract` | R1a-greedy-footprints-are-witnesses (related); R2c-satisfies-implies-satisfiesBy-for-witness-recovering-strategies (counterexample to hc); R2-greedy-monitor-complete-for-disjPrecise-contracts (counterexample to hdp); R2-greedy-characterization (counterexample to hdp) | `Quot.sound`, `propext` | `a29c21d7835138acd57e5e47fef67ba82b9192bd29333ed09bb7c40ca2992ab6` | `bd4db0fa07f5252e79d25b928cd1f8cb8a175338863c3b1dc7756def7d1926f0` (77) |
| `fpGreedy_strategySound_nonvacuous` | R1a-greedy-footprints-are-witnesses (non-vacuity) | `Quot.sound`, `propext` | `e537de93c1b605962b50448378397ab57e1c0da2cd7df59216ca865f0aa1be0e` | `fb2d91c6427a963e795db39282cd97988f71251f69ae981ac254e7f8ece2cf3c` (24) |
| `fpGreedyR_strategySound` | R1a-greedy-footprints-are-witnesses (related) | `Quot.sound`, `propext` | `8814fff85656bba5360f7f74b4fc814aec7e12e4d477a5ce81954c7f7dbc5813` | `98a41c563f81c5e3b9a523d16701872663530285d38d60fdb9036030085a1618` (30) |
| `fpSearch_existsFootprintComplete` | R2b-search-recovers-every-witness-for-precise (related) | `Quot.sound`, `propext` | `4dd689911549ed5283df488a4817c1d4c41ed0fb44dc160868f24e00f9cb56b6` | `4273c1dc1191921c461d0643c7c1863aae5fa3404c61f09b36e687b641c9f1c0` (30) |
| `fpSearch_recoversEveryWitness_of_precise_nonvacuous` | R2b-search-recovers-every-witness-for-precise (non-vacuity) | `Quot.sound`, `propext` | `26c8318ca62605b901c099608e769a947567f4adc93e50cd3faabf5a5238adfb` | `12b1fd4b2ce75fcac10d3a66c4f7a5c2059521fdc9d2e5a47bfa85349c9389f0` (25) |
| `fpSearch_rejects_satisfying_run_imprecise_contract` | R1b-search-footprints-are-witnesses (related); R2-search-monitor-complete-for-precise-contracts (counterexample to hp); R2-search-characterization (counterexample to hp) | `Quot.sound`, `propext` | `c9cc47064262443f479ca9f787b360faf0b1d7d36289c58ac93757e201963ca8` | `069b659b42bf23823e23206dc3c9485dca1e4e80116eb6d8920af28d7ddceb4f` (70) |
| `fpSearch_strategySound_nonvacuous` | R1b-search-footprints-are-witnesses (non-vacuity) | `Quot.sound`, `propext` | `726e918fee3785a3eaf646aff6d9748d47b70ed33cd5b87eb0d2662046d4ccaf` | `c606d972a57d9e9634709b591ffd794b127f779fff4d38ed01bc100861d28f4c` (24) |
| `monitorAux_sound` | R1-monitor-soundness (related) | `Quot.sound`, `propext` | `8b215e17308253585d124deee45a47c0756ae3526cb42efa557ec71a4e2f6ed0` | `21eeb3e577813a87b41f89921e9b4ac1178260633fb05f5320d2bbcbdfe74b60` (58) |
| `noLeakCheck_accepts_leaky_post` | R1-monitor-soundness (counterexample to hleak); R1-trusted-soundness-under-unannot-confinement (counterexample to hleak) | `Classical.choice`, `Quot.sound`, `propext` | `f2e2b458969af3e5300ea8a4383fc29959614723f8934b24ae525059d79dbf19` | `6a74332cec740378c9a5abd71ff312869fdce0bbba0a0f5a4f55ef92a2634132` (71) |
| `not_precise_C` | R2-disjPrecise-implies-precise (counterexample to hA); R2-recovers-every-witness-implies-precise (counterexample to hc) | `Quot.sound`, `propext` | `0bc9105405ca04e68f11b56ea6f9d0d6ff02f861300af48830d7dfb7ee310fcc` | `4b26e95b7decd2a326c2fc41329ee08ad5815a278ceb473da54212f4ab042653` (23) |
| `not_recoversEveryWitness_fpGreedy_C` | R2a-greedy-recovers-every-witness-for-disjPrecise (counterexample to hA) | `Quot.sound`, `propext` | `9e4ee5c62f0f3634d21262e570ab384743634890a04ef61767e3ade3f71f72ae` | `0fb417a3def2a6b27b21ba2ac5986f69c0c09536486a63f477d1e849258cbc38` (32) |
| `not_recoversEveryWitness_fpSearch_C` | R2b-search-recovers-every-witness-for-precise (counterexample to hA) | `Quot.sound`, `propext` | `bb8c895cbc8cab49c92af177864eb7de1eebaecc15c8aec61a93043ebc2ffabc` | `ca128330c8fda86c11d99f824bc99a507974794a6374c66ed27a26e94f9bc9f2` (31) |
| `owned0_or_owned1_each_run_accepted_by_some_strategy` | R2-owned0-or-owned1-defeats-every-sound-online-strategy (positive control) | `Quot.sound`, `propext` | `c6f217fb8222464087d106426fabe0d3e075b1a92392e9a711fecb0de6471ece` | `a2a3b242c749805bb0d67ffb9f9f4fadaf1b7002716415dc20d47a9779f1d4de` (73) |
| `owned0_or_owned1_no_sound_strategy_accepts_both_nonvacuous` | R2-owned0-or-owned1-defeats-every-sound-online-strategy (non-vacuity) | `Quot.sound`, `propext` | `88394c376a3588e7a2228b649a5087440cbe516519943750f0c278a09a1ff4b7` | `41667b48d78cf51b4247cf4ce0286cc760dbaf168fd0e6976dbe5bbaed14ad8c` (55) |
| `owned0_or_owned1_unsound_strategy_accepts_both` | R2-owned0-or-owned1-defeats-every-sound-online-strategy (counterexample to StrategySound s) | `Quot.sound`, `propext` | `36418b1d27e55db3ac433a10af6b97e4f89048d295da7eb4b649df0da087f5c8` | `93fd4aedd5e2d0f1f2764bae31a74e68f32d823dd7bbd1849d90268fbeda2f9d` (62) |
| `precise_of_disjPrecise_nonvacuous` | R2-disjPrecise-implies-precise (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `306af0f536233bca33c26a7dea341bad76c5cafe77773d31e2892e5351d7a4ca` | `70e453ddd2c9f6ca268211852c6e8e11deaf514e2945052eb6441b271070db27` (25) |
| `precise_of_recoversEveryWitness_nonvacuous` | R2-recovers-every-witness-implies-precise (non-vacuity) | `Quot.sound`, `propext` | `e693ef56c1463f51c2625388539e8f5226f88234c8e00f12c27aee26189aeea8` | `afe0a9ba955f4e55cec4560f2ea3dfcc2452c4199aca4f25fc34fe40b1a502c6` (27) |
| `read_unowned_rejected_and_unsatisfied` | R1-monitor-soundness (counterexample to hacc); R1prime-no-false-alarms-relative-to-own-footprints (counterexample to hsat); R1-trusted-soundness-under-unannot-confinement (counterexample to hacc); R2c-satisfies-implies-satisfiesBy-for-witness-recovering-strategies (counterexample to hsat); R2-greedy-monitor-complete-for-disjPrecise-contracts (counterexample to hsat); R2-search-monitor-complete-for-precise-contracts (counterexample to hsat) | `Quot.sound`, `propext` | `6b3ebe10f2600cd1d4d0f49742cafc635ed048abbaf7efddee10b1e3434e8809` | `8dae3fef9085d8979cec4518e30769fadaa44a3756a2528572efcae6774fb3cb` (73) |
| `restrict_witnesses_sep_allows_unallocated_addrs` | R1-footprint-witnesses-separating-conjunction (related) | `Quot.sound`, `propext` | `81abdcc77e1487f747cfc19cea74a703390bd0f3aefb5ce3933fd8d13230b023` | `ca132a64174c4d4d94cde3e82fe3f2afa0c39626b1fff9a1618763c467692d69` (26) |
| `restrict_witnesses_sep_needs_sat` | R1-footprint-witnesses-separating-conjunction (counterexample to hA) | `Quot.sound`, `propext` | `2bed5fe1a5d6d5268ed820d4cf9b41d90bfb17b8dea95be7f29f5e842d0d1d89` | `fab4d127adad661c33b43e056c143f8a9de2623989e123c516480909b8cb6b40` (25) |
| `restrict_witnesses_sep_nonvacuous` | R1-footprint-witnesses-separating-conjunction (non-vacuity) | `Quot.sound`, `propext` | `3bca8e46e0c0904678850c7ac1c3cc1596cd5410e95a09c669bf81903c156bed` | `9fc58a706d5d0677399c035119b6000191ee4c3e112a81ce03a64fcf3ea49fa7` (23) |
| `satisfies_frame_needs_not_mem` | R1-frame-property (counterexample to a ∉ O) | `Quot.sound`, `propext` | `9f0e7256dc31be0d8414d8a4ff5f2c810a674f4190d3bf286f3d951753c879cf` | `83752e08e939e63d2a832480914ef9c451e04daeebdfbf458a0532578c97edb9` (42) |
| `satisfies_frame_nonvacuous` | R1-frame-property (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `f4f67cc5fedd96fd9eaa3c9dfe2e9ee848bd42b2c88ac45541fb485dc8c3db45` | `3f39338ee072f3bf3111ca5e12128c943c729410c8a5d5ee3ebb99d116029958` (45) |
| `satisfies_imp_satisfiesBy_of_recoversEveryWitness_nonvacuous` | R2c-satisfies-implies-satisfiesBy-for-witness-recovering-strategies (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `e2213ceb2e9bff8a7bebc3e5e2835b154888afe4a829db3b71d0ed883aa02dfe` | `fc57d4e0a35b551fa760b961f8213ae4a053fece15c7397842a350dd7d01468d` (54) |
| `satisfiesBy_imp_accepts_nonvacuous` | R1prime-no-false-alarms-relative-to-own-footprints (non-vacuity) | `Classical.choice`, `Quot.sound`, `propext` | `ae1bf1c4d9d6981b91d1fd17821edc1b5b9bf66f036556bbf7412660ca08d66a` | `3d6afb0e055edbb855385404e1d389a931cbe1ff1c81b557474080f8bdb9ad27` (49) |
| `trusted_monitor_checks_nested_annotated_call` | R1-trusted-soundness-under-unannot-confinement (related) | `Classical.choice`, `Quot.sound`, `propext` | `ddc3f5112a84330616bc2f069a2d22b7072eea30225fd775f374e9897e28212a` | `d69f15b65c766fddb86e5c108bfb0e89654455f05380247e5541f7227b610e46` (68) |
| `trusted_unannot_read_outside_footprint_accepted_heap_unchanged` | R1-trusted-soundness-under-unannot-confinement (related); R3-trusted-unannotated-callee-breaks-soundness (related) | `Quot.sound`, `propext` | `d4e999fd5c7032c59758a1b2601a091473a58b2063080f2a4364cd3188e3ce32` | `5645ddecb9598614d1008660261564cb1318d335aecdf6d340a64fd6c94a7b38` (69) |
| `unsound_strategy_accepts_contract_violating_run` | R1-monitor-soundness (counterexample to hs); R1-trusted-soundness-under-unannot-confinement (counterexample to hs) | `Classical.choice`, `Quot.sound`, `propext` | `ed1f5151a10026c94fc182aeec0833bccc6f6762a97844b3a7089790d5efbb11` | `9c43b7a7980c3d25968161c11626f8c778ec8c21cf8924db70868f3d469eb9f0` (70) |
| `write_outside_frame_changes_byte` | R1-frame-property (counterexample to Satisfies p h O) | `Quot.sound`, `propext` | `d2ef3e474d37d9d583ac348c307d9a62a2d057753dc344452a7772ddcae26ccf` | `4b52141f1c2fcd08233db7ecbb1c029bdabcb74a80bc3d2f1999e343ba75d64b` (42) |

### Primary and secondary sources

Citation keys `[S1]`–`[S15]` are used under **Findings**. Each entry below is the exact text of the
corresponding prior-art record in `results.json`. Verification on 2026-11-20: every DOI below resolves
(Crossref) to the stated title and venue; the GitHub facts in [S5] and [S6] (issue metadata, the links in
the issue body, the six comments, the branch head commit and its author and date) were re-read through the
GitHub REST API; the CN quotations in [S2] were re-read in the open-access full text in the University of
Cambridge repository; the Separata entry [S12] was re-read on its Archive of Formal Proofs page, and the 'Affine' chapter of
[S15] was re-read on its web page. Section
references and quotations for [S1], [S3], [S4] and [S6] were taken from the full texts or source files read
on 2026-11-20, and their bibliographic records (and for [S6] the commit identity) were verified on the same
date. Entries marked "not examined" or "bibliographic data
verified" were not read beyond what they say.

Subjects in `REPORT.json`: the Lean toolchain, [S1], [S2], [S3], [S4] and [S12]. [S5] (an issue) and [S6]
(an unmerged branch of a fork) are context only.

* **[S1]** Rini Banerjee, Kayvan Memarian, Dhruv Makwana, Christopher Pulte, Neel Krishnaswami, Peter Sewell, 'Fulminate: Testing CN Separation-Logic Specifications in C', Proc. ACM Program. Lang. 9(POPL), Article 43, 2025, doi:10.1145/3704879. Sec. 2.3: reified ghost state records the C stack depth owning each byte; at a call the precondition's resources must be mapped at the caller's depth and are moved to the current depth, postconditions move them back, and leak checking is optional; Sec. 4.5.3: memory accesses are (optionally) instrumented to check ownership at the current depth. Sec. 2.4.2: CN restricts classical separation logic (resource outputs computed from inputs; if-then-else with guarded clauses instead of general disjunction, 'similar to RefinedC') so that runtime checking can determine 'without backtracking' which clause applies. Sec. 3.4: Theorem 3.5 and Corollary 3.6 relate two dynamic semantics (resource passing and the ghost-state instrumentation: they bisimulate and fail under the same conditions); they do not relate a monitor to a declarative satisfaction relation. Sec. 4.6: generated code is placed in a single file and multiple-file compilation units are not handled at present; the paper does not discuss uninstrumented or unannotated callees.
* **[S2]** Christopher Pulte, Dhruv C. Makwana, Thomas Sewell, Kayvan Memarian, Peter Sewell, Neel Krishnaswami, 'CN: Verifying Systems C Code with Separation-Logic Refinement Types', Proc. ACM Program. Lang. 7(POPL), Article 1, 2023, doi:10.1145/3571194. Introduces CN, a separation-logic refinement type system for C (static verification); Fulminate tests specifications written in CN's specification language at run time. CN restricts specifications so that resources and logical variables can be inferred without backtracking: 'CN does not allow general disjunction in predicate definitions; instead predicate definitions are ordered lists of guarded cases' (Sec. 2.9); resource types use 'a conditional rather than a traditional disjunction to avoid backtracking during typechecking' (Sec. 4.1); and logical variables may be introduced only as outputs of resources, through resource-let-bindings such as let O = Owned<struct s>(p), because unrestricted quantifiers would allow imprecise specifications (Sec. 2.6, 2.12). Sec. 6 says this well-moded style of assertion 'should also be amenable to runtime checking (though we leave this to future work)'. The paper defines no runtime monitor.
* **[S3]** Huu Hai Nguyen, Viktor Kuncak, Wei-Ngan Chin, 'Runtime Checking for Separation Logic', VMCAI 2008, LNCS 4905, pp. 203-217, doi:10.1007/978-3-540-78163-9_19. Marks (colours) the objects in a formula's footprint, an attempt to mark an object twice makes the disjunct unsatisfiable; for F1 or F2 it evaluates F1 first and, if F1 fails, undoes F1's colouring and evaluates F2.
* **[S4]** Peter W. O'Hearn, Hongseok Yang, John C. Reynolds, 'Separation and Information Hiding', POPL 2004, pp. 268-280, doi:10.1145/964001.964024. Defines: 'A predicate p is precise if and only if for all states (s,h), there is at most one subheap hp of h for which (s,hp) in p'. Sec. 6 ('A Conundrum') uses the imprecise precondition emp or x|->- and observes that with imprecise assertions 'different splittings can be chosen at different times'.
* **[S5]** rust-lang/compiler-team issue #942, 'Contracts: primitive ownership assertions: owned and alloc_block' (major change proposal by Dawid Lachowicz, opened 2025-11-10, closed as accepted 2025-11-22), https://github.com/rust-lang/compiler-team/issues/942. Proposes Fulminate-inspired owned/alloc_block assertions for Rust contracts: owned 'asserts exclusive ownership of memory pointed at by some raw pointer'; asserting a resource in a precondition consumes it and in a postcondition gives it back; read-only permissions are 'an open question and out of scope of this proposal'; runtime ownership tracking is left to interpreters, and the proposal mentions that a prototype runtime ownership tracker exists in Miri. The seconding comment notes that the compiler-team ask is only the addition of some intrinsics, with design decisions left to the owners of the contracts experiment; further progress is tracked in rust-lang/rust#149213.
* **[S6]** Prototype ownership tracking in Miri: repository JoJoDeveloping/miri, branch 'fulminate', commit a33a3c076f10bd42c742ca9eec9c30ed1d0166af (author Johannes Hostert, 2025-08-18; src/ownership/mod.rs, src/ownership/fraction.rs). One map per annotated frame from bytes (and allocation block tokens) to dyadic fractions; writes require the full fraction, reads a nonzero one; owned transfers a full fraction between the top annotated frame and its parent (into the child in preconditions, into the parent in postconditions; the partial-split variant is marked #[allow(unused)]); source comment: 'If non-ownership-annotated funcs are called, we treat it as if they were inlined', i.e. they run in the topmost annotated frame with access checks still active; when an annotated frame is popped (on_stack_pop) every remaining entry is inserted into the parent frame (no check that the popped frame is empty is made there). compiler-team #942 links this prototype directly: its section 'Fulminate' states that Johannes Hostert 'has already implemented a prototype runtime ownership tracker in Miri' and links https://github.com/JoJoDeveloping/miri/tree/fulminate, and its sections 'Examples', 'Semantics of owned and alloc_block' and 'Miri implementation' link example_dream.rs at commit a33a3c076f10bd42c742ca9eec9c30ed1d0166af (in 'Miri implementation' as a 'prototype ownership checker for contracts in Miri'; in 'Examples' at line 155). That commit was the head of branch 'fulminate' when checked (2026-11-20), so the source summarized here is the revision #942 links; #942 links example_dream.rs, not src/ownership/ itself, and none of the comments on #942 links the prototype.
* **[S7]** Samin S. Ishtiaq, Peter W. O'Hearn, 'BI as an Assertion Language for Mutable Data Structures', POPL 2001, pp. 14-26, doi:10.1145/360204.375719; John C. Reynolds, 'Separation Logic: A Logic for Shared Mutable Data Structures', LICS 2002, pp. 55-74, doi:10.1109/LICS.2002.1029817 - foundational accounts of separation-logic assertions over heap fragments, separating conjunction, and the frame rule; the exact (classical) reading of assertions used here, as opposed to an intuitionistic or affine one, is one of the variants discussed in this line of work (bibliographic data verified; bodies not re-examined).
* **[S8]** Gradual verification: Johannes Bader, Jonathan Aldrich, Eric Tanter, 'Gradual Program Verification', VMCAI 2018, LNCS 10747, pp. 25-46, doi:10.1007/978-3-319-73721-8_2; Jenna Wise, Johannes Bader, Cameron Wong, Jonathan Aldrich, Eric Tanter, Joshua Sunshine, 'Gradual Verification of Recursive Heap Data Structures', Proc. ACM Program. Lang. 4(OOPSLA), 2020, doi:10.1145/3428296; Conrad Zimmerman, Jenna DiVincenzo, Jonathan Aldrich, 'Sound Gradual Verification with Symbolic Execution', Proc. ACM Program. Lang. 8(POPL), 2024, doi:10.1145/3632927. Combine static verification of partial specifications (implicit dynamic frames / separation-logic style heap ownership) with run-time checks where static information is missing, with soundness results for the combination (bibliographic data and abstracts verified; bodies not examined). Related in spirit (run-time checks standing in for missing proof), not in the specific monitor/footprint-strategy setting here.
* **[S9]** Neven Villani, Johannes Hostert, Derek Dreyer, Ralf Jung, 'Tree Borrows', Proc. ACM Program. Lang. 9(PLDI), 2025, doi:10.1145/3735592; Ralf Jung, Benjamin Kimock, Christian Poveda, Eduardo Sanchez Munoz, Oli Scherer, Qian Wang, 'Miri: Practical Undefined Behavior Detection for Rust', Proc. ACM Program. Lang. 10(POPL), 2026, doi:10.1145/3776690 - context only (the aliasing model and the interpreter hosting the prototype above); bibliographic data verified, not examined for ownership contracts.
* **[S10]** Pieter Agten, Bart Jacobs, Frank Piessens, 'Sound Modular Verification of C Code Executing in an Unverified Context', POPL 2015, pp. 581-594, doi:10.1145/2676726.2676972 - as summarized in Fulminate Sec. 6: runtime checking of separation-logic contracts at module boundaries, with an integrity check that the untrusted context has not mutated the module state; not fine-grained checks of all accesses (the paper itself was not examined).
* **[S11]** Gerwin Klein, Rafal Kolanski, Andrew Boyton, 'Mechanised Separation Algebra', ITP 2012, LNCS 7406, pp. 332-337, doi:10.1007/978-3-642-32347-8_22 (Isabelle/HOL library; Archive of Formal Proofs entry Separation_Algebra). Mechanizes separation algebras and defines precise predicates (at most one sub-state of a state satisfies P); the specific closure lemmas were not examined.
* **[S12]** Zhe Hou, David Sanan, Alwen Tiu, Rajeev Gore, Ranald Clouston, 'Separata: Isabelle tactics for Separation Algebra', Archive of Formal Proofs, November 2016, https://isa-afp.org/entries/Separata.html. Theory Separata, lemma precise_sep_conj: 'assumes precise I and precise I' shows precise (I ∧* I')'. Separata imports the Separation_Algebra entry (Klein, Kolanski, Boyton) and uses its precise without redefining it.
* **[S13]** Michael Sammler, Rodolphe Lepigre, Robbert Krebbers, Kayvan Memarian, Derek Dreyer, Deepak Garg, 'RefinedC: Automating the Foundational Verification of C Code with Refined Ownership Types', PLDI 2021, pp. 158-174, doi:10.1145/3453483.3454036 - cited by Fulminate Sec. 2.4.2 as precedent for guarded clauses replacing general disjunction (the paper itself was not examined).
* **[S14]** Jan Smans, Bart Jacobs, Frank Piessens, 'Implicit Dynamic Frames', ACM Trans. Program. Lang. Syst. 34(1), Article 2, 2012, doi:10.1145/2160910.2160911 - as summarized in Fulminate Sec. 6: a variant of separation logic with executable heap-dependent assertions and access sets, discussing runtime checking as one advantage while focusing on proof (the paper itself was not examined).
* **[S15]** Arthur Chargueraud, 'Separation Logic Foundations', Software Foundations Vol. 6 (Coq), https://softwarefoundations.cis.upenn.edu - mechanized separation logic whose 'Affine' chapter generalizes the linear (exact) logic so that heap predicates may be discarded (the \GC predicate), as needed for garbage-collected languages; this is the affine alternative to the exact postconditions enforced here by the leak check.

### Novelty search record

Tiers `T1` rest on this search (2026-11-20): web searches for runtime checking of separation logic with
ownership monitors, completeness, precise assertions, disjunction, online footprint choice and
backtracking, gradual verification, and mechanized separation algebras; reading of Fulminate (full text),
Nguyen-Kuncak-Chin (full text), O'Hearn-Yang-Reynolds (full text), compiler-team #942 (full text) and the
Miri prototype source. No source examined states these results in this form or mechanizes them; the ideas
are standard, hence `T1` rather than `T3`. `T0` results restate known facts (each card names the source).
No result is claimed novel (`T3`).

## Revalidation

Requirements: [`elan`](https://github.com/leanprover/elan) (so that `lake` uses the toolchain pinned in
`lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. Nothing else is downloaded: the Lean
project has no dependencies.

**Primary check.** From the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory (the package is not modified), runs `lake build`, rejects
`sorry`, `admit`, `native_decide` and `axiom` declarations in the sources, computes the axioms of every
declaration of the `ToyMonitor` library with `Lean.collectAxioms` and requires them to be among
`propext`, `Classical.choice`, `Quot.sound`, and recomputes `statement_sha256`, `closure_sha256` and
`closure_size` (defined under **Evidence**) for every name referenced by `results.json` and every name in
`audit/statements.json`, comparing them with `audit/statements.json`. It prints `REVALIDATED` and exits
with status 0 iff every check passes. The script states in its header exactly what is hashed.

**Equivalent manual check** (same hashes, only `lake` and `python3`):

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean > /tmp/revalidation_audit.txt
cd ..
python3 - <<'EOF'
import hashlib, json
recorded = json.load(open("audit/statements.json"))["statements"]
allowed = {"propext", "Classical.choice", "Quot.sound"}
seen, bad = set(), 0
for line in open("/tmp/revalidation_audit.txt", encoding="utf-8"):
    if line.startswith("REVALIDATION_MISSING"):
        print(line.strip()); bad += 1
    if not line.startswith("REVALIDATION_STMT "):
        continue
    s = json.loads(line[len("REVALIDATION_STMT "):])
    got = {"statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
           "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
           "closure_size": len(s["closure"])}
    ok = recorded.get(s["name"]) == got and set(s["axioms"]) <= allowed
    bad += not ok
    seen.add(s["name"])
    print("ok  " if ok else "FAIL", s["name"], sorted(s["axioms"]))
unchecked = sorted(set(recorded) - seen)
bad += len(unchecked)
print("ALL OK" if bad == 0 else f"{bad} FAILURES; unchecked: {unchecked}")
EOF
```

`lean/RevalidationAudit.lean` is not part of the library target (`lake build` does not build it). For each
of the 58 names in `audit/statements.json` it prints the declaration's axioms (as `#print axioms`
would), the `repr` of its statement, and its sorted definition closure; the inline program hashes these and
compares them with `audit/statements.json`, printing `ALL OK` on success. To inspect one statement
directly, run `#check @Toy.Monitor.<name>` and `#print axioms Toy.Monitor.<name>` in a file that starts
with `import ToyMonitor`.

**What a pass establishes.** The theorems, with exactly the recorded statements and definition closures,
are accepted by the Lean kernel of the pinned toolchain using only the three standard axioms. It does not
re-check any claim about a real system (the modeling bridges), the citations, or the prose; when a
statement or a definition changes, the hashes change and the corresponding card must be re-read against
the new Lean source.
