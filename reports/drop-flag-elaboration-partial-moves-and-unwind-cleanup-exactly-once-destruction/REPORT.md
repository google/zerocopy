# Drop-flag elaboration, partial moves and unwind cleanup: exactly-once destruction in a toy model (Lean 4)

## Summary

This package is a Lean 4 toy model of drop elaboration with drop flags: affine values with destructors, partial moves, conditional moves and re-initialization, calls that may panic, unwind (cleanup) edges, scope-exit drops resolved into unconditional drops, no drops or drop-flag tests, and the double-panic rule. It contains 16 results (R1–R8), every one kernel-checked with no axioms beyond `propext`, `Classical.choice` and `Quot.sound`. Vocabulary: **exactly-once** (`ExactlyOnce`) is a property of one run (no value destroyed twice, no uncreated value destroyed, no destructor on unwritten memory, and, if the run returns or completes an unwind, every created value destroyed); **elaboration-correct** (`ElabCorrect`) is a property of an elaborated program (every run terminates and is exactly-once). "Every run" always means the run of `runElab` (the target semantics `run` with the step bound `fuelFor s`) on each input bit stream: every choice point reads one input bit and `run` is a function of the input, so each input determines one run. `run_eq_follow` proves that, on every input, `run` agrees with following that input through the exhaustive tree of runs (`run rule P fuel inp = (explore rule P fuel).follow inp`).

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

One sentence per result (its plain-language claim, with its hypotheses):

- **R1** (`stdElab_correct_of_forward_moveChecked_noNormalPathToResume`; theorem, T1): Assume that a destructor panic during unwinding aborts the process, and let s be a forward (acyclic, topologically numbered) toy program that only mentions valid move paths, moves only definitely-initialized places (call arguments pairwise disjoint), initializes only definitely-uninitialized places, and has no resume node reachable from the entry along normal edges only. Then the standard drop elaboration (flags set at init, cleared at move and, for call arguments, before the call, set for a call's destination on its normal edge; unconditional drop where must-init, nothing where not may-init, flag test otherwise; cleanup drops without landing pads) of s is elaboration-correct: on every input its run terminates (returns, completes an unwind, or aborts) and is exactly-once, i.e. destroys no value twice, destroys no uncreated value, runs no destructor on unwritten memory, and, if it returns or completes an unwind, destroys every created value.
- **R2s** (`elabCorrect_of_allCompatible_of_forward_moveChecked_noNormalPathToResume`; theorem, T1): Assume that a destructor panic during unwinding aborts the process, let s be a forward (acyclic, topologically numbered) toy program that only mentions valid move paths, moves only definitely-initialized places (call arguments pairwise disjoint), initializes only definitely-uninitialized places, and has no resume node reachable from the entry along normal edges only, and let d be a decision map that is compatible with the fine analyses at every forward-reachable drop point (an unconditional drop only for must-init atoms, nothing only for atoms that are not may-init, a flag test anywhere). Then the elaboration of s with the standard flag maintenance and decision map d is elaboration-correct: on every input its run terminates (returns, completes an unwind, or aborts) and is exactly-once, i.e. destroys no value twice, destroys no uncreated value, runs no destructor on unwritten memory, and, if it returns or completes an unwind, destroys every created value.
- **R2** (`elabCorrect_iff_allCompatible_of_forward_moveChecked_noNormalPathToResume`; characterization, T1): Assume that a destructor panic during unwinding aborts the process and let s be a forward (acyclic, topologically numbered) toy program that only mentions valid move paths, moves only definitely-initialized places (call arguments pairwise disjoint), initializes only definitely-uninitialized places, and has no resume node reachable from the entry along normal edges only. Then, with the standard flag maintenance, a decision map d is elaboration-correct (every run terminates and is exactly-once) if and only if d is compatible with the fine analyses at every forward-reachable drop point (an unconditional drop only for must-init atoms, nothing only for atoms that are not may-init, a flag test anywhere). Consequently (staticChoice_compatible_iff), at a forward-reachable drop point a flag test is required for an atom exactly when it is may-init and not must-init there; at other forward-reachable drop points some static choice is compatible.
- **R2n** (`allCompatible_of_exactlyOnce_of_placesAreMovePaths`; theorem, T1): Assume only that every place mentioned by the program s is a valid move path. If every run of the elaboration of s with decision map d (standard flag maintenance, abort rule; a run is the result of `runElab`, the target semantics `run` with step bound `fuelFor s`, on one input bit stream) is exactly-once, then d is compatible with the fine analyses at every forward-reachable drop point: d drops an atom unconditionally only where it is must-init and does nothing for an atom only where it is not may-init. Forwardness, MovesFromInit, InitsIntoUninit and NoNormalPathToResume are not assumed, and termination is not assumed.
- **R3** (`staticChoice_at_disagreement_fails_of_placesAreMovePaths`; impossibility, T1): Assume only that every place mentioned by the program s is a valid move path, let i be a drop point (a ret or resume node) and let atom a be may-init but not must-init at i. Then, with the standard flag maintenance and the abort rule (runs are results of `runElab`, the target semantics `run` with step bound `fuelFor s`), (1) replacing the standard decision for a at i by an unconditional drop gives an input whose run violates NoDoubleDrop (a value destroyed twice, an uncreated value destroyed, or a destructor on unwritten memory), and (2) replacing it by nothing gives an input whose run returns or completes an unwind and violates NoLeak. Forwardness, MovesFromInit, InitsIntoUninit and NoNormalPathToResume are not assumed.
- **R4a** (`staticDrop_at_join_double_drops`; counterexample, T0): On progJoin (init x; branch; move x on one branch; ret), which satisfies all hypotheses of R1 and whose standard elaboration is elaboration-correct (by R1, `stdElab_correct_of_forward_moveChecked_noNormalPathToResume`, since `MoveChecked` is `PlacesAreMovePaths ∧ MovesFromInit ∧ InitsIntoUninit`), replacing only the decision for x at the join (node 3, where x is may-init and not must-init) by an unconditional drop gives, on input [true], the log [create 0, consume 0, drop 0], which violates NoDoubleDrop.
- **R4a-skip** (`staticSkip_at_join_leaks`; counterexample, T0): On progJoin, replacing only the decision for x at the join by nothing gives, on input [false, false], a run that returns with log [create 0], which violates NoLeak.
- **R4b** (`argFlagNotClearedOnUnwind_double_drops`; counterexample, T1): On progCleanup (two calls sharing one cleanup node; the second call consumes x), which satisfies all hypotheses of R1 and whose standard elaboration is elaboration-correct (by R1, `stdElab_correct_of_forward_moveChecked_noNormalPathToResume`, since `MoveChecked` is `PlacesAreMovePaths ∧ MovesFromInit ∧ InitsIntoUninit`), clearing call-argument flags only on the call's normal edge (clearArgsBeforeCall := false, everything else standard) gives, on input [false, true, false], a run that completes an unwind with log [create 0, consume 0, drop 0]: the second call consumes x and panics, and the shared cleanup still sees x's flag set. NoDoubleDrop is violated.
- **R4c-kill** (`wholeKillAnalysis_leaks_remaining_field`, `wholeKillFlags_leaks_remaining_field`; counterexample, T0): Treating a partial move as a move of the whole local breaks exactly-once, in each of two ingredients separately: (analysis) on progPartial (init x : pair of two leaves; move x.0; ret), static decisions computed by the whole-local analysis (stdMap at granularity wholeKill, flag maintenance standard; on this straight-line program no flag is tested, flagConfig_gran_inert_on_progPartial) drop nothing at the ret, and the run on [] returns with log [create 0, create 1, consume 0], violating NoLeak; (flags) on progPartialFlag (conditional init, conditional move of x.0), with the standard fine decisions and flag updates at granularity wholeKill, the run on [true, true] returns with log [create 0, create 1, consume 0], violating NoLeak.
- **R4c-keep** (`wholeKeepAnalysis_drops_moved_field`, `wholeKeepFlags_drops_moved_field`; counterexample, T0): Ignoring partial moves breaks exactly-once, in each of two ingredients separately: (analysis) on progPartial, static decisions computed by an analysis that tracks only whole-local moves (stdMap at granularity wholeKeep, flag maintenance standard) drop the moved field: the run on [] has log [create 0, create 1, consume 0, drop 1, drop 0], violating NoDoubleDrop; (flags) on progPartialFlag, with the standard fine decisions and flag updates at granularity wholeKeep, the run on [true, true, false] has log [create 0, create 1, consume 0, drop 1, drop 0], violating NoDoubleDrop.
- **R4d** (`reinitWithoutFlagSet_leaks`; counterexample, T0): On progReinit (init x; move x; branch; re-init x on one branch; ret), which satisfies all hypotheses of R1 and whose standard elaboration is elaboration-correct (by R1, `stdElab_correct_of_forward_moveChecked_noNormalPathToResume`, since `MoveChecked` is `PlacesAreMovePaths ∧ MovesFromInit ∧ InitsIntoUninit`), omitting only the flag update of the re-initialization at node 3 gives, on input [true], a run that returns with log [create 0, consume 0, create 1], violating NoLeak.
- **R5** (`stdElab_noDoubleDrop_continueUnwind_of_forward_placesAreMovePaths_movesFromInit`; theorem, T1): Assume that a destructor panic during unwinding continues unwinding (here: leaves the frame, since cleanup drops have no landing pad), and let s be a forward program that only mentions valid move paths and moves only definitely-initialized places (call arguments pairwise disjoint). Then for every input the run of the standard elaboration of s terminates and satisfies NoDoubleDrop (no value destroyed twice, no uncreated value destroyed, no destructor on unwritten memory). InitsIntoUninit and NoNormalPathToResume are not assumed.
- **R6** (`continueUnwind_completedUnwind_leaks_of_forward_moveChecked`, `continueUnwind_not_elabCorrect_for_all_forward_moveChecked`; impossibility, T1): Assume that a destructor panic during unwinding continues unwinding (leaves the frame) instead of aborting. Then there is a program satisfying every hypothesis of R1 — progUnwind: a struct without its own destructor whose two leaf fields are live across a call whose unwind edge goes directly to a resume node — and an input, [true, true] (the call panics, then the destructor of the first field dropped by the cleanup ladder panics), on which the run of the standard elaboration completes an unwind, satisfies NoDoubleDrop, and violates NoLeak (the other field is never destroyed). Hence, under this rule, the standard elaboration is not elaboration-correct for every program satisfying R1's hypotheses.
- **R7** (`stdFlagSet_subset_of_exactlyOnce_of_placesAreMovePaths`; theorem, T1): Assume only that every place mentioned by the program s is a valid move path. If every run of the elaboration of s with decision map d (same CFG, one flag per atom, standard flag maintenance, abort rule; a run is the result of `runElab`, the target semantics `run` with step bound `fuelFor s`, on one input bit stream) is exactly-once, then every atom that the standard map tests at some forward-reachable drop point is also tested by d at some forward-reachable drop point: the standard flag set is a lower bound (subset) of d's flag set. This does not assert that the standard map is itself elaboration-correct.
- **R7L** (`stdMap_correct_and_flagSet_least_of_forward_moveChecked_noNormalPathToResume`; theorem, T1): Assume that a destructor panic during unwinding aborts the process and let s be a forward (acyclic, topologically numbered) toy program that only mentions valid move paths, moves only definitely-initialized places (call arguments pairwise disjoint), initializes only definitely-uninitialized places, and has no resume node reachable from the entry along normal edges only. Then the standard decision map is elaboration-correct, and every elaboration-correct decision map (same CFG, one flag per atom, standard flag maintenance) tests every atom that the standard map tests at some forward-reachable drop point; so the standard flag set is the least flag set among elaboration-correct decision maps of this class.
- **R8** (`fewerFlags_than_std_not_exactlyOnce_of_placesAreMovePaths`; impossibility, T1): Assume only that every place mentioned by the program s is a valid move path. If a decision map d (same CFG, one flag per atom, standard flag maintenance, abort rule) has a strictly shorter flag set than the standard map (atoms tested at forward-reachable drop points), then some input gives a run of d's elaboration (the result of `runElab`, the target semantics `run` with step bound `fuelFor s`) that is not exactly-once.

What these results do not show is listed first under **Boundaries** (non-claims, common and per result); read the relevant non-claims before relying on a result. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, a C++ implementation or any real program: no embedding, abstraction or simulation relation between the toy model and any of these systems is proved (model–system relation: none proved). The connections to rustc and C++ are separate claims labelled `derived (modeling bridge)` under **Findings**.

## Applicability

### Model fidelity

This is a toy model, not a mirror of any compiler's data structures; no relation (embedding, abstraction or simulation) between it and rustc, LLVM or a C++ implementation is proved (model–system relation: none proved), so its results neither establish nor refute the corresponding claims about those systems. It is meant to capture drop elaboration as performed for Rust MIR: per-location initialization analyses, the classification of each drop into a static drop, no drop or a flag-guarded drop, drop-flag maintenance at initializations, moves and calls, cleanup ladders on unwind edges, landing-pad-free drops in cleanup code, and the rule that a destructor panic during unwinding aborts. Known gaps (each repeated as a non-claim under **Boundaries**): programs are acyclic (the analyses are one forward pass); drop points are the frame-exit terminators `ret` and `resume`; every type has at least one destructor unit; an atom's drop glue runs in one step with one panic bit; branches, call panics and destructor panics are independent input bits; enums, arrays, moves between locals, drop-and-replace assignment, borrows, nested scopes, `catch_unwind` and async drops are not modelled; a call inside cleanup code may panic and keep unwinding, which MIR forbids.

### Lean environment and subjects

Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core library (no Mathlib, no `Std` imports, no `[[require]]`). Lake project in `lean/` (library `ToyDropFlags`, namespace `Toy.DropFlags`); the main results are in `lean/ToyDropFlags/Results.lean`. The Lean toolchain is the subject that checks every finding. The other subjects in `REPORT.json` (a rustc commit, RFC 320, the Rust Reference, the C++ working draft N4950, and the published mechanizations) are sources for prior art and for the modeling-bridge claims; no finding is a measurement of them.

### Definitions

Each definition below is quoted verbatim from the Lean source. Each core predicate (`Ty.isMovePath`, `NoDoubleDrop`, `NoLeak`, `Forward`, `ForwardReachable`, `PlacesAreMovePaths`, `MovesFromInit`, `InitsIntoUninit`, `NoNormalPathToResume`, `MoveChecked`, `ExactlyOnce`, `ElabCorrect`, `AllCompatible`) has proved positive and negative examples in `lean/ToyDropFlags/Examples.lean` (names given with each item).

#### Types, units, atoms

```lean
-- lean/ToyDropFlags/Basic.lean:30
abbrev Path := List Bool
```

```lean
-- lean/ToyDropFlags/Basic.lean:24-27
inductive Ty where
  | leaf : Ty
  | pair (hasDrop : Bool) (a b : Ty) : Ty
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyDropFlags/Basic.lean:35-38
def Ty.units : Ty → List Path
  | .leaf => [[]]
  | .pair d a b =>
      (if d then [[]] else []) ++ (a.units.map (false :: ·) ++ b.units.map (true :: ·))
```

```lean
-- lean/ToyDropFlags/Basic.lean:41-44
def Ty.atoms : Ty → List Path
  | .leaf => [[]]
  | .pair true _ _ => [[]]
  | .pair false a b => a.atoms.map (false :: ·) ++ b.atoms.map (true :: ·)
```

```lean
-- lean/ToyDropFlags/Basic.lean:56-59
structure Place where
  loc : Nat
  path : Path
  deriving DecidableEq, Repr
```

A `Path` is a list of field selectors (`false` selects field `.0`, `true` selects field `.1`); a `Place` is a local (by index into the program's locals) and a path into that local's type. A `leaf` is an owned resource with a destructor; `pair d a b` is a struct with fields `.0`, `.1`; `d = true` iff it has its own destructor (a `Drop` impl). A *unit* is a node whose destruction is logged (every leaf, and every struct with its own destructor); an *atom* is a maximal move path (a struct with its own destructor cannot be partially moved, so it is one atom). Examples: `dropT.units = [[], [false], [true]]`, `dropT.atoms = [[]]`, `pairT.atoms = [[false], [true]]`. `Ty.isMovePath t p`: `p` follows `t` and never enters a struct with its own destructor (positive `isMovePath_pos`, negative `isMovePath_neg`). `atomsOf ls p`: the atoms overlapping place `p`; `unitsUnder ls p`: the units inside `p`.

#### Destructor logs

```lean
-- lean/ToyDropFlags/Basic.lean:101-106
inductive Event where
  | create (v : Nat)
  | consume (v : Nat)
  | drop (v : Nat)
  | garbage
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyDropFlags/Basic.lean:109-110
def destroyCount (log : List Event) (v : Nat) : Nat :=
  log.countP fun e => e == .consume v || e == .drop v
```

```lean
-- lean/ToyDropFlags/Basic.lean:113-117
def destroyedIds (log : List Event) : List Nat :=
  log.filterMap fun
    | .consume v => some v
    | .drop v => some v
    | _ => none
```

```lean
-- lean/ToyDropFlags/Basic.lean:120-123
def createdIds (log : List Event) : List Nat :=
  log.filterMap fun
    | .create v => some v
    | _ => none
```

```lean
-- lean/ToyDropFlags/Basic.lean:131-134
def NoDoubleDrop (log : List Event) : Prop :=
  (∀ v ∈ destroyedIds log, destroyCount log v ≤ 1) ∧
  (∀ v ∈ destroyedIds log, v ∈ createdIds log) ∧
  Event.garbage ∉ log
```

```lean
-- lean/ToyDropFlags/Basic.lean:137-138
def NoLeak (log : List Event) : Prop :=
  ∀ v ∈ createdIds log, 1 ≤ destroyCount log v
```

Events: `create v` (a value with id `v` was written), `consume v` (ownership handed to a consumer, a sink or a callee, which then destroys it, so a hand-off counts as a destruction), `drop v` (its destructor ran), `garbage` (a destructor or consumer ran on never-written memory). The order of events is not checked. NoDoubleDrop: positive `noDoubleDrop_pos`; negatives `noDoubleDrop_neg_afterConsume`, `noDoubleDrop_neg_garbage`, `noDoubleDrop_neg_uncreated`. NoLeak: positive `noLeak_pos`; negative `noLeak_neg`.

#### Source programs, analyses and the move checker

```lean
-- lean/ToyDropFlags/Source.lean:27-35
inductive SNode where
  | init (p : Place) (next : Nat)
  | move (p : Place) (next : Nat)
  | branch (l₁ l₂ : Nat)
  | call (args : List Place) (dest : Option Place) (next unwind : Nat)
  | ret
  | resume
  | abort
  deriving DecidableEq, Repr
```

Node `0` is the entry. There are no explicit drops: `ret` (normal return) and `resume` (continue unwinding) are the **drop points**, at which every still-owned part of every local must be destroyed. `init` covers first initialization and re-initialization after a move.

```lean
-- lean/ToyDropFlags/Source.lean:38-41
structure SProg where
  locals : List Ty
  nodes : List SNode
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyDropFlags/Source.lean:55-57
def Forward (s : SProg) : Prop :=
  0 < s.nodes.length ∧
  ∀ i < s.nodes.length, ∀ j ∈ (s.node i).succs, i < j ∧ j < s.nodes.length
```

Positive `forward_pos` (`progJoin`); negative `forward_neg` (`progLoop`). The may-init and must-init analyses (`mayInit s g i a`, `mustInit s g i a`) are one forward pass in node order along index-increasing edges from forward-reachable predecessors; may: union, must: intersection; entry: no atoms; a node that is not forward-reachable gets may = no atoms and must = all atoms. Edge transfer: `init p` adds `atomsOf p`; `move p` removes `killSet g p` (at granularity `fine`: `atomsOf p`); a call removes its arguments' atoms on both edges and adds its destination's atoms on the normal edge. On a forward program these have their path meaning (some / every path from the entry); on other programs they describe index-increasing paths (`forwardReachable_ignores_backward_index_edges`).

```lean
-- lean/ToyDropFlags/Source.lean:67-71
inductive Granularity where
  | fine
  | wholeKill
  | wholeKeep
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyDropFlags/Source.lean:74-78
def killSet (ls : List Ty) (g : Granularity) (p : Place) : List Place :=
  match g with
  | .fine => atomsOf ls p
  | .wholeKill => atomsOf ls ⟨p.loc, []⟩
  | .wholeKeep => if p.path = [] then atomsOf ls p else []
```

`killSet ls g p` is the set of atoms whose tracked state a move of `p` clears at granularity `g`: at `fine`, exactly the atoms overlapping `p` (`atomsOf ls p`); at `wholeKill`, all atoms of `p`'s local (a move of any part of a local is tracked as a move of the whole local); at `wholeKeep`, the atoms of `p` if `p` is a whole local and none otherwise (a move of a proper part of a local is not tracked). Initializations are tracked per atom at every granularity. `wholeKill` and `wholeKeep` occur in the counterexamples R4c-kill and R4c-keep (as the analysis granularity of `stdMap`, or as `FlagConfig.gran`) and in their supporting lemma `flagConfig_gran_inert_on_progPartial`; all other results, counterexamples and witnesses in this package use `fine`.

```lean
-- lean/ToyDropFlags/Source.lean:99-105
def reachableAux (s : SProg) : Nat → List Bool → List Bool
  | 0, acc => acc
  | k + 1, acc =>
      let j := acc.length
      let r := j = 0 ||
        (List.range j).any fun i => acc.getD i false && (s.node i).succs.contains j
      reachableAux s k (acc ++ [r])
```

```lean
-- lean/ToyDropFlags/Source.lean:108
def reachList (s : SProg) : List Bool := reachableAux s s.nodes.length []
```

```lean
-- lean/ToyDropFlags/Source.lean:114
def ForwardReachable (s : SProg) (j : Nat) : Bool := (reachList s).getD j false
```

`ForwardReachable s j`: node `j` is reachable from the entry along a path of index-increasing edges (normal or unwind edges, computed in one pass in node order). For a forward program every edge is index-increasing, so this is ordinary reachability in the control-flow graph; for other programs it can miss nodes reachable through an edge to a smaller or equal index (`forwardReachable_ignores_backward_index_edges`). Positive `forwardReachable_pos` (node 2 of `progJoin`); negative `forwardReachable_neg` (a node with no incoming edge).

```lean
-- lean/ToyDropFlags/Source.lean:175-176
def PlacesAreMovePaths (s : SProg) : Prop :=
  ∀ i < s.nodes.length, ∀ p ∈ (s.node i).places, isMovePlace s.locals p = true
```

```lean
-- lean/ToyDropFlags/Source.lean:186-193
def MovesFromInit (s : SProg) : Prop :=
  ∀ i < s.nodes.length,
    match s.node i with
    | .move p _ => ∀ a ∈ atomsOf s.locals p, mustInit s .fine i a = true
    | .call args _ _ _ =>
        (∀ p ∈ args, ∀ a ∈ atomsOf s.locals p, mustInit s .fine i a = true) ∧
        pairwiseDisjoint args = true
    | _ => True
```

```lean
-- lean/ToyDropFlags/Source.lean:198-205
def InitsIntoUninit (s : SProg) : Prop :=
  ∀ i < s.nodes.length,
    match s.node i with
    | .init p _ => ∀ a ∈ atomsOf s.locals p, mayInit s .fine i a = false
    | .call args (some d) _ _ =>
        ∀ a ∈ atomsOf s.locals d,
          mayInit s .fine i a = false ∨ (args.any fun q => q.overlaps a) = true
    | _ => True
```

```lean
-- lean/ToyDropFlags/Source.lean:233-234
def NoNormalPathToResume (s : SProg) : Prop :=
  ∀ i < s.nodes.length, NormalReachable s i = true → s.node i ≠ .resume
```

```lean
-- lean/ToyDropFlags/Source.lean:253-254
def MoveChecked (s : SProg) : Prop :=
  PlacesAreMovePaths s ∧ MovesFromInit s ∧ InitsIntoUninit s
```

Positive/negative examples: `placesAreMovePaths_pos`/`placesAreMovePaths_neg`; `movesFromInit_pos`/`movesFromInit_neg` (use after move) and `movesFromInit_neg_duplicateCallArg` (the same value passed twice to one call); `initsIntoUninit_pos`/`initsIntoUninit_neg`; `noNormalPathToResume_pos` (`progCleanup`, `progMultiStepCleanup` with two-node cleanup code, `progUnwindToRet` whose unwind edge enters normal code)/`noNormalPathToResume_neg` (`progResumeNormal`). `NormalReachable s j`: `j` is reachable from the entry along index-increasing normal edges (no call's unwind edge). `MoveChecked s` (the move checker) is the conjunction `PlacesAreMovePaths s ∧ MovesFromInit s ∧ InitsIntoUninit s`; the counterexample statements R4a–R4d and R6 state it for their programs. Positive `moveChecked_pos` (`progJoin`); negative `moveChecked_neg` (`progUseAfterMove`).

#### Target semantics and exactly-once

Target nodes add `goto`, `setFlags`, `test a ifSet ifClear`, `drop a next unwind` (the drop glue of atom `a`; `unwind = none`: no landing pad) and `stuck`. Machine state: `pc`, `unwinding`, `mem : Place → Option Nat` (unit ↦ id last written; moves do not clear memory), `flags` (all `false` initially), a fresh-id counter and the log. `init` writes fresh ids; `move` logs `consume` per unit; a call consumes its arguments, then on panic goes to its unwind target with `unwinding := true`, otherwise writes its destination; `drop a` logs one `drop` per unit of `a` (or `garbage`), then: no panic ⇒ next; panic while unwinding under `PanicRule.abort` ⇒ outcome `aborted`; otherwise ⇒ the unwind target if any (setting `unwinding`), else outcome `unwound`. `ret` ⇒ `returned`, `resume` ⇒ `unwound`, `abort` ⇒ `aborted`, `stuck` ⇒ `stuck`.

The machine state, and the initial state of a run (all flags `false`, no memory written, empty log):

```lean
-- lean/ToyDropFlags/Target.lean:82-88
structure Mach (L : Type) where
  pc : L
  unwinding : Bool
  mem : Place → Option Nat
  flags : Place → Bool
  fresh : Nat
  log : List Event
```

```lean
-- lean/ToyDropFlags/Target.lean:157-159
def initMach {L : Type} (P : TProg L) : Mach L :=
  { pc := P.entry, unwinding := false, mem := fun _ => none, flags := fun _ => false,
    fresh := 0, log := [] }
```

```lean
-- lean/ToyDropFlags/Target.lean:56-59
inductive PanicRule where
  | abort
  | continueUnwind
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyDropFlags/Target.lean:66-72
inductive Outcome where
  | returned
  | unwound
  | aborted
  | stuck
  | outOfFuel
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyDropFlags/Target.lean:75-78
structure Result where
  outcome : Outcome
  log : List Event
  deriving DecidableEq, Repr
```

`PanicRule` fixes what a destructor panic does while the frame is already unwinding: under `abort` the run ends with outcome `aborted`; under `continueUnwind` it is handled like any other destructor panic (to the drop's unwind target if there is one, otherwise outcome `unwound`; drops in cleanup code have no unwind target). Outcomes: `returned` (normal return), `unwound` (a completed unwind: the panic left the frame), `aborted` (process abort), `stuck` (an ill-formed program point, `TNode.stuck`), `outOfFuel` (the step bound was exhausted). `returned`, `unwound` and `aborted` count as termination; `returned` and `unwound` are the complete outcomes:

```lean
-- lean/ToyDropFlags/Target.lean:288-290
def Outcome.complete : Outcome → Bool
  | .returned | .unwound => true
  | _ => false
```

```lean
-- lean/ToyDropFlags/Target.lean:293-295
def Outcome.terminated : Outcome → Bool
  | .returned | .unwound | .aborted => true
  | _ => false
```

```lean
-- lean/ToyDropFlags/Target.lean:301-302
def ExactlyOnce (r : Result) : Prop :=
  NoDoubleDrop r.log ∧ (r.outcome.complete = true → NoLeak r.log)
```

Positive `exactlyOnce_pos`, `exactlyOnce_pos_aborted`; negative `exactlyOnce_neg_leak`, `exactlyOnce_neg_double`. Every choice point reads one input bit; the exhaustive run tree agrees with `run` on every input:

```lean
-- lean/ToyDropFlags/Target.lean:251-252
theorem run_eq_follow {L : Type} (rule : PanicRule) (P : TProg L) (fuel : Nat)
    (inp : List Bool) : run rule P fuel inp = (explore rule P fuel).follow inp := …
```

#### Elaboration

```lean
-- lean/ToyDropFlags/Elab.lean:27-31
inductive Decision where
  | drop
  | skip
  | test
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyDropFlags/Elab.lean:35-36
def stdDecision (may must : Bool) : Decision :=
  if !may then .skip else if must then .drop else .test
```

```lean
-- lean/ToyDropFlags/Elab.lean:39-40
def stdMap (s : SProg) (g : Granularity) : Nat → Place → Decision :=
  fun i a => stdDecision (mayInit s g i a) (mustInit s g i a)
```

```lean
-- lean/ToyDropFlags/Elab.lean:43-45
def overrideAt (d : Nat → Place → Decision) (i : Nat) (a : Place) (x : Decision) :
    Nat → Place → Decision :=
  fun j b => if j = i ∧ b = a then x else d j b
```

`overrideAt d i a x` is the decision map `d` with the single entry for atom `a` at node `i` replaced by `x` (R3, R4a and R4a-skip compare the standard map with such one-entry overrides).

```lean
-- lean/ToyDropFlags/Elab.lean:51-54
structure FlagConfig where
  gran : Granularity := .fine
  clearArgsBeforeCall : Bool := true
  initSetsFlags : Nat → Bool := fun _ => true
```

```lean
-- lean/ToyDropFlags/Elab.lean:57
def FlagConfig.std : FlagConfig := {}
```

`elaborate fc d s` keeps the source CFG; after `init p` (if `fc.initSetsFlags i`) it sets the flags of `atomsOf p`; after `move p` it clears `killSet fc.gran p`; before a call it clears the arguments' flags (if `fc.clearArgsBeforeCall`; otherwise on the normal edge); on a call's normal edge it sets the destination's flags. At each `ret`/`resume` node `i` it emits a ladder over all atoms in reverse atom order: `d i a = drop` ⇒ unconditional drop, `skip` ⇒ nothing, `test` ⇒ a flag test guarding a drop. Drops in a `ret` ladder have an unwind successor (a cleanup ladder for the atoms not yet visited, same decisions, ending in `resume`); drops in cleanup code have none. A source index outside the program elaborates to `stuck` (`progOOB_stuck`). `FlagConfig.std` (`{}`) is the standard flag maintenance and `stdElab s = elaborate .std (stdMap s .fine) s`.

```lean
-- lean/ToyDropFlags/Elab.lean:161
def fuelFor (s : SProg) : Nat := 3 * s.nodes.length + 4 * (allAtoms s.locals).length + 4
```

```lean
-- lean/ToyDropFlags/Elab.lean:164-166
def runElab (rule : PanicRule) (fc : FlagConfig) (d : Nat → Place → Decision) (s : SProg)
    (inp : List Bool) : Result :=
  run rule (elaborate fc d s) (fuelFor s) inp
```

```lean
-- lean/ToyDropFlags/Elab.lean:172-174
def ElabCorrect (rule : PanicRule) (fc : FlagConfig) (d : Nat → Place → Decision) (s : SProg) :
    Prop :=
  ∀ inp, ExactlyOnce (runElab rule fc d s inp) ∧ (runElab rule fc d s inp).outcome.terminated
```

```lean
-- lean/ToyDropFlags/Elab.lean:177-178
def isDropPoint (s : SProg) (i : Nat) : Bool :=
  s.node i == .ret || s.node i == .resume
```

```lean
-- lean/ToyDropFlags/Elab.lean:182-185
def Compatible (may must : Bool) : Decision → Bool
  | .test => true
  | .drop => must
  | .skip => !may
```

```lean
-- lean/ToyDropFlags/Elab.lean:196-198
def AllCompatible (s : SProg) (d : Nat → Place → Decision) : Prop :=
  ∀ i < s.nodes.length, isDropPoint s i = true → ForwardReachable s i = true →
    ∀ a ∈ allAtoms s.locals, Compatible (mayInit s .fine i a) (mustInit s .fine i a) (d i a) = true
```

```lean
-- lean/ToyDropFlags/Elab.lean:206-209
def flagSet (s : SProg) (d : Nat → Place → Decision) : List Place :=
  (allAtoms s.locals).filter fun a =>
    (List.range s.nodes.length).any fun i =>
      isDropPoint s i && ForwardReachable s i && d i a == .test
```

`ElabCorrect`: positive `elabCorrect_pos`, negative `elabCorrect_neg`. `AllCompatible`: positive `allCompatible_pos`, negative `allCompatible_neg`. `stdDecision_compatible`: the standard decision is always compatible. `staticChoice_compatible_iff`: some static decision is compatible iff not (may-init and not must-init). `flagSet` examples: `flagSet_progJoin = [x]`, `flagSet_progPartial = []`, `flagSet_progShare = [x0, x1]`, `flagSet_ignores_unreachable_test`.

#### Example programs

`x = ⟨0,[]⟩`, `x0 = ⟨0,[false]⟩`, `x1 = ⟨0,[true]⟩`, `y = ⟨1,[]⟩`; `pairT = pair false leaf leaf`, `dropT = pair true leaf leaf`. The node lists are renderings of the Lean definitions in `lean/ToyDropFlags/Examples.lean` and `lean/ToyDropFlags/Counterexamples.lean` (`i: node`; `call args dest normal/unwind`).

| Program | Locals | Nodes |
| :--- | :--- | :--- |
| `progJoin` | `[leaf]` | 0: init x→1; 1: branch 2 3; 2: move x→3; 3: ret |
| `progCleanup` | `[leaf]` | 0: init x→1; 1: call [] none 2/4; 2: call [x] none 3/4; 3: ret; 4: resume |
| `progPartial` | `[pairT]` | 0: init x→1; 1: move x0→2; 2: ret |
| `progReinit` | `[leaf]` | 0: init x→1; 1: move x→2; 2: branch 3 4; 3: init x→4; 4: ret |
| `progUnwind` | `[pairT]` | 0: init x→1; 1: call [] none 2/3; 2: ret; 3: resume |
| `progShare` | `[pairT]` | 0: init x→1; 1: branch 2 4; 2: move x0→3; 3: move x1→4; 4: ret |
| `progMultiStepCleanup` | `[pairT]` | 0: init x→1; 1: call [] none 4/2; 2: move x0→3; 3: resume; 4: ret |
| `progUnwindToRet` | `[pairT]` | 0: init x→1; 1: call [] none 2/2; 2: ret |
| `progPartialFlag` | `[pairT]` | 0: branch 1 4; 1: init x→2; 2: branch 3 4; 3: move x0→4; 4: ret |
| `progLoop` | `[leaf]` | 0: init x→1; 1: branch 0 2; 2: ret (back edge) |
| `progLoopMove` | `[leaf]` | 0: init x→1; 1: move x→2; 2: branch 1 3; 3: ret (back edge) |
| `progDropStruct` | `[dropT]` | 0: init x→1; 1: move x0→2; 2: ret |
| `progInitInsideDrop` | `[dropT]` | 0: init x0→1; 1: ret |
| `progUseAfterMove` | `[leaf]` | 0: init x→1; 1: move x→2; 2: move x→3; 3: ret |
| `progOverwrite` | `[leaf]` | 0: init x→1; 1: init x→2; 2: ret |
| `progResumeNormal` | `[leaf, leaf]` | 0: init x→1; 1: init y→2; 2: resume |
| `progIllTyped` | `[leaf]` | 0: branch 1 2; 1: init ⟨0,[true]⟩→2; 2: ret |
| `progJoinOff` | `[leaf]` | 0: init x→1; 1: branch 2 3; 2: move x→3; 3: branch 4 4; 4: ret |
| `progMoved` | `[leaf]` | 0: init x→1; 1: move x→2; 2: ret |
| `progKept` | `[leaf]` | 0: init x→1; 1: ret |
| `progOOB` | `[leaf]` | 0: init x→99 |
| `progDuplicateCallArg` | `[leaf]` | 0: init x→1; 1: call [x, x] none 2/3; 2: ret; 3: resume |

#### Further definitions cited by name

Verbatim quotes of the remaining package definitions that this report names (in prose, tables or statements), including the example programs rendered in the table above. Helper functions that occur only inside these bodies are not quoted; their definitions are covered by the closure hashes of the recorded statements that use them (see **Evidence**).

```lean
-- lean/ToyDropFlags/Basic.lean:48-53
def Ty.isMovePath : Ty → Path → Bool
  | _, [] => true
  | .leaf, _ :: _ => false
  | .pair true _ _, _ :: _ => false
  | .pair false a _, false :: p => a.isMovePath p
  | .pair false _ b, true :: p => b.isMovePath p

-- lean/ToyDropFlags/Basic.lean:78
def allAtoms (ls : List Ty) : List Place := placesFrom Ty.atoms 0 ls

-- lean/ToyDropFlags/Basic.lean:81-82
def unitsUnder (ls : List Ty) (p : Place) : List Place :=
  (allUnits ls).filter (p.covers ·)

-- lean/ToyDropFlags/Basic.lean:86-87
def atomsOf (ls : List Ty) (p : Place) : List Place :=
  (allAtoms ls).filter (p.overlaps ·)

-- lean/ToyDropFlags/Basic.lean:90-93
def isMovePlace (ls : List Ty) (p : Place) : Bool :=
  match ls[p.loc]? with
  | some t => t.isMovePath p.path
  | none => false
```

```lean
-- lean/ToyDropFlags/Source.lean:150-151
def mayInit (s : SProg) (g : Granularity) (j : Nat) (a : Place) : Bool :=
  ((analysis s g true).getD j []).contains a

-- lean/ToyDropFlags/Source.lean:157-158
def mustInit (s : SProg) (g : Granularity) (j : Nat) (a : Place) : Bool :=
  ((analysis s g false).getD j (allAtoms s.locals)).contains a

-- lean/ToyDropFlags/Source.lean:179-181
def pairwiseDisjoint : List Place → Bool
  | [] => true
  | p :: ps => ps.all (fun q => !p.overlaps q) && pairwiseDisjoint ps

-- lean/ToyDropFlags/Source.lean:226
def NormalReachable (s : SProg) (j : Nat) : Bool := (normalReachAux s s.nodes.length []).getD j false
```

```lean
-- lean/ToyDropFlags/Target.lean:34-47
inductive TNode (L : Type) where
  | init (p : Place) (next : L)
  | move (p : Place) (next : L)
  | call (args : List Place) (dest : Option Place) (next unwind : L)
  | branch (l₁ l₂ : L)
  | goto (l : L)
  | setFlags (us : List (Place × Bool)) (next : L)
  | test (a : Place) (ifSet ifClear : L)
  | drop (a : Place) (next : L) (unwind : Option L)
  | ret
  | resume
  | abort
  | stuck
  deriving Repr

-- lean/ToyDropFlags/Target.lean:50-53
structure TProg (L : Type) where
  locals : List Ty
  entry : L
  node : L → TNode L

-- lean/ToyDropFlags/Target.lean:175-176
def run {L : Type} (rule : PanicRule) (P : TProg L) (fuel : Nat) (inp : List Bool) : Result :=
  runAux rule P fuel inp (initMach P)

-- lean/ToyDropFlags/Target.lean:213-214
def explore {L : Type} (rule : PanicRule) (P : TProg L) (fuel : Nat) : RunTree :=
  exploreAux rule P fuel (initMach P)
```

```lean
-- lean/ToyDropFlags/Elab.lean:153-154
def elaborate (fc : FlagConfig) (d : Nat → Place → Decision) (s : SProg) : TProg Lbl :=
  { locals := s.locals, entry := .src 0, node := elabNode fc d s }

-- lean/ToyDropFlags/Elab.lean:157
def stdElab (s : SProg) : TProg Lbl := elaborate .std (stdMap s .fine) s
```

```lean
-- lean/ToyDropFlags/Examples.lean:15
def x : Place := ⟨0, []⟩

-- lean/ToyDropFlags/Examples.lean:17
def x0 : Place := ⟨0, [false]⟩

-- lean/ToyDropFlags/Examples.lean:19
def x1 : Place := ⟨0, [true]⟩

-- lean/ToyDropFlags/Examples.lean:21
def y : Place := ⟨1, []⟩

-- lean/ToyDropFlags/Examples.lean:24
def pairT : Ty := .pair false .leaf .leaf

-- lean/ToyDropFlags/Examples.lean:26
def dropT : Ty := .pair true .leaf .leaf

-- lean/ToyDropFlags/Examples.lean:31-32
def progJoin : SProg :=
  { locals := [.leaf], nodes := [.init x 1, .branch 2 3, .move x 3, .ret] }

-- lean/ToyDropFlags/Examples.lean:35-37
def progCleanup : SProg :=
  { locals := [.leaf],
    nodes := [.init x 1, .call [] none 2 4, .call [x] none 3 4, .ret, .resume] }

-- lean/ToyDropFlags/Examples.lean:40-41
def progPartial : SProg :=
  { locals := [pairT], nodes := [.init x 1, .move x0 2, .ret] }

-- lean/ToyDropFlags/Examples.lean:44-45
def progReinit : SProg :=
  { locals := [.leaf], nodes := [.init x 1, .move x 2, .branch 3 4, .init x 4, .ret] }

-- lean/ToyDropFlags/Examples.lean:48-49
def progUnwind : SProg :=
  { locals := [pairT], nodes := [.init x 1, .call [] none 2 3, .ret, .resume] }

-- lean/ToyDropFlags/Examples.lean:52-53
def progLoop : SProg :=
  { locals := [.leaf], nodes := [.init x 1, .branch 0 2, .ret] }

-- lean/ToyDropFlags/Examples.lean:56-57
def progDropStruct : SProg :=
  { locals := [dropT], nodes := [.init x 1, .move x0 2, .ret] }

-- lean/ToyDropFlags/Examples.lean:60-61
def progUseAfterMove : SProg :=
  { locals := [.leaf], nodes := [.init x 1, .move x 2, .move x 3, .ret] }

-- lean/ToyDropFlags/Examples.lean:64-65
def progOverwrite : SProg :=
  { locals := [.leaf], nodes := [.init x 1, .init x 2, .ret] }

-- lean/ToyDropFlags/Examples.lean:68-69
def progResumeNormal : SProg :=
  { locals := [.leaf, .leaf], nodes := [.init x 1, .init y 2, .resume] }

-- lean/ToyDropFlags/Examples.lean:72-73
def progShare : SProg :=
  { locals := [pairT], nodes := [.init x 1, .branch 2 4, .move x0 3, .move x1 4, .ret] }

-- lean/ToyDropFlags/Examples.lean:77-79
def progMultiStepCleanup : SProg :=
  { locals := [pairT],
    nodes := [.init x 1, .call [] none 4 2, .move x0 3, .resume, .ret] }

-- lean/ToyDropFlags/Examples.lean:82-83
def progUnwindToRet : SProg :=
  { locals := [pairT], nodes := [.init x 1, .call [] none 2 2, .ret] }

-- lean/ToyDropFlags/Examples.lean:86
def progOOB : SProg := { locals := [.leaf], nodes := [.init x 99] }

-- lean/ToyDropFlags/Examples.lean:89-90
def progDuplicateCallArg : SProg :=
  { locals := [.leaf], nodes := [.init x 1, .call [x, x] none 2 3, .ret, .resume] }
```

```lean
-- lean/ToyDropFlags/Counterexamples.lean:224-225
def progPartialFlag : SProg :=
  { locals := [pairT], nodes := [.branch 1 4, .init x 2, .branch 3 4, .move x0 4, .ret] }

-- lean/ToyDropFlags/Counterexamples.lean:321-322
def progLoopMove : SProg :=
  { locals := [.leaf], nodes := [.init x 1, .move x 2, .branch 1 3, .ret] }

-- lean/ToyDropFlags/Counterexamples.lean:325-326
def progInitInsideDrop : SProg :=
  { locals := [dropT], nodes := [.init x0 1, .ret] }

-- lean/ToyDropFlags/Counterexamples.lean:363
def badPlace : Place := ⟨0, [true]⟩

-- lean/ToyDropFlags/Counterexamples.lean:367-368
def progIllTyped : SProg :=
  { locals := [.leaf], nodes := [.branch 1 2, .init badPlace 2, .ret] }

-- lean/ToyDropFlags/Counterexamples.lean:396-397
def progJoinOff : SProg :=
  { locals := [.leaf], nodes := [.init x 1, .branch 2 3, .move x 3, .branch 4 4, .ret] }

-- lean/ToyDropFlags/Counterexamples.lean:400
def progMoved : SProg := { locals := [.leaf], nodes := [.init x 1, .move x 2, .ret] }

-- lean/ToyDropFlags/Counterexamples.lean:403
def progKept : SProg := { locals := [.leaf], nodes := [.init x 1, .ret] }
```

## Findings

Common hypotheses ("the hypotheses of R1"): `hfwd : Forward s`, `hplaces : PlacesAreMovePaths s`, `hmoves : MovesFromInit s`, `hinits : InitsIntoUninit s`, `hclean : NoNormalPathToResume s`. In every hypothesis ledger, *tight* means: a fully proved counterexample theorem (named) states that every other hypothesis holds, the named hypothesis fails, and the conclusion fails; the class of that witness is recorded. Every hypothesis of every result in this package is tight in this sense.

### How the sufficiency and continue-unwinding theorems are proved

R2s (and with it R1, R2, R7L) and R5 are proved by one invariant-based simulation in `lean/ToyDropFlags/Sufficiency.lean`, culminating in `runElab_good`. For a forward program with valid move paths and `MovesFromInit`, and a decision map compatible with the fine analyses at every forward-reachable drop point, every run under either panic rule is followed node by node. At each source node `i` the run carries an initialized-atom set `P` with: `P` within the may-init set and containing the must-init set at `i` (soundness of the one-pass analyses along every edge, `analysis_step`); every unit of an atom in `P` holds a created, not yet destroyed value, and every unit of an atom outside `P` is unwritten or holds a destroyed value; the log has no double destruction; the drop flags equal membership in `P`; the run is unwinding unless `i` is normal-reachable; and, under `InitsIntoUninit`, every created value is destroyed or held by a unit of an atom in `P`. A drop ladder then drops exactly the atoms of `P` once each (a compatible unconditional drop needs must-init, so the atom is in `P`; a compatible skip needs not may-init, so it is not; a test reads the flag), panics inside a ladder go to a cleanup ladder for the remaining atoms or end the run, and the step count stays within `fuelFor s` (at most three target steps per source node on an index-increasing path, at most two per atom over both ladders, plus two). Under the abort rule, `NoNormalPathToResume` excludes a completed unwind from a `resume` ladder reached without unwinding, the remaining case in which a complete run could leak.

Basis: execution (Lean kernel check)

### R1: `stdElab_correct_of_forward_moveChecked_noNormalPathToResume`

**Kind:** theorem. **Tier:** T1. **Depth:** substantive. **Proof status:** proved (from R2s).

Lean statement (verbatim source quote):

```lean
-- lean/ToyDropFlags/Results.lean:47-50
theorem stdElab_correct_of_forward_moveChecked_noNormalPathToResume (s : SProg)
    (hfwd : Forward s) (hplaces : PlacesAreMovePaths s) (hmoves : MovesFromInit s)
    (hinits : InitsIntoUninit s) (hclean : NoNormalPathToResume s) :
    ElabCorrect .abort .std (stdMap s .fine) s := …
```

Unfolded rendering of the conclusion, with `ElabCorrect` and `ExactlyOnce` expanded (re-elaborated and checked definitionally equal):

```lean
∀ inp : List Bool,
  (NoDoubleDrop (runElab .abort .std (stdMap s .fine) s inp).log ∧
    ((runElab .abort .std (stdMap s .fine) s inp).outcome.complete = true → NoLeak (runElab .abort .std (stdMap s .fine) s inp).log)) ∧
  (runElab .abort .std (stdMap s .fine) s inp).outcome.terminated = true
```

**Plain claim.** Assume that a destructor panic during unwinding aborts the process, and let s be a forward (acyclic, topologically numbered) toy program that only mentions valid move paths, moves only definitely-initialized places (call arguments pairwise disjoint), initializes only definitely-uninitialized places, and has no resume node reachable from the entry along normal edges only. Then the standard drop elaboration (flags set at init, cleared at move and, for call arguments, before the call, set for a call's destination on its normal edge; unconditional drop where must-init, nothing where not may-init, flag test otherwise; cleanup drops without landing pads) of s is elaboration-correct: on every input its run terminates (returns, completes an unwind, or aborts) and is exactly-once, i.e. destroys no value twice, destroys no uncreated value, runs no destructor on unwritten memory, and, if it returns or completes an unwind, destroys every created value.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hfwd : Forward s` | the one-pass initialization analyses follow index-increasing edges only, which are all edges exactly when the program is forward (acyclic, topologically numbered) | tight | `stdElab_fails_without_forward` | a 1-local (leaf), 3-node program with one back edge (progLoop) |
| `hplaces : PlacesAreMovePaths s` | every mentioned place follows its local's type and never enters a struct with its own destructor, so the analysis's atoms match the units written and destroyed | tight | `stdElab_fails_without_placesAreMovePaths` | a 1-local, 3-node forward program whose local is a struct with its own destructor and two leaf fields (progDropStruct) |
| `hmoves : MovesFromInit s` | no use after move: every moved place (and call argument) is must-init, and call arguments are pairwise disjoint | tight | `stdElab_fails_without_movesFromInit` | a 1-local (leaf), 4-node forward program (progUseAfterMove) |
| `hinits : InitsIntoUninit s` | no overwrite of an owned value: every initialized place (and call destination not overlapped by an argument) is not may-init | tight | `stdElab_fails_without_initsIntoUninit` | a 1-local (leaf), 3-node forward program (progOverwrite) |
| `hclean : NoNormalPathToResume s` | no resume node is reachable from the entry along normal edges only, so a resume ladder (whose drops have no landing pad) runs only while unwinding, where a destructor panic aborts | tight | `stdElab_fails_without_noNormalPathToResume` | a 2-local (two leaves), 3-node forward program (progResumeNormal) |

**Non-vacuity witness.** progCleanup (two calls sharing one cleanup node, the second consuming x) satisfies all five hypotheses and its standard elaboration tests one flag on the cleanup path; progMultiStepCleanup (cleanup code of two nodes) also satisfies them. The conclusion is kernel-checked on all runs of eight example programs (progJoin, progCleanup, progPartial, progReinit, progUnwind, progShare, progMultiStepCleanup, progUnwindToRet). (Lean: `exactlyOnce_hypotheses_hold_progCleanup`, `exactlyOnce_hypotheses_hold_progMultiStepCleanup`)

**Tier rationale.** T1. The panic-free part is mechanized elsewhere for other languages: RustCompCert (Rocq, complete) proves its drop elaboration correct by forward simulation, and Fukala's thesis (Coq; complete without tuples) proves a flag-based elaboration correct; neither models panics, unwinding or cleanup code. The combination stated here — cleanup ladders on unwind edges, landing-pad-free cleanup drops, the abort rule for destructor panics during unwinding, and atomic structs with their own destructor — is informal folklore (RFC 320, rustc's drop elaboration); no mechanized statement of it was found.

**Prior art.**

- RFC 320 'Non-zeroing dynamic drop', rust-lang/rfcs f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/0320-nonzeroing-dynamic-drop.md lines 6-15 (stack-local boolean flags for 'dynamic drop obligations'), lines 99-114 (drop obligations: a Drop type is one obligation, otherwise the union of its fields'; removed when moved, consumed by a call, or at scope end), lines 116-142 (dynamic obligations at a merge point = union minus intersection of the predecessors' sets), lines 144-155 (subsection 'Stack-local drop flags'; lines 153-155: 'we do not specify the precise set of boolean flags that are injected') [design document, historical; informal]
- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_transform/src/elaborate_drops.rs lines 165-188 (drop_style: (maybe_init, maybe_uninit) = (false, _) => Dead, (true, false) => Static, (true, true) => Conditional/Open) and lines 290-334 (collect_drop_flags; lines 310-312 create a flag iff maybe_init && maybe_uninit at a drop) [source; prose only]
- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_transform/src/elaborate_drops.rs lines 424-431 (all flags set false at function start), 433-451 (call destination flags set at the start of the return target), 464-520 (per-location flag effects inserted at the location, i.e. before the statement/terminator); compiler/rustc_mir_dataflow/src/drop_flag_effects.rs lines 108-137 (drop_flag_effects_for_location: moves out => Absent) and 139-150 (for_location_inits: InitKind::Unconditional => Present, InitKind::OnReturn => no effect at the call) [source; prose only]
- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_transform/src/elaborate_drop.rs lines 49-56 and 66-71 (Unwind::InCleanup: 'Already in an unwind path, any panic will cause an abort.'; into_action => UnwindAction::Terminate(UnwindTerminateReason::InCleanup)); elaborate_drops.rs lines 359-375 (drops in cleanup blocks get Unwind::InCleanup); compiler/rustc_middle/src/mir/syntax.rs lines 657-683 (cleanup blocks: every unwind field must be Terminate or Unreachable; Return is not allowed; blocks reachable from cleanup blocks are cleanup) and 1010-1038 (UnwindAction::Terminate 'Terminates the execution if unwind happens'); compiler/rustc_mir_transform/src/validate.rs lines 246-275 (the validator rejects Cleanup or Continue unwind actions in cleanup blocks); library/core/src/panicking.rs lines 356-370 (lang item panic_in_cleanup: non-unwinding panic 'panic in a destructor during cleanup') [source; prose only]
- J. Wu, Y. Wang, L. Yu, L. Meng, 'RustCompCert: A Verified and Verifying Compiler for a Sequential Subset of Rust', arXiv:2602.07455v1 (7 Feb 2026; companion: 'End-to-end Compositional Verification of Program Safety through Verified and Verifying Compilation', arXiv:2510.10015v1); Rocq development github.com/SJTU-PLV/CompCert commit e3d03ed822a7aaf452b7022c347187ed1efc1c12 (branch rust-verified-compiler): rustfrontend/InitAnalysis.v lines 83-84 (maybe-init and maybe-uninit as Kildall fixpoints over a possibly cyclic CFG); rustfrontend/ElaborateDrop.v lines 33-52 (a drop flag for a place that is may-init and not must-init at a drop), 147-181 (flag-guarded drop, flag reset before the drop; once a place has a flag, the guarded form is used at all its drops), 253-276 (flag updates at assignments, moves and calls); rustfrontend/ElaborateDropProof.v lines 4492-4513 (transl_program_correct: forward simulation from the ownership-tracking semantics to the explicit-drop semantics; no Admitted/admit in the file; not compiled here). No unwind, panic or cleanup construct occurs in rustfrontend/ (a call node has one successor). No necessity or minimality statement [mechanized prior art]
- V. Fukala, 'Formalization of Rust Drop Elaboration', Bachelor thesis, Programming Language Foundations Lab, ETH Zurich, August 5, 2024 (supervisors I. van Bakel, R. Jung), PDF https://ethz.ch/content/dam/ethz/special-interest/infk/inst-pls/plf-dam/documents/StudentProjects/BachelorTheses/2024-Viktor-Thesis.pdf: a structured language (if, while, calls, tuples; no control-flow graphs, section 3) with flag-based drop elaboration in Coq; a complete correctness proof for a scalar-only version, and a proof relying on unproved lemmas for tuples (sections 5.4, 6, Appendix A); unwinding left to future work (section 6.1). The Coq repository named in Appendix A requires sign-in and was not inspected [mechanized prior art, partly]
- T. Ramananandro, G. Dos Reis, X. Leroy, 'A Mechanized Semantics for C++ Object Construction and Destruction, with Applications to Resource Management', POPL 2012, pp. 521-532, DOI 10.1145/2103656.2103718 (also ACM SIGPLAN Notices 47(1), DOI 10.1145/2103621.2103718): Coq-mechanized construction/destruction semantics ('every object ... is constructed exactly once', reverse-order destruction); no moves, no conditional initialization, exceptions not modelled [mechanized; related]
- A. Weiss, O. Gierczak, D. Patterson, A. Ahmed, 'Oxide: The Essence of Rust', arXiv:1903.00982v4 (2021), DOI 10.48550/arXiv.1903.00982: T-Drop is a weakening-style typing rule; destructors, panics and unwinding are not modelled [related formal work; no drop elaboration]

**Design question.** What must drop elaboration maintain for exactly-once destruction on normal and cleanup edges?

**Non-claims.** See **Boundaries**, common non-claims and the R1 entry.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) for any reading of this result as a statement about a real system. Such a reading relies on the bridges "Standard decision and rustc drop styles", "Flag maintenance", "Cleanup code and MIR cleanup blocks", "Abort rule in rustc and C++", "Drop glue as one step" under **Modeling bridges** below, which state the correspondence, its reasoning and the known mismatches; the kernel check is about the toy model and neither establishes nor refutes these correspondences (model–system relation: none proved).

### R2s: `elabCorrect_of_allCompatible_of_forward_moveChecked_noNormalPathToResume`

**Kind:** theorem. **Tier:** T1. **Depth:** substantive. **Proof status:** proved.

Lean statement (verbatim source quote):

```lean
-- lean/ToyDropFlags/Results.lean:27-31
theorem elabCorrect_of_allCompatible_of_forward_moveChecked_noNormalPathToResume (s : SProg)
    (hfwd : Forward s) (hplaces : PlacesAreMovePaths s) (hmoves : MovesFromInit s)
    (hinits : InitsIntoUninit s) (hclean : NoNormalPathToResume s)
    (d : Nat → Place → Decision) (hcompat : AllCompatible s d) :
    ElabCorrect .abort .std d s := …
```

Unfolded rendering of the conclusion, with `ElabCorrect` and `ExactlyOnce` expanded (re-elaborated and checked definitionally equal):

```lean
∀ inp : List Bool,
  (NoDoubleDrop (runElab .abort .std d s inp).log ∧
    ((runElab .abort .std d s inp).outcome.complete = true → NoLeak (runElab .abort .std d s inp).log)) ∧
  (runElab .abort .std d s inp).outcome.terminated = true
```

**Plain claim.** Assume that a destructor panic during unwinding aborts the process, let s be a forward (acyclic, topologically numbered) toy program that only mentions valid move paths, moves only definitely-initialized places (call arguments pairwise disjoint), initializes only definitely-uninitialized places, and has no resume node reachable from the entry along normal edges only, and let d be a decision map that is compatible with the fine analyses at every forward-reachable drop point (an unconditional drop only for must-init atoms, nothing only for atoms that are not may-init, a flag test anywhere). Then the elaboration of s with the standard flag maintenance and decision map d is elaboration-correct: on every input its run terminates (returns, completes an unwind, or aborts) and is exactly-once, i.e. destroys no value twice, destroys no uncreated value, runs no destructor on unwritten memory, and, if it returns or completes an unwind, destroys every created value.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hfwd : Forward s` | the one-pass initialization analyses follow index-increasing edges only, which are all edges exactly when the program is forward (acyclic, topologically numbered) | tight | `sufficiency_fails_without_forward` | a 1-local (leaf), 3-node program with one back edge (progLoop) |
| `hplaces : PlacesAreMovePaths s` | every mentioned place follows its local's type and never enters a struct with its own destructor, so the analysis's atoms match the units written and destroyed | tight | `sufficiency_fails_without_placesAreMovePaths` | a 1-local, 3-node forward program whose local is a struct with its own destructor and two leaf fields (progDropStruct) |
| `hmoves : MovesFromInit s` | no use after move: every moved place (and call argument) is must-init, and call arguments are pairwise disjoint | tight | `sufficiency_fails_without_movesFromInit` | a 1-local (leaf), 4-node forward program (progUseAfterMove) |
| `hinits : InitsIntoUninit s` | no overwrite of an owned value: every initialized place (and call destination not overlapped by an argument) is not may-init | tight | `sufficiency_fails_without_initsIntoUninit` | a 1-local (leaf), 3-node forward program (progOverwrite) |
| `hclean : NoNormalPathToResume s` | no resume node is reachable from the entry along normal edges only, so a resume ladder (whose drops have no landing pad) runs only while unwinding, where a destructor panic aborts | tight | `sufficiency_fails_without_noNormalPathToResume` | a 2-local (two leaves), 3-node forward program (progResumeNormal) |
| `hcompat : AllCompatible s d` | the decisions agree with what the analyses guarantee at every forward-reachable drop point | tight | `sufficiency_fails_without_allCompatible` | a 1-local (leaf), 4-node forward program (progJoin) with the decision map that drops x unconditionally at the join |

**Non-vacuity witness.** progJoin with the decision map that tests x at every drop point satisfies all six hypotheses. (Lean: `sufficiency_hypotheses_hold_progJoin_testEverywhere`)

**Tier rationale.** T1, as for R1. RustCompCert's verified elaboration tests a flag at some drops where the place is must-init once a flag exists for it, i.e. a compatible non-standard decision map in this vocabulary; the general statement for every compatible map with unwinding was not found mechanized.

**Prior art.**

- RFC 320 'Non-zeroing dynamic drop', rust-lang/rfcs f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/0320-nonzeroing-dynamic-drop.md lines 6-15 (stack-local boolean flags for 'dynamic drop obligations'), lines 99-114 (drop obligations: a Drop type is one obligation, otherwise the union of its fields'; removed when moved, consumed by a call, or at scope end), lines 116-142 (dynamic obligations at a merge point = union minus intersection of the predecessors' sets), lines 144-155 (subsection 'Stack-local drop flags'; lines 153-155: 'we do not specify the precise set of boolean flags that are injected') [design document, historical; informal]
- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_transform/src/elaborate_drops.rs lines 165-188 (drop_style: (maybe_init, maybe_uninit) = (false, _) => Dead, (true, false) => Static, (true, true) => Conditional/Open) and lines 290-334 (collect_drop_flags; lines 310-312 create a flag iff maybe_init && maybe_uninit at a drop) [source; prose only]
- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_dataflow/src/impls/initialized.rs lines 103-139 and 344-380 (MaybeInitializedPlaces / MaybeUninitializedPlaces docs: the intersection of the two at a drop 'yields the set of places that would require a dynamic drop-flag'), lines 206-227 (domain MaybeReachable, bottom Unreachable) [source; prose only]
- J. Wu, Y. Wang, L. Yu, L. Meng, 'RustCompCert: A Verified and Verifying Compiler for a Sequential Subset of Rust', arXiv:2602.07455v1 (7 Feb 2026; companion: 'End-to-end Compositional Verification of Program Safety through Verified and Verifying Compilation', arXiv:2510.10015v1); Rocq development github.com/SJTU-PLV/CompCert commit e3d03ed822a7aaf452b7022c347187ed1efc1c12 (branch rust-verified-compiler): rustfrontend/InitAnalysis.v lines 83-84 (maybe-init and maybe-uninit as Kildall fixpoints over a possibly cyclic CFG); rustfrontend/ElaborateDrop.v lines 33-52 (a drop flag for a place that is may-init and not must-init at a drop), 147-181 (flag-guarded drop, flag reset before the drop; once a place has a flag, the guarded form is used at all its drops), 253-276 (flag updates at assignments, moves and calls); rustfrontend/ElaborateDropProof.v lines 4492-4513 (transl_program_correct: forward simulation from the ownership-tracking semantics to the explicit-drop semantics; no Admitted/admit in the file; not compiled here). No unwind, panic or cleanup construct occurs in rustfrontend/ (a call node has one successor). No necessity or minimality statement [mechanized prior art]
- V. Fukala, 'Formalization of Rust Drop Elaboration', Bachelor thesis, Programming Language Foundations Lab, ETH Zurich, August 5, 2024 (supervisors I. van Bakel, R. Jung), PDF https://ethz.ch/content/dam/ethz/special-interest/infk/inst-pls/plf-dam/documents/StudentProjects/BachelorTheses/2024-Viktor-Thesis.pdf: a structured language (if, while, calls, tuples; no control-flow graphs, section 3) with flag-based drop elaboration in Coq; a complete correctness proof for a scalar-only version, and a proof relying on unproved lemmas for tuples (sections 5.4, 6, Appendix A); unwinding left to future work (section 6.1). The Coq repository named in Appendix A requires sign-in and was not inspected [mechanized prior art, partly]

**Design question.** Which per-drop-point choices among static drop, no drop and flag test are safe?

**Non-claims.** See **Boundaries**, common non-claims and the R2s entry.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) for any reading of this result as a statement about a real system. Such a reading relies on the bridges "Standard decision and rustc drop styles", "Flag maintenance", "Cleanup code and MIR cleanup blocks", "Abort rule in rustc and C++" under **Modeling bridges** below, which state the correspondence, its reasoning and the known mismatches; the kernel check is about the toy model and neither establishes nor refutes these correspondences (model–system relation: none proved).

### R2: `elabCorrect_iff_allCompatible_of_forward_moveChecked_noNormalPathToResume`

**Kind:** characterization. **Tier:** T1. **Depth:** substantive. **Proof status:** proved (from R2s and R2n).

Lean statement (verbatim source quote):

```lean
-- lean/ToyDropFlags/Results.lean:89-93
theorem elabCorrect_iff_allCompatible_of_forward_moveChecked_noNormalPathToResume (s : SProg)
    (hfwd : Forward s) (hplaces : PlacesAreMovePaths s) (hmoves : MovesFromInit s)
    (hinits : InitsIntoUninit s) (hclean : NoNormalPathToResume s)
    (d : Nat → Place → Decision) :
    ElabCorrect .abort .std d s ↔ AllCompatible s d := …
```

**Plain claim.** Assume that a destructor panic during unwinding aborts the process and let s be a forward (acyclic, topologically numbered) toy program that only mentions valid move paths, moves only definitely-initialized places (call arguments pairwise disjoint), initializes only definitely-uninitialized places, and has no resume node reachable from the entry along normal edges only. Then, with the standard flag maintenance, a decision map d is elaboration-correct (every run terminates and is exactly-once) if and only if d is compatible with the fine analyses at every forward-reachable drop point (an unconditional drop only for must-init atoms, nothing only for atoms that are not may-init, a flag test anywhere). Consequently (staticChoice_compatible_iff), at a forward-reachable drop point a flag test is required for an atom exactly when it is may-init and not must-init there; at other forward-reachable drop points some static choice is compatible.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hfwd : Forward s` | the one-pass initialization analyses follow index-increasing edges only, which are all edges exactly when the program is forward (acyclic, topologically numbered) | tight | `characterization_fails_without_forward` | a 1-local (leaf), 3-node program with one back edge (progLoop) |
| `hplaces : PlacesAreMovePaths s` | every mentioned place follows its local's type and never enters a struct with its own destructor, so the analysis's atoms match the units written and destroyed | tight | `characterization_fails_without_placesAreMovePaths` | a 1-local, 3-node forward program whose local is a struct with its own destructor and two leaf fields (progDropStruct) |
| `hmoves : MovesFromInit s` | no use after move: every moved place (and call argument) is must-init, and call arguments are pairwise disjoint | tight | `characterization_fails_without_movesFromInit` | a 1-local (leaf), 4-node forward program (progUseAfterMove) |
| `hinits : InitsIntoUninit s` | no overwrite of an owned value: every initialized place (and call destination not overlapped by an argument) is not may-init | tight | `characterization_fails_without_initsIntoUninit` | a 1-local (leaf), 3-node forward program (progOverwrite) |
| `hclean : NoNormalPathToResume s` | no resume node is reachable from the entry along normal edges only, so a resume ladder (whose drops have no landing pad) runs only while unwinding, where a destructor panic aborts | tight | `characterization_fails_without_noNormalPathToResume` | a 2-local (two leaves), 3-node forward program (progResumeNormal) |

**Non-vacuity witness.** progCleanup satisfies all five hypotheses (with any decision map). Informative instances: on progJoin the standard map is compatible and elaboration-correct (allCompatible_pos, elabCorrect_pos); an unconditional drop at the join is neither (allCompatible_neg, elabCorrect_neg). (Lean: `exactlyOnce_hypotheses_hold_progCleanup`)

**Tier rationale.** T1. rustc's MaybeInitializedPlaces documentation states informally that may-init ∩ may-uninit at a drop is the set of places needing a dynamic flag; RustCompCert and Fukala mechanize the sufficiency of one particular flag placement without unwinding; neither proves the converse (necessity) nor the characterization of all decision maps.

**Prior art.**

- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_dataflow/src/impls/initialized.rs lines 103-139 and 344-380 (MaybeInitializedPlaces / MaybeUninitializedPlaces docs: the intersection of the two at a drop 'yields the set of places that would require a dynamic drop-flag'), lines 206-227 (domain MaybeReachable, bottom Unreachable) [source; prose only]
- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_transform/src/elaborate_drops.rs lines 165-188 (drop_style: (maybe_init, maybe_uninit) = (false, _) => Dead, (true, false) => Static, (true, true) => Conditional/Open) and lines 290-334 (collect_drop_flags; lines 310-312 create a flag iff maybe_init && maybe_uninit at a drop) [source; prose only]
- RFC 320 'Non-zeroing dynamic drop', rust-lang/rfcs f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/0320-nonzeroing-dynamic-drop.md lines 6-15 (stack-local boolean flags for 'dynamic drop obligations'), lines 99-114 (drop obligations: a Drop type is one obligation, otherwise the union of its fields'; removed when moved, consumed by a call, or at scope end), lines 116-142 (dynamic obligations at a merge point = union minus intersection of the predecessors' sets), lines 144-155 (subsection 'Stack-local drop flags'; lines 153-155: 'we do not specify the precise set of boolean flags that are injected') [design document, historical; informal]
- J. Wu, Y. Wang, L. Yu, L. Meng, 'RustCompCert: A Verified and Verifying Compiler for a Sequential Subset of Rust', arXiv:2602.07455v1 (7 Feb 2026; companion: 'End-to-end Compositional Verification of Program Safety through Verified and Verifying Compilation', arXiv:2510.10015v1); Rocq development github.com/SJTU-PLV/CompCert commit e3d03ed822a7aaf452b7022c347187ed1efc1c12 (branch rust-verified-compiler): rustfrontend/InitAnalysis.v lines 83-84 (maybe-init and maybe-uninit as Kildall fixpoints over a possibly cyclic CFG); rustfrontend/ElaborateDrop.v lines 33-52 (a drop flag for a place that is may-init and not must-init at a drop), 147-181 (flag-guarded drop, flag reset before the drop; once a place has a flag, the guarded form is used at all its drops), 253-276 (flag updates at assignments, moves and calls); rustfrontend/ElaborateDropProof.v lines 4492-4513 (transl_program_correct: forward simulation from the ownership-tracking semantics to the explicit-drop semantics; no Admitted/admit in the file; not compiled here). No unwind, panic or cleanup construct occurs in rustfrontend/ (a call node has one successor). No necessity or minimality statement [mechanized prior art]
- V. Fukala, 'Formalization of Rust Drop Elaboration', Bachelor thesis, Programming Language Foundations Lab, ETH Zurich, August 5, 2024 (supervisors I. van Bakel, R. Jung), PDF https://ethz.ch/content/dam/ethz/special-interest/infk/inst-pls/plf-dam/documents/StudentProjects/BachelorTheses/2024-Viktor-Thesis.pdf: a structured language (if, while, calls, tuples; no control-flow graphs, section 3) with flag-based drop elaboration in Coq; a complete correctness proof for a scalar-only version, and a proof relying on unproved lemmas for tuples (sections 5.4, 6, Appendix A); unwinding left to future work (section 6.1). The Coq repository named in Appendix A requires sign-in and was not inspected [mechanized prior art, partly]

**Design question.** Where are dynamic flags necessary?

**Non-claims.** See **Boundaries**, common non-claims and the R2 entry.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) for any reading of this result as a statement about a real system. Such a reading relies on the bridges "Standard decision and rustc drop styles", "Flag maintenance", "Cleanup code and MIR cleanup blocks", "Abort rule in rustc and C++" under **Modeling bridges** below, which state the correspondence, its reasoning and the known mismatches; the kernel check is about the toy model and neither establishes nor refutes these correspondences (model–system relation: none proved).

### R2n: `allCompatible_of_exactlyOnce_of_placesAreMovePaths`

**Kind:** theorem. **Tier:** T1. **Depth:** substantive. **Proof status:** proved.

Lean statement (verbatim source quote):

```lean
-- lean/ToyDropFlags/Results.lean:60-63
theorem allCompatible_of_exactlyOnce_of_placesAreMovePaths (s : SProg)
    (hplaces : PlacesAreMovePaths s) (d : Nat → Place → Decision)
    (hd : ∀ inp, ExactlyOnce (runElab .abort .std d s inp)) :
    AllCompatible s d := …
```

Unfolded rendering of the conclusion, with `AllCompatible` expanded (re-elaborated and checked definitionally equal):

```lean
∀ i < s.nodes.length, isDropPoint s i = true → ForwardReachable s i = true →
  ∀ a ∈ allAtoms s.locals,
    Compatible (mayInit s .fine i a) (mustInit s .fine i a) (d i a) = true
```

**Plain claim.** Assume only that every place mentioned by the program s is a valid move path. If every run of the elaboration of s with decision map d (standard flag maintenance, abort rule; a run is the result of `runElab`, the target semantics `run` with step bound `fuelFor s`, on one input bit stream) is exactly-once, then d is compatible with the fine analyses at every forward-reachable drop point: d drops an atom unconditionally only where it is must-init and does nothing for an atom only where it is not may-init. Forwardness, MovesFromInit, InitsIntoUninit and NoNormalPathToResume are not assumed, and termination is not assumed.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hplaces : PlacesAreMovePaths s` | an ill-typed init creates nothing although the analysis marks its atom initialized, so may-init no longer implies that a value exists | tight | `allCompatible_necessity_fails_without_placesAreMovePaths` | a 1-local (leaf), 3-node forward program with one ill-typed place (progIllTyped) |
| `hd : ∀ inp, ExactlyOnce (runElab .abort .std d s inp)` | the conclusion is about decision maps whose runs are all exactly-once | tight | `allCompatible_necessity_fails_without_exactlyOnce` | a 1-local (leaf), 4-node forward program (progJoin) with the decision map that drops x unconditionally at the join |

**Non-vacuity witness.** progJoin with the decision map that tests x at every drop point: places are move paths and every run is exactly-once. (Lean: `allCompatible_necessity_hypotheses_hold_progJoin`)

**Tier rationale.** T1. Stated informally in rustc's MaybeInitializedPlaces documentation; the mechanized developments found (RustCompCert, Fukala) prove sufficiency of their own flag placement only.

**Prior art.**

- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_dataflow/src/impls/initialized.rs lines 103-139 and 344-380 (MaybeInitializedPlaces / MaybeUninitializedPlaces docs: the intersection of the two at a drop 'yields the set of places that would require a dynamic drop-flag'), lines 206-227 (domain MaybeReachable, bottom Unreachable) [source; prose only]
- RFC 320 'Non-zeroing dynamic drop', rust-lang/rfcs f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/0320-nonzeroing-dynamic-drop.md lines 6-15 (stack-local boolean flags for 'dynamic drop obligations'), lines 99-114 (drop obligations: a Drop type is one obligation, otherwise the union of its fields'; removed when moved, consumed by a call, or at scope end), lines 116-142 (dynamic obligations at a merge point = union minus intersection of the predecessors' sets), lines 144-155 (subsection 'Stack-local drop flags'; lines 153-155: 'we do not specify the precise set of boolean flags that are injected') [design document, historical; informal]
- J. Wu, Y. Wang, L. Yu, L. Meng, 'RustCompCert: A Verified and Verifying Compiler for a Sequential Subset of Rust', arXiv:2602.07455v1 (7 Feb 2026; companion: 'End-to-end Compositional Verification of Program Safety through Verified and Verifying Compilation', arXiv:2510.10015v1); Rocq development github.com/SJTU-PLV/CompCert commit e3d03ed822a7aaf452b7022c347187ed1efc1c12 (branch rust-verified-compiler): rustfrontend/InitAnalysis.v lines 83-84 (maybe-init and maybe-uninit as Kildall fixpoints over a possibly cyclic CFG); rustfrontend/ElaborateDrop.v lines 33-52 (a drop flag for a place that is may-init and not must-init at a drop), 147-181 (flag-guarded drop, flag reset before the drop; once a place has a flag, the guarded form is used at all its drops), 253-276 (flag updates at assignments, moves and calls); rustfrontend/ElaborateDropProof.v lines 4492-4513 (transl_program_correct: forward simulation from the ownership-tracking semantics to the explicit-drop semantics; no Admitted/admit in the file; not compiled here). No unwind, panic or cleanup construct occurs in rustfrontend/ (a call node has one successor). No necessity or minimality statement [mechanized prior art]
- V. Fukala, 'Formalization of Rust Drop Elaboration', Bachelor thesis, Programming Language Foundations Lab, ETH Zurich, August 5, 2024 (supervisors I. van Bakel, R. Jung), PDF https://ethz.ch/content/dam/ethz/special-interest/infk/inst-pls/plf-dam/documents/StudentProjects/BachelorTheses/2024-Viktor-Thesis.pdf: a structured language (if, while, calls, tuples; no control-flow graphs, section 3) with flag-based drop elaboration in Coq; a complete correctness proof for a scalar-only version, and a proof relying on unproved lemmas for tuples (sections 5.4, 6, Appendix A); unwinding left to future work (section 6.1). The Coq repository named in Appendix A requires sign-in and was not inspected [mechanized prior art, partly]

**Design question.** Where are dynamic flags necessary?

**Non-claims.** See **Boundaries**, common non-claims and the R2n entry.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) for any reading of this result as a statement about a real system. Such a reading relies on the bridges "Standard decision and rustc drop styles", "Flag maintenance" under **Modeling bridges** below, which state the correspondence, its reasoning and the known mismatches; the kernel check is about the toy model and neither establishes nor refutes these correspondences (model–system relation: none proved).

### R3: `staticChoice_at_disagreement_fails_of_placesAreMovePaths`

**Kind:** impossibility. **Tier:** T1. **Depth:** substantive. **Proof status:** proved.

Lean statement (verbatim source quote):

```lean
-- lean/ToyDropFlags/Results.lean:106-113
theorem staticChoice_at_disagreement_fails_of_placesAreMovePaths (s : SProg)
    (hplaces : PlacesAreMovePaths s) (i : Nat) (hdrop : isDropPoint s i = true) (a : Place)
    (hmay : mayInit s .fine i a = true) (hmust : mustInit s .fine i a = false) :
    (∃ inp, ¬ NoDoubleDrop
        (runElab .abort .std (overrideAt (stdMap s .fine) i a .drop) s inp).log) ∧
    (∃ inp,
        (runElab .abort .std (overrideAt (stdMap s .fine) i a .skip) s inp).outcome.complete = true ∧
        ¬ NoLeak (runElab .abort .std (overrideAt (stdMap s .fine) i a .skip) s inp).log) := …
```

**Plain claim.** Assume only that every place mentioned by the program s is a valid move path, let i be a drop point (a ret or resume node) and let atom a be may-init but not must-init at i. Then, with the standard flag maintenance and the abort rule (runs are results of `runElab`, the target semantics `run` with step bound `fuelFor s`), (1) replacing the standard decision for a at i by an unconditional drop gives an input whose run violates NoDoubleDrop (a value destroyed twice, an uncreated value destroyed, or a destructor on unwritten memory), and (2) replacing it by nothing gives an input whose run returns or completes an unwind and violates NoLeak. Forwardness, MovesFromInit, InitsIntoUninit and NoNormalPathToResume are not assumed.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hplaces : PlacesAreMovePaths s` | an ill-typed init creates nothing although the analysis marks its atom initialized | tight | `staticChoice_necessity_fails_without_placesAreMovePaths` | a 1-local (leaf), 3-node forward program with one ill-typed place (progIllTyped) |
| `hdrop : isDropPoint s i = true` | only drop points have drop decisions; elsewhere the override changes nothing | tight | `staticChoice_necessity_fails_at_non_drop_point` | a 1-local (leaf), 5-node forward program (progJoinOff), node 3 a branch |
| `hmay : mayInit s .fine i a = true` | if a is not may-init, doing nothing is correct, so the leak half fails | tight | `staticChoice_necessity_fails_without_mayInit` | a 1-local (leaf), 3-node forward program (progMoved) |
| `hmust : mustInit s .fine i a = false` | if a is must-init, an unconditional drop is correct, so the double-drop half fails | tight | `staticChoice_necessity_fails_without_notMustInit` | a 1-local (leaf), 2-node forward program (progKept) |

**Non-vacuity witness.** Node 3 (the join) of progJoin for x; both halves are exhibited concretely by R4a and R4a-skip. (Lean: `staticChoice_hypotheses_hold_progJoin`)

**Positive control** (a nearby setting where the impossibility's conclusion fails): `progKept_drop_correct`, `progMoved_skip_correct`.

**Tier rationale.** T1 (the necessity direction of the folklore flag rule; not found mechanized).

**Prior art.**

- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_dataflow/src/impls/initialized.rs lines 103-139 and 344-380 (MaybeInitializedPlaces / MaybeUninitializedPlaces docs: the intersection of the two at a drop 'yields the set of places that would require a dynamic drop-flag'), lines 206-227 (domain MaybeReachable, bottom Unreachable) [source; prose only]
- RFC 320 'Non-zeroing dynamic drop', rust-lang/rfcs f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/0320-nonzeroing-dynamic-drop.md lines 6-15 (stack-local boolean flags for 'dynamic drop obligations'), lines 99-114 (drop obligations: a Drop type is one obligation, otherwise the union of its fields'; removed when moved, consumed by a call, or at scope end), lines 116-142 (dynamic obligations at a merge point = union minus intersection of the predecessors' sets), lines 144-155 (subsection 'Stack-local drop flags'; lines 153-155: 'we do not specify the precise set of boolean flags that are injected') [design document, historical; informal]

**Design question.** Where are dynamic flags necessary?

**Non-claims.** See **Boundaries**, common non-claims and the R3 entry.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) for any reading of this result as a statement about a real system. Such a reading relies on the bridges "Standard decision and rustc drop styles" under **Modeling bridges** below, which state the correspondence, its reasoning and the known mismatches; the kernel check is about the toy model and neither establishes nor refutes these correspondences (model–system relation: none proved).

### R4a: `staticDrop_at_join_double_drops`

**Kind:** counterexample. **Tier:** T0. **Depth:** definitional. **Proof status:** proved.

Lean statement (verbatim source quote):

```lean
-- lean/ToyDropFlags/Counterexamples.lean:175-181
theorem staticDrop_at_join_double_drops :
    Forward progJoin ∧ MoveChecked progJoin ∧ NoNormalPathToResume progJoin ∧
    mayInit progJoin .fine 3 x = true ∧ mustInit progJoin .fine 3 x = false ∧
    (runElab .abort .std (overrideAt (stdMap progJoin .fine) 3 x .drop) progJoin [true]).log =
      [.create 0, .consume 0, .drop 0] ∧
    ¬ NoDoubleDrop
      (runElab .abort .std (overrideAt (stdMap progJoin .fine) 3 x .drop) progJoin [true]).log := …
```

**Plain claim.** On progJoin (init x; branch; move x on one branch; ret), which satisfies all hypotheses of R1 and whose standard elaboration is elaboration-correct (by R1, `stdElab_correct_of_forward_moveChecked_noNormalPathToResume`, since `MoveChecked` is `PlacesAreMovePaths ∧ MovesFromInit ∧ InitsIntoUninit`), replacing only the decision for x at the join (node 3, where x is may-init and not must-init) by an unconditional drop gives, on input [true], the log [create 0, consume 0, drop 0], which violates NoDoubleDrop.

**Hypothesis ledger.** None: the statement has no hypotheses (it is about concrete programs and inputs, or it is existential).

**Non-vacuity witness.** progJoin; the theorem itself states the hypotheses of R1 for progJoin. (Lean: `staticDrop_at_join_double_drops`)

**Tier rationale.** T0: the conditional-move join is the standard motivating example of dynamic drop flags (RFC 320) and is covered by the mechanized elaborations of RustCompCert and Fukala; this is a concrete kernel-evaluated trace of it.

**Prior art.**

- RFC 320 'Non-zeroing dynamic drop', rust-lang/rfcs f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/0320-nonzeroing-dynamic-drop.md lines 6-15 (stack-local boolean flags for 'dynamic drop obligations'), lines 99-114 (drop obligations: a Drop type is one obligation, otherwise the union of its fields'; removed when moved, consumed by a call, or at scope end), lines 116-142 (dynamic obligations at a merge point = union minus intersection of the predecessors' sets), lines 144-155 (subsection 'Stack-local drop flags'; lines 153-155: 'we do not specify the precise set of boolean flags that are injected') [design document, historical; informal]
- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_transform/src/elaborate_drops.rs lines 424-431 (all flags set false at function start), 433-451 (call destination flags set at the start of the return target), 464-520 (per-location flag effects inserted at the location, i.e. before the statement/terminator); compiler/rustc_mir_dataflow/src/drop_flag_effects.rs lines 108-137 (drop_flag_effects_for_location: moves out => Absent) and 139-150 (for_location_inits: InitKind::Unconditional => Present, InitKind::OnReturn => no effect at the call) [source; prose only]
- J. Wu, Y. Wang, L. Yu, L. Meng, 'RustCompCert: A Verified and Verifying Compiler for a Sequential Subset of Rust', arXiv:2602.07455v1 (7 Feb 2026; companion: 'End-to-end Compositional Verification of Program Safety through Verified and Verifying Compilation', arXiv:2510.10015v1); Rocq development github.com/SJTU-PLV/CompCert commit e3d03ed822a7aaf452b7022c347187ed1efc1c12 (branch rust-verified-compiler): rustfrontend/InitAnalysis.v lines 83-84 (maybe-init and maybe-uninit as Kildall fixpoints over a possibly cyclic CFG); rustfrontend/ElaborateDrop.v lines 33-52 (a drop flag for a place that is may-init and not must-init at a drop), 147-181 (flag-guarded drop, flag reset before the drop; once a place has a flag, the guarded form is used at all its drops), 253-276 (flag updates at assignments, moves and calls); rustfrontend/ElaborateDropProof.v lines 4492-4513 (transl_program_correct: forward simulation from the ownership-tracking semantics to the explicit-drop semantics; no Admitted/admit in the file; not compiled here). No unwind, panic or cleanup construct occurs in rustfrontend/ (a call node has one successor). No necessity or minimality statement [mechanized prior art]
- V. Fukala, 'Formalization of Rust Drop Elaboration', Bachelor thesis, Programming Language Foundations Lab, ETH Zurich, August 5, 2024 (supervisors I. van Bakel, R. Jung), PDF https://ethz.ch/content/dam/ethz/special-interest/infk/inst-pls/plf-dam/documents/StudentProjects/BachelorTheses/2024-Viktor-Thesis.pdf: a structured language (if, while, calls, tuples; no control-flow graphs, section 3) with flag-based drop elaboration in Coq; a complete correctness proof for a scalar-only version, and a proof relying on unproved lemmas for tuples (sections 5.4, 6, Appendix A); unwinding left to future work (section 6.1). The Coq repository named in Appendix A requires sign-in and was not inspected [mechanized prior art, partly]

**Design question.** What exactly must elaboration maintain on normal and cleanup edges?

**Non-claims.** See **Boundaries**, common non-claims and the R4a entry.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) for any reading of this result as a statement about a real system. Such a reading relies on the bridges "Standard decision and rustc drop styles" under **Modeling bridges** below, which state the correspondence, its reasoning and the known mismatches; the kernel check is about the toy model and neither establishes nor refutes these correspondences (model–system relation: none proved).

### R4a-skip: `staticSkip_at_join_leaks`

**Kind:** counterexample. **Tier:** T0. **Depth:** definitional. **Proof status:** proved.

Lean statement (verbatim source quote):

```lean
-- lean/ToyDropFlags/Counterexamples.lean:185-192
theorem staticSkip_at_join_leaks :
    Forward progJoin ∧ MoveChecked progJoin ∧ NoNormalPathToResume progJoin ∧
    (runElab .abort .std (overrideAt (stdMap progJoin .fine) 3 x .skip) progJoin
      [false, false]).outcome = .returned ∧
    (runElab .abort .std (overrideAt (stdMap progJoin .fine) 3 x .skip) progJoin
      [false, false]).log = [.create 0] ∧
    ¬ NoLeak (runElab .abort .std (overrideAt (stdMap progJoin .fine) 3 x .skip) progJoin
      [false, false]).log := …
```

**Plain claim.** On progJoin, replacing only the decision for x at the join by nothing gives, on input [false, false], a run that returns with log [create 0], which violates NoLeak.

**Hypothesis ledger.** None: the statement has no hypotheses (it is about concrete programs and inputs, or it is existential).

**Non-vacuity witness.** progJoin. (Lean: `staticSkip_at_join_leaks`)

**Tier rationale.** T0, as R4a.

**Prior art.**

- RFC 320 'Non-zeroing dynamic drop', rust-lang/rfcs f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/0320-nonzeroing-dynamic-drop.md lines 6-15 (stack-local boolean flags for 'dynamic drop obligations'), lines 99-114 (drop obligations: a Drop type is one obligation, otherwise the union of its fields'; removed when moved, consumed by a call, or at scope end), lines 116-142 (dynamic obligations at a merge point = union minus intersection of the predecessors' sets), lines 144-155 (subsection 'Stack-local drop flags'; lines 153-155: 'we do not specify the precise set of boolean flags that are injected') [design document, historical; informal]
- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_transform/src/elaborate_drops.rs lines 424-431 (all flags set false at function start), 433-451 (call destination flags set at the start of the return target), 464-520 (per-location flag effects inserted at the location, i.e. before the statement/terminator); compiler/rustc_mir_dataflow/src/drop_flag_effects.rs lines 108-137 (drop_flag_effects_for_location: moves out => Absent) and 139-150 (for_location_inits: InitKind::Unconditional => Present, InitKind::OnReturn => no effect at the call) [source; prose only]
- J. Wu, Y. Wang, L. Yu, L. Meng, 'RustCompCert: A Verified and Verifying Compiler for a Sequential Subset of Rust', arXiv:2602.07455v1 (7 Feb 2026; companion: 'End-to-end Compositional Verification of Program Safety through Verified and Verifying Compilation', arXiv:2510.10015v1); Rocq development github.com/SJTU-PLV/CompCert commit e3d03ed822a7aaf452b7022c347187ed1efc1c12 (branch rust-verified-compiler): rustfrontend/InitAnalysis.v lines 83-84 (maybe-init and maybe-uninit as Kildall fixpoints over a possibly cyclic CFG); rustfrontend/ElaborateDrop.v lines 33-52 (a drop flag for a place that is may-init and not must-init at a drop), 147-181 (flag-guarded drop, flag reset before the drop; once a place has a flag, the guarded form is used at all its drops), 253-276 (flag updates at assignments, moves and calls); rustfrontend/ElaborateDropProof.v lines 4492-4513 (transl_program_correct: forward simulation from the ownership-tracking semantics to the explicit-drop semantics; no Admitted/admit in the file; not compiled here). No unwind, panic or cleanup construct occurs in rustfrontend/ (a call node has one successor). No necessity or minimality statement [mechanized prior art]
- V. Fukala, 'Formalization of Rust Drop Elaboration', Bachelor thesis, Programming Language Foundations Lab, ETH Zurich, August 5, 2024 (supervisors I. van Bakel, R. Jung), PDF https://ethz.ch/content/dam/ethz/special-interest/infk/inst-pls/plf-dam/documents/StudentProjects/BachelorTheses/2024-Viktor-Thesis.pdf: a structured language (if, while, calls, tuples; no control-flow graphs, section 3) with flag-based drop elaboration in Coq; a complete correctness proof for a scalar-only version, and a proof relying on unproved lemmas for tuples (sections 5.4, 6, Appendix A); unwinding left to future work (section 6.1). The Coq repository named in Appendix A requires sign-in and was not inspected [mechanized prior art, partly]

**Design question.** What exactly must elaboration maintain on normal and cleanup edges?

**Non-claims.** See **Boundaries**, common non-claims and the R4a-skip entry.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) for any reading of this result as a statement about a real system. Such a reading relies on the bridges "Standard decision and rustc drop styles" under **Modeling bridges** below, which state the correspondence, its reasoning and the known mismatches; the kernel check is about the toy model and neither establishes nor refutes these correspondences (model–system relation: none proved).

### R4b: `argFlagNotClearedOnUnwind_double_drops`

**Kind:** counterexample. **Tier:** T1. **Depth:** definitional. **Proof status:** proved.

Lean statement (verbatim source quote):

```lean
-- lean/ToyDropFlags/Counterexamples.lean:198-206
theorem argFlagNotClearedOnUnwind_double_drops :
    Forward progCleanup ∧ MoveChecked progCleanup ∧ NoNormalPathToResume progCleanup ∧
    (runElab .abort { FlagConfig.std with clearArgsBeforeCall := false }
      (stdMap progCleanup .fine) progCleanup [false, true, false]).outcome = .unwound ∧
    (runElab .abort { FlagConfig.std with clearArgsBeforeCall := false }
      (stdMap progCleanup .fine) progCleanup [false, true, false]).log =
      [.create 0, .consume 0, .drop 0] ∧
    ¬ NoDoubleDrop (runElab .abort { FlagConfig.std with clearArgsBeforeCall := false }
      (stdMap progCleanup .fine) progCleanup [false, true, false]).log := …
```

**Plain claim.** On progCleanup (two calls sharing one cleanup node; the second call consumes x), which satisfies all hypotheses of R1 and whose standard elaboration is elaboration-correct (by R1, `stdElab_correct_of_forward_moveChecked_noNormalPathToResume`, since `MoveChecked` is `PlacesAreMovePaths ∧ MovesFromInit ∧ InitsIntoUninit`), clearing call-argument flags only on the call's normal edge (clearArgsBeforeCall := false, everything else standard) gives, on input [false, true, false], a run that completes an unwind with log [create 0, consume 0, drop 0]: the second call consumes x and panics, and the shared cleanup still sees x's flag set. NoDoubleDrop is violated.

**Hypothesis ledger.** None: the statement has no hypotheses (it is about concrete programs and inputs, or it is existential).

**Non-vacuity witness.** progCleanup. (Lean: `argFlagNotClearedOnUnwind_double_drops`)

**Tier rationale.** T1: the interaction of argument flags with shared cleanup code is implemented by rustc (per-location flag effects before the call) but is not covered by the mechanized developments found, which have no unwinding.

**Prior art.**

- RFC 320 'Non-zeroing dynamic drop', rust-lang/rfcs f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/0320-nonzeroing-dynamic-drop.md lines 6-15 (stack-local boolean flags for 'dynamic drop obligations'), lines 99-114 (drop obligations: a Drop type is one obligation, otherwise the union of its fields'; removed when moved, consumed by a call, or at scope end), lines 116-142 (dynamic obligations at a merge point = union minus intersection of the predecessors' sets), lines 144-155 (subsection 'Stack-local drop flags'; lines 153-155: 'we do not specify the precise set of boolean flags that are injected') [design document, historical; informal]
- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_transform/src/elaborate_drops.rs lines 424-431 (all flags set false at function start), 433-451 (call destination flags set at the start of the return target), 464-520 (per-location flag effects inserted at the location, i.e. before the statement/terminator); compiler/rustc_mir_dataflow/src/drop_flag_effects.rs lines 108-137 (drop_flag_effects_for_location: moves out => Absent) and 139-150 (for_location_inits: InitKind::Unconditional => Present, InitKind::OnReturn => no effect at the call) [source; prose only]
- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_transform/src/elaborate_drop.rs lines 49-56 and 66-71 (Unwind::InCleanup: 'Already in an unwind path, any panic will cause an abort.'; into_action => UnwindAction::Terminate(UnwindTerminateReason::InCleanup)); elaborate_drops.rs lines 359-375 (drops in cleanup blocks get Unwind::InCleanup); compiler/rustc_middle/src/mir/syntax.rs lines 657-683 (cleanup blocks: every unwind field must be Terminate or Unreachable; Return is not allowed; blocks reachable from cleanup blocks are cleanup) and 1010-1038 (UnwindAction::Terminate 'Terminates the execution if unwind happens'); compiler/rustc_mir_transform/src/validate.rs lines 246-275 (the validator rejects Cleanup or Continue unwind actions in cleanup blocks); library/core/src/panicking.rs lines 356-370 (lang item panic_in_cleanup: non-unwinding panic 'panic in a destructor during cleanup') [source; prose only]
- J. Wu, Y. Wang, L. Yu, L. Meng, 'RustCompCert: A Verified and Verifying Compiler for a Sequential Subset of Rust', arXiv:2602.07455v1 (7 Feb 2026; companion: 'End-to-end Compositional Verification of Program Safety through Verified and Verifying Compilation', arXiv:2510.10015v1); Rocq development github.com/SJTU-PLV/CompCert commit e3d03ed822a7aaf452b7022c347187ed1efc1c12 (branch rust-verified-compiler): rustfrontend/InitAnalysis.v lines 83-84 (maybe-init and maybe-uninit as Kildall fixpoints over a possibly cyclic CFG); rustfrontend/ElaborateDrop.v lines 33-52 (a drop flag for a place that is may-init and not must-init at a drop), 147-181 (flag-guarded drop, flag reset before the drop; once a place has a flag, the guarded form is used at all its drops), 253-276 (flag updates at assignments, moves and calls); rustfrontend/ElaborateDropProof.v lines 4492-4513 (transl_program_correct: forward simulation from the ownership-tracking semantics to the explicit-drop semantics; no Admitted/admit in the file; not compiled here). No unwind, panic or cleanup construct occurs in rustfrontend/ (a call node has one successor). No necessity or minimality statement [mechanized prior art]
- V. Fukala, 'Formalization of Rust Drop Elaboration', Bachelor thesis, Programming Language Foundations Lab, ETH Zurich, August 5, 2024 (supervisors I. van Bakel, R. Jung), PDF https://ethz.ch/content/dam/ethz/special-interest/infk/inst-pls/plf-dam/documents/StudentProjects/BachelorTheses/2024-Viktor-Thesis.pdf: a structured language (if, while, calls, tuples; no control-flow graphs, section 3) with flag-based drop elaboration in Coq; a complete correctness proof for a scalar-only version, and a proof relying on unproved lemmas for tuples (sections 5.4, 6, Appendix A); unwinding left to future work (section 6.1). The Coq repository named in Appendix A requires sign-in and was not inspected [mechanized prior art, partly]

**Design question.** What exactly must elaboration maintain on normal and cleanup edges?

**Non-claims.** See **Boundaries**, common non-claims and the R4b entry.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) for any reading of this result as a statement about a real system. Such a reading relies on the bridges "Flag maintenance" under **Modeling bridges** below, which state the correspondence, its reasoning and the known mismatches; the kernel check is about the toy model and neither establishes nor refutes these correspondences (model–system relation: none proved).

### R4c-kill: `wholeKillAnalysis_leaks_remaining_field / wholeKillFlags_leaks_remaining_field`

**Kind:** counterexample. **Tier:** T0. **Depth:** definitional. **Proof status:** proved.

Lean statement (verbatim source quotes):

```lean
-- lean/ToyDropFlags/Counterexamples.lean:235-240
theorem wholeKillAnalysis_leaks_remaining_field :
    Forward progPartial ∧ MoveChecked progPartial ∧ NoNormalPathToResume progPartial ∧
    (runElab .abort .std (stdMap progPartial .wholeKill) progPartial []).outcome = .returned ∧
    (runElab .abort .std (stdMap progPartial .wholeKill) progPartial []).log =
      [.create 0, .create 1, .consume 0] ∧
    ¬ NoLeak (runElab .abort .std (stdMap progPartial .wholeKill) progPartial []).log := …
```

```lean
-- lean/ToyDropFlags/Counterexamples.lean:246-253
theorem wholeKillFlags_leaks_remaining_field :
    Forward progPartialFlag ∧ MoveChecked progPartialFlag ∧ NoNormalPathToResume progPartialFlag ∧
    (runElab .abort { FlagConfig.std with gran := .wholeKill } (stdMap progPartialFlag .fine)
      progPartialFlag [true, true]).outcome = .returned ∧
    (runElab .abort { FlagConfig.std with gran := .wholeKill } (stdMap progPartialFlag .fine)
      progPartialFlag [true, true]).log = [.create 0, .create 1, .consume 0] ∧
    ¬ NoLeak (runElab .abort { FlagConfig.std with gran := .wholeKill }
      (stdMap progPartialFlag .fine) progPartialFlag [true, true]).log := …
```

**Plain claim.** Treating a partial move as a move of the whole local breaks exactly-once, in each of two ingredients separately: (analysis) on progPartial (init x : pair of two leaves; move x.0; ret), static decisions computed by the whole-local analysis (stdMap at granularity wholeKill, flag maintenance standard; on this straight-line program no flag is tested, flagConfig_gran_inert_on_progPartial) drop nothing at the ret, and the run on [] returns with log [create 0, create 1, consume 0], violating NoLeak; (flags) on progPartialFlag (conditional init, conditional move of x.0), with the standard fine decisions and flag updates at granularity wholeKill, the run on [true, true] returns with log [create 0, create 1, consume 0], violating NoLeak.

**Hypothesis ledger.** None: the statement has no hypotheses (it is about concrete programs and inputs, or it is existential).

**Non-vacuity witness.** progPartial and progPartialFlag (both satisfy all hypotheses of R1; progPartial_stdElab_correct, progPartialFlag_stdElab_correct). (Lean: `wholeKillAnalysis_leaks_remaining_field`, `wholeKillFlags_leaks_remaining_field`)

**Tier rationale.** T0: per-field tracking of partial moves is part of RFC 320's drop obligations and of the mechanized elaborations (RustCompCert; Fukala's tuple support, proof incomplete); this is a concrete trace.

**Prior art.**

- RFC 320 'Non-zeroing dynamic drop', rust-lang/rfcs f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/0320-nonzeroing-dynamic-drop.md lines 6-15 (stack-local boolean flags for 'dynamic drop obligations'), lines 99-114 (drop obligations: a Drop type is one obligation, otherwise the union of its fields'; removed when moved, consumed by a call, or at scope end), lines 116-142 (dynamic obligations at a merge point = union minus intersection of the predecessors' sets), lines 144-155 (subsection 'Stack-local drop flags'; lines 153-155: 'we do not specify the precise set of boolean flags that are injected') [design document, historical; informal]
- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_transform/src/elaborate_drops.rs lines 424-431 (all flags set false at function start), 433-451 (call destination flags set at the start of the return target), 464-520 (per-location flag effects inserted at the location, i.e. before the statement/terminator); compiler/rustc_mir_dataflow/src/drop_flag_effects.rs lines 108-137 (drop_flag_effects_for_location: moves out => Absent) and 139-150 (for_location_inits: InitKind::Unconditional => Present, InitKind::OnReturn => no effect at the call) [source; prose only]
- J. Wu, Y. Wang, L. Yu, L. Meng, 'RustCompCert: A Verified and Verifying Compiler for a Sequential Subset of Rust', arXiv:2602.07455v1 (7 Feb 2026; companion: 'End-to-end Compositional Verification of Program Safety through Verified and Verifying Compilation', arXiv:2510.10015v1); Rocq development github.com/SJTU-PLV/CompCert commit e3d03ed822a7aaf452b7022c347187ed1efc1c12 (branch rust-verified-compiler): rustfrontend/InitAnalysis.v lines 83-84 (maybe-init and maybe-uninit as Kildall fixpoints over a possibly cyclic CFG); rustfrontend/ElaborateDrop.v lines 33-52 (a drop flag for a place that is may-init and not must-init at a drop), 147-181 (flag-guarded drop, flag reset before the drop; once a place has a flag, the guarded form is used at all its drops), 253-276 (flag updates at assignments, moves and calls); rustfrontend/ElaborateDropProof.v lines 4492-4513 (transl_program_correct: forward simulation from the ownership-tracking semantics to the explicit-drop semantics; no Admitted/admit in the file; not compiled here). No unwind, panic or cleanup construct occurs in rustfrontend/ (a call node has one successor). No necessity or minimality statement [mechanized prior art]
- V. Fukala, 'Formalization of Rust Drop Elaboration', Bachelor thesis, Programming Language Foundations Lab, ETH Zurich, August 5, 2024 (supervisors I. van Bakel, R. Jung), PDF https://ethz.ch/content/dam/ethz/special-interest/infk/inst-pls/plf-dam/documents/StudentProjects/BachelorTheses/2024-Viktor-Thesis.pdf: a structured language (if, while, calls, tuples; no control-flow graphs, section 3) with flag-based drop elaboration in Coq; a complete correctness proof for a scalar-only version, and a proof relying on unproved lemmas for tuples (sections 5.4, 6, Appendix A); unwinding left to future work (section 6.1). The Coq repository named in Appendix A requires sign-in and was not inspected [mechanized prior art, partly]

**Design question.** What exactly must elaboration maintain on normal and cleanup edges?

**Non-claims.** See **Boundaries**, common non-claims and the R4c-kill entry.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) for any reading of this result as a statement about a real system. Such a reading relies on the bridges "Atoms, drop obligations and move paths", "Flag maintenance" under **Modeling bridges** below, which state the correspondence, its reasoning and the known mismatches; the kernel check is about the toy model and neither establishes nor refutes these correspondences (model–system relation: none proved).

### R4c-keep: `wholeKeepAnalysis_drops_moved_field / wholeKeepFlags_drops_moved_field`

**Kind:** counterexample. **Tier:** T0. **Depth:** definitional. **Proof status:** proved.

Lean statement (verbatim source quotes):

```lean
-- lean/ToyDropFlags/Counterexamples.lean:258-262
theorem wholeKeepAnalysis_drops_moved_field :
    Forward progPartial ∧ MoveChecked progPartial ∧ NoNormalPathToResume progPartial ∧
    (runElab .abort .std (stdMap progPartial .wholeKeep) progPartial []).log =
      [.create 0, .create 1, .consume 0, .drop 1, .drop 0] ∧
    ¬ NoDoubleDrop (runElab .abort .std (stdMap progPartial .wholeKeep) progPartial []).log := …
```

```lean
-- lean/ToyDropFlags/Counterexamples.lean:267-273
theorem wholeKeepFlags_drops_moved_field :
    Forward progPartialFlag ∧ MoveChecked progPartialFlag ∧ NoNormalPathToResume progPartialFlag ∧
    (runElab .abort { FlagConfig.std with gran := .wholeKeep } (stdMap progPartialFlag .fine)
      progPartialFlag [true, true, false]).log =
      [.create 0, .create 1, .consume 0, .drop 1, .drop 0] ∧
    ¬ NoDoubleDrop (runElab .abort { FlagConfig.std with gran := .wholeKeep }
      (stdMap progPartialFlag .fine) progPartialFlag [true, true, false]).log := …
```

**Plain claim.** Ignoring partial moves breaks exactly-once, in each of two ingredients separately: (analysis) on progPartial, static decisions computed by an analysis that tracks only whole-local moves (stdMap at granularity wholeKeep, flag maintenance standard) drop the moved field: the run on [] has log [create 0, create 1, consume 0, drop 1, drop 0], violating NoDoubleDrop; (flags) on progPartialFlag, with the standard fine decisions and flag updates at granularity wholeKeep, the run on [true, true, false] has log [create 0, create 1, consume 0, drop 1, drop 0], violating NoDoubleDrop.

**Hypothesis ledger.** None: the statement has no hypotheses (it is about concrete programs and inputs, or it is existential).

**Non-vacuity witness.** progPartial and progPartialFlag. (Lean: `wholeKeepAnalysis_drops_moved_field`, `wholeKeepFlags_drops_moved_field`)

**Tier rationale.** T0, as R4c-kill.

**Prior art.**

- RFC 320 'Non-zeroing dynamic drop', rust-lang/rfcs f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/0320-nonzeroing-dynamic-drop.md lines 6-15 (stack-local boolean flags for 'dynamic drop obligations'), lines 99-114 (drop obligations: a Drop type is one obligation, otherwise the union of its fields'; removed when moved, consumed by a call, or at scope end), lines 116-142 (dynamic obligations at a merge point = union minus intersection of the predecessors' sets), lines 144-155 (subsection 'Stack-local drop flags'; lines 153-155: 'we do not specify the precise set of boolean flags that are injected') [design document, historical; informal]
- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_transform/src/elaborate_drops.rs lines 424-431 (all flags set false at function start), 433-451 (call destination flags set at the start of the return target), 464-520 (per-location flag effects inserted at the location, i.e. before the statement/terminator); compiler/rustc_mir_dataflow/src/drop_flag_effects.rs lines 108-137 (drop_flag_effects_for_location: moves out => Absent) and 139-150 (for_location_inits: InitKind::Unconditional => Present, InitKind::OnReturn => no effect at the call) [source; prose only]
- J. Wu, Y. Wang, L. Yu, L. Meng, 'RustCompCert: A Verified and Verifying Compiler for a Sequential Subset of Rust', arXiv:2602.07455v1 (7 Feb 2026; companion: 'End-to-end Compositional Verification of Program Safety through Verified and Verifying Compilation', arXiv:2510.10015v1); Rocq development github.com/SJTU-PLV/CompCert commit e3d03ed822a7aaf452b7022c347187ed1efc1c12 (branch rust-verified-compiler): rustfrontend/InitAnalysis.v lines 83-84 (maybe-init and maybe-uninit as Kildall fixpoints over a possibly cyclic CFG); rustfrontend/ElaborateDrop.v lines 33-52 (a drop flag for a place that is may-init and not must-init at a drop), 147-181 (flag-guarded drop, flag reset before the drop; once a place has a flag, the guarded form is used at all its drops), 253-276 (flag updates at assignments, moves and calls); rustfrontend/ElaborateDropProof.v lines 4492-4513 (transl_program_correct: forward simulation from the ownership-tracking semantics to the explicit-drop semantics; no Admitted/admit in the file; not compiled here). No unwind, panic or cleanup construct occurs in rustfrontend/ (a call node has one successor). No necessity or minimality statement [mechanized prior art]
- V. Fukala, 'Formalization of Rust Drop Elaboration', Bachelor thesis, Programming Language Foundations Lab, ETH Zurich, August 5, 2024 (supervisors I. van Bakel, R. Jung), PDF https://ethz.ch/content/dam/ethz/special-interest/infk/inst-pls/plf-dam/documents/StudentProjects/BachelorTheses/2024-Viktor-Thesis.pdf: a structured language (if, while, calls, tuples; no control-flow graphs, section 3) with flag-based drop elaboration in Coq; a complete correctness proof for a scalar-only version, and a proof relying on unproved lemmas for tuples (sections 5.4, 6, Appendix A); unwinding left to future work (section 6.1). The Coq repository named in Appendix A requires sign-in and was not inspected [mechanized prior art, partly]

**Design question.** What exactly must elaboration maintain on normal and cleanup edges?

**Non-claims.** See **Boundaries**, common non-claims and the R4c-keep entry.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) for any reading of this result as a statement about a real system. Such a reading relies on the bridges "Atoms, drop obligations and move paths", "Flag maintenance" under **Modeling bridges** below, which state the correspondence, its reasoning and the known mismatches; the kernel check is about the toy model and neither establishes nor refutes these correspondences (model–system relation: none proved).

### R4d: `reinitWithoutFlagSet_leaks`

**Kind:** counterexample. **Tier:** T0. **Depth:** definitional. **Proof status:** proved.

Lean statement (verbatim source quote):

```lean
-- lean/ToyDropFlags/Counterexamples.lean:278-285
theorem reinitWithoutFlagSet_leaks :
    Forward progReinit ∧ MoveChecked progReinit ∧ NoNormalPathToResume progReinit ∧
    (runElab .abort { FlagConfig.std with initSetsFlags := fun j => j != 3 }
      (stdMap progReinit .fine) progReinit [true]).outcome = .returned ∧
    (runElab .abort { FlagConfig.std with initSetsFlags := fun j => j != 3 }
      (stdMap progReinit .fine) progReinit [true]).log = [.create 0, .consume 0, .create 1] ∧
    ¬ NoLeak (runElab .abort { FlagConfig.std with initSetsFlags := fun j => j != 3 }
      (stdMap progReinit .fine) progReinit [true]).log := …
```

**Plain claim.** On progReinit (init x; move x; branch; re-init x on one branch; ret), which satisfies all hypotheses of R1 and whose standard elaboration is elaboration-correct (by R1, `stdElab_correct_of_forward_moveChecked_noNormalPathToResume`, since `MoveChecked` is `PlacesAreMovePaths ∧ MovesFromInit ∧ InitsIntoUninit`), omitting only the flag update of the re-initialization at node 3 gives, on input [true], a run that returns with log [create 0, consume 0, create 1], violating NoLeak.

**Hypothesis ledger.** None: the statement has no hypotheses (it is about concrete programs and inputs, or it is existential).

**Non-vacuity witness.** progReinit. (Lean: `reinitWithoutFlagSet_leaks`)

**Tier rationale.** T0: setting the flag at (re-)initialization is part of every flag-based elaboration (RFC 320, rustc, RustCompCert); this is a concrete trace.

**Prior art.**

- RFC 320 'Non-zeroing dynamic drop', rust-lang/rfcs f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/0320-nonzeroing-dynamic-drop.md lines 6-15 (stack-local boolean flags for 'dynamic drop obligations'), lines 99-114 (drop obligations: a Drop type is one obligation, otherwise the union of its fields'; removed when moved, consumed by a call, or at scope end), lines 116-142 (dynamic obligations at a merge point = union minus intersection of the predecessors' sets), lines 144-155 (subsection 'Stack-local drop flags'; lines 153-155: 'we do not specify the precise set of boolean flags that are injected') [design document, historical; informal]
- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_transform/src/elaborate_drops.rs lines 424-431 (all flags set false at function start), 433-451 (call destination flags set at the start of the return target), 464-520 (per-location flag effects inserted at the location, i.e. before the statement/terminator); compiler/rustc_mir_dataflow/src/drop_flag_effects.rs lines 108-137 (drop_flag_effects_for_location: moves out => Absent) and 139-150 (for_location_inits: InitKind::Unconditional => Present, InitKind::OnReturn => no effect at the call) [source; prose only]
- J. Wu, Y. Wang, L. Yu, L. Meng, 'RustCompCert: A Verified and Verifying Compiler for a Sequential Subset of Rust', arXiv:2602.07455v1 (7 Feb 2026; companion: 'End-to-end Compositional Verification of Program Safety through Verified and Verifying Compilation', arXiv:2510.10015v1); Rocq development github.com/SJTU-PLV/CompCert commit e3d03ed822a7aaf452b7022c347187ed1efc1c12 (branch rust-verified-compiler): rustfrontend/InitAnalysis.v lines 83-84 (maybe-init and maybe-uninit as Kildall fixpoints over a possibly cyclic CFG); rustfrontend/ElaborateDrop.v lines 33-52 (a drop flag for a place that is may-init and not must-init at a drop), 147-181 (flag-guarded drop, flag reset before the drop; once a place has a flag, the guarded form is used at all its drops), 253-276 (flag updates at assignments, moves and calls); rustfrontend/ElaborateDropProof.v lines 4492-4513 (transl_program_correct: forward simulation from the ownership-tracking semantics to the explicit-drop semantics; no Admitted/admit in the file; not compiled here). No unwind, panic or cleanup construct occurs in rustfrontend/ (a call node has one successor). No necessity or minimality statement [mechanized prior art]
- V. Fukala, 'Formalization of Rust Drop Elaboration', Bachelor thesis, Programming Language Foundations Lab, ETH Zurich, August 5, 2024 (supervisors I. van Bakel, R. Jung), PDF https://ethz.ch/content/dam/ethz/special-interest/infk/inst-pls/plf-dam/documents/StudentProjects/BachelorTheses/2024-Viktor-Thesis.pdf: a structured language (if, while, calls, tuples; no control-flow graphs, section 3) with flag-based drop elaboration in Coq; a complete correctness proof for a scalar-only version, and a proof relying on unproved lemmas for tuples (sections 5.4, 6, Appendix A); unwinding left to future work (section 6.1). The Coq repository named in Appendix A requires sign-in and was not inspected [mechanized prior art, partly]

**Design question.** What exactly must elaboration maintain on normal and cleanup edges?

**Non-claims.** See **Boundaries**, common non-claims and the R4d entry.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) for any reading of this result as a statement about a real system. Such a reading relies on the bridges "Flag maintenance" under **Modeling bridges** below, which state the correspondence, its reasoning and the known mismatches; the kernel check is about the toy model and neither establishes nor refutes these correspondences (model–system relation: none proved).

### R5: `stdElab_noDoubleDrop_continueUnwind_of_forward_placesAreMovePaths_movesFromInit`

**Kind:** theorem. **Tier:** T1. **Depth:** substantive. **Proof status:** proved.

Lean statement (verbatim source quote):

```lean
-- lean/ToyDropFlags/Results.lean:125-130
theorem stdElab_noDoubleDrop_continueUnwind_of_forward_placesAreMovePaths_movesFromInit
    (s : SProg)
    (hfwd : Forward s) (hplaces : PlacesAreMovePaths s) (hmoves : MovesFromInit s) :
    ∀ inp,
      NoDoubleDrop (runElab .continueUnwind .std (stdMap s .fine) s inp).log ∧
      (runElab .continueUnwind .std (stdMap s .fine) s inp).outcome.terminated = true := …
```

**Plain claim.** Assume that a destructor panic during unwinding continues unwinding (here: leaves the frame, since cleanup drops have no landing pad), and let s be a forward program that only mentions valid move paths and moves only definitely-initialized places (call arguments pairwise disjoint). Then for every input the run of the standard elaboration of s terminates and satisfies NoDoubleDrop (no value destroyed twice, no uncreated value destroyed, no destructor on unwritten memory). InitsIntoUninit and NoNormalPathToResume are not assumed.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hfwd : Forward s` | the one-pass analyses miss back edges; a loop can re-run a move | tight | `noDoubleDrop_continueUnwind_fails_without_forward` | a 1-local (leaf), 4-node program with one back edge (progLoopMove) |
| `hplaces : PlacesAreMovePaths s` | an init inside a struct with its own destructor leaves the struct's own unit unwritten, so its drop runs on unwritten memory | tight | `noDoubleDrop_continueUnwind_fails_without_placesAreMovePaths` | a 1-local, 2-node forward program whose local is a struct with its own destructor (progInitInsideDrop) |
| `hmoves : MovesFromInit s` | a use after move hands the same value to two consumers | tight | `noDoubleDrop_continueUnwind_fails_without_movesFromInit` | a 1-local (leaf), 4-node forward program (progUseAfterMove) |

**Non-vacuity witness.** progUnwind (a two-field struct live across a call) satisfies the three hypotheses and the conclusion is kernel-checked on all its runs. (Lean: `continueUnwind_noDoubleDrop_holds_progUnwind`)

**Tier rationale.** T1 (folklore about why panics in cleanup terminate; not found mechanized).

**Prior art.**

- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_transform/src/elaborate_drop.rs lines 49-56 and 66-71 (Unwind::InCleanup: 'Already in an unwind path, any panic will cause an abort.'; into_action => UnwindAction::Terminate(UnwindTerminateReason::InCleanup)); elaborate_drops.rs lines 359-375 (drops in cleanup blocks get Unwind::InCleanup); compiler/rustc_middle/src/mir/syntax.rs lines 657-683 (cleanup blocks: every unwind field must be Terminate or Unreachable; Return is not allowed; blocks reachable from cleanup blocks are cleanup) and 1010-1038 (UnwindAction::Terminate 'Terminates the execution if unwind happens'); compiler/rustc_mir_transform/src/validate.rs lines 246-275 (the validator rejects Cleanup or Continue unwind actions in cleanup blocks); library/core/src/panicking.rs lines 356-370 (lang item panic_in_cleanup: non-unwinding panic 'panic in a destructor during cleanup') [source; prose only]
- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, library/core/src/ops/drop.rs lines 221-235 (Drop::drop: a panic in drop during unwinding (a 'double panic') 'will likely abort the program'; 'even if this panics, the value is considered to be dropped') [documentation]
- C++ working draft N4950 (C++23; cplusplus/draft tag n4950 = commit 4e4de1df8ee941255b653b61d0a62050b34cf8c9, source/exceptions.tex): [except.throw]/7 (normative: 'If the exception handling mechanism handling an uncaught exception directly invokes a function that exits via an exception, the function std::terminate is invoked', with Note 5: a destructor directly invoked by stack unwinding that exits via an exception invokes std::terminate); [except.terminate]/1 Note 1 item (1.4) (informative note listing that case); [except.terminate]/2 (normative: in that case the stack shall not be unwound before std::terminate is invoked); [except.ctor]/3 (normative: if a destructor is terminated by an exception, the remaining subobject destructors are still invoked); [except.spec]/3 and /8 (a destructor without a noexcept-specifier is potentially-throwing iff a destructor of a potentially constructed subobject (or, for a virtual destructor, of a virtual base) is potentially-throwing; otherwise it is non-throwing) and /5 (an exception reaching the outermost block of a non-throwing function invokes std::terminate) [normative unless marked as a note; prose only]

**Design question.** What happens when a destructor panics during unwinding?

**Non-claims.** See **Boundaries**, common non-claims and the R5 entry.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) for any reading of this result as a statement about a real system. Such a reading relies on the bridges "Abort rule in rustc and C++", "Cleanup code and MIR cleanup blocks", "Drop glue as one step" under **Modeling bridges** below, which state the correspondence, its reasoning and the known mismatches; the kernel check is about the toy model and neither establishes nor refutes these correspondences (model–system relation: none proved).

Remark (proved, not a separate card): the same simulation, `runElab_good`, gives no double destruction and termination for every decision map compatible with the fine analyses under either panic rule, from `Forward`, `PlacesAreMovePaths` and `MovesFromInit`; R5 is its instance for the standard map under the continue-unwinding rule.

### R6: `continueUnwind_completedUnwind_leaks_of_forward_moveChecked / continueUnwind_not_elabCorrect_for_all_forward_moveChecked`

**Kind:** impossibility. **Tier:** T1. **Depth:** definitional. **Proof status:** proved.

Lean statement (verbatim source quotes):

```lean
-- lean/ToyDropFlags/Results.lean:142-148
theorem continueUnwind_completedUnwind_leaks_of_forward_moveChecked :
    ∃ (s : SProg) (inp : List Bool),
      Forward s ∧ PlacesAreMovePaths s ∧ MovesFromInit s ∧ InitsIntoUninit s ∧
      NoNormalPathToResume s ∧
      (runElab .continueUnwind .std (stdMap s .fine) s inp).outcome = .unwound ∧
      NoDoubleDrop (runElab .continueUnwind .std (stdMap s .fine) s inp).log ∧
      ¬ NoLeak (runElab .continueUnwind .std (stdMap s .fine) s inp).log := …
```

```lean
-- lean/ToyDropFlags/Results.lean:156-158
theorem continueUnwind_not_elabCorrect_for_all_forward_moveChecked :
    ¬ ∀ s : SProg, Forward s → PlacesAreMovePaths s → MovesFromInit s → InitsIntoUninit s →
        NoNormalPathToResume s → ElabCorrect .continueUnwind .std (stdMap s .fine) s := …
```

**Plain claim.** Assume that a destructor panic during unwinding continues unwinding (leaves the frame) instead of aborting. Then there is a program satisfying every hypothesis of R1 — progUnwind: a struct without its own destructor whose two leaf fields are live across a call whose unwind edge goes directly to a resume node — and an input, [true, true] (the call panics, then the destructor of the first field dropped by the cleanup ladder panics), on which the run of the standard elaboration completes an unwind, satisfies NoDoubleDrop, and violates NoLeak (the other field is never destroyed). Hence, under this rule, the standard elaboration is not elaboration-correct for every program satisfying R1's hypotheses.

**Hypothesis ledger.** None: the statement has no hypotheses (it is about concrete programs and inputs, or it is existential).

**Non-vacuity witness.** The witness program and input are part of the statement (continueUnwind_leaks_partially_dropped: log [create 0, create 1, drop 1], outcome unwound). (Lean: `continueUnwind_leaks_partially_dropped`)

**Positive control** (a nearby setting where the impossibility's conclusion fails): `progUnwind_stdElab_correct_abort`, `abort_on_same_input`.

**Tier rationale.** T1 (the rationale for terminating on a panic during cleanup is folklore; not found mechanized).

**Prior art.**

- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_transform/src/elaborate_drop.rs lines 49-56 and 66-71 (Unwind::InCleanup: 'Already in an unwind path, any panic will cause an abort.'; into_action => UnwindAction::Terminate(UnwindTerminateReason::InCleanup)); elaborate_drops.rs lines 359-375 (drops in cleanup blocks get Unwind::InCleanup); compiler/rustc_middle/src/mir/syntax.rs lines 657-683 (cleanup blocks: every unwind field must be Terminate or Unreachable; Return is not allowed; blocks reachable from cleanup blocks are cleanup) and 1010-1038 (UnwindAction::Terminate 'Terminates the execution if unwind happens'); compiler/rustc_mir_transform/src/validate.rs lines 246-275 (the validator rejects Cleanup or Continue unwind actions in cleanup blocks); library/core/src/panicking.rs lines 356-370 (lang item panic_in_cleanup: non-unwinding panic 'panic in a destructor during cleanup') [source; prose only]
- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, library/core/src/ops/drop.rs lines 221-235 (Drop::drop: a panic in drop during unwinding (a 'double panic') 'will likely abort the program'; 'even if this panics, the value is considered to be dropped') [documentation]
- C++ working draft N4950 (C++23; cplusplus/draft tag n4950 = commit 4e4de1df8ee941255b653b61d0a62050b34cf8c9, source/exceptions.tex): [except.throw]/7 (normative: 'If the exception handling mechanism handling an uncaught exception directly invokes a function that exits via an exception, the function std::terminate is invoked', with Note 5: a destructor directly invoked by stack unwinding that exits via an exception invokes std::terminate); [except.terminate]/1 Note 1 item (1.4) (informative note listing that case); [except.terminate]/2 (normative: in that case the stack shall not be unwound before std::terminate is invoked); [except.ctor]/3 (normative: if a destructor is terminated by an exception, the remaining subobject destructors are still invoked); [except.spec]/3 and /8 (a destructor without a noexcept-specifier is potentially-throwing iff a destructor of a potentially constructed subobject (or, for a virtual destructor, of a virtual base) is potentially-throwing; otherwise it is non-throwing) and /5 (an exception reaching the outermost block of a non-throwing function invokes std::terminate) [normative unless marked as a note; prose only]
- The Rust Reference, rust-lang/reference c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c: src/destructors.md r[destructors.intro] (a partially initialized variable drops only its initialized fields), r[destructors.operation] (Drop::drop, then fields in declaration order); src/panic.md r[panic.unwind.destruction]. No statement of a panic-during-unwinding abort rule was found in src/destructors.md, src/panic.md, src/items/functions.md or src/runtime.md at this commit [normative; negative finding]

**Design question.** What happens when a destructor panics during unwinding?

**Non-claims.** See **Boundaries**, common non-claims and the R6 entry.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) for any reading of this result as a statement about a real system. Such a reading relies on the bridges "Abort rule in rustc and C++", "Drop glue as one step" under **Modeling bridges** below, which state the correspondence, its reasoning and the known mismatches; the kernel check is about the toy model and neither establishes nor refutes these correspondences (model–system relation: none proved).

### R7: `stdFlagSet_subset_of_exactlyOnce_of_placesAreMovePaths`

**Kind:** theorem. **Tier:** T1. **Depth:** shallow. **Proof status:** proved (from R2n).

Lean statement (verbatim source quote):

```lean
-- lean/ToyDropFlags/Results.lean:170-173
theorem stdFlagSet_subset_of_exactlyOnce_of_placesAreMovePaths (s : SProg)
    (hplaces : PlacesAreMovePaths s) (d : Nat → Place → Decision)
    (hd : ∀ inp, ExactlyOnce (runElab .abort .std d s inp)) :
    ∀ a ∈ flagSet s (stdMap s .fine), a ∈ flagSet s d := …
```

**Plain claim.** Assume only that every place mentioned by the program s is a valid move path. If every run of the elaboration of s with decision map d (same CFG, one flag per atom, standard flag maintenance, abort rule; a run is the result of `runElab`, the target semantics `run` with step bound `fuelFor s`, on one input bit stream) is exactly-once, then every atom that the standard map tests at some forward-reachable drop point is also tested by d at some forward-reachable drop point: the standard flag set is a lower bound (subset) of d's flag set. This does not assert that the standard map is itself elaboration-correct.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hplaces : PlacesAreMovePaths s` | an ill-typed init makes the analysis demand a flag that no run needs | tight | `flagSubset_fails_without_placesAreMovePaths` | a 1-local (leaf), 3-node forward program with one ill-typed place (progIllTyped) |
| `hd : ∀ inp, ExactlyOnce (runElab .abort .std d s inp)` | an incorrect map can test fewer atoms | tight | `flagSubset_fails_without_exactlyOnce` | a 1-local (leaf), 4-node forward program (progJoin) with the decision map that drops x unconditionally at the join |

**Non-vacuity witness.** progJoin with the map that tests x at every drop point (every run exactly-once; flag sets [x] and [x]). (Lean: `stdFlagSet_subset_witness_progJoin`)

**Tier rationale.** T1. RFC 320 leaves the flag set unspecified and rustc allocates flags exactly for may-init ∧ may-uninit places; a minimality statement was not found, informal or mechanized, beyond these.

**Prior art.**

- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_transform/src/elaborate_drops.rs lines 165-188 (drop_style: (maybe_init, maybe_uninit) = (false, _) => Dead, (true, false) => Static, (true, true) => Conditional/Open) and lines 290-334 (collect_drop_flags; lines 310-312 create a flag iff maybe_init && maybe_uninit at a drop) [source; prose only]
- RFC 320 'Non-zeroing dynamic drop', rust-lang/rfcs f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/0320-nonzeroing-dynamic-drop.md lines 6-15 (stack-local boolean flags for 'dynamic drop obligations'), lines 99-114 (drop obligations: a Drop type is one obligation, otherwise the union of its fields'; removed when moved, consumed by a call, or at scope end), lines 116-142 (dynamic obligations at a merge point = union minus intersection of the predecessors' sets), lines 144-155 (subsection 'Stack-local drop flags'; lines 153-155: 'we do not specify the precise set of boolean flags that are injected') [design document, historical; informal]
- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_dataflow/src/move_paths/builder.rs lines 24-70 (root move paths per local), 107-305 (move_path_for: a child move path is created, lines 283-294, only for a projection visited while gathering the body's moves and inits, lines 346-412), 180-184 (no descent into an ADT with a destructor); compiler/rustc_mir_transform/src/elaborate_drop.rs lines 725-728 ('when dropping an ADT, multiple fields may be joined together under the rest subpath. They are all controlled by the primary drop flag') and 1533-1558 (drop_flag_reset_block: flags reset after drops on normal paths, not on unwind paths) [source; prose only]
- J. Wu, Y. Wang, L. Yu, L. Meng, 'RustCompCert: A Verified and Verifying Compiler for a Sequential Subset of Rust', arXiv:2602.07455v1 (7 Feb 2026; companion: 'End-to-end Compositional Verification of Program Safety through Verified and Verifying Compilation', arXiv:2510.10015v1); Rocq development github.com/SJTU-PLV/CompCert commit e3d03ed822a7aaf452b7022c347187ed1efc1c12 (branch rust-verified-compiler): rustfrontend/InitAnalysis.v lines 83-84 (maybe-init and maybe-uninit as Kildall fixpoints over a possibly cyclic CFG); rustfrontend/ElaborateDrop.v lines 33-52 (a drop flag for a place that is may-init and not must-init at a drop), 147-181 (flag-guarded drop, flag reset before the drop; once a place has a flag, the guarded form is used at all its drops), 253-276 (flag updates at assignments, moves and calls); rustfrontend/ElaborateDropProof.v lines 4492-4513 (transl_program_correct: forward simulation from the ownership-tracking semantics to the explicit-drop semantics; no Admitted/admit in the file; not compiled here). No unwind, panic or cleanup construct occurs in rustfrontend/ (a call node has one successor). No necessity or minimality statement [mechanized prior art]
- V. Fukala, 'Formalization of Rust Drop Elaboration', Bachelor thesis, Programming Language Foundations Lab, ETH Zurich, August 5, 2024 (supervisors I. van Bakel, R. Jung), PDF https://ethz.ch/content/dam/ethz/special-interest/infk/inst-pls/plf-dam/documents/StudentProjects/BachelorTheses/2024-Viktor-Thesis.pdf: a structured language (if, while, calls, tuples; no control-flow graphs, section 3) with flag-based drop elaboration in Coq; a complete correctness proof for a scalar-only version, and a proof relying on unproved lemmas for tuples (sections 5.4, 6, Appendix A); unwinding left to future work (section 6.1). The Coq repository named in Appendix A requires sign-in and was not inspected [mechanized prior art, partly]

**Design question.** Is the analysis-driven flag placement minimal?

**Non-claims.** See **Boundaries**, common non-claims and the R7 entry.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) for any reading of this result as a statement about a real system. Such a reading relies on the bridges "Atoms, drop obligations and move paths", "Standard decision and rustc drop styles" under **Modeling bridges** below, which state the correspondence, its reasoning and the known mismatches; the kernel check is about the toy model and neither establishes nor refutes these correspondences (model–system relation: none proved).

### R7L: `stdMap_correct_and_flagSet_least_of_forward_moveChecked_noNormalPathToResume`

**Kind:** theorem. **Tier:** T1. **Depth:** shallow. **Proof status:** proved (from R1 and R7).

Lean statement (verbatim source quote):

```lean
-- lean/ToyDropFlags/Results.lean:198-203
theorem stdMap_correct_and_flagSet_least_of_forward_moveChecked_noNormalPathToResume (s : SProg)
    (hfwd : Forward s) (hplaces : PlacesAreMovePaths s) (hmoves : MovesFromInit s)
    (hinits : InitsIntoUninit s) (hclean : NoNormalPathToResume s) :
    ElabCorrect .abort .std (stdMap s .fine) s ∧
    ∀ d : Nat → Place → Decision, ElabCorrect .abort .std d s →
      ∀ a ∈ flagSet s (stdMap s .fine), a ∈ flagSet s d := …
```

**Plain claim.** Assume that a destructor panic during unwinding aborts the process and let s be a forward (acyclic, topologically numbered) toy program that only mentions valid move paths, moves only definitely-initialized places (call arguments pairwise disjoint), initializes only definitely-uninitialized places, and has no resume node reachable from the entry along normal edges only. Then the standard decision map is elaboration-correct, and every elaboration-correct decision map (same CFG, one flag per atom, standard flag maintenance) tests every atom that the standard map tests at some forward-reachable drop point; so the standard flag set is the least flag set among elaboration-correct decision maps of this class.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hfwd : Forward s` | the one-pass initialization analyses follow index-increasing edges only, which are all edges exactly when the program is forward (acyclic, topologically numbered) | tight | `stdFlagLeast_fails_without_forward` | a 1-local (leaf), 3-node program with one back edge (progLoop) |
| `hplaces : PlacesAreMovePaths s` | every mentioned place follows its local's type and never enters a struct with its own destructor, so the analysis's atoms match the units written and destroyed | tight | `stdFlagLeast_fails_without_placesAreMovePaths` | a 1-local, 3-node forward program whose local is a struct with its own destructor and two leaf fields (progDropStruct) |
| `hmoves : MovesFromInit s` | no use after move: every moved place (and call argument) is must-init, and call arguments are pairwise disjoint | tight | `stdFlagLeast_fails_without_movesFromInit` | a 1-local (leaf), 4-node forward program (progUseAfterMove) |
| `hinits : InitsIntoUninit s` | no overwrite of an owned value: every initialized place (and call destination not overlapped by an argument) is not may-init | tight | `stdFlagLeast_fails_without_initsIntoUninit` | a 1-local (leaf), 3-node forward program (progOverwrite) |
| `hclean : NoNormalPathToResume s` | no resume node is reachable from the entry along normal edges only, so a resume ladder (whose drops have no landing pad) runs only while unwinding, where a destructor panic aborts | tight | `stdFlagLeast_fails_without_noNormalPathToResume` | a 2-local (two leaves), 3-node forward program (progResumeNormal) |

**Non-vacuity witness.** progCleanup satisfies all five hypotheses. (Lean: `exactlyOnce_hypotheses_hold_progCleanup`)

**Tier rationale.** T1, as R7.

**Prior art.**

- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_transform/src/elaborate_drops.rs lines 165-188 (drop_style: (maybe_init, maybe_uninit) = (false, _) => Dead, (true, false) => Static, (true, true) => Conditional/Open) and lines 290-334 (collect_drop_flags; lines 310-312 create a flag iff maybe_init && maybe_uninit at a drop) [source; prose only]
- RFC 320 'Non-zeroing dynamic drop', rust-lang/rfcs f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/0320-nonzeroing-dynamic-drop.md lines 6-15 (stack-local boolean flags for 'dynamic drop obligations'), lines 99-114 (drop obligations: a Drop type is one obligation, otherwise the union of its fields'; removed when moved, consumed by a call, or at scope end), lines 116-142 (dynamic obligations at a merge point = union minus intersection of the predecessors' sets), lines 144-155 (subsection 'Stack-local drop flags'; lines 153-155: 'we do not specify the precise set of boolean flags that are injected') [design document, historical; informal]
- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_dataflow/src/move_paths/builder.rs lines 24-70 (root move paths per local), 107-305 (move_path_for: a child move path is created, lines 283-294, only for a projection visited while gathering the body's moves and inits, lines 346-412), 180-184 (no descent into an ADT with a destructor); compiler/rustc_mir_transform/src/elaborate_drop.rs lines 725-728 ('when dropping an ADT, multiple fields may be joined together under the rest subpath. They are all controlled by the primary drop flag') and 1533-1558 (drop_flag_reset_block: flags reset after drops on normal paths, not on unwind paths) [source; prose only]
- J. Wu, Y. Wang, L. Yu, L. Meng, 'RustCompCert: A Verified and Verifying Compiler for a Sequential Subset of Rust', arXiv:2602.07455v1 (7 Feb 2026; companion: 'End-to-end Compositional Verification of Program Safety through Verified and Verifying Compilation', arXiv:2510.10015v1); Rocq development github.com/SJTU-PLV/CompCert commit e3d03ed822a7aaf452b7022c347187ed1efc1c12 (branch rust-verified-compiler): rustfrontend/InitAnalysis.v lines 83-84 (maybe-init and maybe-uninit as Kildall fixpoints over a possibly cyclic CFG); rustfrontend/ElaborateDrop.v lines 33-52 (a drop flag for a place that is may-init and not must-init at a drop), 147-181 (flag-guarded drop, flag reset before the drop; once a place has a flag, the guarded form is used at all its drops), 253-276 (flag updates at assignments, moves and calls); rustfrontend/ElaborateDropProof.v lines 4492-4513 (transl_program_correct: forward simulation from the ownership-tracking semantics to the explicit-drop semantics; no Admitted/admit in the file; not compiled here). No unwind, panic or cleanup construct occurs in rustfrontend/ (a call node has one successor). No necessity or minimality statement [mechanized prior art]
- V. Fukala, 'Formalization of Rust Drop Elaboration', Bachelor thesis, Programming Language Foundations Lab, ETH Zurich, August 5, 2024 (supervisors I. van Bakel, R. Jung), PDF https://ethz.ch/content/dam/ethz/special-interest/infk/inst-pls/plf-dam/documents/StudentProjects/BachelorTheses/2024-Viktor-Thesis.pdf: a structured language (if, while, calls, tuples; no control-flow graphs, section 3) with flag-based drop elaboration in Coq; a complete correctness proof for a scalar-only version, and a proof relying on unproved lemmas for tuples (sections 5.4, 6, Appendix A); unwinding left to future work (section 6.1). The Coq repository named in Appendix A requires sign-in and was not inspected [mechanized prior art, partly]

**Design question.** Is the analysis-driven flag placement minimal?

**Non-claims.** See **Boundaries**, common non-claims and the R7L entry.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) for any reading of this result as a statement about a real system. Such a reading relies on the bridges "Atoms, drop obligations and move paths", "Standard decision and rustc drop styles", "Abort rule in rustc and C++" under **Modeling bridges** below, which state the correspondence, its reasoning and the known mismatches; the kernel check is about the toy model and neither establishes nor refutes these correspondences (model–system relation: none proved).

### R8: `fewerFlags_than_std_not_exactlyOnce_of_placesAreMovePaths`

**Kind:** impossibility. **Tier:** T1. **Depth:** shallow. **Proof status:** proved (from R7).

Lean statement (verbatim source quote):

```lean
-- lean/ToyDropFlags/Results.lean:215-218
theorem fewerFlags_than_std_not_exactlyOnce_of_placesAreMovePaths (s : SProg)
    (hplaces : PlacesAreMovePaths s) (d : Nat → Place → Decision)
    (hlt : (flagSet s d).length < (flagSet s (stdMap s .fine)).length) :
    ∃ inp, ¬ ExactlyOnce (runElab .abort .std d s inp) := …
```

**Plain claim.** Assume only that every place mentioned by the program s is a valid move path. If a decision map d (same CFG, one flag per atom, standard flag maintenance, abort rule) has a strictly shorter flag set than the standard map (atoms tested at forward-reachable drop points), then some input gives a run of d's elaboration (the result of `runElab`, the target semantics `run` with step bound `fuelFor s`) that is not exactly-once.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hplaces : PlacesAreMovePaths s` | an ill-typed init makes the analysis demand a flag that no run needs | tight | `fewerFlags_fails_without_placesAreMovePaths` | a 1-local (leaf), 3-node forward program with one ill-typed place (progIllTyped) |
| `hlt : (flagSet s d).length < (flagSet s (stdMap s .fine)).length` | with as many flags, the standard map itself is correct | tight | `fewerFlags_fails_without_lt` | a 1-local (leaf), 4-node forward program (progJoin) with the standard map compared to itself |

**Non-vacuity witness.** progJoin with the map that drops x unconditionally at the join: flag sets [] and [x]; input [true] double-drops. (Lean: `fewerFlags_hypotheses_hold_progJoin`)

**Positive control** (a nearby setting where the impossibility's conclusion fails): `dupProg_matches_stdElab_progJoin`, `shareProg_matches_stdElab_progShare`, `earlyDropProg_matches_stdElab_progJoin`.

**Tier rationale.** T1, as R7 (a counting corollary of R7).

**Prior art.**

- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_transform/src/elaborate_drops.rs lines 165-188 (drop_style: (maybe_init, maybe_uninit) = (false, _) => Dead, (true, false) => Static, (true, true) => Conditional/Open) and lines 290-334 (collect_drop_flags; lines 310-312 create a flag iff maybe_init && maybe_uninit at a drop) [source; prose only]
- RFC 320 'Non-zeroing dynamic drop', rust-lang/rfcs f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/0320-nonzeroing-dynamic-drop.md lines 6-15 (stack-local boolean flags for 'dynamic drop obligations'), lines 99-114 (drop obligations: a Drop type is one obligation, otherwise the union of its fields'; removed when moved, consumed by a call, or at scope end), lines 116-142 (dynamic obligations at a merge point = union minus intersection of the predecessors' sets), lines 144-155 (subsection 'Stack-local drop flags'; lines 153-155: 'we do not specify the precise set of boolean flags that are injected') [design document, historical; informal]
- RFC 320, rust-lang/rfcs f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/0320-nonzeroing-dynamic-drop.md lines 50-55, 59-64, 68-75 (the withdrawn 'static drop semantics' proposal, RFC PR #210: drop certain values earlier so that the drop obligations agree at every merge point; rejected as non-intuitive) [design document, historical]
- rust-lang/rust c7d5ba59d8e11ee2e2204b173458eec4cb41c973, compiler/rustc_mir_dataflow/src/move_paths/builder.rs lines 24-70 (root move paths per local), 107-305 (move_path_for: a child move path is created, lines 283-294, only for a projection visited while gathering the body's moves and inits, lines 346-412), 180-184 (no descent into an ADT with a destructor); compiler/rustc_mir_transform/src/elaborate_drop.rs lines 725-728 ('when dropping an ADT, multiple fields may be joined together under the rest subpath. They are all controlled by the primary drop flag') and 1533-1558 (drop_flag_reset_block: flags reset after drops on normal paths, not on unwind paths) [source; prose only]

**Design question.** Is the analysis-driven flag placement minimal?

**Non-claims.** See **Boundaries**, common non-claims and the R8 entry.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) for any reading of this result as a statement about a real system. Such a reading relies on the bridges "Atoms, drop obligations and move paths", "Standard decision and rustc drop styles" under **Modeling bridges** below, which state the correspondence, its reasoning and the known mismatches; the kernel check is about the toy model and neither establishes nor refutes these correspondences (model–system relation: none proved).

### Modeling bridges

Each item is a separate claim connecting the toy model to a real system, reasoned from the cited sources (listed under **Evidence**); none is kernel-checked, and none is implied by the theorems above (model–system relation: none proved).

- **Atoms, drop obligations and move paths.** RFC 320 defines a local's drop obligations structurally: a type implementing `Drop` is one obligation, otherwise the union of its fields' obligations. This is `Ty.atoms`, which splits every struct without a destructor eagerly. rustc's move-path data is built lazily: a child move path exists for a projection that occurs in the function body, and no move path is created below a type with a destructor; at a drop, fields without their own move path are dropped together under the parent's ("rest") flag. So for a struct without a destructor that is never moved field by field, rustc tracks one move path and needs at most one flag, where the toy tracks one atom per field and `flagSet` of the standard map can count two. The toy's per-atom state coincides with rustc's per-move-path state when every field is mentioned separately; elsewhere rustc's choice corresponds to the flag-sharing positive control `shareProg_matches_stdElab_progShare`, which is outside the class of R2–R8.

  Basis: derived (modeling bridge)

- **Standard decision and rustc drop styles.** rustc's `drop_style` maps `(maybe_init, maybe_uninit)` to `Dead` (`maybe_init = false`), `Static` (`true, false`) and `Conditional`/`Open` (`true, true`), and `collect_drop_flags` creates a flag exactly when `maybe_init && maybe_uninit` at some drop. With must-init = ¬maybe-uninit this is `stdDecision`/`flagSet`; `Open` (a partially initialized aggregate dropped field by field) corresponds to the toy's per-atom ladder. rustc's analyses are fixpoints over cyclic CFGs; the toy's are one pass over forward programs.

  Basis: derived (modeling bridge)

- **Flag maintenance.** rustc sets all flags false at function start, inserts per-location flag effects at the location (so the flags of a call's moved-out arguments are cleared before the call, on both its return and its unwind edge), and sets a call destination's flags at the start of the return target. This is `FlagConfig.std`; R4b models clearing the arguments' flags on the return edge alone. rustc also resets a dropped place's flag after a drop on normal paths, which MIR needs because it has drops at scope exits inside a function; the toy's drops occur at frame exits and never reset flags.

  Basis: derived (modeling bridge)

- **Cleanup code and MIR cleanup blocks.** In MIR, cleanup blocks are entered along unwind edges and may form a sub-CFG of several blocks; a cleanup block may not contain `Return`, every block reachable from a cleanup block is itself cleanup, and every call or drop in a cleanup block has unwind action `Terminate` (or `Unreachable`), so a panic escaping it terminates instead of unwinding further. `NoNormalPathToResume` is the toy's counterpart and is weaker: it requires that a `resume` is never reached without an unwind edge, so it also admits unwind edges that lead back into code that returns (`progUnwindToRet`), and a call in the toy's cleanup code may panic and continue unwinding.

  Basis: derived (modeling bridge)

- **Abort rule in rustc and C++.** rustc gives drops in cleanup blocks `Unwind::InCleanup`, lowered to `UnwindAction::Terminate(InCleanup)`, and the `panic_in_cleanup` lang item is a non-unwinding panic; the user-facing statement is in `Drop::drop`'s documentation ("will likely abort"). C++ invokes `std::terminate` when a function directly invoked by the exception handling mechanism, such as a destructor run by stack unwinding, exits via an exception ([except.throw]/7, normative; also listed in the informative note [except.terminate]/1 Note 1 (1.4)), and in that case the stack is not unwound further before `std::terminate` ([except.terminate]/2). A C++ destructor without a noexcept-specifier is non-throwing unless a destructor of one of its potentially constructed subobjects (or, for a virtual destructor, of a virtual base) is potentially-throwing ([except.spec]/3, /8), and an exception reaching the outermost block of a non-throwing function invokes `std::terminate` even when no unwinding is in progress ([except.spec]/5). The toy's destructors, which may panic as a first panic and propagate, correspond to potentially-throwing destructors (for example ones declared `noexcept(false)`). `PanicRule.abort` with landing-pad-free cleanup drops models the terminate-on-second-panic behaviour; `continueUnwind` models replacing that terminate action by "continue unwinding to the caller", a hypothetical design that is not the current behaviour of either language.

  Basis: derived (modeling bridge)

- **Drop glue as one step.** C++ still runs the remaining subobject destructors when a destructor exits via an exception ([except.ctor]/3); rustc's drop shims likewise drop remaining fields on the unwind path. The toy collapses an atom's glue into one step whose internal cleanup always completes.

  Basis: derived (modeling bridge)

Whether a C++ compiler's conditional-cleanup machinery for temporaries corresponds to drop flags was not examined.

## Boundaries

### Non-claims common to several results

- (R1, R2s, R2, R2n, R3, R4a, R4a-skip, R4b, R4c-kill, R4c-keep, R4d, R5, R6, R7, R7L, R8) These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, a C++ implementation or any real program (model–system relation: none proved). Connections to real systems are separate derived (modeling bridge) claims.
- (R1, R2s, R2, R2n, R3, R7, R7L, R8) Branches, call panics and destructor panics are independent free input bits; the theorem quantifies over all of them, not over the feasible paths of a real program. With correlated conditions a flag the analysis requires can be semantically unnecessary (not proved here).
- (R1, R2s, R2, R2n, R3, R5) Every `Ty` in the model contains at least one destructor unit (`leaf` always logs destruction); non-droppable (`Copy`/scalar) fields, `Drop` structs whose fields are purely scalar, and suppression of drop flags for types without destructors (`ty.needs_drop`) are not modeled.
- (R4a, R4a-skip, R4b, R4c-kill, R4c-keep, R4d) Each row shows one program and one input: it does not show that the failure mode is the only possible one for that defect, that every program in the class fails, or rank the defects.
- (R1, R2s, R2, R5, R7L) The results concern acyclic (forward) programs; they neither establish nor refute the corresponding claims for programs with loops, whose fixpoint analyses are not modelled (stdElab_fails_without_forward shows that the one-pass analysis is wrong on a loop).
- (R1, R2s, R2, R5) In this model drop points occur only at frame-exit terminators (`ret` and `resume`), so `FlagConfig.std` never clears an atom's drop flag after dropping it. In an IR where drops also occur at mid-function scope exits, loop exits, or overwrites (such as Rust MIR `TerminatorKind::Drop`), normal drop paths must also reset the dropped place's flag to `false` or outer scope exits will double-drop (not proved here).
- (R1, R2s, R5, R6) Each `drop a` executes the entire drop glue of atom `a` (including a `Drop` struct's own destructor and all of its fields' destructors) in one step with a single panic bit; a panic in `Drop::drop` followed by a second panic in a field destructor inside the same atom's drop shim is not modeled.
- (R4a, R4a-skip, R4b, R4d) The program satisfies all hypotheses of R1, and its unchanged standard elaboration is elaboration-correct on all inputs (kernel-checked; by R1, `stdElab_correct_of_forward_moveChecked_noNormalPathToResume`), so the failure is caused by the one changed ingredient.
- (R1, R2s, R2) `NoNormalPathToResume` constrains only how `resume` nodes are reached: unwind edges may lead to cleanup code of several nodes (branches, moves, calls, merges with normal code). Unwind edges may also lead back into code that returns, which MIR forbids for cleanup blocks. A call inside cleanup code that panics is treated like any other panicking call (control goes to its unwind successor, still unwinding); in MIR a call or drop in a cleanup block has unwind action Terminate (or Unreachable), so a panic escaping it terminates. That restriction is not modelled; only a destructor panic during unwinding is subject to the panic rule.
- (R1, R2s, R5) NoDoubleDrop and NoLeak count events per id and do not check their order; drop order among atoms is a modelling device and is not checked against the language's drop-order rules.
- (R2s, R2, R2n) Drop points that are not forward-reachable are unconstrained (AllCompatible and flagSet ignore them). On a forward program every edge is index-increasing, so these are exactly the unreachable drop points; on other programs forward reachability is the index-increasing approximation of reachability (forwardReachable_ignores_backward_index_edges).
- (R7, R7L, R8) The class of elaborations compared is fixed: the source CFG is kept, there is one flag per atom (maintained at every init, move and call), and only the per-(drop point, atom) decision varies. Elaborations outside this class can use fewer flags: duplicating the join (dupProg_matches_stdElab_progJoin), sharing one flag across atoms whose states are correlated (shareProg_matches_stdElab_progShare), and dropping early on one branch before a shared exit (earlyDropProg_matches_stdElab_progJoin), all proved for one program each; encoding initialization in memory by zeroing or value niches is not modelled; correlated branch predicates can make one side of a may-init-but-not-must-init split infeasible (not proved here).
- (R2n, R7, R8) `ExactlyOnce` exempts runs whose outcome is `aborted`, `stuck` or `outOfFuel` from NoLeak: its leak clause is guarded by `Outcome.complete`, which is true for `returned` and `unwound` and false for the other outcomes. Termination is not assumed, and runs are results of `runElab`, cut off at the step bound `fuelFor s` (outcome `outOfFuel`).
- (R7, R7L, R8) `Ty.atoms` splits every struct without its own destructor eagerly into its fields, like RFC 320's structural drop obligations. rustc creates child move paths only for projections that occur in the body and drops the remaining fields under the parent's flag, so for a struct moved only as a whole it uses one flag where flagSet of the standard map counts two (derived (modeling bridge); not proved here).

### Non-claims per result

#### R1

- Not modelled: enums/sums and moves out of variant fields; arrays/slices; moves between locals; assignment with implicit drop of the old value (drop-and-replace); borrows; nested scopes with their own exits (drop points are only ret/resume); catch_unwind; async drops.
- Aborted runs are exempt from NoLeak: process abort is treated as reclaiming everything, so under the abort rule a double panic satisfies ExactlyOnce's leak clause by definition.
- It is about one flag maintenance (`FlagConfig.std`); R4b and R4d show that two single deviations from it break exactly-once on one program each, not that it is the only correct maintenance.
- Other correct decision maps exist (R2 characterizes them); elaborations outside the same-CFG one-flag-per-atom class are not covered.

#### R2s

- Not modelled: enums/sums and moves out of variant fields; arrays/slices; moves between locals; assignment with implicit drop of the old value (drop-and-replace); borrows; nested scopes with their own exits (drop points are only ret/resume); catch_unwind; async drops.
- Aborted runs are exempt from NoLeak: process abort is treated as reclaiming everything, so under the abort rule a double panic satisfies ExactlyOnce's leak clause by definition.

#### R2

- Proof structure: the direction elaboration-correct → compatible is R2n, which needs only PlacesAreMovePaths and only the exactly-once part of elaboration-correctness; the direction compatible → elaboration-correct is R2s.
- The characterization is about decision maps over the source CFG with one flag per atom and the standard flag maintenance; it does not say that dynamic flags are needed by every correct compilation (see R8's positive controls).

#### R2n

- It concerns decision maps over the source CFG with one flag per atom and the standard flag maintenance. Elaborations outside this class are not decision maps and are not covered; the positive controls shareProg_matches_stdElab_progShare, dupProg_matches_stdElab_progJoin and earlyDropProg_matches_stdElab_progJoin exhibit exactly-once elaborations outside the class that test fewer flags than the standard map (one program each).
- The hypothesis `hd` (every run is exactly-once) is weaker than `ElabCorrect`: since `ExactlyOnce` exempts `aborted`, `stuck` and `outOfFuel` runs from NoLeak, `hd` constrains leaks on runs that return or complete an unwind and says nothing about leaks on runs that abort, reach a `stuck` node or exhaust the step bound `fuelFor s`.

#### R3

- Premises dropped as derivable: i < s.nodes.length (lt_of_isDropPoint) and forward reachability of i and a ∈ allAtoms s.locals (forwardReachable_and_mem_allAtoms_of_mayInit), both proved.
- It shows that some run fails for each of the two static overrides of the standard map at one point; it does not say how many runs fail or rank the two failures.
- It concerns elaborations over the source CFG with one flag per atom and the standard flag maintenance.

#### R4a

- No result-specific non-claims beyond the common ones listed above.

#### R4a-skip

- No result-specific non-claims beyond the common ones listed above.

#### R4b

- No result-specific non-claims beyond the common ones listed above.

#### R4c-kill

- The programs progPartial and progPartialFlag satisfy all hypotheses of R1, and their unchanged standard elaborations are elaboration-correct on all inputs (kernel-checked: progPartial_stdElab_correct, progPartialFlag_stdElab_correct), so each failure is caused by the one changed ingredient.

#### R4c-keep

- The programs progPartial and progPartialFlag satisfy all hypotheses of R1, and their unchanged standard elaborations are elaboration-correct on all inputs (kernel-checked: progPartial_stdElab_correct, progPartialFlag_stdElab_correct), so each failure is caused by the one changed ingredient.

#### R4d

- No result-specific non-claims beyond the common ones listed above.

#### R5

- InitsIntoUninit and NoNormalPathToResume are not assumed, and R5 states nothing about leaks: under the continue-unwinding rule a completed unwind can leak even on a program satisfying every hypothesis of R1 (R6), and on programs violating InitsIntoUninit or NoNormalPathToResume the standard elaboration is not elaboration-correct under the abort rule either (stdElab_fails_without_initsIntoUninit, stdElab_fails_without_noNormalPathToResume).
- Continue-unwinding is modelled as 'a panicking cleanup drop leaves the frame'. Other alternatives (a landing pad that re-enters a cleanup ladder, or swallowing the second panic and continuing the ladder) are not examined; under some of them a double drop or no failure at all may occur (not proved here).

#### R6

- The statement exhibits one run; that no run of the standard elaboration under continue-unwinding destroys a value twice (for forward programs with valid move paths and MovesFromInit) is the separate statement R5.
- Escape hatches from this impossibility: (i) the abort rule — on the witness program every run is then elaboration-correct (progUnwind_stdElab_correct_abort), and in general this is R1; (ii) destructors that never panic during cleanup (as with non-throwing destructors), under which continue-unwinding and abort coincide (not proved here); (iii) programs in which at most one droppable atom can be live on any unwind path (not proved here); (iv) an alternative double-panic semantics that records or suppresses the second panic while continuing the remaining cleanup ladder, which is not modelled here (not proved here).
- Continue-unwinding is modelled as 'a panicking cleanup drop leaves the frame'; it is a hypothetical design, not the current behaviour of rustc (which aborts) or of C++ (which calls std::terminate).

#### R7

- It states a lower bound, not correctness: the standard map is the least flag set among elaboration-correct maps under the hypotheses of R1 (R7L), not under PlacesAreMovePaths alone.
- Only PlacesAreMovePaths is assumed. Outside the hypotheses of R1 two degeneracies occur: on programs where no decision map has all runs exactly-once (for example a loop whose re-initialization leaks the first value; not proved here) the lower bound holds vacuously; and on programs that are not forward, flagSet counts only forward-reachable drop points, which may miss drop points reachable through an edge to a smaller index, and the standard map need not be elaboration-correct (stdElab_fails_without_forward).
- The hypothesis `hd` (every run is exactly-once) is weaker than `ElabCorrect`: since `ExactlyOnce` exempts `aborted`, `stuck` and `outOfFuel` runs from NoLeak, `hd` constrains leaks on runs that return or complete an unwind and says nothing about leaks on runs that abort, reach a `stuck` node or exhaust the step bound `fuelFor s`.

#### R7L

- No result-specific non-claims beyond the common ones listed above.

#### R8

- Only PlacesAreMovePaths is assumed: on programs where no decision map has all runs exactly-once, the conclusion also holds for maps with more flags (not proved here); the statement compares the lengths of the two flag sets, not the sets themselves.
- By the definition of `ExactlyOnce`, the run given by the conclusion violates NoDoubleDrop, or returns or completes an unwind and violates NoLeak; a leak on a run that aborts, reaches a `stuck` node or exhausts the step bound does not make a run fail to be exactly-once.

### Escape hatches from the impossibility results

- **R3** (static choice at a disagreement point fails): it concerns the standard flag maintenance over the source CFG with one flag per atom; it is defeated where the atom is not both may-init and not must-init (`staticChoice_compatible_iff`; positive controls `progKept_drop_correct` and `progMoved_skip_correct`), and by elaborations outside the same-CFG class such as `dupProg_matches_stdElab_progJoin` and `earlyDropProg_matches_stdElab_progJoin`.
- **R6** (a completed unwind can leak under continue-unwinding): defeated by the abort rule (R1; on the witness `progUnwind_stdElab_correct_abort`, and on the same input `abort_on_same_input`). Further escape hatches, each not proved here: destructors that never panic during cleanup; programs in which at most one droppable atom can be live on any unwind path; a double-panic semantics that records or suppresses the second panic while continuing the remaining cleanup ladder.
- **R8** (fewer flags than the standard map is not exactly-once): it fixes the class of elaborations (source CFG kept, one flag per atom, standard flag maintenance, per-(drop point, atom) decisions). Outside the class fewer flags suffice on one program each: `dupProg_matches_stdElab_progJoin` (duplicating the join), `shareProg_matches_stdElab_progShare` (one flag shared by correlated atoms), `earlyDropProg_matches_stdElab_progJoin` (dropping early on one branch before a shared exit).

### Hypotheses whose tightness is not established

None: every hypothesis of every result is `tight`, with the counterexample named in its ledger.

### Disproved, dropped or unresolved statements

None. All 16 results are proved as stated; no statement was found false and none was omitted.

## Evidence

### Kernel-check record

Toolchain: `leanprover/lean4:v4.34.1` (GitHub tag `v4.34.1` of `leanprover/lean4` = commit `5045d0056413266e57c625dcd7c365b10e377c52`, fetched from the GitHub API on 2026-11-21). The project builds with no `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declarations. `audit/axioms.json` records `collectAxioms` for all 1150 package declarations; each depends on at most `propext`, `Classical.choice` and `Quot.sound`. `audit/statements.json` records, for every Lean name referenced by `results.json`, the SHA-256 of its statement (Lean `repr` of its type) and of its definition closure (types and values of every package constant reachable from the statement, theorem bodies excluded). Besides the result theorems, hypothesis counterexamples, non-vacuity witnesses and positive controls, `results.json` lists under `lean_names` every further package definition and lemma that this report cites by name, so that its hashes are recorded as well (role "cited by name" below); these are not results. For a definition, the statement hash covers its type, and its value is covered by the closure hash of every recorded statement whose closure reaches it.

| Declaration | Role | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- | :--- |
| `AllCompatible` | cited by name (R2s) | propext | `71a060dfec275c9ac6410037f106d29c87010a880444c09f6359311d66e437d0` | `df59ffe6b1116739f28fc5f6de3c6d90686b192e5957ed2b06871fd1e6ce42cc` |
| `Compatible` | cited by name (R1) | none | `a26c76bc5b3e5e8b0629890e5fbb9c7a9bd7fa2cbf5154a839ddb1c8170f1046` | `a5dc8dc9d0848432c133e9bd1d303e7ad912fa71277cf0ba7bf11b34146eaf0a` |
| `Decision` | cited by name (R1) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `ElabCorrect` | cited by name (R1) | propext | `89e6c3ea6c0ab0e0b4705448e4154ede01afa41cb0f143d573b89f17b42b08bb` | `650d6143f81392caa52ea8bae8bdac35de92ecffeaa959978ceb519715977fa7` |
| `Event` | cited by name (R1) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `ExactlyOnce` | cited by name (R1) | propext | `bd4b40c585207495d353475c8bf4c48f6aa32e9b3c6375c41bd4b438c086db41` | `7be62103d744fa20b372974c477c604e4852b82dfa96c905fd78337f3f38feda` |
| `FlagConfig` | cited by name (R1) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `FlagConfig.std` | cited by name (R1) | none | `df94e211c107615f5ddab690d8dacfdedbc8e015964c03f8fe4c48be5e9d5000` | `03cdd73ffa7fe0127de59f4d1efc194ddd91b3c22b82909467f5a34aea0f23b3` |
| `Forward` | cited by name (R1) | propext | `b010d08a25f57f401044ac0b67026d83eeac747a03315fa65c9b4c5ea968a912` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `ForwardReachable` | cited by name (R1) | propext | `5f619f9ff768d01fdf45fbeb0ec9cde263d8fab58b47e12c11e4f1ce0c3699a0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `Granularity` | cited by name (R1) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `InitsIntoUninit` | cited by name (R1) | propext | `b010d08a25f57f401044ac0b67026d83eeac747a03315fa65c9b4c5ea968a912` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `Mach` | cited by name (R1) | none | `d655f6b8e62aa58d2291fef19ce4347b67de078a780747a2a1428e9a2647c0f1` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `MoveChecked` | cited by name (R1) | propext | `b010d08a25f57f401044ac0b67026d83eeac747a03315fa65c9b4c5ea968a912` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `MovesFromInit` | cited by name (R1) | propext | `b010d08a25f57f401044ac0b67026d83eeac747a03315fa65c9b4c5ea968a912` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `NoDoubleDrop` | cited by name (R3) | propext | `3bdf817d506454ea06eaec317c6dc893af0da21249914485399eb3c14eda4508` | `dc75f23e51ab7a259ceb18eaae04abf69829f439e405ea33c9a454f3b846fae8` |
| `NoLeak` | cited by name (R1) | propext | `3bdf817d506454ea06eaec317c6dc893af0da21249914485399eb3c14eda4508` | `dc75f23e51ab7a259ceb18eaae04abf69829f439e405ea33c9a454f3b846fae8` |
| `NoNormalPathToResume` | cited by name (R1) | propext | `b010d08a25f57f401044ac0b67026d83eeac747a03315fa65c9b4c5ea968a912` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `NormalReachable` | cited by name (R1) | propext | `5f619f9ff768d01fdf45fbeb0ec9cde263d8fab58b47e12c11e4f1ce0c3699a0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `Outcome` | cited by name (R1) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Outcome.complete` | cited by name (R1) | propext | `6015e6fd9b16bbece88a84680d54be2c69ba24737a4b848f35bc81b507e6502e` | `5182dbd63bfc8a38ad7d0291de8e8121d42ee702bc8185bcda422a4d71e73f59` |
| `Outcome.terminated` | cited by name (R1) | propext | `6015e6fd9b16bbece88a84680d54be2c69ba24737a4b848f35bc81b507e6502e` | `5182dbd63bfc8a38ad7d0291de8e8121d42ee702bc8185bcda422a4d71e73f59` |
| `PanicRule` | cited by name (R1) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Path` | cited by name (R1) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Place` | cited by name (R1) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `PlacesAreMovePaths` | cited by name (R1) | propext | `b010d08a25f57f401044ac0b67026d83eeac747a03315fa65c9b4c5ea968a912` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `Result` | cited by name (R1) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `SNode` | cited by name (R1) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `SProg` | cited by name (R1) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `TNode` | cited by name (R1) | none | `d655f6b8e62aa58d2291fef19ce4347b67de078a780747a2a1428e9a2647c0f1` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `TProg` | cited by name (R1) | none | `d655f6b8e62aa58d2291fef19ce4347b67de078a780747a2a1428e9a2647c0f1` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Ty` | cited by name (R1) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Ty.atoms` | cited by name (R1) | none | `6a0a53c825a678294f4f4f06c75206ca5ffc3f32af50c4b0dca293d44a32e28d` | `64672000cf0aaeade292e0d1cac550fff3b2a13a35c5dcba1be0a3df8fa115b1` |
| `Ty.isMovePath` | cited by name (R1) | none | `91033776a6c6b1aed613d980295c0f377a30d52816961bf0226011b63c3d0811` | `64672000cf0aaeade292e0d1cac550fff3b2a13a35c5dcba1be0a3df8fa115b1` |
| `Ty.units` | cited by name (R1) | none | `6a0a53c825a678294f4f4f06c75206ca5ffc3f32af50c4b0dca293d44a32e28d` | `64672000cf0aaeade292e0d1cac550fff3b2a13a35c5dcba1be0a3df8fa115b1` |
| `abort_on_same_input` | R6 positive control | propext | `7723fac544405d9fd222308ca61ab0660cbca4e476f013124bff3f24c19edda6` | `ceecff740be9c34d00c05b4b372f5b6f9b4ac4b25c5c3edbcc834f999cac82a2` |
| `allAtoms` | cited by name (R2n) | none | `a2db65ba221d1c374790ac64aa1d2dce19ce55f854b65d7c7be5e6cfa82ef123` | `f859fb1a81e40e7d7ce61db43a201dfc9a52eef6729e82c500ba9ce2b57f8fcf` |
| `allCompatible_necessity_fails_without_exactlyOnce` | R2n counterexample (hd) | Quot.sound, propext | `6588fd4900a5dab9ba3bd6fe55d555639af6fe8223e2c1fb81fa929894287706` | `4b1eac3ff054fd3f6f3fb1a168e93b47631befceca7abdfcf1d5f1df8a0efb40` |
| `allCompatible_necessity_fails_without_placesAreMovePaths` | R2n counterexample (hplaces) | Quot.sound, propext | `f736fcc2185ae1691229158eebd31cd802635fd1fcbce1cf8a71f9c418f67904` | `f107579fd2b5ccfe8ee65fcb8ed5f176ece2ec9dd17787b938fe0ca8bcb21bb5` |
| `allCompatible_necessity_hypotheses_hold_progJoin` | R2n non-vacuity | Quot.sound, propext | `0a5d328b3ff94fcd44fb197d7cdba9b25cc605564eb69abfbafc158739997d5a` | `6132e7d819ba4ac7e4b33cdf0dd2d2ca0bb5f4ac50642329c57d033fdf10de1c` |
| `allCompatible_neg` | cited by name (R2) | propext | `587ec1a488569132847526ab2ef89412d41b63de9c7382d52c0b50b9644db7c4` | `1213fad04df598bf312f5e41311879d0dc3be05030d94f2ebe14383a56b666e0` |
| `allCompatible_of_exactlyOnce_of_placesAreMovePaths` | R2n result | Classical.choice, Quot.sound, propext | `bf5af67c55cdf6bcaaaf658c9024c284083bc01e4df97c19334e69a17d07877a` | `ba23c1a5182759a76a28c3313ec5e5c7749a6287a9c11582bdba6852c1556388` |
| `allCompatible_pos` | cited by name (R2) | propext | `a2cc195088f3325d64be3dfaa229dc717609b91d2145a133a49deb663cf78a14` | `14e1ae45b642e2eb968a48a35c01b31dbca29424c1cb99bb61387ce49d5c4591` |
| `analysis_step` | cited by name (R1) | Classical.choice, Quot.sound, propext | `0c106e8a4b6362737cbc5e9e3c23b3cf08f6edbe56f4a0e5cb77edf1432ce178` | `12a8fa39e779f6f42ee40286b622f1dd4e658db4c9ea901e2a8497e3370af108` |
| `argFlagNotClearedOnUnwind_double_drops` | R4b result; R4b non-vacuity | Quot.sound, propext | `1560de73a6681f6ba9cb983d941527179b8a9039f3f42c3041f9c5a5d031d91b` | `8338d4f9bad5600218a5c609822ea4caf172c50c0522be7ae4f6f663635db6d1` |
| `atomsOf` | cited by name (R1) | none | `faf813582f857d0c2c22141aca0738fc4b5a10ff9f0fec60870e58c97a4725cc` | `f859fb1a81e40e7d7ce61db43a201dfc9a52eef6729e82c500ba9ce2b57f8fcf` |
| `badPlace` | cited by name (R1) | none | `e4b61f5265a3835153916772655b4b658f3357a04f734b8fa06a9f35ce099438` | `b6d557a74aff04fbeb2c2933d1ad70edfddfa41420b46a17c95fb064a4fd8d33` |
| `characterization_fails_without_forward` | R2 counterexample (hfwd) | Quot.sound, propext | `77f25c49a4d0e732021830071cb000f64b9cd40a6121f7b1b400489321cafa70` | `db483bddaed20a1af0c59fc5bd3a4cbb9095a2d2cda5dcffdf5f6dd09ac2c179` |
| `characterization_fails_without_initsIntoUninit` | R2 counterexample (hinits) | Quot.sound, propext | `e8617714fd9d9b9e17f240947f80e5607256561d6e15ca69d97a9352d4ddb13f` | `9055bb6c6327a0a29278c66149eaf8f801b97d7e0e49c337e3b0eff4df375327` |
| `characterization_fails_without_movesFromInit` | R2 counterexample (hmoves) | Quot.sound, propext | `ccc1ea9665ae12813220767b1cbe4c78a2e16ee6fe2e6565b27a5be64b5a5ee7` | `d52802a7240c88d70648f4464cb5c72dbbb8968776b29b181841d1bd98085aee` |
| `characterization_fails_without_noNormalPathToResume` | R2 counterexample (hclean) | Quot.sound, propext | `31109c11db7ac062ed06e46e656c42042a9c5af81288fcc6e84fd38a9943a3af` | `51be371415e679ce8da5f075f19f441a6efd6cf05acff9a02834b9069a0a89a2` |
| `characterization_fails_without_placesAreMovePaths` | R2 counterexample (hplaces) | Quot.sound, propext | `63bb6c9c2c2f42393987e88f5e59b00f385a44228d69f034b3cb5b42c1305df1` | `4aa0193ebce686109e66a251c3ffac7bfa4843fb2a2234045474ec78750d11a3` |
| `continueUnwind_completedUnwind_leaks_of_forward_moveChecked` | R6 result | Quot.sound, propext | `9bea68430d3ea96b6e8235726c7ea63227631645a4ca0b5497c2f3e9c35cc10b` | `efac8d54fb08f2e696b35e2ddae851202eef10f8aaf6dbd36fd36c3546d86556` |
| `continueUnwind_leaks_partially_dropped` | R6 non-vacuity | Quot.sound, propext | `9bc5f75f6ca64264487562ad9d836fa63d292a81553c4fe7316734590839845c` | `48d0f7bb85c9673f68131de1e7f263c33d337abb62741cc1406f4b71654c1fec` |
| `continueUnwind_noDoubleDrop_holds_progUnwind` | R5 non-vacuity | Quot.sound, propext | `44a67f56f0d05e529527a67ec0aedce02ae3117ee075a98ba07ad3102507bbfc` | `4fc6bc42cbacc2cbf581fbe5257539eac40d548797720e5f6f171c2a33d30a15` |
| `continueUnwind_not_elabCorrect_for_all_forward_moveChecked` | R6 result | Quot.sound, propext | `a7a6db1a4eeef5d6d1b5147f862c54ce12e3b33aa7ae75c12e017fc9040a22e6` | `a7dfa54fc46697fd4d40bf5009a186d79f4d25e48a2837959fbe7a0ca8b1aa0b` |
| `createdIds` | cited by name (R1) | propext | `9ec94b93cc2bc286cecf0af71d7f2f297060cfa06659fecc76c4a6dc6049e2d0` | `dc75f23e51ab7a259ceb18eaae04abf69829f439e405ea33c9a454f3b846fae8` |
| `destroyCount` | cited by name (R1) | none | `430ab3390ae443ade44c07cce230d4a48ead5e7bc73cc316d1f689fc74398bb2` | `dc75f23e51ab7a259ceb18eaae04abf69829f439e405ea33c9a454f3b846fae8` |
| `destroyedIds` | cited by name (R1) | propext | `9ec94b93cc2bc286cecf0af71d7f2f297060cfa06659fecc76c4a6dc6049e2d0` | `dc75f23e51ab7a259ceb18eaae04abf69829f439e405ea33c9a454f3b846fae8` |
| `dropT` | cited by name (R1) | none | `7c6d05ab0e39c4365f306394f3d7964381f86b7983d8cf4aa49b97028a91975c` | `3666f16a911e1f1d3c8cd0a8cac585012faf118805f7180b93a6f0cfd7f53ab6` |
| `dupProg_matches_stdElab_progJoin` | R8 positive control | propext | `26826f9f86387f6587b55fd755a2979139585a30ec43cf60810666120a0a2518` | `ff97699fb884c6bb5760439bd4a9718ce2de59b3c44ff4116d82d24378d95a75` |
| `earlyDropProg_matches_stdElab_progJoin` | R8 positive control | propext | `fbea28a2d8aa6f3338316caae0395c4b52ffb6530654f2047691684c983320d8` | `5baf847983a8e01e62d0f9760af2eee3d6b1b520ba6b2fb5ca9698f34ec62247` |
| `elabCorrect_iff_allCompatible_of_forward_moveChecked_noNormalPathToResume` | R2 result | Classical.choice, Quot.sound, propext | `b014fe4dbd925b67069acb13c72dbc561b8c40d5f4c9bdfb1bbf221f65cfc9fb` | `a0c9586858d0e3ee9d8e85a3e58ade0bbb2973b9bb73044295c6bf3009a287d6` |
| `elabCorrect_neg` | cited by name (R2) | Quot.sound, propext | `e1499fb98fc066284158d24dc7247781364e81ed92f2f3cbd8f307028715ac46` | `3d6fb8cb3a481c1b0f8a85d57e4955776880c28f95d3db95df6bad5fd40db1e7` |
| `elabCorrect_of_allCompatible_of_forward_moveChecked_noNormalPathToResume` | R2s result | Classical.choice, Quot.sound, propext | `4dd04f03e95b7668541f5af9d58d1b2ba676d4e6ed19123752b4bb372b4aef34` | `a0c9586858d0e3ee9d8e85a3e58ade0bbb2973b9bb73044295c6bf3009a287d6` |
| `elabCorrect_pos` | cited by name (R2) | Quot.sound, propext | `8913afa0ec57c23cd8848909a556a4fa8795a4e4e92b09cf780330fcb88f9059` | `5fe904eafb742ba41464eba113122aa66d7726fc7c2e37c3d48f7b8d719d8d04` |
| `elaborate` | cited by name (R1) | propext | `64b71d234e6fdf797b8b235ab2c233a797393f39c48c8df1c63c2ec19c1b7fae` | `6d84bb29cda21076fdd3c0d2a1f3b3a26d9687fb006b48e30d7238bb0448e056` |
| `exactlyOnce_hypotheses_hold_progCleanup` | R1 non-vacuity; R2 non-vacuity; R7L non-vacuity | propext | `2db78ec0c147d9742262dca586b0b585fb63eb386691e35c254b9484e151686e` | `117b15282bbea594f2b6dd2078b3f99d93fc21dc26e396fd15b30b625df6454f` |
| `exactlyOnce_hypotheses_hold_progMultiStepCleanup` | R1 non-vacuity | propext | `3a700959c396aa9da66de008709432248e12267d1bab336ba5bc1664ec082dfa` | `1913accf362e63410ae0e26b1e9671bbf52128461714ba58d064c649d9c35651` |
| `exactlyOnce_neg_double` | cited by name (R1) | Quot.sound, propext | `fa9c4cec46d21ec8976adf24932f6c201656a7e3a3f8cf185f9f0157bab018a4` | `d8e9f47745e881ebc84cc58abc6b87fa2747f866395a28ad118004ac4efa391e` |
| `exactlyOnce_neg_leak` | cited by name (R1) | Quot.sound, propext | `e9fab0fbca4b9997025522f5d9e330623d3e5d6c77722b30d27f8017b7f66547` | `d8e9f47745e881ebc84cc58abc6b87fa2747f866395a28ad118004ac4efa391e` |
| `exactlyOnce_pos` | cited by name (R1) | Quot.sound, propext | `c6c5fd26df5de44eb387a0fb6b2a5feda5e20312f03b51716fd782f2e9fd504d` | `d8e9f47745e881ebc84cc58abc6b87fa2747f866395a28ad118004ac4efa391e` |
| `exactlyOnce_pos_aborted` | cited by name (R1) | Quot.sound, propext | `87246a050d57c3efcd7bfa2df1528d01937e310b6f86a27f2c76a8ce9e5e670b` | `d8e9f47745e881ebc84cc58abc6b87fa2747f866395a28ad118004ac4efa391e` |
| `explore` | cited by name (R1) | propext | `7b0d71e0f253aedbdd5da08a92ba9c7635c8a129ab7ddffc8444fa693c79b542` | `644b6e98071ff914cd6a2a7917efbfdbd6fab752bf710697659cf647092e2059` |
| `fewerFlags_fails_without_lt` | R8 counterexample (hlt) | Quot.sound, propext | `55def7d897b440911c20efa175e335c31e8f856c973172e18e2eca2feaf81e4f` | `40e055331c7611e03f6052c2131a77aa3f4d02d4c01f0a134bd72095150dd23b` |
| `fewerFlags_fails_without_placesAreMovePaths` | R8 counterexample (hplaces) | Quot.sound, propext | `8e50cb4a05d80152ec3628556eac684ef5ab423573521fe1feaa4b5179febb9c` | `520896cc6fb0ca6e4af17af78008cb06a3370c36bbcde3bc9f8c5ea0278571f2` |
| `fewerFlags_hypotheses_hold_progJoin` | R8 non-vacuity | Quot.sound, propext | `317c7801b740c1831afc2517ef910cedd2d8d6680a1a4f63edbc545e4a20ee83` | `a5e6fa7ecf447a72363aacbb9811bbc70262c517943d810e0405e64eb98b16d2` |
| `fewerFlags_than_std_not_exactlyOnce_of_placesAreMovePaths` | R8 result | Classical.choice, Quot.sound, propext | `be4368fd1cbc6247d829374342c63b64c9ee4281a9bb5245f722b577eba17416` | `32b1c6f913a08f85baa8701702165c11901207df2e35dcc4308e30919885560a` |
| `flagConfig_gran_inert_on_progPartial` | cited by name (R4c-kill) | propext | `ad54e6d87feec6c7b9fad210698b883b7c9bc13b585e6ef9a520ded07bc934ef` | `c5df1f385b49a340467f5b8cf0f27e74e97d4ab81d311331f7aae82cf52bec2b` |
| `flagSet` | cited by name (R7) | propext | `1ea9a48db2cb0f35f4c665d9c9c487acb1fd378ab4907e4388c767ac7cebc93b` | `df59ffe6b1116739f28fc5f6de3c6d90686b192e5957ed2b06871fd1e6ce42cc` |
| `flagSet_ignores_unreachable_test` | cited by name (R1) | propext | `aeb3c2f3814ed08831ab517bcdf1da359d68ca813aa68155ea8c6abb70ac174a` | `cb0a352a8e367c5e0cfcb2464faffeae912f18cf5a23181d75a6268285551f6c` |
| `flagSet_progJoin` | cited by name (R1) | propext | `055555fc174838ebb735d668a64ae36ee775ec05b9a2867144fdcf237500225e` | `92d7609ed8377583c107a8708797f1f95bea4083f4b3e04d81679746546edcbe` |
| `flagSet_progPartial` | cited by name (R1) | propext | `53ae3462d4402dfccbbc7396c4ac946a8493130442b92db7153d59c32ae9a55d` | `30d5b33e108903e35f7c0598924cd639f9051a15c47d475e28c5dc150eed8ca0` |
| `flagSet_progShare` | cited by name (R1) | propext | `a1001770b902a8daf7daddc736b539501f9995a510d51ccf77f996b4fcce0615` | `f37035c3e32ae200f31f4b729af4f0fdf8f69a4b43a833098305b02378c4ea10` |
| `flagSubset_fails_without_exactlyOnce` | R7 counterexample (hd) | Quot.sound, propext | `9f095b1243df98000cf7d611ccb673cf49bb20f0040af4230988651151b65865` | `a5e6fa7ecf447a72363aacbb9811bbc70262c517943d810e0405e64eb98b16d2` |
| `flagSubset_fails_without_placesAreMovePaths` | R7 counterexample (hplaces) | Quot.sound, propext | `52e8377a441b54588e19eaa69d392b06dc94d81087f24e1b09f6d86a6a96bc86` | `520896cc6fb0ca6e4af17af78008cb06a3370c36bbcde3bc9f8c5ea0278571f2` |
| `forwardReachable_and_mem_allAtoms_of_mayInit` | cited by name (R3) | Classical.choice, Quot.sound, propext | `b0b19a8e7cfa5c3c3151df01a83bfb71f7d28f7d82407cfd4dae498f84a5ff31` | `c371a52c201a68210ec66c21ee6633c1fb102f9fc1d4466dcab238c3ebd159d0` |
| `forwardReachable_ignores_backward_index_edges` | cited by name (R1) | propext | `6a2a8616ea1ac1b6c1c4f4f0efe6df7dc1a61d8b474d74e101089f1dcccb9424` | `cb7c594c7b8309df89041e3aebf816c3d4812033a4d3aa1e5aebc2d410305ed3` |
| `forwardReachable_neg` | cited by name (R1) | propext | `5d04b0c4b6baec6dc286d1d11a098d3349df9af2c5c861b9e349d35ac5569fa4` | `cb7c594c7b8309df89041e3aebf816c3d4812033a4d3aa1e5aebc2d410305ed3` |
| `forwardReachable_pos` | cited by name (R1) | propext | `d3237f28542b477b3270621a631275874f2a2f947ec2bb617819bfab2f040384` | `cad90add509c3c08329b0134331260c14f8aa46297b2eec502215aa821b1d059` |
| `forward_neg` | cited by name (R1) | propext | `56334ee5ca1c81d77c608ff91f3ff25a4e2c9cec50d439aed9fb17dbdf4a79fd` | `17986afa33c1e7a31d33de931f3c79821326c55dbbdfd886aab4a222dce99e37` |
| `forward_pos` | cited by name (R1) | propext | `a74ed13c3b4faac136e0de6bd217a33dcd57eb8b12191aaa9c710af0f2918385` | `78abd25b44f26c8403c152df18a796ea75f9b861097494781f6a56f586cba3e4` |
| `fuelFor` | cited by name (R2n) | none | `293a026f4671a1cbded1ee595ae84223dc8debe9e8f0818447f201b94c0fda29` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `initMach` | cited by name (R1) | none | `1da0dd4f7981fdfc1829ce5f07adabf1a92b2f3202151acbc66b0cdff5a89964` | `e8cc16d59a17f9b6ed763205ebcb7ddaa5bb06ddb9fc7f83853cd427f9bb7c75` |
| `initsIntoUninit_neg` | cited by name (R1) | propext | `cd98fa6162c870b125e420a42795ed095410660e15ca2e85c8a8dd127c3c2486` | `a00d5ed50b1cabdeef7ffffac5d8192290bec5400568488d69a04de4d1ada2f8` |
| `initsIntoUninit_pos` | cited by name (R1) | propext | `08a48b81b7cdd432f67e370b75c63e95090a1eb4c53d0e1e03aee3a1fefd0c6e` | `844dd86c2f12350f717e4d39143464c357899ffc8a157a4019929a6a4116cca4` |
| `isDropPoint` | cited by name (R3) | propext | `9dcf12ad9b26d959c962c60bc258c6abcdc3a2667bbb08c78d05945da80b8968` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `isMovePath_neg` | cited by name (R1) | none | `da686bdcef2e84942b60b1ad5c93459640e7ed88a8024fa5983735b6e2d85d89` | `6e10537dcc5298aefbc8312c2784ebd2d70b937ade96882ce4eefe012abf8bfa` |
| `isMovePath_pos` | cited by name (R1) | none | `491c8414d83a9ff46e186ce7fd6a3c5ea5bf3d552d7ac064480840b7060fb4ee` | `fbe0ea040bb3ff059b71cbc15167753170d9b9b5345dd83d80ccafe64a63d5d1` |
| `isMovePlace` | cited by name (R1) | propext | `fc37fbd2e06195b6ec866a7092de4d48068c571e6552bd64f2ccf3ddb36b12b4` | `f859fb1a81e40e7d7ce61db43a201dfc9a52eef6729e82c500ba9ce2b57f8fcf` |
| `killSet` | cited by name (R1) | none | `1100e2a177603be0e29689755083c1a44828c5b483e810158cbf62157dfe3b77` | `f81f778f8808e387d19928bd730c99485ba3f2ee5ffed994b32775f75290a7cf` |
| `lt_of_isDropPoint` | cited by name (R3) | Classical.choice, Quot.sound, propext | `b7bdc6594fdfe1334e4895d062f08ac260ae157f9dcd2a29ee82c17ae26508e7` | `4a90d686ca1fc6b1980c60d407188bd49ed6ab2accf6536ee70361427cedd773` |
| `mayInit` | cited by name (R2n) | propext | `f5348b6cd229214256c5c1e17b7d5bb1312c3389d7fa2499b96b2ad5cd1d53a5` | `a3a68d4013b51d2d996006c15085c3f3770329bd6221b27a4aa29112b717e2e8` |
| `moveChecked_neg` | cited by name (R1) | propext | `31f5ef8167aec06fabb9b3febac95c447fc6954c40ac7b3b9d00d0cb7fa97ad6` | `8f86a490a751ef3b5d05470e59999415a19ae32379409e564c82737b39989d91` |
| `moveChecked_pos` | cited by name (R1) | propext | `06ff2fc1c3cf3c805bfc83712eac4f9cf213b15f7001523a6e99315dd2ef4427` | `dcbc8c07fe584f7095b631f705c5563f4dc9e99af8fd6e0e6741f25299a0cc31` |
| `movesFromInit_neg` | cited by name (R1) | propext | `fea339c945e9ddfee4b1a50fadeaa9b8ce6d3735138c9134f535627bbe1f8550` | `e09c260174ecd779d2ab3d53ee09510a31d6483b3c90437b49ab933b44adb2eb` |
| `movesFromInit_neg_duplicateCallArg` | cited by name (R1) | propext | `4312672a1ff686e2b79d93def0211a72abd1b7de1d9d01361d75c8b6149d8b6d` | `763bdf0f0c6e1abbf9178b4132dd4fb4c8bd59f996d3614f422eb80d5650bdfb` |
| `movesFromInit_pos` | cited by name (R1) | propext | `adc5816590c969430fb7c76134214e0c1cfbdfdb46c6611ab53263230cec33e9` | `26b4d62c2aed92e52bf6c2b22c66cc67c788a43c223897607297ef4950ad1db0` |
| `mustInit` | cited by name (R2n) | propext | `f5348b6cd229214256c5c1e17b7d5bb1312c3389d7fa2499b96b2ad5cd1d53a5` | `a3a68d4013b51d2d996006c15085c3f3770329bd6221b27a4aa29112b717e2e8` |
| `noDoubleDrop_continueUnwind_fails_without_forward` | R5 counterexample (hfwd) | Quot.sound, propext | `ff3a14c5ba0511843121104da5b661f716a02dd4e0e368cfe1c3d91e58957350` | `093b78018eb005ea24b44bd20e0ded0b26980147dd74a9d38346a453d71c470a` |
| `noDoubleDrop_continueUnwind_fails_without_movesFromInit` | R5 counterexample (hmoves) | Quot.sound, propext | `3cba90fded4c209edbba7a7baca99d1580befca76780a8869d15608366089d98` | `b9b9a2931cf4c709ef23fcc72c0586a673fa2d8e707c6316f24a6d888e659dc4` |
| `noDoubleDrop_continueUnwind_fails_without_placesAreMovePaths` | R5 counterexample (hplaces) | Quot.sound, propext | `6eb4f7939155adb9ea24765633fbecbe1a43f24c9995f02b998f93a8fe8e004e` | `a9d8667a2819a308083069389a2fcf2a635a9b30417d1fb88151173497074fe0` |
| `noDoubleDrop_neg_afterConsume` | cited by name (R1) | Quot.sound, propext | `05d10d2c4bd7f7a9c0ce272fca58b7a542f0112a395e715d3d468c124698efb7` | `cd9f5a676275b5b7d753dc9b057dc0fced7c9122d5a1538ed3ebae1a8fa01499` |
| `noDoubleDrop_neg_garbage` | cited by name (R1) | Quot.sound, propext | `4d6efe92da7db5f20e07045e734b9d666b6fd361fff8c32b9ea68159d6750ccc` | `cd9f5a676275b5b7d753dc9b057dc0fced7c9122d5a1538ed3ebae1a8fa01499` |
| `noDoubleDrop_neg_uncreated` | cited by name (R1) | Quot.sound, propext | `93e9b57e5ab651874da8f24f7ceb40831ab8c81b86368ea423887add476658b7` | `cd9f5a676275b5b7d753dc9b057dc0fced7c9122d5a1538ed3ebae1a8fa01499` |
| `noDoubleDrop_pos` | cited by name (R1) | Quot.sound, propext | `b205e59f6ee81aa8a28b86c2336b966486410e32854ba3bf4ae8f20143418029` | `cd9f5a676275b5b7d753dc9b057dc0fced7c9122d5a1538ed3ebae1a8fa01499` |
| `noLeak_neg` | cited by name (R1) | propext | `97889ca76c875175757fc71ed8680b3dc68f07d62cc6ea631585d866e79cff64` | `37b556383872dc7490a6b67bff31d1ceab70ea8829b29fe4600a51ff53df701e` |
| `noLeak_pos` | cited by name (R1) | propext | `b185b34cb3b67b65f6bee466bae92b28bb1e79ec0036035ab2846ed8c483af2a` | `37b556383872dc7490a6b67bff31d1ceab70ea8829b29fe4600a51ff53df701e` |
| `noNormalPathToResume_neg` | cited by name (R1) | propext | `38d85cf793881c6c1b999138f87edbb10074f850d53f90abf33c32ccad03f193` | `b19535d91c92ee1e3537d36679ccdb837bb5b9bbbe0b3ce1490865f0277c3ee6` |
| `noNormalPathToResume_pos` | cited by name (R1) | propext | `7e96a9847dd8d517e61f17bcb82b627cbeb6ae945f9fab6546f8bae4efb34f20` | `ff9ba23554d43915877c221f5b0060865166bfb4d3c4c765dab39461d348a703` |
| `overrideAt` | cited by name (R1) | none | `10f47b3664142c5a81cfa78227cf049778b9980516d17cbacf62592124337150` | `52e703fb735ab73fcb4887c1ea054bf3c07e989b0a4dc5af2dcdf071345067b2` |
| `pairT` | cited by name (R1) | none | `7c6d05ab0e39c4365f306394f3d7964381f86b7983d8cf4aa49b97028a91975c` | `3666f16a911e1f1d3c8cd0a8cac585012faf118805f7180b93a6f0cfd7f53ab6` |
| `pairwiseDisjoint` | cited by name (R1) | none | `165ad1dcec01310d8d192e8371c664491942d0fbb661009fab02959e7d211a89` | `b6d557a74aff04fbeb2c2933d1ad70edfddfa41420b46a17c95fb064a4fd8d33` |
| `placesAreMovePaths_neg` | cited by name (R1) | propext | `e4ce6f635a8804ecb2e9fdce6f0f078e3acd82f31eae165c555b5dd70108684d` | `06a015b62007d4cbb9cf9d1854d2776f604904642392efbc18662c1df21764dc` |
| `placesAreMovePaths_pos` | cited by name (R1) | propext | `c770521294f8980b5c774948a1306d20c20dcab8623e9b7c588b5bcd6bf3689c` | `62d656404c2f904942d7e6a6ab6e6e78a11933a823d96a5f6fa5727b4bb5d7c4` |
| `progCleanup` | cited by name (R1) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progDropStruct` | cited by name (R1) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progDuplicateCallArg` | cited by name (R1) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progIllTyped` | cited by name (R2n) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progInitInsideDrop` | cited by name (R5) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progJoin` | cited by name (R1) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progJoinOff` | cited by name (R3) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progKept` | cited by name (R3) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progKept_drop_correct` | R3 positive control | Quot.sound, propext | `61d9843c8af3db2ab1452acbcdce14abdc1ecd3a7d87fafadff40f47efddae37` | `4d8eb94c73885ce73d50eebf8f4ecf0998469e88cde55eea657b495127185e8d` |
| `progLoop` | cited by name (R1) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progLoopMove` | cited by name (R5) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progMoved` | cited by name (R3) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progMoved_skip_correct` | R3 positive control | Quot.sound, propext | `d63eb0c309700d6fbfef3f2085a8c15c11b7bb579a403032cd1bfe9adb975c05` | `7ce8969dc7463680f8cfbc301a3769f127c51646d12e8c944a1109da3c8a6167` |
| `progMultiStepCleanup` | cited by name (R1) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progOOB` | cited by name (R1) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progOOB_stuck` | cited by name (R1) | propext | `5a866393dae01ba91af8ebfdff0f7f9d7fb80350feb7aafab56cfac2b79f6bbe` | `234c013a77c2871adfc63eca4fd50621e8c7344b6f6a49287f400d140ea1538a` |
| `progOverwrite` | cited by name (R1) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progPartial` | cited by name (R1) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progPartialFlag` | cited by name (R4c-kill) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progPartialFlag_stdElab_correct` | cited by name (R4c-kill) | Quot.sound, propext | `cfc0cd8de5f992dea97be1e3b15ef37b1cabfee60d1d3cb4e9feb1ea5a172945` | `f5a6e1584a23fb39fea6e6ac813e4a6deb7dbe63516deb57bb7932fc5319e841` |
| `progPartial_stdElab_correct` | cited by name (R4c-kill) | Quot.sound, propext | `6576c9402d9a660fd4a4175cd9d0f27d2a16acc9f9368a02da5e46478adeef9a` | `6b55979126ea2d35cb59c6bf2b1cc82bf3286db578cbf078fe7bee717fff85a2` |
| `progReinit` | cited by name (R1) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progResumeNormal` | cited by name (R1) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progShare` | cited by name (R1) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progUnwind` | cited by name (R1) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progUnwindToRet` | cited by name (R1) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `progUnwind_stdElab_correct_abort` | R6 positive control | Quot.sound, propext | `01553aea492956f075f9629b88df1e8a44870164c84cc9eb3d005f091e1c71ba` | `38f788dbb06eaf8318199decc50de560505157661ce244b4b36b41c3dcf8343c` |
| `progUseAfterMove` | cited by name (R1) | none | `0a52ea76ad8751866d670ddcd43d7d67adf7c487653f9b83dbc49cd072917be0` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `reachList` | cited by name (R1) | propext | `f728b2b086ed0e45d12f84661d4e040703de76b547a9cfcdeb3dac79822f67e1` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `reachableAux` | cited by name (R1) | propext | `2b5476a2ee470f988c09c46ef5decbb754772689625400ec2bd9c0c339c31190` | `c26b275225ef02a0f6c73c868b96d536367b531658be543f936ee33168007b5d` |
| `reinitWithoutFlagSet_leaks` | R4d result; R4d non-vacuity | propext | `91f5f1b7adf10d4a9b8470a0fd033f73e612bde13bbbf536e05a8421994d5f59` | `956ee7089d6252ab9c88931dbe2a682344a1d01b115675a308a455475b8b8af1` |
| `run` | cited by name (R1) | propext | `d2708efa472c2e19951bfa6ab834c35f6edb1fcb5ad723bcca67b89f1b206368` | `486bf7ebe84f6a1455db44b331d7ac4dd124e1968ffee7ea21350fe16dbb03ca` |
| `runElab` | cited by name (R2n) | propext | `2918d25518bec7815d48bba018a4fdd1e06d770a850a7fca9d93427548782870` | `00398ff1b50573d0295744f273c1c95097d9cb82f88db9f56e8a60389251c78b` |
| `runElab_good` | cited by name (R5) | Classical.choice, Quot.sound, propext | `eeb7f7fe17ad1082ec21ecef06eead8dfb2941e6365b28a6c63b1b59dca3c93d` | `b3b31645a4d74c8735138761e9431c2b9ee0f4d9eab40031a982a937267871b2` |
| `run_eq_follow` | cited by name (R1) | Quot.sound, propext | `9808a4dbe352635f8d275bb06628509da17ce8384f6a22e9d62d8f44892fb6cc` | `bb115d5cfa1b869f43443de6e35c0f17505ae19fcf7fde6496e3b368d8901831` |
| `shareProg_matches_stdElab_progShare` | R8 positive control | propext | `4ccaec973ce4d2c4129b5d9d973c39cb8aa68965b3e83c492638dd5fa8a27894` | `7bbd66356d4c644621208b66e3d1b0422805eac3e447f70a7e559d79d3222b5b` |
| `staticChoice_at_disagreement_fails_of_placesAreMovePaths` | R3 result | Classical.choice, Quot.sound, propext | `b86a08313d9114a82ddb15e30bf019a696b4d200bcb68296e3c41ef03cb04dc7` | `9ea774261cebf678c03b6671a6982926a7cf1169a048098cdbf7866d75c98e71` |
| `staticChoice_compatible_iff` | cited by name (R2) | none | `c030b6c4533daf4a07c7470519d631fbf0ee68460f89fcf4bbf219b52a1843c7` | `ab0f76ef68679acf376c49d3593d4759285bf1b93f3848f25e4f44534ba0cc7d` |
| `staticChoice_hypotheses_hold_progJoin` | R3 non-vacuity | propext | `3dce9f4f23a79de6ccb379a6e6bf107bdf676516b9458cb1190092e2da093178` | `07db1b529189d2046c6bdca7b52c5290421e849ada1fc8a14e8701d5d959a3f4` |
| `staticChoice_necessity_fails_at_non_drop_point` | R3 counterexample (hdrop) | Quot.sound, propext | `8b8aa046169a219f4c397ecc52ce0b5e0daa8203fbaa006b869a07933200533f` | `2a5e30ff44fec561427fc08ba57ab07a40d5452aaca8e30c607b1f9d79622bc0` |
| `staticChoice_necessity_fails_without_mayInit` | R3 counterexample (hmay) | Quot.sound, propext | `5e1f6905d715a3f3a32ab9e664820900503523244af7acfd6842483f9d414265` | `a8b2d6d61732c203a5716cec5f0f9dd488d17483c949d618b6fe2a505f2a6080` |
| `staticChoice_necessity_fails_without_notMustInit` | R3 counterexample (hmust) | Quot.sound, propext | `fd835452a84e8da7f62319fefb4ea0e9847c89a2a0845b6e3712dd46fa409ee0` | `40445f12ae3f07cad11dd5cc990ce18ab5d6ed6ec712f022f338433bd4cbf57b` |
| `staticChoice_necessity_fails_without_placesAreMovePaths` | R3 counterexample (hplaces) | Quot.sound, propext | `e83c5f82d59d2410cc39a3761d804039c221005f32cf97bd3462fc2a7afb1655` | `cf9ca055bbff9da62cda0c0edff9d5dbd1791dc6ab62d59bc2ff20787a3c3065` |
| `staticDrop_at_join_double_drops` | R4a result; R4a non-vacuity | Quot.sound, propext | `f4a44352b9c2b5149a19bb4a21c9ef6c02449876155c1a259be7755a5c227a39` | `b401bf9b2c16989af1afc22b963ab94a1b7e4f176e570abe4aae0c232b5641f2` |
| `staticSkip_at_join_leaks` | R4a-skip result; R4a-skip non-vacuity | propext | `158dabf09b566e48fc940ec9065fa2f0bdcc3899bd587a24a42167cd8a2e3d33` | `3b565011fa3bb3cd489d18718abb4e4a5c3a57b6f330bf88a76deceb2749e603` |
| `stdDecision` | cited by name (R1) | none | `c9a37cdf9d99fcf007104e1455868287d286e237f6af2fdb8a37154c9fa634f1` | `a5dc8dc9d0848432c133e9bd1d303e7ad912fa71277cf0ba7bf11b34146eaf0a` |
| `stdDecision_compatible` | cited by name (R1) | none | `096ed0de97998f8e375b7ad66fa3c168eddf52485faf1f639aacb279c1e47f9c` | `1476ee26965413b8a5f5bba5ae70036318b0ff29e300f2f27a9e769e5384e251` |
| `stdElab` | cited by name (R1) | propext | `8873e0f25c10712d18f89dfde7af0f10ffa6e8ab09223d528c9dc82e022917eb` | `053bfdebfb8e19f6b31ec3d21f7e2ef7bb57a326eac1de302e9c2c2a944201a8` |
| `stdElab_correct_of_forward_moveChecked_noNormalPathToResume` | R1 result | Classical.choice, Quot.sound, propext | `a516732cb670ea00cdc495bdfb6a86a6ee46c8669dece5d04ecad2e5fa8a851e` | `a7dfa54fc46697fd4d40bf5009a186d79f4d25e48a2837959fbe7a0ca8b1aa0b` |
| `stdElab_fails_without_forward` | R1 counterexample (hfwd) | Quot.sound, propext | `ef448328398ebc8585f27a03d4120d77e77897fe47d168de376c444f2380484e` | `82eb1330b534ce1645ffc9642757a96492eb1c3fdd705d496834b55bbbcc8c7b` |
| `stdElab_fails_without_initsIntoUninit` | R1 counterexample (hinits) | Quot.sound, propext | `c0309d312f070b7fac2b25eb48be9704d582d7c9b979014793ccfd2020c57d1c` | `1cdcac32e28594dde22f1dddc1ad4686cd752c3111f51223da206e2a341e822e` |
| `stdElab_fails_without_movesFromInit` | R1 counterexample (hmoves) | Quot.sound, propext | `e86cabfb9ea29bc345b39fff3b84b231c2c969f70e0c6e35624e9788394b3e79` | `057fee6255ef87d6274a6a810e504f6d0dde51218cbde63ccabd2e67e34b664f` |
| `stdElab_fails_without_noNormalPathToResume` | R1 counterexample (hclean) | Quot.sound, propext | `59c5bf2779ff7cc9a0b54c23b872407d3d81e264e2b44c852f4ed809171bcdfb` | `f599063c9dbbc3e8d137c85281ec66c0e998e5dd70cfe4c264bc84993f5012f1` |
| `stdElab_fails_without_placesAreMovePaths` | R1 counterexample (hplaces) | Quot.sound, propext | `e112ff4bf93ca59cd96b11a2ce3400b02c70f299fb30092bb2142383538c00a9` | `640545e868fa459ae97610b8141e2574916e641308d8eb7337e833ce89f0eeee` |
| `stdElab_noDoubleDrop_continueUnwind_of_forward_placesAreMovePaths_movesFromInit` | R5 result | Classical.choice, Quot.sound, propext | `05d91f4d4ed35c43886f1d0f6b4316b46bb9c8effdaef56ba3d0c6926ff31c85` | `23e376224c1647d9ba768bb77da04f129cf0ae0ec387fa9e25959c8f72082c83` |
| `stdFlagLeast_fails_without_forward` | R7L counterexample (hfwd) | Quot.sound, propext | `26ff368c3421a5b92d08159658d11e442a739bbd0a18b8a46aad8c3d19d067d0` | `6c7f668cc83681431b5cfe7ef7a63ce73bc6a57601fead6452a672711be40ed4` |
| `stdFlagLeast_fails_without_initsIntoUninit` | R7L counterexample (hinits) | Quot.sound, propext | `cdb45a852c6743c78a54c152bf082cf6e69815dbd72728b68e9ebb152818b7d7` | `72a9ddd24e4f7fdd3881831e2a5f7d1b80f5c09730102e237fa9a6339d09c07e` |
| `stdFlagLeast_fails_without_movesFromInit` | R7L counterexample (hmoves) | Quot.sound, propext | `d3d11ec5b7adbd2660dab33fb39e88db63a8c6d259c94461d5fcd1fd2ae2933f` | `be1ef5f669c75bb9e36020bafa2f24928d3263fd54ee6c9517cac42412d2af25` |
| `stdFlagLeast_fails_without_noNormalPathToResume` | R7L counterexample (hclean) | Quot.sound, propext | `16f6458e1d0e242535f6e2328681c1bb67b30612e431bf8f053f023ec8be5729` | `5f6a403bef2d429fa000ab67eb93762f46d76d531e20d5066ee43ab7702b0cad` |
| `stdFlagLeast_fails_without_placesAreMovePaths` | R7L counterexample (hplaces) | Quot.sound, propext | `46bf9e9303d36da3359a84cc3c1d7e1644ceb7073d20695c0a0ae2d4b1ad4563` | `dc47d15ee53f096ee6226779d20159d859546e9861bfe49cd4423e8e056a515c` |
| `stdFlagSet_subset_of_exactlyOnce_of_placesAreMovePaths` | R7 result | Classical.choice, Quot.sound, propext | `d9720cd17ba291a9cd3acae1b9d26a2f232fd731de059cec92baaa0df8684f31` | `32b1c6f913a08f85baa8701702165c11901207df2e35dcc4308e30919885560a` |
| `stdFlagSet_subset_witness_progJoin` | R7 non-vacuity | Quot.sound, propext | `da8049e96ba6193b0c46af85d5485a606ba0376084a93f56993b8a88a38e2d79` | `40e055331c7611e03f6052c2131a77aa3f4d02d4c01f0a134bd72095150dd23b` |
| `stdMap` | cited by name (R4c-kill) | propext | `1af21422803a3b076e0506769aa35df04389f3dbccb174ee2cb162beb509ab18` | `7cc915eb859080813b7eb165303368171bb09cbde897fde2125e4f89e47877b8` |
| `stdMap_correct_and_flagSet_least_of_forward_moveChecked_noNormalPathToResume` | R7L result | Classical.choice, Quot.sound, propext | `4d5f7ad046bcc4e252f32dda91614e88021e1bd6ba6979165cd6f8816aded028` | `ed78d9f43cbecb38ffc834c49a6ca62f5982b06c966db3fc088bbd51e2b4e735` |
| `sufficiency_fails_without_allCompatible` | R2s counterexample (hcompat) | Quot.sound, propext | `455eb660448101cef381f8062f7633d2706b72181fc81d5c76246e8f4c026720` | `1eb4517ff3bee4762d0523fdddd1d8bc4077e9c08b376695e22ff5aacf2a5621` |
| `sufficiency_fails_without_forward` | R2s counterexample (hfwd) | Quot.sound, propext | `8f6151203be91be57d49edfdd52d77b5face584c6e1450a2b8f319ace3e8f31e` | `db483bddaed20a1af0c59fc5bd3a4cbb9095a2d2cda5dcffdf5f6dd09ac2c179` |
| `sufficiency_fails_without_initsIntoUninit` | R2s counterexample (hinits) | Quot.sound, propext | `d9daf65e36ca9286038e90a5ae52ce58c5a4cc4477f9eb5d376bf3598602599d` | `9055bb6c6327a0a29278c66149eaf8f801b97d7e0e49c337e3b0eff4df375327` |
| `sufficiency_fails_without_movesFromInit` | R2s counterexample (hmoves) | Quot.sound, propext | `512a007f73c67355366cec0d7f9b23ca63e96a7d5c46124dd6f535c6afbcfb2c` | `d52802a7240c88d70648f4464cb5c72dbbb8968776b29b181841d1bd98085aee` |
| `sufficiency_fails_without_noNormalPathToResume` | R2s counterexample (hclean) | Quot.sound, propext | `56ad3c1a04e5d2e18ac85efb6a39bf2fb1dda0a2b0ec66a8c882a5d8f6851967` | `51be371415e679ce8da5f075f19f441a6efd6cf05acff9a02834b9069a0a89a2` |
| `sufficiency_fails_without_placesAreMovePaths` | R2s counterexample (hplaces) | Quot.sound, propext | `1ed0147b8877ebb07c6b32a5f6c618fd642ceb138d009fc4d74eda24f655b7e5` | `4aa0193ebce686109e66a251c3ffac7bfa4843fb2a2234045474ec78750d11a3` |
| `sufficiency_hypotheses_hold_progJoin_testEverywhere` | R2s non-vacuity | propext | `c26357c9e8dc8efb2f5d8e93f1f80b8c1f8466c1cb62581a90e35b8f1e1bebaf` | `201470dbdf1beb4a08d9531b2e466770fcd1a37c6980924b1f4c7ff5f81858e4` |
| `unitsUnder` | cited by name (R1) | none | `faf813582f857d0c2c22141aca0738fc4b5a10ff9f0fec60870e58c97a4725cc` | `f859fb1a81e40e7d7ce61db43a201dfc9a52eef6729e82c500ba9ce2b57f8fcf` |
| `wholeKeepAnalysis_drops_moved_field` | R4c-keep result; R4c-keep non-vacuity | Quot.sound, propext | `8fb9dff5d5aeb5086112764b034f2269a92710318b8700949195d254d14675ce` | `334eefa0adcd221f9d01f6509657ad5b7d835da6c297f98693021cac54070145` |
| `wholeKeepFlags_drops_moved_field` | R4c-keep result; R4c-keep non-vacuity | Quot.sound, propext | `d3b0a1293a064baff8b1784b39939be236738914424f94bb734d9d9573814c4f` | `09e96e0ae5c443afe03fae8a33e705d397f8cf1ce1252e00ccb2f710fc1375cc` |
| `wholeKillAnalysis_leaks_remaining_field` | R4c-kill result; R4c-kill non-vacuity | propext | `3aae8d4e7d3fb0e2a7d3ace2ee0ab156c724aa3f1d09bfb096c042c7078d5619` | `37874c93966e8e8f90078ed57c2b63d533e76f2488c378d2f1c18b06130102d4` |
| `wholeKillFlags_leaks_remaining_field` | R4c-kill result; R4c-kill non-vacuity | propext | `04aa8a01fb8222bbc66b3aca75bf06ea9367784b92a1dd89ca94b755456859c6` | `40b2dbebf6636ac04e3ecbd1bb9fac89e20fba7fa07b746261edce85e9398477` |
| `x` | cited by name (R1) | none | `e4b61f5265a3835153916772655b4b658f3357a04f734b8fa06a9f35ce099438` | `b6d557a74aff04fbeb2c2933d1ad70edfddfa41420b46a17c95fb064a4fd8d33` |
| `x0` | cited by name (R1) | none | `e4b61f5265a3835153916772655b4b658f3357a04f734b8fa06a9f35ce099438` | `b6d557a74aff04fbeb2c2933d1ad70edfddfa41420b46a17c95fb064a4fd8d33` |
| `x1` | cited by name (R1) | none | `e4b61f5265a3835153916772655b4b658f3357a04f734b8fa06a9f35ce099438` | `b6d557a74aff04fbeb2c2933d1ad70edfddfa41420b46a17c95fb064a4fd8d33` |
| `y` | cited by name (R1) | none | `e4b61f5265a3835153916772655b4b658f3357a04f734b8fa06a9f35ce099438` | `b6d557a74aff04fbeb2c2933d1ad70edfddfa41420b46a17c95fb064a4fd8d33` |

### Auxiliary lemmas cited by name

Statements (verbatim, proofs elided) of the package lemmas that this report names outside the result cards' own statement blocks: counterexamples named in hypothesis ledgers, non-vacuity witnesses, positive controls, examples of the definitions, and supporting lemmas. Each is kernel-checked under the same axiom bound as the results (`propext`, `Classical.choice`, `Quot.sound`), and each has a recorded statement hash in the table above.

```lean
-- lean/ToyDropFlags/Elab.lean:189-191
theorem staticChoice_compatible_iff (may must : Bool) :
    (Compatible may must .drop = true ∨ Compatible may must .skip = true) ↔
      ¬ (may = true ∧ must = false) := …

-- lean/ToyDropFlags/Elab.lean:212-213
theorem stdDecision_compatible (may must : Bool) :
    Compatible may must (stdDecision may must) = true := …

-- lean/ToyDropFlags/Elab.lean:217-218
theorem lt_of_isDropPoint (s : SProg) (i : Nat) (h : isDropPoint s i = true) :
    i < s.nodes.length := …
```

```lean
-- lean/ToyDropFlags/AnalysisFacts.lean:222-223
theorem forwardReachable_and_mem_allAtoms_of_mayInit (s : SProg) (i : Nat) (a : Place)
    (h : mayInit s .fine i a = true) : ForwardReachable s i = true ∧ a ∈ allAtoms s.locals := …
```

```lean
-- lean/ToyDropFlags/Examples.lean:110
theorem isMovePath_pos : pairT.isMovePath [false] = true := …

-- lean/ToyDropFlags/Examples.lean:112
theorem isMovePath_neg : dropT.isMovePath [false] = false := …

-- lean/ToyDropFlags/Examples.lean:120
theorem noDoubleDrop_pos : NoDoubleDrop [.create 0, .drop 0] := …

-- lean/ToyDropFlags/Examples.lean:122
theorem noDoubleDrop_neg_afterConsume : ¬ NoDoubleDrop [.create 0, .consume 0, .drop 0] := …

-- lean/ToyDropFlags/Examples.lean:125
theorem noDoubleDrop_neg_garbage : ¬ NoDoubleDrop [.garbage] := …

-- lean/ToyDropFlags/Examples.lean:127
theorem noDoubleDrop_neg_uncreated : ¬ NoDoubleDrop [.drop 0] := …

-- lean/ToyDropFlags/Examples.lean:129
theorem noLeak_pos : NoLeak [.create 0, .consume 0] := …

-- lean/ToyDropFlags/Examples.lean:131
theorem noLeak_neg : ¬ NoLeak [.create 0] := …

-- lean/ToyDropFlags/Examples.lean:133
theorem exactlyOnce_pos : ExactlyOnce ⟨.returned, [.create 0, .drop 0]⟩ := …

-- lean/ToyDropFlags/Examples.lean:135
theorem exactlyOnce_pos_aborted : ExactlyOnce ⟨.aborted, [.create 0]⟩ := …

-- lean/ToyDropFlags/Examples.lean:137
theorem exactlyOnce_neg_leak : ¬ ExactlyOnce ⟨.returned, [.create 0]⟩ := …

-- lean/ToyDropFlags/Examples.lean:139
theorem exactlyOnce_neg_double : ¬ ExactlyOnce ⟨.aborted, [.create 0, .drop 0, .drop 0]⟩ := …

-- lean/ToyDropFlags/Examples.lean:144
theorem forward_pos : Forward progJoin := …

-- lean/ToyDropFlags/Examples.lean:145
theorem forward_neg : ¬ Forward progLoop := …

-- lean/ToyDropFlags/Examples.lean:146
theorem placesAreMovePaths_pos : PlacesAreMovePaths progPartial := …

-- lean/ToyDropFlags/Examples.lean:147
theorem placesAreMovePaths_neg : ¬ PlacesAreMovePaths progDropStruct := …

-- lean/ToyDropFlags/Examples.lean:148
theorem movesFromInit_pos : MovesFromInit progJoin := …

-- lean/ToyDropFlags/Examples.lean:149
theorem movesFromInit_neg : ¬ MovesFromInit progUseAfterMove := …

-- lean/ToyDropFlags/Examples.lean:150
theorem initsIntoUninit_pos : InitsIntoUninit progReinit := …

-- lean/ToyDropFlags/Examples.lean:151
theorem initsIntoUninit_neg : ¬ InitsIntoUninit progOverwrite := …

-- lean/ToyDropFlags/Examples.lean:154-155
theorem movesFromInit_neg_duplicateCallArg :
    mustInit progDuplicateCallArg .fine 1 x = true ∧ ¬ MovesFromInit progDuplicateCallArg := …

-- lean/ToyDropFlags/Examples.lean:159-161
theorem noNormalPathToResume_pos :
    NoNormalPathToResume progCleanup ∧ NoNormalPathToResume progMultiStepCleanup ∧
    NoNormalPathToResume progUnwindToRet := …

-- lean/ToyDropFlags/Examples.lean:163
theorem noNormalPathToResume_neg : ¬ NoNormalPathToResume progResumeNormal := …

-- lean/ToyDropFlags/Examples.lean:168
theorem moveChecked_pos : MoveChecked progJoin := …

-- lean/ToyDropFlags/Examples.lean:169
theorem moveChecked_neg : ¬ MoveChecked progUseAfterMove := …

-- lean/ToyDropFlags/Examples.lean:180
theorem forwardReachable_pos : ForwardReachable progJoin 2 = true := …

-- lean/ToyDropFlags/Examples.lean:181-182
theorem forwardReachable_neg :
    ForwardReachable { locals := [.leaf], nodes := [.ret, .init x 2, .ret] } 1 = false := …

-- lean/ToyDropFlags/Examples.lean:185-187
theorem forwardReachable_ignores_backward_index_edges :
    ForwardReachable { locals := [.leaf], nodes := [.init x 2, .ret, .branch 1 3, .move x 1] } 1
      = false := …

-- lean/ToyDropFlags/Examples.lean:204
theorem allCompatible_pos : AllCompatible progJoin (stdMap progJoin .fine) := …

-- lean/ToyDropFlags/Examples.lean:206-207
theorem allCompatible_neg :
    ¬ AllCompatible progJoin (overrideAt (stdMap progJoin .fine) 3 x .drop) := …

-- lean/ToyDropFlags/Examples.lean:210
theorem flagSet_progJoin : flagSet progJoin (stdMap progJoin .fine) = [x] := …

-- lean/ToyDropFlags/Examples.lean:212
theorem flagSet_progPartial : flagSet progPartial (stdMap progPartial .fine) = [] := …

-- lean/ToyDropFlags/Examples.lean:214
theorem flagSet_progShare : flagSet progShare (stdMap progShare .fine) = [x0, x1] := …

-- lean/ToyDropFlags/Examples.lean:216-218
theorem flagSet_ignores_unreachable_test :
    flagSet { locals := [.leaf], nodes := [.ret, .ret] }
      (overrideAt (stdMap { locals := [.leaf], nodes := [.ret, .ret] } .fine) 1 x .test) = [] := …

-- lean/ToyDropFlags/Examples.lean:223-225
theorem progOOB_stuck :
    (runElab .abort .std (stdMap progOOB .fine) progOOB []).outcome = .stuck ∧
    ¬ ElabCorrect .abort .std (stdMap progOOB .fine) progOOB := …

-- lean/ToyDropFlags/Examples.lean:237
theorem elabCorrect_pos : ElabCorrect .abort .std (stdMap progJoin .fine) progJoin := …

-- lean/ToyDropFlags/Examples.lean:241-242
theorem elabCorrect_neg :
    ¬ ElabCorrect .abort .std (overrideAt (stdMap progJoin .fine) 3 x .drop) progJoin := …
```

```lean
-- lean/ToyDropFlags/Counterexamples.lean:20-21
theorem progPartial_stdElab_correct :
    ElabCorrect .abort .std (stdMap progPartial .fine) progPartial := …

-- lean/ToyDropFlags/Counterexamples.lean:26-27
theorem progUnwind_stdElab_correct_abort :
    ElabCorrect .abort .std (stdMap progUnwind .fine) progUnwind := …

-- lean/ToyDropFlags/Counterexamples.lean:43-46
theorem exactlyOnce_hypotheses_hold_progCleanup :
    Forward progCleanup ∧ PlacesAreMovePaths progCleanup ∧ MovesFromInit progCleanup ∧
    InitsIntoUninit progCleanup ∧ NoNormalPathToResume progCleanup ∧
    flagSet progCleanup (stdMap progCleanup .fine) = [x] := …

-- lean/ToyDropFlags/Counterexamples.lean:56-59
theorem exactlyOnce_hypotheses_hold_progMultiStepCleanup :
    Forward progMultiStepCleanup ∧ PlacesAreMovePaths progMultiStepCleanup ∧
    MovesFromInit progMultiStepCleanup ∧ InitsIntoUninit progMultiStepCleanup ∧
    NoNormalPathToResume progMultiStepCleanup := …

-- lean/ToyDropFlags/Counterexamples.lean:65-68
theorem stdElab_fails_without_forward :
    ¬ Forward progLoop ∧ PlacesAreMovePaths progLoop ∧ MovesFromInit progLoop ∧
    InitsIntoUninit progLoop ∧ NoNormalPathToResume progLoop ∧
    ¬ ElabCorrect .abort .std (stdMap progLoop .fine) progLoop := …

-- lean/ToyDropFlags/Counterexamples.lean:75-79
theorem stdElab_fails_without_placesAreMovePaths :
    Forward progDropStruct ∧ ¬ PlacesAreMovePaths progDropStruct ∧
    MovesFromInit progDropStruct ∧ InitsIntoUninit progDropStruct ∧
    NoNormalPathToResume progDropStruct ∧
    ¬ ElabCorrect .abort .std (stdMap progDropStruct .fine) progDropStruct := …

-- lean/ToyDropFlags/Counterexamples.lean:85-89
theorem stdElab_fails_without_movesFromInit :
    Forward progUseAfterMove ∧ PlacesAreMovePaths progUseAfterMove ∧
    ¬ MovesFromInit progUseAfterMove ∧ InitsIntoUninit progUseAfterMove ∧
    NoNormalPathToResume progUseAfterMove ∧
    ¬ ElabCorrect .abort .std (stdMap progUseAfterMove .fine) progUseAfterMove := …

-- lean/ToyDropFlags/Counterexamples.lean:95-98
theorem stdElab_fails_without_initsIntoUninit :
    Forward progOverwrite ∧ PlacesAreMovePaths progOverwrite ∧ MovesFromInit progOverwrite ∧
    ¬ InitsIntoUninit progOverwrite ∧ NoNormalPathToResume progOverwrite ∧
    ¬ ElabCorrect .abort .std (stdMap progOverwrite .fine) progOverwrite := …

-- lean/ToyDropFlags/Counterexamples.lean:106-110
theorem stdElab_fails_without_noNormalPathToResume :
    Forward progResumeNormal ∧ PlacesAreMovePaths progResumeNormal ∧
    MovesFromInit progResumeNormal ∧ InitsIntoUninit progResumeNormal ∧
    ¬ NoNormalPathToResume progResumeNormal ∧
    ¬ ElabCorrect .abort .std (stdMap progResumeNormal .fine) progResumeNormal := …

-- lean/ToyDropFlags/Counterexamples.lean:123-127
theorem characterization_fails_without_forward :
    ¬ Forward progLoop ∧ PlacesAreMovePaths progLoop ∧ MovesFromInit progLoop ∧
    InitsIntoUninit progLoop ∧ NoNormalPathToResume progLoop ∧
    ¬ (ElabCorrect .abort .std (stdMap progLoop .fine) progLoop ↔
       AllCompatible progLoop (stdMap progLoop .fine)) := …

-- lean/ToyDropFlags/Counterexamples.lean:132-137
theorem characterization_fails_without_placesAreMovePaths :
    Forward progDropStruct ∧ ¬ PlacesAreMovePaths progDropStruct ∧
    MovesFromInit progDropStruct ∧ InitsIntoUninit progDropStruct ∧
    NoNormalPathToResume progDropStruct ∧
    ¬ (ElabCorrect .abort .std (stdMap progDropStruct .fine) progDropStruct ↔
       AllCompatible progDropStruct (stdMap progDropStruct .fine)) := …

-- lean/ToyDropFlags/Counterexamples.lean:142-147
theorem characterization_fails_without_movesFromInit :
    Forward progUseAfterMove ∧ PlacesAreMovePaths progUseAfterMove ∧
    ¬ MovesFromInit progUseAfterMove ∧ InitsIntoUninit progUseAfterMove ∧
    NoNormalPathToResume progUseAfterMove ∧
    ¬ (ElabCorrect .abort .std (stdMap progUseAfterMove .fine) progUseAfterMove ↔
       AllCompatible progUseAfterMove (stdMap progUseAfterMove .fine)) := …

-- lean/ToyDropFlags/Counterexamples.lean:152-156
theorem characterization_fails_without_initsIntoUninit :
    Forward progOverwrite ∧ PlacesAreMovePaths progOverwrite ∧ MovesFromInit progOverwrite ∧
    ¬ InitsIntoUninit progOverwrite ∧ NoNormalPathToResume progOverwrite ∧
    ¬ (ElabCorrect .abort .std (stdMap progOverwrite .fine) progOverwrite ↔
       AllCompatible progOverwrite (stdMap progOverwrite .fine)) := …

-- lean/ToyDropFlags/Counterexamples.lean:161-166
theorem characterization_fails_without_noNormalPathToResume :
    Forward progResumeNormal ∧ PlacesAreMovePaths progResumeNormal ∧
    MovesFromInit progResumeNormal ∧ InitsIntoUninit progResumeNormal ∧
    ¬ NoNormalPathToResume progResumeNormal ∧
    ¬ (ElabCorrect .abort .std (stdMap progResumeNormal .fine) progResumeNormal ↔
       AllCompatible progResumeNormal (stdMap progResumeNormal .fine)) := …

-- lean/ToyDropFlags/Counterexamples.lean:211-219
theorem flagConfig_gran_inert_on_progPartial :
    explore .abort
      (elaborate { FlagConfig.std with gran := .wholeKill } (stdMap progPartial .fine) progPartial)
      (fuelFor progPartial) =
      explore .abort (stdElab progPartial) (fuelFor progPartial) ∧
    explore .abort
      (elaborate { FlagConfig.std with gran := .wholeKeep } (stdMap progPartial .fine) progPartial)
      (fuelFor progPartial) =
      explore .abort (stdElab progPartial) (fuelFor progPartial) := …

-- lean/ToyDropFlags/Counterexamples.lean:227-228
theorem progPartialFlag_stdElab_correct :
    ElabCorrect .abort .std (stdMap progPartialFlag .fine) progPartialFlag := …

-- lean/ToyDropFlags/Counterexamples.lean:293-302
theorem continueUnwind_leaks_partially_dropped :
    Forward progUnwind ∧ MoveChecked progUnwind ∧ NoNormalPathToResume progUnwind ∧
    (runElab .continueUnwind .std (stdMap progUnwind .fine) progUnwind [true, true]).outcome =
      .unwound ∧
    (runElab .continueUnwind .std (stdMap progUnwind .fine) progUnwind [true, true]).log =
      [.create 0, .create 1, .drop 1] ∧
    NoDoubleDrop
      (runElab .continueUnwind .std (stdMap progUnwind .fine) progUnwind [true, true]).log ∧
    ¬ NoLeak
      (runElab .continueUnwind .std (stdMap progUnwind .fine) progUnwind [true, true]).log := …

-- lean/ToyDropFlags/Counterexamples.lean:306-307
theorem abort_on_same_input :
    (runElab .abort .std (stdMap progUnwind .fine) progUnwind [true, true]).outcome = .aborted := …

-- lean/ToyDropFlags/Counterexamples.lean:312-315
theorem continueUnwind_noDoubleDrop_holds_progUnwind :
    Forward progUnwind ∧ PlacesAreMovePaths progUnwind ∧ MovesFromInit progUnwind ∧
    (explore .continueUnwind (stdElab progUnwind) (fuelFor progUnwind)).all
      (fun r => decide (NoDoubleDrop r.log) && r.outcome.terminated) = true := …

-- lean/ToyDropFlags/Counterexamples.lean:328-333
theorem noDoubleDrop_continueUnwind_fails_without_forward :
    ¬ Forward progLoopMove ∧ PlacesAreMovePaths progLoopMove ∧ MovesFromInit progLoopMove ∧
    ¬ (∀ inp, NoDoubleDrop
          (runElab .continueUnwind .std (stdMap progLoopMove .fine) progLoopMove inp).log ∧
        (runElab .continueUnwind .std (stdMap progLoopMove .fine) progLoopMove inp).outcome.terminated
          = true) := …

-- lean/ToyDropFlags/Counterexamples.lean:338-344
theorem noDoubleDrop_continueUnwind_fails_without_placesAreMovePaths :
    Forward progInitInsideDrop ∧ ¬ PlacesAreMovePaths progInitInsideDrop ∧
    MovesFromInit progInitInsideDrop ∧
    ¬ (∀ inp, NoDoubleDrop (runElab .continueUnwind .std (stdMap progInitInsideDrop .fine)
          progInitInsideDrop inp).log ∧
        (runElab .continueUnwind .std (stdMap progInitInsideDrop .fine)
          progInitInsideDrop inp).outcome.terminated = true) := …

-- lean/ToyDropFlags/Counterexamples.lean:349-355
theorem noDoubleDrop_continueUnwind_fails_without_movesFromInit :
    Forward progUseAfterMove ∧ PlacesAreMovePaths progUseAfterMove ∧
    ¬ MovesFromInit progUseAfterMove ∧
    ¬ (∀ inp, NoDoubleDrop (runElab .continueUnwind .std (stdMap progUseAfterMove .fine)
          progUseAfterMove inp).log ∧
        (runElab .continueUnwind .std (stdMap progUseAfterMove .fine)
          progUseAfterMove inp).outcome.terminated = true) := …

-- lean/ToyDropFlags/Counterexamples.lean:379-388
theorem staticChoice_necessity_fails_without_placesAreMovePaths :
    ¬ PlacesAreMovePaths progIllTyped ∧ isDropPoint progIllTyped 2 = true ∧
    mayInit progIllTyped .fine 2 x = true ∧ mustInit progIllTyped .fine 2 x = false ∧
    ¬ ((∃ inp, ¬ NoDoubleDrop (runElab .abort .std
          (overrideAt (stdMap progIllTyped .fine) 2 x .drop) progIllTyped inp).log) ∧
       (∃ inp,
          (runElab .abort .std (overrideAt (stdMap progIllTyped .fine) 2 x .skip) progIllTyped
            inp).outcome.complete = true ∧
          ¬ NoLeak (runElab .abort .std (overrideAt (stdMap progIllTyped .fine) 2 x .skip)
            progIllTyped inp).log)) := …

-- lean/ToyDropFlags/Counterexamples.lean:408-409
theorem progMoved_skip_correct :
    ElabCorrect .abort .std (overrideAt (stdMap progMoved .fine) 2 x .skip) progMoved := …

-- lean/ToyDropFlags/Counterexamples.lean:411-412
theorem progKept_drop_correct :
    ElabCorrect .abort .std (overrideAt (stdMap progKept .fine) 1 x .drop) progKept := …

-- lean/ToyDropFlags/Counterexamples.lean:418-427
theorem staticChoice_necessity_fails_at_non_drop_point :
    PlacesAreMovePaths progJoinOff ∧ ¬ (isDropPoint progJoinOff 3 = true) ∧
    mayInit progJoinOff .fine 3 x = true ∧ mustInit progJoinOff .fine 3 x = false ∧
    ¬ ((∃ inp, ¬ NoDoubleDrop (runElab .abort .std
          (overrideAt (stdMap progJoinOff .fine) 3 x .drop) progJoinOff inp).log) ∧
       (∃ inp,
          (runElab .abort .std (overrideAt (stdMap progJoinOff .fine) 3 x .skip) progJoinOff
            inp).outcome.complete = true ∧
          ¬ NoLeak (runElab .abort .std (overrideAt (stdMap progJoinOff .fine) 3 x .skip)
            progJoinOff inp).log)) := …

-- lean/ToyDropFlags/Counterexamples.lean:434-443
theorem staticChoice_necessity_fails_without_mayInit :
    PlacesAreMovePaths progMoved ∧ isDropPoint progMoved 2 = true ∧
    ¬ (mayInit progMoved .fine 2 x = true) ∧ mustInit progMoved .fine 2 x = false ∧
    ¬ ((∃ inp, ¬ NoDoubleDrop (runElab .abort .std
          (overrideAt (stdMap progMoved .fine) 2 x .drop) progMoved inp).log) ∧
       (∃ inp,
          (runElab .abort .std (overrideAt (stdMap progMoved .fine) 2 x .skip) progMoved
            inp).outcome.complete = true ∧
          ¬ NoLeak (runElab .abort .std (overrideAt (stdMap progMoved .fine) 2 x .skip)
            progMoved inp).log)) := …

-- lean/ToyDropFlags/Counterexamples.lean:450-459
theorem staticChoice_necessity_fails_without_notMustInit :
    PlacesAreMovePaths progKept ∧ isDropPoint progKept 1 = true ∧
    mayInit progKept .fine 1 x = true ∧ ¬ (mustInit progKept .fine 1 x = false) ∧
    ¬ ((∃ inp, ¬ NoDoubleDrop (runElab .abort .std
          (overrideAt (stdMap progKept .fine) 1 x .drop) progKept inp).log) ∧
       (∃ inp,
          (runElab .abort .std (overrideAt (stdMap progKept .fine) 1 x .skip) progKept
            inp).outcome.complete = true ∧
          ¬ NoLeak (runElab .abort .std (overrideAt (stdMap progKept .fine) 1 x .skip)
            progKept inp).log)) := …

-- lean/ToyDropFlags/Counterexamples.lean:475-479
theorem allCompatible_necessity_fails_without_placesAreMovePaths :
    ¬ PlacesAreMovePaths progIllTyped ∧
    (∀ inp, ExactlyOnce
      (runElab .abort .std (overrideAt (stdMap progIllTyped .fine) 2 x .skip) progIllTyped inp)) ∧
    ¬ AllCompatible progIllTyped (overrideAt (stdMap progIllTyped .fine) 2 x .skip) := …

-- lean/ToyDropFlags/Counterexamples.lean:484-488
theorem allCompatible_necessity_fails_without_exactlyOnce :
    PlacesAreMovePaths progJoin ∧
    ¬ (∀ inp, ExactlyOnce
      (runElab .abort .std (overrideAt (stdMap progJoin .fine) 3 x .drop) progJoin inp)) ∧
    ¬ AllCompatible progJoin (overrideAt (stdMap progJoin .fine) 3 x .drop) := …

-- lean/ToyDropFlags/Counterexamples.lean:494-499
theorem flagSubset_fails_without_placesAreMovePaths :
    ¬ PlacesAreMovePaths progIllTyped ∧
    (∀ inp, ExactlyOnce
      (runElab .abort .std (overrideAt (stdMap progIllTyped .fine) 2 x .skip) progIllTyped inp)) ∧
    ¬ (∀ a ∈ flagSet progIllTyped (stdMap progIllTyped .fine),
        a ∈ flagSet progIllTyped (overrideAt (stdMap progIllTyped .fine) 2 x .skip)) := …

-- lean/ToyDropFlags/Counterexamples.lean:504-509
theorem flagSubset_fails_without_exactlyOnce :
    PlacesAreMovePaths progJoin ∧
    ¬ (∀ inp, ExactlyOnce
      (runElab .abort .std (overrideAt (stdMap progJoin .fine) 3 x .drop) progJoin inp)) ∧
    ¬ (∀ a ∈ flagSet progJoin (stdMap progJoin .fine),
        a ∈ flagSet progJoin (overrideAt (stdMap progJoin .fine) 3 x .drop)) := …

-- lean/ToyDropFlags/Counterexamples.lean:515-520
theorem fewerFlags_fails_without_placesAreMovePaths :
    ¬ PlacesAreMovePaths progIllTyped ∧
    (flagSet progIllTyped (overrideAt (stdMap progIllTyped .fine) 2 x .skip)).length <
      (flagSet progIllTyped (stdMap progIllTyped .fine)).length ∧
    ¬ (∃ inp, ¬ ExactlyOnce
      (runElab .abort .std (overrideAt (stdMap progIllTyped .fine) 2 x .skip) progIllTyped inp)) := …

-- lean/ToyDropFlags/Counterexamples.lean:526-530
theorem fewerFlags_fails_without_lt :
    PlacesAreMovePaths progJoin ∧
    ¬ ((flagSet progJoin (stdMap progJoin .fine)).length <
        (flagSet progJoin (stdMap progJoin .fine)).length) ∧
    ¬ (∃ inp, ¬ ExactlyOnce (runElab .abort .std (stdMap progJoin .fine) progJoin inp)) := …

-- lean/ToyDropFlags/Counterexamples.lean:537-539
theorem staticChoice_hypotheses_hold_progJoin :
    PlacesAreMovePaths progJoin ∧ isDropPoint progJoin 3 = true ∧
    mayInit progJoin .fine 3 x = true ∧ mustInit progJoin .fine 3 x = false := …

-- lean/ToyDropFlags/Counterexamples.lean:553-555
theorem allCompatible_necessity_hypotheses_hold_progJoin :
    PlacesAreMovePaths progJoin ∧
    ∀ inp, ExactlyOnce (runElab .abort .std (fun _ _ => .test) progJoin inp) := …

-- lean/ToyDropFlags/Counterexamples.lean:560-564
theorem stdFlagSet_subset_witness_progJoin :
    PlacesAreMovePaths progJoin ∧
    (∀ inp, ExactlyOnce (runElab .abort .std (fun _ _ => .test) progJoin inp)) ∧
    flagSet progJoin (fun _ _ => .test) = [x] ∧
    flagSet progJoin (stdMap progJoin .fine) = [x] := …

-- lean/ToyDropFlags/Counterexamples.lean:570-575
theorem fewerFlags_hypotheses_hold_progJoin :
    PlacesAreMovePaths progJoin ∧
    (flagSet progJoin (overrideAt (stdMap progJoin .fine) 3 x .drop)).length <
      (flagSet progJoin (stdMap progJoin .fine)).length ∧
    ∃ inp, ¬ ExactlyOnce
      (runElab .abort .std (overrideAt (stdMap progJoin .fine) 3 x .drop) progJoin inp) := …

-- lean/ToyDropFlags/Counterexamples.lean:605-607
theorem dupProg_matches_stdElab_progJoin :
    explore .abort dupProg 10 = explore .abort (stdElab progJoin) (fuelFor progJoin) ∧
    flagSet progJoin (stdMap progJoin .fine) = [x] := …

-- lean/ToyDropFlags/Counterexamples.lean:646-648
theorem shareProg_matches_stdElab_progShare :
    explore .abort shareProg 16 = explore .abort (stdElab progShare) (fuelFor progShare) ∧
    flagSet progShare (stdMap progShare .fine) = [x0, x1] := …

-- lean/ToyDropFlags/Counterexamples.lean:674-675
theorem earlyDropProg_matches_stdElab_progJoin :
    explore .abort earlyDropProg 10 = explore .abort (stdElab progJoin) (fuelFor progJoin) := …

-- lean/ToyDropFlags/Counterexamples.lean:683-688
theorem stdFlagLeast_fails_without_forward :
    ¬ Forward progLoop ∧ PlacesAreMovePaths progLoop ∧ MovesFromInit progLoop ∧
    InitsIntoUninit progLoop ∧ NoNormalPathToResume progLoop ∧
    ¬ (ElabCorrect .abort .std (stdMap progLoop .fine) progLoop ∧
       ∀ d : Nat → Place → Decision, ElabCorrect .abort .std d progLoop →
         ∀ a ∈ flagSet progLoop (stdMap progLoop .fine), a ∈ flagSet progLoop d) := …

-- lean/ToyDropFlags/Counterexamples.lean:692-699
theorem stdFlagLeast_fails_without_placesAreMovePaths :
    Forward progDropStruct ∧ ¬ PlacesAreMovePaths progDropStruct ∧
    MovesFromInit progDropStruct ∧ InitsIntoUninit progDropStruct ∧
    NoNormalPathToResume progDropStruct ∧
    ¬ (ElabCorrect .abort .std (stdMap progDropStruct .fine) progDropStruct ∧
       ∀ d : Nat → Place → Decision, ElabCorrect .abort .std d progDropStruct →
         ∀ a ∈ flagSet progDropStruct (stdMap progDropStruct .fine),
           a ∈ flagSet progDropStruct d) := …

-- lean/ToyDropFlags/Counterexamples.lean:703-710
theorem stdFlagLeast_fails_without_movesFromInit :
    Forward progUseAfterMove ∧ PlacesAreMovePaths progUseAfterMove ∧
    ¬ MovesFromInit progUseAfterMove ∧ InitsIntoUninit progUseAfterMove ∧
    NoNormalPathToResume progUseAfterMove ∧
    ¬ (ElabCorrect .abort .std (stdMap progUseAfterMove .fine) progUseAfterMove ∧
       ∀ d : Nat → Place → Decision, ElabCorrect .abort .std d progUseAfterMove →
         ∀ a ∈ flagSet progUseAfterMove (stdMap progUseAfterMove .fine),
           a ∈ flagSet progUseAfterMove d) := …

-- lean/ToyDropFlags/Counterexamples.lean:714-719
theorem stdFlagLeast_fails_without_initsIntoUninit :
    Forward progOverwrite ∧ PlacesAreMovePaths progOverwrite ∧ MovesFromInit progOverwrite ∧
    ¬ InitsIntoUninit progOverwrite ∧ NoNormalPathToResume progOverwrite ∧
    ¬ (ElabCorrect .abort .std (stdMap progOverwrite .fine) progOverwrite ∧
       ∀ d : Nat → Place → Decision, ElabCorrect .abort .std d progOverwrite →
         ∀ a ∈ flagSet progOverwrite (stdMap progOverwrite .fine), a ∈ flagSet progOverwrite d) := …

-- lean/ToyDropFlags/Counterexamples.lean:723-730
theorem stdFlagLeast_fails_without_noNormalPathToResume :
    Forward progResumeNormal ∧ PlacesAreMovePaths progResumeNormal ∧
    MovesFromInit progResumeNormal ∧ InitsIntoUninit progResumeNormal ∧
    ¬ NoNormalPathToResume progResumeNormal ∧
    ¬ (ElabCorrect .abort .std (stdMap progResumeNormal .fine) progResumeNormal ∧
       ∀ d : Nat → Place → Decision, ElabCorrect .abort .std d progResumeNormal →
         ∀ a ∈ flagSet progResumeNormal (stdMap progResumeNormal .fine),
           a ∈ flagSet progResumeNormal d) := …

-- lean/ToyDropFlags/Counterexamples.lean:743-747
theorem sufficiency_fails_without_forward :
    ¬ Forward progLoop ∧ PlacesAreMovePaths progLoop ∧ MovesFromInit progLoop ∧
    InitsIntoUninit progLoop ∧ NoNormalPathToResume progLoop ∧
    AllCompatible progLoop (stdMap progLoop .fine) ∧
    ¬ ElabCorrect .abort .std (stdMap progLoop .fine) progLoop := …

-- lean/ToyDropFlags/Counterexamples.lean:751-756
theorem sufficiency_fails_without_placesAreMovePaths :
    Forward progDropStruct ∧ ¬ PlacesAreMovePaths progDropStruct ∧
    MovesFromInit progDropStruct ∧ InitsIntoUninit progDropStruct ∧
    NoNormalPathToResume progDropStruct ∧
    AllCompatible progDropStruct (stdMap progDropStruct .fine) ∧
    ¬ ElabCorrect .abort .std (stdMap progDropStruct .fine) progDropStruct := …

-- lean/ToyDropFlags/Counterexamples.lean:760-765
theorem sufficiency_fails_without_movesFromInit :
    Forward progUseAfterMove ∧ PlacesAreMovePaths progUseAfterMove ∧
    ¬ MovesFromInit progUseAfterMove ∧ InitsIntoUninit progUseAfterMove ∧
    NoNormalPathToResume progUseAfterMove ∧
    AllCompatible progUseAfterMove (stdMap progUseAfterMove .fine) ∧
    ¬ ElabCorrect .abort .std (stdMap progUseAfterMove .fine) progUseAfterMove := …

-- lean/ToyDropFlags/Counterexamples.lean:769-773
theorem sufficiency_fails_without_initsIntoUninit :
    Forward progOverwrite ∧ PlacesAreMovePaths progOverwrite ∧ MovesFromInit progOverwrite ∧
    ¬ InitsIntoUninit progOverwrite ∧ NoNormalPathToResume progOverwrite ∧
    AllCompatible progOverwrite (stdMap progOverwrite .fine) ∧
    ¬ ElabCorrect .abort .std (stdMap progOverwrite .fine) progOverwrite := …

-- lean/ToyDropFlags/Counterexamples.lean:777-782
theorem sufficiency_fails_without_noNormalPathToResume :
    Forward progResumeNormal ∧ PlacesAreMovePaths progResumeNormal ∧
    MovesFromInit progResumeNormal ∧ InitsIntoUninit progResumeNormal ∧
    ¬ NoNormalPathToResume progResumeNormal ∧
    AllCompatible progResumeNormal (stdMap progResumeNormal .fine) ∧
    ¬ ElabCorrect .abort .std (stdMap progResumeNormal .fine) progResumeNormal := …

-- lean/ToyDropFlags/Counterexamples.lean:788-792
theorem sufficiency_fails_without_allCompatible :
    Forward progJoin ∧ PlacesAreMovePaths progJoin ∧ MovesFromInit progJoin ∧
    InitsIntoUninit progJoin ∧ NoNormalPathToResume progJoin ∧
    ¬ AllCompatible progJoin (overrideAt (stdMap progJoin .fine) 3 x .drop) ∧
    ¬ ElabCorrect .abort .std (overrideAt (stdMap progJoin .fine) 3 x .drop) progJoin := …

-- lean/ToyDropFlags/Counterexamples.lean:797-800
theorem sufficiency_hypotheses_hold_progJoin_testEverywhere :
    Forward progJoin ∧ PlacesAreMovePaths progJoin ∧ MovesFromInit progJoin ∧
    InitsIntoUninit progJoin ∧ NoNormalPathToResume progJoin ∧
    AllCompatible progJoin (fun _ _ => .test) := …
```

```lean
-- lean/ToyDropFlags/Sufficiency.lean:670-676
theorem analysis_step (s : SProg) {i j : Nat} (hj : j < s.nodes.length) (hij : i < j)
    (hreach : (reachList s).getD i false = true) {Qm QM : List Place}
    (hm : (j, Qm) ∈ edgeOut s.locals .fine (s.node i) ((analysis s .fine true).getD i []))
    (hM : (j, QM) ∈ edgeOut s.locals .fine (s.node i) ((analysis s .fine false).getD i [])) :
    (reachList s).getD j false = true ∧
      (∀ a ∈ Qm, a ∈ (analysis s .fine true).getD j []) ∧
      (∀ a ∈ (analysis s .fine false).getD j [], a ∈ QM) := …

-- lean/ToyDropFlags/Sufficiency.lean:1368-1371
theorem runElab_good (rule : PanicRule) (d : Nat → Place → Decision) (s : SProg)
    (hfwd : Forward s) (hplaces : PlacesAreMovePaths s) (hmoves : MovesFromInit s)
    (hcompat : AllCompatible s d) (inp : List Bool) :
    Good s rule (runElab rule .std d s inp) := …
```

### Primary sources

Fetched and checked on 2026-11-21 (GitHub objects by full commit; papers by DOI or arXiv record).

- **rustc**, `rust-lang/rust` commit `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` (prose only): `compiler/rustc_mir_transform/src/elaborate_drops.rs` lines 21–30 (pass overview), 165–188 (`drop_style`), 290–334 (`collect_drop_flags`; lines 310–312: a flag iff `maybe_init && maybe_uninit`), 359–375 (cleanup blocks ⇒ `Unwind::InCleanup`), 424–431 (flags false at start), 433–451 (call destination flags on the return target), 464–520 (per-location flag effects); `compiler/rustc_mir_transform/src/elaborate_drop.rs` lines 49–56 and 66–71 (`Unwind::InCleanup`: "Already in an unwind path, any panic will cause an abort."; `into_action` ⇒ `UnwindAction::Terminate(UnwindTerminateReason::InCleanup)`), 725–728 (fields "joined together under the `rest` subpath" are "controlled by the primary drop flag"), 1533–1558 (`drop_flag_reset_block`; lines 1539–1543 skip the reset on unwind paths); `compiler/rustc_mir_dataflow/src/drop_flag_effects.rs` lines 108–137 (`drop_flag_effects_for_location`), 139–150 (`for_location_inits`); `compiler/rustc_mir_dataflow/src/move_paths/builder.rs` lines 24–70, 107–305 (child paths created at lines 283–294 for projections visited in the body, via `gather_moves`, lines 346–412), 180–184 (no descent into an ADT with a destructor); `compiler/rustc_mir_dataflow/src/impls/initialized.rs` lines 103–139, 344–380, 206–227; `compiler/rustc_middle/src/mir/syntax.rs` lines 657–683 (cleanup-block restrictions), 1010–1038 (`UnwindAction`); `compiler/rustc_mir_transform/src/validate.rs` lines 246–275 (`check_unwind_edge`); `library/core/src/ops/drop.rs` lines 221–235 (`Drop::drop` "Panics"); `library/core/src/panicking.rs` lines 356–370 (`panic_in_cleanup`).
- **RFC 320, *Non-zeroing dynamic drop***, `rust-lang/rfcs` commit `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `text/0320-nonzeroing-dynamic-drop.md`: lines 6–15 (summary), 50–55, 59–64, 68–75 (the withdrawn static-drop proposal), 99–114 (drop obligations), 116–142 (merge-point rule), 144–155 (stack-local drop flags; lines 153–155: the precise set of flags is not specified).
- **The Rust Reference**, `rust-lang/reference` commit `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`: `src/destructors.md` (`r[destructors.intro]`, `r[destructors.operation]`, `r[destructors.process-termination]`) and `src/panic.md` (`r[panic.unwind.destruction]`). No panic-during-unwinding abort rule was found in `src/destructors.md`, `src/panic.md`, `src/items/functions.md` or `src/runtime.md` at this commit.
- **C++ working draft N4950** (C++23), `cplusplus/draft` tag `n4950` = commit `4e4de1df8ee941255b653b61d0a62050b34cf8c9`, `source/exceptions.tex`: [except.throw]/7 (normative) and its Note 5; [except.terminate]/1 Note 1 item (1.4) (informative); [except.terminate]/2 (normative); [except.ctor]/3; [except.spec]/3, /5, /8. Prose only.
- **J. Wu, Y. Wang, L. Yu, L. Meng, *RustCompCert: A Verified and Verifying Compiler for a Sequential Subset of Rust***, arXiv:2602.07455v1 (DOI 10.48550/arXiv.2602.07455), with the companion arXiv:2510.10015v1; Rocq development `SJTU-PLV/CompCert` commit `e3d03ed822a7aaf452b7022c347187ed1efc1c12`: `rustfrontend/InitAnalysis.v` lines 83–84 (maybe-init / maybe-uninit as Kildall fixpoints), `rustfrontend/ElaborateDrop.v` lines 33–52, 147–181, 253–276, `rustfrontend/ElaborateDropProof.v` lines 4492–4513 (`transl_program_correct`, a forward simulation; the development was not compiled here). No construct for panics, unwinding or cleanup occurs in `rustfrontend/`.
- **V. Fukala, *Formalization of Rust Drop Elaboration***, Bachelor thesis, Programming Language Foundations Lab, ETH Zürich, August 5, 2024 (supervisors I. van Bakel, R. Jung), https://ethz.ch/content/dam/ethz/special-interest/infk/inst-pls/plf-dam/documents/StudentProjects/BachelorTheses/2024-Viktor-Thesis.pdf (§3, §5.4, §6, §6.1, Appendix A). The thesis is identified by this institutional URL, its title, author and date: no DOI, version identifier or published checksum for the PDF was found, and no SHA-256 of the examined copy was recorded, so the file served at the URL is not pinned to an immutable coordinate. The Coq repository named in Appendix A requires a sign-in; its contents and commit were not inspected.
- **T. Ramananandro, G. Dos Reis, X. Leroy, *A Mechanized Semantics for C++ Object Construction and Destruction, with Applications to Resource Management***, POPL 2012, pp. 521–532, DOI 10.1145/2103656.2103718 (also ACM SIGPLAN Notices 47(1), DOI 10.1145/2103621.2103718).
- **A. Weiss, O. Gierczak, D. Patterson, A. Ahmed, *Oxide: The Essence of Rust***, arXiv:1903.00982v4, DOI 10.48550/arXiv.1903.00982.

Novelty: no T3 claim is made. The mechanized developments above cover the panic-free sufficiency of particular flag placements; no mechanized statement was found of exactly-once destruction with unwinding and cleanup ladders, of the necessity direction (R2n, R3), of the characterization of all decision maps (R2), or of flag-set minimality (R7, R7L, R8). The search was not exhaustive.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`) and `python3`. From the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` to a temporary directory (the package is not modified), runs `lake build`, rejects `sorry`, `admit`, `native_decide` and `axiom` in the sources, computes `collectAxioms` for every package declaration (allowed: `propext`, `Classical.choice`, `Quot.sound`), and recomputes for every Lean name referenced by `results.json` (and every name recorded in `audit/statements.json`) the SHA-256 of the statement (Lean `repr` of the type) and of the definition closure (types and values of every package constant reachable from the statement; theorem bodies excluded), comparing them with `audit/statements.json`. Exit status 0 iff every check passes.

A narrower manual check of the main results:

```sh
cd lean
lake build
cat > /tmp/DropFlagsAxioms.lean <<'EOF'
import ToyDropFlags
#print axioms Toy.DropFlags.stdElab_correct_of_forward_moveChecked_noNormalPathToResume
#print axioms Toy.DropFlags.elabCorrect_of_allCompatible_of_forward_moveChecked_noNormalPathToResume
#print axioms Toy.DropFlags.elabCorrect_iff_allCompatible_of_forward_moveChecked_noNormalPathToResume
#print axioms Toy.DropFlags.stdElab_noDoubleDrop_continueUnwind_of_forward_placesAreMovePaths_movesFromInit
#print axioms Toy.DropFlags.stdMap_correct_and_flagSet_least_of_forward_moveChecked_noNormalPathToResume
EOF
lake env lean /tmp/DropFlagsAxioms.lean
```

Each `#print axioms` line must list at most `propext`, `Classical.choice` and `Quot.sound`. To check that the findings still hold after a change to the model, rerun both commands; a change to any definition in a statement's closure changes its closure hash, and `support/revalidate.py` then reports which statements are affected.
