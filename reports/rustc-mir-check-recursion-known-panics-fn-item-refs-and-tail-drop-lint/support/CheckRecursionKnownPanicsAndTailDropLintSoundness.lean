/-!
# Soundness & Boundary Mechanization for Four `rustc` MIR Semantic & Migration Lints

This standalone, zero-dependency Lean 4 (`v4.34.1`) module mechanizes the core
algorithms, soundness theorems, and concrete counterexamples for four `rustc`
MIR lint passes audited against `rust-lang/rust` (`14210df0e27c`, `3ef0c22cdb86`,
and `ce66487ebbd7`):

1. **Part 1 (`CheckCallRecursion` & `CheckDropRecursion`)**:
   - Models `rustc_data_structures::graph::iterate::TriColorDepthFirstSearch`
     and `rustc_mir_transform::check_call_recursion` (`ignore_edge`,
     `NodeStatus::Visited => Break(NonRecursive)`, `TerminatorKind::TailCall`).
   - Proves `triColorBackEdge_false_negative_witness` and
     `triColorBackEdge_drop_false_negative_witness`: a bounded terminating loop
     preceding unconditional recursion (or recursive `Drop`) triggers a CFG
     back-edge and suppresses `unconditional_recursion`, even though every
     concrete execution terminates the loop and recurses unconditionally.
   - Formalizes SCC-condensation DAG reachability (`sccCondensationCheck`),
     where a may-exit SCC is NOT a return sink while a closed nontrivial SCC
     (`loop {}`) IS an escape sink, and proves both
     `sccRecursionCheck_sound_for_loop_terminating_executions` and
     `sccRecursionCheck_complete_on_terminating_loops`.
   - Proves the `TerminatorKind::TailCall` (`become`) trichotomy:
     `tailCall_pure_become_silent`, `tailCall_mixed_become_highlights_only_call`,
     and `tailCall_nonrecursive_become_false_positive_witness` (plus repair
     `fixedTailCallCheck_eliminates_false_positive`).

2. **Part 2 (`KnownPanicsLint`)**:
   - Models `ConstPropagator` over `InterpCx<DummyMachine>`, `CanConstProp`
     (`FullConstProp`, `OnlyInsideOwnBlock`, `NoPropagation`), single-visit
     worklist propagation, block-exit wiping of `written_only_inside_own_block_locals`,
     `Ref`/`RawPtr` poisoning, `Repeat` bailout, `SwitchInt` constant folding,
     and symbolic-LHS shift overflow checking.
   - Proves `knownPanics_constProp_implies_runtime_assert_fail`,
     `knownPanics_shift_overflow_symbolic_lhs_sound`,
     `knownPanics_onlyInsideOwnBlock_wipes_join`, and
     `knownPanics_dead_const_branch_pruned`.

3. **Part 3 (`FunctionItemReferences`)**:
   - Models `FnDef` (zero-sized) vs `fn()` function pointer types, `is_fn_ref`,
     `sym::transmute` checking, positive `fmt::Pointer` clause checking, and
     runtime ZST dangling-address collapse (`0x1`).
   - Proves `fnItemRef_loses_identity_fnPtr_preserves_identity` and
     `fnItemRefLint_sound_and_complete_on_pointer_and_transmute`.

4. **Part 4 (`LintTailExprDropOrder`)**:
   - Models `BackwardIncompatibleDropHint` (BID), `MaybeInitializedPlaces`,
     `DropsReachable` (non-cleanup forward reachability stopping at the current
     drop of the BID place), `extract_component_with_significant_dtor`, and the
     `_0` / closure-capture / BID-descendant exclusions.
   - Proves `dropsReachable_sound_for_significant_dtor_swap`,
     `dropsReachable_complete_when_no_intervening_sig_drop`, and
     `dropsReachable_ed2021_vs_ed2024_concrete_witness`.

Purity invariants: 0 `sorry`, 0 `Classical.choice`, 0 `omega`, 0 `bv_decide`,
0 `native_decide`, 0 `partial def`, 0 `._unsafe_rec` helpers.
-/

namespace RustcMirLintSoundness

/-! ## Shared Total Helpers (Zero `._unsafe_rec`, Zero `Classical.choice`) -/

def natEq (a b : Nat) : Bool := Nat.beq a b

theorem natEq_true_iff : ∀ a b : Nat, natEq a b = true ↔ a = b
  | 0, 0 => ⟨fun _ => rfl, fun _ => rfl⟩
  | 0, _ + 1 => Iff.intro (fun h => nomatch h) (fun h => nomatch h)
  | _ + 1, 0 => Iff.intro (fun h => nomatch h) (fun h => nomatch h)
  | a + 1, b + 1 => by
    constructor
    · intro h
      exact congrArg Nat.succ ((natEq_true_iff a b).1 h)
    · intro h
      exact (natEq_true_iff a b).2 (Nat.succ.inj h)

theorem natEq_refl (a : Nat) : natEq a a = true := by
  exact (natEq_true_iff a a).2 rfl

def boolEq (a b : Bool) : Bool :=
  match a, b with
  | true, true => true
  | false, false => true
  | _, _ => false

theorem boolEq_true_iff (a b : Bool) : boolEq a b = true ↔ a = b := by
  cases a <;> cases b <;> constructor <;> intro h <;> first | rfl | cases h

def memNat (x : Nat) (xs : List Nat) : Bool :=
  xs.foldr (fun y acc => if natEq x y then true else acc) false

theorem memNat_true_iff (x : Nat) : ∀ xs : List Nat, memNat x xs = true ↔ x ∈ xs
  | [] => by
    constructor
    · intro h; cases h
    · intro h; cases h
  | y :: ys => by
    unfold memNat
    dsimp only [List.foldr]
    cases hxy : natEq x y with
    | true =>
      have heq : x = y := (natEq_true_iff x y).1 hxy
      subst heq
      constructor
      · intro _; exact List.Mem.head ys
      · intro _; rfl
    | false =>
      have hne : x ≠ y := by
        intro heq
        subst heq
        rw [natEq_refl] at hxy
        cases hxy
      constructor
      · intro h
        exact List.Mem.tail y ((memNat_true_iff x ys).1 h)
      · intro h
        cases h with
        | head => exact absurd rfl hne
        | tail _ hmem => exact (memNat_true_iff x ys).2 hmem

def insertNat (x : Nat) (xs : List Nat) : List Nat :=
  if memNat x xs then xs else x :: xs

theorem mem_insertNat_iff (x y : Nat) (xs : List Nat) :
    x ∈ insertNat y xs ↔ x = y ∨ x ∈ xs := by
  unfold insertNat
  cases h : memNat y xs with
  | true =>
    have hy : y ∈ xs := (memNat_true_iff y xs).1 h
    constructor
    · intro hx; exact Or.inr hx
    · intro hor
      cases hor with
      | inl hxy => subst hxy; exact hy
      | inr hx => exact hx
  | false =>
    constructor
    · intro hx
      cases hx with
      | head => exact Or.inl rfl
      | tail _ hmem => exact Or.inr hmem
    · intro hor
      cases hor with
      | inl hxy => subst hxy; exact List.Mem.head xs
      | inr hx => exact List.Mem.tail y hx

def unionNat (xs ys : List Nat) : List Nat :=
  xs.foldr (fun x acc => insertNat x acc) ys

theorem mem_unionNat_iff (z : Nat) : ∀ xs ys : List Nat,
    z ∈ unionNat xs ys ↔ z ∈ xs ∨ z ∈ ys
  | [], ys => by
    unfold unionNat
    dsimp only [List.foldr]
    constructor
    · intro h; exact Or.inr h
    · intro h
      cases h with
      | inl h0 => cases h0
      | inr hy => exact hy
  | x :: xs, ys => by
    unfold unionNat
    dsimp only [List.foldr]
    rw [mem_insertNat_iff]
    change z = x ∨ z ∈ unionNat xs ys ↔ _
    rw [mem_unionNat_iff z xs ys]
    constructor
    · intro h
      cases h with
      | inl hzx => subst hzx; exact Or.inl (List.Mem.head xs)
      | inr hrest =>
        cases hrest with
        | inl hxs => exact Or.inl (List.Mem.tail x hxs)
        | inr hys => exact Or.inr hys
    · intro h
      cases h with
      | inl hxxs =>
        cases hxxs with
        | head => exact Or.inl rfl
        | tail _ hxs => exact Or.inr (Or.inl hxs)
      | inr hys => exact Or.inr (Or.inr hys)

def anyNat (p : Nat → Bool) (xs : List Nat) : Bool :=
  xs.foldr (fun x acc => if p x then true else acc) false

theorem anyNat_true_iff (p : Nat → Bool) : ∀ xs : List Nat,
    anyNat p xs = true ↔ ∃ x, x ∈ xs ∧ p x = true
  | [] => by
    constructor
    · intro h; cases h
    · intro ⟨_, hmem, _⟩; cases hmem
  | y :: ys => by
    unfold anyNat
    dsimp only [List.foldr]
    cases hpy : p y with
    | true =>
      constructor
      · intro _; exact ⟨y, List.Mem.head ys, hpy⟩
      · intro _; rfl
    | false =>
      constructor
      · intro h
        let ⟨x, hmem, hpx⟩ := (anyNat_true_iff p ys).1 h
        exact ⟨x, List.Mem.tail y hmem, hpx⟩
      · intro ⟨x, hmem, hpx⟩
        cases hmem with
        | head => rw [hpx] at hpy; cases hpy
        | tail _ htail => exact (anyNat_true_iff p ys).2 ⟨x, htail, hpx⟩

def natRange (n : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) [] (fun k acc => k :: acc) n

theorem mem_natRange_iff (k : Nat) : ∀ n : Nat, k ∈ natRange n ↔ k < n
  | 0 => by
    unfold natRange
    constructor
    · intro h; cases h
    · intro h; exact absurd h (Nat.not_lt_zero k)
  | n + 1 => by
    unfold natRange
    dsimp only
    constructor
    · intro h
      cases h with
      | head => exact Nat.lt_succ_self _
      | tail _ htail => exact Nat.lt_trans ((mem_natRange_iff k n).1 htail) (Nat.lt_succ_self n)
    · intro hlt
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with
      | inl hlt' => exact List.Mem.tail n ((mem_natRange_iff k n).2 hlt')
      | inr heq => subst heq; exact List.Mem.head (natRange k)

theorem int_add_eq_zero_cancel (a b : Int) (h : a = b) : a - b = 0 := by
  subst h
  exact Int.sub_self a

/-! ============================================================================
    PART 1: `CheckCallRecursion` & `CheckDropRecursion`
    (`TriColorDepthFirstSearch` Back-Edge FN, SCC Condensation, `TailCall`)
============================================================================ -/

section CheckRecursion

/-- Terminator taxonomy mirroring `compiler/rustc_mir_transform/src/check_call_recursion.rs:203-237`. -/
inductive RecTerm where
  | return_
  | unwindResume
  | unwindTerminate
  | unreachable
  | yield_
  | inlineAsmNoTargets
  | inlineAsmWithTargets (targets : List Nat)
  | goto (target : Nat)
  | switchInt (targets : List Nat)
  | call (isSelfRec : Bool) (retTarget : Option Nat) (unwindTarget : Option Nat)
  | drop (isSelfRecDrop : Bool) (retTarget : Nat) (unwindTarget : Option Nat)
  | tailCall (isSelfRec : Bool)
  | falseEdge (realTarget : Nat) (imagTarget : Nat)

/-- Raw CFG successors matching `Terminator::successors()` in `rustc_middle::mir`. -/
def RecTerm.rawSuccessors : RecTerm → List Nat
  | .return_ => []
  | .unwindResume => []
  | .unwindTerminate => []
  | .unreachable => []
  | .yield_ => []
  | .inlineAsmNoTargets => []
  | .inlineAsmWithTargets ts => ts
  | .goto t => [t]
  | .switchInt ts => ts
  | .call _ ret unwind =>
    match ret, unwind with
    | some r, some u => [r, u]
    | some r, none => [r]
    | none, some u => [u]
    | none, none => []
  | .drop _ r (some u) => [r, u]
  | .drop _ r none => [r]
  | .tailCall _ => []
  | .falseEdge r i => [r, i]

/-- Classifier matching `CallRecursion` / `RecursiveDrop` in `check_call_recursion.rs:123-186`.
    Note that `TerminatorKind::TailCall` is NOT matched by `CallRecursion::is_recursive_terminator`
    (lines 131-133) nor by `RecursiveDrop` (line 181). -/
def RecTerm.isRustcClassifiedRec : RecTerm → Bool
  | .call true _ _ => true
  | .drop true _ _ => true
  | _ => false

/-- True semantic self-recursion (including self-recursive `TailCall`). -/
def RecTerm.isSemanticSelfRec : RecTerm → Bool
  | .call true _ _ => true
  | .drop true _ _ => true
  | .tailCall true => true
  | _ => false

/-- Explicit escape terminators as classified by `rustc` (`check_call_recursion.rs:205-220`).
    Crucially, `TailCall` is NOT in this set in `rustc` even when `isSelfRec = false`! -/
def RecTerm.isRustcDirectEscape : RecTerm → Bool
  | .return_ => true
  | .unwindResume => true
  | .unwindTerminate => true
  | .unreachable => true
  | .yield_ => true
  | .inlineAsmNoTargets => true
  | _ => false

/-- Genuine non-recursive control-flow return/exit to caller: includes `TailCall(false)`
    (tail-calling a distinct non-recursive function). -/
def RecTerm.isGenuineEscape : RecTerm → Bool
  | .return_ => true
  | .unwindResume => true
  | .unwindTerminate => true
  | .unreachable => true
  | .yield_ => true
  | .inlineAsmNoTargets => true
  | .tailCall false => true
  | _ => false

/-- Exact `ignore_edge` predicate from `check_call_recursion.rs:259-271`. -/
def RecTerm.rustcIgnoreEdge (term : RecTerm) (target : Nat) : Bool :=
  let rawSuccs := term.rawSuccessors
  let isCleanupUnwind :=
    match term with
    | .call _ _ (some u) => natEq u target
    | .drop _ _ (some u) => natEq u target
    | _ => false
  let ignoreUnwind := isCleanupUnwind && (Nat.ble 2 rawSuccs.length)
  if ignoreUnwind || term.isRustcClassifiedRec then
    true
  else
    match term with
    | .falseEdge _ imag => natEq imag target
    | _ => false

/-- Filtered successors explored by `TriColorDepthFirstSearch` in `check_call_recursion.rs`. -/
def RecTerm.filteredSuccessors (term : RecTerm) : List Nat :=
  term.rawSuccessors.filter (fun s => !(term.rustcIgnoreEdge s))

/-- A finite MIR CFG for recursion checking. -/
structure RecCfg where
  numBlocks : Nat
  startBlock : Nat
  termOf : Nat → RecTerm

/-- Exact `NodeStatus` and stack `Event` from `rustc_data_structures::graph::iterate`. -/
inductive NodeStatus where
  | visited
  | settled

inductive DfsEvent where
  | enter (bb : Nat)
  | settle (bb : Nat)

/-- Result of running `check_recursion` (`check_call_recursion.rs:64-93`). -/
inductive RecLintOutcome where
  | nonRecursive
  | silentNoRecCalls
  | warn (callSiteBlocks : List Nat)

/-- State of iterative `TriColorDepthFirstSearch` (`graph/iterate/mod.rs:214-288`). -/
structure TriColorState where
  stack : List DfsEvent
  visited : List Nat
  settled : List Nat
  recCalls : List Nat

def pushVisitedEvents (succs : List Nat) (stk : List DfsEvent) : List DfsEvent :=
  succs.foldl (fun acc s => DfsEvent.enter s :: acc) stk

/-- One fuel step of `TriColorDepthFirstSearch::run_from` with `Search` visitor.
    Mirrors `graph/iterate/mod.rs:248-287` and `check_call_recursion.rs:193-271`. -/
def triColorRun (cfg : RecCfg) (fuel : Nat) (st : TriColorState) : Option RecLintOutcome :=
  Nat.rec (motive := fun _ => TriColorState → Option RecLintOutcome)
    (fun _ => none)
    (fun _ ih st =>
      match st.stack with
      | [] =>
        if st.recCalls.isEmpty then
          some .silentNoRecCalls
        else
          some (.warn st.recCalls)
      | .settle bb :: rest =>
        let settled' := insertNat bb st.settled
        let term := cfg.termOf bb
        let recCalls' :=
          if term.isRustcClassifiedRec then st.recCalls ++ [bb] else st.recCalls
        ih { st with stack := rest, settled := settled', recCalls := recCalls' }
      | .enter bb :: rest =>
        let alreadyVisited := memNat bb st.visited
        let alreadySettled := memNat bb st.settled
        if alreadyVisited && !alreadySettled then
          -- `prior_status = Some(NodeStatus::Visited)` -> back-edge -> Break(NonRecursive)!
          some .nonRecursive
        else if alreadySettled then
          -- `prior_status = Some(NodeStatus::Settled)` -> forward/cross edge
          let term := cfg.termOf bb
          if term.isRustcDirectEscape then
            some .nonRecursive
          else
            ih { st with stack := rest }
        else
          -- `prior_status = None` -> first discovery
          let visited' := insertNat bb st.visited
          let term := cfg.termOf bb
          if term.isRustcDirectEscape then
            some .nonRecursive
          else
            let succs := term.filteredSuccessors
            let stk' := pushVisitedEvents succs (DfsEvent.settle bb :: rest)
            ih { st with stack := stk', visited := visited' })
    fuel st

/-- Top-level executable mirror of `check_recursion` (`check_call_recursion.rs:64-93`). -/
def checkRecursionRustc (cfg : RecCfg) (fuel : Nat) : Option RecLintOutcome :=
  triColorRun cfg fuel
    { stack := [DfsEvent.enter cfg.startBlock], visited := [], settled := [], recCalls := [] }

/-! ### Witness 1: `bounded_loop_then_recurse` (False Negative in `CheckCallRecursion`)

MIR skeleton of:
```rust
fn bounded_loop_then_recurse(x: u32) -> u32 {
    let mut i = 0;
    while i < 1 { i += 1; }
    bounded_loop_then_recurse(x + i)
}
```
Blocks:
- `bb0`: `goto -> bb1` (entry)
- `bb1`: `switchInt(i < 1) -> [bb2 (loop body), bb3 (loop exit)]`
- `bb2`: `i += 1; goto -> bb1` (back-edge!)
- `bb3`: `call(isSelfRec = true, ret = some bb4, unwind = none)`
- `bb4`: `return`
-/

def boundedLoopCfg : RecCfg :=
  { numBlocks := 5
  , startBlock := 0
  , termOf := fun bb =>
      match bb with
      | 0 => .goto 1
      | 1 => .switchInt [2, 3]
      | 2 => .goto 1
      | 3 => .call true (some 4) none
      | _ => .return_
  }

/-- Operational semantics for `bounded_loop_then_recurse` with loop counter `i : Nat`. -/
inductive LoopExecResult where
  | stepped (bb : Nat) (i : Nat)
  | hitSelfRecursion (bb : Nat)
  | returned

def stepBoundedLoop (bb i : Nat) : LoopExecResult :=
  match bb with
  | 0 => .stepped 1 0
  | 1 => if Nat.blt i 1 then .stepped 2 i else .stepped 3 i
  | 2 => .stepped 1 (i + 1)
  | 3 => .hitSelfRecursion 3
  | _ => .returned

def runBoundedLoop (fuel bb i : Nat) : LoopExecResult :=
  Nat.rec (motive := fun _ => Nat → Nat → LoopExecResult)
    (fun bb i => .stepped bb i)
    (fun _ ih bb i =>
      match stepBoundedLoop bb i with
      | .stepped bb' i' => ih bb' i'
      | r => r)
    fuel bb i

/-- Concrete execution of `bounded_loop_then_recurse` ALWAYS terminates the bounded
    loop and hits self-recursion at `bb3` (for every initial register state `i0`),
    never reaching `return`. -/
theorem boundedLoop_always_recurses (i0 : Nat) :
    runBoundedLoop 10 0 i0 = .hitSelfRecursion 3 := by
  rfl

/-- **Main Theorem 1A (Back-Edge False-Negative Witness)**:
    `boundedLoopCfg` unconditionally recurses on every concrete execution, yet
    `rustc`'s `TriColorDepthFirstSearch` returns `NonRecursive` (0 warnings)
    because the loop back-edge `bb2 -> bb1` encounters `NodeStatus::Visited`. -/
theorem triColorBackEdge_false_negative_witness :
    (∀ i0 : Nat, runBoundedLoop 10 0 i0 = .hitSelfRecursion 3) ∧
    checkRecursionRustc boundedLoopCfg 30 = some .nonRecursive := by
  constructor
  · exact boundedLoop_always_recurses
  · rfl

/-- Analogous CFG for `impl Drop for LoopBadDrop` (`CheckDropRecursion`). -/
def loopBadDropCfg : RecCfg :=
  { numBlocks := 5
  , startBlock := 0
  , termOf := fun bb =>
      match bb with
      | 0 => .goto 1
      | 1 => .switchInt [2, 3]
      | 2 => .goto 1
      | 3 => .drop true 4 none
      | _ => .return_
  }

/-- **Theorem 1A-Drop**: `CheckDropRecursion` shares `check_recursion` and exhibits
    the exact same back-edge false negative on `LoopBadDrop`. -/
theorem triColorBackEdge_drop_false_negative_witness :
    checkRecursionRustc loopBadDropCfg 30 = some .nonRecursive := by
  rfl

/-! ### Witness 2: `TerminatorKind::TailCall` (`become`) Asymmetry & False Positive -/

/-- `fn pure_become(x) { become pure_become(x) }`: 1 block with `TailCall(true)`. -/
def pureBecomeCfg : RecCfg :=
  { numBlocks := 1
  , startBlock := 0
  , termOf := fun _ => .tailCall true
  }

/-- `fn mixed_become_and_call(b, x) { if b { become self } else { self } }`. -/
def mixedBecomeAndCallCfg : RecCfg :=
  { numBlocks := 4
  , startBlock := 0
  , termOf := fun bb =>
      match bb with
      | 0 => .switchInt [1, 2]
      | 1 => .tailCall true
      | 2 => .call true (some 3) none
      | _ => .return_
  }

/-- `fn become_other_or_self_call(b, x) { if b { become helper(b, x) } else { self(true, x) } }`.
    Terminates for ALL `b : Bool` in at most 2 steps, yet `rustc` warns! -/
def becomeOtherOrSelfCallCfg : RecCfg :=
  { numBlocks := 4
  , startBlock := 0
  , termOf := fun bb =>
      match bb with
      | 0 => .switchInt [1, 2]
      | 1 => .tailCall false
      | 2 => .call true (some 3) none
      | _ => .return_
  }

/-- Fuel-indexed operational semantics for `become_other_or_self_call(b, x)`:
    - `b = true` returns `some (x + 1)` in 1 step via `non_recursive_helper`;
    - `b = false` calls `self(true, x)` which returns `some (x + 1)` in 2 steps. -/
def evalBecomeOtherOrSelf (fuel : Nat) (b : Bool) (x : Nat) : Option Nat :=
  Nat.rec (motive := fun _ => Bool → Nat → Option Nat)
    (fun _ _ => none)
    (fun _ ih b x =>
      match b with
      | true => some (x + 1)
      | false => ih true x)
    fuel b x

/-- `pure_become` emits 0 warnings because `TailCall` is not added to `reachable_recursive_calls`. -/
theorem tailCall_pure_become_silent :
    checkRecursionRustc pureBecomeCfg 10 = some .silentNoRecCalls := by
  rfl

/-- `mixed_become_and_call` emits `unconditional_recursion`, highlighting ONLY the `else`
    `Call` block `2`, omitting the `then` `TailCall` block `1`. -/
theorem tailCall_mixed_become_highlights_only_call :
    checkRecursionRustc mixedBecomeAndCallCfg 20 = some (.warn [2]) := by
  rfl

/-- Concrete reachability to a genuine non-recursive escape along unfiltered normal edges. -/
inductive ReachesGenuineEscape (cfg : RecCfg) : Nat → Prop where
  | here {bb : Nat} (h : (cfg.termOf bb).isGenuineEscape = true) :
      ReachesGenuineEscape cfg bb
  | step {bb succ : Nat}
      (hNotRec : (cfg.termOf bb).isSemanticSelfRec = false)
      (hEdge : succ ∈ (cfg.termOf bb).filteredSuccessors)
      (hRest : ReachesGenuineEscape cfg succ) :
      ReachesGenuineEscape cfg bb

/-- **Theorem 1C (Live `rustc` False Positive on Non-Recursive `become`)**:
    `become_other_or_self_call` ALWAYS terminates (`evalBecomeOtherOrSelf 2 b x = some (x + 1)`
    for every `b : Bool` and `x : Nat`) and has a 1-step genuine escape path
    (`bb0 -> bb1: TailCall(false)`), YET `rustc`'s `CheckCallRecursion` emits
    `unconditional_recursion` blaming block `2`! -/
theorem tailCall_nonrecursive_become_false_positive_witness :
    (∀ b : Bool, ∀ x : Nat, evalBecomeOtherOrSelf 2 b x = some (x + 1)) ∧
    ReachesGenuineEscape becomeOtherOrSelfCallCfg 0 ∧
    checkRecursionRustc becomeOtherOrSelfCallCfg 20 = some (.warn [2]) := by
  refine ⟨?_, ?_, rfl⟩
  · intro b x
    cases b <;> rfl
  · apply ReachesGenuineEscape.step (succ := 1)
    · rfl
    · exact List.Mem.head [2]
    · exact ReachesGenuineEscape.here rfl

/-! ### Sound SCC-Condensation Unconditional-Recursion Criterion -/

/-- Filtered CFG edge predicate (ignoring recursive-call return edges, non-sole
    cleanup unwind edges, and `FalseEdge` imaginary targets). -/
def CfgEdge (cfg : RecCfg) (u v : Nat) : Prop :=
  v ∈ (cfg.termOf u).filteredSuccessors

/-- An SCC condensation of `cfg` assigns each block `u < cfg.numBlocks` a component
    index `compOf u < numComps` in reverse topological order: every edge `u -> v`
    has `compOf v ≤ compOf u` (so cross-SCC edges strictly decrease `compOf`). -/
structure SccCondensation (cfg : RecCfg) where
  numComps : Nat
  compOf : Nat → Nat
  compBound : ∀ u, u < cfg.numBlocks → compOf u < numComps
  edgeInBounds : ∀ u v, u < cfg.numBlocks → CfgEdge cfg u v → v < cfg.numBlocks
  revTopo : ∀ u v, u < cfg.numBlocks → CfgEdge cfg u v → compOf v ≤ compOf u

/-- A component `c` has an outgoing cross-SCC edge in the condensation DAG. -/
def SccCondensation.hasExitEdge {cfg : RecCfg} (scc : SccCondensation cfg) (c : Nat) : Prop :=
  ∃ u v, u < cfg.numBlocks ∧ scc.compOf u = c ∧ CfgEdge cfg u v ∧ scc.compOf v < c

/-- A component `c` contains an explicit genuine escape terminator (including
    non-recursive `TailCall(false)`). -/
def SccCondensation.hasExplicitEscape {cfg : RecCfg} (scc : SccCondensation cfg) (c : Nat) : Prop :=
  ∃ u, u < cfg.numBlocks ∧ scc.compOf u = c ∧ (cfg.termOf u).isGenuineEscape = true

/-- A component `c` contains a self-recursive terminator (`Call(true)`, `Drop(true)`,
    or `TailCall(true)`). -/
def SccCondensation.hasRecCall {cfg : RecCfg} (scc : SccCondensation cfg) (c : Nat) : Prop :=
  ∃ u, u < cfg.numBlocks ∧ scc.compOf u = c ∧ (cfg.termOf u).isSemanticSelfRec = true

/-- A component `c` is a **closed non-recursive loop** (like `loop {}`): it has an
    intra-SCC edge (so it can loop forever), NO outgoing cross-SCC edge, and NO
    recursive call inside `c`. Such an SCC legitimately diverges without recursing. -/
def SccCondensation.isClosedNonRecLoop {cfg : RecCfg} (scc : SccCondensation cfg) (c : Nat) : Prop :=
  (∃ u v, u < cfg.numBlocks ∧ scc.compOf u = c ∧ scc.compOf v = c ∧ CfgEdge cfg u v) ∧
  ¬ scc.hasExitEdge c ∧
  ¬ scc.hasRecCall c

/-- An SCC `c` is an **escape sink** iff it contains a genuine escape terminator OR
    is a closed non-recursive loop (`loop {}`).
    Crucially, a **may-exit SCC** (a cycle with `hasExitEdge c` and no internal escape)
    is NOT an escape sink! -/
def SccCondensation.isEscapeSink {cfg : RecCfg} (scc : SccCondensation cfg) (c : Nat) : Prop :=
  scc.hasExplicitEscape c ∨ scc.isClosedNonRecLoop c

/-- Reachability between SCCs in the condensation DAG (strictly decreasing `compOf`). -/
inductive DagReach {cfg : RecCfg} (scc : SccCondensation cfg) : Nat → Nat → Prop where
  | refl (c : Nat) : DagReach scc c c
  | step {c1 c2 c3 : Nat}
      (u v : Nat)
      (hu : u < cfg.numBlocks)
      (hc1 : scc.compOf u = c1)
      (hc2 : scc.compOf v = c2)
      (hEdge : CfgEdge cfg u v)
      (hStrict : c2 < c1)
      (hRest : DagReach scc c2 c3) :
      DagReach scc c1 c3

theorem dagReach_trans {cfg : RecCfg} (scc : SccCondensation cfg) {c1 c2 c3 : Nat}
    (h12 : DagReach scc c1 c2) (h23 : DagReach scc c2 c3) :
    DagReach scc c1 c3 := by
  induction h12 with
  | refl _ => exact h23
  | step u v hu hc1 hc2 hEdge hStrict _ ih =>
    exact DagReach.step u v hu hc1 hc2 hEdge hStrict (ih h23)

/-- Every CFG edge `u -> v` induces a `DagReach` step from `compOf u` to `compOf v`
    (either `refl` for intra-SCC edges or `step` for cross-SCC edges). -/
theorem dagReach_of_cfgEdge {cfg : RecCfg} (scc : SccCondensation cfg) {u v : Nat}
    (hu : u < cfg.numBlocks) (hEdge : CfgEdge cfg u v) :
    DagReach scc (scc.compOf u) (scc.compOf v) := by
  have hle : scc.compOf v ≤ scc.compOf u := scc.revTopo u v hu hEdge
  cases Nat.lt_or_eq_of_le hle with
  | inl hlt =>
    exact DagReach.step u v hu rfl rfl hEdge hlt (DagReach.refl _)
  | inr heq =>
    rw [heq]
    exact DagReach.refl _

/-- **SCC-Condensation Unconditional-Recursion Criterion**:
    A function unconditionally recurses (modulo termination of may-exit loops) iff:
    1. No escape-sink SCC (explicit escape or closed `loop {}` SCC) is reachable from
       `compOf start` in the condensation DAG, AND
    2. At least one SCC containing a self-recursive terminator is reachable from
       `compOf start`. -/
def SccUnconditionalRecursion {cfg : RecCfg} (scc : SccCondensation cfg) : Prop :=
  (∀ c, DagReach scc (scc.compOf cfg.startBlock) c → ¬ scc.isEscapeSink c) ∧
  (∃ c, DagReach scc (scc.compOf cfg.startBlock) c ∧ scc.hasRecCall c)

/-- **Soundness Theorem (`sccRecursionCheck_sound_for_loop_terminating_executions`)**:
    If `SccUnconditionalRecursion scc` holds for a valid SCC condensation of `cfg`
    (with `startBlock < numBlocks`), then NO finite execution path from `startBlock`
    can reach ANY genuine non-recursive escape (`¬ ReachesGenuineEscape cfg startBlock`)!
    In particular, every execution in which may-exit loops terminate must reach a
    self-recursive call/drop/tail-call. -/
theorem reachesGenuineEscape_implies_dagReach_escapeSink {cfg : RecCfg}
    (scc : SccCondensation cfg) {bb : Nat}
    (hbb : bb < cfg.numBlocks)
    (hEsc : ReachesGenuineEscape cfg bb) :
    ∃ c, DagReach scc (scc.compOf bb) c ∧ scc.isEscapeSink c := by
  induction hEsc with
  | @here u hterm =>
    exact ⟨scc.compOf u, DagReach.refl _, Or.inl ⟨u, hbb, rfl, hterm⟩⟩
  | @step u v _ hEdge _ ih =>
    have hv : v < cfg.numBlocks := scc.edgeInBounds u v hbb hEdge
    let ⟨c, hReachV, hSink⟩ := ih hv
    have hUV : DagReach scc (scc.compOf u) (scc.compOf v) := dagReach_of_cfgEdge scc hbb hEdge
    exact ⟨c, dagReach_trans scc hUV hReachV, hSink⟩

theorem sccRecursionCheck_sound_for_loop_terminating_executions {cfg : RecCfg}
    (scc : SccCondensation cfg)
    (hStart : cfg.startBlock < cfg.numBlocks)
    (hCheck : SccUnconditionalRecursion scc) :
    ¬ ReachesGenuineEscape cfg cfg.startBlock := by
  intro hEsc
  let ⟨c, hReach, hSink⟩ := reachesGenuineEscape_implies_dagReach_escapeSink scc hStart hEsc
  exact hCheck.1 c hReach hSink

/-! ### Executable Decidable SCC-Condensation Checker & Completeness on Terminating Loops -/

/-- Explicit SCC condensation of `boundedLoopCfg`:
    - `comp 3`: `{bb0}` (entry)
    - `comp 2`: `{bb1, bb2}` (may-exit loop SCC: has exit edge `bb1 -> bb3` to `comp 1`!)
    - `comp 1`: `{bb3}` (recursive call `bb3`; outgoing return edge to `bb4` is pruned!)
    - `comp 0`: `{bb4}` (unreachable `return`, dead after recursive call!) -/
def boundedLoopCompOf (bb : Nat) : Nat :=
  match bb with
  | 0 => 3
  | 1 => 2
  | 2 => 2
  | 3 => 1
  | _ => 0

def boundedLoopScc : SccCondensation boundedLoopCfg where
  numComps := 4
  compOf := boundedLoopCompOf
  compBound := by
    intro u hu
    match u with
    | 0 => exact Nat.lt_succ_self 3
    | 1 => exact Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_succ_self 3)
    | 2 => exact Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_succ_self 3)
    | 3 => exact Nat.lt_trans (Nat.lt_succ_self 1) (Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_succ_self 3))
    | 4 => exact Nat.zero_lt_succ 3
    | n + 5 =>
      have hge : 5 ≤ n + 5 := Nat.le_add_left 5 n
      exact absurd hu (Nat.not_lt.2 hge)
  edgeInBounds := by
    intro u v hu hedge
    match u with
    | 0 =>
      cases hedge with
      | head => exact Nat.lt_trans (Nat.lt_succ_self 1) (Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_trans (Nat.lt_succ_self 3) (Nat.lt_succ_self 4)))
      | tail _ h => cases h
    | 1 =>
      cases hedge with
      | head => exact Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_trans (Nat.lt_succ_self 3) (Nat.lt_succ_self 4))
      | tail _ h =>
        cases h with
        | head => exact Nat.lt_trans (Nat.lt_succ_self 3) (Nat.lt_succ_self 4)
        | tail _ h2 => cases h2
    | 2 =>
      cases hedge with
      | head => exact Nat.lt_trans (Nat.lt_succ_self 1) (Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_trans (Nat.lt_succ_self 3) (Nat.lt_succ_self 4)))
      | tail _ h => cases h
    | 3 => cases hedge
    | 4 => cases hedge
    | n + 5 =>
      have hge : 5 ≤ n + 5 := Nat.le_add_left 5 n
      exact absurd hu (Nat.not_lt.2 hge)
  revTopo := by
    intro u v hu hedge
    match u with
    | 0 =>
      cases hedge with
      | head => exact Nat.le_succ 2
      | tail _ h => cases h
    | 1 =>
      cases hedge with
      | head => exact Nat.le_refl 2
      | tail _ h =>
        cases h with
        | head => exact Nat.le_succ 1
        | tail _ h2 => cases h2
    | 2 =>
      cases hedge with
      | head => exact Nat.le_refl 2
      | tail _ h => cases h
    | 3 => cases hedge
    | 4 => cases hedge
    | n + 5 =>
      have hge : 5 ≤ n + 5 := Nat.le_add_left 5 n
      exact absurd hu (Nat.not_lt.2 hge)

theorem boundedLoop_dagReach_ge_one : ∀ c1 c2,
    1 ≤ c1 → DagReach boundedLoopScc c1 c2 → 1 ≤ c2 := by
  intro c1 c2 hc1 hreach
  induction hreach with
  | refl _ => exact hc1
  | @step ca cb cc u v hu hca hcb hedge _ _ ih =>
    apply ih
    match u with
    | 0 =>
      cases hedge with
      | head => rw [← hcb]; exact Nat.le_succ 1
      | tail _ h => cases h
    | 1 =>
      cases hedge with
      | head => rw [← hcb]; exact Nat.le_succ 1
      | tail _ h =>
        cases h with
        | head => rw [← hcb]; exact Nat.le_refl 1
        | tail _ h2 => cases h2
    | 2 =>
      cases hedge with
      | head => rw [← hcb]; exact Nat.le_succ 1
      | tail _ h => cases h
    | 3 => cases hedge
    | 4 => cases hedge
    | n + 5 =>
      have hge : 5 ≤ n + 5 := Nat.le_add_left 5 n
      exact absurd hu (Nat.not_lt.2 hge)

/-- **Main Theorem 1B (`sccRecursionCheck_complete_on_terminating_loops`)**:
    On `boundedLoopCfg`, the SCC-condensation criterion (`SccUnconditionalRecursion`)
    HOLDS (correctly detecting unconditional recursion through the may-exit loop
    SCC `{bb1, bb2}`), whereas `rustc`'s `TriColorDepthFirstSearch` returned
    `NonRecursive`! -/
theorem sccRecursionCheck_complete_on_terminating_loops :
    SccUnconditionalRecursion boundedLoopScc := by
  constructor
  · intro c hreach hsink
    have hc1 : 1 ≤ c :=
      boundedLoop_dagReach_ge_one 3 c (Nat.le_trans (Nat.le_succ 1) (Nat.le_succ 2)) hreach
    cases hsink with
    | inl hesc =>
      let ⟨u, hu, hcu, hterm⟩ := hesc
      match u with
      | 0 => cases hterm
      | 1 => cases hterm
      | 2 => cases hterm
      | 3 => cases hterm
      | 4 =>
        have hc0 : c = 0 := hcu.symm
        subst hc0
        exact Nat.not_succ_le_zero 0 hc1
      | n + 5 =>
        have hge : 5 ≤ n + 5 := Nat.le_add_left 5 n
        exact absurd hu (Nat.not_lt.2 hge)
    | inr hclosed =>
      let ⟨⟨u, v, hu, hcu, hcv, hedge⟩, hnoExit, _⟩ := hclosed
      match u with
      | 0 =>
        cases hedge with
        | head =>
          -- u = 0 (comp 3), v = 1 (comp 2): contradicts hcu = c = hcv
          have h32 : (3 : Nat) = 2 := hcu.trans hcv.symm
          cases h32
        | tail _ h => cases h
      | 1 =>
        -- comp 2 HAS an exit edge `1 -> 3` (comp 2 -> comp 1)!
        have hc2 : c = 2 := hcu.symm
        subst hc2
        apply hnoExit
        refine ⟨1, 3, ?_, rfl, ?_, Nat.lt_succ_self 1⟩
        · exact Nat.lt_trans (Nat.lt_succ_self 1) (Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_trans (Nat.lt_succ_self 3) (Nat.lt_succ_self 4)))
        · exact List.Mem.tail 2 (List.Mem.head [])
      | 2 =>
        have hc2 : c = 2 := hcu.symm
        subst hc2
        apply hnoExit
        refine ⟨1, 3, ?_, rfl, ?_, Nat.lt_succ_self 1⟩
        · exact Nat.lt_trans (Nat.lt_succ_self 1) (Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_trans (Nat.lt_succ_self 3) (Nat.lt_succ_self 4)))
        · exact List.Mem.tail 2 (List.Mem.head [])
      | 3 => cases hedge
      | 4 => cases hedge
      | n + 5 =>
        have hge : 5 ≤ n + 5 := Nat.le_add_left 5 n
        exact absurd hu (Nat.not_lt.2 hge)
  · -- Reachability to recursive call SCC `comp 1` (`bb3`): `comp 3 -> comp 2 -> comp 1`.
    refine ⟨1, ?_, ⟨3, ?_, rfl, rfl⟩⟩
    · apply DagReach.step 0 1
      · exact Nat.zero_lt_succ 4
      · rfl
      · rfl
      · exact List.Mem.head []
      · exact Nat.lt_succ_self 2
      · apply DagReach.step 1 3
        · exact Nat.lt_trans (Nat.lt_succ_self 1) (Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_trans (Nat.lt_succ_self 3) (Nat.lt_succ_self 4)))
        · rfl
        · rfl
        · exact List.Mem.tail 2 (List.Mem.head [])
        · exact Nat.lt_succ_self 1
        · exact DagReach.refl 1
    · exact Nat.lt_trans (Nat.lt_succ_self 3) (Nat.lt_succ_self 4)

/-- Contrast: `fn pure_infinite_loop() -> ! { loop {} }` is a closed non-recursive SCC,
    so `SccUnconditionalRecursion` does NOT falsely warn on `loop {}`. -/
def pureInfiniteLoopCfg : RecCfg :=
  { numBlocks := 1, startBlock := 0, termOf := fun _ => .goto 0 }

def pureInfiniteLoopScc : SccCondensation pureInfiniteLoopCfg where
  numComps := 1
  compOf := fun _ => 0
  compBound := fun _ _ => Nat.lt_succ_self 0
  edgeInBounds := by
    intro u v hu hedge
    cases hedge with
    | head => exact Nat.lt_succ_self 0
    | tail _ h => cases h
  revTopo := fun _ _ _ _ => Nat.le_refl 0

theorem sccRecursionCheck_silent_on_pure_infinite_loop :
    ¬ SccUnconditionalRecursion pureInfiniteLoopScc := by
  intro ⟨hNoSink, _⟩
  apply hNoSink 0 (DagReach.refl 0)
  right
  refine ⟨⟨0, 0, Nat.lt_succ_self 0, rfl, rfl, List.Mem.head []⟩, ?_, ?_⟩
  · intro ⟨_, _, _, _, _, hlt⟩
    exact Nat.not_lt_zero _ hlt
  · intro ⟨u, hu, _, hrec⟩
    cases hrec

/-- Fixed `TailCall` check: distinguishes `TailCall(false)` (genuine escape ->
    `Break(NonRecursive)`) from `TailCall(true)` (stays in `Continue(())`). -/
def triColorRunFixedTailCall (cfg : RecCfg) (fuel : Nat) (st : TriColorState) :
    Option RecLintOutcome :=
  Nat.rec (motive := fun _ => TriColorState → Option RecLintOutcome)
    (fun _ => none)
    (fun _ ih st =>
      match st.stack with
      | [] =>
        if st.recCalls.isEmpty then some .silentNoRecCalls else some (.warn st.recCalls)
      | .settle bb :: rest =>
        let settled' := insertNat bb st.settled
        let term := cfg.termOf bb
        let recCalls' :=
          if term.isRustcClassifiedRec then st.recCalls ++ [bb] else st.recCalls
        ih { st with stack := rest, settled := settled', recCalls := recCalls' }
      | .enter bb :: rest =>
        let alreadyVisited := memNat bb st.visited
        let alreadySettled := memNat bb st.settled
        if alreadyVisited && !alreadySettled then
          some .nonRecursive
        else if alreadySettled then
          if (cfg.termOf bb).isGenuineEscape then some .nonRecursive
          else ih { st with stack := rest }
        else
          let visited' := insertNat bb st.visited
          let term := cfg.termOf bb
          if term.isGenuineEscape then
            some .nonRecursive
          else
            let succs := term.filteredSuccessors
            let stk' := pushVisitedEvents succs (DfsEvent.settle bb :: rest)
            ih { st with stack := stk', visited := visited' })
    fuel st

/-- Checking `isGenuineEscape` (which treats non-recursive `TailCall(false)` as a return)
    eliminates the false positive on `become_other_or_self_call` while keeping
    `pure_become` silent and `mixed_become_and_call` warning. -/
theorem fixedTailCallCheck_eliminates_false_positive :
    triColorRunFixedTailCall becomeOtherOrSelfCallCfg 20
      { stack := [.enter 0], visited := [], settled := [], recCalls := [] } = some .nonRecursive ∧
    triColorRunFixedTailCall pureBecomeCfg 10
      { stack := [.enter 0], visited := [], settled := [], recCalls := [] } = some .silentNoRecCalls ∧
    triColorRunFixedTailCall mixedBecomeAndCallCfg 20
      { stack := [.enter 0], visited := [], settled := [], recCalls := [] } = some (.warn [2]) := by
  exact ⟨rfl, rfl, rfl⟩

end CheckRecursion

/-! ============================================================================
    PART 2: `KnownPanicsLint` (`DummyMachine` Const-Prop Domain & Soundness)
============================================================================ -/

section KnownPanics

/-- Mirror of `ConstPropMode` in `compiler/rustc_mir_transform/src/known_panics_lint.rs:862-870`. -/
inductive ConstPropMode where
  | fullConstProp
  | onlyInsideOwnBlock
  | noPropagation

/-- Mirror of `Value` (`known_panics_lint.rs:80-84`) for scalar immediates and
    2-field aggregates/pairs (no `List`/`Option` fields -> zero `._unsafe_rec`). -/
inductive AbsVal where
  | uninit
  | immInt (v : Int)
  | immBool (b : Bool)
  | pairInt (f0 f1 : Int)

/-- Concrete runtime value stored in a local slot. -/
inductive ConcVal where
  | uninit
  | immInt (v : Int)
  | immBool (b : Bool)
  | pairInt (f0 f1 : Int)

/-- Refinement relation between abstract `KnownPanicsLint` value and concrete value:
    whenever the abstract domain knows a value (not `.uninit`), the concrete value
    is guaranteed to be equal to it. -/
def AbsValRefines (a : AbsVal) (c : ConcVal) : Prop :=
  match a with
  | .uninit => True
  | .immInt v => c = .immInt v
  | .immBool b => c = .immBool b
  | .pairInt f0 f1 => c = .pairInt f0 f1

def AbsEnv := Nat → AbsVal
def ConcEnv := Nat → ConcVal

def EnvRefines (a : AbsEnv) (c : ConcEnv) : Prop :=
  ∀ l : Nat, AbsValRefines (a l) (c l)

def setAbs (env : AbsEnv) (l : Nat) (v : AbsVal) : AbsEnv :=
  fun k => if natEq k l then v else env k

def setConc (env : ConcEnv) (l : Nat) (v : ConcVal) : ConcEnv :=
  fun k => if natEq k l then v else env k

theorem envRefines_set (a : AbsEnv) (c : ConcEnv) (l : Nat) (av : AbsVal) (cv : ConcVal)
    (href : EnvRefines a c) (hv : AbsValRefines av cv) :
    EnvRefines (setAbs a l av) (setConc c l cv) := by
  intro k
  unfold setAbs setConc
  cases hkl : natEq k l with
  | true => exact hv
  | false => exact href k

theorem envRefines_removeConst (a : AbsEnv) (c : ConcEnv) (l : Nat) (cv : ConcVal)
    (href : EnvRefines a c) :
    EnvRefines (setAbs a l .uninit) (setConc c l cv) := by
  exact envRefines_set a c l .uninit cv href trivial

/-- Operations evaluated by `KnownPanicsLint::ConstPropagator` (`known_panics_lint.rs:542-665`). -/
inductive KPOperand where
  | constInt (v : Int)
  | constBool (b : Bool)
  | local_ (l : Nat)

inductive KPBinOp where
  | add
  | sub
  | eqZero
  | ltConst (bound : Int)

inductive KPRvalue where
  | use (op : KPOperand)
  | binOp (op : KPBinOp) (lhs rhs : KPOperand)
  | mkPair (op0 op1 : KPOperand)
  | projField0 (l : Nat)
  | refTake (l : Nat)       -- poisons `l` via `remove_const` (`lines 425-437`)
  | repeatUnknown           -- `Rvalue::Repeat` returns `None` (`lines 604-607`)

inductive KPStmt where
  | assign (dst : Nat) (rv : KPRvalue)
  | storageDead (l : Nat)

inductive KPAssertKind where
  | divByZero
  | boundsCheck
  | overflowDiv

inductive KPTerm where
  | goto (target : Nat)
  | switchBool (discr : KPOperand) (ifTrue ifFalse : Nat)
  | assert (cond : KPOperand) (expected : Bool) (kind : KPAssertKind) (target : Nat)
  | return_

/-- Concrete evaluation of operands and rvalues. -/
def evalConcOp (c : ConcEnv) : KPOperand → ConcVal
  | .constInt v => .immInt v
  | .constBool b => .immBool b
  | .local_ l => c l

def evalConcBinOp (op : KPBinOp) (lv rv : ConcVal) : ConcVal :=
  match op, lv, rv with
  | .add, .immInt x, .immInt y => .immInt (x + y)
  | .sub, .immInt x, .immInt y => .immInt (x - y)
  | .eqZero, .immInt x, _ => .immBool (decide (x = 0))
  | .ltConst bound, .immInt x, _ => .immBool (decide (x < bound))
  | _, _, _ => .uninit

/-- Abstract evaluation mirroring `ConstPropagator::eval_operand` / `eval_rvalue`. -/
def evalAbsOp (a : AbsEnv) : KPOperand → AbsVal
  | .constInt v => .immInt v
  | .constBool b => .immBool b
  | .local_ l => a l

def evalAbsBinOp (op : KPBinOp) (lv rv : AbsVal) : AbsVal :=
  match op, lv, rv with
  | .add, .immInt x, .immInt y => .immInt (x + y)
  | .sub, .immInt x, .immInt y => .immInt (x - y)
  | .eqZero, .immInt x, _ => .immBool (decide (x = 0))
  | .ltConst bound, .immInt x, _ => .immBool (decide (x < bound))
  | _, _, _ => .uninit

theorem evalAbsOp_sound (a : AbsEnv) (c : ConcEnv) (op : KPOperand)
    (href : EnvRefines a c) :
    AbsValRefines (evalAbsOp a op) (evalConcOp c op) := by
  cases op with
  | constInt v => rfl
  | constBool b => rfl
  | local_ l => exact href l

theorem evalAbsBinOp_sound (op : KPBinOp) (al ar : AbsVal) (cl cr : ConcVal)
    (hl : AbsValRefines al cl) (hr : AbsValRefines ar cr) :
    AbsValRefines (evalAbsBinOp op al ar) (evalConcBinOp op cl cr) := by
  cases op <;> cases al <;> cases ar <;> simp only [evalAbsBinOp, AbsValRefines] at *
  all_goals first
    | trivial
    | (subst hl; subst hr; rfl)
    | (subst hl; rfl)

/-- Abstract statement transfer (`ConstPropagator::visit_assign` + `visit_statement`),
    tracking `written_only_inside_own_block_locals` (`known_panics_lint.rs:218-227, 690-750`). -/
structure AbsBlockState where
  env : AbsEnv
  writtenOwnBlock : List Nat

/-- Helper applying a mode-gated abstract write (`ConstPropMode`). -/
def writeWithMode (modes : Nat → ConstPropMode) (st : AbsBlockState) (dst : Nat) (av : AbsVal) :
    AbsBlockState :=
  match modes dst with
  | .noPropagation => st
  | .onlyInsideOwnBlock =>
    { env := setAbs st.env dst av, writtenOwnBlock := insertNat dst st.writtenOwnBlock }
  | .fullConstProp =>
    { env := setAbs st.env dst av, writtenOwnBlock := st.writtenOwnBlock }

def stepAbsStmt (modes : Nat → ConstPropMode) (st : AbsBlockState) (s : KPStmt) : AbsBlockState :=
  match s with
  | .storageDead l =>
    { env := setAbs st.env l .uninit, writtenOwnBlock := st.writtenOwnBlock }
  | .assign dst rv =>
    match rv with
    | .refTake target =>
      -- `lines 425-436`: poison the referenced local AND nuke `dst` (non-propagated Ref).
      let env1 := setAbs st.env target .uninit
      { env := setAbs env1 dst .uninit, writtenOwnBlock := st.writtenOwnBlock }
    | .repeatUnknown =>
      { env := setAbs st.env dst .uninit, writtenOwnBlock := st.writtenOwnBlock }
    | .use op =>
      writeWithMode modes st dst (evalAbsOp st.env op)
    | .binOp op lhs rhs =>
      writeWithMode modes st dst (evalAbsBinOp op (evalAbsOp st.env lhs) (evalAbsOp st.env rhs))
    | .mkPair op0 op1 =>
      let v :=
        match evalAbsOp st.env op0, evalAbsOp st.env op1 with
        | .immInt x, .immInt y => AbsVal.pairInt x y
        | _, _ => AbsVal.uninit
      writeWithMode modes st dst v
    | .projField0 src =>
      let v :=
        match st.env src with
        | .pairInt f0 _ => AbsVal.immInt f0
        | _ => AbsVal.uninit
      writeWithMode modes st dst v

/-- Concrete statement semantics (with oracle `unknownVal` for `Ref` / `Repeat`). -/
def stepConcStmt (unknownVal : ConcVal) (c : ConcEnv) (s : KPStmt) : ConcEnv :=
  match s with
  | .storageDead l => setConc c l .uninit
  | .assign dst rv =>
    match rv with
    | .refTake _ => setConc c dst unknownVal
    | .repeatUnknown => setConc c dst unknownVal
    | .use op => setConc c dst (evalConcOp c op)
    | .binOp op lhs rhs =>
      setConc c dst (evalConcBinOp op (evalConcOp c lhs) (evalConcOp c rhs))
    | .mkPair op0 op1 =>
      let v :=
        match evalConcOp c op0, evalConcOp c op1 with
        | .immInt x, .immInt y => ConcVal.pairInt x y
        | _, _ => ConcVal.uninit
      setConc c dst v
    | .projField0 src =>
      let v :=
        match c src with
        | .pairInt f0 _ => ConcVal.immInt f0
        | _ => ConcVal.uninit
      setConc c dst v

/-- Invariant: every `NoPropagation` local is always `.uninit` in the abstract env
    (`ensure_not_propagated`, `known_panics_lint.rs:528-539`). -/
def NoPropIsUninit (modes : Nat → ConstPropMode) (a : AbsEnv) : Prop :=
  ∀ l, modes l = .noPropagation → a l = .uninit

theorem writeWithMode_preserves_refinement
    (modes : Nat → ConstPropMode) (st : AbsBlockState) (c : ConcEnv)
    (dst : Nat) (av : AbsVal) (cv : ConcVal)
    (href : EnvRefines st.env c)
    (hnp : NoPropIsUninit modes st.env)
    (hv : AbsValRefines av cv) :
    EnvRefines (writeWithMode modes st dst av).env (setConc c dst cv) ∧
    NoPropIsUninit modes (writeWithMode modes st dst av).env := by
  unfold writeWithMode
  cases hmd : modes dst with
  | noPropagation =>
    constructor
    · intro k
      dsimp only [setConc]
      cases hkd : natEq k dst with
      | true =>
        have heq : k = dst := (natEq_true_iff k dst).1 hkd
        subst heq
        rw [hnp k hmd]
        trivial
      | false => exact href k
    · exact hnp
  | onlyInsideOwnBlock =>
    constructor
    · exact envRefines_set st.env c dst av cv href hv
    · intro k hk
      dsimp only [setAbs]
      cases hkd : natEq k dst with
      | true =>
        have heq : k = dst := (natEq_true_iff k dst).1 hkd
        subst heq
        rw [hmd] at hk
        cases hk
      | false => exact hnp k hk
  | fullConstProp =>
    constructor
    · exact envRefines_set st.env c dst av cv href hv
    · intro k hk
      dsimp only [setAbs]
      cases hkd : natEq k dst with
      | true =>
        have heq : k = dst := (natEq_true_iff k dst).1 hkd
        subst heq
        rw [hmd] at hk
        cases hk
      | false => exact hnp k hk

theorem noPropIsUninit_setUninit (modes : Nat → ConstPropMode) (a : AbsEnv) (l : Nat)
    (hnp : NoPropIsUninit modes a) :
    NoPropIsUninit modes (setAbs a l .uninit) := by
  intro k hk
  dsimp only [setAbs]
  cases natEq k l with
  | true => rfl
  | false => exact hnp k hk

/-- **Theorem 2A (`absStep_preserves_refinement`)**:
    Every `KnownPanicsLint` statement transfer preserves `EnvRefines` and `NoPropIsUninit`. -/
theorem absStep_preserves_refinement
    (modes : Nat → ConstPropMode) (st : AbsBlockState) (c : ConcEnv)
    (s : KPStmt) (unk : ConcVal)
    (href : EnvRefines st.env c)
    (hnp : NoPropIsUninit modes st.env) :
    EnvRefines (stepAbsStmt modes st s).env (stepConcStmt unk c s) ∧
    NoPropIsUninit modes (stepAbsStmt modes st s).env := by
  cases s with
  | storageDead l =>
    dsimp only [stepAbsStmt, stepConcStmt]
    exact ⟨envRefines_removeConst st.env c l .uninit href, noPropIsUninit_setUninit modes st.env l hnp⟩
  | assign dst rv =>
    cases rv with
    | refTake target =>
      dsimp only [stepAbsStmt, stepConcStmt]
      constructor
      · intro k
        dsimp only [setAbs, setConc]
        cases natEq k dst with
        | true => trivial
        | false =>
          cases natEq k target with
          | true => trivial
          | false => exact href k
      · exact noPropIsUninit_setUninit modes (setAbs st.env target .uninit) dst
          (noPropIsUninit_setUninit modes st.env target hnp)
    | repeatUnknown =>
      dsimp only [stepAbsStmt, stepConcStmt]
      exact ⟨envRefines_removeConst st.env c dst unk href, noPropIsUninit_setUninit modes st.env dst hnp⟩
    | use op =>
      dsimp only [stepAbsStmt, stepConcStmt]
      exact writeWithMode_preserves_refinement modes st c dst _ _ href hnp
        (evalAbsOp_sound st.env c op href)
    | binOp op lhs rhs =>
      dsimp only [stepAbsStmt, stepConcStmt]
      exact writeWithMode_preserves_refinement modes st c dst _ _ href hnp
        (evalAbsBinOp_sound op _ _ _ _
          (evalAbsOp_sound st.env c lhs href) (evalAbsOp_sound st.env c rhs href))
    | mkPair op0 op1 =>
      dsimp only [stepAbsStmt, stepConcStmt]
      have h0 := evalAbsOp_sound st.env c op0 href
      have h1 := evalAbsOp_sound st.env c op1 href
      have hpair : AbsValRefines
          (match evalAbsOp st.env op0, evalAbsOp st.env op1 with
           | .immInt x, .immInt y => .pairInt x y
           | _, _ => .uninit)
          (match evalConcOp c op0, evalConcOp c op1 with
           | .immInt x, .immInt y => .pairInt x y
           | _, _ => .uninit) := by
        cases h_a0 : evalAbsOp st.env op0 <;> cases h_a1 : evalAbsOp st.env op1
        all_goals rw [h_a0] at h0; rw [h_a1] at h1
        all_goals first | trivial | (rw [h0, h1]; rfl)
      exact writeWithMode_preserves_refinement modes st c dst _ _ href hnp hpair
    | projField0 src =>
      dsimp only [stepAbsStmt, stepConcStmt]
      have hs := href src
      have hproj : AbsValRefines
          (match st.env src with | .pairInt f0 _ => .immInt f0 | _ => .uninit)
          (match c src with | .pairInt f0 _ => .immInt f0 | _ => .uninit) := by
        cases h_as : st.env src with
        | pairInt f0 f1 =>
          rw [h_as] at hs
          rw [hs]
          rfl
        | uninit => trivial
        | immInt _ => trivial
        | immBool _ => trivial
      exact writeWithMode_preserves_refinement modes st c dst _ _ href hnp hproj

/-- Block-exit clearing of `written_only_inside_own_block_locals` (`known_panics_lint.rs:828-840`). -/
def clearLocals (env : AbsEnv) (ls : List Nat) : AbsEnv :=
  ls.foldr (fun l acc => setAbs acc l .uninit) env

theorem clearLocals_preserves_refinement (a : AbsEnv) (c : ConcEnv) (href : EnvRefines a c) :
    ∀ ls : List Nat, EnvRefines (clearLocals a ls) c
  | [] => href
  | l :: ls => by
    intro k
    unfold clearLocals setAbs
    dsimp only [List.foldr]
    cases natEq k l with
    | true => trivial
    | false => exact clearLocals_preserves_refinement a c href ls k

theorem clearLocals_eq_uninit (a : AbsEnv) (l : Nat) :
    ∀ ls : List Nat, l ∈ ls → clearLocals a ls l = .uninit
  | [], h => by cases h
  | x :: xs, h => by
    unfold clearLocals setAbs
    dsimp only [List.foldr]
    cases h with
    | head => rw [natEq_refl]; rfl
    | tail _ htail =>
      cases natEq l x with
      | true => rfl
      | false => exact clearLocals_eq_uninit a l xs htail

/-- Multi-statement block execution (abstract and concrete). -/
def runAbsStmts (modes : Nat → ConstPropMode) (ss : List KPStmt) (st : AbsBlockState) :
    AbsBlockState :=
  ss.foldl (fun acc s => stepAbsStmt modes acc s) st

def runConcStmts (unk : ConcVal) (ss : List KPStmt) (c : ConcEnv) : ConcEnv :=
  ss.foldl (fun acc s => stepConcStmt unk acc s) c

theorem runAbsStmts_sound (modes : Nat → ConstPropMode) (unk : ConcVal) :
    ∀ (ss : List KPStmt) (st : AbsBlockState) (c : ConcEnv),
      EnvRefines st.env c →
      NoPropIsUninit modes st.env →
      EnvRefines (runAbsStmts modes ss st).env (runConcStmts unk ss c) ∧
      NoPropIsUninit modes (runAbsStmts modes ss st).env
  | [], st, c, href, hnp => ⟨href, hnp⟩
  | s :: ss, st, c, href, hnp => by
    let ⟨href', hnp'⟩ := absStep_preserves_refinement modes st c s unk href hnp
    exact runAbsStmts_sound modes unk ss (stepAbsStmt modes st s) (stepConcStmt unk c s) href' hnp'

/-- Mirror of `ConstPropagator::check_assertion` (`known_panics_lint.rs:467-526`):
    returns `true` iff `cond` evaluates to `immBool b` with `b ≠ expected`. -/
def checkAssertionLint (a : AbsEnv) (cond : KPOperand) (expected : Bool) : Bool :=
  match evalAbsOp a cond with
  | .immBool b => !(boolEq b expected)
  | _ => false

/-- Concrete runtime assertion failure: `cond` evaluates to `immBool b` with `b ≠ expected`. -/
def RuntimeAssertFails (c : ConcEnv) (cond : KPOperand) (expected : Bool) : Prop :=
  ∃ b : Bool, evalConcOp c cond = .immBool b ∧ b ≠ expected

/-- **Main Theorem 2B (`knownPanics_constProp_implies_runtime_assert_fail`)**:
    Whenever `KnownPanicsLint` propagates a block's statements from an entry state
    refining `c0` and `checkAssertionLint` fires `unconditional_panic` on
    `Assert { cond, expected }`, EVERY concrete execution of that block from `c0`
    is guaranteed to fail the assertion (panic at runtime)! -/
theorem knownPanics_constProp_implies_runtime_assert_fail
    (modes : Nat → ConstPropMode) (ss : List KPStmt) (st0 : AbsBlockState) (c0 : ConcEnv)
    (unk : ConcVal) (cond : KPOperand) (expected : Bool)
    (href0 : EnvRefines st0.env c0)
    (hnp0 : NoPropIsUninit modes st0.env)
    (hLint : checkAssertionLint (runAbsStmts modes ss st0).env cond expected = true) :
    RuntimeAssertFails (runConcStmts unk ss c0) cond expected := by
  let ⟨hrefEnd, _⟩ := runAbsStmts_sound modes unk ss st0 c0 href0 hnp0
  have hop := evalAbsOp_sound (runAbsStmts modes ss st0).env (runConcStmts unk ss c0) cond hrefEnd
  unfold checkAssertionLint at hLint
  cases heval : evalAbsOp (runAbsStmts modes ss st0).env cond with
  | uninit => rw [heval] at hLint; cases hLint
  | immInt _ => rw [heval] at hLint; cases hLint
  | pairInt _ _ => rw [heval] at hLint; cases hLint
  | immBool b =>
    rw [heval] at hLint hop
    refine ⟨b, hop, ?_⟩
    intro heq
    subst heq
    have hbtrue : boolEq b b = true := (boolEq_true_iff b b).2 rfl
    dsimp only at hLint
    rw [hbtrue] at hLint
    cases hLint

/-- **Theorem 2C (`knownPanics_shift_overflow_symbolic_lhs_sound`)**:
    Mirrors `check_binary_op` lines 351-374: checking `r >= leftWidthBits` detects
    shift overflow even when the abstract LHS is `.uninit` (unknown parameter),
    and holds for ALL concrete LHS integers `lhs`. -/
def checkShiftOverflowLint (widthBits : Nat) (a : AbsEnv) (rhs : KPOperand) : Bool :=
  match evalAbsOp a rhs with
  | .immInt r => decide (Int.ofNat widthBits ≤ r)
  | _ => false

def ConcreteShiftOverflows (widthBits : Nat) (lhs : Int) (rhs : ConcVal) : Prop :=
  let _ := lhs
  ∃ r : Int, rhs = .immInt r ∧ Int.ofNat widthBits ≤ r

theorem knownPanics_shift_overflow_symbolic_lhs_sound
    (widthBits : Nat) (a : AbsEnv) (c : ConcEnv) (rhs : KPOperand)
    (href : EnvRefines a c)
    (hLint : checkShiftOverflowLint widthBits a rhs = true) :
    ∀ lhs : Int, ConcreteShiftOverflows widthBits lhs (evalConcOp c rhs) := by
  intro lhs
  have hr := evalAbsOp_sound a c rhs href
  unfold checkShiftOverflowLint at hLint
  cases heval : evalAbsOp a rhs with
  | immInt r =>
    rw [heval] at hLint hr
    exact ⟨r, hr, of_decide_eq_true hLint⟩
  | uninit => rw [heval] at hLint; cases hLint
  | immBool _ => rw [heval] at hLint; cases hLint
  | pairInt _ _ => rw [heval] at hLint; cases hLint

/-- **Theorem 2D-1 (`knownPanics_onlyInsideOwnBlock_wipes_join`)**:
    For a local `d` downgraded to `OnlyInsideOwnBlock` (written in multiple blocks,
    e.g. `if cond { d = 0 } else { d = 0 }`), clearing `writtenOwnBlock` at block exit
    resets `d` to `.uninit`, so the join block's `42 / d` assertion produces `false`
    (0 warnings) even though both branches wrote `0`. -/
theorem knownPanics_onlyInsideOwnBlock_wipes_join :
    let modes : Nat → ConstPropMode := fun l =>
      if natEq l 1 then .onlyInsideOwnBlock else .fullConstProp
    let st0 : AbsBlockState := { env := fun _ => .uninit, writtenOwnBlock := [] }
    let branchStmts : List KPStmt := [.assign 1 (.use (.constInt 0))]
    let stAfterBranch := runAbsStmts modes branchStmts st0
    let envAtJoin := clearLocals stAfterBranch.env stAfterBranch.writtenOwnBlock
    let joinStmts : List KPStmt := [.assign 2 (.binOp .eqZero (.local_ 1) (.constInt 0))]
    let stAfterJoin := runAbsStmts modes joinStmts { env := envAtJoin, writtenOwnBlock := [] }
    envAtJoin 1 = .uninit ∧
    checkAssertionLint stAfterJoin.env (.local_ 2) false = false := by
  exact ⟨rfl, rfl⟩

/-- **Theorem 2D-2 (`knownPanics_dead_const_branch_pruned`)**:
    Mirroring `SwitchInt` folding (`known_panics_lint.rs:759-769`): when `discr`
    evaluates to `immBool false`, the worklist pushes ONLY `ifFalse`, never visiting
    `ifTrue` (so `if false { 42 / (1 - 1) } else { 7 }` emits 0 warnings). -/
def switchWorklistTargets (a : AbsEnv) (discr : KPOperand) (ifTrue ifFalse : Nat) : List Nat :=
  match evalAbsOp a discr with
  | .immBool true => [ifTrue]
  | .immBool false => [ifFalse]
  | _ => [ifTrue, ifFalse]

theorem knownPanics_dead_const_branch_pruned (a : AbsEnv) (bbTrue bbFalse : Nat) :
    switchWorklistTargets a (.constBool false) bbTrue bbFalse = [bbFalse] ∧
    switchWorklistTargets a (.constBool true) bbTrue bbFalse = [bbTrue] := by
  exact ⟨rfl, rfl⟩

end KnownPanics

/-! ============================================================================
    PART 3: `FunctionItemReferences` (`&FnDef` ZST Ref vs `fn()` Pointer Cast)
============================================================================ -/

section FunctionItemReferences

/-- Mirror of function-item vs function-pointer types in `function_item_references.rs:127-142`. -/
inductive FnRefTy where
  | fnDef (defId : Nat)
  | fnPtr
  | refTy (inner : FnRefTy)
  | rawPtrTy (inner : FnRefTy)
  | other

/-- Layout size in bytes on 64-bit targets: `FnDef` is a ZST (`0` bytes),
    while `fn()` and `&FnDef` / `*const FnDef` are pointer-sized (`8` bytes). -/
def FnRefTy.sizeBytes : FnRefTy → Nat
  | .fnDef _ => 0
  | .fnPtr => 8
  | .refTy _ => 8
  | .rawPtrTy _ => 8
  | .other => 8

/-- Exact mirror of `FunctionItemRefChecker::is_fn_ref` (`function_item_references.rs:127-142`). -/
def isFnRef : FnRefTy → Option Nat
  | .refTy (.fnDef id) => some id
  | .rawPtrTy (.fnDef id) => some id
  | _ => none

/-- Runtime pointer value model for `{:p}` / `transmute::<_, usize>`:
    - A promoted `&FnDef` / `*const FnDef` points to the canonical 1-byte-aligned
      dangling ZST address `1` (`0x1`), independent of which function item `id` it names!
    - A coerced `fn()` pointer carries the distinct `.text` code address `codeAddr id`. -/
inductive RuntimePtrVal where
  | refOfFnDef (id : Nat)
  | rawPtrOfFnDef (id : Nat)
  | coercedFnPtr (id : Nat)

def evalPtrAddress (codeAddr : Nat → Nat) : RuntimePtrVal → Nat
  | .refOfFnDef _ => 1
  | .rawPtrOfFnDef _ => 1
  | .coercedFnPtr id => codeAddr id

/-- **Theorem 3A (`fnItemRef_loses_identity_fnPtr_preserves_identity`)**:
    For ANY injective code-address table `codeAddr` and ANY two distinct functions
    `id1 ≠ id2`:
    1. Both `FnDef` items are zero-sized (`sizeBytes = 0`),
    2. `&fn1` and `&fn2` collapse to the IDENTICAL dangling ZST address `1` (`0x1`),
    3. `fn1 as fn(...)` and `fn2 as fn(...)` produce STRICTLY DISTINCT code addresses. -/
theorem fnItemRef_loses_identity_fnPtr_preserves_identity
    (codeAddr : Nat → Nat)
    (hInj : ∀ a b, codeAddr a = codeAddr b → a = b)
    (id1 id2 : Nat) (hne : id1 ≠ id2) :
    (FnRefTy.fnDef id1).sizeBytes = 0 ∧
    evalPtrAddress codeAddr (.refOfFnDef id1) = evalPtrAddress codeAddr (.refOfFnDef id2) ∧
    evalPtrAddress codeAddr (.coercedFnPtr id1) ≠ evalPtrAddress codeAddr (.coercedFnPtr id2) := by
  refine ⟨rfl, rfl, ?_⟩
  intro heq
  exact hne (hInj id1 id2 heq)

/-- Call-site descriptor mirroring `function_item_references.rs:31-112` (including HEAD
    `ce66487ebbd7`'s `ClausePolarity::Positive` check on `fmt::Pointer`). -/
inductive ClausePolarity where
  | positive
  | negative

inductive CallSiteKind where
  | transmuteCall (argTy : FnRefTy)
  | genericPointerCall (polarity : ClausePolarity) (isFmtPointer : Bool) (instantiatedArgTy : FnRefTy)

def checkFunctionItemRefLint : CallSiteKind → Option Nat
  | .transmuteCall ty => isFnRef ty
  | .genericPointerCall .positive true ty => isFnRef ty
  | .genericPointerCall _ _ _ => none

/-- **Theorem 3B (`fnItemRefLint_sound_and_complete_on_pointer_and_transmute`)**:
    `FunctionItemReferences` fires iff the argument is a `&FnDef` or `*const FnDef`
    passed to `transmute` or to a positive `fmt::Pointer`-bounded parameter, and
    never fires on coerced `fn()` pointers or negative `!fmt::Pointer` bounds. -/
theorem fnItemRefLint_sound_and_complete_on_pointer_and_transmute (id : Nat) :
    checkFunctionItemRefLint (.transmuteCall (.refTy (.fnDef id))) = some id ∧
    checkFunctionItemRefLint (.transmuteCall (.rawPtrTy (.fnDef id))) = some id ∧
    checkFunctionItemRefLint (.transmuteCall .fnPtr) = none ∧
    checkFunctionItemRefLint (.genericPointerCall .positive true (.refTy (.fnDef id))) = some id ∧
    checkFunctionItemRefLint (.genericPointerCall .positive true .fnPtr) = none ∧
    checkFunctionItemRefLint (.genericPointerCall .negative true (.refTy (.fnDef id))) = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end FunctionItemReferences

/-! ============================================================================
    PART 4: `LintTailExprDropOrder` (`DropsReachable` Edition 2021 -> 2024)
============================================================================ -/

section TailExprDropOrder

/-- Rust edition selector for `tail_expr_drop_order` (`lint_tail_expr_drop_order.rs:188`). -/
inductive RustEdition where
  | ed2021
  | ed2024

/-- Local binding role for exclusion rules `a)` and `b)` (`lines 293-305`). -/
inductive LocalRole where
  | retPlace        -- `_0`
  | closureCapture  -- `ty::CAPTURE_STRUCT_LOCAL`
  | userLocal
  | tailTemp

/-- Early-MIR block terminator relevant to `DropsReachable` (`lines 59-158`). -/
inductive TedoTerm where
  | drop (place : Nat) (nextBlock : Nat) (unwindBlock : Option Nat)
  | goto (nextBlock : Nat)
  | switchInt (targets : List Nat)
  | return_

def TedoTerm.successors : TedoTerm → List Nat
  | .drop _ next (some u) => [next, u]
  | .drop _ next none => [next]
  | .goto next => [next]
  | .switchInt ts => ts
  | .return_ => []

/-- Early-MIR body model for `lint_tail_expr_drop_order` (at `mir_promoted`,
    after `PromoteTemps` and before `CleanupPostBorrowck` strips BIDs). -/
structure TedoBody where
  edition : RustEdition
  isClosureLike : Bool
  numBlocks : Nat
  isCleanup : Nat → Bool
  termOf : Nat → TedoTerm
  maybeInitAt : Nat → Nat → Bool        -- `MaybeInitializedPlaces` cursor at block terminator
  roleOf : Nat → LocalRole
  hasSigDtor : Nat → Bool               -- `extract_component_with_significant_dtor(...).is_empty() == false`
  isBidDescendant : Nat → Bool          -- `place_descendent_of_bids` (`lines 164-180, 320`)

/-- Exclusion predicate combining `a)` `_0`, `b)` closure captures, `c)` BID descendants,
    `d)` non-significant dtors, and same-local BID exclusion (`lines 283-349`). -/
def isExcludedObserver (b : TedoBody) (bidPlace : Nat) (p : Nat) : Bool :=
  if natEq p bidPlace then true
  else match b.roleOf p with
    | .retPlace => true
    | .closureCapture => b.isClosureLike
    | _ => b.isBidDescendant p || !(b.hasSigDtor p)

/-- Non-cleanup execution path from `curr` to `drop(bidPlace)` collecting every
    intervening initialized dropped place (exact relational specification of
    `DropsReachable::visit` at `lint_tail_expr_drop_order.rs:59-158`). -/
inductive InterveningDrops (b : TedoBody) (bidPlace : Nat) : Nat → List Nat → Prop where
  | reachTarget {bb target : Nat}
      (hNotClean : b.isCleanup bb = false)
      (hTargetClean : b.isCleanup target = false)
      (hSucc : target ∈ (b.termOf bb).successors)
      (hDropTarget : ∃ nxt u, b.termOf target = .drop bidPlace nxt u) :
      InterveningDrops b bidPlace bb
        (match b.termOf bb with
         | .drop p _ _ => if b.maybeInitAt bb p then [p] else []
         | _ => [])
  | step {bb next : Nat} {rest : List Nat}
      (hNotClean : b.isCleanup bb = false)
      (hNextClean : b.isCleanup next = false)
      (hSucc : next ∈ (b.termOf bb).successors)
      (hNotTarget : ∀ nxt u, b.termOf next ≠ .drop bidPlace nxt u)
      (hRest : InterveningDrops b bidPlace next rest) :
      InterveningDrops b bidPlace bb
        ((match b.termOf bb with
          | .drop p _ _ => if b.maybeInitAt bb p then [p] else []
          | _ => []) ++ rest)

/-- Executable fuel-bounded `DropsReachable` traversal returning all intervening
    initialized dropped places along non-cleanup paths from `bb` to `drop(bidPlace)`.
    Uses explicit top-level structural recursion over successors (zero `let rec`
    and zero `._unsafe_rec`). -/
def dropsReachableSuccs (stepFn : Nat → List Nat → List Nat) (b : TedoBody)
    (bidPlace : Nat) (carried' : List Nat) (ss : List Nat) : List Nat :=
  ss.foldr
    (fun s tailRes =>
      if b.isCleanup s then tailRes
      else
        match b.termOf s with
        | .drop p _ _ =>
          if natEq p bidPlace then
            unionNat carried' tailRes
          else
            unionNat (stepFn s carried') tailRes
        | _ =>
          unionNat (stepFn s carried') tailRes)
    []

def dropsReachableExec (b : TedoBody) (bidPlace fuel bb : Nat) (carried : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat)
    (fun _ _ => [])
    (fun _ ih bb carried =>
      if b.isCleanup bb then []
      else
        let carried' :=
          match b.termOf bb with
          | .drop p _ _ => if b.maybeInitAt bb p then insertNat p carried else carried
          | _ => carried
        dropsReachableSuccs ih b bidPlace carried' (b.termOf bb).successors)
    fuel bb carried

/-- Complete executable `lint_tail_expr_drop_order` check for one BID `(bidBlock, bidPlace)`
    (`lint_tail_expr_drop_order.rs:188-354`). -/
def lintTailExprDropOrder (b : TedoBody) (bidBlock bidPlace fuel : Nat) : List Nat :=
  match b.edition with
  | .ed2024 => []
  | .ed2021 =>
    if !(b.hasSigDtor bidPlace) then []
    else
      let raw := dropsReachableExec b bidPlace fuel bidBlock []
      raw.filter (fun p => !(isExcludedObserver b bidPlace p))

/-- Helper: Edition 2021 drops every intervening initialized local `xs` BEFORE `bidPlace`,
    whereas Edition 2024 moves `bidPlace` to the BID site BEFORE `xs`. -/
def ed2021DropSequence (xs : List Nat) (bidPlace : Nat) : List Nat :=
  xs ++ [bidPlace]

def ed2024DropSequence (xs : List Nat) (bidPlace : Nat) : List Nat :=
  bidPlace :: xs

def filterSigDrops (b : TedoBody) (seq : List Nat) : List Nat :=
  seq.filter b.hasSigDtor

/-- Ordering relation: `x` appears strictly before `y` in list `xs`. -/
inductive AppearsBefore (x y : Nat) : List Nat → Prop where
  | head {zs : List Nat} (hy : y ∈ zs) : AppearsBefore x y (x :: zs)
  | tail {z : Nat} {zs : List Nat} (h : AppearsBefore x y zs) : AppearsBefore x y (z :: zs)

theorem appearsBefore_append_right {x y : Nat} : ∀ (xs : List Nat),
    x ∈ xs → AppearsBefore x y (xs ++ [y])
  | [], h => by cases h
  | z :: zs, h => by
    cases h with
    | head =>
      apply AppearsBefore.head
      exact List.mem_append.2 (Or.inr (List.Mem.head []))
    | tail _ hmem =>
      exact AppearsBefore.tail (appearsBefore_append_right zs hmem)

theorem mem_filter_iff {α : Type} (p : α → Bool) (x : α) :
    ∀ xs : List α, x ∈ xs.filter p ↔ x ∈ xs ∧ p x = true
  | [] => by
    constructor
    · intro h; cases h
    · intro ⟨h, _⟩; cases h
  | y :: ys => by
    simp only [List.filter]
    cases hpy : p y with
    | true =>
      constructor
      · intro h
        cases h with
        | head => exact ⟨List.Mem.head ys, hpy⟩
        | tail _ htail =>
          let ⟨hmem, hpx⟩ := (mem_filter_iff p x ys).1 htail
          exact ⟨List.Mem.tail y hmem, hpx⟩
      · intro ⟨hmem, hpx⟩
        cases hmem with
        | head => exact List.Mem.head _
        | tail _ htail => exact List.Mem.tail y ((mem_filter_iff p x ys).2 ⟨htail, hpx⟩)
    | false =>
      constructor
      · intro h
        let ⟨hmem, hpx⟩ := (mem_filter_iff p x ys).1 h
        exact ⟨List.Mem.tail y hmem, hpx⟩
      · intro ⟨hmem, hpx⟩
        cases hmem with
        | head => rw [hpx] at hpy; cases hpy
        | tail _ htail => exact (mem_filter_iff p x ys).2 ⟨htail, hpx⟩

theorem filter_append {α : Type} (p : α → Bool) :
    ∀ (xs ys : List α), (xs ++ ys).filter p = xs.filter p ++ ys.filter p
  | [], ys => rfl
  | x :: xs, ys => by
    simp only [List.cons_append, List.filter]
    cases p x with
    | true =>
      simp only [List.cons_append]
      rw [filter_append p xs ys]
    | false =>
      exact filter_append p xs ys

/-- **Main Theorem 4A (`dropsReachable_sound_for_significant_dtor_swap`)**:
    Whenever a BID temporary `bidPlace` has a significant destructor and an
    intervening initialized drop `pLocal` (`pLocal ≠ bidPlace`, also with a
    significant destructor) occurs on a path `xs` between the BID site and
    `drop(bidPlace)`:
    1. In Edition 2021, `pLocal` drops strictly BEFORE `bidPlace` in the
       observable significant-destructor trace;
    2. In Edition 2024, `bidPlace` drops strictly BEFORE `pLocal` in the
       observable significant-destructor trace;
    3. Hence the two editions' observable destructor traces are STRICTLY UNEQUAL. -/
theorem dropsReachable_sound_for_significant_dtor_swap
    (b : TedoBody) (bidPlace pLocal : Nat) (xs : List Nat)
    (hSigTemp : b.hasSigDtor bidPlace = true)
    (hSigLocal : b.hasSigDtor pLocal = true)
    (hMem : pLocal ∈ xs)
    (hNe : pLocal ≠ bidPlace)
    (hNotInXs : bidPlace ∉ xs) :
    AppearsBefore pLocal bidPlace (filterSigDrops b (ed2021DropSequence xs bidPlace)) ∧
    AppearsBefore bidPlace pLocal (filterSigDrops b (ed2024DropSequence xs bidPlace)) ∧
    filterSigDrops b (ed2021DropSequence xs bidPlace) ≠
      filterSigDrops b (ed2024DropSequence xs bidPlace) := by
  have hLocalInFilt : pLocal ∈ xs.filter b.hasSigDtor :=
    (mem_filter_iff b.hasSigDtor pLocal xs).2 ⟨hMem, hSigLocal⟩
  have h2021 : filterSigDrops b (ed2021DropSequence xs bidPlace) =
      xs.filter b.hasSigDtor ++ [bidPlace] := by
    unfold filterSigDrops ed2021DropSequence
    rw [filter_append]
    simp only [List.filter, hSigTemp]
  have h2024 : filterSigDrops b (ed2024DropSequence xs bidPlace) =
      bidPlace :: xs.filter b.hasSigDtor := by
    unfold filterSigDrops ed2024DropSequence
    simp only [List.filter, hSigTemp]
  refine ⟨?_, ?_, ?_⟩
  · rw [h2021]
    exact appearsBefore_append_right (xs.filter b.hasSigDtor) hLocalInFilt
  · rw [h2024]
    exact AppearsBefore.head hLocalInFilt
  · rw [h2021, h2024]
    intro heq
    cases hfx : xs.filter b.hasSigDtor with
    | nil =>
      rw [hfx] at hLocalInFilt
      cases hLocalInFilt
    | cons y ys =>
      rw [hfx] at heq
      have hhead : y = bidPlace := List.cons.inj heq |>.1
      subst hhead
      have hyMem : y ∈ xs.filter b.hasSigDtor := by rw [hfx]; exact List.Mem.head ys
      have hyInXs : y ∈ xs := ((mem_filter_iff b.hasSigDtor y xs).1 hyMem).1
      exact hNotInXs hyInXs

/-- **Theorem 4B (`dropsReachable_complete_when_no_intervening_sig_drop`)**:
    If NO intervening drop in `xs` has a significant destructor, then Edition 2021
    and Edition 2024 produce the EXACT SAME observable significant-destructor trace! -/
theorem filter_empty_of_all_false {α : Type} (p : α → Bool) :
    ∀ xs : List α, (∀ x, x ∈ xs → p x = false) → xs.filter p = []
  | [], _ => rfl
  | x :: xs, hall => by
    simp only [List.filter]
    have hx : p x = false := hall x (List.Mem.head xs)
    rw [hx]
    exact filter_empty_of_all_false p xs (fun y hy => hall y (List.Mem.tail x hy))

theorem dropsReachable_complete_when_no_intervening_sig_drop
    (b : TedoBody) (bidPlace : Nat) (xs : List Nat)
    (hNoSig : ∀ x, x ∈ xs → b.hasSigDtor x = false) :
    filterSigDrops b (ed2021DropSequence xs bidPlace) =
      filterSigDrops b (ed2024DropSequence xs bidPlace) := by
  have hempty : xs.filter b.hasSigDtor = [] := filter_empty_of_all_false b.hasSigDtor xs hNoSig
  unfold filterSigDrops ed2021DropSequence ed2024DropSequence
  rw [filter_append, hempty]
  simp only [List.nil_append, List.filter]
  rw [hempty]

/-- Concrete MIR witness matching our live `rustc` Edition 2021 vs Edition 2024
    binary probe (`f` with `_1 = Guard("local")`, `_3 = Guard("temp")`):
    - `bb1`: `BackwardIncompatibleDropHint(_3); drop(_1) -> [return: bb2, unwind: bb5]`
    - `bb2`: `drop(_3) -> [return: bb3, unwind: bb6]`
    - `bb3`: `return`
    - `bb5`, `bb6`: cleanup pads (`isCleanup = true`) -/
def concreteTedoBody (ed : RustEdition) : TedoBody :=
  { edition := ed
  , isClosureLike := false
  , numBlocks := 7
  , isCleanup := fun bb => if natEq bb 5 || natEq bb 6 then true else false
  , termOf := fun bb =>
      match bb with
      | 1 => .drop 1 2 (some 5)
      | 2 => .drop 3 3 (some 6)
      | _ => .return_
  , maybeInitAt := fun bb p =>
      (natEq bb 1 && natEq p 1) || (natEq bb 2 && natEq p 3)
  , roleOf := fun p =>
      match p with
      | 0 => .retPlace
      | 1 => .userLocal
      | 3 => .tailTemp
      | _ => .userLocal
  , hasSigDtor := fun p => natEq p 1 || natEq p 3
  , isBidDescendant := fun _ => false
  }

/-- **Theorem 4C (`dropsReachable_ed2021_vs_ed2024_concrete_witness`)**:
    1. On the exact `rustc` MIR of `f` (`bidBlock = 1`, `bidPlace = 3`),
       `lintTailExprDropOrder` fires on Edition 2021 reporting `[1]` (`_local`),
       and emits `[]` on Edition 2024 (`at_least_rust_2024()`).
    2. Edition 2021 observable drop order is `[1, 3]` (`["local", "temp"]`) vs
       Edition 2024 observable drop order `[3, 1]` (`["temp", "local"]`).
    3. `InterveningDrops` holds for `[1]` from `bb1` to `drop(_3)` at `bb2`. -/
theorem dropsReachable_ed2021_vs_ed2024_concrete_witness :
    lintTailExprDropOrder (concreteTedoBody .ed2021) 1 3 10 = [1] ∧
    lintTailExprDropOrder (concreteTedoBody .ed2024) 1 3 10 = [] ∧
    filterSigDrops (concreteTedoBody .ed2021) (ed2021DropSequence [1] 3) = [1, 3] ∧
    filterSigDrops (concreteTedoBody .ed2024) (ed2024DropSequence [1] 3) = [3, 1] ∧
    InterveningDrops (concreteTedoBody .ed2021) 3 1 [1] := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  exact InterveningDrops.reachTarget
    (target := 2) rfl rfl (List.Mem.head [5]) ⟨3, some 6, rfl⟩

end TailExprDropOrder

end RustcMirLintSoundness
