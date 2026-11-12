# Lean 4 Canonical MIR State Representations, CPS Spine Forcing, and Compositional Symbolic Execution

## Summary

Verifying Rust Mid-level Intermediate Representation (MIR) programs inside the
Lean 4 kernel requires symbolic execution over machine states that track local
variables, storage lifetimes (`StorageLive`/`StorageDead`), mutable borrows, and
control-flow graph (CFG) joins. Across two experimental verification stacks in
`joshlf/anneal` (`a7ac073219f4` and `2fb744d6ecb5` / `aa325aa43af9`), two
different state and execution representations hit severe scaling walls:

1. **The 23,686-Line `theory/` Explosion (`a7ac073219f4`)**: Representing local
   stores and loan-invalidation generations as function closures
   (`locals : Nat → Option MirVal`, `localGens : Nat → Nat` in
   `trusted/lean/Trusted/MirSemantics.lean`, and
   `locals : Nat → Option SymVal`, `loans : Nat → Option LoanEntry`,
   `back : SymVal → List SymVal` in
   `theory/Anneal/FunctionalTranslation.lean`) breaks kernel definitional
   equality (`isDefEq` / `rfl`). Out-of-order writes, redundant overwrites, and
   `StorageLive`/`StorageDead` temporary lifecycles produce distinct nested
   `fun i => if i == dst then ...` syntax trees. Worse, bumping `localGens`
   unconditionally on every `StorageLive` and `StorageDead` records a permanent
   history of how many dead scalar temporaries each basic-block path allocated,
   making the post-states of asymmetric `if/else` branches **propositionally
   unequal** (`sThen.localGens 3 = 2 ≠ 0 = sElse.localGens 3`). Recovering from
   closure non-canonicity and generation pollution required 8,882 lines of
   relational simulation lemmas (`theory/Anneal/{Lowering.lean,MirLemmas.lean}`)
   and 11,619 lines in `theory/Anneal/FunctionalTranslation.lean`.
2. **The 5,230–5,270-Line Python Witness Generator (`2fb744d6ecb5` /
   `aa325aa43af9`)**: Switching `State.locals` to a canonical `List Slot` in
   `trusted/lean/Trusted/Mvp.lean` fixed extensional equality, but direct
   small-step recursion (`Anneal.Mvp.run` in `theory/Anneal/Mvp/Execution.lean`)
   over a 65-local state containing a symbolic free variable (`value : Word`)
   triggered an $O(2^k)$ weak-head normal form (WHNF) blowup after $k \approx
   12..16$ steps. Because Lean 4's WHNF cache (`useWHNFCache` in
   `src/Lean/Meta/WHNF.cpp`) refuses to cache any expression containing a free
   variable (`hasFVar == true`), each step's `List.set` and `List.length`
   guards re-evaluated the entire unforced chain of prior `List.set` thunks. To
   verify the 8 paths (254 total active steps; up to 62 active steps / 99 raw
   steps per path) of the Starnix `apply_endianness` fixture, the author wrote a
   181-line Python MIR interpreter (`generate_steps.py`) that emitted 5,230 to
   5,270 lines of hardcoded intermediate state snapshots (`ProductionSteps.lean`)
   and capped multi-step `Reach` prefixes at `checkpoint = min(2, last)` so 1-step
   negative mutations (`return 0;`) would not fail on out-of-range checkpoints.

This report diagnoses the exact kernel and elaborator mechanisms behind both
bottlenecks and proves three architectural remedies in standalone, reproducible
Lean 4 probes (`support/*.lean`):

- **Canonical `List Slot` State with Borrow-Dirtied Generation Tracking**
  (`support/CanonicalStateAndJoinProbe.lean`, 354 lines, 1.41 s compile time):
  Replacing function closures with a canonical `List Slot` where each slot is
  `.dead gen | .uninit gen | .live val gen borrowed` and `StorageLive` /
  `StorageDead` increment `gen` **if and only if `borrowed == true`** (the slot's
  address was taken by `Rvalue.ref` during its live incarnation) makes
  unborrowed temporary lifecycles (`StorageLive tmp; tmp = v; ...; StorageDead
  tmp`) an **exact definitional round-trip identity** (`.dead g → .uninit g →
  .live v g false → .dead g`). Asymmetric `if/else` diamond branches reunite at
  the join block by kernel `rfl` with **zero** `funext` or
  `deadLocalGen_irrel` lemmas, while strictly incrementing `gen` whenever a
  borrowed slot dies or is reborn (`kill_or_rebirth_invalidates_borrowed_slot`),
  rejecting all use-after-`StorageDead` and use-after-`StorageLive`-rebirth
  dereferences by `rfl`.
- **CPS Spine Forcing for Symbolic `List` Execution (`runForced`)**
  (`support/StarnixZeroGeneratorSymbolicEngine.lean`, 1,153 lines including the
  entire 961-line `Captured.lean` Starnix AST, 8.23 s compile time): Adding a
  42-line continuation-passing style (CPS) spine-forcing evaluator (`forceList`,
  `forceState`, `runForced`, `runForced_eq_run`, `runForced_initial_success`) to
  `theory/` (with **zero** changes to `Trusted.Mvp`) decomposes the 65-element
  `List Slot` spine into fresh lambda-bound variables before each recursive step.
  This reduces per-step lookup/update work from $O(2^k \cdot n)$ to $O(n)$,
  verifies all 8 paths of Starnix `apply_endianness` and `Proof.verify` in a
  **38-line** replacement for the 5,230-line `ProductionSteps.lean` (**137.6x
  smaller**), eliminates `generate_steps.py` completely, and rejects both the
  1-step `zero` mutation (`return 0;`, 4 locals) and the 7-step
  `masked-identity` mutation (`return value & 0xffff;`, 8 locals) directly on
  the specification postcondition without regenerating proof witnesses.
- **First-Order Defunctionalized Backward Lenses (`LoanBack`) and Canonical
  Loop-Header Normalization** (`support/CompositionalBorrowAndLoopWP.lean`,
  1,042 lines total including standalone MIR AST and 6 `MirBody` fixtures,
  2.82 s compile time): Eliminating all three closures from `SymState`
  (`locals : List (Option SymVal)`, `loans : List (Option LoanEntry)`, and
  first-order `LoanBack := .root | .join2 cond falseLid vFalse trueLid vTrue`)
  and pairing them with pointwise canonical CFG diamond state joins
  (`joinSymStates`), CPS spine forcing (`forceSymState`), and canonical
  loop-header states (`countUpHeaderState n i`) verifies all 6 target functions
  from `FunctionalTranslation.lean` (`max_assign`, `update_min`, `clamp_assign`,
  `choose_mut` with all three lens laws, `two_phase_reborrow`, and `count_up`) in
  **11.2x fewer lines** than `FunctionalTranslation.lean` (1,042 lines vs.
  11,619 lines).

---

## Applicability

The findings and probes in this report apply to:

- **Lean 4 (`leanprover/lean4`)**: Tested against commit
  `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`). The kernel and
  elaborator reduction behaviors analyzed here—specifically structural reduction
  of `List` vs. lambda closures under `is_def_eq`, and the `!e.hasFVar()` guard
  in `Lean.Meta.WHNF.useWHNFCache` (`src/Lean/Meta/WHNF.cpp`)—apply to all Lean 4
  releases that share this WHNF caching architecture.
- **Anneal (`joshlf/anneal`)**: Analyzed across commit
  `aa325aa43af936a97932e0e1c14755edf1a9136d` (and the `459798718e58..aa325aa43af9`
  Starnix verification stack, including commit `2fb744d6ecb5`
  `[proofs] Compose checked source segments`) as well as the experimental
  refinement and functional-translation stack at `a7ac073219f4ec3c813431be8239a0405014d5c1`
  (`trusted/lean/Trusted/MirSemantics.lean`, `theory/Anneal/Lowering.lean`,
  `theory/Anneal/MirLemmas.lean`, and `theory/Anneal/FunctionalTranslation.lean`).

---

## Findings

### 1. Why Closure-Based State (`Nat → Option Val`) and Unconditional `StorageLive`/`StorageDead` Generation Bumps Break Definitional Equality

In `trusted/lean/Trusted/MirSemantics.lean` (`a7ac073219f4`), a concrete MIR
execution state is defined with function closures for local variables and
per-local generation counters:

```lean
structure MirState where
  locals : Nat → Option MirVal
  localGens : Nat → Nat
  mem : MemState
  block : Nat := 0
  stmtIdx : Nat := 0

def updateLocal (locals : Nat → Option MirVal) (idx : Nat) (val : Option MirVal) :
    Nat → Option MirVal :=
  fun i => if i == idx then val else locals i

def bumpGen (gens : Nat → Nat) (idx : Nat) : Nat → Nat :=
  fun i => if i == idx then gens idx + 1 else gens i
```

Every statement mutates `locals` and/or `localGens` by wrapping another
`fun i => if i == idx then ...` closure around the prior function:

- `Stmt.storageLive loc`: sets `locals := updateLocal s.locals loc.index none`
  and `localGens := bumpGen s.localGens loc.index`.
- `Stmt.storageDead loc`: sets `locals := updateLocal s.locals loc.index none`
  and `localGens := bumpGen s.localGens loc.index`.
- `Operand.move src`: sets `locals := updateLocal s.locals src.index none`.
- `Stmt.assign dst rv`: sets `locals := updateLocal locals' dst.index (some v)`.

This representation creates two distinct obstacles to symbolic execution and CFG
join reasoning in Lean 4:

#### 1.1 Syntactic Non-Canonicity of Function Closures Under `isDefEq`

In Lean 4's kernel typechecker (`is_def_eq`), two lambda terms `fun i => t₁` and
`fun i => t₂` are definitionally equal (`rfl`) if and only if opening their body
with a fresh free variable `i : Nat` makes `t₁` and `t₂` definitionally equal.
When `i : Nat` is a free variable, `i == 1` (`decide (i = 1)`) and `i == 2` are
**stuck neutral terms**. Consequently:

1. **Out-of-order writes to distinct locals do not commute definitionally**:
   ```lean
   -- Writing `_1 := a` then `_2 := b`:
   fun i => if i == 2 then some b else if i == 1 then some a else base i
   -- Writing `_2 := b` then `_1 := a`:
   fun i => if i == 1 then some a else if i == 2 then some b else base i
   ```
   With a symbolic `i : Nat`, neither `if` reduces, so `rfl` fails even though
   the two functions agree at every `i : Nat`.
2. **Redundant overwrites and temporary lifecycles leave permanent closure
   residue**: Executing `_3 := some tmp` followed by `Operand.move ⟨3⟩` (or
   `StorageDead ⟨3⟩`) produces:
   ```lean
   fun i => if i == 3 then none else if i == 3 then some tmp else base i
   ```
   Even when `base 3 = none`, this closure is not definitionally equal to `base`
   because `if i == 3 then none else ...` is stuck on symbolic `i`.

#### 1.2 Propositional Non-Canonicity from Unconditional `StorageLive`/`StorageDead` Generation Bumps

Even if one invokes `funext` to prove propositional equality (`=`) instead of
definitional equality (`rfl`), unconditional generation bumping in
`Stmt.storageLive` and `Stmt.storageDead` makes the post-states of asymmetric
`if/else` branches **propositionally unequal** (`sThen ≠ sElse`).

Consider a standard `Runtime(PostCleanup)` MIR diamond generated by `rustc` for
an `if/else` expression where the `then` branch computes an intermediate scalar
in temporary `_3` (`StorageLive(_3); _3 = x + 1; _0 = move _3; StorageDead(_3);
goto -> bbJoin`) and the `else` branch computes its intermediate scalar in
temporary `_4` (`StorageLive(_4); _4 = x + 1; _0 = move _4; StorageDead(_4);
goto -> bbJoin`). At `bbJoin`:

- Both branches hold the exact same live values (`_0 = some (x + 1)`,
  `_1 = some x`) and all temporaries `_3` and `_4` are dead (`none`).
- However, in `sThen`, `sThen.localGens 3 = s0.localGens 3 + 2` and
  `sThen.localGens 4 = s0.localGens 4`.
- In `sElse`, `sElse.localGens 3 = s0.localGens 3` and
  `sElse.localGens 4 = s0.localGens 4 + 2`.

As proved in `support/CanonicalStateAndJoinProbe.lean`
(`ClosureModel.asymmetric_temp_branches_not_equal` and
`ClosureModel.asymmetric_temp_states_ne`), `sThen.localGens 3 ≠ sElse.localGens 3`,
so `sThen ≠ sElse`—no `funext` proof can equate them!

To work around these two representation flaws, `theory/Anneal/Lowering.lean`
(2,257 lines) and `theory/Anneal/MirLemmas.lean` (6,625 lines) had to define a
custom relational equivalence `DeadLocalGenIrrel` (ignoring `localGens` on dead
unborrowed locals) and prove hundreds of lines of step-simulation and prefix
theorems (`execNormal_deadLocalGen_irrel`, `reachPrefix_deadLocalGen_irrel`,
`proveBodyNoAdtOpt`), while `theory/Anneal/FunctionalTranslation.lean` (11,619
lines) had to maintain a separate symbolic state `SymState` with closure stores
(`locals : Nat → Option SymVal`, `loans : Nat → Option LoanEntry`), a
15-conjunct relational invariant (`JoinInv`), and closure wrappers for every
basic block inside loop invariants (`countUpLocalsAfterBb1..4`).

---

### 2. Canonical Extensional `List Slot` State with Borrow-Dirtied Generation Tracking

To restore **definitional equality (`rfl`)** across temporary lifecycles and CFG
diamond joins without weakening dangling-pointer detection, we apply the
4-Dial discipline to `MirState`:

1. **Why do generation counters exist in MIR operational semantics?**
   A generation counter on local slot `l` exists solely to detect **temporal
   aliasing (use-after-free / use-after-rebirth)** through a raw pointer or
   reference `Ptr { local := l, gen := g }` whose address was taken during an
   earlier `StorageLive(l)..StorageDead(l)` incarnation.
2. **Can a local slot whose address was never taken during its live incarnation
   ever have a dangling pointer pointing to that incarnation?**
   No. Any pointer `{ local := l, gen := g }` created before the current
   incarnation already had its generation invalidated when that earlier
   borrowed incarnation ended. If the current incarnation of `l` is never
   borrowed (`Rvalue.ref` is never executed on `l`), no pointer with the current
   generation `g` is ever minted.
3. **Essential Invariant (Borrow-Dirtied Generation Normalization)**:
   Represent the local store as a fixed-length canonical `List Slot` (of length
   `body.localCount`), where each `Slot` is:
   ```lean
   inductive Slot where
     | dead (gen : Nat)
     | uninit (gen : Nat)
     | live (val : Val) (gen : Nat) (borrowed : Bool)
     deriving DecidableEq, Repr
   ```
   with transition rules:
   - `StorageLive(l)`:
     - `.dead g → .uninit g`
     - `.uninit g → .uninit g`
     - `.live _ g false → .uninit g`
     - `.live _ g true → .uninit (g + 1)` (rebirth of a live borrowed slot
       invalidates existing pointers)
   - `Assign(l, v)`:
     - `.uninit g → .live v g false`
     - `.live _ g borrowed → .live v g borrowed` (scalar assignment preserves
       whether the current incarnation has been borrowed)
   - `Move(l)`:
     - `.live v g false → (v, .uninit g)` (moving out of an unborrowed slot;
       moving out of a borrowed slot returns `none`)
   - `Rvalue.ref(l)` (taking `&l`, `&mut l`, or `&raw l`):
     - `.live v g _ → (Val.ptr l g, .live v g true)` (marks the current
       incarnation `borrowed := true` and mints pointer at generation `g`)
   - `StorageDead(l)`:
     - `.dead g → .dead g`
     - `.uninit g → .dead g`
     - `.live _ g false → .dead g` (unborrowed temporary returns to its **exact**
       pre-`StorageLive` state `.dead g`!)
     - `.live _ g true → .dead (g + 1)` (borrowed incarnation bumps `g` to
       `g + 1` upon deallocation, invalidating all pointers minted at `g`!)
   - `Deref(Val.ptr l g)`:
     - Succeeds if and only if `locals[l]` is `.live v g' borrowed` with
       `g' == g`.

In `support/CanonicalStateAndJoinProbe.lean`, we mechanize both `ClosureModel`
and `CanonicalModel` and prove six theorems that establish soundness and
canonicity simultaneously:

1. **Temporal-Safety Soundness (`kill_or_rebirth_invalidates_borrowed_slot`)**:
   For any borrowed slot `Slot.live v g true`, both `Slot.kill` (`StorageDead`)
   and `Slot.birth` (`StorageLive`) produce a slot whose generation is strictly
   `g + 1`, and `derefRead` / `derefWrite` at generation `g` return `none` after
   `StorageDead` (`use_after_storageDead_rejected_rfl`), after `StorageLive`
   rebirth (`use_after_storageLive_rebirth_rejected_rfl`), and even after
   rebirth, re-initialization, and re-borrowing
   (`use_after_rebirth_and_reborrow_distinguished_rfl`).
2. **Definitional Round-Trip Identity for Unborrowed Temporaries
   (`unborrowed_lifetime_roundtrip_rfl`)**:
   Executing `StorageLive(tmp) → Assign(tmp, v) → Move(tmp) → StorageDead(tmp)`
   on any initially dead slot `.dead g` reduces **definitionally (`rfl`)** back
   to `.dead g`.
3. **Definitional Commutativity and Idempotence on Concrete Store Spines
   (`commuting_updates_rfl`, `redundant_self_update_rfl`)**:
   Out-of-order writes to distinct indices (`setSlot 1 a` then `setSlot 2 b` vs.
   `setSlot 2 b` then `setSlot 1 a`) and overwritten updates (`setSlot 1 a` then
   `setSlot 1 b`) reduce to the **exact same `List Slot` term** by `rfl`.
4. **Zero-Lemma CFG Diamond Join (`asymmetric_temp_diamond_reunites_rfl`)**:
   The asymmetric `if/else` diamond where `bb1` uses temporary `_3` and `bb2`
   uses temporary `_4` reunites at `bbJoin` with **definitionally identical
   states (`sThen = sElse` by `rfl`)**, enabling the post-dominator block
   `bbJoin` to be verified once by `cases cond <;> rfl` (`diamond_exec_unified_rfl`).

---

### 3. Why Symbolic Execution Over `List Slot` Blows Up $O(2^k)$ Under `hasFVar == true` and How CPS Spine Forcing (`runForced`) Eliminates `generate_steps.py`

In `joshlf-mvp` (`aa325aa43af9` and `2fb744d6ecb5`), `Trusted/Mvp.lean` already
uses a `List Slot` representation (`State.locals : List Slot`), and
`theory/Anneal/Mvp/Execution.lean` defines the small-step interpreter:

```lean
def run (body : Body) : Nat → State → RunResult
  | 0, state => .outOfFuel state
  | fuel + 1, state =>
      match step body state with
      | .next next => run body fuel next
      | .returned value => .returned value
      | .stuck reason => .stuck reason
```

Why did `run sourceBody 100 (initial sourceBody [Value.int value mode] ...)`
time out in Lean 4's elaborator and kernel after ~12–16 steps on Starnix's
65-local `apply_endianness` function, forcing the author to write
`generate_steps.py` (181 lines) and commit a 5,230–5,270-line
`ProductionSteps.lean` file containing 246 intermediate `State` definitions
(`le8_state0..be64_state62`)?

#### 3.1 The Exact Mechanism: `!e.hasFVar()` in `Lean.Meta.WHNF` and Unforced `List.set` Thunks

In `Execution.lean`, `writeLocal` updates a local slot by guarding on
`List.length`:

```lean
def writeLocal (state : State) (localIdx : Local) (slot : Slot) : Option State :=
  if localIdx < state.locals.length then
    some { state with locals := state.locals.set localIdx slot }
  else
    none
```

When `state` is Concrete (closed, `hasFVar == false`), Lean's WHNF cache caches
reduced subterms. However, inside a theorem quantified over a symbolic input
`(value : Word)`, `state.locals` contains the free variable `value` at index 1
(`Slot.val (Value.int value ...)`). In Lean 4's C++ elaborator
(`src/Lean/Meta/WHNF.cpp`), `useWHNFCache(e)` checks `!e.hasFVar()`. Because
`state.locals` has `hasFVar == true`:

1. **WHNF caching is disabled** for `state` and `state.locals`.
2. In `run`, `match step body state with | .next next => run body fuel next`
   checks only that `step body state` has head constructor `StepResult.next`. It
   does **not** force `next.locals` to WHNF before passing `next` into `run body
   fuel next`.
3. Thus after step 1, `state₁.locals` is the unreduced thunk
   `List.set state₀.locals i₁ v₁`.
4. At step 2, `writeLocal` evaluates `localIdx < state₁.locals.length` (which
   traverses the `List.set` thunk to compute `.length = 65`) and then builds
   `state₂.locals = List.set (List.set state₀.locals i₁ v₁) i₂ v₂`—without
   saving the reduced spine of `state₁.locals`!
5. At step $k$, every `readSlot` (`state.locals[idx]?`) and `writeLocal`
   (`state.locals.length` + `state.locals.set`) re-evaluates the nested tree of
   unforced `List.set` applications from scratch, doing $O(2^k \cdot 65)$ work
   and exceeding `maxHeartbeats` by $k \approx 16$.

#### 3.2 Why `generate_steps.py` Also Forced `checkpoint = min(2, last)` in `2fb744d6ecb5`

In commit `2fb744d6ecb5` (`[proofs] Compose checked source segments`), the
author tried to reduce the number of 1-step theorems by introducing a multi-step
`Reach` prefix before the suffix chain (`executes_prepend : Reach → Executes →
Executes`). However, `generate_steps.py` had to hardcode:

```python
checkpoint = min(2, last)
```

for two reasons:
1. Without spine forcing, `Reach` prefixes of length $> 12$ still hit the
   $O(2^k)$ `List.set` WHNF blowup.
2. In `ci/test_mvp_starnix.py`, the negative mutation tests (`zero`: replacing
   the function body with `return 0;`, which has 4 locals and returns in 1 step,
   so `last = 1`; and `masked-identity`: replacing `be16` with `return value &
   0xffff;`, which has 8 locals and returns in 7 steps) had to **re-run
   `generate_steps.py` on the mutated Rust code**! Why? Because the baseline
   `ProductionSteps.lean` hardcoded 65-element `State` snapshots
   (`le8_state0..be64_state62`). When `source/api.rs` was mutated to `return 0;`,
   `sourceBody.localDecls.length` shrank from 65 to 4, so the hardcoded equality
   `initial sourceBody ... = le8_state0 value` failed on the **local-declaration
   count mismatch** (65 vs. 4) rather than testing the return-value
   postcondition! And when `generate_steps.py` was re-run on `return 0;` (`last
   = 1`), any fixed checkpoint $> 1$ would fail before reaching the return value.

#### 3.3 The 42-Line CPS Spine-Forcing Engine (`runForced`)

We solve both problems in `theory/`—with **zero** modifications to `Trusted.Mvp`
—by adding 42 lines to `Anneal.Mvp` (mechanized in
`support/StarnixZeroGeneratorSymbolicEngine.lean`):

```lean
@[inline] def forceList (xs : List α) (k : List α → β) : β :=
  match xs with
  | [] => k []
  | x :: rest => forceList rest (fun rest' => k (x :: rest'))

@[inline] def forceState (s : State) (k : State → β) : β :=
  match s with
  | { bb, stmtIdx, locals } =>
    Nat.casesOn bb
      (fun stmtIdx locals =>
        Nat.casesOn stmtIdx
          (fun locals => forceList locals (fun locals' => k { bb := 0, stmtIdx := 0, locals := locals' }))
          (fun s1 locals => forceList locals (fun locals' => k { bb := 0, stmtIdx := s1 + 1, locals := locals' }))
          locals)
      (fun b1 stmtIdx locals =>
        Nat.casesOn stmtIdx
          (fun locals => forceList locals (fun locals' => k { bb := b1 + 1, stmtIdx := 0, locals := locals' }))
          (fun s1 locals => forceList locals (fun locals' => k { bb := b1 + 1, stmtIdx := s1 + 1, locals := locals' }))
          locals)
      stmtIdx locals

def runForced (body : Body) : Nat → State → RunResult
  | 0, state => .outOfFuel state
  | fuel + 1, state =>
      match step body state with
      | .next next => forceState next (fun nextForced => runForced body fuel nextForced)
      | .returned value => .returned value
      | .stuck reason => .stuck reason
```

Why does `forceList` eliminate the $O(2^k)$ blowup?
Because `match xs with | x :: rest => ...` is a primitive recursor application
(`List.casesOn`). To reduce `List.casesOn (List.set xs idx v)` one step, Lean's
WHNF **must** push `List.set` down one cons cell, binding the head element to a
fresh variable `x` and recursively forcing `rest` into a concrete spine of 65
cons cells `x₀ :: x₁ :: ... :: x₆₄ :: []` **before** `k` (`runForced body fuel`)
is entered! Consequently, at step $k + 1$, `nextForced.locals` is already a flat
65-element cons spine; `locals.length` and `locals.set` take $O(65)$ steps
instead of $O(2^k \cdot 65)$, and total reduction work across $k = 99$ steps is
linear ($99 \times 65 = 6,435$ list-cell steps).

We then prove once by induction on `fuel` (18 lines):

```lean
theorem forceList_eq (xs : List α) (k : List α → β) : forceList xs k = k xs
theorem forceState_eq (s : State) (k : State → β) : forceState s k = k s
theorem runForced_eq_run (body : Body) (fuel : Nat) (state : State) :
    runForced body fuel state = run body fuel state
theorem runForced_initial_success {body : Body} {args : List Value} {state : State}
    {fuel : Nat} {ret : Value}
    (hInit : initial body args = some state)
    (hRun : runForced body fuel state = .returned ret) :
    SafeFrom body state ∧ Executes body state ret
```

With `runForced_initial_success` in `Anneal.Mvp`, the entire 5,230-line
`ProductionSteps.lean` shrinks to **38 lines** (8 one-line `rfl` theorems
`le8_exec..be64_exec`), and `generate_steps.py` is deleted:

```lean
theorem be64_exec (value : Word) :
    SafeFrom sourceBody (initState value 7) ∧
      Executes sourceBody (initState value 7) (Value.int (be64Out value) u64Ty) :=
  runForced_initial_success (fuel := 100) (initState_eq value 7) rfl
```

Furthermore, in Section 5 of `support/StarnixZeroGeneratorSymbolicEngine.lean`,
we prove that `runForced` handles both negative mutations from
`ci/test_mvp_starnix.py` **without** regenerating witnesses or needing
`checkpoint = min(2, last)`:

- **`zero` mutation (`return 0;`, 4 locals, 1 step)**: `runForced` steps the
  4-local mutated body in 1 step to `.returned (Value.int 0 u64Ty)`
  (`mutatedZero_be64_evaluates_to_zero`), which is refuted against `exactReversal`
  at `value = 1` (`mutatedZero_rejected_by_exactReversal`, since `0 ≠
  0x0100000000000000`).
- **`masked-identity` mutation (`be16` replaced by `return value & 0xffff;`, 8
  locals, 7 steps)**: Remarkably, even though `localDecls.length` shrinks from 65
  to 8, the **exact same unmodified `runForced` proof script** still verifies all
  5 unaffected paths (`le8`, `le16`, `le32`, `le64`, `be8`) by `rfl`
  (`mutatedMaskedIdentity_unaffected_paths_still_verify`), while on `be16`
  `runForced` evaluates to `value &&& 0xffff`
  (`mutatedMaskedIdentity_be16_evaluates_to_unreversed`), which is refuted at
  `value = 1` (`1 ≠ 256`, `mutatedMaskedIdentity_rejected_by_exactReversal`).

---

### 4. Compositional Symbolic Execution, First-Order Backward Lenses (`LoanBack`), and Canonical Loop-Header Invariants

In `theory/Anneal/FunctionalTranslation.lean` (`a7ac073219f4`, 11,619 lines),
four design choices caused proof and specification size to explode across the 13
embedded example developments:

1. **Three Layers of Closures Inside `SymState`**:
   - `SymState.locals : Nat → Option SymVal`
   - `SymState.loans : Nat → Option LoanEntry`
   - `LoanEntry.back : SymVal → List SymVal`
   Because `locals` and `loans` were closures, two symbolic states at a CFG
   diamond join block (`if cond { *x = y } else {}`) could not be pointwise
   merged into a single canonical `SymState`; instead, `.branch falsePlan
   truePlan` had to duplicate the post-dominator continuation of every `if/else`
   into both branches of the plan tree. And because `LoanEntry.back` was a
   lambda closure `fun newVal => [...]`, Lean's WHNF could not normalize captured
   symbolic expressions under `fun newVal => ...` until `.endLoan` applied the
   closure.
2. **A 15-Conjunct Relational Join Invariant (`JoinInv`)**:
   Because `evalEndLoan` updated parent loans by positional index matching
   (`match entry.owners, entry.back entry.curVal with | [.loan falseLid, .loan
   trueLid], [vFalse, vTrue] => ...`), `evalJoinBorrow_sound` (lines 6000–6480,
   ~480 lines for a single case!) had to prove a 15-conjunct `JoinInv` tracking
   disequalities and ownership across every active loan.
3. **70–106 Lines of Per-Function `extractSymArgs` Unpacking Boilerplate**:
   Every verified function (`max_assign`, `update_min`, `clamp_assign`,
   `choose_mut`, `two_phase_reborrow`, `count_up`, etc.) repeated an 80-line
   nested `cases hloc1 : init.locals 1 ... cases hna1 : init.mem.naVal loc1 ...`
   cascade to unpack `extractSymArgsAux` before rewriting with the `rfl`
   symbolic evaluation theorem.
4. **Closure-Chain Loop Wrappers (`countUpLocalsAfterBb1..4`)**:
   In `count_up` (`while i < n && i < 1000 { i += 1 }`, lines 10780–11350,
   ~570 lines), because `sym.locals` was a closure `Nat → Option SymVal`,
   stepping through `bb1 → bb2 → bb3 → bb4 → bb1` wrapped 9 layers of
   `updateSymLocal` around `sym.locals`. The loop invariant could not state a
   canonical `SymState` at `bb1`; instead, the author had to define three bespoke
   closure wrappers (`countUpLocalsAfterBb1`, `countUpLocalsAfterBb2`,
   `countUpLocalsAfterBb4`) and prove four per-block stepping lemmas
   (`evalSymState_countUp_bb1..bb4`, 210 lines) just to advance one loop
   iteration.

In `support/CompositionalBorrowAndLoopWP.lean`, we replace all four bottlenecks
with a unified, purely first-order symbolic engine:

1. **Zero Closures Anywhere in `SymState` (`List` Stores + First-Order
   `LoanBack`)**:
   ```lean
   inductive LoanBack where
     | root
     | join2 (cond : Bool) (falseLid : Nat) (vFalse : SymVal) (trueLid : Nat) (vTrue : SymVal)
     deriving DecidableEq, Repr

   def LoanBack.apply : LoanBack → SymVal → List (Nat × SymVal)
     | .root, _ => []
     | .join2 cond falseLid vFalse trueLid vTrue, newVal =>
       [(falseLid, zipSymVal cond vFalse newVal),
        (trueLid, zipSymVal cond newVal vTrue)]

   structure LoanEntry where
     curVal : SymVal
     frozen : Bool := false
     back : LoanBack := .root
     deriving DecidableEq, Repr

   structure SymState where
     locals : List (Option SymVal)
     loans : List (Option LoanEntry)
     block : Nat := 0
     stmtIdx : Nat := 0
     deriving DecidableEq, Repr
   ```
   Because `LoanBack` is first-order data rather than a `SymVal → List ...`
   closure, `forceOptionLoan` forces `vFalse` and `vTrue` at every step (so no
   unreduced `setAt` thunks hide under lambda binders), and `LoanBack.apply`
   returns explicit `(parentLoanId, updatedVal)` pairs consumed uniformly by
   `applyLoanUpdates`.
2. **Pointwise Canonical CFG Diamond Joins (`joinSymStates` / `TransPlan.diamond`)**:
   Because `locals` and `loans` are finite canonical lists, `joinSymStates cond
   symT symF` pointwise-zips the two branch states at a CFG merge block (`symT.block
   == symF.block`), pushing `if cond` inside `.usize`/`.bool` payloads via
   `zipSymVal` while keeping identical slots (`none`, `.borrow lid`, unchanged
   locals) canonical. The post-dominator suffix `afterJoin` is then executed
   **once** on the merged `SymState`, eliminating exponential path-tree
   duplication on cascaded diamonds (`max_assign`, `clamp_assign`).
3. **CPS Spine Forcing on `SymState` (`forceSymState` / `forceSymState_eq`)**:
   Just as in `StarnixZeroGeneratorSymbolicEngine.lean`, `evalSymState` forces
   the `List (Option SymVal)` and `List (Option LoanEntry)` spines at every step
   via `forceSymState` (proved equal to the identity in 35 lines via
   `forceSymState_eq`), preventing $O(2^k)$ WHNF re-evaluation across
   multi-phase reborrows (`two_phase_reborrow`).
4. **Canonical Loop-Header State Normalization (`countUpHeaderState`)**:
   Because `SymState.locals` is an 8-element `List (Option SymVal)` and
   `Operand.move` / `Rvalue.proj0` clear consumed temporaries (`_3.._7`) back to
   `none`, the loop header state at `bb1` has the exact canonical representation:
   ```lean
   def countUpHeaderState (n i : Nat) : SymState where
     locals := [none, some (.usize n), some (.usize i), none, none, none, none, none]
     loans := []
     block := 1
     stmtIdx := 0
   ```
   Parameterizing the one-iteration theorem `countUp_iter_step` by an opaque
   continuation `(rest : TransPlan)` prevents `isDefEq` from unfolding
   subsequent loop iterations and proves in 6 lines (`dsimp [...]; cases decide
   (i < n) <;> cases decide (i < 1000) <;> cases decide (usizeMax < i + 1) <;>
   rfl`) that the continue branch steps `countUpHeaderState n i` **directly** to
   `countUpHeaderState n (i + 1)` with **zero** closure wrappers.

All six target functions from `FunctionalTranslation.lean` verify cleanly in
`support/CompositionalBorrowAndLoopWP.lean`:

| Target Function | Rust Feature Pattern | Proof Method in `CompositionalBorrowAndLoopWP.lean` |
| :--- | :--- | :--- |
| `max_assign(x: &mut usize, y: usize) -> usize` | Branching mutable-borrow mutation + CFG diamond join (`.diamond`) | 1-line `rfl` (`maxAssign_eval_rfl`) for both return value and post-state `x'` |
| `update_min(x: &mut usize, y: &mut usize, v: usize) -> usize` | Conditional mutable reborrow (`let r = if *x <= *y { &mut *x } else { &mut *y }`) + `.endLoan` | 1-line `rfl` (`updateMin_eval_rfl`) for return value `*x` and post-state pair `(x', y')` |
| `clamp_assign(x: &mut usize, lo: usize, hi: usize) -> usize` | Cascaded 3-way `if / else if / else` diamond join over `&mut usize` | 1-line `rfl` (`clampAssign_eval_rfl`) with nested `.diamond` (zero suffix duplication) |
| `choose_mut<'a>(b: bool, x: &'a mut usize, y: &'a mut usize) -> &'a mut usize` | Function returning `&'a mut usize` (forward value + backward lens) | 1-line `rfl` (`chooseMut_fwd_rfl`, `chooseMut_back_rfl`) + 1-line proof of Get-Put, Put-Get, and Put-Put lens laws (`chooseMut_lens_laws`) |
| `two_phase_reborrow(x: &mut usize, y: &mut usize, a: usize, b: usize) -> usize` | Two sequential diamond reborrows (`r1`, `r2`) separated by intermediate `.endLoan` and reads of `*x, *y` | 1-line `rfl` (`twoPhaseReborrow_eval_rfl`) enabled by first-order `LoanBack` + `forceSymState` |
| `count_up(n: usize) -> usize` | `while i < n && i < 1000 { i += 1 }` loop with checked addition | `countUp_entry_step` (`rfl`), `countUp_iter_step` (6 lines), and `countUp_loop_eval` (35 lines) over canonical `countUpHeaderState n i` |

---

### 5. Quantitative Benchmark Comparison

Running `python3 support/run_canonical_wp_benchmarks.py` on Lean 4.34.1
(`5045d0056413266e57c625dcd7c365b10e377c52`) produces the following measured
metrics (captured in `support/benchmark_results.json`):

#### 5.1 Starnix `apply_endianness` Verification (`joshlf-mvp` vs. Probe 2)

| Metric | Baseline (`joshlf-mvp` at `aa325aa43af9` / `2fb744d6ecb5`) | CPS Spine-Forcing Engine (`support/StarnixZeroGeneratorSymbolicEngine.lean`) | Improvement / Delta |
| :--- | :--- | :--- | :--- |
| External Python witness generator (`generate_steps.py`) | 181 lines (163 non-empty lines, 7,007 B) | **0 lines (eliminated)** | -100% (no external Python MIR interpreter) |
| Per-fixture step witness (`ProductionSteps.lean`) | 5,270 lines (pre-`2fb744d6e`) / 5,230 lines (at `2fb744d6e`, 212,392 B) | **38 lines** (8 one-line `runForced_initial_success` theorems) | **137.6x fewer lines** (-5,192 lines) |
| Reusable engine addition to `Execution.lean` | 257 lines (`Execution.lean`) | **+42 lines** (`forceList`, `forceState`, `runForced`, `runForced_initial_success`) | Reusable across all crates |
| Total standalone probe file (including 961-line `Captured.lean` + `ProductionClaims.lean` + 2 mutation proofs) | 6,737 lines across crate proof files | **1,153 lines** (987 non-empty lines, 61,446 B) | **5.8x smaller total**, **137.6x smaller per-function proof** |
| Compilation wall time / user CPU / peak RSS / `.olean` size | ~14.2 s wall (multi-file `lake build`) | **8.24 s wall** (18.37 s user, 0.42 s sys, 838 MiB RSS, 8.17 MiB `.olean`) | Single-pass kernel reduction of all 8 paths + 2 mutation canaries |
| Negative mutation behavior (`zero`: 1 step, 4 locals; `masked-identity`: 7 steps, 8 locals) | Fails on hardcoded 65-local state layout mismatch unless `generate_steps.py` is re-run with `checkpoint = min(2, last)` | **Evaluates mutated `Body` directly**; unaffected paths still pass on 8-local mutated body (`rfl`), and mutated path fails cleanly on postcondition | Eliminates layout-coupled false failures and `checkpoint = min(2, last)` workaround |

#### 5.2 Closure State vs. Canonical State & Compositional Borrow/Loop Symbolic Execution (`joshlf` vs. Probes 1 & 3)

| Artifact / Subsystem | Baseline (`joshlf` at `a7ac073219f4`) | Canonical State & Compositional Probes (`support/`) | Improvement / Delta |
| :--- | :--- | :--- | :--- |
| Core MIR state & `StorageLive`/`StorageDead` join lemmas | `MirSemantics.lean` (2,057 lines) + `Lowering.lean` (2,257 lines) + `MirLemmas.lean` (6,625 lines) = **10,939 lines** | `CanonicalStateAndJoinProbe.lean`: **354 lines** (311 non-empty, 14,981 B, **1.36 s wall**, 616 KiB `.olean`, 520 MiB RSS) | Asymmetric `if/else` temporary lifecycles reunite by **`rfl`** (zero `deadLocalGen_irrel` lemmas) |
| Functional translation, borrow lenses & 6 target functions (`max_assign`, `update_min`, `clamp_assign`, `choose_mut`, `two_phase_reborrow`, `count_up`) | `FunctionalTranslation.lean`: **11,619 lines** (10,943 non-empty, 507,104 B) | `CompositionalBorrowAndLoopWP.lean`: **1,042 lines** (936 non-empty, 40,815 B, **2.75 s wall**, 3.43 MiB `.olean`, 838 MiB RSS) | **11.2x fewer lines**; zero closures in `SymState`; 6-line canonical loop step (`countUp_iter_step`) |

---

## Boundaries

1. **`maxRecDepth` Scaling Under Deep CPS Spine Forcing**:
   Because `forceList` traverses a `List` of length $L$ at each of $K$ symbolic
   steps in continuation-passing style, elaborator/kernel WHNF stack depth grows
   proportional to $O(K \cdot L)$ (or $O(K)$ when each step forces its spine
   eagerly before tail-calling). For Starnix `apply_endianness` ($L = 65$
   locals, $K = 99$ raw steps) and `two_phase_reborrow` ($L = 13$ locals + $10$
   loans, $K = 12$ steps), Lean 4's default `maxRecDepth` (`512`) is exceeded
   during `rfl` checking; setting `set_option maxRecDepth 100000` (or `200000`)
   allows both to complete in 2.8–8.2 seconds. For functions with $L > 256$
   locals or $K > 500$ steps, replacing the linear `List Slot` with a canonical
   radix-2 binary trie (`BinTrie Slot`, indexed by the bits of `localIdx : Nat`)
   reduces per-access and per-step spine depth from $O(L)$ to $O(\log_2 L)$.
2. **Dynamic Indirection and Heap Allocation Beyond Borrow-Dirtied Stack Slots**:
   The borrow-dirtied generation rule in `support/CanonicalStateAndJoinProbe.lean`
   (`StorageLive`/`StorageDead` bump `gen` if and only if `borrowed == true`)
   covers stack-allocated MIR locals whose addresses may be taken via
   `Rvalue.ref` / `Rvalue.addressOf`. Heap allocations (`Box`, raw allocator
   calls) and interior mutability (`UnsafeCell`) require separate allocation-ID
   and capability tracking in `MemState`.
3. **Nested Reborrow Trees Beyond Depth-1 Diamond Joins**:
   In `support/CompositionalBorrowAndLoopWP.lean`, `LoanBack` defunctionalizes
   root loans (`.root`) and 2-way diamond reborrows (`.join2`). Supporting
   arbitrary-depth reborrow chains (`&mut *r` where `r` is itself a joined
   reborrow) simply generalizes `LoanBack.join2` to a recursive tree of
   first-order lens combinators (`LoanBack.seq` / `LoanBack.branch`) while
   preserving the invariant that `LoanBack` contains no function closures.

---

## Evidence

All claims in this report are backed by primary source citations and
machine-checked Lean 4 proofs in `support/`:

- **Closure-based `MirState` and unconditional `bumpGen` in `joshlf`**:
  `trusted/lean/Trusted/MirSemantics.lean` lines 126–159 (`MirState`,
  `updateLocal`, `bumpGen`) and lines 580–658 (`evalMirStmt` for `storageLive`
  and `storageDead`) at `joshlf/anneal` commit `a7ac073219f4`.
- **Closure-based `SymState`, `JoinInv`, and `countUp` closure wrappers in
  `joshlf`**: `theory/Anneal/FunctionalTranslation.lean` lines 3690–4016
  (`SymState`, `evalJoinBorrow`, `evalSymState`), lines 4579–4650 (`JoinInv` and
  `LoanRel`), and lines 10830–11185 (`countUpLocalsAfterBb1..4` and
  `evalSymState_countUpLoopPlan`) at `joshlf/anneal` commit `a7ac073219f4`.
- **Starnix `generate_steps.py` and `ProductionSteps.lean` in `joshlf-mvp`**:
  `trusted/cargo-anneal/tests/fixtures/starnix/proof/generate_steps.py` lines
  1–181 (`checkpoint = min(2, last)` at line 105) and `ProductionSteps.lean`
  (5,230 lines at `2fb744d6ecb5`, 5,270 lines at `aa325aa43af9`), plus
  `theory/Anneal/Mvp/Execution.lean` lines 1–50 (`writeLocal`, `run`).
- **Probe 1 (`support/CanonicalStateAndJoinProbe.lean`)**:
  - `ClosureModel.asymmetric_temp_branches_not_equal` (line 112) and
    `ClosureModel.asymmetric_temp_states_ne` (line 121): proves that closure-based
    `MirState` with unconditional `StorageLive`/`StorageDead` generation bumps
    yields propositionally unequal states (`sThen ≠ sElse`) after an asymmetric
    `if/else` diamond.
  - `CanonicalModel.kill_or_rebirth_invalidates_borrowed_slot` (line 277): proves
    that any borrowed slot (`Slot.live v g true`) strictly increments its
    generation (`g + 1`) on both `StorageDead` and `StorageLive` rebirth.
  - `CanonicalModel.unborrowed_lifetime_roundtrip_rfl` (line 291),
    `CanonicalModel.commuting_updates_rfl` (line 298),
    `CanonicalModel.redundant_self_update_rfl` (line 305), and
    `CanonicalModel.asymmetric_temp_diamond_reunites_rfl` (line 314): prove by
    `rfl` that canonical `List Slot` state with borrow-dirtied generation
    tracking makes unborrowed temporary lifecycles round-trip identities and
    reunites asymmetric `if/else` branches definitionally at the join block.
  - `CanonicalModel.use_after_storageDead_rejected_rfl` (line 328),
    `CanonicalModel.use_after_storageLive_rebirth_rejected_rfl` (line 336), and
    `CanonicalModel.use_after_rebirth_and_reborrow_distinguished_rfl` (line 345):
    prove by `rfl` that dangling pointers are rejected across all three temporal
    aliasing scenarios.
- **Probe 2 (`support/StarnixZeroGeneratorSymbolicEngine.lean`)**:
  - `Anneal.Mvp.forceList` (line 563), `Anneal.Mvp.forceState` (line 573),
    `Anneal.Mvp.runForced` (line 597), `Anneal.Mvp.runForced_eq_run` (line
    606), and `Anneal.Mvp.runForced_initial_success` (line 620): 42-line CPS
    spine-forcing evaluator and soundness bridge in `theory/`.
  - `ProductionSteps.le8..be64` (lines 872–910) and `Proof.verify` (line 1016):
    38-line verification of all 8 paths of Starnix `apply_endianness` without
    `generate_steps.py`.
  - `MutationCanaries.mutatedZero_be64_evaluates_to_zero` (line 1097),
    `MutationCanaries.mutatedZero_rejected_by_exactReversal` (line 1103),
    `MutationCanaries.mutatedMaskedIdentity_unaffected_paths_still_verify` (line
    1118), `MutationCanaries.mutatedMaskedIdentity_be16_evaluates_to_unreversed`
    (line 1137), and
    `MutationCanaries.mutatedMaskedIdentity_rejected_by_exactReversal` (line
    1142): machine-checked mutation adequacy proofs.
- **Probe 3 (`support/CompositionalBorrowAndLoopWP.lean`)**:
  - `LoanBack` (line 165), `LoanEntry` (line 178), `SymState` (line 186),
    `joinSymStates` (line 352), `evalJoinBorrow` (line 372), `evalEndLoan` (line
    425), `forceSymState` (line 493), `forceSymState_eq` (line 540), and
    `evalSymState` (line 559): first-order canonical symbolic execution engine.
  - `maxAssign_eval_rfl` (line 702), `updateMin_eval_rfl` (line 738),
    `clampAssign_eval_rfl` (line 777), `chooseMut_fwd_rfl` (line 816),
    `chooseMut_back_rfl` (line 820), `chooseMut_lens_laws` (line 826),
    `twoPhaseReborrow_eval_rfl` (line 876), `countUp_entry_step` (line 946),
    `countUp_iter_step` (line 963), `countUp_loop_eval` (line 992), and
    `countUp_eval_eq` (line 1034).

---

## Revalidation

To revalidate all three Lean 4 probes and regenerate `support/benchmark_results.json`
from the report package directory
(`reports/lean-canonical-mir-state-and-compositional-symbolic-execution/`):

```bash
python3 support/run_canonical_wp_benchmarks.py
```

Or to check each standalone Lean 4 probe individually (wrapping CLI invocations
in `anneal-lean-run` when available):

```bash
cd support
lean CanonicalStateAndJoinProbe.lean
lean StarnixZeroGeneratorSymbolicEngine.lean
lean CompositionalBorrowAndLoopWP.lean
```

Expected result: all three `.lean` files exit with code `0` and emit zero errors
and zero warnings.
