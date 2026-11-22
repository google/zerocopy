/-
Toy matches: tests, guards, arms, the lowered decision procedure, exhaustiveness and the
freezing disciplines.

These are definitions of a toy model. `runMatch` is meant to capture the observable behaviour
of a decision tree produced by match lowering: tests are tried arm by arm, a switch on a place
reads that place's head at most once and later arms reuse the recorded result, guards run
between tests, and failing every arm reaches `Unreachable`. Deref-pattern tests go through the
box at their scrutinee each time they are evaluated (the deref result is not shared across a
guard). These are not rustc's definitions.
-/
import ToyMatchGuard.Places

namespace Toy.MatchGuard

/-- A test node of the lowered match.
* `switch p h`: switch on the head at place `p`; succeeds when it is `h`.
* `derefSwitch p q h`: a deref-pattern test: the value at the deref-pattern scrutinee `p` must
  be a box, and the head at place `q` inside its pointee must be `h`. The pointee is not a
  place that a borrow check sees; only `p` is. -/
inductive Test where
  | switch (p : Place) (h : Head)
  | derefSwitch (p : Place) (q : Place) (h : Head)

/-- The head that a deref-pattern test reads: through the box at `p`, at `q` inside it. -/
def derefHead (v : Val) (p q : Place) : Option Head :=
  match lookup v p with
  | some (.box c) => headAt c q
  | _ => none

/-- Direct evaluation of a test against a value (no recorded results). -/
def Test.holds (v : Val) : Test → Bool
  | .switch p h => decide (headAt v p = some h)
  | .derefSwitch p q h => decide (derefHead v p q = some h)

/-- Recorded switch results: a place and the head that was read there. -/
abbrev Memo := List (Place × Option Head)

/-- The most recent recorded result for a place, if any. -/
def memoFind : Memo → Place → Option (Option Head)
  | [], _ => none
  | (q, r) :: m, p => if q = p then some r else memoFind m p

/-- Lowered evaluation of one test: a switch reuses a recorded result for its place if there is
one, and otherwise reads the place and records the result; a deref-pattern test always reads
through the box. -/
def evalTest (v : Val) (m : Memo) : Test → Bool × Memo
  | .switch p h =>
    match memoFind m p with
    | some r => (decide (r = some h), m)
    | none => (decide (headAt v p = some h), (p, headAt v p) :: m)
  | .derefSwitch p q h => (decide (derefHead v p q = some h), m)

/-- Lowered evaluation of an arm's tests, left to right, stopping at the first failure. -/
def evalTests (v : Val) : Memo → List Test → Bool × Memo
  | m, [] => (true, m)
  | m, t :: ts =>
    match evalTest v m t with
    | (true, m') => evalTests v m' ts
    | (false, m') => (false, m')

/-- Binding environments: a binding name and the value read at its place (by-value snapshot
when the arm's tests succeed). -/
abbrev Env := List (Nat × Option Val)

/-- A guard: a list of writes to places of the scrutinee, executed left to right (each written
value may depend on the bindings and on the memory just before that write), followed by a
condition that may read the bindings and the memory after the writes. -/
structure Guard where
  writes : List (Place × (Env → Val → Val))
  cond : Env → Val → Bool

/-- Runs a guard's writes left to right with bindings `env`. -/
def runWrites (env : Env) : Val → List (Place × (Env → Val → Val)) → Val
  | v, [] => v
  | v, (w, f) :: ws => runWrites env (writeOrSkip v w (f env v)) ws

/-- A match arm: the tests of its (or-free) pattern, its bindings, and an optional guard. -/
structure Arm where
  tests : List Test
  binds : List (Nat × Place) := []
  guard : Option Guard := none

/-- The bindings of an arm, read from memory `v`. -/
def bindEnv (v : Val) (bs : List (Nat × Place)) : Env := bs.map (fun xp => (xp.1, lookup v xp.2))

/-- The result of a lowered match: the selected arm (with its bindings and the memory after its
guard), or `Unreachable` (with the memory at that point), which is undefined behaviour. -/
inductive Outcome where
  | arm (index : Nat) (env : Env) (mem : Val)
  | unreachable (mem : Val)

/-- Whether the lowered match reached `Unreachable`. -/
def Outcome.reachesUnreachable : Outcome → Bool
  | .unreachable _ => true
  | .arm .. => false

/-- The index of the selected arm, if any. -/
def Outcome.selected : Outcome → Option Nat
  | .unreachable _ => none
  | .arm i _ _ => some i

/-- The lowered decision procedure from memory `v`, recorded results `m`, arm index `i`. -/
def runArms (v : Val) (m : Memo) (i : Nat) : List Arm → Outcome
  | [] => .unreachable v
  | a :: as =>
    match evalTests v m a.tests with
    | (false, m') => runArms v m' (i + 1) as
    | (true, m') =>
      match a.guard with
      | none => .arm i (bindEnv v a.binds) v
      | some g =>
        let env := bindEnv v a.binds
        if g.cond env (runWrites env v g.writes) then .arm i env (runWrites env v g.writes)
        else runArms (runWrites env v g.writes) m' (i + 1) as

/-- The lowered execution of a match on scrutinee memory `v`. -/
def runMatch (arms : List Arm) (v : Val) : Outcome := runArms v [] 0 arms

/-- Direct matching of an arm's pattern against a value (guards ignored). -/
def Arm.matchesDirect (v : Val) (a : Arm) : Bool := a.tests.all (Test.holds v)

/-- Type-level exhaustiveness relative to a value domain `Dom` (the values of the scrutinee
type): every value in `Dom` is matched directly by some arm without a guard. Guarded arms do
not count, as in Rust's exhaustiveness check. -/
def Exhaustive (Dom : Val → Prop) (arms : List Arm) : Prop :=
  ∀ v, Dom v → ∃ a ∈ arms, a.guard = none ∧ a.matchesDirect v = true

/-- The place a switch test reads (`none` for a deref-pattern test). -/
def Test.switchPlace? : Test → Option Place
  | .switch p _ => some p
  | .derefSwitch .. => none

/-- The deref-pattern scrutinee of a deref-pattern test (`none` for a switch test). -/
def Test.derefScrutinee? : Test → Option Place
  | .switch .. => none
  | .derefSwitch p _ _ => some p

/-- The places an arm's switch tests read. -/
def Arm.switchPlaces (a : Arm) : List Place := a.tests.filterMap Test.switchPlace?

/-- The deref-pattern scrutinees of an arm's deref-pattern tests. -/
def Arm.derefScrutinees (a : Arm) : List Place := a.tests.filterMap Test.derefScrutinee?

/-- The places an arm's guard writes (empty for an unguarded arm). -/
def Arm.guardWrites (a : Arm) : List Place :=
  match a.guard with
  | none => []
  | some g => g.writes.map Prod.fst

/-- Whether no arm has a deref-pattern test. -/
def NoDerefPatterns (arms : List Arm) : Prop := ∀ a ∈ arms, a.derefScrutinees = []

/-- Shallow conflict of a write at `w` with a shallow freeze of `p`: `w` is `p` or a prefix of
`p`. Writes strictly inside `p` do not conflict. -/
def ShallowConflict (w p : Place) : Prop := w <+: p

/-- Deep conflict of a write at `w` with a deep freeze of `p`: the places overlap (one is a
prefix of the other), so the write is to `p`, to a prefix of `p`, or to anything inside `p`. -/
def DeepConflict (w p : Place) : Prop := w <+: p ∨ p <+: w

instance (w p : Place) : Decidable (ShallowConflict w p) := by
  unfold ShallowConflict; infer_instance
instance (w p : Place) : Decidable (DeepConflict w p) := by
  unfold DeepConflict; infer_instance

/-- Static shallow freezing (one fake-borrow set for the whole match): no guard write of any arm
shallow-conflicts with any place switched on by any arm. -/
def ShallowFrozenAll (arms : List Arm) : Prop :=
  ∀ a ∈ arms, ∀ w ∈ a.guardWrites, ∀ b ∈ arms, ∀ p ∈ b.switchPlaces, ¬ ShallowConflict w p

/-- Static deep freezing of deref-pattern scrutinees: no guard write of any arm deep-conflicts
with any deref-pattern scrutinee of any arm. -/
def DeepFrozenAll (arms : List Arm) : Prop :=
  ∀ a ∈ arms, ∀ w ∈ a.guardWrites, ∀ b ∈ arms, ∀ p ∈ b.derefScrutinees, ¬ DeepConflict w p

/-- Static shallow freezing applied to deref-pattern scrutinees (used to show that shallow
freezing of a deref-pattern scrutinee is not enough). -/
def ShallowFrozenDerefAll (arms : List Arm) : Prop :=
  ∀ a ∈ arms, ∀ w ∈ a.guardWrites, ∀ b ∈ arms, ∀ p ∈ b.derefScrutinees, ¬ ShallowConflict w p

/-- Static deep freezing applied to switched places (used to compare with shallow freezing). -/
def DeepFrozenSwitchAll (arms : List Arm) : Prop :=
  ∀ a ∈ arms, ∀ w ∈ a.guardWrites, ∀ b ∈ arms, ∀ p ∈ b.switchPlaces, ¬ DeepConflict w p

/-- Per-guard shallow freezing, given the switched places `seen` of the arms before: the guard
of each arm must not shallow-conflict with a place switched on by that arm or by an earlier
arm. Places switched on only by later arms are not frozen. -/
def ShallowFrozenBeforeAux : List Place → List Arm → Prop
  | _, [] => True
  | seen, a :: as =>
    (∀ w ∈ a.guardWrites, ∀ p ∈ seen ++ a.switchPlaces, ¬ ShallowConflict w p) ∧
      ShallowFrozenBeforeAux (seen ++ a.switchPlaces) as

/-- Per-guard deep freezing of deref-pattern scrutinees of that arm and of earlier arms. -/
def DeepFrozenBeforeAux : List Place → List Arm → Prop
  | _, [] => True
  | seen, a :: as =>
    (∀ w ∈ a.guardWrites, ∀ p ∈ seen ++ a.derefScrutinees, ¬ DeepConflict w p) ∧
      DeepFrozenBeforeAux (seen ++ a.derefScrutinees) as

/-- Per-guard shallow freezing of the places switched on by the guard's arm and earlier arms. -/
def ShallowFrozenBefore (arms : List Arm) : Prop := ShallowFrozenBeforeAux [] arms

/-- Per-guard deep freezing of the deref-pattern scrutinees of the guard's arm and earlier arms. -/
def DeepFrozenBefore (arms : List Arm) : Prop := DeepFrozenBeforeAux [] arms

/-- Guards are well-typed: for every guarded arm `a` and every memory `v` in `Dom` on which `a`
matches directly (`a.matchesDirect v = true`), running the guard's writes from `v`, with the arm's
bindings read from `v`, gives a memory in `Dom`. The condition is required from every such `v`,
whether or not the lowered execution can reach that guard with memory `v`; it is not required
from memories on which the arm does not match. -/
def GuardsPreserveDom (Dom : Val → Prop) (arms : List Arm) : Prop :=
  ∀ a ∈ arms, ∀ g, a.guard = some g → ∀ v, Dom v → a.matchesDirect v = true →
    Dom (runWrites (bindEnv v a.binds) v g.writes)

instance decShallowFrozenBeforeAux : (seen : List Place) → (as : List Arm) →
    Decidable (ShallowFrozenBeforeAux seen as)
  | _, [] => isTrue trivial
  | seen, a :: as => by
    unfold ShallowFrozenBeforeAux
    have := decShallowFrozenBeforeAux (seen ++ a.switchPlaces) as
    infer_instance

instance decDeepFrozenBeforeAux : (seen : List Place) → (as : List Arm) →
    Decidable (DeepFrozenBeforeAux seen as)
  | _, [] => isTrue trivial
  | seen, a :: as => by
    unfold DeepFrozenBeforeAux
    have := decDeepFrozenBeforeAux (seen ++ a.derefScrutinees) as
    infer_instance

instance (arms : List Arm) : Decidable (ShallowFrozenAll arms) := by
  unfold ShallowFrozenAll; infer_instance
instance (arms : List Arm) : Decidable (DeepFrozenAll arms) := by
  unfold DeepFrozenAll; infer_instance
instance (arms : List Arm) : Decidable (ShallowFrozenDerefAll arms) := by
  unfold ShallowFrozenDerefAll; infer_instance
instance (arms : List Arm) : Decidable (DeepFrozenSwitchAll arms) := by
  unfold DeepFrozenSwitchAll; infer_instance
instance (arms : List Arm) : Decidable (ShallowFrozenBefore arms) := by
  unfold ShallowFrozenBefore; infer_instance
instance (arms : List Arm) : Decidable (DeepFrozenBefore arms) := by
  unfold DeepFrozenBefore; infer_instance
instance (arms : List Arm) : Decidable (NoDerefPatterns arms) := by
  unfold NoDerefPatterns; infer_instance

end Toy.MatchGuard
