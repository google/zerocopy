import ToyTwoPhase.Decide

/-!
# Reference aliasing semantics (ground truth)

A state machine for the permission of `r`, in the style of Tree Borrows' `Reserved` /
`Unique` (formerly `Active`) / `Frozen` / `Disabled` permissions, plus, for each shared
reference `s`, whether it has been created and whether a write through `r` happened after its
creation.

* `reserve`: `r` becomes `reserved` (a new loan).
* `activate` (the first write through `r`, which starts the mutable phase): `reserved`/`active`
  → `active`, and, like `writeThrough`, it marks every created `s` dirty; `none` → no effect
  (there is no reservation to activate); `frozen`/`invalid` → UB.
* Foreign reads (`readX`, `borrowShared s`, `useShared s`): `active` → `frozen`; other
  permissions unchanged (a reservation tolerates foreign reads).
* `useShared s` is UB if a write through `r` (an activation or a `writeThrough`) happened after
  `s` was created. On an `s` that was never created it acts as a plain foreign read (programs
  are not required to create `s` before using it).
* Foreign write (`writeX`): `reserved`/`active`/`frozen` → `invalid`.
* `writeThrough`: allowed iff `active` (marks every created `s` dirty); UB if `frozen` or
  `invalid`; a safe halt if `none` or `reserved` (`r` does not yet hold a usable pointer: in
  the source language the reference is obtained from the activation, so such an
  execution stops, as `Option::unwrap` on `None` does).
* `endLoan`: `r` becomes `none`.

Safety: no run (walk from `entry`, along any edges) reaches UB.
-/

namespace Toy.TwoPhase

variable {n : Nat}

/-- Permission of the two-phase reference `r`. -/
inductive Perm | none | reserved | active | frozen | invalid
  deriving DecidableEq, Repr

/-- State of one shared reference. -/
structure SSt where
  created : Bool
  dirty : Bool
  deriving DecidableEq, Repr

/-- Reference-semantics state. -/
structure RState where
  perm : Perm
  sh0 : SSt
  sh1 : SSt
  deriving DecidableEq, Repr

namespace RState

def sh (σ : RState) : SRef → SSt
  | .s0 => σ.sh0
  | .s1 => σ.sh1

def setSh (σ : RState) : SRef → SSt → RState
  | .s0, t => { σ with sh0 := t }
  | .s1, t => { σ with sh1 := t }

/-- Initial state: no loan, no shared reference created. -/
def init : RState := ⟨.none, ⟨false, false⟩, ⟨false, false⟩⟩

end RState

/-- Result of executing one node. -/
inductive Outcome
  | ok (σ : RState)
  | halt
  | ub
  deriving DecidableEq, Repr

/-- Effect of a foreign read on `r`'s permission. -/
def foreignRead : Perm → Perm
  | .active => .frozen
  | q => q

/-- Effect of a foreign write on `r`'s permission. -/
def foreignWrite : Perm → Perm
  | .reserved | .active | .frozen => .invalid
  | q => q

def SSt.markWrite (t : SSt) : SSt := { t with dirty := t.dirty || t.created }

/-- One step of the reference semantics. -/
def exec : Op → RState → Outcome
  | .reserve, σ => .ok { σ with perm := .reserved }
  | .activate, σ =>
    match σ.perm with
    | .reserved | .active =>
      .ok { σ with perm := .active, sh0 := σ.sh0.markWrite, sh1 := σ.sh1.markWrite }
    | .none => .ok σ
    | .frozen | .invalid => .ub
  | .readX, σ => .ok { σ with perm := foreignRead σ.perm }
  | .borrowShared s, σ => .ok (({ σ with perm := foreignRead σ.perm } : RState).setSh s ⟨true, false⟩)
  | .useShared s, σ => if (σ.sh s).dirty then .ub else .ok { σ with perm := foreignRead σ.perm }
  | .writeX, σ => .ok { σ with perm := foreignWrite σ.perm }
  | .writeThrough, σ =>
    match σ.perm with
    | .active => .ok { σ with sh0 := σ.sh0.markWrite, sh1 := σ.sh1.markWrite }
    | .none | .reserved => .halt
    | .frozen | .invalid => .ub
  | .endLoan, σ => .ok { σ with perm := .none }
  | .nop, σ => .ok σ

/-- Execute the nodes of a list in order from state `σ`. -/
def run (p : Prog n) : RState → List (Fin n) → Outcome
  | σ, [] => .ok σ
  | σ, i :: rest =>
    match exec (p.op i) σ with
    | .ok σ' => run p σ' rest
    | .halt => .halt
    | .ub => .ub

/-- `Safe p`: no walk from `entry` (along normal and unwinding edges) reaches UB. -/
def Safe (p : Prog n) : Prop :=
  ∀ π : List (Fin n), IsWalk p.edges π → π.head? = some p.entry → run p RState.init π ≠ .ub

/-- `ReachesUB p π`: `π` is a walk from `entry` whose execution reaches UB. -/
def ReachesUB (p : Prog n) (π : List (Fin n)) : Prop :=
  IsWalk p.edges π ∧ π.head? = some p.entry ∧ run p RState.init π = .ub

instance (p : Prog n) (π : List (Fin n)) : Decidable (ReachesUB p π) := by
  unfold ReachesUB; infer_instance

theorem not_safe_of_reachesUB {p : Prog n} {π : List (Fin n)} (h : ReachesUB p π) :
    ¬ Safe p :=
  fun hs => hs π h.1 h.2.1 h.2.2

/-! ## Safety certificates (inductive invariants over node × state) -/

/-- `certOK p S`: every pair `(x, σ)` in `S` executes without UB, and for every `.ok` step from
such a pair, the pair of each successor along `p.edges` (normal or unwinding) and the new state
is again in `S`. -/
def certOK (p : Prog n) (S : List (Fin n × RState)) : Bool :=
  S.all fun q =>
    match exec (p.op q.1) q.2 with
    | .ok σ' => (p.edges q.1).all fun y => S.contains (y, σ')
    | .halt => true
    | .ub => false

theorem run_ne_ub_of_cert {p : Prog n} {S : List (Fin n × RState)} (hS : certOK p S = true) :
    ∀ (π : List (Fin n)) (x : Fin n) (σ : RState), IsWalk p.edges (x :: π) → (x, σ) ∈ S →
      run p σ (x :: π) ≠ .ub := by
  intro π
  induction π with
  | nil =>
    intro x σ _ hx
    have h := List.all_eq_true.1 hS _ hx
    simp only [run]
    revert h
    cases exec (p.op x) σ <;> simp
  | cons y t ih =>
    intro x σ hw hx
    have h := List.all_eq_true.1 hS _ hx
    simp only [run]
    revert h
    cases hex : exec (p.op x) σ with
    | ok σ' =>
      intro h
      simp only at h
      have hy : (y, σ') ∈ S := by
        have := List.all_eq_true.1 h y hw.1
        simpa using this
      exact ih y σ' hw.2 hy
    | halt => simp
    | ub => simp

/-- A certificate containing `(entry, init)` proves safety. -/
theorem safe_of_cert {p : Prog n} (S : List (Fin n × RState)) (hS : certOK p S = true)
    (hinit : (p.entry, RState.init) ∈ S) : Safe p := by
  intro π hw hh
  cases π with
  | nil => exact absurd hw (fun h => h)
  | cons x t =>
    simp at hh; subst hh
    exact run_ne_ub_of_cert hS t p.entry RState.init hw hinit

/-- Breadth-first exploration of reachable node × state pairs (used to compute certificates;
its correctness is not needed, since `certOK` is checked). -/
def explore (p : Prog n) : Nat → List (Fin n × RState) → List (Fin n × RState)
  | 0, S => S
  | k + 1, S =>
    let new := S.flatMap fun q =>
      match exec (p.op q.1) q.2 with
      | .ok σ' => (p.edges q.1).map fun y => (y, σ')
      | _ => []
    explore p k (new.foldl (fun acc q => if acc.contains q then acc else acc ++ [q]) S)

end Toy.TwoPhase
