import Lean

namespace ObligationPilot

structure State where
  live : Bool
  initialized : Bool
  readable : Bool
  writable : Bool
  aligned : Bool
  value : Nat
  deriving DecidableEq

inductive Op where
  | load
  | store (value : Nat)
  | storageLive
  | storageDead
  | assertion (condition : Bool)
  deriving DecidableEq

inductive Outcome where
  | returned (state : State)
  | panic
  | ub
  deriving DecidableEq

-- A fixed one-cell u32-like primitive fragment, with explicit resource flags.
-- These flags need a source-memory interpretation; this file does not import Rust.
def guard : Op → State → Bool
  | .load, s => s.live && s.initialized && s.readable && s.aligned && decide (s.value < 4294967296)
  | .store v, s => s.live && s.writable && s.aligned && decide (v < 4294967296)
  | _, _ => true

def next : Op → State → Option State
  | .store v, s => some { s with initialized := true, value := v }
  | .storageLive, s => some { s with live := true, initialized := false }
  | .storageDead, s => some { s with live := false, initialized := false }
  | .assertion true, s => some s
  | .assertion false, _ => none
  | .load, s => some s

def step (op : Op) (s : State) : Outcome :=
  if guard op s then
    match next op s with
    | some t => .returned t
    | none => .panic
  else .ub

def run : List Op → State → Outcome
  | [], s => .returned s
  | op :: rest, s =>
    match step op s with
    | .returned t => run rest t
    | .panic => .panic
    | .ub => .ub

def Safe : Outcome → Prop
  | .ub => False
  | _ => True

-- Logical obligations traverse the complete independently selected instruction list.
-- Panic is allowed and terminates this execution, so no later instruction is required.
def generate : List Op → State → Prop
  | [], _ => True
  | op :: rest, s => guard op s = true ∧
    match next op s with
    | some t => generate rest t
    | none => True

theorem generated_exact (ops : List Op) (s : State) :
    generate ops s ↔ Safe (run ops s) := by
  induction ops generalizing s with
  | nil => simp [generate, run, Safe]
  | cons op rest ih =>
    cases hg : guard op s <;> cases hn : next op s <;>
      simp [generate, run, step, hg, hn, Safe, ih]

theorem aggregate (original proposed : List Op) (Domain : State → Prop)
    (binding : proposed = original)
    (discharged : ∀ s, Domain s → generate proposed s) :
    ∀ s, Domain s → Safe (run original s) := by
  subst proposed
  intro s hs
  exact (generated_exact original s).mp (discharged s hs)

def Entry (s : State) : Prop :=
  s.live = true ∧ s.readable = true ∧ s.writable = true ∧ s.aligned = true

theorem init_then_read (s : State) (h : Entry s) :
    Safe (run [.store 7, .load] s) := by
  apply (generated_exact _ _).mp
  rcases h with ⟨hl, hr, hw, ha⟩
  simp [generate, guard, next, hl, hr, hw, ha]

def uninitialized : State := ⟨true, false, true, true, true, 0⟩

theorem omitted_operation_is_material :
    generate [] uninitialized ∧ ¬ Safe (run [.load] uninitialized) := by
  simp [generate, Safe, run, step, guard, next, uninitialized]

theorem ignored_storage_is_material :
    Safe (run [.store 7, .load] uninitialized) ∧
    ¬ Safe (run [.store 7, .storageDead, .load] uninitialized) := by
  simp [generate, Safe, run, step, guard, next, uninitialized]

theorem panic_is_not_ub :
    Safe (run [.assertion false, .load] uninitialized) ∧
    ¬ Safe (run [.load, .assertion false] uninitialized) := by
  simp [generate, Safe, run, step, guard, next, uninitialized]

#print axioms generated_exact
#print axioms aggregate
#print axioms init_then_read
#print axioms omitted_operation_is_material
#print axioms ignored_storage_is_material
#print axioms panic_is_not_ub
end ObligationPilot
