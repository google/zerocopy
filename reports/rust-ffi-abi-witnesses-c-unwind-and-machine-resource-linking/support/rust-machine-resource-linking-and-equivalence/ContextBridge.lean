import Std

namespace AnnealAssembly

theorem context_replacement
    {Rust Machine Observation : Type}
    (rel : Rust → Machine → Prop)
    (rustStep : Rust → Rust → Prop) (machineStep : Machine → Machine → Prop)
    (observeRust : Rust → Observation) (observeMachine : Machine → Observation)
    (reflect : ∀ r m m', rel r m → machineStep m m' →
      ∃ r', rustStep r r' ∧ rel r' m')
    (observations : ∀ r m, rel r m → observeRust r = observeMachine m)
    (r : Rust) (m m' : Machine) (start : rel r m) (run : machineStep m m') :
    ∃ r', rustStep r r' ∧ observeRust r' = observeMachine m' := by
  obtain ⟨r', hr, hrel⟩ := reflect r m m' start run
  exact ⟨r', hr, observations r' m' hrel⟩

theorem exact_spec_equivalence
    {Input Result : Type} (spec rust asm : Input → Result)
    (hr : ∀ x, rust x = spec x) (ha : ∀ x, asm x = spec x) :
    ∀ x, rust x = asm x := by
  intro x
  exact (hr x).trans (ha x).symm

theorem loose_spec_is_not_equivalence :
    (0 : Nat) ≤ 1 ∧ (0 : Nat) ≤ 2 ∧ (1 : Nat) ≠ 2 := by decide

structure ResourceState where
  value : Nat
  borrowLive : Bool
  deriving DecidableEq

def before : ResourceState := ⟨7, true⟩
def afterBad : ResourceState := ⟨7, false⟩

theorem value_equivalence_is_not_context_safety :
    before.value = afterBad.value ∧ before.borrowLive ≠ afterBad.borrowLive := by decide

inductive Outcome where
  | returnValue (n : Nat)
  | panic
  | diverge
  deriving DecidableEq

def wrap8 (n : Nat) : Outcome := .returnValue (n % 256)
def checked8 (n : Nat) : Outcome := if n < 256 then .returnValue n else .panic

theorem overflow_policy_changes_behavior : checked8 256 ≠ wrap8 256 := by decide

def addressedTrace (secret : Bool) : List Nat := if secret then [1] else [0]
def fixedTrace (_secret : Bool) : List Nat := [0]

theorem fixed_trace_noninterference (a b : Bool) : fixedTrace a = fixedTrace b := rfl
theorem same_result_can_leak :
    (7 : Nat) = 7 ∧ addressedTrace false ≠ addressedTrace true := by decide

#print axioms context_replacement
#print axioms exact_spec_equivalence
#print axioms loose_spec_is_not_equivalence
#print axioms value_equivalence_is_not_context_safety
#print axioms overflow_policy_changes_behavior
#print axioms fixed_trace_noninterference
#print axioms same_result_can_leak

end AnnealAssembly
