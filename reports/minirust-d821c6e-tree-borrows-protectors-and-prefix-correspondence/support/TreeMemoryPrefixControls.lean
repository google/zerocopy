import AnnealResearch.TreeMemoryClient
import AnnealResearch.TreeGeometryControls

/-!
Enabled infinite internal steps and explicit terminal UB discriminate the prefix
observer from termination-conditional safety. A primitive counts as one client
transition; this is not a Rust internal-step, timing or fairness theorem. The
release failure fixture is shape-admitted, without a reachability claim.
-/
namespace AnnealResearch.TreeMemoryPrefixControls

open TreeMemoryClient

def loop : Controller Nat := fun control => .internal (control + 1)

theorem floop_prefix (count control : Nat) (memory : TreeFactoredMemory.State) :
    fIterate loop count (.running control memory) = some (.running (control + count) memory) := by
  induction count generalizing control with
  | zero => rfl
  | succ count ih =>
      change fIterate loop count (.running (control + 1) memory) =
        some (.running (control + (count + 1)) memory)
      rw [ih]
      simp [Nat.add_comm, Nat.add_left_comm]

theorem rloop_prefix (count control : Nat) (memory : TreeMemory.State) :
    rIterate loop count (.running control memory) = some (.running (control + count) memory) := by
  induction count generalizing control with
  | zero => rfl
  | succ count ih =>
      change rIterate loop count (.running (control + 1) memory) =
        some (.running (control + (count + 1)) memory)
      rw [ih]
      simp [Nat.add_comm, Nat.add_left_comm]

theorem floop_NoUB (control : Nat) (memory : TreeFactoredMemory.State) :
    FNoUB loop (.running control memory) := by
  intro count reached found
  rw [floop_prefix] at found
  cases found
  exact False.elim

theorem rloop_NoUB (control : Nat) (memory : TreeMemory.State) :
    RNoUB loop (.running control memory) := by
  intro count reached found
  rw [rloop_prefix] at found
  cases found
  exact False.elim

def failing : Controller Unit := fun _ => .call (.release (0, [0])) (fun _ => ())
def initial : FConfig Unit := .running () TreeMemoryPairing.liveFailure
def failed : FConfig Unit :=
  .ub () (.tree .unprotectedLocalWriteFrozen) TreeGeometryControls.changedState

theorem failed_step : fStep failing initial = some failed := by
  simp only [fStep, failing, initial, fDispatch, TreeGeometryControls.actual_release_UB,
    fMap, fResume, failed]

theorem failed_prefix : fIterate failing 1 initial = some failed := by
  change (fStep failing initial).bind (fun next => some next) = some failed
  rw [failed_step]
  rfl

theorem failed_not_NoUB : ¬ FNoUB failing initial := by
  intro safe
  exact safe 1 failed failed_prefix (by trivial)

theorem failed_no_resumption (count : Nat) :
    fIterate failing (count + 1) failed = none :=
  iterate_no_successor (fStep failing) failed count rfl

theorem failed_later_prefix_absent (count : Nat) :
    fIterate failing (count + 2) initial = none := by
  change (fStep failing initial).bind
    (fun next => iterate (fStep failing) (count + 1) next) = none
  rw [failed_step]
  exact failed_no_resumption count

/-- This unsafe client has no normally finished horizon; safety still rejects it. -/
theorem failed_never_finishes (count : Nat) (control : Unit) (result : Nat)
    (memory : TreeFactoredMemory.State) :
    fIterate failing count initial ≠ some (.finished control result memory) := by
  cases count with
  | zero => simp [fIterate, iterate, initial]
  | succ count =>
      cases count with
      | zero => rw [failed_prefix]; simp [failed]
      | succ count =>
          rw [failed_later_prefix_absent]
          simp

theorem failed_retains_changed_memory :
    failed.memory = TreeGeometryControls.changedState ∧
    failed.memory ≠ initial.memory := ⟨rfl, TreeGeometryControls.changed_state⟩

theorem failed_retains_domain : ConfigWellSized failed := TreeGeometryControls.changed_sized

#print axioms floop_prefix
#print axioms rloop_prefix
#print axioms floop_NoUB
#print axioms rloop_NoUB
#print axioms failed_step
#print axioms failed_prefix
#print axioms failed_not_NoUB
#print axioms failed_no_resumption
#print axioms failed_later_prefix_absent
#print axioms failed_never_finishes
#print axioms failed_retains_changed_memory
#print axioms failed_retains_domain

end AnnealResearch.TreeMemoryPrefixControls
