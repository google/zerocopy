import Miri.Interpreter.Files

/-! Explicit Rc/Weak lifetime state for file descriptions, including references
held by pending callbacks. Table slot counts alone never determine liveness. -/
namespace Miri.Interpreter.FileOwnership
open Files
structure Entry (D : Type) where
  ref : Files.Ref D
  strong : Nat
structure Registry (D : Type) where
  entries : Array (Entry D) := #[]

def register (state : Registry D) (ref : Files.Ref D) : Except StepError (Registry D) := do
  if state.entries.any (·.ref.id == ref.id) then throw (.invalidProgram "duplicate live file description ID")
  return { entries := state.entries.push ⟨ref,1⟩ }

def retain (state : Registry D) (id : FdId) (referenceBudget : Nat) :
    Except StepError (Registry D × Files.Ref D) := do
  let matching := state.entries.filter (·.ref.id == id)
  if matching.size != 1 then throw (.invalidProgram "retaining absent/ambiguous file description")
  let some entry := matching[0]? | throw (.invalidProgram "missing file description")
  if entry.strong == 0 then throw (.invalidProgram "retaining closed file description")
  if entry.strong + 1 >= referenceBudget then throw (.resourceExhaustion "file-description reference budget exhausted")
  let entries := state.entries.map fun old => if old.ref.id == id then { old with strong := old.strong + 1 } else old
  return (⟨entries⟩,entry.ref)

/-- Last release returns the real payload for destructor/readiness cleanup.
The runtime must execute that cleanup; this function does not fake host close. -/
def release (state : Registry D) (id : FdId) : Except StepError (Registry D × Option D) := do
  let matching := state.entries.filter (·.ref.id == id)
  if matching.size != 1 then throw (.invalidProgram "releasing absent/ambiguous file description")
  let some entry := matching[0]? | throw (.invalidProgram "missing file description")
  if entry.strong == 0 then throw (.invalidProgram "file description double release")
  if entry.strong == 1 then
    return (⟨state.entries.filter (·.ref.id != id)⟩,some entry.ref.value)
  return (⟨state.entries.map fun old => if old.ref.id == id then { old with strong := old.strong - 1 } else old⟩,none)

def upgrade (state : Registry D) (weak : Files.WeakRef) (referenceBudget : Nat) :
    Except StepError (Registry D × Option (Files.Ref D)) := do
  if !(state.entries.any (fun entry => entry.ref.id == weak.id && entry.strong > 0)) then return (state,none)
  let (state,ref) ← retain state weak.id referenceBudget
  return (state,some ref)

def isClosed (state : Registry D) (weak : Files.WeakRef) : Bool :=
  !(state.entries.any fun entry => entry.ref.id == weak.id && entry.strong > 0)

def downgrade (ref : Files.Ref D) : Files.WeakRef := ⟨ref.id⟩
end Miri.Interpreter.FileOwnership
