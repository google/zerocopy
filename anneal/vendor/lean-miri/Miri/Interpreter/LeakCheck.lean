import Lean.Util.Profile
import Miri.Interpreter.MachineHooks
import Miri.Memory.MiriMemoryKind

/-! rustc interpret/memory.rs::take_leaked_allocations. This is deliberately
separate from provenance GC: only global-kind allocations and static_roots
seed leak reachability. Taking leaks is destructive and permits no continuation. -/
namespace Miri.Interpreter.LeakCheck
open Miri.Memory

def allocationIds (allocation : Allocation Provenance E) : Array AllocId := Id.run do
  let mut ids := #[]
  for (_,prov) in allocation.provenanceMap.ptrs do
    if let some id := prov.getAllocId then ids := ids.push id
  if let some fragments := allocation.provenanceMap.byteFragments then
    for (_,fragment) in fragments do
      if let some id := fragment.prov.getAllocId then ids := ids.push id
  return ids

private def walk (memory : MemoryState Provenance E MiriMemoryKind) :
    Nat → List AllocId → Array AllocId → Except StepError (Array AllocId)
  | _,[],seen => .ok seen
  | 0,_::_,_ => .error (.invalidProgram "leak reachability edge budget exhausted")
  | fuel+1,id::todo,seen =>
    if seen.contains id then walk memory fuel todo seen
    else
      let children := match memory.live.find? (·.1 == id) with
        | none => []
        | some (_,entry) => (allocationIds entry.allocation).toList
      walk memory fuel (children ++ todo) (seen.push id)

def mayLeak : MemoryKind MiriMemoryKind → Bool
  | .stack => false
  | .callerLocation => true
  | .machine kind => kind.mayLeak

/-- No access/retag/deallocation hook runs here. Source removes allocations
straight from alloc_map after reachability, retaining their bytes and extras in
the returned report. Missing unchanged compiler globals do not add edges. -/
def takeProfiled (profile : Lean.Options)
    (memory : MemoryState Provenance E MiriMemoryKind) (staticRoots : Array AllocId) :
    Except StepError (MemoryState Provenance E MiriMemoryKind ×
      Array (AllocId × LocalAllocation Provenance E MiriMemoryKind)) := do
  let globals := memory.live.filterMap fun (id,entry) =>
    if entry.kind == .machine .global then some id else none
  let todo := globals ++ staticRoots
  let edges := memory.live.foldl (fun count (_,entry) => count + (allocationIds entry.allocation).size) 0
  let todo := Lean.profileit
    s!"finalization.leak_walk.start.live_{memory.live.size}.roots_{todo.size}.edges_{edges}"
    profile (fun _ => todo)
  let reachable ← Lean.profileit "finalization.leak_walk.complete" profile fun _ =>
    walk memory (todo.size + edges) todo.toList #[]
  let leaked := memory.live.filter fun (id,entry) => !mayLeak entry.kind && !reachable.contains id
  return ({memory with live := memory.live.filter fun (id,_) => !(leaked.any (·.1 == id))},leaked)

def take (memory : MemoryState Provenance E MiriMemoryKind) (staticRoots : Array AllocId) :
    Except StepError (MemoryState Provenance E MiriMemoryKind ×
      Array (AllocId × LocalAllocation Provenance E MiriMemoryKind)) :=
  takeProfiled {} memory staticRoots

theorem takeProfiled_eq_take (profile : Lean.Options)
    (memory : MemoryState Provenance E MiriMemoryKind) (staticRoots : Array AllocId) :
    takeProfiled profile memory staticRoots = take memory staticRoots := by
  rfl
end Miri.Interpreter.LeakCheck
