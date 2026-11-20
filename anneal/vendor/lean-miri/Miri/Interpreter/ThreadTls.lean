import Miri.Interpreter.ThreadExit

/-! Pinned shims/tls.rs::TlsData (44-220). Keys retain actual typed runtime
pointers, full destructor instances and source spans. NULL normalization uses
source pointer addresses; no pointer is reconstructed from an opaque token. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev TlsKey := U128
structure TlsDestructor where
  fnInstance : CallInstance
  span : MIR.SpanRef
structure TlsKeyEntry (P : Type) where
  key : TlsKey
  data : Array (ThreadId × Pointer (Option P))
  destructor : Option TlsDestructor
structure ThreadAtexitEntry (P : Type) where
  fnInstance : CallInstance
  data : Scalar P
  span : MIR.SpanRef
structure ThreadTlsData (P : Type) where
  nextKey : TlsKey
  keys : Array (TlsKeyEntry P)
  threadAtexit : Array (ThreadId × Array (ThreadAtexitEntry P))

inductive ThreadTlsError where
  | keyCounterOverflow
  | keySpaceExhausted
  | duplicateKey
  | nonexistentKey (key : TlsKey)
  | destructorsRemain
  | size (error : SizeError)
  | nullDestructorData
  deriving Repr

/-- All source GC-relevant values, including atexit arguments. Function
instances and callback stages contain only compiler identities. -/
inductive TlsProvenanceRoot (P : Type) where
  | pointer (value : Pointer (Option P))
  | scalar (value : Scalar P)

namespace ThreadTlsData
/-- Exact source TlsData::default. Windows forbids allocating key zero. -/
def initial : ThreadTlsData P := ⟨BitVec.ofNat 128 1, #[], #[]⟩

def createKey (data : ThreadTlsData P) (destructor : Option TlsDestructor) (keySize : Size) :
    EStateM.Result ThreadTlsError (ThreadTlsData P) TlsKey := Id.run do
  let key := data.nextKey
  if key.toNat + 1 ≥ 2^128 then return .error .keyCounterOverflow data
  let next := { data with nextKey := BitVec.ofNat 128 (key.toNat + 1) }
  if data.keys.any (·.key == key) then return .error .duplicateKey next
  let next := { next with keys := next.keys.push ⟨key,#[],destructor⟩ }
  let maximum ← match keySize.unsignedIntMax with
    | .ok maximum => pure maximum
    | .error error => return .error (.size error) next
  if key.toNat > maximum.toNat then return .error .keySpaceExhausted next
  return .ok key next

def deleteKey (data : ThreadTlsData P) (key : TlsKey) :
    EStateM.Result ThreadTlsError (ThreadTlsData P) (TlsKeyEntry P) :=
  match data.keys.find? (·.key == key) with
  | none => .error (.nonexistentKey key) data
  | some entry => .ok entry { data with keys := data.keys.filter (·.key != key) }

def load (data : ThreadTlsData P) (key : TlsKey) (thread : ThreadId) : Except ThreadTlsError (Pointer (Option P)) := do
  let some entry := data.keys.find? (·.key == key) | throw (.nonexistentKey key)
  match entry.data.find? (·.1 == thread) with
  | some (_,pointer) => pure pointer
  | none => pure ⟨.ZERO,none⟩

def store (data : ThreadTlsData P) (key : TlsKey) (thread : ThreadId) (pointer : Pointer (Option P)) :
    Except ThreadTlsError (ThreadTlsData P) := do
  let some index := data.keys.findIdx? (·.key == key) | throw (.nonexistentKey key)
  let some entry := data.keys[index]? | throw (.nonexistentKey key)
  let values := entry.data.filter (·.1 != thread)
  let values := if pointer.offset.bytes == 0 then values else values.push (thread,pointer)
  pure { data with keys := data.keys.mapIdx fun i old => if i == index then { entry with data := values } else old }

def addThreadAtexit (data : ThreadTlsData P) (thread : ThreadId) (entry : ThreadAtexitEntry P) : ThreadTlsData P :=
  if data.threadAtexit.any (·.1 == thread) then
    { data with threadAtexit := data.threadAtexit.map fun (id,entries) =>
      (id, if id == thread then entries.push entry else entries) }
  else { data with threadAtexit := data.threadAtexit.push (thread,#[entry]) }

/-- Pthread keys are visited in BTreeMap numeric order and cleared before call.
The caller restarts from None after reaching the end of the current round. -/
def fetchDestructor (data : ThreadTlsData P) (lastKey : Option TlsKey) (thread : ThreadId) :
    Option (TlsDestructor × Pointer (Option P) × TlsKey) × ThreadTlsData P := Id.run do
  let eligible := data.keys.filter fun entry =>
    (lastKey.all (fun key => key.toNat < entry.key.toNat)) && entry.destructor.isSome && entry.data.any (·.1 == thread)
  let first := eligible.foldl (fun best entry => match best with
    | none => some entry
    | some previous => if entry.key.toNat < previous.key.toNat then some entry else best) none
  let some entry := first | return (none,data)
  let some destructor := entry.destructor | return (none,data)
  let some (_,pointer) := entry.data.find? (·.1 == thread) | return (none,data)
  let keys := data.keys.map fun item => if item.key == entry.key then
    { item with data := item.data.filter (·.1 != thread) } else item
  return (some (destructor,pointer,entry.key),{ data with keys := keys })

def popThreadAtexit (data : ThreadTlsData P) (thread : ThreadId) : Option (ThreadAtexitEntry P) × ThreadTlsData P :=
  match data.threadAtexit.findIdx? (·.1 == thread) with
  | none => (none,data)
  | some index =>
    match data.threadAtexit[index]? with
    | none => (none,data)
    | some (_,entries) =>
      match entries.back? with
      | none => (none,data)
      | some entry => (some entry,{ data with threadAtexit := data.threadAtexit.mapIdx fun i old => if i == index then (thread,entries.pop) else old })

def deleteAllThreadTls (data : ThreadTlsData P) (thread : ThreadId) :
    EStateM.Result ThreadTlsError (ThreadTlsData P) Unit :=
  let entries := data.threadAtexit.find? (·.1 == thread)
  let next := { data with
    keys := data.keys.map fun entry => { entry with data := entry.data.filter (·.1 != thread) },
    threadAtexit := data.threadAtexit.filter (·.1 != thread) }
  match entries with
  | some (_,dtors) => if dtors.isEmpty then .ok () next else .error .destructorsRemain next
  | none => .ok () next

def leakAllThreadTls [PointerProvenance P] (data : ThreadTlsData P) (thread : ThreadId)
    (roots : Array AllocId) : Array AllocId := Id.run do
  let mut roots := roots
  for entry in data.keys do
    if let some (_,pointer) := entry.data.find? (·.1 == thread) then
      if let some provenance := pointer.provenance then
        if let some id := PointerProvenance.getAllocId provenance then roots := roots.push id
  return roots

/-- Exact fields visited by source VisitProvenance for TlsData. No integer
address is mistaken for an allocation ID; consumers visit the typed values. -/
def provenanceRoots (data : ThreadTlsData P) : Array (TlsProvenanceRoot P) :=
  let pointerRoots := data.keys.flatMap fun entry => entry.data.map fun (_,pointer) => .pointer pointer
  let scalarRoots := data.threadAtexit.flatMap fun (_,entries) => entries.map fun entry => .scalar entry.data
  pointerRoots ++ scalarRoots

end ThreadTlsData
end Miri.Interpreter
