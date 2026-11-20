import Miri.Interpreter.Native.Types

/-! Rust-side native call staging from pinned `shims/native_lib/mod.rs`.
Required leaves describe concrete compiler, allocation, and external host
operations; libffi does not acquire a fabricated pure Lean implementation. -/
namespace Miri.Interpreter.Native
open Miri.ABI Miri.Memory Miri.MIR
structure Hooks (P S C V Code : Type) where
  target : TargetDataLayout
  hostBits : Nat
  typeShape : C → TyAndLayout TyId → RvalueM S TypeShape
  layoutOf : C → TyId → RvalueM S (Except Unit (TyAndLayout TyId))
  libraries : S → Array Library
  lookupSymbol : C → Library → String → RvalueM S (Option (SymbolInfo Code))
  tracingEnabled : S → Bool
  placeLayout : V → TyAndLayout TyId
  placePointer : V → Except StepError (Pointer (Option P))
  resolve : C → Pointer (Option P) → Nat → RvalueM S (AllocId × Nat)
  allocation : C → AllocId → RvalueM S (RawAllocation P)
  provenanceRange : C → AllocId → Nat → Nat → RvalueM S (Array P)
  inspectOutsideInterpreter : C → AllocId → Nat → Nat → RvalueM S (Array UInt8)
  expose : C → P → RvalueM S Unit
  /-- Process-wide AtomicBool diagnostic dedup, before exposing provenance. -/
  warningEmitted : S → Bool
  setWarningEmitted : S → Bool → S
  diagnosticSharedMemory : C → Bool → RvalueM S Unit
  /-- Reachability traversal is the canonical allocation visitor (including newly
  exposed allocations); callback mutations/errors must commit in source order. -/
  visitExposed : C → (AllocId → RvalueM S Unit) → RvalueM S Unit
  isLiveData : C → AllocId → RvalueM S Bool
  exposePhysical : C → AllocId → Bool → RvalueM S Unit
  nativeWrite : C → AllocId → Option (Nat × Nat) → RvalueM S Unit
  /-- Actual libffi+supervisor operation. OwnedArg descriptors are consumed once. -/
  rawCall : C → Code → Array OwnedArg → FfiType → Size → RvalueM S (Array UInt8 × Option (Array AccessEvent))
  writeBytes : C → Pointer (Option P) → Array UInt8 → RvalueM S Unit
  tryResolve : C → Pointer (Option P) → Nat → RvalueM S (Option (AllocId × Nat))
  enforceValidity : C → TyAndLayout TyId → RvalueM S Bool
  enforceRecursively : C → TyAndLayout TyId → RvalueM S Bool
  validate : C → V → Bool → Bool → RvalueM S Unit
  /-- Exact native address resolver; length is the remaining range *after*
  popping its current byte, as in source Range::next followed by Range::len. -/
  allocationFromAddress : C → Nat → Nat → RvalueM S (Option AllocId)

private def invalid (message : String) : RvalueM S A := throw (.invalidProgram message)
private def unsupported (message : String) : RvalueM S A := throw (.unsupported message)
private def liftResult (result : Except StepError A) : RvalueM S A :=
  match result with | .ok value => pure value | .error error => throw error
private def checked (h : Hooks P S C V Code) (n : Nat) : RvalueM S Nat :=
  if n < 2^h.hostBits then pure n else invalid "native host usize arithmetic overflow"

/-- A known compiler layout failure is unsupported FFI type; an unavailable
compiler query remains an outer RvalueM error and is never converted to success. -/
def queryLayout (h : Hooks P S C V Code) (choice : C) (ty : TyId) : RvalueM S (TyAndLayout TyId) := do
  match ← h.layoutOf choice ty with
  | .ok layout => pure layout
  | .error _ => unsupported "compiler layout unavailable for native FFI type"

/-- Type conversion fails before any operand inspection/exposure. The explicit
query fuel is an obligation on recursive compiler metadata, never a success default. -/
def ffiType (h : Hooks P S C V Code) (choice : C) : Nat → TyAndLayout TyId → RvalueM S FfiType
  | 0, _ => throw (.callback "native FFI recursive type query budget exhausted")
  | fuel+1, layout => do
    match layout.layout.backendRepr with
    | .Scalar scalar =>
      match ← h.typeShape choice layout with
      | .adt isEnum _ reprC _ =>
        if !isEnum && reprC then invalid "repr(C) non-enum has scalar backend ABI"
      | _ => pure ()
      match scalar.primitive with
      | .Int .I8 true => pure .i8 | .Int .I16 true => pure .i16
      | .Int .I32 true => pure .i32 | .Int .I64 true => pure .i64
      | .Int .I8 false => pure .u8 | .Int .I16 false => pure .u16
      | .Int .I32 false => pure .u32 | .Int .I64 false => pure .u64
      | .Float .F32 => pure .f32 | .Float .F64 => pure .f64
      | .Pointer space =>
        if space == AddressSpace.ZERO then pure .pointer else unsupported "native nonzero address-space pointer"
      | _ => unsupported "unsupported scalar type for native call"
    | _ =>
      match ← h.typeShape choice layout with
      | .emptyTuple => pure .void
      | .adt _ isStruct reprC fields =>
        unless isStruct && reprC do unsupported "native call requires repr(C) struct"
        let mut result := #[]
        for field in fields do
          let layout ← queryLayout h choice field
          result := result.push (← ffiType h choice fuel layout)
        pure (.structureType result)
      | .other => unsupported "unsupported type for native call"

private def exposeArgument (h : Hooks P S C V Code) (choice : C) (tracing : Bool) (prov : P) : RvalueM S Unit := do
  unless h.warningEmitted (← get) do
    modify fun state => h.setWarningEmitted state true
    h.diagnosticSharedMemory choice tracing
  h.expose choice prov

private def scalarBytes [PointerProvenance P] (h : Hooks P S C V Code) (choice : C)
    (tracing : Bool) (buffer : Array UInt8) (position : Nat) (scalar : Memory.Scalar P) : RvalueM S (Array UInt8) := do
  match ← liftResult (scalar.toBitsOrPtrInternal scalar.size |>.mapError ScalarOps.scalarError) with
  | .pointer ptr => exposeArgument h choice tracing ptr.provenance
  | .bits _ => pure ()
  let integer ← liftResult (scalar.toScalarInt |>.mapError ScalarOps.scalarError)
  let n := scalar.size.bytes.toNat
  if position+n > buffer.size then invalid "native scalar serialization exceeds layout size"
  let bits := integer.toBitsUnchecked.toNat
  let mut result := buffer
  for i in [:n] do
    let j := if h.target.endian == .little then i else n-1-i
    result := result.mapIdx fun index byte => if index == position+i then UInt8.ofNat (bits / 2^(8*j) % 256) else byte
  pure result

/-- Indirect argument inspection deliberately allows uninit and pointer bytes;
it must use the outside-interpreter accessor, not normal Rust memory reads. -/
def argument [PointerProvenance P] (h : Hooks P S C V Code) (choice : C)
    (fuel : Nat) (tracing : Bool) (value : OpTy P) : RvalueM S OwnedArg := do
  let type ← ffiType h choice fuel value.layout
  let bytes ← match value.op with
    | .indirect place => do
      let n ← checked h value.layout.layout.size.bytes.toNat
      if n == 0 then unsupported "attempting to pass a ZST over FFI"
      let (id,offset) ← h.resolve choice place.ptr n
      let _ ← checked h (offset+n)
      let provs ← h.provenanceRange choice id offset n
      for prov in provs do exposeArgument h choice tracing prov
      h.inspectOutsideInterpreter choice id offset n
    | .immediate imm => do
      let n ← checked h value.layout.layout.size.bytes.toNat
      let bytes := Array.replicate n (0 : UInt8)
      match imm with
      | .scalar sc => scalarBytes h choice tracing bytes 0 sc
      | .scalarPair first second =>
        let offset ← match value.layout.layout.backendRepr with
          | .ScalarPair (bOffset := offset) => pure offset.bytes.toNat
          | _ => invalid "native scalar pair has invalid layout"
        let bytes ← scalarBytes h choice tracing bytes 0 first
        scalarBytes h choice tracing bytes offset second
      | .uninit => pure bytes
  pure ⟨type,bytes⟩

private def prepare (h : Hooks P S C V Code) (choice : C) (tracing : Bool) (id : AllocId) : RvalueM S Unit := do
  unless ← h.isLiveData choice id do return
  let alloc ← h.allocation choice id
  h.exposePhysical choice id false
  unless tracing do
    for prov in alloc.provenances do h.expose choice prov
  if alloc.mutable then
    unless tracing do h.nativeWrite choice id none
    h.exposePhysical choice id true

/-- Decreasing byte budget permits splitting a native vectorized access across
adjacent allocations while exposing only the provenances actually read. -/
private def applyRange (h : Hooks P S C V Code) (choice : C) (event : AccessEvent)
    (endAddr : Nat) : Nat → Nat → RvalueM S Unit
  | 0, current => if current >= endAddr then pure () else invalid "native access traversal budget exhausted"
  | fuel+1, current => do
    if current >= endAddr then return
    let some id ← h.allocationFromAddress choice current (endAddr-current-1)
      | throw (.undefinedBehavior "Foreign code did an out-of-bounds access!")
    let alloc ← h.allocation choice id
    if current < alloc.address || endAddr < alloc.address then invalid "native allocation address subtraction underflow"
    let start := current-alloc.address
    let finish := min alloc.size (endAddr-alloc.address)
    if finish <= start then invalid "native traced access has empty allocation overlap"
    match event with
    | .read _ =>
      for prov in (← h.provenanceRange choice id start (finish-start)) do h.expose choice prov
    | .write _ certain =>
      if certain || alloc.mutable then h.nativeWrite choice id (some (start,finish-start))
    let advance := finish-start
    applyRange h choice event endAddr fuel (current+advance)


def applyAccesses (h : Hooks P S C V Code) (choice : C) (events : Array AccessEvent) : RvalueM S Unit := do
  for event in events do
    let r := event.range
    let endAddr ← checked h (r.addr+r.size)
    applyRange h choice event endAddr r.size r.addr

def returnToMemory (h : Hooks P S C V Code) (choice : C) (bytes : Array UInt8) (dest : V) : RvalueM S Unit := do
  let ptr ← liftResult (h.placePointer dest)
  h.writeBytes choice ptr bytes
  if bytes.isEmpty then return
  let some (id,offset) ← h.tryResolve choice ptr 0 | invalid "native return destination allocation unavailable"
  let _ ← h.allocation choice id
  h.nativeWrite choice id (some (offset,(h.placeLayout dest).layout.size.bytes.toNat))
  if ← h.enforceValidity choice (h.placeLayout dest) then
    let recursively ← h.enforceRecursively choice (h.placeLayout dest)
    h.validate choice dest recursively true

def findSymbol (h : Hooks P S C V Code) (choice : C) (name : String) : RvalueM S (Option Code) := do
  for library in h.libraries (← get) do
    if let some symbol ← h.lookupSymbol choice library name then
      if symbol.definingPath == library.path then return some symbol.code
  pure none

/-- Full Rust-side call pipeline: lookup, argument conversion, return ABI query,
reachable-memory preparation, host call, trace application, return validation. -/
def call [PointerProvenance P] (h : Hooks P S C V Code) (choice : C)
    (fuel : Nat) (name : String) (dest : V) (args : Array (OpTy P)) : RvalueM S Bool := do
  let some code ← findSymbol h choice name | return false
  let tracing := h.tracingEnabled (← get)
  let mut owned := #[]
  for arg in args do owned := owned.push (← argument h choice fuel tracing arg)
  let retType ← ffiType h choice fuel (h.placeLayout dest)
  h.visitExposed choice (prepare h choice tracing)
  let (bytes,events) ← h.rawCall choice code owned retType (h.placeLayout dest).layout.size
  if tracing then
    let some events := events | invalid "native tracing enabled but supervisor returned no events"
    applyAccesses h choice events
  returnToMemory h choice bytes dest
  pure true
end Miri.Interpreter.Native
