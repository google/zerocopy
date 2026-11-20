import Miri.Memory.Pointer
import Miri.Memory.Allocation
import Miri.ABI.Align

/-!
The allocation-bounds and pointer-alignment helpers from the pinned
`rustc_const_eval/src/interpret/memory.rs`. Pointer-to-allocation resolution,
live-allocation lookup, and machine policy are explicit inputs: this module
does not infer liveness or dereference validity from an allocation ID alone.
-/

namespace Miri.Memory

open Miri.ABI

inductive CheckInAllocMsg where
  | memoryAccess
  | inboundsPointerArithmetic
  | dereferenceable (description : String)
  | other (description : String)
  deriving DecidableEq, Repr

namespace CheckInAllocMsg

def asString : CheckInAllocMsg → String
  | .memoryAccess => "memory access"
  | .inboundsPointerArithmetic => "inbounds pointer arithmetic"
  | .dereferenceable description => s!"dereferenceable {description}"
  | .other description => description

end CheckInAllocMsg

inductive AllocationKind where
  | liveData
  | function
  | vaList
  | vtable
  | typeId
  | dead
  deriving DecidableEq, Repr

structure AllocationInfo where
  size : Size
  align : Align
  kind : AllocationKind
  mutability : Mutability
  deriving DecidableEq, Repr

structure Misalignment where
  has : Align
  required : Align
  deriving DecidableEq, Repr

inductive AllocationLookupError where
  | deadAllocation (id : AllocId)
  | unavailable (id : AllocId)
  deriving DecidableEq, Repr

inductive AccessError where
  | sizeDoesNotFitI64 (size : Size)
  | signedSizeOutsideI64 (size : Int)
  | danglingIntegerPointer (address : UInt64) (size : Int) (message : CheckInAllocMsg)
  | allocationLookup (reason : AllocationLookupError)
  | pointerArithmetic (reason : PointerError)
  | pointerOutOfBounds (id : AllocId) (allocationSize : Size) (offset : Int)
      (inboundsSize : Int) (message : CheckInAllocMsg)
  | malformedAlignment (reason : AlignError)
  | alignmentCheckFailed (misalignment : Misalignment)
  deriving DecidableEq, Repr

instance : ToString AccessError where
  toString
    | .sizeDoesNotFitI64 size => s!"access size {size.bytes} does not fit in signed i64"
    | .signedSizeOutsideI64 size => s!"signed access size {size} is outside i64"
    | .danglingIntegerPointer address size message =>
        s!"integer address {address} is not dereferenceable for {size} bytes ({message.asString})"
    | .allocationLookup (.deadAllocation id) => s!"allocation {id.value} has been deallocated"
    | .allocationLookup (.unavailable id) => s!"allocation metadata for {id.value} is unavailable"
    | .pointerArithmetic _ => "target pointer offset could not be sign-extended to isize"
    | .pointerOutOfBounds id allocationSize offset size message =>
        s!"pointer {id.value}+{offset} is out of bounds for allocation size {allocationSize.bytes}, access {size} ({message.asString})"
    | .malformedAlignment reason => s!"invalid source alignment: {reason}"
    | .alignmentCheckFailed misalignment =>
        s!"pointer alignment {misalignment.has.pow2} is below required {misalignment.required.pow2}"

structure ResolvedPointer (ProvExtra : Type) where
  allocId : AllocId
  offset : Size
  extra : ProvExtra

structure CheckedPointerAccess (ProvExtra : Type) where
  pointer : ResolvedPointer ProvExtra
  allocation : AllocationInfo

abbrev PointerResolver (Prov ProvExtra : Type) :=
  Pointer (Option Prov) → Int → Except UInt64 (ResolvedPointer ProvExtra)

abbrev LiveAllocationLookup := AllocId → Except AllocationLookupError AllocationInfo

private def fitsI64 (value : Int) : Bool :=
  -(2 ^ 63 : Int) ≤ value && value < (2 ^ 63 : Int)

def sizeAsI64 (size : Size) : Except AccessError Int :=
  if size.bytes.toNat < 9223372036854775808 then
    .ok (Int.ofNat size.bytes.toNat)
  else
    .error (.sizeDoesNotFitI64 size)

private def checkedAlign (align : Align) : Except AccessError Align := do
  let bytes ← (Align.bytes align).mapError AccessError.malformedAlignment
  let normalized ← (Align.fromBytes bytes).mapError AccessError.malformedAlignment
  if normalized == align then return align
  throw (.malformedAlignment (.tooLarge bytes))

def checkedBounds (target : PointerArithmetic) (id : AllocId) (allocationSize offset : Size)
    (signedSize : Int) (message : CheckInAllocMsg) : Except AccessError Unit := do
  if !fitsI64 signedSize then throw (.signedSizeOutsideI64 signedSize)
  let offsetNat := offset.bytes.toNat
  let allocationNat := allocationSize.bytes.toNat
  let inBounds := if signedSize >= 0 then
      offsetNat + signedSize.toNat ≤ allocationNat
    else
      let amount := (-signedSize).toNat
      amount ≤ offsetNat && offsetNat ≤ allocationNat
  if !inBounds then
    let signedOffset ← (target.signExtendToTargetIsize offset.bytes).mapError AccessError.pointerArithmetic
    throw (.pointerOutOfBounds id allocationSize signedOffset.toInt signedSize message)

/-- The exact common `check_and_deref_ptr` order. Zero-sized accesses return
`none` without pointer resolution or allocation lookup. Nonzero accesses first
resolve provenance/address, then obtain live allocation metadata, then perform
the checked signed interval test. The callbacks are the unported Machine and
memory-map dependencies of the source method. -/
def checkAndDerefPtr {Prov ProvExtra : Type}
    (target : PointerArithmetic) (ptr : Pointer (Option Prov)) (signedSize : Int) (message : CheckInAllocMsg)
    (resolve : PointerResolver Prov ProvExtra) (lookup : LiveAllocationLookup) :
    Except AccessError (Option (CheckedPointerAccess ProvExtra)) := do
  if !fitsI64 signedSize then throw (.signedSizeOutsideI64 signedSize)
  if signedSize == 0 then return none
  let resolved ← match resolve ptr signedSize with
    | .ok resolved => pure resolved
    | .error address => throw (.danglingIntegerPointer address signedSize message)
  let allocation ← match lookup resolved.allocId with
    | .ok allocation => pure allocation
    | .error (.deadAllocation id) => throw (.allocationLookup (.deadAllocation id))
    | .error (.unavailable id) => throw (.allocationLookup (.unavailable id))
  if allocation.kind == .dead then
    throw (.allocationLookup (.deadAllocation resolved.allocId))
  checkedBounds target resolved.allocId allocation.size resolved.offset signedSize message
  return some ⟨resolved, allocation⟩

/-- Source `get_ptr_access`: converting `Size` to host `i64` is checked, then
the common dereference/bounds helper supplies the live allocation details. -/
def getPtrAccess {Prov ProvExtra : Type}
    (target : PointerArithmetic) (ptr : Pointer (Option Prov)) (size : Size) (message : CheckInAllocMsg)
    (resolve : PointerResolver Prov ProvExtra) (lookup : LiveAllocationLookup) :
    Except AccessError (Option (Size × Align × (AllocId × Size × ProvExtra))) := do
  let signedSize ← sizeAsI64 size
  let checked ← checkAndDerefPtr target ptr signedSize message resolve lookup
  return checked.map fun access =>
    (access.allocation.size, access.allocation.align,
      (access.pointer.allocId, access.pointer.offset, access.pointer.extra))

/-- Source `check_ptr_access`, retaining its configurable access diagnostic. -/
def checkPtrAccess {Prov ProvExtra : Type}
    (target : PointerArithmetic) (ptr : Pointer (Option Prov)) (size : Size) (message : CheckInAllocMsg)
    (resolve : PointerResolver Prov ProvExtra) (lookup : LiveAllocationLookup) :
    Except AccessError Unit := do
  let _ ← checkAndDerefPtr target ptr (← sizeAsI64 size) message resolve lookup
  return ()

/-- Source `check_ptr_access_signed`; a negative amount checks bytes to the
left of the pointer, and zero retains the source's no-dereference behavior. -/
def checkPtrAccessSigned {Prov ProvExtra : Type}
    (target : PointerArithmetic) (ptr : Pointer (Option Prov)) (size : Int64) (message : CheckInAllocMsg)
    (resolve : PointerResolver Prov ProvExtra) (lookup : LiveAllocationLookup) :
    Except AccessError Unit := do
  let _ ← checkAndDerefPtr target ptr size.toInt message resolve lookup
  return ()

/-- Source's built-in offset test: a non-multiple offset has exactly the
alignment represented by its trailing zero bits. -/
private def offsetMisalignment (offset : Size) (required : Align) :
    Except AccessError (Option Misalignment) := do
  let required ← checkedAlign required
  let requiredBytes ← (Align.bytes required).mapError AccessError.malformedAlignment
  if requiredBytes == 0 || offset.bytes % requiredBytes == 0 then return none
  return some ⟨Align.maxAlignedFactor offset, required⟩

/-- Source `is_ptr_misaligned`, factored over explicit resolver, allocation
metadata, enforcement policy, and machine-specific alignment hook. For
address-based provenance, the pointer offset is its absolute address; for
relative provenance, both allocation alignment and relative offset are checked.
The hook must be supplied by the selected Machine, including its default `None`
behavior when no machine-specific rule applies. -/
def isPtrMisaligned {Prov ProvExtra : Type} [PointerProvenance Prov]
    (ptr : Pointer (Option Prov)) (required : Align) (enforceAlignment : Bool)
    (resolve : PointerResolver Prov ProvExtra) (lookup : AllocId → Except AllocationLookupError AllocationInfo)
    (machineAlignmentCheck : AllocId → Align → AllocationKind → Size → Align → Option Misalignment) :
    Except AccessError (Option Misalignment) := do
  let required ← checkedAlign required
  let requiredBytes ← (Align.bytes required).mapError AccessError.malformedAlignment
  if !enforceAlignment || requiredBytes == 1 then return none
  let resolved := resolve ptr 0
  match resolved with
  | .error address =>
    offsetMisalignment (Size.ofBytes address) required
  | .ok resolved =>
    let info ← match lookup resolved.allocId with
      | .ok info => pure info
      | .error reason => throw (.allocationLookup reason)
    let allocationAlign ← checkedAlign info.align
    if let some misalignment := machineAlignmentCheck resolved.allocId allocationAlign
        info.kind resolved.offset required then
      return some misalignment
    if PointerProvenance.offsetIsAddr (Prov := Prov) then
      return ← offsetMisalignment ptr.offset required
    let allocationAlignBytes ← (Align.bytes allocationAlign).mapError AccessError.malformedAlignment
    if allocationAlignBytes < requiredBytes then
      return some ⟨allocationAlign, required⟩
    return ← offsetMisalignment resolved.offset required

/-- Source `check_ptr_align` error boundary. The source message is always
`CheckAlignMsg::AccessedPtr` for this API. -/
def checkPtrAlign {Prov ProvExtra : Type} [PointerProvenance Prov]
    (ptr : Pointer (Option Prov)) (required : Align) (enforceAlignment : Bool)
    (resolve : PointerResolver Prov ProvExtra)
    (lookup : AllocId → Except AllocationLookupError AllocationInfo)
    (machineAlignmentCheck : AllocId → Align → AllocationKind → Size → Align → Option Misalignment) :
    Except AccessError Unit := do
  match ← isPtrMisaligned ptr required enforceAlignment resolve lookup machineAlignmentCheck with
  | none => return ()
  | some misalignment => throw (.alignmentCheckFailed misalignment)

theorem zero_sized_check_skips_resolution {Prov ProvExtra : Type}
    (ptr : Pointer (Option Prov)) (message : CheckInAllocMsg)
    (resolve : PointerResolver Prov ProvExtra) (lookup : LiveAllocationLookup)
    (target : PointerArithmetic) :
    checkAndDerefPtr target ptr 0 message resolve lookup = .ok none := by
  rfl

end Miri.Memory
