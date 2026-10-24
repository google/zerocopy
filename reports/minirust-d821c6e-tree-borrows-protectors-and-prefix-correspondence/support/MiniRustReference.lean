import Std

/-!
Audited transcription of the raw BasicMemory API in MiniRust
  d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed
on its spec/prelude/target.md x86_64 target. See docs/rust-opsem/minirust-fragment.md.

This is an independently written reference kernel, not a verified source import,
a transcription of the complete Machine, or a Rust adequacy claim. The upstream
list is represented by a finite minted-ID domain of an option-valued map. Natural
addresses are the explicitly admitted bounded-address subset of source Int;
fragment positions are restricted to nonnegative source Int positions.

No representation decoder, alias permission, concurrent wrapper, or prophecy is
part of this raw-memory kernel. In particular raw loads can return Uninit.
-/
namespace AnnealResearch.MiniRustReference

structure Frag where
  allocId : Nat
  position : Nat
  deriving DecidableEq, Repr

inductive Byte where
  | uninit
  | init (number : Fin 256) (fragment : Option Frag)
  deriving DecidableEq, Repr

structure Ptr where
  addr : Nat
  provenance : Option Nat
  deriving DecidableEq, Repr

inductive Kind where
  | stack | heap | global | function | vtable
  deriving DecidableEq, Repr

structure Allocation where
  base : Nat
  size : Nat
  align : Nat
  kind : Kind
  live : Bool
  data : Nat → Byte

structure State where
  next : Nat
  allocations : Nat → Option Allocation

/-- Distinct diagnostics preserve the order in basic.md rather than merging
    alignment, absent provenance, lifetime, geometry, and free metadata errors. -/
inductive UB where
  | allocationTooLarge
  | misalignedLoad
  | misalignedStore
  | noProvenance
  | dead
  | bounds
  | freeNoProvenance
  | doubleFree
  | freeNotBase
  | freeKind
  | freeSize
  | freeAlign
  deriving DecidableEq, Repr

/-- noChoice is absent allocator behavior, not a source error transition.
    unsupported marks an out-of-contract representation input, such as a forged
    allocation ID or zero represented as an Align. It never means success. -/
inductive Result (α : Type) where
  | ok (value : α)
  | ub (diagnostic : UB)
  | noChoice
  | unsupported

/-- The source has distinct MachineStop and MemoryLeak termination tags. -/
inductive ExitResult where
  | machineStop
  | memoryLeak
  deriving DecidableEq, Repr

abbrev pointerBytes : Nat := 8
abbrev pointerAlignment : Nat := 8
abbrev addressLimit : Nat := 2 ^ 64
abbrev sizeLimit : Nat := 2 ^ 63

/-- Source Align is a positive power of two. Runtime Nat arguments are used only
    under this admission; no finite upper bound on alignment is added. -/
def AlignWF (align : Nat) : Prop := ∃ exponent : Nat, align = 2 ^ exponent

def PtrWF (s : State) (p : Ptr) : Prop :=
  p.addr < addressLimit ∧
  match p.provenance with
  | none => True
  | some id => id < s.next

def ByteWF (s : State) : Byte → Prop
  | .uninit => True
  | .init _ none => True
  | .init _ (some fragment) => fragment.allocId < s.next

def overlaps (a : Allocation) (otherBase otherSize : Nat) : Prop :=
  a.base = otherBase ∨
    ¬ (a.base + a.size ≤ otherBase ∨ otherBase + otherSize ≤ a.base)

instance (a : Allocation) (otherBase otherSize : Nat) :
    Decidable (overlaps a otherBase otherSize) := by
  unfold overlaps
  infer_instance

/-- Structural admission, not NoUB. It does not check the operands of any
    future command for live/bounds/access alignment or correct free metadata. -/
structure StateWF (s : State) : Prop where
  domain : ∀ id, (∃ allocation, s.allocations id = some allocation) ↔ id < s.next
  geometry : ∀ id allocation, s.allocations id = some allocation →
    0 < allocation.base ∧ AlignWF allocation.align ∧
    allocation.base % allocation.align = 0 ∧
    allocation.size < sizeLimit ∧ allocation.base + allocation.size < addressLimit
  knownFragments : ∀ id allocation offset,
    s.allocations id = some allocation → offset < allocation.size →
    ByteWF s (allocation.data offset)
  liveSeparation : ∀ id first otherId second,
    s.allocations id = some first → s.allocations otherId = some second →
    id ≠ otherId → first.live = true → second.live = true →
    ¬ overlaps first second.base second.size

def empty : State := { next := 0, allocations := fun _ => none }

def replace (s : State) (id : Nat) (allocation : Allocation) : State :=
  { s with allocations := fun current =>
      if current = id then some allocation else s.allocations current }

/-- IDs are list positions: the old count is appended and never reused. -/
def append (s : State) (allocation : Allocation) : State :=
  { next := s.next + 1
    allocations := fun current =>
      if current = s.next then some allocation else s.allocations current }

structure CheckedSpan where
  id : Nat
  allocation : Allocation
  offset : Nat

/-- basic.md:197-224. In particular zero length precedes provenance/lifetime.
    Negative source offsets are checked before using Nat subtraction. -/
def checkPtr (s : State) (p : Ptr) (len : Nat) : Result (Option CheckedSpan) :=
  if len = 0 then .ok none
  else
    match p.provenance with
    | none => .ub .noProvenance
    | some id =>
      match s.allocations id with
      | none => .unsupported
      | some allocation =>
        if allocation.live = false then .ub .dead
        else if p.addr < allocation.base then .ub .bounds
        else
          let offset := p.addr - allocation.base
          if allocation.size < offset + len then .ub .bounds
          else .ok (some { id, allocation, offset })

/-- basic.md:253-274,333-335. Requested alignment is checked before n=0.
    Unit extras have no permission effects; the exact raw bytes are returned. -/
def load (s : State) (p : Ptr) (len align : Nat) :
    Result (List Byte × State) :=
  if align = 0 then .unsupported
  else if p.addr % align ≠ 0 then .ub .misalignedLoad
  else
    match checkPtr s p len with
    | .ok none => .ok ([], s)
    | .ok (some checked) =>
      .ok (List.ofFn (fun i : Fin len => checked.allocation.data (checked.offset + i.val)), s)
    | .ub error => .ub error
    | .noChoice => .noChoice
    | .unsupported => .unsupported

/-- basic.md:227-250,329-331. No state is committed before a failed check. -/
def store (s : State) (p : Ptr) (bytes : List Byte) (align : Nat) : Result State :=
  if align = 0 then .unsupported
  else if p.addr % align ≠ 0 then .ub .misalignedStore
  else
    match checkPtr s p bytes.length with
    | .ok none => .ok s
    | .ok (some checked) =>
      let written : Allocation := { checked.allocation with
        data := fun index =>
          if checked.offset ≤ index ∧ index < checked.offset + bytes.length then
            bytes.getD (index - checked.offset) .uninit
          else checked.allocation.data index }
      .ok (replace s checked.id written)
    | .ub error => .ub error
    | .noChoice => .noChoice
    | .unsupported => .unsupported

/-- basic.md:144-184,325-327. Preserve provenance/live/base/kind/size/align
    ordering and retain the dead record and its contents. -/
def free (s : State) (p : Ptr) (kind : Kind) (size align : Nat) : Result State :=
  match p.provenance with
  | none => .ub .freeNoProvenance
  | some id =>
    match s.allocations id with
    | none => .unsupported
    | some allocation =>
      if allocation.live = false then .ub .doubleFree
      else if p.addr ≠ allocation.base then .ub .freeNotBase
      else if kind ≠ allocation.kind then .ub .freeKind
      else if size ≠ allocation.size then .ub .freeSize
      else if align ≠ allocation.align then .ub .freeAlign
      else .ok (replace s id { allocation with live := false })

/-- Quantification is over the minted finite list, with dead records ignored.
    Same-base overlap is retained even for zero-size allocations. -/
def liveOverlap (s : State) (base size : Nat) : Bool :=
  (List.range s.next).any fun id =>
    match s.allocations id with
    | none => false
    | some allocation => allocation.live && decide (overlaps allocation base size)

def AllocationCandidate (s : State) (size align addr : Nat) : Prop :=
  0 < addr ∧ addr % align = 0 ∧ addr + size < addressLimit ∧
    liveOverlap s addr size = false

instance (s : State) (size align addr : Nat) :
    Decidable (AllocationCandidate s size align addr) := by
  unfold AllocationCandidate
  infer_instance

/-- basic.md:92-141. The addr parameter witnesses one demonic branch. A
    noChoice result contributes NO transition, not UB. Too-large allocation
    is UB before evaluating candidates, including when no candidate exists. -/
def allocateAt (s : State) (kind : Kind) (size align addr : Nat) :
    Result (Ptr × State) :=
  if sizeLimit ≤ size then .ub .allocationTooLarge
  else if align = 0 then .unsupported
  else if AllocationCandidate s size align addr then
    let allocation : Allocation :=
      { base := addr, size, align, kind, live := true, data := fun _ => .uninit }
    .ok ({ addr, provenance := some s.next }, append s allocation)
  else .noChoice

/-- The actual allocator relation has all satisfying branches. Invalid
    candidates are absent; oversized requests expose one UB transition. -/
def Allocate (s : State) (kind : Kind) (size align : Nat)
    (result : Result (Ptr × State)) : Prop :=
  result ≠ .noChoice ∧ ∃ addr, allocateAt s kind size align addr = result

/-- basic.md:337-339. No alignment requirement is imposed by this API. -/
def dereferenceable (s : State) (p : Ptr) (len : Nat) : Result Unit :=
  match checkPtr s p len with
  | .ok _ => .ok ()
  | .ub error => .ub error
  | .noChoice => .noChoice
  | .unsupported => .unsupported

/-- basic.md:278-296 and step/intrinsics.md:85-100. This is source Exit's
    leak result, not a conflation of memory leaks and UB. -/
def exit (s : State) : ExitResult :=
  if (List.range s.next).any (fun id =>
      match s.allocations id with
      | none => false
      | some allocation => allocation.live && decide (allocation.kind = .heap)) then
    .memoryLeak
  else .machineStop

/-- pointer.md:52-58: wrapping offset preserves provenance. -/
def wrappingOffset (p : Ptr) (offset : Int) : Ptr :=
  { p with addr := ((Int.ofNat p.addr + offset) % Int.ofNat addressLimit).toNat }

/- Simple clause controls. The parent runs Lean and audits any repaired proofs;
   this worker intentionally does not execute Lean or builds. -/
theorem checkPtr_zero (s : State) (p : Ptr) : checkPtr s p 0 = .ok none := by
  simp [checkPtr]

theorem load_zero (s : State) (p : Ptr) (align : Nat)
    (nonzero : align ≠ 0) (aligned : p.addr % align = 0) :
    load s p 0 align = .ok ([], s) := by
  simp [load, nonzero, aligned, checkPtr]

theorem store_empty (s : State) (p : Ptr) (align : Nat)
    (nonzero : align ≠ 0) (aligned : p.addr % align = 0) :
    store s p [] align = .ok s := by
  simp [store, nonzero, aligned, checkPtr]

theorem oversized_allocation (s : State) (kind : Kind) (size align addr : Nat)
    (large : sizeLimit ≤ size) :
    allocateAt s kind size align addr = .ub .allocationTooLarge := by
  simp [allocateAt, large]

theorem append_fresh (s : State) (allocation : Allocation) :
    (append s allocation).allocations s.next = some allocation := by
  simp [append]

theorem replace_other (s : State) (id other : Nat) (allocation : Allocation)
    (different : other ≠ id) :
    (replace s id allocation).allocations other = s.allocations other := by
  simp [replace, different]

#print axioms checkPtr_zero
#print axioms load_zero
#print axioms store_empty
#print axioms oversized_allocation
#print axioms append_fresh
#print axioms replace_other

end AnnealResearch.MiniRustReference
