import Miri.Interpreter.NativeIsolatedAlloc

/-! Pinned alloc/alloc_bytes.rs:41–165, isolated-allocator branch. The host
pointer is retained with its original (possibly empty) slice layout; allocation
and destruction use the one-byte-adjusted layout. Host copy/read are genuine
memory effects, never manufactured byte observations. Global allocator mode
remains outside this isolated-native construction. -/
namespace Miri.Interpreter.NativeAllocBytes
open NativeIsolatedAlloc
structure Buffer where
  pointer : Nat
  layout : Layout
  deriving Repr
structure Host (S : Type) where
  allocator : NativeIsolatedAlloc.Host S
  copyFrom : Nat → Array UInt8 → EStateM StepError S Unit
  read : Nat → Nat → EStateM StepError S (Array UInt8)
private def actualLayout (layout : Layout) : Layout :=
  {layout with size := max 1 layout.size}

/-- `alloc_with`: the actual isolated allocator's address, including distinct
nonempty backing for zero-length slices. Layout validation runs in allocate. -/
def allocate (access : Access S) (host : Host S) (layout : Layout)
    (zeroed : Bool) : EStateM StepError S Buffer := do
  let pointer ← NativeIsolatedAlloc.allocate access host.allocator (actualLayout layout) zeroed
  pure ⟨pointer,layout⟩

def fromBytes (access : Access S) (host : Host S) (bytes : Array UInt8)
    (align : Nat) : EStateM StepError S Buffer := do
  let buffer ← allocate access host ⟨bytes.size,align⟩ false
  try
    host.copyFrom buffer.pointer bytes
    pure buffer
  catch error =>
    NativeIsolatedAlloc.deallocate access host.allocator buffer.pointer (actualLayout buffer.layout)
    throw error

def zeroed (access : Access S) (host : Host S) (size align : Nat) : EStateM StepError S Buffer :=
  allocate access host ⟨size,align⟩ true

/-- Source Deref exposes exactly the original size, even for empty slices. -/
def snapshot (host : Host S) (buffer : Buffer) : EStateM StepError S (Array UInt8) := do
  let bytes ← host.read buffer.pointer buffer.layout.size
  unless bytes.size == buffer.layout.size do
    throw (.invalidProgram "native backing host snapshot has incorrect slice length")
  pure bytes

def clone (access : Access S) (host : Host S) (buffer : Buffer) : EStateM StepError S Buffer := do
  fromBytes access host (← snapshot host buffer) buffer.layout.align

def release (access : Access S) (host : Host S) (buffer : Buffer) : EStateM StepError S Unit :=
  NativeIsolatedAlloc.deallocate access host.allocator buffer.pointer (actualLayout buffer.layout)
end Miri.Interpreter.NativeAllocBytes

namespace Miri.Interpreter.NativeAllocBytes
/-- Actual standard allocator effects. Null is allocation exhaustion, unlike
isolated mmap failure (which is a source assertion failure). -/
structure GlobalHost (S : Type) where
  hostBits : Nat
  allocate : NativeIsolatedAlloc.Layout → Bool → EStateM StepError S Nat
  deallocate : Nat → NativeIsolatedAlloc.Layout → EStateM StepError S Unit
  copyFrom : Nat → Array UInt8 → EStateM StepError S Unit
  read : Nat → Nat → EStateM StepError S (Array UInt8)

private def globalLayoutValid (host : GlobalHost S) (layout : NativeIsolatedAlloc.Layout) : Bool :=
  host.hostBits != 0 && layout.align != 0 && layout.align < 2^host.hostBits &&
  layout.align &&& (layout.align-1) == 0 && layout.size < 2^host.hostBits &&
  ((layout.size+layout.align-1)/layout.align)*layout.align <= 2^(host.hostBits-1)-1

/-- Source alloc_with returns None for conversion/layout errors or null. -/
def globalAllocate (host : GlobalHost S) (layout : NativeIsolatedAlloc.Layout)
    (zeroed : Bool) : EStateM StepError S (Option Buffer) := do
  if !globalLayoutValid host layout then return none
  unless globalLayoutValid host (actualLayout layout) do
    throw (.invalidProgram "zero-size native allocation adjusted Layout is invalid")
  let pointer ← host.allocate (actualLayout layout) zeroed
  if pointer == 0 then return none
  unless pointer < 2^host.hostBits do
    host.deallocate pointer (actualLayout layout)
    throw (.invalidProgram "global native allocator returned non-usize pointer")
  pure (some ⟨pointer,layout⟩)

def globalFromBytes (host : GlobalHost S) (bytes : Array UInt8) (align : Nat) : EStateM StepError S Buffer := do
  let some buffer ← globalAllocate host ⟨bytes.size,align⟩ false
    | throw (.resourceExhaustion "Miri ran out of memory: cannot create native allocation")
  try
    host.copyFrom buffer.pointer bytes
    pure buffer
  catch error =>
    host.deallocate buffer.pointer (actualLayout buffer.layout)
    throw error

def globalSnapshot (host : GlobalHost S) (buffer : Buffer) : EStateM StepError S (Array UInt8) := do
  let bytes ← host.read buffer.pointer buffer.layout.size
  unless bytes.size == buffer.layout.size do throw (.invalidProgram "global native buffer snapshot length mismatch")
  pure bytes

def globalClone (host : GlobalHost S) (buffer : Buffer) : EStateM StepError S Buffer := do
  globalFromBytes host (← globalSnapshot host buffer) buffer.layout.align

def globalRelease (host : GlobalHost S) (buffer : Buffer) : EStateM StepError S Unit :=
  host.deallocate buffer.pointer (actualLayout buffer.layout)
end Miri.Interpreter.NativeAllocBytes
