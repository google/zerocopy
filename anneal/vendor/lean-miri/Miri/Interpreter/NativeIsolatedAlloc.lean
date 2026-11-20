import Miri.Interpreter.Step

/-! Pinned alloc/isolated_alloc.rs:1–309. Actual anonymous RW mmap, munmap,
zeroing and sysconf are external host effects. Layout normalization, first-fit
compressed bitmaps, page/huge ownership and removal order are source operations.
These are host addresses, never fabricated MIR allocation addresses. -/
namespace Miri.Interpreter.NativeIsolatedAlloc
structure Layout where
  size : Nat
  align : Nat
  deriving Repr
structure Page where
  address : Nat
  occupied : Array Bool
  deriving Repr
structure Segment where
  address : Nat
  size : Nat
  deriving Repr
structure Storage where
  pageSize : Nat
  pages : Array Page := #[]
  huge : Array Segment := #[]
  deriving Repr
structure Access (S : Type) where
  get : S → Storage
  put : S → Storage → S
structure Host (S : Type) where
  hostBits : Nat
  sysconfPageSize : EStateM StepError S Nat
  /-- Host MAP_PRIVATE|MAP_ANONYMOUS with PROT_READ|PROT_WRITE, null hint,
  fd=-1 and offset=0. Actual OS zeroed pages, no substituted return address. -/
  mmapAnonymousReadWrite : Nat → EStateM StepError S Nat
  munmap : Nat → Nat → EStateM StepError S Int32
  zero : Nat → Nat → EStateM StepError S Unit
private def invalid (reason : String) : EStateM StepError S A := throw (.invalidProgram reason)
private def word (h : Host S) (value : Nat) : EStateM StepError S Nat := do
  unless value < 2^h.hostBits do invalid "native host usize arithmetic overflow"
  pure value
private def normalized (h : Host S) (layout : Layout) : EStateM StepError S Layout := do
  -- std::alloc::Layout's unsafe-call domain, not Rust program UB.
  unless layout.align != 0 && layout.align &&& (layout.align-1) == 0 do
    invalid "native allocator requires a valid power-of-two host Layout alignment"
  let rounded := ((layout.size+layout.align-1)/layout.align)*layout.align
  unless h.hostBits != 0 && rounded <= 2^(h.hostBits-1)-1 do invalid "native allocator host Layout exceeds isize domain"
  let size ← word h (((layout.size+3)/4)*4)
  let align := max layout.align 4
  let padded := ((size+align-1)/align)*align
  unless padded <= 2^(h.hostBits-1)-1 do invalid "normalized native allocator Layout exceeds isize domain"
  pure ⟨size,align⟩
private def hugeSize (h : Host S) (state : Storage) (layout : Layout) : EStateM StepError S Nat := do
  if state.pageSize == 0 then invalid "native allocator page size is zero"
  let size ← word h (((layout.size+state.pageSize-1)/state.pageSize)*state.pageSize)
  let align := max layout.align state.pageSize
  -- strict_div is checked integer division, not exact-divisibility checking.
  -- Its divisor was checked nonzero above.
  word h ((size/state.pageSize + (align/state.pageSize-1))*state.pageSize)
private def isHuge (state : Storage) (layout : Layout) : Bool :=
  layout.align > state.pageSize/2 || layout.size >= state.pageSize/2
private def put (a : Access S) (value : Storage) : EStateM StepError S Unit :=
  modify fun state => a.put state value
private def mapped (h : Host S) (size : Nat) : EStateM StepError S Nat := do
  let address ← h.mmapAnonymousReadWrite size
  unless address < 2^h.hostBits do invalid "native mmap returned a non-usize address"
  if address == 2^h.hostBits-1 then invalid "native mmap failed"
  if address == 0 then invalid "native mmap returned null"
  pure address

/-- Source construction queries the real host page size once. -/
def create (h : Host S) : EStateM StepError S Storage := do
  let size ← h.sysconfPageSize
  let size ← word h size
  pure ⟨size,#[],#[]⟩

private def allocateSmall (a : Access S) (h : Host S) (layout : Layout)
    (pageIndex : Nat) (zeroed : Bool) : EStateM StepError S (Option Nat) := do
  let storage := a.get (← get)
  let some page := storage.pages[pageIndex]? | invalid "native small page index unavailable"
  if layout.align == 0 then invalid "native normalized layout has zero alignment"
  for index in [:((storage.pageSize+layout.align-1)/layout.align)] do
    let offset := index*layout.align
    let start := offset/4
    let count := layout.size/4
    if page.occupied.size < start+count then break
    if !(page.occupied.extract start (start+count)).any id then
      let updated := {page with occupied := page.occupied.mapIdx fun i bit => if start <= i && i < start+count then true else bit}
      put a {storage with pages := storage.pages.mapIdx fun i old => if i == pageIndex then updated else old}
      let pointer ← word h (page.address+offset)
      if zeroed then h.zero pointer layout.size
      return some pointer
  pure none

/-- Compression normalization precedes huge dispatch. Existing pages are tried
in source vector order. Bitmap insertion occurs before host zeroing, so errors
retain the same allocation prefix. Huge mmap is always zeroed by its OS contract. -/
def allocate (a : Access S) (h : Host S) (requested : Layout) (zeroed : Bool) : EStateM StepError S Nat := do
  let layout ← normalized h requested
  let storage := a.get (← get)
  if isHuge storage layout then
    let size ← hugeSize h storage layout
    let address ← mapped h size
    let current := a.get (← get)
    put a {current with huge := current.huge.push ⟨address,size⟩}
    word h (((address+layout.align-1)/layout.align)*layout.align)
  else
    for index in [:storage.pages.size] do
      if let some pointer ← allocateSmall a h layout index zeroed then return pointer
    let address ← mapped h storage.pageSize
    unless storage.pageSize % 4 == 0 do invalid "native page size not divisible by compression factor"
    let current := a.get (← get)
    let index := current.pages.size
    put a {current with pages := current.pages.push ⟨address,Array.replicate (storage.pageSize/4) false⟩}
    let some pointer ← allocateSmall a h layout index zeroed
      | invalid "native allocation failed to fit fresh small page"
    pure pointer

/-- Source removes the owning page/segment before munmap, retaining that
removal on host failure. Huge wrong-layout assertion also follows removal. -/
def deallocate (a : Access S) (h : Host S) (pointer : Nat) (requested : Layout) : EStateM StepError S Unit := do
  let layout ← normalized h requested
  let storage := a.get (← get)
  if isHuge storage layout then
    let size ← hugeSize h storage layout
    let mut selected := none
    for index in [:storage.huge.size] do
      let some segment := storage.huge[index]? | invalid "native huge index unavailable"
      let finish ← word h (segment.address+segment.size)
      if segment.address <= pointer && pointer < finish then
        selected := some (index,segment)
        break
    let some (index,segment) := selected | invalid "freeing unallocated native huge pages"
    put a {storage with huge := storage.huge.extract 0 index ++ storage.huge.extract (index+1) storage.huge.size}
    unless size == segment.size do invalid "wrong layout in native huge deallocation"
    unless (← h.munmap segment.address size) == 0 do invalid "native huge munmap failed"
  else
    if storage.pageSize == 0 then invalid "native allocator page size is zero"
    let offset := pointer % storage.pageSize
    let base := pointer-offset
    let mut selected := none
    for index in [:storage.pages.size] do
      if let some page := storage.pages[index]? then
        if page.address == base then
          selected := some (index,page)
          break
    let some (index,page) := selected | invalid "freeing in an unallocated native page"
    let start := offset/4
    let count := layout.size/4
    unless start+count <= page.occupied.size do invalid "native deallocation bit range out of bounds"
    let updated := {page with occupied := page.occupied.mapIdx fun i bit => if start <= i && i < start+count then false else bit}
    let changed := {storage with pages := storage.pages.mapIdx fun i old => if i == index then updated else old}
    put a changed
    if !updated.occupied.any id then
      put a {changed with pages := changed.pages.extract 0 index ++ changed.pages.extract (index+1) changed.pages.size}
      unless (← h.munmap page.address storage.pageSize) == 0 do invalid "native small munmap failed"

/-- Small-page ranges precede huge ranges, as source Iterator::chain. -/
def pages (storage : Storage) : Array Segment :=
  storage.pages.map (fun page => ⟨page.address,storage.pageSize⟩) ++ storage.huge
end Miri.Interpreter.NativeIsolatedAlloc
