/-!
# Memory: allocations, pointers with a minimal provenance, cells, loads and stores

A toy memory model. It is meant to capture the parts of a Rust-like abstract machine
that decide whether *computing a place* or *accessing a value* is undefined behaviour
(UB): live allocations with a base address and a size, pointers that carry an optional
allocation identifier ("derived from allocation `k`"), alignment, dereferenceability and
in-bounds offsets, and memory cells that are uninitialized, hold a byte, or hold one
fragment of a pointer.

Nothing here mirrors a production definition. Model–system relation: none proved.
-/

namespace Toy.PlaceEval

/-- Names of locals. -/
abbrev Local := Nat

/-- Allocation identifiers: allocation `k` is the `k`-th entry of `Mem.allocs`. -/
abbrev AllocId := Nat

/-- A pointer: an optional provenance and an address. `prov = some k` means "derived from
allocation `k`"; `prov = none` is a pointer without provenance (for example a null pointer
or an integer reinterpreted as a pointer). Addresses are unbounded natural numbers; there
is no wrapping. -/
structure Ptr where
  prov : Option AllocId
  addr : Nat
deriving DecidableEq, Repr

/-- Move a pointer forward by `k` bytes, keeping its provenance (no check). -/
def Ptr.offset (q : Ptr) (k : Nat) : Ptr := ⟨q.prov, q.addr + k⟩

/-- An allocation: base address, size in bytes, and whether it is still live (freed
allocations stay in the table with `live = false`, so dangling pointers keep a meaningful
provenance). -/
structure Alloc where
  base : Nat
  size : Nat
  live : Bool
deriving DecidableEq, Repr

/-- A memory cell (one byte of storage): uninitialized, an initialized byte, or fragment
`i` of the stored pointer `q`. Bytes are natural numbers; only `b % 256` is ever decoded. -/
inductive Cell where
  | uninit
  | byte (b : Nat)
  | ptrFrag (q : Ptr) (i : Nat)
deriving DecidableEq, Repr

/-- Memory: the allocation table and the cell contents, an association list from addresses
to cells (the first entry for an address wins; absent addresses are uninitialized). Cells
are addressed physically: two allocations whose address ranges overlap share cells. -/
structure Mem where
  allocs : List Alloc
  cells : List (Nat × Cell)
deriving DecidableEq, Repr

/-- The cell at address `a`. -/
def Mem.get (m : Mem) (a : Nat) : Cell :=
  match m.cells.find? (fun e => e.1 == a) with
  | some e => e.2
  | none => .uninit

/-- The `n` cells at addresses `a, a+1, …, a+n-1`. -/
def Mem.readCells (m : Mem) (a n : Nat) : List Cell :=
  (List.range n).map fun i => m.get (a + i)

/-- Entries placing the cells `cs` at consecutive addresses from `a`. -/
def placeCells : Nat → List Cell → List (Nat × Cell)
  | _, [] => []
  | a, c :: cs => (a, c) :: placeCells (a + 1) cs

/-- Overwrite the cells at `a, a+1, …` with `cs`. -/
def Mem.writeCells (m : Mem) (a : Nat) (cs : List Cell) : Mem :=
  { m with cells := placeCells a cs ++ m.cells }

/-- `aligned al a`: the address `a` is a multiple of `al`, computed as `a % al = 0` with
Nat remainder. Degenerate edge: for `al = 0` exactly the address `0` is aligned
(`a % 0 = a`). Layouts and types with alignment `0` are admitted; a result that needs
alignment at least `1` states it as a hypothesis. -/
def aligned (al a : Nat) : Bool := a % al == 0

/-- `m.inBounds q n`: `q` is derived from a *live* allocation `k` and the whole range
`q.addr .. q.addr + n` lies within it (`base ≤ q.addr` and `q.addr + n ≤ base + size`;
the end address may be one past the last byte). For `n = 0` this still requires a live
allocation containing `q.addr` (or ending exactly there). -/
def Mem.inBounds (m : Mem) (q : Ptr) (n : Nat) : Bool :=
  match q.prov with
  | none => false
  | some k =>
    match m.allocs[k]? with
    | none => false
    | some al => al.live && decide (al.base ≤ q.addr) && decide (q.addr + n ≤ al.base + al.size)

/-- `m.dereferenceable q n`: an access of `n` bytes through `q` is permitted by the
allocation rules. Zero-byte accesses are permitted for every pointer (including null and
dangling pointers); otherwise `m.inBounds q n` is required. -/
def Mem.dereferenceable (m : Mem) (q : Ptr) (n : Nat) : Bool :=
  n == 0 || m.inBounds q n

/-- `m.offsetInbounds q k`: offsetting `q` by `k ≥ 0` bytes satisfies the in-bounds
pointer-arithmetic rule: either `k = 0` (a zero offset is permitted on every pointer), or
`q` is derived from a live allocation and the whole range `q.addr .. q.addr + k` is in
bounds of it. (In the toy this coincides with `dereferenceable`; see
`offsetInbounds_eq_dereferenceable`.) -/
def Mem.offsetInbounds (m : Mem) (q : Ptr) (k : Nat) : Bool :=
  k == 0 || m.inBounds q k

theorem offsetInbounds_eq_dereferenceable (m : Mem) (q : Ptr) (k : Nat) :
    m.offsetInbounds q k = m.dereferenceable q k := rfl

/-! ## Types and values -/

/-- Scalar types of accessed values. `int size align` is an unsigned integer of `size`
bytes (little-endian); `ptr` is a raw pointer type of size `ptrSize` and alignment
`ptrAlign`; `enum size align valid` is a field-less enum represented by an integer tag of
`size` bytes whose valid tags are the members of `valid`. -/
inductive Ty where
  | int (size align : Nat)
  | ptr
  | enum (size align : Nat) (valid : List Nat)
deriving DecidableEq, Repr

/-- Size of the toy raw pointer type, in bytes. -/
def ptrSize : Nat := 2

/-- Alignment of the toy raw pointer type, in bytes. -/
def ptrAlign : Nat := 2

/-- Size of a type, in bytes. -/
def Ty.size : Ty → Nat
  | .int s _ => s
  | .ptr => ptrSize
  | .enum s _ _ => s

/-- Alignment of a type, in bytes. -/
def Ty.align : Ty → Nat
  | .int _ a => a
  | .ptr => ptrAlign
  | .enum _ a _ => a

/-- Values: integers and pointers. There is no "uninitialized" value: a read that would
produce one is UB. -/
inductive Val where
  | int (n : Nat)
  | ptr (q : Ptr)
deriving DecidableEq, Repr

/-- Little-endian decoding of byte cells; `none` if some cell is not a byte. Each byte
contributes `b % 256` (Nat remainder). -/
def decodeLE : List Cell → Option Nat
  | [] => some 0
  | .byte b :: cs => (decodeLE cs).map fun v => b % 256 + 256 * v
  | _ :: _ => none

/-- Little-endian encoding of `v` into `n` byte cells (digits `v / 256^i % 256`, floor
division and Nat remainder; bits beyond `n` bytes are dropped). -/
def encodeLE : Nat → Nat → List Cell
  | 0, _ => []
  | n + 1, v => .byte (v % 256) :: encodeLE n (v / 256)

/-- Decoding two cells as a pointer: the two fragments of one pointer `q` give `q`; two
byte cells give a pointer without provenance whose address is the little-endian value;
anything else (an uninitialized cell, mixed or mismatched fragments, a wrong length) is
not a pointer value. -/
def decodePtr : List Cell → Option Ptr
  | [.ptrFrag q 0, .ptrFrag q' 1] => if q = q' then some q else none
  | cs => if cs.length = ptrSize then (decodeLE cs).map fun a => ⟨none, a⟩ else none

/-- Decoding cells at a type: integers need byte cells; pointers need a pointer value
(`decodePtr`); enums need byte cells encoding a valid tag. -/
def Ty.decode : Ty → List Cell → Option Val
  | .int _ _, cs => (decodeLE cs).map Val.int
  | .ptr, cs => (decodePtr cs).map Val.ptr
  | .enum _ _ valid, cs =>
    match decodeLE cs with
    | some n => if n ∈ valid then some (.int n) else none
    | none => none

/-- Encoding a value into `n` cells: integers little-endian, pointers as fragments
`0 … n-1`. -/
def Val.encode (n : Nat) : Val → List Cell
  | .int v => encodeLE n v
  | .ptr q => (List.range n).map (Cell.ptrFrag q)

/-- Load a value of type `τ` through `q`: UB (`none`) unless `q` is dereferenceable for
`τ.size` bytes, aligned for `τ.align`, and the cells decode at `τ`. -/
def Mem.load (m : Mem) (q : Ptr) (τ : Ty) : Option Val :=
  if m.dereferenceable q τ.size && aligned τ.align q.addr then
    τ.decode (m.readCells q.addr τ.size)
  else none

/-- Store value `v` at type `τ` through `q`: UB (`none`) unless `q` is dereferenceable for
`τ.size` bytes and aligned for `τ.align`. -/
def Mem.store (m : Mem) (q : Ptr) (τ : Ty) (v : Val) : Option Mem :=
  if m.dereferenceable q τ.size && aligned τ.align q.addr then
    some (m.writeCells q.addr (v.encode τ.size))
  else none

/-- Load a pointer through `q` (the load performed by a `Deref` projection). -/
def Mem.loadPtr (m : Mem) (q : Ptr) : Option Ptr :=
  match m.load q .ptr with
  | some (.ptr r) => some r
  | _ => none

/-- `DerefLoadOk m q`: the pointer load performed by a `Deref` projection at `q`
succeeds: `q` is dereferenceable for `ptrSize` bytes ("allocated"), aligned for
`ptrAlign`, and the cells hold a pointer value (`decodePtr` succeeds). -/
def DerefLoadOk (m : Mem) (q : Ptr) : Prop :=
  m.dereferenceable q ptrSize = true ∧ aligned ptrAlign q.addr = true ∧
    ∃ r, decodePtr (m.readCells q.addr ptrSize) = some r

/-- The `Deref` load succeeds exactly under `DerefLoadOk`. -/
theorem loadPtr_isSome_iff (m : Mem) (q : Ptr) :
    (m.loadPtr q).isSome = true ↔ DerefLoadOk m q := by
  unfold Mem.loadPtr Mem.load DerefLoadOk
  by_cases h : (m.dereferenceable q Ty.ptr.size && aligned Ty.ptr.align q.addr) = true
  · simp only [h, ↓reduceIte]
    simp only [Bool.and_eq_true] at h
    simp only [Ty.decode]
    cases hd : decodePtr (m.readCells q.addr Ty.ptr.size) with
    | none =>
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, false_iff]
      rintro ⟨_, _, r, hr⟩
      simp [Ty.size] at hd
      rw [hd] at hr
      cases hr
    | some r =>
      simp only [Option.map_some, Option.isSome_some, true_iff]
      exact ⟨h.1, h.2, r, hd⟩
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨h1, h2, _⟩
    apply h
    simp only [Bool.and_eq_true]
    exact ⟨h1, h2⟩

end Toy.PlaceEval
