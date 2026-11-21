import Toy.PlaceEval.PlaceUB

/-!
# Concrete programs used by the examples, counterexamples and positive controls

All programs have one or two blocks. Locals are named by index. Unless stated otherwise
they are run under the static slot assignment `sEx` (local `x` at address `4 * x + 4`:
distinct, non-overlapping for sizes up to 4, 4-aligned, never `0`).
-/

namespace Toy.PlaceEval

/-- Layout of the toy pointer type. -/
def ptrL : Layout := ⟨ptrSize, ptrAlign⟩

/-- A one-byte integer type. -/
def u8 : Ty := .int 1 1

/-- The example slot assignment: local `x` at address `4 * x + 4`. -/
def sEx : Local → Nat := fun x => 4 * x + 4

/-- The example deterministic semantics. -/
def SEx : Sem := .slots sEx

/-- The null pointer constant (no provenance, address `0`). -/
def nullV : Val := .ptr ⟨none, 0⟩

/-- `placeMention (*(*pp))` where `*pp` is uninitialized: locals `0 : ptr` (the pointer
`pp`) and `1 : ptr` (with markers, so freshly allocated and uninitialized). -/
def pDerefUninit : Prog :=
  ⟨[ptrL, ptrL],
   [⟨[.storageLive 1, .assign ⟨0, []⟩ .ptr (.rawRef ⟨1, []⟩),
      .placeMention ⟨0, [.deref, .deref]⟩], .halt⟩]⟩

/-- `placeMention ((*p).field off)` for a dangling `p` (pointing to the freed 4-byte
local `1`). -/
def pDanglingMention (off : Nat) : Prog :=
  ⟨[ptrL, ⟨4, 2⟩],
   [⟨[.storageLive 1, .assign ⟨0, []⟩ .ptr (.rawRef ⟨1, []⟩), .storageDead 1,
      .placeMention ⟨0, [.deref, .field off]⟩], .halt⟩]⟩

/-- `r := &raw (*p).field off` for a dangling `p` (pointing to the freed 4-byte local `1`;
`r` is local `2`). -/
def pDanglingRaw (off : Nat) : Prog :=
  ⟨[ptrL, ⟨4, 2⟩, ptrL],
   [⟨[.storageLive 1, .assign ⟨0, []⟩ .ptr (.rawRef ⟨1, []⟩), .storageDead 1,
      .assign ⟨2, []⟩ .ptr (.rawRef ⟨0, [.deref, .field off]⟩)], .halt⟩]⟩

/-- A null `p`: `placeMention (*p)` and `r := &raw (*p).field off`. -/
def pNull (off : Nat) : Prog :=
  ⟨[ptrL, ptrL],
   [⟨[.assign ⟨0, []⟩ .ptr (.use (.const nullV)), .placeMention ⟨0, [.deref]⟩,
      .assign ⟨1, []⟩ .ptr (.rawRef ⟨0, [.deref, .field off]⟩)], .halt⟩]⟩

/-- A misaligned `p` (with provenance): `p := &raw (y.field 1)` for a 4-byte, 2-aligned
local `y` (local `1`, at address `8` under `sEx`, so `p` has address `9`); then
`placeMention (*p)` and `r := &raw (*p).field 0`. -/
def pMisaligned : Prog :=
  ⟨[ptrL, ⟨4, 2⟩, ptrL],
   [⟨[.assign ⟨0, []⟩ .ptr (.rawRef ⟨1, [.field 1]⟩), .placeMention ⟨0, [.deref]⟩,
      .assign ⟨2, []⟩ .ptr (.rawRef ⟨0, [.deref, .field 0]⟩)], .halt⟩]⟩

/-- Two identical failing `placeMention (*(*pp))` statements (indices 2 and 3). -/
def pTwoMentions : Prog :=
  ⟨[ptrL, ptrL],
   [⟨[.storageLive 1, .assign ⟨0, []⟩ .ptr (.rawRef ⟨1, []⟩),
      .placeMention ⟨0, [.deref, .deref]⟩, .placeMention ⟨0, [.deref, .deref]⟩], .halt⟩]⟩

/-- A switch on an uninitialized one-byte integer (local `0`, no markers, never written);
both targets are block `1`. -/
def pSwUninit : Prog :=
  ⟨[⟨1, 1⟩], [⟨[], .switchInt (.copy ⟨0, []⟩ u8) [(0, 1)] 1⟩, ⟨[], .halt⟩]⟩

/-- The field-less enum type with valid tags `0` and `1`. -/
def bool2 : Ty := .enum 1 1 [0, 1]

/-- Write the byte `v` into local `0` (as an integer), then switch on it read as `bool2`;
both targets are block `1`. For `v = 2` the tag is invalid. -/
def pSwTag (v : Nat) : Prog :=
  ⟨[⟨1, 1⟩],
   [⟨[.assign ⟨0, []⟩ u8 (.use (.const (.int v)))],
      .switchInt (.copy ⟨0, []⟩ bool2) [(0, 1)] 1⟩, ⟨[], .halt⟩]⟩

/-- The statement `r := &(*p)` with pointee layout `⟨4, 2⟩` (`r` is local `2`). -/
def refDerefStmt : Stmt := .assign ⟨2, []⟩ .ptr (.ref ⟨0, [.deref]⟩ ⟨4, 2⟩)

/-- The statement `r := &raw (*p)`. -/
def rawDerefStmt : Stmt := .assign ⟨2, []⟩ .ptr (.rawRef ⟨0, [.deref]⟩)

/-- `r := &raw (*p)` for a dangling `p` (statement index 3). -/
def pRawDangling : Prog :=
  ⟨[ptrL, ⟨4, 2⟩, ptrL],
   [⟨[.storageLive 1, .assign ⟨0, []⟩ .ptr (.rawRef ⟨1, []⟩), .storageDead 1, rawDerefStmt],
     .halt⟩]⟩

/-- `r := &(*p)` for a dangling `p` (statement index 3). -/
def pRefDangling : Prog :=
  ⟨[ptrL, ⟨4, 2⟩, ptrL],
   [⟨[.storageLive 1, .assign ⟨0, []⟩ .ptr (.rawRef ⟨1, []⟩), .storageDead 1, refDerefStmt],
     .halt⟩]⟩

/-- A packed struct local `0` of size 3 and alignment 1, with a 2-byte, 2-aligned field at
offset 1 (as `repr(packed) struct { a: u8, b: u16 }`); `r := &raw (s.b)` (local `1`).
Under `sEx` the field address is `5`. -/
def pRawPacked : Prog :=
  ⟨[⟨3, 1⟩, ptrL], [⟨[.assign ⟨1, []⟩ .ptr (.rawRef ⟨0, [.field 1]⟩)], .halt⟩]⟩

/-- The statement `r := &(s.b)` with pointee layout `⟨2, 2⟩`. -/
def refPackedStmt : Stmt := .assign ⟨1, []⟩ .ptr (.ref ⟨0, [.field 1]⟩ ⟨2, 2⟩)

/-- Slot assignment in which locals `0` and `1` share address `4`. -/
def sShare : Local → Nat := fun x => if x ≤ 1 then 4 else 4 * x + 4

/-- Locals `0` and `1` (one byte each, with markers) have disjoint live ranges:
`SL 0; x0 := 5; SD 0; SL 1; x1 := 7; SD 1; SL 0; emit x0`. The final read of `x0` after
its re-`storageLive` is UB. -/
def pShare : Prog :=
  ⟨[⟨1, 1⟩, ⟨1, 1⟩],
   [⟨[.storageLive 0, .assign ⟨0, []⟩ u8 (.use (.const (.int 5))), .storageDead 0,
      .storageLive 1, .assign ⟨1, []⟩ u8 (.use (.const (.int 7))), .storageDead 1,
      .storageLive 0, .emit (.use (.copy ⟨0, []⟩ u8))], .halt⟩]⟩

/-- A stale read after a re-`storageLive`: `SL 0; x := 5; SD 0; SL 0; emit x`. -/
def pStale : Prog :=
  ⟨[⟨1, 1⟩],
   [⟨[.storageLive 0, .assign ⟨0, []⟩ u8 (.use (.const (.int 5))), .storageDead 0,
      .storageLive 0, .emit (.use (.copy ⟨0, []⟩ u8))], .halt⟩]⟩

/-- Address observed across two live ranges of `x` (local `1`, one byte, markers):
`SL x; rr.0 := &raw x; SD x; SL x; rr.2 := &raw x; SD x; emit (rr.0 == rr.2)`, where
`rr` (local `0`, 4 bytes, no markers) holds two pointers. This is two iterations of a
loop body, unrolled. -/
def pAddrCmp : Prog :=
  ⟨[⟨4, 2⟩, ⟨1, 1⟩],
   [⟨[.storageLive 1, .assign ⟨0, []⟩ .ptr (.rawRef ⟨1, []⟩), .storageDead 1,
      .storageLive 1, .assign ⟨0, [.field 2]⟩ .ptr (.rawRef ⟨1, []⟩), .storageDead 1,
      .emit (.ptrEq (.copy ⟨0, []⟩ .ptr) (.copy ⟨0, [.field 2]⟩ .ptr))], .halt⟩]⟩

/-- A use of `x` (local `0`) while it is unallocated, followed by `unreachable`:
`SL 0; SD 0; x := 1; unreachable`. -/
def pDeadUse : Prog :=
  ⟨[⟨1, 1⟩],
   [⟨[.storageLive 0, .storageDead 0, .assign ⟨0, []⟩ u8 (.use (.const (.int 1)))],
      .unreachable⟩]⟩

/-- The address of `x` (local `1`) compared with itself within one live range:
`SL x; r := &raw x; emit (r == r)` (`r` is local `0`). -/
def pAddrSelf : Prog :=
  ⟨[ptrL, ⟨1, 1⟩],
   [⟨[.storageLive 1, .assign ⟨0, []⟩ .ptr (.rawRef ⟨1, []⟩),
      .emit (.ptrEq (.copy ⟨0, []⟩ .ptr) (.copy ⟨0, []⟩ .ptr))], .halt⟩]⟩

/-- A UB-free single live range: `SL 0; x := 5; emit x; SD 0`. -/
def pLive : Prog :=
  ⟨[⟨1, 1⟩],
   [⟨[.storageLive 0, .assign ⟨0, []⟩ u8 (.use (.const (.int 5))),
      .emit (.use (.copy ⟨0, []⟩ u8)), .storageDead 0], .halt⟩]⟩

/-- A program that halts immediately. -/
def pHalt : Prog := ⟨[], [⟨[], .halt⟩]⟩

end Toy.PlaceEval
