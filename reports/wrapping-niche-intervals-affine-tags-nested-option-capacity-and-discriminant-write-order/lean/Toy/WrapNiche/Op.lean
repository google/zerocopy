import Toy.WrapNiche.Nest

/-!
# Operational semantics of discriminant writes

A *place* is a list of bytes, each uninitialized (`none`) or holding a value (bytes carry no
provenance). The niche field of an enum layout `L : OpLayout` occupies the `L.nw` bytes starting
at offset `L.no` and is read little-endian as a value of `Pat L.nw = Fin (256 ^ L.nw)`.

* Out-of-bounds accesses are undefined behaviour in the semantics: a `write` operation whose
  bytes do not all lie inside the place, a tag write into a niche field that does not lie inside
  the place, and a read of a byte outside the place all give `none`. (The helper `writeBytes`
  is total and keeps the length of the place; the semantics calls it only on in-bounds ranges.)

* `readDisc L p` reads the niche field and decodes it with the checked decoder of
  `genLayout`: it is undefined behaviour (`none`) if a niche byte is uninitialized, if the
  value lies in the tag range at a dead slot, or if it lies outside the tag range and is
  invalid for the payload; otherwise it returns a variant index.
* `setDisc sem L v`:
  - for `v ≠ u`: writes `v`'s tag into the niche field if `v` is live and in the niche range
    and the niche field lies inside the place, and is undefined behaviour otherwise (both
    semantics);
  - for `v = u`, `Sem.operational`: reads the discriminant and is undefined behaviour unless the
    result is `u`; it writes nothing;
  - for `v = u`, `Sem.erased`: does nothing (no check and no write).
* `run sem L prog` runs a list of operations (`write`, `setDisc`, `readDisc`) on a place,
  collecting the results of `readDisc` in an output list; `none` means undefined behaviour.
-/

namespace Toy.WrapNiche

open Imported

/-- A place: bytes, each uninitialized (`none`) or holding a byte value. -/
abbrev Bytes : Type := List (Option (Fin 256))

/-- Write the bytes `bs` starting at offset `off` (a total helper). The place keeps its length;
bytes that would land at or beyond `p.length` are dropped. The semantics (`stepOp`, `setDisc`)
treats a write that does not fit as undefined behaviour and calls this helper only on in-bounds
ranges. -/
def writeBytes (p : Bytes) (off : Nat) (bs : List (Fin 256)) : Bytes :=
  (List.range p.length).map fun i =>
    if off ≤ i ∧ i < off + bs.length then some (bs.getD (i - off) 0) else p.getD i none

/-- Read `len` bytes starting at `off`: `none` if any of them is uninitialized or outside the
place. -/
def readBytes (p : Bytes) (off len : Nat) : Option (List (Fin 256)) :=
  ((List.range len).map fun j => p.getD (off + j) none).mapM id

/-- Little-endian value of a byte list. -/
def leVal (bs : List (Fin 256)) : Nat := bs.foldr (fun b acc => b.val + 256 * acc) 0

/-- The `w`-byte little-endian encoding of `x` (of `x mod 256 ^ w`). -/
def leBytes (w x : Nat) : List (Fin 256) :=
  (List.range w).map fun j => ⟨x / 256 ^ j % 256, Nat.mod_lt _ (by decide)⟩

/-- An enum layout for the operational semantics: the niche field's offset `no` and width `nw`
(in bytes), the enum shape `E`, the affine encoding `A` on `Pat nw`, and the validity `V` of
the niche field for the untagged variant's payload. The niche field is read and written
little-endian. `nw = 0` is a degenerate edge (`Pat 0` has one value and reading it checks no
byte, so it succeeds even when `no` lies outside the place). -/
structure OpLayout where
  /-- Byte offset of the niche field. -/
  no : Nat
  /-- Width of the niche field in bytes. -/
  nw : Nat
  /-- Enum shape. -/
  E : EnumSpec
  /-- Affine niche encoding. -/
  A : AffineNiche (256 ^ nw)
  /-- Validity of the niche field for the untagged variant's payload. -/
  V : Validity nw

namespace OpLayout

/-- Read the niche field: `none` if any of its bytes is uninitialized or outside the place
(for `nw = 0` there is no byte to check). -/
def readNiche (L : OpLayout) (p : Bytes) : Option (Pat L.nw) :=
  (readBytes p L.no L.nw).map fun bs => ⟨leVal bs % 256 ^ L.nw, Nat.mod_lt _ (pat_card_pos _)⟩

/-- Write the value `x` into the niche field. -/
def writeNiche (L : OpLayout) (p : Bytes) (x : Pat L.nw) : Bytes :=
  writeBytes p L.no (leBytes L.nw x.val)

/-- Read the discriminant with the checked decoder of `genLayout`; `none` is undefined
behaviour. -/
def readDisc (L : OpLayout) (p : Bytes) : Option Nat :=
  match L.readNiche p with
  | none => none
  | some x =>
    ((genLayout L.E L.A L.V).dec x).map fun
      | .inl i => i.val
      | .inr _ => L.E.u

/-- Variant `v` is a live variant other than `u` (inhabited, `v < k`, `v ≠ u`) that the encoding
can tag: it lies in the niche range. -/
def Encodable (L : OpLayout) (v : Nat) : Prop :=
  L.E.Live v ∧ L.A.first ≤ v ∧ v ≤ L.A.first + L.A.span

instance (L : OpLayout) (v : Nat) : Decidable (L.Encodable v) := by
  unfold Encodable; infer_instance

/-- The byte range `[off, off + len)` does not overlap the niche field. This is a sufficient
condition: an empty range (`len = 0`) strictly inside the niche field is rejected although it
overlaps nothing. -/
def DisjointFromNiche (L : OpLayout) (off len : Nat) : Prop :=
  off + len ≤ L.no ∨ L.no + L.nw ≤ off

instance (L : OpLayout) (off len : Nat) : Decidable (L.DisjointFromNiche off len) := by
  unfold DisjointFromNiche; infer_instance

end OpLayout

/-- The two semantics of `SetDiscriminant` for the untagged variant. -/
inductive Sem
  /-- Checks that the place already decodes to the untagged variant. -/
  | operational
  /-- Does nothing for the untagged variant: no check and no write. -/
  | erased
deriving DecidableEq, Repr

/-- `SetDiscriminant v`; `none` is undefined behaviour. -/
def setDisc (sem : Sem) (L : OpLayout) (v : Nat) (p : Bytes) : Option Bytes :=
  if v = L.E.u then
    match sem with
    | .operational => if L.readDisc p = some L.E.u then some p else none
    | .erased => some p
  else if L.Encodable v then
    if L.no + L.nw ≤ p.length then some (L.writeNiche p (L.A.tagOf (v - L.A.first))) else none
  else none

/-- Operations on a place. -/
inductive Op
  /-- Write bytes at an offset (a field write). -/
  | write (off : Nat) (bs : List (Fin 256))
  /-- `SetDiscriminant v`. -/
  | setDisc (v : Nat)
  /-- Read the discriminant and append it to the output. -/
  | readDisc

/-- One operation on a place and an output list; `none` is undefined behaviour (including a
`write` whose bytes do not all lie inside the place). -/
def stepOp (sem : Sem) (L : OpLayout) : Op → Bytes × List Nat → Option (Bytes × List Nat)
  | .write off bs, (p, out) =>
    if off + bs.length ≤ p.length then some (writeBytes p off bs, out) else none
  | .setDisc v, (p, out) => (setDisc sem L v p).map fun p' => (p', out)
  | .readDisc, (p, out) => (L.readDisc p).map fun i => (p, out ++ [i])

/-- Run a program; `none` is undefined behaviour. -/
def run (sem : Sem) (L : OpLayout) : List Op → Bytes × List Nat → Option (Bytes × List Nat)
  | [], s => some s
  | o :: os, s => (stepOp sem L o s).bind (run sem L os)

/-- The field writes of a list of `(offset, bytes)` pairs, as operations. -/
def writesOf (ws : List (Nat × List (Fin 256))) : List Op := ws.map fun w => .write w.1 w.2

end Toy.WrapNiche
