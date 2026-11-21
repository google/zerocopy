/-!
# Toy register lowering: abstract bytes, scalars, representations

This file sets up a Mathlib-free toy model of *representation lowering*: replacing a
byte-level value by one or two backend scalars (a `Scalar` or `ScalarPair` backend
representation) instead of keeping it as a memory blob.

Attribution. The abstract-byte type has the shape of MiniRust's `AbstractByte`
(`Uninit`, and `Init(data, Option<ProvenanceFrag>)` with a fragment carrying a provenance and a
position), and `AByte.leb` is MiniRust's `le_defined` order on abstract bytes. The same
shape is used, with different encodings, by the byte-representation and pointer-provenance
packages of this library; the definitions here are restated, not imported.
-/

namespace Toy.ReprLower

/-! ## Abstract bytes -/

/-- An abstract byte.
* `uninit`: an uninitialized byte (padding, never-written memory); MiniRust `Uninit`.
* `bits b`: an initialized byte with data `b` and no provenance; MiniRust `Init(b, None)`.
* `ptrFrag b prov i`: an initialized byte with data `b` that is byte number `i` of a pointer with
  provenance `prov`; MiniRust `Init(b, Some(ProvenanceFrag { provenance: prov, position: i }))`.

Data is an unbounded `Nat` (no 8-bit wrapping is modelled; no result depends on byte
arithmetic). -/
inductive AByte where
  | uninit
  | bits (b : Nat)
  | ptrFrag (b : Nat) (prov : Nat) (i : Nat)
  deriving DecidableEq, Repr

namespace AByte

/-- "Less or equally defined" (MiniRust `le_defined` on `AbstractByte`): `uninit` is below
everything; `bits b` is below `bits b` and below every fragment with data `b` (adding provenance
makes a byte more defined); a fragment is below only itself. -/
def leb : AByte → AByte → Bool
  | uninit, _ => true
  | bits b, bits c => b == c
  | bits b, ptrFrag c _ _ => b == c
  | ptrFrag b p i, ptrFrag c q j => b == c && p == q && i == j
  | _, _ => false

/-- Whether a byte is initialized (`bits` or `ptrFrag`). -/
def isInit : AByte → Bool
  | uninit => false
  | _ => true

/-- Whether a byte is a pointer fragment (carries provenance). -/
def isFrag : AByte → Bool
  | ptrFrag .. => true
  | _ => false

/-- Whether a byte is a plain data byte without provenance. -/
def isBits : AByte → Bool
  | bits _ => true
  | _ => false

/-- The data of a byte. An `uninit` byte has data `0`; every use of `data` in this package that
can affect a result (lowering, typed reads, range conditions, field validity) is guarded by a
check that the bytes are initialized, so no result depends on this placeholder. -/
def data : AByte → Nat
  | uninit => 0
  | bits b => b
  | ptrFrag b _ _ => b

end AByte

/-- Pointwise `AByte.leb` on byte lists of equal length (MiniRust's order on `List`). -/
def bytesLeb : List AByte → List AByte → Bool
  | [], [] => true
  | a :: as, b :: bs => a.leb b && bytesLeb as bs
  | _, _ => false

/-- `BytesLe x y`: `y` is at least as defined as `x`, byte by byte, and has the same length.
With UB as the top of the refinement order, replacing `x` by `y` is a refinement for every use
that is monotone in this order (see `typedReads_mono_of_bytesLe`). -/
def BytesLe (x y : List AByte) : Prop := bytesLeb x y = true

instance (x y : List AByte) : Decidable (BytesLe x y) :=
  inferInstanceAs (Decidable (bytesLeb x y = true))

/-! ## Segments and byte-list predicates -/

/-- The bytes `[off, off + w)` of `x`, truncated at the end of `x` (`drop` then `take`). -/
def seg (x : List AByte) (off w : Nat) : List AByte := (x.drop off).take w

/-- Every byte is initialized. -/
def allInit (bs : List AByte) : Bool := bs.all AByte.isInit

/-- Every byte is `uninit`. -/
def allUninit (bs : List AByte) : Bool := bs.all (· == .uninit)

/-- Every byte is a plain data byte without provenance. -/
def allBits (bs : List AByte) : Bool := bs.all AByte.isBits

/-- The data bytes, in memory order. -/
def datas (bs : List AByte) : List Nat := bs.map AByte.data

/-- `fragsFrom p k bs`: `bs` is a run of fragments of provenance `p` with positions
`k, k+1, …` in order (true for the empty run). -/
def fragsFrom (p : Nat) : Nat → List AByte → Bool
  | _, [] => true
  | k, .ptrFrag _ q i :: bs => q == p && i == k && fragsFrom p (k + 1) bs
  | _, _ :: _ => false

/-- The provenance of the first byte, if it is a fragment. -/
def fragProv : List AByte → Option Nat
  | .ptrFrag _ p _ :: _ => some p
  | _ => none

/-- Pointer provenance as MiniRust's `decode_ptr` computes it: the common provenance if every
byte is a fragment of it at the matching position (from position `0`), else none. -/
def ptrProv (bs : List AByte) : Option Nat :=
  match fragProv bs with
  | some p => if fragsFrom p 0 bs then some p else none
  | none => none

/-! ## Primitives, scalars, representations -/

/-- A scalar primitive with its width in bytes: an integer or a (thin) pointer. Widths are
arbitrary, including `0`; results that need a positive width say so. -/
inductive Prim where
  | int (w : Nat)
  | ptr (w : Nat)
  deriving DecidableEq, Repr

/-- The width in bytes. -/
def Prim.size : Prim → Nat
  | .int w => w
  | .ptr w => w

/-- One scalar component of a backend representation.
* `initialized p range`: every byte initialized; a pointer scalar carries at most one
  provenance; the data bytes lie in `range` (the toy's stand-in for a valid range: any set of
  data-byte vectors, given as a Boolean predicate on the data bytes in memory order).
* `union p`: may be (partially) uninitialized and has no range (no niche).

Meant to capture `rustc_abi::Scalar::{Initialized, Union}`. -/
inductive Scalar where
  | initialized (p : Prim) (range : List Nat → Bool)
  | union (p : Prim)

/-- The primitive of a scalar. -/
def Scalar.prim : Scalar → Prim
  | .initialized p _ => p
  | .union p => p

/-- The width in bytes of a scalar. -/
def Scalar.size (s : Scalar) : Nat := s.prim.size

/-- A backend representation of a value of byte size `n` (the size is passed separately).
* `scalar s`: one scalar at offset `0`;
* `pair a b bOff`: two scalars in memory order, `a` at offset `0` and `b` at offset `bOff`;
* `memory`: a memory blob.

Meant to capture `rustc_abi::BackendRepr::{Scalar, ScalarPair, Memory}` (vectors omitted). -/
inductive BRepr where
  | scalar (s : Scalar)
  | pair (a b : Scalar) (bOff : Nat)
  | memory

/-- The scalar components with their offsets, in memory order (empty for `memory`). -/
def BRepr.comps : BRepr → List (Nat × Scalar)
  | .scalar s => [(0, s)]
  | .pair a b o => [(0, a), (o, b)]
  | .memory => []

/-- Whether byte `i` lies in a scalar extent (every byte does for `memory`). -/
def BRepr.inExtent : BRepr → Nat → Bool
  | .scalar s, i => decide (i < s.size)
  | .pair a b o, i => decide (i < a.size) || (decide (o ≤ i) && decide (i < o + b.size))
  | .memory, _ => true

/-! ## Register values, lowering and raising -/

/-- A register value for one scalar.
* `poison`: no defined value;
* `int ds`: an integer register with data bytes `ds` (memory order), no provenance;
* `ptr prov ds`: a pointer register with address bytes `ds` and at most one provenance;
* `raw bs`: a `union` scalar's register, which holds abstract bytes as they are (initialized,
  uninitialized or fragments). That a union register can hold every abstract byte, provenance
  fragments included, is a modelling assumption of the toy. -/
inductive RVal where
  | poison
  | int (ds : List Nat)
  | ptr (prov : Option Nat) (ds : List Nat)
  | raw (bs : List AByte)
  deriving DecidableEq, Repr

/-- Lowering initialized bytes to a pointer register, as MiniRust's `decode_ptr` does: the
address bytes are kept, and the provenance is `ptrProv` of the bytes. One pointer's fragments, in
order from position `0`, with one provenance, give a pointer with that provenance; any other
initialized bytes (plain bytes, or fragments with mixed provenance or shifted positions) give a
provenance-free pointer. `lowerScalar` calls it only on all-initialized bytes. -/
def ptrLower (bs : List AByte) : RVal := .ptr (ptrProv bs) (datas bs)

/-- Lowering one scalar's bytes to a register value.
* `union`: the bytes as they are (`raw`).
* `initialized p range`: `poison` unless every byte is initialized and the data lies in `range`
  (a partially or wholly uninitialized scalar, or an out-of-range one, becomes `poison`); then an
  integer scalar drops any provenance (`int`), and a pointer scalar uses `ptrLower` (MiniRust's
  `decode_ptr`: bytes that are not one pointer's fragments in order give a provenance-free
  pointer). -/
def lowerScalar : Scalar → List AByte → RVal
  | .union _, bs => .raw bs
  | .initialized p rng, bs =>
    if allInit bs && rng (datas bs) then
      match p with
      | .int _ => .int (datas bs)
      | .ptr _ => ptrLower bs
    else .poison

/-- Fragments of a pointer with provenance `p` and address bytes `ds`, positions from `k`. -/
def fragsList (p : Nat) : Nat → List Nat → List AByte
  | _, [] => []
  | k, d :: ds => .ptrFrag d p k :: fragsList p (k + 1) ds

/-- Raising one register value back to bytes. `poison` becomes `s.size` uninitialized bytes; an
integer or provenance-free pointer becomes plain bytes; a pointer with provenance becomes its
fragments in order; `raw` bytes are returned as they are. -/
def raiseScalar (s : Scalar) : RVal → List AByte
  | .poison => List.replicate s.size .uninit
  | .int ds => ds.map .bits
  | .ptr none ds => ds.map .bits
  | .ptr (some p) ds => fragsList p 0 ds
  | .raw bs => bs

/-- Lowered values: one register, two registers, or a memory blob. -/
inductive Lowered where
  | one (v : RVal)
  | two (va vb : RVal)
  | mem (bs : List AByte)
  deriving DecidableEq, Repr

/-- Lowering a byte-level value to a representation: each scalar reads its own extent; bytes
outside the extents are not read. `memory` keeps the bytes. -/
def lower : BRepr → List AByte → Lowered
  | .scalar s, x => .one (lowerScalar s (seg x 0 s.size))
  | .pair a b o, x => .two (lowerScalar a (seg x 0 a.size)) (lowerScalar b (seg x o b.size))
  | .memory, x => .mem x

/-- The byte at `i` of a list of chunks `(offset, bytes)`: the first chunk covering `i`, else
`uninit`. -/
def chunkAt : List (Nat × List AByte) → Nat → AByte
  | [], _ => .uninit
  | (o, c) :: cs, i => if o ≤ i ∧ i < o + c.length then c.getD (i - o) .uninit else chunkAt cs i

/-- `n` bytes assembled from chunks; uncovered bytes are `uninit`. -/
def place (n : Nat) (cs : List (Nat × List AByte)) : List AByte :=
  (List.range n).map (chunkAt cs)

/-- Raising a lowered value of byte size `n`: each scalar's bytes are written at its offset and
every other byte (padding) is `uninit`. A `memory` blob is returned as it is. A lowered value of
the wrong shape raises to `n` uninitialized bytes. -/
def raise (n : Nat) : BRepr → Lowered → List AByte
  | .scalar s, .one v => place n [(0, raiseScalar s v)]
  | .pair a b o, .two va vb => place n [(0, raiseScalar a va), (o, raiseScalar b vb)]
  | .memory, .mem bs => bs
  | _, _ => List.replicate n .uninit

/-! ## Refinement and the conditions of the lowering characterization -/

/-- The round trip `raise n r ∘ lower r` refines the identity on every value in `V`: for every
`x` with `V x`, the raised bytes are at least as defined as `x` (`BytesLe`). `V` is the set of
byte-level values a program may hold at the type (for a byte-level move, this includes bytes
written by byte-level transmutes). -/
def RoundTripRefines (n : Nat) (r : BRepr) (V : List AByte → Prop) : Prop :=
  ∀ x, V x → BytesLe x (raise n r (lower r x))

/-- Condition (a): every byte below `n` outside the scalar extents is `uninit` in every value of
`V`. -/
def OutsideExtentsUninit (n : Nat) (r : BRepr) (V : List AByte → Prop) : Prop :=
  ∀ x, V x → ∀ i, i < n → r.inExtent i = false → x.getD i .uninit = .uninit

/-- Per-scalar form of condition (b): an `initialized` scalar's bytes are all initialized or all
uninitialized. -/
def initUniformAt : Scalar → List AByte → Bool
  | .initialized _ _, bs => allInit bs || allUninit bs
  | .union _, _ => true

/-- Condition (b): every `initialized` scalar's bytes are uniformly initialized (all or none) in
every value of `V`. -/
def InitUniform (r : BRepr) (V : List AByte → Prop) : Prop :=
  ∀ x, V x → r.comps.all (fun c => initUniformAt c.2 (seg x c.1 c.2.size)) = true

/-- Per-scalar form of condition (d): if an `initialized` scalar's bytes are all initialized
and not all uninitialized (that is, initialized and non-empty), their data lies in the scalar's
range. Partially initialized bytes are left to condition (b); the data of `uninit` bytes is never
consulted. -/
def rangeInclAt : Scalar → List AByte → Bool
  | .initialized _ rng, bs => allUninit bs || !allInit bs || rng (datas bs)
  | .union _, _ => true

/-- Condition (d): validity implies the range, for every `initialized` scalar of every value in
`V` whose bytes are not all uninitialized. -/
def RangeIncl (r : BRepr) (V : List AByte → Prop) : Prop :=
  ∀ x, V x → r.comps.all (fun c => rangeInclAt c.2 (seg x c.1 c.2.size)) = true

/-- Provenance coherence for a primitive: an integer scalar's bytes carry no pointer fragment;
a pointer scalar's bytes carry no pointer fragment (a provenance-free pointer), or are exactly one
pointer's fragments, in order from position `0`, with one provenance (`ptrProv` is defined). -/
def coherentFor : Prim → List AByte → Bool
  | .int _, bs => !bs.any AByte.isFrag
  | .ptr _, bs => !bs.any AByte.isFrag || (ptrProv bs).isSome

/-- Per-scalar form of condition (c). -/
def provCoherentAt : Scalar → List AByte → Bool
  | .initialized p _, bs => allUninit bs || coherentFor p bs
  | .union _, _ => true

/-- Condition (c): every `initialized` scalar's bytes, unless all uninitialized, are provenance
coherent for its primitive (`coherentFor`), in every value of `V`. -/
def ProvCoherent (r : BRepr) (V : List AByte → Prop) : Prop :=
  ∀ x, V x → r.comps.all (fun c => provCoherentAt c.2 (seg x c.1 c.2.size)) = true

/-! ## Typed reads (uses) -/

/-- A value produced by a typed read. -/
inductive Val where
  | int (ds : List Nat)
  | ptr (prov : Option Nat) (ds : List Nat)
  deriving DecidableEq, Repr

/-- "Less or equally defined" on values (MiniRust): integers must be equal; pointers must have
the same address bytes, and a provenance-free pointer is below every pointer with that
address. -/
def Val.leb : Val → Val → Bool
  | .int a, .int b => a == b
  | .ptr none a, .ptr _ b => a == b
  | .ptr (some p) a, .ptr (some q) b => a == b && p == q
  | _, _ => false

/-- Outcomes ordered with UB (`none`) at the bottom of definedness: a source outcome `none`
permits every target outcome (UB is the top of the refinement order). -/
def OutLe : Option Val → Option Val → Prop
  | none, _ => True
  | some v, some w => v.leb w = true
  | some _, none => False

instance : (a b : Option Val) → Decidable (OutLe a b)
  | none, _ => isTrue trivial
  | some v, some w => inferInstanceAs (Decidable (v.leb w = true))
  | some _, none => isFalse id

/-- A typed integer read of `w` bytes at `off`: UB unless all `w` bytes exist and are
initialized; provenance is ignored. -/
def readInt (off w : Nat) (x : List AByte) : Option Val :=
  if (seg x off w).length = w ∧ allInit (seg x off w) = true then
    some (.int (datas (seg x off w)))
  else none

/-- A typed pointer read of `w` bytes at `off`: UB unless all `w` bytes exist and are
initialized; the provenance is `ptrProv` of the bytes (MiniRust `decode_ptr`). -/
def readPtr (off w : Nat) (x : List AByte) : Option Val :=
  if (seg x off w).length = w ∧ allInit (seg x off w) = true then
    some (.ptr (ptrProv (seg x off w)) (datas (seg x off w)))
  else none

end Toy.ReprLower
