/-!
# Toy model of memory reinterpretation: types as bit-validity predicates

This module fixes the vocabulary of the package.

* A *type* of size `n` over a byte alphabet `B` is modelled only by its **bit validity**:
  a predicate on `n`-byte sequences (`Validity B n`). This captures a language's
  *validity invariant* (the bytes a value of the type may consist of without immediate
  undefined behaviour). Alignment, provenance, padding and uninitialised bytes, pointer
  metadata, and aliasing rules are not modelled.
* Both the original typed view (`Side.src`, typed at the source type `T`) and the
  reinterpreted view (`Side.dst`, typed at the destination type `U`) look at the **same**
  single region of `n` bytes. Sizes are equal by construction: casts between types of
  different sizes cannot be expressed in this model.
* A program run against the region is a finite list of operations (`Op`): a typed read
  through one of the two views, or a typed write of a whole byte sequence through one of
  the two views. A write is *well typed* when the written bytes are valid at the writer's
  type (`Op.WellTyped`): this is all that code using only well-typed references can do.
* `NoInvalidRead T U m tr` says that running `tr` from initial contents `m` never reads a
  byte sequence that is invalid at the type of the view it is read through.
* A *cast discipline* (`Protocol`) says which operation sequences may happen while the
  cast is in effect; `Sound P T U` is the safety contract: from every `T`-valid initial
  value, every permitted, well-typed run never observes invalid bytes. A run starts at the
  moment the cast is performed; what happened to the region before the cast is summarised
  by the initial contents.
* `CheckedSound P T U` is the same contract for a cast that is *checked once at cast time*:
  only initial contents that are valid at both `T` and `U` are considered (the check
  rejected everything else), and the run after the check is unchecked. This models
  fallible conversions that validate the bytes once and then hand out an ordinary value or
  reference.
* Values are flat byte sequences: a value whose bytes encode a pointer to other memory is
  modelled only through its own bytes; the memory it points to is not part of the model.

The four disciplines of interest (value transmute, shared-reference cast, mutable-reference
cast, shared-reference cast with interior mutability) are defined at the end of this file.
-/

namespace Toy.Transmute

/-- An `n`-byte sequence over the byte alphabet `B` (the contents of one memory region). -/
abbrev Bytes (B : Type) (n : Nat) := Fin n → B

/-- The bit validity of a type of size `n`: which `n`-byte sequences are valid
representations of a value of the type. Meant to capture a language's *validity invariant*
(not its library-level *safety invariant*). -/
abbrev Validity (B : Type) (n : Nat) := Bytes B n → Prop

/-- Validity inclusion: every `T`-valid byte sequence is `U`-valid. Meant to capture
"every bit pattern of `T` is a bit pattern of `U`". -/
def Includes {B : Type} {n : Nat} (T U : Validity B n) : Prop :=
  ∀ m, T m → U m

/-- Extensional validity equality: `T` and `U` accept exactly the same byte sequences.
This is extensional, not syntactic: two differently written predicates can be equal. -/
def ValidityEq {B : Type} {n : Nat} (T U : Validity B n) : Prop :=
  ∀ m, T m ↔ U m

/-- A type is satisfiable (inhabited at the byte level) when some byte sequence is valid
for it. An uninhabited type (such as an empty enumeration) is not satisfiable. -/
def Satisfiable {B : Type} {n : Nat} (T : Validity B n) : Prop :=
  ∃ m, T m

/-- The two views of the region: `src` is the original reference/owner, typed at the source
type; `dst` is the reinterpreted reference/value, typed at the destination type. -/
inductive Side where
  /-- The original view, typed at the source type. -/
  | src
  /-- The reinterpreted view, typed at the destination type. -/
  | dst
  deriving DecidableEq, Repr

/-- The type a view is typed at, given source type `T` and destination type `U`. -/
def Side.ty {B : Type} {n : Nat} (T U : Validity B n) : Side → Validity B n
  | .src => T
  | .dst => U

/-- One operation on the shared region: a typed read through a view, or a typed write of a
whole byte sequence through a view. -/
inductive Op (B : Type) (n : Nat) where
  /-- Read the whole region through view `s`, at that view's type. -/
  | read (s : Side)
  /-- Overwrite the whole region with `v` through view `s`. -/
  | write (s : Side) (v : Bytes B n)

/-- The view an operation goes through. -/
def Op.side {B : Type} {n : Nat} : Op B n → Side
  | .read s => s
  | .write s _ => s

/-- An operation is a read. -/
def Op.IsRead {B : Type} {n : Nat} : Op B n → Prop
  | .read _ => True
  | .write _ _ => False

/-- A well-typed operation: a write through a view stores bytes that are valid at that
view's type. Reads are always well typed (whether they *observe* valid bytes is what
`NoInvalidRead` checks). This captures "safe code writes only valid values of the type it
holds a reference to". -/
def Op.WellTyped {B : Type} {n : Nat} (T U : Validity B n) : Op B n → Prop
  | .read _ => True
  | .write s v => s.ty T U v

/-- Running the operations `tr` from region contents `m`, every read observes a byte
sequence that is valid at the type of the view it is read through. A read of invalid bytes
models the undefined behaviour of producing an invalid value.

Validity is checked only at reads: a run that never reads, or overwrites the contents
before reading them, is not affected by invalid initial contents (see
`noInvalidRead_unchecked_until_read`). Cast-time validity is nevertheless enforced by
`Sound`, which quantifies over every permitted run, including the run that reads through
the cast view immediately (`readDst`). -/
def NoInvalidRead {B : Type} {n : Nat} (T U : Validity B n) :
    Bytes B n → List (Op B n) → Prop
  | _, [] => True
  | m, .read s :: rest => s.ty T U m ∧ NoInvalidRead T U m rest
  | _, .write _ v :: rest => NoInvalidRead T U v rest

/-- A cast discipline: the set of operation sequences that may be performed on the region
while the cast is in effect. It constrains only *which views* perform *which kinds* of
operation; well-typedness of writes is imposed separately by `Sound`. -/
abbrev Protocol (B : Type) (n : Nat) := List (Op B n) → Prop

/-- The safety contract for a cast discipline `P` from source type `T` to destination type
`U`: starting from any `T`-valid contents, every permitted run whose writes are well typed
never reads invalid bytes. This is "a program that only reads and writes through well-typed
views never observes invalid bytes for the type it reads at", specialised to `P`. -/
def Sound {B : Type} {n : Nat} (P : Protocol B n) (T U : Validity B n) : Prop :=
  ∀ m, T m → ∀ tr, P tr → (∀ op ∈ tr, op.WellTyped T U) → NoInvalidRead T U m tr

/-! ## The four cast disciplines -/

/-- **Value transmute** `T → U`: the source value is moved into the destination, which owns
the bytes from then on and may read and write them at `U`. The source view performs no
operation on these bytes afterwards (a source that is copied keeps an independent copy,
which is a different region). The empty run is permitted; the requirement that the
transmuted value be valid at once is recovered because `Sound` also quantifies over the
run that reads immediately (`readDst`). -/
def valueProtocol {B : Type} {n : Nat} : Protocol B n :=
  fun tr => ∀ op ∈ tr, op.side = .dst

/-- **Shared-reference cast without interior mutability** `&T → &U`: both the original
reference and the cast reference may read, in any interleaving; nobody writes. -/
def sharedProtocol {B : Type} {n : Nat} : Protocol B n :=
  fun tr => ∀ op ∈ tr, op.IsRead

/-- **Mutable-reference cast** `&mut T → &mut U`: first the cast reference is used
exclusively (reads and writes at `U`); after it is dropped, the original owner uses the
bytes again (reads and writes at `T`). The two periods do not interleave. A run starts when
the cast reference is created: whatever the owner did before the cast is summarised by the
initial contents, and the owner may not act while the cast reference is still to be used. -/
def mutProtocol {B : Type} {n : Nat} : Protocol B n :=
  fun tr => ∃ during after, tr = during ++ after ∧
    (∀ op ∈ during, op.side = .dst) ∧ (∀ op ∈ after, op.side = .src)

/-- Which writes a shared cast with interior mutability permits: reads through either view
are always permitted; a write through the source view is permitted iff `srcWrites`, and a
write through the destination view iff `dstWrites`. -/
def Op.PermittedIM {B : Type} {n : Nat} (srcWrites dstWrites : Bool) : Op B n → Prop
  | .read _ => True
  | .write .src _ => srcWrites = true
  | .write .dst _ => dstWrites = true

/-- **Shared-reference cast with interior mutability**: both references stay live and may
be used in any interleaving; each side may additionally write when its flag is set (for
instance, the side whose type has an interior-mutable cell over the region). With both
flags `false` this is `sharedProtocol` (see `sharedIMProtocol_false_false`). -/
def sharedIMProtocol {B : Type} {n : Nat} (srcWrites dstWrites : Bool) : Protocol B n :=
  fun tr => ∀ op ∈ tr, op.PermittedIM srcWrites dstWrites

/-- Soundness of a value transmute from `T` to `U`. -/
def ValueSound {B : Type} {n : Nat} (T U : Validity B n) : Prop := Sound valueProtocol T U

/-- Soundness of a shared-reference cast (no interior mutability) from `T` to `U`. -/
def SharedSound {B : Type} {n : Nat} (T U : Validity B n) : Prop := Sound sharedProtocol T U

/-- Soundness of a mutable-reference cast from `T` to `U`. -/
def MutSound {B : Type} {n : Nat} (T U : Validity B n) : Prop := Sound mutProtocol T U

/-- Soundness of a shared-reference cast with interior mutability from `T` to `U`, with the
given write permissions for the source and destination sides. -/
def SharedIMSound {B : Type} {n : Nat} (srcWrites dstWrites : Bool) (T U : Validity B n) :
    Prop :=
  Sound (sharedIMProtocol srcWrites dstWrites) T U

/-- **Checked (entry-validated) cast.** The safety contract for a cast discipline `P` from `T`
to `U` when the cast performs a run-time validity check once, at the moment of the cast: the
cast goes ahead only on contents that are valid at `T` (they hold a source value) *and* at
`U` (the check succeeded). After the check, the run is unchecked, exactly as in `Sound`:
well-typed writes through either permitted view, reads through either permitted view. This
models fallible conversions that validate once and then return an ordinary value or
reference. -/
def CheckedSound {B : Type} {n : Nat} (P : Protocol B n) (T U : Validity B n) : Prop :=
  ∀ m, T m → U m → ∀ tr, P tr → (∀ op ∈ tr, op.WellTyped T U) → NoInvalidRead T U m tr

/-! ## Validity as a lattice -/

/-- Meet of validities: valid for both types (the intersection of the bit patterns). -/
def Validity.meet {B : Type} {n : Nat} (T U : Validity B n) : Validity B n :=
  fun m => T m ∧ U m

/-- Join of validities: valid for either type (the union of the bit patterns). In this toy
model this is the validity of a hypothetical "either `T` or `U`" type; it is **not** the
validity of a language-level union type, whose validity requirements may be weaker. -/
def Validity.join {B : Type} {n : Nat} (T U : Validity B n) : Validity B n :=
  fun m => T m ∨ U m

/-! ## Concrete one-byte types over `Fin 256` -/

/-- The one-byte sequence whose only byte is `x`. -/
def byteSeq (x : Fin 256) : Bytes (Fin 256) 1 := fun _ => x

/-- A `bool`-like one-byte type: valid iff the byte is `0` or `1`. -/
def boolV : Validity (Fin 256) 1 := fun m => m 0 = 0 ∨ m 0 = 1

/-- The same bit validity as `boolV`, written differently (byte value below `2`). Used to
check that statements depend on validity extensionally, not on its syntax. -/
def boolV' : Validity (Fin 256) 1 := fun m => (m 0).val < 2

/-- A raw initialised byte: every byte value is valid. -/
def byteV : Validity (Fin 256) 1 := fun _ => True

/-- An uninhabited one-byte type: no byte value is valid. -/
def neverV : Validity (Fin 256) 1 := fun _ => False

/-- A one-byte type whose only valid byte is `0` (a unit-like enumeration). -/
def zeroV : Validity (Fin 256) 1 := fun m => m 0 = 0

/-- A one-byte type whose only valid byte is `2`. -/
def twoV : Validity (Fin 256) 1 := fun m => m 0 = 2

end Toy.Transmute
