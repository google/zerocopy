import ToyTbaa.Basic

/-!
# The two memory semantics

* **(E) effective types (C-like).** Every allocated byte carries an effective-type state:
  either *allocated storage* with an optional leaf tag (no tag = no effective type yet), or a
  *declared object* whose leaf type is fixed. A store at a non-byte type sets the tags of
  allocated storage; a load is a `type` fault when a byte's tag is incompatible with the
  load's leaf type; a store into a declared object at an incompatible leaf type is a `type`
  fault. Byte (`u8`) accesses are exempt under the standard discipline, and `memcpy` copies
  tags into allocated storage. The compatibility discipline is a parameter (`ECfg`), so that
  the role of the character exemption can be studied.
* **(U) untyped (Rust-like).** Bytes carry no type. A load at `T` succeeds iff the bytes are
  allocated and valid for `T`, and reinterprets them.

Checks run in the order allocation → value validity → effective type, so an effective-type
(`type`) fault in (E) occurs only where (U) has no fault.
-/

namespace Toy.Tbaa

/-! ## Shared helpers -/

/-- Update one register. -/
def updReg (rs : Reg → Val) (r : Reg) (v : Val) : Reg → Val :=
  fun r' => if r' = r then v else rs r'

/-- Apply `f (a - p)` to the contents of every address `a` with `p ≤ a < p + n`. -/
def updRange {α : Type} (m : Nat → Option α) (p n : Nat) (f : Nat → α → α) : Nat → Option α :=
  fun a => if p ≤ a ∧ a < p + n then (m a).map (f (a - p)) else m a

/-- The `n` entries at `p, p+1, …, p+n-1`, or `none` if any of them is unallocated. -/
def readRange {α : Type} (m : Nat → Option α) (p : Nat) : Nat → Option (List α)
  | 0 => some []
  | n + 1 =>
    match m p, readRange m (p + 1) n with
    | some c, some cs => some (c :: cs)
    | _, _ => none

/-! ## (E) Effective-type memory -/

/-- Effective-type state of one byte.
* `alloc t`: allocated storage (no declared type). `t = none` means no effective type yet;
  `t = some s` means the byte currently belongs to an object of leaf type `s`.
* `decl s`: the byte belongs to a declared object whose leaf type `s` is fixed for its
  lifetime. -/
inductive Eff where
  | alloc (tag : Option Scalar)
  | decl (s : Scalar)
  deriving DecidableEq, Repr

/-- The effective-type tag of a byte. -/
def Eff.tag : Eff → Option Scalar
  | .alloc t => t
  | .decl s => some s

/-- A byte of effective-type memory: its value and its effective-type state. -/
structure Cell where
  val : Byte
  eff : Eff
  deriving DecidableEq, Repr

/-- Effective-type memory: `none` = unallocated. -/
abbrev Mem := Nat → Option Cell

/-- State of the effective-type semantics. -/
structure St where
  mem : Mem
  regs : Reg → Val

/-- A compatibility discipline: `c t s` says whether a byte whose effective-type tag is `t`
may be accessed as leaf type `s`. -/
abbrev Compat := Option Scalar → Scalar → Bool

/-- The standard (C-like) discipline: a byte may be accessed at leaf `s` if `s` is the
character type (the exemption), if the byte has no effective type yet, or if its tag is `s`. -/
def stdCompat : Compat
  | _, .u8 => true
  | none, _ => true
  | some a, b => decide (a = b)

/-- The discipline without the character exemption in the access checks: a `u8` access to a
byte with an effective type is checked like any other access (allowed only if the tag is `u8`).
Only the *checks* change: the effect of a byte store on tags is fixed by `storeCell` for every
discipline (a `u8` store into allocated storage keeps the byte's tag), so under this discipline
a `u8` store before a `u32` load of the same allocated bytes is still not separable by types
(see `Results.strict_typed_load_above_byte_store_not_refines`). -/
def strictCompat : Compat
  | none, _ => true
  | some a, b => decide (a = b)

/-- Configuration of the effective-type semantics: the compatibility discipline, and whether
`memcpy` reads and writes its bytes as `u8` accesses subject to that discipline (`true` in the
intended model; `false` gives a copy primitive that bypasses effective-type checks, used only
as a positive control). -/
structure ECfg where
  compat : Compat
  memcpyChecksBytes : Bool

/-- The intended C-like configuration: standard discipline, `memcpy` performs `u8` accesses. -/
def stdCfg : ECfg := ⟨stdCompat, true⟩

/-- Load check: every byte's tag is compatible with the corresponding leaf of `T`. -/
def TagsOk (c : Compat) (cs : List Cell) (T : Ty) : Bool :=
  (cs.zip T.leaves).all fun x => c x.1.eff.tag x.2

/-- Store check: every byte of a declared object accepts the corresponding leaf of `T`.
Allocated storage accepts every store (the store sets its effective type). -/
def DeclOk (c : Compat) (cs : List Cell) (T : Ty) : Bool :=
  (cs.zip T.leaves).all fun x =>
    match x.1.eff with
    | .decl d => c (some d) x.2
    | .alloc _ => true

/-- Effect of a `T`-store of value `v` on the byte at offset `i`: the value is written; the
tag of allocated storage becomes the leaf of `T` at `i`, except that a byte (`u8`) store
leaves the tag unchanged; declared bytes keep their declared type. -/
def storeCell (T : Ty) (v : Val) (i : Nat) (cell : Cell) : Cell :=
  { val := v.getD i 0
    eff := match cell.eff, T.leafAt i with
      | .alloc t, .u8 => .alloc t
      | .alloc _, s => .alloc (some s)
      | .decl d, _ => .decl d }

/-- Effect of `memcpy` on destination byte `cell` receiving source byte `sc`: the value is
copied; allocated storage takes the source byte's tag; declared bytes keep their type. -/
def copyCell (sc cell : Cell) : Cell :=
  { val := sc.val
    eff := match cell.eff with
      | .alloc _ => .alloc sc.eff.tag
      | .decl d => .decl d }

/-- The destination update of `memcpy` from the source bytes `cs` (read before any write). -/
def copyFrom (cs : List Cell) (i : Nat) (cell : Cell) : Cell :=
  match cs[i]? with
  | some sc => copyCell sc cell
  | none => cell

/-- Byte-access check for `memcpy`: every source byte is readable as `u8` and every declared
destination byte accepts a `u8` write. -/
def CopyBytesOk (c : Compat) (cs ds : List Cell) : Bool :=
  cs.all (fun x => c x.eff.tag .u8) &&
  ds.all (fun x => match x.eff with | .decl d => c (some d) .u8 | .alloc _ => true)

/-- One step of the effective-type semantics. -/
def stepE (cfg : ECfg) : Instr → St → Step St
  | .set r v, σ => .next { σ with regs := updReg σ.regs r v }
  | .load r T p, σ =>
    match readRange σ.mem p T.size with
    | none => .fault .base
    | some cs =>
      if T.Valid (cs.map Cell.val) then
        if TagsOk cfg.compat cs T then .next { σ with regs := updReg σ.regs r (cs.map Cell.val) }
        else .fault .type
      else .fault .base
  | .store T p r, σ =>
    match readRange σ.mem p T.size with
    | none => .fault .base
    | some cs =>
      if T.Valid (σ.regs r) then
        if DeclOk cfg.compat cs T then
          .next { σ with mem := updRange σ.mem p T.size (storeCell T (σ.regs r)) }
        else .fault .type
      else .fault .base
  | .memcpy dst src n, σ =>
    match readRange σ.mem src n, readRange σ.mem dst n with
    | some cs, some ds =>
      if !cfg.memcpyChecksBytes || CopyBytesOk cfg.compat cs ds then
        .next { σ with mem := updRange σ.mem dst n (copyFrom cs) }
      else .fault .type
    | _, _ => .fault .base
  | .out r, σ => .emit (σ.regs r) σ

/-! ## (U) Untyped memory -/

/-- Untyped memory: `none` = unallocated. -/
abbrev UMem := Nat → Option Byte

/-- State of the untyped semantics. -/
structure USt where
  mem : UMem
  regs : Reg → Val

/-- One step of the untyped semantics. -/
def stepU : Instr → USt → Step USt
  | .set r v, u => .next { u with regs := updReg u.regs r v }
  | .load r T p, u =>
    match readRange u.mem p T.size with
    | none => .fault .base
    | some bs => if T.Valid bs then .next { u with regs := updReg u.regs r bs } else .fault .base
  | .store T p r, u =>
    match readRange u.mem p T.size with
    | none => .fault .base
    | some _ =>
      if T.Valid (u.regs r) then
        .next { u with mem := updRange u.mem p T.size (fun i _ => (u.regs r).getD i 0) }
      else .fault .base
  | .memcpy dst src n, u =>
    match readRange u.mem src n, readRange u.mem dst n with
    | some bs, some _ =>
      .next { u with mem := updRange u.mem dst n (fun i b => bs.getD i b) }
    | _, _ => .fault .base
  | .out r, u => .emit (u.regs r) u

/-- Forget effective types. -/
def erase (σ : St) : USt := ⟨fun a => (σ.mem a).map Cell.val, σ.regs⟩

/-! ## Predicates used as hypotheses -/

/-- `T` and `U` share no leaf scalar type: no byte of a `T` object can be a byte of the same
scalar type as a byte of a `U` object. (For the toy universe this holds exactly for the
unordered pairs `{u32, f32}`, `{u16, u32}`, `{u16, f32}`, `{u16, pair}` and `{u8, X}` for every
`X ≠ u8`; see `Examples.noCommonLeaf_table`.) It is a per-byte criterion: it is coarser than C's
"neither type is (an aggregate containing) the other" (two distinct structs with a common
member type share a leaf) and it ignores offsets inside aggregates. -/
def NoCommonLeaf (T U : Ty) : Prop := ∀ s, s ∈ T.leaves → s ∉ U.leaves

instance (T U : Ty) : Decidable (NoCommonLeaf T U) :=
  inferInstanceAs (Decidable (∀ s, s ∈ T.leaves → s ∉ U.leaves))

/-- The address ranges `[p, p+n)` and `[q, q+m)` are disjoint. -/
def RangesDisjoint (p n q m : Nat) : Prop := p + n ≤ q ∨ q + m ≤ p

instance (p n q m : Nat) : Decidable (RangesDisjoint p n q m) :=
  inferInstanceAs (Decidable (p + n ≤ q ∨ q + m ≤ p))

/-- Whether a byte belongs to a declared object. -/
def Eff.isDecl : Eff → Bool
  | .decl _ => true
  | .alloc _ => false

/-- Every allocated byte of `[p, p+n)` belongs to a declared object (none is allocated
storage). Execution never changes whether a byte is declared, so this is a property of the
initial state that persists. -/
def DeclaredOn (σ : St) (p n : Nat) : Prop :=
  ∀ i, i < n → (σ.mem (p + i)).all (fun cell => cell.eff.isDecl) = true

instance (σ : St) (p n : Nat) : Decidable (DeclaredOn σ p n) :=
  inferInstanceAs (Decidable (∀ i, i < n → (σ.mem (p + i)).all (fun cell => cell.eff.isDecl) = true))

/-- Dual of `DeclaredOn`: every allocated byte of `[p, p+n)` is allocated storage (none belongs
to a declared object). Unallocated bytes are permitted, as in `DeclaredOn`. Like `DeclaredOn`,
it persists through execution. -/
def AllocatedOn (σ : St) (p n : Nat) : Prop :=
  ∀ i, i < n → (σ.mem (p + i)).all (fun cell => !cell.eff.isDecl) = true

instance (σ : St) (p n : Nat) : Decidable (AllocatedOn σ p n) :=
  inferInstanceAs (Decidable (∀ i, i < n → (σ.mem (p + i)).all (fun cell => !cell.eff.isDecl) = true))

/-- Decide `∃ cs, readRange m p n = some cs ∧ f cs = true` by computing the range. -/
instance decExistsRange {α : Type} (m : Nat → Option α) (p n : Nat) (f : List α → Bool) :
    Decidable (∃ cs, readRange m p n = some cs ∧ f cs = true) :=
  decidable_of_iff ((readRange m p n).any f = true) (by
    cases readRange m p n <;> simp)

/-- A `T`-load from `p` passes the allocation and effective-type checks of discipline `c`. -/
def ReadableAt (c : Compat) (σ : St) (T : Ty) (p : Nat) : Prop :=
  ∃ cs, readRange σ.mem p T.size = some cs ∧ TagsOk c cs T = true

instance (c : Compat) (σ : St) (T : Ty) (p : Nat) : Decidable (ReadableAt c σ T p) :=
  decExistsRange σ.mem p T.size (fun cs => TagsOk c cs T)

/-- The bytes at `[q, q + T.size)` are allocated and every declared byte among them accepts
the corresponding leaf of `T` under the standard discipline (allocated-storage bytes accept
anything). -/
def ReceivesAt (σ : St) (T : Ty) (q : Nat) : Prop :=
  ∃ ds, readRange σ.mem q T.size = some ds ∧ DeclOk stdCompat ds T = true

instance (σ : St) (T : Ty) (q : Nat) : Decidable (ReceivesAt σ T q) :=
  decExistsRange σ.mem q T.size (fun ds => DeclOk stdCompat ds T)

/-- Per-byte check of `MemcpyLoadOk` on `((source byte, destination byte), leaf)`: the leaf must
be compatible with the destination's declared leaf if the destination byte is declared, and
with the source byte's tag otherwise. -/
def memcpyLoadCheck (x : (Cell × Cell) × Scalar) : Bool :=
  match x.1.2.eff with
  | .decl d => stdCompat (some d) x.2
  | .alloc _ => stdCompat x.1.1.eff.tag x.2

/-- Exact precondition for `memcpy q p T.size` followed by a `T`-load from `q` under the
standard discipline: both ranges are allocated, and for each byte offset `i < T.size` the byte
the load will see is compatible with the leaf `T.leafAt i` — the destination's declared leaf if
destination byte `i` belongs to a declared object (its type is not changed by the copy), and the
source byte's tag if destination byte `i` is allocated storage (the copy transfers the tag). It
covers both copying a `T`-object into allocated storage and `memcpy` type punning into a declared
object. -/
def MemcpyLoadOk (σ : St) (T : Ty) (p q : Nat) : Prop :=
  ∃ cs ds,
    readRange σ.mem p T.size = some cs ∧
    readRange σ.mem q T.size = some ds ∧
    ((cs.zip ds).zip T.leaves).all memcpyLoadCheck = true

instance (σ : St) (T : Ty) (p q : Nat) : Decidable (MemcpyLoadOk σ T p q) := by
  unfold MemcpyLoadOk
  cases readRange σ.mem p T.size with
  | none => exact isFalse (by intro ⟨_, _, h, _, _⟩; cases h)
  | some cs =>
    cases readRange σ.mem q T.size with
    | none => exact isFalse (by intro ⟨_, _, _, h, _⟩; cases h)
    | some ds =>
      exact decidable_of_iff (((cs.zip ds).zip T.leaves).all memcpyLoadCheck = true)
        ⟨fun h => ⟨cs, ds, rfl, rfl, h⟩,
         fun ⟨_, _, h1, h2, h3⟩ => by cases h1; cases h2; exact h3⟩

/-- The values stored at `[p, p+n)` (empty if some byte is unallocated). -/
def valsAt (σ : St) (p n : Nat) : List Byte :=
  ((readRange σ.mem p n).getD []).map Cell.val

/-- Boolean form of `TypeFaults`: run `stepE cfg` and report whether the first fault (if
any) is a `type` fault. -/
def typeFaultsB (cfg : ECfg) : List Instr → St → Bool
  | [], _ => false
  | i :: P, σ =>
    match stepE cfg i σ with
    | .fault k => k == .type
    | .next σ' => typeFaultsB cfg P σ'
    | .emit _ σ' => typeFaultsB cfg P σ'

/-- `TypeFaults cfg P σ`: the effective-type execution `stepE cfg` of `P` from `σ` stops at a
`type` fault, i.e. it reaches an access whose bytes are all allocated and whose value is
well-sized but which the effective-type check of `cfg` rejects (a load whose leaf types are
incompatible with the tags, a store into a declared object at an incompatible leaf type, or,
when `memcpy` checks its bytes, a rejected `memcpy` byte access).

This is a verdict of the semantics, not the programming idiom "type punning": reinterpreting
bytes in sanctioned ways (reading any object through `u8` under `stdCfg`, or `memcpy` into a
declared object followed by a load at the declared type) does not type-fault
(`Examples.typeFaults_rejects`), and for a nonstandard `cfg` even a same-type access can
type-fault (`Examples.typeFaults_same_type_nonstandard_cfg`). -/
def TypeFaults (cfg : ECfg) (P : List Instr) (σ : St) : Prop := typeFaultsB cfg P σ = true

instance (cfg : ECfg) (P : List Instr) (σ : St) : Decidable (TypeFaults cfg P σ) :=
  inferInstanceAs (Decidable (typeFaultsB cfg P σ = true))

/-- The untyped execution of `P` from `u` terminates without undefined behaviour. -/
def UDefined (P : List Instr) (u : USt) : Prop := ∃ t, exec stepU P u = .done t

instance (P : List Instr) (u : USt) : Decidable (UDefined P u) :=
  decidable_of_iff ((exec stepU P u).isDone = true) (by
    unfold UDefined; cases exec stepU P u <;> simp [Outcome.isDone])

instance {S : Type} (step : Instr → S → Step S) (P : List Instr) (s : S) (o : Outcome) :
    Decidable (Beh step P s o) :=
  inferInstanceAs (Decidable (Allows (exec step P s) o))

/-! ## Concrete states used by examples and witnesses -/

/-- `n` bytes of allocated storage with no effective type and value `0` at addresses
`p..p+n-1`; every register holds `rv`. -/
def freshAt (p n : Nat) (rv : Val) : St :=
  ⟨fun a => if p ≤ a ∧ a < p + n then some ⟨0, .alloc none⟩ else none, fun _ => rv⟩

/-- `n` bytes of a declared object of leaf type `s` with value `0` at addresses `0..n-1`;
every register holds `rv`. -/
def declSt (s : Scalar) (n : Nat) (rv : Val) : St :=
  ⟨fun a => if a < n then some ⟨0, .decl s⟩ else none, fun _ => rv⟩

/-- A declared `pair` object with value bytes `0` at addresses `0..7` (bytes `0..3` declared
`u32`, bytes `4..7` declared `f32`); every register holds `rv`. -/
def declPairSt (rv : Val) : St :=
  ⟨fun a => if a < 4 then some ⟨0, .decl .u32⟩ else if a < 8 then some ⟨0, .decl .f32⟩ else none,
   fun _ => rv⟩

/-- Replace the register file. -/
def St.withRegs (σ : St) (rs : Reg → Val) : St := ⟨σ.mem, rs⟩

/-- Register file holding `v0` in register `0` and `v1` in every other register. -/
def regs2 (v0 v1 : Val) : Reg → Val := fun r => if r = 0 then v0 else v1

/-- Witness state for the character-exemption results: an object of effective type `T` (value
bytes `0`) at addresses `0..T.size-1` in allocated storage, further untyped allocated storage
up to address `15`, and every register holding `T.size` bytes of value `1`. -/
def objSt (T : Ty) : St :=
  ⟨fun a => if a < T.size then some ⟨0, .alloc (some (T.leafAt a))⟩
            else if a < 16 then some ⟨0, .alloc none⟩ else none,
   fun _ => List.replicate T.size 1⟩

end Toy.Tbaa
