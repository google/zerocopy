/-!
# Abstract bytes, the definedness order, and representations

This module fixes the vocabulary of the package (namespace `Toy.Repr`).

* `AByte D` models one byte of memory in the style of MiniRust's "abstract bytes":
  either `uninit` (e.g. a padding byte, or memory never written), or `init d` with
  payload `d : D`. In the provenance-free model `D` is a plain byte value (e.g. `UInt8`);
  in the provenance model (module `ToyRepr.Provenance`) `D` is a pair
  `(byte value, optional provenance tag)`.
* The *definedness order* `x ⊑ y` ("`y` is at least as defined as `x`") has
  `uninit ⊑ x` for every `x`, and `init a ⊑ init b ↔ a = b`; it is lifted pointwise to
  fixed-length byte vectors `Bytes D n`.
* A *representation* `Rep α V` of a value type `V` in a carrier `α` (usually `Bytes D n`)
  is a pair `encode : V → α`, `decode : α → Option V`. The three laws
  `DecodeMono`, `DecodeEncode`, `EncodeLeast` are kept as separate propositions.
* Byte-level "trait" predicates: `IntoBytes` (no encoding contains `uninit`),
  `FromBytes` (every fully initialized byte vector decodes), and the partial cast
  `tryFrom` from fully initialized byte data.
* `transmute ra rb := rb.decode ∘ ra.encode` for two representations in the same carrier
  (so in particular of the same size).
-/

namespace Toy.Repr

/-! ## Definedness relations -/

/-- A carrier equipped with a *definedness* relation `x ⊑ y`, read "`y` is at least as
defined as `x`". Representation laws are stated against this relation. No order axioms are
bundled. Results stated for an arbitrary `[Definedness α]` (R1e, R5a, R5b) use no property of
the relation at all; the remaining results are stated for the concrete carriers below. Every
concrete instance in this package is a partial order, with reflexivity, transitivity and
antisymmetry proved: `AByte.le_refl`/`le_trans`/`le_antisymm`, `Bytes.le_refl`/`le_trans`/
`le_antisymm`, `OptLe.refl`/`trans`/`antisymm`, and `PBytesInc.le_refl`/`le_trans`/
`le_antisymm` (module `ToyRepr.Provenance`). -/
class Definedness (α : Type) where
  /-- `le x y` means `y` is at least as defined as `x`. -/
  le : α → α → Prop

@[inherit_doc] scoped infix:50 " ⊑ " => Definedness.le

/-! ## Abstract bytes -/

/-- An abstract byte: `uninit` (no defined value, e.g. padding or never-written memory),
or `init d` carrying the payload `d : D` of an initialized byte. -/
inductive AByte (D : Type) where
  /-- An uninitialized byte. -/
  | uninit : AByte D
  /-- An initialized byte with payload `d`. -/
  | init (d : D) : AByte D
  deriving DecidableEq

namespace AByte

variable {D : Type}

/-- The definedness order on abstract bytes (flat above `uninit`):
`uninit ⊑ x` for all `x`; `init a ⊑ init b` iff `a = b`; `init a ⋢ uninit`. -/
def le : AByte D → AByte D → Prop
  | uninit, _ => True
  | init a, init b => a = b
  | init _, uninit => False

instance : Definedness (AByte D) := ⟨AByte.le⟩

/-- Whether an abstract byte is initialized. -/
def isInit : AByte D → Bool
  | uninit => false
  | init _ => true

/-- The payload of an initialized byte. -/
def get : (b : AByte D) → b.isInit = true → D
  | init d, _ => d

theorem le_def (x y : AByte D) : (x ⊑ y) = AByte.le x y := rfl

instance decLe [DecidableEq D] : (x y : AByte D) → Decidable (x ⊑ y)
  | uninit, _ => isTrue trivial
  | init a, init b => if h : a = b then isTrue h else isFalse h
  | init _, uninit => isFalse id

@[simp] theorem uninit_le (x : AByte D) : (uninit : AByte D) ⊑ x := trivial

@[simp] theorem init_le_init_iff (a b : D) : (init a : AByte D) ⊑ init b ↔ a = b := Iff.rfl

@[simp] theorem not_init_le_uninit (a : D) : ¬ ((init a : AByte D) ⊑ uninit) := fun h => h

theorem le_refl (x : AByte D) : x ⊑ x := by
  cases x
  · exact trivial
  · exact rfl

theorem le_trans {x y z : AByte D} (hxy : x ⊑ y) (hyz : y ⊑ z) : x ⊑ z := by
  cases x with
  | uninit => exact trivial
  | init a =>
    cases y with
    | uninit => exact absurd hxy (not_init_le_uninit a)
    | init b =>
      cases z with
      | uninit => exact absurd hyz (not_init_le_uninit b)
      | init c =>
        have h1 : a = b := hxy
        have h2 : b = c := hyz
        show a = c
        rw [h1, h2]

theorem le_antisymm {x y : AByte D} (hxy : x ⊑ y) (hyx : y ⊑ x) : x = y := by
  cases x with
  | uninit =>
    cases y with
    | uninit => rfl
    | init b => exact absurd hyx (not_init_le_uninit b)
  | init a =>
    cases y with
    | uninit => exact absurd hxy (not_init_le_uninit a)
    | init b =>
      have h : a = b := hxy
      rw [h]

@[simp] theorem le_uninit_iff {x : AByte D} : x ⊑ uninit ↔ x = uninit := by
  cases x with
  | uninit => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | init a => exact ⟨fun h => absurd h (not_init_le_uninit a), fun h => by cases h⟩

@[simp] theorem init_le_iff {a : D} {y : AByte D} : (init a : AByte D) ⊑ y ↔ y = init a := by
  cases y with
  | uninit => exact ⟨fun h => absurd h (not_init_le_uninit a), fun h => by cases h⟩
  | init b =>
    constructor
    · intro h
      have h' : a = b := h
      rw [h']
    · intro h
      cases h
      exact rfl

/-- An initialized byte is maximal: anything at least as defined is equal to it. -/
theorem eq_of_le_of_isInit {x y : AByte D} (hxy : x ⊑ y) (hx : x.isInit = true) : y = x := by
  cases x with
  | uninit => cases hx
  | init a => exact init_le_iff.mp hxy

@[simp] theorem isInit_init (d : D) : (init d).isInit = true := rfl

@[simp] theorem isInit_uninit : (uninit : AByte D).isInit = false := rfl

theorem isInit_iff_ne_uninit (x : AByte D) : x.isInit = true ↔ x ≠ uninit := by
  cases x with
  | uninit => exact ⟨fun h => (by cases h), fun h => absurd rfl h⟩
  | init d => exact ⟨fun _ h => (by cases h), fun _ => rfl⟩

@[simp] theorem get_init (d : D) (h : (init d).isInit = true) : (init d).get h = d := rfl

theorem init_get (b : AByte D) (h : b.isInit = true) : init (b.get h) = b := by
  cases b with
  | uninit => cases h
  | init d => rfl

theorem get_eq_of_eq_init {b : AByte D} {d : D} (h : b.isInit = true) (hb : b = init d) :
    b.get h = d := by
  subst hb
  rfl

end AByte

/-! ## Byte vectors -/

/-- Fixed-length vectors of abstract bytes. -/
abbrev Bytes (D : Type) (n : Nat) := Vector (AByte D) n

/-- The pointwise lift of the byte definedness order to byte vectors. -/
instance {D : Type} {n : Nat} : Definedness (Bytes D n) :=
  ⟨fun x y => ∀ (i : Nat) (h : i < n), x[i] ⊑ y[i]⟩

namespace Bytes

variable {D : Type} {n : Nat}

theorem le_def (x y : Bytes D n) : (x ⊑ y) = ∀ (i : Nat) (h : i < n), x[i] ⊑ y[i] := rfl

instance decLe [DecidableEq D] (x y : Bytes D n) : Decidable (x ⊑ y) :=
  inferInstanceAs (Decidable (∀ (i : Nat) (h : i < n), x[i] ⊑ y[i]))

theorem le_one {x y : Bytes D 1} (h0 : x[0] ⊑ y[0]) : x ⊑ y := by
  intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  exact h0

theorem le_two {x y : Bytes D 2} (h0 : x[0] ⊑ y[0]) (h1 : x[1] ⊑ y[1]) : x ⊑ y := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · exact h0
  · exact h1

theorem le_refl (x : Bytes D n) : x ⊑ x := fun i _ => AByte.le_refl x[i]

theorem le_trans {x y z : Bytes D n} (hxy : x ⊑ y) (hyz : y ⊑ z) : x ⊑ z :=
  fun i h => AByte.le_trans (hxy i h) (hyz i h)

theorem le_antisymm {x y : Bytes D n} (hxy : x ⊑ y) (hyx : y ⊑ x) : x = y :=
  Vector.ext fun i h => AByte.le_antisymm (hxy i h) (hyx i h)

/-- The all-`uninit` byte vector. -/
def uninit (n : Nat) : Bytes D n := Vector.replicate n .uninit

theorem uninit_le (x : Bytes D n) : (uninit n : Bytes D n) ⊑ x := by
  intro i h
  simp [uninit]

/-- A byte vector is fully initialized (contains no `uninit` byte). -/
def IsInit (x : Bytes D n) : Prop := ∀ (i : Nat) (h : i < n), x[i].isInit = true

instance (x : Bytes D n) : Decidable x.IsInit :=
  inferInstanceAs (Decidable (∀ (i : Nat) (h : i < n), x[i].isInit = true))

/-- A fully initialized byte vector is maximal in the definedness order. -/
theorem eq_of_le_of_isInit {x y : Bytes D n} (hxy : x ⊑ y) (hx : x.IsInit) : y = x :=
  Vector.ext fun i h => AByte.eq_of_le_of_isInit (hxy i h) (hx i h)

/-- The byte vector whose bytes are all initialized with the given data. -/
def ofData (ds : Vector D n) : Bytes D n := ds.map .init

@[simp] theorem getElem_ofData (ds : Vector D n) (i : Nat) (h : i < n) :
    (ofData ds)[i] = .init ds[i] := by
  simp [ofData]

theorem ofData_singleton (a : D) : ofData #v[a] = (#v[.init a] : Bytes D 1) := by
  apply Vector.ext
  intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  simp

theorem ofData_pair (a b : D) : ofData #v[a, b] = (#v[.init a, .init b] : Bytes D 2) := by
  apply Vector.ext
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp

theorem isInit_one {x : Bytes D 1} (h0 : x[0].isInit = true) : x.IsInit := by
  intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  exact h0

theorem isInit_two {x : Bytes D 2} (h0 : x[0].isInit = true) (h1 : x[1].isInit = true) :
    x.IsInit := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · exact h0
  · exact h1

theorem isInit_ofData (ds : Vector D n) : (ofData ds).IsInit := by
  intro i h
  simp

/-- The data of a fully initialized byte vector (`none` if some byte is `uninit`). -/
def toData? (x : Bytes D n) : Option (Vector D n) :=
  if h : x.IsInit then some (Vector.ofFn fun i => x[i.val].get (h i.val i.isLt)) else none

theorem toData?_ofData (ds : Vector D n) : toData? (ofData ds) = some ds := by
  unfold toData?
  rw [dite_eq_left_of_eq_true (eq_true (isInit_ofData ds))]
  congr 1
  apply Vector.ext
  intro i h
  rw [Vector.getElem_ofFn]
  exact AByte.get_eq_of_eq_init _ (getElem_ofData ds i h)

theorem ofData_of_toData? {x : Bytes D n} {ds : Vector D n} (h : toData? x = some ds) :
    x = ofData ds := by
  unfold toData? at h
  split at h
  · rename_i hinit
    cases h
    apply Vector.ext
    intro i hi
    simp only [getElem_ofData, Vector.getElem_ofFn]
    exact (AByte.init_get _ _).symm
  · cases h

theorem toData?_eq_none_of_not_isInit {x : Bytes D n} (h : ¬ x.IsInit) : toData? x = none := by
  unfold toData?
  rw [dite_eq_right_of_eq_false (eq_false h)]

/-- Every fully initialized byte vector is `ofData` of some data. -/
theorem exists_ofData_of_isInit {x : Bytes D n} (h : x.IsInit) : ∃ ds, x = ofData ds := by
  refine ⟨Vector.ofFn fun i => x[i.val].get (h i.val i.isLt), ?_⟩
  apply ofData_of_toData?
  unfold toData?
  rw [dite_eq_left_of_eq_true (eq_true h)]

end Bytes

/-! ## The flat order on decoding results -/

/-- The definedness order on decoding results (flat): `none ⊑ o` for every `o`;
`some v ⊑ some w` iff `v = w`; `some v ⋢ none`. With this order, "decode is monotone"
says: making bytes more defined never makes a successful decode fail, and never changes
the decoded value. Value types here carry no order of their own, so distinct values are never
comparable. (MiniRust instead orders values non-flatly, e.g. a pointer without provenance lies
below the same address with provenance; such value orders appear in this package only through
`Rep.DecodeMonoBy` in `ToyRepr.Provenance`.) -/
def OptLe {V : Type} : Option V → Option V → Prop
  | none, _ => True
  | some v, some w => v = w
  | some _, none => False

instance {V : Type} : Definedness (Option V) := ⟨OptLe⟩

namespace OptLe

variable {V : Type}

@[simp] theorem none_le (o : Option V) : (none : Option V) ⊑ o := trivial

instance decLe [DecidableEq V] : (o o' : Option V) → Decidable (o ⊑ o')
  | none, _ => isTrue trivial
  | some v, some w => if h : v = w then isTrue h else isFalse h
  | some _, none => isFalse id

theorem refl (o : Option V) : o ⊑ o := by
  cases o
  · exact trivial
  · exact rfl

@[simp] theorem some_le_iff {v : V} {o : Option V} : (some v : Option V) ⊑ o ↔ o = some v := by
  cases o with
  | none => exact ⟨fun h => absurd h id, fun h => by cases h⟩
  | some w =>
    constructor
    · intro h
      have h' : v = w := h
      rw [h']
    · intro h
      cases h
      exact rfl

theorem trans {o₁ o₂ o₃ : Option V} (h₁ : o₁ ⊑ o₂) (h₂ : o₂ ⊑ o₃) : o₁ ⊑ o₃ := by
  cases o₁ with
  | none => exact trivial
  | some v =>
    have e₂ : o₂ = some v := some_le_iff.mp h₁
    subst e₂
    exact h₂

theorem antisymm {o₁ o₂ : Option V} (h₁ : o₁ ⊑ o₂) (h₂ : o₂ ⊑ o₁) : o₁ = o₂ := by
  cases o₁ with
  | none =>
    cases o₂ with
    | none => rfl
    | some w => exact some_le_iff.mp h₂
  | some v => exact (some_le_iff.mp h₁).symm

end OptLe

/-! ## Representations and their laws -/

/-- A *representation* of values of type `V` in a carrier `α` (usually `Bytes D n`, i.e. the
`n` bytes a value of type `V` occupies): an encoder `encode : V → α` and a partial decoder
`decode : α → Option V` (`none` = the bytes are not a valid `V`).

Modeling notes. `decode` depends on the bytes only: machine-state-dependent validity (e.g.
MiniRust's separate `check_value` step, used for dereferenceability of references) is not
modeled. MiniRust lists a fourth generic law, monotonicity of `encode` with respect to a value
order; with the flat value order used here (distinct values incomparable) that law holds for
every encoder, so only three laws appear. -/
structure Rep (α V : Type) where
  /-- Bytes produced when storing a value. -/
  encode : V → α
  /-- Value read back from bytes, if the bytes are valid. -/
  decode : α → Option V

namespace Rep

variable {α V : Type}

/-- **Decode monotonicity** (flat `Option` order): if `x ⊑ y` then `decode x ⊑ decode y`,
i.e. whenever `decode x = some v`, also `decode y = some v`. More-defined bytes never decode
to a different value, and never fail where less-defined bytes succeeded. -/
def DecodeMono [Definedness α] (r : Rep α V) : Prop :=
  ∀ x y : α, x ⊑ y → r.decode x ⊑ r.decode y

/-- **Decode monotonicity with respect to a given order `leV` on decoding results.** Used to
state monotonicity for non-flat value orders (e.g. MiniRust's pointer order, where a pointer
without provenance lies below the same address with provenance). `DecodeMono` is the special case
of the flat order (`Rep.decodeMono_iff_decodeMonoBy`). -/
def DecodeMonoBy [Definedness α] (r : Rep α V) (leV : Option V → Option V → Prop) : Prop :=
  ∀ x y : α, x ⊑ y → leV (r.decode x) (r.decode y)

theorem decodeMono_iff_decodeMonoBy [Definedness α] (r : Rep α V) :
    r.DecodeMono ↔ r.DecodeMonoBy (fun o o' => o ⊑ o') := Iff.rfl

/-- **Lossless encoding**: `decode (encode v) = some v` for every `v`. -/
def DecodeEncode (r : Rep α V) : Prop :=
  ∀ v : V, r.decode (r.encode v) = some v

/-- **Encode is least**: whenever `decode x = some v`, `encode v ⊑ x` (the encoder never
writes more defined bytes than needed; e.g. padding it does not need is left `uninit`). -/
def EncodeLeast [Definedness α] (r : Rep α V) : Prop :=
  ∀ (x : α) (v : V), r.decode x = some v → r.encode v ⊑ x

/-- **Lower-adjoint (Galois) form**: `encode v ⊑ x ↔ decode x = some v` for all `v, x`.
`encode : V → α` and `decode : α → Option V` do not have mutually inverse types; the standard
Galois-connection reading is obtained by extending `encode` to `Option V` with
`none ↦ ⊥` (for byte vectors, `Bytes.uninit n`), see `Rep.lowerAdjoint_iff_galois_liftEncode`.
The lifted pair need not be a Galois insertion or coinsertion: `decode (Bytes.uninit n)` may be
`some v` (a pure-padding type). -/
def LowerAdjoint [Definedness α] (r : Rep α V) : Prop :=
  ∀ (v : V) (x : α), r.encode v ⊑ x ↔ r.decode x = some v

/-- The *validity set* of a representation: carrier elements that decode successfully. -/
def Valid (r : Rep α V) (x : α) : Prop := ∃ v, r.decode x = some v

/-- The *image* of the encoder. -/
def Image (r : Rep α V) (x : α) : Prop := ∃ v, r.encode v = x

/-- `decode` ignores byte `i`: overwriting byte `i` with anything does not change the result
(byte `i` is padding for this decoder). -/
def DecodeIgnores {D : Type} {n : Nat} (r : Rep (Bytes D n) V) (i : Nat) (hi : i < n) : Prop :=
  ∀ (x : Bytes D n) (b : AByte D), r.decode (x.set i b hi) = r.decode x

/-- **`IntoBytes`** (semantic): no encoding contains an `uninit` byte, so every value can be
viewed as plain initialized bytes. Named after zerocopy's `IntoBytes`, with one divergence: when
the byte payload `D` carries pointer provenance (`PBytes` in `ToyRepr.Provenance`), "initialized"
includes bytes that carry provenance, so a pointer representation can be `IntoBytes` here, while
zerocopy's `IntoBytes` (sound conversion to `&[u8]`) is not implemented for raw pointers. -/
def IntoBytes {D : Type} {n : Nat} (r : Rep (Bytes D n) V) : Prop :=
  ∀ v : V, (r.encode v).IsInit

/-- **`FromBytes`** (semantic): every fully initialized byte vector decodes to some value. When
`D` carries provenance, this quantifies over bytes with provenance too (reading pointer bytes at
the type), which is stronger than zerocopy's `FromBytes` (conversion from `&[u8]`, i.e. from
valid `u8` bytes). -/
def FromBytes {D : Type} {n : Nat} (r : Rep (Bytes D n) V) : Prop :=
  ∀ x : Bytes D n, x.IsInit → ∃ v, r.decode x = some v

/-- The partial cast from fully initialized byte data (`TryFromBytes`-style): decode the
bytes `init ds[0], …, init ds[n-1]`. Every representation has this partial function;
`FromBytes` says it is total. Unlike zerocopy's `TryFromBytes`, whose runtime check may reject
bit-valid values (it is documented as not symmetric with `IntoBytes`), `tryFrom` is the exact
decoder on initialized bytes. -/
def tryFrom {D : Type} {n : Nat} (r : Rep (Bytes D n) V) (ds : Vector D n) : Option V :=
  r.decode (Bytes.ofData ds)

/-- The validity set restricted to fully initialized bytes, as a predicate on byte data
(the notion of "bit validity" used when bytes are never uninitialized). Defined from the exact
decoder, not from a conservative runtime check. -/
def InitValid {D : Type} {n : Nat} (r : Rep (Bytes D n) V) (ds : Vector D n) : Prop :=
  ∃ v, r.tryFrom ds = some v

/-- The bytes of a value, available for `IntoBytes` representations (an `as_bytes`-style view). -/
def asBytes {D : Type} {n : Nat} (r : Rep (Bytes D n) V) (h : r.IntoBytes) (v : V) : Vector D n :=
  Vector.ofFn fun i => (r.encode v)[i.val].get (h v i.val i.isLt)

end Rep

/-! ## Transmutes -/

/-- By-value transmute from `A` to `B` through a common carrier (same byte size):
encode with `ra`, decode with `rb`. -/
def transmute {α A B : Type} (ra : Rep α A) (rb : Rep α B) (a : A) : Option B :=
  rb.decode (ra.encode a)

/-- The transmute from `A` to `B` never fails. -/
def TransmuteTotal {α A B : Type} (ra : Rep α A) (rb : Rep α B) : Prop :=
  ∀ a : A, ∃ b : B, transmute ra rb a = some b

/-! ## Basic facts about the trait predicates (proved) -/

theorem Rep.fromBytes_iff_tryFrom_total {D V : Type} {n : Nat} (r : Rep (Bytes D n) V) :
    r.FromBytes ↔ ∀ ds : Vector D n, ∃ v, r.tryFrom ds = some v := by
  constructor
  · intro h ds
    exact h _ (Bytes.isInit_ofData ds)
  · intro h x hx
    obtain ⟨ds, rfl⟩ := Bytes.exists_ofData_of_isInit hx
    exact h ds

theorem Rep.ofData_asBytes {D V : Type} {n : Nat} (r : Rep (Bytes D n) V) (h : r.IntoBytes)
    (v : V) : Bytes.ofData (r.asBytes h v) = r.encode v := by
  apply Vector.ext
  intro i hi
  simp only [Bytes.getElem_ofData, Rep.asBytes, Vector.getElem_ofFn]
  exact AByte.init_get _ _

/-- `DecodeEncode` alone makes the encoder injective (no order is involved). -/
theorem Rep.encode_injective_of_decodeEncode {α V : Type} (r : Rep α V) (hDE : r.DecodeEncode) :
    Function.Injective r.encode := by
  intro v w h
  have h' : r.decode (r.encode v) = r.decode (r.encode w) := congrArg r.decode h
  rw [hDE v, hDE w] at h'
  injection h'

/-- The encoder extended to `Option V`: `none` is sent to the all-`uninit` vector. -/
def Rep.liftEncode {D V : Type} {n : Nat} (r : Rep (Bytes D n) V) : Option V → Bytes D n
  | none => Bytes.uninit n
  | some v => r.encode v

/-- `LowerAdjoint` is exactly the statement that `liftEncode` and `decode` form a Galois
connection between `Option V` (flat order) and `Bytes D n` (pointwise order). -/
theorem Rep.lowerAdjoint_iff_galois_liftEncode {D V : Type} {n : Nat} (r : Rep (Bytes D n) V) :
    r.LowerAdjoint ↔ ∀ (o : Option V) (x : Bytes D n), r.liftEncode o ⊑ x ↔ o ⊑ r.decode x := by
  constructor
  · intro h o x
    cases o with
    | none => exact ⟨fun _ => OptLe.none_le _, fun _ => Bytes.uninit_le x⟩
    | some v => exact (h v x).trans OptLe.some_le_iff.symm
  · intro h v x
    exact (h (some v) x).trans OptLe.some_le_iff

end Toy.Repr
