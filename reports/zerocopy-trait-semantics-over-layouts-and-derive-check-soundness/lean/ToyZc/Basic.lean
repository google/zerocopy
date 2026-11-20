/-!
# Abstract bytes and representations

This module contains, in namespace `Toy.Zc`, a small byte-representation vocabulary: abstract
bytes, representations as encoder/decoder pairs, and the byte-level `IntoBytes`/`FromBytes`
predicates. It is a self-contained subset of a larger vocabulary of this kind; the definedness
order on abstract bytes and the representation laws (round-trip, monotonicity) are omitted because
no statement here uses them.

* `AByte D`: one abstract byte, either `uninit` or `init d`.
* `Bytes D n`: a fixed-length vector of abstract bytes.
* `Rep α V`: a representation `encode : V → α`, `decode : α → Option V`.
* `Rep.IntoBytes` (no encoding contains `uninit`), `Rep.FromBytes` (every fully initialized
  byte vector decodes), `Rep.tryFrom` (the partial cast from initialized byte data).
* `transmute ra rb := rb.decode ∘ ra.encode` and `TransmuteTotal`.
-/

namespace Toy.Zc

/-! ## Abstract bytes -/

/-- An abstract byte: `uninit` (no defined value, e.g. padding or never-written memory),
or `init d` carrying the payload `d : D` of an initialized byte. -/
inductive AByte (D : Type) where
  /-- An uninitialized byte. -/
  | uninit : AByte D
  /-- An initialized byte with payload `d`. -/
  | init (d : D) : AByte D
  deriving DecidableEq, Repr

namespace AByte

variable {D : Type}

/-- Whether an abstract byte is initialized. -/
def isInit : AByte D → Bool
  | uninit => false
  | init _ => true

/-- The payload of an initialized byte. -/
def get : (b : AByte D) → b.isInit = true → D
  | init d, _ => d

@[simp] theorem isInit_init (d : D) : (init d).isInit = true := rfl

@[simp] theorem isInit_uninit : (uninit : AByte D).isInit = false := rfl

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

namespace Bytes

variable {D : Type} {n : Nat}

/-- A byte vector is fully initialized (contains no `uninit` byte). -/
def IsInit (x : Bytes D n) : Prop := ∀ (i : Nat) (h : i < n), x[i].isInit = true

instance (x : Bytes D n) : Decidable x.IsInit :=
  inferInstanceAs (Decidable (∀ (i : Nat) (h : i < n), x[i].isInit = true))

/-- The byte vector whose bytes are all initialized with the given data. -/
def ofData (ds : Vector D n) : Bytes D n := ds.map .init

@[simp] theorem getElem_ofData (ds : Vector D n) (i : Nat) (h : i < n) :
    (ofData ds)[i] = .init ds[i] := by
  simp [ofData]

theorem isInit_ofData (ds : Vector D n) : (ofData ds).IsInit := by
  intro i h
  simp

/-- The data of a fully initialized byte vector (`none` if some byte is `uninit`). -/
def toData? (x : Bytes D n) : Option (Vector D n) :=
  if h : x.IsInit then some (Vector.ofFn fun i => x[i.val].get (h i.val i.isLt)) else none

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

/-- Every fully initialized byte vector is `ofData` of some data. -/
theorem exists_ofData_of_isInit {x : Bytes D n} (h : x.IsInit) : ∃ ds, x = ofData ds := by
  refine ⟨Vector.ofFn fun i => x[i.val].get (h i.val i.isLt), ?_⟩
  apply ofData_of_toData?
  unfold toData?
  rw [dite_eq_left_of_eq_true (eq_true h)]

end Bytes

/-! ## Representations -/

/-- A *representation* of values of type `V` in a carrier `α` (usually `Bytes D n`, i.e. the
`n` bytes a value of type `V` occupies): an encoder `encode : V → α` and a partial decoder
`decode : α → Option V` (`none` = the bytes are not a valid `V`). -/
structure Rep (α V : Type) where
  /-- Bytes produced when storing a value. -/
  encode : V → α
  /-- Value read back from bytes, if the bytes are valid. -/
  decode : α → Option V

namespace Rep

/-- **`IntoBytes`** (semantic): no encoding contains an `uninit` byte, so every value can be
viewed as plain initialized bytes. -/
def IntoBytes {D V : Type} {n : Nat} (r : Rep (Bytes D n) V) : Prop :=
  ∀ v : V, (r.encode v).IsInit

/-- **`FromBytes`** (semantic): every fully initialized byte vector decodes to some value. -/
def FromBytes {D V : Type} {n : Nat} (r : Rep (Bytes D n) V) : Prop :=
  ∀ x : Bytes D n, x.IsInit → ∃ v, r.decode x = some v

/-- The partial cast from fully initialized byte data (`TryFromBytes`-style): decode the
bytes `init ds[0], …, init ds[n-1]`. -/
def tryFrom {D V : Type} {n : Nat} (r : Rep (Bytes D n) V) (ds : Vector D n) : Option V :=
  r.decode (Bytes.ofData ds)

end Rep

/-! ## Transmutes -/

/-- By-value transmute from `A` to `B` through a common carrier (same byte size):
encode with `ra`, decode with `rb`. -/
def transmute {α A B : Type} (ra : Rep α A) (rb : Rep α B) (a : A) : Option B :=
  rb.decode (ra.encode a)

/-- The transmute from `A` to `B` never fails. -/
def TransmuteTotal {α A B : Type} (ra : Rep α A) (rb : Rep α B) : Prop :=
  ∀ a : A, ∃ b : B, transmute ra rb a = some b

/-- `FromBytes` is totality of `tryFrom`. -/
theorem Rep.fromBytes_iff_tryFrom_total {D V : Type} {n : Nat} (r : Rep (Bytes D n) V) :
    r.FromBytes ↔ ∀ ds : Vector D n, ∃ v, r.tryFrom ds = some v := by
  constructor
  · intro h ds
    exact h _ (Bytes.isInit_ofData ds)
  · intro h x hx
    obtain ⟨ds, rfl⟩ := Bytes.exists_ofData_of_isInit hx
    exact h ds

/-- The byte payload used throughout: an initialized byte carries a `UInt8`. -/
abbrev Byte := UInt8

end Toy.Zc
