/-!
# Core Resource Algebra Definitions

This module defines discrete, unbundled raw resource algebras (`RawRA α`),
separate named algebraic laws (`OpAssoc`, `OpComm`, `ValidOpL`, `IsRightUnit`,
`HasLocalRightUnits`, `HasRightIdOnValid`, `IsExclusive`, `IsCoreFreeRA`),
right-frame-preserving updates (`fpUpdate`, `fpUpdateP`, `fpUpdateBare`), local
updates (`LocalUpdate`), and the product combinator (`prodRA`).

Keeping each algebraic law as a separate `Prop` lets every theorem state a
tight (irredundant) set of hypotheses sufficient for its conclusion. `RawRA` and `IsCoreFreeRA` capture
discrete core-free composition and validity laws, omitting Iris's partial core
(`pcore`), step-indexed OFE distance metrics, and PCM unit or cancellativity
axioms.
-/

namespace Toy.RA

/-- A discrete raw magma equipped with a validity predicate (`op : α → α → α`,
`valid : α → Prop`), serving as unbundled carrier-operation-validity data prior
to imposing associativity, commutativity, or validity-closure laws. Omits Iris's
partial core (`pcore`), step-indexed OFE structure, and any PCM unit or
cancellativity axiom. -/
structure RawRA (α : Type) where
  op : α → α → α
  valid : α → Prop

/-- Compose an element `a` with an optional frame `mf`: `none` leaves `a`
unchanged (empty frame), while `some f` composes `a` with `f` on the right.
Captures Iris's `opM` (`⋅?`), allowing frame-preserving updates and local
updates to work uniformly on non-unital resource algebras. -/
def opOpt {α : Type} (R : RawRA α) (a : α) : Option α → α
  | none => a
  | some f => R.op a f

/-- Strict algebraic resource inclusion (`a ≼ b`): `b` can be obtained by
composing `a` with some carrier element `c` on the right. Captures Iris's
`included` (`≼`) on discrete algebras. In a non-unital RA this relation need not
be reflexive. -/
def included {α : Type} (R : RawRA α) (a b : α) : Prop :=
  ∃ c : α, R.op a c = b

/-- Reflexive resource inclusion (`a ≼? b`): `b` equals `a` or is obtained by
composing `a` with some carrier element on the right. Captures Iris's inclusion
under the unit-adjoining `option` functor (`Some a ≼ Some b`). -/
def includedRefl {α : Type} (R : RawRA α) (a b : α) : Prop :=
  ∃ mc : Option α, opOpt R a mc = b

/-- Associativity of resource composition. Captures the discrete CMRA
associativity axiom (`cmra_assoc`). -/
def OpAssoc {α : Type} (R : RawRA α) : Prop :=
  ∀ x y z : α, R.op (R.op x y) z = R.op x (R.op y z)

/-- Commutativity of resource composition. Captures the discrete CMRA
commutativity axiom (`cmra_comm`). -/
def OpComm {α : Type} (R : RawRA α) : Prop :=
  ∀ x y : α, R.op x y = R.op y x

/-- Leftward downward closure of validity under composition: if `x · y` is
valid, then `x` is valid. Captures Iris's `cmra_valid_op_l`. -/
def ValidOpL {α : Type} (R : RawRA α) : Prop :=
  ∀ x y : α, R.valid (R.op x y) → R.valid x

/-- Validity is downward closed under strict inclusion `included`. -/
def ValidClosedUnderIncluded {α : Type} (R : RawRA α) : Prop :=
  ∀ x y : α, included R x y → R.valid y → R.valid x

/-- Validity is downward closed under reflexive inclusion `includedRefl`. -/
def ValidClosedUnderIncludedRefl {α : Type} (R : RawRA α) : Prop :=
  ∀ x y : α, includedRefl R x y → R.valid y → R.valid x

/-- `e` is a right identity for `R.op`. Captures the right-unit law of a unital
resource algebra (UCMRA). -/
def IsRightUnit {α : Type} (R : RawRA α) (e : α) : Prop :=
  ∀ x : α, R.op x e = x

/-- Every valid element admits some right identity in `R` (`x · c = x`).
Weakest per-element right-identity condition sufficient (together with
`ValidOpL`) for `fpUpdate` to coincide with `fpUpdateBare`. Unlike Iris's
`CmraTotal`, this requires neither right identities on invalid elements nor an
idempotent, monotone core function. -/
def HasRightIdOnValid {α : Type} (R : RawRA α) : Prop :=
  ∀ x : α, R.valid x → ∃ c : α, R.op x c = x

/-- Every carrier element admits some right identity in `R` (`∀ x, ∃ c, x · c = x`).
Corresponds to the multi-unit separation-algebra axiom of Dockins, Hobor, and
Appel (APLAS 2009, §2, axiom (15)), up to side and without cancellativity.
Unlike Iris's `CmraTotal`, no canonical idempotent or monotone core map is
assumed. -/
def HasLocalRightUnits {α : Type} (R : RawRA α) : Prop :=
  ∀ x : α, ∃ c : α, R.op x c = x

/-- An element `a` is right-exclusive if no element `f` composes validly with
it on the right (`¬ R.valid (R.op a f)`). This matches Iris's discrete
`Exclusive`, which is likewise stated for right composition. Under `OpComm`, it
coincides with left exclusivity (`∀ f, ¬ R.valid (R.op f a)`); it does not
address simultaneous two-sided contexts `R.op l (R.op a r)`. Without `OpComm`,
left compositions `R.op f a` may still be valid. -/
def IsExclusive {α : Type} (R : RawRA α) (a : α) : Prop :=
  ∀ f : α, ¬ R.valid (R.op a f)

/-- Convenience conjunction asserting the three core-free discrete RA laws
(`OpAssoc`, `OpComm`, `ValidOpL`), omitting Iris's partial core (`pcore`) and
core laws as well as PCM unit and cancellativity axioms. Used to certify
concrete algebras; general update theorems take only the individual laws they
use. -/
def IsCoreFreeRA {α : Type} (R : RawRA α) : Prop :=
  OpAssoc R ∧ OpComm R ∧ ValidOpL R

/-- Deterministic right-frame-preserving update (`a ⤳ b`): every optional frame
`mf` composed on the right (`opOpt R a mf`) that is compatible with `a` remains
compatible with `b`. Captures Iris's discrete `cmra_update` (`~~>`) under
`OpAssoc` and `OpComm`; under `OpComm` alone, right-frame preservation also
preserves each single left-composed frame (`fpUpdate_preserve_left_of_opComm`),
whereas simultaneous two-sided frames `l · (a · r)` additionally require
`OpAssoc`. Without `OpComm`, left-composed frames `R.op f a` need not be
preserved. Including `mf = none` ensures a valid element cannot update to an
invalid element even when `R` has no unit. -/
def fpUpdate {α : Type} (R : RawRA α) (a b : α) : Prop :=
  ∀ mf : Option α, R.valid (opOpt R a mf) → R.valid (opOpt R b mf)

/-- Non-deterministic (set-valued) right-frame-preserving update (`a ⤳: P`): for
every optional frame `mf` composed on the right that is compatible with `a`,
there exists a target `b` satisfying `P` that remains compatible with `mf`.
Captures Iris's discrete `cmra_updateP` (`~~>:`) under `OpComm`. -/
def fpUpdateP {α : Type} (R : RawRA α) (a : α) (P : α → Prop) : Prop :=
  ∀ mf : Option α, R.valid (opOpt R a mf) → ∃ b : α, P b ∧ R.valid (opOpt R b mf)

/-- Bare (non-empty right-frame-only) frame-preserving update: quantifies only
over carrier elements `f : α`, omitting the empty frame `none`. With a right
unit, or with right identities on valid elements together with `ValidOpL`, this
agrees with `fpUpdate` (`fpUpdate_iff_bare_of_rightUnit`,
`fpUpdate_iff_bare_of_rightIdOnValid_validOpL`); local right units alone do not
suffice without `ValidOpL`, and in non-unital algebras without right identities
such as `exclRA` it permits updating valid elements to invalid ones. -/
def fpUpdateBare {α : Type} (R : RawRA α) (a b : α) : Prop :=
  ∀ f : α, R.valid (R.op a f) → R.valid (R.op b f)

/-- Discrete local update `(a, b) ~l~> (a', b')`: whenever `a` is valid and
decomposes as `b` composed on the right with an optional remainder `mz`, `a'` is
valid and decomposes as `b'` composed with the same remainder `mz`. Captures
Iris's discrete `local_update`. -/
def LocalUpdate {α : Type} (R : RawRA α) (a b a' b' : α) : Prop :=
  ∀ mz : Option α,
    R.valid a → opOpt R b mz = a → R.valid a' ∧ opOpt R b' mz = a'

/-- Cartesian product of two raw resource algebras, with componentwise
composition and validity. Captures Iris's `prodR`. -/
def prodRA {α β : Type} (R₁ : RawRA α) (R₂ : RawRA β) : RawRA (α × β) where
  op p q := (R₁.op p.1 q.1, R₂.op p.2 q.2)
  valid p := R₁.valid p.1 ∧ R₂.valid p.2

/-! ## Basic Equational and Law-Free Lemmas -/

theorem opOpt_none {α : Type} (R : RawRA α) (a : α) : opOpt R a none = a := rfl

theorem opOpt_some {α : Type} (R : RawRA α) (a f : α) : opOpt R a (some f) = R.op a f := rfl

theorem hasRightIdOnValid_of_hasLocalRightUnits {α : Type} {R : RawRA α}
    (h : HasLocalRightUnits R) : HasRightIdOnValid R :=
  fun x _ => h x

/-- Under `OpComm`, a right-frame-preserving update also preserves each single
left-composed frame (`f · a ↦ f · b`). Simultaneous two-sided contexts
`l · (a · r)` are preserved under `OpComm` and `OpAssoc` (`fpUpdate2_of_assoc_comm`),
not under `OpComm` alone (`opComm_alone_not_two_sided`). -/
theorem fpUpdate_preserve_left_of_opComm {α : Type} (R : RawRA α) (hComm : OpComm R)
    {a b : α} (h : fpUpdate R a b) (f : α) (hf : R.valid (R.op f a)) :
    R.valid (R.op f b) := by
  rw [hComm f a] at hf
  rw [hComm f b]
  exact h (some f) hf

theorem validOpL_iff_validClosedUnderIncluded {α : Type} (R : RawRA α) :
    ValidOpL R ↔ ValidClosedUnderIncluded R := by
  constructor
  · intro h x y ⟨c, hc⟩ hy
    rw [← hc] at hy
    exact h x c hy
  · intro h x y hxy
    exact h x (R.op x y) ⟨y, rfl⟩ hxy

theorem validOpL_iff_validClosedUnderIncludedRefl {α : Type} (R : RawRA α) :
    ValidOpL R ↔ ValidClosedUnderIncludedRefl R := by
  constructor
  · intro h x y ⟨mc, hmc⟩ hy
    cases mc with
    | none =>
      rw [opOpt_none] at hmc
      exact hmc ▸ hy
    | some c =>
      rw [opOpt_some] at hmc
      rw [← hmc] at hy
      exact h x c hy
  · intro h x y hxy
    exact h x (R.op x y) ⟨some y, rfl⟩ hxy

theorem includedRefl_refl {α : Type} (R : RawRA α) (a : α) : includedRefl R a a :=
  ⟨none, rfl⟩

theorem includedRefl_iff_included_of_rightUnit {α : Type} (R : RawRA α) (e : α)
    (he : IsRightUnit R e) (a b : α) :
    includedRefl R a b ↔ included R a b := by
  constructor
  · intro ⟨mc, hmc⟩
    cases mc with
    | none => exact ⟨e, by rw [he, ← hmc]; rfl⟩
    | some c => exact ⟨c, hmc⟩
  · intro ⟨c, hc⟩
    exact ⟨some c, hc⟩

theorem fpUpdate_refl {α : Type} (R : RawRA α) (a : α) : fpUpdate R a a :=
  fun _ h => h

theorem fpUpdate_trans {α : Type} (R : RawRA α) {a b c : α}
    (hab : fpUpdate R a b) (hbc : fpUpdate R b c) : fpUpdate R a c :=
  fun mf h => hbc mf (hab mf h)

theorem fpUpdate_iff_fpUpdateP {α : Type} (R : RawRA α) (a b : α) :
    fpUpdate R a b ↔ fpUpdateP R a (· = b) := by
  constructor
  · intro h mf ha
    exact ⟨b, rfl, h mf ha⟩
  · intro h mf ha
    rcases h mf ha with ⟨b', rfl, hb'⟩
    exact hb'

theorem fpUpdateP_id {α : Type} (R : RawRA α) {a : α} {P : α → Prop} (ha : P a) :
    fpUpdateP R a P :=
  fun _ hv => ⟨a, ha, hv⟩

theorem fpUpdateP_compose {α : Type} (R : RawRA α) {a : α} {P Q : α → Prop}
    (hP : fpUpdateP R a P) (hPQ : ∀ b, P b → fpUpdateP R b Q) :
    fpUpdateP R a Q := by
  intro mf ha
  rcases hP mf ha with ⟨b, hPb, hvb⟩
  exact hPQ b hPb mf hvb

theorem fpUpdateP_weaken {α : Type} (R : RawRA α) {a : α} {P Q : α → Prop}
    (hP : fpUpdateP R a P) (hPQ : ∀ b, P b → Q b) :
    fpUpdateP R a Q := by
  intro mf ha
  rcases hP mf ha with ⟨b, hPb, hvb⟩
  exact ⟨b, hPQ b hPb, hvb⟩

theorem fpUpdate_imp_fpUpdateBare {α : Type} (R : RawRA α) {a b : α}
    (h : fpUpdate R a b) : fpUpdateBare R a b :=
  fun f hf => h (some f) hf

/-- Any right-exclusive element `a` admits a right-frame-preserving update to
any valid element `b`, using no algebraic laws on `R`. Captures Iris's
`cmra_update_exclusive` under `OpComm`; without `OpComm`, left frames `f · a`
need not be preserved. -/
theorem exclusive_fpUpdate {α : Type} (R : RawRA α) (a b : α)
    (hExcl : IsExclusive R a) (hb : R.valid b) :
    fpUpdate R a b := by
  intro mf hmf
  cases mf with
  | none => exact hb
  | some f => exact False.elim (hExcl f hmf)

theorem localUpdate_refl {α : Type} (R : RawRA α) (a b : α) :
    LocalUpdate R a b a b :=
  fun _ ha h => ⟨ha, h⟩

theorem localUpdate_trans {α : Type} (R : RawRA α) {a₁ b₁ a₂ b₂ a₃ b₃ : α}
    (h₁₂ : LocalUpdate R a₁ b₁ a₂ b₂) (h₂₃ : LocalUpdate R a₂ b₂ a₃ b₃) :
    LocalUpdate R a₁ b₁ a₃ b₃ := by
  intro mz ha₁ heq₁
  rcases h₁₂ mz ha₁ heq₁ with ⟨ha₂, heq₂⟩
  exact h₂₃ mz ha₂ heq₂

/-- Over a raw RA with a right unit `e`, `LocalUpdate` reduces to quantifying
over non-optional remainders `c : α`. Captures Iris's
`local_update_unital_discrete`. -/
theorem localUpdate_unital_iff {α : Type} (R : RawRA α) (e : α) (he : IsRightUnit R e)
    (a b a' b' : α) :
    LocalUpdate R a b a' b' ↔
      ∀ c : α, R.valid a → R.op b c = a → R.valid a' ∧ R.op b' c = a' := by
  constructor
  · intro h c ha heq
    exact h (some c) ha heq
  · intro h mz ha heq
    cases mz with
    | none =>
      rw [opOpt_none] at heq ⊢
      have h' := h e ha (by rw [he, heq])
      rw [he] at h'
      exact h'
    | some c =>
      exact h c ha heq

/-! ## Product RA Law Preservation -/

theorem prodRA_opAssoc {α β : Type} (R₁ : RawRA α) (R₂ : RawRA β)
    (h₁ : OpAssoc R₁) (h₂ : OpAssoc R₂) :
    OpAssoc (prodRA R₁ R₂) := by
  intro x y z
  exact Prod.ext (h₁ x.1 y.1 z.1) (h₂ x.2 y.2 z.2)

theorem prodRA_opComm {α β : Type} (R₁ : RawRA α) (R₂ : RawRA β)
    (h₁ : OpComm R₁) (h₂ : OpComm R₂) :
    OpComm (prodRA R₁ R₂) := by
  intro x y
  exact Prod.ext (h₁ x.1 y.1) (h₂ x.2 y.2)

theorem prodRA_validOpL {α β : Type} (R₁ : RawRA α) (R₂ : RawRA β)
    (h₁ : ValidOpL R₁) (h₂ : ValidOpL R₂) :
    ValidOpL (prodRA R₁ R₂) := by
  intro x y hxy
  exact ⟨h₁ x.1 y.1 hxy.1, h₂ x.2 y.2 hxy.2⟩

theorem prodRA_isCoreFreeRA {α β : Type} (R₁ : RawRA α) (R₂ : RawRA β)
    (h₁ : IsCoreFreeRA R₁) (h₂ : IsCoreFreeRA R₂) :
    IsCoreFreeRA (prodRA R₁ R₂) :=
  ⟨prodRA_opAssoc R₁ R₂ h₁.1 h₂.1,
   prodRA_opComm R₁ R₂ h₁.2.1 h₂.2.1,
   prodRA_validOpL R₁ R₂ h₁.2.2 h₂.2.2⟩

/-! ## Positive and Negative Examples for Core Definitions -/

/-- Additive natural numbers with universal validity. -/
def natAddRA : RawRA Nat where
  op := Nat.add
  valid _ := True

/-- Additive natural numbers capped at `2` (`valid n := n ≤ 2`), providing
non-degenerate positive and negative examples where validity is selective. -/
def cappedNatRA : RawRA Nat where
  op := Nat.add
  valid n := n ≤ 2

/-- Truncated subtraction on `Nat`: negative example for `OpAssoc`. -/
def natSubRA : RawRA Nat where
  op := Nat.sub
  valid _ := True

/-- Left projection on `Bool`: negative example for `OpComm`. -/
def boolLeftProjRA : RawRA Bool where
  op x _ := x
  valid _ := True

/-- `Bool` under `xor` where only `false` is valid: satisfies `OpAssoc` and
`OpComm`, but fails `ValidOpL` since `true ^^ true = false` is valid while
`true` is invalid. -/
def xorValidFalseRA : RawRA Bool where
  op := xor
  valid b := b = false

/-- Shifted addition `(x, y) ↦ x + y + 1` on `Nat`: negative example for
`HasLocalRightUnits`. -/
def natSuccAddRA : RawRA Nat where
  op x y := x + y + 1
  valid _ := True

/-- Two-element exclusive algebra (`some ()` valid, `none` invalid, all
compositions `none`): positive example for `IsExclusive` and negative example for
`HasRightIdOnValid`. -/
def exclUnitRA : RawRA (Option Unit) where
  op _ _ := none
  valid o := o.isSome = true

theorem opAssoc_cappedNatRA : OpAssoc cappedNatRA := Nat.add_assoc

theorem opComm_cappedNatRA : OpComm cappedNatRA := Nat.add_comm

-- `OpAssoc` positive & negative examples
theorem opAssoc_pos_example : OpAssoc natAddRA := Nat.add_assoc

theorem opAssoc_neg_example : ¬ OpAssoc natSubRA := by
  intro h
  have h0 := h 2 1 1
  simp [natSubRA] at h0

-- `OpComm` positive & negative examples
theorem opComm_pos_example : OpComm natAddRA := Nat.add_comm

theorem opComm_neg_example : ¬ OpComm boolLeftProjRA := by
  intro h
  have h0 := h false true
  simp [boolLeftProjRA] at h0

-- `ValidOpL` positive & negative examples
theorem validOpL_pos_example : ValidOpL cappedNatRA := by
  intro x y (hxy : x + y ≤ 2)
  show x ≤ 2
  omega

theorem validOpL_neg_example : ¬ ValidOpL xorValidFalseRA := by
  intro h
  have h0 := h true true rfl
  simp [xorValidFalseRA] at h0

-- `ValidClosedUnderIncluded` & `ValidClosedUnderIncludedRefl` positive & negative examples
theorem validClosedUnderIncluded_pos_example : ValidClosedUnderIncluded cappedNatRA :=
  (validOpL_iff_validClosedUnderIncluded cappedNatRA).mp validOpL_pos_example

theorem validClosedUnderIncluded_neg_example : ¬ ValidClosedUnderIncluded xorValidFalseRA :=
  fun h => validOpL_neg_example ((validOpL_iff_validClosedUnderIncluded xorValidFalseRA).mpr h)

theorem validClosedUnderIncludedRefl_pos_example : ValidClosedUnderIncludedRefl cappedNatRA :=
  (validOpL_iff_validClosedUnderIncludedRefl cappedNatRA).mp validOpL_pos_example

theorem validClosedUnderIncludedRefl_neg_example : ¬ ValidClosedUnderIncludedRefl xorValidFalseRA :=
  fun h => validOpL_neg_example ((validOpL_iff_validClosedUnderIncludedRefl xorValidFalseRA).mpr h)

-- `IsCoreFreeRA` positive & negative examples
theorem isCoreFreeRA_pos_example : IsCoreFreeRA cappedNatRA :=
  ⟨opAssoc_cappedNatRA, opComm_cappedNatRA, validOpL_pos_example⟩

theorem isCoreFreeRA_neg_example : ¬ IsCoreFreeRA xorValidFalseRA :=
  fun h => validOpL_neg_example h.2.2

-- `included` and `includedRefl` positive & negative examples
theorem included_pos_example : included natAddRA 2 5 := ⟨3, rfl⟩

theorem included_neg_example : ¬ included natAddRA 5 2 := by
  intro ⟨c, hc⟩
  dsimp [natAddRA] at hc
  omega

theorem includedRefl_pos_example : includedRefl exclUnitRA (some ()) (some ()) :=
  ⟨none, rfl⟩

theorem includedRefl_neg_example : ¬ includedRefl natAddRA 5 2 := by
  intro ⟨mc, hmc⟩
  cases mc with
  | none => simp [opOpt] at hmc
  | some c =>
    dsimp [opOpt, natAddRA] at hmc
    omega

-- `IsRightUnit` positive & negative examples
theorem isRightUnit_pos_example : IsRightUnit natAddRA 0 := Nat.add_zero

theorem isRightUnit_neg_example : ¬ IsRightUnit natAddRA 1 := by
  intro h
  have h0 := h 0
  simp [natAddRA] at h0

-- `HasLocalRightUnits` & `HasRightIdOnValid` positive & negative examples
theorem hasLocalRightUnits_pos_example : HasLocalRightUnits cappedNatRA :=
  fun x => ⟨0, Nat.add_zero x⟩

theorem hasLocalRightUnits_neg_example : ¬ HasLocalRightUnits natSuccAddRA := by
  intro h
  rcases h 0 with ⟨c, hc⟩
  dsimp [natSuccAddRA] at hc
  omega

theorem hasRightIdOnValid_pos_example : HasRightIdOnValid cappedNatRA :=
  hasRightIdOnValid_of_hasLocalRightUnits hasLocalRightUnits_pos_example

theorem hasRightIdOnValid_neg_example : ¬ HasRightIdOnValid exclUnitRA := by
  intro h
  rcases h (some ()) rfl with ⟨c, hc⟩
  cases hc

-- `IsExclusive` positive & negative examples
theorem isExclusive_pos_example : IsExclusive exclUnitRA (some ()) := by
  intro f hf
  simp [exclUnitRA] at hf

theorem isExclusive_neg_example : ¬ IsExclusive natAddRA 0 := by
  intro h
  exact h 0 trivial

-- `fpUpdate` positive & negative examples (both in `cappedNatRA`, where `2 ⤳ 1` holds and `1 ⤳ 2` fails)
theorem fpUpdate_pos_example : fpUpdate cappedNatRA 2 1 := by
  intro mf hmf
  cases mf with
  | none =>
    show 1 ≤ 2
    omega
  | some f =>
    have h : 2 + f ≤ 2 := hmf
    show 1 + f ≤ 2
    omega

theorem fpUpdate_neg_example : ¬ fpUpdate cappedNatRA 1 2 := by
  intro h
  have h1 : cappedNatRA.valid (opOpt cappedNatRA 1 (some 1)) := by
    simp [cappedNatRA, opOpt]
  have h2 := h (some 1) h1
  simp [cappedNatRA, opOpt] at h2

-- `fpUpdateP` positive & negative examples (both in `cappedNatRA`)
theorem fpUpdateP_pos_example : fpUpdateP cappedNatRA 2 (fun b => b = 0 ∨ b = 1) :=
  fun mf hmf => ⟨1, Or.inr rfl, fpUpdate_pos_example mf hmf⟩

theorem fpUpdateP_neg_example : ¬ fpUpdateP cappedNatRA 1 (fun b => b = 2 ∨ b = 3) := by
  intro h
  have h1 : cappedNatRA.valid (opOpt cappedNatRA 1 (some 1)) := by
    simp [cappedNatRA, opOpt]
  rcases h (some 1) h1 with ⟨b, hb, hvb⟩
  rcases hb with rfl | rfl <;> simp [cappedNatRA, opOpt] at hvb

-- `fpUpdateBare` positive & negative examples (both in `cappedNatRA`)
theorem fpUpdateBare_pos_example : fpUpdateBare cappedNatRA 2 1 :=
  fpUpdate_imp_fpUpdateBare cappedNatRA fpUpdate_pos_example

theorem fpUpdateBare_neg_example : ¬ fpUpdateBare cappedNatRA 1 2 := by
  intro h
  have h1 : cappedNatRA.valid (cappedNatRA.op 1 1) := by simp [cappedNatRA]
  have h2 := h 1 h1
  simp [cappedNatRA] at h2

-- `LocalUpdate` positive & negative examples
theorem localUpdate_pos_example : LocalUpdate natAddRA 2 1 3 2 := by
  intro mz _ h
  cases mz with
  | none => simp [opOpt] at h
  | some c =>
    dsimp [opOpt, natAddRA] at h ⊢
    exact ⟨trivial, by omega⟩

theorem localUpdate_neg_example : ¬ LocalUpdate natAddRA 2 1 1 1 := by
  intro h
  have h' := h (some 1) trivial rfl
  simp [opOpt, natAddRA] at h'

-- `prodRA` positive & negative examples
theorem prodRA_pos_example :
    IsCoreFreeRA (prodRA cappedNatRA cappedNatRA) ∧
    (prodRA cappedNatRA cappedNatRA).valid (1, 2) :=
  ⟨prodRA_isCoreFreeRA cappedNatRA cappedNatRA isCoreFreeRA_pos_example isCoreFreeRA_pos_example,
   ⟨by show 1 ≤ 2; omega, by show 2 ≤ 2; omega⟩⟩

theorem prodRA_neg_example :
    ¬ (prodRA cappedNatRA natAddRA).valid (3, 0) ∧
    ¬ IsCoreFreeRA (prodRA xorValidFalseRA natAddRA) := by
  refine ⟨?_, ?_⟩
  · intro ⟨h1, _⟩
    simp [cappedNatRA] at h1
  · intro ⟨_, _, hvl⟩
    have h0 := hvl (true, 0) (true, 0) ⟨rfl, trivial⟩
    simp [prodRA, xorValidFalseRA] at h0

end Toy.RA
