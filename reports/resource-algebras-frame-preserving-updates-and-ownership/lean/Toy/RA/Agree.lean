import Toy.RA.Core
import Toy.RA.Excl

/-!
# Agreement Resource Algebra (`Agree`)

Models duplicable, immutable consensus on a value `x : α` (the discrete limit
of Iris's `agreeR`). Elements are non-empty predicates (subsets) of `α`,
composed by union; an element is valid iff all its members are equal (i.e. it
is a singleton `Agree.ag x`). Because `ag x` is idempotent, any other party
may hold a duplicate copy `ag x` as a frame, preventing any frame-preserving
change to a distinct value `y ≠ x`.
-/

namespace Toy.RA

/-- Elements of the discrete agreement resource algebra over `α`: non-empty
predicates (subsets) of `α`, without requiring decidable equality on `α`.
Captures the discrete non-empty-set semantics of Iris's `agree A`. -/
structure Agree (α : Type) where
  mem : α → Prop
  nonempty : ∃ x : α, mem x

@[ext]
theorem Agree.ext {α : Type} {a b : Agree α} (h : ∀ x, a.mem x ↔ b.mem x) : a = b := by
  cases a
  cases b
  congr
  funext x
  exact propext (h x)

/-- Singleton agreement element holding value `x`. Captures Iris's
`to_agree x`. -/
def Agree.ag {α : Type} (x : α) : Agree α where
  mem y := y = x
  nonempty := ⟨x, rfl⟩

/-- The discrete agreement resource algebra over `α`: composition takes the
union of underlying subsets; validity requires all members to agree. -/
def agreeRA (α : Type) : RawRA (Agree α) where
  op a b := ⟨fun x => a.mem x ∨ b.mem x, let ⟨x, hx⟩ := a.nonempty; ⟨x, Or.inl hx⟩⟩
  valid a := ∀ x y : α, a.mem x → a.mem y → x = y

theorem agreeRA_opAssoc (α : Type) : OpAssoc (agreeRA α) := by
  intro a b c
  ext x
  exact or_assoc

theorem agreeRA_opComm (α : Type) : OpComm (agreeRA α) := by
  intro a b
  ext x
  exact or_comm

theorem agreeRA_validOpL (α : Type) : ValidOpL (agreeRA α) := by
  intro a b hab x y hx hy
  exact hab x y (Or.inl hx) (Or.inl hy)

theorem agreeRA_isCoreFreeRA (α : Type) : IsCoreFreeRA (agreeRA α) :=
  ⟨agreeRA_opAssoc α, agreeRA_opComm α, agreeRA_validOpL α⟩

theorem agree_hasLocalRightUnits (α : Type) : HasLocalRightUnits (agreeRA α) := by
  intro a
  refine ⟨a, ?_⟩
  ext x
  exact ⟨fun h => h.elim id id, Or.inl⟩

theorem agree_hasRightIdOnValid (α : Type) : HasRightIdOnValid (agreeRA α) :=
  hasRightIdOnValid_of_hasLocalRightUnits (agree_hasLocalRightUnits α)

/-- `agreeRA Bool` has no global right unit (confirming it is a genuine
non-unital algebra with local right units). -/
theorem agreeRA_bool_no_rightUnit : ¬ ∃ e : Agree Bool, IsRightUnit (agreeRA Bool) e := by
  rintro ⟨e, he⟩
  obtain ⟨z, hz⟩ := e.nonempty
  have h1 : ((agreeRA Bool).op (.ag false) e).mem z := Or.inr hz
  have h2 : ((agreeRA Bool).op (.ag true) e).mem z := Or.inr hz
  rw [he] at h1 h2
  have a1 : z = false := h1
  have a2 : z = true := h2
  exact Bool.false_ne_true (a1.symm.trans a2)

theorem agree_ag_valid {α : Type} (x : α) : (agreeRA α).valid (.ag x) := by
  intro a b ha hb
  exact ha.trans hb.symm

theorem agree_ag_idemp {α : Type} (x : α) :
    (agreeRA α).op (.ag x) (.ag x) = .ag x := by
  ext y
  exact ⟨fun h => h.elim id id, Or.inl⟩

/-- Two singleton agreement elements compose validly if and only if they carry
the same value. Captures Iris's `to_agree_op_valid_L`. -/
theorem agree_ag_op_valid_iff {α : Type} (x y : α) :
    (agreeRA α).valid ((agreeRA α).op (.ag x) (.ag y)) ↔ x = y := by
  constructor
  · intro hv
    exact hv x y (Or.inl rfl) (Or.inr rfl)
  · rintro rfl a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rfl

/-- Every valid element of `agreeRA α` is equal to a singleton `Agree.ag x`.
Captures Iris's `to_agree_uninj`. -/
theorem agree_valid_eq_ag {α : Type} {s : Agree α} (hs : (agreeRA α).valid s) :
    ∃ x : α, s = .ag x := by
  rcases s.nonempty with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  ext y
  constructor
  · intro hy
    exact hs y x hy hx
  · rintro rfl
    exact hx

/-! ## Positive and Negative Examples for `agreeRA` -/

theorem agreeRA_valid_pos_example :
    (agreeRA Bool).valid ((agreeRA Bool).op (.ag false) (.ag false)) :=
  (agree_ag_op_valid_iff false false).mpr rfl

theorem agreeRA_valid_neg_example :
    ¬ (agreeRA Bool).valid ((agreeRA Bool).op (.ag false) (.ag true)) := by
  intro h
  have heq := (agree_ag_op_valid_iff false true).mp h
  cases heq

/-! ## Main Results for Agreement -/

/-- Exact characterization of frame-preserving updates out of an agreement
singleton `Agree.ag x` over all carrier targets `s : Agree α`:
`ag x ⤳ s` holds if and only if `s = ag x`. -/
theorem agree_fpUpdate_iff {α : Type} (x : α) (s : Agree α) :
    fpUpdate (agreeRA α) (.ag x) s ↔ s = .ag x := by
  constructor
  · intro hupd
    have hv : (agreeRA α).valid (opOpt (agreeRA α) (.ag x) (some (.ag x))) :=
      (agree_ag_op_valid_iff x x).mpr rfl
    have hvsf := hupd (some (.ag x)) hv
    have hvs : (agreeRA α).valid s := agreeRA_validOpL α s (.ag x) hvsf
    rcases agree_valid_eq_ag hvs with ⟨y, rfl⟩
    rw [(agree_ag_op_valid_iff y x).mp hvsf]
  · rintro rfl
    exact fpUpdate_refl (agreeRA α) (.ag x)

/-- Singleton specialization: `ag x ⤳ ag y ↔ x = y`. -/
theorem agree_ag_fpUpdate_iff {α : Type} (x y : α) :
    fpUpdate (agreeRA α) (.ag x) (.ag y) ↔ x = y := by
  rw [agree_fpUpdate_iff]
  constructor
  · intro h
    have hm := congrArg (fun s : Agree α => s.mem y) h
    exact (Eq.mp hm rfl).symm
  · rintro rfl
    rfl

/-- Set-valued frame-preserving updates do not escape agreement immutability:
if `ag x ⤳: P`, then `P` already holds at `ag x`. -/
theorem agree_fpUpdateP_imp_mem {α : Type} (x : α) {P : Agree α → Prop}
    (h : fpUpdateP (agreeRA α) (.ag x) P) : P (.ag x) := by
  have hv : (agreeRA α).valid (opOpt (agreeRA α) (.ag x) (some (.ag x))) :=
    (agree_ag_op_valid_iff x x).mpr rfl
  rcases h (some (.ag x)) hv with ⟨s, hPs, hvsf⟩
  have hvs : (agreeRA α).valid s := agreeRA_validOpL α s (.ag x) hvsf
  rcases agree_valid_eq_ag hvs with ⟨y, rfl⟩
  have heq : y = x := (agree_ag_op_valid_iff y x).mp hvsf
  subst heq
  exact hPs

theorem agree_fpUpdate_iff_nonvacuity :
    IsCoreFreeRA (agreeRA Bool) ∧ (agreeRA Bool).valid (.ag false) ∧
    (agreeRA Bool).valid (.ag true) :=
  ⟨agreeRA_isCoreFreeRA Bool, agree_ag_valid false, agree_ag_valid true⟩

/-- Exposed witness frame for the naive agreement update: whenever `x ≠ y`, the
duplicate frame `Agree.ag x` composes validly with `Agree.ag x` but composes
invalidly with `Agree.ag y`. -/
theorem agree_naive_update_witness_frame {α : Type} {x y : α} (hxy : x ≠ y) :
    (agreeRA α).valid ((agreeRA α).op (.ag x) (.ag x)) ∧
    ¬ (agreeRA α).valid ((agreeRA α).op (.ag y) (.ag x)) := by
  refine ⟨(agree_ag_op_valid_iff x x).mpr rfl, ?_⟩
  intro hv
  exact hxy ((agree_ag_op_valid_iff y x).mp hv).symm

/-- Impossibility of changing an agreed value, with the conflicting duplicate
frame `Agree.ag x` exposed directly: whenever `x ≠ y`, `ag x` composes validly
with `ag x` and invalidly with `ag y`, refuting `ag x ⤳ ag y`. -/
theorem agree_distinct_not_fpUpdate {α : Type} {x y : α} (hxy : x ≠ y) :
    (agreeRA α).valid ((agreeRA α).op (.ag x) (.ag x)) ∧
    ¬ (agreeRA α).valid ((agreeRA α).op (.ag y) (.ag x)) ∧
    ¬ fpUpdate (agreeRA α) (.ag x) (.ag y) := by
  have ⟨hv, hnv⟩ := agree_naive_update_witness_frame hxy
  exact ⟨hv, hnv, fun hupd => hnv (hupd (some (.ag x)) hv)⟩

/-- Concrete ground counterexample for the naive agreement update on `Bool`:
changing `ag false` to `ag true` breaks compatibility with frame `ag false`. -/
theorem agree_naive_update_bool_counterexample :
    (agreeRA Bool).valid ((agreeRA Bool).op (.ag false) (.ag false)) ∧
    ¬ (agreeRA Bool).valid ((agreeRA Bool).op (.ag true) (.ag false)) ∧
    ¬ fpUpdate (agreeRA Bool) (.ag false) (.ag true) :=
  agree_distinct_not_fpUpdate Bool.false_ne_true

theorem agree_distinct_not_fpUpdate_nonvacuity :
    IsCoreFreeRA (agreeRA Bool) ∧ (false ≠ true) :=
  ⟨agreeRA_isCoreFreeRA Bool, Bool.false_ne_true⟩

/-- Canonical tightness counterexample for `hxy : x ≠ y` in
`agree_distinct_not_fpUpdate`: when `x = y`, the no-op update `ag false ⤳ ag false`
is frame-preserving, refuting the impossibility conclusion. -/
theorem agree_same_fpUpdate_counterexample :
    IsCoreFreeRA (agreeRA Bool) ∧ ¬ (false ≠ false) ∧
    fpUpdate (agreeRA Bool) (.ag false) (.ag false) ∧
    ¬ ((agreeRA Bool).valid ((agreeRA Bool).op (.ag false) (.ag false)) ∧
       ¬ (agreeRA Bool).valid ((agreeRA Bool).op (.ag false) (.ag false)) ∧
       ¬ fpUpdate (agreeRA Bool) (.ag false) (.ag false)) :=
  ⟨agreeRA_isCoreFreeRA Bool, fun h => h rfl,
   fpUpdate_refl (agreeRA Bool) (.ag false),
   fun ⟨_, _, hnot⟩ => hnot (fpUpdate_refl (agreeRA Bool) (.ag false))⟩

/-- Positive control for `agree_distinct_not_fpUpdate`: replacing duplicable
agreement (`agreeRA Bool`) with exclusive ownership (`exclRA Bool`) makes the
update from `false` to `true` frame-preserving. -/
theorem agree_distinct_positive_control_excl :
    IsCoreFreeRA (exclRA Bool) ∧ (false ≠ true) ∧
    fpUpdate (exclRA Bool) (.excl false) (.excl true) :=
  ⟨exclRA_isCoreFreeRA Bool, Bool.false_ne_true, excl_fpUpdate false true⟩

/-! ## Exclusivity Tightness Counterexample for `exclusive_fpUpdate` -/

/-- Canonical counterexample showing `hExcl : IsExclusive R a` is necessary in
`exclusive_fpUpdate`: in `agreeRA Bool`, `IsCoreFreeRA` holds and target `.ag true`
is valid, `.ag false` is not exclusive (compatible with itself), and
`.ag false ⤳ .ag true` fails. -/
theorem exclusive_fpUpdate_not_exclusive_counterexample :
    IsCoreFreeRA (agreeRA Bool) ∧
    (agreeRA Bool).valid (.ag true) ∧
    ¬ IsExclusive (agreeRA Bool) (.ag false) ∧
    ¬ fpUpdate (agreeRA Bool) (.ag false) (.ag true) := by
  refine ⟨agreeRA_isCoreFreeRA Bool, agree_ag_valid true, ?_,
          (agree_distinct_not_fpUpdate Bool.false_ne_true).2.2⟩
  intro hex
  exact hex (.ag false) ((agree_ag_op_valid_iff false false).mpr rfl)

end Toy.RA
