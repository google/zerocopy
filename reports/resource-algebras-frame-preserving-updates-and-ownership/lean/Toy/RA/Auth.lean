import Toy.RA.Core

/-!
# Authoritative / Fragment Resource Algebra (`Auth`) and Local Updates

Models Iris's authoritative resource algebra (`authRA R`), combining a unique
authoritative snapshot `authElem a` (`● a`) with shareable fragments
`fragElem b` (`◯ b`). Composition of `authElem a` and `fragElem b` is valid
iff `R.valid a ∧ includedRefl R b a` (which simplifies to `b ≤ a` for the
additive counter algebra `counterRA := natAddRA`).

Contains both:
- `auth_both_fpUpdate_iff`: the exact, law-free characterization of
  right-frame-preserving authoritative/fragment updates (matching `iris-lean`'s
  `auth_update_ord`), and
- `auth_localUpdate_fpUpdate`: the standard sufficient condition lifting any
  `LocalUpdate` on an associative base algebra `R` to a right-frame-preserving
  update `auth a · frag b ⤳ auth a' · frag b'` (capturing Iris's `auth_update`
  via `optionUR` + `option_local_update`).
-/

namespace Toy.RA

/-- The authoritative-token component of an `AuthElem`: either absent (`none`),
uniquely held with snapshot `a` (`excl a`), or conflicted (`conflict`) when two
authoritative elements are composed. -/
inductive AuthPart (α : Type) where
  | none
  | excl (a : α)
  | conflict
  deriving DecidableEq, Repr

/-- Composition on `AuthPart`: `none` is an identity, and composing any two
non-empty authoritative parts yields `conflict`. -/
def AuthPart.op {α : Type} : AuthPart α → AuthPart α → AuthPart α
  | .none, p => p
  | p, .none => p
  | _, _ => .conflict

/-- Unit-adjoining composition on `Option α`: `none` acts as a two-sided
identity, while two `some` values combine via `f`. Captures Iris's `option`
CMRA composition. -/
def optOp {α : Type} (f : α → α → α) : Option α → Option α → Option α
  | none, y => y
  | x, none => x
  | some a, some b => some (f a b)

/-- Elements of the authoritative/fragment resource algebra over carrier `α`:
an authoritative token slot (`auth`) paired with an optional fragment (`frag`).
Using `Option α` for fragments allows `authRA R` to work uniformly for any
`RawRA α` without requiring a unit on `R` (matching Iris's `auth (optionUR R)`). -/
structure AuthElem (α : Type) where
  auth : AuthPart α
  frag : Option α
  deriving DecidableEq, Repr

@[ext]
theorem AuthElem.ext {α : Type} {x y : AuthElem α}
    (ha : x.auth = y.auth) (hf : x.frag = y.frag) : x = y := by
  cases x
  cases y
  cases ha
  cases hf
  rfl

/-- Authoritative snapshot element `● a` (no fragment attached). -/
def authElem {α : Type} (a : α) : AuthElem α :=
  ⟨.excl a, none⟩

/-- Fragment element `◯ b` (no authoritative snapshot attached). -/
def fragElem {α : Type} (b : α) : AuthElem α :=
  ⟨.none, some b⟩

/-- Empty authoritative element `ε` (identity of `authRA R`). -/
def authUnit {α : Type} : AuthElem α :=
  ⟨.none, none⟩

/-- The discrete authoritative/fragment resource algebra over a base `RawRA α`
`R`. Captures Iris's discrete `auth` construction (with exclusive authoritative
ownership and optional fragment slot, matching `auth (optionUR R)`). -/
def authRA {α : Type} (R : RawRA α) : RawRA (AuthElem α) where
  op x y := ⟨AuthPart.op x.auth y.auth, optOp R.op x.frag y.frag⟩
  valid x :=
    match x.auth, x.frag with
    | .conflict, _ => False
    | .none, none => True
    | .none, some b => R.valid b
    | .excl a, none => R.valid a
    | .excl a, some b => R.valid a ∧ includedRefl R b a

/-! ## Algebraic Laws and Structural Properties of `authRA` -/

theorem AuthPart.op_assoc {α : Type} (x y z : AuthPart α) :
    AuthPart.op (AuthPart.op x y) z = AuthPart.op x (AuthPart.op y z) := by
  cases x <;> cases y <;> cases z <;> rfl

theorem AuthPart.op_comm {α : Type} (x y : AuthPart α) :
    AuthPart.op x y = AuthPart.op y x := by
  cases x <;> cases y <;> rfl

theorem optOp_assoc {α : Type} {f : α → α → α}
    (hAssoc : ∀ x y z, f (f x y) z = f x (f y z)) (x y z : Option α) :
    optOp f (optOp f x y) z = optOp f x (optOp f y z) := by
  cases x <;> cases y <;> cases z <;> simp [optOp, hAssoc]

theorem optOp_comm {α : Type} {f : α → α → α}
    (hComm : ∀ x y, f x y = f y x) (x y : Option α) :
    optOp f x y = optOp f y x := by
  cases x <;> cases y <;> simp [optOp, hComm]

theorem authRA_opAssoc {α : Type} (R : RawRA α) (hAssoc : OpAssoc R) :
    OpAssoc (authRA R) := by
  intro x y z
  exact AuthElem.ext (AuthPart.op_assoc x.auth y.auth z.auth)
                     (optOp_assoc hAssoc x.frag y.frag z.frag)

theorem authRA_opComm {α : Type} (R : RawRA α) (hComm : OpComm R) :
    OpComm (authRA R) := by
  intro x y
  exact AuthElem.ext (AuthPart.op_comm x.auth y.auth)
                     (optOp_comm hComm x.frag y.frag)

theorem authRA_validOpL {α : Type} (R : RawRA α) (hAssoc : OpAssoc R) (hValidOpL : ValidOpL R) :
    ValidOpL (authRA R) := by
  rintro ⟨xa, xf⟩ ⟨ya, yf⟩ hxy
  cases xa with
  | conflict =>
    cases ya <;> exact False.elim hxy
  | none =>
    cases xf with
    | none => exact trivial
    | some b₁ =>
      cases ya with
      | conflict => exact False.elim hxy
      | none =>
        cases yf with
        | none => exact hxy
        | some b₂ => exact hValidOpL b₁ b₂ hxy
      | excl a =>
        cases yf with
        | none =>
          rcases hxy with ⟨hva, mc, hmc⟩
          cases mc with
          | none =>
            rw [opOpt_none] at hmc
            exact hmc ▸ hva
          | some c =>
            rw [opOpt_some] at hmc
            exact hValidOpL b₁ c (hmc ▸ hva)
        | some b₂ =>
          rcases hxy with ⟨hva, mc, hmc⟩
          cases mc with
          | none =>
            rw [opOpt_none] at hmc
            exact hValidOpL b₁ b₂ (hmc ▸ hva)
          | some c =>
            rw [opOpt_some] at hmc
            exact hValidOpL b₁ b₂ (hValidOpL (R.op b₁ b₂) c (hmc ▸ hva))
  | excl a =>
    cases ya with
    | excl _ => exact False.elim hxy
    | conflict => exact False.elim hxy
    | none =>
      cases xf with
      | none =>
        cases yf with
        | none => exact hxy
        | some _ => exact hxy.1
      | some b₁ =>
        cases yf with
        | none => exact hxy
        | some b₂ =>
          rcases hxy with ⟨hva, mc, hmc⟩
          refine ⟨hva, ?_⟩
          cases mc with
          | none =>
            rw [opOpt_none] at hmc
            exact ⟨some b₂, hmc⟩
          | some c =>
            rw [opOpt_some, hAssoc] at hmc
            exact ⟨some (R.op b₂ c), hmc⟩

theorem authRA_isCoreFreeRA {α : Type} (R : RawRA α) (h : IsCoreFreeRA R) :
    IsCoreFreeRA (authRA R) :=
  ⟨authRA_opAssoc R h.1, authRA_opComm R h.2.1, authRA_validOpL R h.1 h.2.2⟩

theorem authRA_rightUnit {α : Type} (R : RawRA α) : IsRightUnit (authRA R) authUnit := by
  intro x
  cases hxA : x.auth <;> cases hxF : x.frag <;>
    exact AuthElem.ext (by simp [authRA, authUnit, AuthPart.op, hxA])
                       (by simp [authRA, authUnit, optOp, hxF])

/-- Two authoritative tokens cannot validly compose. Captures Iris's
`auth_auth_op_valid`. -/
theorem auth_auth_exclusive {α : Type} (R : RawRA α) (a₁ a₂ : α) :
    ¬ (authRA R).valid ((authRA R).op (authElem a₁) (authElem a₂)) :=
  fun h => h

/-- Exact validity characterization for `auth a · frag b`: it is valid iff `a`
is valid in `R` and `b` is reflexively included in `a`. Captures Iris's
`auth_both_valid_discrete`. -/
theorem auth_both_valid_iff {α : Type} (R : RawRA α) (a b : α) :
    (authRA R).valid ((authRA R).op (authElem a) (fragElem b)) ↔
      R.valid a ∧ includedRefl R b a :=
  Iff.rfl

/-! ## Concrete Counter Resource Algebra (`counterRA`) -/

/-- Alias for `natAddRA` (`Nat` under `+` with universal validity) when used
as the base counter algebra of `authRA`. -/
abbrev counterRA : RawRA Nat := natAddRA

theorem counterRA_opAssoc : OpAssoc counterRA := opAssoc_pos_example

theorem counterRA_opComm : OpComm counterRA := opComm_pos_example

theorem counterRA_validOpL : ValidOpL counterRA := fun _ _ _ => trivial

theorem counterRA_isCoreFreeRA : IsCoreFreeRA counterRA :=
  ⟨counterRA_opAssoc, counterRA_opComm, counterRA_validOpL⟩

theorem counterRA_rightUnit : IsRightUnit counterRA 0 := isRightUnit_pos_example

theorem counter_included_iff (b a : Nat) : included counterRA b a ↔ b ≤ a := by
  constructor
  · rintro ⟨c, rfl⟩
    exact Nat.le_add_right b c
  · intro h
    exact ⟨a - b, Nat.add_sub_of_le h⟩

theorem counter_includedRefl_iff (b a : Nat) : includedRefl counterRA b a ↔ b ≤ a :=
  (includedRefl_iff_included_of_rightUnit counterRA 0 counterRA_rightUnit b a).trans
    (counter_included_iff b a)

/-- In `authRA counterRA`, `auth a · frag b` is valid iff `b ≤ a`. -/
theorem auth_counter_both_valid_iff (a b : Nat) :
    (authRA counterRA).valid ((authRA counterRA).op (authElem a) (fragElem b)) ↔ b ≤ a := by
  rw [auth_both_valid_iff, counter_includedRefl_iff]
  exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

/-! ## Positive and Negative Examples for `authRA` and `counterRA` -/

theorem authRA_pos_example :
    IsCoreFreeRA (authRA counterRA) ∧
    (authRA counterRA).valid ((authRA counterRA).op (authElem 3) (fragElem 2)) :=
  ⟨authRA_isCoreFreeRA counterRA counterRA_isCoreFreeRA,
   (auth_counter_both_valid_iff 3 2).mpr (by omega)⟩

theorem authRA_neg_example :
    ¬ (authRA counterRA).valid ((authRA counterRA).op (authElem 2) (fragElem 3)) ∧
    ¬ (authRA counterRA).valid ((authRA counterRA).op (authElem 2) (authElem 2)) :=
  ⟨fun h => by have := (auth_counter_both_valid_iff 2 3).mp h; omega,
   auth_auth_exclusive counterRA 2 2⟩

/-! ## Main Result 4a-exact: Law-Free Authoritative/Fragment Update Characterization -/

/-- Exact, law-free characterization of right-frame-preserving updates on
`authRA R`: `authElem a · fragElem b ⤳ authElem a' · fragElem b'` holds iff for
every optional external fragment frame `mbf : Option α`, validity of `a` and
reflexive inclusion `(b ·? mbf) ≼? a` imply validity of `a'` and
`(b' ·? mbf) ≼? a'`. Captures the discrete counterpart of `iris-lean`'s
`auth_update_ord`, requiring zero algebraic laws on `R`. Under `OpComm R`,
right-frame preservation also preserves each single left-composed frame
(`fpUpdate_preserve_left_of_opComm`); simultaneous two-sided contexts
`l · (x · r)` are preserved under `OpComm R` and `OpAssoc R`
(`fpUpdate2_of_assoc_comm`), not under `OpComm R` alone
(`auth_opComm_alone_not_two_sided`). -/
theorem auth_both_fpUpdate_iff {α : Type} (R : RawRA α) (a b a' b' : α) :
    fpUpdate (authRA R) ((authRA R).op (authElem a) (fragElem b))
                        ((authRA R).op (authElem a') (fragElem b')) ↔
      ∀ mbf : Option α, R.valid a ∧ includedRefl R (opOpt R b mbf) a →
        R.valid a' ∧ includedRefl R (opOpt R b' mbf) a' := by
  constructor
  · intro h mbf hv
    cases mbf with
    | none => exact h none hv
    | some bf => exact h (some (fragElem bf)) hv
  · intro h mf hmf
    rcases mf with _ | ⟨pf, mbf⟩
    · exact h none hmf
    · cases pf with
      | excl _ => exact False.elim hmf
      | conflict => exact False.elim hmf
      | none =>
        cases mbf with
        | none => exact h none hmf
        | some bf => exact h (some bf) hmf

theorem auth_both_fpUpdate_iff_nonvacuity :
    IsCoreFreeRA (authRA counterRA) ∧
    (authRA counterRA).valid ((authRA counterRA).op (authElem 2) (fragElem 1)) ∧
    ¬ LocalUpdate counterRA 2 1 3 1 ∧
    (∀ mbf : Option Nat,
      counterRA.valid 2 ∧ includedRefl counterRA (opOpt counterRA 1 mbf) 2 →
      counterRA.valid 3 ∧ includedRefl counterRA (opOpt counterRA 1 mbf) 3) := by
  refine ⟨authRA_isCoreFreeRA counterRA counterRA_isCoreFreeRA,
          (auth_counter_both_valid_iff 2 1).mpr (by omega), ?_, ?_⟩
  · intro hloc
    have h' := hloc (some 1) trivial rfl
    dsimp [opOpt, counterRA, natAddRA] at h'
    omega
  · intro mbf ⟨_, hmbf⟩
    cases mbf with
    | none =>
      have hle : 1 ≤ 2 := (counter_includedRefl_iff 1 2).mp hmbf
      exact ⟨trivial, (counter_includedRefl_iff 1 3).mpr (by omega)⟩
    | some bf =>
      have hle : 1 + bf ≤ 2 := (counter_includedRefl_iff (1 + bf) 2).mp hmbf
      exact ⟨trivial, (counter_includedRefl_iff (1 + bf) 3).mpr (by omega)⟩

/-! ## Main Result 4a: Sufficient Local-Update Lifting Theorem -/

/-- Sufficient local condition for right-frame-preserving authoritative updates:
if `R` is associative and `(a, b)` locally updates to `(a', b')`, then
`auth a · frag b ⤳ auth a' · frag b'` in `authRA R` (reducing `LocalUpdate` to
the exact frame-inclusion condition `auth_both_fpUpdate_iff`). Captures Iris's
`auth_update` instantiated via `optionUR` (`option_local_update`), which uses
only associativity for right-composed frames; without `OpComm R`, right-frame
`fpUpdate` does not protect fragments composed on the left
(`auth_pathCat_localUpdate_breaks_left_frame`). -/
theorem auth_localUpdate_fpUpdate {α : Type} (R : RawRA α) (hAssoc : OpAssoc R)
    (a b a' b' : α) (hLoc : LocalUpdate R a b a' b') :
    fpUpdate (authRA R) ((authRA R).op (authElem a) (fragElem b))
                        ((authRA R).op (authElem a') (fragElem b')) := by
  refine (auth_both_fpUpdate_iff R a b a' b').mpr ?_
  rintro mbf ⟨hva, mc, hmc⟩
  let mz : Option α := optOp R.op mbf mc
  have hz : ∀ x : α, opOpt R (opOpt R x mbf) mc = opOpt R x mz := by
    intro x
    cases mbf <;> cases mc <;> first | rfl | exact hAssoc _ _ _
  rw [hz] at hmc
  rcases hLoc mz hva hmc with ⟨hva', heq⟩
  refine ⟨hva', mc, ?_⟩
  rw [hz]; exact heq

/-! ## Main Result 4b: Concrete Counter Increment Instance (Fully Proved) -/

/-- Standard local-update instance: adding `k` to both the authoritative
counter `a` and the owned fragment `b` is a local update in `counterRA`. -/
theorem counter_inc_localUpdate (a b k : Nat) :
    LocalUpdate counterRA a b (a + k) (b + k) := by
  intro mz _ h
  cases mz with
  | none =>
    rw [opOpt_none] at h ⊢
    exact ⟨trivial, by omega⟩
  | some c =>
    dsimp [opOpt, counterRA, natAddRA] at h ⊢
    exact ⟨trivial, by omega⟩

/-- Matched decrement of both `auth` and `frag` by `1` (`(2, 1) → (1, 0)`) is a
valid `LocalUpdate` in `counterRA`, contrasting with `auth_counter_dec_auth_only_fails`. -/
theorem counter_dec_both_localUpdate : LocalUpdate counterRA 2 1 1 0 := by
  intro mz _ h
  cases mz with
  | none => simp [opOpt] at h
  | some c =>
    dsimp [opOpt, counterRA, natAddRA] at h ⊢
    exact ⟨trivial, by omega⟩

/-- Concrete authoritative counter increment is frame-preserving:
`auth a · frag b ⤳ auth (a + k) · frag (b + k)` for all `a b k : Nat`. -/
theorem auth_counter_inc_fpUpdate (a b k : Nat) :
    fpUpdate (authRA counterRA)
      ((authRA counterRA).op (authElem a) (fragElem b))
      ((authRA counterRA).op (authElem (a + k)) (fragElem (b + k))) := by
  intro mf hmf
  cases mf with
  | none =>
    have hle := (auth_counter_both_valid_iff a b).mp hmf
    exact (auth_counter_both_valid_iff (a + k) (b + k)).mpr (by omega)
  | some f =>
    rcases f with ⟨pf, mbf⟩
    cases pf with
    | excl _ => exact False.elim hmf
    | conflict => exact False.elim hmf
    | none =>
      cases mbf with
      | none =>
        have hle := (auth_counter_both_valid_iff a b).mp hmf
        exact (auth_counter_both_valid_iff (a + k) (b + k)).mpr (by omega)
      | some bf =>
        have hle : b + bf ≤ a := (counter_includedRefl_iff (b + bf) a).mp hmf.2
        refine ⟨trivial, (counter_includedRefl_iff ((b + k) + bf) (a + k)).mpr ?_⟩
        omega

theorem auth_counter_inc_fpUpdate_nonvacuity :
    IsCoreFreeRA (authRA counterRA) ∧
    (authRA counterRA).valid ((authRA counterRA).op (authElem 2) (fragElem 1)) ∧
    LocalUpdate counterRA 2 1 5 4 :=
  ⟨authRA_isCoreFreeRA counterRA counterRA_isCoreFreeRA,
   (auth_counter_both_valid_iff 2 1).mpr (by omega),
   counter_inc_localUpdate 2 1 3⟩

theorem auth_localUpdate_fpUpdate_nonvacuity :
    OpAssoc counterRA ∧ LocalUpdate counterRA 2 1 3 2 ∧
    (authRA counterRA).valid ((authRA counterRA).op (authElem 2) (fragElem 1)) :=
  ⟨counterRA_opAssoc, counter_inc_localUpdate 2 1 1,
   (auth_counter_both_valid_iff 2 1).mpr (by omega)⟩

/-! ## Naive-Update Counterexamples and Tightness Witnesses for `auth_localUpdate_fpUpdate` -/

/-- Canonical tightness counterexample for `hLoc` in `auth_localUpdate_fpUpdate`
and concrete naive-update counterexample: in `counterRA` (hence in `authRA counterRA`
by `authRA_isCoreFreeRA`), decrementing the authoritative counter from `2` to `1`
while keeping fragment `1` is not a local update and breaks compatibility with
another frame `frag 1`. -/
theorem auth_counter_dec_auth_only_fails :
    OpAssoc counterRA ∧ OpComm counterRA ∧ ValidOpL counterRA ∧
    ¬ LocalUpdate counterRA 2 1 1 1 ∧
    (authRA counterRA).valid
      ((authRA counterRA).op ((authRA counterRA).op (authElem 2) (fragElem 1)) (fragElem 1)) ∧
    ¬ (authRA counterRA).valid
      ((authRA counterRA).op ((authRA counterRA).op (authElem 1) (fragElem 1)) (fragElem 1)) ∧
    ¬ fpUpdate (authRA counterRA)
      ((authRA counterRA).op (authElem 2) (fragElem 1))
      ((authRA counterRA).op (authElem 1) (fragElem 1)) := by
  have hv :
      (authRA counterRA).valid
        ((authRA counterRA).op ((authRA counterRA).op (authElem 2) (fragElem 1)) (fragElem 1)) :=
    ⟨trivial, (counter_includedRefl_iff 2 2).mpr (by omega)⟩
  have hnv :
      ¬ (authRA counterRA).valid
        ((authRA counterRA).op ((authRA counterRA).op (authElem 1) (fragElem 1)) (fragElem 1)) := by
    intro h
    have hle := (counter_includedRefl_iff 2 1).mp h.2
    omega
  refine ⟨counterRA_opAssoc, counterRA_opComm, counterRA_validOpL, ?_, hv, hnv, ?_⟩
  · intro hloc
    have h' := hloc (some 1) trivial rfl
    dsimp [opOpt, counterRA, natAddRA] at h'
    omega
  · intro hupd
    exact hnv (hupd (some (fragElem 1)) hv)

/-- Naive fragment-only inflation fails: `frag 1 ⤳ frag 2` is not
frame-preserving in `authRA counterRA`, witnessed by frame `auth 1`. -/
theorem auth_counter_inc_frag_only_fails :
    (authRA counterRA).valid ((authRA counterRA).op (fragElem 1) (authElem 1)) ∧
    ¬ (authRA counterRA).valid ((authRA counterRA).op (fragElem 2) (authElem 1)) ∧
    ¬ fpUpdate (authRA counterRA) (fragElem 1) (fragElem 2) := by
  have hv : (authRA counterRA).valid ((authRA counterRA).op (fragElem 1) (authElem 1)) :=
    ⟨trivial, (counter_includedRefl_iff 1 1).mpr (by omega)⟩
  have hnv : ¬ (authRA counterRA).valid ((authRA counterRA).op (fragElem 2) (authElem 1)) := by
    intro h
    have hle := (counter_includedRefl_iff 2 1).mp h.2
    omega
  exact ⟨hv, hnv, fun hupd => hnv (hupd (some (authElem 1)) hv)⟩

/-- Non-converse witness for `auth_localUpdate_fpUpdate`: in `counterRA`,
`auth 2 · frag 1 ⤳ auth 3 · frag 1` IS frame-preserving even though
`(2, 1) → (3, 1)` is NOT a `LocalUpdate`. Shows `LocalUpdate` is sufficient
but not necessary for authoritative frame-preserving updates. -/
theorem auth_counter_alloc_only_not_localUpdate :
    ¬ LocalUpdate counterRA 2 1 3 1 ∧
    fpUpdate (authRA counterRA)
      ((authRA counterRA).op (authElem 2) (fragElem 1))
      ((authRA counterRA).op (authElem 3) (fragElem 1)) := by
  refine ⟨?_, ?_⟩
  · intro hloc
    have h' := hloc (some 1) trivial rfl
    dsimp [opOpt, counterRA, natAddRA] at h'
    omega
  · exact (auth_both_fpUpdate_iff counterRA 2 1 3 1).mpr
      auth_both_fpUpdate_iff_nonvacuity.2.2.2

/-- Four-element carrier used to show `OpAssoc R` is strictly necessary in
`auth_localUpdate_fpUpdate`. -/
inductive Four where
  | e0 | e1 | e2 | e3
  deriving DecidableEq, Repr

/-- Symmetric, universally valid, non-associative 4-element raw algebra where
`(e0, e1) → (e2, e2)` is a non-vacuous `LocalUpdate`, yet
`auth e0 · frag e1 ⤳ auth e2 · frag e2` fails at frame `frag e1`. -/
def authNonAssocRA : RawRA Four where
  op
    | .e0, .e0 => .e0 | .e0, .e1 => .e0 | .e0, .e2 => .e2 | .e0, .e3 => .e0
    | .e1, .e0 => .e0 | .e1, .e1 => .e3 | .e1, .e2 => .e3 | .e1, .e3 => .e3
    | .e2, .e0 => .e2 | .e2, .e1 => .e3 | .e2, .e2 => .e2 | .e2, .e3 => .e3
    | .e3, .e0 => .e0 | .e3, .e1 => .e3 | .e3, .e2 => .e3 | .e3, .e3 => .e0
  valid _ := True

theorem authNonAssocRA_opComm : OpComm authNonAssocRA := by
  intro x y
  cases x <;> cases y <;> rfl

theorem authNonAssocRA_validOpL : ValidOpL authNonAssocRA :=
  fun _ _ _ => trivial

theorem authNonAssocRA_not_opAssoc : ¬ OpAssoc authNonAssocRA := by
  intro h
  have h0 := h .e1 .e1 .e3
  cases h0

theorem authNonAssocRA_localUpdate :
    LocalUpdate authNonAssocRA .e0 .e1 .e2 .e2 := by
  intro mz _ h
  cases mz with
  | none => cases h
  | some c =>
    cases c with
    | e0 => exact ⟨trivial, rfl⟩
    | e1 => cases h
    | e2 => cases h
    | e3 => cases h

/-- Canonical tightness counterexample showing `hAssoc : OpAssoc R` is
necessary in `auth_localUpdate_fpUpdate`: `authNonAssocRA` satisfies `OpComm`,
`ValidOpL`, and `LocalUpdate authNonAssocRA e0 e1 e2 e2` (with valid source
`auth e0 · frag e1`), fails `OpAssoc`, and breaks
`auth e0 · frag e1 ⤳ auth e2 · frag e2` at frame `frag e1`. -/
theorem auth_localUpdate_nonAssoc_counterexample :
    OpComm authNonAssocRA ∧ ValidOpL authNonAssocRA ∧
    ¬ OpAssoc authNonAssocRA ∧
    LocalUpdate authNonAssocRA .e0 .e1 .e2 .e2 ∧
    (authRA authNonAssocRA).valid
      ((authRA authNonAssocRA).op (authElem .e0) (fragElem .e1)) ∧
    ¬ fpUpdate (authRA authNonAssocRA)
      ((authRA authNonAssocRA).op (authElem .e0) (fragElem .e1))
      ((authRA authNonAssocRA).op (authElem .e2) (fragElem .e2)) := by
  refine ⟨authNonAssocRA_opComm, authNonAssocRA_validOpL,
          authNonAssocRA_not_opAssoc, authNonAssocRA_localUpdate,
          ⟨trivial, some .e0, rfl⟩, ?_⟩
  intro hupd
  have hv :
      (authRA authNonAssocRA).valid
        (opOpt (authRA authNonAssocRA)
          ((authRA authNonAssocRA).op (authElem .e0) (fragElem .e1))
          (some (fragElem .e1))) :=
    ⟨trivial, some .e3, rfl⟩
  have hv' := hupd (some (fragElem .e1)) hv
  rcases hv'.2 with ⟨mc, hmc⟩
  cases mc with
  | none => cases hmc
  | some c => cases c <;> cases hmc

end Toy.RA
