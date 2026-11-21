/-
Toy.Modality.SROA
=================

Scalar replacement of aggregates (SROA) in the toy type language, with the
documented deep modality computation `modAt`, and three repair policies.

A scalarization of a local of type `τ` replaces it by new locals, one per
field path `q`, each with a type.  A program asserts validity of pointer leaves
(at retags and passes); an execution assigns to every asserted leaf the call
trace observed there.  The source asserts the leaf's modality computed in `τ`;
the target asserts the modality computed in the new local's type at the same
program point.  Scalarization is a refinement for all programs when every
execution that is defined for the source is defined for the target.
-/
import Toy.Modality.Niche

namespace Toy.Modality

/-! ## Fields and position modality -/

/-- The documented modality of the pointer leaf at path `p` of `τ`. -/
def modAt (τ : Ty) (p : Path) : Option (Shape × Mod) := comp tRelax true τ p

/-- Declared type of the field at path `q` of `τ` (`[]` is `τ` itself). -/
def fieldTy : Ty → Path → Option Ty
  | τ, [] => some τ
  | .pair a _, .fst :: q => fieldTy a q
  | .pair _ b, .snd :: q => fieldTy b q
  | .wrap _ τ, .inner :: q => fieldTy τ q
  | _, _ => none

/-- Transformer of one wrapper: `tRelax` for relaxing wrappers, identity
otherwise. -/
def wrapTrans (w : Wrap) (m : Mod) : Mod := if w.relaxes then tRelax m else m

/-- Composition of the transformers of all wrappers enclosing the field at
path `q` of `τ` (innermost first). -/
def posTrans : Ty → Path → Mod → Mod
  | _, [] => id
  | .pair a _, .fst :: q => posTrans a q
  | .pair _ b, .snd :: q => posTrans b q
  | .wrap w τ, .inner :: q => fun m => wrapTrans w (posTrans τ q m)
  | _, _ => id

/-! ## Programs, scalarizations, refinement -/

/-- A program over one local, abstracted to the pointer leaves (absolute paths)
at which it asserts validity and the call trace observed at each assertion. -/
structure Prog where
  asserts : Path → Bool
  exec : Path → Trace

/-- The source program is defined: every asserted leaf satisfies its modality
in `τ`. -/
def SrcSafe (τ : Ty) (P : Prog) : Prop :=
  ∀ p s m, modAt τ p = some (s, m) → P.asserts p = true → den s m (P.exec p)

/-- The scalarized program is defined: for every new local `(q, σ)`, every
asserted leaf `q ++ p'` satisfies the modality of leaf `p'` in `σ`. -/
def TgtSafe (locals : List (Path × Ty)) (P : Prog) : Prop :=
  ∀ q σ, (q, σ) ∈ locals → ∀ p' s m, modAt σ p' = some (s, m) →
    P.asserts (q ++ p') = true → den s m (P.exec (q ++ p'))

/-- Replacing a local of type `τ` by the new locals is a refinement for all
programs. -/
def Refines (τ : Ty) (locals : List (Path × Ty)) : Prop :=
  ∀ P, SrcSafe τ P → TgtSafe locals P

/-- SROA: one new local per field path in `qs`, with the field's declared
type (paths that are not fields of `τ` are skipped). -/
def scalarize (τ : Ty) (qs : List Path) : List (Path × Ty) :=
  qs.filterMap fun q => (fieldTy τ q).map fun σ => (q, σ)

/-! ## Helper lemmas -/

theorem fieldTy_nil (τ : Ty) : fieldTy τ [] = some τ := by cases τ <;> rfl

theorem posTrans_nil (τ : Ty) : posTrans τ [] = id := by cases τ <;> rfl

theorem modAt_append (τ : Ty) (q p' : Path) (σ : Ty) (h : fieldTy τ q = some σ) :
    modAt τ (q ++ p') = (modAt σ p').map (fun x => (x.1, posTrans τ q x.2)) := by
  induction τ generalizing q with
  | scalar =>
    cases q with
    | nil => rw [fieldTy_nil] at h; cases h; simp [posTrans_nil]
    | cons st q => simp [fieldTy] at h
  | ptr s m =>
    cases q with
    | nil => rw [fieldTy_nil] at h; cases h; simp [posTrans_nil]
    | cons st q => cases st <;> simp [fieldTy] at h
  | pair a b iha ihb =>
    cases q with
    | nil => rw [fieldTy_nil] at h; cases h; simp [posTrans_nil]
    | cons st q =>
      cases st
      · simp only [fieldTy] at h; simp only [List.cons_append, modAt, comp, posTrans]
        exact iha q h
      · simp only [fieldTy] at h; simp only [List.cons_append, modAt, comp, posTrans]
        exact ihb q h
      · simp [fieldTy] at h
  | wrap w τ ih =>
    cases q with
    | nil => rw [fieldTy_nil] at h; cases h; simp [posTrans_nil]
    | cons st q =>
      cases st
      · simp [fieldTy] at h
      · simp [fieldTy] at h
      · simp only [fieldTy] at h
        simp only [List.cons_append, modAt, comp] at ih ⊢
        rw [ih q h, Option.map_map]
        congr 1
        funext x
        simp [posTrans, wrapTrans]

theorem posTrans_eq (τ : Ty) (q : Path) (m : Mod) :
    posTrans τ q m = if relaxedOn τ q then tRelax m else m := by
  induction τ generalizing q with
  | scalar => cases q <;> simp [posTrans, relaxedOn]
  | ptr s m' => cases q with
    | nil => simp [posTrans, relaxedOn]
    | cons st q => cases st <;> simp [posTrans, relaxedOn]
  | pair a b iha ihb =>
    cases q with
    | nil => simp [posTrans, relaxedOn]
    | cons st q =>
      cases st
      · simp only [posTrans, relaxedOn]; exact iha q
      · simp only [posTrans, relaxedOn]; exact ihb q
      · simp [posTrans, relaxedOn]
  | wrap w τ ih =>
    cases q with
    | nil => simp [posTrans, relaxedOn]
    | cons st q =>
      cases st
      · simp [posTrans, relaxedOn]
      · simp [posTrans, relaxedOn]
      · simp only [posTrans, relaxedOn, ih q, wrapTrans]
        cases w <;> by_cases hr : relaxedOn τ q = true <;> simp [hr, Wrap.relaxes, tRelax_tRelax]

/-- An aligned, non-null, dangling address whose first pointee byte is written
through an unrelated pointer during the call, and whose argument-derived
pointer reads the byte just past the pointee. -/
def tDangleAliased (s : Shape) : Trace :=
  ⟨s.align, [], [.write .other s.align, .read .arg (s.align + s.size)], []⟩

theorem den_tRelax_tDangleAliased (s : Shape) (m : Mod) : den s (tRelax m) (tDangleAliased s) := by
  have hp := s.align_pos
  refine (relaxRule_iff_den s m _).1 ⟨fun _ => align_mod_align s, fun _ => ?_⟩
  show s.align ≠ 0; omega

theorem not_den_tDangleAliased (s : Shape) (m : Mod)
    (h : m.derefEntry = true ∨ m.derefWhole = true ∨ m.frozen = true ∨ m.unique = true ∨
      m.bounded = true) :
    ¬ den s m (tDangleAliased s) := by
  intro hd
  have hnd := not_dereferenceable_of_live_nil s (tDangleAliased s) rfl
  rcases h with h | h | h | h | h
  · exact hnd (hd .derefEntry h)
  · exact hnd (hd .derefWhole h).1
  · exact hd .frozen h s.align (inRange_self s _) ⟨.other, by simp [tDangleAliased]⟩
  · exact hd .unique h s.align (inRange_self s _) (Or.inr (by simp [tDangleAliased]))
  · have := hd .bounded h (s.align + s.size) (Or.inl (by simp [tDangleAliased]))
    exact Nat.lt_irrefl _ this.2

theorem le_tRelax_iff (m : Mod) :
    m ≤ tRelax m ↔ ¬ (m.derefEntry = true ∨ m.derefWhole = true ∨ m.frozen = true ∨
      m.unique = true ∨ m.bounded = true) := by
  constructor
  · intro h hc
    rcases hc with hc | hc | hc | hc | hc
    · have := h .derefEntry hc; simp [tRelax, Mod.has, Mod.bot] at this
    · have := h .derefWhole hc; simp [tRelax, Mod.has, Mod.bot] at this
    · have := h .frozen hc; simp [tRelax, Mod.has, Mod.bot] at this
    · have := h .unique hc; simp [tRelax, Mod.has, Mod.bot] at this
    · have := h .bounded hc; simp [tRelax, Mod.has, Mod.bot] at this
  · intro h a ha
    cases a <;> simp_all [tRelax, clDeref, Mod.has, Mod.bot]

theorem mem_scalarize (τ : Ty) (qs : List Path) (q : Path) (σ : Ty) :
    (q, σ) ∈ scalarize τ qs ↔ q ∈ qs ∧ fieldTy τ q = some σ := by
  simp only [scalarize, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨q', hq', σ', hσ', rfl, rfl⟩; exact ⟨hq', hσ'⟩
  · rintro ⟨hq, hσ⟩; exact ⟨q, hq, σ, hσ, rfl, rfl⟩

/-! ## Results -/

/-- **SROA modality monotonicity, necessary and sufficient.**  For every type
`τ` and list of field paths `qs`: replacing a local of type `τ` by one local per
field path in `qs`, each with the field's declared type, is a refinement for
all programs (every assertion pattern `P.asserts` and every assignment
`P.exec` of call traces to asserted leaves) iff for every `q ∈ qs` with
declared field type `σ` and every pointer leaf `p'` of `σ` whose modality
computed inside `σ` is `m` (`modAt σ p' = some (s, m)`), `m ≤ posTrans τ q m`
(the field-local modality is at most the position modality). -/
theorem scalarize_refines_iff_declared_le_posMod (τ : Ty) (qs : List Path) :
    Refines τ (scalarize τ qs) ↔
    ∀ q ∈ qs, ∀ σ, fieldTy τ q = some σ → ∀ p' s m, modAt σ p' = some (s, m) →
      m ≤ posTrans τ q m := by
  constructor
  · intro h q hq σ hσ p' s m hm
    apply Classical.byContradiction; intro hle
    rw [posTrans_eq] at hle
    cases hr : relaxedOn τ q
    · rw [hr] at hle; exact hle (mod_bounded_lattice.1 m)
    · rw [hr] at hle
      simp only [↓reduceIte] at hle
      have hbad := Classical.not_not.mp (mt (le_tRelax_iff m).2 hle)
      let P : Prog := ⟨fun r => decide (r = q ++ p'), fun _ => tDangleAliased s⟩
      have hsrc : SrcSafe τ P := by
        intro r s₀ m₀ hr₀ ha
        have : r = q ++ p' := of_decide_eq_true ha
        subst this
        rw [modAt_append τ q p' σ hσ, hm] at hr₀
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr₀
        obtain ⟨rfl, rfl⟩ := hr₀
        rw [posTrans_eq, hr]
        exact den_tRelax_tDangleAliased s m
      exact not_den_tDangleAliased s m hbad
        (h P hsrc q σ ((mem_scalarize τ qs q σ).2 ⟨hq, hσ⟩) p' s m hm (by simp [P]))
  · intro h P hsrc q σ hmem p' s m hm ha
    obtain ⟨hq, hσ⟩ := (mem_scalarize τ qs q σ).1 hmem
    have hτ : modAt τ (q ++ p') = some (s, posTrans τ q m) := by
      rw [modAt_append τ q p' σ hσ, hm]; rfl
    exact den_antitone s (h q hq σ hσ p' s m hm) _ (hsrc _ _ _ hτ ha)

/-- `ManuallyDrop<(&mut T, u8)>` with `T` a scalar of shape `s`. -/
def tyMDPair (s : Shape) : Ty := .wrap .manuallyDrop (.pair (mutRefTy s .scalar) .scalar)

/-- Scalarize `tyMDPair s` into its two innermost fields. -/
def qsMDPair : List Path := [[.inner, .fst], [.inner, .snd]]

/-- A program that asserts validity of the wrapped reference once, observing a
dangling (aligned, non-null, unallocated) pointer. -/
def progDangling (s : Shape) : Prog :=
  ⟨fun r => decide (r = [.inner, .fst]), fun _ => tDangling s⟩

/-- **Hoisting a reference out of `ManuallyDrop` re-attaches promises**
(headline counterexample).  For every shape `s`, scalarizing
`ManuallyDrop<(&mut T, u8)>` (`tyMDPair s`) into its fields `&mut T` and `u8`
with their declared types turns the program `progDangling s`, whose wrapped
reference legally dangles, from defined into undefined: the position modality
of the reference is `tRelax mutFull` while its declared modality is `mutFull`,
whose argument lowering contains `dereferenceable` and `noalias` that the
position modality's lowering lacks. -/
theorem sroa_hoist_out_of_manuallyDrop_counterexample (s : Shape) :
    scalarize (tyMDPair s) qsMDPair =
      [([.inner, .fst], mutRefTy s .scalar), ([.inner, .snd], .scalar)] ∧
    modAt (tyMDPair s) [.inner, .fst] = some (s, tRelax mutFull) ∧
    modAt (mutRefTy s .scalar) [] = some (s, mutFull) ∧
    SrcSafe (tyMDPair s) (progDangling s) ∧
    ¬ TgtSafe (scalarize (tyMDPair s) qsMDPair) (progDangling s) ∧
    ¬ Refines (tyMDPair s) (scalarize (tyMDPair s) qsMDPair) ∧
    (lower s .arg mutFull).dereferenceable = true ∧ (lower s .arg mutFull).noalias = true ∧
    (lower s .arg (tRelax mutFull)).dereferenceable = false ∧
    (lower s .arg (tRelax mutFull)).noalias = false := by
  have hsrc : SrcSafe (tyMDPair s) (progDangling s) := by
    intro r s₀ m₀ hr ha
    have : r = [.inner, .fst] := of_decide_eq_true ha
    subst this
    have : modAt (tyMDPair s) [.inner, .fst] = some (s, tRelax mutFull) := rfl
    rw [this] at hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact den_tRelax_tDangling s _
  have htgt : ¬ TgtSafe (scalarize (tyMDPair s) qsMDPair) (progDangling s) := by
    intro h
    have hd := h [.inner, .fst] (mutRefTy s .scalar) (by simp [scalarize, qsMDPair, tyMDPair,
      fieldTy]) [] s mutFull rfl (by simp [progDangling])
    exact not_dereferenceable_of_live_nil s (tDangling s) rfl (hd .derefEntry rfl)
  exact ⟨by simp [scalarize, qsMDPair, tyMDPair, fieldTy], rfl, rfl, hsrc, htgt,
    fun h => htgt (h _ hsrc), rfl, rfl, rfl, rfl⟩

/-! ## Repairs -/

/-- The type contains a relaxing wrapper (anywhere, by value). -/
def containsRelaxer : Ty → Bool
  | .scalar => false
  | .ptr _ _ => false
  | .pair a b => containsRelaxer a || containsRelaxer b
  | .wrap w τ => w.relaxes || containsRelaxer τ

/-- Replace every pointer leaf's modality `m` by `tRelax m`: a pointer type
that keeps only the alignment and non-null promises of `m` (the modality a
pointer has inside a relaxing wrapper).  If `tRelax m = Mod.bot`, this is `kindBase .raw`;
otherwise it is not the modality of any documented pointer constructor (not proved here). -/
def relaxAll : Ty → Ty
  | .scalar => .scalar
  | .ptr s m => .ptr s (tRelax m)
  | .pair a b => .pair (relaxAll a) (relaxAll b)
  | .wrap w τ => .wrap w (relaxAll τ)

/-- New type for the local of field `q` with declared type `σ`: `relaxAll σ` if a
relaxing wrapper encloses the field, else `σ`. -/
def retype (τ : Ty) (q : Path) (σ : Ty) : Ty := if relaxedOn τ q then relaxAll σ else σ

/-- An SROA policy: given the local's type and requested field paths, either
refuse (`none`) or return the new locals. -/
abbrev Policy := Ty → List Path → Option (List (Path × Ty))

/-- Exclusion policy: refuse aggregates that contain a relaxing wrapper
anywhere; otherwise scalarize with declared types. -/
def repairExclude : Policy := fun τ qs => if containsRelaxer τ then none else some (scalarize τ qs)

/-- Retyping policy: always scalarize, giving each new local the type
`retype`. -/
def repairRetype : Policy := fun τ qs =>
  some (qs.filterMap fun q => (fieldTy τ q).map fun σ => (q, retype τ q σ))

/-- Stop-at-relaxer policy: scalarize with declared types if no requested field
path of `τ` passes through a relaxing wrapper (requested paths that are not
fields of `τ` are ignored); otherwise refuse. -/
def repairStopAtRelaxer : Policy := fun τ qs =>
  if qs.all (fun q => (fieldTy τ q).isNone || !relaxedOn τ q) then some (scalarize τ qs) else none

/-- Unrepaired SROA: always scalarize with declared types. -/
def naivePolicy : Policy := fun τ qs => some (scalarize τ qs)

/-- Every result of the policy is a refinement for all programs. -/
def PolicySound (pol : Policy) : Prop :=
  ∀ τ qs locals, pol τ qs = some locals → Refines τ locals

/-- Every result of the policy has one new local per requested field path of
`τ`, in order (paths that are not fields are dropped), and every pointer leaf
of a new local has exactly the modality the same leaf has in `τ`. -/
def PolicyExact (pol : Policy) : Prop :=
  ∀ τ qs locals, pol τ qs = some locals →
    locals.map Prod.fst = qs.filter (fun q => (fieldTy τ q).isSome) ∧
    ∀ q σ, (q, σ) ∈ locals → ∀ p', modAt σ p' = modAt τ (q ++ p')

theorem relaxedOn_eq_false_of_containsRelaxer (τ : Ty) (q : Path)
    (h : containsRelaxer τ = false) : relaxedOn τ q = false := by
  induction τ generalizing q with
  | scalar => cases q <;> simp [relaxedOn]
  | ptr s m => cases q <;> simp [relaxedOn]
  | pair a b iha ihb =>
    simp only [containsRelaxer, Bool.or_eq_false_iff] at h
    cases q with
    | nil => simp [relaxedOn]
    | cons st q => cases st <;> simp [relaxedOn, iha q h.1, ihb q h.2]
  | wrap w τ ih =>
    simp only [containsRelaxer, Bool.or_eq_false_iff] at h
    cases q with
    | nil => simp [relaxedOn]
    | cons st q => cases st <;> simp [relaxedOn, h.1, ih q h.2]

theorem modAt_relaxAll (σ : Ty) (p : Path) :
    modAt (relaxAll σ) p = (modAt σ p).map (fun x => (x.1, tRelax x.2)) := by
  induction σ generalizing p with
  | scalar => cases p <;> simp [modAt, relaxAll, comp]
  | ptr s m => cases p <;> simp [modAt, relaxAll, comp]
  | pair a b iha ihb =>
    cases p with
    | nil => simp [modAt, relaxAll, comp]
    | cons st p =>
      cases st
      · simp only [modAt, relaxAll, comp] at iha ⊢; exact iha p
      · simp only [modAt, relaxAll, comp] at ihb ⊢; exact ihb p
      · simp [modAt, relaxAll, comp]
  | wrap w τ ih =>
    cases p with
    | nil => simp [modAt, relaxAll, comp]
    | cons st p =>
      cases st
      · simp [modAt, relaxAll, comp]
      · simp [modAt, relaxAll, comp]
      · simp only [modAt, relaxAll, comp] at ih ⊢
        rw [ih p, Option.map_map, Option.map_map]
        congr 1
        funext x
        cases w <;> simp [Wrap.relaxes, tRelax_tRelax]

/-- `retype` gives every pointer leaf of the new local exactly the modality the
same leaf has in `τ`. -/
theorem modAt_retype (τ : Ty) (q p' : Path) (σ : Ty) (h : fieldTy τ q = some σ) :
    modAt (retype τ q σ) p' = modAt τ (q ++ p') := by
  rw [modAt_append τ q p' σ h]
  unfold retype
  cases hr : relaxedOn τ q
  · simp [posTrans_eq, hr]
  · simp [modAt_relaxAll, posTrans_eq, hr]

theorem modAt_eq_of_not_relaxedOn (τ : Ty) (q p' : Path) (σ : Ty) (h : fieldTy τ q = some σ)
    (hr : relaxedOn τ q = false) : modAt σ p' = modAt τ (q ++ p') := by
  rw [modAt_append τ q p' σ h]
  simp [posTrans_eq, hr]

theorem filterMap_fieldTy_map_fst (τ : Ty) (qs : List Path) (f : Path → Ty → Ty) :
    (qs.filterMap fun q => (fieldTy τ q).map fun σ => (q, f q σ)).map Prod.fst =
      qs.filter (fun q => (fieldTy τ q).isSome) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    cases h : fieldTy τ q <;> simp [h, ih]

theorem scalarize_map_fst (τ : Ty) (qs : List Path) :
    (scalarize τ qs).map Prod.fst = qs.filter (fun q => (fieldTy τ q).isSome) :=
  filterMap_fieldTy_map_fst τ qs (fun _ σ => σ)

theorem refines_scalarize_of_not_relaxedOn (τ : Ty) (qs : List Path)
    (h : ∀ q ∈ qs, relaxedOn τ q = false) : Refines τ (scalarize τ qs) := by
  rw [scalarize_refines_iff_declared_le_posMod]
  intro q hq σ _ p' s m _
  rw [posTrans_eq, h q hq]
  exact mod_bounded_lattice.1 m

/-- An exact policy is sound. -/
theorem policySound_of_exact (pol : Policy) (h : PolicyExact pol) : PolicySound pol := by
  intro τ qs locals hp P hsrc q σ hmem p' s m hm ha
  have he := (h τ qs locals hp).2 q σ hmem p'
  rw [he] at hm
  exact hsrc _ _ _ hm ha

/-- **Scope of `PolicyExact`.**  The always-refusing policy is exact
(vacuously: it returns no scalarization), and `PolicyExact` constrains the
modalities of pointer leaves (`modAt`), not the scalar structure of the new
locals: a policy that retypes every scalar field as a pair of scalars, and
otherwise behaves like `repairRetype`, is exact. -/
theorem policyExact_refusing_and_scalar_reshaping :
    PolicyExact (fun _ _ => none) ∧
    PolicyExact (fun τ qs =>
      some (qs.filterMap fun q => (fieldTy τ q).map fun σ =>
        (q, match σ with | .scalar => .pair .scalar .scalar | _ => retype τ q σ))) := by
  refine ⟨fun _ _ _ h => by simp at h, fun τ qs locals h => ?_⟩
  simp only [Option.some.injEq] at h
  subst h
  refine ⟨filterMap_fieldTy_map_fst τ qs _, fun q σ' hmem p' => ?_⟩
  simp only [List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq] at hmem
  obtain ⟨q₀, _, σ, hσ, rfl, rfl⟩ := hmem
  cases σ with
  | scalar =>
    rw [modAt_append τ q₀ p' .scalar hσ]
    cases p' with
    | nil => rfl
    | cons st p' => cases st <;> cases p' <;> rfl
  | ptr s m => exact modAt_retype τ q₀ p' (.ptr s m) hσ
  | pair a b => exact modAt_retype τ q₀ p' (.pair a b) hσ
  | wrap w τ' => exact modAt_retype τ q₀ p' (.wrap w τ') hσ

theorem stopAtRelaxer_not_relaxedOn {τ : Ty} {qs : List Path}
    (hall : qs.all (fun q => (fieldTy τ q).isNone || !relaxedOn τ q) = true)
    {q : Path} (hq : q ∈ qs) {σ : Ty} (hσ : fieldTy τ q = some σ) : relaxedOn τ q = false := by
  have := List.all_eq_true.1 hall q hq
  simp [hσ] at this
  exact this

/-- **Repairs are sound; the unrepaired policy is not.**  The exclusion policy
`repairExclude`, the retyping policy `repairRetype` and the stop-at-relaxer
policy `repairStopAtRelaxer` are each sound (every scalarization they return is
a refinement for all programs), and `naivePolicy` is not. -/
theorem repairs_sound :
    PolicySound repairExclude ∧ PolicySound repairRetype ∧ PolicySound repairStopAtRelaxer ∧
    ¬ PolicySound naivePolicy := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro τ qs locals h
    simp only [repairExclude] at h
    cases hc : containsRelaxer τ
    · rw [hc] at h; simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact refines_scalarize_of_not_relaxedOn τ qs
        (fun q _ => relaxedOn_eq_false_of_containsRelaxer τ q hc)
    · rw [hc] at h; simp at h
  · intro τ qs locals h P hsrc q σ' hmem p' s m' hm ha
    simp only [repairRetype, Option.some.injEq] at h
    subst h
    simp only [List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq] at hmem
    obtain ⟨q₀, _, σ, hσ, rfl, rfl⟩ := hmem
    rw [modAt_retype τ q₀ p' σ hσ] at hm
    exact hsrc _ _ _ hm ha
  · intro τ qs locals h P hsrc q σ hmem p' s m hm ha
    simp only [repairStopAtRelaxer] at h
    split at h
    · rename_i hall
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hq, hσ⟩ := (mem_scalarize τ qs q σ).1 hmem
      rw [modAt_eq_of_not_relaxedOn τ q p' σ hσ (stopAtRelaxer_not_relaxedOn hall hq hσ)] at hm
      exact hsrc _ _ _ hm ha
    · simp at h
  · intro h
    exact (sroa_hoist_out_of_manuallyDrop_counterexample s1).2.2.2.2.2.1
      (h _ _ _ rfl)

/-- **The repairs are exact; the retyping policy never refuses.**  The three
repair policies satisfy `PolicyExact` (one new local per requested field, each
leaf with exactly its modality in the original type), and `repairRetype`
returns a scalarization for every type and every list of paths. -/
theorem repairs_exact_and_retype_total :
    PolicyExact repairExclude ∧ PolicyExact repairRetype ∧ PolicyExact repairStopAtRelaxer ∧
    ∀ τ qs, (repairRetype τ qs).isSome = true := by
  refine ⟨?_, ?_, ?_, fun _ _ => rfl⟩
  · intro τ qs locals h
    simp only [repairExclude] at h
    cases hc : containsRelaxer τ
    · rw [hc] at h; simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      refine ⟨scalarize_map_fst τ qs, fun q σ hmem p' => ?_⟩
      obtain ⟨_, hσ⟩ := (mem_scalarize τ qs q σ).1 hmem
      exact modAt_eq_of_not_relaxedOn τ q p' σ hσ (relaxedOn_eq_false_of_containsRelaxer τ q hc)
    · rw [hc] at h; simp at h
  · intro τ qs locals h
    simp only [repairRetype, Option.some.injEq] at h
    subst h
    refine ⟨filterMap_fieldTy_map_fst τ qs _, fun q σ' hmem p' => ?_⟩
    simp only [List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq] at hmem
    obtain ⟨q₀, _, σ, hσ, rfl, rfl⟩ := hmem
    exact modAt_retype τ q₀ p' σ hσ
  · intro τ qs locals h
    simp only [repairStopAtRelaxer] at h
    split at h
    · rename_i hall
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨scalarize_map_fst τ qs, fun q σ hmem p' => ?_⟩
      obtain ⟨hq, hσ⟩ := (mem_scalarize τ qs q σ).1 hmem
      exact modAt_eq_of_not_relaxedOn τ q p' σ hσ (stopAtRelaxer_not_relaxedOn hall hq hσ)
    · simp at h

/-- **Soundness alone admits degenerate policies.**  The policy that always
refuses and the policy that always returns no locals are sound; the latter is
not exact. -/
theorem policySound_degenerate :
    PolicySound (fun _ _ => none) ∧ PolicySound (fun _ _ => some []) ∧
    ¬ PolicyExact (fun _ _ => some []) := by
  refine ⟨fun _ _ _ h => by simp at h, fun _ _ _ h => ?_, fun h => ?_⟩
  · simp only [Option.some.injEq] at h
    subst h
    intro P _ q σ hmem; simp at hmem
  · have := (h .scalar [[]] [] rfl).1
    simp [fieldTy] at this

/-- `(ManuallyDrop<&mut T>, u8)`: a pair whose first field is a relaxing
wrapper. -/
def tyPairMD (s : Shape) : Ty := .pair (.wrap .manuallyDrop (mutRefTy s .scalar)) .scalar

/-- `ManuallyDrop<u8>`: a relaxing wrapper around a scalar. -/
def tyMDScalar : Ty := .wrap .manuallyDrop .scalar

/-- **Acceptance hierarchy of the repair policies.**  Whenever the exclusion
policy scalarizes, the stop-at-relaxer policy returns the same locals; whenever
the stop-at-relaxer policy scalarizes, the retyping policy returns the same
locals.  Both inclusions are strict: for `tyPairMD s1` with paths
`[[.fst], [.snd]]` the exclusion policy refuses while the stop-at-relaxer
policy scalarizes, and for `tyMDPair s1` with `qsMDPair` the stop-at-relaxer
policy refuses while the retyping policy scalarizes.  The stop-at-relaxer
policy also refuses `tyMDScalar` with paths `[[.inner]]` although that
scalarization with declared types is a refinement. -/
theorem repair_policies_acceptance_hierarchy :
    (∀ τ qs locals, repairExclude τ qs = some locals → repairStopAtRelaxer τ qs = some locals) ∧
    (∀ τ qs locals, repairStopAtRelaxer τ qs = some locals → repairRetype τ qs = some locals) ∧
    repairExclude (tyPairMD s1) [[.fst], [.snd]] = none ∧
    (repairStopAtRelaxer (tyPairMD s1) [[.fst], [.snd]]).isSome = true ∧
    repairStopAtRelaxer (tyMDPair s1) qsMDPair = none ∧
    (repairRetype (tyMDPair s1) qsMDPair).isSome = true ∧
    repairStopAtRelaxer tyMDScalar [[.inner]] = none ∧
    Refines tyMDScalar (scalarize tyMDScalar [[.inner]]) := by
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · intro τ qs locals h
    simp only [repairExclude] at h
    cases hc : containsRelaxer τ
    · rw [hc] at h; simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      have hno := fun q => relaxedOn_eq_false_of_containsRelaxer τ q hc
      simp [repairStopAtRelaxer, hno]
    · rw [hc] at h; simp at h
  · intro τ qs locals h
    simp only [repairStopAtRelaxer] at h
    split at h
    · rename_i hall
      simp only [Option.some.injEq] at h
      subst h
      simp only [repairRetype, scalarize, Option.some.injEq]
      induction qs with
      | nil => rfl
      | cons q qs ih =>
        simp only [List.all_cons, Bool.and_eq_true] at hall
        simp only [List.filterMap_cons, ih hall.2]
        cases hf : fieldTy τ q with
        | none => rfl
        | some σ =>
          have hr : relaxedOn τ q = false := by simpa [hf] using hall.1
          simp [retype, hr]
    · simp at h
  · rw [scalarize_refines_iff_declared_le_posMod]
    intro q hq σ hσ p' s m hm
    simp at hq; subst hq
    simp [tyMDScalar, fieldTy] at hσ; subst hσ
    cases p' <;> simp [modAt, comp] at hm

end Toy.Modality
