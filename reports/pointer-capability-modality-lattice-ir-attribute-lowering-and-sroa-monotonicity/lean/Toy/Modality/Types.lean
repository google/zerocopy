/-
Toy.Modality.Types
==================

A toy type language and the bottom-up computation of the modality of every
pointer leaf, parameterized by the transformer used for relaxing
wrappers and by whether that transformer is propagated to every nested
pointer leaf (`deep`) or only to a pointer that is the wrapper's immediate
content (shallow).  The reference semantics `req` is defined top-down: a
pointer leaf must satisfy its base modality, weakened by `tRelax` if any
enclosing wrapper on its path is relaxing.

No enums or unions are part of this type language (enums with a niche are
treated at a single pointer leaf in `Toy.Modality.Niche`).  A pointer leaf
`ptr s m` erases its pointee type: the computation follows by-value nesting
(pairs and wrappers), never a pointer indirection.
-/
import Toy.Modality.Transformers

namespace Toy.Modality

/-! ## Types -/

/-- Single-field value-level wrappers.  `maybeDangling` and `manuallyDrop` are
relaxing; `transparent` (a newtype struct), `unsafeCell` and `unsafePinned` are
the identity on the modalities of the pointers they contain by value. -/
inductive Wrap
  | maybeDangling
  | manuallyDrop
  | transparent
  | unsafeCell
  | unsafePinned
  deriving DecidableEq, Repr

/-- Whether a wrapper relaxes the pointers it contains. -/
def Wrap.relaxes : Wrap → Bool
  | .maybeDangling => true
  | .manuallyDrop => true
  | _ => false

/-- Toy types.  `ptr s m` is a pointer leaf whose pointee has shape `s` and
whose type promises base modality `m` (the documented pointer types are the
smart constructors `refTy`, `mutRefTy`, `boxTy`, `rawTy`); `pair` models
transparent structs and tuples (n-ary products as nested pairs); `wrap` models
single-field wrappers. -/
inductive Ty
  | scalar
  | ptr (s : Shape) (m : Mod)
  | pair (a b : Ty)
  | wrap (w : Wrap) (τ : Ty)

/-- Field-projection steps: first or second component of a pair, or the
content of a wrapper. -/
inductive Step
  | fst
  | snd
  | inner
  deriving DecidableEq, Repr

/-- A path of field projections from the root of a type. -/
abbrev Path := List Step

/-- The type is a pointer leaf. -/
def Ty.isPtr : Ty → Bool
  | .ptr _ _ => true
  | _ => false

/-- Toy `Freeze`: no `UnsafeCell` by value (pointers are `Freeze` whatever their
pointee). -/
def Ty.freeze : Ty → Bool
  | .scalar => true
  | .ptr _ _ => true
  | .pair a b => a.freeze && b.freeze
  | .wrap .unsafeCell _ => false
  | .wrap _ τ => τ.freeze

/-- Toy `Unpin` (standing for the conjunction of `Unpin` and the unsafe-unpin
predicate): no `UnsafePinned` by value (pointers are `Unpin`). -/
def Ty.unpin : Ty → Bool
  | .scalar => true
  | .ptr _ _ => true
  | .pair a b => a.unpin && b.unpin
  | .wrap .unsafePinned _ => false
  | .wrap _ τ => τ.unpin

/-- `&T` with pointee `T` of shape `s`. -/
def refTy (s : Shape) (T : Ty) : Ty := .ptr s (kindBase (.shared T.freeze))

/-- `&mut T` with pointee `T` of shape `s`. -/
def mutRefTy (s : Shape) (T : Ty) : Ty := .ptr s (kindBase (.mutRef T.unpin))

/-- `Box<T>` with pointee `T` of shape `s`. -/
def boxTy (s : Shape) (T : Ty) : Ty := .ptr s (kindBase (.box T.unpin))

/-- A raw pointer (no promise: base modality `Mod.bot`). -/
def rawTy (s : Shape) : Ty := .ptr s (kindBase .raw)

/-! ## Leaves, bottom-up computation, top-down reference semantics -/

/-- The pointer leaf at path `p`: its pointee shape and base modality. -/
def leafAt : Ty → Path → Option (Shape × Mod)
  | .ptr s m, [] => some (s, m)
  | .pair a _, .fst :: p => leafAt a p
  | .pair _ b, .snd :: p => leafAt b p
  | .wrap _ τ, .inner :: p => leafAt τ p
  | _, _ => none

/-- Whether some wrapper strictly above the end of path `p` is relaxing. -/
def relaxedOn : Ty → Path → Bool
  | .pair a _, .fst :: p => relaxedOn a p
  | .pair _ b, .snd :: p => relaxedOn b p
  | .wrap w τ, .inner :: p => w.relaxes || relaxedOn τ p
  | _, _ => false

/-- Bottom-up modality computation with relaxing transformer `T`.  With
`deep = true` the transformer of a relaxing wrapper is applied to every pointer
leaf below it; with `deep = false` only when the wrapper's content is itself a
pointer.  Non-relaxing wrappers and pairs are the identity. -/
def comp (T : Mod → Mod) (deep : Bool) : Ty → Path → Option (Shape × Mod)
  | .ptr s m, [] => some (s, m)
  | .pair a _, .fst :: p => comp T deep a p
  | .pair _ b, .snd :: p => comp T deep b p
  | .wrap w τ, .inner :: p =>
      (comp T deep τ p).map fun sm =>
        (sm.1, if w.relaxes && (deep || τ.isPtr) then T sm.2 else sm.2)
  | _, _ => none

/-- Top-down reference semantics, with flag `r` = "a relaxing wrapper has been
passed": the leaf must satisfy its base modality, weakened by `tRelax` if `r`. -/
def reqAux : Bool → Ty → Path → Option (Shape × Mod)
  | r, .ptr s m, [] => some (s, if r then tRelax m else m)
  | r, .pair a _, .fst :: p => reqAux r a p
  | r, .pair _ b, .snd :: p => reqAux r b p
  | r, .wrap w τ, .inner :: p => reqAux (r || w.relaxes) τ p
  | _, _, _ => none

/-- The reference requirement on the pointer leaf at path `p` of `τ`. -/
def req (τ : Ty) (p : Path) : Option (Shape × Mod) := reqAux false τ p

/-- A relaxing transformer `T` is sound: for every shape and base modality `m`,
every trace permitted by the reference requirement `tRelax m` satisfies `T m`. -/
def TransformerSound (T : Mod → Mod) : Prop :=
  ∀ (s : Shape) (m : Mod) (t : Trace), den s (tRelax m) t → den s (T m) t

/-- The computation `comp T deep` is sound: at every pointer leaf, every trace
permitted by the reference requirement satisfies the computed modality. -/
def CompSound (T : Mod → Mod) (deep : Bool) : Prop :=
  ∀ (τ : Ty) (p : Path) (s : Shape) (m m₀ : Mod),
    comp T deep τ p = some (s, m) → req τ p = some (s, m₀) → ∀ t, den s m₀ t → den s m t

/-! ## Helper lemmas -/

theorem reqAux_eq (r : Bool) (τ : Ty) (p : Path) :
    reqAux r τ p = (leafAt τ p).map
      (fun x => (x.1, if r || relaxedOn τ p then tRelax x.2 else x.2)) := by
  induction τ generalizing r p with
  | scalar => cases p <;> simp [reqAux, leafAt]
  | ptr s m =>
    cases p with
    | nil => cases r <;> simp [reqAux, leafAt, relaxedOn]
    | cons st p => simp [reqAux, leafAt]
  | pair a b iha ihb =>
    cases p with
    | nil => simp [reqAux, leafAt]
    | cons st p =>
      cases st
      · simp [reqAux, leafAt, relaxedOn, iha]
      · simp [reqAux, leafAt, relaxedOn, ihb]
      · simp [reqAux, leafAt]
  | wrap w τ ih =>
    cases p with
    | nil => simp [reqAux, leafAt]
    | cons st p =>
      cases st
      · simp [reqAux, leafAt]
      · simp [reqAux, leafAt]
      · simp only [reqAux, leafAt, relaxedOn, ih, Bool.or_assoc]
        rfl

theorem comp_eq_some_leaf (T : Mod → Mod) (deep : Bool) (τ : Ty) (p : Path) (s : Shape)
    (c : Mod) (h : comp T deep τ p = some (s, c)) : ∃ b, leafAt τ p = some (s, b) := by
  induction τ generalizing p c with
  | scalar => cases p <;> simp [comp] at h
  | ptr s' m =>
    cases p with
    | nil => simp [comp] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨m, rfl⟩
    | cons st p => simp [comp] at h
  | pair a b iha ihb =>
    cases p with
    | nil => simp [comp] at h
    | cons st p =>
      cases st
      · exact iha p c (by simpa [comp] using h)
      · exact ihb p c (by simpa [comp] using h)
      · simp [comp] at h
  | wrap w τ ih =>
    cases p with
    | nil => simp [comp] at h
    | cons st p =>
      cases st
      · simp [comp] at h
      · simp [comp] at h
      · simp only [comp, Option.map_eq_some_iff] at h
        obtain ⟨⟨s', c'⟩, hc, he⟩ := h
        simp at he
        obtain ⟨rfl, -⟩ := he
        exact ih p c' hc

/-- Invariant of the deep computation with a sound transformer. -/
theorem comp_deep_inv (T : Mod → Mod) (hT : TransformerSound T) (τ : Ty) (p : Path)
    (s : Shape) (c b : Mod) (hc : comp T true τ p = some (s, c))
    (hb : leafAt τ p = some (s, b)) :
    (relaxedOn τ p = false → c = b) ∧
    (relaxedOn τ p = true → ∀ t, den s (tRelax b) t → den s c t) := by
  induction τ generalizing p c with
  | scalar => cases p <;> simp [comp] at hc
  | ptr s' m =>
    cases p with
    | nil =>
      simp [comp] at hc; simp [leafAt] at hb
      obtain ⟨rfl, rfl⟩ := hc; obtain ⟨-, rfl⟩ := hb
      simp [relaxedOn]
    | cons st p => simp [comp] at hc
  | pair a b' iha ihb =>
    cases p with
    | nil => simp [comp] at hc
    | cons st p =>
      cases st
      · simp only [comp, leafAt, relaxedOn] at hc hb ⊢; exact iha p c hc hb
      · simp only [comp, leafAt, relaxedOn] at hc hb ⊢; exact ihb p c hc hb
      · simp [comp] at hc
  | wrap w τ ih =>
    cases p with
    | nil => simp [comp] at hc
    | cons st p =>
      cases st
      · simp [comp] at hc
      · simp [comp] at hc
      · simp only [comp, Option.map_eq_some_iff] at hc
        obtain ⟨⟨s', c'⟩, hc', he⟩ := hc
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        simp only [leafAt] at hb
        have ⟨i1, i2⟩ := ih p c' hc' hb
        simp only [relaxedOn, Bool.true_or, Bool.and_true]
        cases hw : w.relaxes
        · simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
          exact ⟨i1, i2⟩
        · simp only [Bool.true_or, Bool.true_eq_false, false_implies, ↓reduceIte, forall_const,
            true_and]
          intro t ht
          apply hT _ c' t
          cases hr : relaxedOn τ p
          · rw [i1 hr]; exact ht
          · exact (den_transformer_of_den s' c' t (i2 hr t ht)).1

/-- A concrete one-byte, alignment-1 shape used by counterexamples. -/
def s1 : Shape := ⟨1, 0, by decide⟩

/-- A two-byte, two-aligned pointee shape (`u16`-like). -/
def s2 : Shape := ⟨2, 1, by decide⟩

/-- The type `MaybeDangling<(Wrapper(&mut T), u8)>` with `T` a scalar of shape
`s` (`Wrapper` a transparent newtype). -/
def tyNestedMD (s : Shape) : Ty :=
  .wrap .maybeDangling (.pair (.wrap .transparent (mutRefTy s .scalar)) .scalar)

/-- Path of the nested `&mut T` leaf in `tyNestedMD s`. -/
def pathNestedMD : Path := [.inner, .fst, .inner]

theorem den_tRelax_tDangling (s : Shape) (m : Mod) : den s (tRelax m) (tDangling s) :=
  (relaxRule_iff_den s m _).1 ⟨fun _ => atomSat_tDangling s _ (Or.inl rfl),
    fun _ => atomSat_tDangling s _ (Or.inr (Or.inl rfl))⟩

theorem den_tRelax_tForeignRead (s : Shape) (m : Mod) : den s (tRelax m) (tForeignRead s) :=
  (relaxRule_iff_den s m _).1 ⟨fun _ => atomSat_tForeignRead s _ (by decide),
    fun _ => atomSat_tForeignRead s _ (by decide)⟩

theorem tRelax_tRelax (m : Mod) : tRelax (tRelax m) = tRelax m :=
  (transformers_deflationary_closed s1).2.2 m

/-- Transformer soundness is the syntactic inequality `T m ≤ tRelax m` for
every `m`. -/
theorem transformerSound_iff_le_tRelax (T : Mod → Mod) :
    TransformerSound T ↔ ∀ m, T m ≤ tRelax m := by
  constructor
  · intro h m
    have hcl := (den_subset_iff_le_cl s2 (tRelax m) (T m)).1 (h s2 m)
    have hfix : cl s2 (tRelax m) = tRelax m := by
      apply Mod.ext_has; intro a; cases a <;> simp [cl, s2, tRelax, clDeref, Mod.has, Mod.bot]
    rwa [hfix] at hcl
  · intro h s m t ht
    exact den_antitone s (h m) t ht

/-! ## Results -/

/-- **Shallow relaxing leaves promises on nested pointers** (counterexample).
For every shape `s`, in `tyNestedMD s` (`MaybeDangling<(Wrapper(&mut T), u8)>`),
the shallow computation with any relaxing transformer `T` (in particular the
documented `tRelax`) gives the nested `&mut T` leaf the full modality `mutFull`
(with `derefEntry` and `unique`), while the reference requirement is `tRelax mutFull`; the dangling
trace `tDangling s` and the foreign-read trace `tForeignRead s` satisfy the
requirement and violate `derefEntry`, respectively `unique`. -/
theorem shallow_relaxer_leaves_nested_promises (s : Shape) :
    (∀ T : Mod → Mod, comp T false (tyNestedMD s) pathNestedMD = some (s, mutFull)) ∧
    req (tyNestedMD s) pathNestedMD = some (s, tRelax mutFull) ∧
    mutFull.derefEntry = true ∧ mutFull.unique = true ∧
    den s (tRelax mutFull) (tDangling s) ∧ ¬ atomSat s .derefEntry (tDangling s) ∧
    den s (tRelax mutFull) (tForeignRead s) ∧ ¬ atomSat s .unique (tForeignRead s) := by
  refine ⟨fun _ => rfl, rfl, rfl, rfl, den_tRelax_tDangling s _,
    not_dereferenceable_of_live_nil s _ rfl, den_tRelax_tForeignRead s _,
    not_atomSat_tForeignRead_unique s⟩

/-- **Compositional computation: sound iff the transformer is sound and
propagated deeply.**  For every relaxing transformer `T : Mod → Mod` and flag
`deep`, the bottom-up computation `comp T deep` is sound against the
reference semantics `req` at every pointer leaf of every type (pointer leaves
`Ty.ptr s m` of every shape and modality included) iff `T` is sound
(`TransformerSound T`) and `deep = true`. -/
theorem compSound_iff_transformerSound_and_deep (T : Mod → Mod) (deep : Bool) :
    CompSound T deep ↔ TransformerSound T ∧ deep = true := by
  constructor
  · intro h
    refine ⟨fun s m t ht => ?_, ?_⟩
    · have hc : comp T deep (.wrap .maybeDangling (.ptr s m)) [.inner] = some (s, T m) := by
        simp [comp, Wrap.relaxes, Ty.isPtr]
      have hr : req (.wrap .maybeDangling (.ptr s m)) [.inner] = some (s, tRelax m) := by
        simp [req, reqAux, Wrap.relaxes]
      exact h _ _ _ _ _ hc hr t ht
    · cases deep
      · exfalso
        obtain ⟨hc, hr, -, -, hd, hnd, -⟩ := shallow_relaxer_leaves_nested_promises s1
        exact hnd ((h _ _ _ _ _ (hc T) hr _ hd) .derefEntry rfl)
      · rfl
  · rintro ⟨hT, rfl⟩ τ p s m m₀ hc hr t ht
    obtain ⟨b, hb⟩ := comp_eq_some_leaf T true τ p s m hc
    have ⟨i1, i2⟩ := comp_deep_inv T hT τ p s m b hc hb
    simp only [req, reqAux_eq, hb, Option.map_some, Bool.false_or, Option.some.injEq,
      Prod.mk.injEq, true_and] at hr
    cases hrel : relaxedOn τ p
    · rw [hrel] at hr; simp at hr; subst hr; rw [i1 hrel]; exact ht
    · rw [hrel] at hr; simp at hr; subst hr; exact i2 hrel t ht

theorem comp_tRelax_deep_eq_leaf (τ : Ty) (p : Path) :
    comp tRelax true τ p = (leafAt τ p).map
      (fun x => (x.1, if relaxedOn τ p then tRelax x.2 else x.2)) := by
  induction τ generalizing p with
  | scalar => cases p <;> simp [comp, leafAt]
  | ptr s m =>
    cases p with
    | nil => simp [comp, leafAt, relaxedOn]
    | cons st p => simp [comp, leafAt]
  | pair a b iha ihb =>
    cases p with
    | nil => simp [comp, leafAt]
    | cons st p =>
      cases st
      · simp only [comp, leafAt, relaxedOn]; exact iha p
      · simp only [comp, leafAt, relaxedOn]; exact ihb p
      · simp [comp, leafAt]
  | wrap w τ ih =>
    cases p with
    | nil => simp [comp, leafAt]
    | cons st p =>
      cases st
      · simp [comp, leafAt]
      · simp [comp, leafAt]
      · simp only [comp, leafAt, relaxedOn, ih p, Option.map_map]
        cases leafAt τ p with
        | none => simp
        | some x =>
          by_cases hr : relaxedOn τ p = true <;>
            cases w <;> simp [hr, Wrap.relaxes, tRelax_tRelax]

/-- **The documented deep computation is exact.**  For every type `τ` and path
`p`, `comp tRelax true τ p = req τ p`. -/
theorem comp_tRelax_deep_eq_req (τ : Ty) (p : Path) : comp tRelax true τ p = req τ p := by
  rw [req, reqAux_eq, comp_tRelax_deep_eq_leaf]
  simp

/-! ## Documented constructors only -/

/-- Types built from scalars, pairs, wrappers and the four documented pointer
constructors `refTy`, `mutRefTy`, `boxTy`, `rawTy` (no other pointer leaf). -/
inductive DocTy : Ty → Prop
  | scalar : DocTy .scalar
  | ref (s : Shape) {T : Ty} : DocTy T → DocTy (refTy s T)
  | mutRef (s : Shape) {T : Ty} : DocTy T → DocTy (mutRefTy s T)
  | box (s : Shape) {T : Ty} : DocTy T → DocTy (boxTy s T)
  | raw (s : Shape) : DocTy (rawTy s)
  | pair {a b : Ty} : DocTy a → DocTy b → DocTy (.pair a b)
  | wrap (w : Wrap) {τ : Ty} : DocTy τ → DocTy (.wrap w τ)

theorem DocTy.leaf_kindBase {τ : Ty} (h : DocTy τ) :
    ∀ p s m, leafAt τ p = some (s, m) → ∃ k, m = kindBase k := by
  induction h with
  | scalar => intro p _ _ hl; cases p <;> simp [leafAt] at hl
  | ref s _ =>
    intro p _ _ hl; cases p <;> simp [refTy, leafAt] at hl
    exact ⟨.shared _, hl.2.symm⟩
  | mutRef s _ =>
    intro p _ _ hl; cases p <;> simp [mutRefTy, leafAt] at hl
    exact ⟨.mutRef _, hl.2.symm⟩
  | box s _ =>
    intro p _ _ hl; cases p <;> simp [boxTy, leafAt] at hl
    exact ⟨.box _, hl.2.symm⟩
  | raw s =>
    intro p _ _ hl; cases p <;> simp [rawTy, leafAt] at hl
    exact ⟨.raw, hl.2.symm⟩
  | pair _ _ iha ihb =>
    intro p s m hl; cases p with
    | nil => simp [leafAt] at hl
    | cons st p => cases st <;> simp [leafAt] at hl
                   · exact iha p s m hl
                   · exact ihb p s m hl
  | wrap w _ ih =>
    intro p s m hl; cases p with
    | nil => simp [leafAt] at hl
    | cons st p => cases st <;> simp [leafAt] at hl; exact ih p s m hl

/-- The modality with the single atom `frozen` (the base modality of no
documented pointer constructor). -/
def modFrozenOnly : Mod := ⟨false, false, false, false, true, false, false⟩

/-- A relaxing transformer that agrees with `tRelax` except at `modFrozenOnly`,
which it maps to `Mod.top`. -/
def tRelaxExceptFrozenOnly (m : Mod) : Mod := if m == modFrozenOnly then Mod.top else tRelax m

/-- **Restricted to the documented constructors, sound deep computation does
not imply a sound transformer** (counterexample).  With
`T = tRelaxExceptFrozenOnly`, the deep computation `comp T true` is sound
against `req` at every pointer leaf of every type built by `DocTy`, while
`TransformerSound T` fails. -/
theorem compSound_on_docTy_not_imply_transformerSound :
    (∀ τ, DocTy τ → ∀ p s m m₀, comp tRelaxExceptFrozenOnly true τ p = some (s, m) →
      req τ p = some (s, m₀) → ∀ t, den s m₀ t → den s m t) ∧
    ¬ TransformerSound tRelaxExceptFrozenOnly := by
  have hcomp_eq : ∀ τ, DocTy τ → ∀ p,
      comp tRelaxExceptFrozenOnly true τ p = comp tRelax true τ p := by
    intro τ hτ p
    induction hτ generalizing p with
    | scalar => cases p <;> rfl
    | ref _ _ => cases p <;> rfl
    | mutRef _ _ => cases p <;> rfl
    | box _ _ => cases p <;> rfl
    | raw _ => cases p <;> rfl
    | pair _ _ iha ihb =>
      cases p with
      | nil => rfl
      | cons st p => cases st <;> simp [comp, iha, ihb]
    | wrap w hinner ih =>
      cases p with
      | nil => rfl
      | cons st p =>
        cases st
        · rfl
        · rfl
        · simp only [comp, ih p, comp_tRelax_deep_eq_leaf, Option.map_map]
          cases hl : leafAt _ p with
          | none => rfl
          | some sm =>
            obtain ⟨k, hk⟩ := hinner.leaf_kindBase p sm.1 sm.2 hl
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and,
              Function.comp, hk]
            cases hw : w.relaxes
            · simp
            · simp only [Bool.true_or, Bool.true_and, ↓reduceIte]
              cases hr : relaxedOn _ p <;>
                cases k with
                | shared f => cases f <;> decide
                | mutRef u => cases u <;> decide
                | box u => cases u <;> decide
                | raw => decide
  refine ⟨?_, ?_⟩
  · intro τ hτ p s m m₀ hc hr t ht
    rw [hcomp_eq τ hτ p, comp_tRelax_deep_eq_req, hr] at hc
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hc
    subst hc
    exact ht
  · intro h
    have hle := (transformerSound_iff_le_tRelax tRelaxExceptFrozenOnly).1 h modFrozenOnly
      .frozen (by decide)
    simp [tRelax, modFrozenOnly, Mod.has, Mod.bot] at hle

end Toy.Modality
