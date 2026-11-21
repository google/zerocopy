/-
Toy.Modality.Transformers
=========================

Per-constructor transformers on modalities, the documented rules they
abstract, and their soundness and optimality.

* `tRelax` (`MaybeDangling` / `ManuallyDrop`): keep `aligned` and `nonnull`
  (including `nonnull` implied by a deref atom), drop every other atom.
* `tCell` (`UnsafeCell` in the pointee of a shared reference): drop `frozen`,
  `derefWhole`, `unique`.
* `tPin` (mutable reference to a type that is not `Unpin`): drop `unique`,
  `derefWhole`.
* `tBox` (`Box`): drop `derefWhole`.
* transparent structs and tuples: identity on the field at the pointer's
  position.

Every transformer first adds the atoms implied by `derefWhole ⇒ derefEntry ⇒
nonnull` (`clDeref`), so dropping an atom keeps what it implied and the
transformers respect semantic equivalence (`transformers_respect_den`).

The rules (`kindRule`, `relaxRule`) are trace predicates that transcribe the
documented language-level guarantees in terms of the atom meanings; the
transformers compute modalities.  Because the rules are transcriptions, both
soundness and optimality of the transformers follow from the order embedding
`den_subset_iff_le_cl`; no independent operational semantics is involved.
-/
import Toy.Modality.Lattice

namespace Toy.Modality

/-! ## Transformers -/

/-- Shape-independent part of the implication closure:
`derefWhole ⇒ derefEntry ⇒ nonnull`. -/
def clDeref (m : Mod) : Mod :=
  { m with
    nonnull := m.nonnull || m.derefEntry || m.derefWhole
    derefEntry := m.derefEntry || m.derefWhole }

/-- Relaxing wrapper (`MaybeDangling`, `ManuallyDrop`): keep `aligned` and
`nonnull` (after `clDeref`), drop the rest (including `bounded`). -/
def tRelax (m : Mod) : Mod :=
  { Mod.bot with aligned := m.aligned, nonnull := (clDeref m).nonnull }

/-- `UnsafeCell` in the pointee of a shared reference: drop `frozen`,
`derefWhole` and `unique` (after `clDeref`). -/
def tCell (m : Mod) : Mod := { clDeref m with frozen := false, derefWhole := false, unique := false }

/-- Mutable reference to a pointee that is not `Unpin`: drop `unique` and
`derefWhole` (after `clDeref`). -/
def tPin (m : Mod) : Mod := { clDeref m with unique := false, derefWhole := false }

/-- `Box`: drop `derefWhole` (after `clDeref`; the box may be freed during the
call). -/
def tBox (m : Mod) : Mod := { clDeref m with derefWhole := false }

/-- Shared reference to a `Freeze` pointee: aligned, non-null, live for the
whole call, frozen, bounded.  (Shared references never carry `unique`.) -/
def refFull : Mod := ⟨true, true, true, true, true, false, true⟩

/-- Mutable reference to an `Unpin` pointee: aligned, non-null, live for the
whole call, unique, bounded.  (Not `frozen`: the reference may write.) -/
def mutFull : Mod := ⟨true, true, true, true, false, true, true⟩

/-- Pointer kinds of the toy language, with the pointee predicate that
matters for each: `Freeze` for shared references, `Unpin` for mutable
references and boxes. -/
inductive PtrKind
  | shared (freeze : Bool)
  | mutRef (unpin : Bool)
  | box (unpin : Bool)
  | raw
  deriving DecidableEq, Repr

/-- Base modality of each pointer kind, computed with the transformers. -/
def kindBase : PtrKind → Mod
  | .shared true => refFull
  | .shared false => tCell refFull
  | .mutRef true => mutFull
  | .mutRef false => tPin mutFull
  | .box true => tBox mutFull
  | .box false => tBox (tPin mutFull)
  | .raw => Mod.bot

/-! ## Documented rules as trace predicates -/

/-- The toy's transcription of the requirement on a pointer of each kind, for
the duration of a call, as a trace predicate.  "Bounded" means that accesses
through the pointer stay inside the pointee bytes (`ArgInRange`).
* shared reference to a `Freeze` pointee: aligned, non-null, live at entry,
  not freed during the call, not written during the call, bounded;
* shared reference to a non-`Freeze` pointee: aligned, non-null, live at
  entry, bounded (writes and deallocation during the call are permitted);
* mutable reference to an `Unpin` pointee: aligned, non-null, live at entry,
  not freed, no access through unrelated pointers, bounded;
* mutable reference to a non-`Unpin` pointee: aligned, non-null, live at
  entry, bounded;
* `Box` of an `Unpin` pointee: aligned, non-null, live at entry, no access
  through unrelated pointers, bounded (deallocation permitted);
* `Box` of a non-`Unpin` pointee: aligned, non-null, live at entry, bounded;
* raw pointer: no requirement (every trace). -/
def kindRule (s : Shape) : PtrKind → Trace → Prop
  | .shared true, t => atomSat s .aligned t ∧ atomSat s .nonnull t ∧
      Dereferenceable s t ∧ NotFreedDuring t ∧ atomSat s .frozen t ∧ ArgInRange s t
  | .shared false, t => atomSat s .aligned t ∧ atomSat s .nonnull t ∧
      Dereferenceable s t ∧ ArgInRange s t
  | .mutRef true, t => atomSat s .aligned t ∧ atomSat s .nonnull t ∧
      Dereferenceable s t ∧ NotFreedDuring t ∧ atomSat s .unique t ∧ ArgInRange s t
  | .mutRef false, t => atomSat s .aligned t ∧ atomSat s .nonnull t ∧
      Dereferenceable s t ∧ ArgInRange s t
  | .box true, t => atomSat s .aligned t ∧ atomSat s .nonnull t ∧
      Dereferenceable s t ∧ atomSat s .unique t ∧ ArgInRange s t
  | .box false, t => atomSat s .aligned t ∧ atomSat s .nonnull t ∧
      Dereferenceable s t ∧ ArgInRange s t
  | .raw, _ => True

/-- The toy's transcription of the requirement on a pointer of base modality
`m` inside a relaxing wrapper: the by-value part survives, i.e. alignment and
non-nullness if `m` promises them (semantically: if they are in the closure
`cl s m`). -/
def relaxRule (s : Shape) (m : Mod) (t : Trace) : Prop :=
  ((cl s m).aligned = true → atomSat s .aligned t) ∧
    ((cl s m).nonnull = true → atomSat s .nonnull t)

/-! ## Helper equivalences -/

theorem kindRule_iff_den (s : Shape) (k : PtrKind) (t : Trace) :
    kindRule s k t ↔ den s (kindBase k) t := by
  rw [den_iff]
  cases k with
  | shared f => cases f <;>
      simp [kindRule, kindBase, refFull, tCell, clDeref, atomSat] <;> intros <;> simp_all
  | mutRef u => cases u <;>
      simp [kindRule, kindBase, mutFull, tPin, clDeref, atomSat] <;> intros <;> simp_all
  | box u => cases u <;>
      simp [kindRule, kindBase, mutFull, tPin, tBox, clDeref, atomSat] <;> intros <;> simp_all
  | raw => simp [kindRule, kindBase, Mod.bot]

theorem relaxRule_iff_den (s : Shape) (m : Mod) (t : Trace) :
    relaxRule s m t ↔ den s (tRelax m) t := by
  rw [den_iff]
  simp only [relaxRule, tRelax, clDeref, cl, Mod.bot, Bool.or_eq_true, beq_iff_eq,
    Bool.false_eq_true, false_implies, and_true]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (Or.inl h), fun h => h2 h⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rintro (h | h)
    · exact h1 h
    · exact mod_align_of_alignLog_eq_zero h _

/-- Each transformer, applied after closing, gives the same closure as applied
directly. -/
theorem cl_transformer_cl (s : Shape) (m : Mod) :
    cl s (tRelax (cl s m)) = cl s (tRelax m) ∧ cl s (tCell (cl s m)) = cl s (tCell m) ∧
    cl s (tPin (cl s m)) = cl s (tPin m) ∧ cl s (tBox (cl s m)) = cl s (tBox m) := by
  cases m with
  | mk a b c d e f g =>
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp [cl, tRelax, tCell, tPin, tBox, clDeref, Mod.bot]

/-! ## Results -/

/-- **Transformers respect semantic equivalence.**  For every shape `s` and
modalities `m₁ m₂` with `⟦m₁⟧ = ⟦m₂⟧`, each of `tRelax`, `tCell`, `tPin`,
`tBox` gives modalities with equal semantics. -/
theorem transformers_respect_den (s : Shape) (m₁ m₂ : Mod)
    (h : ∀ t, den s m₁ t ↔ den s m₂ t) :
    (∀ t, den s (tRelax m₁) t ↔ den s (tRelax m₂) t) ∧
    (∀ t, den s (tCell m₁) t ↔ den s (tCell m₂) t) ∧
    (∀ t, den s (tPin m₁) t ↔ den s (tPin m₂) t) ∧
    (∀ t, den s (tBox m₁) t ↔ den s (tBox m₂) t) := by
  have hc := cl_eq_of_den_iff s h
  have h1 := cl_transformer_cl s m₁
  have h2 := cl_transformer_cl s m₂
  have key : ∀ (T : Mod → Mod), cl s (T (cl s m₁)) = cl s (T m₁) →
      cl s (T (cl s m₂)) = cl s (T m₂) → ∀ t, den s (T m₁) t ↔ den s (T m₂) t := by
    intro T e1 e2 t
    rw [← den_cl_iff s (T m₁), ← den_cl_iff s (T m₂), ← e1, ← e2, hc]
  exact ⟨key _ h1.1 h2.1, key _ h1.2.1 h2.2.1, key _ h1.2.2.1 h2.2.2.1, key _ h1.2.2.2 h2.2.2.2⟩

/-- **Base modalities are the best abstraction of the transcribed rules.**  For
every shape `s`, pointer kind `k` and modality `m'`: every trace permitted by
`kindRule s k` satisfies `m'` iff `m' ≤ cl s (kindBase k)`.  In particular
(taking `m' = kindBase k`) the transformer-computed base modality is sound, and
any atom outside its closure fails on some rule-permitted trace. -/
theorem kindBase_best (s : Shape) (k : PtrKind) (m' : Mod) :
    (∀ t, kindRule s k t → den s m' t) ↔ m' ≤ cl s (kindBase k) := by
  rw [← den_subset_iff_le_cl]
  exact ⟨fun h t ht => h t ((kindRule_iff_den s k t).2 ht),
    fun h t ht => h t ((kindRule_iff_den s k t).1 ht)⟩

/-- **The relaxing transformer is the best abstraction of the relaxing rule.**
For every shape `s` and modalities `m m'`: every trace permitted by
`relaxRule s m` satisfies `m'` iff `m' ≤ cl s (tRelax m)`. -/
theorem tRelax_best (s : Shape) (m m' : Mod) :
    (∀ t, relaxRule s m t → den s m' t) ↔ m' ≤ cl s (tRelax m) := by
  rw [← den_subset_iff_le_cl]
  exact ⟨fun h t ht => h t ((relaxRule_iff_den s m t).2 ht),
    fun h t ht => h t ((relaxRule_iff_den s m t).1 ht)⟩

/-- **Every atom a transformer drops can fail.**  For every shape `s`, explicit
rule-permitted traces violate each atom that a transformer removes from the
modality it is applied to: inside a relaxing wrapper a former `refFull`
pointer may dangle (failing `derefEntry` and `derefWhole`), its pointee may be
written (failing `frozen`) and it may be used outside the pointee (failing
`bounded`), and a former `mutFull` pointer may be accessed through an
unrelated pointer (failing `unique`); for a shared reference to a non-`Freeze`
pointee (`tCell refFull`) the pointee may be written (failing `frozen`) and
freed (failing `derefWhole`); for a mutable reference to a non-`Unpin` pointee
(`tPin mutFull`) the pointee may be read through an unrelated pointer (failing
`unique`) and freed (failing `derefWhole`); a `Box` of an `Unpin` pointee
(`tBox mutFull`) may be freed (failing `derefWhole`); a `Box` of a non-`Unpin`
pointee (`tBox (tPin mutFull)`) may be read through an unrelated pointer
(failing `unique`) and freed (failing `derefWhole`). -/
theorem transformer_dropped_atoms_can_fail (s : Shape) :
    (relaxRule s refFull (tDangling s) ∧ ¬ atomSat s .derefEntry (tDangling s) ∧
      ¬ atomSat s .derefWhole (tDangling s)) ∧
    (relaxRule s refFull (tArgWrite s) ∧ ¬ atomSat s .frozen (tArgWrite s)) ∧
    (relaxRule s refFull (tOutOfRange s) ∧ ¬ atomSat s .bounded (tOutOfRange s)) ∧
    (relaxRule s mutFull (tForeignRead s) ∧ ¬ atomSat s .unique (tForeignRead s)) ∧
    (kindRule s (.shared false) (tArgWrite s) ∧ ¬ atomSat s .frozen (tArgWrite s)) ∧
    (kindRule s (.shared false) (tFreed s) ∧ ¬ atomSat s .derefWhole (tFreed s)) ∧
    (kindRule s (.mutRef false) (tForeignRead s) ∧ ¬ atomSat s .unique (tForeignRead s)) ∧
    (kindRule s (.mutRef false) (tFreed s) ∧ ¬ atomSat s .derefWhole (tFreed s)) ∧
    (kindRule s (.box true) (tFreed s) ∧ ¬ atomSat s .derefWhole (tFreed s)) ∧
    (kindRule s (.box false) (tForeignRead s) ∧ ¬ atomSat s .unique (tForeignRead s)) ∧
    (kindRule s (.box false) (tFreed s) ∧ ¬ atomSat s .derefWhole (tFreed s)) := by
  have hDang : ¬ Dereferenceable s (tDangling s) := not_dereferenceable_of_live_nil s _ rfl
  have rel : ∀ m t, atomSat s .aligned t → atomSat s .nonnull t → relaxRule s m t :=
    fun m t ha hn => ⟨fun _ => ha, fun _ => hn⟩
  have hFreedRule : ∀ k, (k = .shared false ∨ k = .mutRef false ∨ k = .box false) →
      kindRule s k (tFreed s) := by
    intro k hk
    have h1 := atomSat_tFreed s .aligned (by decide)
    have h2 := atomSat_tFreed s .nonnull (by decide)
    have h3 := atomSat_tFreed s .derefEntry (by decide)
    have h7 := atomSat_tFreed s .bounded (by decide)
    rcases hk with rfl | rfl | rfl
    · exact ⟨h1, h2, h3, h7⟩
    · exact ⟨h1, h2, h3, h7⟩
    · exact ⟨h1, h2, h3, h7⟩
  have hFR : ∀ k, (k = .mutRef false ∨ k = .box false) → kindRule s k (tForeignRead s) := by
    intro k hk
    have h1 := atomSat_tForeignRead s .aligned (by decide)
    have h2 := atomSat_tForeignRead s .nonnull (by decide)
    have h3 := atomSat_tForeignRead s .derefEntry (by decide)
    have h7 := atomSat_tForeignRead s .bounded (by decide)
    rcases hk with rfl | rfl
    · exact ⟨h1, h2, h3, h7⟩
    · exact ⟨h1, h2, h3, h7⟩
  have hNF : ¬ atomSat s .derefWhole (tFreed s) := fun h => not_notFreedDuring_tFreed s h.2
  refine ⟨⟨rel _ _ (atomSat_tDangling s _ (Or.inl rfl))
      (atomSat_tDangling s _ (Or.inr (Or.inl rfl))), hDang, fun h => hDang h.1⟩,
    ⟨rel _ _ (atomSat_tArgWrite s _ (by decide)) (atomSat_tArgWrite s _ (by decide)),
      not_atomSat_tArgWrite_frozen s⟩,
    ⟨rel _ _ (atomSat_tOutOfRange s _ (by decide)) (atomSat_tOutOfRange s _ (by decide)),
      not_atomSat_tOutOfRange_bounded s⟩,
    ⟨rel _ _ (atomSat_tForeignRead s _ (by decide)) (atomSat_tForeignRead s _ (by decide)),
      not_atomSat_tForeignRead_unique s⟩,
    ⟨⟨atomSat_tArgWrite s _ (by decide), atomSat_tArgWrite s _ (by decide),
      atomSat_tArgWrite s .derefEntry (by decide), atomSat_tArgWrite s .bounded (by decide)⟩,
      not_atomSat_tArgWrite_frozen s⟩,
    ⟨hFreedRule _ (Or.inl rfl), hNF⟩,
    ⟨hFR _ (Or.inl rfl), not_atomSat_tForeignRead_unique s⟩,
    ⟨hFreedRule _ (Or.inr (Or.inl rfl)), hNF⟩,
    ⟨⟨atomSat_tFreed s _ (by decide), atomSat_tFreed s _ (by decide),
      atomSat_tFreed s .derefEntry (by decide), atomSat_tFreed s .unique (by decide),
      atomSat_tFreed s .bounded (by decide)⟩, hNF⟩,
    ⟨hFR _ (Or.inr rfl), not_atomSat_tForeignRead_unique s⟩,
    ⟨hFreedRule _ (Or.inr (Or.inr rfl)), hNF⟩⟩

/-- **Transformers only weaken and preserve closedness.**  For every shape `s`:
each of `tRelax`, `tCell`, `tPin`, `tBox` maps every modality `m` to a modality
`≤ cl s m` (so `⟦m⟧ ⊆ ⟦T m⟧`), maps closed modalities to closed modalities, and
`tRelax` is idempotent. -/
theorem transformers_deflationary_closed (s : Shape) :
    (∀ m, tRelax m ≤ cl s m ∧ tCell m ≤ cl s m ∧ tPin m ≤ cl s m ∧ tBox m ≤ cl s m) ∧
    (∀ m, Closed s m → Closed s (tRelax m) ∧ Closed s (tCell m) ∧ Closed s (tPin m) ∧
      Closed s (tBox m)) ∧
    (∀ m, tRelax (tRelax m) = tRelax m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro a h <;> cases a <;>
      simp_all [Mod.has, tRelax, tCell, tPin, tBox, clDeref, cl, Mod.bot]
  · intro m h
    rw [closed_iff] at h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [closed_iff] <;>
      simp_all [tRelax, tCell, tPin, tBox, clDeref, Mod.bot] <;>
      rintro (h | h) <;> simp [h]
  · intro m
    cases m with
    | mk a b c d e f g => simp [tRelax, clDeref, Mod.bot]

/-- Semantic weakening: every trace of `⟦m⟧` is a trace of `⟦T m⟧` for each
transformer `T`. -/
theorem den_transformer_of_den (s : Shape) (m : Mod) (t : Trace) (h : den s m t) :
    den s (tRelax m) t ∧ den s (tCell m) t ∧ den s (tPin m) t ∧ den s (tBox m) t := by
  have hc := (den_cl_iff s m t).2 h
  have hd := (transformers_deflationary_closed s).1 m
  exact ⟨den_antitone s hd.1 t hc, den_antitone s hd.2.1 t hc, den_antitone s hd.2.2.1 t hc,
    den_antitone s hd.2.2.2 t hc⟩

end Toy.Modality
