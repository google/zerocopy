/-
Imported module (not a result of this package).

Copied from the published corpus package `enum-niche-layout-guarantees-and-validity-invariants`
(repository `google/zerocopy`, branch `reference`, published at commit
`00c8f874bf1e70c933b7a2ea2572a76c1baa7327`; Lean sources unchanged at the latest correction
commit `f9bee82a6d3f8bb6698b4c9e716138018db94d4d`), file
`reports/enum-niche-layout-guarantees-and-validity-invariants/lean/Toy/Niche/Counting.lean`,
whose SHA-256 at both commits is
`ef8273526a1df77512aca86f330684938898314d9d3d48a1fc1f3b935af2001f`.
The only edits are the namespace (`Toy.Niche` renamed to `Toy.WrapNiche.Imported`) and this
header. Declaration names, statements and proofs are otherwise verbatim.
-/

import Toy.WrapNiche.Imported.Lemmas

/-!
# Counting lemmas (fully proved)

Finite-list counting facts used by the pigeonhole results: a duplicate-free list contained
in another is no longer than it; a duplicate-free list at least as long as a list containing
it covers it; the valid and invalid patterns of a payload partition all `256 ^ n` patterns;
and the list of a payload's values is duplicate-free with as many entries as valid patterns.
-/

namespace Toy.WrapNiche.Imported.Counting

open Toy.WrapNiche.Imported

theorem nodup_map_of_injOn {α β : Type} {f : α → β} {l : List α}
    (hf : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) (h : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (fun x hx y hy =>
      hf x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy)) h.2⟩
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨b, hb, hba⟩ := hmem
    have heq := hf b (List.mem_cons_of_mem a hb) a (List.mem_cons_self ..) hba
    exact h.1 (heq ▸ hb)

theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] {l₁ l₂ : List α}
    (hnd : l₁.Nodup) (hsub : ∀ x ∈ l₁, x ∈ l₂) : l₁.length ≤ l₂.length := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    have ha : a ∈ l₂ := hsub a (List.mem_cons_self ..)
    have hsub' : ∀ x ∈ t, x ∈ l₂.erase a := by
      intro x hx
      have hne : x ≠ a := fun h => hnd.1 (h ▸ hx)
      exact (List.mem_erase_of_ne hne).mpr (hsub x (List.mem_cons_of_mem a hx))
    have hle := ih hnd.2 hsub'
    have hlen : (l₂.erase a).length + 1 = l₂.length := by
      rw [List.length_erase_of_mem ha]
      have hpos : 0 < l₂.length := List.length_pos_of_mem ha
      omega
    simp only [List.length_cons]
    omega

theorem mem_of_nodup_of_length_ge {α : Type} [DecidableEq α] {l₁ l₂ : List α}
    (hnd₁ : l₁.Nodup) (hsub : ∀ x ∈ l₁, x ∈ l₂) (hlen : l₂.length ≤ l₁.length) :
    ∀ x ∈ l₂, x ∈ l₁ := by
  intro x hx
  exact Classical.byContradiction fun hnx => by
    have hsub' : ∀ y ∈ l₁, y ∈ l₂.erase x := by
      intro y hy
      have hne : y ≠ x := fun h => hnx (h ▸ hy)
      exact (List.mem_erase_of_ne hne).mpr (hsub y hy)
    have hle := nodup_length_le_of_subset hnd₁ hsub'
    have hpos : 0 < l₂.length := List.length_pos_of_mem hx
    rw [List.length_erase_of_mem hx] at hle
    omega

/-- The valid and the invalid patterns of `V` together account for all `256 ^ n` patterns. -/
theorem numValid_add_numInvalid {n : Nat} (V : Validity n) :
    ((List.finRange (256 ^ n)).filter (fun p => V p)).length + numInvalid V = 256 ^ n := by
  unfold numInvalid invalidPats
  have h : ∀ l : List (Pat n),
      (l.filter (fun p => V p)).length + (l.filter (fun p => !V p)).length = l.length := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih => cases hv : V a <;> simp [hv] <;> omega
  simpa using h (List.finRange (256 ^ n))

/-- The values of `V`, listed in increasing order of their patterns. -/
def valList {n : Nat} (V : Validity n) : List (Val V) :=
  ((List.finRange (256 ^ n)).filter (fun p => V p)).pmap (fun p hp => ⟨p, hp⟩)
    (fun _ hp => (List.mem_filter.mp hp).2)

theorem valList_length {n : Nat} (V : Validity n) :
    (valList V).length = ((List.finRange (256 ^ n)).filter (fun p => V p)).length := by
  simp [valList]

theorem valList_nodup {n : Nat} (V : Validity n) : (valList V).Nodup := by
  have hnd : ((List.finRange (256 ^ n)).filter (fun p => V p)).Nodup :=
    List.Pairwise.filter _ (List.nodup_finRange _)
  have hmap : ∀ (l : List (Pat n)) (hl : ∀ p ∈ l, V p = true),
      (l.pmap (fun p hp => (⟨p, hp⟩ : Val V)) hl).map Subtype.val = l := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a t ih =>
      intro hl
      simp only [List.pmap, List.map_cons, ih (fun p hp => hl p (List.mem_cons_of_mem a hp))]
  have aux : ∀ {l : List (Val V)}, (l.map Subtype.val).Nodup → l.Nodup := by
    intro l hl
    induction l with
    | nil => simp
    | cons a t ih =>
      rw [List.map_cons, List.nodup_cons] at hl
      rw [List.nodup_cons]
      exact ⟨fun hm => hl.1 (List.mem_map_of_mem hm), ih hl.2⟩
  exact aux ((hmap _ _).symm ▸ hnd)

end Toy.WrapNiche.Imported.Counting
