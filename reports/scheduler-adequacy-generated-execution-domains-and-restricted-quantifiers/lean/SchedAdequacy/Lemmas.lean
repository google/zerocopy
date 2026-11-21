import SchedAdequacy.Basic
import SchedAdequacy.Traces
import SchedAdequacy.Bounded

/-!
# Supporting lemmas for the operational semantics

Membership lemmas for `shuffle` and `Interleavings`, one-step soundness and
completeness lemmas for `stepPerNode` and `stepShared`, and the oracle-consumption
bounds used by the main results. Everything here is fully proved.
-/

namespace Toy.SchedAdequacy

open Prog

variable {α : Type}

/-! ## `shuffle` -/

theorem shuffle_nil_left (ys : List α) : shuffle [] ys = [ys] := rfl

theorem shuffle_cons_nil (x : α) (xs : List α) :
    shuffle (x :: xs) [] = (shuffle xs []).map (x :: ·) := rfl

theorem shuffle_cons_cons (x y : α) (xs ys : List α) :
    shuffle (x :: xs) (y :: ys) =
      (shuffle xs (y :: ys)).map (x :: ·) ++ (shuffle (x :: xs) ys).map (y :: ·) := rfl

theorem shuffle_nil_right : ∀ xs : List α, shuffle xs [] = [xs]
  | [] => rfl
  | x :: xs => by rw [shuffle_cons_nil, shuffle_nil_right xs]; rfl

theorem mem_shuffle_cons_left {x : α} {xs ys zs : List α} (h : zs ∈ shuffle xs ys) :
    x :: zs ∈ shuffle (x :: xs) ys := by
  cases ys with
  | nil => rw [shuffle_cons_nil]; exact List.mem_map.mpr ⟨_, h, rfl⟩
  | cons y ys =>
      rw [shuffle_cons_cons]; exact List.mem_append_left _ (List.mem_map.mpr ⟨_, h, rfl⟩)

theorem mem_shuffle_cons_right {y : α} {xs ys zs : List α} (h : zs ∈ shuffle xs ys) :
    y :: zs ∈ shuffle xs (y :: ys) := by
  cases xs with
  | nil =>
      rw [shuffle_nil_left] at h ⊢
      rw [List.mem_singleton] at h
      subst h; exact List.mem_singleton_self _
  | cons x xs =>
      rw [shuffle_cons_cons]; exact List.mem_append_right _ (List.mem_map.mpr ⟨_, h, rfl⟩)

theorem nil_mem_shuffle {xs ys : List α} (h : [] ∈ shuffle xs ys) : xs = [] ∧ ys = [] := by
  cases xs with
  | nil =>
      rw [shuffle_nil_left, List.mem_singleton] at h; exact ⟨rfl, h.symm⟩
  | cons x xs =>
      cases ys with
      | nil => rw [shuffle_cons_nil] at h; simp at h
      | cons y ys => rw [shuffle_cons_cons] at h; simp at h

theorem cons_mem_shuffle {z : α} {zs xs ys : List α} (h : z :: zs ∈ shuffle xs ys) :
    (∃ xs', xs = z :: xs' ∧ zs ∈ shuffle xs' ys) ∨
      (∃ ys', ys = z :: ys' ∧ zs ∈ shuffle xs ys') := by
  cases xs with
  | nil =>
      rw [shuffle_nil_left, List.mem_singleton] at h
      exact Or.inr ⟨zs, h.symm, List.mem_singleton_self _⟩
  | cons x xs =>
      cases ys with
      | nil =>
          rw [shuffle_cons_nil] at h
          obtain ⟨w, hw, he⟩ := List.mem_map.mp h
          obtain ⟨rfl, rfl⟩ := List.cons.inj he
          exact Or.inl ⟨xs, rfl, hw⟩
      | cons y ys =>
          rw [shuffle_cons_cons, List.mem_append] at h
          rcases h with h | h
          · obtain ⟨w, hw, he⟩ := List.mem_map.mp h
            obtain ⟨rfl, rfl⟩ := List.cons.inj he
            exact Or.inl ⟨xs, rfl, hw⟩
          · obtain ⟨w, hw, he⟩ := List.mem_map.mp h
            obtain ⟨rfl, rfl⟩ := List.cons.inj he
            exact Or.inr ⟨ys, rfl, hw⟩

theorem perm_of_mem_shuffle : ∀ {zs xs ys : List α}, zs ∈ shuffle xs ys → zs.Perm (xs ++ ys)
  | [], _, _, h => by
      obtain ⟨rfl, rfl⟩ := nil_mem_shuffle h; exact List.Perm.refl _
  | z :: _, _, _, h => by
      rcases cons_mem_shuffle h with ⟨xs', rfl, h'⟩ | ⟨ys', rfl, h'⟩
      · exact (perm_of_mem_shuffle h').cons z
      · exact ((perm_of_mem_shuffle h').cons z).trans List.perm_middle.symm

theorem append_mem_shuffle : ∀ xs ys : List α, xs ++ ys ∈ shuffle xs ys
  | [], ys => List.mem_singleton_self ys
  | _ :: xs, ys => mem_shuffle_cons_left (append_mem_shuffle xs ys)

/-! ## `Interleavings` -/

theorem mem_interleavings_act {x : α} {t : List α} :
    t ∈ Interleavings (.act x) ↔ t = [x] := by
  simp [Interleavings]

theorem mem_interleavings_seq {p q : Prog α} {u : List α} :
    u ∈ Interleavings (.seq p q) ↔
      ∃ s ∈ Interleavings p, ∃ t ∈ Interleavings q, u = s ++ t := by
  simp only [Interleavings, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩; exact ⟨s, hs, t, ht, rfl⟩
  · rintro ⟨s, hs, t, ht, rfl⟩; exact ⟨s, hs, t, ht, rfl⟩

theorem mem_interleavings_par {p q : Prog α} {u : List α} :
    u ∈ Interleavings (.par p q) ↔
      ∃ s ∈ Interleavings p, ∃ t ∈ Interleavings q, u ∈ shuffle s t := by
  simp only [Interleavings, List.mem_flatMap]

theorem actions_length : ∀ p : Prog α, p.actions.length = p.size
  | .act _ => rfl
  | .seq p q => by simp [actions, size, actions_length p, actions_length q]
  | .par p q => by simp [actions, size, actions_length p, actions_length q]

theorem size_pos : ∀ p : Prog α, 0 < p.size
  | .act _ => Nat.one_pos
  | .seq p _ => Nat.lt_of_lt_of_le (size_pos p) (Nat.le_add_right _ _)
  | .par p _ => Nat.lt_of_lt_of_le (size_pos p) (Nat.le_add_right _ _)

/-- Every interleaving of `p` is a permutation of the actions of `p`. -/
theorem perm_actions_of_mem_interleavings :
    ∀ {p : Prog α} {t : List α}, t ∈ Interleavings p → t.Perm p.actions
  | .act _, _, h => by rw [mem_interleavings_act.mp h]; exact List.Perm.refl _
  | .seq p q, _, h => by
      obtain ⟨s, hs, t, ht, rfl⟩ := mem_interleavings_seq.mp h
      exact (perm_actions_of_mem_interleavings hs).append (perm_actions_of_mem_interleavings ht)
  | .par p q, _, h => by
      obtain ⟨s, hs, t, ht, hu⟩ := mem_interleavings_par.mp h
      exact (perm_of_mem_shuffle hu).trans
        ((perm_actions_of_mem_interleavings hs).append (perm_actions_of_mem_interleavings ht))

theorem length_of_mem_interleavings {p : Prog α} {t : List α} (h : t ∈ Interleavings p) :
    t.length = p.size :=
  (perm_actions_of_mem_interleavings h).length_eq.trans (actions_length p)

theorem interleavings_nonempty : ∀ p : Prog α, ∃ t, t ∈ Interleavings p
  | .act x => ⟨[x], mem_interleavings_act.mpr rfl⟩
  | .seq p q => by
      obtain ⟨s, hs⟩ := interleavings_nonempty p
      obtain ⟨t, ht⟩ := interleavings_nonempty q
      exact ⟨s ++ t, mem_interleavings_seq.mpr ⟨s, hs, t, ht, rfl⟩⟩
  | .par p q => by
      obtain ⟨s, hs⟩ := interleavings_nonempty p
      obtain ⟨t, ht⟩ := interleavings_nonempty q
      exact ⟨s ++ t, mem_interleavings_par.mpr ⟨s, hs, t, ht, append_mem_shuffle s t⟩⟩

/-! ## One step of the per-step semantics -/

/-- What one step must satisfy: a final step (`none`) means the program was the
single action performed; otherwise the residual is one action smaller and
prefixing the action to any of its interleavings gives an interleaving of the
original program. -/
def StepOK (p : Prog α) (x : α) : Option (Prog α) → Prop
  | none => p = .act x
  | some p' => p.size = p'.size + 1 ∧ ∀ s ∈ Interleavings p', x :: s ∈ Interleavings p

theorem stepOK_seq {p q : Prog α} {x : α} {r : Option (Prog α)} (h : StepOK p x r) :
    StepOK (.seq p q) x (some (match r with | none => q | some p' => .seq p' q)) := by
  cases r with
  | none =>
      cases h
      refine ⟨by simp only [size] <;> omega, fun s hs => ?_⟩
      exact mem_interleavings_seq.mpr ⟨[x], mem_interleavings_act.mpr rfl, s, hs, rfl⟩
  | some p' =>
      obtain ⟨hsz, hmem⟩ := h
      refine ⟨by simp only [size] <;> omega, fun s hs => ?_⟩
      obtain ⟨s₁, hs₁, t, ht, rfl⟩ := mem_interleavings_seq.mp hs
      exact mem_interleavings_seq.mpr ⟨x :: s₁, hmem s₁ hs₁, t, ht, rfl⟩

theorem stepOK_par_left {p q : Prog α} {x : α} {r : Option (Prog α)} (h : StepOK p x r) :
    StepOK (.par p q) x (some (match r with | none => q | some p' => .par p' q)) := by
  cases r with
  | none =>
      cases h
      refine ⟨by simp only [size] <;> omega, fun s hs => ?_⟩
      exact mem_interleavings_par.mpr ⟨[x], mem_interleavings_act.mpr rfl, s, hs,
        mem_shuffle_cons_left (List.mem_singleton_self s)⟩
  | some p' =>
      obtain ⟨hsz, hmem⟩ := h
      refine ⟨by simp only [size] <;> omega, fun s hs => ?_⟩
      obtain ⟨s₁, hs₁, t, ht, hu⟩ := mem_interleavings_par.mp hs
      exact mem_interleavings_par.mpr ⟨x :: s₁, hmem s₁ hs₁, t, ht, mem_shuffle_cons_left hu⟩

theorem stepOK_par_right {p q : Prog α} {x : α} {r : Option (Prog α)} (h : StepOK q x r) :
    StepOK (.par p q) x (some (match r with | none => p | some q' => .par p q')) := by
  cases r with
  | none =>
      cases h
      refine ⟨by simp only [size] <;> omega, fun s hs => ?_⟩
      refine mem_interleavings_par.mpr ⟨s, hs, [x], mem_interleavings_act.mpr rfl, ?_⟩
      apply mem_shuffle_cons_right
      rw [shuffle_nil_right]; exact List.mem_singleton_self s
  | some q' =>
      obtain ⟨hsz, hmem⟩ := h
      refine ⟨by simp only [size] <;> omega, fun s hs => ?_⟩
      obtain ⟨s₁, hs₁, t, ht, hu⟩ := mem_interleavings_par.mp hs
      exact mem_interleavings_par.mpr ⟨s₁, hs₁, x :: t, hmem t ht, mem_shuffle_cons_right hu⟩

theorem stepPerNode_ok : ∀ (p : Prog α) (o : Oracle),
    StepOK p (stepPerNode p o).1 (stepPerNode p o).2.1
  | .act _, _ => rfl
  | .seq p q, o => by
      have hp := stepPerNode_ok p o
      simp only [stepPerNode]
      rcases h : stepPerNode p o with ⟨x, _ | p', o'⟩ <;> rw [h] at hp
      · exact stepOK_seq (q := q) hp
      · exact stepOK_seq (q := q) hp
  | .par p q, o => by
      simp only [stepPerNode]
      split
      · have hq := stepPerNode_ok q o.tail
        rcases h : stepPerNode q o.tail with ⟨x, _ | q', o'⟩ <;> rw [h] at hq
        · exact stepOK_par_right (p := p) hq
        · exact stepOK_par_right (p := p) hq
      · have hp := stepPerNode_ok p o.tail
        rcases h : stepPerNode p o.tail with ⟨x, _ | p', o'⟩ <;> rw [h] at hp
        · exact stepOK_par_left (q := q) hp
        · exact stepOK_par_left (q := q) hp

theorem runPerStepAux_mem : ∀ (n : Nat) (p : Prog α) (o : Oracle), p.size = n →
    runPerStepAux n o p ∈ Interleavings p
  | 0, p, _, h => absurd h (Nat.ne_of_gt (size_pos p))
  | n + 1, p, o, h => by
      have hok := stepPerNode_ok p o
      simp only [runPerStepAux]
      rcases hs : stepPerNode p o with ⟨x, _ | p', o'⟩ <;> rw [hs] at hok
      · cases hok; exact mem_interleavings_act.mpr rfl
      · obtain ⟨hsz, hmem⟩ := hok
        exact hmem _ (runPerStepAux_mem n p' o' (by omega))

/-- What the rest of a trace must satisfy after a step with result `r`. -/
def RestOK (s : List α) : Option (Prog α) → Prop
  | none => s = []
  | some p' => s ∈ Interleavings p'

theorem stepPerNode_complete : ∀ (p : Prog α) (x : α) (s : List α), x :: s ∈ Interleavings p →
    ∃ (o₁ : Oracle) (r : Option (Prog α)),
      ∀ o₂ : Oracle, stepPerNode p (o₁ ++ o₂) = (x, r, o₂) ∧ RestOK s r
  | .act y, x, s, h => by
      obtain ⟨rfl, rfl⟩ := List.cons.inj (mem_interleavings_act.mp h)
      exact ⟨[], none, fun o₂ => ⟨rfl, rfl⟩⟩
  | .seq p q, x, s, h => by
      obtain ⟨s₁, hs₁, t, ht, he⟩ := mem_interleavings_seq.mp h
      cases s₁ with
      | nil =>
          have := length_of_mem_interleavings hs₁
          have := size_pos p
          simp at *; omega
      | cons y s₁' =>
          obtain ⟨rfl, rfl⟩ := List.cons.inj he
          obtain ⟨o₁, r₁, ho⟩ := stepPerNode_complete p x s₁' hs₁
          refine ⟨o₁, some (match r₁ with | none => q | some p' => .seq p' q), fun o₂ => ?_⟩
          obtain ⟨hst, hrest⟩ := ho o₂
          refine ⟨by simp only [stepPerNode, hst]; cases r₁ <;> rfl, ?_⟩
          cases r₁ with
          | none => cases hrest; exact ht
          | some p' => exact mem_interleavings_seq.mpr ⟨s₁', hrest, t, ht, rfl⟩
  | .par p q, x, s, h => by
      obtain ⟨s₁, hs₁, t, ht, hu⟩ := mem_interleavings_par.mp h
      rcases cons_mem_shuffle hu with ⟨s₁', rfl, hu'⟩ | ⟨t', rfl, hu'⟩
      · obtain ⟨o₁, r₁, ho⟩ := stepPerNode_complete p x s₁' hs₁
        refine ⟨false :: o₁, some (match r₁ with | none => q | some p' => .par p' q), fun o₂ => ?_⟩
        obtain ⟨hst, hrest⟩ := ho o₂
        refine ⟨by simp only [List.cons_append, stepPerNode, List.headD_cons, List.tail_cons, hst,
          Bool.false_eq_true, ite_false]; cases r₁ <;> rfl, ?_⟩
        cases r₁ with
        | none =>
            cases hrest
            rw [shuffle_nil_left, List.mem_singleton] at hu'
            subst hu'; exact ht
        | some p' => exact mem_interleavings_par.mpr ⟨s₁', hrest, t, ht, hu'⟩
      · obtain ⟨o₁, r₁, ho⟩ := stepPerNode_complete q x t' ht
        refine ⟨true :: o₁, some (match r₁ with | none => p | some q' => .par p q'), fun o₂ => ?_⟩
        obtain ⟨hst, hrest⟩ := ho o₂
        refine ⟨by simp only [List.cons_append, stepPerNode, List.headD_cons, List.tail_cons, hst,
          ite_true]; cases r₁ <;> rfl, ?_⟩
        cases r₁ with
        | none =>
            cases hrest
            rw [shuffle_nil_right, List.mem_singleton] at hu'
            subst hu'; exact hs₁
        | some q' => exact mem_interleavings_par.mpr ⟨s₁, hs₁, t', hrest, hu'⟩

theorem runPerStepAux_complete : ∀ (n : Nat) (p : Prog α), p.size = n →
    ∀ t ∈ Interleavings p, ∃ o, runPerStepAux n o p = t
  | 0, p, h, _, _ => absurd h (Nat.ne_of_gt (size_pos p))
  | n + 1, p, h, t, ht => by
      cases t with
      | nil =>
          have := length_of_mem_interleavings ht
          have := size_pos p
          simp at *; omega
      | cons x s =>
          obtain ⟨o₁, r, ho⟩ := stepPerNode_complete p x s ht
          cases r with
          | none =>
              obtain ⟨hst, hrest⟩ := ho []
              cases hrest
              exact ⟨o₁ ++ [], by simp only [runPerStepAux, hst]⟩
          | some p' =>
              have hok := stepPerNode_ok p (o₁ ++ [])
              rw [(ho []).1] at hok
              obtain ⟨hsz, _⟩ := hok
              obtain ⟨o', ho'⟩ := runPerStepAux_complete n p' (by omega) s (ho []).2
              exact ⟨o₁ ++ o', by simp only [runPerStepAux, (ho o').1, ho']⟩

/-! ## One step of the shared-choice semantics -/

theorem stepShared_ok : ∀ (p : Prog α) (b : Bool), StepOK p (stepShared p b).1 (stepShared p b).2
  | .act _, _ => rfl
  | .seq p q, b => by
      have hp := stepShared_ok p b
      simp only [stepShared]
      rcases h : stepShared p b with ⟨x, _ | p'⟩ <;> rw [h] at hp
      · exact stepOK_seq (q := q) hp
      · exact stepOK_seq (q := q) hp
  | .par p q, b => by
      simp only [stepShared]
      split
      · have hq := stepShared_ok q b
        rcases h : stepShared q b with ⟨x, _ | q'⟩ <;> rw [h] at hq
        · exact stepOK_par_right (p := p) hq
        · exact stepOK_par_right (p := p) hq
      · have hp := stepShared_ok p b
        rcases h : stepShared p b with ⟨x, _ | p'⟩ <;> rw [h] at hp
        · exact stepOK_par_left (q := q) hp
        · exact stepOK_par_left (q := q) hp

/-- The bit and remaining oracle used by one step of `runSharedAux`. -/
def sharedBit (p : Prog α) (o : Oracle) : Bool × Oracle :=
  if needsChoice p then (o.headD false, o.tail) else (false, o)

theorem runSharedAux_succ (n : Nat) (o : Oracle) (p : Prog α) :
    runSharedAux (n + 1) o p =
      match stepShared p (sharedBit p o).1 with
      | (x, none) => [x]
      | (x, some p') => x :: runSharedAux n (sharedBit p o).2 p' := rfl

theorem runSharedAux_mem : ∀ (n : Nat) (p : Prog α) (o : Oracle), p.size = n →
    runSharedAux n o p ∈ Interleavings p
  | 0, p, _, h => absurd h (Nat.ne_of_gt (size_pos p))
  | n + 1, p, o, h => by
      have hok := stepShared_ok p (sharedBit p o).1
      rw [runSharedAux_succ]
      rcases hs : stepShared p (sharedBit p o).1 with ⟨x, _ | p'⟩ <;> rw [hs] at hok
      · cases hok; exact mem_interleavings_act.mpr rfl
      · obtain ⟨hsz, hmem⟩ := hok
        exact hmem _ (runSharedAux_mem n p' _ (by omega))

/-! ## Shared-choice completeness without nested parallel composition -/

theorem noNestedPar_of_hasPar_false : ∀ {p : Prog α}, p.hasPar = false → NoNestedPar p
  | .act _, _ => trivial
  | .seq _ _, h => by
      simp only [hasPar, Bool.or_eq_false_iff] at h
      exact ⟨noNestedPar_of_hasPar_false h.1, noNestedPar_of_hasPar_false h.2⟩
  | .par _ _, h => by simp [hasPar] at h

/-- On a program without parallel composition the shared step is the unique
step, whatever the bit. -/
theorem stepShared_complete_parFree : ∀ (p : Prog α), p.hasPar = false →
    ∀ (x : α) (s : List α), x :: s ∈ Interleavings p → ∀ b : Bool,
      ∃ r, stepShared p b = (x, r) ∧ RestOK s r ∧
        (∀ p', r = some p' → p'.hasPar = false)
  | .act y, _, x, s, h, b => by
      obtain ⟨rfl, rfl⟩ := List.cons.inj (mem_interleavings_act.mp h)
      exact ⟨none, rfl, rfl, fun _ h => nomatch h⟩
  | .seq p q, hpar, x, s, h, b => by
      simp only [hasPar, Bool.or_eq_false_iff] at hpar
      obtain ⟨s₁, hs₁, t, ht, he⟩ := mem_interleavings_seq.mp h
      cases s₁ with
      | nil =>
          have := length_of_mem_interleavings hs₁
          have := size_pos p
          simp at *; omega
      | cons y s₁' =>
          obtain ⟨rfl, rfl⟩ := List.cons.inj he
          obtain ⟨r₁, hst, hrest, hpf⟩ := stepShared_complete_parFree p hpar.1 x s₁' hs₁ b
          refine ⟨some (match r₁ with | none => q | some p' => .seq p' q),
            by simp only [stepShared, hst]; cases r₁ <;> rfl, ?_, ?_⟩
          · cases r₁ with
            | none => cases hrest; exact ht
            | some p' => exact mem_interleavings_seq.mpr ⟨s₁', hrest, t, ht, rfl⟩
          · intro p' hp'
            cases r₁ with
            | none => cases hp'; exact hpar.2
            | some p'' =>
                cases hp'
                simp [hasPar, hpf p'' rfl, hpar.2]
  | .par _ _, hpar, _, _, _, _ => by simp [hasPar] at hpar

theorem stepShared_complete_noNestedPar : ∀ (p : Prog α), NoNestedPar p →
    ∀ (x : α) (s : List α), x :: s ∈ Interleavings p →
      ∃ b r, stepShared p b = (x, r) ∧ RestOK s r ∧ (∀ p', r = some p' → NoNestedPar p')
  | .act y, _, x, s, h => by
      obtain ⟨rfl, rfl⟩ := List.cons.inj (mem_interleavings_act.mp h)
      exact ⟨false, none, rfl, rfl, fun _ h => nomatch h⟩
  | .seq p q, hn, x, s, h => by
      obtain ⟨s₁, hs₁, t, ht, he⟩ := mem_interleavings_seq.mp h
      cases s₁ with
      | nil =>
          have := length_of_mem_interleavings hs₁
          have := size_pos p
          simp at *; omega
      | cons y s₁' =>
          obtain ⟨rfl, rfl⟩ := List.cons.inj he
          obtain ⟨b, r₁, hst, hrest, hnn⟩ := stepShared_complete_noNestedPar p hn.1 x s₁' hs₁
          refine ⟨b, some (match r₁ with | none => q | some p' => .seq p' q),
            by simp only [stepShared, hst]; cases r₁ <;> rfl, ?_, ?_⟩
          · cases r₁ with
            | none => cases hrest; exact ht
            | some p' => exact mem_interleavings_seq.mpr ⟨s₁', hrest, t, ht, rfl⟩
          · intro p' hp'
            cases r₁ with
            | none => cases hp'; exact hn.2
            | some p'' => cases hp'; exact ⟨hnn p'' rfl, hn.2⟩
  | .par p q, hn, x, s, h => by
      obtain ⟨hp, hq⟩ := hn
      obtain ⟨s₁, hs₁, t, ht, hu⟩ := mem_interleavings_par.mp h
      rcases cons_mem_shuffle hu with ⟨s₁', rfl, hu'⟩ | ⟨t', rfl, hu'⟩
      · obtain ⟨r₁, hst, hrest, hpf⟩ := stepShared_complete_parFree p hp x s₁' hs₁ false
        refine ⟨false, some (match r₁ with | none => q | some p' => .par p' q),
          by simp only [stepShared, hst, Bool.false_eq_true, ite_false]; cases r₁ <;> rfl, ?_, ?_⟩
        · cases r₁ with
          | none =>
              cases hrest
              rw [shuffle_nil_left, List.mem_singleton] at hu'
              subst hu'; exact ht
          | some p' => exact mem_interleavings_par.mpr ⟨s₁', hrest, t, ht, hu'⟩
        · intro p' hp'
          cases r₁ with
          | none => cases hp'; exact noNestedPar_of_hasPar_false hq
          | some p'' => cases hp'; exact ⟨hpf p'' rfl, hq⟩
      · obtain ⟨r₁, hst, hrest, hpf⟩ := stepShared_complete_parFree q hq x t' ht true
        refine ⟨true, some (match r₁ with | none => p | some q' => .par p q'),
          by simp only [stepShared, hst, ite_true]; cases r₁ <;> rfl, ?_, ?_⟩
        · cases r₁ with
          | none =>
              cases hrest
              rw [shuffle_nil_right, List.mem_singleton] at hu'
              subst hu'; exact hs₁
          | some q' => exact mem_interleavings_par.mpr ⟨s₁, hs₁, t', hrest, hu'⟩
        · intro p' hp'
          cases r₁ with
          | none => cases hp'; exact noNestedPar_of_hasPar_false hp
          | some q'' => cases hp'; exact ⟨hp, hpf q'' rfl⟩

/-- A step that crosses no parallel composition does not look at its bit. -/
theorem stepShared_eq_of_needsChoice_false : ∀ (p : Prog α), needsChoice p = false →
    ∀ b, stepShared p b = stepShared p false
  | .act _, _, _ => rfl
  | .seq p _, h, b => by
      simp only [needsChoice] at h
      simp only [stepShared, stepShared_eq_of_needsChoice_false p h b]
  | .par _ _, h, _ => by simp [needsChoice] at h

theorem runSharedAux_complete_noNestedPar : ∀ (n : Nat) (p : Prog α), p.size = n →
    NoNestedPar p → ∀ t ∈ Interleavings p, ∃ o, runSharedAux n o p = t
  | 0, p, h, _, _, _ => absurd h (Nat.ne_of_gt (size_pos p))
  | n + 1, p, h, hn, t, ht => by
      cases t with
      | nil =>
          have := length_of_mem_interleavings ht
          have := size_pos p
          simp at *; omega
      | cons x s =>
          obtain ⟨b, r, hst, hrest, hnn⟩ := stepShared_complete_noNestedPar p hn x s ht
          -- an oracle whose first used bit is `b` (if a bit is used at all), followed by `o'`
          have key : ∀ o' : Oracle, ∃ o, stepShared p (sharedBit p o).1 = (x, r) ∧
              (sharedBit p o).2 = o' := by
            intro o'
            cases hc : needsChoice p
            · refine ⟨o', ?_, by simp [sharedBit, hc]⟩
              simp only [sharedBit, hc, Bool.false_eq_true, ite_false]
              rw [← stepShared_eq_of_needsChoice_false p hc b]; exact hst
            · exact ⟨b :: o', by simpa [sharedBit, hc] using hst, by simp [sharedBit, hc]⟩
          cases r with
          | none =>
              cases hrest
              obtain ⟨o, ho, _⟩ := key []
              exact ⟨o, by rw [runSharedAux_succ, ho]⟩
          | some p' =>
              have hok := stepShared_ok p b
              rw [hst] at hok
              obtain ⟨hsz, _⟩ := hok
              obtain ⟨o', ho'⟩ := runSharedAux_complete_noNestedPar n p' (by omega)
                (hnn p' rfl) s hrest
              obtain ⟨o, ho, ho2⟩ := key o'
              exact ⟨o, by rw [runSharedAux_succ, ho]; simp only [ho2, ho']⟩

/-! ## Oracle consumption -/

theorem take_headD {o : Oracle} {k : Nat} (hk : 0 < k) : (o.take k).headD false = o.headD false := by
  cases o with
  | nil => simp
  | cons b o => cases k with
    | zero => omega
    | succ k => simp

theorem take_tail (o : Oracle) (k : Nat) : (o.take k).tail = o.tail.take (k - 1) := by
  cases o with
  | nil => simp
  | cons b o => cases k with
    | zero => simp
    | succ k => simp

theorem drop_succ_eq_tail_drop (o : Oracle) (c : Nat) : o.drop (c + 1) = o.tail.drop c := by
  cases o <;> simp

theorem stepShared_none {p : Prog α} {b : Bool} {x : α} (h : stepShared p b = (x, none)) :
    p = .act x := by
  have hok := stepShared_ok p b
  rw [h] at hok
  exact hok

theorem stepShared_some_size {p p' : Prog α} {b : Bool} {x : α} (h : stepShared p b = (x, some p')) :
    p.size = p'.size + 1 := by
  have hok := stepShared_ok p b
  rw [h] at hok
  exact hok.1

/-- Each shared step that crosses a parallel composition lowers `schedPoints` by
at least one; other steps do not raise it. -/
theorem stepShared_schedPoints : ∀ (p : Prog α) (b : Bool) (x : α) (p' : Prog α),
    stepShared p b = (x, some p') →
      schedPoints p' + (if needsChoice p then 1 else 0) ≤ schedPoints p
  | .act _, _, _, _, h => by simp [stepShared] at h
  | .seq p q, b, x, p', h => by
      rcases h1 : stepShared p b with ⟨x1, _ | p1⟩
      · have := stepShared_none h1
        subst this
        simp only [stepShared, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨_, rfl⟩ := h
        simp [needsChoice, schedPoints]
      · have ih := stepShared_schedPoints p b x1 p1 h1
        simp only [stepShared, h1, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨_, rfl⟩ := h
        simp only [needsChoice, schedPoints]
        by_cases hc : needsChoice p = true <;> simp only [hc, ↓reduceIte] at ih ⊢ <;> omega
  | .par p q, b, x, p', h => by
      have hp := size_pos p
      have hq := size_pos q
      simp only [needsChoice, ite_true]
      simp only [stepShared] at h
      split at h
      · rcases h1 : stepShared q b with ⟨x1, _ | q1⟩ <;> rw [h1] at h <;>
          simp only [Prod.mk.injEq, Option.some.injEq] at h <;> obtain ⟨_, rfl⟩ := h
        · have := stepShared_none h1
          subst this
          simp only [schedPoints, size]
          omega
        · have ih := stepShared_schedPoints q b x1 q1 h1
          have hsz := stepShared_some_size h1
          have : schedPoints q1 ≤ schedPoints q := Nat.le_trans (Nat.le_add_right _ _) ih
          simp only [schedPoints]
          split at ih <;> omega
      · rcases h1 : stepShared p b with ⟨x1, _ | p1⟩ <;> rw [h1] at h <;>
          simp only [Prod.mk.injEq, Option.some.injEq] at h <;> obtain ⟨_, rfl⟩ := h
        · have := stepShared_none h1
          subst this
          simp only [schedPoints, size]
          omega
        · have ih := stepShared_schedPoints p b x1 p1 h1
          have hsz := stepShared_some_size h1
          simp only [schedPoints]
          split at ih <;> omega

theorem runSharedAux_take : ∀ (n : Nat) (p : Prog α) (o : Oracle) (k : Nat), p.size = n →
    schedPoints p ≤ k → runSharedAux n (o.take k) p = runSharedAux n o p
  | 0, _, _, _, _, _ => rfl
  | n + 1, p, o, k, h, hk => by
      rw [runSharedAux_succ, runSharedAux_succ]
      cases hc : needsChoice p
      · have e1 : sharedBit p (o.take k) = (false, o.take k) := by simp [sharedBit, hc]
        have e2 : sharedBit p o = (false, o) := by simp [sharedBit, hc]
        rw [e1, e2]
        rcases hs : stepShared p false with ⟨x, _ | p'⟩
        · rfl
        · have hsp := stepShared_schedPoints p false x p' hs
          have hsz := stepShared_some_size hs
          simp only [hc] at hsp
          simp only
          rw [runSharedAux_take n p' o k (by omega) (by simp at hsp; omega)]
      · have e1 : sharedBit p (o.take k) = ((o.take k).headD false, (o.take k).tail) := by
          simp [sharedBit, hc]
        have e2 : sharedBit p o = (o.headD false, o.tail) := by simp [sharedBit, hc]
        rw [e1, e2]
        rcases hs : stepShared p (o.headD false) with ⟨x, _ | p'⟩
        · have := stepShared_none hs
          subst this; simp [needsChoice] at hc
        · have hsp := stepShared_schedPoints p _ x p' hs
          have hsz := stepShared_some_size hs
          simp only [hc, ite_true] at hsp
          have hk1 : 0 < k := by omega
          rw [take_headD hk1, hs, take_tail]
          simp only
          rw [runSharedAux_take n p' o.tail (k - 1) (by omega) (by omega)]

/-- A sharper bound for the shared-choice generator: one bit per step at most,
and none on the last step. -/
theorem runSharedAux_take_size : ∀ (n : Nat) (p : Prog α) (o : Oracle) (k : Nat), p.size = n →
    n - 1 ≤ k → runSharedAux n (o.take k) p = runSharedAux n o p
  | 0, _, _, _, _, _ => rfl
  | n + 1, p, o, k, h, hk => by
      rw [runSharedAux_succ, runSharedAux_succ]
      cases hc : needsChoice p
      · have e1 : sharedBit p (o.take k) = (false, o.take k) := by simp [sharedBit, hc]
        have e2 : sharedBit p o = (false, o) := by simp [sharedBit, hc]
        rw [e1, e2]
        rcases hs : stepShared p false with ⟨x, _ | p'⟩
        · rfl
        · have hsz := stepShared_some_size hs
          simp only
          rw [runSharedAux_take_size n p' o k (by omega) (by omega)]
      · have e1 : sharedBit p (o.take k) = ((o.take k).headD false, (o.take k).tail) := by
          simp [sharedBit, hc]
        have e2 : sharedBit p o = (o.headD false, o.tail) := by simp [sharedBit, hc]
        rw [e1, e2]
        rcases hs : stepShared p (o.headD false) with ⟨x, _ | p'⟩
        · have := stepShared_none hs
          subst this; simp [needsChoice] at hc
        · have hsz := stepShared_some_size hs
          have hp' := size_pos p'
          have hk1 : 0 < k := by omega
          rw [take_headD hk1, hs, take_tail]
          simp only
          rw [runSharedAux_take_size n p' o.tail (k - 1) (by omega) (by omega)]

/-- Bits consumed by one per-step step: `c` bits are read, and the residual's
`schedPoints` drops by at least `c`. -/
def BitsOK (p : Prog α) : Option (Prog α) → Nat → Prop
  | none, c => c = 0
  | some p', c => schedPoints p' + c ≤ schedPoints p

theorem stepPerNode_take : ∀ (p : Prog α) (o : Oracle) (x : α) (r : Option (Prog α)) (o' : Oracle),
    stepPerNode p o = (x, r, o') →
    ∃ c, o' = o.drop c ∧ BitsOK p r c ∧
      ∀ k, c ≤ k → stepPerNode p (o.take k) = (x, r, o'.take (k - c))
  | .act y, o, x, r, o', h => by
      simp only [stepPerNode, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨0, rfl, rfl, fun k _ => by simp [stepPerNode]⟩
  | .seq p q, o, x, r, o', h => by
      rcases h1 : stepPerNode p o with ⟨x1, r1, o1⟩
      obtain ⟨c, ho1, hb, hk⟩ := stepPerNode_take p o x1 r1 o1 h1
      refine ⟨c, ?_, ?_, ?_⟩
      · cases r1 <;> simp only [stepPerNode, h1, Prod.mk.injEq] at h <;> obtain ⟨_, _, rfl⟩ := h <;>
          exact ho1
      · cases r1 with
        | none =>
            simp only [stepPerNode, h1, Prod.mk.injEq] at h
            obtain ⟨_, rfl, _⟩ := h
            have := stepPerNode_ok p o
            rw [h1] at this
            subst this
            simp only [BitsOK] at hb ⊢
            simp [schedPoints, hb]
        | some p1 =>
            simp only [stepPerNode, h1, Prod.mk.injEq] at h
            obtain ⟨_, rfl, _⟩ := h
            simp only [BitsOK] at hb ⊢
            simp only [schedPoints]
            omega
      · intro k hck
        cases r1 <;> simp only [stepPerNode, h1, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;>
          simp only [stepPerNode, hk k hck]
  | .par p q, o, x, r, o', h => by
      have hp := size_pos p
      have hq := size_pos q
      simp only [stepPerNode] at h
      by_cases hbit : o.headD false = true
      · simp only [hbit, ↓reduceIte] at h
        rcases h1 : stepPerNode q o.tail with ⟨x1, r1, o1⟩
        obtain ⟨c, ho1, hb, hk⟩ := stepPerNode_take q o.tail x1 r1 o1 h1
        refine ⟨c + 1, ?_, ?_, ?_⟩
        · cases r1 <;> simp only [h1, Prod.mk.injEq] at h <;> obtain ⟨_, _, rfl⟩ := h <;>
            (rw [drop_succ_eq_tail_drop]; exact ho1)
        · cases r1 with
          | none =>
              simp only [h1, Prod.mk.injEq] at h
              obtain ⟨_, rfl, _⟩ := h
              have := stepPerNode_ok q o.tail
              rw [h1] at this
              subst this
              simp only [BitsOK] at hb ⊢
              simp only [schedPoints, size]
              omega
          | some q1 =>
              simp only [h1, Prod.mk.injEq] at h
              obtain ⟨_, rfl, _⟩ := h
              have hok := stepPerNode_ok q o.tail
              rw [h1] at hok
              have hsz := hok.1
              simp only [BitsOK] at hb ⊢
              simp only [schedPoints]
              omega
        · intro k hck
          have hk1 : 0 < k := by omega
          simp only [stepPerNode]
          rw [take_headD hk1]
          simp only [hbit, ↓reduceIte]
          rw [take_tail, hk (k - 1) (by omega)]
          have e : k - 1 - c = k - (c + 1) := by omega
          cases r1 <;> simp only [h1, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;>
            simp only [e]
      · simp only [hbit, Bool.false_eq_true, ↓reduceIte] at h
        rcases h1 : stepPerNode p o.tail with ⟨x1, r1, o1⟩
        obtain ⟨c, ho1, hb, hk⟩ := stepPerNode_take p o.tail x1 r1 o1 h1
        refine ⟨c + 1, ?_, ?_, ?_⟩
        · cases r1 <;> simp only [h1, Prod.mk.injEq] at h <;> obtain ⟨_, _, rfl⟩ := h <;>
            (rw [drop_succ_eq_tail_drop]; exact ho1)
        · cases r1 with
          | none =>
              simp only [h1, Prod.mk.injEq] at h
              obtain ⟨_, rfl, _⟩ := h
              have := stepPerNode_ok p o.tail
              rw [h1] at this
              subst this
              simp only [BitsOK] at hb ⊢
              simp only [schedPoints, size]
              omega
          | some p1 =>
              simp only [h1, Prod.mk.injEq] at h
              obtain ⟨_, rfl, _⟩ := h
              have hok := stepPerNode_ok p o.tail
              rw [h1] at hok
              have hsz := hok.1
              simp only [BitsOK] at hb ⊢
              simp only [schedPoints]
              omega
        · intro k hck
          have hk1 : 0 < k := by omega
          simp only [stepPerNode]
          rw [take_headD hk1]
          simp only [hbit, Bool.false_eq_true, ↓reduceIte]
          rw [take_tail, hk (k - 1) (by omega)]
          have e : k - 1 - c = k - (c + 1) := by omega
          cases r1 <;> simp only [h1, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;>
            simp only [e]

theorem runPerStepAux_take : ∀ (n : Nat) (p : Prog α) (o : Oracle) (k : Nat), p.size = n →
    schedPoints p ≤ k → runPerStepAux n (o.take k) p = runPerStepAux n o p
  | 0, _, _, _, _, _ => rfl
  | n + 1, p, o, k, h, hk => by
      rcases hs : stepPerNode p o with ⟨x, r, o'⟩
      obtain ⟨c, _, hb, htk⟩ := stepPerNode_take p o x r o' hs
      have hok := stepPerNode_ok p o
      rw [hs] at hok
      cases r with
      | none =>
          simp only [BitsOK] at hb
          subst hb
          simp only [runPerStepAux, htk k (Nat.zero_le _), hs]
      | some p' =>
          simp only [BitsOK] at hb
          have hsz := hok.1
          simp only [runPerStepAux, htk k (by omega), hs]
          rw [runPerStepAux_take n p' o' (k - c) (by omega) (by omega)]

/-! ## Necessity of `NoNestedPar` for distinct labels -/

/-- The actions that can come first in some interleaving of `p`. -/
def firsts : Prog α → List α
  | .act x => [x]
  | .seq p _ => firsts p
  | .par p q => firsts p ++ firsts q

theorem exists_interleaving_of_mem_firsts : ∀ {p : Prog α} {y : α}, y ∈ firsts p →
    ∃ s, y :: s ∈ Interleavings p
  | .act x, y, h => by
      simp only [firsts, List.mem_singleton] at h
      subst h; exact ⟨[], mem_interleavings_act.mpr rfl⟩
  | .seq p q, y, h => by
      obtain ⟨s, hs⟩ := exists_interleaving_of_mem_firsts (p := p) h
      obtain ⟨t, ht⟩ := interleavings_nonempty q
      exact ⟨s ++ t, mem_interleavings_seq.mpr ⟨y :: s, hs, t, ht, rfl⟩⟩
  | .par p q, y, h => by
      simp only [firsts, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨s, hs⟩ := exists_interleaving_of_mem_firsts h
        obtain ⟨t, ht⟩ := interleavings_nonempty q
        exact ⟨s ++ t, mem_interleavings_par.mpr
          ⟨y :: s, hs, t, ht, mem_shuffle_cons_left (append_mem_shuffle s t)⟩⟩
      · obtain ⟨s, hs⟩ := exists_interleaving_of_mem_firsts h
        obtain ⟨t, ht⟩ := interleavings_nonempty p
        exact ⟨t ++ s, mem_interleavings_par.mpr
          ⟨t, ht, y :: s, hs, mem_shuffle_cons_right (append_mem_shuffle t s)⟩⟩

theorem firsts_subset_actions : ∀ {p : Prog α} {y : α}, y ∈ firsts p → y ∈ p.actions
  | .act _, _, h => h
  | .seq _ _, _, h => List.mem_append_left _ (firsts_subset_actions h)
  | .par _ _, _, h => by
      simp only [firsts, List.mem_append] at h
      rcases h with h | h
      · exact List.mem_append_left _ (firsts_subset_actions h)
      · exact List.mem_append_right _ (firsts_subset_actions h)

theorem stepShared_seq_fst (p q : Prog α) (b : Bool) :
    (stepShared (.seq p q) b).1 = (stepShared p b).1 := by
  simp only [stepShared]; rcases stepShared p b with ⟨x, _ | p'⟩ <;> rfl

theorem stepShared_par_false_fst (p q : Prog α) :
    (stepShared (.par p q) false).1 = (stepShared p false).1 := by
  simp only [stepShared, Bool.false_eq_true, ↓reduceIte]
  rcases stepShared p false with ⟨x, _ | p'⟩ <;> rfl

theorem stepShared_par_true_fst (p q : Prog α) :
    (stepShared (.par p q) true).1 = (stepShared q true).1 := by
  simp only [stepShared, ↓reduceIte]
  rcases stepShared q true with ⟨x, _ | p'⟩ <;> rfl

theorem stepShared_fst_mem_firsts : ∀ (p : Prog α) (b : Bool), (stepShared p b).1 ∈ firsts p
  | .act _, _ => List.mem_singleton_self _
  | .seq p q, b => by rw [stepShared_seq_fst]; exact stepShared_fst_mem_firsts p b
  | .par p q, b => by
      cases b
      · rw [stepShared_par_false_fst]
        exact List.mem_append_left _ (stepShared_fst_mem_firsts p false)
      · rw [stepShared_par_true_fst]
        exact List.mem_append_right _ (stepShared_fst_mem_firsts q true)

/-- With distinct labels, the two bits of a step that crosses a parallel
composition perform different actions. -/
theorem stepShared_fst_ne_of_needsChoice : ∀ (p : Prog α), p.actions.Nodup →
    needsChoice p = true → (stepShared p false).1 ≠ (stepShared p true).1
  | .act _, _, h => by simp [needsChoice] at h
  | .seq p q, hd, h => by
      rw [stepShared_seq_fst, stepShared_seq_fst]
      exact stepShared_fst_ne_of_needsChoice p (List.nodup_append.mp hd).1 h
  | .par p q, hd, _ => by
      rw [stepShared_par_false_fst, stepShared_par_true_fst]
      exact (List.nodup_append.mp hd).2.2 _
        (firsts_subset_actions (stepShared_fst_mem_firsts p false)) _
        (firsts_subset_actions (stepShared_fst_mem_firsts q true))

/-- With distinct labels, the action of a shared step determines its residual. -/
theorem stepShared_det {p : Prog α} (hd : p.actions.Nodup) {b₁ b₂ : Bool} {x : α}
    {r₁ r₂ : Option (Prog α)} (h₁ : stepShared p b₁ = (x, r₁)) (h₂ : stepShared p b₂ = (x, r₂)) :
    r₁ = r₂ := by
  cases hc : needsChoice p
  · rw [stepShared_eq_of_needsChoice_false p hc] at h₁ h₂
    rw [h₁] at h₂; cases h₂; rfl
  · have hne := stepShared_fst_ne_of_needsChoice p hd hc
    cases b₁ <;> cases b₂
    · rw [h₁] at h₂; cases h₂; rfl
    · rw [h₁, h₂] at hne; exact absurd rfl hne
    · rw [h₁, h₂] at hne; exact absurd rfl hne
    · rw [h₁] at h₂; cases h₂; rfl

theorem stepShared_perm_actions : ∀ {p p' : Prog α} {b : Bool} {x : α},
    stepShared p b = (x, some p') → p.actions.Perm (x :: p'.actions)
  | .act _, _, _, _, h => by simp [stepShared] at h
  | .seq p q, p', b, x, h => by
      rcases h1 : stepShared p b with ⟨x1, _ | p1⟩ <;>
        simp only [stepShared, h1, Prod.mk.injEq, Option.some.injEq] at h <;>
        obtain ⟨rfl, rfl⟩ := h
      · have := stepShared_none h1
        subst this
        exact List.Perm.refl _
      · exact (stepShared_perm_actions h1).append_right q.actions
  | .par p q, p', b, x, h => by
      simp only [stepShared] at h
      split at h
      · rcases h1 : stepShared q b with ⟨x1, _ | q1⟩ <;> rw [h1] at h <;>
          simp only [Prod.mk.injEq, Option.some.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
        · have := stepShared_none h1
          subst this
          exact List.perm_middle.trans (by simp)
        · exact ((stepShared_perm_actions h1).append_left p.actions).trans List.perm_middle
      · rcases h1 : stepShared p b with ⟨x1, _ | p1⟩ <;> rw [h1] at h <;>
          simp only [Prod.mk.injEq, Option.some.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
        · have := stepShared_none h1
          subst this
          exact List.Perm.refl _
        · exact (stepShared_perm_actions h1).append_right q.actions

theorem nodup_of_stepShared {p p' : Prog α} {b : Bool} {x : α} (hd : p.actions.Nodup)
    (h : stepShared p b = (x, some p')) : p'.actions.Nodup :=
  (List.nodup_cons.mp ((stepShared_perm_actions h).nodup_iff.mp hd)).2

/-- An initial action that neither bit reaches is never generated first. -/
theorem not_complete_of_mem_firsts {p : Prog α} {y : α} (hy : y ∈ firsts p)
    (h0 : y ≠ (stepShared p false).1) (h1 : y ≠ (stepShared p true).1) :
    ¬ Complete runShared p := by
  intro hc
  obtain ⟨s, hs⟩ := exists_interleaving_of_mem_firsts hy
  obtain ⟨o, ho⟩ := hc _ hs
  have hpos := size_pos p
  obtain ⟨m, hm⟩ : ∃ m, p.size = m + 1 := ⟨p.size - 1, by omega⟩
  simp only [runShared, hm, runSharedAux_succ] at ho
  have hfst : ∀ b, (stepShared p b).1 = y → False := by
    intro b hb; cases b
    · exact h0 hb.symm
    · exact h1 hb.symm
  rcases hst : stepShared p (sharedBit p o).1 with ⟨x, _ | p'⟩ <;> rw [hst] at ho
  · obtain ⟨rfl, _⟩ := List.cons.inj ho
    exact hfst _ (by rw [hst])
  · obtain ⟨rfl, _⟩ := List.cons.inj ho
    exact hfst _ (by rw [hst])

/-- Incompleteness of a residual propagates back along a shared step (distinct labels). -/
theorem not_complete_of_step {p p' : Prog α} {b : Bool} {x : α} (hd : p.actions.Nodup)
    (h : stepShared p b = (x, some p')) (hnc : ¬ Complete runShared p') :
    ¬ Complete runShared p := by
  intro hc
  apply hnc
  intro s hs
  have hok := stepShared_ok p b
  rw [h] at hok
  obtain ⟨hsz, hmem⟩ := hok
  obtain ⟨o, ho⟩ := hc _ (hmem s hs)
  simp only [runShared, hsz, runSharedAux_succ] at ho
  rcases hst : stepShared p (sharedBit p o).1 with ⟨x2, _ | p2⟩ <;> rw [hst] at ho
  · obtain ⟨rfl, rfl⟩ := List.cons.inj ho
    have := stepShared_det hd hst h
    cases this
  · obtain ⟨rfl, hrest⟩ := List.cons.inj ho
    have := stepShared_det hd hst h
    cases this
    exact ⟨_, hrest⟩

/-- A residual of a program that crosses no parallel composition at its next
step keeps every parallel composition. -/
theorem hasPar_of_stepShared : ∀ {R R' : Prog α} {b : Bool} {x : α}, needsChoice R = false →
    R.hasPar = true → stepShared R b = (x, some R') → R'.hasPar = true
  | .act _, _, _, _, _, hp, _ => by simp [hasPar] at hp
  | .seq p q, R', b, x, hc, hp, h => by
      simp only [needsChoice] at hc
      rcases h1 : stepShared p b with ⟨x1, _ | p1⟩ <;>
        simp only [stepShared, h1, Prod.mk.injEq, Option.some.injEq] at h <;>
        obtain ⟨rfl, rfl⟩ := h
      · have := stepShared_none h1
        subst this
        simpa [hasPar] using hp
      · simp only [hasPar, Bool.or_eq_true] at hp ⊢
        rcases hp with hp | hp
        · exact Or.inl (hasPar_of_stepShared hc hp h1)
        · exact Or.inr hp
  | .par _ _, _, _, _, hc, _, _ => by simp [needsChoice] at hc

/-- Progress: a program with a nested parallel composition either has an
initial action that neither bit reaches, or has a shared step to a residual that
still has a nested parallel composition. -/
theorem nested_progress : ∀ (p : Prog α), p.actions.Nodup → ¬ NoNestedPar p →
    (∃ y ∈ firsts p, y ≠ (stepShared p false).1 ∧ y ≠ (stepShared p true).1) ∨
      (∃ b x p', stepShared p b = (x, some p') ∧ ¬ NoNestedPar p')
  | .act _, _, hn => absurd trivial hn
  | .seq p q, hd, hn => by
      have hdp := (List.nodup_append.mp hd).1
      by_cases hnp : NoNestedPar p
      · have hnq : ¬ NoNestedPar q := fun hq => hn ⟨hnp, hq⟩
        right
        rcases h1 : stepShared p false with ⟨x1, _ | p1⟩
        · exact ⟨false, x1, q, by simp only [stepShared, h1], hnq⟩
        · exact ⟨false, x1, .seq p1 q, by simp only [stepShared, h1], fun h => hnq h.2⟩
      · rcases nested_progress p hdp hnp with ⟨y, hy, h0, h1⟩ | ⟨b, x, p', h, hn'⟩
        · left
          exact ⟨y, hy, by rw [stepShared_seq_fst]; exact h0, by rw [stepShared_seq_fst]; exact h1⟩
        · right
          exact ⟨b, x, .seq p' q, by simp only [stepShared, h], fun h' => hn' h'.1⟩
  | .par L R, hd, hn => by
      obtain ⟨hdL, hdR, hdisj⟩ := List.nodup_append.mp hd
      have hLR : L.hasPar = true ∨ R.hasPar = true := by
        cases hl : L.hasPar <;> cases hr : R.hasPar <;> simp_all [NoNestedPar]
      rcases hLR with hL | hR
      · cases hc : needsChoice L
        · right
          rcases h1 : stepShared L false with ⟨x1, _ | L'⟩
          · have := stepShared_none h1
            subst this; simp [hasPar] at hL
          · refine ⟨false, x1, .par L' R, ?_, ?_⟩
            · simp only [stepShared, h1, Bool.false_eq_true, ↓reduceIte]
            · intro h'
              have := hasPar_of_stepShared hc hL h1
              rw [h'.1] at this; exact Bool.noConfusion this
        · left
          refine ⟨(stepShared L true).1,
            List.mem_append_left _ (stepShared_fst_mem_firsts L true), ?_, ?_⟩
          · rw [stepShared_par_false_fst]
            exact (stepShared_fst_ne_of_needsChoice L hdL hc).symm
          · rw [stepShared_par_true_fst]
            exact hdisj _ (firsts_subset_actions (stepShared_fst_mem_firsts L true)) _
              (firsts_subset_actions (stepShared_fst_mem_firsts R true))
      · cases hc : needsChoice R
        · right
          rcases h1 : stepShared R true with ⟨x1, _ | R'⟩
          · have := stepShared_none h1
            subst this; simp [hasPar] at hR
          · refine ⟨true, x1, .par L R', ?_, ?_⟩
            · simp only [stepShared, h1, ↓reduceIte]
            · intro h'
              have := hasPar_of_stepShared hc hR h1
              rw [h'.2] at this; exact Bool.noConfusion this
        · left
          refine ⟨(stepShared R false).1,
            List.mem_append_right _ (stepShared_fst_mem_firsts R false), ?_, ?_⟩
          · rw [stepShared_par_false_fst]
            intro he
            exact hdisj _ (firsts_subset_actions (stepShared_fst_mem_firsts L false)) _
              (firsts_subset_actions (stepShared_fst_mem_firsts R false)) he.symm
          · rw [stepShared_par_true_fst]
            exact stepShared_fst_ne_of_needsChoice R hdR hc

theorem not_complete_of_not_noNestedPar : ∀ (n : Nat) (p : Prog α), p.size ≤ n →
    p.actions.Nodup → ¬ NoNestedPar p → ¬ Complete runShared p
  | 0, p, h, _, _ => absurd h (Nat.not_le.mpr (size_pos p))
  | n + 1, p, h, hd, hn => by
      rcases nested_progress p hd hn with ⟨y, hy, h0, h1⟩ | ⟨b, x, p', hst, hn'⟩
      · exact not_complete_of_mem_firsts hy h0 h1
      · have hsz := stepShared_some_size hst
        exact not_complete_of_step hd hst
          (not_complete_of_not_noNestedPar n p' (by omega) (nodup_of_stepShared hd hst) hn')

end Toy.SchedAdequacy
