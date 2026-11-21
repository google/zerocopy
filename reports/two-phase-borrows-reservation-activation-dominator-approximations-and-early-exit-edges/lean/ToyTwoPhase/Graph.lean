import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm

/-!
# Finite control-flow graphs: walks, path-defined reachability, dominance

Nodes are `Fin n`. An edge relation is a successor list per node. All graph notions used by
the package are defined by quantifying over walks (lists of nodes). A decidable checker
`pathViaB` (iterated successor closure) is proved to agree with the walk definition
(`pathViaB_iff`), so concrete instances can be settled by `decide`.
-/

namespace Toy.TwoPhase

/-- Successor lists over the nodes `Fin n`. -/
abbrev Edges (n : Nat) := Fin n → List (Fin n)

variable {n : Nat}

/-- `IsWalk E π`: `π` is a nonempty list of nodes in which each node is followed by one of
its `E`-successors. -/
def IsWalk (E : Edges n) : List (Fin n) → Prop
  | [] => False
  | [_] => True
  | a :: b :: rest => b ∈ E a ∧ IsWalk E (b :: rest)

instance instDecidableIsWalk (E : Edges n) : (π : List (Fin n)) → Decidable (IsWalk E π)
  | [] => isFalse (fun h => h)
  | [_] => isTrue trivial
  | a :: b :: rest =>
    haveI := instDecidableIsWalk E (b :: rest)
    if h : b ∈ E a then
      if h' : IsWalk E (b :: rest) then isTrue ⟨h, h'⟩ else isFalse (fun hw => h' hw.2)
    else isFalse (fun hw => h hw.1)

/-- `PathVia E ok u v`: there is a walk `u = x₀ → x₁ → … → x_k = v` (`k ≥ 0`) along `E`
whose nodes `x₀, …, x_{k-1}` (all but the last) satisfy `ok`. The last node is
unconstrained. -/
def PathVia (E : Edges n) (ok : Fin n → Bool) (u v : Fin n) : Prop :=
  ∃ π : List (Fin n), IsWalk E (π ++ [v]) ∧ (π ++ [v]).head? = some u ∧ ∀ x ∈ π, ok x = true

/-! ## The decidable checker -/

/-- One closure step: keep every node of `S`, add every `E`-successor of an `ok` node of `S`.
The result is always a sublist of `List.finRange n`. -/
def closeStep (E : Edges n) (ok : Fin n → Bool) (S : List (Fin n)) : List (Fin n) :=
  (List.finRange n).filter (fun w => S.contains w || S.any (fun x => ok x && (E x).contains w))

/-- `k` closure steps from `{u}`. -/
def closeIter (E : Edges n) (ok : Fin n → Bool) (u : Fin n) : Nat → List (Fin n)
  | 0 => (List.finRange n).filter (fun w => w == u)
  | k + 1 => closeStep E ok (closeIter E ok u k)

/-- Decidable checker for `PathVia`: `n` closure steps from `{u}` contain `v`. -/
def pathViaB (E : Edges n) (ok : Fin n → Bool) (u v : Fin n) : Bool :=
  (closeIter E ok u n).contains v

/-! ## Agreement of `pathViaB` with `PathVia` -/

theorem mem_closeStep {E : Edges n} {ok : Fin n → Bool} {S : List (Fin n)} {w : Fin n} :
    w ∈ closeStep E ok S ↔ w ∈ S ∨ ∃ x ∈ S, ok x = true ∧ w ∈ E x := by
  simp [closeStep, List.mem_filter, List.mem_finRange]

theorem mem_closeIter_zero {E : Edges n} {ok : Fin n → Bool} {u w : Fin n} :
    w ∈ closeIter E ok u 0 ↔ w = u := by
  simp [closeIter, List.mem_filter, List.mem_finRange]

theorem isWalk_append_pair (E : Edges n) (x v : Fin n) (hv : v ∈ E x) :
    ∀ l : List (Fin n), IsWalk E (l ++ [x]) → IsWalk E (l ++ [x, v])
  | [], _ => ⟨hv, trivial⟩
  | [_], h => ⟨h.1, hv, trivial⟩
  | _ :: b :: t, h => ⟨h.1, isWalk_append_pair E x v hv (b :: t) h.2⟩

theorem head?_append_pair (l : List (Fin n)) (x v : Fin n) :
    (l ++ [x, v]).head? = (l ++ [x]).head? := by
  cases l <;> rfl

theorem pathVia_of_mem_closeIter {E : Edges n} {ok : Fin n → Bool} {u : Fin n} :
    ∀ (k : Nat) (v : Fin n), v ∈ closeIter E ok u k → PathVia E ok u v
  | 0, v, h => by
    have hv : v = u := mem_closeIter_zero.1 h
    subst hv
    exact ⟨[], trivial, rfl, by simp⟩
  | k + 1, v, h => by
    rcases mem_closeStep.1 h with h | ⟨x, hx, hok, hvx⟩
    · exact pathVia_of_mem_closeIter k v h
    · obtain ⟨π, hw, hh, hall⟩ := pathVia_of_mem_closeIter k x hx
      refine ⟨π ++ [x], ?_, ?_, ?_⟩
      · have := isWalk_append_pair E x v hvx π hw
        simpa [List.append_assoc] using this
      · have := head?_append_pair π x v
        simp only [List.append_assoc, List.cons_append, List.nil_append] at this ⊢
        rw [this]; exact hh
      · intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact hall y hy
        · simp at hy; subst hy; exact hok

theorem closeIter_eq_filter (E : Edges n) (ok : Fin n → Bool) (u : Fin n) (k : Nat) :
    ∃ p : Fin n → Bool, closeIter E ok u k = (List.finRange n).filter p := by
  cases k with
  | zero => exact ⟨_, rfl⟩
  | succ k => exact ⟨_, rfl⟩

theorem filter_length_lt {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ w ∈ l, p w = true → q w = true) → (∃ w ∈ l, q w = true ∧ p w = false) →
      (l.filter p).length < (l.filter q).length
  | [], _, ⟨_, hw, _⟩ => by simp at hw
  | a :: t, hpq, ⟨w, hw, hq, hp⟩ => by
    have hpq' : ∀ w ∈ t, p w = true → q w = true := fun w hw => hpq w (List.mem_cons_of_mem _ hw)
    have hle : (t.filter p).length ≤ (t.filter q).length := by
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      exact List.countP_mono_left (fun x hx hpx => hpq' x hx hpx)
    rcases List.mem_cons.1 hw with rfl | hw'
    · simp [hq, hp]; omega
    · have ih := filter_length_lt p q t hpq' ⟨w, hw', hq, hp⟩
      by_cases hpa : p a = true
      · have hqa := hpq a (List.mem_cons_self) hpa
        simp [hpa, hqa]; omega
      · by_cases hqa : q a = true
        · simp [hpa, hqa]; omega
        · simp [hpa, hqa]; omega

section Completeness
variable {E : Edges n} {ok : Fin n → Bool} {u : Fin n}

private abbrev S (E : Edges n) (ok : Fin n → Bool) (u : Fin n) (k : Nat) := closeIter E ok u k

theorem nodup_closeIter (k : Nat) : (closeIter E ok u k).Nodup := by
  obtain ⟨p, hp⟩ := closeIter_eq_filter E ok u k
  rw [hp]; exact List.Pairwise.filter p (List.nodup_finRange n)

theorem length_closeIter_le (k : Nat) : (closeIter E ok u k).length ≤ n := by
  have := List.Nodup.length_le_of_subset (nodup_closeIter (E := E) (ok := ok) (u := u) k)
    (l₂ := List.finRange n) (fun x _ => List.mem_finRange x)
  simpa using this

theorem closeIter_mono {k : Nat} {w : Fin n} (h : w ∈ closeIter E ok u k) :
    w ∈ closeIter E ok u (k + 1) :=
  mem_closeStep.2 (Or.inl h)

theorem closeIter_filter_self (k : Nat) :
    closeIter E ok u k = (List.finRange n).filter (fun w => (closeIter E ok u k).contains w) := by
  obtain ⟨p, hp⟩ := closeIter_eq_filter E ok u k
  rw [hp]
  apply List.filter_congr
  intro x _
  simp [List.mem_filter, List.mem_finRange]

theorem closeIter_length_lt {k : Nat} (h : ∃ w ∈ closeIter E ok u (k + 1), w ∉ closeIter E ok u k) :
    (closeIter E ok u k).length < (closeIter E ok u (k + 1)).length := by
  rw [closeIter_filter_self (k := k), closeIter_filter_self (k := k + 1)]
  apply filter_length_lt
  · intro w _ hw
    simp only [List.contains_iff_mem] at hw ⊢
    exact closeIter_mono hw
  · obtain ⟨w, hw, hw'⟩ := h
    exact ⟨w, List.mem_finRange w, by simpa using hw, by simpa using hw'⟩

theorem closeStep_congr {S T : List (Fin n)} (h : ∀ w, w ∈ S ↔ w ∈ T) :
    closeStep E ok S = closeStep E ok T := by
  unfold closeStep
  apply List.filter_congr
  intro w _
  apply Bool.eq_iff_iff.2
  simp only [Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro (hw | ⟨x, hx, hr⟩)
    · exact Or.inl ((h w).1 hw)
    · exact Or.inr ⟨x, (h x).1 hx, hr⟩
  · rintro (hw | ⟨x, hx, hr⟩)
    · exact Or.inl ((h w).2 hw)
    · exact Or.inr ⟨x, (h x).2 hx, hr⟩

theorem closeIter_mono_le {j k : Nat} {w : Fin n} (h : w ∈ closeIter E ok u j) (hjk : j ≤ k) :
    w ∈ closeIter E ok u k := by
  induction k with
  | zero => have : j = 0 := by omega
            subst this; exact h
  | succ k ih =>
    by_cases hj : j = k + 1
    · subst hj; exact h
    · exact closeIter_mono (ih (by omega))

/-- `Stable k`: step `k+1` adds nothing new. -/
private def Stable (E : Edges n) (ok : Fin n → Bool) (u : Fin n) (k : Nat) : Prop :=
  ∀ w, w ∈ closeIter E ok u (k + 1) ↔ w ∈ closeIter E ok u k

theorem stable_succ {k : Nat} (h : Stable E ok u k) : Stable E ok u (k + 1) := by
  intro w
  show w ∈ closeStep E ok (closeIter E ok u (k + 1)) ↔ w ∈ closeIter E ok u (k + 1)
  rw [closeStep_congr h]; rfl

theorem stable_of_le {j m : Nat} (h : Stable E ok u j) (hjm : j ≤ m) : Stable E ok u m := by
  induction m with
  | zero => have : j = 0 := by omega
            subst this; exact h
  | succ m ih =>
    by_cases hj : j = m + 1
    · subst hj; exact h
    · exact stable_succ (ih (by omega))

theorem length_or_stable (k : Nat) :
    k + 1 ≤ (closeIter E ok u k).length ∨ ∃ j, j < k ∧ Stable E ok u j := by
  induction k with
  | zero =>
    left
    have : u ∈ closeIter E ok u 0 := mem_closeIter_zero.2 rfl
    exact List.length_pos_of_mem this
  | succ k ih =>
    rcases ih with ih | ⟨j, hj, hs⟩
    · by_cases hs : Stable E ok u k
      · exact Or.inr ⟨k, by omega, hs⟩
      · left
        have hnew : ∃ w ∈ closeIter E ok u (k + 1), w ∉ closeIter E ok u k := by
          apply Classical.byContradiction
          intro hne
          apply hs
          intro w
          constructor
          · intro hw
            apply Classical.byContradiction
            intro hw'
            exact hne ⟨w, hw, hw'⟩
          · exact closeIter_mono
        have := closeIter_length_lt hnew
        omega
    · exact Or.inr ⟨j, by omega, hs⟩

theorem stable_n : Stable E ok u n := by
  rcases length_or_stable (E := E) (ok := ok) (u := u) (n + 1) with h | ⟨j, hj, hs⟩
  · have := length_closeIter_le (E := E) (ok := ok) (u := u) (n + 1)
    omega
  · exact stable_of_le hs (by omega)

theorem closeIter_n_closed {x w : Fin n} (hx : x ∈ closeIter E ok u n) (hok : ok x = true)
    (hw : w ∈ E x) : w ∈ closeIter E ok u n :=
  (stable_n w).1 (mem_closeStep.2 (Or.inr ⟨x, hx, hok, hw⟩))

theorem mem_closeIter_of_walk (v : Fin n) :
    ∀ (π : List (Fin n)) (w : Fin n), IsWalk E (π ++ [v]) → (π ++ [v]).head? = some w →
      w ∈ closeIter E ok u n → (∀ x ∈ π, ok x = true) → v ∈ closeIter E ok u n
  | [], w, _, hh, hw, _ => by
    simp at hh; subst hh; exact hw
  | [a], w, hwalk, hh, hw, hall => by
    simp at hh; subst hh
    exact closeIter_n_closed hw (hall a (by simp)) hwalk.1
  | a :: b :: t, w, hwalk, hh, hw, hall => by
    simp at hh; subst hh
    have hb : b ∈ closeIter E ok u n := closeIter_n_closed hw (hall a (by simp)) hwalk.1
    exact mem_closeIter_of_walk v (b :: t) b hwalk.2 rfl hb
      (fun x hx => hall x (List.mem_cons_of_mem _ hx))

end Completeness

/-- The checker agrees with the walk definition. -/
theorem pathViaB_iff {E : Edges n} {ok : Fin n → Bool} {u v : Fin n} :
    pathViaB E ok u v = true ↔ PathVia E ok u v := by
  unfold pathViaB
  rw [List.contains_iff_mem]
  constructor
  · exact pathVia_of_mem_closeIter n v
  · rintro ⟨π, hw, hh, hall⟩
    exact mem_closeIter_of_walk v π u hw hh (closeIter_mono_le (mem_closeIter_zero.2 rfl) (Nat.zero_le n)) hall

instance instDecidablePathVia (E : Edges n) (ok : Fin n → Bool) (u v : Fin n) :
    Decidable (PathVia E ok u v) :=
  decidable_of_iff _ pathViaB_iff

end Toy.TwoPhase
