import ToyTailCall.Machine

/-!
# Proof support: run composition and finalization lemmas
-/

namespace Toy.TailCall

/-- Running `a + b` steps is running `a` steps, then `b` steps. -/
theorem run_add (sem : Sem) (D : Option Nat) (p : Prog) :
    ∀ (a b : Nat) (c : Conf), run sem D p (a + b) c = run sem D p b (run sem D p a c)
  | 0, _, _ => by simp [run]
  | a + 1, b, .halted r => by simp [run, run_halted]
  | a + 1, b, .running st => by
    rw [Nat.succ_add]
    exact run_add sem D p a b (step sem D p st)

/-- `c'` is reachable from `c` in some number of steps. -/
def Reaches (sem : Sem) (D : Option Nat) (p : Prog) (c c' : Conf) : Prop :=
  ∃ n, run sem D p n c = c'

theorem Reaches.refl (sem : Sem) (D : Option Nat) (p : Prog) (c : Conf) : Reaches sem D p c c :=
  ⟨0, rfl⟩

theorem Reaches.trans {sem : Sem} {D : Option Nat} {p : Prog} {c₁ c₂ c₃ : Conf}
    (h₁ : Reaches sem D p c₁ c₂) (h₂ : Reaches sem D p c₂ c₃) : Reaches sem D p c₁ c₃ := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  exact ⟨a + b, by rw [run_add, ha, hb]⟩

theorem Reaches.step {sem : Sem} {D : Option Nat} {p : Prog} {st : State} {c : Conf}
    (h : step sem D p st = c) : Reaches sem D p (.running st) c :=
  ⟨1, by simp [run, h]⟩

theorem runsTo_of_reaches {sem : Sem} {D : Option Nat} {p : Prog} {r : Result}
    (h : Reaches sem D p (start D p) (.halted r)) : RunsTo sem D p r := h

private theorem kill_isLive_self (fr : Frame) (s : Slot) : (fr.kill s).isLive s = false := by
  unfold Frame.kill Frame.isLive
  by_cases h : s < fr.live.length
  · simp [List.getD_eq_getElem?_getD, h]
  · have hle : (fr.live.set s false).length ≤ s := by
      rw [List.length_set]
      exact Nat.le_of_not_lt h
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle]

private theorem kill_isLive_of_false (fr : Frame) (s t : Slot) (hf : fr.isLive t = false) :
    (fr.kill s).isLive t = false := by
  unfold Frame.kill Frame.isLive at *
  by_cases hst : s = t
  · subst hst; exact kill_isLive_self fr s
  · by_cases ht : t < fr.live.length
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne hst]
      exact hf
    · have hle : (fr.live.set s false).length ≤ t := by
        rw [List.length_set]
        exact Nat.le_of_not_lt ht
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle]

/-- A non-aborting `dropList` keeps the values, keeps dead slots dead and kills every slot it
drops. -/
theorem dropList_kills_mem (fn : Fn) (fr : Frame) (ss : List Slot) (unw : Bool)
    (hna : (dropList fn fr ss unw).2.2 ≠ .abort) :
    (dropList fn fr ss unw).1.vals = fr.vals ∧
    (∀ t, fr.isLive t = false → (dropList fn fr ss unw).1.isLive t = false) ∧
    (∀ s ∈ ss, (dropList fn fr ss unw).1.isLive s = false) := by
  induction ss generalizing fr unw with
  | nil => exact ⟨rfl, fun _ h => h, fun _ h => nomatch h⟩
  | cons s ss ih =>
    simp only [dropList] at hna ⊢
    cases hds : (fn.dtor s == .panics)
    · simp only [hds, Bool.false_eq_true, ↓reduceIte] at hna ⊢
      have ⟨hv, hpres, hmem⟩ := ih (fr.kill s) unw hna
      refine ⟨hv, fun t ht => hpres t (kill_isLive_of_false fr s t ht), ?_⟩
      intro x hx
      cases List.mem_cons.mp hx with
      | inl heq => rw [heq]; exact hpres s (kill_isLive_self fr s)
      | inr htail => exact hmem x htail
    · simp only [hds, ↓reduceIte] at hna ⊢
      cases unw with
      | true => exact absurd rfl hna
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hna ⊢
        have ⟨hv, hpres, hmem⟩ := ih (fr.kill s) true hna
        refine ⟨hv, fun t ht => hpres t (kill_isLive_of_false fr s t ht), ?_⟩
        intro x hx
        cases List.mem_cons.mp hx with
        | inl heq => rw [heq]; exact hpres s (kill_isLive_self fr s)
        | inr htail => exact hmem x htail

/-- Without panicking destructors, `dropList` emits one `drop` per slot and ends normally. -/
theorem dropList_no_panics (fn : Fn) (fr : Frame) (ss : List Slot) (unw : Bool)
    (hnp : ss.filter (fun s => fn.dtor s == .panics) = []) :
    (dropList fn fr ss unw).2.1 = ss.map (fun s => Event.drop (fr.get s).obs) ∧
    (dropList fn fr ss unw).2.2 = if unw then .unwind else .ok := by
  induction ss generalizing fr with
  | nil => simp [dropList]
  | cons s ss ih =>
    simp only [List.filter_cons] at hnp
    cases hds : (fn.dtor s == .panics)
    · simp only [hds, Bool.false_eq_true, ↓reduceIte] at hnp
      simp only [dropList, hds, Bool.false_eq_true, ↓reduceIte]
      have ⟨he, hd⟩ := ih (fr.kill s) hnp
      exact ⟨by simp only [List.map_cons, he]; congr 1, hd⟩
    · simp [hds] at hnp

/-- With exactly one panicking destructor, `dropList` (not unwinding) emits one `drop` per slot
and ends unwinding. -/
theorem dropList_one_panic (fn : Fn) (fr : Frame) (ss : List Slot)
    (hone : (ss.filter (fun s => fn.dtor s == .panics)).length = 1) :
    (dropList fn fr ss false).2.1 = ss.map (fun s => Event.drop (fr.get s).obs) ∧
    (dropList fn fr ss false).2.2 = .unwind := by
  induction ss generalizing fr with
  | nil => simp at hone
  | cons s ss ih =>
    simp only [List.filter_cons] at hone
    cases hds : (fn.dtor s == .panics)
    · simp only [hds, Bool.false_eq_true, ↓reduceIte] at hone
      simp only [dropList, hds, Bool.false_eq_true, ↓reduceIte]
      have ⟨he, hd⟩ := ih (fr.kill s) hone
      exact ⟨by simp only [List.map_cons, he]; congr 1, hd⟩
    · simp only [hds, ↓reduceIte, List.length_cons] at hone
      have h0 : ss.filter (fun s => fn.dtor s == .panics) = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      simp only [dropList, hds, ↓reduceIte, Bool.false_eq_true]
      have ⟨he, hd⟩ := dropList_no_panics fn (fr.kill s) ss true h0
      exact ⟨by simp only [List.map_cons, he]; congr 1, by simpa using hd⟩

end Toy.TailCall
