import ToyProv.Transform

/-!
# Generic lemmas about executions

Proved infrastructure: executions of concatenated programs, replacement of one instruction by
another that steps identically in every reachable state, and identical-value substitution.
-/

namespace Toy.Prov

theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- Executing `P ++ Q` runs `P`, then `Q` from every UB-free state `P` reaches. -/
theorem exec_append (m : Model) (P Q : Prog) (s : St) :
    exec m (P ++ Q) s = (exec m P s).flatMap (fun o => match o with
      | none => [none]
      | some s' => exec m Q s') := by
  induction P generalizing s with
  | nil => simp [exec]
  | cons i P ih =>
    simp only [List.cons_append, exec, List.flatMap_assoc]
    apply flatMap_congr_mem
    intro o _
    cases o with
    | none => simp
    | some s' => simp [ih]

theorem mem_after {m : Model} {pre : Prog} {s : St} :
    s ∈ after m pre ↔ some s ∈ exec m pre init := by
  simp [after, List.mem_filterMap]

/-- Replacing one instruction by another that has the same successor list in every reachable
state leaves the set of executions unchanged. -/
theorem exec_replace_of_step_eq (m : Model) (pre post : Prog) (i i' : Instr)
    (h : ∀ s ∈ after m pre, step m s i' = step m s i) :
    exec m (pre ++ i' :: post) init = exec m (pre ++ i :: post) init := by
  rw [exec_append, exec_append]
  apply flatMap_congr_mem
  intro o ho
  cases o with
  | none => rfl
  | some s => simp only [exec]; rw [h s (mem_after.mpr ho)]

theorem beh_replace_of_step_eq (m : Model) (pre post : Prog) (i i' : Instr)
    (h : ∀ s ∈ after m pre, step m s i' = step m s i) :
    beh m (pre ++ i' :: post) = beh m (pre ++ i :: post) := by
  unfold beh runs
  rw [exec_replace_of_step_eq m pre post i i' h]

theorem refines_of_beh_eq {m : Model} {tgt src : Prog} (h : beh m tgt = beh m src) :
    Refines m tgt src :=
  Or.inr (fun _ ho => h ▸ ho)

theorem regs_subReg {s : St} {q p : Reg} (h : s.regs p = s.regs q) (r : Reg) :
    s.regs (subReg q p r) = s.regs r := by
  unfold subReg; split <;> simp_all

/-- Substituting reads of `q` by reads of `p` does not change a step when the two registers hold
the same value (in every model). -/
theorem step_substUse (m : Model) (s : St) (i : Instr) (q p : Reg) (h : s.regs p = s.regs q) :
    step m s (i.substUse q p) = step m s i := by
  cases i <;> simp only [Instr.substUse, step, regs_subReg h]

theorem AllAfter_nil {m : Model} {c : St → Bool} : AllAfter m [] c ↔ c init = true := by
  simp [AllAfter, after, exec]

/-- If every execution reaches UB, the behaviour is `[ub]`. -/
theorem beh_ub_of_all_none {m : Model} {P : Prog} (h : ∀ o ∈ exec m P init, o = none) :
    beh m P = [.ub] := by
  have hall : (runs m P).all (fun o => decide (o = .ub)) = true := by
    unfold runs
    rw [List.all_eq_true]
    intro x hx
    rw [List.mem_map] at hx
    rcases hx with ⟨o, ho, rfl⟩
    rw [h o ho]
    rfl
  unfold beh
  dsimp only
  split
  · rfl
  · rename_i hne; exact absurd hall hne

end Toy.Prov
