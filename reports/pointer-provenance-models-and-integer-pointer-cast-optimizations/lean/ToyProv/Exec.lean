import ToyProv.Lemmas
import ToyProv.Monotone

/-!
# Execution lemmas

`execOk m P s` lists the UB-free final states of running `P` from `s`; `after m P` is
`execOk m P init`. This module relates `exec`, `after` and `beh`, and proves that the `flat` and
`strict` models are deterministic (every instruction has exactly one successor, defined or UB).
-/

namespace Toy.Prov

def execOk (m : Model) (P : Prog) (s : St) : List St :=
  (exec m P s).filterMap id

theorem after_eq_execOk (m : Model) (P : Prog) : after m P = execOk m P init := rfl

theorem execOk_nil (m : Model) (s : St) : execOk m [] s = [s] := rfl

theorem filterMap_id_append {α : Type} (l₁ l₂ : List (Option α)) :
    (l₁ ++ l₂).filterMap id = l₁.filterMap id ++ l₂.filterMap id := by
  induction l₁ with
  | nil => rfl
  | cons o l ih =>
    cases o <;> simp [List.filterMap, ih]

theorem filterMap_opt_flatMap (l : List (Option St)) (f : St → List (Option St)) :
    (l.flatMap (fun o => match o with | none => [none] | some s' => f s')).filterMap id =
      (l.filterMap id).flatMap (fun s' => (f s').filterMap id) := by
  induction l with
  | nil => rfl
  | cons o l ih =>
    cases o with
    | none => simp [List.flatMap_cons, List.filterMap, ih]
    | some s' =>
      simp only [List.flatMap_cons, List.filterMap_cons, id_eq, filterMap_id_append, ih]

theorem execOk_cons (m : Model) (i : Instr) (P : Prog) (s : St) :
    execOk m (i :: P) s = ((step m s i).filterMap id).flatMap (execOk m P) := by
  simp only [execOk]
  rw [show exec m (i :: P) s = (step m s i).flatMap
    (fun o => match o with | none => [none] | some s' => exec m P s') from rfl]
  exact filterMap_opt_flatMap (step m s i) (exec m P)

theorem execOk_append (m : Model) (P Q : Prog) (s : St) :
    execOk m (P ++ Q) s = (execOk m P s).flatMap (execOk m Q) := by
  unfold execOk
  rw [exec_append]
  exact filterMap_opt_flatMap (exec m P s) (exec m Q)

theorem all_map_outcome_eq (l : List (Option St)) (f : Option St → Outcome)
    (hfn : f none = .ub) (hfs : ∀ s, f (some s) = .done s.out)
    (p : Outcome → Bool) (hp : p .ub = true) (hd : ∀ s, p (.done s) = false) :
    (l.map f).all p = (l.filterMap id).isEmpty := by
  induction l with
  | nil => rfl
  | cons o l ih =>
    cases o with
    | none => simp [List.filterMap, hfn, hp, ih]
    | some s => simp [List.filterMap, hfs, hd]

theorem filter_map_outcome_eq (l : List (Option St)) (f : Option St → Outcome)
    (hfn : f none = .ub) (hfs : ∀ s, f (some s) = .done s.out)
    (q : Outcome → Bool) (hq : q .ub = false) (hd : ∀ s, q (.done s) = true) :
    (l.map f).filter q = (l.filterMap id).map (fun s => .done s.out) := by
  induction l with
  | nil => rfl
  | cons o l ih =>
    cases o with
    | none => simp [List.filterMap, hfn, hq, ih]
    | some s => simp [List.filterMap, hfs, hd, ih]

theorem beh_eq_of_after (m : Model) (P : Prog) :
    beh m P = if (after m P).isEmpty then [.ub] else (after m P).map (fun s => .done s.out) := by
  unfold beh runs after
  dsimp only
  rw [all_map_outcome_eq (exec m P init) _ rfl (fun _ => rfl) _ (by decide) (fun _ => by simp),
    filter_map_outcome_eq (exec m P init) _ rfl (fun _ => rfl) _ (by decide) (fun _ => by simp)]

theorem refines_of_after_map_out_eq {m : Model} {tgt src : Prog}
    (h : (after m tgt).map St.out = (after m src).map St.out) :
    Refines m tgt src := by
  apply refines_of_beh_eq
  rw [beh_eq_of_after, beh_eq_of_after]
  have hem : (after m tgt).isEmpty = (after m src).isEmpty := by
    have hl : (after m tgt).length = (after m src).length := by
      simpa using congrArg List.length h
    cases ht : after m tgt <;> cases hs : after m src <;> simp_all
  have hm : (after m tgt).map (fun s => Outcome.done s.out) =
      (after m src).map (fun s => Outcome.done s.out) := by
    simpa [List.map_map, Function.comp_def] using congrArg (List.map Outcome.done) h
  rw [hem, hm]

theorem refines_of_after_eq {m : Model} {tgt src : Prog} (h : after m tgt = after m src) :
    Refines m tgt src :=
  refines_of_after_map_out_eq (congrArg (List.map St.out) h)

theorem step_det {m : Model} (hm : m = .flat ∨ m = .strict) (s : St) (i : Instr) :
    ∃ o, step m s i = [o] := by
  have hcast : ∀ d a, ∃ o, castToPtr m s d a = [o] := by
    intro d a
    rcases hm with rfl | rfl <;> exact ⟨_, rfl⟩
  cases i with
  | alloc d n => by_cases hn : n = 0 <;> simp [step, hn]
  | free p =>
    cases h : s.regs p with
    | none => exact ⟨none, by simp [step, h]⟩
    | some v =>
      cases v with
      | int _ => exact ⟨none, by simp [step, h]⟩
      | ptr x =>
        cases hft : freeTarget m s x <;> simp [step, h, hft]
  | load d ty p =>
    cases h : s.regs p with
    | none => exact ⟨none, by simp [step, h]⟩
    | some v =>
      cases v with
      | int _ => exact ⟨none, by simp [step, h]⟩
      | ptr x =>
        by_cases hacc : canAccess m s x 2 = true
        · cases ty with
          | int =>
            cases hdec : decodeInt (s.mem x.addr) (s.mem (x.addr + 1)) with
            | none => exact ⟨none, by simp [step, h, hacc, hdec]⟩
            | some np => exact ⟨some ((s.setReg d (.int np.1)).expose np.2), by simp [step, h, hacc, hdec]⟩
          | ptr =>
            cases hdec : decodePtr (s.mem x.addr) (s.mem (x.addr + 1)) with
            | none => exact ⟨none, by simp [step, h, hacc, hdec]⟩
            | some res =>
              cases res with
              | inl q => exact ⟨some (s.setReg d (.ptr q)), by simp [step, h, hacc, hdec]⟩
              | inr n => simp only [step, h, hacc, hdec]; exact hcast d n
        · exact ⟨none, by simp [step, h, hacc]⟩
  | store p r =>
    cases hp : s.regs p with
    | none => exact ⟨none, by simp [step, hp]⟩
    | some vp =>
      cases vp with
      | int _ => exact ⟨none, by simp [step, hp]⟩
      | ptr x =>
        cases hr : s.regs r with
        | none => exact ⟨none, by simp [step, hp, hr]⟩
        | some vr => by_cases hacc : canAccess m s x 2 = true <;> simp [step, hp, hr, hacc]
  | memcpy d r n =>
    cases hd : s.regs d with
    | none => exact ⟨none, by simp [step, hd]⟩
    | some vd =>
      cases vd with
      | int _ => exact ⟨none, by simp [step, hd]⟩
      | ptr x =>
        cases hr : s.regs r with
        | none => exact ⟨none, by simp [step, hd, hr]⟩
        | some vr =>
          cases vr with
          | int _ => exact ⟨none, by simp [step, hd, hr]⟩
          | ptr y =>
            by_cases hacc : (canAccess m s x n && canAccess m s y n) = true <;>
              simp [step, hd, hr, hacc]
  | ptr2int d p =>
    cases hp : s.regs p with
    | none => exact ⟨none, by simp [step, hp]⟩
    | some v => cases v <;> simp [step, hp]
  | int2ptr d i =>
    cases hi : s.regs i with
    | none => exact ⟨none, by simp [step, hi]⟩
    | some v =>
      cases v with
      | ptr _ => exact ⟨none, by simp [step, hi]⟩
      | int a => simp only [step, hi]; exact hcast d a
  | ptrEq d p q =>
    cases hp : s.regs p with
    | none => exact ⟨none, by simp [step, hp]⟩
    | some vp =>
      cases vp with
      | int _ => exact ⟨none, by simp [step, hp]⟩
      | ptr x =>
        cases hq : s.regs q with
        | none => exact ⟨none, by simp [step, hp, hq]⟩
        | some vq => cases vq <;> simp [step, hp, hq]
  | intEq d i j =>
    cases hi : s.regs i with
    | none => exact ⟨none, by simp [step, hi]⟩
    | some vi =>
      cases vi with
      | ptr _ => exact ⟨none, by simp [step, hi]⟩
      | int a =>
        cases hj : s.regs j with
        | none => exact ⟨none, by simp [step, hi, hj]⟩
        | some vj => cases vj <;> simp [step, hi, hj]
  | offset d p k =>
    cases hp : s.regs p with
    | none => exact ⟨none, by simp [step, hp]⟩
    | some vp =>
      cases vp with
      | int _ => exact ⟨none, by simp [step, hp]⟩
      | ptr x => cases hoa : offsetAddr x.addr k <;> simp [step, hp, hoa]
  | const d n => exact ⟨_, rfl⟩
  | copy d r => cases hr : s.regs r <;> simp [step, hr]
  | obs r =>
    cases hr : s.regs r with
    | none => exact ⟨none, by simp [step, hr]⟩
    | some v => cases v <;> simp [step, hr]

theorem exec_det {m : Model} (hm : m = .flat ∨ m = .strict) (P : Prog) (s : St) :
    ∃ o, exec m P s = [o] := by
  induction P generalizing s with
  | nil => exact ⟨some s, rfl⟩
  | cons i P ih =>
    obtain ⟨o, ho⟩ := step_det hm s i
    simp only [exec, ho, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    cases o with
    | none => exact ⟨none, rfl⟩
    | some s' => exact ih s'

theorem execOk_det_length {m : Model} (hm : m = .flat ∨ m = .strict) (P : Prog) (s : St) :
    (execOk m P s).length ≤ 1 := by
  obtain ⟨o, ho⟩ := exec_det hm P s
  unfold execOk
  rw [ho]
  cases o <;> simp

theorem execOk_det_eq {m : Model} (hm : m = .flat ∨ m = .strict) {P : Prog} {s₀ s₁ s₂ : St}
    (h₁ : s₁ ∈ execOk m P s₀) (h₂ : s₂ ∈ execOk m P s₀) : s₁ = s₂ := by
  obtain ⟨o, ho⟩ := exec_det hm P s₀
  unfold execOk at h₁ h₂
  rw [ho] at h₁ h₂
  cases o with
  | none => simp at h₁
  | some s =>
    simp only [List.filterMap, id_eq, List.mem_singleton] at h₁ h₂
    exact h₁.trans h₂.symm

theorem castToPtr_execOk_nonempty (m : Model) (s : St) (d : Reg) (a : Addr) :
    (castToPtr m s d a).filterMap id ≠ [] := by
  cases m with
  | flat => simp [castToPtr]
  | strict => simp [castToPtr]
  | exposed =>
    simp only [castToPtr]
    cases candidates s a <;> simp

end Toy.Prov
