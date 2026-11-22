import ToyLoanFlow.Analyses

/-!
# Soundness of the location-sensitive checker

An inductive invariant over the configurations reached by `run` from `RState.init`
(the node about to execute and the current state) shows that every well-typed program accepted
by `LSAccepts` is `Safe`.
-/

namespace Toy.LoanFlow

variable {n m : Nat}

namespace Sound

/-! ## State lemmas -/

theorem get_invalidate (sel : Rec n m → Bool) (σ : RState n m) (w : Fin m) :
    (invalidate sel σ).get w =
      (σ.get w).map (fun R => if sel R then { R with valid := false } else R) := by
  unfold invalidate RState.get
  rw [List.getElem?_map]
  cases σ[w.val]? with
  | none => rfl
  | some x => cases x <;> rfl

theorem length_invalidate (sel : Rec n m → Bool) (σ : RState n m) :
    (invalidate sel σ).length = σ.length := by
  simp [invalidate]

theorem length_set (σ : RState n m) (v : Fin m) (x : Option (Rec n m)) :
    (σ.set v x).length = σ.length := by
  simp [RState.set]

theorem get_set_self (σ : RState n m) (v : Fin m) (x : Option (Rec n m)) (h : σ.length = m) :
    (σ.set v x).get v = x := by
  unfold RState.set RState.get
  rw [List.getElem?_set_self (by omega)]
  rfl

theorem get_set_ne (σ : RState n m) {v w : Fin m} (x : Option (Rec n m)) (h : w ≠ v) :
    (σ.set v x).get w = σ.get w := by
  unfold RState.set RState.get
  rw [List.getElem?_set_ne (fun h' => h (Fin.ext h'.symm))]

theorem get_init (w : Fin m) : (RState.init : RState n m).get w = none := by
  unfold RState.init RState.get
  rw [List.getElem?_replicate]
  split <;> rfl

theorem length_init : (RState.init : RState n m).length = m := by
  simp [RState.init]

theorem get_invalidate_some {sel : Rec n m → Bool} {σ : RState n m} {w : Fin m} {R : Rec n m}
    (h : (invalidate sel σ).get w = some R) :
    ∃ R0, σ.get w = some R0 ∧ R = if sel R0 then { R0 with valid := false } else R0 := by
  rw [get_invalidate] at h
  cases h0 : σ.get w with
  | none => rw [h0] at h; cases h
  | some R0 =>
    rw [h0] at h
    exact ⟨R0, rfl, (Option.some.inj h).symm⟩

theorem get_invalidate_keep {sel : Rec n m → Bool} {σ : RState n m} {w : Fin m} {R : Rec n m}
    (h : σ.get w = some R) (hs : sel R = false) : (invalidate sel σ).get w = some R := by
  rw [get_invalidate, h]
  simp [hs]

theorem get_invalidate_none {sel : Rec n m → Bool} {σ : RState n m} {w : Fin m}
    (h : σ.get w = none) : (invalidate sel σ).get w = none := by
  rw [get_invalidate, h]; rfl

/-- Fields of an invalidated record. -/
theorem fields_of_get_invalidate {sel : Rec n m → Bool} {σ : RState n m} {w : Fin m}
    {R : Rec n m} (h : (invalidate sel σ).get w = some R) :
    ∃ R0, σ.get w = some R0 ∧ R.tgt = R0.tgt ∧ R.mu = R0.mu ∧ R.tag = R0.tag ∧
      (R.valid = true → R = R0) := by
  obtain ⟨R0, h0, hR⟩ := get_invalidate_some h
  refine ⟨R0, h0, ?_, ?_, ?_, ?_⟩ <;> subst hR <;> split <;> simp_all

theorem ite_t {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_f {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

/-! ## Invariant components -/

/-- Every record carries the source and mutability of the loan that created it, and its holder's
type is the record's mutability over its target's type. -/
def WF (p : Prog n m) (σ : RState n m) : Prop :=
  ∀ w R, σ.get w = some R → loanOf p R.tag = some (R.tgt, R.mu) ∧ p.ty w = R.mu :: p.ty R.tgt

/-- A valid mutable record excludes valid records of other tags on its target. -/
def Uniq (σ : RState n m) : Prop :=
  ∀ w₁ w₂ (R₁ R₂ : Rec n m), σ.get w₁ = some R₁ → σ.get w₂ = some R₂ → R₁.valid = true →
    R₂.valid = true → R₁.tgt = R₂.tgt → R₁.mu = .mut → R₂.tag = R₁.tag

/-- Every valid record of `σ'` is held, unchanged, by some local in `σ`. -/
def ValidFrom (σ' σ : RState n m) : Prop :=
  ∀ w (R : Rec n m), σ'.get w = some R → R.valid = true → ∃ w', σ.get w' = some R

theorem uniq_of_validFrom {σ' σ : RState n m} (hU : Uniq σ) (h : ValidFrom σ' σ) : Uniq σ' := by
  intro w₁ w₂ R₁ R₂ h₁ h₂ hv₁ hv₂ ht hm
  obtain ⟨w₁', h₁'⟩ := h w₁ R₁ h₁ hv₁
  obtain ⟨w₂', h₂'⟩ := h w₂ R₂ h₂ hv₂
  exact hU w₁' w₂' R₁ R₂ h₁' h₂' hv₁ hv₂ ht hm

theorem validFrom_refl (σ : RState n m) : ValidFrom σ σ := fun w _ h _ => ⟨w, h⟩

theorem validFrom_trans {σ'' σ' σ : RState n m} (h₁ : ValidFrom σ'' σ') (h₂ : ValidFrom σ' σ) :
    ValidFrom σ'' σ := by
  intro w R h hv
  obtain ⟨w', h'⟩ := h₁ w R h hv
  exact h₂ w' R h' hv

theorem validFrom_invalidate (sel : Rec n m → Bool) (σ : RState n m) :
    ValidFrom (invalidate sel σ) σ := by
  intro w R h hv
  obtain ⟨R0, h0, -, -, -, he⟩ := fields_of_get_invalidate h
  exact ⟨w, by rw [h0, he hv]⟩

theorem validFrom_set {σ' σ : RState n m} {v : Fin m} {x : Option (Rec n m)}
    (hl : σ'.length = m)
    (h : ValidFrom σ' σ) (hx : ∀ R, x = some R → R.valid = true → ∃ w', σ.get w' = some R) :
    ValidFrom (σ'.set v x) σ := by
  intro w R hw hv
  by_cases hwv : w = v
  · subst hwv
    rw [get_set_self _ _ _ hl] at hw
    exact hx R hw hv
  · rw [get_set_ne _ _ hwv] at hw
    exact h w R hw hv

theorem wf_invalidate {p : Prog n m} {σ : RState n m} (sel : Rec n m → Bool) (h : WF p σ) :
    WF p (invalidate sel σ) := by
  intro w R hw
  obtain ⟨R0, h0, ht, hm, hg, -⟩ := fields_of_get_invalidate hw
  rw [ht, hm, hg]
  exact h w R0 h0


theorem valid_invalidate {sel : Rec n m → Bool} {σ : RState n m} {w : Fin m} {R : Rec n m}
    (h : (invalidate sel σ).get w = some R) (hv : R.valid = true) :
    sel R = false ∧ σ.get w = some R := by
  obtain ⟨R0, h0, hR⟩ := get_invalidate_some h
  by_cases hs : sel R0 = true
  · simp only [hs, ↓reduceIte] at hR; subst hR; simp at hv
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hR; subst hR
    exact ⟨by simpa using hs, h0⟩

/-! ## The invariant -/

/-- The facts the invariant records about one local `w` holding the record `R`, for a
configuration about to execute node `q`. -/
def LocalOK (p : Prog n m) (q : Fin n) (w : Fin m) (R : Rec n m) : Prop :=
  R.valid = true ∧
  (∃ qp, q ∈ p.succ qp ∧ LS.Holds .overwrite .inv p R.tag (w, 0) qp) ∧
  (R.mu = .mut → LiveAt p R.tgt q → ∀ j, j < (p.ty R.tgt).length →
    (∃ qp, q ∈ p.succ qp ∧ LS.SubAt .inv p (w, j + 1) (R.tgt, j) qp) ∧
    (∃ qp, q ∈ p.succ qp ∧ LS.SubAt .inv p (R.tgt, j) (w, j + 1) qp))

/-- The invariant at a configuration (node `q` about to execute, state `σ`). -/
structure Inv (p : Prog n m) (q : Fin n) (σ : RState n m) : Prop where
  len : σ.length = m
  wf : WF p σ
  uniq : Uniq σ
  live : ∀ w R, σ.get w = some R → LiveAt p w q → LocalOK p q w R

theorem inv_init (p : Prog n m) : Inv p p.entry RState.init where
  len := length_init
  wf := fun w R h => by rw [get_init] at h; cases h
  uniq := fun w₁ _ R₁ _ h₁ => by rw [get_init] at h₁; cases h₁
  live := fun w R h => by rw [get_init] at h; cases h

/-! ## Basic facts -/

theorem tgt_ne_self {p : Prog n m} {σ : RState n m} (hwf : WF p σ) {w : Fin m} {R : Rec n m}
    (h : σ.get w = some R) : R.tgt ≠ w := by
  intro he
  have h2 := congrArg List.length (hwf w R h).2
  rw [he] at h2
  simp at h2

theorem no_conflict {p : Prog n m} {q : Fin n} {σ : RState n m} (hacc : LSAccepts p)
    (hI : Inv p q σ) {w : Fin m} {R : Rec n m} (h : σ.get w = some R) (hl : LiveAt p w q) :
    ¬ Conflicts p R.tag q := by
  intro hc
  obtain ⟨-, ⟨qp, hq, hh⟩, -⟩ := hI.live w R h hl
  exact hacc R.tag q hc ⟨(w, 0), qp, hh, hq, hl⟩

theorem placeWrite_sel {p : Prog n m} {q : Fin n} {t : Fin m} {R : Rec n m}
    (hlo : loanOf p R.tag = some (R.tgt, R.mu)) (ht : (t, Acc.wr) ∈ (p.stmt q).accesses)
    (hnc : ¬ Conflicts p R.tag q) : (R.tgt == t) = false := by
  cases h : (R.tgt == t)
  · rfl
  · exfalso
    have he : R.tgt = t := by simpa using h
    exact hnc ⟨R.tgt, R.mu, .wr, hlo, he ▸ ht, .inl rfl⟩

theorem placeRead_sel {p : Prog n m} {q : Fin n} {t : Fin m} {R : Rec n m}
    (hlo : loanOf p R.tag = some (R.tgt, R.mu)) (ht : (t, Acc.rd) ∈ (p.stmt q).accesses)
    (hnc : ¬ Conflicts p R.tag q) : (R.tgt == t && R.mu == .mut) = false := by
  cases h : (R.tgt == t && R.mu == .mut)
  · rfl
  · exfalso
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨he, hm⟩ := h
    exact hnc ⟨R.tgt, R.mu, .rd, hlo, he ▸ ht, .inr hm⟩

theorem thruWrite_sel {σ : RState n m} (hU : Uniq σ) {v w : Fin m} {R R' : Rec n m}
    (hR : σ.get v = some R) (hRv : R.valid = true) (hRm : R.mu = .mut)
    (hR' : σ.get w = some R') (hR'v : R'.valid = true) :
    (R'.tgt == R.tgt && R'.tag != R.tag) = false := by
  cases h : (R'.tgt == R.tgt)
  · rfl
  · have he : R'.tgt = R.tgt := by simpa using h
    have := hU v w R R' hR hR' hRv hR'v he.symm hRm
    simp [this]

theorem thruRead_sel {σ : RState n m} (hU : Uniq σ) {v w : Fin m} {R R' : Rec n m}
    (hR : σ.get v = some R) (hRv : R.valid = true)
    (hR' : σ.get w = some R') (hR'v : R'.valid = true) :
    (R'.tgt == R.tgt && R'.mu == .mut && R'.tag != R.tag) = false := by
  cases h : (R'.tgt == R.tgt && R'.mu == .mut)
  · rfl
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    have := hU w v R' R hR' hR hR'v hRv h.1 h.2
    simp [this]

theorem defs_wr (s : Stmt m) {t : Fin m} (h : t ∈ s.defs) : (t, Acc.wr) ∈ s.accesses := by
  cases s with
  | borrow mu d s => cases mu <;> simp_all [Stmt.defs, Stmt.accesses]
  | copy d s => simp_all [Stmt.defs, Stmt.accesses]
  | _ => simp [Stmt.defs] at h

theorem killsAt_false {p : Prog n m} {q : Fin n} {w : Fin m}
    (h : w ∉ (p.stmt q).defs ∨ w ∈ (p.stmt q).uses) : killsAt .overwrite p q w = false := by
  rcases h with h | h <;> simp [killsAt, h]

theorem invariantAt_inv_mut (T : List Mutbl) (j : Nat) :
    invariantAt .inv (.mut :: T) (j + 1) = true := by
  simp [invariantAt]

theorem mem_gen_borrow {p : Prog n m} {q : Fin n} {d s : Fin m}
    (hst : p.stmt q = .borrow .mut d s) {j : Nat} (hj : j < (p.ty s).length) :
    ((s, j), (d, j + 1)) ∈ gen .inv p q ∧ ((d, j + 1), (s, j)) ∈ gen .inv p q := by
  unfold gen
  rw [hst]
  simp only [List.mem_flatMap, List.mem_range]
  have hinv := invariantAt_inv_mut (p.ty s) j
  refine ⟨⟨j, hj, ?_⟩, ⟨j, hj, ?_⟩⟩ <;> rw [hinv] <;> simp

theorem mem_relate_zero {vm : VarMode} {T : List Mutbl} {a b : Fin m} {da db : Nat}
    (hT : T ≠ []) : ((a, da), (b, db)) ∈ relate vm T a da b db := by
  unfold relate
  simp only [List.mem_flatMap, List.mem_range]
  refine ⟨0, ?_, ?_⟩
  · cases T with
    | nil => exact absurd rfl hT
    | cons _ _ => simp
  · split <;> simp

theorem mem_relate_mut {T : List Mutbl} {a b : Fin m} {da db j : Nat}
    (hj : j < T.length) :
    ((a, j + 1 + da), (b, j + 1 + db)) ∈ relate .inv (.mut :: T) a da b db ∧
    ((b, j + 1 + db), (a, j + 1 + da)) ∈ relate .inv (.mut :: T) a da b db := by
  unfold relate
  simp only [List.mem_flatMap, List.mem_range]
  have hinv := invariantAt_inv_mut T j
  refine ⟨⟨j + 1, by simp; omega, ?_⟩, ⟨j + 1, by simp; omega, ?_⟩⟩ <;> rw [hinv] <;> simp


/-! ## Assembling the invariant after one step -/

/-- A local that the step at `q` does not write keeps its record and its facts. -/
theorem frame_local {p : Prog n m} {q q'' : Fin n} {σ σ' : RState n m}
    (hacc : LSAccepts p) (hI : Inv p q σ) (hq'' : q'' ∈ p.succ q)
    {w : Fin m} (hwd : w ∉ (p.stmt q).defs) (hframe : σ'.get w = σ.get w)
    {R : Rec n m} (hR : σ'.get w = some R) (hl : LiveAt p w q'') : LocalOK p q'' w R := by
  have hlq : LiveAt p w q := .step hwd hq'' hl
  have hσ : σ.get w = some R := hframe ▸ hR
  obtain ⟨hv, ⟨qp, hq, hh⟩, hsub⟩ := hI.live w R hσ hlq
  refine ⟨hv, ⟨q, hq'', .carry hh hq (killsAt_false (.inl hwd))⟩, ?_⟩
  intro hm htl j hj
  have htq : LiveAt p R.tgt q := by
    by_cases ht : R.tgt ∈ (p.stmt q).defs
    · exfalso
      exact no_conflict hacc hI hσ hlq
        ⟨R.tgt, R.mu, .wr, (hI.wf w R hσ).1, defs_wr _ ht, .inl rfl⟩
    · exact .step ht hq'' htl
  obtain ⟨⟨qa, hqa, ha⟩, ⟨qb, hqb, hb⟩⟩ := hsub hm htq j hj
  exact ⟨⟨q, hq'', .persist ha hqa hlq htq⟩, ⟨q, hq'', .persist hb hqb htq hlq⟩⟩

/-- The invariant after a step, from its global parts, a frame condition for the locals the
step does not write, and the local facts for the locals it writes. -/
theorem inv_of_parts {p : Prog n m} {q q'' : Fin n} {σ σ' : RState n m}
    (hacc : LSAccepts p) (hI : Inv p q σ) (hq'' : q'' ∈ p.succ q)
    (hlen : σ'.length = m) (hwf : WF p σ') (hU : Uniq σ')
    (W : Fin m → Prop) (hWd : ∀ w, w ∈ (p.stmt q).defs → W w)
    (hframe : ∀ w, ¬ W w → LiveAt p w q → σ'.get w = σ.get w)
    (hW : ∀ w R, W w → σ'.get w = some R → LiveAt p w q'' → LocalOK p q'' w R) :
    Inv p q'' σ' where
  len := hlen
  wf := hwf
  uniq := hU
  live := by
    intro w R hR hl
    by_cases hw : W w
    · exact hW w R hw hR hl
    · have hwd : w ∉ (p.stmt q).defs := fun h => hw (hWd w h)
      exact frame_local hacc hI hq'' hwd (hframe w hw (.step hwd hq'' hl)) hR hl

/-- A live local's record survives an invalidation whose selector it does not satisfy. -/
theorem keep_of_sel {sel : Rec n m → Bool} {σ : RState n m} {w : Fin m}
    (hs : ∀ R, σ.get w = some R → sel R = false) : (invalidate sel σ).get w = σ.get w := by
  cases h : σ.get w with
  | none => exact get_invalidate_none h
  | some R => exact get_invalidate_keep h (hs R h)


theorem keep_placeWrite {p : Prog n m} {q : Fin n} {σ σ0 : RState n m} (hacc : LSAccepts p)
    (hI : Inv p q σ) {t : Fin m} (ht : (t, Acc.wr) ∈ (p.stmt q).accesses) {w : Fin m}
    (hl : LiveAt p w q) (h0 : σ0.get w = σ.get w) : (placeWrite t σ0).get w = σ.get w := by
  rw [← h0]
  exact keep_of_sel fun R h =>
    placeWrite_sel (hI.wf w R (h0 ▸ h)).1 ht (no_conflict hacc hI (h0 ▸ h) hl)

theorem keep_placeRead {p : Prog n m} {q : Fin n} {σ σ0 : RState n m} (hacc : LSAccepts p)
    (hI : Inv p q σ) {t : Fin m} (ht : (t, Acc.rd) ∈ (p.stmt q).accesses) {w : Fin m}
    (hl : LiveAt p w q) (h0 : σ0.get w = σ.get w) : (placeRead t σ0).get w = σ.get w := by
  rw [← h0]
  exact keep_of_sel fun R h =>
    placeRead_sel (hI.wf w R (h0 ▸ h)).1 ht (no_conflict hacc hI (h0 ▸ h) hl)

theorem keep_thruWrite {p : Prog n m} {q : Fin n} {σ σ0 : RState n m}
    (hI : Inv p q σ) (hU : Uniq σ0) {v : Fin m} {R : Rec n m} (hR : σ0.get v = some R)
    (hRv : R.valid = true) (hRm : R.mu = .mut) {w : Fin m}
    (hl : LiveAt p w q) (h0 : σ0.get w = σ.get w) : (thruWrite R σ0).get w = σ.get w := by
  rw [← h0]
  exact keep_of_sel fun R' h =>
    thruWrite_sel hU hR hRv hRm h (hI.live w R' (h0 ▸ h) hl).1

theorem keep_thruRead {p : Prog n m} {q : Fin n} {σ σ0 : RState n m}
    (hI : Inv p q σ) (hU : Uniq σ0) {v : Fin m} {R : Rec n m} (hR : σ0.get v = some R)
    (hRv : R.valid = true) {w : Fin m}
    (hl : LiveAt p w q) (h0 : σ0.get w = σ.get w) : (thruRead R σ0).get w = σ.get w := by
  rw [← h0]
  exact keep_of_sel fun R' h =>
    thruRead_sel hU hR hRv h (hI.live w R' (h0 ▸ h) hl).1

theorem len_placeWrite {σ : RState n m} {t : Fin m} (h : σ.length = m) :
    (placeWrite t σ).length = m := by rw [placeWrite, length_invalidate]; exact h
theorem len_placeRead {σ : RState n m} {t : Fin m} (h : σ.length = m) :
    (placeRead t σ).length = m := by rw [placeRead, length_invalidate]; exact h
theorem len_thruWrite {σ : RState n m} {R : Rec n m} (h : σ.length = m) :
    (thruWrite R σ).length = m := by rw [thruWrite, length_invalidate]; exact h
theorem len_thruRead {σ : RState n m} {R : Rec n m} (h : σ.length = m) :
    (thruRead R σ).length = m := by rw [thruRead, length_invalidate]; exact h

/-! ## Steps that write no local -/

theorem no_defs {p : Prog n m} {q : Fin n} (h : (p.stmt q).defs = []) :
    ∀ w, w ∈ (p.stmt q).defs → False := by
  intro w hw; rw [h] at hw; simp at hw

theorem step_nop {p : Prog n m} {q q'' : Fin n} {σ : RState n m} (hacc : LSAccepts p)
    (hI : Inv p q σ) (hq'' : q'' ∈ p.succ q) (hst : p.stmt q = .nop) : Inv p q'' σ :=
  inv_of_parts hacc hI hq'' hI.len hI.wf hI.uniq (fun _ => False)
    (no_defs (by rw [hst]; rfl)) (fun _ _ _ => rfl) (fun _ _ h => h.elim)

theorem step_access_rd {p : Prog n m} {q q'' : Fin n} {σ : RState n m} (hacc : LSAccepts p)
    (hI : Inv p q σ) (hq'' : q'' ∈ p.succ q) {v : Fin m} (hst : p.stmt q = .access .rd v) :
    Inv p q'' (placeRead v σ) :=
  inv_of_parts hacc hI hq'' (len_placeRead hI.len) (wf_invalidate _ hI.wf)
    (uniq_of_validFrom hI.uniq (validFrom_invalidate _ _)) (fun _ => False)
    (no_defs (by rw [hst]; rfl))
    (fun _ _ hl => keep_placeRead hacc hI (by rw [hst]; simp [Stmt.accesses]) hl rfl)
    (fun _ _ h => h.elim)

theorem step_access_wr {p : Prog n m} {q q'' : Fin n} {σ : RState n m} (hacc : LSAccepts p)
    (hI : Inv p q σ) (hq'' : q'' ∈ p.succ q) {v : Fin m} (hst : p.stmt q = .access .wr v) :
    Inv p q'' (placeWrite v σ) :=
  inv_of_parts hacc hI hq'' (len_placeWrite hI.len) (wf_invalidate _ hI.wf)
    (uniq_of_validFrom hI.uniq (validFrom_invalidate _ _)) (fun _ => False)
    (no_defs (by rw [hst]; rfl))
    (fun _ _ hl => keep_placeWrite hacc hI (by rw [hst]; simp [Stmt.accesses]) hl rfl)
    (fun _ _ h => h.elim)

theorem step_deref_rd {p : Prog n m} {q q'' : Fin n} {σ : RState n m} (hacc : LSAccepts p)
    (hI : Inv p q σ) (hq'' : q'' ∈ p.succ q) {a : Acc} {v : Fin m}
    (hst : p.stmt q = .deref a v) {R : Rec n m} (hR : (placeRead v σ).get v = some R)
    (hRv : R.valid = true) : Inv p q'' (thruRead R (placeRead v σ)) := by
  have hU1 : Uniq (placeRead v σ) := uniq_of_validFrom hI.uniq (validFrom_invalidate _ _)
  exact inv_of_parts hacc hI hq'' (len_thruRead (len_placeRead hI.len))
    (wf_invalidate _ (wf_invalidate _ hI.wf))
    (uniq_of_validFrom hU1 (validFrom_invalidate _ _)) (fun _ => False)
    (no_defs (by rw [hst]; rfl))
    (fun _ _ hl => keep_thruRead hI hU1 hR hRv hl
      (keep_placeRead hacc hI (by rw [hst]; simp [Stmt.accesses]) hl rfl))
    (fun _ _ h => h.elim)

theorem step_deref_wr {p : Prog n m} {q q'' : Fin n} {σ : RState n m} (hacc : LSAccepts p)
    (hI : Inv p q σ) (hq'' : q'' ∈ p.succ q) {a : Acc} {v : Fin m}
    (hst : p.stmt q = .deref a v) {R : Rec n m} (hR : (placeRead v σ).get v = some R)
    (hRv : R.valid = true) (hRm : R.mu = .mut) : Inv p q'' (thruWrite R (placeRead v σ)) := by
  have hU1 : Uniq (placeRead v σ) := uniq_of_validFrom hI.uniq (validFrom_invalidate _ _)
  exact inv_of_parts hacc hI hq'' (len_thruWrite (len_placeRead hI.len))
    (wf_invalidate _ (wf_invalidate _ hI.wf))
    (uniq_of_validFrom hU1 (validFrom_invalidate _ _)) (fun _ => False)
    (no_defs (by rw [hst]; rfl))
    (fun _ _ hl => keep_thruWrite hI hU1 hR hRv hRm hl
      (keep_placeRead hacc hI (by rw [hst]; simp [Stmt.accesses]) hl rfl))
    (fun _ _ h => h.elim)


/-! ## Steps that write one local -/

theorem step_borrow {p : Prog n m} {q q'' : Fin n} {σ σ1 : RState n m} (hwt : WellTyped p)
    (hacc : LSAccepts p) (hI : Inv p q σ) (hq'' : q'' ∈ p.succ q) {mu : Mutbl} {d s : Fin m}
    (hst : p.stmt q = .borrow mu d s)
    (h1len : σ1.length = m) (h1wf : WF p σ1) (h1vf : ValidFrom σ1 σ)
    (h1frame : ∀ w, LiveAt p w q → σ1.get w = σ.get w)
    (h1s : ∀ w R, σ1.get w = some R → R.valid = true → R.tgt = s → mu = .shr ∧ R.mu = .shr) :
    Inv p q'' ((placeWrite d σ1).set d (some ⟨s, mu, q, true⟩)) := by
  have h2len : (placeWrite d σ1).length = m := len_placeWrite h1len
  have hget : ∀ w, (((placeWrite d σ1).set d (some ⟨s, mu, q, true⟩)).get w =
      if w = d then some ⟨s, mu, q, true⟩ else (placeWrite d σ1).get w) := by
    intro w
    by_cases hw : w = d
    · subst hw; rw [get_set_self _ _ _ h2len, ite_t rfl]
    · rw [get_set_ne _ _ hw, ite_f hw]
  have hty : p.ty d = mu :: p.ty s := by have := hwt q; rw [hst] at this; exact this
  have hlo : loanOf p q = some (s, mu) := by simp [loanOf, hst]
  refine inv_of_parts hacc hI hq'' (by rw [length_set]; exact h2len) ?_ ?_ (fun w => w = d)
    ?_ ?_ ?_
  · intro w R hR
    rw [hget] at hR
    by_cases hw : w = d
    · rw [ite_t hw] at hR; cases hR; subst hw; exact ⟨hlo, hty⟩
    · rw [ite_f hw] at hR; exact wf_invalidate _ h1wf w R hR
  · intro w₁ w₂ R₁ R₂ h₁ h₂ hv₁ hv₂ ht hm
    rw [hget] at h₁ h₂
    by_cases hw₁ : w₁ = d <;> by_cases hw₂ : w₂ = d
    · rw [ite_t hw₁] at h₁; rw [ite_t hw₂] at h₂; cases h₁; cases h₂; rfl
    · rw [ite_t hw₁] at h₁; rw [ite_f hw₂] at h₂; cases h₁
      obtain ⟨-, h₂'⟩ := valid_invalidate h₂ hv₂
      have := h1s w₂ R₂ h₂' hv₂ ht.symm
      simp at hm; rw [hm] at this; cases this.1
    · rw [ite_f hw₁] at h₁; rw [ite_t hw₂] at h₂; cases h₂
      obtain ⟨-, h₁'⟩ := valid_invalidate h₁ hv₁
      have := h1s w₁ R₁ h₁' hv₁ ht
      rw [hm] at this; cases this.2
    · rw [ite_f hw₁] at h₁; rw [ite_f hw₂] at h₂
      obtain ⟨-, h₁'⟩ := valid_invalidate h₁ hv₁
      obtain ⟨-, h₂'⟩ := valid_invalidate h₂ hv₂
      obtain ⟨w₁', h₁''⟩ := h1vf w₁ R₁ h₁' hv₁
      obtain ⟨w₂', h₂''⟩ := h1vf w₂ R₂ h₂' hv₂
      exact hI.uniq w₁' w₂' R₁ R₂ h₁'' h₂'' hv₁ hv₂ ht hm
  · intro w hw; rw [hst] at hw; simpa [Stmt.defs] using hw
  · intro w hw hl
    rw [hget, ite_f hw]
    exact keep_placeWrite hacc hI (by rw [hst]; cases mu <;> simp [Stmt.accesses]) hl
      (h1frame w hl)
  · intro w R hw hR hl
    subst hw
    rw [hget, ite_t rfl] at hR
    cases hR
    refine ⟨rfl, ⟨q, hq'', .intro hst⟩, ?_⟩
    intro hm _ j hj
    simp only at hm
    subst hm
    have hg := mem_gen_borrow hst hj
    exact ⟨⟨q, hq'', .base hg.2⟩, ⟨q, hq'', .base hg.1⟩⟩

theorem step_copy {p : Prog n m} {q q'' : Fin n} {σ : RState n m} (hwt : WellTyped p)
    (hacc : LSAccepts p) (hI : Inv p q σ) (hq'' : q'' ∈ p.succ q) {d s : Fin m}
    (hst : p.stmt q = .copy d s) :
    Inv p q'' ((placeWrite d (placeRead s σ)).set d ((placeRead s σ).get s)) := by
  have hs1 : (placeRead s σ).get s = σ.get s :=
    keep_of_sel fun R h => by have := tgt_ne_self hI.wf h; simp [this]
  have h2len : (placeWrite d (placeRead s σ)).length = m := len_placeWrite (len_placeRead hI.len)
  have hget : ∀ w, (((placeWrite d (placeRead s σ)).set d ((placeRead s σ).get s)).get w =
      if w = d then σ.get s else (placeWrite d (placeRead s σ)).get w) := by
    intro w
    by_cases hw : w = d
    · subst hw; rw [get_set_self _ _ _ h2len, ite_t rfl, hs1]
    · rw [get_set_ne _ _ hw, ite_f hw]
  have hty : p.ty d = p.ty s ∧ p.ty s ≠ [] := by have := hwt q; rw [hst] at this; exact this
  have hls : LiveAt p s q := .use (by rw [hst]; simp [Stmt.uses])
  refine inv_of_parts hacc hI hq'' (by rw [length_set]; exact h2len) ?_ ?_ (fun w => w = d)
    ?_ ?_ ?_
  · intro w R hR
    rw [hget] at hR
    by_cases hw : w = d
    · rw [ite_t hw] at hR; subst hw
      obtain ⟨h1, h2⟩ := hI.wf s R hR
      exact ⟨h1, hty.1.trans h2⟩
    · rw [ite_f hw] at hR; exact wf_invalidate _ (wf_invalidate _ hI.wf) w R hR
  · apply uniq_of_validFrom hI.uniq
    apply validFrom_set h2len
      (validFrom_trans (validFrom_invalidate _ _) (validFrom_invalidate _ _))
    intro R hx _
    exact ⟨s, hs1 ▸ hx⟩
  · intro w hw; rw [hst] at hw; simpa [Stmt.defs] using hw
  · intro w hw hl
    rw [hget, ite_f hw]
    exact keep_placeWrite hacc hI (by rw [hst]; simp [Stmt.accesses]) hl
      (keep_placeRead hacc hI (by rw [hst]; simp [Stmt.accesses]) hl rfl)
  · intro w R hw hR hl
    subst hw
    rw [hget, ite_t rfl] at hR
    obtain ⟨hv, ⟨qp, hq, hh⟩, hsub⟩ := hI.live s R hR hls
    refine ⟨hv, ?_, ?_⟩
    · by_cases hsd : s = w
      · subst hsd
        exact ⟨q, hq'', .carry hh hq (killsAt_false (.inr (by rw [hst]; simp [Stmt.uses])))⟩
      · refine ⟨q, hq'', .step hh hq ?_ ?_⟩
        · unfold gen; rw [hst]; exact mem_relate_zero hty.2
        · rw [hst]; simpa [Stmt.defs] using hsd
    · intro hm htl j hj
      have hwfs := (hI.wf s R hR).2
      rw [hm] at hwfs
      have htw : R.tgt ≠ w := by
        intro he
        have h3 := congrArg List.length (hty.1.trans hwfs)
        rw [he] at h3; simp at h3
      have htq : LiveAt p R.tgt q :=
        .step (by rw [hst]; simpa [Stmt.defs] using htw) hq'' htl
      obtain ⟨⟨qa, hqa, ha⟩, ⟨qb, hqb, hb⟩⟩ := hsub hm htq j hj
      have SA := LS.SubAt.persist ha hqa hls htq
      have SB := LS.SubAt.persist hb hqb htq hls
      by_cases hsd : s = w
      · subst hsd; exact ⟨⟨q, hq'', SA⟩, ⟨q, hq'', SB⟩⟩
      · have G : ((s, j + 1), (w, j + 1)) ∈ gen .inv p q ∧
            ((w, j + 1), (s, j + 1)) ∈ gen .inv p q := by
          have hgen : gen .inv p q = relate .inv (p.ty s) s 0 w 0 := by unfold gen; rw [hst]
          rw [hgen, hwfs]; exact mem_relate_mut hj
        exact ⟨⟨q, hq'', .trans (.base G.2) SA⟩, ⟨q, hq'', .trans SB (.base G.1)⟩⟩


theorem step_store {p : Prog n m} {q q'' : Fin n} {σ : RState n m} (hwt : WellTyped p)
    (hacc : LSAccepts p) (hI : Inv p q σ) (hq'' : q'' ∈ p.succ q) {q' s : Fin m}
    (hst : p.stmt q = .store q' s) {R : Rec n m}
    (hR : (placeRead s (placeRead q' σ)).get q' = some R) (hRv : R.valid = true)
    (hRm : R.mu = .mut) :
    Inv p q'' ((thruWrite R (placeRead s (placeRead q' σ))).set R.tgt
      ((placeRead s (placeRead q' σ)).get s)) := by
  have hq'l : LiveAt p q' q := .use (by rw [hst]; simp [Stmt.uses])
  have hsl : LiveAt p s q := .use (by rw [hst]; simp [Stmt.uses])
  have hnd : ∀ w, w ∉ (p.stmt q).defs := by intro w; rw [hst]; simp [Stmt.defs]
  have hRσ : σ.get q' = some R := by
    obtain ⟨-, h1⟩ := valid_invalidate hR hRv
    exact (valid_invalidate h1 hRv).2
  have htyq : p.ty q' = .mut :: p.ty s := by have := hwt q; rw [hst] at this; exact this
  have hc : p.ty R.tgt = p.ty s := by
    have h := (hI.wf q' R hRσ).2
    rw [hRm, htyq] at h
    exact (List.cons.inj h).2.symm
  have hs1 : (placeRead s (placeRead q' σ)).get s = σ.get s := by
    have hne : ∀ R', σ.get s = some R' → R'.tgt ≠ s ∧ R'.tgt ≠ q' := by
      intro R' h
      refine ⟨tgt_ne_self hI.wf h, fun he => ?_⟩
      have h2 := (hI.wf s R' h).2
      rw [he, htyq] at h2
      have h3 := congrArg List.length h2
      simp at h3; omega
    have h0 : (placeRead q' σ).get s = σ.get s :=
      keep_of_sel fun R' h => by simp [(hne R' h).2]
    rw [← h0]
    exact keep_of_sel fun R' h => by rw [h0] at h; simp [(hne R' h).1]
  have hU1 : Uniq (placeRead s (placeRead q' σ)) :=
    uniq_of_validFrom hI.uniq
      (validFrom_trans (validFrom_invalidate _ _) (validFrom_invalidate _ _))
  have h2len : (thruWrite R (placeRead s (placeRead q' σ))).length = m :=
    len_thruWrite (len_placeRead (len_placeRead hI.len))
  have hget : ∀ w, (((thruWrite R (placeRead s (placeRead q' σ))).set R.tgt
      ((placeRead s (placeRead q' σ)).get s)).get w =
      if w = R.tgt then σ.get s else (thruWrite R (placeRead s (placeRead q' σ))).get w) := by
    intro w
    by_cases hw : w = R.tgt
    · subst hw; rw [get_set_self _ _ _ h2len, ite_t rfl, hs1]
    · rw [get_set_ne _ _ hw, ite_f hw]
  refine inv_of_parts hacc hI hq'' (by rw [length_set]; exact h2len) ?_ ?_ (fun w => w = R.tgt)
    (fun w h => absurd h (hnd w)) ?_ ?_
  · intro w R' hR'
    rw [hget] at hR'
    by_cases hw : w = R.tgt
    · rw [ite_t hw] at hR'; subst hw
      obtain ⟨h1, h2⟩ := hI.wf s R' hR'
      exact ⟨h1, hc.trans h2⟩
    · rw [ite_f hw] at hR'
      exact wf_invalidate _ (wf_invalidate _ (wf_invalidate _ hI.wf)) w R' hR'
  · apply uniq_of_validFrom hI.uniq
    apply validFrom_set h2len
      (validFrom_trans (validFrom_invalidate _ _)
        (validFrom_trans (validFrom_invalidate _ _) (validFrom_invalidate _ _)))
    intro R' hx _
    exact ⟨s, hs1 ▸ hx⟩
  · intro w hw hl
    rw [hget, ite_f hw]
    exact keep_thruWrite hI hU1 hR hRv hRm hl
      (keep_placeRead hacc hI (by rw [hst]; simp [Stmt.accesses]) hl
        (keep_placeRead hacc hI (by rw [hst]; simp [Stmt.accesses]) hl rfl))
  · intro w R' hw hR' hl
    subst hw
    rw [hget, ite_t rfl] at hR'
    have hcl : LiveAt p R.tgt q := .step (hnd _) hq'' hl
    obtain ⟨hv, ⟨qp, hq, hh⟩, hsub⟩ := hI.live s R' hR' hsl
    obtain ⟨-, -, hsubq⟩ := hI.live q' R hRσ hq'l
    have hwfs := (hI.wf s R' hR').2
    refine ⟨hv, ?_, ?_⟩
    · have G0 : ((s, 0), (q', 1)) ∈ gen .inv p q := by
        have hgen : gen .inv p q = relate .inv (p.ty s) s 0 q' 1 := by unfold gen; rw [hst]
        rw [hgen]; exact mem_relate_zero (by rw [hwfs]; simp)
      have H1 := LS.Holds.step hh hq G0 (hnd s)
      have hlen0 : 0 < (p.ty R.tgt).length := by rw [hc, hwfs]; simp
      obtain ⟨⟨qa, hqa, ha⟩, -⟩ := hsubq hRm hcl 0 hlen0
      exact ⟨q, hq'', .sub H1 (.persist ha hqa hq'l hcl)⟩
    · intro hm htl j hj
      have heq : LiveAt p R'.tgt q := .step (hnd _) hq'' htl
      rw [hm] at hwfs
      obtain ⟨⟨qa, hqa, ha⟩, ⟨qb, hqb, hb⟩⟩ := hsub hm heq j hj
      have A1 := LS.SubAt.persist ha hqa hsl heq
      have A2 := LS.SubAt.persist hb hqb heq hsl
      have B : ((s, j + 1), (q', j + 1 + 1)) ∈ gen .inv p q ∧
          ((q', j + 1 + 1), (s, j + 1)) ∈ gen .inv p q := by
        have hgen : gen .inv p q = relate .inv (p.ty s) s 0 q' 1 := by unfold gen; rw [hst]
        rw [hgen, hwfs]; exact mem_relate_mut hj
      have hj' : j + 1 < (p.ty R.tgt).length := by rw [hc, hwfs]; simp; omega
      obtain ⟨⟨qc, hqc, hc1⟩, ⟨qd, hqd, hd1⟩⟩ := hsubq hRm hcl (j + 1) hj'
      have C1 := LS.SubAt.persist hc1 hqc hq'l hcl
      have C2 := LS.SubAt.persist hd1 hqd hcl hq'l
      exact ⟨⟨q, hq'', .trans C2 (.trans (.base B.2) A1)⟩,
        ⟨q, hq'', .trans A2 (.trans (.base B.1) C1)⟩⟩


/-! ## One step of `exec` preserves the invariant and never reaches UB -/

theorem step_inv {p : Prog n m} {q q'' : Fin n} {σ σ' : RState n m} (hwt : WellTyped p)
    (hacc : LSAccepts p) (hI : Inv p q σ) (hex : exec p q σ = .ok σ')
    (hq'' : q'' ∈ p.succ q) : Inv p q'' σ' := by
  unfold exec at hex
  split at hex
  · rename_i hst; cases hex; exact step_nop hacc hI hq'' hst
  · rename_i mu d s hst
    cases hex
    cases mu
    · refine step_borrow hwt hacc hI hq'' hst (len_placeRead hI.len) (wf_invalidate _ hI.wf)
        (validFrom_invalidate _ _)
        (fun w hl => keep_placeRead hacc hI (by rw [hst]; simp [Stmt.accesses]) hl rfl) ?_
      intro w R h hv ht
      obtain ⟨hs, -⟩ := valid_invalidate h hv
      simp only [ht, beq_self_eq_true, Bool.true_and, beq_eq_false_iff_ne, ne_eq] at hs
      exact ⟨rfl, by cases hR : R.mu <;> simp_all⟩
    · refine step_borrow hwt hacc hI hq'' hst (len_placeWrite hI.len) (wf_invalidate _ hI.wf)
        (validFrom_invalidate _ _)
        (fun w hl => keep_placeWrite hacc hI (by rw [hst]; simp [Stmt.accesses]) hl rfl) ?_
      intro w R h hv ht
      obtain ⟨hs, -⟩ := valid_invalidate h hv
      simp [ht] at hs
  · rename_i d s hst; cases hex; exact step_copy hwt hacc hI hq'' hst
  · rename_i a v hst
    dsimp only at hex
    split at hex
    · cases hex
    · rename_i R hR
      split at hex
      · cases hex
      · rename_i hRv
        have hRv' : R.valid = true := by simpa using hRv
        split at hex
        · cases hex; exact step_deref_rd hacc hI hq'' hst hR hRv'
        · rename_i hm; cases hex; exact step_deref_wr hacc hI hq'' hst hR hRv' hm
        · cases hex
  · rename_i a v hst
    cases a
    · cases hex; exact step_access_rd hacc hI hq'' hst
    · cases hex; exact step_access_wr hacc hI hq'' hst
  · rename_i q' s hst
    dsimp only at hex
    split at hex
    · cases hex
    · rename_i R hR
      split at hex
      · cases hex
      · rename_i hRv
        have hRv' : R.valid = true := by simpa using hRv
        split at hex
        · cases hex
        · rename_i hm; cases hex; exact step_store hwt hacc hI hq'' hst hR hRv' hm
  · dsimp only at hex
    split at hex
    · cases hex
    · split at hex <;> cases hex

theorem exec_ne_ub {p : Prog n m} {q : Fin n} {σ : RState n m}
    (hacc : LSAccepts p) (hI : Inv p q σ) : exec p q σ ≠ .ub := by
  intro hex
  unfold exec at hex
  split at hex
  · cases hex
  · cases hex
  · cases hex
  · rename_i a v hst
    have hl : LiveAt p v q := .use (by rw [hst]; simp [Stmt.uses])
    have hk := keep_placeRead (t := v) hacc hI (by rw [hst]; simp [Stmt.accesses]) hl rfl
    dsimp only at hex
    split at hex
    · cases hex
    · rename_i R hR
      rw [hk] at hR
      have hv := (hI.live v R hR hl).1
      split at hex
      · rename_i hRv; simp [hv] at hRv
      · split at hex <;> cases hex
  · rename_i a v hst; cases a <;> cases hex
  · rename_i q' s hst
    have hl : LiveAt p q' q := .use (by rw [hst]; simp [Stmt.uses])
    have hk := keep_placeRead (t := s) hacc hI (by rw [hst]; simp [Stmt.accesses]) hl
      (keep_placeRead (t := q') hacc hI (by rw [hst]; simp [Stmt.accesses]) hl rfl)
    dsimp only at hex
    split at hex
    · cases hex
    · rename_i R hR
      rw [hk] at hR
      have hv := (hI.live q' R hR hl).1
      split at hex
      · rename_i hRv; simp [hv] at hRv
      · split at hex <;> cases hex
  · rename_i v hst
    have hl : LiveAt p v q := .use (by rw [hst]; simp [Stmt.uses])
    have hk := keep_placeRead (t := v) hacc hI (by rw [hst]; simp [Stmt.accesses]) hl rfl
    dsimp only at hex
    split at hex
    · cases hex
    · rename_i R hR
      rw [hk] at hR
      have hv := (hI.live v R hR hl).1
      split at hex
      · rename_i hRv; simp [hv] at hRv
      · cases hex

theorem run_not_ub {p : Prog n m} (hwt : WellTyped p) (hacc : LSAccepts p) :
    ∀ (π : List (Fin n)) (x : Fin n) (σ : RState n m), IsWalk p.succ (x :: π) →
      Inv p x σ → (run p σ (x :: π)).isUB = false := by
  intro π
  induction π with
  | nil =>
    intro x σ _ hI
    have hne := exec_ne_ub hacc hI
    simp only [run]
    cases h : exec p x σ with
    | ok σ' => rfl
    | halt => rfl
    | ub => exact absurd h hne
  | cons y t ih =>
    intro x σ hw hI
    have hne := exec_ne_ub hacc hI
    simp only [run]
    cases h : exec p x σ with
    | ok σ' => exact ih y σ' hw.2 (step_inv hwt hacc hI h hw.1)
    | halt => rfl
    | ub => exact absurd h hne

end Sound

end Toy.LoanFlow
