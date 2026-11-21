import ToyTbaa.Semantics

/-!
# Proof infrastructure

Generic facts about executions and block replacement, about `readRange`/`updRange`, and
one-step characterizations of the two semantics. Nothing here is a result card; everything is
fully proved.
-/

namespace Toy.Tbaa
namespace Lemmas

/-! ## Executions and block replacement -/

/-- Running `P ++ Q` runs `P` and then, if `P` did not fault, runs `Q`. -/
theorem runFrom_append {S : Type} (step : Instr → S → Step S) :
    ∀ (P Q : List Instr) (s : S) (t : List Val),
      runFrom step (P ++ Q) s t =
        match runFrom step P s t with
        | .ok s' t' => runFrom step Q s' t'
        | .fault k t' => .fault k t'
  | [], _, _, _ => rfl
  | i :: P, Q, s, t => by
    simp only [List.cons_append, runFrom]
    cases step i s with
    | next s' => exact runFrom_append step P Q s' t
    | emit v s' => exact runFrom_append step P Q s' (t ++ [v])
    | fault _ => rfl

theorem runFrom_cons_next {S : Type} {step : Instr → S → Step S} {i : Instr} {s s' : S}
    (h : step i s = .next s') (P : List Instr) (t : List Val) :
    runFrom step (i :: P) s t = runFrom step P s' t := by
  simp only [runFrom, h]

theorem runFrom_cons_emit {S : Type} {step : Instr → S → Step S} {i : Instr} {s s' : S} {v : Val}
    (h : step i s = .emit v s') (P : List Instr) (t : List Val) :
    runFrom step (i :: P) s t = runFrom step P s' (t ++ [v]) := by
  simp only [runFrom, h]

theorem runFrom_cons_fault {S : Type} {step : Instr → S → Step S} {i : Instr} {s : S} {k : Fault}
    (h : step i s = .fault k) (P : List Instr) (t : List Val) :
    runFrom step (i :: P) s t = .fault k t := by
  simp only [runFrom, h]

/-- Traces only grow. -/
theorem runFrom_trace_prefix {S : Type} (step : Instr → S → Step S) :
    ∀ (P : List Instr) (s : S) (t : List Val), t <+: (runFrom step P s t).outcome.trace
  | [], _, t => List.prefix_refl t
  | i :: P, s, t => by
    simp only [runFrom]
    cases step i s with
    | next s' => exact runFrom_trace_prefix step P s' t
    | emit v s' => exact List.IsPrefix.trans ⟨[v], rfl⟩ (runFrom_trace_prefix step P s' (t ++ [v]))
    | fault _ => exact List.prefix_refl t

/-- A state predicate preserved by every non-faulting step is preserved by every
non-faulting run. -/
theorem runFrom_inv {S : Type} {step : Instr → S → Step S} {Inv : S → Prop}
    (hstep : ∀ i s s', Inv s → (step i s = .next s' ∨ ∃ v, step i s = .emit v s') → Inv s') :
    ∀ (P : List Instr) (s s' : S) (t t' : List Val),
      Inv s → runFrom step P s t = .ok s' t' → Inv s'
  | [], s, s', t, t', hs, h => by
    simp only [runFrom, Final.ok.injEq] at h; exact h.1 ▸ hs
  | i :: P, s, s', t, t', hs, h => by
    simp only [runFrom] at h
    cases hi : step i s with
    | next s1 =>
      rw [hi] at h; exact runFrom_inv hstep P s1 s' t t' (hstep i s s1 hs (Or.inl hi)) h
    | emit v s1 =>
      rw [hi] at h
      exact runFrom_inv hstep P s1 s' (t ++ [v]) t' (hstep i s s1 hs (Or.inr ⟨v, hi⟩)) h
    | fault k => rw [hi] at h; cases h

/-- **Block lemma.** Let `Inv` be preserved by non-faulting steps and implied by `Pre`. If, from
every state satisfying `Inv`, the source block either faults without emitting or terminates
in a state from which the target block terminates identically, then replacing `src` by `tgt`
is sound from `Pre`. -/
theorem reorderSoundFrom_of_block {S : Type} {step : Instr → S → Step S} {Pre Inv : S → Prop}
    {src tgt : List Instr}
    (hpre : ∀ s, Pre s → Inv s)
    (hstep : ∀ i s s', Inv s → (step i s = .next s' ∨ ∃ v, step i s = .emit v s') → Inv s')
    (hblk : ∀ s t, Inv s →
      (∃ k, runFrom step src s t = .fault k t) ∨
      (∃ s', runFrom step src s t = .ok s' t ∧ runFrom step tgt s t = .ok s' t)) :
    ReorderSoundFrom Pre step src tgt := by
  intro pre post s0 hs0
  rw [refines_beh_iff]
  unfold exec
  rw [List.append_assoc, List.append_assoc, runFrom_append, runFrom_append]
  cases hp : runFrom step pre s0 [] with
  | fault k t => exact Allows.refl _
  | ok s1 t1 =>
    simp only
    rw [runFrom_append, runFrom_append]
    rcases hblk s1 t1 (runFrom_inv hstep pre s0 s1 [] t1 (hpre s0 hs0) hp) with
      ⟨k, hk⟩ | ⟨s2, h1, h2⟩
    · rw [hk]
      show t1 <+: _
      have h := runFrom_trace_prefix step tgt s1 t1
      cases ht : runFrom step tgt s1 t1 with
      | ok s3 t3 =>
        rw [ht] at h
        exact List.IsPrefix.trans h (runFrom_trace_prefix step post s3 t3)
      | fault k' t3 => rw [ht] at h; exact h
    · rw [h1, h2]; exact Allows.refl _

/-! ## `readRange` and `updRange` -/

theorem readRange_congr {α : Type} {m m' : Nat → Option α} :
    ∀ {p n : Nat}, (∀ i, i < n → m (p + i) = m' (p + i)) → readRange m p n = readRange m' p n
  | _, 0, _ => rfl
  | p, n + 1, h => by
    have h0 : m p = m' p := by simpa using h 0 (by omega)
    have ih : readRange m (p + 1) n = readRange m' (p + 1) n :=
      readRange_congr (fun i hi => by
        have := h (i + 1) (by omega)
        rwa [show p + (i + 1) = p + 1 + i by omega] at this)
    simp only [readRange, h0, ih]

theorem readRange_length {α : Type} {m : Nat → Option α} :
    ∀ {p n : Nat} {cs : List α}, readRange m p n = some cs → cs.length = n
  | _, 0, cs, h => by simp only [readRange, Option.some.injEq] at h; subst h; rfl
  | p, n + 1, cs, h => by
    simp only [readRange] at h
    cases hm : m p <;> cases hr : readRange m (p + 1) n <;> rw [hm, hr] at h <;>
      simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    simp [readRange_length hr]

theorem readRange_get {α : Type} {m : Nat → Option α} :
    ∀ {p n : Nat} {cs : List α}, readRange m p n = some cs →
      ∀ i (h : i < cs.length), m (p + i) = some cs[i]
  | _, 0, cs, h, i, hi => by
    simp only [readRange, Option.some.injEq] at h; subst h; simp at hi
  | p, n + 1, cs, h, i, hi => by
    simp only [readRange] at h
    cases hm : m p <;> cases hr : readRange m (p + 1) n <;> rw [hm, hr] at h <;>
      simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    cases i with
    | zero => simpa using hm
    | succ i =>
      have := readRange_get hr i (by simpa using hi)
      rw [show p + (i + 1) = p + 1 + i by omega]
      simpa using this

theorem readRange_isSome {α : Type} {m : Nat → Option α} :
    ∀ {p n : Nat}, (∀ i, i < n → (m (p + i)).isSome) → (readRange m p n).isSome
  | _, 0, _ => rfl
  | p, n + 1, h => by
    have h0 : (m p).isSome := by simpa using h 0 (by omega)
    have ih : (readRange m (p + 1) n).isSome :=
      readRange_isSome (fun i hi => by
        have := h (i + 1) (by omega)
        rwa [show p + (i + 1) = p + 1 + i by omega] at this)
    simp only [readRange]
    cases hm : m p <;> cases hr : readRange m (p + 1) n <;> simp_all

theorem readRange_map {α β : Type} (f : α → β) (m : Nat → Option α) :
    ∀ (p n : Nat), readRange (fun a => (m a).map f) p n = (readRange m p n).map (List.map f)
  | _, 0 => rfl
  | p, n + 1 => by
    simp only [readRange, readRange_map f m (p + 1) n]
    cases m p <;> cases readRange m (p + 1) n <;> rfl

theorem updRange_of_lt {α : Type} (m : Nat → Option α) (p n : Nat) (f : Nat → α → α) {a : Nat}
    (h : a < p ∨ p + n ≤ a) : updRange m p n f a = m a := by
  unfold updRange; split
  · omega
  · rfl

theorem updRange_of_mem {α : Type} (m : Nat → Option α) (p n : Nat) (f : Nat → α → α) {a : Nat}
    (h1 : p ≤ a) (h2 : a < p + n) : updRange m p n f a = (m a).map (f (a - p)) := by
  unfold updRange; split
  · rfl
  · omega

theorem updRange_isSome {α : Type} (m : Nat → Option α) (p n : Nat) (f : Nat → α → α) (a : Nat) :
    (updRange m p n f a).isSome = (m a).isSome := by
  unfold updRange; split <;> simp

/-- Updates of disjoint ranges commute. -/
theorem updRange_comm {α : Type} (m : Nat → Option α) (p n q k : Nat) (f g : Nat → α → α)
    (h : RangesDisjoint p n q k) :
    updRange (updRange m p n f) q k g = updRange (updRange m q k g) p n f := by
  funext a
  unfold RangesDisjoint at h
  unfold updRange
  by_cases ha : p ≤ a ∧ a < p + n <;> by_cases hb : q ≤ a ∧ a < q + k <;>
    simp only [ha, hb, ite_false]
  omega

/-- A range read is unaffected by an update of a disjoint range. -/
theorem readRange_updRange_disjoint {α : Type} (m : Nat → Option α) (p n q k : Nat)
    (f : Nat → α → α) (h : RangesDisjoint p n q k) :
    readRange (updRange m q k f) p n = readRange m p n := by
  apply readRange_congr
  intro i hi
  unfold RangesDisjoint at h
  exact updRange_of_lt m q k f (by omega)

/-! ## List checks by index -/

theorem all_zip_get {α β : Type} {f : α × β → Bool} {l₁ : List α} {l₂ : List β}
    (h : (l₁.zip l₂).all f = true) (i : Nat) (h1 : i < l₁.length) (h2 : i < l₂.length) :
    f (l₁[i], l₂[i]) = true := by
  rw [List.all_eq_true] at h
  have hi : i < (l₁.zip l₂).length := by simp [List.length_zip]; omega
  have := h _ (List.getElem_mem hi)
  simpa [List.getElem_zip] using this

theorem tagsOk_get {c : Compat} {cs : List Cell} {T : Ty} (h : TagsOk c cs T = true)
    (i : Nat) (h1 : i < cs.length) (h2 : i < T.leaves.length) :
    c cs[i].eff.tag T.leaves[i] = true := by
  unfold TagsOk at h; exact all_zip_get (f := fun x => c x.1.eff.tag x.2) h i h1 h2

theorem declOk_get {c : Compat} {cs : List Cell} {T : Ty} (h : DeclOk c cs T = true)
    (i : Nat) (h1 : i < cs.length) (h2 : i < T.leaves.length) :
    (match cs[i].eff with
     | .decl d => c (some d) T.leaves[i]
     | .alloc _ => true) = true := by
  unfold DeclOk at h
  exact all_zip_get (f := fun x => match x.1.eff with
    | .decl d => c (some d) x.2
    | .alloc _ => true) h i h1 h2

/-! ## Finite facts about the type universe -/

theorem leaf_ne_u8_of_ne_u8 {T : Ty} (hT : T ≠ .u8) {x : Scalar} (hx : x ∈ T.leaves) :
    x ≠ .u8 := by
  cases T <;> simp [Ty.leaves] at hx hT ⊢ <;> (try rcases hx with rfl | rfl) <;> simp_all

theorem stdCompat_some_of_ne_u8 {a b : Scalar} (hb : b ≠ .u8) (h : stdCompat (some a) b = true) :
    a = b := by
  cases a <;> cases b <;> simp_all [stdCompat]

theorem size_pos (T : Ty) : 0 < T.size := by cases T <;> decide

theorem size_le_eight (T : Ty) : T.size ≤ 8 := by cases T <;> decide

theorem leafAt_eq (T : Ty) {i : Nat} (h : i < T.leaves.length) : T.leafAt i = T.leaves[i] := by
  unfold Ty.leafAt; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem noCommonLeaf_get {T U : Ty} (h : NoCommonLeaf T U) {i j : Nat}
    (hi : i < T.leaves.length) (hj : j < U.leaves.length) : T.leaves[i] ≠ U.leaves[j] := by
  intro heq
  exact h _ (List.getElem_mem hi) (heq ▸ List.getElem_mem hj)

/-- Two nonempty ranges that are not disjoint share an address. -/
theorem exists_overlap {p n q k : Nat} (hn : 0 < n) (hk : 0 < k) (h : ¬ RangesDisjoint p n q k) :
    ∃ i j, i < n ∧ j < k ∧ p + i = q + j := by
  unfold RangesDisjoint at h
  by_cases hpq : p ≤ q
  · exact ⟨q - p, 0, by omega, by omega, by omega⟩
  · exact ⟨0, p - q, by omega, by omega, by omega⟩

/-! ## One-step characterizations -/

section StepE
variable {cfg : ECfg}

theorem stepE_load_next {r : Reg} {T : Ty} {p : Nat} {σ σ' : St}
    (h : stepE cfg (.load r T p) σ = .next σ') :
    ∃ cs, readRange σ.mem p T.size = some cs ∧ TagsOk cfg.compat cs T = true ∧
      σ' = { σ with regs := updReg σ.regs r (cs.map Cell.val) } := by
  simp only [stepE] at h
  cases hr : readRange σ.mem p T.size with
  | none => rw [hr] at h; cases h
  | some cs =>
    rw [hr] at h
    simp only at h
    split at h
    · split at h
      · exact ⟨cs, rfl, by assumption, by injection h with h; exact h.symm⟩
      · cases h
    · cases h

theorem stepE_load_of {r : Reg} {T : Ty} {p : Nat} {σ : St} {cs : List Cell}
    (h1 : readRange σ.mem p T.size = some cs) (h2 : TagsOk cfg.compat cs T = true) :
    stepE cfg (.load r T p) σ = .next { σ with regs := updReg σ.regs r (cs.map Cell.val) } := by
  have hv : T.Valid (cs.map Cell.val) := by
    unfold Ty.Valid; rw [List.length_map]; exact readRange_length h1
  simp only [stepE, h1, hv, h2, ite_true]

theorem stepE_store_next {T : Ty} {p : Nat} {r : Reg} {σ σ' : St}
    (h : stepE cfg (.store T p r) σ = .next σ') :
    ∃ ds, readRange σ.mem p T.size = some ds ∧ T.Valid (σ.regs r) ∧
      DeclOk cfg.compat ds T = true ∧
      σ' = { σ with mem := updRange σ.mem p T.size (storeCell T (σ.regs r)) } := by
  simp only [stepE] at h
  cases hr : readRange σ.mem p T.size with
  | none => rw [hr] at h; cases h
  | some ds =>
    rw [hr] at h
    simp only at h
    split at h
    · split at h
      · exact ⟨ds, rfl, by assumption, by assumption, by injection h with h; exact h.symm⟩
      · cases h
    · cases h

theorem stepE_store_of {T : Ty} {p : Nat} {r : Reg} {σ : St} {ds : List Cell}
    (h1 : readRange σ.mem p T.size = some ds) (h2 : T.Valid (σ.regs r))
    (h3 : DeclOk cfg.compat ds T = true) :
    stepE cfg (.store T p r) σ =
      .next { σ with mem := updRange σ.mem p T.size (storeCell T (σ.regs r)) } := by
  simp only [stepE, h1, h2, h3, ite_true]

/-- Only `out` emits. -/
theorem stepE_emit {i : Instr} {σ σ' : St} {v : Val} (h : stepE cfg i σ = .emit v σ') :
    ∃ r, i = .out r := by
  cases i with
  | out r => exact ⟨r, rfl⟩
  | set r w => simp [stepE] at h
  | load r T p =>
    simp only [stepE] at h
    split at h
    · cases h
    · split at h
      · split at h <;> cases h
      · cases h
  | store T p r =>
    simp only [stepE] at h
    split at h
    · cases h
    · split at h
      · split at h <;> cases h
      · cases h
  | memcpy d s n =>
    simp only [stepE] at h
    split at h
    · split at h <;> cases h
    · cases h

end StepE

theorem stepU_load_next {r : Reg} {T : Ty} {p : Nat} {u u' : USt}
    (h : stepU (.load r T p) u = .next u') :
    ∃ bs, readRange u.mem p T.size = some bs ∧ u' = { u with regs := updReg u.regs r bs } := by
  simp only [stepU] at h
  cases hr : readRange u.mem p T.size with
  | none => rw [hr] at h; cases h
  | some bs =>
    rw [hr] at h
    simp only at h
    split at h
    · exact ⟨bs, rfl, by injection h with h; exact h.symm⟩
    · cases h

theorem stepU_load_of {r : Reg} {T : Ty} {p : Nat} {u : USt} {bs : List Byte}
    (h1 : readRange u.mem p T.size = some bs) :
    stepU (.load r T p) u = .next { u with regs := updReg u.regs r bs } := by
  have hv : T.Valid bs := readRange_length h1
  simp only [stepU, h1, hv, ite_true]

theorem stepU_store_next {T : Ty} {p : Nat} {r : Reg} {u u' : USt}
    (h : stepU (.store T p r) u = .next u') :
    (readRange u.mem p T.size).isSome ∧ T.Valid (u.regs r) ∧
      u' = { u with mem := updRange u.mem p T.size (fun i _ => (u.regs r).getD i 0) } := by
  simp only [stepU] at h
  cases hr : readRange u.mem p T.size with
  | none => rw [hr] at h; cases h
  | some bs =>
    rw [hr] at h
    simp only at h
    split at h
    · exact ⟨rfl, by assumption, by injection h with h; exact h.symm⟩
    · cases h

theorem stepU_store_of {T : Ty} {p : Nat} {r : Reg} {u : USt}
    (h1 : (readRange u.mem p T.size).isSome) (h2 : T.Valid (u.regs r)) :
    stepU (.store T p r) u =
      .next { u with mem := updRange u.mem p T.size (fun i _ => (u.regs r).getD i 0) } := by
  cases hr : readRange u.mem p T.size with
  | none => rw [hr] at h1; cases h1
  | some bs => simp only [stepU, hr, h2, ite_true]

theorem stepU_emit {i : Instr} {u u' : USt} {v : Val} (h : stepU i u = .emit v u') :
    ∃ r, i = .out r := by
  cases i with
  | out r => exact ⟨r, rfl⟩
  | set r w => simp [stepU] at h
  | load r T p =>
    simp only [stepU] at h
    split at h
    · cases h
    · split at h <;> cases h
  | store T p r =>
    simp only [stepU] at h
    split at h
    · cases h
    · split at h <;> cases h
  | memcpy d s n =>
    simp only [stepU] at h
    split at h
    · cases h
    · cases h

/-! ## Two-instruction blocks without `out` -/

theorem block2_ok {S : Type} {step : Instr → S → Step S} {i₁ i₂ : Instr} {s s₁ s₂ : S}
    {t : List Val} (h₁ : step i₁ s = .next s₁) (h₂ : step i₂ s₁ = .next s₂) :
    runFrom step [i₁, i₂] s t = .ok s₂ t := by
  simp [runFrom, h₁, h₂]

theorem block2_cases {S : Type} {step : Instr → S → Step S} {i₁ i₂ : Instr}
    (h₁ : ∀ s v s', step i₁ s ≠ .emit v s') (h₂ : ∀ s v s', step i₂ s ≠ .emit v s')
    (s : S) (t : List Val) :
    (∃ k, runFrom step [i₁, i₂] s t = .fault k t) ∨
    (∃ s₁ s₂, step i₁ s = .next s₁ ∧ step i₂ s₁ = .next s₂ ∧
      runFrom step [i₁, i₂] s t = .ok s₂ t) := by
  cases e₁ : step i₁ s with
  | fault k => left; exact ⟨k, by simp [runFrom, e₁]⟩
  | emit v s₁ => exact absurd e₁ (h₁ s v s₁)
  | next s₁ =>
    cases e₂ : step i₂ s₁ with
    | fault k => left; exact ⟨k, by simp [runFrom, e₁, e₂]⟩
    | emit v s₂ => exact absurd e₂ (h₂ s₁ v s₂)
    | next s₂ => right; exact ⟨s₁, s₂, rfl, e₂, block2_ok e₁ e₂⟩

theorem stepE_load_noEmit (cfg : ECfg) (r : Reg) (T : Ty) (p : Nat) :
    ∀ σ v σ', stepE cfg (.load r T p) σ ≠ .emit v σ' :=
  fun _ _ _ h => by obtain ⟨_, h'⟩ := stepE_emit h; cases h'

theorem stepE_store_noEmit (cfg : ECfg) (T : Ty) (p : Nat) (r : Reg) :
    ∀ σ v σ', stepE cfg (.store T p r) σ ≠ .emit v σ' :=
  fun _ _ _ h => by obtain ⟨_, h'⟩ := stepE_emit h; cases h'

theorem stepU_load_noEmit (r : Reg) (T : Ty) (p : Nat) :
    ∀ u v u', stepU (.load r T p) u ≠ .emit v u' :=
  fun _ _ _ h => by obtain ⟨_, h'⟩ := stepU_emit h; cases h'

theorem stepU_store_noEmit (T : Ty) (p : Nat) (r : Reg) :
    ∀ u v u', stepU (.store T p r) u ≠ .emit v u' :=
  fun _ _ _ h => by obtain ⟨_, h'⟩ := stepU_emit h; cases h'

/-! ## Declared-ness is preserved by execution -/

theorem stepE_isDecl_preserved {cfg : ECfg} {i : Instr} {σ σ' : St}
    (h : stepE cfg i σ = .next σ' ∨ ∃ v, stepE cfg i σ = .emit v σ') (a : Nat) :
    (σ'.mem a).map (fun c => c.eff.isDecl) = (σ.mem a).map (fun c => c.eff.isDecl) := by
  rcases h with h | ⟨v, h⟩
  · cases i with
    | set r w => simp only [stepE, Step.next.injEq] at h; subst h; rfl
    | out r => simp [stepE] at h
    | load r T p => obtain ⟨_, _, _, rfl⟩ := stepE_load_next h; rfl
    | store T p r =>
      obtain ⟨_, _, _, _, rfl⟩ := stepE_store_next h
      simp only [updRange]
      split
      · cases σ.mem a with
        | none => rfl
        | some c =>
          simp only [Option.map, storeCell]
          cases c.eff with
          | alloc t => cases T.leafAt (a - p) <;> rfl
          | decl d => rfl
      · rfl
    | memcpy dst src n =>
      simp only [stepE] at h
      split at h
      · split at h
        · simp only [Step.next.injEq] at h; subst h
          simp only [updRange]
          split
          · cases σ.mem a with
            | none => rfl
            | some c =>
              simp only [Option.map, copyFrom]
              split
              · simp only [copyCell]; cases c.eff <;> rfl
              · rfl
          · rfl
        · cases h
      · cases h
  · obtain ⟨r, rfl⟩ := stepE_emit h
    simp only [stepE, Step.emit.injEq] at h; rw [← h.2]

theorem declaredOn_step {cfg : ECfg} {p n : Nat} :
    ∀ i σ σ', DeclaredOn σ p n → (stepE cfg i σ = .next σ' ∨ ∃ v, stepE cfg i σ = .emit v σ') →
      DeclaredOn σ' p n := by
  intro i σ σ' hD hs k hk
  have e := stepE_isDecl_preserved hs (p + k)
  have := hD k hk
  cases h1 : σ'.mem (p + k) <;> cases h2 : σ.mem (p + k) <;> simp_all [Option.all, Option.map]

theorem allocatedOn_step {cfg : ECfg} {p n : Nat} :
    ∀ i σ σ', AllocatedOn σ p n → (stepE cfg i σ = .next σ' ∨ ∃ v, stepE cfg i σ = .emit v σ') →
      AllocatedOn σ' p n := by
  intro i σ σ' hA hs k hk
  have e := stepE_isDecl_preserved hs (p + k)
  have := hA k hk
  cases h1 : σ'.mem (p + k) <;> cases h2 : σ.mem (p + k) <;> simp_all [Option.all, Option.map]

/-! ## Per-byte incompatibility facts -/

/-- After a non-character `U`-store passes its declared-object check on a byte, that byte's tag
is the store's leaf; a `T`-load at a leaf not shared with `U` is then rejected. -/
theorem stored_tag_rejects {T U : Ty} (hT : T ≠ .u8) (hU : U ≠ .u8) (hTU : NoCommonLeaf T U)
    {i j : Nat} (hi : i < T.leaves.length) (hj : j < U.leaves.length) (cell : Cell) (v : Val)
    (hd : (match cell.eff with
           | .decl d => stdCompat (some d) U.leaves[j]
           | .alloc _ => true) = true) :
    stdCompat (storeCell U v j cell).eff.tag T.leaves[i] = false := by
  have hx : U.leaves[j] ≠ .u8 := leaf_ne_u8_of_ne_u8 hU (List.getElem_mem hj)
  have hy : T.leaves[i] ≠ .u8 := leaf_ne_u8_of_ne_u8 hT (List.getElem_mem hi)
  have hxy : T.leaves[i] ≠ U.leaves[j] := noCommonLeaf_get hTU hi hj
  have hl : U.leafAt j = U.leaves[j] := leafAt_eq U hj
  cases hc : cell.eff with
  | alloc t =>
    have : (storeCell U v j cell).eff = .alloc (some U.leaves[j]) := by
      simp only [storeCell, hc, hl]
      try (revert hx; cases U.leaves[j] <;> simp)
    rw [this]; simp only [Eff.tag]
    cases h : stdCompat (some U.leaves[j]) T.leaves[i]
    · rfl
    · exact absurd (stdCompat_some_of_ne_u8 hy h).symm hxy
  | decl d =>
    rw [hc] at hd
    have hdx : d = U.leaves[j] := stdCompat_some_of_ne_u8 hx hd
    have : (storeCell U v j cell).eff = .decl d := by simp only [storeCell, hc]
    rw [this]; simp only [Eff.tag]
    cases h : stdCompat (some d) T.leaves[i]
    · rfl
    · exact absurd ((stdCompat_some_of_ne_u8 hy h).symm.trans hdx) hxy

/-- A declared byte cannot pass both a check at leaf `x` and a check at leaf `y` when `x` and
`y` are distinct non-character leaves. -/
theorem decl_two_checks {d x y : Scalar} (hx : x ≠ .u8) (hy : y ≠ .u8) (hxy : x ≠ y)
    (h1 : stdCompat (some d) x = true) (h2 : stdCompat (some d) y = true) : False :=
  hxy ((stdCompat_some_of_ne_u8 hx h1).symm.trans (stdCompat_some_of_ne_u8 hy h2))

theorem isDecl_of_declaredOn {σ : St} {p n i : Nat} (hD : DeclaredOn σ p n) (hi : i < n)
    {c : Cell} (hc : σ.mem (p + i) = some c) : ∃ d, c.eff = .decl d := by
  have := hD i hi
  rw [hc] at this
  simp only [Option.all] at this
  cases h : c.eff with
  | decl d => exact ⟨d, rfl⟩
  | alloc t => rw [h] at this; cases this

/-! ## Simulation between (E) and (U) through `erase` -/

theorem erase_mem_store (m : Mem) (p n : Nat) (T : Ty) (v : Val) :
    (fun a => (updRange m p n (storeCell T v) a).map Cell.val) =
      updRange (fun a => (m a).map Cell.val) p n (fun i _ => v.getD i 0) := by
  funext a
  simp only [updRange]
  split
  · cases m a <;> rfl
  · rfl

theorem erase_mem_copy (m : Mem) (dst n : Nat) (cs : List Cell) :
    (fun a => (updRange m dst n (copyFrom cs) a).map Cell.val) =
      updRange (fun a => (m a).map Cell.val) dst n (fun i b => (cs.map Cell.val).getD i b) := by
  funext a
  simp only [updRange]
  split
  · cases m a with
    | none => rfl
    | some c =>
      simp only [Option.map, copyFrom, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases cs[a - dst]? <;> rfl
  · rfl

/-- One step of (E) either type-faults, or is matched exactly by one step of (U) on the erased
state. -/
theorem step_sim (cfg : ECfg) (i : Instr) (σ : St) :
    stepE cfg i σ = .fault .type ∨
    (stepE cfg i σ = .fault .base ∧ stepU i (erase σ) = .fault .base) ∨
    (∃ σ', stepE cfg i σ = .next σ' ∧ stepU i (erase σ) = .next (erase σ')) ∨
    (∃ v σ', stepE cfg i σ = .emit v σ' ∧ stepU i (erase σ) = .emit v (erase σ')) := by
  cases i with
  | set r v => exact Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩))
  | out r => exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl, rfl⟩))
  | load r T p =>
    cases h : readRange σ.mem p T.size with
    | none =>
      exact Or.inr (Or.inl ⟨by simp [stepE, h], by simp [stepU, erase, readRange_map, h]⟩)
    | some cs =>
      have hU : readRange (erase σ).mem p T.size = some (cs.map Cell.val) := by
        simp [erase, readRange_map, h]
      by_cases hv : T.Valid (cs.map Cell.val)
      · cases ht : TagsOk cfg.compat cs T
        · exact Or.inl (by simp [stepE, h, hv, ht])
        · exact Or.inr (Or.inr (Or.inl ⟨{ σ with regs := updReg σ.regs r (cs.map Cell.val) },
            by simp [stepE, h, hv, ht],
            by simp only [stepU, hU, hv, ite_true]; rfl⟩))
      · exact Or.inr (Or.inl ⟨by simp [stepE, h, hv], by simp [stepU, hU, hv]⟩)
  | store T p r =>
    cases h : readRange σ.mem p T.size with
    | none =>
      exact Or.inr (Or.inl ⟨by simp [stepE, h], by simp [stepU, erase, readRange_map, h]⟩)
    | some cs =>
      have hU : readRange (erase σ).mem p T.size = some (cs.map Cell.val) := by
        simp [erase, readRange_map, h]
      by_cases hv : T.Valid (σ.regs r)
      · cases hd : DeclOk cfg.compat cs T
        · exact Or.inl (by simp [stepE, h, hv, hd])
        · refine Or.inr (Or.inr (Or.inl
            ⟨{ σ with mem := updRange σ.mem p T.size (storeCell T (σ.regs r)) },
             by simp [stepE, h, hv, hd], ?_⟩))
          simp only [stepU, hU]
          have hv' : T.Valid ((erase σ).regs r) := hv
          simp only [hv', ite_true]
          simp only [erase, erase_mem_store]
      · have hv' : ¬ T.Valid ((erase σ).regs r) := hv
        exact Or.inr (Or.inl ⟨by simp [stepE, h, hv], by simp [stepU, hU, hv']⟩)
  | memcpy dst src n =>
    cases h1 : readRange σ.mem src n with
    | none =>
      exact Or.inr (Or.inl ⟨by simp [stepE, h1], by simp [stepU, erase, readRange_map, h1]⟩)
    | some cs =>
      cases h2 : readRange σ.mem dst n with
      | none =>
        exact Or.inr (Or.inl ⟨by simp [stepE, h1, h2],
          by simp [stepU, erase, readRange_map, h1, h2]⟩)
      | some ds =>
        have hU1 : readRange (erase σ).mem src n = some (cs.map Cell.val) := by
          simp [erase, readRange_map, h1]
        have hU2 : readRange (erase σ).mem dst n = some (ds.map Cell.val) := by
          simp [erase, readRange_map, h2]
        cases hc : (!cfg.memcpyChecksBytes || CopyBytesOk cfg.compat cs ds)
        · exact Or.inl (by simp only [stepE, h1, h2, hc]; rfl)
        · refine Or.inr (Or.inr (Or.inl ⟨{ σ with mem := updRange σ.mem dst n (copyFrom cs) },
            by simp only [stepE, h1, h2, hc]; rfl, ?_⟩))
          simp only [stepU, hU1, hU2]
          simp only [erase, erase_mem_copy]

/-- The untyped run from the erased state is allowed by the effective-type run. -/
theorem runFrom_sim_allows (cfg : ECfg) :
    ∀ (P : List Instr) (σ : St) (t : List Val),
      Allows (runFrom (stepE cfg) P σ t).outcome (runFrom stepU P (erase σ) t).outcome
  | [], _, _ => Allows.refl _
  | i :: P, σ, t => by
    rcases step_sim cfg i σ with h | ⟨h1, h2⟩ | ⟨σ', h1, h2⟩ | ⟨v, σ', h1, h2⟩
    · have hE : runFrom (stepE cfg) (i :: P) σ t = .fault .type t := by
        simp only [runFrom, h]
      rw [hE]
      exact runFrom_trace_prefix stepU (i :: P) (erase σ) t
    · simp only [runFrom, h1, h2]; exact Allows.refl _
    · simp only [runFrom, h1, h2]; exact runFrom_sim_allows cfg P σ' t
    · simp only [runFrom, h1, h2]; exact runFrom_sim_allows cfg P σ' (t ++ [v])

/-- Without a type fault, the two runs have the same outcome. -/
theorem runFrom_sim_eq (cfg : ECfg) :
    ∀ (P : List Instr) (σ : St) (t : List Val), typeFaultsB cfg P σ = false →
      (runFrom (stepE cfg) P σ t).outcome = (runFrom stepU P (erase σ) t).outcome
  | [], _, _, _ => rfl
  | i :: P, σ, t, hP => by
    rcases step_sim cfg i σ with h | ⟨h1, h2⟩ | ⟨σ', h1, h2⟩ | ⟨v, σ', h1, h2⟩
    · simp only [typeFaultsB, h] at hP; cases hP
    · simp only [runFrom, h1, h2]; rfl
    · simp only [typeFaultsB, h1] at hP
      simp only [runFrom, h1, h2]; exact runFrom_sim_eq cfg P σ' t hP
    · simp only [typeFaultsB, h1] at hP
      simp only [runFrom, h1, h2]; exact runFrom_sim_eq cfg P σ' (t ++ [v]) hP

/-- A type fault makes the effective-type run undefined. -/
theorem runFrom_typeFaults_ub (cfg : ECfg) :
    ∀ (P : List Instr) (σ : St) (t : List Val), typeFaultsB cfg P σ = true →
      ∃ t', (runFrom (stepE cfg) P σ t).outcome = .ub t'
  | [], _, _, h => by simp [typeFaultsB] at h
  | i :: P, σ, t, h => by
    simp only [typeFaultsB] at h
    simp only [runFrom]
    cases e : stepE cfg i σ with
    | fault k => exact ⟨t, rfl⟩
    | next σ' => rw [e] at h; exact runFrom_typeFaults_ub cfg P σ' t h
    | emit v σ' => rw [e] at h; exact runFrom_typeFaults_ub cfg P σ' (t ++ [v]) h

/-! ## Further helpers -/

/-- Equal block runs from every reachable state give a sound replacement. -/
theorem reorderSoundFrom_of_eq {S : Type} {step : Instr → S → Step S} {Pre Inv : S → Prop}
    {src tgt : List Instr}
    (hpre : ∀ s, Pre s → Inv s)
    (hstep : ∀ i s s', Inv s → (step i s = .next s' ∨ ∃ v, step i s = .emit v s') → Inv s')
    (heq : ∀ s t, Inv s → runFrom step tgt s t = runFrom step src s t) :
    ReorderSoundFrom Pre step src tgt := by
  intro pre post s0 hs0
  rw [refines_beh_iff]
  unfold exec
  rw [List.append_assoc, List.append_assoc, runFrom_append, runFrom_append]
  cases hp : runFrom step pre s0 [] with
  | fault k t => exact Allows.refl _
  | ok s1 t1 =>
    simp only
    rw [runFrom_append, runFrom_append, heq s1 t1 (runFrom_inv hstep pre s0 s1 [] t1 (hpre s0 hs0) hp)]
    exact Allows.refl _

theorem readRange_const {α : Type} {m : Nat → Option α} {c : α} :
    ∀ {p n : Nat}, (∀ i, i < n → m (p + i) = some c) → readRange m p n = some (List.replicate n c)
  | _, 0, _ => rfl
  | p, n + 1, h => by
    have h0 : m p = some c := by simpa using h 0 (by omega)
    have ih : readRange m (p + 1) n = some (List.replicate n c) :=
      readRange_const (fun i hi => by
        have := h (i + 1) (by omega)
        rwa [show p + (i + 1) = p + 1 + i by omega] at this)
    simp only [readRange, h0, ih, List.replicate_succ]

theorem stepU_store_invalid {T : Ty} {p : Nat} {r : Reg} {u : USt} (h : ¬ T.Valid (u.regs r)) :
    stepU (.store T p r) u = .fault .base := by
  simp only [stepU]
  cases readRange u.mem p T.size <;> simp [h]

theorem copyBytesOk_stdCompat (cs ds : List Cell) : CopyBytesOk stdCompat cs ds = true := by
  unfold CopyBytesOk
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  exact ⟨fun x _ => by cases x.eff.tag <;> rfl, fun x _ => by cases x.eff <;> rfl⟩

/-! ## `memcpy` followed by a typed load -/

theorem readRange_updRange_copyFrom :
    ∀ (m : Nat → Option Cell) (q k n : Nat) (cs ds : List Cell),
      readRange m (q + k) n = some ds →
      cs.length = k + n →
      readRange (updRange m q (k + n) (copyFrom cs)) (q + k) n =
        some (List.zipWith copyCell (cs.drop k) ds)
  | _, _, _, 0, _, ds, hds, _ => by
    simp only [readRange, Option.some.injEq] at hds; subst hds
    simp [readRange]
  | m, q, k, n + 1, cs, ds, hds, hlen => by
    simp only [readRange] at hds ⊢
    cases hm : m (q + k) <;> rw [hm] at hds
    · cases hds
    · rename_i d
      cases hr : readRange m (q + k + 1) n <;> rw [hr] at hds
      · cases hds
      · rename_i ds_tail
        simp only [Option.some.injEq] at hds; subst hds
        have hk : k < cs.length := by omega
        have hdrop : cs.drop k = cs[k] :: cs.drop (k + 1) := List.drop_eq_getElem_cons hk
        have hupd : updRange m q (k + (n + 1)) (copyFrom cs) (q + k) = some (copyCell cs[k] d) := by
          rw [updRange_of_mem _ _ _ _ (by omega) (by omega), hm]
          simp [copyFrom, List.getElem?_eq_getElem hk]
        rw [hupd]
        have heq_addr : q + k + 1 = q + (k + 1) := by omega
        have heq_len : k + (n + 1) = (k + 1) + n := by omega
        rw [heq_addr, heq_len]
        have ih := readRange_updRange_copyFrom m q (k + 1) n cs ds_tail
          (by rwa [← heq_addr]) (by omega)
        rw [ih, hdrop]
        rfl

theorem zipWith_copyCell_val :
    ∀ (cs ds : List Cell), cs.length = ds.length →
      (List.zipWith copyCell cs ds).map Cell.val = cs.map Cell.val
  | [], [], _ => rfl
  | c :: cs, d :: ds, h => by
    simp [List.zipWith, copyCell, zipWith_copyCell_val cs ds (Nat.succ.inj h)]

theorem tagsOk_zipWith_copyCell :
    ∀ (cs ds : List Cell) (leaves : List Scalar),
      cs.length = leaves.length → ds.length = leaves.length →
      (((List.zipWith copyCell cs ds).zip leaves).all (fun x => stdCompat x.1.eff.tag x.2)) =
        (((cs.zip ds).zip leaves).all memcpyLoadCheck)
  | [], [], [], _, _ => rfl
  | sc :: cs, dc :: ds, l :: ls, h1, h2 => by
    have ih := tagsOk_zipWith_copyCell cs ds ls (Nat.succ.inj h1) (Nat.succ.inj h2)
    simp only [List.zipWith_cons_cons, List.zip_cons_cons, List.all_cons, copyCell, memcpyLoadCheck]
    rw [ih]
    cases dc.eff <;> rfl
  | _ :: _, [], [], h1, _ => by cases h1
  | [], _ :: _, [], _, h2 => by cases h2
  | [], _, _ :: _, h1, _ => by cases h1
  | _ :: _, [], _ :: _, _, h2 => by cases h2

end Lemmas
end Toy.Tbaa
