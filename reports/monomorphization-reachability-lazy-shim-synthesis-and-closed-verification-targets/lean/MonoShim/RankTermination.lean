import MonoShim.Termination

/-!
# Termination of collection under the rank check
-/

namespace Toy.MonoShim

/-! ## Generic worklist termination over a finite universe -/

/-- Number of entries of `U` not in `done`. -/
def rtCntNot (done : List Key) : List Key → Nat
  | [] => 0
  | x :: xs => (if x ∈ done then 0 else 1) + rtCntNot done xs

theorem rtCntNot_le (k : Key) (done : List Key) :
    ∀ U : List Key, rtCntNot (k :: done) U ≤ rtCntNot done U
  | [] => by simp [rtCntNot]
  | x :: xs => by
    have ih := rtCntNot_le k done xs
    simp only [rtCntNot]
    by_cases h1 : x ∈ done
    · have h2 : x ∈ k :: done := List.mem_cons_of_mem _ h1
      simp only [h1, h2, ↓reduceIte]; omega
    · by_cases h2 : x ∈ k :: done
      · simp only [h1, h2, ↓reduceIte]; omega
      · simp only [h1, h2, ↓reduceIte]; omega

theorem rtCntNot_lt (k : Key) (done : List Key) (hk : k ∉ done) :
    ∀ U : List Key, k ∈ U → rtCntNot (k :: done) U < rtCntNot done U
  | [], h => by simp at h
  | x :: xs, h => by
    rcases List.mem_cons.mp h with h | h
    · have := rtCntNot_le k done xs
      have hx : x ∉ done := h ▸ hk
      have hx2 : x ∈ k :: done := by simp [h]
      simp only [rtCntNot, hx, hx2, ↓reduceIte]; omega
    · have ih := rtCntNot_lt k done hk xs h
      simp only [rtCntNot]
      by_cases h1 : x ∈ done
      · have h2 : x ∈ k :: done := List.mem_cons_of_mem _ h1
        simp only [h1, h2, ↓reduceIte]; omega
      · by_cases h2 : x ∈ k :: done
        · simp only [h1, h2, ↓reduceIte]; omega
        · simp only [h1, h2, ↓reduceIte]; omega

theorem rt_collectGo_terminates (edges : Key → List Key) (sched : List Key → List Key → List Key)
    (hs : SchedOK sched) (U : List Key) (Rp : Key → Prop)
    (hR : ∀ k, Rp k → ∀ k' ∈ edges k, Rp k') (hU : ∀ k, Rp k → k ∈ U) :
    ∀ (n : Nat) (done : List Key), rtCntNot done U = n → ∀ work : List Key, (∀ k ∈ work, Rp k) →
      ∃ fuel T, collectGo edges sched fuel work done = some T := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro done hn work
  induction work with
  | nil => intro _; exact ⟨1, done, rfl⟩
  | cons k work ihw =>
    intro hw
    have hkR : Rp k := hw k (by simp)
    by_cases hk : k ∈ done
    · obtain ⟨fuel, T, h⟩ := ihw (fun k' h' => hw k' (List.mem_cons_of_mem _ h'))
      exact ⟨fuel + 1, T, by simp only [collectGo, hk, ite_true]; exact h⟩
    · have hlt : rtCntNot (k :: done) U < n := hn ▸ rtCntNot_lt k done hk U (hU k hkR)
      obtain ⟨fuel, T, h⟩ := ih _ hlt (k :: done) rfl (sched work (edges k)) (by
        intro k' h'
        rcases (hs work (edges k) k').mp h' with h' | h'
        · exact hw k' (List.mem_cons_of_mem _ h')
        · exact hR k hkR k' h')
      exact ⟨fuel + 1, T, by simp only [collectGo, hk, ite_false]; exact h⟩

/-! ## Weights -/

/-- Weight of a type: its size plus all numeric labels it carries. -/
def Ty.wt : Ty → Nat
  | .base n => n + 1
  | .box t => t.wt + 1
  | .pair a b => a.wt + b.wt + 1
  | .dyn n => n + 1
  | .fnPtr => 1
  | .param i => i + 1
  | .proj tr t => tr + t.wt + 1

theorem Ty.wt_pos (t : Ty) : 1 ≤ t.wt := by
  cases t <;> simp [Ty.wt]

theorem rt_getD_mem_or (σ : List Ty) : ∀ (i : Nat) (d : Ty), σ.getD i d ∈ σ ∨ σ.getD i d = d := by
  induction σ with
  | nil => intro i d; right; simp
  | cons x xs ih =>
    intro i d
    cases i with
    | zero => left; simp
    | succ i =>
      rw [List.getD_cons_succ]
      rcases ih i d with h | h
      · left; exact List.mem_cons_of_mem _ h
      · right; exact h

theorem Ty.wt_subst (σ : List Ty) (W : Nat) (hW : 1 ≤ W) (hσ : ∀ s ∈ σ, s.wt ≤ W) :
    ∀ t : Ty, (t.subst σ).wt ≤ t.wt * W := by
  intro t
  induction t with
  | base n => exact Nat.le_mul_of_pos_right _ hW
  | box t ih => simp only [Ty.subst, Ty.wt]; rw [Nat.add_mul, Nat.one_mul]; omega
  | pair a b iha ihb =>
    simp only [Ty.subst, Ty.wt]; rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega
  | dyn n => exact Nat.le_mul_of_pos_right _ hW
  | fnPtr => exact Nat.le_mul_of_pos_right _ hW
  | param i =>
    simp only [Ty.subst]
    rcases rt_getD_mem_or σ i (.param i) with h | h
    · have := hσ _ h
      simp only [Ty.wt]; rw [Nat.add_mul, Nat.one_mul]; omega
    · rw [h]; exact Nat.le_mul_of_pos_right _ hW
  | proj tr t ih =>
    simp only [Ty.subst, Ty.wt]; rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
    have : tr ≤ tr * W := Nat.le_mul_of_pos_right _ hW
    omega

theorem rt_assocLookup_some {A : List (Nat × Ty × Ty)} {tr : Nat} {t rhs : Ty}
    (h : assocLookup A tr t = some rhs) : ∃ e ∈ A, e.2.2 = rhs := by
  unfold assocLookup at h
  rcases hf : A.find? (fun e => decide (e.1 = tr ∧ e.2.1 = t)) with _ | e
  · rw [hf] at h; simp at h
  · rw [hf] at h; simp at h
    exact ⟨e, List.mem_of_find?_eq_some hf, h⟩

theorem Ty.wt_norm (A : List (Nat × Ty × Ty)) (M : Nat) (hM : 1 ≤ M)
    (hA : ∀ e ∈ A, e.2.2.wt ≤ M) : ∀ t : Ty, (t.norm A).wt ≤ M * t.wt := by
  intro t
  induction t with
  | base n => exact Nat.le_mul_of_pos_left _ hM
  | box t ih => simp only [Ty.norm, Ty.wt]; rw [Nat.mul_add, Nat.mul_one]; omega
  | pair a b iha ihb =>
    simp only [Ty.norm, Ty.wt]; rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega
  | dyn n => exact Nat.le_mul_of_pos_left _ hM
  | fnPtr => exact Nat.le_mul_of_pos_left _ hM
  | param i => exact Nat.le_mul_of_pos_left _ hM
  | proj tr t ih =>
    simp only [Ty.norm]
    have htr : tr ≤ M * tr := Nat.le_mul_of_pos_left _ hM
    rcases h : assocLookup A tr (t.norm A) with _ | rhs
    · simp only [Option.getD_none, Ty.wt]; rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega
    · simp only [Option.getD_some]
      obtain ⟨e, he, rfl⟩ := rt_assocLookup_some h
      have := hA e he
      simp only [Ty.wt]; rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega

theorem Ty.subst_of_hasParam_false (σ : List Ty) : ∀ t : Ty, t.hasParam = false → t.subst σ = t := by
  intro t
  induction t with
  | base n => intro _; rfl
  | box t ih => intro h; simp only [Ty.hasParam] at h; simp only [Ty.subst, ih h]
  | pair a b iha ihb =>
    intro h; simp only [Ty.hasParam, Bool.or_eq_false_iff] at h
    simp only [Ty.subst, iha h.1, ihb h.2]
  | dyn n => intro _; rfl
  | fnPtr => intro _; rfl
  | param i => intro h; simp [Ty.hasParam] at h
  | proj tr t ih => intro h; simp only [Ty.hasParam] at h; simp only [Ty.subst, ih h]

/-! ## Finite enumerations -/

/-- All types of weight at most `n`. -/
def allTys : Nat → List Ty
  | 0 => []
  | n + 1 =>
    (List.range (n + 1)).map Ty.base ++ (allTys n).map Ty.box ++
    (allTys n).flatMap (fun a => (allTys n).map (Ty.pair a)) ++
    (List.range (n + 1)).map Ty.dyn ++ [Ty.fnPtr] ++ (List.range (n + 1)).map Ty.param ++
    (List.range (n + 1)).flatMap (fun tr => (allTys n).map (Ty.proj tr))

theorem mem_allTys : ∀ (n : Nat) (t : Ty), t.wt ≤ n → t ∈ allTys n := by
  intro n
  induction n with
  | zero => intro t h; have := Ty.wt_pos t; omega
  | succ n ih =>
    intro t h
    cases t with
    | base k => simp [Ty.wt] at h; simp [allTys]; omega
    | box t => simp [Ty.wt] at h; simp [allTys, ih t h]
    | pair a b =>
      simp [Ty.wt] at h
      simp [allTys, ih a (by omega), ih b (by omega)]
    | dyn k => simp [Ty.wt] at h; simp [allTys]; omega
    | fnPtr => simp [allTys]
    | param k => simp [Ty.wt] at h; simp [allTys]; omega
    | proj tr t =>
      simp [Ty.wt] at h
      simp [allTys, ih t (by omega)]; omega

/-- All lists of length at most `n` over `xs`. -/
def allLists {α : Type} (xs : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => [] :: xs.flatMap (fun x => (allLists xs n).map (x :: ·))

theorem mem_allLists {α : Type} (xs : List α) :
    ∀ (n : Nat) (l : List α), l.length ≤ n → (∀ x ∈ l, x ∈ xs) → l ∈ allLists xs n
  | 0, l, h, _ => by
    cases l with
    | nil => simp [allLists]
    | cons => simp at h
  | n + 1, [], _, _ => by simp [allLists]
  | n + 1, x :: l, h, hx => by
    simp only [allLists, List.mem_cons, List.mem_flatMap, List.mem_map]
    right
    exact ⟨x, hx x (by simp), l,
      mem_allLists xs n l (by simp at h; omega) (fun y hy => hx y (by simp [hy])), rfl⟩

/-- Key bounded by `n`: every label and list length is at most `n`, every type has weight at
most `n`. -/
def KB (n : Nat) : Key → Prop
  | .inst g τs => g ≤ n ∧ τs.length ≤ n ∧ ∀ t ∈ τs, t.wt ≤ n
  | .meth tr m t => tr ≤ n ∧ m ≤ n ∧ t.wt ≤ n
  | .userDrop k => k ≤ n
  | .userClone k => k ≤ n
  | .dropGlue t => t.wt ≤ n
  | .cloneShim t => t.wt ≤ n
  | .reifyShim g τs => g ≤ n ∧ τs.length ≤ n ∧ ∀ t ∈ τs, t.wt ≤ n

theorem KB.mono {a b : Nat} (hab : a ≤ b) : ∀ {k : Key}, KB a k → KB b k := by
  intro k h
  cases k with
  | inst g τs => obtain ⟨h1, h2, h3⟩ := h; exact ⟨by omega, by omega, fun t ht => by have := h3 t ht; omega⟩
  | meth tr m t => obtain ⟨h1, h2, h3⟩ := h; exact ⟨by omega, by omega, by omega⟩
  | userDrop k => simp only [KB] at h ⊢; omega
  | userClone k => simp only [KB] at h ⊢; omega
  | dropGlue t => simp only [KB] at h ⊢; omega
  | cloneShim t => simp only [KB] at h ⊢; omega
  | reifyShim g τs => obtain ⟨h1, h2, h3⟩ := h; exact ⟨by omega, by omega, fun t ht => by have := h3 t ht; omega⟩

/-- All keys bounded by `n`. -/
def allKeys (n : Nat) : List Key :=
  (List.range (n + 1)).flatMap (fun g => (allLists (allTys n) n).map (Key.inst g)) ++
  (List.range (n + 1)).flatMap (fun tr => (List.range (n + 1)).flatMap
    (fun m => (allTys n).map (Key.meth tr m))) ++
  (List.range (n + 1)).map Key.userDrop ++ (List.range (n + 1)).map Key.userClone ++
  (allTys n).map Key.dropGlue ++ (allTys n).map Key.cloneShim ++
  (List.range (n + 1)).flatMap (fun g => (allLists (allTys n) n).map (Key.reifyShim g))

theorem mem_allKeys (n : Nat) : ∀ k : Key, KB n k → k ∈ allKeys n := by
  intro k h
  cases k with
  | inst g τs =>
    obtain ⟨h1, h2, h3⟩ := h
    have hl : τs ∈ allLists (allTys n) n :=
      mem_allLists _ n τs h2 (fun t ht => mem_allTys n t (h3 t ht))
    simp only [allKeys, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨g, by omega, τs, hl, rfl⟩)))))
  | meth tr m t =>
    obtain ⟨h1, h2, h3⟩ := h
    simp only [allKeys, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
      ⟨tr, by omega, m, by omega, t, mem_allTys n t h3, rfl⟩)))))
  | userDrop k =>
    simp only [KB] at h
    simp only [allKeys, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨k, by omega, rfl⟩))))
  | userClone k =>
    simp only [KB] at h
    simp only [allKeys, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨k, by omega, rfl⟩)))
  | dropGlue t =>
    simp only [KB] at h
    simp only [allKeys, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl (Or.inr ⟨t, mem_allTys n t h, rfl⟩))
  | cloneShim t =>
    simp only [KB] at h
    simp only [allKeys, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    exact Or.inl (Or.inr ⟨t, mem_allTys n t h, rfl⟩)
  | reifyShim g τs =>
    obtain ⟨h1, h2, h3⟩ := h
    have hl : τs ∈ allLists (allTys n) n :=
      mem_allLists _ n τs h2 (fun t ht => mem_allTys n t (h3 t ht))
    simp only [allKeys, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    exact Or.inr ⟨g, by omega, τs, hl, rfl⟩

/-! ## Literal bounds of the program -/

def rtSum {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => f x + rtSum f xs

theorem le_rtSum {α : Type} (f : α → Nat) : ∀ (l : List α) (x : α), x ∈ l → f x ≤ rtSum f l
  | [], x, h => by simp at h
  | y :: ys, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp only [rtSum]; omega
    · have := le_rtSum f ys x h; simp only [rtSum]; omega

def Key.lb : Key → Nat
  | .inst f τs => f + τs.length + rtSum Ty.wt τs
  | .meth tr m t => tr + m + t.wt
  | .userDrop n => n
  | .userClone n => n
  | .dropGlue t => t.wt
  | .cloneShim t => t.wt
  | .reifyShim f τs => f + τs.length + rtSum Ty.wt τs

theorem KB_of_lb (k : Key) : KB k.lb k := by
  cases k with
  | inst f τs => exact ⟨by simp only [Key.lb]; omega, by simp only [Key.lb]; omega,
      fun t ht => by have := le_rtSum Ty.wt τs t ht; simp only [Key.lb]; omega⟩
  | meth tr m t => exact ⟨by simp only [Key.lb]; omega, by simp only [Key.lb]; omega,
      by simp only [Key.lb]; omega⟩
  | userDrop n => simp [KB, Key.lb]
  | userClone n => simp [KB, Key.lb]
  | dropGlue t => simp [KB, Key.lb]
  | cloneShim t => simp [KB, Key.lb]
  | reifyShim f τs => exact ⟨by simp only [Key.lb]; omega, by simp only [Key.lb]; omega,
      fun t ht => by have := le_rtSum Ty.wt τs t ht; simp only [Key.lb]; omega⟩

def Stmt.lb : Stmt → Nat
  | .skip => 0
  | .seq a b => a.lb + b.lb
  | .emit _ => 0
  | .panic => 0
  | .call f τs => f + τs.length + rtSum Ty.wt τs
  | .invoke k => k.lb
  | .mcall tr m t => tr + m + t.wt
  | .drop t => t.wt
  | .clone t => t.wt
  | .reify _ f τs => f + τs.length + rtSum Ty.wt τs
  | .callPtr _ => 0
  | .unsize _ t tr => t.wt + tr
  | .callDyn _ _ => 0
  | .dropDyn _ => 0
  | .onUnwind a b => a.lb + b.lb
  | .cloneAgg ts => rtSum Ty.wt ts
  | .guard s => s.lb

def methLb (P : Program) : Nat := rtSum (fun e => rtSum id e.2) P.methods

theorem rt_lookup_mem {β : Type} : ∀ (l : List (Nat × β)) (a : Nat) (b : β), l.lookup a = some b → (a, b) ∈ l
  | [], a, b, h => by simp at h
  | (k, v) :: l, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hk; simp at h hk; subst h; subst hk; simp
    · exact List.mem_cons_of_mem _ (rt_lookup_mem l a b h)

theorem le_methLb (P : Program) (tr m : Nat) (h : m ∈ P.sig.methods tr) : m ≤ methLb P := by
  simp only [Program.sig] at h
  rcases hl : P.methods.lookup tr with _ | ms
  · rw [hl] at h; simp at h
  · rw [hl] at h; simp only [Option.getD_some] at h
    have hmem := rt_lookup_mem _ _ _ hl
    have h1 := le_rtSum id ms m h
    have h2 := le_rtSum (fun e : Nat × List Nat => rtSum id e.2) _ _ hmem
    simp only [id] at h1 h2
    unfold methLb; omega

theorem lb_cloneKey (t : Ty) : (cloneKey t).lb ≤ t.wt := by
  cases t <;> simp [cloneKey, Key.lb, Ty.wt]

theorem lb_refs (P : Program) : ∀ (s : Stmt) (k : Key), k ∈ refs P.sig s → k.lb ≤ s.lb + methLb P := by
  intro s
  induction s with
  | skip => intro k h; simp [refs] at h
  | seq a b iha ihb =>
    intro k h; simp only [refs, List.mem_append] at h
    rcases h with h | h
    · have := iha k h; simp only [Stmt.lb]; omega
    · have := ihb k h; simp only [Stmt.lb]; omega
  | emit _ => intro k h; simp [refs] at h
  | panic => intro k h; simp [refs] at h
  | call f τs => intro k h; simp [refs] at h; subst h; simp [Key.lb, Stmt.lb]
  | invoke k0 => intro k h; simp [refs] at h; subst h; simp [Stmt.lb]
  | mcall tr m t => intro k h; simp [refs] at h; subst h; simp [Key.lb, Stmt.lb]
  | drop t => intro k h; simp [refs] at h; subst h; simp [Key.lb, Stmt.lb]
  | clone t => intro k h; simp [refs] at h; subst h; have := lb_cloneKey t; simp only [Stmt.lb]; omega
  | reify j f τs =>
    intro k h; simp [refs] at h; subst h
    unfold reifyKey; split <;> simp [Key.lb, Stmt.lb]
  | callPtr _ => intro k h; simp [refs] at h
  | unsize j t tr =>
    intro k h
    simp only [refs, vtEntries, List.map_map, List.mem_append, List.mem_map, List.mem_singleton,
      Function.comp] at h
    rcases h with ⟨m, hm, rfl⟩ | rfl
    · have := le_methLb P tr m hm; simp only [Key.lb, Stmt.lb]; omega
    · simp only [Key.lb, Stmt.lb]; omega
  | callDyn _ _ => intro k h; simp [refs] at h
  | dropDyn _ => intro k h; simp [refs] at h
  | onUnwind a b iha ihb =>
    intro k h; simp only [refs, List.mem_append] at h
    rcases h with h | h
    · have := iha k h; simp only [Stmt.lb]; omega
    · have := ihb k h; simp only [Stmt.lb]; omega
  | cloneAgg ts =>
    intro k h
    simp only [refs, List.mem_append, List.mem_map] at h
    rcases h with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · have := lb_cloneKey t; have := le_rtSum Ty.wt ts t ht; simp only [Stmt.lb]; omega
    · have := le_rtSum Ty.wt ts t ht; simp only [Key.lb, Stmt.lb]; omega
  | guard s ih => intro k h; simp only [refs] at h; have := ih k h; simp only [Stmt.lb]; omega

/-! ## Normalization facts -/

theorem Key.norm_idem_rt (P : Program) (h : assocNormal P = true) (k : Key) :
    (k.norm P).norm P = k.norm P := by
  have hi := ty_norm_idem_of_assocNormal P h
  cases k <;> simp [Key.norm, hi]

theorem edgesM_norm (P : Program) (h : assocNormal P = true) (cfg : MonoCfg) (k k' : Key)
    (hk : k' ∈ edgesM P cfg k) : k'.norm P = k' := by
  unfold edgesM at hk
  split at hk
  · simp only [List.mem_map] at hk
    obtain ⟨x, _, rfl⟩ := hk
    exact Key.norm_idem_rt P h x
  · simp at hk

theorem rt_map_eq_self {α : Type} (f : α → α) : ∀ (l : List α), l.map f = l → ∀ x ∈ l, f x = x
  | [], _, x, hx => by simp at hx
  | y :: ys, h, x, hx => by
    simp only [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact rt_map_eq_self f ys h.2 x hx

/-! ## References of an instantiated body -/

theorem rt_clone_case (P : Program) (σ : List Ty) (t : Ty) :
    ((cloneKey t) ∈ [cloneKey t]) ∧
    (cloneKey ((t.subst σ).norm P.assoc) = ((cloneKey t).subst σ).norm P ∨
      ∃ t0, cloneKey t = .cloneShim t0 ∧
        cloneKey ((t.subst σ).norm P.assoc) = cloneKey ((t0.subst σ).norm P.assoc)) := by
  refine ⟨by simp, ?_⟩
  cases t with
  | base n => left; rfl
  | _ => right; exact ⟨_, rfl, rfl⟩

theorem refs_subst_norm (P : Program) (σ : List Ty) :
    ∀ (s : Stmt) (x : Key), x ∈ refs P.sig ((s.subst σ).norm P) →
      ∃ k0 ∈ refs P.sig s, x = (k0.subst σ).norm P ∨
        ∃ t0, k0 = .cloneShim t0 ∧ x = cloneKey ((t0.subst σ).norm P.assoc) := by
  intro s
  induction s with
  | skip => intro x h; simp [Stmt.subst, Stmt.norm, refs] at h
  | seq a b iha ihb =>
    intro x h
    simp only [Stmt.subst, Stmt.norm, refs, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨k0, hk0, hx⟩ := iha x h; exact ⟨k0, by simp [refs, hk0], hx⟩
    · obtain ⟨k0, hk0, hx⟩ := ihb x h; exact ⟨k0, by simp [refs, hk0], hx⟩
  | emit _ => intro x h; simp [Stmt.subst, Stmt.norm, refs] at h
  | panic => intro x h; simp [Stmt.subst, Stmt.norm, refs] at h
  | call f τs =>
    intro x h
    simp only [Stmt.subst, Stmt.norm, refs, List.mem_singleton] at h
    subst h
    exact ⟨.inst f τs, by simp [refs], Or.inl rfl⟩
  | invoke k =>
    intro x h
    simp only [Stmt.subst, Stmt.norm, refs, List.mem_singleton] at h
    subst h
    exact ⟨k, by simp [refs], Or.inl rfl⟩
  | mcall tr m t =>
    intro x h
    simp only [Stmt.subst, Stmt.norm, refs, List.mem_singleton] at h
    subst h
    exact ⟨.meth tr m t, by simp [refs], Or.inl rfl⟩
  | drop t =>
    intro x h
    simp only [Stmt.subst, Stmt.norm, refs, List.mem_singleton] at h
    subst h
    exact ⟨.dropGlue t, by simp [refs], Or.inl rfl⟩
  | clone t =>
    intro x h
    simp only [Stmt.subst, Stmt.norm, refs, List.mem_singleton] at h
    subst h
    obtain ⟨h1, h2⟩ := rt_clone_case P σ t
    rcases h2 with h2 | ⟨t0, h3, h4⟩
    · exact ⟨cloneKey t, by simp [refs], Or.inl h2⟩
    · exact ⟨cloneKey t, by simp [refs], Or.inr ⟨t0, h3, h4⟩⟩
  | reify j f τs =>
    intro x h
    simp only [Stmt.subst, Stmt.norm, refs, List.mem_singleton] at h
    subst h
    refine ⟨reifyKey P.sig f τs, by simp [refs], Or.inl ?_⟩
    unfold reifyKey; split <;> rfl
  | callPtr _ => intro x h; simp [Stmt.subst, Stmt.norm, refs] at h
  | unsize j t tr =>
    intro x h
    simp only [Stmt.subst, Stmt.norm, refs, vtEntries, List.map_map, List.mem_append,
      List.mem_map, List.mem_singleton, Function.comp] at h
    rcases h with ⟨m, hm, rfl⟩ | rfl
    · refine ⟨.meth tr m t, ?_, Or.inl rfl⟩
      simp only [refs, vtEntries, List.map_map, List.mem_append, List.mem_map, Function.comp]
      exact Or.inl ⟨m, hm, rfl⟩
    · exact ⟨.dropGlue t, by simp [refs], Or.inl rfl⟩
  | callDyn _ _ => intro x h; simp [Stmt.subst, Stmt.norm, refs] at h
  | dropDyn _ => intro x h; simp [Stmt.subst, Stmt.norm, refs] at h
  | onUnwind a b iha ihb =>
    intro x h
    simp only [Stmt.subst, Stmt.norm, refs, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨k0, hk0, hx⟩ := iha x h; exact ⟨k0, by simp [refs, hk0], hx⟩
    · obtain ⟨k0, hk0, hx⟩ := ihb x h; exact ⟨k0, by simp [refs, hk0], hx⟩
  | cloneAgg ts =>
    intro x h
    simp only [Stmt.subst, Stmt.norm, refs, List.map_map, List.mem_append, List.mem_map,
      Function.comp] at h
    rcases h with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · obtain ⟨_, h2⟩ := rt_clone_case P σ t
      have hm : cloneKey t ∈ refs P.sig (.cloneAgg ts) := by
        simp only [refs, List.mem_append, List.mem_map]; exact Or.inl ⟨t, ht, rfl⟩
      rcases h2 with h2 | ⟨t0, h3, h4⟩
      · exact ⟨cloneKey t, hm, Or.inl h2⟩
      · exact ⟨cloneKey t, hm, Or.inr ⟨t0, h3, h4⟩⟩
    · refine ⟨.dropGlue t, ?_, Or.inl rfl⟩
      simp only [refs, List.mem_append, List.mem_map]; exact Or.inr ⟨t, ht, rfl⟩
  | guard s ih =>
    intro x h
    simp only [Stmt.subst, Stmt.norm, refs] at h
    obtain ⟨k0, hk0, hx⟩ := ih x h; exact ⟨k0, by simp [refs, hk0], hx⟩

theorem rt_cloneKey_not_inst (t : Ty) (g : Nat) (us : List Ty) :
    cloneKey t ≠ .inst g us ∧ cloneKey t ≠ .reifyShim g us := by
  cases t <;> simp [cloneKey]

theorem instRefs_of_refs (sig : Sig) : ∀ (s : Stmt) (g : Nat) (us : List Ty),
    (Key.inst g us ∈ refs sig s ∨ Key.reifyShim g us ∈ refs sig s) → (g, us) ∈ instRefs s := by
  intro s
  induction s with
  | seq a b iha ihb =>
    intro g us h
    simp only [refs, List.mem_append] at h
    simp only [instRefs, List.mem_append]
    rcases h with (h | h) | (h | h)
    · exact Or.inl (iha g us (Or.inl h))
    · exact Or.inr (ihb g us (Or.inl h))
    · exact Or.inl (iha g us (Or.inr h))
    · exact Or.inr (ihb g us (Or.inr h))
  | onUnwind a b iha ihb =>
    intro g us h
    simp only [refs, List.mem_append] at h
    simp only [instRefs, List.mem_append]
    rcases h with (h | h) | (h | h)
    · exact Or.inl (iha g us (Or.inl h))
    · exact Or.inr (ihb g us (Or.inl h))
    · exact Or.inl (iha g us (Or.inr h))
    · exact Or.inr (ihb g us (Or.inr h))
  | guard s ih => intro g us h; exact ih g us h
  | call f τs => intro g us h; simp [refs] at h; simp [instRefs, h]
  | invoke k =>
    intro g us h
    cases k <;> simp [refs] at h <;> simp [instRefs, h]
  | reify j f τs =>
    intro g us h
    simp only [refs, reifyKey, List.mem_singleton] at h
    split at h <;> simp at h <;> simp [instRefs, h]
  | unsize j t tr =>
    intro g us h
    simp [refs, vtEntries] at h
  | clone t =>
    intro g us h
    simp only [refs, List.mem_singleton] at h
    have := rt_cloneKey_not_inst t g us
    rcases h with h | h
    · exact absurd h.symm this.1
    · exact absurd h.symm this.2
  | cloneAgg ts =>
    intro g us h
    simp only [refs, List.mem_append, List.mem_map] at h
    rcases h with (⟨t, _, h⟩ | ⟨t, _, h⟩) | (⟨t, _, h⟩ | ⟨t, _, h⟩)
    · exact absurd h (rt_cloneKey_not_inst t g us).1
    · cases h
    · exact absurd h (rt_cloneKey_not_inst t g us).2
    · cases h
  | _ => intro g us h; simp [refs] at h

/-! ## Weight bounds for transformed literal keys -/

theorem rt_ty_bound (P : Program) (σ : List Ty) (M W : Nat) (hM : 1 ≤ M) (hW : 1 ≤ W)
    (hA : ∀ e ∈ P.assoc, e.2.2.wt ≤ M) (hσ : ∀ s ∈ σ, s.wt ≤ W) (t : Ty) (ht : t.wt ≤ M) :
    ((t.subst σ).norm P.assoc).wt ≤ M * M * W := by
  have h1 := Ty.wt_norm P.assoc M hM hA (t.subst σ)
  have h2 := Ty.wt_subst σ W hW hσ t
  have h3 : t.wt * W ≤ M * W := Nat.mul_le_mul_right W ht
  have h4 : M * (t.subst σ).wt ≤ M * (M * W) := Nat.mul_le_mul_left M (Nat.le_trans h2 h3)
  rw [← Nat.mul_assoc] at h4
  omega

theorem rt_lab_bound (M W : Nat) (hM : 1 ≤ M) (hW : 1 ≤ W) : M ≤ M * M * W := by
  have : M * 1 * 1 ≤ M * M * W := Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl M) hM) hW
  simpa using this

theorem KB_subst_norm (P : Program) (σ : List Ty) (M W : Nat) (hM : 1 ≤ M) (hW : 1 ≤ W)
    (hA : ∀ e ∈ P.assoc, e.2.2.wt ≤ M) (hσ : ∀ s ∈ σ, s.wt ≤ W) (k0 : Key) (hk0 : KB M k0) :
    KB (M * M * W) ((k0.subst σ).norm P) := by
  have hty := rt_ty_bound P σ M W hM hW hA hσ
  have hlab := rt_lab_bound M W hM hW
  cases k0 with
  | inst f τs =>
    obtain ⟨h1, h2, h3⟩ := hk0
    simp only [Key.subst, Key.norm, KB, List.length_map, List.map_map, List.mem_map,
      Function.comp]
    refine ⟨by omega, by omega, ?_⟩
    rintro _ ⟨u, hu, rfl⟩; exact hty u (h3 u hu)
  | meth tr m t =>
    obtain ⟨h1, h2, h3⟩ := hk0
    simp only [Key.subst, Key.norm, KB]
    exact ⟨by omega, by omega, hty t h3⟩
  | userDrop n => simp only [Key.subst, Key.norm, KB] at hk0 ⊢; omega
  | userClone n => simp only [Key.subst, Key.norm, KB] at hk0 ⊢; omega
  | dropGlue t => simp only [Key.subst, Key.norm, KB] at hk0 ⊢; exact hty t hk0
  | cloneShim t => simp only [Key.subst, Key.norm, KB] at hk0 ⊢; exact hty t hk0
  | reifyShim f τs =>
    obtain ⟨h1, h2, h3⟩ := hk0
    simp only [Key.subst, Key.norm, KB, List.length_map, List.map_map, List.mem_map,
      Function.comp]
    refine ⟨by omega, by omega, ?_⟩
    rintro _ ⟨u, hu, rfl⟩; exact hty u (h3 u hu)

/-- The normalized clone key of a type `c` is bounded by the weight of `c.norm`. -/
theorem KB_norm_cloneKey (P : Program) (c : Ty) :
    KB (c.norm P.assoc).wt ((cloneKey c).norm P) := by
  cases c with
  | base n => simp [cloneKey, Key.norm, KB, Ty.norm, Ty.wt]
  | _ => simp [cloneKey, Key.norm, KB]

theorem norm_cloneKey_kind (P : Program) (c : Ty) :
    (∃ n, (cloneKey c).norm P = .userClone n) ∨ (∃ t, (cloneKey c).norm P = .cloneShim t) := by
  cases c with
  | base n => left; exact ⟨n, rfl⟩
  | _ => right; exact ⟨_, rfl⟩

/-! ## Empty substitution -/

theorem Ty.subst_nil_rt : ∀ t : Ty, t.subst [] = t := by
  intro t
  induction t with
  | param i => simp [Ty.subst]
  | box t ih => simp [Ty.subst, ih]
  | pair a b iha ihb => simp [Ty.subst, iha, ihb]
  | proj tr t ih => simp [Ty.subst, ih]
  | _ => rfl

theorem Ty.subst_nil_fun_rt : Ty.subst [] = id := funext Ty.subst_nil_rt

theorem Key.subst_nil_rt (k : Key) : k.subst [] = k := by
  cases k <;> simp [Key.subst, Ty.subst_nil_rt, Ty.subst_nil_fun_rt]

theorem Stmt.subst_nil_rt : ∀ s : Stmt, s.subst [] = s := by
  intro s
  induction s with
  | seq a b iha ihb => simp [Stmt.subst, iha, ihb]
  | onUnwind a b iha ihb => simp [Stmt.subst, iha, ihb]
  | guard s ih => simp [Stmt.subst, ih]
  | _ => simp [Stmt.subst, Ty.subst_nil_rt, Key.subst_nil_rt, Ty.subst_nil_fun_rt]

/-! ## Edges, key by key -/

theorem mem_edgesM_rt (P : Program) (k k' : Key) (h : k' ∈ edgesM P (stdCfg P) k) :
    ∃ b, bodyM P (stdCfg P) k = some b ∧ ∃ x ∈ refs P.sig b, k' = x.norm P := by
  unfold edgesM at h
  split at h
  · rename_i b hb
    simp only [List.mem_map] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact ⟨b, hb, x, hx, rfl⟩
  · simp at h

theorem rt_getElem?_some {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    i < l.length ∧ a ∈ l := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, rfl⟩
  exact ⟨hi, List.getElem_mem hi⟩

theorem rt_fixed_edge (P : Program) (hassoc : assocNormal P = true) (M W : Nat) (hM : 1 ≤ M)
    (hW : 1 ≤ W) (hA : ∀ e ∈ P.assoc, e.2.2.wt ≤ M) (σ : List Ty) (hσ : ∀ s ∈ σ, s.wt ≤ W)
    (b0 : Stmt) (hb0 : ∀ k ∈ refs P.sig b0, KB M k) (x : Key)
    (hx : x ∈ refs P.sig ((b0.subst σ).norm P)) : KB (M * M * W) (x.norm P) := by
  obtain ⟨k0, hk0, h⟩ := refs_subst_norm P σ b0 x hx
  rcases h with rfl | ⟨t0, rfl, rfl⟩
  · rw [Key.norm_idem_rt P hassoc]
    exact KB_subst_norm P σ M W hM hW hA hσ k0 (hb0 k0 hk0)
  · have hc := KB_norm_cloneKey P ((t0.subst σ).norm P.assoc)
    rw [ty_norm_idem_of_assocNormal P hassoc] at hc
    have ht0 : t0.wt ≤ M := by have := hb0 _ hk0; simpa [KB] using this
    exact KB.mono (rt_ty_bound P σ M W hM hW hA hσ t0 ht0) hc

theorem rt_arg_bound (P : Program) (M W bg : Nat) (hM : 1 ≤ M)
    (hA : ∀ e ∈ P.assoc, e.2.2.wt ≤ M) (τs : List Ty)
    (hτ : ∀ s ∈ τs, s.norm P.assoc = s ∧ s.wt ≤ W) (hW : W ≤ bg) (hC : M * M ≤ bg)
    (u : Ty) (hu : u.wt ≤ M) (hg : u.grows = false) : ((u.subst τs).norm P.assoc).wt ≤ bg := by
  have hMM : M ≤ M * M := Nat.le_mul_of_pos_left M hM
  by_cases hp : ∃ i, u = .param i
  · obtain ⟨i, rfl⟩ := hp
    simp only [Ty.subst]
    rcases rt_getD_mem_or τs i (.param i) with h | h
    · obtain ⟨h1, h2⟩ := hτ _ h; rw [h1]; omega
    · rw [h]; simp only [Ty.norm]; simp only [Ty.wt] at hu ⊢; omega
  · have hp' : u.hasParam = false := by
      cases u with
      | param i => exact absurd ⟨i, rfl⟩ hp
      | _ => exact hg
    rw [Ty.subst_of_hasParam_false τs u hp']
    have h1 := Ty.wt_norm P.assoc M hM hA u
    have h2 : M * u.wt ≤ M * M := Nat.mul_le_mul_left M hu
    omega

theorem rt_rankCheck (P : Program) (rank : Nat → Nat) (h : rankCheck P rank = true) (f : Nat)
    (hf : f < P.fns.length) (fd : FnDef) (hfd : P.fns[f]? = some fd) (g : Nat) (us : List Ty)
    (hr : (g, us) ∈ instRefs fd.body) :
    (us.any Ty.grows = true → rank g < rank f) ∧ (us.any Ty.grows = false → rank g ≤ rank f) := by
  unfold rankCheck at h
  have h1 := (List.all_eq_true.mp h) f (List.mem_range.mpr hf)
  rw [hfd] at h1
  simp only at h1
  have h2 := (List.all_eq_true.mp h1) (g, us) hr
  simp only at h2
  constructor
  · intro hg; rw [hg] at h2; simpa using h2
  · intro hg; rw [hg] at h2; simpa using h2

/-- Rank-indexed bound on instance arguments. -/
def InstB (bnd : Nat → Nat) (len : Nat) : Key → Prop
  | .inst g τs => g < len → ∀ t ∈ τs, t.wt ≤ bnd g
  | .reifyShim g τs => g < len → ∀ t ∈ τs, t.wt ≤ bnd g
  | _ => True

theorem InstB_of_KB (bnd : Nat → Nat) (len C : Nat) (hC : ∀ g, C ≤ bnd g) (k : Key) (h : KB C k) :
    InstB bnd len k := by
  cases k with
  | inst g τs => intro _ t ht; exact Nat.le_trans (h.2.2 t ht) (hC g)
  | reifyShim g τs => intro _ t ht; exact Nat.le_trans (h.2.2 t ht) (hC g)
  | _ => exact trivial

theorem rt_child_bound (A : List (Nat × Ty × Ty)) (M N : Nat) (hM : 1 ≤ M)
    (hA : ∀ e ∈ A, e.2.2.wt ≤ M) (hMMN : M * M ≤ N) (t c : Ty)
    (hT : t.wt ≤ M ∨ (t.norm A = t ∧ t.wt ≤ N)) (hlt : c.wt < t.wt)
    (hcn : t.norm A = t → c.norm A = c) : (c.norm A).wt ≤ N := by
  rcases hT with h | ⟨h1, h2⟩
  · have := Ty.wt_norm A M hM hA c
    have : M * c.wt ≤ M * M := Nat.mul_le_mul_left M (by omega)
    omega
  · rw [hcn h1]; omega

/-! ## The closure step -/

theorem rt_step (P : Program) (rank : Nat → Nat) (hrank : rankCheck P rank = true)
    (hassoc : assocNormal P = true) (roots : List Key) (M N : Nat) (bnd : Nat → Nat)
    (hM : 1 ≤ M) (hA : ∀ e ∈ P.assoc, e.2.2.wt ≤ M)
    (hFn : ∀ fd ∈ P.fns, ∀ k ∈ refs P.sig fd.body, KB M k)
    (hImpl : ∀ e ∈ P.impls, ∀ k ∈ refs P.sig e.body, KB M k)
    (hDrop : ∀ e ∈ P.dropImpls, ∀ k ∈ refs P.sig e.2, KB M k)
    (hClone : ∀ e ∈ P.cloneImpls, ∀ k ∈ refs P.sig e.2, KB M k)
    (hRoot : ∀ k ∈ roots, KB M k)
    (hC : ∀ g, M * M * M ≤ bnd g) (hCN : M * M * M ≤ N)
    (hN : ∀ g, g < P.fns.length → M * M * bnd g ≤ N)
    (hGrow : ∀ f g, f < P.fns.length → rank g < rank f → M * M * bnd f ≤ bnd g)
    (hFlat : ∀ f g, rank g ≤ rank f → bnd f ≤ bnd g)
    (k k' : Key) (hk : k ∈ roots ∨ (k.norm P = k ∧ KB N k ∧ InstB bnd P.fns.length k))
    (hk' : k' ∈ edgesM P (stdCfg P) k) : KB N k' ∧ InstB bnd P.fns.length k' := by
  have hMM : M ≤ M * M := Nat.le_mul_of_pos_left M hM
  have hMMM : M * M ≤ M * M * M := Nat.le_mul_of_pos_right _ hM
  have hMN : M ≤ N := by omega
  have hMMN : M * M ≤ N := by omega
  have hC1 : ∀ g, 1 ≤ bnd g := fun g => by have := hC g; omega
  have hfixed : ∀ b0 : Stmt, (∀ k ∈ refs P.sig b0, KB M k) → ∀ x ∈ refs P.sig (b0.norm P),
      KB N (x.norm P) ∧ InstB bnd P.fns.length (x.norm P) := by
    intro b0 hb0 x hx
    have hx' : x ∈ refs P.sig ((b0.subst []).norm P) := by rw [Stmt.subst_nil_rt]; exact hx
    have h := rt_fixed_edge P hassoc M 1 hM (Nat.le_refl 1) hA [] (by simp) b0 hb0 x hx'
    rw [Nat.mul_one] at h
    exact ⟨KB.mono (by omega) h, InstB_of_KB bnd _ (M * M * M) hC _ (KB.mono hMMM h)⟩
  obtain ⟨b, hb, x, hx, rfl⟩ := mem_edgesM_rt P k k' hk'
  cases k with
  | inst f τs =>
    change (P.fns[f]?).map (fun fd => (fd.body.subst τs).norm P) = some b at hb
    rcases hfd : P.fns[f]? with _ | fd
    · rw [hfd] at hb; cases hb
    rw [hfd] at hb; simp at hb; subst hb
    obtain ⟨hf, hfdm⟩ := rt_getElem?_some hfd
    have hb0 := hFn fd hfdm
    rcases hk with hroot | ⟨hn, hkb, hib⟩
    · have hτ : ∀ s ∈ τs, s.wt ≤ M := (hRoot _ hroot).2.2
      have h := rt_fixed_edge P hassoc M M hM hM hA τs hτ fd.body hb0 x hx
      exact ⟨KB.mono hCN h, InstB_of_KB bnd _ _ hC _ h⟩
    · have hτ : ∀ s ∈ τs, s.wt ≤ bnd f := hib hf
      have h := rt_fixed_edge P hassoc M (bnd f) hM (hC1 f) hA τs hτ fd.body hb0 x hx
      refine ⟨KB.mono (hN f hf) h, ?_⟩
      have hnorm : ∀ s ∈ τs, s.norm P.assoc = s := by
        simp only [Key.norm, Key.inst.injEq, true_and] at hn
        exact rt_map_eq_self _ τs hn
      obtain ⟨k0, hk0, hxk⟩ := refs_subst_norm P τs fd.body x hx
      rcases hxk with rfl | ⟨t0, rfl, rfl⟩
      · rw [Key.norm_idem_rt P hassoc]
        have hkb0 := hb0 k0 hk0
        have key : ∀ g us, (k0 = .inst g us ∨ k0 = .reifyShim g us) → g < P.fns.length →
            ∀ t ∈ ((us.map (Ty.subst τs)).map (Ty.norm P.assoc)), t.wt ≤ bnd g := by
          intro g us hk0eq hg t ht
          have hir : (g, us) ∈ instRefs fd.body := by
            apply instRefs_of_refs P.sig fd.body g us
            rcases hk0eq with rfl | rfl
            · exact Or.inl hk0
            · exact Or.inr hk0
          have hus : ∀ u ∈ us, u.wt ≤ M := by
            rcases hk0eq with rfl | rfl
            · exact hkb0.2.2
            · exact hkb0.2.2
          obtain ⟨hr1, hr2⟩ := rt_rankCheck P rank hrank f hf fd hfd g us hir
          simp only [List.map_map, List.mem_map, Function.comp] at ht
          obtain ⟨u, hu, rfl⟩ := ht
          cases hany : us.any Ty.grows
          · have hflat := hr2 hany
            have hng : u.grows = false := by
              have := List.any_eq_false.mp hany u hu; simpa using this
            exact rt_arg_bound P M (bnd f) (bnd g) hM hA τs (fun s hs => ⟨hnorm s hs, hτ s hs⟩)
              (hFlat f g hflat) (Nat.le_trans hMMM (hC g)) u (hus u hu) hng
          · have hlt := hr1 hany
            exact Nat.le_trans (rt_ty_bound P τs M (bnd f) hM (hC1 f) hA hτ u (hus u hu))
              (hGrow f g hf hlt)
        cases k0 with
        | inst g us => exact key g us (Or.inl rfl)
        | reifyShim g us => exact key g us (Or.inr rfl)
        | _ => exact trivial
      · rcases norm_cloneKey_kind P ((t0.subst τs).norm P.assoc) with ⟨n, hn'⟩ | ⟨t1, ht1⟩
        · rw [hn']; exact trivial
        · rw [ht1]; exact trivial
  | meth tr m t =>
    change (implLookup P tr m t).map (Stmt.norm P) = some b at hb
    rcases hl : implLookup P tr m t with _ | b0
    · rw [hl] at hb; cases hb
    · rw [hl] at hb; simp at hb; subst hb
      unfold implLookup at hl
      rcases hf : P.impls.find? (fun e => decide (e.tr = tr ∧ e.m = m ∧ e.ty = t)) with _ | e
      · rw [hf] at hl; cases hl
      · rw [hf] at hl; simp at hl; subst hl
        exact hfixed e.body (hImpl e (List.mem_of_find?_eq_some hf)) x hx
  | userDrop n =>
    change (natLookup P.dropImpls n).map (Stmt.norm P) = some b at hb
    rcases hl : natLookup P.dropImpls n with _ | b0
    · rw [hl] at hb; cases hb
    · rw [hl] at hb; simp at hb; subst hb
      exact hfixed b0 (hDrop (n, b0) (rt_lookup_mem _ _ _ hl)) x hx
  | userClone n =>
    change (natLookup P.cloneImpls n).map (Stmt.norm P) = some b at hb
    rcases hl : natLookup P.cloneImpls n with _ | b0
    · rw [hl] at hb; cases hb
    · rw [hl] at hb; simp at hb; subst hb
      exact hfixed b0 (hClone (n, b0) (rt_lookup_mem _ _ _ hl)) x hx
  | dropGlue t =>
    change glueSrc P t = some b at hb
    have hT : t.wt ≤ M ∨ (t.norm P.assoc = t ∧ t.wt ≤ N) := by
      rcases hk with hroot | ⟨hn, hkb, _⟩
      · exact Or.inl (hRoot _ hroot)
      · simp only [Key.norm, Key.dropGlue.injEq] at hn
        exact Or.inr ⟨hn, hkb⟩
    have hch := rt_child_bound P.assoc M N hM hA hMMN t
    cases t with
    | base n =>
      simp only [glueSrc, Option.some.injEq] at hb
      subst hb
      split at hx
      · simp only [refs, List.mem_singleton] at hx; subst hx
        refine ⟨?_, trivial⟩
        simp only [Key.norm, KB]
        rcases hT with h | ⟨_, h⟩ <;> simp only [Ty.wt] at h <;> omega
      · simp [refs] at hx
    | box c =>
      simp only [glueSrc, Option.some.injEq] at hb; subst hb
      simp only [refs, List.mem_singleton] at hx; subst hx
      refine ⟨?_, trivial⟩
      exact hch c hT (by simp only [Ty.wt]; omega)
        (fun h => by simp only [Ty.norm, Ty.box.injEq] at h; exact h)
    | pair a c =>
      simp only [glueSrc, Option.some.injEq] at hb; subst hb
      simp only [refs, List.mem_append, List.mem_singleton] at hx
      rcases hx with (rfl | rfl) | rfl
      · exact ⟨hch a hT (by simp only [Ty.wt]; omega)
          (fun h => by simp only [Ty.norm, Ty.pair.injEq] at h; exact h.1), trivial⟩
      · exact ⟨hch c hT (by simp only [Ty.wt]; omega)
          (fun h => by simp only [Ty.norm, Ty.pair.injEq] at h; exact h.2), trivial⟩
      · exact ⟨hch c hT (by simp only [Ty.wt]; omega)
          (fun h => by simp only [Ty.norm, Ty.pair.injEq] at h; exact h.2), trivial⟩
    | fnPtr =>
      simp only [glueSrc, Option.some.injEq] at hb; subst hb
      simp [refs] at hx
    | dyn n => simp [glueSrc] at hb
    | param i => simp [glueSrc] at hb
    | proj tr t => simp [glueSrc] at hb
  | cloneShim t =>
    change synthStd P (.cloneShim t) = some b at hb
    have hT : t.wt ≤ M ∨ (t.norm P.assoc = t ∧ t.wt ≤ N) := by
      rcases hk with hroot | ⟨hn, hkb, _⟩
      · exact Or.inl (hRoot _ hroot)
      · simp only [Key.norm, Key.cloneShim.injEq] at hn
        exact Or.inr ⟨hn, hkb⟩
    have hch := rt_child_bound P.assoc M N hM hA hMMN t
    have hcl : ∀ c, c.wt < t.wt → (t.norm P.assoc = t → c.norm P.assoc = c) →
        KB N ((cloneKey c).norm P) ∧ InstB bnd P.fns.length ((cloneKey c).norm P) := by
      intro c hlt hcn
      refine ⟨KB.mono (hch c hT hlt hcn) (KB_norm_cloneKey P c), ?_⟩
      rcases norm_cloneKey_kind P c with ⟨n, hn'⟩ | ⟨t1, ht1⟩
      · rw [hn']; exact trivial
      · rw [ht1]; exact trivial
    cases t with
    | pair a c =>
      simp only [synthStd, Option.some.injEq] at hb; subst hb
      have ha1 : a.wt < (Ty.pair a c).wt := by simp only [Ty.wt]; omega
      have hc1 : c.wt < (Ty.pair a c).wt := by simp only [Ty.wt]; omega
      have ha2 : (Ty.pair a c).norm P.assoc = Ty.pair a c → a.norm P.assoc = a :=
        fun h => by simp only [Ty.norm, Ty.pair.injEq] at h; exact h.1
      have hc2 : (Ty.pair a c).norm P.assoc = Ty.pair a c → c.norm P.assoc = c :=
        fun h => by simp only [Ty.norm, Ty.pair.injEq] at h; exact h.2
      simp [ladder, refs] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hcl a ha1 ha2
      · exact hcl c hc1 hc2
      · exact ⟨hch c hT hc1 hc2, trivial⟩
      · exact ⟨hch a hT ha1 ha2, trivial⟩
    | fnPtr =>
      simp only [synthStd, Option.some.injEq] at hb; subst hb
      simp [refs] at hx
    | base n => simp [synthStd] at hb
    | box c => simp [synthStd] at hb
    | dyn n => simp [synthStd] at hb
    | param i => simp [synthStd] at hb
    | proj tr c => simp [synthStd] at hb
  | reifyShim g us =>
    change (P.fns[g]?).map (fun _ => Stmt.call g us) = some b at hb
    rcases hfd : P.fns[g]? with _ | fd
    · rw [hfd] at hb; cases hb
    rw [hfd] at hb; simp at hb; subst hb
    simp only [refs, List.mem_singleton] at hx
    subst hx
    rcases hk with hroot | ⟨hn, hkb, hib⟩
    · obtain ⟨h1, h2, h3⟩ := hRoot _ hroot
      have hkc : KB (M * M * M) ((Key.inst g us).norm P) := by
        simp only [Key.norm, KB, List.length_map, List.mem_map]
        refine ⟨by omega, by omega, ?_⟩
        rintro _ ⟨u, hu, rfl⟩
        have := Ty.wt_norm P.assoc M hM hA u
        have : M * u.wt ≤ M * M := Nat.mul_le_mul_left M (h3 u hu)
        omega
      exact ⟨KB.mono hCN hkc, InstB_of_KB bnd _ _ hC _ hkc⟩
    · simp only [Key.norm, Key.reifyShim.injEq, true_and] at hn
      simp only [Key.norm, hn]
      exact ⟨hkb, hib⟩

/-! ## Constants -/

/-- A bound on every literal label, list length and type weight in the program and the roots. -/
def litM (P : Program) (roots : List Key) : Nat :=
  1 + rtSum (fun fd : FnDef => fd.body.lb) P.fns + rtSum (fun e : ImplEntry => e.body.lb) P.impls +
    rtSum (fun e : Nat × Stmt => e.2.lb) P.dropImpls +
    rtSum (fun e : Nat × Stmt => e.2.lb) P.cloneImpls +
    rtSum (fun e : Nat × Ty × Ty => e.2.2.wt) P.assoc + methLb P + rtSum Key.lb roots

theorem litM_pos (P : Program) (roots : List Key) : 1 ≤ litM P roots := by
  unfold litM; omega

theorem litM_assoc (P : Program) (roots : List Key) : ∀ e ∈ P.assoc, e.2.2.wt ≤ litM P roots := by
  intro e he
  have h : e.2.2.wt ≤ rtSum (fun e : Nat × Ty × Ty => e.2.2.wt) P.assoc :=
    le_rtSum (fun e : Nat × Ty × Ty => e.2.2.wt) _ e he
  unfold litM; omega

theorem litM_fns (P : Program) (roots : List Key) :
    ∀ fd ∈ P.fns, ∀ k ∈ refs P.sig fd.body, KB (litM P roots) k := by
  intro fd hfd k hk
  have h1 : fd.body.lb ≤ rtSum (fun fd : FnDef => fd.body.lb) P.fns :=
    le_rtSum (fun fd : FnDef => fd.body.lb) _ fd hfd
  have h2 := lb_refs P fd.body k hk
  refine KB.mono ?_ (KB_of_lb k)
  unfold litM; omega

theorem litM_impls (P : Program) (roots : List Key) :
    ∀ e ∈ P.impls, ∀ k ∈ refs P.sig e.body, KB (litM P roots) k := by
  intro e he k hk
  have h1 : e.body.lb ≤ rtSum (fun e : ImplEntry => e.body.lb) P.impls :=
    le_rtSum (fun e : ImplEntry => e.body.lb) _ e he
  have h2 := lb_refs P e.body k hk
  refine KB.mono ?_ (KB_of_lb k)
  unfold litM; omega

theorem litM_drops (P : Program) (roots : List Key) :
    ∀ e ∈ P.dropImpls, ∀ k ∈ refs P.sig e.2, KB (litM P roots) k := by
  intro e he k hk
  have h1 : e.2.lb ≤ rtSum (fun e : Nat × Stmt => e.2.lb) P.dropImpls :=
    le_rtSum (fun e : Nat × Stmt => e.2.lb) _ e he
  have h2 := lb_refs P e.2 k hk
  refine KB.mono ?_ (KB_of_lb k)
  unfold litM; omega

theorem litM_clones (P : Program) (roots : List Key) :
    ∀ e ∈ P.cloneImpls, ∀ k ∈ refs P.sig e.2, KB (litM P roots) k := by
  intro e he k hk
  have h1 : e.2.lb ≤ rtSum (fun e : Nat × Stmt => e.2.lb) P.cloneImpls :=
    le_rtSum (fun e : Nat × Stmt => e.2.lb) _ e he
  have h2 := lb_refs P e.2 k hk
  refine KB.mono ?_ (KB_of_lb k)
  unfold litM; omega

theorem litM_roots (P : Program) (roots : List Key) : ∀ k ∈ roots, KB (litM P roots) k := by
  intro k hk
  have h1 : k.lb ≤ rtSum Key.lb roots := le_rtSum _ _ k hk
  refine KB.mono ?_ (KB_of_lb k)
  unfold litM; omega

/-- Maximum of `rank` below `n`. -/
def maxUpTo (rank : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => max (rank n) (maxUpTo rank n)

theorem le_maxUpTo (rank : Nat → Nat) : ∀ n f, f < n → rank f ≤ maxUpTo rank n
  | 0, f, h => absurd h (Nat.not_lt_zero _)
  | n + 1, f, h => by
    simp only [maxUpTo]
    by_cases hf : f = n
    · subst hf; exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_maxUpTo rank n f (by omega)) (Nat.le_max_right _ _)

theorem rt_grow_arith (C K d e : Nat) (hK : 1 ≤ K) (hde : d + 1 ≤ e) :
    K * (C * K ^ d) ≤ C * K ^ e := by
  have h1 : K * (C * K ^ d) = C * K ^ (d + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm K (C * K ^ d), Nat.mul_assoc]
  rw [h1]
  exact Nat.mul_le_mul_left C (Nat.pow_le_pow_right hK hde)

theorem rt_mono_arith (C K d e : Nat) (hK : 1 ≤ K) (hde : d ≤ e) : C * K ^ d ≤ C * K ^ e :=
  Nat.mul_le_mul_left C (Nat.pow_le_pow_right hK hde)

theorem rt_base_arith (C K d : Nat) (hK : 1 ≤ K) : C ≤ C * K ^ d := by
  have h1 : 1 ≤ K ^ d := Nat.pow_pos hK
  have h2 := Nat.mul_le_mul_left C h1
  simpa using h2

/-- The whole argument with the constants abstracted. -/
theorem rt_main (P : Program) (rank : Nat → Nat)
    (hrank : rankCheck P rank = true) (hassoc : assocNormal P = true)
    (sched : List Key → List Key → List Key) (hs : SchedOK sched) (roots : List Key) :
    ∃ fuel T, collect (edgesM P (stdCfg P)) sched roots fuel = some T := by
  obtain ⟨M, hMdef⟩ : ∃ M, M = litM P roots := ⟨_, rfl⟩
  have hM : 1 ≤ M := hMdef ▸ litM_pos P roots
  have hA : ∀ e ∈ P.assoc, e.2.2.wt ≤ M := hMdef ▸ litM_assoc P roots
  have hFn : ∀ fd ∈ P.fns, ∀ k ∈ refs P.sig fd.body, KB M k := hMdef ▸ litM_fns P roots
  have hImpl : ∀ e ∈ P.impls, ∀ k ∈ refs P.sig e.body, KB M k := hMdef ▸ litM_impls P roots
  have hDrop : ∀ e ∈ P.dropImpls, ∀ k ∈ refs P.sig e.2, KB M k := hMdef ▸ litM_drops P roots
  have hClone : ∀ e ∈ P.cloneImpls, ∀ k ∈ refs P.sig e.2, KB M k := hMdef ▸ litM_clones P roots
  have hRoot : ∀ k ∈ roots, KB M k := hMdef ▸ litM_roots P roots
  obtain ⟨R, hRdef⟩ : ∃ R, R = maxUpTo rank P.fns.length := ⟨_, rfl⟩
  have hK : 1 ≤ M * M := Nat.mul_pos hM hM
  let bnd : Nat → Nat := fun g => M * M * M * (M * M) ^ (R - rank g)
  let N : Nat := M * M * (M * M * M * (M * M) ^ R)
  have hC : ∀ g, M * M * M ≤ bnd g := fun g => rt_base_arith _ _ _ hK
  have hCN : M * M * M ≤ N := by
    have h1 : M * M * M ≤ M * M * M * (M * M) ^ R := rt_base_arith _ _ _ hK
    have h2 : M * M * M * (M * M) ^ R ≤ N := Nat.le_mul_of_pos_left _ hK
    omega
  have hN : ∀ g, g < P.fns.length → M * M * bnd g ≤ N := fun g _ =>
    Nat.mul_le_mul_left _ (rt_mono_arith _ _ _ _ hK (Nat.sub_le R (rank g)))
  have hGrow : ∀ f g, f < P.fns.length → rank g < rank f → M * M * bnd f ≤ bnd g := by
    intro f g hf hlt
    have hfR : rank f ≤ R := hRdef ▸ le_maxUpTo rank _ f hf
    exact rt_grow_arith _ _ _ _ hK (by omega)
  have hFlat : ∀ f g, rank g ≤ rank f → bnd f ≤ bnd g := fun f g h =>
    rt_mono_arith _ _ _ _ hK (by omega)
  have hinv : ∀ k, Reach (edgesM P (stdCfg P)) roots k →
      k ∈ roots ∨ (k.norm P = k ∧ KB N k ∧ InstB bnd P.fns.length k) := by
    intro k hk
    induction hk with
    | root h => exact Or.inl h
    | step _ he ih =>
      have h := rt_step P rank hrank hassoc roots M N bnd hM hA hFn hImpl hDrop hClone hRoot
        hC hCN hN hGrow hFlat _ _ ih he
      exact Or.inr ⟨edgesM_norm P hassoc _ _ _ he, h⟩
  have hU : ∀ k, Reach (edgesM P (stdCfg P)) roots k → k ∈ roots ++ allKeys N := by
    intro k hk
    rcases hinv k hk with h | ⟨_, h, _⟩
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (mem_allKeys N k h)
  obtain ⟨fuel, T, h⟩ := rt_collectGo_terminates (edgesM P (stdCfg P)) sched hs
    (roots ++ allKeys N) (Reach (edgesM P (stdCfg P)) roots)
    (fun k hk k' hk' => Reach.step hk hk') hU _ [] rfl roots (fun k hk => Reach.root hk)
  exact ⟨fuel, T, h⟩


/-- **Termination under the rank check and a normal associated-type table.** If some rank
certificate passes `rankCheck` and every right-hand side of `P.assoc` is in normal form
(`assocNormal`), then for every admissible scheduler and every root list the standard collector
returns a set for some fuel. -/
theorem collect_terminates_of_rankCheck_of_assocNormal (P : Program) (rank : Nat → Nat)
    (hrank : rankCheck P rank = true) (hassoc : assocNormal P = true)
    (sched : List Key → List Key → List Key) (hs : SchedOK sched) (roots : List Key) :
    ∃ fuel T, collect (edgesM P (stdCfg P)) sched roots fuel = some T := by
  exact rt_main P rank hrank hassoc sched hs roots

end Toy.MonoShim
