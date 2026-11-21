import ToyTwoPhase.Checkers

/-!
# Supporting lemmas for the main results

General facts about walks and `PathVia`, the characterization of the forward may-analysis,
the run invariant behind the soundness of the exact-phase checker, and the walk argument behind
the soundness of the dominator test.
-/

namespace Toy.TwoPhase

variable {n : Nat}

/-! ## `PathVia` toolkit -/

theorem pathVia_refl (E : Edges n) (ok : Fin n → Bool) (u : Fin n) : PathVia E ok u u :=
  ⟨[], trivial, rfl, by simp⟩

theorem pathVia_cons {E : Edges n} {ok : Fin n → Bool} {u w v : Fin n}
    (hu : ok u = true) (hw : w ∈ E u) (h : PathVia E ok w v) : PathVia E ok u v := by
  obtain ⟨π, hπ, hh, hall⟩ := h
  refine ⟨u :: π, ?_, rfl, ?_⟩
  · cases π with
    | nil => simp at hh; subst hh; exact ⟨hw, trivial⟩
    | cons c t => simp at hh; subst hh; exact ⟨hw, hπ⟩
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hu
    · exact hall x hx

theorem pathVia_snoc {E : Edges n} {ok : Fin n → Bool} {u v w : Fin n}
    (h : PathVia E ok u v) (hv : ok v = true) (hw : w ∈ E v) : PathVia E ok u w := by
  obtain ⟨π, hπ, hh, hall⟩ := h
  refine ⟨π ++ [v], ?_, ?_, ?_⟩
  · have := isWalk_append_pair E v w hw π hπ
    simpa [List.append_assoc] using this
  · have := head?_append_pair π v w
    simp only [List.append_assoc, List.cons_append, List.nil_append] at this ⊢
    rw [this]; exact hh
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hall x hx
    · simp at hx; subst hx; exact hv

theorem pathVia_trans {E : Edges n} {ok : Fin n → Bool} {u v w : Fin n}
    (h₁ : PathVia E ok u v) (h₂ : PathVia E ok v w) : PathVia E ok u w := by
  obtain ⟨π, hπ, hh, hall⟩ := h₁
  induction π generalizing u with
  | nil => simp at hh; subst hh; exact h₂
  | cons a t ih =>
    simp at hh; subst hh
    have hu : ok a = true := hall a (List.mem_cons_self)
    cases t with
    | nil =>
      exact pathVia_cons hu hπ.1 h₂
    | cons c t' =>
      exact pathVia_cons hu hπ.1
        (ih hπ.2 rfl (fun x hx => hall x (List.mem_cons_of_mem _ hx)))

theorem pathVia_mono {E : Edges n} {ok ok' : Fin n → Bool} {u v : Fin n}
    (himp : ∀ x, ok x = true → ok' x = true) (h : PathVia E ok u v) : PathVia E ok' u v := by
  obtain ⟨π, hπ, hh, hall⟩ := h
  exact ⟨π, hπ, hh, fun x hx => himp x (hall x hx)⟩

/-- Either every node before the end of a path satisfies `q`, or the path passes a node `b`
violating `q` (and satisfying `ok`), splitting there. -/
theorem pathVia_split {E : Edges n} {ok : Fin n → Bool} {u v : Fin n} (q : Fin n → Bool)
    (h : PathVia E ok u v) :
    PathVia E (fun x => ok x && q x) u v ∨
      ∃ b, q b = false ∧ PathVia E ok u b ∧ PathVia E ok b v := by
  obtain ⟨π, hπ, hh, hall⟩ := h
  induction π generalizing u with
  | nil => simp at hh; subst hh; exact Or.inl (pathVia_refl _ _ _)
  | cons a t ih =>
    simp at hh; subst hh
    have hu : ok a = true := hall a (List.mem_cons_self)
    have hrest : PathVia E ok a v := ⟨a :: t, hπ, rfl, hall⟩
    by_cases hq : q a = true
    · cases t with
      | nil =>
        exact Or.inl (pathVia_cons (by simp [hu, hq]) hπ.1 (pathVia_refl _ _ _))
      | cons c t' =>
        rcases ih hπ.2 rfl (fun x hx => hall x (List.mem_cons_of_mem _ hx)) with h' | ⟨b, hb, h1, h2⟩
        · exact Or.inl (pathVia_cons (by simp [hu, hq]) hπ.1 h')
        · exact Or.inr ⟨b, hb, pathVia_cons hu hπ.1 h1, h2⟩
    · exact Or.inr ⟨a, by simpa using hq, pathVia_refl _ _ _, hrest⟩

/-! ## Facts about programs -/

theorem op_eq_activate_iff (p : Prog n) (P : Fin n) : p.op P = .activate ↔ P = p.A := by
  unfold Prog.op
  by_cases hR : P = p.R
  · subst hR
    simp only [ite_true]
    constructor
    · intro h; cases h
    · intro h; exact absurd h p.hRA
  · by_cases hA : P = p.A
    · subst hA; simp [hR]
    · simp only [hR, hA, ite_false, iff_false]
      cases p.stmt P <;> simp

theorem isKill_R (p : Prog n) : p.isKill p.R = true := by
  simp [Prog.isKill, Prog.op]

theorem ne_R_of_not_isKill {p : Prog n} {x : Fin n} (h : (!p.isKill x) = true) : x ≠ p.R := by
  intro hx; subst hx; simp [isKill_R] at h

theorem isUse_A (p : Prog n) : p.isUse p.A = true := by
  have := (op_eq_activate_iff p p.A).2 rfl
  simp [Prog.isUse, this]

theorem edges_eq_succ_of_noUnwind {p : Prog n} (hnu : NoUnwind p) : p.edges = p.succ := by
  funext i; simp [Prog.edges, hnu i]

theorem loanLive_of_isUse {p : Prog n} {U : Fin n} (h : p.isUse U = true) : LoanLive p U :=
  (loanLive_iff p U).2 ⟨U, h, pathVia_refl _ _ _⟩

theorem loanLive_of_pathVia {p : Prog n} {b L : Fin n}
    (hp : PathVia p.edges (fun x => !p.isKill x) b L) (hL : LoanLive p L) : LoanLive p b := by
  obtain ⟨U, hU, hpath⟩ := (loanLive_iff p L).1 hL
  exact (loanLive_iff p b).2 ⟨U, hU, pathVia_trans hp hpath⟩

theorem loanLive_step {p : Prog n} {L L' : Fin n} (hk : p.isKill L = false)
    (hL' : L' ∈ p.edges L) (h : LoanLive p L') : LoanLive p L :=
  loanLive_of_pathVia (pathVia_cons (by simp [hk]) hL' (pathVia_refl _ _ _)) h

theorem sharedLive_self {p : Prog n} {s : SRef} {U : Fin n} (h : p.op U = .useShared s) :
    SharedLive p s U :=
  (sharedLive_iff p s U).2 ⟨U, h, pathVia_refl _ _ _⟩

theorem sharedLive_step {p : Prog n} {s : SRef} {L L' : Fin n} (hb : p.op L ≠ .borrowShared s)
    (hL' : L' ∈ p.edges L) (h : SharedLive p s L') : SharedLive p s L := by
  obtain ⟨U, hU, hpath⟩ := (sharedLive_iff p s L').1 h
  exact (sharedLive_iff p s L).2 ⟨U, hU, pathVia_cons (by simp [hb]) hL' hpath⟩

theorem maybeActive_step {p : Prog n} {L L' : Fin n} (h : MaybeActive p L)
    (hk : p.isKill L = false) (hL' : L' ∈ p.edges L) : MaybeActive p L' := by
  obtain ⟨hreach, y, hy, hpath⟩ := (maybeActive_iff p L).1 h
  exact (maybeActive_iff p L').2 ⟨hreach, y, hy, pathVia_snoc hpath (by simp [hk]) hL'⟩

theorem maybeActive_of_activation {p : Prog n} {L' : Fin n}
    (hreach : PathVia p.edges (fun _ => true) p.entry p.A) (hL' : L' ∈ p.edges p.A) :
    MaybeActive p L' :=
  (maybeActive_iff p L').2 ⟨hreach, L', hL', pathVia_refl _ _ _⟩

/-! ## The forward may-analysis (R1a) -/

/-- The fact the analysis computes, as a path property: some path starts at a successor of `A`
and reaches `L` without passing a kill (`R` or `endLoan`) before `L`. -/
def GenReach (p : Prog n) (L : Fin n) : Prop :=
  ∃ y ∈ p.edges p.A, PathVia p.edges (fun x => !p.isKill x) y L

theorem dfOut_eq_true_iff (p : Prog n) (P : Fin n) (b : Bool) :
    dfOut p P b = true ↔ P = p.A ∨ (p.isKill P = false ∧ b = true) := by
  rw [← op_eq_activate_iff]
  unfold dfOut Prog.isKill
  cases p.op P <;> simp

theorem mem_dfStep (p : Prog n) (S : List (Fin n)) (L : Fin n) :
    L ∈ dfStep p S ↔ ∃ P, L ∈ p.edges P ∧ dfOut p P (S.contains P) = true := by
  simp [dfStep, List.mem_filter, List.mem_finRange, List.any_eq_true]

theorem genReach_of_mem_dfIter (p : Prog n) :
    ∀ (k : Nat) (L : Fin n), L ∈ dfIter p k → GenReach p L
  | 0, L, h => by simp [dfIter] at h
  | k + 1, L, h => by
    obtain ⟨P, hL, hout⟩ := (mem_dfStep p _ L).1 h
    rcases (dfOut_eq_true_iff p P _).1 hout with hP | ⟨hk, hP⟩
    · subst hP; exact ⟨L, hL, pathVia_refl _ _ _⟩
    · obtain ⟨y, hy, hpath⟩ := genReach_of_mem_dfIter p k P (by simpa using hP)
      exact ⟨y, hy, pathVia_snoc hpath (by simp [hk]) hL⟩

theorem dfIter_mono (p : Prog n) :
    ∀ (k : Nat) (L : Fin n), L ∈ dfIter p k → L ∈ dfIter p (k + 1)
  | 0, L, h => by simp [dfIter] at h
  | k + 1, L, h => by
    obtain ⟨P, hL, hout⟩ := (mem_dfStep p _ L).1 h
    refine (mem_dfStep p _ L).2 ⟨P, hL, ?_⟩
    rcases (dfOut_eq_true_iff p P _).1 hout with hP | ⟨hk, hP⟩
    · exact (dfOut_eq_true_iff p P _).2 (Or.inl hP)
    · refine (dfOut_eq_true_iff p P _).2 (Or.inr ⟨hk, ?_⟩)
      have := dfIter_mono p k P (by simpa using hP)
      simpa using this

theorem dfIter_mono_le (p : Prog n) {j k : Nat} {L : Fin n} (h : L ∈ dfIter p j) (hjk : j ≤ k) :
    L ∈ dfIter p k := by
  induction k with
  | zero =>
    have : j = 0 := by omega
    subst this; exact h
  | succ k ih =>
    by_cases hj : j = k + 1
    · subst hj; exact h
    · exact dfIter_mono p k L (ih (by omega))

theorem dfIter_filter_self (p : Prog n) (k : Nat) :
    dfIter p k = (List.finRange n).filter (fun w => (dfIter p k).contains w) := by
  have hq : ∃ q : Fin n → Bool, dfIter p k = (List.finRange n).filter q := by
    cases k with
    | zero => exact ⟨fun _ => false, by simp [dfIter]⟩
    | succ k => exact ⟨_, rfl⟩
  obtain ⟨q, hq⟩ := hq
  rw [hq]
  apply List.filter_congr
  intro x _
  simp [List.mem_filter, List.mem_finRange]

theorem nodup_dfIter (p : Prog n) (k : Nat) : (dfIter p k).Nodup := by
  rw [dfIter_filter_self]; exact List.Pairwise.filter _ (List.nodup_finRange n)

theorem length_dfIter_le (p : Prog n) (k : Nat) : (dfIter p k).length ≤ n := by
  have := List.Nodup.length_le_of_subset (nodup_dfIter p k)
    (l₂ := List.finRange n) (fun x _ => List.mem_finRange x)
  simpa using this

theorem dfIter_length_lt (p : Prog n) {k : Nat}
    (h : ∃ w ∈ dfIter p (k + 1), w ∉ dfIter p k) :
    (dfIter p k).length < (dfIter p (k + 1)).length := by
  rw [dfIter_filter_self p k, dfIter_filter_self p (k + 1)]
  apply filter_length_lt
  · intro w _ hw
    simp only [List.contains_iff_mem] at hw ⊢
    exact dfIter_mono p k w hw
  · obtain ⟨w, hw, hw'⟩ := h
    exact ⟨w, List.mem_finRange w, by simpa using hw, by simpa using hw'⟩

theorem dfStep_congr (p : Prog n) {S T : List (Fin n)} (h : ∀ w, w ∈ S ↔ w ∈ T) :
    dfStep p S = dfStep p T := by
  have hc : ∀ x, S.contains x = T.contains x := by
    intro x; apply Bool.eq_iff_iff.2; simp [h]
  unfold dfStep
  simp only [hc]

/-- `DfStable p k`: iteration `k + 1` adds nothing to iteration `k`. -/
def DfStable (p : Prog n) (k : Nat) : Prop := ∀ w, w ∈ dfIter p (k + 1) ↔ w ∈ dfIter p k

theorem dfStable_succ (p : Prog n) {k : Nat} (h : DfStable p k) : DfStable p (k + 1) := by
  intro w
  show w ∈ dfStep p (dfIter p (k + 1)) ↔ w ∈ dfIter p (k + 1)
  rw [dfStep_congr p h]; rfl

theorem dfStable_of_le (p : Prog n) {j m : Nat} (h : DfStable p j) (hjm : j ≤ m) :
    DfStable p m := by
  induction m with
  | zero =>
    have : j = 0 := by omega
    subst this; exact h
  | succ m ih =>
    by_cases hj : j = m + 1
    · subst hj; exact h
    · exact dfStable_succ p (ih (by omega))

theorem dfIter_length_or_stable (p : Prog n) (k : Nat) :
    k ≤ (dfIter p k).length ∨ ∃ j, j < k ∧ DfStable p j := by
  induction k with
  | zero => exact Or.inl (Nat.zero_le _)
  | succ k ih =>
    rcases ih with ih | ⟨j, hj, hs⟩
    · by_cases hs : DfStable p k
      · exact Or.inr ⟨k, by omega, hs⟩
      · left
        have hnew : ∃ w ∈ dfIter p (k + 1), w ∉ dfIter p k := by
          apply Classical.byContradiction
          intro hne
          apply hs
          intro w
          constructor
          · intro hw
            apply Classical.byContradiction
            intro hw'
            exact hne ⟨w, hw, hw'⟩
          · exact dfIter_mono p k w
        have := dfIter_length_lt p hnew
        omega
    · exact Or.inr ⟨j, by omega, hs⟩

theorem dfStable_n (p : Prog n) : DfStable p n := by
  rcases dfIter_length_or_stable p (n + 1) with h | ⟨j, hj, hs⟩
  · have := length_dfIter_le p (n + 1)
    omega
  · exact dfStable_of_le p hs (by omega)

theorem mem_dfIter_n_of_mem (p : Prog n) {k : Nat} {L : Fin n} (h : L ∈ dfIter p k) :
    L ∈ dfIter p n := by
  by_cases hk : k ≤ n
  · exact dfIter_mono_le p h hk
  · have key : ∀ d, L ∈ dfIter p (n + d) → L ∈ dfIter p n := by
      intro d
      induction d with
      | zero => exact id
      | succ d ih =>
        intro hd
        exact ih ((dfStable_of_le p (dfStable_n p) (Nat.le_add_right n d) L).1 hd)
    have : k = n + (k - n) := by omega
    rw [this] at h
    exact key _ h

theorem mem_dfIter_of_walk (p : Prog n) (v : Fin n) :
    ∀ (π : List (Fin n)) (u : Fin n) (k : Nat), IsWalk p.edges (π ++ [v]) →
      (π ++ [v]).head? = some u → (∀ x ∈ π, (!p.isKill x) = true) → u ∈ dfIter p k →
      v ∈ dfIter p (k + π.length)
  | [], u, k, _, hh, _, hu => by simp at hh; subst hh; simpa using hu
  | a :: t, u, k, hw, hh, hall, hu => by
    simp at hh; subst hh
    have hk : p.isKill a = false := by simpa using hall a (List.mem_cons_self)
    have hnext : ∀ w, w ∈ p.edges a → w ∈ dfIter p (k + 1) := by
      intro w hw'
      refine (mem_dfStep p _ w).2 ⟨a, hw', ?_⟩
      exact (dfOut_eq_true_iff p a _).2 (Or.inr ⟨hk, by simpa using hu⟩)
    have hlen : k + (a :: t).length = (k + 1) + t.length := by simp; omega
    rw [hlen]
    cases t with
    | nil =>
      simpa using hnext v hw.1
    | cons c t' =>
      exact mem_dfIter_of_walk p v (c :: t') c (k + 1) hw.2 rfl
        (fun x hx => hall x (List.mem_cons_of_mem _ hx)) (hnext c hw.1)

theorem mem_dfIter_n_of_genReach (p : Prog n) {L : Fin n} (h : GenReach p L) :
    L ∈ dfIter p n := by
  obtain ⟨y, hy, π, hw, hh, hall⟩ := h
  have hy1 : y ∈ dfIter p 1 := by
    refine (mem_dfStep p _ y).2 ⟨p.A, hy, ?_⟩
    exact (dfOut_eq_true_iff p p.A _).2 (Or.inl rfl)
  exact mem_dfIter_n_of_mem p (mem_dfIter_of_walk p L π y 1 hw hh hall hy1)

theorem dfMaybeActive_iff_genReach (p : Prog n) (L : Fin n) :
    dfMaybeActive p L = true ↔ GenReach p L := by
  unfold dfMaybeActive
  rw [List.contains_iff_mem]
  exact ⟨genReach_of_mem_dfIter p n L, mem_dfIter_n_of_genReach p⟩

/-- Completeness of the analysis needs no reachability hypothesis. -/
theorem dfMaybeActive_of_maybeActive {p : Prog n} {L : Fin n} (h : MaybeActive p L) :
    dfMaybeActive p L = true :=
  (dfMaybeActive_iff_genReach p L).2 ((maybeActive_iff p L).1 h).2

/-! ## Soundness of the exact-phase checker (R1b): a run invariant -/

theorem accepts_not_writeX {p : Prog n} {ph : Fin n → Prop} (h : Accepts p ph) {L : Fin n}
    (hop : p.op L = .writeX) : ¬ LoanLive p L :=
  fun hl => h L (Or.inl ⟨hop, hl⟩)

theorem accepts_not_read {p : Prog n} {ph : Fin n → Prop} (h : Accepts p ph) {L : Fin n}
    (hr : (p.op L).isRead = true) (hl : LoanLive p L) : ¬ ph L :=
  fun hph => h L (Or.inr (Or.inl ⟨hr, hl, hph⟩))

theorem accepts_not_sharedLive_A {p : Prog n} {ph : Fin n → Prop} (h : Accepts p ph) (s : SRef) :
    ¬ SharedLive p s p.A := by
  intro hs
  apply h p.A
  refine Or.inr (Or.inr ⟨rfl, ?_⟩)
  cases s
  · exact Or.inl hs
  · exact Or.inr hs

theorem op_A (p : Prog n) : p.op p.A = .activate := (op_eq_activate_iff p p.A).2 rfl

/-- Under the exact-phase checker, a point where the loan may be active, is live, and from which
a shared reference `s` is live, does not exist: either no `borrowShared s` lies between `A` and
that point (then `s` is live at `A`, flagged by the activation check) or one does (then that
read is flagged). -/
theorem exactPhaseAccepts_no_active_live_shared {p : Prog n} (h : ExactPhaseAccepts p)
    {s : SRef} {L : Fin n} (hma : MaybeActive p L) (hsl : SharedLive p s L)
    (hl : LoanLive p L) : False := by
  obtain ⟨hreach, y, hy, hpath⟩ := (maybeActive_iff p L).1 hma
  obtain ⟨U, hU, hpathU⟩ := (sharedLive_iff p s L).1 hsl
  rcases pathVia_split (fun x => p.op x != .borrowShared s) hpath with h1 | ⟨b, hb, h1, h2⟩
  · apply accepts_not_sharedLive_A h s
    refine (sharedLive_iff p s p.A).2 ⟨U, hU, ?_⟩
    have hA : (p.op p.A != .borrowShared s) = true := by simp [op_A]
    exact pathVia_cons hA hy (pathVia_trans (pathVia_mono (fun x hx => by
      simp only [Bool.and_eq_true] at hx; exact hx.2) h1) hpathU)
  · have hbop : p.op b = .borrowShared s := by simpa using hb
    have hread : (p.op b).isRead = true := by simp [hbop, Op.isRead]
    exact accepts_not_read h hread (loanLive_of_pathVia h2 hl)
      ((maybeActive_iff p b).2 ⟨hreach, y, hy, h1⟩)

/-- The invariant for a node `L` about to execute in state `σ`. -/
def RunInv (p : Prog n) (L : Fin n) (σ : RState) : Prop :=
  PathVia p.edges (fun _ => true) p.entry L ∧
  ((σ.perm = .frozen ∨ σ.perm = .invalid) → ¬ LoanLive p L) ∧
  (σ.perm = .active → MaybeActive p L) ∧
  (∀ s, (σ.sh s).dirty = true → ¬ SharedLive p s L)

theorem runInv_init (p : Prog n) : RunInv p p.entry RState.init := by
  refine ⟨pathVia_refl _ _ _, ?_, ?_, ?_⟩
  · intro h; simp [RState.init] at h
  · intro h; simp [RState.init] at h
  · intro s; cases s <;> simp [RState.init, RState.sh]

theorem runInv_not_ub {p : Prog n} {L : Fin n} {σ : RState}
    (hI : RunInv p L σ) : exec (p.op L) σ ≠ .ub := by
  obtain ⟨_, hfi, _, hdirty⟩ := hI
  cases hop : p.op L with
  | activate =>
    have hl : LoanLive p L := loanLive_of_isUse (by simp [Prog.isUse, hop])
    cases hp : σ.perm <;> simp [exec, hp] <;> simp_all
  | writeThrough =>
    have hl : LoanLive p L := loanLive_of_isUse (by simp [Prog.isUse, hop])
    cases hp : σ.perm <;> simp [exec, hp] <;> simp_all
  | useShared s =>
    have hs := hdirty s
    have hsl : SharedLive p s L := sharedLive_self hop
    by_cases hd : (σ.sh s).dirty = true
    · exact absurd hsl (hs hd)
    · simp [exec, hd]
  | reserve => simp [exec]
  | readX => simp [exec]
  | writeX => simp [exec]
  | borrowShared s => simp [exec]
  | endLoan => simp [exec]
  | nop => simp [exec]

theorem foreignRead_ne_active (q : Perm) : foreignRead q ≠ .active := by
  cases q <;> simp [foreignRead]

theorem foreignWrite_ne_active (q : Perm) : foreignWrite q ≠ .active := by
  cases q <;> simp [foreignWrite]

theorem sh_setSh_ne (σ : RState) {s s' : SRef} (t : SSt) (h : s' ≠ s) :
    (σ.setSh s t).sh s' = σ.sh s' := by
  cases s <;> cases s' <;> simp_all [RState.setSh, RState.sh]

theorem sh_setSh_self (σ : RState) (s : SRef) (t : SSt) : (σ.setSh s t).sh s = t := by
  cases s <;> rfl

theorem perm_setSh (σ : RState) (s : SRef) (t : SSt) : (σ.setSh s t).perm = σ.perm := by
  cases s <;> rfl

/-- Dirty flags are preserved by any step whose op is not `borrowShared s`, `activate` or
`writeThrough`, and the invariant's shared-reference clause then carries over. -/
theorem runInv_dirty_carry {p : Prog n} {L L' : Fin n} {σ σ' : RState}
    (hdirty : ∀ s, (σ.sh s).dirty = true → ¬ SharedLive p s L)
    (hsh : ∀ s, σ'.sh s = σ.sh s) (hb : ∀ s, p.op L ≠ .borrowShared s) (hL' : L' ∈ p.edges L) :
    ∀ s, (σ'.sh s).dirty = true → ¬ SharedLive p s L' := by
  intro s hd hsl
  rw [hsh s] at hd
  exact hdirty s hd (sharedLive_step (hb s) hL' hsl)

theorem runInv_step {p : Prog n} (h : ExactPhaseAccepts p) {L L' : Fin n} {σ σ' : RState}
    (hI : RunInv p L σ) (hex : exec (p.op L) σ = .ok σ') (hL' : L' ∈ p.edges L) :
    RunInv p L' σ' := by
  obtain ⟨hreach, hfi, hact, hdirty⟩ := hI
  have hreach' : PathVia p.edges (fun _ => true) p.entry L' := pathVia_snoc hreach rfl hL'
  refine ⟨hreach', ?_⟩
  cases hop : p.op L with
  | reserve =>
    rw [hop] at hex; simp [exec] at hex; subst hex
    refine ⟨by simp, by simp, ?_⟩
    exact runInv_dirty_carry hdirty (fun _ => rfl) (by simp [hop]) hL'
  | endLoan =>
    rw [hop] at hex; simp [exec] at hex; subst hex
    refine ⟨by simp, by simp, ?_⟩
    exact runInv_dirty_carry hdirty (fun _ => rfl) (by simp [hop]) hL'
  | nop =>
    rw [hop] at hex; simp [exec] at hex; subst hex
    have hk : p.isKill L = false := by simp [Prog.isKill, hop]
    refine ⟨fun hp hl => hfi hp (loanLive_step hk hL' hl),
      fun hp => maybeActive_step (hact hp) hk hL', ?_⟩
    exact runInv_dirty_carry hdirty (fun _ => rfl) (by simp [hop]) hL'
  | readX =>
    rw [hop] at hex; simp [exec] at hex; subst hex
    have hk : p.isKill L = false := by simp [Prog.isKill, hop]
    refine ⟨?_, fun hp => absurd hp (foreignRead_ne_active _), ?_⟩
    · intro hp hl
      have hlL := loanLive_step hk hL' hl
      cases hq : σ.perm <;> simp [foreignRead, hq] at hp
      · exact accepts_not_read h (by simp [hop, Op.isRead]) hlL (hact hq)
      · exact hfi (Or.inl hq) hlL
      · exact hfi (Or.inr hq) hlL
    · exact runInv_dirty_carry hdirty (fun _ => rfl) (by simp [hop]) hL'
  | writeX =>
    rw [hop] at hex; simp [exec] at hex; subst hex
    have hk : p.isKill L = false := by simp [Prog.isKill, hop]
    refine ⟨?_, fun hp => absurd hp (foreignWrite_ne_active _), ?_⟩
    · intro _ hl
      exact accepts_not_writeX h hop (loanLive_step hk hL' hl)
    · exact runInv_dirty_carry hdirty (fun _ => rfl) (by simp [hop]) hL'
  | borrowShared t =>
    rw [hop] at hex; simp [exec] at hex; subst hex
    have hk : p.isKill L = false := by simp [Prog.isKill, hop]
    refine ⟨?_, ?_, ?_⟩
    · intro hp hl
      rw [perm_setSh] at hp
      have hlL := loanLive_step hk hL' hl
      cases hq : σ.perm <;> simp [foreignRead, hq] at hp
      · exact accepts_not_read h (by simp [hop, Op.isRead]) hlL (hact hq)
      · exact hfi (Or.inl hq) hlL
      · exact hfi (Or.inr hq) hlL
    · intro hp
      rw [perm_setSh] at hp
      exact absurd hp (foreignRead_ne_active _)
    · intro s hd hsl
      by_cases hs : s = t
      · subst hs; rw [sh_setSh_self] at hd; simp at hd
      · rw [sh_setSh_ne _ _ hs] at hd
        exact hdirty s hd (sharedLive_step (by simp [hop]; exact fun h' => hs h'.symm) hL' hsl)
  | useShared t =>
    rw [hop] at hex
    by_cases hd0 : (σ.sh t).dirty = true
    · simp [exec, hd0] at hex
    · simp [exec, hd0] at hex; subst hex
      have hk : p.isKill L = false := by simp [Prog.isKill, hop]
      refine ⟨?_, fun hp => absurd hp (foreignRead_ne_active _), ?_⟩
      · intro hp hl
        have hlL := loanLive_step hk hL' hl
        cases hq : σ.perm <;> simp [foreignRead, hq] at hp
        · exact exactPhaseAccepts_no_active_live_shared h (hact hq) (sharedLive_self hop) hlL
        · exact hfi (Or.inl hq) hlL
        · exact hfi (Or.inr hq) hlL
      · exact runInv_dirty_carry hdirty (fun _ => rfl) (by simp [hop]) hL'
  | activate =>
    rw [hop] at hex
    have hLA : L = p.A := (op_eq_activate_iff p L).1 hop
    subst hLA
    cases hq : σ.perm with
    | none =>
      simp [exec, hq] at hex; subst hex
      refine ⟨by simp [hq], by simp [hq], ?_⟩
      intro s _ hsl
      exact accepts_not_sharedLive_A h s (sharedLive_step (by simp [op_A]) hL' hsl)
    | reserved =>
      simp [exec, hq] at hex; subst hex
      refine ⟨by simp, fun _ => maybeActive_of_activation hreach hL', ?_⟩
      intro s _ hsl
      exact accepts_not_sharedLive_A h s (sharedLive_step (by simp [op_A]) hL' hsl)
    | active =>
      simp [exec, hq] at hex; subst hex
      refine ⟨by simp, fun _ => maybeActive_of_activation hreach hL', ?_⟩
      intro s _ hsl
      exact accepts_not_sharedLive_A h s (sharedLive_step (by simp [op_A]) hL' hsl)
    | frozen => simp [exec, hq] at hex
    | invalid => simp [exec, hq] at hex
  | writeThrough =>
    rw [hop] at hex
    have hk : p.isKill L = false := by simp [Prog.isKill, hop]
    cases hq : σ.perm with
    | active =>
      simp [exec, hq] at hex; subst hex
      refine ⟨by simp, fun _ => maybeActive_step (hact hq) hk hL', ?_⟩
      intro s _ hsl
      exact exactPhaseAccepts_no_active_live_shared h (hact hq)
        (sharedLive_step (by simp [hop]) hL' hsl) (loanLive_of_isUse (by simp [Prog.isUse, hop]))
    | none => simp [exec, hq] at hex
    | reserved => simp [exec, hq] at hex
    | frozen => simp [exec, hq] at hex
    | invalid => simp [exec, hq] at hex

theorem run_ne_ub_of_runInv {p : Prog n} (h : ExactPhaseAccepts p) :
    ∀ (π : List (Fin n)) (x : Fin n) (σ : RState), IsWalk p.edges (x :: π) → RunInv p x σ →
      run p σ (x :: π) ≠ .ub := by
  intro π
  induction π with
  | nil =>
    intro x σ _ hI
    have hne := runInv_not_ub hI
    simp only [run]
    revert hne
    cases exec (p.op x) σ <;> simp
  | cons y t ih =>
    intro x σ hw hI
    have hne := runInv_not_ub hI
    simp only [run]
    revert hne
    cases hex : exec (p.op x) σ with
    | ok σ' => intro _; exact ih y σ' hw.2 (runInv_step h hI hex hw.1)
    | halt => simp
    | ub => simp

/-! ## The dominator test (R2a, R2b, R7a): walk arguments -/

/-- A list containing `x` splits at the last occurrence of `x`. -/
theorem exists_split_last {α : Type} [DecidableEq α] (x : α) :
    ∀ l : List α, x ∈ l → ∃ l₁ l₂, l = l₁ ++ x :: l₂ ∧ x ∉ l₂
  | [], h => by simp at h
  | a :: t, h => by
    by_cases ht : x ∈ t
    · obtain ⟨l₁, l₂, he, hn⟩ := exists_split_last x t ht
      exact ⟨a :: l₁, l₂, by simp [he], hn⟩
    · have hax : a = x := by
        rcases List.mem_cons.1 h with h | h
        · exact h.symm
        · exact absurd h ht
      exact ⟨[], t, by simp [hax], ht⟩

/-- If every walk (over all edges) ending at `L` uses normal edges only, and the CFG
conditions of R2b hold, then the dominator test is sound at `L`. -/
theorem isActiveDom_of_maybeActive_of_succWalks (p : Prog n) (hre : ReentryFree p)
    (hasr : ActivationStaysReachable p) (L : Fin n)
    (hsucc : ∀ π : List (Fin n), IsWalk p.edges (π ++ [L]) → IsWalk p.succ (π ++ [L]))
    (hL : MaybeActive p L) : IsActiveDom p L := by
  apply Classical.byContradiction
  intro hnot
  obtain ⟨hnA, hnR⟩ := not_or.1 hnot
  have ⟨hRL, hdR⟩ := Classical.not_not.1 hnR
  -- a walk from `entry` to `L` avoiding `A`
  have hpA := Classical.not_not.1 ((not_congr (dom_iff_not_pathVia p.edges p.entry p.A L)).1 hnA)
  obtain ⟨hLA, π, hw, hh, hall⟩ := hpA
  -- it passes `R`; split at the last `R`
  have hRmem : p.R ∈ π ++ [L] := hdR (π ++ [L]) hw hh (by simp)
  have hRπ : p.R ∈ π := by
    rcases List.mem_append.1 hRmem with h | h
    · exact h
    · simp at h; exact absurd h hRL
  obtain ⟨π₁, π₂, hsplit, hRn⟩ := exists_split_last p.R π hRπ
  have hw' : IsWalk p.edges ((π₁ ++ p.R :: π₂) ++ [L]) := by rw [← hsplit]; exact hw
  have hws : IsWalk p.succ ((π₁ ++ p.R :: π₂) ++ [L]) := hsucc _ hw'
  have hsuf : IsWalk p.succ (p.R :: (π₂ ++ [L])) := by
    have := isWalk_suffix (E := p.succ) p.R (π₂ ++ [L]) π₁ (by simpa [List.append_assoc] using hws)
    exact this
  have hallA : ∀ x ∈ π₂, x ≠ p.A := by
    intro x hx
    have : x ∈ π := by rw [hsplit]; simp [hx]
    simpa using hall x this
  -- the region path from the first node after `R` to `L`
  have hreg : ∃ y ∈ p.succ p.R, y ≠ p.R ∧
      PathVia p.succ (fun z => z != p.A && z != p.R) y L := by
    cases π₂ with
    | nil => exact ⟨L, hsuf.1, fun h => hRL h.symm, pathVia_refl _ _ _⟩
    | cons c t =>
      refine ⟨c, hsuf.1, fun h => hRn (by simp [h]), c :: t, hsuf.2, rfl, ?_⟩
      intro x hx
      have hxA := hallA x hx
      have hxR : x ≠ p.R := fun h => hRn (h ▸ hx)
      simp [hxA, hxR]
  obtain ⟨y, hy, hyR, hpath⟩ := hreg
  have hback : PathVia p.succ (fun z => z != p.R) L p.A := hasr y hy hyR L hRL.symm hpath
  -- the walk from `A` to `L` given by `MaybeActive`, along normal edges
  obtain ⟨pre, mid, hwm, _, hmid⟩ := hL
  have hwm' : IsWalk p.succ (p.A :: (mid ++ [L])) := by
    have h1 : IsWalk p.succ ((pre ++ p.A :: mid) ++ [L]) :=
      hsucc _ (by simpa [List.append_assoc] using hwm)
    exact isWalk_suffix p.A (mid ++ [L]) pre (by simpa [List.append_assoc] using h1)
  have hfwd : ∃ z ∈ p.succ p.A, PathVia p.succ (fun x => x != p.R) z L := by
    cases mid with
    | nil => exact ⟨L, hwm'.1, pathVia_refl _ _ _⟩
    | cons c t =>
      refine ⟨c, hwm'.1, c :: t, hwm'.2, rfl, ?_⟩
      intro x hx
      have := hmid x hx
      have hxR : x ≠ p.R := ne_R_of_not_isKill (by simp [this])
      simp [hxR]
  obtain ⟨z, hz, hzL⟩ := hfwd
  exact (reentryFree_iff p).1 hre z hz (pathVia_trans hzL hback)

theorem domRegionReachesA_of_activationStaysReachable {p : Prog n}
    (h : ActivationStaysReachable p) : DomRegionReachesA p :=
  fun y hy hyR x hxR _ hpath => h y hy hyR x hxR hpath

/-- The walk argument of `isActiveDom_of_maybeActive_of_succWalks` with `DomRegionReachesA`
in place of `ActivationStaysReachable`, under no unwinding edges. -/
theorem isActiveDom_of_maybeActive_of_domRegion (p : Prog n) (hre : ReentryFree p)
    (hdr : DomRegionReachesA p) (hnu : NoUnwind p) (L : Fin n) (hL : MaybeActive p L) :
    IsActiveDom p L := by
  apply Classical.byContradiction
  intro hnot
  obtain ⟨hnA, hnR⟩ := not_or.1 hnot
  have ⟨hRL, hdR⟩ := Classical.not_not.1 hnR
  have hdRs : Dom p.succ p.entry p.R L := by rwa [edges_eq_succ_of_noUnwind hnu] at hdR
  have hpA := Classical.not_not.1 ((not_congr (dom_iff_not_pathVia p.edges p.entry p.A L)).1 hnA)
  obtain ⟨_, π, hw, hh, hall⟩ := hpA
  have hRmem : p.R ∈ π ++ [L] := hdR (π ++ [L]) hw hh (by simp)
  have hRπ : p.R ∈ π := by
    rcases List.mem_append.1 hRmem with h | h
    · exact h
    · simp at h; exact absurd h hRL
  obtain ⟨π₁, π₂, hsplit, hRn⟩ := exists_split_last p.R π hRπ
  have hw' : IsWalk p.edges ((π₁ ++ p.R :: π₂) ++ [L]) := by rw [← hsplit]; exact hw
  have hws : IsWalk p.succ ((π₁ ++ p.R :: π₂) ++ [L]) := by
    rwa [edges_eq_succ_of_noUnwind hnu] at hw'
  have hsuf : IsWalk p.succ (p.R :: (π₂ ++ [L])) :=
    isWalk_suffix (E := p.succ) p.R (π₂ ++ [L]) π₁ (by simpa [List.append_assoc] using hws)
  have hallA : ∀ x ∈ π₂, x ≠ p.A := by
    intro x hx
    have : x ∈ π := by rw [hsplit]; simp [hx]
    simpa using hall x this
  have hreg : ∃ y ∈ p.succ p.R, y ≠ p.R ∧
      PathVia p.succ (fun z => z != p.A && z != p.R) y L := by
    cases π₂ with
    | nil => exact ⟨L, hsuf.1, fun h => hRL h.symm, pathVia_refl _ _ _⟩
    | cons c t =>
      refine ⟨c, hsuf.1, fun h => hRn (by simp [h]), c :: t, hsuf.2, rfl, ?_⟩
      intro x hx
      have hxA := hallA x hx
      have hxR : x ≠ p.R := fun h => hRn (h ▸ hx)
      simp [hxA, hxR]
  obtain ⟨y, hy, hyR, hpath⟩ := hreg
  have hback : PathVia p.succ (fun z => z != p.R) L p.A := hdr y hy hyR L hRL.symm hdRs hpath
  obtain ⟨pre, mid, hwm, _, hmid⟩ := hL
  have hwm' : IsWalk p.succ (p.A :: (mid ++ [L])) := by
    have h1 : IsWalk p.succ ((pre ++ p.A :: mid) ++ [L]) := by
      rw [← edges_eq_succ_of_noUnwind hnu]; simpa [List.append_assoc] using hwm
    exact isWalk_suffix p.A (mid ++ [L]) pre (by simpa [List.append_assoc] using h1)
  have hfwd : ∃ z ∈ p.succ p.A, PathVia p.succ (fun x => x != p.R) z L := by
    cases mid with
    | nil => exact ⟨L, hwm'.1, pathVia_refl _ _ _⟩
    | cons c t =>
      refine ⟨c, hwm'.1, c :: t, hwm'.2, rfl, ?_⟩
      intro x hx
      have := hmid x hx
      have hxR : x ≠ p.R := ne_R_of_not_isKill (by simp [this])
      simp [hxR]
  obtain ⟨z, hz, hzL⟩ := hfwd
  exact (reentryFree_iff p).1 hre z hz (pathVia_trans hzL hback)

theorem isWalk_succ_of_not_isCleanup {p : Prog n} {L : Fin n} (hnc : ¬ IsCleanup p L) :
    ∀ π : List (Fin n), IsWalk p.edges (π ++ [L]) → IsWalk p.succ (π ++ [L])
  | [], _ => trivial
  | a :: t, hw => by
    have hrest : IsWalk p.edges (t ++ [L]) := isWalk_tail (by simp) hw
    have ih := isWalk_succ_of_not_isCleanup hnc t hrest
    cases t with
    | nil =>
      have hb : L ∈ p.edges a := hw.1
      rcases List.mem_append.1 hb with hb | hb
      · exact ⟨hb, trivial⟩
      · exact absurd ⟨a, L, hb, pathVia_refl _ _ _⟩ hnc
    | cons c t' =>
      have hb : c ∈ p.edges a := hw.1
      rcases List.mem_append.1 hb with hb | hb
      · exact ⟨hb, ih⟩
      · exact absurd ⟨a, c, hb, c :: t', hrest, rfl, by simp⟩ hnc

theorem not_isCleanup_of_noUnwind {p : Prog n} (hnu : NoUnwind p) (L : Fin n) :
    ¬ IsCleanup p L := by
  rintro ⟨x, c, hc, _⟩
  rw [hnu x] at hc; simp at hc

theorem not_isCleanup_of_cleanupReadsUnderDeadLoan {p : Prog n}
    (hcl : CleanupReadsUnderDeadLoan p) {L : Fin n} (hread : (p.op L).isRead = true)
    (hlive : LoanLive p L) : ¬ IsCleanup p L :=
  fun hc => hcl L hc hread hlive

/-! ### Acyclic CFGs -/

theorem nodup_of_isWalk_acyclic {E : Edges n} (hac : Acyclic E) :
    ∀ l : List (Fin n), IsWalk E l → l.Nodup
  | [], _ => List.nodup_nil
  | [_], _ => List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩
  | a :: b :: t, hw => by
    refine List.nodup_cons.2 ⟨?_, nodup_of_isWalk_acyclic hac (b :: t) hw.2⟩
    intro ha
    obtain ⟨s, s', he⟩ := List.append_of_mem ha
    have h1 : IsWalk E ((a :: s) ++ a :: s') := by rw [List.cons_append, ← he]; exact hw
    have h2 := isWalk_prefix a s' (a :: s) h1
    exact hac a s (by simpa using h2)

theorem length_le_of_nodup {l : List (Fin n)} (h : l.Nodup) : l.length ≤ n := by
  have := List.Nodup.length_le_of_subset h (l₂ := List.finRange n) (fun x _ => List.mem_finRange x)
  simpa using this

theorem reentryFree_of_acyclic {p : Prog n} (hac : Acyclic p.succ) : ReentryFree p :=
  fun mid hw => absurd hw (hac p.A mid)

/-- In an acyclic CFG where `A` post-dominates `R`, every `A`-avoiding walk from `R` can be
extended to `A` without passing `R` (by induction on the remaining length bound). -/
theorem pathVia_to_A_of_acyclic_pdom {p : Prog n} (hac : Acyclic p.succ)
    (hpd : PDom p.succ p.A p.R) :
    ∀ (k : Nat) (π : List (Fin n)) (x : Fin n), IsWalk p.succ (p.R :: (π ++ [x])) →
      (∀ z ∈ π ++ [x], z ≠ p.A) → n - π.length ≤ k →
      PathVia p.succ (fun z => z != p.R) x p.A := by
  intro k
  induction k with
  | zero =>
    intro π x hw _ hk
    have hnd := nodup_of_isWalk_acyclic hac _ hw
    have := length_le_of_nodup hnd
    simp at this; omega
  | succ k ih =>
    intro π x hw hA hk
    have hnd := nodup_of_isWalk_acyclic hac _ hw
    have hxR : x ≠ p.R := by
      intro h; subst h
      exact (List.nodup_cons.1 hnd).1 (by simp)
    cases hsx : p.succ x with
    | nil =>
      exfalso
      have hmem := hpd (p.R :: (π ++ [x])) x hw rfl (by rw [← List.cons_append]; exact List.getLast?_concat) hsx
      rcases List.mem_cons.1 hmem with h | h
      · exact p.hRA h.symm
      · exact hA p.A h rfl
    | cons w ws =>
      have hw' : w ∈ p.succ x := by rw [hsx]; simp
      by_cases hwA : w = p.A
      · subst hwA
        exact pathVia_cons (by simp [hxR]) hw' (pathVia_refl _ _ _)
      · have hext : IsWalk p.succ (p.R :: ((π ++ [x]) ++ [w])) := by
          have := isWalk_append_pair p.succ x w hw' (p.R :: π) (by simpa using hw)
          simpa [List.append_assoc] using this
        have hA' : ∀ z ∈ (π ++ [x]) ++ [w], z ≠ p.A := by
          intro z hz
          rcases List.mem_append.1 hz with hz | hz
          · exact hA z hz
          · simp at hz; subst hz; exact hwA
        have hnd' := nodup_of_isWalk_acyclic hac _ hext
        have hlen := length_le_of_nodup hnd'
        simp at hlen
        have hk' : n - (π ++ [x]).length ≤ k := by simp; omega
        exact pathVia_cons (by simp [hxR]) hw' (ih (π ++ [x]) w hext hA' hk')

theorem activationStaysReachable_of_acyclic_pdom {p : Prog n} (hac : Acyclic p.succ)
    (hpd : PDom p.succ p.A p.R) : ActivationStaysReachable p := by
  intro y hy _ x _ hpath
  by_cases hxA : x = p.A
  · subst hxA; exact pathVia_refl _ _ _
  · obtain ⟨ρ, hw, hh, hall⟩ := hpath
    have hw' : IsWalk p.succ (p.R :: (ρ ++ [x])) := by
      cases ρ with
      | nil => simp at hh; subst hh; exact ⟨hy, trivial⟩
      | cons c t => simp at hh; subst hh; exact ⟨hy, hw⟩
    have hA : ∀ z ∈ ρ ++ [x], z ≠ p.A := by
      intro z hz
      rcases List.mem_append.1 hz with hz | hz
      · have := hall z hz; simp at this; exact this.1
      · simp at hz; subst hz; exact hxA
    exact pathVia_to_A_of_acyclic_pdom hac hpd n ρ x hw' hA (Nat.sub_le n _)

end Toy.TwoPhase
