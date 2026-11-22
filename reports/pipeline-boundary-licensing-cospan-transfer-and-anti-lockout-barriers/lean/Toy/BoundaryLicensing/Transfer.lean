import Toy.BoundaryLicensing.Basic

set_option autoImplicit false

namespace Toy.BoundaryLicensing

/-! ## Single-Boundary Soundness, `5 × 5` Shape Separation, and Cell Sharpness -/

/-! ### Helper Morphism Implications and Trace Lemmas -/

/-- One-branch system starting at `v₀` and looping forever at `v₁`. -/
def oneBranchSys (v₀ v₁ : Valuation) : Sys :=
  maskedBranchSys (k := 0) (fun _ => (v₀, v₁))

theorem isEmbedFrom_isHomFrom {A B : Sys} (h : IsEmbedFrom A B) : IsHomFrom A B := by
  rcases h with ⟨f, _, hinit, hstep, hval⟩
  refine ⟨f, fun s hs => (hinit s).2 hs, fun s s' hs => (hstep s s').2 hs, ?_⟩
  intro s a hsa
  rw [hval s]
  exact hsa

theorem isSurjHomFrom_isHomFrom {A B : Sys} (h : IsSurjHomFrom A B) : IsHomFrom A B := by
  rcases h with ⟨f, _, hinit, hstep, hval⟩
  exact ⟨f, hinit, hstep, hval⟩

theorem isPosBoundedMorphFrom_isHomFrom {A B : Sys} (h : IsPosBoundedMorphFrom A B) :
    IsHomFrom A B := by
  rcases h with ⟨f, hinit, _, hstep, _, hval⟩
  exact ⟨f, hinit, hstep, hval⟩

theorem isEmbedFrom_lockStepSimFrom {A B : Sys} (h : IsEmbedFrom A B) : LockStepSimFrom A B := by
  rcases h with ⟨f, _, hinit, hstep, hval⟩
  refine ⟨fun s t => f s = t, ?_, ?_, ?_⟩
  · intro s₀ hs₀
    exact ⟨f s₀, (hinit s₀).2 hs₀, rfl⟩
  · intro s t hR
    subst hR
    exact (hval s).symm
  · intro s s' t hR hs
    subst hR
    exact ⟨f s', (hstep s s').2 hs, rfl⟩

theorem lockStepSimFrom_wfStutterSimFrom {A B : Sys} (h : LockStepSimFrom A B) :
    WfStutterSimFrom A B := by
  rcases h with ⟨R, hinit, hval, hstep⟩
  refine ⟨R, fun _ _ => 0, hinit, hval, ?_⟩
  intro s s' t hR hs
  obtain ⟨t', ht', hR'⟩ := hstep s s' t hR hs
  exact Or.inr (.step_done hR ht' hR')

theorem wfStutterSimFrom_stutterSimFrom {A B : Sys} (h : WfStutterSimFrom A B) :
    StutterSimFrom A B := by
  rcases h with ⟨R, _, hinit, hval, hstep⟩
  refine ⟨R, hinit, hval, ?_⟩
  intro s s' t hR hs
  rcases hstep s s' t hR hs with ⟨hR', _⟩ | hpm
  · exact Or.inl hR'
  · exact Or.inr hpm

theorem lockStepSimFrom_traceIncl {A B : Sys} (h : LockStepSimFrom A B) : TraceIncl A B := by
  rcases h with ⟨R, hinit, hval, hstep⟩
  rintro τ ⟨π, ⟨hπ0, hπstep⟩, hτ⟩
  have hex0 : ∃ t₀, B.init t₀ ∧ R (π 0) t₀ := hinit (π 0) hπ0
  let t₀ := Classical.choose hex0
  have ht₀ : B.init t₀ ∧ R (π 0) t₀ := Classical.choose_spec hex0
  have hnext : ∀ (n : Nat) (t : B.State), R (π n) t → ∃ t', B.step t t' ∧ R (π (n + 1)) t' :=
    fun n t hR => hstep (π n) (π (n + 1)) t hR (hπstep n)
  let seq : (n : Nat) → { t : B.State // R (π n) t } :=
    fun n => Nat.recOn n ⟨t₀, ht₀.2⟩ (fun m cur =>
      ⟨Classical.choose (hnext m cur.1 cur.2), (Classical.choose_spec (hnext m cur.1 cur.2)).2⟩)
  refine ⟨fun n => (seq n).1, ⟨ht₀.1, ?_⟩, ?_⟩
  · intro n
    exact (Classical.choose_spec (hnext n (seq n).1 (seq n).2)).1
  · intro n
    rw [hτ n]
    exact hval (π n) (seq n).1 (seq n).2

theorem cospanSysWitness_iff_traceIncl (ir exec : Sys) :
    CospanSysWitness ir exec ↔ TraceIncl exec ir := by
  constructor
  · rintro ⟨s0, pass, cap, lower, hok, hlow, hpass, hcap, hlowref⟩ τ hτ
    rw [← hlow] at hτ
    exact hcap (pass s0) ir hok τ (hpass τ (hlowref τ hτ))
  · intro htr
    refine ⟨ir, id, Except.ok, fun _ => exec, rfl, rfl, fun _ h => h, ?_, htr⟩
    intro p q hok
    cases hok
    exact fun _ h => h

theorem isHomFrom_preserves_existWitness {A B : Sys} (h : IsHomFrom A B) (P : Spec) :
    EvalShape .existWitness A P → EvalShape .existWitness B P := by
  rcases h with ⟨f, hinit, hstep, hval⟩
  rintro ⟨τ, ⟨π, ⟨h0, hs⟩, hτ⟩, n, hn⟩
  refine ⟨fun m => B.val (f (π m)), ⟨fun m => f (π m), ⟨hinit _ h0, fun m => hstep _ _ (hs m)⟩,
    fun _ => rfl⟩, n, ?_⟩
  rw [hτ n] at hn
  exact evalVal_mono (hval (π n)) hn

theorem isPosBoundedMorphFrom_lifts_exec {A B : Sys} (h : IsPosBoundedMorphFrom A B)
    {πB : Nat → B.State} (hB : IsExec B πB) :
    ∃ πA : Nat → A.State, IsExec A πA ∧ ∀ n a, A.val (πA n) a = true → B.val (πB n) a = true := by
  rcases h with ⟨f, _, hinitB, _, hstepB, hval⟩
  obtain ⟨s₀, hs₀, hf₀⟩ := hinitB (πB 0) hB.1
  have hlift : ∀ (n : Nat) (s : A.State), f s = πB n →
      ∃ s', A.step s s' ∧ f s' = πB (n + 1) := by
    intro n s hfs
    have hb : B.step (f s) (πB (n + 1)) := by rw [hfs]; exact hB.2 n
    exact hstepB s (πB (n + 1)) hb
  let seq : (n : Nat) → { s : A.State // f s = πB n } :=
    fun n => Nat.recOn n ⟨s₀, hf₀⟩ (fun m cur =>
      ⟨Classical.choose (hlift m cur.1 cur.2), (Classical.choose_spec (hlift m cur.1 cur.2)).2⟩)
  refine ⟨fun n => (seq n).1, ⟨hs₀, ?_⟩, ?_⟩
  · intro n
    exact (Classical.choose_spec (hlift n (seq n).1 (seq n).2)).1
  · intro n a ha
    rw [← (seq n).2]
    exact hval (seq n).1 a ha

theorem isPosBoundedMorphFrom_preserves_univSafety {A B : Sys} (h : IsPosBoundedMorphFrom A B)
    (P : Spec) :
    EvalShape .univSafety A P → EvalShape .univSafety B P := by
  intro hA τB ⟨πB, hπB, hτB⟩ n
  obtain ⟨πA, hπA, hmono⟩ := isPosBoundedMorphFrom_lifts_exec h hπB
  have htrA : HasTrace A (fun m => A.val (πA m)) := ⟨πA, hπA, fun _ => rfl⟩
  have hn := hA _ htrA n
  rw [hτB n]
  exact evalVal_mono (hmono n) hn

theorem isPosBoundedMorphFrom_preserves_termination {A B : Sys} (h : IsPosBoundedMorphFrom A B)
    (P : Spec) :
    EvalShape .termination A P → EvalShape .termination B P := by
  intro hA τB ⟨πB, hπB, hτB⟩
  obtain ⟨πA, hπA, hmono⟩ := isPosBoundedMorphFrom_lifts_exec h hπB
  have htrA : HasTrace A (fun m => A.val (πA m)) := ⟨πA, hπA, fun _ => rfl⟩
  obtain ⟨n, hn⟩ := hA _ htrA
  refine ⟨n, ?_⟩
  rw [hτB n]
  exact evalVal_mono (hmono n) hn

/-! ### Reachability and Stuttering Simulation Lemmas -/

/-- Reflexive-transitive closure of `S.step`. -/
inductive Steps (S : Sys) : S.State → S.State → Prop where
  | refl (s : S.State) : Steps S s s
  | tail {s u v : S.State} : Steps S s u → S.step u v → Steps S s v

theorem steps_trans {S : Sys} {a b c : S.State} (h₁ : Steps S a b) (h₂ : Steps S b c) :
    Steps S a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hstep ih => exact .tail ih hstep

theorem extend_reachable_to_trace (S : Sys) {t₀ t : S.State} (h0 : S.init t₀)
    (hreach : Steps S t₀ t) : ∃ τ, HasTrace S τ ∧ ∃ m, τ m = S.val t := by
  have h_list : ∃ (k : Nat) (pre : Nat → S.State),
      pre 0 = t₀ ∧ pre k = t ∧ ∀ i < k, S.step (pre i) (pre (i + 1)) := by
    induction hreach with
    | refl => exact ⟨0, fun _ => t₀, rfl, rfl, fun _ hi => by omega⟩
    | @tail u v _ hstep ih =>
      rcases ih with ⟨k, pre, hp0, hpk, hps⟩
      refine ⟨k + 1, fun i => if i ≤ k then pre i else v, ?_, ?_, ?_⟩
      · simp [hp0]
      · have hnle : ¬ (k + 1 ≤ k) := by omega
        simp [hnle]
      · intro i hi
        by_cases hik : i < k
        · have hik1 : i + 1 ≤ k := by omega
          have hi_le : i ≤ k := by omega
          simp [hi_le, hik1, hps i hik]
        · have heq : i = k := by omega
          subst i
          have hnle : ¬ (k + 1 ≤ k) := by omega
          simp [hnle, hpk, hstep]
  rcases h_list with ⟨k, pre, hp0, hpk, hps⟩
  let next : S.State → S.State := fun s => Classical.choose (S.step_total s)
  let tailSeq : Nat → S.State := fun m => Nat.recOn m t (fun _ cur => next cur)
  let π : Nat → S.State := fun n => if n ≤ k then pre n else tailSeq (n - k)
  refine ⟨fun n => S.val (π n), ⟨π, ⟨?_, ?_⟩, fun _ => rfl⟩, k, ?_⟩
  · simp [π, hp0, h0]
  · intro n
    by_cases hnk : n < k
    · have hle1 : n ≤ k := by omega
      have hle2 : n + 1 ≤ k := by omega
      simp [π, hle1, hle2, hps n hnk]
    · by_cases heq : n = k
      · subst n
        have hnle : ¬ (k + 1 ≤ k) := by omega
        have hsub : k + 1 - k = 1 := by omega
        simp only [π, Nat.le_refl, hnle, hpk, hsub, ↓reduceIte]
        exact Classical.choose_spec (S.step_total t)
      · have hnle1 : ¬ (n ≤ k) := by omega
        have hnle2 : ¬ (n + 1 ≤ k) := by omega
        have hsub : n + 1 - k = (n - k) + 1 := by omega
        simp only [π, hnle1, hnle2, hsub, ↓reduceIte]
        exact Classical.choose_spec (S.step_total (tailSeq (n - k)))
  · simp [π, hpk]

theorem plusMatch_steps {A B : Sys} {R : A.State → B.State → Prop} {s s' : A.State} {t : B.State}
    (hpm : PlusMatch R s s' t) : ∃ t', Steps B t t' ∧ R s' t' := by
  induction hpm with
  | step_done _ hstep hR' => exact ⟨_, .tail (.refl _) hstep, hR'⟩
  | step_stut _ hstep _ ih =>
    rcases ih with ⟨t', hsteps, hR'⟩
    exact ⟨t', steps_trans (.tail (.refl _) hstep) hsteps, hR'⟩

theorem stutterSimFrom_pointwise_match {A B : Sys} (h : StutterSimFrom A B)
    {π : Nat → A.State} (hπ : IsExec A π) (n : Nat) :
    ∃ t₀ tₙ, B.init t₀ ∧ Steps B t₀ tₙ ∧ B.val tₙ = A.val (π n) := by
  rcases h with ⟨R, hinit, hval, hstep⟩
  have hind : ∀ m, ∃ t₀ tₘ, B.init t₀ ∧ Steps B t₀ tₘ ∧ R (π m) tₘ := by
    intro m
    induction m with
    | zero =>
      obtain ⟨t₀, ht₀, hR₀⟩ := hinit (π 0) hπ.1
      exact ⟨t₀, t₀, ht₀, .refl t₀, hR₀⟩
    | succ m ih =>
      rcases ih with ⟨t₀, tₘ, ht₀, hsteps, hRₘ⟩
      rcases hstep (π m) (π (m + 1)) tₘ hRₘ (hπ.2 m) with hR' | hpm
      · exact ⟨t₀, tₘ, ht₀, hsteps, hR'⟩
      · obtain ⟨t', hsteps', hR'⟩ := plusMatch_steps hpm
        exact ⟨t₀, t', ht₀, steps_trans hsteps hsteps', hR'⟩
  obtain ⟨t₀, tₙ, ht₀, hsteps, hR⟩ := hind n
  exact ⟨t₀, tₙ, ht₀, hsteps, (hval (π n) tₙ hR).symm⟩

theorem stutterSimFrom_preserves_existWitness {A B : Sys} (h : StutterSimFrom A B) (P : Spec) :
    EvalShape .existWitness A P → EvalShape .existWitness B P := by
  rintro ⟨τA, ⟨πA, hπA, hτA⟩, n, hn⟩
  obtain ⟨t₀, tₙ, ht₀, hsteps, hveq⟩ := stutterSimFrom_pointwise_match h hπA n
  obtain ⟨τB, hτB, m, hm⟩ := extend_reachable_to_trace B ht₀ hsteps
  refine ⟨τB, hτB, m, ?_⟩
  rw [hm, hveq, ← hτA n]
  exact hn

theorem stutterSimFrom_reflects_univSafety {A B : Sys} (h : StutterSimFrom A B) (P : Spec) :
    EvalShape .univSafety B P → EvalShape .univSafety A P := by
  intro hB τA ⟨πA, hπA, hτA⟩ n
  obtain ⟨t₀, tₙ, ht₀, hsteps, hveq⟩ := stutterSimFrom_pointwise_match h hπA n
  obtain ⟨τB, hτB, m, hm⟩ := extend_reachable_to_trace B ht₀ hsteps
  have hb := hB τB hτB m
  rw [hm, hveq] at hb
  rw [hτA n]
  exact hb

theorem plusMatch_rel_head {A B : Sys} {R : A.State → B.State → Prop} {s s' : A.State} {t : B.State}
    (hpm : PlusMatch R s s' t) : R s t := by
  cases hpm with
  | step_done hR _ _ => exact hR
  | step_stut hR _ _ => exact hR

theorem plusMatch_step_unpack {A B : Sys} {R : A.State → B.State → Prop}
    {s s' : A.State} {t : B.State} (hpm : PlusMatch R s s' t) :
    (∃ t', B.step t t' ∧ R s' t') ∨ (∃ u, B.step t u ∧ PlusMatch R s s' u) := by
  cases hpm with
  | step_done _ hstep hR' => exact Or.inl ⟨_, hstep, hR'⟩
  | step_stut _ hstep hnext => exact Or.inr ⟨_, hstep, hnext⟩

theorem wfStutter_find_progress {A B : Sys} {R : A.State → B.State → Prop}
    {rank : A.State → B.State → Nat}
    (hstep : ∀ s s' t, R s t → A.step s s' → (R s' t ∧ rank s' t < rank s t) ∨ PlusMatch R s s' t)
    {π : Nat → A.State} (hπ : IsExec A π) :
    ∀ (r n : Nat) (t : B.State), R (π n) t → rank (π n) t ≤ r →
      ∃ n', PlusMatch R (π n') (π (n' + 1)) t := by
  intro r
  induction r with
  | zero =>
    intro n t hR hr
    rcases hstep (π n) (π (n + 1)) t hR (hπ.2 n) with ⟨_, hlt⟩ | hpm
    · omega
    · exact ⟨n, hpm⟩
  | succ r ih =>
    intro n t hR hr
    rcases hstep (π n) (π (n + 1)) t hR (hπ.2 n) with ⟨hR', hlt⟩ | hpm
    · exact ih (n + 1) t hR' (by omega)
    · exact ⟨n, hpm⟩

private structure WfCursor (A B : Sys) (R : A.State → B.State → Prop) (π : Nat → A.State) where
  idx : Nat
  bState : B.State
  inChain : Bool
  valid : if inChain then PlusMatch R (π idx) (π (idx + 1)) bState else R (π idx) bState

private theorem wfCursor_rel {A B : Sys} {R : A.State → B.State → Prop} {π : Nat → A.State}
    (c : WfCursor A B R π) : R (π c.idx) c.bState := by
  rcases c with ⟨idx, bState, inChain, valid⟩
  cases inChain with
  | false => exact valid
  | true => exact plusMatch_rel_head valid

theorem wfStutterSimFrom_reflects_termination {A B : Sys} (h : WfStutterSimFrom A B) (P : Spec) :
    EvalShape .termination B P → EvalShape .termination A P := by
  rcases h with ⟨R, rank, hinit, hval, hstep⟩
  intro hB τA ⟨πA, hπA, hτA⟩
  obtain ⟨t₀, ht₀, hR₀⟩ := hinit (πA 0) hπA.1
  have hadvance : ∀ c : WfCursor A B R πA,
      ∃ c' : WfCursor A B R πA, B.step c.bState c'.bState := by
    rintro ⟨idx, bState, inChain, valid⟩
    cases inChain with
    | true =>
      rcases plusMatch_step_unpack valid with ⟨t', hbt, hR'⟩ | ⟨u, hbu, pm'⟩
      · exact ⟨⟨idx + 1, t', false, hR'⟩, hbt⟩
      · exact ⟨⟨idx, u, true, pm'⟩, hbu⟩
    | false =>
      have hex := wfStutter_find_progress hstep hπA (rank (πA idx) bState) idx bState
        valid (Nat.le_refl _)
      obtain ⟨n', pm⟩ := hex
      rcases plusMatch_step_unpack pm with ⟨t', hbt, hR'⟩ | ⟨u, hbu, pm'⟩
      · exact ⟨⟨n' + 1, t', false, hR'⟩, hbt⟩
      · exact ⟨⟨n', u, true, pm'⟩, hbu⟩
  let c₀ : WfCursor A B R πA := ⟨0, t₀, false, hR₀⟩
  let cSeq : Nat → WfCursor A B R πA :=
    fun m => Nat.recOn m c₀ (fun _ cur => Classical.choose (hadvance cur))
  have hExecB : IsExec B (fun m => (cSeq m).bState) := by
    refine ⟨ht₀, ?_⟩
    intro m
    exact Classical.choose_spec (hadvance (cSeq m))
  have htrB : HasTrace B (fun m => B.val (cSeq m).bState) :=
    ⟨fun m => (cSeq m).bState, hExecB, fun _ => rfl⟩
  obtain ⟨m, hm⟩ := hB _ htrB
  refine ⟨(cSeq m).idx, ?_⟩
  rw [hτA (cSeq m).idx, hval _ _ (wfCursor_rel (cSeq m))]
  exact hm

theorem traceIncl_preserves_s2m {src tgt : Sys} (htr : TraceIncl tgt src) (P : Spec) :
    (EvalShape .univSafety src P → EvalShape .univSafety tgt P) ∧
    (¬ EvalShape .existWitness src P → ¬ EvalShape .existWitness tgt P) ∧
    (EvalShape .termination src P → EvalShape .termination tgt P) ∧
    (EvalShape .hyperSubsetClosed src P → EvalShape .hyperSubsetClosed tgt P) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h τ hτ n; exact h τ (htr τ hτ) n
  · intro h ⟨τ, hτ, n, hn⟩; exact h ⟨τ, htr τ hτ, n, hn⟩
  · intro h τ hτ; exact h τ (htr τ hτ)
  · intro h τ₁ τ₂ h₁ h₂ h0 n; exact h τ₁ τ₂ (htr τ₁ h₁) (htr τ₂ h₂) h0 n

private theorem traceEquiv_preserves_all {src tgt : Sys}
    (htr1 : TraceIncl src tgt) (htr2 : TraceIncl tgt src) (sh : PosShape) (P : Spec) :
    EvalShape sh src P → EvalShape sh tgt P := by
  intro hs
  cases sh with
  | univSafety => exact (traceIncl_preserves_s2m htr2 P).1 hs
  | existWitness =>
    rcases hs with ⟨τ, hτ, n, hn⟩
    exact ⟨τ, htr1 τ hτ, n, hn⟩
  | termination => exact (traceIncl_preserves_s2m htr2 P).2.2.1 hs
  | hyperSubsetClosed => exact (traceIncl_preserves_s2m htr2 P).2.2.2 hs
  | hyperGeneral =>
    intro τ₁ h₁
    obtain ⟨τ₂, h₂, h0, n, hneq⟩ := hs τ₁ (htr2 τ₁ h₁)
    exact ⟨τ₂, htr1 τ₂ h₂, h0, n, hneq⟩

/-! ### Single-Boundary Soundness -/

/-- Single-boundary soundness: for every boundary relation `rel`, positive shape `sh`,
positive formula `P`, and realization `Realizes rel src tgt`, `transfer` bounds `tgt`'s status. -/
theorem transfer_sound (rel : BoundaryRel) (sh : PosShape) (P : Spec) (src tgt : Sys)
    (hrel : Realizes rel src tgt) :
    (transfer rel sh (statusOf src sh P)).le (statusOf tgt sh P) := by
  have sup_ok : EvalShape sh tgt P → Status.supported = statusOf tgt sh P :=
    fun h => ((statusOf_eq_supported_iff tgt sh P).2 h).symm
  have con_ok : ¬ EvalShape sh tgt P → Status.contradicted = statusOf tgt sh P :=
    fun h => ((statusOf_eq_contradicted_iff tgt sh P).2 h).symm
  by_cases hs : EvalShape sh src P
  · have hsrc : statusOf src sh P = .supported := (statusOf_eq_supported_iff _ _ _).2 hs
    rw [hsrc]
    cases rel with
    | none => trivial
    | hom d =>
      cases d <;> cases sh <;> simp [transfer, preservesDefinite, Status.le]
      exact sup_ok (isHomFrom_preserves_existWitness hrel P hs)
    | surjHom d =>
      cases d <;> cases sh <;> simp [transfer, preservesDefinite, Status.le]
      exact sup_ok (isHomFrom_preserves_existWitness (isSurjHomFrom_isHomFrom hrel) P hs)
    | posBoundedMorph d =>
      cases d <;> cases sh <;> simp [transfer, preservesDefinite, Status.le]
      · exact sup_ok (isPosBoundedMorphFrom_preserves_univSafety hrel P hs)
      · exact sup_ok (isHomFrom_preserves_existWitness (isPosBoundedMorphFrom_isHomFrom hrel) P hs)
      · exact sup_ok (isPosBoundedMorphFrom_preserves_termination hrel P hs)
    | embed d =>
      cases d with
      | m2s =>
        cases sh <;> simp [transfer, preservesDefinite, Status.le]
        exact sup_ok (isHomFrom_preserves_existWitness (isEmbedFrom_isHomFrom hrel) P hs)
      | s2m =>
        have htr := lockStepSimFrom_traceIncl (isEmbedFrom_lockStepSimFrom hrel)
        have hp := traceIncl_preserves_s2m htr P
        cases sh <;> simp [transfer, preservesDefinite, Status.le]
        · exact sup_ok (hp.1 hs)
        · exact sup_ok (hp.2.2.1 hs)
        · exact sup_ok (hp.2.2.2 hs)
    | traceRefine d =>
      cases d with
      | m2s =>
        cases sh <;> simp [transfer, preservesDefinite, Status.le]
        rcases hs with ⟨τ, hτ, n, hn⟩
        exact sup_ok ⟨τ, hrel τ hτ, n, hn⟩
      | s2m =>
        have hp := traceIncl_preserves_s2m hrel P
        cases sh <;> simp [transfer, preservesDefinite, Status.le]
        · exact sup_ok (hp.1 hs)
        · exact sup_ok (hp.2.2.1 hs)
        · exact sup_ok (hp.2.2.2 hs)
    | stutterSim d =>
      cases d with
      | m2s =>
        cases sh <;> simp [transfer, preservesDefinite, Status.le]
        exact sup_ok (stutterSimFrom_preserves_existWitness hrel P hs)
      | s2m =>
        cases sh <;> simp [transfer, preservesDefinite, Status.le]
        exact sup_ok (stutterSimFrom_reflects_univSafety hrel P hs)
    | wfStutterSim d =>
      cases d with
      | m2s =>
        cases sh <;> simp [transfer, preservesDefinite, Status.le]
        exact sup_ok (stutterSimFrom_preserves_existWitness (wfStutterSimFrom_stutterSimFrom hrel) P hs)
      | s2m =>
        cases sh <;> simp [transfer, preservesDefinite, Status.le]
        · exact sup_ok (stutterSimFrom_reflects_univSafety (wfStutterSimFrom_stutterSimFrom hrel) P hs)
        · exact sup_ok (wfStutterSimFrom_reflects_termination hrel P hs)
    | lockStepSim d =>
      cases d with
      | m2s =>
        have htr := lockStepSimFrom_traceIncl hrel
        cases sh <;> simp [transfer, preservesDefinite, Status.le]
        rcases hs with ⟨τ, hτ, n, hn⟩
        exact sup_ok ⟨τ, htr τ hτ, n, hn⟩
      | s2m =>
        have hp := traceIncl_preserves_s2m (lockStepSimFrom_traceIncl hrel) P
        cases sh <;> simp [transfer, preservesDefinite, Status.le]
        · exact sup_ok (hp.1 hs)
        · exact sup_ok (hp.2.2.1 hs)
        · exact sup_ok (hp.2.2.2 hs)
    | cospanCaptureLower =>
      have hp := traceIncl_preserves_s2m ((cospanSysWitness_iff_traceIncl src tgt).1 hrel) P
      cases sh <;> simp [transfer, preservesDefinite, Status.le]
      · exact sup_ok (hp.1 hs)
      · exact sup_ok (hp.2.2.1 hs)
      · exact sup_ok (hp.2.2.2 hs)
    | certFaithfulSoundPinned =>
      obtain ⟨htr1, htr2⟩ := (certPinnedLink_iff_traceEquiv src tgt).1 hrel
      simp only [transfer, preservesDefinite, Status.le]
      exact sup_ok (traceEquiv_preserves_all htr1 htr2 sh P hs)
    | termRoundTrip =>
      obtain ⟨htr1, htr2⟩ := (roundTripLink_iff_traceEquiv src tgt).1 hrel
      simp only [transfer, preservesDefinite, Status.le]
      exact sup_ok (traceEquiv_preserves_all htr1 htr2 sh P hs)
    | litEntails =>
      simp only [transfer, preservesDefinite, Status.le]
      exact sup_ok (hrel sh P hs)
  · have hsrc : statusOf src sh P = .contradicted := (statusOf_eq_contradicted_iff _ _ _).2 hs
    rw [hsrc]
    cases rel with
    | none => trivial
    | hom d =>
      cases d <;> cases sh <;> simp [transfer, preservesDefinite, Status.le]
      exact con_ok (fun ht => hs (isHomFrom_preserves_existWitness hrel P ht))
    | surjHom d =>
      cases d <;> cases sh <;> simp [transfer, preservesDefinite, Status.le]
      exact con_ok (fun ht => hs (isHomFrom_preserves_existWitness (isSurjHomFrom_isHomFrom hrel) P ht))
    | posBoundedMorph d =>
      cases d <;> cases sh <;> simp [transfer, preservesDefinite, Status.le]
      · exact con_ok (fun ht => hs (isPosBoundedMorphFrom_preserves_univSafety hrel P ht))
      · exact con_ok (fun ht => hs (isHomFrom_preserves_existWitness (isPosBoundedMorphFrom_isHomFrom hrel) P ht))
      · exact con_ok (fun ht => hs (isPosBoundedMorphFrom_preserves_termination hrel P ht))
    | embed d =>
      cases d with
      | m2s =>
        have htr := lockStepSimFrom_traceIncl (isEmbedFrom_lockStepSimFrom hrel)
        have hp := traceIncl_preserves_s2m htr P
        cases sh <;> simp [transfer, preservesDefinite, Status.le]
        · exact con_ok (fun ht => hs (hp.1 ht))
        · exact con_ok (fun ht => hs (hp.2.2.1 ht))
        · exact con_ok (fun ht => hs (hp.2.2.2 ht))
      | s2m =>
        cases sh <;> simp [transfer, preservesDefinite, Status.le]
        exact con_ok (fun ht => hs (isHomFrom_preserves_existWitness (isEmbedFrom_isHomFrom hrel) P ht))
    | traceRefine d =>
      cases d with
      | m2s =>
        have hp := traceIncl_preserves_s2m hrel P
        cases sh <;> simp [transfer, preservesDefinite, Status.le]
        · exact con_ok (fun ht => hs (hp.1 ht))
        · exact con_ok (fun ht => hs (hp.2.2.1 ht))
        · exact con_ok (fun ht => hs (hp.2.2.2 ht))
      | s2m =>
        cases sh <;> simp [transfer, preservesDefinite, Status.le]
        exact con_ok (fun ⟨τ, hτ, n, hn⟩ => hs ⟨τ, hrel τ hτ, n, hn⟩)
    | stutterSim d =>
      cases d with
      | m2s =>
        cases sh <;> simp [transfer, preservesDefinite, Status.le]
        exact con_ok (fun ht => hs (stutterSimFrom_reflects_univSafety hrel P ht))
      | s2m =>
        cases sh <;> simp [transfer, preservesDefinite, Status.le]
        exact con_ok (fun ht => hs (stutterSimFrom_preserves_existWitness hrel P ht))
    | wfStutterSim d =>
      cases d with
      | m2s =>
        cases sh <;> simp [transfer, preservesDefinite, Status.le]
        · exact con_ok (fun ht => hs (stutterSimFrom_reflects_univSafety (wfStutterSimFrom_stutterSimFrom hrel) P ht))
        · exact con_ok (fun ht => hs (wfStutterSimFrom_reflects_termination hrel P ht))
      | s2m =>
        cases sh <;> simp [transfer, preservesDefinite, Status.le]
        exact con_ok (fun ht => hs (stutterSimFrom_preserves_existWitness (wfStutterSimFrom_stutterSimFrom hrel) P ht))
    | lockStepSim d =>
      cases d with
      | m2s =>
        have hp := traceIncl_preserves_s2m (lockStepSimFrom_traceIncl hrel) P
        cases sh <;> simp [transfer, preservesDefinite, Status.le]
        · exact con_ok (fun ht => hs (hp.1 ht))
        · exact con_ok (fun ht => hs (hp.2.2.1 ht))
        · exact con_ok (fun ht => hs (hp.2.2.2 ht))
      | s2m =>
        have htr := lockStepSimFrom_traceIncl hrel
        cases sh <;> simp [transfer, preservesDefinite, Status.le]
        exact con_ok (fun ⟨τ, hτ, n, hn⟩ => hs ⟨τ, htr τ hτ, n, hn⟩)
    | cospanCaptureLower =>
      have htr := (cospanSysWitness_iff_traceIncl src tgt).1 hrel
      cases sh <;> simp [transfer, preservesDefinite, Status.le]
      exact con_ok (fun ⟨τ, hτ, n, hn⟩ => hs ⟨τ, htr τ hτ, n, hn⟩)
    | certFaithfulSoundPinned =>
      obtain ⟨htr1, htr2⟩ := (certPinnedLink_iff_traceEquiv src tgt).1 hrel
      simp only [transfer, preservesDefinite, Status.le]
      exact con_ok (fun ht => hs (traceEquiv_preserves_all htr2 htr1 sh P ht))
    | termRoundTrip =>
      obtain ⟨htr1, htr2⟩ := (roundTripLink_iff_traceEquiv src tgt).1 hrel
      simp only [transfer, preservesDefinite, Status.le]
      exact con_ok (fun ht => hs (traceEquiv_preserves_all htr2 htr1 sh P ht))
    | litEntails =>
      simp [transfer, preservesDefinite, Status.le]

/-- Tightness counterexample for `hrel` in `transfer_sound`: without `Realizes rel src tgt`,
`(transfer .termRoundTrip .univSafety (statusOf src .univSafety specAtom0)).le` fails. -/
theorem cex_transfer_sound_without_realizes :
    ¬ (transfer .termRoundTrip .univSafety (statusOf (constSys valTrue) .univSafety specAtom0)).le
        (statusOf (constSys valFalse) .univSafety specAtom0) := by
  have hs : statusOf (constSys valTrue) .univSafety specAtom0 = .supported := statusOf_pos
  have ht : statusOf (constSys valFalse) .univSafety specAtom0 = .contradicted :=
    (statusOf_eq_contradicted_iff _ _ _).2 evalShape_univSafety_neg
  rw [hs, ht]
  decide

/-- Non-vacuity witness for `transfer_sound` on a definite `.supported` preservation cell. -/
theorem nonvacuity_transfer_sound :
    Realizes (.lockStepSim .s2m) (constSys valTrue) (constSys valTrue) ∧
    transfer (.lockStepSim .s2m) .hyperSubsetClosed
      (statusOf (constSys valTrue) .hyperSubsetClosed specAtom0) = .supported ∧
    statusOf (constSys valTrue) .hyperSubsetClosed specAtom0 = .supported := by
  have hsup : statusOf (constSys valTrue) .hyperSubsetClosed specAtom0 = .supported :=
    (statusOf_eq_supported_iff _ _ _).2 (evalShape_constSys_valTrue specAtom0 rfl).2.2.2.1
  exact ⟨realizes_refl _ _, by rw [hsup]; rfl, hsup⟩

/-- Separation between plain surjective homomorphisms (`IsSurjHomFrom`, no step-lifting) and
positive bounded morphisms (`IsPosBoundedMorphFrom`): even bijective exact-valuation homomorphisms
without step back-lifting break `.univSafety` and `.termination` over execution traces. -/
theorem surjHom_breaks_trace_univSafety_and_termination :
    (∃ A B : Sys, IsSurjHomFrom A B ∧
      statusOf A .univSafety specAtom0 = .supported ∧
      statusOf B .univSafety specAtom0 = .contradicted) ∧
    (∃ C D : Sys, IsSurjHomFrom C D ∧
      statusOf C .termination specAtom0 = .supported ∧
      statusOf D .termination specAtom0 = .contradicted) := by
  let A : Sys := {
    State := Bool
    init := fun b => b = true
    step := fun b b' => b' = b
    val := fun b => if b then valTrue else valFalse
    init_nonempty := ⟨true, rfl⟩
    step_total := fun b => ⟨b, rfl⟩
  }
  let B : Sys := {
    State := Bool
    init := fun b => b = true
    step := fun _ _ => True
    val := fun b => if b then valTrue else valFalse
    init_nonempty := ⟨true, rfl⟩
    step_total := fun b => ⟨b, trivial⟩
  }
  let C : Sys := stepSys valFalse valTrue
  let D : Sys := {
    State := Bool
    init := fun b => b = false
    step := fun _ _ => True
    val := fun b => if b then valTrue else valFalse
    init_nonempty := ⟨false, rfl⟩
    step_total := fun b => ⟨b, trivial⟩
  }
  refine ⟨⟨A, B, ⟨id, Function.surjective_id, fun _ h => h, fun _ _ _ => trivial, fun _ _ h => h⟩, ?_, ?_⟩,
    ⟨C, D, ⟨id, Function.surjective_id, fun _ h => h, fun _ _ _ => trivial, fun _ _ h => h⟩, ?_, ?_⟩⟩
  · rw [statusOf_eq_supported_iff]
    rintro τ ⟨π, ⟨h0, hstep⟩, hτ⟩ n
    have htrue : ∀ k, π k = true := by
      intro k
      induction k with
      | zero => exact h0
      | succ k ih => exact (hstep k).trans ih
    rw [hτ n]
    simp [A, htrue n, evalVal, specAtom0, valTrue]
  · rw [statusOf_eq_contradicted_iff]
    intro hsafe
    let πB : Nat → Bool := fun n => match n with | 0 => true | _ + 1 => false
    have htrB : HasTrace B (fun n => B.val (πB n)) := ⟨πB, ⟨rfl, fun _ => trivial⟩, fun _ => rfl⟩
    have h1 := hsafe _ htrB 1
    simp [B, πB, evalVal, specAtom0, valFalse] at h1
  · rw [statusOf_eq_supported_iff]
    intro τ hτ
    exact ⟨1, by rw [(hasTrace_stepSys_iff valFalse valTrue τ).1 hτ |>.2 0]; rfl⟩
  · rw [statusOf_eq_contradicted_iff]
    intro hterm
    have htrD : HasTrace D (fun _ => valFalse) := ⟨fun _ => false, ⟨rfl, fun _ => trivial⟩, fun _ => rfl⟩
    obtain ⟨n, hn⟩ := hterm _ htrD
    simp [evalVal, specAtom0, valFalse] at hn

/-! ### `5 × 5` Upper-Triangular Shape Separation -/

/-- Row ordering of five boundary relations witnessing upper-triangular separation of `PosShape`. -/
def sepRel : Fin 5 → BoundaryRel
  | ⟨0, _⟩ => .litEntails
  | ⟨1, _⟩ => .lockStepSim .s2m
  | ⟨2, _⟩ => .wfStutterSim .s2m
  | ⟨3, _⟩ => .stutterSim .s2m
  | ⟨4, _⟩ => .embed .m2s

/-- Column ordering of the five positive claim shapes matching `sepRel`. -/
def sepShape : Fin 5 → PosShape
  | ⟨0, _⟩ => .hyperGeneral
  | ⟨1, _⟩ => .hyperSubsetClosed
  | ⟨2, _⟩ => .termination
  | ⟨3, _⟩ => .univSafety
  | ⟨4, _⟩ => .existWitness

theorem sepRel_pos : sepRel ⟨0, by omega⟩ = .litEntails := rfl
theorem sepRel_neg : sepRel ⟨1, by omega⟩ ≠ .litEntails := by decide
theorem sepShape_pos : sepShape ⟨0, by omega⟩ = .hyperGeneral := rfl
theorem sepShape_neg : sepShape ⟨1, by omega⟩ ≠ .hyperGeneral := by decide

/-- Upper-triangular separation theorem: every diagonal entry `(i, i)` preserves `.supported`
while every strict sub-diagonal entry `j < i` collapses `.supported` to `.undetermined`. -/
theorem sepMatrix_upperTriangular :
    (∀ i : Fin 5, transfer (sepRel i) (sepShape i) .supported = .supported) ∧
    (∀ i j : Fin 5, j.1 < i.1 → transfer (sepRel i) (sepShape j) .supported = .undetermined) := by
  decide

/-- All five `PosShape` columns have pairwise distinct `.supported` transfer profiles. -/
theorem posShape_columns_pairwise_distinct (sh₁ sh₂ : PosShape) (hne : sh₁ ≠ sh₂) :
    ∃ rel : BoundaryRel, transfer rel sh₁ .supported ≠ transfer rel sh₂ .supported := by
  cases sh₁ <;> cases sh₂ <;> first
    | contradiction
    | exact ⟨.embed .m2s, by decide⟩
    | exact ⟨.stutterSim .s2m, by decide⟩
    | exact ⟨.wfStutterSim .s2m, by decide⟩
    | exact ⟨.lockStepSim .s2m, by decide⟩

/-- Tightness counterexample for `hne : sh₁ ≠ sh₂` in `posShape_columns_pairwise_distinct`. -/
theorem cex_posShape_distinct_without_ne :
    ¬ ∃ rel : BoundaryRel,
        transfer rel .univSafety .supported ≠ transfer rel .univSafety .supported := by
  rintro ⟨_, hne⟩
  exact hne rfl

/-- Non-vacuity witness for `sepMatrix_subdiagonal_countermodels` and `posShape_columns_pairwise_distinct`. -/
theorem nonvacuity_posShape_distinct :
    ((⟨1, by omega⟩ : Fin 5).1 < (⟨2, by omega⟩ : Fin 5).1) ∧
    PosShape.termination ≠ PosShape.hyperSubsetClosed ∧
    transfer (.wfStutterSim .s2m) .termination .supported = .supported ∧
    transfer (.wfStutterSim .s2m) .hyperSubsetClosed .supported = .undetermined := by
  decide

/-! ### Cell-by-Cell Sharpness of `.undetermined` -/

theorem isEmbedFrom_one_two (a₀ a₁ b₀ b₁ : Valuation) :
    IsEmbedFrom (oneBranchSys a₀ a₁) (twoBranchSys a₀ a₁ b₀ b₁) := by
  refine ⟨fun p => (⟨0, by omega⟩, p.2), ?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨i₁, hi₁⟩, s₁⟩ ⟨⟨i₂, hi₂⟩, s₂⟩ h
    have hi : i₁ = i₂ := by omega
    cases hi
    cases h
    rfl
  · intro _; exact Iff.rfl
  · rintro ⟨⟨i₁, hi₁⟩, s₁⟩ ⟨⟨i₂, hi₂⟩, s₂⟩
    have hi : i₁ = i₂ := by omega
    subst hi
    simp [oneBranchSys, twoBranchSys, maskedBranchSys]
  · rintro ⟨⟨i, hi⟩, s⟩
    simp [oneBranchSys, twoBranchSys, maskedBranchSys]

theorem isEmbedFrom_two_three (a₀ a₁ b₀ b₁ c₀ c₁ : Valuation) :
    IsEmbedFrom (twoBranchSys a₀ a₁ b₀ b₁) (threeBranchSys a₀ a₁ b₀ b₁ c₀ c₁) := by
  refine ⟨fun p => (⟨p.1.1, by omega⟩, p.2), ?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨i₁, hi₁⟩, s₁⟩ ⟨⟨i₂, hi₂⟩, s₂⟩ h
    injection h with hfin hs
    injection hfin with hnat
    subst hnat hs
    rfl
  · intro _; exact Iff.rfl
  · rintro ⟨⟨i₁, hi₁⟩, s₁⟩ ⟨⟨i₂, hi₂⟩, s₂⟩
    dsimp only [twoBranchSys, threeBranchSys, maskedBranchSys]
    constructor
    · rintro ⟨h1, h2⟩
      injection h1 with hnat
      subst hnat
      exact ⟨rfl, h2⟩
    · rintro ⟨h1, h2⟩
      injection h1 with hnat
      subst hnat
      exact ⟨rfl, h2⟩
  · rintro ⟨⟨i, hi⟩, s⟩
    by_cases h0 : i = 0
    · subst h0; simp [twoBranchSys, threeBranchSys, maskedBranchSys]
    · have h1 : i = 1 := by omega
      subst h1; simp [twoBranchSys, threeBranchSys, maskedBranchSys]

theorem evalShape_oneBranch (v₀ v₁ : Valuation) :
    (∀ τ, HasTrace (oneBranchSys v₀ v₁) τ ↔ τ 0 = v₀ ∧ ∀ n, τ (n + 1) = v₁) := by
  intro τ
  unfold oneBranchSys
  rw [hasTrace_maskedBranchSys_iff]
  constructor
  · rintro ⟨_, h0, h1⟩; exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩; exact ⟨⟨0, by omega⟩, h0, h1⟩

theorem evalShape_oneBranch_vt (P : Spec) (ht : evalVal P valTrue = true) :
    EvalShape .univSafety (oneBranchSys valTrue valTrue) P ∧
    EvalShape .termination (oneBranchSys valTrue valTrue) P := by
  refine ⟨?_, ?_⟩
  · intro τ hτ n
    rcases (evalShape_oneBranch valTrue valTrue τ).1 hτ with ⟨h0, h1⟩
    cases n with
    | zero => rw [h0, ht]
    | succ m => rw [h1 m, ht]
  · intro τ hτ
    rcases (evalShape_oneBranch valTrue valTrue τ).1 hτ with ⟨h0, _⟩
    exact ⟨0, by rw [h0, ht]⟩

theorem evalShape_oneBranch_vf (P : Spec) (hf : evalVal P valFalse = false) :
    ¬ EvalShape .existWitness (oneBranchSys valFalse valFalse) P := by
  rintro ⟨τ, hτ, n, hn⟩
  rcases (evalShape_oneBranch valFalse valFalse τ).1 hτ with ⟨h0, h1⟩
  cases n with
  | zero => rw [h0, hf] at hn; cases hn
  | succ m => rw [h1 m, hf] at hn; cases hn

theorem evalShape_oneBranch_vf_vt (P : Spec) :
    EvalShape .hyperSubsetClosed (oneBranchSys valFalse valTrue) P ∧
    ¬ EvalShape .hyperGeneral (oneBranchSys valFalse valTrue) P := by
  refine ⟨?_, ?_⟩
  · intro τ₁ τ₂ h₁ h₂ _ n
    rcases (evalShape_oneBranch valFalse valTrue τ₁).1 h₁ with ⟨h10, hs1⟩
    rcases (evalShape_oneBranch valFalse valTrue τ₂).1 h₂ with ⟨h20, hs2⟩
    cases n with
    | zero => rw [h10, h20]
    | succ m => rw [hs1 m, hs2 m]
  · intro hgni
    let τ₀ : Trace := fun n => match n with | 0 => valFalse | _ + 1 => valTrue
    have hτ₀ : HasTrace (oneBranchSys valFalse valTrue) τ₀ :=
      (evalShape_oneBranch valFalse valTrue τ₀).2 ⟨rfl, fun _ => rfl⟩
    obtain ⟨τ₂, h₂, _, n, hneq⟩ := hgni τ₀ hτ₀
    rcases (evalShape_oneBranch valFalse valTrue τ₂).1 h₂ with ⟨h20, hs2⟩
    cases n with
    | zero => simp [τ₀, h20] at hneq
    | succ m => simp [τ₀, hs2 m] at hneq

theorem evalShape_twoBranch_vt_vf (P : Spec)
    (hf : evalVal P valFalse = false) (ht : evalVal P valTrue = true) :
    ¬ EvalShape .univSafety (twoBranchSys valTrue valTrue valFalse valFalse) P ∧
    ¬ EvalShape .termination (twoBranchSys valTrue valTrue valFalse valFalse) P ∧
    EvalShape .existWitness (twoBranchSys valFalse valFalse valTrue valTrue) P := by
  have hbad : HasTrace (twoBranchSys valTrue valTrue valFalse valFalse) (fun _ => valFalse) := by
    unfold twoBranchSys; rw [hasTrace_maskedBranchSys_iff]
    exact ⟨⟨1, by omega⟩, rfl, fun _ => rfl⟩
  have hgood : HasTrace (twoBranchSys valFalse valFalse valTrue valTrue) (fun _ => valTrue) := by
    unfold twoBranchSys; rw [hasTrace_maskedBranchSys_iff]
    exact ⟨⟨1, by omega⟩, rfl, fun _ => rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h; have := h _ hbad 0; simp [hf] at this
  · intro h; obtain ⟨n, hn⟩ := h _ hbad; simp [hf] at hn
  · exact ⟨fun _ => valTrue, hgood, 0, ht⟩

theorem evalShape_threeBranch_no_gni (P : Spec)
    (hf : evalVal P valFalse = false) (ht : evalVal P valTrue = true) :
    ¬ EvalShape .hyperGeneral
      (threeBranchSys valFalse valTrue valFalse valFalse valTrue valTrue) P := by
  intro hgni
  have htr : HasTrace (threeBranchSys valFalse valTrue valFalse valFalse valTrue valTrue)
      (fun _ => valTrue) := by
    unfold threeBranchSys; rw [hasTrace_maskedBranchSys_iff]
    exact ⟨⟨2, by omega⟩, rfl, fun _ => rfl⟩
  obtain ⟨τ₂, h₂, h0, n, hneq⟩ := hgni _ htr
  unfold threeBranchSys at h₂
  rw [hasTrace_maskedBranchSys_iff] at h₂
  rcases h₂ with ⟨i, hi0, hi1⟩
  by_cases hz : i.1 = 0
  · simp [hz, ht, hf, hi0] at h0
  · by_cases ho : i.1 = 1
    · simp [ho, ht, hf, hi0] at h0
    · have h2 : i.1 = 2 := by have := i.2; omega
      cases n with
      | zero => simp [h2, hi0, ht] at hneq
      | succ m =>
        have hs := hi1 m
        simp [h2, hs, ht] at hneq

theorem embedM2S_flip_witness (sh : PosShape) (P : Spec) (b : Bool)
    (hf : evalVal P valFalse = false) (ht : evalVal P valTrue = true)
    (hnot : preservesDefinite (.embed .m2s) sh b = false) :
    ∃ A B : Sys, IsEmbedFrom A B ∧
      statusOf A sh P = (if b then .supported else .contradicted) ∧
      statusOf B sh P = (if b then .contradicted else .supported) := by
  cases sh <;> cases b <;> simp [preservesDefinite] at hnot
  · -- (univSafety, true)
    refine ⟨oneBranchSys valTrue valTrue, twoBranchSys valTrue valTrue valFalse valFalse,
      isEmbedFrom_one_two _ _ _ _, ?_, ?_⟩
    · exact (statusOf_eq_supported_iff _ _ _).2 (evalShape_oneBranch_vt P ht).1
    · exact (statusOf_eq_contradicted_iff _ _ _).2 (evalShape_twoBranch_vt_vf P hf ht).1
  · -- (existWitness, false)
    refine ⟨oneBranchSys valFalse valFalse, twoBranchSys valFalse valFalse valTrue valTrue,
      isEmbedFrom_one_two _ _ _ _, ?_, ?_⟩
    · exact (statusOf_eq_contradicted_iff _ _ _).2 (evalShape_oneBranch_vf P hf)
    · exact (statusOf_eq_supported_iff _ _ _).2 (evalShape_twoBranch_vt_vf P hf ht).2.2
  · -- (termination, true)
    refine ⟨oneBranchSys valTrue valTrue, twoBranchSys valTrue valTrue valFalse valFalse,
      isEmbedFrom_one_two _ _ _ _, ?_, ?_⟩
    · exact (statusOf_eq_supported_iff _ _ _).2 (evalShape_oneBranch_vt P ht).2
    · exact (statusOf_eq_contradicted_iff _ _ _).2 (evalShape_twoBranch_vt_vf P hf ht).2.1
  · -- (hyperSubsetClosed, true)
    refine ⟨oneBranchSys valFalse valTrue, twoBranchSys valFalse valTrue valFalse valFalse,
      isEmbedFrom_one_two _ _ _ _, ?_, ?_⟩
    · exact (statusOf_eq_supported_iff _ _ _).2 (evalShape_oneBranch_vf_vt P).1
    · exact (statusOf_eq_contradicted_iff _ _ _).2 (evalShape_twoBranch_gni P hf ht).1
  · -- (hyperGeneral, false)
    refine ⟨oneBranchSys valFalse valTrue, twoBranchSys valFalse valTrue valFalse valFalse,
      isEmbedFrom_one_two _ _ _ _, ?_, ?_⟩
    · exact (statusOf_eq_contradicted_iff _ _ _).2 (evalShape_oneBranch_vf_vt P).2
    · exact (statusOf_eq_supported_iff _ _ _).2 (evalShape_twoBranch_gni P hf ht).2
  · -- (hyperGeneral, true)
    refine ⟨twoBranchSys valFalse valTrue valFalse valFalse,
      threeBranchSys valFalse valTrue valFalse valFalse valTrue valTrue,
      isEmbedFrom_two_three _ _ _ _ _ _, ?_, ?_⟩
    · exact (statusOf_eq_supported_iff _ _ _).2 (evalShape_twoBranch_gni P hf ht).2
    · exact (statusOf_eq_contradicted_iff _ _ _).2 (evalShape_threeBranch_no_gni P hf ht)

theorem wfStutter_finiteStutter_to_step :
    WfStutterSimFrom (finiteStutterSys valFalse valTrue) (stepSys valFalse valTrue) := by
  refine ⟨fun s b => if s.1 == 2 then b = true else b = false,
    fun s _ => if s.1 == 0 then 1 else 0, ?_, ?_, ?_⟩
  · rintro ⟨n, hn⟩ hs₀
    refine ⟨false, rfl, ?_⟩
    simp [finiteStutterSys] at hs₀
    subst hs₀
    rfl
  · intro s b hR
    by_cases h2 : s.1 == 2
    · simp [h2] at hR; subst hR; simp [finiteStutterSys, stepSys, h2]
    · simp [h2] at hR; subst hR; simp [finiteStutterSys, stepSys, h2]
  · rintro ⟨s, hs⟩ ⟨s', hs'⟩ b hR hstep
    simp only [finiteStutterSys] at hstep
    rcases hstep with ⟨hs0, hs'1 | hs'2⟩ | ⟨hs1, hs'2⟩ | ⟨hs2, hs'2⟩
    · subst hs0 hs'1
      simp at hR; subst hR
      exact Or.inl ⟨rfl, by show 0 < 1; omega⟩
    · subst hs0 hs'2
      simp at hR; subst hR
      exact Or.inr (.step_done rfl rfl rfl)
    · subst hs1 hs'2
      simp at hR; subst hR
      exact Or.inr (.step_done rfl rfl rfl)
    · subst hs2 hs'2
      simp at hR; subst hR
      exact Or.inr (.step_done rfl rfl rfl)

theorem evalShape_finiteStutter_not_subClosed (P : Spec)
    (hf : evalVal P valFalse = false) (ht : evalVal P valTrue = true) :
    ¬ EvalShape .hyperSubsetClosed (finiteStutterSys valFalse valTrue) P ∧
    EvalShape .hyperSubsetClosed (stepSys valFalse valTrue) P := by
  refine ⟨?_, ?_⟩
  · intro hsub
    let π₁ : Nat → (finiteStutterSys valFalse valTrue).State :=
      fun n => match n with | 0 => ⟨0, by omega⟩ | _ + 1 => ⟨2, by omega⟩
    let π₂ : Nat → (finiteStutterSys valFalse valTrue).State :=
      fun n => match n with
        | 0 => ⟨0, by omega⟩
        | 1 => ⟨1, by omega⟩
        | _ + 2 => ⟨2, by omega⟩
    have htr₁ : HasTrace (finiteStutterSys valFalse valTrue)
        (fun n => (finiteStutterSys valFalse valTrue).val (π₁ n)) := by
      refine ⟨π₁, ⟨rfl, ?_⟩, fun _ => rfl⟩
      intro n; cases n <;> simp [π₁, finiteStutterSys]
    have htr₂ : HasTrace (finiteStutterSys valFalse valTrue)
        (fun n => (finiteStutterSys valFalse valTrue).val (π₂ n)) := by
      refine ⟨π₂, ⟨rfl, ?_⟩, fun _ => rfl⟩
      intro n; cases n with
      | zero => simp [π₂, finiteStutterSys]
      | succ m => cases m <;> simp [π₂, finiteStutterSys]
    have heq := hsub _ _ htr₁ htr₂ rfl 1
    simp [π₁, π₂, finiteStutterSys, ht, hf] at heq
  · intro τ₁ τ₂ h₁ h₂ _ n
    rcases (hasTrace_stepSys_iff valFalse valTrue τ₁).1 h₁ with ⟨h10, h1s⟩
    rcases (hasTrace_stepSys_iff valFalse valTrue τ₂).1 h₂ with ⟨h20, h2s⟩
    cases n with
    | zero => rw [h10, h20]
    | succ m => rw [h1s m, h2s m]

theorem stutter_constFalse_to_step :
    StutterSimFrom (constSys valFalse) (stepSys valFalse valTrue) := by
  refine ⟨fun _ b => b = false, fun _ _ => ⟨false, rfl, rfl⟩, ?_, ?_⟩
  · intro _ b hb; subst hb; rfl
  · intro _ _ b hb _; exact Or.inl hb

theorem evalShape_stepSys_terminates (P : Spec) (ht : evalVal P valTrue = true) :
    EvalShape .termination (stepSys valFalse valTrue) P := by
  intro τ hτ
  exact ⟨1, by rw [(hasTrace_stepSys_iff valFalse valTrue τ).1 hτ |>.2 0, ht]⟩

theorem isPosBoundedMorphFrom_to_constValTrue (A : Sys) :
    IsPosBoundedMorphFrom A (constSys valTrue) := by
  refine ⟨fun _ => (), fun _ _ => trivial, ?_, fun _ _ _ => trivial, ?_, ?_⟩
  · intro _ _; obtain ⟨s₀, hs₀⟩ := A.init_nonempty; exact ⟨s₀, hs₀, rfl⟩
  · intro s u _; cases u; obtain ⟨s', hs'⟩ := A.step_total s; exact ⟨s', hs', rfl⟩
  · intro _ _ _; rfl

theorem isSurjHomFrom_to_constValTrue (A : Sys) : IsSurjHomFrom A (constSys valTrue) := by
  refine ⟨fun _ => (), ?_, fun _ _ => trivial, fun _ _ _ => trivial, fun _ _ _ => rfl⟩
  intro u; cases u; obtain ⟨s₀, _⟩ := A.init_nonempty; exact ⟨s₀, rfl⟩

theorem isHomFrom_to_constValTrue (A : Sys) : IsHomFrom A (constSys valTrue) :=
  isPosBoundedMorphFrom_isHomFrom (isPosBoundedMorphFrom_to_constValTrue A)

theorem posBoundedMorphM2S_flip_witness (sh : PosShape) (P : Spec) (b : Bool)
    (hf : evalVal P valFalse = false) (ht : evalVal P valTrue = true)
    (hnot : preservesDefinite (.posBoundedMorph .m2s) sh b = false) :
    ∃ A B : Sys, IsPosBoundedMorphFrom A B ∧
      statusOf A sh P = (if b then .supported else .contradicted) ∧
      statusOf B sh P = (if b then .contradicted else .supported) := by
  have hvt := evalShape_constSys_valTrue P ht
  have hvf := evalShape_constSys_valFalse P hf
  have hgni := evalShape_twoBranch_gni P hf ht
  cases sh <;> cases b <;> simp [preservesDefinite] at hnot
  · exact ⟨constSys valFalse, constSys valTrue, isPosBoundedMorphFrom_to_constValTrue _,
      (statusOf_eq_contradicted_iff _ _ _).2 hvf.1, (statusOf_eq_supported_iff _ _ _).2 hvt.1⟩
  · exact ⟨constSys valFalse, constSys valTrue, isPosBoundedMorphFrom_to_constValTrue _,
      (statusOf_eq_contradicted_iff _ _ _).2 hvf.2.1, (statusOf_eq_supported_iff _ _ _).2 hvt.2.1⟩
  · exact ⟨constSys valFalse, constSys valTrue, isPosBoundedMorphFrom_to_constValTrue _,
      (statusOf_eq_contradicted_iff _ _ _).2 hvf.2.2.1, (statusOf_eq_supported_iff _ _ _).2 hvt.2.2.1⟩
  · exact ⟨twoBranchSys valFalse valTrue valFalse valFalse, constSys valTrue,
      isPosBoundedMorphFrom_to_constValTrue _,
      (statusOf_eq_contradicted_iff _ _ _).2 hgni.1,
      (statusOf_eq_supported_iff _ _ _).2 hvt.2.2.2.1⟩
  · let A := twoBranchSys valFalse valTrue valTrue valFalse
    let B := twoBranchSys valTrue valTrue valTrue valFalse
    have hbm : IsPosBoundedMorphFrom A B := by
      refine ⟨id, fun _ h => h, fun t ht' => ⟨t, ht', rfl⟩,
        fun _ _ h => h, fun _ t' ht' => ⟨t', ht', rfl⟩, ?_⟩
      rintro ⟨⟨i, hi⟩, step⟩ a ha
      by_cases h0 : i = 0
      · subst h0
        cases step
        · simp [A, twoBranchSys, maskedBranchSys, valFalse] at ha
        · rfl
      · have h1 : i = 1 := by omega
        subst h1
        exact ha
    refine ⟨A, B, hbm, ?_, ?_⟩
    · simp only [↓reduceIte, statusOf_eq_supported_iff]
      intro τ₁ τ₂ h₁ h₂ h0eq n
      unfold A twoBranchSys at h₁ h₂
      rw [hasTrace_maskedBranchSys_iff] at h₁ h₂
      rcases h₁ with ⟨i₁, h10, h11⟩
      rcases h₂ with ⟨i₂, h20, h21⟩
      by_cases hi1 : i₁.1 = 0 <;> by_cases hi2 : i₂.1 = 0
      · cases n with
        | zero => rw [h10, h20]; simp [hi1, hi2]
        | succ m => rw [h11 m, h21 m]; simp [hi1, hi2]
      · have hi2' : i₂.1 = 1 := by have := i₂.2; omega
        simp [h10, h20, hi1, hi2', ht, hf] at h0eq
      · have hi1' : i₁.1 = 1 := by have := i₁.2; omega
        simp [h10, h20, hi1', hi2, ht, hf] at h0eq
      · have hi1' : i₁.1 = 1 := by have := i₁.2; omega
        have hi2' : i₂.1 = 1 := by have := i₂.2; omega
        cases n with
        | zero => rw [h10, h20]; simp [hi1', hi2']
        | succ m => rw [h11 m, h21 m]; simp [hi1', hi2']
    · simp only [↓reduceIte, statusOf_eq_contradicted_iff]
      intro hsub
      let τ₀ : Trace := fun _ => valTrue
      let τ₁ : Trace := fun n => match n with | 0 => valTrue | _ + 1 => valFalse
      have hτ₀ : HasTrace B τ₀ := by
        unfold B twoBranchSys; rw [hasTrace_maskedBranchSys_iff]
        exact ⟨⟨0, by omega⟩, rfl, fun _ => rfl⟩
      have hτ₁ : HasTrace B τ₁ := by
        unfold B twoBranchSys; rw [hasTrace_maskedBranchSys_iff]
        exact ⟨⟨1, by omega⟩, rfl, fun _ => rfl⟩
      have heq := hsub τ₀ τ₁ hτ₀ hτ₁ rfl 1
      simp [τ₀, τ₁, ht, hf] at heq
  · let A := twoBranchSys valFalse valFalse valFalse valFalse
    let B := twoBranchSys valFalse valTrue valFalse valFalse
    have hbm : IsPosBoundedMorphFrom A B := by
      refine ⟨id, fun _ h => h, fun t ht' => ⟨t, ht', rfl⟩,
        fun _ _ h => h, fun _ t' ht' => ⟨t', ht', rfl⟩, ?_⟩
      rintro ⟨_, step⟩ _ ha
      cases step <;> simp [A, twoBranchSys, maskedBranchSys, valFalse] at ha
    refine ⟨A, B, hbm, ?_, (statusOf_eq_supported_iff _ _ _).2 hgni.2⟩
    simp only [Bool.false_eq_true, ↓reduceIte, statusOf_eq_contradicted_iff]
    intro hgA
    have htr : HasTrace A (fun _ => valFalse) := by
      unfold A twoBranchSys; rw [hasTrace_maskedBranchSys_iff]
      exact ⟨⟨0, by omega⟩, rfl, fun _ => rfl⟩
    obtain ⟨τ₂, h₂, _, n, hneq⟩ := hgA _ htr
    unfold A twoBranchSys at h₂
    rw [hasTrace_maskedBranchSys_iff] at h₂
    rcases h₂ with ⟨i, hi0, hi1⟩
    by_cases hz : i.1 = 0
    · cases n with
      | zero => simp [hz, hi0] at hneq
      | succ m => have hs := hi1 m; simp [hz] at hs; simp [hs] at hneq
    · have ho : i.1 = 1 := by have := i.2; omega
      cases n with
      | zero => simp [ho, hi0] at hneq
      | succ m => have hs := hi1 m; simp [ho] at hs; simp [hs] at hneq
  · exact ⟨twoBranchSys valFalse valTrue valFalse valFalse, constSys valTrue,
      isPosBoundedMorphFrom_to_constValTrue _,
      (statusOf_eq_supported_iff _ _ _).2 hgni.2,
      (statusOf_eq_contradicted_iff _ _ _).2 hvt.2.2.2.2⟩

theorem surjHomM2S_flip_witness (sh : PosShape) (P : Spec) (b : Bool)
    (hf : evalVal P valFalse = false) (ht : evalVal P valTrue = true)
    (hnot : preservesDefinite (.surjHom .m2s) sh b = false) :
    ∃ A B : Sys, IsSurjHomFrom A B ∧
      statusOf A sh P = (if b then .supported else .contradicted) ∧
      statusOf B sh P = (if b then .contradicted else .supported) := by
  by_cases hbm_not : preservesDefinite (.posBoundedMorph .m2s) sh b = false
  · have hvt := evalShape_constSys_valTrue P ht
    have hvf := evalShape_constSys_valFalse P hf
    have hgni := evalShape_twoBranch_gni P hf ht
    cases sh <;> cases b <;> simp [preservesDefinite] at hbm_not
    · exact ⟨constSys valFalse, constSys valTrue, isSurjHomFrom_to_constValTrue _,
        (statusOf_eq_contradicted_iff _ _ _).2 hvf.1, (statusOf_eq_supported_iff _ _ _).2 hvt.1⟩
    · exact ⟨constSys valFalse, constSys valTrue, isSurjHomFrom_to_constValTrue _,
        (statusOf_eq_contradicted_iff _ _ _).2 hvf.2.1, (statusOf_eq_supported_iff _ _ _).2 hvt.2.1⟩
    · exact ⟨constSys valFalse, constSys valTrue, isSurjHomFrom_to_constValTrue _,
        (statusOf_eq_contradicted_iff _ _ _).2 hvf.2.2.1, (statusOf_eq_supported_iff _ _ _).2 hvt.2.2.1⟩
    · exact ⟨twoBranchSys valFalse valTrue valFalse valFalse, constSys valTrue,
        isSurjHomFrom_to_constValTrue _,
        (statusOf_eq_contradicted_iff _ _ _).2 hgni.1,
        (statusOf_eq_supported_iff _ _ _).2 hvt.2.2.2.1⟩
    · let A := twoBranchSys valFalse valTrue valTrue valFalse
      let B := twoBranchSys valTrue valTrue valTrue valFalse
      have hsurj : IsSurjHomFrom A B := by
        refine ⟨id, Function.surjective_id, fun _ h => h, fun _ _ h => h, ?_⟩
        rintro ⟨⟨i, hi⟩, step⟩ a ha
        by_cases h0 : i = 0
        · subst h0
          cases step
          · simp [A, twoBranchSys, maskedBranchSys, valFalse] at ha
          · rfl
        · have h1 : i = 1 := by omega
          subst h1
          exact ha
      refine ⟨A, B, hsurj, ?_, ?_⟩
      · simp only [↓reduceIte, statusOf_eq_supported_iff]
        intro τ₁ τ₂ h₁ h₂ h0eq n
        unfold A twoBranchSys at h₁ h₂
        rw [hasTrace_maskedBranchSys_iff] at h₁ h₂
        rcases h₁ with ⟨i₁, h10, h11⟩
        rcases h₂ with ⟨i₂, h20, h21⟩
        by_cases hi1 : i₁.1 = 0 <;> by_cases hi2 : i₂.1 = 0
        · cases n with
          | zero => rw [h10, h20]; simp [hi1, hi2]
          | succ m => rw [h11 m, h21 m]; simp [hi1, hi2]
        · have hi2' : i₂.1 = 1 := by have := i₂.2; omega
          simp [h10, h20, hi1, hi2', ht, hf] at h0eq
        · have hi1' : i₁.1 = 1 := by have := i₁.2; omega
          simp [h10, h20, hi1', hi2, ht, hf] at h0eq
        · have hi1' : i₁.1 = 1 := by have := i₁.2; omega
          have hi2' : i₂.1 = 1 := by have := i₂.2; omega
          cases n with
          | zero => rw [h10, h20]; simp [hi1', hi2']
          | succ m => rw [h11 m, h21 m]; simp [hi1', hi2']
      · simp only [↓reduceIte, statusOf_eq_contradicted_iff]
        intro hsub
        let τ₀ : Trace := fun _ => valTrue
        let τ₁ : Trace := fun n => match n with | 0 => valTrue | _ + 1 => valFalse
        have hτ₀ : HasTrace B τ₀ := by
          unfold B twoBranchSys; rw [hasTrace_maskedBranchSys_iff]
          exact ⟨⟨0, by omega⟩, rfl, fun _ => rfl⟩
        have hτ₁ : HasTrace B τ₁ := by
          unfold B twoBranchSys; rw [hasTrace_maskedBranchSys_iff]
          exact ⟨⟨1, by omega⟩, rfl, fun _ => rfl⟩
        have heq := hsub τ₀ τ₁ hτ₀ hτ₁ rfl 1
        simp [τ₀, τ₁, ht, hf] at heq
    · -- (hyperGeneral, false): `h = id` (surjective!)
      let A := twoBranchSys valFalse valFalse valFalse valFalse
      let B := twoBranchSys valFalse valTrue valFalse valFalse
      have hsurj : IsSurjHomFrom A B := by
        refine ⟨id, Function.surjective_id, fun _ h => h, fun _ _ h => h, ?_⟩
        rintro ⟨_, step⟩ _ ha
        cases step <;> simp [A, twoBranchSys, maskedBranchSys, valFalse] at ha
      refine ⟨A, B, hsurj, ?_, (statusOf_eq_supported_iff _ _ _).2 hgni.2⟩
      simp only [Bool.false_eq_true, ↓reduceIte, statusOf_eq_contradicted_iff]
      intro hgA
      have htr : HasTrace A (fun _ => valFalse) := by
        unfold A twoBranchSys; rw [hasTrace_maskedBranchSys_iff]
        exact ⟨⟨0, by omega⟩, rfl, fun _ => rfl⟩
      obtain ⟨τ₂, h₂, _, n, hneq⟩ := hgA _ htr
      unfold A twoBranchSys at h₂
      rw [hasTrace_maskedBranchSys_iff] at h₂
      rcases h₂ with ⟨i, hi0, hi1⟩
      by_cases hz : i.1 = 0
      · cases n with
        | zero => simp [hz, hi0] at hneq
        | succ m => have hs := hi1 m; simp [hz] at hs; simp [hs] at hneq
      · have ho : i.1 = 1 := by have := i.2; omega
        cases n with
        | zero => simp [ho, hi0] at hneq
        | succ m => have hs := hi1 m; simp [ho] at hs; simp [hs] at hneq
    · exact ⟨twoBranchSys valFalse valTrue valFalse valFalse, constSys valTrue,
        isSurjHomFrom_to_constValTrue _,
        (statusOf_eq_supported_iff _ _ _).2 hgni.2,
        (statusOf_eq_contradicted_iff _ _ _).2 hvt.2.2.2.2⟩
  · -- Remaining 2 cells where `posBoundedMorph` is `true` and `surjHom` is `false`:
    -- `(univSafety, true)` and `(termination, true)`!
    have hrem : (sh = .univSafety ∧ b = true) ∨ (sh = .termination ∧ b = true) := by
      revert hnot hbm_not; cases sh <;> cases b <;> decide
    rcases hrem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · let A : Sys := {
        State := Bool
        init := fun b => b = true
        step := fun b b' => b' = b
        val := fun b => if b then valTrue else valFalse
        init_nonempty := ⟨true, rfl⟩
        step_total := fun b => ⟨b, rfl⟩
      }
      let B : Sys := {
        State := Bool
        init := fun b => b = true
        step := fun _ _ => True
        val := fun b => if b then valTrue else valFalse
        init_nonempty := ⟨true, rfl⟩
        step_total := fun b => ⟨b, trivial⟩
      }
      refine ⟨A, B, ⟨id, Function.surjective_id, fun _ h => h, fun _ _ _ => trivial, fun _ _ h => h⟩, ?_, ?_⟩
      · simp only [↓reduceIte, statusOf_eq_supported_iff]
        rintro τ ⟨π, ⟨h0, hstep⟩, hτ⟩ n
        have htrue : ∀ k, π k = true := by
          intro k
          induction k with
          | zero => exact h0
          | succ k ih => exact (hstep k).trans ih
        rw [hτ n]
        simp [A, htrue n, ht]
      · simp only [↓reduceIte, statusOf_eq_contradicted_iff]
        intro hsafe
        let πB : Nat → Bool := fun n => match n with | 0 => true | _ + 1 => false
        have htrB : HasTrace B (fun n => B.val (πB n)) := ⟨πB, ⟨rfl, fun _ => trivial⟩, fun _ => rfl⟩
        have h1 := hsafe _ htrB 1
        simp [B, πB, hf] at h1
    · let C : Sys := stepSys valFalse valTrue
      let D : Sys := {
        State := Bool
        init := fun b => b = false
        step := fun _ _ => True
        val := fun b => if b then valTrue else valFalse
        init_nonempty := ⟨false, rfl⟩
        step_total := fun b => ⟨b, trivial⟩
      }
      refine ⟨C, D, ⟨id, Function.surjective_id, fun _ h => h, fun _ _ _ => trivial, fun _ _ h => h⟩, ?_, ?_⟩
      · exact (statusOf_eq_supported_iff _ _ _).2 (evalShape_stepSys_terminates P ht)
      · simp only [↓reduceIte, statusOf_eq_contradicted_iff]
        intro hterm
        have htrD : HasTrace D (fun _ => valFalse) :=
          ⟨fun _ => false, ⟨rfl, fun _ => trivial⟩, fun _ => rfl⟩
        obtain ⟨n, hn⟩ := hterm _ htrD
        rw [hf] at hn
        cases hn

theorem litEntails_constFalse_constTrue :
    LitEntailsLink (constSys valFalse) (constSys valTrue) := by
  intro sh Q hQ
  cases hqf : evalVal Q valFalse with
  | true =>
    have hall := evalVal_all_true_of_valFalse hqf
    cases sh with
    | univSafety => exact fun _ _ _ => hall _
    | existWitness =>
      obtain ⟨τ, hτ⟩ := hasTrace_nonempty (constSys valTrue)
      exact ⟨τ, hτ, 0, hall _⟩
    | termination => exact fun _ _ => ⟨0, hall _⟩
    | hyperSubsetClosed => exact fun _ _ _ _ _ _ => by rw [hall, hall]
    | hyperGeneral =>
      obtain ⟨τ, hτ⟩ := hasTrace_nonempty (constSys valFalse)
      obtain ⟨_, _, _, n, hneq⟩ := hQ τ hτ
      rw [hall, hall] at hneq
      exact False.elim (hneq rfl)
  | false =>
    cases hqt : evalVal Q valTrue with
    | true =>
      have hvf := evalShape_constSys_valFalse Q hqf
      have hvt := evalShape_constSys_valTrue Q hqt
      cases sh with
      | univSafety => exact False.elim (hvf.1 hQ)
      | existWitness => exact False.elim (hvf.2.1 hQ)
      | termination => exact False.elim (hvf.2.2.1 hQ)
      | hyperSubsetClosed => exact hvt.2.2.2.1
      | hyperGeneral => exact False.elim (hvf.2.2.2.2 hQ)
    | false =>
      have hall := evalVal_all_false_of_valTrue hqt
      cases sh with
      | univSafety =>
        obtain ⟨τ, hτ⟩ := hasTrace_nonempty (constSys valFalse)
        have := hQ τ hτ 0
        rw [hall] at this
        cases this
      | existWitness =>
        rcases hQ with ⟨_, _, _, hn⟩
        rw [hall] at hn
        cases hn
      | termination =>
        obtain ⟨τ, hτ⟩ := hasTrace_nonempty (constSys valFalse)
        obtain ⟨_, hn⟩ := hQ τ hτ
        rw [hall] at hn
        cases hn
      | hyperSubsetClosed => exact fun _ _ _ _ _ _ => by rw [hall, hall]
      | hyperGeneral =>
        obtain ⟨τ, hτ⟩ := hasTrace_nonempty (constSys valFalse)
        obtain ⟨_, _, _, n, hneq⟩ := hQ τ hτ
        rw [hall, hall] at hneq
        exact False.elim (hneq rfl)

theorem evalShape_threeBranch_mixed (Q : Spec)
    (hf : evalVal Q valFalse = false) (ht : evalVal Q valTrue = true) :
    let S := threeBranchSys valFalse valTrue valFalse valFalse valTrue valFalse
    ¬ EvalShape .univSafety S Q ∧
    EvalShape .existWitness S Q ∧
    ¬ EvalShape .termination S Q ∧
    ¬ EvalShape .hyperSubsetClosed S Q ∧
    ¬ EvalShape .hyperGeneral S Q := by
  intro S
  let τ₀ : Trace := fun n => match n with | 0 => valFalse | _ + 1 => valTrue
  let τ₁ : Trace := fun _ => valFalse
  let τ₂ : Trace := fun n => match n with | 0 => valTrue | _ + 1 => valFalse
  have hτ₀ : HasTrace S τ₀ := by
    unfold S threeBranchSys; rw [hasTrace_maskedBranchSys_iff]
    exact ⟨⟨0, by omega⟩, rfl, fun _ => rfl⟩
  have hτ₁ : HasTrace S τ₁ := by
    unfold S threeBranchSys; rw [hasTrace_maskedBranchSys_iff]
    exact ⟨⟨1, by omega⟩, rfl, fun _ => rfl⟩
  have hτ₂ : HasTrace S τ₂ := by
    unfold S threeBranchSys; rw [hasTrace_maskedBranchSys_iff]
    exact ⟨⟨2, by omega⟩, rfl, fun _ => rfl⟩
  refine ⟨?_, ⟨τ₀, hτ₀, 1, ht⟩, ?_, ?_, ?_⟩
  · intro h; have := h τ₁ hτ₁ 0; simp [τ₁, hf] at this
  · intro h; obtain ⟨n, hn⟩ := h τ₁ hτ₁; simp [τ₁, hf] at hn
  · intro h; have heq := h τ₀ τ₁ hτ₀ hτ₁ rfl 1; simp [τ₀, τ₁, ht, hf] at heq
  · intro hgni
    obtain ⟨τ', h', h0, n, hneq⟩ := hgni τ₂ hτ₂
    unfold S threeBranchSys at h'
    rw [hasTrace_maskedBranchSys_iff] at h'
    rcases h' with ⟨i, hi0, hi1⟩
    by_cases hz : i.1 = 0
    · simp [τ₂, hz, hi0, ht, hf] at h0
    · by_cases ho : i.1 = 1
      · simp [τ₂, ho, hi0, ht, hf] at h0
      · have h2 : i.1 = 2 := by have := i.2; omega
        cases n with
        | zero => simp [τ₂, h2, hi0, ht] at hneq
        | succ m =>
          have hs := hi1 m
          simp [τ₂, h2, hs, hf] at hneq

theorem litEntails_mixed_to_vt_and_gni :
    let S := threeBranchSys valFalse valTrue valFalse valFalse valTrue valFalse
    LitEntailsLink S (constSys valTrue) ∧
    LitEntailsLink S (twoBranchSys valFalse valTrue valFalse valFalse) := by
  intro S
  refine ⟨?_, ?_⟩
  · intro sh Q hQ
    cases hqf : evalVal Q valFalse with
    | true =>
      have hall := evalVal_all_true_of_valFalse hqf
      cases sh with
      | univSafety => exact fun _ _ _ => hall _
      | existWitness =>
        obtain ⟨τ, hτ⟩ := hasTrace_nonempty (constSys valTrue)
        exact ⟨τ, hτ, 0, hall _⟩
      | termination => exact fun _ _ => ⟨0, hall _⟩
      | hyperSubsetClosed => exact fun _ _ _ _ _ _ => by rw [hall, hall]
      | hyperGeneral =>
        obtain ⟨τ, hτ⟩ := hasTrace_nonempty S
        obtain ⟨_, _, _, n, hneq⟩ := hQ τ hτ
        rw [hall, hall] at hneq
        exact False.elim (hneq rfl)
    | false =>
      cases hqt : evalVal Q valTrue with
      | true =>
        have hmS := evalShape_threeBranch_mixed Q hqf hqt
        have hvt := evalShape_constSys_valTrue Q hqt
        cases sh with
        | univSafety => exact False.elim (hmS.1 hQ)
        | existWitness => exact hvt.2.1
        | termination => exact False.elim (hmS.2.2.1 hQ)
        | hyperSubsetClosed => exact False.elim (hmS.2.2.2.1 hQ)
        | hyperGeneral => exact False.elim (hmS.2.2.2.2 hQ)
      | false =>
        have hall := evalVal_all_false_of_valTrue hqt
        cases sh with
        | univSafety =>
          obtain ⟨τ, hτ⟩ := hasTrace_nonempty S
          have := hQ τ hτ 0; rw [hall] at this; cases this
        | existWitness => rcases hQ with ⟨_, _, _, hn⟩; rw [hall] at hn; cases hn
        | termination =>
          obtain ⟨τ, hτ⟩ := hasTrace_nonempty S
          obtain ⟨_, hn⟩ := hQ τ hτ; rw [hall] at hn; cases hn
        | hyperSubsetClosed => exact fun _ _ _ _ _ _ => by rw [hall, hall]
        | hyperGeneral =>
          obtain ⟨τ, hτ⟩ := hasTrace_nonempty S
          obtain ⟨_, _, _, n, hneq⟩ := hQ τ hτ; rw [hall, hall] at hneq
          exact False.elim (hneq rfl)
  · intro sh Q hQ
    cases hqf : evalVal Q valFalse with
    | true =>
      have hall := evalVal_all_true_of_valFalse hqf
      cases sh with
      | univSafety => exact fun _ _ _ => hall _
      | existWitness =>
        obtain ⟨τ, hτ⟩ := hasTrace_nonempty (twoBranchSys valFalse valTrue valFalse valFalse)
        exact ⟨τ, hτ, 0, hall _⟩
      | termination => exact fun _ _ => ⟨0, hall _⟩
      | hyperSubsetClosed => exact fun _ _ _ _ _ _ => by rw [hall, hall]
      | hyperGeneral =>
        obtain ⟨τ, hτ⟩ := hasTrace_nonempty S
        obtain ⟨_, _, _, n, hneq⟩ := hQ τ hτ; rw [hall, hall] at hneq
        exact False.elim (hneq rfl)
    | false =>
      cases hqt : evalVal Q valTrue with
      | true =>
        have hmS := evalShape_threeBranch_mixed Q hqf hqt
        cases sh with
        | univSafety => exact False.elim (hmS.1 hQ)
        | existWitness =>
          let τ₀ : Trace := fun n => match n with | 0 => valFalse | _ + 1 => valTrue
          have hτ₀ : HasTrace (twoBranchSys valFalse valTrue valFalse valFalse) τ₀ := by
            unfold twoBranchSys; rw [hasTrace_maskedBranchSys_iff]
            exact ⟨⟨0, by omega⟩, rfl, fun _ => rfl⟩
          exact ⟨τ₀, hτ₀, 1, hqt⟩
        | termination => exact False.elim (hmS.2.2.1 hQ)
        | hyperSubsetClosed => exact False.elim (hmS.2.2.2.1 hQ)
        | hyperGeneral => exact False.elim (hmS.2.2.2.2 hQ)
      | false =>
        have hall := evalVal_all_false_of_valTrue hqt
        cases sh with
        | univSafety =>
          obtain ⟨τ, hτ⟩ := hasTrace_nonempty S
          have := hQ τ hτ 0; rw [hall] at this; cases this
        | existWitness => rcases hQ with ⟨_, _, _, hn⟩; rw [hall] at hn; cases hn
        | termination =>
          obtain ⟨τ, hτ⟩ := hasTrace_nonempty S
          obtain ⟨_, hn⟩ := hQ τ hτ; rw [hall] at hn; cases hn
        | hyperSubsetClosed => exact fun _ _ _ _ _ _ => by rw [hall, hall]
        | hyperGeneral =>
          obtain ⟨τ, hτ⟩ := hasTrace_nonempty S
          obtain ⟨_, _, _, n, hneq⟩ := hQ τ hτ; rw [hall, hall] at hneq
          exact False.elim (hneq rfl)

private theorem swap_flip_eq {st₁ st₂ : Status} {b : Bool}
    (hA : st₁ = if (!b) then .supported else .contradicted)
    (hB : st₂ = if (!b) then .contradicted else .supported) :
    st₂ = (if b then .supported else .contradicted) ∧
    st₁ = (if b then .contradicted else .supported) := by
  cases b <;> exact ⟨hB, hA⟩

private theorem exists_flip_bool (rel : BoundaryRel) (sh : PosShape) (P : Spec) (b : Bool)
    (hnd : NonDegen sh P) (hnot : preservesDefinite rel sh b = false) :
    ∃ src tgt : Sys, Realizes rel src tgt ∧
      statusOf src sh P = (if b then .supported else .contradicted) ∧
      statusOf tgt sh P = (if b then .contradicted else .supported) := by
  obtain ⟨hf, ht⟩ := (nonDegen_iff_evalVal_false_true sh P).1 hnd
  cases rel with
  | none =>
    rcases hnd with ⟨⟨S₁, h₁⟩, ⟨S₂, h₂⟩⟩
    cases b
    · exact ⟨S₂, S₁, trivial, h₂, h₁⟩
    · exact ⟨S₁, S₂, trivial, h₁, h₂⟩
  | embed d =>
    cases d with
    | m2s => exact embedM2S_flip_witness sh P b hf ht hnot
    | s2m =>
      have hnot' : preservesDefinite (.embed .m2s) sh (!b) = false := by
        revert hnot; cases sh <;> cases b <;> decide
      obtain ⟨A, B, hemb, hA, hB⟩ := embedM2S_flip_witness sh P (!b) hf ht hnot'
      have hs := swap_flip_eq hA hB
      exact ⟨B, A, hemb, hs.1, hs.2⟩
  | lockStepSim d =>
    cases d with
    | m2s =>
      have hnot' : preservesDefinite (.embed .m2s) sh b = false := by
        revert hnot; cases sh <;> cases b <;> decide
      obtain ⟨A, B, hemb, hA, hB⟩ := embedM2S_flip_witness sh P b hf ht hnot'
      exact ⟨A, B, isEmbedFrom_lockStepSimFrom hemb, hA, hB⟩
    | s2m =>
      have hnot' : preservesDefinite (.embed .m2s) sh (!b) = false := by
        revert hnot; cases sh <;> cases b <;> decide
      obtain ⟨A, B, hemb, hA, hB⟩ := embedM2S_flip_witness sh P (!b) hf ht hnot'
      have hs := swap_flip_eq hA hB
      exact ⟨B, A, isEmbedFrom_lockStepSimFrom hemb, hs.1, hs.2⟩
  | traceRefine d =>
    cases d with
    | m2s =>
      have hnot' : preservesDefinite (.embed .m2s) sh b = false := by
        revert hnot; cases sh <;> cases b <;> decide
      obtain ⟨A, B, hemb, hA, hB⟩ := embedM2S_flip_witness sh P b hf ht hnot'
      exact ⟨A, B, lockStepSimFrom_traceIncl (isEmbedFrom_lockStepSimFrom hemb), hA, hB⟩
    | s2m =>
      have hnot' : preservesDefinite (.embed .m2s) sh (!b) = false := by
        revert hnot; cases sh <;> cases b <;> decide
      obtain ⟨A, B, hemb, hA, hB⟩ := embedM2S_flip_witness sh P (!b) hf ht hnot'
      have hs := swap_flip_eq hA hB
      exact ⟨B, A, lockStepSimFrom_traceIncl (isEmbedFrom_lockStepSimFrom hemb), hs.1, hs.2⟩
  | cospanCaptureLower =>
    have hnot' : preservesDefinite (.embed .m2s) sh (!b) = false := by
      revert hnot; cases sh <;> cases b <;> decide
    obtain ⟨A, B, hemb, hA, hB⟩ := embedM2S_flip_witness sh P (!b) hf ht hnot'
    have hcs : CospanSysWitness B A :=
      (cospanSysWitness_iff_traceIncl B A).2
        (lockStepSimFrom_traceIncl (isEmbedFrom_lockStepSimFrom hemb))
    have hs := swap_flip_eq hA hB
    exact ⟨B, A, hcs, hs.1, hs.2⟩
  | wfStutterSim d =>
    cases d with
    | m2s =>
      by_cases hspec : sh = .hyperSubsetClosed ∧ b = false
      · rcases hspec with ⟨rfl, rfl⟩
        have hfs := evalShape_finiteStutter_not_subClosed P hf ht
        exact ⟨finiteStutterSys valFalse valTrue, stepSys valFalse valTrue,
          wfStutter_finiteStutter_to_step,
          (statusOf_eq_contradicted_iff _ _ _).2 hfs.1,
          (statusOf_eq_supported_iff _ _ _).2 hfs.2⟩
      · have hnot' : preservesDefinite (.embed .m2s) sh b = false := by
          revert hnot hspec; cases sh <;> cases b <;> decide
        obtain ⟨A, B, hemb, hA, hB⟩ := embedM2S_flip_witness sh P b hf ht hnot'
        exact ⟨A, B, lockStepSimFrom_wfStutterSimFrom (isEmbedFrom_lockStepSimFrom hemb), hA, hB⟩
    | s2m =>
      by_cases hspec : sh = .hyperSubsetClosed ∧ b = true
      · rcases hspec with ⟨rfl, rfl⟩
        have hfs := evalShape_finiteStutter_not_subClosed P hf ht
        exact ⟨stepSys valFalse valTrue, finiteStutterSys valFalse valTrue,
          wfStutter_finiteStutter_to_step,
          (statusOf_eq_supported_iff _ _ _).2 hfs.2,
          (statusOf_eq_contradicted_iff _ _ _).2 hfs.1⟩
      · have hnot' : preservesDefinite (.embed .m2s) sh (!b) = false := by
          revert hnot hspec; cases sh <;> cases b <;> decide
        obtain ⟨A, B, hemb, hA, hB⟩ := embedM2S_flip_witness sh P (!b) hf ht hnot'
        have hs := swap_flip_eq hA hB
        exact ⟨B, A, lockStepSimFrom_wfStutterSimFrom (isEmbedFrom_lockStepSimFrom hemb), hs.1, hs.2⟩
  | stutterSim d =>
    cases d with
    | m2s =>
      by_cases hterm : sh = .termination ∧ b = false
      · rcases hterm with ⟨rfl, rfl⟩
        exact ⟨constSys valFalse, stepSys valFalse valTrue, stutter_constFalse_to_step,
          (statusOf_eq_contradicted_iff _ _ _).2 (evalShape_constSys_valFalse P hf).2.2.1,
          (statusOf_eq_supported_iff _ _ _).2 (evalShape_stepSys_terminates P ht)⟩
      · by_cases hspec : sh = .hyperSubsetClosed ∧ b = false
        · rcases hspec with ⟨rfl, rfl⟩
          have hfs := evalShape_finiteStutter_not_subClosed P hf ht
          exact ⟨finiteStutterSys valFalse valTrue, stepSys valFalse valTrue,
            wfStutterSimFrom_stutterSimFrom wfStutter_finiteStutter_to_step,
            (statusOf_eq_contradicted_iff _ _ _).2 hfs.1,
            (statusOf_eq_supported_iff _ _ _).2 hfs.2⟩
        · have hnot' : preservesDefinite (.embed .m2s) sh b = false := by
            revert hnot hterm hspec; cases sh <;> cases b <;> decide
          obtain ⟨A, B, hemb, hA, hB⟩ := embedM2S_flip_witness sh P b hf ht hnot'
          exact ⟨A, B,
            wfStutterSimFrom_stutterSimFrom (lockStepSimFrom_wfStutterSimFrom (isEmbedFrom_lockStepSimFrom hemb)),
            hA, hB⟩
    | s2m =>
      by_cases hterm : sh = .termination ∧ b = true
      · rcases hterm with ⟨rfl, rfl⟩
        exact ⟨stepSys valFalse valTrue, constSys valFalse, stutter_constFalse_to_step,
          (statusOf_eq_supported_iff _ _ _).2 (evalShape_stepSys_terminates P ht),
          (statusOf_eq_contradicted_iff _ _ _).2 (evalShape_constSys_valFalse P hf).2.2.1⟩
      · by_cases hspec : sh = .hyperSubsetClosed ∧ b = true
        · rcases hspec with ⟨rfl, rfl⟩
          have hfs := evalShape_finiteStutter_not_subClosed P hf ht
          exact ⟨stepSys valFalse valTrue, finiteStutterSys valFalse valTrue,
            wfStutterSimFrom_stutterSimFrom wfStutter_finiteStutter_to_step,
            (statusOf_eq_supported_iff _ _ _).2 hfs.2,
            (statusOf_eq_contradicted_iff _ _ _).2 hfs.1⟩
        · have hnot' : preservesDefinite (.embed .m2s) sh (!b) = false := by
            revert hnot hterm hspec; cases sh <;> cases b <;> decide
          obtain ⟨A, B, hemb, hA, hB⟩ := embedM2S_flip_witness sh P (!b) hf ht hnot'
          have hs := swap_flip_eq hA hB
          exact ⟨B, A,
            wfStutterSimFrom_stutterSimFrom (lockStepSimFrom_wfStutterSimFrom (isEmbedFrom_lockStepSimFrom hemb)),
            hs.1, hs.2⟩
  | hom d =>
    have hvt := evalShape_constSys_valTrue P ht
    have hvf := evalShape_constSys_valFalse P hf
    have hgni := evalShape_twoBranch_gni P hf ht
    cases d with
    | m2s =>
      by_cases hextra : b = false ∧ (sh = .univSafety ∨ sh = .termination ∨ sh = .hyperSubsetClosed)
      · rcases hextra with ⟨rfl, rfl | rfl | rfl⟩
        · exact ⟨constSys valFalse, constSys valTrue, isHomFrom_to_constValTrue _,
            (statusOf_eq_contradicted_iff _ _ _).2 hvf.1, (statusOf_eq_supported_iff _ _ _).2 hvt.1⟩
        · exact ⟨constSys valFalse, constSys valTrue, isHomFrom_to_constValTrue _,
            (statusOf_eq_contradicted_iff _ _ _).2 hvf.2.2.1,
            (statusOf_eq_supported_iff _ _ _).2 hvt.2.2.1⟩
        · exact ⟨twoBranchSys valFalse valTrue valFalse valFalse, constSys valTrue,
            isHomFrom_to_constValTrue _,
            (statusOf_eq_contradicted_iff _ _ _).2 hgni.1,
            (statusOf_eq_supported_iff _ _ _).2 hvt.2.2.2.1⟩
      · have hnot' : preservesDefinite (.embed .m2s) sh b = false := by
          revert hnot hextra; cases sh <;> cases b <;> decide
        obtain ⟨A, B, hemb, hA, hB⟩ := embedM2S_flip_witness sh P b hf ht hnot'
        exact ⟨A, B, isEmbedFrom_isHomFrom hemb, hA, hB⟩
    | s2m =>
      by_cases hextra : b = true ∧ (sh = .univSafety ∨ sh = .termination ∨ sh = .hyperSubsetClosed)
      · rcases hextra with ⟨rfl, rfl | rfl | rfl⟩
        · exact ⟨constSys valTrue, constSys valFalse, isHomFrom_to_constValTrue _,
            (statusOf_eq_supported_iff _ _ _).2 hvt.1, (statusOf_eq_contradicted_iff _ _ _).2 hvf.1⟩
        · exact ⟨constSys valTrue, constSys valFalse, isHomFrom_to_constValTrue _,
            (statusOf_eq_supported_iff _ _ _).2 hvt.2.2.1,
            (statusOf_eq_contradicted_iff _ _ _).2 hvf.2.2.1⟩
        · exact ⟨constSys valTrue, twoBranchSys valFalse valTrue valFalse valFalse,
            isHomFrom_to_constValTrue _,
            (statusOf_eq_supported_iff _ _ _).2 hvt.2.2.2.1,
            (statusOf_eq_contradicted_iff _ _ _).2 hgni.1⟩
      · have hnot' : preservesDefinite (.embed .m2s) sh (!b) = false := by
          revert hnot hextra; cases sh <;> cases b <;> decide
        obtain ⟨A, B, hemb, hA, hB⟩ := embedM2S_flip_witness sh P (!b) hf ht hnot'
        have hs := swap_flip_eq hA hB
        exact ⟨B, A, isEmbedFrom_isHomFrom hemb, hs.1, hs.2⟩
  | surjHom d =>
    cases d with
    | m2s => exact surjHomM2S_flip_witness sh P b hf ht hnot
    | s2m =>
      have hnot' : preservesDefinite (.surjHom .m2s) sh (!b) = false := by
        revert hnot; cases sh <;> cases b <;> decide
      obtain ⟨A, B, hsurj, hA, hB⟩ := surjHomM2S_flip_witness sh P (!b) hf ht hnot'
      have hs := swap_flip_eq hA hB
      exact ⟨B, A, hsurj, hs.1, hs.2⟩
  | posBoundedMorph d =>
    cases d with
    | m2s => exact posBoundedMorphM2S_flip_witness sh P b hf ht hnot
    | s2m =>
      have hnot' : preservesDefinite (.posBoundedMorph .m2s) sh (!b) = false := by
        revert hnot; cases sh <;> cases b <;> decide
      obtain ⟨A, B, hbm, hA, hB⟩ := posBoundedMorphM2S_flip_witness sh P (!b) hf ht hnot'
      have hs := swap_flip_eq hA hB
      exact ⟨B, A, hbm, hs.1, hs.2⟩
  | certFaithfulSoundPinned => exact False.elim (by revert hnot; cases sh <;> cases b <;> decide)
  | termRoundTrip => exact False.elim (by revert hnot; cases sh <;> cases b <;> decide)
  | litEntails =>
    have hb : b = false := by revert hnot; cases sh <;> cases b <;> decide
    subst hb
    have hvt := evalShape_constSys_valTrue P ht
    have hvf := evalShape_constSys_valFalse P hf
    have hmS := evalShape_threeBranch_mixed P hf ht
    have hgni := evalShape_twoBranch_gni P hf ht
    have hlinks := litEntails_mixed_to_vt_and_gni
    cases sh with
    | univSafety =>
      exact ⟨constSys valFalse, constSys valTrue, litEntails_constFalse_constTrue,
        (statusOf_eq_contradicted_iff _ _ _).2 hvf.1, (statusOf_eq_supported_iff _ _ _).2 hvt.1⟩
    | existWitness =>
      exact ⟨constSys valFalse, constSys valTrue, litEntails_constFalse_constTrue,
        (statusOf_eq_contradicted_iff _ _ _).2 hvf.2.1, (statusOf_eq_supported_iff _ _ _).2 hvt.2.1⟩
    | termination =>
      exact ⟨constSys valFalse, constSys valTrue, litEntails_constFalse_constTrue,
        (statusOf_eq_contradicted_iff _ _ _).2 hvf.2.2.1,
        (statusOf_eq_supported_iff _ _ _).2 hvt.2.2.1⟩
    | hyperSubsetClosed =>
      exact ⟨_, constSys valTrue, hlinks.1,
        (statusOf_eq_contradicted_iff _ _ _).2 hmS.2.2.2.1,
        (statusOf_eq_supported_iff _ _ _).2 hvt.2.2.2.1⟩
    | hyperGeneral =>
      exact ⟨_, twoBranchSys valFalse valTrue valFalse valFalse, hlinks.2,
        (statusOf_eq_contradicted_iff _ _ _).2 hmS.2.2.2.2,
        (statusOf_eq_supported_iff _ _ _).2 hgni.2⟩

/-- Core single-flip witness: whenever `P` is non-degenerate, `st` is definite, and
`transfer rel sh st = .undetermined`, some realization of `rel` flips `st` to `st.flip`. -/
theorem exists_flip_realization (rel : BoundaryRel) (sh : PosShape) (P : Spec) (st : Status)
    (hnd : NonDegen sh P) (hdef : st.Definite) (hund : transfer rel sh st = .undetermined) :
    ∃ src tgt : Sys, Realizes rel src tgt ∧
      statusOf src sh P = st ∧ statusOf tgt sh P = st.flip := by
  rcases hdef with rfl | rfl
  · have hnot : preservesDefinite rel sh true = false := by
      unfold transfer at hund
      cases h : preservesDefinite rel sh true <;> simp_all
    exact exists_flip_bool rel sh P true hnd hnot
  · have hnot : preservesDefinite rel sh false = false := by
      unfold transfer at hund
      cases h : preservesDefinite rel sh false <;> simp_all
    exact exists_flip_bool rel sh P false hnd hnot

/-- Semantic Kripke separation on sub-diagonal entries `j < i` of `sepMatrix_upperTriangular`:
every sub-diagonal cell `(i, j)` admits a concrete `Realizes (sepRel i)` pair flipping `.supported` to `.contradicted`. -/
theorem sepMatrix_subdiagonal_countermodels (i j : Fin 5) (hlt : j.1 < i.1) :
    ∃ src tgt : Sys,
      Realizes (sepRel i) src tgt ∧
      statusOf src (sepShape j) specAtom0 = .supported ∧
      statusOf tgt (sepShape j) specAtom0 = .contradicted := by
  have hund : transfer (sepRel i) (sepShape j) .supported = .undetermined :=
    sepMatrix_upperTriangular.2 i j hlt
  have hnd : NonDegen (sepShape j) specAtom0 :=
    (nonDegen_iff_evalVal_false_true (sepShape j) specAtom0).2 ⟨rfl, rfl⟩
  exact exists_flip_realization (sepRel i) (sepShape j) specAtom0 .supported hnd (Or.inl rfl) hund

/-- Tightness counterexample for `hlt : j.1 < i.1` in `sepMatrix_subdiagonal_countermodels`:
on diagonal cell `i = j = 0`, `transfer_sound` preserves `.supported` so no pair flips to `.contradicted`. -/
theorem cex_sepMatrix_subdiagonal_without_lt :
    let i : Fin 5 := ⟨0, by omega⟩
    ¬ (i.1 < i.1) ∧
    ¬ ∃ src tgt : Sys,
        Realizes (sepRel i) src tgt ∧
        statusOf src (sepShape i) specAtom0 = .supported ∧
        statusOf tgt (sepShape i) specAtom0 = .contradicted := by
  intro i
  refine ⟨by omega, ?_⟩
  rintro ⟨src, tgt, hrel, hsrc, htgt⟩
  have hle := transfer_sound (sepRel i) (sepShape i) specAtom0 src tgt hrel
  rw [hsrc, sepMatrix_upperTriangular.1 i, htgt] at hle
  exact absurd hle (by decide)

/-- Sharpness of `.undetermined`: every `.undetermined` cell of `transfer` on a non-degenerate
specification `P` and definite source verdict `st` admits two realizations with source verdict `st`
and opposite target verdicts `.supported` and `.contradicted`. -/
theorem transfer_undetermined_sharp (rel : BoundaryRel) (sh : PosShape) (P : Spec) (st : Status)
    (hnd : NonDegen sh P) (hdef : st.Definite) (hund : transfer rel sh st = .undetermined) :
    ∃ src₁ tgt₁ src₂ tgt₂ : Sys,
      Realizes rel src₁ tgt₁ ∧
      Realizes rel src₂ tgt₂ ∧
      statusOf src₁ sh P = st ∧
      statusOf src₂ sh P = st ∧
      statusOf tgt₁ sh P = .supported ∧
      statusOf tgt₂ sh P = .contradicted := by
  obtain ⟨src, tgt, hrel, hsrc, htgt⟩ := exists_flip_realization rel sh P st hnd hdef hund
  rcases hdef with rfl | rfl
  · exact ⟨src, src, src, tgt, realizes_refl rel src, hrel, hsrc, hsrc, hsrc, htgt⟩
  · exact ⟨src, tgt, src, src, hrel, realizes_refl rel src, hsrc, hsrc, htgt, hsrc⟩

/-- Tightness counterexample for `hnd : NonDegen sh P` in `transfer_undetermined_sharp`. -/
theorem cex_sharp_without_nonDegen :
    Status.Definite .supported ∧
    transfer .none .univSafety .supported = .undetermined ∧
    ¬ ∃ src₁ tgt₁ src₂ tgt₂ : Sys,
        Realizes .none src₁ tgt₁ ∧
        Realizes .none src₂ tgt₂ ∧
        statusOf src₁ .univSafety specConstTrue = .supported ∧
        statusOf src₂ .univSafety specConstTrue = .supported ∧
        statusOf tgt₁ .univSafety specConstTrue = .supported ∧
        statusOf tgt₂ .univSafety specConstTrue = .contradicted := by
  refine ⟨Or.inl rfl, rfl, ?_⟩
  rintro ⟨_, _, _, tgt₂, _, _, _, _, _, hbad⟩
  rw [statusOf_eq_contradicted_iff] at hbad
  exact hbad (fun _ _ _ => rfl)

/-- Tightness counterexample for `hdef : st.Definite` in `transfer_undetermined_sharp`. -/
theorem cex_sharp_without_definite :
    NonDegen .univSafety specAtom0 ∧
    transfer .none .univSafety .undetermined = .undetermined ∧
    ¬ ∃ src₁ tgt₁ src₂ tgt₂ : Sys,
        Realizes .none src₁ tgt₁ ∧
        Realizes .none src₂ tgt₂ ∧
        statusOf src₁ .univSafety specAtom0 = .undetermined ∧
        statusOf src₂ .univSafety specAtom0 = .undetermined ∧
        statusOf tgt₁ .univSafety specAtom0 = .supported ∧
        statusOf tgt₂ .univSafety specAtom0 = .contradicted := by
  refine ⟨nonDegen_pos, rfl, ?_⟩
  rintro ⟨src₁, _, _, _, _, _, hsrc₁, _, _, _⟩
  exact statusOf_ne_undetermined src₁ .univSafety specAtom0 hsrc₁

/-- Tightness counterexample for `hund : transfer rel sh st = .undetermined` in `transfer_undetermined_sharp`. -/
theorem cex_sharp_without_undetermined :
    NonDegen .univSafety specAtom0 ∧
    Status.Definite .supported ∧
    ¬ ∃ src₁ tgt₁ src₂ tgt₂ : Sys,
        Realizes (.lockStepSim .s2m) src₁ tgt₁ ∧
        Realizes (.lockStepSim .s2m) src₂ tgt₂ ∧
        statusOf src₁ .univSafety specAtom0 = .supported ∧
        statusOf src₂ .univSafety specAtom0 = .supported ∧
        statusOf tgt₁ .univSafety specAtom0 = .supported ∧
        statusOf tgt₂ .univSafety specAtom0 = .contradicted := by
  refine ⟨nonDegen_pos, Or.inl rfl, ?_⟩
  rintro ⟨_, _, src₂, tgt₂, _, hrel₂, _, hsrc₂, _, htgt₂⟩
  have hle := transfer_sound (.lockStepSim .s2m) .univSafety specAtom0 src₂ tgt₂ hrel₂
  rw [hsrc₂, htgt₂] at hle
  exact absurd hle (by decide)

/-- Non-vacuity witness for `transfer_undetermined_sharp`. -/
theorem nonvacuity_transfer_sharp :
    NonDegen .termination specAtom0 ∧
    Status.Definite .supported ∧
    transfer (.stutterSim .s2m) .termination .supported = .undetermined :=
  ⟨(nonDegen_iff_evalVal_false_true .termination specAtom0).2 ⟨rfl, rfl⟩, Or.inl rfl, rfl⟩

/-- Boundary witness explaining why `.litEntails` `.contradicted` sharpness relies on `Spec` being
positive-only: if entailment quantified over arbitrary negation-closed predicates `Valuation → Bool`,
dualizing `p` with `fun v => !p v` would force universal entailment to preserve `.contradicted`
on both `.univSafety` and `.existWitness`. -/
theorem negation_closed_entailment_preserves_contradicted (src tgt : Sys)
    (hlit : ∀ (p : Valuation → Bool),
      ((∀ τ, HasTrace src τ → ∀ n, p (τ n) = true) → (∀ τ, HasTrace tgt τ → ∀ n, p (τ n) = true)) ∧
      ((∃ τ, HasTrace src τ ∧ ∃ n, p (τ n) = true) → (∃ τ, HasTrace tgt τ ∧ ∃ n, p (τ n) = true)))
    (p : Valuation → Bool) :
    (¬ (∀ τ, HasTrace src τ → ∀ n, p (τ n) = true) →
      ¬ (∀ τ, HasTrace tgt τ → ∀ n, p (τ n) = true)) ∧
    (¬ (∃ τ, HasTrace src τ ∧ ∃ n, p (τ n) = true) →
      ¬ (∃ τ, HasTrace tgt τ ∧ ∃ n, p (τ n) = true)) := by
  refine ⟨?_, ?_⟩
  · intro hnotSrc hTgt
    apply hnotSrc
    refine Classical.byContradiction fun hne => ?_
    have hexSrc : ∃ τ, HasTrace src τ ∧ ∃ n, (!p (τ n)) = true := by
      refine Classical.byContradiction fun hno => hne fun τ hτ n => ?_
      cases hp : p (τ n)
      · exact False.elim (hno ⟨τ, hτ, n, by simp [hp]⟩)
      · rfl
    obtain ⟨τ, hτ, n, hn⟩ := (hlit (fun v => !p v)).2 hexSrc
    have ht := hTgt τ hτ n
    simp [ht] at hn
  · intro hnotSrc ⟨τ, hτ, n, hn⟩
    have hSafeSrc : ∀ τ', HasTrace src τ' → ∀ m, (!p (τ' m)) = true := by
      intro τ' hτ' m
      cases hp : p (τ' m)
      · rfl
      · exact False.elim (hnotSrc ⟨τ', hτ', m, hp⟩)
    have hSafeTgt := (hlit (fun v => !p v)).1 hSafeSrc τ hτ n
    simp [hn] at hSafeTgt

/-! ### Paired Claim-Tuple (`PosShape × PosShape`) Soundness & Converse Loss -/

/-- Paired soundness for directional claim tuples `(sh.1, sh.2)` evaluated at `(P₁, P₂)`. -/
theorem transferIff_sound (rel : BoundaryRel) (sh : PosShape × PosShape) (P₁ P₂ : Spec)
    (src tgt : Sys) (hrel : Realizes rel src tgt) :
    let out := transferIff rel sh (statusOf src sh.1 P₁, statusOf src sh.2 P₂)
    out.1.le (statusOf tgt sh.1 P₁) ∧ out.2.le (statusOf tgt sh.2 P₂) :=
  ⟨transfer_sound rel sh.1 P₁ src tgt hrel, transfer_sound rel sh.2 P₂ src tgt hrel⟩

/-- Dedicated tightness counterexample for `hrel : Realizes rel src tgt` in `transferIff_sound`. -/
theorem cex_transferIff_sound_without_realizes :
    let src := constSys valTrue
    let tgt := constSys valFalse
    let out := transferIff .termRoundTrip (.univSafety, .existWitness)
      (statusOf src .univSafety specAtom0, statusOf src .existWitness specAtom1)
    ¬ (out.1.le (statusOf tgt .univSafety specAtom0) ∧
       out.2.le (statusOf tgt .existWitness specAtom1)) := by
  intro src tgt out hboth
  exact cex_transfer_sound_without_realizes hboth.1

/-- Exact classification of the four `BoundaryRel` constructors preserving `(.supported, .supported)`
across a paired `(.univSafety, .existWitness)` claim tuple. -/
theorem transferIff_univSafety_existWitness_supported_iff (rel : BoundaryRel) :
    transferIff rel (.univSafety, .existWitness) (.supported, .supported) =
      (.supported, .supported) ↔
      rel = .posBoundedMorph .m2s ∨ rel = .certFaithfulSoundPinned ∨
      rel = .termRoundTrip ∨ rel = .litEntails := by
  cases rel <;> first | decide | (rename_i d; cases d <;> decide)

/-- Matched-specification witness that `.lockStepSim .s2m` preserves `.univSafety` at `specAtom0`
while losing `.existWitness` at the SAME second specification `specAtom1` (`Spec.atom 1`) across
refinement from `src` to `tgt`. -/
theorem cex_iff_converse_unlicensed :
    ∃ src tgt : Sys,
      Realizes (.lockStepSim .s2m) src tgt ∧
      statusOf src .univSafety specAtom0 = .supported ∧
      statusOf src .existWitness specAtom1 = .supported ∧
      transferIff (.lockStepSim .s2m) (.univSafety, .existWitness) (.supported, .supported) =
        (.supported, .undetermined) ∧
      statusOf tgt .univSafety specAtom0 = .supported ∧
      statusOf tgt .existWitness specAtom1 = .contradicted := by
  let vA : Valuation := fun a => a == 0 || a == 1
  let vB : Valuation := fun a => a == 0
  let src := twoBranchSys vA vA vB vB
  let tgt := oneBranchSys vB vB
  have hrel : Realizes (.lockStepSim .s2m) src tgt := by
    have hemb : IsEmbedFrom tgt src := by
      refine ⟨fun p => (⟨1, by omega⟩, p.2), ?_, ?_, ?_, ?_⟩
      · rintro ⟨⟨i₁, hi₁⟩, s₁⟩ ⟨⟨i₂, hi₂⟩, s₂⟩ h
        have hi : i₁ = i₂ := by omega
        cases hi; cases h; rfl
      · intro _; exact Iff.rfl
      · rintro ⟨⟨i₁, hi₁⟩, s₁⟩ ⟨⟨i₂, hi₂⟩, s₂⟩
        have hi : i₁ = i₂ := by omega
        subst hi; simp [tgt, src, oneBranchSys, twoBranchSys, maskedBranchSys]
      · rintro ⟨⟨i, hi⟩, s⟩
        simp [tgt, src, oneBranchSys, twoBranchSys, maskedBranchSys]
    exact isEmbedFrom_lockStepSimFrom hemb
  refine ⟨src, tgt, hrel, ?_, ?_, rfl, ?_, ?_⟩
  · rw [statusOf_eq_supported_iff]
    intro τ hτ n
    unfold src twoBranchSys at hτ
    rw [hasTrace_maskedBranchSys_iff] at hτ
    rcases hτ with ⟨i, h0, h1⟩
    by_cases hz : i.1 = 0
    · cases n <;> simp [h0, h1, hz, evalVal, specAtom0, vA]
    · have ho : i.1 = 1 := by have := i.2; omega
      cases n <;> simp [h0, h1, ho, evalVal, specAtom0, vB]
  · rw [statusOf_eq_supported_iff]
    have htr : HasTrace src (fun _ => vA) := by
      unfold src twoBranchSys; rw [hasTrace_maskedBranchSys_iff]
      exact ⟨⟨0, by omega⟩, rfl, fun _ => rfl⟩
    exact ⟨fun _ => vA, htr, 0, by simp [evalVal, specAtom1, vA]⟩
  · rw [statusOf_eq_supported_iff]
    intro τ hτ n
    rcases (evalShape_oneBranch vB vB τ).1 hτ with ⟨h0, h1⟩
    cases n <;> simp [h0, h1, evalVal, specAtom0, vB]
  · rw [statusOf_eq_contradicted_iff]
    rintro ⟨τ, hτ, n, hn⟩
    rcases (evalShape_oneBranch vB vB τ).1 hτ with ⟨h0, h1⟩
    cases n <;> simp [h0, h1, evalVal, specAtom1, vB] at hn

end Toy.BoundaryLicensing
