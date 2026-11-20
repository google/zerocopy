import ToyViews.EndSafe

/-!
# Result 3: closed views — completed nested scopes are transparent to outer return authority
# Result 4: necessity (and non-necessity) of the closed-views conditions

`ClosedViews s₀ s₁` relates the state before a (possibly nested) scope to the state after it:
views that already existed in `s₀` keep their *return shape* — parent link, activity flag, and
covered addresses (domain) — and every view created after `s₀` is inactive in `s₁`. Everything else
about old views is unrestricted: cell contents (bytes), cell permission forms (depths, loans), and
also the view *mode* (an old view may change between exclusive and shared,
`Ex.closedViews_ignores_modes`). `ClosedViews` is only the return-authority part of a scope
contract: it does not preserve `LoanTreeInv` (`Ex.closedViews_does_not_preserve_loanTreeInv`), nor
the parent-cell shape that the raw end of an outer view needs
(`Ex.closedViews_does_not_preserve_end_enabledness`), and this model has no allocation lifetime or
deallocation at all.
-/

namespace Toy.Views

/-- Views existing in `s₀` still exist in `s₁` with the same parent link. -/
def ParentsStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.parent = (s₀.view? v).map View.parent

/-- Views existing in `s₀` still exist in `s₁` with the same activity flag. -/
def ActivityStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.active = (s₀.view? v).map View.active

/-- Views existing in `s₀` still exist in `s₁` and cover the same addresses. -/
def DomainsStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.domain = (s₀.view? v).map View.domain

/-- Every view created after `s₀` is inactive in `s₁`. -/
def NewViewsInactive (s₀ s₁ : State) : Prop :=
  ∀ v < s₁.size, s₀.size ≤ v → s₁.isActive v = false

/-- **Closed views**: the four conditions above. -/
structure ClosedViews (s₀ s₁ : State) : Prop where
  parents : ParentsStable s₀ s₁
  activity : ActivityStable s₀ s₁
  domains : DomainsStable s₀ s₁
  fresh : NewViewsInactive s₀ s₁

instance (s₀ s₁ : State) : Decidable (ParentsStable s₀ s₁) := by
  unfold ParentsStable; infer_instance
instance (s₀ s₁ : State) : Decidable (ActivityStable s₀ s₁) := by
  unfold ActivityStable; infer_instance
instance (s₀ s₁ : State) : Decidable (DomainsStable s₀ s₁) := by
  unfold DomainsStable; infer_instance
instance (s₀ s₁ : State) : Decidable (NewViewsInactive s₀ s₁) := by
  unfold NewViewsInactive; infer_instance
instance (s₀ s₁ : State) : Decidable (ClosedViews s₀ s₁) :=
  decidable_of_iff (ParentsStable s₀ s₁ ∧ ActivityStable s₀ s₁ ∧ DomainsStable s₀ s₁ ∧
      NewViewsInactive s₀ s₁)
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

/-- Old views persist, so the view count never shrinks (the analogue of a monotone fresh-id
counter is derivable here). -/
theorem ParentsStable.size_le {s₀ s₁ : State} (h : ParentsStable s₀ s₁) : s₀.size ≤ s₁.size := by
  rcases Nat.eq_zero_or_pos s₀.size with h0 | hpos
  · omega
  · have hv : s₀.size - 1 < s₀.size := by omega
    have e := h _ hv
    have hs : (s₀.view? (s₀.size - 1)).isSome = true := by
      unfold State.view?; unfold State.size at hv ⊢; simp [hv]
    cases h1 : s₁.view? (s₀.size - 1) with
    | none =>
      rw [h1] at e
      cases h2 : s₀.view? (s₀.size - 1) with
      | none => rw [h2] at hs; simp at hs
      | some _ => rw [h2] at e; simp at e
    | some _ =>
      have := State.lt_size_of_view?_eq_some h1
      exact Nat.le_of_pred_lt this

/-- With parents stable, `ParentLt` after the scope gives `ParentsExist` before it. -/
theorem parentsExist_of_parentLt_of_parentsStable {s₀ s₁ : State} (hlt : ParentLt s₁)
    (hps : ParentsStable s₀ s₁) : ParentsExist s₀ := by
  intro v hv p hp
  have e := hps v hv
  unfold State.parentOf at hp
  cases h0 : s₀.view? v with
  | none => rw [h0] at hp; simp at hp
  | some vw₀ =>
    rw [h0] at hp e
    simp only [Option.bind_some] at hp
    cases h1 : s₁.view? v with
    | none => rw [h1] at e; simp at e
    | some vw₁ =>
      rw [h1] at e
      simp only [Option.map_some, Option.some.injEq] at e
      have hv1 := State.lt_size_of_view?_eq_some h1
      have := hlt v hv1 p (by unfold State.parentOf; rw [h1]; simp [e, hp])
      exact Nat.lt_trans this hv

/-! ## Result 3 (main statements) -/

/-- **R3a (preorder, reflexivity).** `ClosedViews` is reflexive. -/
theorem closedViews_refl (s : State) : ClosedViews s s :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ hv hge => absurd hv (Nat.not_lt_of_ge hge)⟩

/-- **R3a (preorder, transitivity).** `ClosedViews` is transitive: consecutive completed scopes
compose. -/
theorem closedViews_trans {s₀ s₁ s₂ : State} (h₁ : ClosedViews s₀ s₁) (h₂ : ClosedViews s₁ s₂) :
    ClosedViews s₀ s₂ := by
  have hle : s₀.size ≤ s₁.size := h₁.parents.size_le
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    exact (h₂.parents v (Nat.lt_of_lt_of_le hv hle)).trans (h₁.parents v hv)
  · intro v hv
    exact (h₂.activity v (Nat.lt_of_lt_of_le hv hle)).trans (h₁.activity v hv)
  · intro v hv
    exact (h₂.domains v (Nat.lt_of_lt_of_le hv hle)).trans (h₁.domains v hv)
  · intro v hv hge
    rcases Nat.lt_or_ge v s₁.size with hv1 | hv1
    · have hact0 := h₁.fresh v hv1 hge
      have heq := h₂.activity v hv1
      unfold State.isActive at hact0 ⊢
      rw [heq]; exact hact0
    · exact h₂.fresh v hv hv1

/-- **R3c (main).** If parent links in `s₀` point to existing views, view `v` has return authority
in `s₀`, and `ClosedViews s₀ s₁`, then `v` has return authority in `s₁`. (For `v ≥ s₀.size` the
hypothesis `ReturnAuthority s₀ v` holds vacuously and `v` cannot be ended in `s₁`:
`returnAuthority_vacuous_of_ge_size`, `endRaw_eq_none_of_closedViews_of_ge_size`.) -/
theorem returnAuthority_of_closedViews_of_parentsExist {s₀ s₁ : State} {v : ViewId}
    (hpe : ParentsExist s₀) (hauth : ReturnAuthority s₀ v) (hcv : ClosedViews s₀ s₁) :
    ReturnAuthority s₁ v := by
  have hcov_eq : ∀ u < s₀.size, ∀ a, s₁.covers u a = s₀.covers u a := by
    intro u hu a
    have hd := hcv.domains u hu
    obtain ⟨vw₀, hu0⟩ := ProofLemmas.view?_isSome_of_lt_size hu
    rw [hu0] at hd
    cases hu1 : s₁.view? u with
    | none => rw [hu1] at hd; simp at hd
    | some vw₁ =>
      rw [hu1] at hd
      simp only [Option.map_some, Option.some.injEq] at hd
      unfold State.covers State.cell?
      rw [hu1, hu0]
      simp only [Option.bind_some]
      apply Bool.eq_iff_iff.mpr
      rw [← mem_domain_iff, ← mem_domain_iff, hd]
  have hparent_eq : ∀ d < s₀.size, s₁.parentOf d = s₀.parentOf d := by
    intro d hd0
    have hps := hcv.parents d hd0
    obtain ⟨vw₀, h0⟩ := ProofLemmas.view?_isSome_of_lt_size hd0
    rw [h0] at hps
    cases h1 : s₁.view? d with
    | none => rw [h1] at hps; simp at hps
    | some vw₁ =>
      rw [h1] at hps
      simp only [Option.map_some, Option.some.injEq] at hps
      unfold State.parentOf
      rw [h1, h0]
      simp [hps]
  have hdesc : ∀ {d u}, ProperDesc s₁ d u → d < s₀.size → ProperDesc s₀ d u ∧ u < s₀.size := by
    intro d u hd
    induction hd with
    | @child d u hp =>
      intro hd0
      have hp0 : s₀.parentOf d = some u := by rw [← hparent_eq d hd0]; exact hp
      exact ⟨.child hp0, hpe d hd0 u hp0⟩
    | @step d x u hp _ ih =>
      intro hd0
      have hp0 : s₀.parentOf d = some x := by rw [← hparent_eq d hd0]; exact hp
      have hx0 : x < s₀.size := hpe d hd0 x hp0
      have ⟨hxu, hu0⟩ := ih hx0
      exact ⟨.step hp0 hxu, hu0⟩
  intro d hd hact1 a hcovv1
  have hd1 : d < s₁.size := State.isActive_lt_size hact1
  have hd0 : d < s₀.size := by
    rcases Nat.lt_or_ge d s₀.size with h | h
    · exact h
    · rw [hcv.fresh d hd1 h] at hact1; cases hact1
  have ⟨hd_s0, hv0⟩ := hdesc hd hd0
  have hact0 : s₀.isActive d = true := by
    unfold State.isActive at hact1 ⊢
    rw [← hcv.activity d hd0]
    exact hact1
  rw [hcov_eq v hv0 a] at hcovv1
  rw [hcov_eq d hd0 a]
  exact hauth d hd_s0 hact0 a hcovv1

/-- Auxiliary: under `ClosedViews s₀ s₁`, every view active in `s₁` already existed in `s₀`. -/
theorem ProofLemmas.old_of_active_of_closedViews {s₀ s₁ : State} (hcv : ClosedViews s₀ s₁) {d : ViewId}
    (hact : s₁.isActive d = true) : d < s₀.size := by
  have hd1 : d < s₁.size := State.isActive_lt_size hact
  rcases Nat.lt_or_ge d s₀.size with h | h
  · exact h
  · rw [hcv.fresh d hd1 h] at hact; cases hact

/-- **R3c (variant with a post-state law).** The same conclusion with the structural hypothesis
moved to the state *after* the scope: if `ParentCoversActive s₁` holds (an invariant law), view `v`
has return authority in `s₀`, and `ClosedViews s₀ s₁`, then `v` has return authority in `s₁`. No
hypothesis about parent links in `s₀` is needed. -/
theorem returnAuthority_of_closedViews_of_parentCoversActive {s₀ s₁ : State} {v : ViewId}
    (hpc : ParentCoversActive s₁) (hauth : ReturnAuthority s₀ v) (hcv : ClosedViews s₀ s₁) :
    ReturnAuthority s₁ v := by
  have hcov_eq : ∀ u < s₀.size, ∀ a, s₁.covers u a = s₀.covers u a := by
    intro u hu a
    have hd := hcv.domains u hu
    obtain ⟨vw₀, hu0⟩ := ProofLemmas.view?_isSome_of_lt_size hu
    rw [hu0] at hd
    cases hu1 : s₁.view? u with
    | none => rw [hu1] at hd; simp at hd
    | some vw₁ =>
      rw [hu1] at hd
      simp only [Option.map_some, Option.some.injEq] at hd
      unfold State.covers State.cell?
      rw [hu1, hu0]
      simp only [Option.bind_some]
      apply Bool.eq_iff_iff.mpr
      rw [← mem_domain_iff, ← mem_domain_iff, hd]
  have hparent_eq : ∀ d < s₀.size, s₁.parentOf d = s₀.parentOf d := by
    intro d hd0
    have hps := hcv.parents d hd0
    obtain ⟨vw₀, h0⟩ := ProofLemmas.view?_isSome_of_lt_size hd0
    rw [h0] at hps
    cases h1 : s₁.view? d with
    | none => rw [h1] at hps; simp at hps
    | some vw₁ =>
      rw [h1] at hps
      simp only [Option.map_some, Option.some.injEq] at hps
      unfold State.parentOf
      rw [h1, h0]
      simp [hps]
  intro d hd hact1 a hcovv1
  -- Every active view covering `a` on the chain from `d` up to `v` is old, and so is `v`.
  have key : ∀ {d u}, ProperDesc s₁ d u → s₁.isActive d = true → s₁.covers d a = true →
      ProperDesc s₀ d u ∧ u < s₀.size := by
    intro d u hdu
    induction hdu with
    | @child d u hp =>
      intro hact hcov
      have hd0 := ProofLemmas.old_of_active_of_closedViews hcv hact
      have hp0 : s₀.parentOf d = some u := by rw [← hparent_eq d hd0]; exact hp
      have ⟨hactu, _⟩ := hpc d (State.isActive_lt_size hact) a (State.covers_lt_width hcov) u hp
        hact hcov
      exact ⟨.child hp0, ProofLemmas.old_of_active_of_closedViews hcv hactu⟩
    | @step d x u hp _ ih =>
      intro hact hcov
      have hd0 := ProofLemmas.old_of_active_of_closedViews hcv hact
      have hp0 : s₀.parentOf d = some x := by rw [← hparent_eq d hd0]; exact hp
      have ⟨hactx, hcovx⟩ := hpc d (State.isActive_lt_size hact) a (State.covers_lt_width hcov) x
        hp hact hcov
      have ⟨hxu, hu0⟩ := ih hactx hcovx
      exact ⟨.step hp0 hxu, hu0⟩
  cases hcd : s₁.covers d a with
  | false => rfl
  | true =>
    exfalso
    have ⟨hd_s0, hv0⟩ := key hd hact1 hcd
    have hd0 := ProofLemmas.old_of_active_of_closedViews hcv hact1
    have hact0 : s₀.isActive d = true := by
      unfold State.isActive at hact1 ⊢
      rw [← hcv.activity d hd0]
      exact hact1
    rw [hcov_eq v hv0 a] at hcovv1
    have := hauth d hd_s0 hact0 a hcovv1
    rw [hcov_eq d hd0 a] at hcd
    rw [hcd] at this; cases this

/-- The *opening step* of a scope: views of `s` keep their parent link, activity flag and domain in
`s₁`, and exactly one view (the fresh id `s.size`) is added. Both `borrow` and `share` produce
such a step (`openScopeShape_of_borrow`, `openScopeShape_of_share`); cell contents and permission
forms of old views (in particular the parent's loaned cells) may change. -/
structure OpenScopeShape (s s₁ : State) : Prop where
  parents : ParentsStable s s₁
  activity : ActivityStable s s₁
  domains : DomainsStable s s₁
  size_eq : s₁.size = s.size + 1

instance (s s₁ : State) : Decidable (OpenScopeShape s s₁) :=
  decidable_of_iff (ParentsStable s s₁ ∧ ActivityStable s s₁ ∧ DomainsStable s s₁ ∧
      s₁.size = s.size + 1)
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

/-- **R3d (main).** A single scope is closed: open a fresh view `c = s.size` by any step that keeps
old views' return shapes (`OpenScopeShape s s₁`), run any closed inner computation
(`ClosedViews s₁ s₂`), then raw-end `c`; the result is closed relative to the state before the
scope. Exclusive versus shared loans play no role. -/
theorem closedViews_of_fresh_scope {s s₁ s₂ s₃ : State} {r : Addr → Byte}
    (hop : OpenScopeShape s s₁) (hin : ClosedViews s₁ s₂)
    (he : endRaw s₂ s.size r = some s₃) : ClosedViews s s₃ := by
  obtain ⟨vc, p, vp, vc₁, hvc, _, hvp, _, hret, _, rfl⟩ := endRaw_unpack he
  let c := s.size
  have hc2 : c < s₂.size := State.lt_size_of_view?_eq_some hvc
  have hp2 : p < s₂.size := State.lt_size_of_view?_eq_some hvp
  have hc_set : c < (s₂.setView p (restoreCells vc vp r)).size := by rw [setView_size]; exact hc2
  have hdom_rest : (restoreCells vc vp r).domain = vp.domain := restoreCells_domain r hret
  have hview_old : ∀ v < s.size,
      (((s₂.setView p (restoreCells vc vp r)).setView c { vc₁ with active := false }).view? v).map
        (fun vw => (vw.parent, vw.active, vw.domain)) =
      (s₂.view? v).map (fun vw => (vw.parent, vw.active, vw.domain)) := by
    intro v hv
    have hvc_ne : v ≠ c := by omega
    rw [view?_setView _ c v _ hc_set]
    simp only [hvc_ne, ↓reduceIte]
    rw [view?_setView _ p v _ hp2]
    by_cases hvp_eq : v = p
    · subst hvp_eq
      simp only [↓reduceIte, hvp, Option.map_some, Option.some.injEq]
      refine Prod.ext ?_ (Prod.ext ?_ hdom_rest)
      · rfl
      · rfl
    · simp [hvp_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    have hv1 : v < s₁.size := by rw [hop.size_eq]; omega
    have h3 := congrArg (Option.map (·.1)) (hview_old v hv)
    simp only [Option.map_map] at h3
    exact h3.trans ((hin.parents v hv1).trans (hop.parents v hv))
  · intro v hv
    have hv1 : v < s₁.size := by rw [hop.size_eq]; omega
    have h3 := congrArg (Option.map (·.2.1)) (hview_old v hv)
    simp only [Option.map_map] at h3
    exact h3.trans ((hin.activity v hv1).trans (hop.activity v hv))
  · intro v hv
    have hv1 : v < s₁.size := by rw [hop.size_eq]; omega
    have h3 := congrArg (Option.map (·.2.2)) (hview_old v hv)
    simp only [Option.map_map] at h3
    exact h3.trans ((hin.domains v hv1).trans (hop.domains v hv))
  · intro v hv hge
    rw [setView_size, setView_size] at hv
    by_cases hvc_eq : v = c
    · subst hvc_eq
      unfold State.isActive
      rw [view?_setView _ c c _ hc_set]
      simp
    · have hv1 : s₁.size ≤ v := by rw [hop.size_eq]; omega
      have hact2 := hin.fresh v hv hv1
      unfold State.isActive at hact2 ⊢
      rw [view?_setView _ c v _ hc_set]
      simp only [hvc_eq, ↓reduceIte]
      rw [view?_setView _ p v _ hp2]
      by_cases hvp_eq : v = p
      · subst hvp_eq
        rw [hvp] at hact2
        simp only [↓reduceIte, Option.map_some, Option.getD_some] at hact2 ⊢
        exact hact2
      · simp only [hvp_eq, ↓reduceIte]
        exact hact2

theorem openScopeShape_of_borrow {s s₁ : State} {p : ViewId} {A : List Addr}
    (hb : borrow s p A = some s₁) : OpenScopeShape s s₁ := by
  unfold borrow at hb
  cases hvp : s.view? p with
  | none => rw [hvp] at hb; simp at hb
  | some vp =>
    rw [hvp] at hb; dsimp only at hb
    by_cases hcond : (vp.active && vp.mode == .excl && A.all (fun a => Cell.isWritable (vp.cell? a))) = true
    · simp only [hcond, ↓reduceIte, Option.some.injEq] at hb
      subst hb
      have hp : p < s.views.length := State.lt_size_of_view?_eq_some hvp
      simp only [Bool.and_eq_true, List.all_eq_true] at hcond
      have hall := hcond.2
      let vp' := vp.mapCells vp.cells.length (fun a x => if A.contains a then some (.loaned s.size) else x)
      let vc : View := {
        parent := some p, mode := .excl, active := true,
        cells := (List.range vp.cells.length).map (fun a =>
          if A.contains a then some (.own 0 (Cell.byteOf (vp.cell? a))) else none) }
      have hdom : vp'.domain = vp.domain := by
        unfold View.domain
        have hlen : vp'.cells.length = vp.cells.length := by simp [vp', View.mapCells]
        rw [hlen]
        congr 1; funext a
        have hca := cell?_mapCells vp vp.cells.length
          (fun a x => if A.contains a then some (.loaned s.size) else x) a
        change (vp'.cell? a).isSome = (vp.cell? a).isSome
        rw [hca]
        rcases Nat.lt_or_ge a vp.cells.length with ha | ha
        · simp only [ha, ↓reduceIte]
          cases hmem : A.contains a with
          | false => rfl
          | true =>
            simp only [↓reduceIte]
            have hw := hall a (List.contains_iff_mem.mp hmem)
            unfold Cell.isWritable at hw
            cases hcell : vp.cell? a with
            | none => rw [hcell] at hw; simp at hw
            | some _ => simp
        · have hnot : ¬ a < vp.cells.length := Nat.not_lt.mpr ha
          simp only [hnot, ↓reduceIte]
          rw [cell?_eq_none_of_ge ha]
      have hget : ∀ v < s.views.length,
          ((s.views.set p vp' ++ [vc])[v]?) = (if v = p then some vp' else s.views[v]?) := by
        intro v hv
        have hv' : v < (s.views.set p vp').length := by simp [hv]
        rw [List.getElem?_append_left hv', List.getElem?_set]
        by_cases heq : v = p
        · subst heq; simp [hp]
        · have hne : p ≠ v := fun e => heq e.symm; simp [heq, hne]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro v hv; unfold State.view?; change ((s.views.set p vp' ++ [vc])[v]?).map View.parent = _
        rw [hget v hv]
        by_cases heq : v = p
        · subst heq; unfold State.view? at hvp; simp [hvp]; rfl
        · simp [heq]
      · intro v hv; unfold State.view?; change ((s.views.set p vp' ++ [vc])[v]?).map View.active = _
        rw [hget v hv]
        by_cases heq : v = p
        · subst heq; unfold State.view? at hvp; simp [hvp]; rfl
        · simp [heq]
      · intro v hv; unfold State.view?; change ((s.views.set p vp' ++ [vc])[v]?).map View.domain = _
        rw [hget v hv]
        by_cases heq : v = p
        · subst heq; unfold State.view? at hvp; simp [hvp, hdom]
        · simp [heq]
      · simp [State.size]
    · simp [hcond] at hb

theorem openScopeShape_of_share {s s₁ : State} {p : ViewId} {A : List Addr}
    (hb : share s p A = some s₁) : OpenScopeShape s s₁ := by
  unfold share at hb
  cases hvp : s.view? p with
  | none => rw [hvp] at hb; simp at hb
  | some vp =>
    rw [hvp] at hb; dsimp only at hb
    by_cases hcond : (vp.active && A.all (fun a => Cell.isOwn (vp.cell? a))) = true
    · simp only [hcond, ↓reduceIte, Option.some.injEq] at hb
      subst hb
      have hp : p < s.views.length := State.lt_size_of_view?_eq_some hvp
      let vp' := vp.mapCells vp.cells.length (fun a x =>
        if A.contains a then match x with | some (.own d b) => some (.own (d + 1) b) | y => y else x)
      let vc : View := {
        parent := some p, mode := .shared, active := true,
        cells := (List.range vp.cells.length).map (fun a =>
          if A.contains a then some (.own 1 (Cell.byteOf (vp.cell? a))) else none) }
      have hdom : vp'.domain = vp.domain := by
        unfold View.domain
        have hlen : vp'.cells.length = vp.cells.length := by simp [vp', View.mapCells]
        rw [hlen]
        congr 1; funext a
        have hca := cell?_mapCells vp vp.cells.length (fun a x =>
          if A.contains a then match x with | some (.own d b) => some (.own (d + 1) b) | y => y else x) a
        change (vp'.cell? a).isSome = (vp.cell? a).isSome
        rw [hca]
        rcases Nat.lt_or_ge a vp.cells.length with ha | ha
        · simp only [ha, ↓reduceIte]
          cases hmem : A.contains a with
          | false => rfl
          | true =>
            simp only [↓reduceIte]
            cases hcell : vp.cell? a with
            | none => rfl
            | some c => cases c <;> rfl
        · have hnot : ¬ a < vp.cells.length := Nat.not_lt.mpr ha
          simp only [hnot, ↓reduceIte]
          rw [cell?_eq_none_of_ge ha]
      have hget : ∀ v < s.views.length,
          ((s.views.set p vp' ++ [vc])[v]?) = (if v = p then some vp' else s.views[v]?) := by
        intro v hv
        have hv' : v < (s.views.set p vp').length := by simp [hv]
        rw [List.getElem?_append_left hv', List.getElem?_set]
        by_cases heq : v = p
        · subst heq; simp [hp]
        · have hne : p ≠ v := fun e => heq e.symm; simp [heq, hne]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro v hv; unfold State.view?; change ((s.views.set p vp' ++ [vc])[v]?).map View.parent = _
        rw [hget v hv]
        by_cases heq : v = p
        · subst heq; unfold State.view? at hvp; simp [hvp]; rfl
        · simp [heq]
      · intro v hv; unfold State.view?; change ((s.views.set p vp' ++ [vc])[v]?).map View.active = _
        rw [hget v hv]
        by_cases heq : v = p
        · subst heq; unfold State.view? at hvp; simp [hvp]; rfl
        · simp [heq]
      · intro v hv; unfold State.view?; change ((s.views.set p vp' ++ [vc])[v]?).map View.domain = _
        rw [hget v hv]
        by_cases heq : v = p
        · subst heq; unfold State.view? at hvp; simp [hvp, hdom]
        · simp [heq]
      · simp [State.size]
    · simp [hcond] at hb

/-- **R3d for exclusive scopes (corollary).** -/
theorem closedViews_of_borrow_scope {s s₁ s₂ s₃ : State} {p : ViewId} {A : List Addr}
    {r : Addr → Byte} (hb : borrow s p A = some s₁) (hin : ClosedViews s₁ s₂)
    (he : endRaw s₂ s.size r = some s₃) : ClosedViews s s₃ :=
  closedViews_of_fresh_scope (openScopeShape_of_borrow hb) hin he

/-- **R3d for shared scopes (corollary).** -/
theorem closedViews_of_share_scope {s s₁ s₂ s₃ : State} {p : ViewId} {A : List Addr}
    {r : Addr → Byte} (hb : share s p A = some s₁) (hin : ClosedViews s₁ s₂)
    (he : endRaw s₂ s.size r = some s₃) : ClosedViews s s₃ :=
  closedViews_of_fresh_scope (openScopeShape_of_share hb) hin he

/-- **R3f.** A write is closed (it changes a byte only). -/
theorem closedViews_of_write {s s' : State} {v : ViewId} {a : Addr} {b : Byte}
    (hw : write s v a b = some s') : ClosedViews s s' := by
  unfold write at hw
  cases hvw : s.view? v with
  | none => rw [hvw] at hw; simp at hw
  | some vw =>
    rw [hvw] at hw; dsimp only at hw
    by_cases hcw : s.canWrite v a = true
    · simp only [hcw, ↓reduceIte, Option.some.injEq] at hw
      subst hw
      have hv : v < s.size := State.lt_size_of_view?_eq_some hvw
      let vw' := vw.mapCells vw.cells.length (fun a' x => if a' = a then some (.own 0 b) else x)
      have hdom : vw'.domain = vw.domain := by
        unfold View.domain
        have hlen : vw'.cells.length = vw.cells.length := by simp [vw', View.mapCells]
        rw [hlen]
        congr 1; funext a'
        have hca := cell?_mapCells vw vw.cells.length
          (fun a' x => if a' = a then some (.own 0 b) else x) a'
        change (vw'.cell? a').isSome = (vw.cell? a').isSome
        rw [hca]
        rcases Nat.lt_or_ge a' vw.cells.length with ha' | ha'
        · simp only [ha', ↓reduceIte]
          by_cases heq : a' = a
          · subst heq
            simp only [↓reduceIte]
            unfold State.canWrite State.depth? State.cell? at hcw
            rw [hvw] at hcw
            simp only [Bool.and_eq_true, beq_iff_eq, Option.bind_some] at hcw
            cases hca0 : vw.cell? a' with
            | none => rw [hca0] at hcw; simp at hcw
            | some _ => simp
          · simp [heq]
        · have hnot : ¬ a' < vw.cells.length := Nat.not_lt.mpr ha'
          simp only [hnot, ↓reduceIte]
          rw [cell?_eq_none_of_ge ha']
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro u hu; rw [view?_setView _ v u _ hv]
        by_cases heq : u = v
        · subst heq; simp [hvw]; rfl
        · simp [heq]
      · intro u hu; rw [view?_setView _ v u _ hv]
        by_cases heq : u = v
        · subst heq; simp [hvw]; rfl
        · simp [heq]
      · intro u hu; rw [view?_setView _ v u _ hv]
        by_cases heq : u = v
        · subst heq; simp only [↓reduceIte, hvw, Option.map_some, Option.some.injEq]; exact hdom
        · simp [heq]
      · intro u hu hge; rw [setView_size] at hu; exact absurd hu (Nat.not_lt_of_ge hge)
    · simp [hcw] at hw

/-- **R3g (corollary of R3c and R2a).** Return authority established before any closed scope
licenses a sound end after it: if `c` had return authority in `s₀`, `ClosedViews s₀ s₁`, and the
five tree-local laws hold in `s₁` (they must be re-established for `s₁`; `ClosedViews` does not
carry them over from `s₀`), then the raw end of `c` in `s₁` preserves the five local laws and
resurrects nothing. -/
theorem endRaw_preserves_localLoanLaws_and_noResurrection_of_returnAuthority_before_closedViews
    {s₀ s₁ s₂ : State} {c : ViewId} {r : Addr → Byte}
    (hauth : ReturnAuthority s₀ c) (hcv : ClosedViews s₀ s₁)
    (hpc : ParentCoversActive s₁) (hecl : ExclChildLoaned s₁) (hscb : SharedChildBelowOwn s₁)
    (hscs : SharedChildrenShared s₁) (hdc : DepthCounts s₁)
    (hend : endRaw s₁ c r = some s₂) : LocalLoanLaws s₂ ∧ NoResurrection s₁ s₂ :=
  endRaw_preserves_localLoanLaws_and_noResurrection_of_returnAuthority hpc hecl hscb hscs hdc
    (returnAuthority_of_closedViews_of_parentCoversActive hpc hauth hcv) hend

/-- **Scoped runs**: the well-bracketed computations built from writes and from scopes that open a
fresh view by `borrow` or `share`, run a scoped inner computation, and then end exactly that fresh
view, composed sequentially. This is the syntax of "any number of nested, completed scopes". -/
inductive ScopedRun : State → State → Prop
  | refl (s : State) : ScopedRun s s
  | write {s s' : State} {v : ViewId} {a : Addr} {b : Byte} :
      write s v a b = some s' → ScopedRun s s'
  | borrowScope {s s₁ s₂ s₃ : State} {p : ViewId} {A : List Addr} {r : Addr → Byte} :
      borrow s p A = some s₁ → ScopedRun s₁ s₂ → endRaw s₂ s.size r = some s₃ → ScopedRun s s₃
  | shareScope {s s₁ s₂ s₃ : State} {p : ViewId} {A : List Addr} {r : Addr → Byte} :
      share s p A = some s₁ → ScopedRun s₁ s₂ → endRaw s₂ s.size r = some s₃ → ScopedRun s s₃
  | seq {s₀ s₁ s₂ : State} : ScopedRun s₀ s₁ → ScopedRun s₁ s₂ → ScopedRun s₀ s₂

/-- **R3h (corollary of R3a, R3d, R3f, by induction).** Every scoped run is closed. -/
theorem closedViews_of_scopedRun {s s' : State} (h : ScopedRun s s') : ClosedViews s s' := by
  induction h with
  | refl s => exact closedViews_refl s
  | write hw => exact closedViews_of_write hw
  | borrowScope hb _ he ih => exact closedViews_of_borrow_scope hb ih he
  | shareScope hb _ he ih => exact closedViews_of_share_scope hb ih he
  | seq _ _ ih₁ ih₂ => exact closedViews_trans ih₁ ih₂

/-- **R3h, authority form (corollary with R3c).** Return authority survives any scoped run,
provided `ParentCoversActive` holds after it. -/
theorem returnAuthority_of_scopedRun_of_parentCoversActive {s₀ s₁ : State} {v : ViewId}
    (hpc : ParentCoversActive s₁) (hauth : ReturnAuthority s₀ v) (hrun : ScopedRun s₀ s₁) :
    ReturnAuthority s₁ v :=
  returnAuthority_of_closedViews_of_parentCoversActive hpc hauth (closedViews_of_scopedRun hrun)

/-- A scoped run never removes views. -/
theorem ScopedRun.size_le {s s' : State} (h : ScopedRun s s') : s.size ≤ s'.size := by
  induction h with
  | refl s => exact Nat.le_refl _
  | write hw => rw [write_size hw]; exact Nat.le_refl _
  | borrowScope hb _ he ih =>
    rw [endRaw_size he]; rw [borrow_size hb] at ih; omega
  | shareScope hb _ he ih =>
    rw [endRaw_size he]; rw [share_size hb] at ih; omega
  | seq _ _ ih₁ ih₂ =>
    exact Nat.le_trans ih₁ ih₂

/-- A write changes no view's activity. -/
theorem write_isActive {s s' : State} {v : ViewId} {a : Addr} {b : Byte}
    (hw : write s v a b = some s') (u : ViewId) : s'.isActive u = s.isActive u := by
  unfold write at hw
  cases hvw : s.view? v with
  | none => rw [hvw] at hw; simp at hw
  | some vw =>
    rw [hvw] at hw; dsimp only at hw
    split at hw
    · simp only [Option.some.injEq] at hw; subst hw
      have hv : v < s.size := State.lt_size_of_view?_eq_some hvw
      unfold State.isActive
      rw [view?_setView _ v u _ hv]
      by_cases h : u = v
      · subst h; simp [hvw]; rfl
      · simp [h]
    · simp at hw

/-- The opening step of a scope changes no old view's activity. -/
theorem OpenScopeShape.isActive_old {s s₁ : State} (hop : OpenScopeShape s s₁)
    {u : ViewId} (hu : u < s.size) : s₁.isActive u = s.isActive u := by
  unfold State.isActive
  rw [hop.activity u hu]

/-- A scoped run leaves the activity of every old view unchanged and leaves every view it creates
inactive. (Proved directly by induction on the run, without R3a, R3d or R3f; it is what rules out
open borrows and ends of old views as scoped runs.) -/
theorem ScopedRun.isActive_eq {s s' : State} (h : ScopedRun s s') (u : ViewId) :
    s'.isActive u = (if u < s.size then s.isActive u else false) := by
  induction h with
  | refl s =>
    by_cases hu : u < s.size
    · simp [hu]
    · simp only [hu, ↓reduceIte]
      unfold State.isActive State.view?
      unfold State.size at hu
      rw [List.getElem?_eq_none (Nat.le_of_not_lt hu)]
      rfl
  | @write s s' v a b hw =>
    rw [write_isActive hw u]
    by_cases hu : u < s.size
    · simp [hu]
    · simp only [hu, ↓reduceIte]
      unfold State.isActive State.view?
      unfold State.size at hu
      rw [List.getElem?_eq_none (Nat.le_of_not_lt hu)]
      rfl
  | @borrowScope s s₁ s₂ s₃ p A r hb _ he ih =>
    have hop := openScopeShape_of_borrow hb
    rw [endRaw_isActive he u]
    by_cases huc : u = s.size
    · subst huc; simp
    · simp only [huc, ↓reduceIte, ih, hop.size_eq]
      by_cases hu : u < s.size
      · have hu1 : u < s.size + 1 := Nat.lt_succ_of_lt hu
        simp only [hu, hu1, ↓reduceIte]
        exact hop.isActive_old hu
      · have hnot1 : ¬ u < s.size + 1 := fun h =>
          hu (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) huc)
        simp [hu, hnot1]
  | @shareScope s s₁ s₂ s₃ p A r hb _ he ih =>
    have hop := openScopeShape_of_share hb
    rw [endRaw_isActive he u]
    by_cases huc : u = s.size
    · subst huc; simp
    · simp only [huc, ↓reduceIte, ih, hop.size_eq]
      by_cases hu : u < s.size
      · have hu1 : u < s.size + 1 := Nat.lt_succ_of_lt hu
        simp only [hu, hu1, ↓reduceIte]
        exact hop.isActive_old hu
      · have hnot1 : ¬ u < s.size + 1 := fun h =>
          hu (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) huc)
        simp [hu, hnot1]
  | @seq s₀ s₁ s₂ h₁ _ ih₁ ih₂ =>
    have hle := h₁.size_le
    rw [ih₂]
    by_cases hu0 : u < s₀.size
    · have hu1 : u < s₁.size := Nat.lt_of_lt_of_le hu0 hle
      simp only [hu0, hu1, ↓reduceIte]
      rw [ih₁]; simp [hu0]
    · simp only [hu0, ↓reduceIte]
      by_cases hu1 : u < s₁.size
      · simp only [hu1, ↓reduceIte]; rw [ih₁]; simp [hu0]
      · simp [hu1]

/-! ## Facts about views created after `s₀` (used by R3c's boundaries) -/

/-- For a view id not yet allocated in `s₀`, return authority in `s₀` holds vacuously. -/
theorem returnAuthority_vacuous_of_ge_size (s₀ : State) {v : ViewId} (hv : s₀.size ≤ v) :
    ReturnAuthority s₀ v := by
  intro _ _ _ a hcov
  unfold State.covers State.cell? State.view? at hcov
  unfold State.size at hv
  rw [List.getElem?_eq_none hv] at hcov
  simp at hcov

/-- After a closed scope, a view id not allocated in `s₀` cannot be ended. -/
theorem endRaw_eq_none_of_closedViews_of_ge_size {s₀ s₁ : State} {v : ViewId}
    (hcv : ClosedViews s₀ s₁) (hv : s₀.size ≤ v) (r : Addr → Byte) :
    endRaw s₁ v r = none := by
  rcases Nat.lt_or_ge v s₁.size with hv1 | hv1
  · have hact : s₁.isActive v = false := hcv.fresh v hv1 hv
    cases hend : endRaw s₁ v r with
    | none => rfl
    | some _ =>
      have his : (endRaw s₁ v r).isSome = true := by rw [hend]; rfl
      obtain ⟨vc, _, _, hvc, hvact, _⟩ := (endRaw_isSome_iff s₁ v r).mp his
      unfold State.isActive at hact
      rw [hvc] at hact
      simp [hvact] at hact
  · unfold endRaw State.view?
    unfold State.size at hv1
    rw [List.getElem?_eq_none hv1]

namespace Ex

/-! ## Further named states -/

/-- `t2e`: ending the innermost shared view `C` in `t2` (`B` back to depth `1`). -/
def t2e : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 1 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.own 1 0)] },
  { parent := some 1, mode := .shared, active := false, cells := [some (.own 1 0)] }]⟩

/-- `t2ee`: ending `B` in `t2e` (`A` back to depth `0`). -/
def t2ee : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 0 0)] },
  { parent := some 0, mode := .shared, active := false, cells := [some (.own 1 0)] },
  { parent := some 1, mode := .shared, active := false, cells := [some (.own 1 0)] }]⟩

/-- `s2ee b`: ending `B` in `s2e _` (after `C` ended), `A` restored to byte `b`. -/
def s2ee (b : Byte) : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 0 b)] },
  { parent := some 0, mode := .excl, active := false, cells := [some (.own 0 0)] },
  { parent := some 1, mode := .excl, active := false, cells := [some (.own 0 0)] }]⟩

/-- `s1w`: `s1` after `B` writes byte `5`. -/
def s1w : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.own 0 5)] }]⟩

/-- `s2w`: `s2` after `C` writes byte `5`. -/
def s2w : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.loaned 2)] },
  { parent := some 1, mode := .excl, active := true, cells := [some (.own 0 5)] }]⟩

/-- `runMid`: `s2w` after ending `C` with byte `7` handed back to `B`. -/
def runMid : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.own 0 7)] },
  { parent := some 1, mode := .excl, active := false, cells := [some (.own 0 5)] }]⟩

/-- `runEnd`: `runMid` after ending `B` with byte `9` handed back to `A`. -/
def runEnd : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 0 9)] },
  { parent := some 0, mode := .excl, active := false, cells := [some (.own 0 7)] },
  { parent := some 1, mode := .excl, active := false, cells := [some (.own 0 5)] }]⟩

/-- Pre-scope state for the `ParentsExist` counterexample: `C` (id 2) has a dangling parent link
to the not-yet-created id `3`. -/
def eS0 : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.loaned 3)] },
  { parent := some 3, mode := .excl, active := true, cells := [some (.own 0 0)] }]⟩

/-- `eS0` after a scope that created view `3` as a child of `B` (borrowing the empty address list)
and ended it. -/
def eS1 : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.loaned 3)] },
  { parent := some 3, mode := .excl, active := true, cells := [some (.own 0 0)] },
  { parent := some 1, mode := .excl, active := false, cells := [none] }]⟩

/-- `eS0` with the scope still open (view `3` active). -/
def eS0open : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.loaned 3)] },
  { parent := some 3, mode := .excl, active := true, cells := [some (.own 0 0)] },
  { parent := some 1, mode := .excl, active := true, cells := [none] }]⟩

/-- `g1`: two addresses; `A` lent address `0` to `B`, and an unrelated root `R` (id 2) owns
address `1`. -/
def g1 : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1), none] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.own 0 0), none] },
  { parent := none, mode := .excl, active := true, cells := [none, some (.own 0 0)] }]⟩

/-- `g1r`: `g1` with the unrelated root `R` retired. -/
def g1r : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1), none] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.own 0 0), none] },
  { parent := none, mode := .excl, active := false, cells := [none, some (.own 0 0)] }]⟩

/-- `s2` extended by an active child `D` of `C` (an inner scope that is not closed). -/
def s2open : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.loaned 2)] },
  { parent := some 1, mode := .excl, active := true, cells := [some (.own 0 0)] },
  { parent := some 2, mode := .excl, active := true, cells := [] }]⟩

/-- `t2` extended by an active shared child `D` of `C` covering nothing (an inner scope that is not
closed). -/
def t2open : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 1 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.own 2 0)] },
  { parent := some 1, mode := .shared, active := true, cells := [some (.own 1 0)] },
  { parent := some 2, mode := .shared, active := true, cells := [] }]⟩

/-! ## Definition examples -/

/-- Positive: a completed nested scope (borrow `B → C`, end `C`) is closed relative to `s1`. -/
theorem closedViews_example_pos (b : Byte) : ClosedViews s1 (s2e b) := of_decide_eq_true rfl

/-- Negative: an open scope (`C` still active) is not closed. -/
theorem closedViews_example_neg : ¬ ClosedViews s1 s2 := by decide

theorem parentsStable_examples : ParentsStable s1 s2 ∧ ¬ ParentsStable u2 t2 := by decide
theorem activityStable_examples : ActivityStable s1 s2 ∧ ¬ ActivityStable aS0 s2 := by decide
theorem domainsStable_examples : DomainsStable s1 s2 ∧ ¬ DomainsStable e2 s2 := by decide
theorem newViewsInactive_examples : NewViewsInactive s1 (s2e 0) ∧ ¬ NewViewsInactive s1 s2 := by
  decide

/-- `OpenScopeShape`: positive for a borrow (`s0 → s1`, `s1 → s2`) and a share (`s0 → t1`);
negative for two new views at once (`s0 → s2`) and for no new view (`s1 → s1`). -/
theorem openScopeShape_examples :
    OpenScopeShape s0 s1 ∧ OpenScopeShape s1 s2 ∧ OpenScopeShape s0 t1 ∧
    ¬ OpenScopeShape s0 s2 ∧ ¬ OpenScopeShape s1 s1 := by decide

/-- `ScopedRun`, positive: from `s0`, borrow `A → B`; inside, borrow `B → C`, write through `C`,
end `C`; then end `B`. -/
theorem scopedRun_example_pos : ScopedRun s0 runEnd :=
  .borrowScope (s₁ := s1) (s₂ := runMid) (p := 0) (A := [0]) (r := fun _ => 9) (by decide)
    (.borrowScope (s₁ := s2) (s₂ := s2w) (p := 1) (A := [0]) (r := fun _ => 7) (by decide)
      (.write (v := 2) (a := 0) (b := 5) (by decide)) rfl) rfl

/-- `ScopedRun`, negative: (1) the open borrow `s1 → s2` (a genuine `borrow` step whose new view `C`
is still active) is not a scoped run; (2) ending the old view `B` (`s2 → s3 0`, a genuine raw end
of a view the run did not open) is not a scoped run; (3) a scoped run never removes views, so `s2`
cannot reach `s1`. (1) and (2) follow from `ScopedRun.isActive_eq`, (3) from `ScopedRun.size_le`. -/
theorem scopedRun_example_neg :
    borrow s1 1 [0] = some s2 ∧ ¬ ScopedRun s1 s2 ∧
    endRaw s2 1 (fun _ => 0) = some (s3 0) ∧ ¬ ScopedRun s2 (s3 0) ∧
    ¬ ScopedRun s2 s1 :=
  ⟨by decide,
   fun h => absurd (ScopedRun.isActive_eq h 2) (by decide),
   rfl,
   fun h => absurd (ScopedRun.isActive_eq h 1) (by decide),
   fun h => absurd (ScopedRun.size_le h) (by decide)⟩

/-! ## Non-vacuity -/

/-- **R3c non-vacuity (both forms).** `B` has authority in `s1`; after the closed nested scope
`s1 → s2e 0`, parent links of `s1` exist and `ParentCoversActive` holds in `s2e 0`. -/
theorem returnAuthority_closedViews_nonvacuous :
    ParentsExist s1 ∧ ReturnAuthority s1 1 ∧ ClosedViews s1 (s2e 0) ∧
      ParentCoversActive (s2e 0) :=
  ⟨by decide, returnAuthority_s1_B, by decide, by decide⟩

/-- **R3a non-vacuity.** Two consecutive closed steps (a write, then a completed nested scope).
(Reflexivity has no hypotheses.) -/
theorem closedViews_trans_nonvacuous :
    ClosedViews s1 s1w ∧ ClosedViews s1w ⟨[
      { parent := none, mode := .excl, active := true, cells := [some (.loaned 1)] },
      { parent := some 0, mode := .excl, active := true, cells := [some (.own 0 7)] },
      { parent := some 1, mode := .excl, active := false, cells := [some (.own 0 5)] }]⟩ :=
  by decide

/-- **R3d non-vacuity, exclusive.** Borrow `A → B` from `s0`; the inner closed scope contains a
nested completed scope (`B → C`, ended), so it allocates a view (`s1.size < (s2e 0).size`); then
end `B`. -/
theorem borrow_scope_nonvacuous (r : Addr → Byte) :
    OpenScopeShape s0 s1 ∧ borrow s0 0 [0] = some s1 ∧ ClosedViews s1 (s2e 0) ∧
      s1.size < (s2e 0).size ∧ endRaw (s2e 0) s0.size r = some (s2ee (r 0)) :=
  ⟨by decide, by decide, by decide, by decide, rfl⟩

/-- **R3d non-vacuity, shared.** Share `A → B` from `s0`; the inner closed scope contains a nested
completed shared scope (`B → C`, ended); then end `B`. -/
theorem share_scope_nonvacuous (r : Addr → Byte) :
    OpenScopeShape s0 t1 ∧ share s0 0 [0] = some t1 ∧ ClosedViews t1 t2e ∧ t1.size < t2e.size ∧
      endRaw t2e s0.size r = some t2ee :=
  ⟨by decide, by decide, by decide, by decide, rfl⟩

/-- **R3f non-vacuity.** -/
theorem write_nonvacuous : write s1 1 0 5 = some s1w := by decide

/-- **R3g non-vacuity.** `B` had authority in `s1`; after the closed scope to `s2e 0` the five
local laws hold and `B`'s raw end succeeds. -/
theorem scoped_end_nonvacuous (r : Addr → Byte) :
    ReturnAuthority s1 1 ∧ ClosedViews s1 (s2e 0) ∧ LocalLoanLaws (s2e 0) ∧
      endRaw (s2e 0) 1 r = some (s2ee (r 0)) :=
  ⟨returnAuthority_s1_B, by decide, by decide, rfl⟩

/-- **R3h non-vacuity.** The nested run `s0 → runEnd`; `A` has authority in `s0`, and
`ParentCoversActive` holds in `runEnd`. -/
theorem scopedRun_nonvacuous :
    ScopedRun s0 runEnd ∧ ReturnAuthority s0 0 ∧ ParentCoversActive runEnd :=
  ⟨scopedRun_example_pos, returnAuthority_of_closed [] (by decide) (by decide), by decide⟩

/-! ## Result 4: each closed-views condition is necessary (canonical form)

For each condition, a pre-scope state `s₀` in which `B` (id 1) has return authority and all
parent links exist, and a post-scope state `s₁` that satisfies the full loan-tree invariant (so
`ParentCoversActive s₁` and the five local laws hold) and the other three conditions but not this
one. `B` loses return authority (the conclusion of both forms of R3c fails), and ending `B` in
`s₁` breaks the local laws (R3g's conclusion fails). -/

/-- **R4a, `NewViewsInactive`.** A scope that leaves its new child `C` active. -/
theorem returnAuthority_lost_without_newViewsInactive (r : Addr → Byte) :
    ParentsExist s1 ∧ ReturnAuthority s1 1 ∧
    ParentsStable s1 s2 ∧ ActivityStable s1 s2 ∧ DomainsStable s1 s2 ∧
    ¬ NewViewsInactive s1 s2 ∧ ¬ ReturnAuthority s2 1 ∧
    LoanTreeInv s2 ∧ endRaw s2 1 r = some (s3 (r 0)) ∧ ¬ LocalLoanLaws (s3 (r 0)) ∧
    ¬ LoanTreeInv (s3 (r 0)) :=
  ⟨by decide, returnAuthority_s1_B, by decide, by decide, by decide, by decide,
   not_returnAuthority_s2_B, by decide, rfl, of_decide_eq_false rfl, of_decide_eq_false rfl⟩

/-- **R4a, `ParentsStable`.** A scope that re-parents the old active shared reader `C` from `A` to
its sibling `B` (`u2 → t2`; the full invariant holds on both sides). -/
theorem returnAuthority_lost_without_parentsStable :
    ParentsExist u2 ∧ ReturnAuthority u2 1 ∧
    ¬ ParentsStable u2 t2 ∧ ActivityStable u2 t2 ∧ DomainsStable u2 t2 ∧
    NewViewsInactive u2 t2 ∧ ¬ ReturnAuthority t2 1 ∧
    LoanTreeInv u2 ∧ LoanTreeInv t2 ∧ endRaw t2 1 (fun _ => 0) = some t3 ∧
    ¬ LocalLoanLaws t3 ∧ ¬ LoanTreeInv t3 :=
  ⟨by decide, returnAuthority_of_closed [] (by decide) (by decide), by decide, by decide,
   by decide, by decide, not_returnAuthority_t2_B, by decide, by decide, rfl, by decide,
   by decide⟩

/-- **R4a, `ActivityStable`.** A scope that re-activates `B`'s retired child `C`. -/
theorem returnAuthority_lost_without_activityStable (r : Addr → Byte) :
    ParentsExist aS0 ∧ ReturnAuthority aS0 1 ∧
    ParentsStable aS0 s2 ∧ ¬ ActivityStable aS0 s2 ∧ DomainsStable aS0 s2 ∧
    NewViewsInactive aS0 s2 ∧ ¬ ReturnAuthority s2 1 ∧
    LoanTreeInv s2 ∧ endRaw s2 1 r = some (s3 (r 0)) ∧ ¬ LocalLoanLaws (s3 (r 0)) ∧
    ¬ LoanTreeInv (s3 (r 0)) :=
  ⟨by decide, returnAuthority_of_closed [2] (by decide) (by decide), by decide, by decide,
   by decide, by decide, not_returnAuthority_s2_B, by decide, rfl, of_decide_eq_false rfl,
   of_decide_eq_false rfl⟩

/-- **R4a, `DomainsStable`.** A scope that grows the domain of `B`'s active, initially empty child
`C` (created by borrowing the empty address list, `e2`) onto `B`'s cell. -/
theorem returnAuthority_lost_without_domainsStable (r : Addr → Byte) :
    ParentsExist e2 ∧ ReturnAuthority e2 1 ∧
    ParentsStable e2 s2 ∧ ActivityStable e2 s2 ∧ ¬ DomainsStable e2 s2 ∧
    NewViewsInactive e2 s2 ∧ ¬ ReturnAuthority s2 1 ∧
    LoanTreeInv e2 ∧ LoanTreeInv s2 ∧ endRaw s2 1 r = some (s3 (r 0)) ∧
    ¬ LocalLoanLaws (s3 (r 0)) ∧ ¬ LoanTreeInv (s3 (r 0)) :=
  ⟨by decide, returnAuthority_of_closed [2] (by decide) (by decide), by decide, by decide,
   by decide, by decide, not_returnAuthority_s2_B, by decide, by decide, rfl,
   of_decide_eq_false rfl, of_decide_eq_false rfl⟩

/-- Tightness of R3c's `ParentsExist s₀` and of the variant's `ParentCoversActive s₁`: an old
active view `C` with a dangling parent link to the future id `3`; the scope creates `3` as a
(retired) child of `B`, which makes `C` an active descendant of `B` on `B`'s cell. All four
closed-views conditions hold. -/
theorem returnAuthority_lost_without_parentsExist :
    ¬ ParentsExist eS0 ∧ ReturnAuthority eS0 1 ∧ ClosedViews eS0 eS1 ∧
    ¬ ParentCoversActive eS1 ∧ ¬ ReturnAuthority eS1 1 :=
  ⟨by decide, returnAuthority_of_closed [] (by decide) (by decide), by decide, by decide,
   fun h => absurd (h 2 (.step (x := 3) rfl (.child rfl)) rfl 0 rfl) (by decide)⟩

/-- Tightness of the authority hypothesis of R3c (both forms) and R3g: with `s₀ = s₁ = s2`, all
other hypotheses hold, but `B` has no authority, and ending it breaks the local laws. -/
theorem returnAuthority_needed_before_scope :
    ParentsExist s2 ∧ ParentCoversActive s2 ∧ ¬ ReturnAuthority s2 1 ∧ ClosedViews s2 s2 ∧
    LocalLoanLaws s2 ∧ ∃ s', endRaw s2 1 (fun _ => 0) = some s' ∧ ¬ LocalLoanLaws s' :=
  ⟨by decide, by decide, not_returnAuthority_s2_B, by decide, by decide, _, rfl, by decide⟩

/-- Tightness of R3g's five local-law hypotheses, with `s₀ = s₁` (closed by `decide`) and the
counterexample states of R2a: for each law, all other hypotheses of R3g hold and its conclusion
fails. -/
theorem scoped_end_needs_local_laws :
    (ReturnAuthority cxParentCoversActive 1 ∧
      ClosedViews cxParentCoversActive cxParentCoversActive ∧
      ¬ ParentCoversActive cxParentCoversActive ∧ ExclChildLoaned cxParentCoversActive ∧
      SharedChildBelowOwn cxParentCoversActive ∧ SharedChildrenShared cxParentCoversActive ∧
      DepthCounts cxParentCoversActive ∧
      ∃ s', endRaw cxParentCoversActive 1 (fun _ => 0) = some s' ∧
        ¬ (LocalLoanLaws s' ∧ NoResurrection cxParentCoversActive s')) ∧
    (ReturnAuthority cxExclChildLoaned 1 ∧ ClosedViews cxExclChildLoaned cxExclChildLoaned ∧
      ParentCoversActive cxExclChildLoaned ∧ ¬ ExclChildLoaned cxExclChildLoaned ∧
      SharedChildBelowOwn cxExclChildLoaned ∧ SharedChildrenShared cxExclChildLoaned ∧
      DepthCounts cxExclChildLoaned ∧
      ∃ s', endRaw cxExclChildLoaned 1 (fun _ => 0) = some s' ∧
        ¬ (LocalLoanLaws s' ∧ NoResurrection cxExclChildLoaned s')) ∧
    (ReturnAuthority cxSharedChildBelowOwn 1 ∧
      ClosedViews cxSharedChildBelowOwn cxSharedChildBelowOwn ∧
      ParentCoversActive cxSharedChildBelowOwn ∧ ExclChildLoaned cxSharedChildBelowOwn ∧
      ¬ SharedChildBelowOwn cxSharedChildBelowOwn ∧ SharedChildrenShared cxSharedChildBelowOwn ∧
      DepthCounts cxSharedChildBelowOwn ∧
      ∃ s', endRaw cxSharedChildBelowOwn 1 (fun _ => 0) = some s' ∧
        ¬ (LocalLoanLaws s' ∧ NoResurrection cxSharedChildBelowOwn s')) ∧
    (ReturnAuthority cxSharedChildrenShared 2 ∧
      ClosedViews cxSharedChildrenShared cxSharedChildrenShared ∧
      ParentCoversActive cxSharedChildrenShared ∧ ExclChildLoaned cxSharedChildrenShared ∧
      SharedChildBelowOwn cxSharedChildrenShared ∧ ¬ SharedChildrenShared cxSharedChildrenShared ∧
      DepthCounts cxSharedChildrenShared ∧
      ∃ s', endRaw cxSharedChildrenShared 2 (fun _ => 0) = some s' ∧
        ¬ (LocalLoanLaws s' ∧ NoResurrection cxSharedChildrenShared s')) ∧
    (ReturnAuthority cxDepthCounts 1 ∧ ClosedViews cxDepthCounts cxDepthCounts ∧
      ParentCoversActive cxDepthCounts ∧ ExclChildLoaned cxDepthCounts ∧
      SharedChildBelowOwn cxDepthCounts ∧ SharedChildrenShared cxDepthCounts ∧
      ¬ DepthCounts cxDepthCounts ∧
      ∃ s', endRaw cxDepthCounts 1 (fun _ => 0) = some s' ∧
        ¬ (LocalLoanLaws s' ∧ NoResurrection cxDepthCounts s')) :=
  ⟨⟨returnAuthority_of_closed [2] (by decide) (by decide), by decide, by decide, by decide,
     by decide, by decide, by decide, _, rfl, fun h => absurd h.1 (by decide)⟩,
   ⟨returnAuthority_of_closed [2] (by decide) (by decide), by decide, by decide, by decide,
     by decide, by decide, by decide, _, rfl, fun h => absurd h.1 (by decide)⟩,
   ⟨returnAuthority_of_closed [2] (by decide) (by decide), by decide, by decide, by decide,
     by decide, by decide, by decide, _, rfl, fun h => absurd h.1 (by decide)⟩,
   ⟨returnAuthority_of_closed [3] (by decide) (by decide), by decide, by decide, by decide,
     by decide, by decide, by decide, _, rfl, fun h => absurd h.1 (by decide)⟩,
   ⟨returnAuthority_of_closed [] (by decide) (by decide), by decide, by decide, by decide,
     by decide, by decide, by decide, _, rfl, fun h => absurd h.1 (by decide)⟩⟩

/-- **R4g (`ClosedViews` is sufficient, not necessary).** Retiring an unrelated root `R` violates
`ActivityStable`, yet `B`'s return authority survives, and the full invariant holds on both sides:
only re-activation (or re-parenting, domain growth, or an open new view), not retirement, of old
views threatens authority. -/
theorem closedViews_not_necessary_for_returnAuthority :
    LoanTreeInv g1 ∧ LoanTreeInv g1r ∧ ReturnAuthority g1 1 ∧ ReturnAuthority g1r 1 ∧
    ¬ ClosedViews g1 g1r :=
  ⟨by decide, by decide, returnAuthority_of_closed [] (by decide) (by decide),
   returnAuthority_of_closed [] (by decide) (by decide), by decide⟩

/-- R3a (transitivity) tightness (both hypotheses, trivially): `ClosedViews s1 s1` and
`ClosedViews s2 s2` hold but `ClosedViews s1 s2` does not, so dropping either hypothesis of
transitivity (with `s₁ := s₀` or `s₂ := s₁`) falsifies it. -/
theorem closedViews_trans_needs_both :
    ClosedViews s1 s1 ∧ ClosedViews s2 s2 ∧ ¬ ClosedViews s1 s2 := by decide

/-- R3d tightness, inner closedness (exclusive): borrow `B → C` from `s1`, run an inner step that
leaves a new view `D` active (not closed), then end `C`: the outcome is not closed relative to
`s1`. -/
theorem closedViews_of_borrow_scope_needs_inner_closed :
    borrow s1 1 [0] = some s2 ∧ OpenScopeShape s1 s2 ∧ ¬ ClosedViews s2 s2open ∧
    ∃ s₃, endRaw s2open s1.size (fun _ => 0) = some s₃ ∧ ¬ ClosedViews s1 s₃ :=
  ⟨by decide, by decide, by decide, _, rfl, by decide⟩

/-- R3d tightness, inner closedness (shared): the same with a shared scope. -/
theorem closedViews_of_share_scope_needs_inner_closed :
    share t1 1 [0] = some t2 ∧ OpenScopeShape t1 t2 ∧ ¬ ClosedViews t2 t2open ∧
    ∃ s₃, endRaw t2open t1.size (fun _ => 0) = some s₃ ∧ ¬ ClosedViews t1 s₃ :=
  ⟨by decide, by decide, by decide, _, rfl, by decide⟩

/-- R3d tightness, opening step: without `OpenScopeShape s s₁` (here `s = s0`, `s₁ = s2`, two new
views), the inner scope is closed and the end of `s0.size` succeeds, but the outcome is not
closed relative to `s0`. -/
theorem fresh_scope_needs_open_step :
    ¬ OpenScopeShape s0 s2 ∧ ClosedViews s2 s2 ∧ endRaw s2 s0.size (fun _ => 0) = some (s3 0) ∧
      ¬ ClosedViews s0 (s3 0) :=
  ⟨by decide, by decide, rfl, by decide⟩

/-- R3d tightness, the final end: without it (taking `s₃ := s₂`) the open view is still active;
and ending any other view than the fresh one (here `1 ≠ s1.size`) also fails. -/
theorem fresh_scope_needs_end_of_fresh_view :
    OpenScopeShape s1 s2 ∧ ClosedViews s2 s2 ∧ ¬ ClosedViews s1 s2 ∧
    endRaw s2 1 (fun _ => 0) = some (s3 0) ∧ ¬ ClosedViews s1 (s3 0) :=
  ⟨by decide, by decide, by decide, rfl, by decide⟩

/-- R3h tightness (first form), the run itself: the open borrow `s1 → s2` is a genuine step but not
a scoped run, and `s2` is not closed relative to `s1`. -/
theorem closedViews_of_scopedRun_needs_scopedRun :
    borrow s1 1 [0] = some s2 ∧ ¬ ScopedRun s1 s2 ∧ ¬ ClosedViews s1 s2 :=
  ⟨by decide, scopedRun_example_neg.2.1, by decide⟩

/-- R3h tightness (authority form). (1) `ParentCoversActive` afterwards: the scoped run `eS0 →
eS1` (borrow the empty address list from `B`, end the new view) is genuine, `B` has authority in
`eS0`, but `eS1` violates `ParentCoversActive` and `B` has no authority there. (2) Authority before:
the empty run on `s2`. (3) The run itself: the open borrow `s1 → s2` is not a scoped run, `B` has
authority in `s1` and `ParentCoversActive s2` holds, but `B` has no authority in `s2`. -/
theorem scopedRun_authority_tightness :
    (ScopedRun eS0 eS1 ∧ ReturnAuthority eS0 1 ∧ ¬ ParentCoversActive eS1 ∧
      ¬ ReturnAuthority eS1 1) ∧
    (ScopedRun s2 s2 ∧ ParentCoversActive s2 ∧ ¬ ReturnAuthority s2 1) ∧
    (¬ ScopedRun s1 s2 ∧ ReturnAuthority s1 1 ∧ ParentCoversActive s2 ∧
      ¬ ReturnAuthority s2 1) :=
  ⟨⟨.borrowScope (s₁ := eS0open) (s₂ := eS0open) (p := 1) (A := []) (r := fun _ => 0)
      (by decide) (.refl _) rfl,
    returnAuthority_of_closed [] (by decide) (by decide), by decide,
    fun h => absurd (h 2 (.step (x := 3) rfl (.child rfl)) rfl 0 rfl) (by decide)⟩,
   ⟨.refl _, by decide, not_returnAuthority_s2_B⟩,
   ⟨scopedRun_example_neg.2.1, returnAuthority_s1_B, by decide, not_returnAuthority_s2_B⟩⟩

/-! ## What `ClosedViews` does not constrain -/

/-- `ClosedViews` ignores view modes: in `t1 → s1` view `B` changes from a read-only shared view to
a writable exclusive view, both states satisfy the full invariant, and `ClosedViews t1 s1` holds. -/
theorem closedViews_ignores_modes :
    ClosedViews t1 s1 ∧ LoanTreeInv t1 ∧ LoanTreeInv s1 ∧ t1.modeOf 1 = some .shared ∧
      s1.modeOf 1 = some .excl := by decide

/-- `ClosedViews` does not preserve the loan-tree invariant: `u2` satisfies it, `ClosedViews u2
cxDepthCounts` holds (only `A`'s depth changed), but `cxDepthCounts` violates `DepthCounts`. -/
theorem closedViews_does_not_preserve_loanTreeInv :
    LoanTreeInv u2 ∧ ClosedViews u2 cxDepthCounts ∧ ¬ LoanTreeInv cxDepthCounts := by decide

/-- `ClosedViews` does not preserve the parent-cell shape needed to end an outer view: `B` can be
ended in `s1`, and `ClosedViews s1 weExclChildLoaned` holds (the parent `A`'s cell changed from
`loaned 1` to `own 0 0`), but `B` can no longer be ended. -/
theorem closedViews_does_not_preserve_end_enabledness :
    (endRaw s1 1 (fun _ => 0)).isSome = true ∧ ClosedViews s1 weExclChildLoaned ∧
      endRaw weExclChildLoaned 1 (fun _ => 0) = none := by decide

end Ex
end Toy.Views
