import ToyViews.Frame

/-!
# Proof lemmas for Result 2

Auxiliary lemmas used only inside the proofs of `ToyViews.EndSafe`: the raw end of a view under
return authority preserves the five tree-local laws and resurrects nothing (R2a), the local return
check implies return authority (R2d), and the seven loan-tree laws imply write exclusivity (R2b).
No definition is introduced here.
-/

namespace Toy.Views.ProofLemmas

open Toy.Views
open Toy.Views.Ex

/-! ## R2a: preservation of the five local laws and no-resurrection -/

theorem view?_isSome_of_lt_size {s : State} {u : ViewId} (hu : u < s.size) :
    ∃ vw, s.view? u = some vw := by
  unfold State.view?
  unfold State.size at hu
  exact ⟨s.views[u]'hu, List.getElem?_eq_getElem hu⟩


theorem restoreCells_at_uncovered {vc vp : View} (r : Addr → Byte) {a : Addr}
    (huncov : vc.cell? a = none) :
    (restoreCells vc vp r).cell? a = vp.cell? a := by
  unfold restoreCells
  rw [cell?_mapCells]
  rcases Nat.lt_or_ge a (max vp.cells.length vc.cells.length) with ha | ha
  · simp [ha, huncov]
  · have hnot : ¬ a < max vp.cells.length vc.cells.length := Nat.not_lt.mpr ha
    simp only [hnot, ↓reduceIte]
    have hpge : vp.cells.length ≤ a := Nat.le_trans (Nat.le_max_left _ _) ha
    rw [cell?_eq_none_of_ge hpge]

theorem restoreCells_at_covered_excl {vc vp : View} (r : Addr → Byte) {a : Addr}
    (hcov : (vc.cell? a).isSome = true) (hm : vc.mode = .excl) :
    (restoreCells vc vp r).cell? a = some (.own 0 (r a)) := by
  have ha : a < max vp.cells.length vc.cells.length :=
    Nat.lt_of_lt_of_le (lt_length_of_cell?_isSome hcov) (Nat.le_max_right _ _)
  unfold restoreCells
  rw [cell?_mapCells]
  simp only [ha, ↓reduceIte]
  cases hca : vc.cell? a with
  | none => rw [hca] at hcov; simp at hcov
  | some _ => simp [hm]

theorem restoreCells_at_covered_shared {vc vp : View} (r : Addr → Byte) {a : Addr} {d : Nat} {b : Byte}
    (hcov : (vc.cell? a).isSome = true) (hm : vc.mode = .shared)
    (hpa : vp.cell? a = some (.own (d + 1) b)) :
    (restoreCells vc vp r).cell? a = some (.own d b) := by
  have ha : a < max vp.cells.length vc.cells.length :=
    Nat.lt_of_lt_of_le (lt_length_of_cell?_isSome hcov) (Nat.le_max_right _ _)
  unfold restoreCells
  rw [cell?_mapCells]
  simp only [ha, ↓reduceIte]
  cases hca : vc.cell? a with
  | none => rw [hca] at hcov; simp at hcov
  | some _ => simp [hm, hpa]

theorem range_nodup_check : ∀ (n : Nat), (List.range n).Nodup
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.nodup_append]
    refine ⟨range_nodup_check n, by simp, ?_⟩
    intro x hx y hy hxy
    subst hxy
    simp only [List.mem_singleton] at hy
    subst hy
    have := List.mem_range.mp hx
    omega

theorem filter_length_eq_of_eq {l : List Nat} {P Q : Nat → Bool}
    (h : ∀ x ∈ l, P x = Q x) :
    (l.filter P).length = (l.filter Q).length := by
  have hfeq : l.filter P = l.filter Q := by
    induction l with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.filter_cons, h x (List.mem_cons_self ..),
        ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
  rw [hfeq]

theorem filter_length_erase_one {l : List Nat} {P Q : Nat → Bool} {c : Nat}
    (hnodup : l.Nodup) (hc : c ∈ l) (hPc : P c = true) (hQc : Q c = false)
    (heq : ∀ x ∈ l, x ≠ c → P x = Q x) :
    (l.filter P).length = (l.filter Q).length + 1 := by
  induction l with
  | nil => cases hc
  | cons x xs ih =>
    obtain ⟨hx_nin, hxs_nd⟩ := List.nodup_cons.mp hnodup
    rcases List.mem_cons.mp hc with rfl | hc_xs
    · simp only [List.filter_cons, hPc, hQc, ↓reduceIte, Bool.false_eq_true, List.length_cons]
      have hrest : (xs.filter P).length = (xs.filter Q).length := by
        apply filter_length_eq_of_eq
        intro y hy
        exact heq y (List.mem_cons_of_mem _ hy) (fun e => hx_nin (e ▸ hy))
      omega
    · have hxc : x ≠ c := fun e => hx_nin (e ▸ hc_xs)
      have hxPQ : P x = Q x := heq x (List.mem_cons_self ..) hxc
      have ih' := ih hxs_nd hc_xs (fun y hy hne => heq y (List.mem_cons_of_mem _ hy) hne)
      simp only [List.filter_cons, hxPQ]
      split <;> simp [ih']

theorem filter_length_two_le {l : List Nat} {P : Nat → Bool} {c₁ c₂ : Nat}
    (hnodup : l.Nodup) (h1 : c₁ ∈ l) (h2 : c₂ ∈ l) (hne : c₁ ≠ c₂)
    (hP1 : P c₁ = true) (hP2 : P c₂ = true) :
    2 ≤ (l.filter P).length := by
  let Q : Nat → Bool := fun x => P x && decide (x ≠ c₁)
  have hlen := filter_length_erase_one (P := P) (Q := Q) hnodup h1 hP1 (by simp [Q]) (by
    intro x _ hx; simp [Q, hx])
  have hc2_mem : c₂ ∈ l.filter Q := by
    rw [List.mem_filter]
    exact ⟨h2, by simp [Q, hP2, Ne.symm hne]⟩
  have hpos : 1 ≤ (l.filter Q).length := List.length_pos_of_mem hc2_mem
  omega

theorem properDesc_first_child {s : State} {d u : ViewId} {a : Addr}
    (hpc : ParentCoversActive s) (hd : ProperDesc s d u)
    (hact : s.isActive d = true) (hcov : s.covers d a = true) :
    ∃ w, s.parentOf w = some u ∧ s.isActive w = true ∧ s.covers w a = true ∧
      (d = w ∨ ProperDesc s d w) := by
  induction hd with
  | @child d u hp =>
    exact ⟨d, hp, hact, hcov, Or.inl rfl⟩
  | @step d x u hp _ ih =>
    have hd_lt : d < s.size := State.isActive_lt_size hact
    have ha_lt : a < s.width := State.covers_lt_width hcov
    have ⟨hact_x, hcov_x⟩ := hpc d hd_lt a ha_lt x hp hact hcov
    obtain ⟨w, hpw, hact_w, hcov_w, hdw⟩ := ih hact_x hcov_x
    refine ⟨w, hpw, hact_w, hcov_w, Or.inr ?_⟩
    rcases hdw with rfl | hxw
    · exact .child hp
    · exact .step hp hxw

theorem properDesc_congr_parentOf {s s' : State}
    (hpar : ∀ v, s'.parentOf v = s.parentOf v) {d u : ViewId} :
    ProperDesc s' d u ↔ ProperDesc s d u := by
  constructor
  · intro h; induction h with
    | child hp => rw [hpar] at hp; exact .child hp
    | step hp _ ih => rw [hpar] at hp; exact .step hp ih
  · intro h; induction h with
    | child hp => rw [← hpar] at hp; exact .child hp
    | step hp _ ih => rw [← hpar] at hp; exact .step hp ih

/-- `endRaw` under `ReturnAuthority` preserves all five tree-local laws and establishes
`NoResurrection`, without `ParentLt` and without `RootsDisjoint`. -/
theorem endRaw_preserves_localLoanLaws_and_noResurrection
    {s s' : State} {c : ViewId} {r : Addr → Byte}
    (hlaws : LocalLoanLaws s) (hauth : ReturnAuthority s c)
    (hend : endRaw s c r = some s') :
    LocalLoanLaws s' ∧ NoResurrection s s' := by
  obtain ⟨vc, p, vp, vc₁, hvc, hp_eq, hvp, hvc_act, hret, _, hs'_eq⟩ := endRaw_unpack hend
  have hc_lt : c < s.size := State.lt_size_of_view?_eq_some hvc
  have hp_lt : p < s.size := State.lt_size_of_view?_eq_some hvp
  have hc_par : s.parentOf c = some p := by unfold State.parentOf; rw [hvc]; exact hp_eq
  have hc_act : s.isActive c = true := by unfold State.isActive; rw [hvc]; exact hvc_act
  have hc_mode : s.modeOf c = some vc.mode := by unfold State.modeOf; rw [hvc]; rfl
  -- Cell lookup in `s'` for any view `v ≠ c`:
  have hcell_ne_c : ∀ v, v ≠ c → ∀ a,
      s'.cell? v a = (if v = p then (restoreCells vc vp r).cell? a else s.cell? v a) := by
    intro v hne a
    have hc_set : c < (s.setView p (restoreCells vc vp r)).size := by rw [setView_size]; exact hc_lt
    rw [hs'_eq]
    unfold State.cell?
    rw [view?_setView _ c v _ hc_set]
    simp only [hne, ↓reduceIte]
    rw [view?_setView _ p v _ hp_lt]
    by_cases hvp_eq : v = p
    · subst hvp_eq; simp
    · simp [hvp_eq]
  have hs_cell_p : ∀ a, s.cell? p a = vp.cell? a := by
    intro a; unfold State.cell?; rw [hvp]; rfl
  have hcov_c_iff : ∀ a, s.covers c a = (vc.cell? a).isSome := by
    intro a; unfold State.covers State.cell?; rw [hvc]; rfl
  -- Active shared children relation between `s` and `s'`:
  let pred (st : State) (v : ViewId) (a : Addr) : ViewId → Bool := fun w =>
    st.parentOf w == some v && st.isActive w && st.modeOf w == some .shared && st.covers w a
  have hcount_unchanged : ∀ v a, (v ≠ p ∨ vc.mode ≠ .shared ∨ s.covers c a = false) →
      s'.activeSharedChildren v a = s.activeSharedChildren v a := by
    intro v a hcase
    unfold State.activeSharedChildren
    rw [endRaw_size hend]
    apply filter_length_eq_of_eq
    intro w _
    simp only [endRaw_parentOf hend w, endRaw_modeOf hend w, endRaw_covers hend w a,
      endRaw_isActive hend w]
    by_cases hwc : w = c
    · subst hwc
      simp only [↓reduceIte, Bool.and_false, Bool.false_and]
      rcases hcase with hvp_ne | hm_ne | huncov
      · have hne : (s.parentOf w == some v) = false := by
          rw [hc_par]; simp [Ne.symm hvp_ne]
        simp [hne]
      · have hne : (s.modeOf w == some .shared) = false := by
          rw [hc_mode]; simp [hm_ne]
        simp [hne]
      · simp [huncov]
    · simp [hwc]
  have hcount_decr : ∀ a, vc.mode = .shared → s.covers c a = true →
      s.activeSharedChildren p a = s'.activeSharedChildren p a + 1 := by
    intro a hm hcov_ca
    unfold State.activeSharedChildren
    rw [endRaw_size hend]
    apply filter_length_erase_one (range_nodup_check s.size) (List.mem_range.mpr hc_lt)
    · simp [hc_par, hc_act, hc_mode, hm, hcov_ca]
    · simp [endRaw_isActive hend c]
    · intro w _ hne
      simp [endRaw_parentOf hend w, endRaw_modeOf hend w, endRaw_covers hend w a,
        endRaw_isActive hend w, hne]
  -- 1. `ParentCoversActive s'`
  have h_pca : ParentCoversActive s' := by
    intro v _ a _ q hpq hactv hcovv
    rw [endRaw_parentOf hend v] at hpq
    rw [endRaw_covers hend v a] at hcovv
    rw [endRaw_covers hend q a]
    rw [endRaw_isActive hend v] at hactv
    have hvc_ne : v ≠ c := by intro e; subst e; simp at hactv
    simp only [hvc_ne, ↓reduceIte] at hactv
    have ⟨hactq, hcovq⟩ := hlaws.parentCoversActive v (State.isActive_lt_size hactv)
      a (State.covers_lt_width hcovv) q hpq hactv hcovv
    refine ⟨?_, hcovq⟩
    rw [endRaw_isActive hend q]
    have hqc_ne : q ≠ c := by
      intro e; subst e
      have hbad := hauth v (.child hpq) hactv a hcovq
      rw [hcovv] at hbad; cases hbad
    simp [hqc_ne, hactq]
  -- 2. `SharedChildrenShared s'`
  have h_scs : SharedChildrenShared s' := by
    intro d _ q hpq hactd hmq
    rw [endRaw_parentOf hend d] at hpq
    rw [endRaw_modeOf hend q] at hmq
    rw [endRaw_modeOf hend d]
    rw [endRaw_isActive hend d] at hactd
    have hdc_ne : d ≠ c := by intro e; subst e; simp at hactd
    simp only [hdc_ne, ↓reduceIte] at hactd
    exact hlaws.sharedChildrenShared d (State.isActive_lt_size hactd) q hpq hactd hmq
  -- 3. `ExclChildLoaned s'`
  have h_ecl : ExclChildLoaned s' := by
    intro d _ a _ q hpq hactd hmd hcovd
    rw [endRaw_parentOf hend d] at hpq
    rw [endRaw_modeOf hend d] at hmd
    rw [endRaw_covers hend d a] at hcovd
    rw [endRaw_isActive hend d] at hactd
    have hdc_ne : d ≠ c := by intro e; subst e; simp at hactd
    simp only [hdc_ne, ↓reduceIte] at hactd
    have hactq : s'.isActive q = true :=
      (h_pca d (by rw [endRaw_size hend]; exact State.isActive_lt_size hactd)
        a (State.covers_lt_width (by rw [endRaw_covers hend d a]; exact hcovd))
        q (by rw [endRaw_parentOf hend d]; exact hpq)
        (by rw [endRaw_isActive hend d]; simp [hdc_ne, hactd])
        (by rw [endRaw_covers hend d a]; exact hcovd)).1
    have hqc_ne : q ≠ c := by rw [endRaw_isActive hend q] at hactq; intro e; subst e; simp at hactq
    have hloan_s := hlaws.exclChildLoaned d (State.isActive_lt_size hactd)
      a (State.covers_lt_width hcovd) q hpq hactd hmd hcovd
    rw [hcell_ne_c q hqc_ne a]
    by_cases hqp : q = p
    · subst hqp
      simp only [↓reduceIte]
      cases hca : vc.cell? a with
      | none => rw [restoreCells_at_uncovered r hca, ← hs_cell_p a]; exact hloan_s
      | some _ =>
        have hcov_ca : (vc.cell? a).isSome = true := by simp [hca]
        rcases returnable_spec hret hcov_ca with ⟨_, hpa⟩ | ⟨_, k, b, hpa, -⟩
        · rw [hs_cell_p a] at hloan_s; rw [hloan_s] at hpa
          simp only [Option.some.injEq, Cell.loaned.injEq] at hpa
          exact absurd hpa hdc_ne
        · rw [hs_cell_p a] at hloan_s; rw [hloan_s] at hpa; cases hpa
    · simp [hqp, hloan_s]
  -- 4. `SharedChildBelowOwn s'`
  have h_scb : SharedChildBelowOwn s' := by
    intro d _ a _ q hpq hactd hmd hcovd
    rw [endRaw_parentOf hend d] at hpq
    rw [endRaw_modeOf hend d] at hmd
    rw [endRaw_covers hend d a] at hcovd
    rw [endRaw_isActive hend d] at hactd
    have hdc_ne : d ≠ c := by intro e; subst e; simp at hactd
    simp only [hdc_ne, ↓reduceIte] at hactd
    have hactq' : s'.isActive q = true :=
      (h_pca d (by rw [endRaw_size hend]; exact State.isActive_lt_size hactd)
        a (State.covers_lt_width (by rw [endRaw_covers hend d a]; exact hcovd))
        q (by rw [endRaw_parentOf hend d]; exact hpq)
        (by rw [endRaw_isActive hend d]; simp [hdc_ne, hactd])
        (by rw [endRaw_covers hend d a]; exact hcovd)).1
    have hqc_ne : q ≠ c := by rw [endRaw_isActive hend q] at hactq'; intro e; subst e; simp at hactq'
    have ⟨k, hk⟩ := hlaws.sharedChildBelowOwn d (State.isActive_lt_size hactd)
      a (State.covers_lt_width hcovd) q hpq hactd hmd hcovd
    unfold State.depth?
    rw [hcell_ne_c q hqc_ne a]
    by_cases hqp : q = p
    · subst hqp
      simp only [↓reduceIte]
      cases hca : vc.cell? a with
      | none =>
        rw [restoreCells_at_uncovered r hca, ← hs_cell_p a]
        exact ⟨k, hk⟩
      | some _ =>
        have hcov_ca : (vc.cell? a).isSome = true := by simp [hca]
        rcases returnable_spec hret hcov_ca with ⟨_, hpa⟩ | ⟨hmc, k', b, hpa, -⟩
        · unfold State.depth? at hk; rw [hs_cell_p a, hpa] at hk; cases hk
        · rw [restoreCells_at_covered_shared r hcov_ca hmc hpa]
          -- Both `c` and `d` (`d ≠ c`) are active shared children of `q` covering `a` in `s`:
          have hcov_ca_s : s.covers c a = true := by rw [hcov_c_iff]; exact hcov_ca
          have h2 : 2 ≤ s.activeSharedChildren q a := by
            unfold State.activeSharedChildren
            exact filter_length_two_le (range_nodup_check s.size)
              (List.mem_range.mpr hc_lt)
              (List.mem_range.mpr (State.isActive_lt_size hactd))
              hdc_ne.symm
              (by simp [hc_par, hc_act, hc_mode, hmc, hcov_ca_s])
              (by simp [hpq, hactd, hmd, hcovd])
          have hactq_s : s.isActive q = true :=
            (hlaws.parentCoversActive d (State.isActive_lt_size hactd)
              a (State.covers_lt_width hcovd) q hpq hactd hcovd).1
          have hdep_p : s.depth? q a = some (k' + 1) := by
            unfold State.depth?; rw [hs_cell_p a, hpa]; rfl
          have hdc_eq := hlaws.depthCounts q (State.isActive_lt_size hactq_s)
            a (State.covers_lt_width hcov_ca_s) (k' + 1) hdep_p hactq_s
          have hk'_pos : 1 ≤ k' := by omega
          exact ⟨k' - 1, by simp [Cell.depth?]; omega⟩
    · simp only [hqp, ↓reduceIte]
      exact ⟨k, hk⟩
  -- 5. `DepthCounts s'`
  have h_dc : DepthCounts s' := by
    intro v _ a _ d' hd' hactv'
    have hactv_rw := hactv'
    rw [endRaw_isActive hend v] at hactv_rw
    have hvc_ne : v ≠ c := by intro e; subst e; simp at hactv_rw
    simp only [hvc_ne, ↓reduceIte] at hactv_rw
    rw [endRaw_baselineOf hend v]
    unfold State.depth? at hd'
    rw [hcell_ne_c v hvc_ne a] at hd'
    by_cases hvp_eq : v = p
    · subst hvp_eq
      simp only [↓reduceIte] at hd'
      cases hca : vc.cell? a with
      | none =>
        rw [restoreCells_at_uncovered r hca, ← hs_cell_p a] at hd'
        have hcov_va : s.covers v a = true := by
          unfold State.covers; cases hcv : s.cell? v a with
          | none => rw [hcv] at hd'; simp at hd'
          | some _ => rfl
        have hcnt := hcount_unchanged v a (Or.inr (Or.inr (by rw [hcov_c_iff, hca]; rfl)))
        rw [hcnt]
        exact hlaws.depthCounts v (State.isActive_lt_size hactv_rw)
          a (State.covers_lt_width hcov_va) d' hd' hactv_rw
      | some _ =>
        have hcov_ca : (vc.cell? a).isSome = true := by simp [hca]
        have hcov_ca_s : s.covers c a = true := by rw [hcov_c_iff]; exact hcov_ca
        rcases returnable_spec hret hcov_ca with ⟨hmc, hpa⟩ | ⟨hmc, k, b, hpa, -⟩
        · rw [restoreCells_at_covered_excl r hcov_ca hmc] at hd'
          simp only [Option.bind_some, Cell.depth?, Option.some.injEq] at hd'
          subst hd'
          -- `v` cannot be shared-mode (`SharedChildrenShared` on `c`):
          have hbase0 : s.baselineOf v = 0 := by
            unfold State.baselineOf State.modeOf
            rw [hvp]
            cases hmp : vp.mode with
            | excl => simp [hmp, Mode.baseline]
            | shared =>
              have hcs := hlaws.sharedChildrenShared c hc_lt v hc_par hc_act
                (by unfold State.modeOf; simp [hvp, hmp])
              rw [hc_mode, hmc] at hcs; cases hcs
          -- `v` has zero active shared children on `a` in `s'` (else `SharedChildBelowOwn` in `s` contradicts `.loaned c`):
          have hcnt0 : s'.activeSharedChildren v a = 0 := by
            rw [hcount_unchanged v a (Or.inr (Or.inl (by simp [hmc])))]
            unfold State.activeSharedChildren
            rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
            intro w hw
            simp only [Bool.and_eq_true, beq_iff_eq]
            rintro ⟨⟨⟨hpw, hactw⟩, hmw⟩, hcovw⟩
            have ⟨k0, hk0⟩ := hlaws.sharedChildBelowOwn w (List.mem_range.mp hw)
              a (State.covers_lt_width hcovw) v hpw hactw hmw hcovw
            unfold State.depth? at hk0
            rw [hs_cell_p a, hpa] at hk0; cases hk0
          omega
        · rw [restoreCells_at_covered_shared r hcov_ca hmc hpa] at hd'
          simp only [Option.bind_some, Cell.depth?, Option.some.injEq] at hd'
          subst hd'
          have hdep_s : s.depth? v a = some (k + 1) := by
            unfold State.depth?; rw [hs_cell_p a, hpa]; rfl
          have hcov_va : s.covers v a = true := by
            unfold State.covers; rw [hs_cell_p a, hpa]; rfl
          have hdc_s := hlaws.depthCounts v (State.isActive_lt_size hactv_rw)
            a (State.covers_lt_width hcov_va) (k + 1) hdep_s hactv_rw
          have hdecr := hcount_decr a hmc hcov_ca_s
          omega
    · simp only [hvp_eq, ↓reduceIte] at hd'
      have hcov_va : s.covers v a = true := by
        unfold State.covers; cases hcv : s.cell? v a with
        | none => rw [hcv] at hd'; simp at hd'
        | some _ => rfl
      rw [hcount_unchanged v a (Or.inl hvp_eq)]
      exact hlaws.depthCounts v (State.isActive_lt_size hactv_rw)
        a (State.covers_lt_width hcov_va) d' hd' hactv_rw
  -- 6. `NoResurrection s s'`
  have h_nr : NoResurrection s s' := by
    intro u _ a _ hlv d hd' hactd'
    have hpos : 0 < s'.level u a := Nat.lt_of_le_of_lt (Nat.zero_le _) hlv
    have hactu' : s'.isActive u = true := by
      unfold State.level State.canWrite State.canRead at hpos
      cases h1 : s'.isActive u with
      | false => simp [h1] at hpos
      | true => rfl
    have huc_ne : u ≠ c := by rw [endRaw_isActive hend u] at hactu'; intro e; subst e; simp at hactu'
    have hdc_ne : d ≠ c := by rw [endRaw_isActive hend d] at hactd'; intro e; subst e; simp at hactd'
    have hactu_s : s.isActive u = true := by
      have h := hactu'; rw [endRaw_isActive hend u] at h; simp [huc_ne] at h; exact h
    have hactd_s : s.isActive d = true := by
      have h := hactd'; rw [endRaw_isActive hend d] at h; simp [hdc_ne] at h; exact h
    -- If `u ≠ p` or `vc.cell? a = none`, `u`'s cell and activity are unchanged, contradicting `hlv`:
    have hlevel_unchanged : s'.cell? u a = s.cell? u a → False := by
      intro hceq
      have hdeq : s'.depth? u a = s.depth? u a := by unfold State.depth?; rw [hceq]
      have hweq : s'.canWrite u a = s.canWrite u a := by
        unfold State.canWrite; rw [hactu', hactu_s, hdeq]
      have hreq : s'.canRead u a = s.canRead u a := by
        unfold State.canRead; rw [hactu', hactu_s, hdeq]
      have hleq : s'.level u a = s.level u a := by
        unfold State.level; rw [hweq, hreq]
      omega
    by_cases hup : u = p
    · subst hup
      cases hca : vc.cell? a with
      | none =>
        exfalso; apply hlevel_unchanged
        rw [hcell_ne_c u huc_ne a]; simp [restoreCells_at_uncovered r hca, hs_cell_p a]
      | some _ =>
        have hcov_ca : (vc.cell? a).isSome = true := by simp [hca]
        have hcov_ca_s : s.covers c a = true := by rw [hcov_c_iff]; exact hcov_ca
        cases hcovd' : s'.covers d a with
        | false => rfl
        | true =>
          exfalso
          have hcovd_s : s.covers d a = true := by rw [← endRaw_covers hend d a]; exact hcovd'
          have hd_s : ProperDesc s d u :=
            (properDesc_congr_parentOf (endRaw_parentOf hend)).mp hd'
          obtain ⟨w, hpw, hactw, hcovw, hdw⟩ :=
            properDesc_first_child hlaws.parentCoversActive hd_s hactd_s hcovd_s
          by_cases hwc : w = c
          · subst hwc
            rcases hdw with rfl | hdc_desc
            · exact hdc_ne rfl
            · have hbad := hauth d hdc_desc hactd_s a hcov_ca_s
              rw [hcovd_s] at hbad; cases hbad
          · -- `w ≠ c` is another active direct child of `u` covering `a` in `s`:
            rcases returnable_spec hret hcov_ca with ⟨_, hpa⟩ | ⟨hmc, k, b, hpa, -⟩
            · -- `c` is exclusive (`u` holds `.loaned c`):
              cases hmw : s.modeOf w with
              | none =>
                obtain ⟨vw_w, hvw_w⟩ := view?_isSome_of_lt_size (State.isActive_lt_size hactw)
                unfold State.modeOf at hmw; rw [hvw_w] at hmw; cases hmw
              | some mw =>
                cases mw with
                | excl =>
                  have hl_w := hlaws.exclChildLoaned w (State.isActive_lt_size hactw)
                    a (State.covers_lt_width hcovw) u hpw hactw hmw hcovw
                  rw [hs_cell_p a, hpa] at hl_w
                  simp only [Option.some.injEq, Cell.loaned.injEq] at hl_w
                  exact hwc hl_w.symm
                | shared =>
                  have ⟨k0, hk0⟩ := hlaws.sharedChildBelowOwn w (State.isActive_lt_size hactw)
                    a (State.covers_lt_width hcovw) u hpw hactw hmw hcovw
                  unfold State.depth? at hk0; rw [hs_cell_p a, hpa] at hk0; cases hk0
            · -- `c` is shared (`u` holds `own (k + 1) b`, so `s.level u a ≥ 1`, forcing `k = 0`):
              have hcell_s : s.cell? u a = some (.own (k + 1) b) := by rw [hs_cell_p a, hpa]
              have hcell_s' : s'.cell? u a = some (.own k b) := by
                rw [hcell_ne_c u huc_ne a]
                simp [restoreCells_at_covered_shared r hcov_ca hmc hpa]
              have hk0 : k = 0 := by
                rcases k with _ | k'
                · rfl
                · have hlv_s : s.level u a = 1 := by
                    unfold State.level State.canWrite State.canRead State.depth?
                    simp [hactu_s, hcell_s, Cell.depth?]
                  have hlv_s' : s'.level u a = 1 := by
                    unfold State.level State.canWrite State.canRead State.depth?
                    simp [hactu', hcell_s', Cell.depth?]
                  omega
              subst hk0
              cases hmw : s.modeOf w with
              | none =>
                obtain ⟨vw_w, hvw_w⟩ := view?_isSome_of_lt_size (State.isActive_lt_size hactw)
                unfold State.modeOf at hmw; rw [hvw_w] at hmw; cases hmw
              | some mw =>
                cases mw with
                | excl =>
                  have hl_w := hlaws.exclChildLoaned w (State.isActive_lt_size hactw)
                    a (State.covers_lt_width hcovw) u hpw hactw hmw hcovw
                  rw [hcell_s] at hl_w; cases hl_w
                | shared =>
                  have h2 : 2 ≤ s.activeSharedChildren u a := by
                    unfold State.activeSharedChildren
                    exact filter_length_two_le (range_nodup_check s.size)
                      (List.mem_range.mpr hc_lt)
                      (List.mem_range.mpr (State.isActive_lt_size hactw))
                      (Ne.symm hwc)
                      (by simp [hc_par, hc_act, hc_mode, hmc, hcov_ca_s])
                      (by simp [hpw, hactw, hmw, hcovw])
                  have hdep_u : s.depth? u a = some 1 := by
                    unfold State.depth?; rw [hcell_s]; rfl
                  have hdc_u := hlaws.depthCounts u (State.isActive_lt_size hactu_s)
                    a (State.covers_lt_width hcov_ca_s) 1 hdep_u hactu_s
                  omega
    · exfalso; apply hlevel_unchanged
      rw [hcell_ne_c u huc_ne a]; simp [hup]
  exact ⟨⟨h_pca, h_ecl, h_scb, h_scs, h_dc⟩, h_nr⟩


/-! ## R2d: the local return check implies return authority -/

theorem activeSharedChildren_pos {s : State} {v w : ViewId} {a : Addr} (hw : w < s.size)
    (hp : s.parentOf w = some v) (hact : s.isActive w = true) (hm : s.modeOf w = some .shared)
    (hcov : s.covers w a = true) : 0 < s.activeSharedChildren v a := by
  unfold State.activeSharedChildren
  apply List.length_pos_of_mem (a := w)
  rw [List.mem_filter, List.mem_range]
  exact ⟨hw, by simp [hp, hact, hm, hcov]⟩

theorem returnAuthority_of_localReturnCheck_proved {s : State} {c : ViewId}
    (hpc : ParentCoversActive s) (hecl : ExclChildLoaned s) (hdc : DepthCounts s)
    (hloc : LocalReturnCheck s c) : ReturnAuthority s c := by
  intro d hd hact a hcovc
  cases hcd : s.covers d a with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨w, hpw, hactw, hcovw, _⟩ := properDesc_first_child hpc hd hact hcd
    have hw : w < s.size := State.isActive_lt_size hactw
    have ha : a < s.width := State.covers_lt_width hcovw
    have ⟨hactc, _⟩ := hpc w hw a ha c hpw hactw hcovw
    have hc : c < s.size := State.isActive_lt_size hactc
    have hdepth := hloc a ha hcovc
    obtain ⟨vw, hvw⟩ := view?_isSome_of_lt_size hw
    have hmode : s.modeOf w = some vw.mode := by unfold State.modeOf; rw [hvw]; rfl
    cases hm : vw.mode with
    | excl =>
      rw [hm] at hmode
      have hl := hecl w hw a ha c hpw hactw hmode hcovw
      unfold State.depth? at hdepth
      rw [hl] at hdepth
      simp [Cell.depth?] at hdepth
    | shared =>
      rw [hm] at hmode
      have hpos := activeSharedChildren_pos hw hpw hactw hmode hcovw
      have heq := hdc c hc a ha _ hdepth hactc
      omega

/-! ## R2b: the seven loan-tree laws imply write exclusivity -/

theorem covers_of_depth?_eq_some {s : State} {v : ViewId} {a d : Nat}
    (hd : s.depth? v a = some d) : s.covers v a = true := by
  unfold State.covers
  unfold State.depth? at hd
  cases hc : s.cell? v a with
  | none => rw [hc] at hd; simp at hd
  | some _ => rfl

/-- Every active view covering `a` has an active root ancestor covering `a`. -/
theorem exists_root_ancestor {s : State} (hlt : ParentLt s) (hpc : ParentCoversActive s)
    {a : Addr} :
    ∀ u, s.isActive u = true → s.covers u a = true →
      ∃ r, s.parentOf r = none ∧ s.isActive r = true ∧ s.covers r a = true ∧
        (u = r ∨ ProperDesc s u r) := by
  intro u
  induction u using Nat.strongRecOn with
  | ind u ih =>
    intro hact hcov
    cases hp : s.parentOf u with
    | none => exact ⟨u, hp, hact, hcov, Or.inl rfl⟩
    | some p =>
      have hu_lt : u < s.size := State.isActive_lt_size hact
      have ha_lt : a < s.width := State.covers_lt_width hcov
      have hp_lt_u : p < u := hlt u hu_lt p hp
      have ⟨hact_p, hcov_p⟩ := hpc u hu_lt a ha_lt p hp hact hcov
      obtain ⟨r, hpr, hact_r, hcov_r, hdesc⟩ := ih p hp_lt_u hact_p hcov_p
      refine ⟨r, hpr, hact_r, hcov_r, Or.inr ?_⟩
      rcases hdesc with rfl | hpr_desc
      · exact .child hp
      · exact .step hp hpr_desc

/-- Along the ancestor chain of an active `.excl` view covering `a`, every ancestor is `.excl` and
its cell at `a` is `.loaned` to the direct child on that chain. -/
theorem excl_chain_to_ancestor {s : State}
    (hpc : ParentCoversActive s) (hecl : ExclChildLoaned s) (hscs : SharedChildrenShared s)
    {d u : ViewId} {a : Addr}
    (hdu : ProperDesc s d u) (hact : s.isActive d = true) (hm : s.modeOf d = some .excl)
    (hcov : s.covers d a = true) :
    s.modeOf u = some .excl ∧
    ∃ c, s.parentOf c = some u ∧ s.isActive c = true ∧ s.modeOf c = some .excl ∧
      s.covers c a = true ∧ s.cell? u a = some (.loaned c) ∧ (d = c ∨ ProperDesc s d c) := by
  induction hdu with
  | @child d u hp =>
    have hd_lt : d < s.size := State.isActive_lt_size hact
    have ha_lt : a < s.width := State.covers_lt_width hcov
    have ⟨hact_u, _⟩ := hpc d hd_lt a ha_lt u hp hact hcov
    have hu_lt : u < s.size := State.isActive_lt_size hact_u
    obtain ⟨vw_u, hvw_u⟩ := view?_isSome_of_lt_size hu_lt
    have hmu : s.modeOf u = some .excl := by
      have hm0 : s.modeOf u = some vw_u.mode := by unfold State.modeOf; rw [hvw_u]; rfl
      cases hmode : vw_u.mode with
      | excl => rw [hmode] at hm0; exact hm0
      | shared =>
        rw [hmode] at hm0
        have hbad := hscs d hd_lt u hp hact hm0
        rw [hm] at hbad; cases hbad
    have hloan := hecl d hd_lt a ha_lt u hp hact hm hcov
    exact ⟨hmu, d, hp, hact, hm, hcov, hloan, Or.inl rfl⟩
  | @step d x u hp _ ih =>
    have hd_lt : d < s.size := State.isActive_lt_size hact
    have ha_lt : a < s.width := State.covers_lt_width hcov
    have ⟨hact_x, hcov_x⟩ := hpc d hd_lt a ha_lt x hp hact hcov
    have hx_lt : x < s.size := State.isActive_lt_size hact_x
    obtain ⟨vw_x, hvw_x⟩ := view?_isSome_of_lt_size hx_lt
    have hmx : s.modeOf x = some .excl := by
      have hm0 : s.modeOf x = some vw_x.mode := by unfold State.modeOf; rw [hvw_x]; rfl
      cases hmode : vw_x.mode with
      | excl => rw [hmode] at hm0; exact hm0
      | shared =>
        rw [hmode] at hm0
        have hbad := hscs d hd_lt x hp hact hm0
        rw [hm] at hbad; cases hbad
    obtain ⟨hmu, c, hpc_eq, hact_c, hmc, hcov_c, hloan_c, hxc⟩ := ih hact_x hmx hcov_x
    refine ⟨hmu, c, hpc_eq, hact_c, hmc, hcov_c, hloan_c, ?_⟩
    rcases hxc with rfl | hxc_desc
    · exact Or.inr (.child hp)
    · exact Or.inr (.step hp hxc_desc)

/-- Given two distinct active descendants (or self) of a common ancestor `r` covering `a`, either
one is a proper descendant of the other, or they diverge at some ancestor `u` with distinct active
direct children `cv ≠ cw` covering `a`. -/
theorem ancestor_trichotomy {s : State} (hlt : ParentLt s) (hpc : ParentCoversActive s)
    {a : Addr} :
    ∀ u v w,
      v ≠ w →
      s.isActive v = true → s.covers v a = true →
      s.isActive w = true → s.covers w a = true →
      (v = u ∨ ProperDesc s v u) → (w = u ∨ ProperDesc s w u) →
      ProperDesc s v w ∨ ProperDesc s w v ∨
      ∃ lca cv cw, cv ≠ cw ∧
        s.parentOf cv = some lca ∧ s.isActive cv = true ∧ s.covers cv a = true ∧
          (v = cv ∨ ProperDesc s v cv) ∧
        s.parentOf cw = some lca ∧ s.isActive cw = true ∧ s.covers cw a = true ∧
          (w = cw ∨ ProperDesc s w cw) := by
  intro u v w hne hactv hcovv hactw hcovw hvu hwu
  suffices H : ∀ k u, s.size - u ≤ k →
      (v = u ∨ ProperDesc s v u) → (w = u ∨ ProperDesc s w u) →
      ProperDesc s v w ∨ ProperDesc s w v ∨
      ∃ lca cv cw, cv ≠ cw ∧
        s.parentOf cv = some lca ∧ s.isActive cv = true ∧ s.covers cv a = true ∧
          (v = cv ∨ ProperDesc s v cv) ∧
        s.parentOf cw = some lca ∧ s.isActive cw = true ∧ s.covers cw a = true ∧
          (w = cw ∨ ProperDesc s w cw) by
    exact H (s.size - u) u (Nat.le_refl _) hvu hwu
  intro k
  induction k with
  | zero =>
    intro u hk hvu hwu
    rcases hvu with rfl | hvu
    · rcases hwu with rfl | hwu
      · exact absurd rfl hne
      · exact Or.inr (Or.inl hwu)
    · rcases hwu with rfl | hwu
      · exact Or.inl hvu
      · obtain ⟨cv, hpcv, hactcv, _, _⟩ := properDesc_first_child hpc hvu hactv hcovv
        have hcv_lt : cv < s.size := State.isActive_lt_size hactcv
        have hu_lt_cv : u < cv := hlt cv hcv_lt u hpcv
        have hu_lt : (u : Nat) < s.size := Nat.lt_trans hu_lt_cv hcv_lt
        have hk0 : (s.size : Nat) - (u : Nat) ≤ 0 := hk
        omega
  | succ k ih =>
    intro u hk hvu hwu
    rcases hvu with rfl | hvu
    · rcases hwu with rfl | hwu
      · exact absurd rfl hne
      · exact Or.inr (Or.inl hwu)
    · rcases hwu with rfl | hwu
      · exact Or.inl hvu
      · obtain ⟨cv, hpcv, hactcv, hcovcv, hv_cv⟩ := properDesc_first_child hpc hvu hactv hcovv
        obtain ⟨cw, hpcw, hactcw, hcovcw, hw_cw⟩ := properDesc_first_child hpc hwu hactw hcovw
        by_cases hcc : cv = cw
        · subst hcc
          have hcv_lt : cv < s.size := State.isActive_lt_size hactcv
          have hu_lt_cv : u < cv := hlt cv hcv_lt u hpcv
          exact ih cv (by omega) hv_cv hw_cw
        · exact Or.inr (Or.inr ⟨u, cv, cw, hcc, hpcv, hactcv, hcovcv, hv_cv,
            hpcw, hactcw, hcovcw, hw_cw⟩)

theorem writeExclusive_of_loanTree_laws_proved {s : State}
    (hlt : ParentLt s) (hpc : ParentCoversActive s) (hecl : ExclChildLoaned s)
    (hscb : SharedChildBelowOwn s) (hscs : SharedChildrenShared s) (hdc : DepthCounts s)
    (hrd : RootsDisjoint s) :
    WriteExclusive s := by
  intro v hv w hw a ha hne hcw
  cases hcr : s.canRead w a with
  | false => rfl
  | true =>
    exfalso
    -- Unpack `canWrite v a = true`:
    unfold State.canWrite at hcw
    simp only [Bool.and_eq_true, beq_iff_eq] at hcw
    obtain ⟨hactv, hdepv⟩ := hcw
    have hcovv : s.covers v a = true := covers_of_depth?_eq_some hdepv
    have hdc_v := hdc v hv a ha 0 hdepv hactv
    obtain ⟨vw_v, hvw_v⟩ := view?_isSome_of_lt_size hv
    have hmv : s.modeOf v = some .excl := by
      unfold State.baselineOf at hdc_v
      unfold State.modeOf at hdc_v ⊢
      rw [hvw_v] at hdc_v ⊢
      cases hm : vw_v.mode with
      | excl => simp [hm]
      | shared => simp [hm, Mode.baseline] at hdc_v; omega
    have hcnt0 : s.activeSharedChildren v a = 0 := by
      unfold State.baselineOf at hdc_v
      rw [hmv] at hdc_v
      simp [Mode.baseline] at hdc_v
      omega
    -- Unpack `canRead w a = true`:
    unfold State.canRead at hcr
    simp only [Bool.and_eq_true] at hcr
    obtain ⟨hactw, hdepw_some⟩ := hcr
    obtain ⟨dw, hdepw⟩ := Option.isSome_iff_exists.mp hdepw_some
    have hcovw : s.covers w a = true := covers_of_depth?_eq_some hdepw
    -- Climb both `v` and `w` to their active roots covering `a`, which coincide by `RootsDisjoint`:
    obtain ⟨rv, hprv, hactrv, hcovrv, hv_rv⟩ := exists_root_ancestor hlt hpc v hactv hcovv
    obtain ⟨rw_, hprw, hactrw, hcovrw, hw_rw⟩ := exists_root_ancestor hlt hpc w hactw hcovw
    have hr_eq : rv = rw_ := by
      by_cases heq : rv = rw_
      · exact heq
      · exfalso
        have hbad := hrd rv (State.isActive_lt_size hactrv) rw_ (State.isActive_lt_size hactrw)
          a ha heq hactrv hactrw hprv hprw hcovrv
        rw [hcovrw] at hbad; cases hbad
    subst hr_eq
    rcases ancestor_trichotomy hlt hpc rv v w hne hactv hcovv hactw hcovw hv_rv hw_rw with
      hvw | hwv | ⟨lca, cv, cw, hcc, hpcv, hactcv, hcovcv, hv_cv, hpcw, hactcw, hcovcw, _⟩
    · -- Case 1: `ProperDesc s v w` (`w` is an ancestor of `v`, so `w`'s cell is `.loaned _`)
      obtain ⟨_, c, _, _, _, _, hloan_w, _⟩ := excl_chain_to_ancestor hpc hecl hscs hvw hactv hmv hcovv
      unfold State.depth? at hdepw
      rw [hloan_w] at hdepw
      simp [Cell.depth?] at hdepw
    · -- Case 2: `ProperDesc s w v` (`v` has an active direct child `c` covering `a`)
      obtain ⟨c, hpc_eq, hactc, hcovc, _⟩ := properDesc_first_child hpc hwv hactw hcovw
      have hc_lt : c < s.size := State.isActive_lt_size hactc
      obtain ⟨vw_c, hvw_c⟩ := view?_isSome_of_lt_size hc_lt
      have hmc0 : s.modeOf c = some vw_c.mode := by unfold State.modeOf; rw [hvw_c]; rfl
      cases hm : vw_c.mode with
      | excl =>
        rw [hm] at hmc0
        have hloan := hecl c hc_lt a ha v hpc_eq hactc hmc0 hcovc
        unfold State.depth? at hdepv
        rw [hloan] at hdepv
        simp [Cell.depth?] at hdepv
      | shared =>
        rw [hm] at hmc0
        have hpos := activeSharedChildren_pos hc_lt hpc_eq hactc hmc0 hcovc
        omega
    · -- Case 3: divergence at `lca` with distinct active children `cv ≠ cw` covering `a`
      have hmcv : s.modeOf cv = some .excl := by
        rcases hv_cv with rfl | hv_cv_desc
        · exact hmv
        · exact (excl_chain_to_ancestor hpc hecl hscs hv_cv_desc hactv hmv hcovv).1
      have hloan_cv := hecl cv (State.isActive_lt_size hactcv) a ha lca hpcv hactcv hmcv hcovcv
      have hcw_lt : cw < s.size := State.isActive_lt_size hactcw
      obtain ⟨vw_cw, hvw_cw⟩ := view?_isSome_of_lt_size hcw_lt
      have hmcw0 : s.modeOf cw = some vw_cw.mode := by unfold State.modeOf; rw [hvw_cw]; rfl
      cases hm : vw_cw.mode with
      | excl =>
        rw [hm] at hmcw0
        have hloan_cw := hecl cw hcw_lt a ha lca hpcw hactcw hmcw0 hcovcw
        rw [hloan_cv] at hloan_cw
        simp only [Option.some.injEq, Cell.loaned.injEq] at hloan_cw
        exact hcc hloan_cw
      | shared =>
        rw [hm] at hmcw0
        have ⟨d, hd⟩ := hscb cw hcw_lt a ha lca hpcw hactcw hmcw0 hcovcw
        unfold State.depth? at hd
        rw [hloan_cv] at hd
        simp [Cell.depth?] at hd


end Toy.Views.ProofLemmas
