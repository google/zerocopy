/-
  PoloniusTriadMemberConstraintsAndTwoPhaseSoundness.lean

  Self-contained, kernel-checked Lean 4 (v4.34.1) formalization of:
    1. The rustc_session / rustc_borrowck Polonius CLI triad
       (CFG_DEFAULT_POLONIUS_NEXT, Polonius::{Off, Next, Legacy}),
       localized loan reachability vs. location-insensitive universal-region
       checking (Off ⊊ Next ⊊ Legacy), operational safety, and Problem Case #3
       / flow_sensitive_invariance / time-travel separation witnesses.
    2. Edition 2021 vs. 2024 RPIT lifetime capturing (use<...>) and
       opaque_types/member_constraints.rs choice-set lattice minimization
       (apply_member_constraint soundness, minimality, E0700 incomparability,
       and diamond/ordered/'static resolution witnesses).
    3. TwoPhaseBorrow reservation-vs.-activation borrowck state machine
       (Unreserved -> Reserved -> Activated -> Released), inductive exclusivity
       preservation across arbitrary traces, and Tree Borrows unprotected
       Reserved vs. protected Reserved(conflicted) correspondence.

  Purity guarantees:
    - Zero imports beyond Lean Init (no Mathlib, no Anneal internal imports).
    - Zero `sorry`, zero `axiom`, zero `partial def`, zero `unsafe`.
    - Zero `omega`, zero `bv_decide`, zero `native_decide`.
    - Zero `deriving` clauses (eliminating `._unsafe_rec` compiler auxiliaries).
    - Zero `Classical.choice` across every declaration.
-/

namespace PoloniusTriadSoundness

/-! ## Part 0: Constructive Bool, Nat, and List Utilities -/

theorem boolAndTrue {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> cases h <;> exact ⟨rfl, rfl⟩

theorem mkBoolAndTrue {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  subst ha; subst hb; rfl

theorem boolOrTrue {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a <;> cases b <;> cases h
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

noncomputable def natEqb (a b : Nat) : Bool := Nat.beq a b

theorem natEqb_true_iff (a b : Nat) : natEqb a b = true ↔ a = b := by
  induction a generalizing b with
  | zero =>
      cases b
      · exact Iff.intro (fun _ => rfl) (fun _ => rfl)
      · exact Iff.intro (fun h => nomatch h) (fun h => nomatch h)
  | succ a ih =>
      cases b with
      | zero => exact Iff.intro (fun h => nomatch h) (fun h => nomatch h)
      | succ b =>
          constructor
          · intro h; exact congrArg Nat.succ ((ih b).mp h)
          · intro h; injection h with h'; exact (ih b).mpr h'

theorem natEqb_refl (a : Nat) : natEqb a a = true := by
  rw [natEqb_true_iff]

noncomputable def memNat (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => natEqb x y || memNat x ys

theorem memNat_true_iff (x : Nat) : ∀ (xs : List Nat), memNat x xs = true ↔ x ∈ xs
  | [] => by
      constructor
      · intro h; cases h
      · intro h; cases h
  | y :: ys => by
      unfold memNat
      constructor
      · intro h
        rcases boolOrTrue h with hxy | hys
        · have heq : x = y := (natEqb_true_iff x y).mp hxy
          subst heq
          exact List.Mem.head _
        · exact List.Mem.tail _ ((memNat_true_iff x ys).mp hys)
      · intro h
        cases h with
        | head =>
            rw [natEqb_refl]
            rfl
        | tail _ hmem =>
            have hys := (memNat_true_iff x ys).mpr hmem
            rw [hys]
            cases natEqb x y <;> rfl

noncomputable def allList {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && allList p xs

noncomputable def anyList {α : Type} (p : α → Bool) : List α → Bool
  | [] => false
  | x :: xs => p x || anyList p xs

noncomputable def filterList {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => if p x then x :: filterList p xs else filterList p xs

theorem allList_true_iff {α : Type} (p : α → Bool) :
    ∀ (xs : List α), allList p xs = true ↔ ∀ x, x ∈ xs → p x = true
  | [] => by
      constructor
      · intro _ x hx; cases hx
      · intro _; rfl
  | x :: xs => by
      constructor
      · intro h y hy
        obtain ⟨hx, hxs⟩ := boolAndTrue h
        cases hy with
        | head => exact hx
        | tail _ hmem => exact (allList_true_iff p xs).mp hxs y hmem
      · intro hall
        apply mkBoolAndTrue
        · exact hall x (List.Mem.head _)
        · rw [allList_true_iff p xs]
          intro y hy
          exact hall y (List.Mem.tail _ hy)

theorem anyList_true_iff {α : Type} (p : α → Bool) :
    ∀ (xs : List α), anyList p xs = true ↔ ∃ x, x ∈ xs ∧ p x = true
  | [] => by
      constructor
      · intro h; cases h
      · intro ⟨_, hmem, _⟩; cases hmem
  | x :: xs => by
      constructor
      · intro h
        rcases boolOrTrue h with hx | hxs
        · exact ⟨x, List.Mem.head _, hx⟩
        · obtain ⟨y, hy, hpy⟩ := (anyList_true_iff p xs).mp hxs
          exact ⟨y, List.Mem.tail _ hy, hpy⟩
      · intro ⟨y, hy, hpy⟩
        cases hy with
        | head =>
            unfold anyList
            rw [hpy]
            rfl
        | tail _ hmem =>
            have hxs : anyList p xs = true :=
              (anyList_true_iff p xs).mpr ⟨y, hmem, hpy⟩
            unfold anyList
            rw [hxs]
            cases p x <;> rfl

theorem mem_filterList_iff {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (x : α), x ∈ filterList p xs ↔ x ∈ xs ∧ p x = true
  | [], _ => by
      constructor
      · intro h; cases h
      · intro ⟨h, _⟩; cases h
  | y :: ys, x => by
      unfold filterList
      cases hpy : p y
      · simp only [Bool.false_eq_true, ↓reduceIte]
        constructor
        · intro hx
          obtain ⟨hxys, hpx⟩ := (mem_filterList_iff p ys x).mp hx
          exact ⟨List.Mem.tail _ hxys, hpx⟩
        · intro ⟨hxmem, hpx⟩
          cases hxmem with
          | head => rw [hpy] at hpx; cases hpx
          | tail _ hxys => exact (mem_filterList_iff p ys x).mpr ⟨hxys, hpx⟩
      · simp only [↓reduceIte]
        constructor
        · intro hx
          cases hx with
          | head => exact ⟨List.Mem.head _, hpy⟩
          | tail _ hrest =>
              obtain ⟨hxys, hpx⟩ := (mem_filterList_iff p ys x).mp hrest
              exact ⟨List.Mem.tail _ hxys, hpx⟩
        · intro ⟨hxmem, hpx⟩
          cases hxmem with
          | head => exact List.Mem.head _
          | tail _ hxys => exact List.Mem.tail _ ((mem_filterList_iff p ys x).mpr ⟨hxys, hpx⟩)

/-! ## Part I: Polonius CLI Triad and `Off ⊊ Next ⊊ Legacy` Hierarchy -/

inductive ChannelFlavor where
  | stable
  | nightly

inductive ToolchainEra where
  | pre199
  | post199

inductive PoloniusMode where
  | off
  | legacy
  | next

inductive RawPoloniusArg where
  | noneSpecified
  | bareZPolonius
  | valOff
  | valLegacy
  | valNext

/-- Channel-gated default corresponding to `Polonius::DEFAULT` in
    `compiler/rustc_session/src/config.rs` and `CFG_DEFAULT_POLONIUS_NEXT` in
    `src/bootstrap/src/core/build_steps/compile.rs`. -/
noncomputable def defaultPoloniusMode : ToolchainEra → ChannelFlavor → PoloniusMode
  | .pre199, _ => .off
  | .post199, .stable => .off
  | .post199, .nightly => .next

/-- CLI parsing corresponding to `parse_polonius` in
    `compiler/rustc_session/src/options.rs`:
    bare `-Zpolonius` selects `Polonius::Legacy`, `-Zpolonius=next` selects
    `Polonius::Next`, and `-Zpolonius=off` selects `Polonius::Off` (rejected pre-1.99). -/
noncomputable def parsePoloniusCli (era : ToolchainEra) (ch : ChannelFlavor) :
    RawPoloniusArg → Option PoloniusMode
  | .noneSpecified => some (defaultPoloniusMode era ch)
  | .bareZPolonius => some .legacy
  | .valLegacy => some .legacy
  | .valNext => some .next
  | .valOff =>
      match era with
      | .pre199 => none
      | .post199 => some .off

theorem cli_triad_exact_disambiguation :
    parsePoloniusCli .post199 .nightly .noneSpecified = some .next ∧
    parsePoloniusCli .post199 .nightly .bareZPolonius = some .legacy ∧
    parsePoloniusCli .post199 .nightly .valOff = some .off ∧
    parsePoloniusCli .post199 .nightly .valNext = some .next ∧
    parsePoloniusCli .post199 .nightly .valLegacy = some .legacy ∧
    parsePoloniusCli .post199 .stable .noneSpecified = some .off ∧
    parsePoloniusCli .pre199 .nightly .noneSpecified = some .off ∧
    parsePoloniusCli .pre199 .nightly .valOff = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem post199_nightly_off_matches_stable_default :
    parsePoloniusCli .post199 .nightly .valOff =
    parsePoloniusCli .post199 .stable .noneSpecified := rfl

theorem post199_nightly_bare_differs_from_default :
    parsePoloniusCli .post199 .nightly .bareZPolonius ≠
    parsePoloniusCli .post199 .nightly .noneSpecified := by
  intro h
  cases h

abbrev PointId := Nat
abbrev OriginId := Nat
abbrev LoanId := Nat

inductive VarianceDir where
  | fwd
  | bwd
  | bidir

noncomputable def VarianceDir.allowsFwd : VarianceDir → Bool
  | .fwd => true
  | .bwd => false
  | .bidir => true

noncomputable def VarianceDir.allowsBwd : VarianceDir → Bool
  | .fwd => false
  | .bwd => true
  | .bidir => true

inductive OutlivesScope where
  | single (pt : PointId)
  | allPts

structure LoanDecl where
  loan : LoanId
  origin : OriginId
  issuePt : PointId

structure OutlivesEdge where
  sup : OriginId
  sub : OriginId
  scope : OutlivesScope

structure ConflictSite where
  loan : LoanId
  pt : PointId

structure UnivPair where
  longer : OriginId
  shorter : OriginId

/-- Abstract borrow/region constraint system capturing both intraprocedural loans
    and universal-region outlives checks across NLL (`Off`), `Polonius::Next`,
    and `Polonius::Legacy`. -/
structure BorrowRegionSystem where
  entry : PointId
  cfgEdges : List (PointId × PointId)
  liveAt : OriginId → PointId → Bool
  dirOf : OriginId → VarianceDir
  loans : List LoanDecl
  outlives : List OutlivesEdge
  knownUnivOutlives : List (OriginId × OriginId)
  conflicts : List ConflictSite
  forbiddenUnivPairs : List UnivPair

/-- Location-insensitive NLL outlives closure (`ConstraintSccs` over all `Single`
    and `All` outlives edges plus `knownUnivOutlives`). -/
inductive NllSubset (sys : BorrowRegionSystem) : OriginId → OriginId → Prop where
  | refl (o : OriginId) : NllSubset sys o o
  | stepEdge {e : OutlivesEdge} :
      e ∈ sys.outlives → NllSubset sys e.sup e.sub
  | stepKnown {o1 o2 : OriginId} :
      (o1, o2) ∈ sys.knownUnivOutlives → NllSubset sys o1 o2
  | trans {o1 o2 o3 : OriginId} :
      NllSubset sys o1 o2 → NllSubset sys o2 o3 → NllSubset sys o1 o3

noncomputable def NllLoanLive (sys : BorrowRegionSystem) (l : LoanId) (p : PointId) : Prop :=
  ∃ ld o, ld ∈ sys.loans ∧ ld.loan = l ∧ NllSubset sys ld.origin o ∧ sys.liveAt o p = true

/-- `Polonius::Off` (location-insensitive NLL): rejects any conflict where the
    loan is NLL-live and rejects any forbidden universal pair in `NllSubset`. -/
noncomputable def OffAccepts (sys : BorrowRegionSystem) : Prop :=
  (∀ c, c ∈ sys.conflicts → ¬ NllLoanLive sys c.loan c.pt) ∧
  (∀ u, u ∈ sys.forbiddenUnivPairs → ¬ NllSubset sys u.longer u.shorter)

/-- Localized outlives graph reachability (`polonius/constraints.rs:100-240`). -/
inductive NextReach (sys : BorrowRegionSystem) (l : LoanId) :
    OriginId × PointId → Prop where
  | start {ld : LoanDecl} :
      ld ∈ sys.loans → ld.loan = l → NextReach sys l (ld.origin, ld.issuePt)
  | singleEdge {e : OutlivesEdge} {pt : PointId} :
      e ∈ sys.outlives → e.scope = .single pt →
      NextReach sys l (e.sup, pt) → NextReach sys l (e.sub, pt)
  | allEdge {e : OutlivesEdge} {pt : PointId} :
      e ∈ sys.outlives → e.scope = .allPts →
      NextReach sys l (e.sup, pt) → NextReach sys l (e.sub, pt)
  | knownEdge {o1 o2 : OriginId} {pt : PointId} :
      (o1, o2) ∈ sys.knownUnivOutlives →
      NextReach sys l (o1, pt) → NextReach sys l (o2, pt)
  | fwdLiveness {o : OriginId} {p1 p2 : PointId} :
      (sys.dirOf o).allowsFwd = true →
      (p1, p2) ∈ sys.cfgEdges →
      sys.liveAt o p2 = true →
      NextReach sys l (o, p1) → NextReach sys l (o, p2)
  | bwdLiveness {o : OriginId} {p1 p2 : PointId} :
      (sys.dirOf o).allowsBwd = true →
      (p1, p2) ∈ sys.cfgEdges →
      sys.liveAt o p2 = true →
      NextReach sys l (o, p2) → NextReach sys l (o, p1)

noncomputable def NextLoanLive (sys : BorrowRegionSystem) (l : LoanId) (p : PointId) : Prop :=
  ∃ o, NextReach sys l (o, p) ∧ sys.liveAt o p = true

/-- `Polonius::Next`: localized `NextLoanLive` for loan conflicts, yet STILL uses
    location-insensitive `NllSubset` (`check_universal_regions`,
    `region_context.rs:216-229`) for universal-region checks! -/
noncomputable def NextAccepts (sys : BorrowRegionSystem) : Prop :=
  (∀ c, c ∈ sys.conflicts → ¬ NextLoanLive sys c.loan c.pt) ∧
  (∀ u, u ∈ sys.forbiddenUnivPairs → ¬ NllSubset sys u.longer u.shorter)

/-- Point-indexed forward-propagating `subset(o1, o2, p)` of `Polonius::Legacy`. -/
inductive LegacySubset (sys : BorrowRegionSystem) :
    OriginId → OriginId → PointId → Prop where
  | refl (o : OriginId) (p : PointId) : LegacySubset sys o o p
  | singleEdge {e : OutlivesEdge} {pt : PointId} :
      e ∈ sys.outlives → e.scope = .single pt → LegacySubset sys e.sup e.sub pt
  | allEdge {e : OutlivesEdge} {pt : PointId} :
      e ∈ sys.outlives → e.scope = .allPts → LegacySubset sys e.sup e.sub pt
  | knownEdge {o1 o2 : OriginId} {pt : PointId} :
      (o1, o2) ∈ sys.knownUnivOutlives → LegacySubset sys o1 o2 pt
  | trans {o1 o2 o3 : OriginId} {p : PointId} :
      LegacySubset sys o1 o2 p → LegacySubset sys o2 o3 p → LegacySubset sys o1 o3 p
  | fwdCfg {o1 o2 : OriginId} {p1 p2 : PointId} :
      (p1, p2) ∈ sys.cfgEdges →
      sys.liveAt o1 p2 = true →
      sys.liveAt o2 p2 = true →
      LegacySubset sys o1 o2 p1 →
      LegacySubset sys o1 o2 p2

/-- Point-indexed `origin_contains_loan_at(o, l, p)` of `Polonius::Legacy`. -/
inductive LegacyLoanAt (sys : BorrowRegionSystem) (l : LoanId) :
    OriginId → PointId → Prop where
  | issued {ld : LoanDecl} :
      ld ∈ sys.loans → ld.loan = l → LegacyLoanAt sys l ld.origin ld.issuePt
  | subset {o1 o2 : OriginId} {p : PointId} :
      LegacyLoanAt sys l o1 p → LegacySubset sys o1 o2 p → LegacyLoanAt sys l o2 p
  | fwdCfg {o : OriginId} {p1 p2 : PointId} :
      (p1, p2) ∈ sys.cfgEdges →
      sys.liveAt o p2 = true →
      LegacyLoanAt sys l o p1 →
      LegacyLoanAt sys l o p2

noncomputable def LegacyLoanLive (sys : BorrowRegionSystem) (l : LoanId) (p : PointId) : Prop :=
  ∃ o, LegacyLoanAt sys l o p ∧ sys.liveAt o p = true

/-- `Polonius::Legacy`: point-indexed `LegacyLoanLive` for loan conflicts AND
    point-indexed `LegacySubset` (`check_polonius_subset_errors`) for universal pairs. -/
noncomputable def LegacyAccepts (sys : BorrowRegionSystem) : Prop :=
  (∀ c, c ∈ sys.conflicts → ¬ LegacyLoanLive sys c.loan c.pt) ∧
  (∀ u, u ∈ sys.forbiddenUnivPairs → ∀ p, ¬ LegacySubset sys u.longer u.shorter p)

/-- Operational safety semantics: along any CFG path from `entry` reaching `c.pt`
    for a conflict `(c.loan, c.pt)`, if the loan was issued along the path and is
    still used/live along a continuation from `c.pt`, no conflict arises.
    Specifically, for our localized alias-flow model, operational execution
    tracks forward CFG paths from loan issue to a live reference use. -/
inductive CfgWalk (sys : BorrowRegionSystem) : PointId → PointId → Prop where
  | here (p : PointId) : CfgWalk sys p p
  | step {p q r : PointId} :
      (p, q) ∈ sys.cfgEdges → CfgWalk sys q r → CfgWalk sys p r

noncomputable def OperationalSafe (sys : BorrowRegionSystem) : Prop :=
  ∀ c, c ∈ sys.conflicts →
    ¬ (∃ ld o, ld ∈ sys.loans ∧ ld.loan = c.loan ∧
        CfgWalk sys sys.entry ld.issuePt ∧
        CfgWalk sys ld.issuePt c.pt ∧
        LegacyLoanAt sys c.loan o c.pt ∧
        sys.liveAt o c.pt = true)

/-! ### Hierarchy & Soundness Proofs -/

theorem nextReach_implies_nllSubset {sys : BorrowRegionSystem} {l : LoanId}
    {node : OriginId × PointId} (h : NextReach sys l node) :
    ∃ ld, ld ∈ sys.loans ∧ ld.loan = l ∧ NllSubset sys ld.origin node.1 := by
  induction h with
  | start hld hl =>
      exact ⟨_, hld, hl, NllSubset.refl _⟩
  | singleEdge he _ _ ih =>
      obtain ⟨ld, hld, hl, hsub⟩ := ih
      exact ⟨ld, hld, hl, NllSubset.trans hsub (NllSubset.stepEdge he)⟩
  | allEdge he _ _ ih =>
      obtain ⟨ld, hld, hl, hsub⟩ := ih
      exact ⟨ld, hld, hl, NllSubset.trans hsub (NllSubset.stepEdge he)⟩
  | knownEdge hk _ ih =>
      obtain ⟨ld, hld, hl, hsub⟩ := ih
      exact ⟨ld, hld, hl, NllSubset.trans hsub (NllSubset.stepKnown hk)⟩
  | fwdLiveness _ _ _ _ ih =>
      exact ih
  | bwdLiveness _ _ _ _ ih =>
      exact ih

theorem nextLoanLive_implies_nllLoanLive {sys : BorrowRegionSystem} {l : LoanId} {p : PointId}
    (h : NextLoanLive sys l p) : NllLoanLive sys l p := by
  obtain ⟨o, hreach, hlive⟩ := h
  obtain ⟨ld, hld, hl, hsub⟩ := nextReach_implies_nllSubset hreach
  exact ⟨ld, o, hld, hl, hsub, hlive⟩

theorem off_accepts_implies_next_accepts (sys : BorrowRegionSystem) :
    OffAccepts sys → NextAccepts sys := by
  intro ⟨hconf, huniv⟩
  constructor
  · intro c hc hnext
    exact hconf c hc (nextLoanLive_implies_nllLoanLive hnext)
  · exact huniv

theorem legacySubset_implies_nllSubset {sys : BorrowRegionSystem}
    {o1 o2 : OriginId} {p : PointId}
    (h : LegacySubset sys o1 o2 p) : NllSubset sys o1 o2 := by
  induction h with
  | refl o _ => exact NllSubset.refl o
  | singleEdge he _ => exact NllSubset.stepEdge he
  | allEdge he _ => exact NllSubset.stepEdge he
  | knownEdge hk => exact NllSubset.stepKnown hk
  | trans _ _ ih1 ih2 => exact NllSubset.trans ih1 ih2
  | fwdCfg _ _ _ _ ih => exact ih

noncomputable def AllOriginsBidir (sys : BorrowRegionSystem) : Prop :=
  ∀ o, (sys.dirOf o).allowsFwd = true ∧ (sys.dirOf o).allowsBwd = true

theorem legacySubset_to_nextReach_of_bidir {sys : BorrowRegionSystem}
    (hbi : AllOriginsBidir sys) {l : LoanId} {o1 o2 : OriginId} {p : PointId}
    (hsub : LegacySubset sys o1 o2 p) :
    NextReach sys l (o1, p) → NextReach sys l (o2, p) := by
  induction hsub with
  | refl _ _ =>
      intro hr
      exact hr
  | singleEdge he hsc =>
      intro hr
      exact NextReach.singleEdge he hsc hr
  | allEdge he hsc =>
      intro hr
      exact NextReach.allEdge he hsc hr
  | knownEdge hk =>
      intro hr
      exact NextReach.knownEdge hk hr
  | trans _ _ ih1 ih2 =>
      intro hr
      exact ih2 (ih1 hr)
  | @fwdCfg o1' o2' _ _ hcfg hl1 hl2 _ ih =>
      intro hr
      have hbwd1 : (sys.dirOf o1').allowsBwd = true := (hbi o1').2
      have hfwd2 : (sys.dirOf o2').allowsFwd = true := (hbi o2').1
      have hr_p1 := NextReach.bwdLiveness hbwd1 hcfg hl1 hr
      have hr_o2_p1 := ih hr_p1
      exact NextReach.fwdLiveness hfwd2 hcfg hl2 hr_o2_p1

theorem legacyLoanAt_to_nextReach_of_bidir {sys : BorrowRegionSystem}
    (hbi : AllOriginsBidir sys) {l : LoanId} {o : OriginId} {p : PointId}
    (hlat : LegacyLoanAt sys l o p) : NextReach sys l (o, p) := by
  induction hlat with
  | issued hld hl =>
      exact NextReach.start hld hl
  | subset _ hsub ih =>
      exact legacySubset_to_nextReach_of_bidir hbi hsub ih
  | fwdCfg hcfg hl _ ih =>
      exact NextReach.fwdLiveness (hbi _).1 hcfg hl ih

theorem next_accepts_implies_legacy_accepts_of_bidir (sys : BorrowRegionSystem)
    (hbi : AllOriginsBidir sys) :
    NextAccepts sys → LegacyAccepts sys := by
  intro ⟨hconf, huniv⟩
  constructor
  · intro c hc ⟨o, hlat, hlive⟩
    exact hconf c hc ⟨o, legacyLoanAt_to_nextReach_of_bidir hbi hlat, hlive⟩
  · intro u hu p hsub
    exact huniv u hu (legacySubset_implies_nllSubset hsub)

theorem legacy_accepts_implies_operational_safe (sys : BorrowRegionSystem) :
    LegacyAccepts sys → OperationalSafe sys := by
  intro ⟨hconf, _⟩ c hc ⟨_, o, _, _, _, _, hlat, hlive⟩
  exact hconf c hc ⟨o, hlat, hlive⟩

theorem next_accepts_implies_operational_safe_of_bidir (sys : BorrowRegionSystem)
    (hbi : AllOriginsBidir sys) :
    NextAccepts sys → OperationalSafe sys := by
  intro hnext
  exact legacy_accepts_implies_operational_safe sys
    (next_accepts_implies_legacy_accepts_of_bidir sys hbi hnext)

theorem off_accepts_implies_operational_safe_of_bidir (sys : BorrowRegionSystem)
    (hbi : AllOriginsBidir sys) :
    OffAccepts sys → OperationalSafe sys := by
  intro hoff
  exact next_accepts_implies_operational_safe_of_bidir sys hbi
    (off_accepts_implies_next_accepts sys hoff)

/-! ### 3-Way Separation Witnesses (`Off ⊊ Next ⊊ Legacy`) & Covariant / Time-Travel Controls -/

/-
  Witness 1 (`pc3Graph`): Models NLL Problem Case #3 (`get_or_insert`):
    Origins: `0` = `'a` (return lifetime), `1` = `'?v` (borrowed reference in `Some(v)`).
    Points: `0` (borrow at `map.get`), `1` (return `v` arm), `2` (`None` arm `map.insert` conflict).
    CFG: `(0, 1)`, `(0, 2)`.
    `'?v` is live at `0` and `1`, DEAD at `2`; `'a` is live at `1` (return) and `0`, DEAD at `2`
    along CFG? Wait: `'a` is live at exit `1` and `3`, NOT at `2`!
    Under NLL (`Off`), `'?v : 'a` (`Single 1`) forces `'?v` to inherit `'a` everywhere, and
    since `'a` is universal (live across the body including `2`), `NllLoanLive` triggers at `2`.
    Under `Next` and `Legacy`, `Single 1` only connects `'?v@1 -> 'a@1`; since `(0, 2)` never
    passes `1`, `loan 0` never reaches `'a` along `(0, 2)` and `'?v` is dead at `2`!
-/
noncomputable def pc3Graph : BorrowRegionSystem where
  entry := 0
  cfgEdges := [(0, 1), (0, 2)]
  liveAt := fun o p =>
    match o, p with
    | 1, 0 => true
    | 1, 1 => true
    | 0, 1 => true
    | 0, 2 => true
    | _, _ => false
  dirOf := fun o =>
    match o with
    | 0 => .fwd
    | _ => .bidir
  loans := [{ loan := 0, origin := 1, issuePt := 0 }]
  outlives := [{ sup := 1, sub := 0, scope := .single 1 }]
  knownUnivOutlives := []
  conflicts := [{ loan := 0, pt := 2 }]
  forbiddenUnivPairs := []

theorem pc3Graph_not_offAccepts : ¬ OffAccepts pc3Graph := by
  intro ⟨hconf, _⟩
  apply hconf { loan := 0, pt := 2 } (List.Mem.head _)
  refine ⟨{ loan := 0, origin := 1, issuePt := 0 }, 0, List.Mem.head _, rfl, ?_, rfl⟩
  have he : OutlivesEdge.mk 1 0 (.single 1) ∈ pc3Graph.outlives := List.Mem.head _
  exact NllSubset.stepEdge he

theorem pc3Graph_nextReach_inversion (o : OriginId) (p : PointId)
    (h : NextReach pc3Graph 0 (o, p)) :
    (o = 1 ∧ p = 0) ∨ (o = 1 ∧ p = 1) ∨ (o = 0 ∧ p = 1) := by
  generalize hnd : (o, p) = nd at h
  revert o p
  induction h with
  | start hld _ =>
      intro o p hnd
      cases hld with
      | head =>
          cases hnd
          exact Or.inl ⟨rfl, rfl⟩
      | tail _ hm => cases hm
  | singleEdge he hsc _ ih =>
      intro o p hnd
      cases he with
      | head =>
          cases hsc
          have := ih _ _ rfl
          rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases h1 <;> cases h2
          cases hnd
          exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      | tail _ hm => cases hm
  | allEdge he hsc _ _ =>
      cases he with
      | head => cases hsc
      | tail _ hm => cases hm
  | knownEdge hk _ _ =>
      cases hk
  | fwdLiveness _ hcfg hlive _ ih =>
      intro o p hnd
      cases hnd
      have hih := ih _ _ rfl
      cases hcfg with
      | head =>
          rcases hih with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases h1 <;> cases h2
          exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | tail _ hcfg2 =>
          cases hcfg2 with
          | head =>
              rcases hih with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases h1 <;> cases h2
              cases hlive
          | tail _ hm => cases hm
  | bwdLiveness hallow hcfg _ _ ih =>
      intro o p hnd
      cases hnd
      have hih := ih _ _ rfl
      cases hcfg with
      | head =>
          rcases hih with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases h1 <;> cases h2
          · exact Or.inl ⟨rfl, rfl⟩
          · cases hallow
      | tail _ hcfg2 =>
          cases hcfg2 with
          | head =>
              rcases hih with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases h1 <;> cases h2
          | tail _ hm => cases hm

theorem pc3Graph_nextAccepts : NextAccepts pc3Graph := by
  constructor
  · intro c hc ⟨o, hreach, hlive⟩
    cases hc with
    | head =>
        rcases pc3Graph_nextReach_inversion o 2 hreach with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ <;>
          cases h2
    | tail _ hm => cases hm
  · intro u hu
    cases hu

theorem pc3Graph_legacySubset_inv {o1 o2 : OriginId} {p : PointId}
    (h : LegacySubset pc3Graph o1 o2 p) :
    o1 = o2 ∨ (o1 = 1 ∧ o2 = 0 ∧ p = 1) := by
  induction h with
  | refl _ _ => exact Or.inl rfl
  | singleEdge he hsc =>
      cases he with
      | head => cases hsc; exact Or.inr ⟨rfl, rfl, rfl⟩
      | tail _ hm => cases hm
  | allEdge he hsc =>
      cases he with
      | head => cases hsc
      | tail _ hm => cases hm
  | knownEdge hk => cases hk
  | trans _ _ ih1 ih2 =>
      rcases ih1 with h1 | ⟨h1, h2, h3⟩ <;> rcases ih2 with h4 | ⟨h4, h5, h6⟩
      · subst h1; subst h4; exact Or.inl rfl
      · subst h1; subst h4; exact Or.inr ⟨rfl, h5, h6⟩
      · subst h4; exact Or.inr ⟨h1, h2, h3⟩
      · subst h2; cases h4
  | fwdCfg hcfg _ _ _ ih =>
      cases hcfg with
      | head =>
          rcases ih with h | ⟨_, _, h3⟩
          · subst h; exact Or.inl rfl
          · cases h3
      | tail _ hcfg2 =>
          cases hcfg2 with
          | head =>
              rcases ih with h | ⟨_, _, h3⟩
              · subst h; exact Or.inl rfl
              · cases h3
          | tail _ hm => cases hm

theorem pc3Graph_legacyLoanAt_inv {o : OriginId} {p : PointId}
    (h : LegacyLoanAt pc3Graph 0 o p) :
    (o = 1 ∧ p = 0) ∨ (o = 1 ∧ p = 1) ∨ (o = 0 ∧ p = 1) := by
  induction h with
  | issued hld _ =>
      cases hld with
      | head => exact Or.inl ⟨rfl, rfl⟩
      | tail _ hm => cases hm
  | subset _ hsub ih =>
      rcases pc3Graph_legacySubset_inv hsub with heq | ⟨ho1, ho2, hp⟩
      · subst heq; exact ih
      · subst ho1; subst ho2; subst hp; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  | fwdCfg hcfg hlive _ ih =>
      cases hcfg with
      | head =>
          rcases ih with ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
          · subst h1; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · cases h2
          · cases h2
      | tail _ hcfg2 =>
          cases hcfg2 with
          | head =>
              rcases ih with ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
              · subst h1; cases hlive
              · cases h2
              · cases h2
          | tail _ hm => cases hm

theorem pc3Graph_legacyAccepts : LegacyAccepts pc3Graph := by
  constructor
  · intro c hc ⟨o, hlat, _⟩
    cases hc with
    | head =>
        rcases pc3Graph_legacyLoanAt_inv hlat with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ <;> cases h2
    | tail _ hm => cases hm
  · intro u hu; cases hu

theorem pc3Graph_operationalSafe : OperationalSafe pc3Graph :=
  legacy_accepts_implies_operational_safe pc3Graph pc3Graph_legacyAccepts

/-
  Witness 2 (`invarianceGraph`): Models `flow_sensitive_invariance<'a, 'b>`!
    Origins: `0` = `'a`, `1` = `'b`, `2` = `returned_value` (`'?11`).
    Points: `0` (creation), `1` (`Ok(returned_value)` branch), `2` (`Err(returned_value)` branch).
    CFG: `(0, 1)`, `(0, 2)` (disjoint branches!).
    Edges: At `pt 1`, `2 ↔ 0` (`Single 1`); at `pt 2`, `2 ↔ 1` (`Single 2`).
    Forbidden universal pairs: `(0, 1)` (`'a: 'b`) and `(1, 0)` (`'b: 'a`).
    - Under `Off` AND `Next`: `NllSubset` chains `0 -> 2 -> 1`, rejecting!
    - Under `Legacy`: at `pt 0` no edges; at `pt 1` only `{0, 2}`; at `pt 2` only `{1, 2}`;
      since there is no CFG edge from `1` to `2` or `2` to `1`, `LegacySubset` NEVER connects `0` and `1`!
-/
noncomputable def invarianceGraph : BorrowRegionSystem where
  entry := 0
  cfgEdges := [(0, 1), (0, 2)]
  liveAt := fun o p =>
    match o, p with
    | 2, 0 => true
    | 2, 1 => true
    | 2, 2 => true
    | 0, 0 => true
    | 0, 1 => true
    | 0, 2 => true
    | 1, 0 => true
    | 1, 1 => true
    | 1, 2 => true
    | _, _ => false
  dirOf := fun _ => .bidir
  loans := []
  outlives := [
    { sup := 0, sub := 2, scope := .single 1 },
    { sup := 2, sub := 0, scope := .single 1 },
    { sup := 1, sub := 2, scope := .single 2 },
    { sup := 2, sub := 1, scope := .single 2 }
  ]
  knownUnivOutlives := []
  conflicts := []
  forbiddenUnivPairs := [{ longer := 0, shorter := 1 }, { longer := 1, shorter := 0 }]

theorem invarianceGraph_not_nextAccepts : ¬ NextAccepts invarianceGraph := by
  intro ⟨_, huniv⟩
  apply huniv { longer := 0, shorter := 1 } (List.Mem.head _)
  have e02 : OutlivesEdge.mk 0 2 (.single 1) ∈ invarianceGraph.outlives := List.Mem.head _
  have e21 : OutlivesEdge.mk 2 1 (.single 2) ∈ invarianceGraph.outlives :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  exact NllSubset.trans (NllSubset.stepEdge e02) (NllSubset.stepEdge e21)

theorem invarianceGraph_not_offAccepts : ¬ OffAccepts invarianceGraph := by
  intro hoff
  exact invarianceGraph_not_nextAccepts (off_accepts_implies_next_accepts invarianceGraph hoff)

noncomputable def invAllowedAt (p : PointId) (o1 o2 : OriginId) : Prop :=
  o1 = o2 ∨
  (p = 1 ∧ (o1 = 0 ∨ o1 = 2) ∧ (o2 = 0 ∨ o2 = 2)) ∨
  (p = 2 ∧ (o1 = 1 ∨ o1 = 2) ∧ (o2 = 1 ∨ o2 = 2))

theorem invAllowedAt_trans {p : PointId} {o1 o2 o3 : OriginId}
    (h1 : invAllowedAt p o1 o2) (h2 : invAllowedAt p o2 o3) :
    invAllowedAt p o1 o3 := by
  rcases h1 with heq | ⟨hp, ha1, ha2⟩ | ⟨hp, ha1, ha2⟩
  · subst heq; exact h2
  · rcases h2 with heq2 | ⟨_, _, hb2⟩ | ⟨hp2, _, _⟩
    · subst heq2; exact Or.inr (Or.inl ⟨hp, ha1, ha2⟩)
    · exact Or.inr (Or.inl ⟨hp, ha1, hb2⟩)
    · rw [hp] at hp2; cases hp2
  · rcases h2 with heq2 | ⟨hp1, _, _⟩ | ⟨_, _, hb2⟩
    · subst heq2; exact Or.inr (Or.inr ⟨hp, ha1, ha2⟩)
    · rw [hp] at hp1; cases hp1
    · exact Or.inr (Or.inr ⟨hp, ha1, hb2⟩)

theorem invarianceGraph_legacySubset_invariant {o1 o2 : OriginId} {p : PointId}
    (h : LegacySubset invarianceGraph o1 o2 p) : invAllowedAt p o1 o2 := by
  induction h with
  | refl o _ =>
      exact Or.inl rfl
  | singleEdge he hsc =>
      cases he with
      | head =>
          cases hsc; exact Or.inr (Or.inl ⟨rfl, Or.inl rfl, Or.inr rfl⟩)
      | tail _ he1 =>
          cases he1 with
          | head =>
              cases hsc; exact Or.inr (Or.inl ⟨rfl, Or.inr rfl, Or.inl rfl⟩)
          | tail _ he2 =>
              cases he2 with
              | head =>
                  cases hsc; exact Or.inr (Or.inr ⟨rfl, Or.inl rfl, Or.inr rfl⟩)
              | tail _ he3 =>
                  cases he3 with
                  | head =>
                      cases hsc; exact Or.inr (Or.inr ⟨rfl, Or.inr rfl, Or.inl rfl⟩)
                  | tail _ hm => cases hm
  | allEdge he hsc =>
      cases he with
      | head => cases hsc
      | tail _ he1 =>
          cases he1 with
          | head => cases hsc
          | tail _ he2 =>
              cases he2 with
              | head => cases hsc
              | tail _ he3 =>
                  cases he3 with
                  | head => cases hsc
                  | tail _ hm => cases hm
  | knownEdge hk =>
      cases hk
  | trans _ _ ih1 ih2 =>
      exact invAllowedAt_trans ih1 ih2
  | fwdCfg hcfg _ _ _ ih =>
      rcases ih with heq | ⟨hp, _, _⟩ | ⟨hp, _, _⟩
      · subst heq; exact Or.inl rfl
      · cases hcfg with
        | head => cases hp
        | tail _ hcfg2 =>
            cases hcfg2 with
            | head => cases hp
            | tail _ hm => cases hm
      · cases hcfg with
        | head => cases hp
        | tail _ hcfg2 =>
            cases hcfg2 with
            | head => cases hp
            | tail _ hm => cases hm

theorem invarianceGraph_legacyAccepts : LegacyAccepts invarianceGraph := by
  constructor
  · intro c hc; cases hc
  · intro u hu p hsub
    have hinv := invarianceGraph_legacySubset_invariant hsub
    cases hu with
    | head =>
        rcases hinv with h01 | ⟨_, _, h2⟩ | ⟨_, h1, _⟩
        · cases h01
        · rcases h2 with h | h <;> cases h
        · rcases h1 with h | h <;> cases h
    | tail _ hu2 =>
        cases hu2 with
        | head =>
            rcases hinv with h10 | ⟨_, h1, _⟩ | ⟨_, _, h2⟩
            · cases h10
            · rcases h1 with h | h <;> cases h
            · rcases h2 with h | h <;> cases h
        | tail _ hm => cases hm

/-- Combined 3-way strict separation theorem: `Off ⊊ Next ⊊ Legacy`! -/
theorem polonius_three_way_strict_separation :
    (∀ sys, OffAccepts sys → NextAccepts sys) ∧
    (∀ sys, AllOriginsBidir sys → NextAccepts sys → LegacyAccepts sys) ∧
    (¬ OffAccepts pc3Graph ∧ NextAccepts pc3Graph ∧ LegacyAccepts pc3Graph) ∧
    (¬ OffAccepts invarianceGraph ∧ ¬ NextAccepts invarianceGraph ∧ LegacyAccepts invarianceGraph) :=
  ⟨off_accepts_implies_next_accepts,
   next_accepts_implies_legacy_accepts_of_bidir,
   ⟨pc3Graph_not_offAccepts, pc3Graph_nextAccepts, pc3Graph_legacyAccepts⟩,
   ⟨invarianceGraph_not_offAccepts, invarianceGraph_not_nextAccepts, invarianceGraph_legacyAccepts⟩⟩

/-- Witness 3 (`covariantGraph`): Replacing invariance with covariance removes
    reverse edges (`0 -> 2`, `1 -> 2`), so ALL THREE modes accept! -/
noncomputable def covariantGraph : BorrowRegionSystem where
  entry := 0
  cfgEdges := [(0, 1), (0, 2)]
  liveAt := fun _ _ => true
  dirOf := fun _ => .fwd
  loans := []
  outlives := [
    { sup := 2, sub := 0, scope := .single 1 },
    { sup := 2, sub := 1, scope := .single 2 }
  ]
  knownUnivOutlives := []
  conflicts := []
  forbiddenUnivPairs := [{ longer := 0, shorter := 1 }, { longer := 1, shorter := 0 }]

theorem covariantGraph_nllSubset_inv {o1 o2 : OriginId}
    (h : NllSubset covariantGraph o1 o2) :
    o1 = o2 ∨ (o1 = 2 ∧ (o2 = 0 ∨ o2 = 1)) := by
  induction h with
  | refl _ => exact Or.inl rfl
  | stepEdge he =>
      cases he with
      | head => exact Or.inr ⟨rfl, Or.inl rfl⟩
      | tail _ he2 =>
          cases he2 with
          | head => exact Or.inr ⟨rfl, Or.inr rfl⟩
          | tail _ hm => cases hm
  | stepKnown hk => cases hk
  | trans _ _ ih1 ih2 =>
      rcases ih1 with h1 | ⟨h2, h3⟩
      · subst h1; exact ih2
      · rcases ih2 with h4 | ⟨h5, _⟩
        · subst h4; exact Or.inr ⟨h2, h3⟩
        · rcases h3 with h | h <;> rw [h] at h5 <;> cases h5

theorem covariantGraph_accepted_by_all_three :
    OffAccepts covariantGraph ∧ NextAccepts covariantGraph ∧ LegacyAccepts covariantGraph := by
  have hoff : OffAccepts covariantGraph := by
    constructor
    · intro c hc; cases hc
    · intro u hu hsub
      have hinv := covariantGraph_nllSubset_inv hsub
      cases hu with
      | head =>
          rcases hinv with heq | ⟨h2, _⟩
          · cases heq
          · cases h2
      | tail _ hu2 =>
          cases hu2 with
          | head =>
              rcases hinv with heq | ⟨h2, _⟩
              · cases heq
              · cases h2
          | tail _ hm => cases hm
  have hnext := off_accepts_implies_next_accepts covariantGraph hoff
  have hleg : LegacyAccepts covariantGraph := by
    constructor
    · intro c hc; cases hc
    · intro u hu p hsub
      exact (hoff.2 u hu) (legacySubset_implies_nllSubset hsub)
  exact ⟨hoff, hnext, hleg⟩

/-- Witness 4 (`timeTravelGraph`): Backward invariance edges are mandatory for
    soundness on `*q = &mut b; b = 3; *p` (`a5`). -/
noncomputable def timeTravelGraph (withBwd : Bool) : BorrowRegionSystem where
  entry := 0
  cfgEdges := [(0, 1), (1, 2)]
  liveAt := fun o p =>
    match o, p with
    | 0, 0 => true
    | 0, 1 => true
    | 1, 0 => true
    | 1, 1 => true
    | 1, 2 => true
    | _, _ => false
  dirOf := fun o =>
    match o, withBwd with
    | 0, true => .bidir
    | _, _ => .fwd
  loans := [{ loan := 0, origin := 0, issuePt := 1 }]
  outlives := [
    { sup := 0, sub := 1, scope := .single 0 },
    { sup := 1, sub := 0, scope := .single 0 }
  ]
  knownUnivOutlives := []
  conflicts := [{ loan := 0, pt := 2 }]
  forbiddenUnivPairs := []

theorem timeTravelGraph_withBwd_rejects : ¬ NextAccepts (timeTravelGraph true) := by
  intro ⟨hconf, _⟩
  apply hconf { loan := 0, pt := 2 } (List.Mem.head _)
  refine ⟨1, ?_, rfl⟩
  have s0 : NextReach (timeTravelGraph true) 0 (0, 1) :=
    NextReach.start (ld := { loan := 0, origin := 0, issuePt := 1 }) (List.Mem.head _) rfl
  have s1 : NextReach (timeTravelGraph true) 0 (0, 0) :=
    NextReach.bwdLiveness rfl (List.Mem.head _) rfl s0
  have s2 : NextReach (timeTravelGraph true) 0 (1, 0) :=
    NextReach.singleEdge (e := { sup := 0, sub := 1, scope := .single 0 }) (List.Mem.head _) rfl s1
  have s3 : NextReach (timeTravelGraph true) 0 (1, 1) :=
    NextReach.fwdLiveness rfl (List.Mem.head _) rfl s2
  exact NextReach.fwdLiveness rfl (List.Mem.tail _ (List.Mem.head _)) rfl s3

theorem timeTravelGraph_noBwd_reachable_inv (o : OriginId) (p : PointId)
    (h : NextReach (timeTravelGraph false) 0 (o, p)) :
    o = 0 ∧ (p = 1 ∨ p = 2) := by
  generalize hnd : (o, p) = nd at h
  revert o p
  induction h with
  | start hld _ =>
      intro o p hnd
      cases hld with
      | head => cases hnd; exact ⟨rfl, Or.inl rfl⟩
      | tail _ hm => cases hm
  | singleEdge he hsc _ ih =>
      intro o p hnd
      have ⟨ho, hp⟩ := ih _ _ rfl
      cases he with
      | head =>
          cases hsc
          rcases hp with h | h <;> cases h
      | tail _ he2 =>
          cases he2 with
          | head =>
              cases hsc
              cases ho
          | tail _ hm => cases hm
  | allEdge he hsc _ _ =>
      cases he with
      | head => cases hsc
      | tail _ he2 =>
          cases he2 with
          | head => cases hsc
          | tail _ hm => cases hm
  | knownEdge hk _ _ => cases hk
  | fwdLiveness _ hcfg hlive _ ih =>
      intro o p hnd
      cases hnd
      have ⟨ho, hp⟩ := ih _ _ rfl
      subst ho
      cases hcfg with
      | head =>
          rcases hp with h | h <;> cases h
      | tail _ hcfg2 =>
          cases hcfg2 with
          | head => cases hlive
          | tail _ hm => cases hm
  | @bwdLiveness o' _ _ hallow _ _ _ _ =>
      cases o' <;> simp [timeTravelGraph] at hallow <;> cases hallow

theorem timeTravelGraph_noBwd_falsely_accepts : NextAccepts (timeTravelGraph false) := by
  constructor
  · intro c hc ⟨o, hreach, hlive⟩
    cases hc with
    | head =>
        have ⟨ho, _⟩ := timeTravelGraph_noBwd_reachable_inv o 2 hreach
        subst ho
        cases hlive
    | tail _ hm => cases hm
  · intro u hu; cases hu

/-! ## Part II: Edition 2024 RPIT `use<...>` Capture & `member_constraints.rs` Lattice -/

inductive RustEdition where
  | ed2021
  | ed2024

inductive OpaqueOriginKind where
  | freeFn
  | inherentMethod
  | traitOrImplRpitit
  | asyncFn
  | typeAlias

/-- Exact model of `opaque_captures_all_in_scope_lifetimes` in
    `compiler/rustc_hir_analysis/src/collect/resolve_bound_vars.rs:322-331`. -/
noncomputable def opaqueCapturesAllInScopeLifetimes (orig : OpaqueOriginKind) (ed : RustEdition)
    (hasUseBound : Bool) : Bool :=
  if hasUseBound then false
  else match orig with
  | .asyncFn | .typeAlias => true
  | .traitOrImplRpitit => true
  | .freeFn | .inherentMethod =>
      match ed with
      | .ed2021 => false
      | .ed2024 => true

theorem edition2024_rpit_delta_exact :
    opaqueCapturesAllInScopeLifetimes .freeFn .ed2021 false = false ∧
    opaqueCapturesAllInScopeLifetimes .freeFn .ed2024 false = true ∧
    opaqueCapturesAllInScopeLifetimes .freeFn .ed2024 true = false ∧
    opaqueCapturesAllInScopeLifetimes .inherentMethod .ed2021 false = false ∧
    opaqueCapturesAllInScopeLifetimes .inherentMethod .ed2024 false = true ∧
    opaqueCapturesAllInScopeLifetimes .traitOrImplRpitit .ed2021 false = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Finite universal-region preorder (`0` represents `'static`, which outlives
    every region). -/
structure RegionPreorder where
  outlives : Nat → Nat → Bool
  refl : ∀ r, outlives r r = true
  trans : ∀ a b c, outlives a b = true → outlives b c = true → outlives a c = true
  staticTop : ∀ r, outlives 0 r = true

/-- `NllMemberConstraint` problem (`opaque_types/mod.rs:286-299`,
    `member_constraints.rs:59-139`). `argRegions` lists captured lifetime args
    excluding `'static`; `applyMemberConstraint` always prepends `0` (`'static`). -/
structure MemberConstraintProblem where
  argRegions : List Nat
  lowerBounds : List Nat
  upperBounds : List Nat

noncomputable def candidateChoices (p : MemberConstraintProblem) : List Nat :=
  0 :: p.argRegions

noncomputable def satisfiesLowerBounds (rel : RegionPreorder) (p : MemberConstraintProblem) (c : Nat) : Bool :=
  allList (fun lb => rel.outlives c lb) p.lowerBounds

noncomputable def satisfiesUpperBounds (rel : RegionPreorder) (p : MemberConstraintProblem) (c : Nat) : Bool :=
  allList (fun ub => rel.outlives ub c) p.upperBounds

noncomputable def admissibleChoices (rel : RegionPreorder) (p : MemberConstraintProblem) : List Nat :=
  filterList
    (fun c => satisfiesLowerBounds rel p c && satisfiesUpperBounds rel p c)
    (candidateChoices p)

noncomputable def totallyOrderedChoices (rel : RegionPreorder) (choices : List Nat) : List Nat :=
  filterList
    (fun r1 => allList (fun r2 => rel.outlives r1 r2 || rel.outlives r2 r1) choices)
    choices

noncomputable def pickSmaller (rel : RegionPreorder) (r1 r2 : Nat) : Nat :=
  match rel.outlives r1 r2, rel.outlives r2 r1 with
  | true, true => if Nat.ble r1 r2 then r1 else r2
  | true, false => r2
  | false, true => r1
  | false, false => r1

noncomputable def reduceLeast (rel : RegionPreorder) (acc : Nat) : List Nat → Nat
  | [] => acc
  | r :: rs => reduceLeast rel (pickSmaller rel acc r) rs

/-- Exact mechanization of `apply_member_constraint` (`member_constraints.rs:74-138`). -/
noncomputable def applyMemberConstraint (rel : RegionPreorder) (p : MemberConstraintProblem) : Option Nat :=
  match totallyOrderedChoices rel (admissibleChoices rel p) with
  | [] => none
  | r :: rs => some (reduceLeast rel r rs)

theorem mem_admissibleChoices_iff (rel : RegionPreorder) (p : MemberConstraintProblem) (c : Nat) :
    c ∈ admissibleChoices rel p ↔
      c ∈ candidateChoices p ∧
      (∀ lb, lb ∈ p.lowerBounds → rel.outlives c lb = true) ∧
      (∀ ub, ub ∈ p.upperBounds → rel.outlives ub c = true) := by
  unfold admissibleChoices
  rw [mem_filterList_iff]
  constructor
  · intro ⟨hcand, hbounds⟩
    obtain ⟨hlb, hub⟩ := boolAndTrue hbounds
    exact ⟨hcand, (allList_true_iff _ _).mp hlb, (allList_true_iff _ _).mp hub⟩
  · intro ⟨hcand, hlb, hub⟩
    refine ⟨hcand, mkBoolAndTrue ?_ ?_⟩
    · exact (allList_true_iff _ _).mpr hlb
    · exact (allList_true_iff _ _).mpr hub

theorem mem_totallyOrderedChoices_iff (rel : RegionPreorder) (choices : List Nat) (r : Nat) :
    r ∈ totallyOrderedChoices rel choices ↔
      r ∈ choices ∧ ∀ r2, r2 ∈ choices → rel.outlives r r2 = true ∨ rel.outlives r2 r = true := by
  unfold totallyOrderedChoices
  rw [mem_filterList_iff]
  constructor
  · intro ⟨hr, hall⟩
    refine ⟨hr, fun r2 hr2 => boolOrTrue ((allList_true_iff _ _).mp hall r2 hr2)⟩
  · intro ⟨hr, hall⟩
    refine ⟨hr, (allList_true_iff _ _).mpr ?_⟩
    intro r2 hr2
    rcases hall r2 hr2 with h1 | h2
    · rw [h1]; rfl
    · rw [h2]; cases rel.outlives r r2 <;> rfl

theorem pickSmaller_is_left_or_right (rel : RegionPreorder) (r1 r2 : Nat) :
    pickSmaller rel r1 r2 = r1 ∨ pickSmaller rel r1 r2 = r2 := by
  unfold pickSmaller
  cases h1 : rel.outlives r1 r2 <;> cases h2 : rel.outlives r2 r1
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · cases Nat.ble r1 r2
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem reduceLeast_mem (rel : RegionPreorder) (xs : List Nat) (acc : Nat)
    (hacc : acc ∈ xs) : ∀ ys, (∀ y, y ∈ ys → y ∈ xs) → reduceLeast rel acc ys ∈ xs := by
  intro ys hys
  induction ys generalizing acc with
  | nil => exact hacc
  | cons y rest ih =>
      apply ih
      · rcases pickSmaller_is_left_or_right rel acc y with h | h <;> rw [h]
        · exact hacc
        · exact hys y (List.Mem.head _)
      · intro z hz
        exact hys z (List.Mem.tail _ hz)

theorem pickSmaller_le_both (rel : RegionPreorder) (r1 r2 : Nat)
    (hcomp : rel.outlives r1 r2 = true ∨ rel.outlives r2 r1 = true) :
    rel.outlives r1 (pickSmaller rel r1 r2) = true ∧
    rel.outlives r2 (pickSmaller rel r1 r2) = true := by
  unfold pickSmaller
  cases h1 : rel.outlives r1 r2 <;> cases h2 : rel.outlives r2 r1
  · rcases hcomp with h | h
    · rw [h1] at h; cases h
    · rw [h2] at h; cases h
  · exact ⟨rel.refl r1, h2⟩
  · exact ⟨h1, rel.refl r2⟩
  · cases Nat.ble r1 r2
    · exact ⟨h1, rel.refl r2⟩
    · exact ⟨rel.refl r1, h2⟩

theorem reduceLeast_le_all (rel : RegionPreorder) (choices : List Nat)
    (htot : ∀ a b, a ∈ choices → b ∈ choices → rel.outlives a b = true ∨ rel.outlives b a = true) :
    ∀ ys, (∀ y, y ∈ ys → y ∈ choices) →
    ∀ acc, acc ∈ choices →
    rel.outlives acc (reduceLeast rel acc ys) = true ∧
    ∀ y, y ∈ ys → rel.outlives y (reduceLeast rel acc ys) = true := by
  intro ys
  induction ys with
  | nil =>
      intro _ acc _
      exact ⟨rel.refl acc, fun _ hy => nomatch hy⟩
  | cons y rest ih =>
      intro hys acc hacc
      have hyc : y ∈ choices := hys y (List.Mem.head _)
      have hcomp := htot acc y hacc hyc
      have ⟨hle1, hle2⟩ := pickSmaller_le_both rel acc y hcomp
      have hp_mem : pickSmaller rel acc y ∈ choices := by
        rcases pickSmaller_is_left_or_right rel acc y with h | h <;> rw [h]
        · exact hacc
        · exact hyc
      have ⟨ih_acc, ih_rest⟩ := ih (fun z hz => hys z (List.Mem.tail _ hz)) _ hp_mem
      refine ⟨rel.trans _ _ _ hle1 ih_acc, ?_⟩
      intro z hz
      cases hz with
      | head => exact rel.trans _ _ _ hle2 ih_acc
      | tail _ hz_rest => exact ih_rest z hz_rest

/-- Soundness theorem for `apply_member_constraint`: any chosen region `m`
    belongs to `candidateChoices p` (`0 :: p.argRegions`), outlives every lower
    bound, and is outlived by every upper bound! -/
theorem applyMemberConstraint_sound (rel : RegionPreorder) (p : MemberConstraintProblem)
    (m : Nat) (h : applyMemberConstraint rel p = some m) :
    m ∈ candidateChoices p ∧
    (∀ lb, lb ∈ p.lowerBounds → rel.outlives m lb = true) ∧
    (∀ ub, ub ∈ p.upperBounds → rel.outlives ub m = true) := by
  unfold applyMemberConstraint at h
  cases htot : totallyOrderedChoices rel (admissibleChoices rel p) with
  | nil =>
      rw [htot] at h
      cases h
  | cons r rs =>
      rw [htot] at h
      cases h
      have hmem_tot : reduceLeast rel r rs ∈ totallyOrderedChoices rel (admissibleChoices rel p) := by
        rw [htot]
        apply reduceLeast_mem rel (r :: rs) r (List.Mem.head _) rs
        intro y hy
        exact List.Mem.tail _ hy
      have hmem_adm : reduceLeast rel r rs ∈ admissibleChoices rel p :=
        ((mem_totallyOrderedChoices_iff rel (admissibleChoices rel p) _).mp hmem_tot).1
      exact (mem_admissibleChoices_iff rel p _).mp hmem_adm

/-- Minimality theorem for `apply_member_constraint`: any chosen region `m` is
    outlived by EVERY region in `totallyOrderedChoices`. -/
theorem applyMemberConstraint_minimal (rel : RegionPreorder) (p : MemberConstraintProblem)
    (m : Nat) (h : applyMemberConstraint rel p = some m) :
    ∀ r, r ∈ totallyOrderedChoices rel (admissibleChoices rel p) →
      rel.outlives r m = true := by
  unfold applyMemberConstraint at h
  cases htot : totallyOrderedChoices rel (admissibleChoices rel p) with
  | nil =>
      rw [htot] at h
      cases h
  | cons hd tl =>
      rw [htot] at h
      cases h
      have htot_pair : ∀ a b, a ∈ totallyOrderedChoices rel (admissibleChoices rel p) →
          b ∈ totallyOrderedChoices rel (admissibleChoices rel p) →
          rel.outlives a b = true ∨ rel.outlives b a = true := by
        intro a b ha hb
        have ha_all := ((mem_totallyOrderedChoices_iff rel _ a).mp ha).2
        have hb_mem := ((mem_totallyOrderedChoices_iff rel _ b).mp hb).1
        exact ha_all b hb_mem
      have hsub : ∀ y, y ∈ tl → y ∈ totallyOrderedChoices rel (admissibleChoices rel p) := by
        intro y hy; rw [htot]; exact List.Mem.tail _ hy
      have hhd_mem : hd ∈ totallyOrderedChoices rel (admissibleChoices rel p) := by
        rw [htot]; exact List.Mem.head _
      have ⟨hle_hd, hle_tl⟩ := reduceLeast_le_all rel _ htot_pair tl hsub hd hhd_mem
      intro r hr
      cases hr with
      | head => exact hle_hd
      | tail _ hr_tl => exact hle_tl r hr_tl

/-! ### Concrete `member_constraints` Witnesses Matching `b4`..`b8` -/

/-- Partial order with `0 = 'static`, `1 = 'a`, `2 = 'b`, `3 = 'c`:
    `'static: 'a, 'b, 'c`; `'a: 'c`; `'b: 'c`; while `'a` and `'b` are incomparable! -/
noncomputable def diamondRelFn (x y : Nat) : Bool :=
  match x, y with
  | 0, _ => true
  | 1, 1 => true
  | 1, 3 => true
  | 2, 2 => true
  | 2, 3 => true
  | 3, 3 => true
  | x, y => Nat.beq x y

theorem diamondRelFn_refl (r : Nat) : diamondRelFn r r = true := by
  cases r with
  | zero => rfl
  | succ r1 =>
      cases r1 with
      | zero => rfl
      | succ r2 =>
          cases r2 with
          | zero => rfl
          | succ r3 =>
              cases r3 with
              | zero => rfl
              | succ r4 => exact natEqb_refl (r4 + 4)

theorem diamondRelFn_trans (a b c : Nat)
    (hab : diamondRelFn a b = true) (hbc : diamondRelFn b c = true) :
    diamondRelFn a c = true := by
  cases a with
  | zero => rfl
  | succ a1 =>
      cases a1 with
      | zero =>
          cases b with
          | zero => cases hab
          | succ b1 =>
              cases b1 with
              | zero => exact hbc
              | succ b2 =>
                  cases b2 with
                  | zero => cases hab
                  | succ b3 =>
                      cases b3 with
                      | zero =>
                          cases c with
                          | zero => cases hbc
                          | succ c1 =>
                              cases c1 with
                              | zero => cases hbc
                              | succ c2 =>
                                  cases c2 with
                                  | zero => cases hbc
                                  | succ c3 =>
                                      cases c3 with
                                      | zero => rfl
                                      | succ c4 => cases hbc
                      | succ b4 => cases hab
      | succ a2 =>
          cases a2 with
          | zero =>
              cases b with
              | zero => cases hab
              | succ b1 =>
                  cases b1 with
                  | zero => cases hab
                  | succ b2 =>
                      cases b2 with
                      | zero => exact hbc
                      | succ b3 =>
                          cases b3 with
                          | zero =>
                              cases c with
                              | zero => cases hbc
                              | succ c1 =>
                                  cases c1 with
                                  | zero => cases hbc
                                  | succ c2 =>
                                      cases c2 with
                                      | zero => cases hbc
                                      | succ c3 =>
                                          cases c3 with
                                          | zero => rfl
                                          | succ c4 => cases hbc
                          | succ b4 => cases hab
          | succ a3 =>
              cases a3 with
              | zero =>
                  cases b with
                  | zero => cases hab
                  | succ b1 =>
                      cases b1 with
                      | zero => cases hab
                      | succ b2 =>
                          cases b2 with
                          | zero => cases hab
                          | succ b3 =>
                              cases b3 with
                              | zero => exact hbc
                              | succ b4 => cases hab
              | succ a4 =>
                  have h1 : a4 + 4 = b := (natEqb_true_iff (a4 + 4) b).mp hab
                  subst h1
                  exact hbc

noncomputable def diamondRel : RegionPreorder where
  outlives := diamondRelFn
  refl := diamondRelFn_refl
  trans := diamondRelFn_trans
  staticTop := fun _ => rfl

/-- Ordered relation `'a: 'b` (`1` outlives `2`, `0` = `'static`). -/
noncomputable def orderedRelFn (x y : Nat) : Bool :=
  match x, y with
  | 0, _ => true
  | 1, 1 => true
  | 1, 2 => true
  | 2, 2 => true
  | x, y => Nat.beq x y

theorem orderedRelFn_refl (r : Nat) : orderedRelFn r r = true := by
  cases r with
  | zero => rfl
  | succ r1 =>
      cases r1 with
      | zero => rfl
      | succ r2 =>
          cases r2 with
          | zero => rfl
          | succ r3 => exact natEqb_refl (r3 + 3)

theorem orderedRelFn_trans (a b c : Nat)
    (hab : orderedRelFn a b = true) (hbc : orderedRelFn b c = true) :
    orderedRelFn a c = true := by
  cases a with
  | zero => rfl
  | succ a1 =>
      cases a1 with
      | zero =>
          cases b with
          | zero => cases hab
          | succ b1 =>
              cases b1 with
              | zero => exact hbc
              | succ b2 =>
                  cases b2 with
                  | zero =>
                      cases c with
                      | zero => cases hbc
                      | succ c1 =>
                          cases c1 with
                          | zero => cases hbc
                          | succ c2 =>
                              cases c2 with
                              | zero => rfl
                              | succ c3 => cases hbc
                  | succ b3 => cases hab
      | succ a2 =>
          cases a2 with
          | zero =>
              cases b with
              | zero => cases hab
              | succ b1 =>
                  cases b1 with
                  | zero => cases hab
                  | succ b2 =>
                      cases b2 with
                      | zero => exact hbc
                      | succ b3 => cases hab
          | succ a3 =>
              have h1 : a3 + 3 = b := (natEqb_true_iff (a3 + 3) b).mp hab
              subst h1
              exact hbc

noncomputable def orderedRel : RegionPreorder where
  outlives := orderedRelFn
  refl := orderedRelFn_refl
  trans := orderedRelFn_trans
  staticTop := fun _ => rfl

/-- `b4` (`member_incomparable`): `use<'a, 'b>` with `if cond { x } else { y }`
    imposes upper bounds `['a, 'b]`; neither `'static`, `'a`, nor `'b` is
    outlived by both `'a` and `'b`, yielding `[]` -> `none` (`E0700`)! -/
noncomputable def b4IncomparableProblem : MemberConstraintProblem :=
  { argRegions := [1, 2], lowerBounds := [], upperBounds := [1, 2] }

/-- `b5` (`member_ordered`): adding `where 'a: 'b` narrows admissible choices to
    `['b]`, picking `some 2` (`'b`). -/
noncomputable def b5OrderedProblem : MemberConstraintProblem :=
  { argRegions := [1, 2], lowerBounds := [], upperBounds := [1, 2] }

/-- `b6` (`member_with_cell`): `Cell<&'a str>` imposes both lower and upper bound
    `'a` (`1`), while `'b` (`2`) fails lower bound `'b: 'a`; picks `some 1` (`'a`). -/
noncomputable def b6UniqueCellProblem : MemberConstraintProblem :=
  { argRegions := [1, 2], lowerBounds := [1], upperBounds := [1] }

/-- `b7` (`member_static`): returning `&'static str` under `use<'a, 'b>` leaves
    `['static, 'a, 'b]` admissible; `'a, 'b` are dropped from `totallyOrderedChoices`,
    leaving `['static]` -> `some 0`. -/
noncomputable def b7StaticProblem : MemberConstraintProblem :=
  { argRegions := [1, 2], lowerBounds := [], upperBounds := [] }

/-- `b8` (`member_diamond`): under `where 'a: 'c, 'b: 'c` (`diamondRel`) with
    `use<'a, 'b, 'c>` and `if cond { x } else { y }`, `3` (`'c`) uniquely satisfies
    upper bounds `[1, 2]` (and even with `upperBounds := []`, `totallyOrderedChoices`
    is `[0, 3]` and picks `some 3` `'c`, NOT `0` `'static`!). -/
noncomputable def b8DiamondBranchProblem : MemberConstraintProblem :=
  { argRegions := [1, 2, 3], lowerBounds := [], upperBounds := [1, 2] }

noncomputable def b8DiamondLowerProblem : MemberConstraintProblem :=
  { argRegions := [1, 2, 3], lowerBounds := [3], upperBounds := [] }

theorem member_constraints_empirical_correspondence :
    applyMemberConstraint diamondRel b4IncomparableProblem = none ∧
    applyMemberConstraint orderedRel b5OrderedProblem = some 2 ∧
    applyMemberConstraint diamondRel b6UniqueCellProblem = some 1 ∧
    applyMemberConstraint diamondRel b7StaticProblem = some 0 ∧
    applyMemberConstraint diamondRel b8DiamondBranchProblem = some 3 ∧
    applyMemberConstraint diamondRel b8DiamondLowerProblem = some 3 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Part III: `TwoPhaseBorrow` Reservation/Activation Machine & Tree Borrows -/

inductive TwoPhasePhase where
  | unreserved
  | reserved
  | activated
  | released

inductive TwoPhaseAction where
  | startPriorShared
  | endPriorShared
  | reserveTwoPhase
  | sharedRead
  | directWrite
  | nestedReserveTwoPhase
  | activateTwoPhase
  | releaseTwoPhase

structure BorrowckTwoPhaseState where
  phase : TwoPhasePhase
  priorSharedCount : Nat
  otherMutActive : Bool

noncomputable def BorrowckTwoPhaseState.init : BorrowckTwoPhaseState :=
  { phase := .unreserved, priorSharedCount := 0, otherMutActive := false }

/-- Exact transition function modeling `rustc_borrowck/src/lib.rs:1288-1375,
    1872-1895`, `borrow_set.rs:442-569`, and `path_utils.rs:60-120`:
    - `reserveTwoPhase`: allowed even when `priorSharedCount > 0` (`lib.rs:1313`)
      unless `otherMutActive` or already reserved/activated.
    - `sharedRead`: allowed when `phase != .activated` (`!is_active`, `lib.rs:1326`).
    - `directWrite` / `nestedReserveTwoPhase`: rejected if `phase = .reserved`
      or `.activated` or `priorSharedCount > 0` (`lib.rs:1347`).
    - `activateTwoPhase`: allowed iff `phase = .reserved ∧ priorSharedCount = 0`
      (`check_activations`, `lib.rs:1872-1895`). -/
noncomputable def borrowckStep (st : BorrowckTwoPhaseState) (act : TwoPhaseAction) :
    Option BorrowckTwoPhaseState :=
  match act with
  | .startPriorShared =>
      match st.phase, st.otherMutActive with
      | .activated, _ => none
      | _, true => none
      | _, false => some { st with priorSharedCount := st.priorSharedCount + 1 }
  | .endPriorShared =>
      match st.priorSharedCount with
      | 0 => none
      | n + 1 => some { st with priorSharedCount := n }
  | .reserveTwoPhase =>
      match st.phase, st.otherMutActive with
      | .unreserved, false => some { st with phase := .reserved }
      | _, _ => none
  | .sharedRead =>
      match st.phase, st.otherMutActive with
      | .activated, _ => none
      | _, true => none
      | _, false => some st
  | .directWrite =>
      match st.phase, st.priorSharedCount, st.otherMutActive with
      | .unreserved, 0, false => some st
      | .released, 0, false => some st
      | _, _, _ => none
  | .nestedReserveTwoPhase =>
      match st.phase, st.priorSharedCount, st.otherMutActive with
      | .unreserved, 0, false => some st
      | .released, 0, false => some st
      | _, _, _ => none
  | .activateTwoPhase =>
      match st.phase, st.priorSharedCount, st.otherMutActive with
      | .reserved, 0, false => some { st with phase := .activated }
      | _, _, _ => none
  | .releaseTwoPhase =>
      match st.phase with
      | .reserved => some { st with phase := .released }
      | .activated => some { st with phase := .released }
      | _ => none

noncomputable def runBorrowckTrace (st : BorrowckTwoPhaseState) :
    List TwoPhaseAction → Option BorrowckTwoPhaseState
  | [] => some st
  | a :: rest =>
      match borrowckStep st a with
      | none => none
      | some st' => runBorrowckTrace st' rest

/-- Aliasing-exclusivity invariant preserved by every borrowck-accepted trace. -/
noncomputable def BorrowckInvariant (st : BorrowckTwoPhaseState) : Prop :=
  (st.phase = .activated → st.priorSharedCount = 0 ∧ st.otherMutActive = false) ∧
  (st.phase = .reserved → st.otherMutActive = false)

theorem borrowckStep_preserves_invariant (st st' : BorrowckTwoPhaseState)
    (act : TwoPhaseAction) (hinv : BorrowckInvariant st)
    (hstep : borrowckStep st act = some st') :
    BorrowckInvariant st' := by
  rcases st with ⟨ph, cnt, om⟩
  rcases hinv with ⟨hact, hres⟩
  cases act
  · -- startPriorShared
    cases ph <;> cases cnt <;> cases om <;> simp [borrowckStep] at hstep
    all_goals (cases hstep; exact And.intro (fun h => nomatch h) (fun _ => rfl))
  · -- endPriorShared
    cases cnt with
    | zero => simp [borrowckStep] at hstep
    | succ n =>
        simp [borrowckStep] at hstep
        cases hstep
        refine ⟨fun h => ?_, fun h => hres h⟩
        have ⟨h0, _⟩ := hact h
        cases h0
  · -- reserveTwoPhase
    cases ph <;> cases om <;> simp [borrowckStep] at hstep
    cases hstep
    exact And.intro (fun h => nomatch h) (fun _ => rfl)
  · -- sharedRead
    cases ph <;> cases om <;> simp [borrowckStep] at hstep
    all_goals (cases hstep; exact ⟨hact, hres⟩)
  · -- directWrite
    cases ph <;> cases cnt <;> cases om <;> simp [borrowckStep] at hstep
    all_goals (cases hstep; exact And.intro (fun h => nomatch h) (fun h => nomatch h))
  · -- nestedReserveTwoPhase
    cases ph <;> cases cnt <;> cases om <;> simp [borrowckStep] at hstep
    all_goals (cases hstep; exact And.intro (fun h => nomatch h) (fun h => nomatch h))
  · -- activateTwoPhase
    cases ph <;> cases cnt <;> cases om <;> simp [borrowckStep] at hstep
    cases hstep
    exact And.intro (fun _ => ⟨rfl, rfl⟩) (fun h => nomatch h)
  · -- releaseTwoPhase
    cases ph <;> simp [borrowckStep] at hstep
    all_goals (cases hstep; exact And.intro (fun h => nomatch h) (fun h => nomatch h))

theorem borrowckTrace_preserves_invariant (tr : List TwoPhaseAction)
    (st st' : BorrowckTwoPhaseState) (hinv : BorrowckInvariant st)
    (hrun : runBorrowckTrace st tr = some st') :
    BorrowckInvariant st' := by
  induction tr generalizing st with
  | nil =>
      cases hrun
      exact hinv
  | cons a rest ih =>
      unfold runBorrowckTrace at hrun
      cases hs : borrowckStep st a with
      | none =>
          rw [hs] at hrun
          cases hrun
      | some st1 =>
          rw [hs] at hrun
          exact ih st1 (borrowckStep_preserves_invariant st st1 a hinv hs) hrun

theorem borrowckTrace_no_write_or_read_race_when_activated
    (st : BorrowckTwoPhaseState) (tr : List TwoPhaseAction) (st' : BorrowckTwoPhaseState)
    (hinv : BorrowckInvariant st)
    (hrun : runBorrowckTrace st tr = some st') :
    st'.phase = .activated → st'.priorSharedCount = 0 ∧ st'.otherMutActive = false :=
  (borrowckTrace_preserves_invariant tr st st' hinv hrun).1

/-! ### Tree Borrows `Reserved` Permission State Machine (`tree_borrows/perms.rs:135-233`) -/

inductive TBState where
  | tbReserved (conflicted : Bool)
  | tbUnique
  | tbFrozen
  | tbDisabled

inductive TBAccess where
  | childRead
  | childWrite
  | foreignRead
  | foreignWrite

/-- Exact `Freeze` permission transition table from
    `src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs:135-233`.
    Returns `none` on Tree Borrows UB. -/
noncomputable def tbStep (isProtected : Bool) (acc : TBAccess) (s : TBState) : Option TBState :=
  match acc, s with
  | .childRead, .tbDisabled => none
  | .childRead, s' => some s'
  | .foreignRead, .tbReserved c =>
      if isProtected then some (.tbReserved true) else some (.tbReserved c)
  | .foreignRead, .tbUnique =>
      if isProtected then some .tbDisabled else some .tbFrozen
  | .foreignRead, s' => some s'
  | .childWrite, .tbReserved true =>
      if isProtected then none else some .tbUnique
  | .childWrite, .tbReserved false => some .tbUnique
  | .childWrite, .tbUnique => some .tbUnique
  | .childWrite, .tbFrozen => none
  | .childWrite, .tbDisabled => none
  | .foreignWrite, _ => some .tbDisabled

noncomputable def runTBTrace (isProtected : Bool) (s : TBState) : List TBAccess → Option TBState
  | [] => some s
  | a :: rest =>
      match tbStep isProtected a s with
      | none => none
      | some s' => runTBTrace isProtected s' rest

noncomputable def twoPhaseActionToTB : TwoPhaseAction → Option TBAccess
  | .sharedRead => some .foreignRead
  | .startPriorShared => some .foreignRead
  | .endPriorShared => none
  | .reserveTwoPhase => none
  | .activateTwoPhase => some .childWrite
  | .directWrite => some .foreignWrite
  | .nestedReserveTwoPhase => some .foreignWrite
  | .releaseTwoPhase => none

/-- Simulation coupling between borrowck two-phase state and unprotected Tree
    Borrows tag state (`RetagKind::TwoPhase`, `isProtected = false`). -/
noncomputable def TBMatchesBorrowck (st : BorrowckTwoPhaseState) (tb : TBState) : Prop :=
  (st.phase = .reserved → tb = .tbReserved false) ∧
  (st.phase = .activated → tb = .tbUnique)

theorem unprotected_foreign_reads_preserve_reserved_nonconflicted :
    tbStep false .foreignRead (.tbReserved false) = some (.tbReserved false) := rfl

theorem unprotected_activation_succeeds_to_unique :
    tbStep false .childWrite (.tbReserved false) = some .tbUnique := rfl

theorem protected_foreign_read_then_child_write_is_tb_ub :
    runTBTrace true (.tbReserved false) [.foreignRead, .childWrite] = none := rfl

/-- Step-wise correspondence: for any borrowck-accepted action while in
    `.reserved` or `.activated` (and `reserveTwoPhase`), unprotected Tree Borrows
    (`isProtected = false`) never triggers UB and preserves `TBMatchesBorrowck`! -/
theorem borrowck_step_unprotected_tb_sound
    (st st' : BorrowckTwoPhaseState) (tb : TBState) (act : TwoPhaseAction)
    (hmatch : TBMatchesBorrowck st tb)
    (hstep : borrowckStep st act = some st')
    (hinit : st.phase = .unreserved → tb = .tbReserved false) :
    ∃ tb',
      (match twoPhaseActionToTB act with
       | none => tb' = tb
       | some acc => tbStep false acc tb = some tb') ∧
      TBMatchesBorrowck st' tb' := by
  rcases st with ⟨ph, cnt, om⟩
  rcases hmatch with ⟨hres, hact⟩
  cases act
  · -- startPriorShared (foreignRead)
    cases ph <;> cases om <;> simp [borrowckStep] at hstep
    · cases hstep
      refine ⟨.tbReserved false, ?_, ?_⟩
      · rw [hinit rfl]; rfl
      · exact And.intro (fun h => nomatch h) (fun h => nomatch h)
    · cases hstep
      refine ⟨.tbReserved false, ?_, ?_⟩
      · rw [hres rfl]; rfl
      · exact And.intro (fun _ => rfl) (fun h => nomatch h)
    · cases hstep
      cases tb with
      | tbReserved c => exact ⟨.tbReserved c, rfl, And.intro (fun h => nomatch h) (fun h => nomatch h)⟩
      | tbUnique => exact ⟨.tbFrozen, rfl, And.intro (fun h => nomatch h) (fun h => nomatch h)⟩
      | tbFrozen => exact ⟨.tbFrozen, rfl, And.intro (fun h => nomatch h) (fun h => nomatch h)⟩
      | tbDisabled => exact ⟨.tbDisabled, rfl, And.intro (fun h => nomatch h) (fun h => nomatch h)⟩
  · -- endPriorShared (none)
    cases cnt with
    | zero => simp [borrowckStep] at hstep
    | succ n =>
        simp [borrowckStep] at hstep
        cases hstep
        exact ⟨tb, rfl, ⟨hres, hact⟩⟩
  · -- reserveTwoPhase (none)
    cases ph <;> cases om <;> simp [borrowckStep] at hstep
    cases hstep
    refine ⟨tb, rfl, ?_⟩
    exact And.intro (fun _ => hinit rfl) (fun h => nomatch h)
  · -- sharedRead (foreignRead)
    cases ph <;> cases om <;> simp [borrowckStep] at hstep
    · cases hstep
      refine ⟨.tbReserved false, ?_, ?_⟩
      · rw [hinit rfl]; rfl
      · exact And.intro (fun h => nomatch h) (fun h => nomatch h)
    · cases hstep
      refine ⟨.tbReserved false, ?_, ?_⟩
      · rw [hres rfl]; rfl
      · exact And.intro (fun _ => rfl) (fun h => nomatch h)
    · cases hstep
      cases tb with
      | tbReserved c => exact ⟨.tbReserved c, rfl, And.intro (fun h => nomatch h) (fun h => nomatch h)⟩
      | tbUnique => exact ⟨.tbFrozen, rfl, And.intro (fun h => nomatch h) (fun h => nomatch h)⟩
      | tbFrozen => exact ⟨.tbFrozen, rfl, And.intro (fun h => nomatch h) (fun h => nomatch h)⟩
      | tbDisabled => exact ⟨.tbDisabled, rfl, And.intro (fun h => nomatch h) (fun h => nomatch h)⟩
  · -- directWrite (foreignWrite)
    cases ph <;> cases cnt <;> cases om <;> simp [borrowckStep] at hstep
    all_goals (cases hstep; exact ⟨.tbDisabled, rfl, And.intro (fun h => nomatch h) (fun h => nomatch h)⟩)
  · -- nestedReserveTwoPhase (foreignWrite)
    cases ph <;> cases cnt <;> cases om <;> simp [borrowckStep] at hstep
    all_goals (cases hstep; exact ⟨.tbDisabled, rfl, And.intro (fun h => nomatch h) (fun h => nomatch h)⟩)
  · -- activateTwoPhase (childWrite)
    cases ph <;> cases cnt <;> cases om <;> simp [borrowckStep] at hstep
    cases hstep
    refine ⟨.tbUnique, ?_, ?_⟩
    · rw [hres rfl]; rfl
    · exact And.intro (fun h => nomatch h) (fun _ => rfl)
  · -- releaseTwoPhase (none)
    cases ph <;> simp [borrowckStep] at hstep
    all_goals (cases hstep; exact ⟨tb, rfl, And.intro (fun h => nomatch h) (fun h => nomatch h)⟩)

/-! ### Concrete Witnesses Matching `c1`..`c6` -/

noncomputable def traceC1VecPushLen : List TwoPhaseAction :=
  [.reserveTwoPhase, .sharedRead, .activateTwoPhase, .releaseTwoPhase]

noncomputable def traceC2WriteWhileReserved : List TwoPhaseAction :=
  [.reserveTwoPhase, .directWrite]

noncomputable def traceC3NestedReserveWhileReserved : List TwoPhaseAction :=
  [.reserveTwoPhase, .nestedReserveTwoPhase]

noncomputable def traceC4ExplicitMutThenRead : List TwoPhaseAction :=
  [.reserveTwoPhase, .activateTwoPhase, .sharedRead]

noncomputable def traceC5PriorSharedEndsBeforeActivation : List TwoPhaseAction :=
  [.startPriorShared, .reserveTwoPhase, .sharedRead, .endPriorShared, .activateTwoPhase, .releaseTwoPhase]

noncomputable def traceC6PriorSharedLiveAtActivation : List TwoPhaseAction :=
  [.startPriorShared, .reserveTwoPhase, .sharedRead, .activateTwoPhase]

theorem twoPhase_empirical_correspondence :
    (∃ st, runBorrowckTrace BorrowckTwoPhaseState.init traceC1VecPushLen = some st ∧ st.phase = .released) ∧
    runBorrowckTrace BorrowckTwoPhaseState.init traceC2WriteWhileReserved = none ∧
    runBorrowckTrace BorrowckTwoPhaseState.init traceC3NestedReserveWhileReserved = none ∧
    runBorrowckTrace BorrowckTwoPhaseState.init traceC4ExplicitMutThenRead = none ∧
    (∃ st, runBorrowckTrace BorrowckTwoPhaseState.init traceC5PriorSharedEndsBeforeActivation = some st ∧
        st.phase = .released) ∧
    runBorrowckTrace BorrowckTwoPhaseState.init traceC6PriorSharedLiveAtActivation = none ∧
    runTBTrace false (.tbReserved false) [.foreignRead, .childWrite] = some .tbUnique ∧
    runTBTrace true (.tbReserved false) [.foreignRead, .childWrite] = none := by
  exact ⟨
    ⟨{ phase := .released, priorSharedCount := 0, otherMutActive := false }, rfl, rfl⟩,
    rfl,
    rfl,
    rfl,
    ⟨{ phase := .released, priorSharedCount := 0, otherMutActive := false }, rfl, rfl⟩,
    rfl,
    rfl,
    rfl
  ⟩

end PoloniusTriadSoundness
