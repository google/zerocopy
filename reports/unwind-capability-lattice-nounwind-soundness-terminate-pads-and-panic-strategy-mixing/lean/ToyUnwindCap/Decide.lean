import ToyUnwindCap.Basic

/-!
# Boolean checkers for concrete programs

Executable versions of the hypotheses, each with a soundness lemma, so that facts about
concrete example programs can be established by kernel evaluation (`decide`).
-/

namespace Toy.UnwindCap

/-- Executable check of the enforcement condition of one statement of `g`. -/
def stmtEnforcedB (cu : Prec) (p : Prog) (g : Nat) : Stmt → Bool
  | .raise act => !p.handler.unwinds || act.Stops
  | .call f act => !p.viewMay cu g f || act.Stops

/-- Executable `Enforced`. -/
def enforcedB (cu : Prec) (p : Prog) : Bool :=
  (List.range p.fns.length).all fun g =>
    (p.fn g).info.foreign || p.selfMay cu g || (p.fn g).body.all (stmtEnforcedB cu p g)

theorem enforced_of_enforcedB (cu : Prec) (p : Prog) (h : enforcedB cu p = true) :
    Enforced cu p := by
  intro g hfor hself
  by_cases hg : g < p.fns.length
  · have h1 := List.all_eq_true.1 h g (List.mem_range.2 hg)
    simp only [hfor, hself, Bool.false_or] at h1
    have h2 := List.all_eq_true.1 h1
    refine ⟨fun hh act hm => ?_, fun f act hm hv => ?_⟩
    · simpa [stmtEnforcedB, hh, Strategy.unwinds] using h2 _ hm
    · have := h2 _ hm
      simp only [stmtEnforcedB, hv, Bool.not_true, Bool.false_or] at this
      exact this
  · have hd := p.fn_of_ge (Nat.le_of_not_lt hg)
    refine ⟨fun _ act hm => ?_, fun f act hm _ => ?_⟩
    · rw [hd] at hm; simp [FnDef.dummy] at hm
    · rw [hd] at hm; simp [FnDef.dummy] at hm

/-- Executable `EnforcedAt`. -/
def enforcedAtB (cu : Prec) (p : Prog) (g : Nat) : Bool :=
  (p.fn g).info.foreign || p.selfMay cu g || (p.fn g).body.all (stmtEnforcedB cu p g)

theorem enforcedAt_of_enforcedAtB (cu : Prec) (p : Prog) (g : Nat)
    (h : enforcedAtB cu p g = true) : EnforcedAt cu p g := by
  intro hfor hself
  simp only [enforcedAtB, hfor, hself, Bool.false_or] at h
  have h2 := List.all_eq_true.1 h
  refine ⟨fun hh act hm => ?_, fun f act hm hv => ?_⟩
  · simpa [stmtEnforcedB, hh, Strategy.unwinds] using h2 _ hm
  · have := h2 _ hm
    simp only [stmtEnforcedB, hv, Bool.not_true, Bool.false_or] at this
    exact this

/-- Executable `ForeignCovered`. -/
def foreignCoveredB (cu : Prec) (p : Prog) : Bool :=
  (List.range p.fns.length).all fun f =>
    !(p.fn f).info.foreign || !(p.fn f).throws || p.selfMay cu f

theorem foreignCovered_of_foreignCoveredB (cu : Prec) (p : Prog)
    (h : foreignCoveredB cu p = true) : ForeignCovered cu p := by
  intro f hfor hth
  by_cases hg : f < p.fns.length
  · have := List.all_eq_true.1 h f (List.mem_range.2 hg)
    simpa [hfor, hth] using this
  · have hd := p.fn_of_ge (Nat.le_of_not_lt hg)
    rw [hd] at hfor; simp [FnDef.dummy] at hfor

/-- Executable check of call-site agreement for one statement of `g`. -/
def stmtAgreeB (cu : Prec) (p : Prog) (g : Nat) : Stmt → Bool
  | .raise _ => true
  | .call f act => act.Stops || p.viewMay cu g f || !p.selfMay cu f

/-- Executable `SiteAgreement`. -/
def siteAgreementB (cu : Prec) (p : Prog) : Bool :=
  (List.range p.fns.length).all fun g =>
    (p.fn g).info.foreign || (p.fn g).body.all (stmtAgreeB cu p g)

/-- Executable `SiteAgreementAt`. -/
def siteAgreementAtB (cu : Prec) (p : Prog) (g : Nat) : Bool :=
  (p.fn g).info.foreign || (p.fn g).body.all (stmtAgreeB cu p g)

theorem siteAgreementAt_of_siteAgreementAtB (cu : Prec) (p : Prog) (g : Nat)
    (h : siteAgreementAtB cu p g = true) : SiteAgreementAt cu p g := by
  intro f act hfor hm hst hv
  simp only [siteAgreementAtB, hfor, Bool.false_or] at h
  have := List.all_eq_true.1 h _ hm
  simpa [stmtAgreeB, hst, hv] using this

theorem siteAgreement_of_siteAgreementB (cu : Prec) (p : Prog)
    (h : siteAgreementB cu p = true) : SiteAgreement cu p := by
  intro g f act hfor hm hst hv
  by_cases hg : g < p.fns.length
  · have h1 := List.all_eq_true.1 h g (List.mem_range.2 hg)
    simp only [hfor, Bool.false_or] at h1
    have := List.all_eq_true.1 h1 _ hm
    simpa [stmtAgreeB, hst, hv] using this
  · have hd := p.fn_of_ge (Nat.le_of_not_lt hg)
    rw [hd] at hm; simp [FnDef.dummy] at hm

/-- Executable `ForeignHonest`. -/
def foreignHonestB (p : Prog) : Bool :=
  (List.range p.fns.length).all fun f =>
    !(p.fn f).info.foreign || !(p.fn f).throws ||
      ((p.fn f).info.abi == .cUnwind && !(p.fn f).info.neverUnwind)

theorem foreignHonest_of_foreignHonestB (p : Prog) (h : foreignHonestB p = true) :
    ForeignHonest p := by
  intro f hfor hth
  by_cases hg : f < p.fns.length
  · have := List.all_eq_true.1 h f (List.mem_range.2 hg)
    simp only [hfor, hth, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
      Bool.not_eq_true'] at this
    exact this
  · have hd := p.fn_of_ge (Nat.le_of_not_lt hg)
    rw [hd] at hfor; simp [FnDef.dummy] at hfor

/-- Executable `ForeignNotGlue`. -/
def foreignNotGlueB (p : Prog) : Bool :=
  (List.range p.fns.length).all fun f => !(p.fn f).info.foreign || !(p.fn f).info.dropGlue

theorem foreignNotGlue_of_foreignNotGlueB (p : Prog) (h : foreignNotGlueB p = true) :
    ForeignNotGlue p := by
  intro f hfor
  by_cases hg : f < p.fns.length
  · have := List.all_eq_true.1 h f (List.mem_range.2 hg)
    simpa [hfor] using this
  · have hd := p.fn_of_ge (Nat.le_of_not_lt hg)
    rw [hd] at hfor; simp [FnDef.dummy] at hfor

/-- Executable check of drop-glue agreement for one statement of `g`. -/
def stmtGlueB (p : Prog) (g : Nat) : Stmt → Bool
  | .raise _ => true
  | .call f act => !(p.fn f).info.dropGlue || act.Stops ||
      (p.crateOf g).panicInDrop == .unwind || (p.crateOf f).panicInDrop == .abort

/-- Executable `GlueAgreement`. -/
def glueAgreementB (p : Prog) : Bool :=
  (List.range p.fns.length).all fun g =>
    (p.fn g).info.foreign || (p.fn g).body.all (stmtGlueB p g)

theorem glueAgreement_of_glueAgreementB (p : Prog) (h : glueAgreementB p = true) :
    GlueAgreement p := by
  intro g f act hfor hm hdg hst hpid
  by_cases hg : g < p.fns.length
  · have h1 := List.all_eq_true.1 h g (List.mem_range.2 hg)
    simp only [hfor, Bool.false_or] at h1
    have := List.all_eq_true.1 h1 _ hm
    simp only [stmtGlueB, hdg, hst, hpid, Bool.not_true, Bool.or_false, Bool.false_or] at this
    simpa using this
  · have hd := p.fn_of_ge (Nat.le_of_not_lt hg)
    rw [hd] at hm; simp [FnDef.dummy] at hm

/-- Executable check that every crate uses the `unwind` strategy. -/
def allUnwindB (p : Prog) : Bool := p.crates.all fun c => c.panic == .unwind

/-- `LinkOK` holds when every crate uses the `unwind` strategy. -/
theorem linkOK_of_allUnwindB (p : Prog) (h : allUnwindB p = true) : LinkOK p := by
  intro _ c hc
  have := List.all_eq_true.1 h c hc
  simpa using this

/-- Executable check that the artifact is not potentially unwinding. -/
def notPotentiallyUnwindingB (p : Prog) : Bool :=
  p.handler == .abort && (List.range p.fns.length).all fun g =>
    (p.fn g).info.foreign || (p.crateOf g).panic == .abort ||
      (p.fn g).body.all fun s => match s with
        | .raise _ => true
        | .call f _ => !((p.fn f).info.abi == .cUnwind)

theorem not_potentiallyUnwinding_of_B (p : Prog) (h : notPotentiallyUnwindingB p = true) :
    ¬ PotentiallyUnwinding p := by
  simp only [notPotentiallyUnwindingB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hh, hall⟩ := h
  rintro (hu | ⟨g, f, act, hfor, hpan, hm, habi⟩)
  · rw [hh] at hu; cases hu
  · by_cases hg : g < p.fns.length
    · have h1 := List.all_eq_true.1 hall g (List.mem_range.2 hg)
      simp only [hfor, hpan, Bool.false_or] at h1
      have h2 := List.all_eq_true.1 (by simpa using h1) _ hm
      simp [habi] at h2
    · have hd := p.fn_of_ge (Nat.le_of_not_lt hg)
      rw [hd] at hm; simp [FnDef.dummy] at hm

/-- `LinkOK` holds when the artifact is not potentially unwinding. -/
theorem linkOK_of_notPotentiallyUnwindingB (p : Prog) (h : notPotentiallyUnwindingB p = true) :
    LinkOK p := fun hpu => absurd hpu (not_potentiallyUnwinding_of_B p h)

end Toy.UnwindCap
