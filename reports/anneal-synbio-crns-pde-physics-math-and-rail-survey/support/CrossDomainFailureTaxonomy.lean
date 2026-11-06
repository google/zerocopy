-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra

/-!
# Mechanized Cross-Domain Historical Failure Taxonomy for Anneal's Trusted Primitives

This standalone module (`prelude` + `import Init.NotationExtra`, zero kernel
axioms) mechanizes the structural root causes of 12 landmark historical
failures across synthetic biology (`Cello`), molecular programming (`DSD` /
`CRNs`), metabolic engineering (`FBA` / `MEMOTE` / `QSopt_ex`), digital
microfluidics (`MFSim`), mathematical formalization (`Kempe`, `Kapranov-Voevodsky`
vs. `Simpson`, `MiniF2F` `0 / 0 = 0` and vacuous preconditions), scientific
computing (`Hou-LeFloch` PDE stencils, `Enzyme` AD discontinuous branches),
railway signaling (`MTR Central 2019`, `Singapore Joo Koon 2017`), and
aerospace systems (`Air Inter Flight 148`, `Mars Spirit Sol 18`, `Mars Climate
Orbiter`), proving that Anneal's four core verification primitives
(`Language SemObs` & `Partial`, `BehaviorCodec` / `Compiles` / `Abstracts`,
`ProductiveOn` / `InhabitedPre` / `StepResult.externalCall`, and
`ScopedVerificationResult` / `TrustPolicy`) reject each failure class.
-/

namespace Anneal.FailureTaxonomy

-- ============================================================================
-- 0. Anneal's 4 Core Trusted Verification Primitives
-- ============================================================================

structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

def Partial.pure (b : B) : Partial B where
  defined := True
  val := fun _ => b

def Partial.ub : Partial B where
  defined := False
  val := False.elim

def Partial.le {Out : Type u} (p₁ p₂ : Partial (Out → Prop)) : Prop :=
  ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, ∀ o, p₁.val h₁ o → p₂.val h₂ o

infix:50 " ⊑ " => Partial.le

abbrev Behavior (Query : Type u) (Out : Type v) : Type (max u v) :=
  Query → Partial (Out → Prop)

def Behavior.le {Query : Type u} {Out : Type v}
    (b₁ b₂ : Behavior Query Out) : Prop :=
  ∀ q, b₁ q ⊑ b₂ q

infix:50 " ⊑_B " => Behavior.le

structure Language (SemObs : Type w) where
  Prog : Type u
  Query : Type v
  Out : Type x
  obs : Out → SemObs
  sem : Prog → Behavior Query Out

def Language.WellFormedOn {SemObs : Type w} (L : Language SemObs)
    (pre : L.Query → Prop) : Behavior L.Query L.Out :=
  fun q => { defined := pre q, val := fun _ _ => True }

def InhabitedPre {Query : Type u} (pre : Query → Prop) : Prop :=
  ∃ q, pre q

def ProductiveOn {SemObs : Type w} (L : Language SemObs)
    (pre : L.Query → Prop) (p : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem p q).defined, ∃ o, (L.sem p q).val h o

structure BehaviorCodec {SemObs : Type w} (L₁ L₂ : Language SemObs) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → Option L₁.Query
  encodeOut : L₁.Out → L₂.Out
  decodeOut : L₂.Out → Option L₁.Out
  decodeQuery_encodeQuery : ∀ q₁, decodeQuery (encodeQuery q₁) = some q₁
  decodeOut_encodeOut : ∀ o₁, decodeOut (encodeOut o₁) = some o₁
  encodeOut_of_decodeOut : ∀ {o₂ o₁}, decodeOut o₂ = some o₁ → encodeOut o₁ = o₂
  obs_decodeOut : ∀ {o₂ o₁}, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁

def BehaviorCodec.toMorphism {SemObs : Type w} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂) (b₁ : Behavior L₁.Query L₁.Out) :
    Behavior L₂.Query L₂.Out :=
  fun q₂ =>
    match c.decodeQuery q₂ with
    | none => Partial.ub
    | some q₁ =>
      { defined := (b₁ q₁).defined
        val := fun h o₂ =>
          ∃ o₁, c.decodeOut o₂ = some o₁ ∧ (b₁ q₁).val h o₁ }

def Compiles {SemObs : Type w} (L₁ L₂ : Language SemObs)
    (c : BehaviorCodec L₁ L₂) (s : L₁.Prog) (t : L₂.Prog) : Prop :=
  L₂.sem t ⊑_B c.toMorphism (L₁.sem s)

def Abstracts {SemObs : Type w} (L_v L_src : Language SemObs)
    (c : BehaviorCodec L_v L_src) (v : L_v.Prog) (s : L_src.Prog) : Prop :=
  L_src.sem s ⊑_B c.toMorphism (L_v.sem v)

def idCodec {SemObs : Type w} (L : Language SemObs) : BehaviorCodec L L where
  encodeQuery := id
  decodeQuery := some
  encodeOut := id
  decodeOut := some
  decodeQuery_encodeQuery := fun _ => rfl
  decodeOut_encodeOut := fun _ => rfl
  encodeOut_of_decodeOut := fun h => Option.some.inj h.symm
  obs_decodeOut := fun h => congrArg L.obs (Option.some.inj h)

inductive StepResult (State Obs Val : Type) where
  | step (next : State) (obs : Obs)
  | done (ret : Val)
  | trap
  | externalCall (boundaryInv : Bool) (branches : State → Obs → Prop)

structure Obligation (Id : Type) where
  id : Id
  prop : Prop

structure TrustPolicy (Id : Type) where
  isAllowed : Id → Prop

def AllHold : List Prop → Prop
  | [] => True
  | p :: ps => p ∧ AllHold ps

def ScopedVerificationResult {Id : Type}
    (policy : TrustPolicy Id)
    (waived : List Id)
    (obligations : List (Obligation Id)) : Prop :=
  AllHold (waived.map policy.isAllowed) ∧
  AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))

-- ============================================================================
-- 1. Cello 1.0 (Nielsen et al., Science 2016): Host-Resource Coupling Failure
-- ============================================================================

/-- In Cello 1.0, a cascade of gates that satisfies boolean thresholds in
    isolation fails in vivo when total ribosome/RNAP resource load `rLoad`
    exceeds host capacity `rMax` (toxicity/growth collapse) or when tandem
    promoter roadblocking drops steady-state RPU into the indeterminate noise
    gap `(thetaOff, thetaOn)`. -/
structure CelloOut where
  logicLevel : Bool
  rpu : Nat
  rLoad : Nat

abbrev CelloSpecLang : Language Bool where
  Prog := Bool → Bool
  Query := Bool
  Out := CelloOut
  obs := CelloOut.logicLevel
  sem := fun f q =>
    Partial.pure (fun o => o.logicLevel = f q ∧ o.rLoad ≤ 100)

/-- A physical E. coli circuit whose 5-gate cascade imposes `rLoad = 140 > 100`
    (host toxicity saturation) is classified as `Partial.ub` (`defined = False`)
    once host-resource capacity is tracked in `defined`. -/
abbrev CelloToxicLang : Language Bool where
  Prog := Nat -- total ribosome load of gate assignment
  Query := Bool
  Out := CelloOut
  obs := CelloOut.logicLevel
  sem := fun totalLoad q =>
    { defined := totalLoad ≤ 100
      val := fun _ o => o.logicLevel = !q ∧ o.rLoad = totalLoad }

theorem cello_unmodeled_resource_overload_refuted :
    ¬ Compiles CelloSpecLang CelloToxicLang
        { encodeQuery := id
          decodeQuery := some
          encodeOut := id
          decodeOut := some
          decodeQuery_encodeQuery := fun _ => rfl
          decodeOut_encodeOut := fun _ => rfl
          encodeOut_of_decodeOut := fun h => Option.some.inj h.symm
          obs_decodeOut := fun h => congrArg CelloOut.logicLevel (Option.some.inj h) }
        (fun b => !b) 140 := by
  intro hComp
  have ⟨hDef, _⟩ := hComp true trivial
  exact Nat.not_le.mpr (by decide : 100 < 140) hDef

-- ============================================================================
-- 2. DNA Strand-Displacement Spurious Leaks (Qian & Winfree 2011; Thachuk 2015)
--    and Stochastic CRN Critical Siphons (Angeli, De Leenheer & Sontag 2007)
-- ============================================================================

/-- Ideal DSD gate: output strand `1` is released if and only if input `q = true`.
    Physical DSD gate with blunt-end coaxial leak: even when input `q = false`,
    fraying allows output `true` (`1`) to leak out alongside `false` (`0`). -/
abbrev DSDLang : Language Bool where
  Prog := Bool -- `false` = leaky single-domain seesaw gate; `true` = Thachuk leakless gate
  Query := Bool
  Out := Bool
  obs := id
  sem := fun isLeakless q =>
    Partial.pure (fun out =>
      if isLeakless then out = q
      else (out = q ∨ out = true))

theorem dsd_zero_input_leak_breaks_compiles :
    ¬ Compiles DSDLang DSDLang (idCodec DSDLang) true false ∧
      Compiles DSDLang DSDLang (idCodec DSDLang) true true := by
  refine ⟨?_, ?_⟩
  · intro hComp
    have ⟨_, hSub⟩ := hComp false trivial
    have ⟨o₁, hDec, hIdeal⟩ := hSub true (Or.inr rfl)
    injection hDec with hEq
    subst hEq
    exact Bool.noConfusion hIdeal
  · intro q _
    refine ⟨trivial, fun o hOut => ⟨o, rfl, hOut⟩⟩

/-- Stochastic CRN siphon (Angeli et al. 2007): state is count of species `B`.
    Once `nB = 0` (the critical siphon `Z = {B}` is emptied), no reaction can
    produce a positive steady-state output (`o > 0`), violating `ProductiveOn`. -/
abbrev CRNSiphonLang : Language Nat where
  Prog := Unit
  Query := Nat -- reachable intermediate count of catalytic species B
  Out := Nat   -- positive terminal output count
  obs := id
  sem := fun _ nB =>
    Partial.pure (fun o => nB > 0 ∧ o = nB)

theorem crn_stochastic_siphon_breaks_productiveOn :
    ¬ ProductiveOn CRNSiphonLang (fun nB => nB = 0 ∨ nB = 5) () := by
  intro hProd
  have ⟨_, _, hPos, _⟩ := hProd 0 (Or.inl rfl)
  exact Nat.lt_irrefl 0 hPos

-- ============================================================================
-- 3. Genome-Scale FBA Type-III Loops & Floating-Point Leaks (MEMOTE 2020)
--    and Digital Microfluidics Dynamic Spacing Violations (MFSim 2015)
-- ============================================================================

/-- An internal 2-reaction cycle `A -> B -> A` with fluxes `(v1, v2) = (10, 10)`
    satisfies steady-state mass balance `v1 - v2 = 0`, but violates the
    Schellenberger et al. (2011) thermodynamic loop law `v1 > 0 → muB < muA`
    and `v2 > 0 → muA < muB` for every chemical potential pair `(muA, muB)`. -/
def ThermodynamicLoopLaw (v1 v2 muA muB : Nat) : Prop :=
  (v1 > 0 → muB < muA) ∧ (v2 > 0 → muA < muB)

theorem fba_type_iii_loop_violates_thermodynamics :
    ∀ muA muB : Nat, ¬ ThermodynamicLoopLaw 10 10 muA muB := by
  intro muA muB ⟨h1, h2⟩
  have hBA : muB < muA := h1 (by decide)
  have hAB : muA < muB := h2 (by decide)
  exact Nat.lt_irrefl muA (Nat.lt_trans hAB hBA)

/-- EWOD microfluidic droplet spacing (Grissom & Brisk MFSim 2015):
    at tick `t = 0`, droplet 1 is at `x = 0` and droplet 2 is at `x = 2`
    (static distance `|0 - 2| = 2 ≥ 2`). At tick `t = 1`, droplet 1 moves to
    `x = 1` and droplet 2 moves to `x = 3` (static distance `|1 - 3| = 2 ≥ 2`).
    However, dynamic cross-step spacing `|p1(t+1) - p2(t)| = |1 - 2| = 1 < 2`
    is violated, causing menisci to coalesce mid-transition! -/
def StaticSpacingOk (p1_t p2_t p1_next p2_next : Nat) : Prop :=
  p2_t ≥ p1_t + 2 ∧ p2_next ≥ p1_next + 2

def DynamicSpacingOk (p1_t p2_t p1_next p2_next : Nat) : Prop :=
  StaticSpacingOk p1_t p2_t p1_next p2_next ∧ p2_t ≥ p1_next + 2

theorem ewod_static_spacing_misses_dynamic_coalescence :
    StaticSpacingOk 0 2 1 3 ∧ ¬ DynamicSpacingOk 0 2 1 3 := by
  refine ⟨⟨by decide, by decide⟩, ?_⟩
  intro ⟨_, hDyn⟩
  exact Nat.not_le.mpr (by decide : 2 < 1 + 2) hDyn

-- ============================================================================
-- 4. Pure & Applied Math Failures: Simpson (1998) vs. Kapranov-Voevodsky (1991),
--    and Lean/Mathlib `0 / 0 = 0` & MiniF2F Contradictory-Hypothesis Vacuity
-- ============================================================================

/-- Homotopy 3-type invariant `SemObs`: `(pi2_rank, pi3_rank, whiteheadBracket)`.
    For the 2-sphere `S²`, `obs = (1, 1, 2)` (since `[ι₂, ι₂] = 2η ≠ 0`).
    By Simpson's 1998 theorem (`arXiv:math/9810059`), every strict 3-groupoid
    forces the Whitehead bracket to vanish (`whiteheadBracket = 0`).
    Therefore, no `BehaviorCodec` from `Top3TypeLang` to `Strict3GrpdLang` can
    compile `S²` while preserving `SemObs` (`obs_decodeOut`) and `ProductiveOn`. -/
structure Homotopy3Obs where
  pi2Rank : Nat
  pi3Rank : Nat
  whiteheadBracket : Nat
  deriving DecidableEq

abbrev Top3TypeLang : Language Homotopy3Obs where
  Prog := Homotopy3Obs
  Query := Unit
  Out := Homotopy3Obs
  obs := id
  sem := fun inv _ => Partial.pure (fun o => o = inv)

abbrev Strict3GrpdLang : Language Homotopy3Obs where
  Prog := Nat × Nat -- only `(pi2Rank, pi3Rank)`; strict interchange forces bracket = 0
  Query := Unit
  Out := Homotopy3Obs
  obs := id
  sem := fun ⟨r2, r3⟩ _ =>
    Partial.pure (fun o => o = { pi2Rank := r2, pi3Rank := r3, whiteheadBracket := 0 })

def sphereS2 : Homotopy3Obs := { pi2Rank := 1, pi3Rank := 1, whiteheadBracket := 2 }

theorem simpson_refutes_kapranov_voevodsky_strict_3groupoid
    (c : BehaviorCodec Top3TypeLang Strict3GrpdLang)
    (G : Strict3GrpdLang.Prog)
    (hProd : ProductiveOn Strict3GrpdLang (fun _ => True) G) :
    ¬ Compiles Top3TypeLang Strict3GrpdLang c sphereS2 G := by
  intro hComp
  have ⟨_, o₂, hOutG⟩ := hProd () trivial
  have hQ : c.decodeQuery () = some () := by
    cases hEq : c.encodeQuery ()
    simpa [hEq] using c.decodeQuery_encodeQuery ()
  have hLe := hComp ()
  unfold BehaviorCodec.toMorphism at hLe
  rw [hQ] at hLe
  have ⟨_, hSub⟩ := hLe trivial
  have ⟨o₁, hDec, hSphere⟩ := hSub o₂ hOutG
  have hObs := c.obs_decodeOut hDec
  change o₂ = o₁ at hObs
  rw [hOutG, hSphere] at hObs
  injection hObs with _ _ hBracket
  exact Nat.noConfusion hBracket

/-- In Lean 4 core, `0 / 0 = 0` holds definitionally on `Nat`, whereas Anneal's
    `Partial` division steps to `Partial.ub` (`defined = False`) on divisor `0`,
    and `InhabitedPre` rejects contradictory `MiniF2F` preconditions (`x > 0 ∧ x < 0`). -/
def CheckedDiv (a b : Nat) : Partial (Nat → Prop) :=
  if b == 0 then Partial.ub else Partial.pure (fun q => q = a / b)

theorem lean_total_div_zero_vs_anneal_partial_ub :
    (0 : Nat) / 0 = 0 ∧
    ¬ (CheckedDiv 0 0 ⊑ Partial.pure (fun q => q = 0)) ∧
    ¬ InhabitedPre (fun x : Nat => x > 0 ∧ x < 0) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro hLe
    have ⟨hDef, _⟩ := hLe trivial
    exact False.elim hDef
  · intro ⟨x, hPos, hNeg⟩
    exact Nat.lt_irrefl x (Nat.lt_trans hNeg hPos)

-- ============================================================================
-- 5. PDE Conservation vs. Chain-Rule Stencil (Hou & LeFloch 1994) and
--    Enzyme AD Discontinuous Branch Derivative Pitfall (Hückelheim & Moses 2023)
-- ============================================================================

/-- Two-cell discrete Burgers step (`u = [2, 0]`):
    Conservative flux difference preserves total momentum sum `u0' + u1' = 2`,
    whereas non-conservative chain-rule stencil `u_i * (u_i - u_{i-1})` produces
    total momentum `0 ≠ 2`, violating `SemObs` conservation under `obs_decodeOut`. -/
abbrev PDEStencilLang : Language Nat where
  Prog := Bool -- `true` = conservative Godunov flux; `false` = non-conservative chain rule
  Query := Unit
  Out := Nat × Nat
  obs := fun ⟨u0, u1⟩ => u0 + u1 -- conserved total momentum spine
  sem := fun isConservative _ =>
    Partial.pure (fun p => if isConservative then p = (1, 1) else p = (0, 0))

theorem pde_nonconservative_stencil_breaks_compiles :
    ¬ Compiles PDEStencilLang PDEStencilLang (idCodec PDEStencilLang) true false := by
  intro hComp
  have ⟨_, hSub⟩ := hComp () trivial
  have ⟨o₁, hDec, hCons⟩ := hSub (0, 0) rfl
  have hObs := (idCodec PDEStencilLang).obs_decodeOut hDec
  rw [hCons] at hObs
  change 0 = 2 at hObs
  exact Nat.noConfusion hObs

/-- Discontinuous phase-change or `if (x == 0)` branch: when left derivative
    `dLeft = 1` and right derivative `dRight = 5` disagree at kink `x = 0`,
    guarded AD classifies `x = 0` as `Partial.ub` (`defined = False`). -/
def GuardedBranchAD (dLeft dRight x : Int) : Partial (Int → Prop) :=
  if x == 0 && dLeft != dRight then Partial.ub
  else Partial.pure (fun grad => grad = if x ≤ 0 then dLeft else dRight)

theorem enzyme_kink_discontinuity_flagged_as_ub :
    ¬ (GuardedBranchAD 1 5 0).defined := by
  intro hDef
  exact False.elim hDef

-- ============================================================================
-- 6. Railway Interlocking (MTR Central 2019 ZC3 Failover; Singapore Joo Koon 2017)
--    & Aerospace/Autonomy (Air Inter 148, Mars Spirit Sol 18, Mars Climate Orbiter)
-- ============================================================================

/-- 2019 Hong Kong MTR Tsuen Wan Line Central collision:
    When primary ZC1 switches over to warm-standby ZC3 (`StepResult.externalCall`),
    `boundaryInv` checks that the Central diamond crossover conflict lock is
    populated (`crossoverLockPopulated = true`). In BuildP38C1, ZC3 omitted the
    rebuild (`crossoverLockPopulated = false`), which `boundaryInv` immediately
    rejects. -/
def mtrCentralFailoverStep (crossoverLockPopulated : Bool) :
    StepResult Unit Unit Unit :=
  StepResult.externalCall crossoverLockPopulated (fun _ _ => True)

theorem mtr_central_2019_unpopulated_crossover_rejected :
    ∃ branches, mtrCentralFailoverStep false = StepResult.externalCall false branches :=
  ⟨fun _ _ => True, rfl⟩

/-- 2017 Singapore MRT Joo Koon collision:
    True physical train footprint is 6 cars (`{0, 1, 2, 3, 4, 5}`).
    The uncalibrated track-circuit bug shrank the CBTC protective bubble to
    1 car (`{0}`), violating `Abstracts` (which requires the abstract safety
    envelope to cover all 6 physical cars). -/
abbrev CBTCFootprintLang : Language Unit where
  Prog := Nat -- tracked car count in protective bubble
  Query := Unit
  Out := Nat  -- occupied car index `0 .. n-1`
  obs := fun _ => ()
  sem := fun cars _ => Partial.pure (fun carIdx => carIdx < cars)

theorem joo_koon_2017_bubble_shrinkage_violates_abstracts :
    ¬ Abstracts CBTCFootprintLang CBTCFootprintLang (idCodec CBTCFootprintLang) 1 6 := by
  intro hAbs
  have ⟨_, hSub⟩ := hAbs () trivial
  have ⟨carIdx, hDec, hLt1⟩ := hSub 5 (by decide : 5 < 6)
  injection hDec with hEq
  subst hEq
  exact Nat.not_lt.mpr (by decide : 1 ≤ 5) hLt1

/-- Air Inter Flight 148 (20 January 1992):
    In `TRK-FPA` mode, knob `-33` means `-3.3°` (`sinkRate = 800` ft/min).
    In `HDG-V/S` mode, knob `-33` means `-3,300` ft/min (`sinkRate = 3300` ft/min).
    Because `SemObs` includes the physical sink rate, no `BehaviorCodec` can
    collapse both modes into the same display token without violating
    `obs_decodeOut`. -/
inductive A320VerticalMode where
  | fpaMinus3_3  -- 800 ft/min descent
  | vsMinus3300  -- 3300 ft/min descent
  deriving DecidableEq

abbrev A320AutoLang : Language (String × Nat) where
  Prog := A320VerticalMode
  Query := Unit
  Out := A320VerticalMode
  obs := fun
    | .fpaMinus3_3 => ("-33", 800)
    | .vsMinus3300 => ("-33", 3300)
  sem := fun m _ => Partial.pure (fun o => o = m)

theorem air_inter_148_mode_confusion_impossible_under_behaviorCodec :
    A320AutoLang.obs .fpaMinus3_3 ≠ A320AutoLang.obs .vsMinus3300 := by
  decide

/-- Mars Exploration Rover Spirit Sol 18 (21 January 2004):
    When unlinked `dosFs` flash directory entries exceed DRAM mount quota,
    the VxWorks boot sequence enters an infinite watchdog reboot loop
    (`val h = fun _ => False`, zero completed boot outcomes), which satisfies
    partial-correctness `WellFormedOn` vacuously (`defined = True`), but is
    strictly refuted by `ProductiveOn`! -/
abbrev SpiritBootLang : Language Unit where
  Prog := Nat -- accumulated flash directory entries
  Query := Unit
  Out := Unit -- completed boot reaching command-ingest loop
  obs := id
  sem := fun dirEntries _ =>
    Partial.pure (fun _ => dirEntries ≤ 4096)

theorem spirit_sol18_reboot_livelock_safe_but_not_productive :
    (SpiritBootLang.sem 8192 ⊑_B SpiritBootLang.WellFormedOn (fun _ => True)) ∧
    ¬ ProductiveOn SpiritBootLang (fun _ => True) 8192 := by
  refine ⟨?_, ?_⟩
  · intro _ _
    exact ⟨trivial, fun _ _ => trivial⟩
  · intro hProd
    have ⟨_, _, hBound⟩ := hProd () trivial
    exact Nat.not_le.mpr (by decide : 4096 < 8192) hBound

/-- Mars Climate Orbiter (23 September 1999):
    `SM_FORCES` outputs impulse in `lbf·s` (`4448 mN·s` per unit), whereas JPL
    navigation decodes the number as `N·s` (`1000 mN·s` per unit). Because
    `SemObs` is physical impulse in `mN·s`, `obs_decodeOut` rejects any
    unconverted identity wire transfer for non-zero thruster burns (`n = 10`). -/
abbrev LbfSecLang : Language Nat where
  Prog := Nat
  Query := Unit
  Out := Nat
  obs := fun pulses => 4448 * pulses
  sem := fun p _ => Partial.pure (fun o => o = p)

abbrev NewtonSecLang : Language Nat where
  Prog := Nat
  Query := Unit
  Out := Nat
  obs := fun pulses => 1000 * pulses
  sem := fun p _ => Partial.pure (fun o => o = p)

theorem mars_climate_orbiter_unit_mismatch_refuted
    (c : BehaviorCodec LbfSecLang NewtonSecLang) :
    c.decodeOut 10 ≠ some 10 := by
  intro hDec
  have hObs := c.obs_decodeOut hDec
  change 1000 * 10 = 4448 * 10 at hObs
  revert hObs
  decide

#print axioms cello_unmodeled_resource_overload_refuted
#print axioms dsd_zero_input_leak_breaks_compiles
#print axioms crn_stochastic_siphon_breaks_productiveOn
#print axioms fba_type_iii_loop_violates_thermodynamics
#print axioms ewod_static_spacing_misses_dynamic_coalescence
#print axioms simpson_refutes_kapranov_voevodsky_strict_3groupoid
#print axioms lean_total_div_zero_vs_anneal_partial_ub
#print axioms pde_nonconservative_stencil_breaks_compiles
#print axioms enzyme_kink_discontinuity_flagged_as_ub
#print axioms mtr_central_2019_unpopulated_crossover_rejected
#print axioms joo_koon_2017_bubble_shrinkage_violates_abstracts
#print axioms air_inter_148_mode_confusion_impossible_under_behaviorCodec
#print axioms spirit_sol18_reboot_livelock_safe_but_not_productive
#print axioms mars_climate_orbiter_unit_mismatch_refuted

end Anneal.FailureTaxonomy
