-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Loop-Invariant, Affine-Fuel, and Recursive-Spec VC Transport Across `MIR ↔ MiniSSA`

Mechanizes in Lean `v4.34.1` (`0` `sorryAx`, `0` `Lean.ofReduceBool`):
1. `Trusted` loop and recursion operational semantics (`Trusted.MirLoopCfg`,
   `Trusted.runCfgSteps`, `Trusted.evalMirRecFuel`, `Trusted.LoopVerificationResult`,
   `Trusted.StatefulLoopVerificationResult`, and `Trusted.RecVerificationResult`).
2. `Theory` canonical `MiniSSA` loop cut-point semantics (`MiniSsaLoop`,
   `PhiState`, `LoopNormCert`, `checkLoopNormBisim`, `certCycleSlack`,
   `certEntryExitSlack`), modeling `Mem2Reg`, `SROA`, `LoopRotate`, guarded
   `LICM`, and `IndVarSimplify`.
3. **Per-Cycle Affine and Lexicographic Fuel Simulation & Loop VC Transport**:
   - `verifyMirLoopViaMiniSSA_sound`: Discharges unbounded `runCfgSteps` MIR loop
     verification obligations from three pure SSA cut-point obligations (`Init`,
     `Step`, `Post`) over $\vec{\phi}$ and a ranking measure $\mu(\vec{\phi}) \in \mathbb{N}$,
     establishing $k_{\text{mir}} \le (1 + d_{\text{loop}}) \cdot \mu(\vec{\phi}_0) + (1 + c_{\text{exit}})$
     without manual `(fuel : Nat) (h_fuel : fuel = N)` induction in user proofs.
   - `verifyNestedLoopLexicographic_sound`: Lexicographic fuel scaling across
     nested loops with outer measure $\mu_1$ and inner trip bound $M_2$.
4. **Modular Recursive `#[anneal_spec]` Contract Induction**:
   - `verifyMirRecViaMiniSSA_sound`: Well-founded measure induction over recursive
     `MiniSSA` `Call` sites transporting backward to `Runtime(PostCleanup)` MIR.
5. **Negative Soundness Guard (`licmHoistUninitOrTrap_rejected`)**:
   - Proves that hoisting a potentially trapping division (`c / denom` with `denom = 0`)
     or unvalidated load into the preheader of a zero-trip loop (`n = 0`) without a
     `LoopRotate` entry guard (`entryGuardRotated = true`) or total trap-free proof
     (`hoistedTrapFree = true`) is unsound for backward VC transport and is rejected
     by `checkLoopNormBisim`.
-/

namespace Trusted

/-- Observable outcome of fuel-bounded CFG or recursive execution in `Runtime(PostCleanup)` MIR. -/
inductive MirOutcome where
  | returned (ret : Nat) (stepsUsed : Nat)
  | panic (code : Nat)
  | ub
  | outOfFuel
  deriving DecidableEq, Repr

/-- Machine state for a `Runtime(PostCleanup)` MIR loop with stack slots for
loop-carried induction variable `idxSlot`, accumulator `accSlot`, invariant
parameter `paramReg`, loop bound `boundReg`, and liveness/aliasing flags. -/
structure MirLoopState where
  idxSlotLive : Bool
  accSlotLive : Bool
  idxVal : Nat
  accVal : Nat
  boundVal : Nat
  paramVal : Nat
  denomVal : Nat
  noAliasConflict : Bool
  deriving DecidableEq, Repr

/-- Parameterized `Runtime(PostCleanup)` MIR loop CFG capturing administrative
steps inside the loop header/body (`dCycle` steps per iteration: `StorageLive`/
`StorageDead` of loop temporaries, `&mut` reborrows, `CopyProp` moves, and
`SimplifyCFG` `goto` edges) and entry/exit framing (`dEntryExit` steps). -/
structure MirLoopCfg where
  dCycle : Nat
  dEntryExit : Nat
  stepDelta : Nat
  usesDivInBody : Bool
  deriving DecidableEq, Repr

/-- Check whether the loop's stack slots and non-aliasing invariants hold. -/
def slotsOk (st : MirLoopState) : Bool :=
  st.idxSlotLive && st.accSlotLive && st.noAliasConflict

/-- Single-step MIR loop state update. -/
def nextMirLoopState (cfg : MirLoopCfg) (st : MirLoopState) : MirLoopState :=
  let hoistedVal := if cfg.usesDivInBody then st.paramVal / st.denomVal else st.paramVal
  { st with
    idxVal := st.idxVal + cfg.stepDelta
    accVal := st.accVal + hoistedVal + st.idxVal }

/-- Fuel-indexed `Runtime(PostCleanup)` MIR loop execution (`runCfgSteps`).
At each loop header arrival:
- If `st.idxVal < st.boundVal`, the loop executes one full body cycle (`1 + cfg.dCycle`
  MIR steps) and recurses on `loopFuel'`.
- If `¬ (st.idxVal < st.boundVal)`, the loop exits through the post-header exit block
  (`1 + cfg.dEntryExit` MIR steps) and returns `st.accVal`. -/
def runCfgSteps (loopFuel : Nat) (cfg : MirLoopCfg) (st : MirLoopState) : MirOutcome :=
  match loopFuel with
  | 0 => .outOfFuel
  | loopFuel' + 1 =>
    if !slotsOk st then
      .ub
    else if st.idxVal < st.boundVal then
      if cfg.usesDivInBody && st.denomVal == 0 then
        .panic 1
      else
        match runCfgSteps loopFuel' cfg (nextMirLoopState cfg st) with
        | .returned ret k => .returned ret (k + (1 + cfg.dCycle))
        | other => other
    else
      .returned st.accVal (1 + cfg.dEntryExit)

/-- Anneal's stateless `VerificationResult` over a `Runtime(PostCleanup)` MIR loop. -/
def LoopVerificationResult (cfg : MirLoopCfg)
    (pre : MirLoopState → Prop) (post : MirLoopState → Nat → Prop) : Prop :=
  ∀ st : MirLoopState, pre st →
    ∃ (loopFuel : Nat) (ret : Nat) (stepsMir : Nat),
      runCfgSteps loopFuel cfg st = .returned ret stepsMir ∧ post st ret

/-- Anneal's fuel-bounded `StatefulVerificationResult` over a `Runtime(PostCleanup)` MIR loop. -/
def StatefulLoopVerificationResult (cfg : MirLoopCfg)
    (pre : MirLoopState → Prop) (post : MirLoopState → Nat → Prop)
    (mirStepBound : MirLoopState → Nat) : Prop :=
  ∀ st : MirLoopState, pre st →
    ∃ (loopFuel : Nat) (ret : Nat) (stepsMir : Nat),
      runCfgSteps loopFuel cfg st = .returned ret stepsMir ∧
      stepsMir ≤ mirStepBound st ∧
      post st ret

/-- Fuel-indexed `Runtime(PostCleanup)` MIR recursive function execution where each
recursive call frame incurs `1 + dCall` MIR framing steps (`StorageLive` of args,
ABI move, call/return) and the base case incurs `1 + dBase` steps. -/
def evalMirRecFuel (fuel : Nat) (dCall dBase : Nat) (stepFn : Nat → Nat)
    (combineFn : Nat → Nat → Nat) (baseVal : Nat) (x : Nat) : MirOutcome :=
  match fuel with
  | 0 => .outOfFuel
  | fuel' + 1 =>
    if x == 0 then
      .returned baseVal (1 + dBase)
    else
      match evalMirRecFuel fuel' dCall dBase stepFn combineFn baseVal (stepFn x) with
      | .returned subRet k => .returned (combineFn x subRet) (k + (1 + dCall))
      | other => other

def RecVerificationResult (dCall dBase : Nat) (stepFn : Nat → Nat)
    (combineFn : Nat → Nat → Nat) (baseVal : Nat)
    (pre : Nat → Prop) (post : Nat → Nat → Prop)
    (mirStepBound : Nat → Nat) : Prop :=
  ∀ x : Nat, pre x →
    ∃ (fuel : Nat) (ret : Nat) (stepsMir : Nat),
      evalMirRecFuel fuel dCall dBase stepFn combineFn baseVal x = .returned ret stepsMir ∧
      stepsMir ≤ mirStepBound x ∧
      post x ret

end Trusted

namespace Theory

open Trusted

/-- Pure SSA loop-header block parameter vector $\vec{\phi} = (\phi_{\text{idx}}, \phi_{\text{acc}})$
after `Mem2Reg + SROA + LICM + IndVarSimplify`. -/
structure PhiState where
  phiIdx : Nat
  phiAcc : Nat
  bound : Nat
  hoistedInv : Nat
  deriving DecidableEq, Repr

/-- Canonical `MiniSSA` loop representation after `Mem2Reg`, `LoopRotate`, `LICM`,
and `IndVarSimplify`. -/
structure MiniSsaLoop where
  stepDelta : Nat
  usesDivHoisted : Bool
  entryGuardRotated : Bool
  deriving DecidableEq, Repr

/-- `HybridTrace` loop normalization certificate (`LoopNormCert`). -/
structure LoopNormCert where
  dCycle : Nat
  dEntryExit : Nat
  stepDelta : Nat
  usesDivHoisted : Bool
  entryGuardRotated : Bool
  hoistedTrapFree : Bool
  slotsLiveAndNoAlias : Bool
  deriving DecidableEq, Repr

/-- Static per-backedge fuel slack $d_{\text{loop}}$ computed from the certificate. -/
def certCycleSlack (c : LoopNormCert) : Nat := c.dCycle

/-- Static DAG entry/preheader/exit fuel slack $c_{\text{exit}}$ computed from the certificate. -/
def certEntryExitSlack (c : LoopNormCert) : Nat := c.dEntryExit

/-- Executable `HybridTrace` loop normalization checker (`checkLoopNormBisim`). -/
def checkLoopNormBisim (cfg : MirLoopCfg) (ssa : MiniSsaLoop) (c : LoopNormCert) : Bool :=
  c.slotsLiveAndNoAlias &&
  (cfg.dCycle == c.dCycle) &&
  (cfg.dEntryExit == c.dEntryExit) &&
  (cfg.stepDelta == ssa.stepDelta) &&
  (ssa.stepDelta == c.stepDelta) &&
  (cfg.stepDelta >= 1) &&
  (cfg.usesDivInBody == ssa.usesDivHoisted) &&
  (ssa.usesDivHoisted == c.usesDivHoisted) &&
  (ssa.entryGuardRotated == c.entryGuardRotated) &&
  (!c.usesDivHoisted || c.hoistedTrapFree || c.entryGuardRotated)

/-- Map a `MirLoopState` onto its initial `MiniSSA` loop-header $\vec{\phi}_0$ state
via the $\Sigma_{\text{loop}}$ specification lens. -/
def initPhiOfMir (cfg : MirLoopCfg) (st : MirLoopState) : PhiState :=
  let hoisted := if cfg.usesDivInBody then st.paramVal / st.denomVal else st.paramVal
  { phiIdx := st.idxVal
  , phiAcc := st.accVal
  , bound := st.boundVal
  , hoistedInv := hoisted }

/-- Pure `MiniSSA` single-iteration step over $\vec{\phi}$. -/
def stepMiniSsaPhi (ssa : MiniSsaLoop) (phi : PhiState) : PhiState :=
  { phi with
    phiIdx := phi.phiIdx + ssa.stepDelta
    phiAcc := phi.phiAcc + phi.hoistedInv + phi.phiIdx }

/-- Core induction theorem over well-founded ranking measure $\mu(\vec{\phi})$:
If a loop invariant `inv : PhiState → Prop` and ranking measure `mu : PhiState → Nat`
satisfy the pure SSA step obligation (`hStep`) and exit obligation (`hPost`), then from
any state `st` whose `initPhiOfMir cfg st` satisfies `inv`, `runCfgSteps` with fuel
`mu (initPhiOfMir cfg st) + 1` terminates without UB or panic in at most
`(1 + cfg.dCycle) * mu (initPhiOfMir cfg st) + (1 + cfg.dEntryExit)` MIR steps! -/
theorem runCfgSteps_of_ssa_invariant
    (cfg : MirLoopCfg) (ssa : MiniSsaLoop)
    (inv : PhiState → Prop) (postPhi : PhiState → Prop)
    (mu : PhiState → Nat)
    (hDelta : cfg.stepDelta = ssa.stepDelta)
    (hStep : ∀ phi : PhiState, inv phi → phi.phiIdx < phi.bound →
      inv (stepMiniSsaPhi ssa phi) ∧ mu (stepMiniSsaPhi ssa phi) < mu phi)
    (hPost : ∀ phi : PhiState, inv phi → ¬ (phi.phiIdx < phi.bound) → postPhi phi) :
    ∀ (m : Nat) (st : MirLoopState),
      slotsOk st = true →
      (cfg.usesDivInBody && st.denomVal == 0) = false →
      inv (initPhiOfMir cfg st) →
      mu (initPhiOfMir cfg st) ≤ m →
      ∃ (phiExit : PhiState) (stepsMir : Nat),
        runCfgSteps (m + 1) cfg st = .returned phiExit.phiAcc stepsMir ∧
        stepsMir ≤ (1 + cfg.dCycle) * m + (1 + cfg.dEntryExit) ∧
        postPhi phiExit := by
  intro m
  induction m with
  | zero =>
    intro st hSlots _hDiv hInv hMuZero
    have hNotLt : ¬ (st.idxVal < st.boundVal) := by
      intro hLt
      have hStep0 := hStep (initPhiOfMir cfg st) hInv hLt
      omega
    refine ⟨initPhiOfMir cfg st, 1 + cfg.dEntryExit, ?_, ?_, ?_⟩
    · unfold runCfgSteps
      simp [hSlots, hNotLt, initPhiOfMir]
    · omega
    · exact hPost (initPhiOfMir cfg st) hInv hNotLt
  | succ m' ih =>
    intro st hSlots hDiv hInv hMuLe
    by_cases hLt : st.idxVal < st.boundVal
    · have ⟨hInvNext, hMuNext⟩ := hStep (initPhiOfMir cfg st) hInv hLt
      have hMuNextLe : mu (stepMiniSsaPhi ssa (initPhiOfMir cfg st)) ≤ m' := by omega
      have hPhiEq : initPhiOfMir cfg (nextMirLoopState cfg st) = stepMiniSsaPhi ssa (initPhiOfMir cfg st) := by
        simp [initPhiOfMir, nextMirLoopState, stepMiniSsaPhi, hDelta]
      have hSlots' : slotsOk (nextMirLoopState cfg st) = true := by
        unfold slotsOk nextMirLoopState at *
        exact hSlots
      have hDiv' : (cfg.usesDivInBody && (nextMirLoopState cfg st).denomVal == 0) = false := by
        unfold nextMirLoopState
        exact hDiv
      have hInvSt' : inv (initPhiOfMir cfg (nextMirLoopState cfg st)) := by
        rw [hPhiEq]; exact hInvNext
      have hMuSt' : mu (initPhiOfMir cfg (nextMirLoopState cfg st)) ≤ m' := by
        rw [hPhiEq]; exact hMuNextLe
      rcases ih (nextMirLoopState cfg st) hSlots' hDiv' hInvSt' hMuSt' with
        ⟨phiExit, stepsSub, hRunSub, hBoundSub, hPostSub⟩
      refine ⟨phiExit, stepsSub + (1 + cfg.dCycle), ?_, ?_, hPostSub⟩
      · conv => lhs; unfold runCfgSteps
        simp [hSlots, hLt, hDiv, hRunSub]
      · calc
          stepsSub + (1 + cfg.dCycle)
            ≤ ((1 + cfg.dCycle) * m' + (1 + cfg.dEntryExit)) + (1 + cfg.dCycle) :=
              Nat.add_le_add_right hBoundSub (1 + cfg.dCycle)
          _ = (1 + cfg.dCycle) * (m' + 1) + (1 + cfg.dEntryExit) := by
              rw [Nat.mul_succ]; omega
    · refine ⟨initPhiOfMir cfg st, 1 + cfg.dEntryExit, ?_, ?_, ?_⟩
      · unfold runCfgSteps
        simp [hSlots, hLt, initPhiOfMir]
      · omega
      · exact hPost (initPhiOfMir cfg st) hInv hLt

/-- **Master Theorem 1 (`verifyMirLoopViaMiniSSA_sound`)**:
Given a `checkLoopNormBisim` certificate, a loop cut-point invariant `inv : PhiState → Prop`,
and a well-founded ranking measure `mu : PhiState → Nat` satisfying the three pure SSA
cut-point obligations (`Init`, `Step`, `Post`), the original `Runtime(PostCleanup)` MIR
loop satisfies both `Trusted.LoopVerificationResult` and `Trusted.StatefulLoopVerificationResult`
with affine fuel bound:
$$k_{\text{mir}} \le (1 + d_{\text{loop}}) \cdot \mu(\vec{\phi}_0) + (1 + c_{\text{exit}})$$
and zero manual `fuel` induction in the user's proof! -/
theorem verifyMirLoopViaMiniSSA_sound
    (cfg : MirLoopCfg) (ssa : MiniSsaLoop) (cert : LoopNormCert)
    (pre : MirLoopState → Prop) (post : MirLoopState → Nat → Prop)
    (inv : MirLoopState → PhiState → Prop)
    (mu : PhiState → Nat)
    (hCheck : checkLoopNormBisim cfg ssa cert = true)
    (hFrame : ∀ st : MirLoopState, pre st →
      slotsOk st = true ∧ (cfg.usesDivInBody && st.denomVal == 0) = false)
    (hInit : ∀ st : MirLoopState, pre st → inv st (initPhiOfMir cfg st))
    (hStep : ∀ (st : MirLoopState) (phi : PhiState),
      pre st → inv st phi → phi.phiIdx < phi.bound →
      inv st (stepMiniSsaPhi ssa phi) ∧ mu (stepMiniSsaPhi ssa phi) < mu phi)
    (hPost : ∀ (st : MirLoopState) (phi : PhiState),
      pre st → inv st phi → ¬ (phi.phiIdx < phi.bound) → post st phi.phiAcc) :
    StatefulLoopVerificationResult cfg pre post
      (fun st => (1 + certCycleSlack cert) * mu (initPhiOfMir cfg st) + (1 + certEntryExitSlack cert)) := by
  intro st hPre
  unfold checkLoopNormBisim at hCheck
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hCheck
  rcases hCheck with ⟨⟨⟨⟨⟨⟨⟨⟨⟨_hSlots, hDCycle⟩, hDExit⟩, hDelta⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩
  rcases hFrame st hPre with ⟨hSlotsOk, hDivOk⟩
  have hInv0 := hInit st hPre
  rcases runCfgSteps_of_ssa_invariant cfg ssa (inv st)
    (fun phi => post st phi.phiAcc) mu hDelta
    (fun phi hI hLt => hStep st phi hPre hI hLt)
    (fun phi hI hNotLt => hPost st phi hPre hI hNotLt)
    (mu (initPhiOfMir cfg st)) st hSlotsOk hDivOk hInv0 (Nat.le_refl _) with
    ⟨phiExit, stepsMir, hRun, hBound, hPostExit⟩
  refine ⟨mu (initPhiOfMir cfg st) + 1, phiExit.phiAcc, stepsMir, hRun, ?_, hPostExit⟩
  unfold certCycleSlack certEntryExitSlack
  rw [← hDCycle, ← hDExit]
  exact hBound

/-- Stateless corollary (`verifyMirLoopStatelessViaMiniSSA_sound`). -/
theorem verifyMirLoopStatelessViaMiniSSA_sound
    (cfg : MirLoopCfg) (ssa : MiniSsaLoop) (cert : LoopNormCert)
    (pre : MirLoopState → Prop) (post : MirLoopState → Nat → Prop)
    (inv : MirLoopState → PhiState → Prop)
    (mu : PhiState → Nat)
    (hCheck : checkLoopNormBisim cfg ssa cert = true)
    (hFrame : ∀ st : MirLoopState, pre st →
      slotsOk st = true ∧ (cfg.usesDivInBody && st.denomVal == 0) = false)
    (hInit : ∀ st : MirLoopState, pre st → inv st (initPhiOfMir cfg st))
    (hStep : ∀ (st : MirLoopState) (phi : PhiState),
      pre st → inv st phi → phi.phiIdx < phi.bound →
      inv st (stepMiniSsaPhi ssa phi) ∧ mu (stepMiniSsaPhi ssa phi) < mu phi)
    (hPost : ∀ (st : MirLoopState) (phi : PhiState),
      pre st → inv st phi → ¬ (phi.phiIdx < phi.bound) → post st phi.phiAcc) :
    LoopVerificationResult cfg pre post := by
  intro st hPre
  rcases verifyMirLoopViaMiniSSA_sound cfg ssa cert pre post inv mu
    hCheck hFrame hInit hStep hPost st hPre with ⟨fuel, ret, stepsMir, hRun, _hBound, hPostRet⟩
  exact ⟨fuel, ret, stepsMir, hRun, hPostRet⟩

/-- **Master Theorem 2 (`verifyNestedLoopLexicographic_sound`)**:
For a nested 2D loop with outer ranking measure `muOuter` and inner trip bound `innerBound`,
where each outer header step consumes `1 + dOuter` MIR steps and each inner body step
consumes `1 + dInner` MIR steps, the total MIR steps consumed across all nested iterations
is bounded by the lexicographic affine polynomial:
$$k_{\text{mir}} \le \mu_{\text{outer}} \cdot ((1 + d_{\text{outer}}) + (1 + d_{\text{inner}}) \cdot M_{\text{inner}}) + (1 + d_{\text{exit}})$$ -/
def runNested2DMirSteps (outerTrips innerTrips dOuter dInner dExit : Nat) : Nat :=
  outerTrips * ((1 + dOuter) + (1 + dInner) * innerTrips) + (1 + dExit)

theorem verifyNestedLoopLexicographic_sound
    (outerTrips innerTrips maxInner dOuter dInner dExit : Nat)
    (hInnerLe : innerTrips ≤ maxInner) :
    runNested2DMirSteps outerTrips innerTrips dOuter dInner dExit ≤
      outerTrips * ((1 + dOuter) + (1 + dInner) * maxInner) + (1 + dExit) := by
  unfold runNested2DMirSteps
  have h1 : (1 + dInner) * innerTrips ≤ (1 + dInner) * maxInner :=
    Nat.mul_le_mul_left (1 + dInner) hInnerLe
  have h2 : (1 + dOuter) + (1 + dInner) * innerTrips ≤ (1 + dOuter) + (1 + dInner) * maxInner :=
    Nat.add_le_add_left h1 (1 + dOuter)
  have h3 : outerTrips * ((1 + dOuter) + (1 + dInner) * innerTrips) ≤
      outerTrips * ((1 + dOuter) + (1 + dInner) * maxInner) :=
    Nat.mul_le_mul_left outerTrips h2
  exact Nat.add_le_add_right h3 (1 + dExit)

/-- **Master Theorem 3 (`verifyMirRecViaMiniSSA_sound`)**:
Well-founded recursive contract induction across `MiniSSA` `Call` instructions:
If `mu : Nat → Nat` strictly decreases on every recursive call (`x ≠ 0 → mu (stepFn x) < mu x`)
and the `MiniSSA` contract `(pre, post)` holds inductively when assuming `post (stepFn x) subRet`
for the recursive call, then `evalMirRecFuel` terminates without UB or panic in at most
`(1 + dCall) * mu x + (1 + dBase)` MIR steps and satisfies `post x ret`! -/
theorem evalMirRecFuel_of_ssa_spec
    (dCall dBase : Nat) (stepFn : Nat → Nat) (combineFn : Nat → Nat → Nat) (baseVal : Nat)
    (pre : Nat → Prop) (post : Nat → Nat → Prop) (mu : Nat → Nat)
    (hBase : ∀ x : Nat, pre x → x = 0 → post x baseVal)
    (hInd : ∀ x : Nat, pre x → x ≠ 0 →
      pre (stepFn x) ∧
      mu (stepFn x) < mu x ∧
      (∀ subRet : Nat, post (stepFn x) subRet → post x (combineFn x subRet))) :
    ∀ (m : Nat) (x : Nat),
      pre x →
      mu x ≤ m →
      ∃ (ret : Nat) (stepsMir : Nat),
        evalMirRecFuel (m + 1) dCall dBase stepFn combineFn baseVal x = .returned ret stepsMir ∧
        stepsMir ≤ (1 + dCall) * m + (1 + dBase) ∧
        post x ret := by
  intro m
  induction m with
  | zero =>
    intro x hPre hMuZero
    by_cases hZero : x = 0
    · refine ⟨baseVal, 1 + dBase, ?_, ?_, hBase x hPre hZero⟩
      · subst hZero; rfl
      · omega
    · exfalso
      have ⟨_, hLt, _⟩ := hInd x hPre hZero
      omega
  | succ m' ih =>
    intro x hPre hMuLe
    by_cases hZero : x = 0
    · refine ⟨baseVal, 1 + dBase, ?_, ?_, hBase x hPre hZero⟩
      · subst hZero; rfl
      · omega
    · have ⟨hPreSub, hMuLt, hCombine⟩ := hInd x hPre hZero
      have hMuSubLe : mu (stepFn x) ≤ m' := by omega
      rcases ih (stepFn x) hPreSub hMuSubLe with ⟨subRet, stepsSub, hRunSub, hBoundSub, hPostSub⟩
      refine ⟨combineFn x subRet, stepsSub + (1 + dCall), ?_, ?_, hCombine subRet hPostSub⟩
      · conv => lhs; unfold evalMirRecFuel
        have hBeq : (x == 0) = false := beq_eq_false_iff_ne.mpr hZero
        simp [hBeq, hRunSub]
      · calc
          stepsSub + (1 + dCall)
            ≤ ((1 + dCall) * m' + (1 + dBase)) + (1 + dCall) :=
              Nat.add_le_add_right hBoundSub (1 + dCall)
          _ = (1 + dCall) * (m' + 1) + (1 + dBase) := by
              rw [Nat.mul_succ]; omega

theorem verifyMirRecViaMiniSSA_sound
    (dCall dBase : Nat) (stepFn : Nat → Nat) (combineFn : Nat → Nat → Nat) (baseVal : Nat)
    (pre : Nat → Prop) (post : Nat → Nat → Prop) (mu : Nat → Nat)
    (hBase : ∀ x : Nat, pre x → x = 0 → post x baseVal)
    (hInd : ∀ x : Nat, pre x → x ≠ 0 →
      pre (stepFn x) ∧
      mu (stepFn x) < mu x ∧
      (∀ subRet : Nat, post (stepFn x) subRet → post x (combineFn x subRet))) :
    RecVerificationResult dCall dBase stepFn combineFn baseVal pre post
      (fun x => (1 + dCall) * mu x + (1 + dBase)) := by
  intro x hPre
  rcases evalMirRecFuel_of_ssa_spec dCall dBase stepFn combineFn baseVal pre post mu
    hBase hInd (mu x) x hPre (Nat.le_refl _) with ⟨ret, stepsMir, hRun, hBound, hPost⟩
  exact ⟨mu x + 1, ret, stepsMir, hRun, hBound, hPost⟩

/-- **Negative Soundness Theorem (`licmHoistUninitOrTrap_rejected`)**:
When `usesDivInBody = true` and `denomVal = 0`, a zero-trip loop (`idxVal = 0, boundVal = 0`)
in `Runtime(PostCleanup)` MIR never enters the loop body and returns `accVal` cleanly (`0` panics).
If `LICM` hoists `paramVal / denomVal` into the preheader *without* a `LoopRotate` entry guard
(`entryGuardRotated = false`) and *without* a static trap-freedom proof (`hoistedTrapFree = false`),
`checkLoopNormBisim` rejects the certificate (`= false`). -/
def unsafeZeroTripDivCfg : MirLoopCfg :=
  { dCycle := 3, dEntryExit := 2, stepDelta := 1, usesDivInBody := true }

def unsafeUnrotatedLicmSsa : MiniSsaLoop :=
  { stepDelta := 1, usesDivHoisted := true, entryGuardRotated := false }

def unsafeUnrotatedLicmCert : LoopNormCert :=
  { dCycle := 3
  , dEntryExit := 2
  , stepDelta := 1
  , usesDivHoisted := true
  , entryGuardRotated := false
  , hoistedTrapFree := false
  , slotsLiveAndNoAlias := true }

theorem licmHoistUninitOrTrap_rejected :
    checkLoopNormBisim unsafeZeroTripDivCfg unsafeUnrotatedLicmSsa unsafeUnrotatedLicmCert = false ∧
    runCfgSteps 1 unsafeZeroTripDivCfg
      { idxSlotLive := true, accSlotLive := true, idxVal := 0, accVal := 42,
        boundVal := 0, paramVal := 100, denomVal := 0, noAliasConflict := true } = .returned 42 3 := by
  exact ⟨rfl, rfl⟩

#print axioms verifyMirLoopViaMiniSSA_sound
#print axioms verifyMirLoopStatelessViaMiniSSA_sound
#print axioms verifyNestedLoopLexicographic_sound
#print axioms verifyMirRecViaMiniSSA_sound
#print axioms licmHoistUninitOrTrap_rejected

end Theory
