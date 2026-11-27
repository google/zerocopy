-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirWp.Core
public import Anneal.MirWp.V2Memory
public import Anneal.StepBound.Core

public section

/-!
# Composable Loop & Step-Bound Combinators (`Anneal.StepBound.V2Loop`)

Pass-1-portable (`0` Trusted LOC, zero `omega`, zero `._unsafe_rec`) loop and
composition combinators over `ReachesDoneWithin` and `ReachesDoneWithinV2`:

- **Sequential composition (`v2_sequential_compose`, `v2_sequential_done`):**
  Direct `b₁ + b₂` additive composition over `BoundedReachV2`,
  `ReachesDoneWithinV2`, and `execStateV2`.
- **Constant-body bounded loop (`v2_loop_const_bound`, `v2_loop_const_or_exit`,
  `v2_loop_const_exec`):** `n` iterations each taking `≤ bodyBound` steps plus
  exit cost `exitBound` yield `n * bodyBound + exitBound` total MIR steps.
- **Rank-based loop with early exit (`v2_loop_rank_const_bound`):** Decreases a
  `rank : State → Nat` measure on every back-edge, supporting early loop breaks
  without weakening the `(rank s) * bodyBound + exitBound` ceiling.
- **Byte-credit / progress-weighted loop (`v2_loop_byte_credit`,
  `v2_loop_byte_credit_strict`):** Iterations consuming `(m - m') ≥ 1` credit
  in `k ≤ K * (m - m')` steps compose to total step bound `K * m + C`.
- **Function-entry wrappers (`execWithinStepsV2_of_setup_loop`,
  `execWithinStepsV2_of_setup_byte_credit`, `execWithinStepsV2_of_bodyCtx`):**
  Combine `initStateV2` / `BodyCtx` admission, setup prefix `S0`, loop bound,
  and `v2_adequacy_bounded` / `v2_adequacy_bounded_post`.
- **Profile v1 symmetry (`v1_loop_const_bound`, `v1_loop_byte_credit`):**
  Matching `0`-axiom loop bounds over `ReachesDoneWithin` / `BoundedReachV1`.
-/

namespace Anneal.StepBound

open Trusted.MirAst Trusted.MirSemantics
open Anneal.MirWp

/-! ## 1. Sequential Composition Combinators (`b₁ + b₂`) -/

/-- Two-stage sequential composition (`b₁ + b₂`) for `BoundedReachV2`. -/
theorem v2_sequential_compose {p : Program} {P Q R : State → Prop}
    {b₁ b₂ : Nat} {s₀ : State}
    (hStage₁ : BoundedReachV2 p P b₁ s₀)
    (hStage₂ : ∀ s₁, P s₁ → BoundedReachV2 p Q b₂ s₁)
    (hPost : ∀ s₂, Q s₂ → R s₂) :
    BoundedReachV2 p R (b₁ + b₂) s₀ :=
  BoundedReachV2.weaken hPost (BoundedReachV2.trans hStage₁ hStage₂)

/-- Bind a `BoundedReachV2` stage (`≤ b₁`) with a terminating
`ReachesDoneWithinV2` continuation (`≤ b₂`) into total bound `b₁ + b₂`. -/
theorem v2_sequential_done {p : Program} {P : State → Prop}
    {post : TerminalOut → Prop} {b₁ b₂ : Nat} {s₀ : State}
    (hStage : BoundedReachV2 p P b₁ s₀)
    (hDone : ∀ s₁, P s₁ → ReachesDoneWithinV2 p post b₂ s₁) :
    ReachesDoneWithinV2 p post (b₁ + b₂) s₀ :=
  BoundedReachV2.bind_done hStage hDone

/-- Bind a `BoundedReachV2` stage (`≤ b₁`) with a terminating `execStateV2`
continuation (`≤ b₂`) into total bound `b₁ + b₂`. -/
theorem v2_sequential_exec {p : Program} {P : State → Prop}
    {post : TerminalOut → Prop} {b₁ b₂ : Nat} {s₀ : State}
    (hStage : BoundedReachV2 p P b₁ s₀)
    (hDone : ∀ s₁, P s₁ → execStateV2 p b₂ s₁ post) :
    execStateV2 p (b₁ + b₂) s₀ post :=
  BoundedReachV2.bind_exec hStage hDone

/-! ## 2. Constant-Per-Iteration Bounded Loop Combinators -/

/-- Countdown loop with constant per-iteration step bound `bodyBound` and
exit bound `exitBound`, yielding `n * bodyBound + exitBound` total steps. -/
theorem v2_loop_const_bound {p : Program} {post : TerminalOut → Prop}
    (Inv : Nat → State → Prop) (bodyBound exitBound : Nat)
    (hExit : ∀ s, Inv 0 s → ReachesDoneWithinV2 p post exitBound s)
    (hStep : ∀ n s, Inv (n + 1) s → BoundedReachV2 p (Inv n) bodyBound s) :
    ∀ (n : Nat) (s : State),
      Inv n s → ReachesDoneWithinV2 p post (n * bodyBound + exitBound) s
  | 0, s, hInv => by
    rw [Nat.zero_mul, Nat.zero_add]
    exact hExit s hInv
  | n + 1, s, hInv => by
    have hNext : BoundedReachV2 p (Inv n) bodyBound s := hStep n s hInv
    have hJoin :
        ReachesDoneWithinV2 p post (bodyBound + (n * bodyBound + exitBound)) s :=
      BoundedReachV2.bind_done hNext
        (fun s' hs' => v2_loop_const_bound Inv bodyBound exitBound hExit hStep n s' hs')
    have hArith :
        bodyBound + (n * bodyBound + exitBound) =
          (n + 1) * bodyBound + exitBound := by
      rw [Nat.succ_mul, Nat.add_comm (n * bodyBound) bodyBound, Nat.add_assoc]
    rw [hArith] at hJoin
    exact hJoin

/-- Countdown loop allowing early exit at positive counts (`n + 1`), yielding
total bound `n * bodyBound + exitBound`. -/
theorem v2_loop_const_or_exit {p : Program} {post : TerminalOut → Prop}
    (Inv : Nat → State → Prop) (bodyBound exitBound : Nat)
    (hExit : ∀ s, Inv 0 s → ReachesDoneWithinV2 p post exitBound s)
    (hStep : ∀ n s, Inv (n + 1) s →
      ReachesDoneWithinV2 p post exitBound s ∨
      BoundedReachV2 p (Inv n) bodyBound s) :
    ∀ (n : Nat) (s : State),
      Inv n s → ReachesDoneWithinV2 p post (n * bodyBound + exitBound) s
  | 0, s, hInv => by
    rw [Nat.zero_mul, Nat.zero_add]
    exact hExit s hInv
  | n + 1, s, hInv => by
    cases hStep n s hInv with
    | inl hEarly =>
      exact ReachesDoneWithinV2.mono
        (Nat.le_add_left exitBound ((n + 1) * bodyBound)) hEarly
    | inr hNext =>
      have hJoin :
          ReachesDoneWithinV2 p post (bodyBound + (n * bodyBound + exitBound)) s :=
        BoundedReachV2.bind_done hNext
          (fun s' hs' =>
            v2_loop_const_or_exit Inv bodyBound exitBound hExit hStep n s' hs')
      have hArith :
          bodyBound + (n * bodyBound + exitBound) =
            (n + 1) * bodyBound + exitBound := by
        rw [Nat.succ_mul, Nat.add_comm (n * bodyBound) bodyBound, Nat.add_assoc]
      rw [hArith] at hJoin
      exact hJoin

/-- `execStateV2` specialization of `v2_loop_const_or_exit`. -/
theorem v2_loop_const_exec {p : Program} {post : TerminalOut → Prop}
    (Inv : Nat → State → Prop) (bodyBound exitBound : Nat)
    (hExit : ∀ s, Inv 0 s → execStateV2 p exitBound s post)
    (hStep : ∀ n s, Inv (n + 1) s →
      execStateV2 p exitBound s post ∨
      BoundedReachV2 p (Inv n) bodyBound s) :
    ∀ (n : Nat) (s : State),
      Inv n s → execStateV2 p (n * bodyBound + exitBound) s post := by
  intro n s hInv
  refine reachesDoneWithinV2_iff_execStateV2.mp ?_
  refine v2_loop_const_or_exit Inv bodyBound exitBound ?_ ?_ n s hInv
  · intro st h0
    exact reachesDoneWithinV2_iff_execStateV2.mpr (hExit st h0)
  · intro k st hk
    cases hStep k st hk with
    | inl hEarly => exact Or.inl (reachesDoneWithinV2_iff_execStateV2.mpr hEarly)
    | inr hNext => exact Or.inr hNext

private theorem v2_loop_rank_cap_aux {p : Program} {post : TerminalOut → Prop}
    (Inv : State → Prop) (rank : State → Nat) (bodyBound exitBound : Nat)
    (hStep : ∀ s, Inv s →
      ReachesDoneWithinV2 p post exitBound s ∨
      BoundedReachV2 p (fun s' => Inv s' ∧ rank s' < rank s) bodyBound s) :
    ∀ (cap : Nat) (s : State),
      Inv s → rank s ≤ cap →
      ReachesDoneWithinV2 p post (cap * bodyBound + exitBound) s
  | 0, s, hInv, hRank => by
    cases hStep s hInv with
    | inl hEarly =>
      rw [Nat.zero_mul, Nat.zero_add]
      exact hEarly
    | inr hNext =>
      let ⟨_, _, _, _, hInv', hLt⟩ := hNext
      exact False.elim (Nat.not_lt_zero _ (Nat.lt_of_lt_of_le hLt hRank))
  | cap + 1, s, hInv, hRank => by
    cases hStep s hInv with
    | inl hEarly =>
      exact ReachesDoneWithinV2.mono
        (Nat.le_add_left exitBound ((cap + 1) * bodyBound)) hEarly
    | inr hNext =>
      have hJoin :
          ReachesDoneWithinV2 p post
            (bodyBound + (cap * bodyBound + exitBound)) s := by
        refine BoundedReachV2.bind_done hNext (fun s' hAnd => ?_)
        have hLe : rank s' ≤ cap :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hAnd.2 hRank)
        exact v2_loop_rank_cap_aux Inv rank bodyBound exitBound hStep
          cap s' hAnd.1 hLe
      have hArith :
          bodyBound + (cap * bodyBound + exitBound) =
            (cap + 1) * bodyBound + exitBound := by
        rw [Nat.succ_mul, Nat.add_comm (cap * bodyBound) bodyBound, Nat.add_assoc]
      rw [hArith] at hJoin
      exact hJoin

/-- Rank-decreasing loop with arbitrary early exit: if every `Inv s` state
either finishes in `≤ exitBound` steps or reaches `Inv s'` with
`rank s' < rank s` in `≤ bodyBound` steps, then
`ReachesDoneWithinV2 p post (rank s * bodyBound + exitBound) s`. -/
theorem v2_loop_rank_const_bound {p : Program} {post : TerminalOut → Prop}
    (Inv : State → Prop) (rank : State → Nat) (bodyBound exitBound : Nat)
    (hStep : ∀ s, Inv s →
      ReachesDoneWithinV2 p post exitBound s ∨
      BoundedReachV2 p (fun s' => Inv s' ∧ rank s' < rank s) bodyBound s) :
    ∀ s : State, Inv s →
      ReachesDoneWithinV2 p post (rank s * bodyBound + exitBound) s := by
  intro s hInv
  exact v2_loop_rank_cap_aux Inv rank bodyBound exitBound hStep (rank s) s hInv
    (Nat.le_refl (rank s))

/-! ## 3. Credit-Weighted Linear Loop Combinators (`K * m + C`) -/

private theorem byte_credit_step_le (k m m' K C : Nat)
    (hm : m' < m) (hk : k ≤ K * (m - m')) :
    k + (K * m' + C) ≤ K * m + C := by
  have h1 : k + (K * m' + C) ≤ K * (m - m') + (K * m' + C) :=
    Nat.add_le_add_right hk (K * m' + C)
  have h2 : K * (m - m') + (K * m' + C) = (K * (m - m') + K * m') + C := by
    rw [Nat.add_assoc]
  have h3 : K * (m - m') + K * m' = K * ((m - m') + m') := by
    rw [← Nat.mul_add]
  have h4 : (m - m') + m' = m := Nat.sub_add_cancel (Nat.le_of_lt hm)
  rw [h2, h3, h4] at h1
  exact h1

private theorem v2_loop_byte_credit_cap_aux {p : Program}
    {post : TerminalOut → Prop}
    (Inv : Nat → State → Prop) (K C : Nat)
    (hExit : ∀ s, Inv 0 s → ReachesDoneWithinV2 p post C s)
    (hStep : ∀ m s, 0 < m → Inv m s →
      ReachesDoneWithinV2 p post C s ∨
      ∃ m' k s', m' < m ∧ k ≤ K * (m - m') ∧ StepsToV2 p k s s' ∧ Inv m' s') :
    ∀ (cap m : Nat) (s : State),
      m ≤ cap → Inv m s → ReachesDoneWithinV2 p post (K * m + C) s
  | 0, m, s, hLe, hInv => by
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hLe
    rw [hm0, Nat.mul_zero, Nat.zero_add]
    rw [hm0] at hInv
    exact hExit s hInv
  | cap + 1, m, s, hLe, hInv => by
    cases m with
    | zero =>
      rw [Nat.mul_zero, Nat.zero_add]
      exact hExit s hInv
    | succ mPrev =>
      cases hStep (mPrev + 1) s (Nat.succ_pos mPrev) hInv with
      | inl hEarly =>
        exact ReachesDoneWithinV2.mono
          (Nat.le_add_left C (K * (mPrev + 1))) hEarly
      | inr hNext =>
        let ⟨m', k, s', hLt, hk, hSteps, hInv'⟩ := hNext
        have hCap : m' ≤ cap :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hLt hLe)
        have hSub : ReachesDoneWithinV2 p post (K * m' + C) s' :=
          v2_loop_byte_credit_cap_aux Inv K C hExit hStep cap m' s' hCap hInv'
        have hSum : ReachesDoneWithinV2 p post (k + (K * m' + C)) s :=
          reachesDoneWithinV2_of_stepsTo hSteps hSub
        exact ReachesDoneWithinV2.mono
          (byte_credit_step_le k (mPrev + 1) m' K C hLt hk) hSum

/-- Progress-weighted (`ByteCredit`) linear loop combinator over
`ReachesDoneWithinV2`: if each iteration from `m > 0` either finishes in `≤ C`
steps or advances to `m' < m` in `k ≤ K * (m - m')` steps, total execution from
`Inv m s` takes at most `K * m + C` steps. -/
theorem v2_loop_byte_credit {p : Program} {post : TerminalOut → Prop}
    (Inv : Nat → State → Prop) (K C : Nat)
    (hExit : ∀ s, Inv 0 s → ReachesDoneWithinV2 p post C s)
    (hStep : ∀ m s, 0 < m → Inv m s →
      ReachesDoneWithinV2 p post C s ∨
      ∃ m' k s', m' < m ∧ k ≤ K * (m - m') ∧ StepsToV2 p k s s' ∧ Inv m' s') :
    ∀ (m : Nat) (s : State),
      Inv m s → ReachesDoneWithinV2 p post (K * m + C) s := by
  intro m s hInv
  exact v2_loop_byte_credit_cap_aux Inv K C hExit hStep m m s
    (Nat.le_refl m) hInv

/-- `execStateV2` interface for `v2_loop_byte_credit` (matches the promoted
`V2Steps.v2_loop_byte_credit` contract cleanly without `omega`). -/
theorem v2_loop_byte_credit_exec {p : Program} {post : TerminalOut → Prop}
    (Inv : Nat → State → Prop) (K C : Nat)
    (hExit : ∀ s, Inv 0 s → execStateV2 p C s post)
    (hStep : ∀ m s, 0 < m → Inv m s →
      execStateV2 p C s post ∨
      ∃ m' k s', m' < m ∧ k ≤ K * (m - m') ∧ StepsToV2 p k s s' ∧ Inv m' s') :
    ∀ (m : Nat) (s : State),
      Inv m s → execStateV2 p (K * m + C) s post := by
  intro m s hInv
  refine reachesDoneWithinV2_iff_execStateV2.mp ?_
  refine v2_loop_byte_credit Inv K C ?_ ?_ m s hInv
  · intro st h0
    exact reachesDoneWithinV2_iff_execStateV2.mpr (hExit st h0)
  · intro cur st hPos hCur
    cases hStep cur st hPos hCur with
    | inl hEarly => exact Or.inl (reachesDoneWithinV2_iff_execStateV2.mpr hEarly)
    | inr hNext => exact Or.inr hNext

/-- Strict no-early-exit variant of `v2_loop_byte_credit_exec`. -/
theorem v2_loop_byte_credit_strict {p : Program} {post : TerminalOut → Prop}
    (Inv : Nat → State → Prop) (K C : Nat)
    (hExit : ∀ s, Inv 0 s → execStateV2 p C s post)
    (hStep : ∀ m s, 0 < m → Inv m s →
      ∃ m' k s', m' < m ∧ k ≤ K * (m - m') ∧ StepsToV2 p k s s' ∧ Inv m' s') :
    ∀ (m : Nat) (s : State),
      Inv m s → execStateV2 p (K * m + C) s post :=
  v2_loop_byte_credit_exec Inv K C hExit
    (fun m s hm hInv => Or.inr (hStep m s hm hInv))

/-! ## 4. Function-Entry & `BodyCtx` End-to-End Bound Wrappers -/

/-- End-to-end Profile v2 setup + constant-step loop bound + adequacy wrapper:
combines `initStateV2 p q = .ok s₀`, setup prefix `setupBound`, loop count
`n * bodyBound + exitBound`, `ExecWithinStepsV2`, `WellFormedV2`,
`¬ DivergesV2`, and `SatisfiesPostV2`. -/
theorem execWithinStepsV2_of_setup_loop {p : Program} {q : Query} {s₀ : State}
    {post : TerminalOut → Prop} (Inv : Nat → State → Prop)
    (setupBound bodyBound exitBound n : Nat)
    (hInit : initStateV2 p q = .ok s₀)
    (hSetup : BoundedReachV2 p (Inv n) setupBound s₀)
    (hExit : ∀ s, Inv 0 s → ReachesDoneWithinV2 p post exitBound s)
    (hStep : ∀ k s, Inv (k + 1) s →
      ReachesDoneWithinV2 p post exitBound s ∨
      BoundedReachV2 p (Inv k) bodyBound s) :
    ExecWithinStepsV2 p q (setupBound + (n * bodyBound + exitBound)) post ∧
    WellFormedV2 p q ∧
    ¬ DivergesV2 p q ∧
    SatisfiesPostV2 p q post ∧
    (∃ out : TerminalOut, BehaviorV2 p q out ∧ post out) := by
  have hLoop := v2_loop_const_or_exit Inv bodyBound exitBound hExit hStep
  have hReach :
      ReachesDoneWithinV2 p post (setupBound + (n * bodyBound + exitBound)) s₀ :=
    BoundedReachV2.bind_done hSetup (fun s₁ hInv => hLoop n s₁ hInv)
  exact v2_adequacy_bounded_post hInit hReach

/-- End-to-end Profile v2 setup + `K * m + C` byte-credit loop + adequacy
wrapper. -/
theorem execWithinStepsV2_of_setup_byte_credit {p : Program} {q : Query}
    {s₀ : State} {post : TerminalOut → Prop} (Inv : Nat → State → Prop)
    (setupBound K C m : Nat)
    (hInit : initStateV2 p q = .ok s₀)
    (hSetup : BoundedReachV2 p (Inv m) setupBound s₀)
    (hExit : ∀ s, Inv 0 s → ReachesDoneWithinV2 p post C s)
    (hStep : ∀ cur s, 0 < cur → Inv cur s →
      ReachesDoneWithinV2 p post C s ∨
      ∃ cur' k s',
        cur' < cur ∧ k ≤ K * (cur - cur') ∧ StepsToV2 p k s s' ∧ Inv cur' s') :
    ExecWithinStepsV2 p q (setupBound + (K * m + C)) post ∧
    WellFormedV2 p q ∧
    ¬ DivergesV2 p q ∧
    SatisfiesPostV2 p q post ∧
    (∃ out : TerminalOut, BehaviorV2 p q out ∧ post out) := by
  have hLoop := v2_loop_byte_credit Inv K C hExit hStep
  have hReach :
      ReachesDoneWithinV2 p post (setupBound + (K * m + C)) s₀ :=
    BoundedReachV2.bind_done hSetup (fun s₁ hInv => hLoop m s₁ hInv)
  exact v2_adequacy_bounded_post hInit hReach

/-- `BodyCtx`-based end-to-end wrapper combining `BodyCtx.initStateV2_ok_of`
with `v2_adequacy_bounded_post`. -/
theorem execWithinStepsV2_of_bodyCtx (ctx : BodyCtx) (q : Query)
    (bound : Nat) (post : TerminalOut → Prop)
    (hBody : ctx.HasBody)
    (hAdm : BodyStaticAdmittedV2 ctx.program ctx.body = true)
    (hValid : ValidEntryArgsV2 ctx.body q)
    (hRun : ReachesDoneWithinV2 ctx.entryProg post bound
      ⟨[⟨ctx.defId, 0, 0, initLocalsLoop ctx.body q.args 0 ctx.body.locals,
        none, none, none⟩],
        q.callerMem,
        entryMemoryForArgsV2 q.callerMem
          ((ctx.body.locals.drop 1).take ctx.body.argumentCount) q.args⟩) :
    ExecWithinStepsV2 ctx.entryProg q bound post ∧
    WellFormedV2 ctx.entryProg q ∧
    ¬ DivergesV2 ctx.entryProg q ∧
    SatisfiesPostV2 ctx.entryProg q post ∧
    (∃ out : TerminalOut, BehaviorV2 ctx.entryProg q out ∧ post out) :=
  v2_adequacy_bounded_post (ctx.initStateV2_ok_of hBody hAdm hValid) hRun

/-! ## 5. Profile v1 Loop Combinators (Symmetric with Profile v2) -/

/-- Countdown loop with constant per-iteration step bound for Profile v1
`ReachesDoneWithin`. -/
theorem v1_loop_const_bound {p : Program} {post : TerminalOut → Prop}
    (Inv : Nat → State → Prop) (bodyBound exitBound : Nat)
    (hExit : ∀ s, Inv 0 s → ReachesDoneWithin p post exitBound s)
    (hStep : ∀ n s, Inv (n + 1) s →
      ReachesDoneWithin p post exitBound s ∨
      BoundedReachV1 p (Inv n) bodyBound s) :
    ∀ (n : Nat) (s : State),
      Inv n s → ReachesDoneWithin p post (n * bodyBound + exitBound) s
  | 0, s, hInv => by
    rw [Nat.zero_mul, Nat.zero_add]
    exact hExit s hInv
  | n + 1, s, hInv => by
    cases hStep n s hInv with
    | inl hEarly =>
      exact ReachesDoneWithin.mono
        (Nat.le_add_left exitBound ((n + 1) * bodyBound)) hEarly
    | inr hNext =>
      have hJoin :
          ReachesDoneWithin p post (bodyBound + (n * bodyBound + exitBound)) s :=
        BoundedReachV1.bind_done hNext
          (fun s' hs' =>
            v1_loop_const_bound Inv bodyBound exitBound hExit hStep n s' hs')
      have hArith :
          bodyBound + (n * bodyBound + exitBound) =
            (n + 1) * bodyBound + exitBound := by
        rw [Nat.succ_mul, Nat.add_comm (n * bodyBound) bodyBound, Nat.add_assoc]
      rw [hArith] at hJoin
      exact hJoin

private theorem v1_loop_byte_credit_cap_aux {p : Program}
    {post : TerminalOut → Prop}
    (Inv : Nat → State → Prop) (K C : Nat)
    (hExit : ∀ s, Inv 0 s → ReachesDoneWithin p post C s)
    (hStep : ∀ m s, 0 < m → Inv m s →
      ReachesDoneWithin p post C s ∨
      ∃ m' k s', m' < m ∧ k ≤ K * (m - m') ∧ StepsToV1 p k s s' ∧ Inv m' s') :
    ∀ (cap m : Nat) (s : State),
      m ≤ cap → Inv m s → ReachesDoneWithin p post (K * m + C) s
  | 0, m, s, hLe, hInv => by
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hLe
    rw [hm0, Nat.mul_zero, Nat.zero_add]
    rw [hm0] at hInv
    exact hExit s hInv
  | cap + 1, m, s, hLe, hInv => by
    cases m with
    | zero =>
      rw [Nat.mul_zero, Nat.zero_add]
      exact hExit s hInv
    | succ mPrev =>
      cases hStep (mPrev + 1) s (Nat.succ_pos mPrev) hInv with
      | inl hEarly =>
        exact ReachesDoneWithin.mono (Nat.le_add_left C (K * (mPrev + 1))) hEarly
      | inr hNext =>
        let ⟨m', k, s', hLt, hk, hSteps, hInv'⟩ := hNext
        have hCap : m' ≤ cap :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hLt hLe)
        have hSub : ReachesDoneWithin p post (K * m' + C) s' :=
          v1_loop_byte_credit_cap_aux Inv K C hExit hStep cap m' s' hCap hInv'
        have hSum : ReachesDoneWithin p post (k + (K * m' + C)) s :=
          reachesDoneWithin_of_stepsTo hSteps hSub
        exact ReachesDoneWithin.mono
          (byte_credit_step_le k (mPrev + 1) m' K C hLt hk) hSum

/-- Progress-weighted (`K * m + C`) linear loop combinator for Profile v1
`ReachesDoneWithin`. -/
theorem v1_loop_byte_credit {p : Program} {post : TerminalOut → Prop}
    (Inv : Nat → State → Prop) (K C : Nat)
    (hExit : ∀ s, Inv 0 s → ReachesDoneWithin p post C s)
    (hStep : ∀ m s, 0 < m → Inv m s →
      ReachesDoneWithin p post C s ∨
      ∃ m' k s', m' < m ∧ k ≤ K * (m - m') ∧ StepsToV1 p k s s' ∧ Inv m' s') :
    ∀ (m : Nat) (s : State),
      Inv m s → ReachesDoneWithin p post (K * m + C) s := by
  intro m s hInv
  exact v1_loop_byte_credit_cap_aux Inv K C hExit hStep m m s
    (Nat.le_refl m) hInv

end Anneal.StepBound

end
