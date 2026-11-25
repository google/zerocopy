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
public import Init.Data.Nat.Div.Basic
public import Trusted.MirAst
public import Trusted.MirSemantics

public section

/-!
# Linear `BiAlign` Stride-`M` Simulation & Narrow-Lane Arithmetic Guards

Compositional relational loop-alignment rules (`BiAlign`) for proving that a
vectorized or unrolled implementation (`stepVec`, processing `stride` scalar
items per iteration) refines or equals a scalar reference loop (`stepScalar`),
without constructing a quadratic path product:

1. **Pure Stride-`M` `BiAlign` & Scalar Tail Epilogue (`[]` zero axioms):**
   - `iterSteps step n s`: forward `n`-step iterator satisfying `iterSteps_add :
     iterSteps step (a + b) s = iterSteps step b (iterSteps step a s)`.
   - `BiAlignTileSpec stride rel stepScalar stepVec`: local 1-tile preservation
     contract `rel s t → rel (iterSteps stepScalar stride s) (stepVec t)`.
   - `biAlign_tiled_sound`: lifts one `BiAlignTileSpec` proof across `numTiles`
     vector tiles (`stride * numTiles` scalar steps vs. `numTiles` vector
     steps).
   - `biAlign_tiled_with_epilogue_sound`: composes `numTiles` vector tiles with
     `extractTail` and `rem` scalar tail steps (`stride * numTiles + rem` total
     scalar iterations).
   - `biAlign_lockstep_fails_on_stride4`: refutes naive `1`-to-`1` lockstep
     alignment on a 4-lane vector counter while `BiAlignTileSpec 4` holds.
2. **Deterministic MIR Step `BiAlign` (`[propext]` only):**
   - `MirStepsDet p n s s'`: `Prop`-valued `n`-step deterministic `evalStep p 0`
     relation (`0` `noncomputable` definitions), backed by `ExecMirStepsDet`
     (`mirStepsDet_of_execMirStepsDet`) and lifting into
     `Trusted.MirSemantics.Reaches` via `reaches_of_mirStepsDet`.
   - `MirBiAlignTileSpec pScalar stride pVec vecSteps rel`: unindexed
     1-tile bisimulation aligning `stride` deterministic MIR steps of `pScalar`
     with `vecSteps` steps of `pVec` (for `0 < stride` and `0 < vecSteps`,
     every related pair must take another full tile, so `rel` applies to
     reactive/non-terminating loops and is empty on terminal states); lifted
     across `numTiles` tiles by `mirBiAlign_tiled_sound`.
   - `MirBiAlignBoundedTileSpec pScalar stride pVec vecSteps rel`:
     remaining-tile-indexed 1-tile contract (`rel (k + 1) s t → ... ∧
     rel k s' t'`) whose base index `rel 0` imposes no further step obligation,
     handling terminating tiled MIR loops; lifted across `numTiles` tiles by
     `mirBiAlign_bounded_tiled_sound`.
3. **Narrow-Lane Wrapping vs. Wide-Accumulator Guard (`[propext]` only):**
   - `narrowAddMod m a b := Nat.mod (Nat.mod a m + Nat.mod b m) m`: models
     packed SIMD lane wrapping addition (`u16` or `u8` lane wrap) against wide
     unwrapped scalar addition `a + b`.
   - `narrowAddMod_eq_add_of_lt`: under domain precondition `a + b < m`, narrow
     lane addition agrees with wide addition (`narrowAddMod m a b = a + b`).
   - `narrowAddMod_ne_add_at_modulus`: when `a < m`, `b < m`, and `a + b = m`,
     `narrowAddMod m a b = 0 ≠ a + b`, isolating the silent SIMD wrap
     divergence caught by `SafeTwin` equivalence when domain preconditions are
     omitted.

All authored definitions are computable (`0` `noncomputable`, `0`
`._unsafe_rec`, `0` `omega`, `0` `decide`) and every authored declaration
compiles using at most `[propext]` (`0` `Classical.choice`, `0` `Quot.sound`).
-/

namespace Anneal.SafeTwin

open Trusted.MirAst Trusted.MirSemantics

/-! ## Part I: Pure Forward Iteration & Stride-`M` `BiAlign` Rules -/

/-- Forward `n`-step state transition iterator defined via `@Nat.rec` (`0`
`._unsafe_rec`) so `iterSteps step (n + 1) x = iterSteps step n (step x)` by
`rfl`. -/
@[expose] def iterSteps {α : Type} (step : α → α) (n : Nat) (x : α) : α :=
  @Nat.rec (fun _ => α → α) (fun y => y) (fun _ ih y => ih (step y)) n x

/-- Zero-step unfolding of `iterSteps`. -/
theorem iterSteps_zero {α : Type} (step : α → α) (x : α) :
    iterSteps step 0 x = x :=
  rfl

/-- Successor unfolding of `iterSteps`. -/
theorem iterSteps_succ {α : Type} (step : α → α) (n : Nat) (x : α) :
    iterSteps step (n + 1) x = iterSteps step n (step x) :=
  rfl

/-- Commuting one outer `step` past `n` iterations (`[]` zero axioms). -/
theorem iterSteps_step_comm {α : Type} (step : α → α) :
    ∀ (n : Nat) (x : α),
      step (iterSteps step n x) = iterSteps step n (step x)
  | 0, _ => rfl
  | n + 1, x => iterSteps_step_comm step n (step x)

/-- Additive composition of `iterSteps`: `a + b` steps equal `a` steps followed
by `b` steps (`[]` zero axioms). -/
theorem iterSteps_add {α : Type} (step : α → α) :
    ∀ (a b : Nat) (x : α),
      iterSteps step (a + b) x = iterSteps step b (iterSteps step a x)
  | 0, b, x => by
    rw [Nat.zero_add]
    rfl
  | a + 1, b, x => by
    rw [Nat.succ_add]
    exact iterSteps_add step a b (step x)

/-- Local 1-tile `BiAlign` simulation obligation: one vector/unrolled step
`stepVec t` preserves `rel` against `stride` scalar steps `iterSteps stepScalar
stride s`. -/
@[expose] def BiAlignTileSpec {S T : Type} (stride : Nat) (rel : S → T → Prop)
    (stepScalar : S → S) (stepVec : T → T) : Prop :=
  ∀ (s : S) (t : T), rel s t → rel (iterSteps stepScalar stride s) (stepVec t)

/-- Linear `BiAlign` tiled loop rule (`[]` zero axioms): a single finite-horizon
`BiAlignTileSpec` lifts to any number of tiles `numTiles` (`stride * numTiles`
scalar steps aligned with `numTiles` vector steps). -/
theorem biAlign_tiled_sound {S T : Type} {stride : Nat} {rel : S → T → Prop}
    {stepScalar : S → S} {stepVec : T → T}
    (hTile : BiAlignTileSpec stride rel stepScalar stepVec) :
    ∀ (numTiles : Nat) {s₀ : S} {t₀ : T},
      rel s₀ t₀ →
      rel (iterSteps stepScalar (stride * numTiles) s₀)
        (iterSteps stepVec numTiles t₀)
  | 0, _, _, h₀ => by
    rw [Nat.mul_zero]
    exact h₀
  | k + 1, s₀, t₀, h₀ => by
    rw [Nat.mul_succ, Nat.add_comm (stride * k) stride,
      iterSteps_add stepScalar stride (stride * k) s₀]
    exact biAlign_tiled_sound hTile k (hTile s₀ t₀ h₀)

/-- Full vector-body + scalar-tail `BiAlign` rule (`[]` zero axioms): aligns
`stride * numTiles + rem` scalar steps with `numTiles` vector tiles, an
accumulator extraction `extractTail : T → U`, and `rem` scalar tail steps. -/
theorem biAlign_tiled_with_epilogue_sound {S T U : Type} {stride : Nat}
    {relBody : S → T → Prop} {relTail : S → U → Prop}
    {stepScalar : S → S} {stepVec : T → T} {extractTail : T → U}
    {stepTail : U → U}
    (hBody : BiAlignTileSpec stride relBody stepScalar stepVec)
    (hDrain : ∀ (s : S) (t : T), relBody s t → relTail s (extractTail t))
    (hTail : BiAlignTileSpec 1 relTail stepScalar stepTail)
    (numTiles rem : Nat) {s₀ : S} {t₀ : T} (h₀ : relBody s₀ t₀) :
    relTail
      (iterSteps stepScalar (stride * numTiles + rem) s₀)
      (iterSteps stepTail rem
        (extractTail (iterSteps stepVec numTiles t₀))) := by
  rw [iterSteps_add stepScalar (stride * numTiles) rem s₀]
  have hAfterBody :
      relTail
        (iterSteps stepScalar (stride * numTiles) s₀)
        (extractTail (iterSteps stepVec numTiles t₀)) :=
    hDrain _ _ (biAlign_tiled_sound hBody numTiles h₀)
  have hAfterTail := biAlign_tiled_sound hTail rem hAfterBody
  rw [Nat.one_mul] at hAfterTail
  exact hAfterTail

/-- Strict `1`-to-`1` lockstep simulation fails on a stride-4 vector counter
(`s = t` fails after 1 step because `1 ≠ 4`), whereas `BiAlignTileSpec 4` holds
for all `numTiles` (`[]` zero axioms). -/
theorem biAlign_lockstep_fails_on_stride4 :
    let stepS := fun n : Nat => n + 1
    let stepV := fun n : Nat => n + 4
    let eqRel := fun (s t : Nat) => s = t
    ¬ BiAlignTileSpec 1 eqRel stepS stepV ∧
    BiAlignTileSpec 4 eqRel stepS stepV := by
  intro stepS stepV eqRel
  refine ⟨?_, ?_⟩
  · intro hLock1
    have hBad : (1 : Nat) = 4 := hLock1 0 0 rfl
    exact Nat.noConfusion (Nat.succ.inj hBad)
  · intro s t hEq
    dsimp only [eqRel, stepS, stepV, iterSteps]
    rw [hEq]
    rfl

/-! ## Part II: Deterministic `Trusted.MirSemantics` Step `BiAlign` -/

private theorem reaches_trans {p : Program} {s₁ s₂ : State}
    (h₁₂ : Reaches p s₁ s₂) :
    ∀ {s₃ : State}, Reaches p s₂ s₃ → Reaches p s₁ s₃
  | _, .refl _ => h₁₂
  | _, .tail h₂₃ hStep =>
    Reaches.tail (reaches_trans h₁₂ h₂₃) hStep

/-- Propositional `n`-step deterministic MIR intermediate-state relation
(`c = 0`) defined via `@Nat.rec` (`0` `._unsafe_rec`): `MirStepsDet p n s s'`
holds iff `s` steps via `n` consecutive `.step` transitions under
`evalStep p 0` to `s'`. -/
@[expose] def MirStepsDet (p : Program) (n : Nat) (s s' : State) : Prop :=
  @Nat.rec (fun _ => State → State → Prop)
    (fun a b => a = b)
    (fun _ ih a b => ∃ s₁ : State, evalStep p 0 a = .step s₁ ∧ ih s₁ b)
    n s s'

/-- Additive composition of `MirStepsDet` (`[propext]` only). -/
theorem mirStepsDet_add (p : Program) :
    ∀ (a b : Nat) {s₁ s₂ s₃ : State},
      MirStepsDet p a s₁ s₂ →
      MirStepsDet p b s₂ s₃ →
      MirStepsDet p (a + b) s₁ s₃
  | 0, b, _, _, _, h₁, h₂ => by
    rw [Nat.zero_add, h₁]
    exact h₂
  | a + 1, b, _, _, _, h₁, h₂ => by
    rw [Nat.succ_add]
    cases h₁ with
    | intro sm hm =>
      exact ⟨sm, hm.1, mirStepsDet_add p a b hm.2 h₂⟩

/-- Every `MirStepsDet p n s₁ s₂` witness implies `Trusted.MirSemantics.Reaches
p s₁ s₂` (`[propext]` only). -/
theorem reaches_of_mirStepsDet (p : Program) :
    ∀ (n : Nat) {s₁ s₂ : State},
      MirStepsDet p n s₁ s₂ → Reaches p s₁ s₂
  | 0, s₁, _, hEq => by
    rw [← hEq]
    exact Reaches.refl s₁
  | n + 1, s₁, _, h => by
    cases h with
    | intro sm hm =>
      have hHead : Reaches p s₁ sm :=
        Reaches.tail (Reaches.refl s₁) ⟨0, rfl, hm.1⟩
      exact reaches_trans hHead (reaches_of_mirStepsDet p n hm.2)

/-- `Prop`-valued `n`-step deterministic MIR step checker (`c = 0`, `0`
`noncomputable`, `0` `._unsafe_rec`): unfolds to `s_n = target` on concrete MIR
programs so finite-step tile witnesses discharge by `rfl`. -/
@[expose] def ExecMirStepsDet (p : Program) (n : Nat) (s target : State) :
    Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun st => st = target)
    (fun _ ih st =>
      match evalStep p 0 st with
      | .step st' => ih st'
      | _ => False)
    n s

/-- Soundness of `ExecMirStepsDet` into `MirStepsDet` (`[propext]` only). -/
theorem mirStepsDet_of_execMirStepsDet (p : Program) :
    ∀ (n : Nat) {s target : State},
      ExecMirStepsDet p n s target → MirStepsDet p n s target
  | 0, _, _, h => h
  | n + 1, s, _, h => by
    dsimp only [ExecMirStepsDet] at h
    cases hStep : evalStep p 0 s with
    | step sm =>
      rw [hStep] at h
      exact ⟨sm, hStep, mirStepsDet_of_execMirStepsDet p n h⟩
    | done _ =>
      rw [hStep] at h
      exact False.elim h
    | fault _ =>
      rw [hStep] at h
      exact False.elim h

/-- Unindexed MIR 1-tile `BiAlign` step contract: from any related states
`rel s t`, `pScalar` takes `scalarSteps` deterministic `.step` transitions to
some `s'` while `pVec` takes `vecSteps` deterministic `.step` transitions to
some `t'` preserving `rel s' t'`. For `0 < scalarSteps` and `0 < vecSteps`,
every related pair must take another full tile, so `rel` applies to
reactive/non-terminating loops and cannot hold on terminal states; use
`MirBiAlignBoundedTileSpec` for terminating tiled loops. -/
@[expose] def MirBiAlignTileSpec (pScalar : Program) (scalarSteps : Nat)
    (pVec : Program) (vecSteps : Nat) (rel : State → State → Prop) : Prop :=
  ∀ (s t : State),
    rel s t →
    ∃ (s' t' : State),
      MirStepsDet pScalar scalarSteps s s' ∧
      MirStepsDet pVec vecSteps t t' ∧
      rel s' t'

/-- Lifts unindexed `MirBiAlignTileSpec` across `numTiles` non-terminating loop
tiles (`scalarSteps * numTiles` scalar MIR steps vs. `vecSteps * numTiles`
candidate MIR steps; `[propext]` only). -/
theorem mirBiAlign_tiled_sound {pScalar : Program} {scalarSteps : Nat}
    {pVec : Program} {vecSteps : Nat} {rel : State → State → Prop}
    (hTile : MirBiAlignTileSpec pScalar scalarSteps pVec vecSteps rel) :
    ∀ (numTiles : Nat) {s₀ t₀ : State},
      rel s₀ t₀ →
      ∃ (sₖ tₖ : State),
        MirStepsDet pScalar (scalarSteps * numTiles) s₀ sₖ ∧
        MirStepsDet pVec (vecSteps * numTiles) t₀ tₖ ∧
        rel sₖ tₖ
  | 0, s₀, t₀, h₀ => by
    rw [Nat.mul_zero, Nat.mul_zero]
    exact ⟨s₀, t₀, rfl, rfl, h₀⟩
  | k + 1, s₀, t₀, h₀ => by
    cases hTile s₀ t₀ h₀ with
    | intro s₁ h₁ =>
      cases h₁ with
      | intro t₁ hStep₁ =>
        cases mirBiAlign_tiled_sound hTile k hStep₁.2.2 with
        | intro sₖ hₖ =>
          cases hₖ with
          | intro tₖ hStepₖ =>
            refine ⟨sₖ, tₖ, ?_, ?_, hStepₖ.2.2⟩
            · rw [Nat.mul_succ, Nat.add_comm (scalarSteps * k) scalarSteps]
              exact mirStepsDet_add pScalar scalarSteps (scalarSteps * k)
                hStep₁.1 hStepₖ.1
            · rw [Nat.mul_succ, Nat.add_comm (vecSteps * k) vecSteps]
              exact mirStepsDet_add pVec vecSteps (vecSteps * k)
                hStep₁.2.1 hStepₖ.2.1

/-- Remaining-tile-indexed MIR 1-tile `BiAlign` step contract for terminating
tiled loops: from any `rel (k + 1) s t`, `pScalar` takes `scalarSteps`
deterministic `.step` transitions to some `s'` while `pVec` takes `vecSteps`
deterministic `.step` transitions to some `t'` reaching `rel k s' t'`. Because
`rel 0` imposes no further step obligation, terminating loops fit directly. -/
@[expose] def MirBiAlignBoundedTileSpec (pScalar : Program) (scalarSteps : Nat)
    (pVec : Program) (vecSteps : Nat) (rel : Nat → State → State → Prop) :
    Prop :=
  ∀ (k : Nat) (s t : State),
    rel (k + 1) s t →
    ∃ (s' t' : State),
      MirStepsDet pScalar scalarSteps s s' ∧
      MirStepsDet pVec vecSteps t t' ∧
      rel k s' t'

/-- Lifts `MirBiAlignBoundedTileSpec` across `numTiles` terminating loop tiles
(`scalarSteps * numTiles` scalar MIR steps vs. `vecSteps * numTiles` candidate
MIR steps; `[propext]` only), landing in exit relation `rel 0 sₖ tₖ`. -/
theorem mirBiAlign_bounded_tiled_sound {pScalar : Program} {scalarSteps : Nat}
    {pVec : Program} {vecSteps : Nat} {rel : Nat → State → State → Prop}
    (hTile : MirBiAlignBoundedTileSpec pScalar scalarSteps pVec vecSteps rel) :
    ∀ (numTiles : Nat) {s₀ t₀ : State},
      rel numTiles s₀ t₀ →
      ∃ (sₖ tₖ : State),
        MirStepsDet pScalar (scalarSteps * numTiles) s₀ sₖ ∧
        MirStepsDet pVec (vecSteps * numTiles) t₀ tₖ ∧
        rel 0 sₖ tₖ
  | 0, s₀, t₀, h₀ => by
    rw [Nat.mul_zero, Nat.mul_zero]
    exact ⟨s₀, t₀, rfl, rfl, h₀⟩
  | k + 1, s₀, t₀, h₀ => by
    cases hTile k s₀ t₀ h₀ with
    | intro s₁ h₁ =>
      cases h₁ with
      | intro t₁ hStep₁ =>
        cases mirBiAlign_bounded_tiled_sound hTile k hStep₁.2.2 with
        | intro sₖ hₖ =>
          cases hₖ with
          | intro tₖ hStepₖ =>
            refine ⟨sₖ, tₖ, ?_, ?_, hStepₖ.2.2⟩
            · rw [Nat.mul_succ, Nat.add_comm (scalarSteps * k) scalarSteps]
              exact mirStepsDet_add pScalar scalarSteps (scalarSteps * k)
                hStep₁.1 hStepₖ.1
            · rw [Nat.mul_succ, Nat.add_comm (vecSteps * k) vecSteps]
              exact mirStepsDet_add pVec vecSteps (vecSteps * k)
                hStep₁.2.1 hStepₖ.2.1

/-! ## Part III: Narrow-Lane SIMD Wrapping vs. Wide-Accumulator Guards -/

/-- Packed narrow-lane modular addition
`Nat.mod (Nat.mod a m + Nat.mod b m) m` (modeling `u8` or `u16` SIMD lane wrap
at modulus `m = 2^w`). -/
@[expose] def narrowAddMod (m a b : Nat) : Nat :=
  Nat.mod (Nat.mod a m + Nat.mod b m) m

private theorem natMod_eq_of_lt {a m : Nat} (h : a < m) : Nat.mod a m = a :=
  Nat.mod_eq_of_lt h

private theorem natMod_self (m : Nat) : Nat.mod m m = 0 :=
  Nat.mod_self m

/-- Under domain guard `a + b < m`, narrow-lane modular addition agrees with
wide unwrapped addition (`[propext]` only). -/
theorem narrowAddMod_eq_add_of_lt {m a b : Nat} (hSumLt : a + b < m) :
    narrowAddMod m a b = a + b := by
  have haLt : a < m := Nat.lt_of_le_of_lt (Nat.le_add_right a b) hSumLt
  have hbLt : b < m := Nat.lt_of_le_of_lt (Nat.le_add_left b a) hSumLt
  unfold narrowAddMod
  rw [natMod_eq_of_lt haLt, natMod_eq_of_lt hbLt, natMod_eq_of_lt hSumLt]

/-- Boundary wrap divergence (`[propext]` only): when `a < m`, `b < m`, and
`a + b = m`, narrow-lane modular addition wraps to `0 ≠ a + b`, demonstrating
why separate panic-freedom proofs miss narrow-SIMD accumulator wraps that
`SafeTwin` equivalence catches unless guarded by `a + b < m`. -/
theorem narrowAddMod_ne_add_at_modulus {m a b : Nat}
    (haLt : a < m) (hbLt : b < m) (hSumEq : a + b = m) :
    narrowAddMod m a b = 0 ∧ narrowAddMod m a b ≠ a + b := by
  have hPos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le a) haLt
  have hModZero : narrowAddMod m a b = 0 := by
    unfold narrowAddMod
    rw [natMod_eq_of_lt haLt, natMod_eq_of_lt hbLt, hSumEq, natMod_self m]
  refine ⟨hModZero, ?_⟩
  intro hEq
  rw [hModZero, hSumEq] at hEq
  exact Nat.ne_of_lt hPos hEq

end Anneal.SafeTwin

end
