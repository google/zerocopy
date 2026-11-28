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
public import Init.Data.List.Basic
public import Init.Data.Option.Basic
public import Trusted.Framework
public import Anneal.Framework.StepWp
public import Anneal.Core.SpecRealizability
public import Anneal.LinearArith
public import Anneal.BitTrieLrat

public section

/-!
# Checked Producers: Gates, Fallbacks, and Ratchets (`Anneal.Hybrid`)

Some components are much easier to check than to compute: a register
allocator, a solver, a SIMD fast path, or a heuristic layout search. Such a
component can be built from an untrusted *producer* that proposes a result,
a verified *checker* that accepts only results satisfying the
specification, and, when every input must get an answer, a verified
*fallback*. The combination meets its specification without any proof
about the producer's logic. This module states that pattern once and proves
the laws its compositions rely on.

1. **Gates (`RawOutcome`, `HybridErr`, `CertifiedGate`, `evalGate`):** a
   producer's result is a `RawOutcome`: a candidate output with a witness
   (such as a certificate), a producer error, or a trap. `CertifiedGate`
   bundles a Boolean checker with its soundness proof and a witness-size
   bound. `evalGate` rejects an oversized witness before calling the
   checker (`evalGate_rejects_oversized`), so `sound` may assume the bound,
   and every accepted output meets the specification (`evalGate_sound`).
2. **Combinators:** `firstAccepted` tries producers in order and returns
   the first output the gate accepts. It succeeds exactly when some
   producer's output is accepted (`firstAccepted_ok_iff_exists`).
   `withFallback` replaces a rejection with a fallback result whose
   correctness is proved directly, so the checker only needs to be sound,
   not complete (`withFallback_total_sound`). `foldHintSteps` applies a
   gated step, or the fallback step, once per hint and preserves an
   invariant (`foldHintSteps_preserves_inv`). `foldStreamPrefix` emits each
   chunk only after the gate accepts it and stops at the first rejection,
   so every emitted chunk is valid (`foldStreamPrefix_all_emitted_valid`).
3. **Certificate cuts (`gateCheckBounded`, `certGateCut_sound`):** a gate's
   bounded check, sealed behind `Anneal.Framework.StepWp.BoolCertCut`,
   lets a certificate produced outside Lean discharge a goal by `rfl`.
   `natCutGate`, `intCutGate`, and `rupGate` wrap the `Anneal.LinearArith`
   and `Anneal.BitTrieLrat` checkers as gates.
4. **In-process producers (`rung15_with_callerMemPreserved_sound`):** a
   producer that runs in the caller's address space, against an abstract
   outcome model over `Trusted.Framework.FnContract`. If the producer is
   free of undefined behavior and leaves caller memory unchanged, the
   gated composition meets the outer contract with no proof about the
   producer's return value. Freedom from undefined behavior alone is not
   enough: a producer can corrupt the memory the checker and fallback then
   read (see `Anneal.Hybrid.Canaries`).
5. **Ratchets (`HybridRefines`):** replacing a component by one whose
   declared effect mask is at least as strong, whose accepted outputs are
   sound, and that accepts on every input the old one accepted preserves
   every caller proof (`hybridRefines_trans`,
   `ratchet_result_preserves_outer_safety_and_availability`). The masks are
   labels: a contract proof for each implementation, such as the one in
   part 4, is what establishes the effects they declare.
6. **Anti-vacuity (`HasAcceptedWitness`, `optionLift`):** two separate
   obligations. An implementation that always rejects satisfies "every
   accepted output is correct", so a fallible component also needs a
   witness that some input is accepted (`HasAcceptedWitness`). Separately,
   the lifted specification `optionLift Spec` should constrain accepted
   outputs: its ordinary postcondition dichotomy holds whenever `Spec`
   rejects some output, even if `Spec` accepts nothing
   (`optionLift_dichotomy_while_none_passes`), whereas its dichotomy inside
   the accepted fibre is exactly the dichotomy of `Spec`
   (`optionLift_acceptedDichotomy_iff`).

Every declaration depends on at most `propext`, recursive definitions use
`List.foldr` or `List.foldl` (`0` `._unsafe_rec`), and nothing here is
bundled or trusted.
-/

namespace Anneal.Hybrid

open Trusted.Framework

/-! ## Part I: Gates -/

/-- What a producer returns once its isolation boundary has run: a candidate
output with a witness, a producer-reported error, or a trap (a panic, fuel
exhaustion, a timeout, or an unreadable result). -/
inductive RawOutcome (E Y W : Type) where
  | candidate (y : Y) (w : W)
  | prodErr (e : E)
  | trapped

/-- Why a gate produced no output. Rejections carry no candidate output and
no witness. -/
inductive HybridErr (E : Type) where
  | producerTrapped
  | producerFailed (e : E)
  | witnessOversized (actual maxAllowed : Nat)
  | rejectedByChecker

/-- A Boolean checker `check` for `Spec` under `Pre`, with a witness-size
bound. `sound` may assume `wSize w ≤ maxWitness x` because `evalGate`
rejects larger witnesses before it calls `check`. Witness-free checks use
`W := Unit` and constant-zero size functions. -/
structure CertifiedGate (X Y W : Type) (Pre : X → Prop)
    (Spec : X → Y → Prop) where
  maxWitness : X → Nat
  wSize : W → Nat
  check : X → Y → W → Bool
  sound : ∀ x y w, Pre x → wSize w ≤ maxWitness x → check x y w = true →
    Spec x y

/-- Evaluate a gate on one producer outcome. -/
@[expose] def evalGate {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X) :
    RawOutcome E Y W → Except (HybridErr E) Y
  | .trapped => .error .producerTrapped
  | .prodErr e => .error (.producerFailed e)
  | .candidate y w =>
    match Nat.ble (g.wSize w) (g.maxWitness x) with
    | false => .error (.witnessOversized (g.wSize w) (g.maxWitness x))
    | true =>
      match g.check x y w with
      | true => .ok y
      | false => .error .rejectedByChecker

/-- A gate accepts a candidate exactly when its witness fits the bound and
the checker accepts it. -/
theorem evalGate_candidate_ok_iff {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X)
    (y : Y) (w : W) (yOut : Y) :
    evalGate (E := E) g x (.candidate y w) = .ok yOut ↔
      yOut = y ∧ g.wSize w ≤ g.maxWitness x ∧ g.check x y w = true := by
  dsimp only [evalGate]
  cases hB : Nat.ble (g.wSize w) (g.maxWitness x) with
  | false =>
    refine ⟨fun h => (by cases h), fun h => ?_⟩
    have hLe : Nat.ble (g.wSize w) (g.maxWitness x) = true :=
      Nat.ble_eq_true_of_le h.2.1
    rw [hB] at hLe
    cases hLe
  | true =>
    cases hC : g.check x y w with
    | false =>
      refine ⟨fun h => (by cases h), fun h => ?_⟩
      have hC' : false = true := h.2.2
      cases hC'
    | true =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · injection h with h
        exact ⟨h.symm, Nat.le_of_ble_eq_true hB, rfl⟩
      · rw [h.1]

/-- Every output a gate accepts satisfies the specification. -/
theorem evalGate_sound {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X)
    (raw : RawOutcome E Y W) (y : Y) (hPre : Pre x)
    (hOk : evalGate g x raw = .ok y) : Spec x y := by
  cases raw with
  | trapped => cases hOk
  | prodErr _ => cases hOk
  | candidate yc wc =>
    have h := (evalGate_candidate_ok_iff g x yc wc y).1 hOk
    rw [h.1]
    exact g.sound x yc wc hPre h.2.1 h.2.2

/-- An oversized witness is rejected without consulting the checker: the
result does not mention `g.check`. -/
theorem evalGate_rejects_oversized {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X)
    (y : Y) (w : W) (hOver : g.maxWitness x < g.wSize w) :
    evalGate (E := E) g x (.candidate y w) =
      .error (.witnessOversized (g.wSize w) (g.maxWitness x)) := by
  dsimp only [evalGate]
  cases hB : Nat.ble (g.wSize w) (g.maxWitness x) with
  | false => rfl
  | true => exact absurd (Nat.le_of_ble_eq_true hB) (Nat.not_le_of_gt hOver)

/-- Project a gate result to `Option`, the fallible carrier that Profile v2
MIR verification supports. -/
@[expose] def toOption {E Y : Type} : Except (HybridErr E) Y → Option Y
  | .ok y => some y
  | .error _ => none

theorem toOption_eq_some_iff {E Y : Type} (res : Except (HybridErr E) Y)
    (y : Y) : toOption res = some y ↔ res = .ok y := by
  cases res with
  | error _ => exact ⟨fun h => (by cases h), fun h => by cases h⟩
  | ok y' =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · injection h with h
      rw [h]
    · injection h with h
      rw [h]
      rfl

theorem toOption_evalGate_sound {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X)
    (raw : RawOutcome E Y W) (y : Y) (hPre : Pre x)
    (hSome : toOption (evalGate g x raw) = some y) : Spec x y :=
  evalGate_sound g x raw y hPre ((toOption_eq_some_iff _ y).1 hSome)

/-! ## Part II: Combinators -/

/-! ### Portfolios (`firstAccepted`) -/

/-- One step of `firstAccepted`: keep `r`'s output if the gate accepts it,
and otherwise use the result for the remaining producers (`none` when there
are none, in which case `r`'s rejection is reported). -/
@[expose] def firstAcceptedStep {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X)
    (r : RawOutcome E Y W) (rest : Option (Except (HybridErr E) Y)) :
    Except (HybridErr E) Y :=
  match evalGate g x r with
  | .ok y => .ok y
  | .error e =>
    match rest with
    | none => .error e
    | some res => res

/-- `firstAccepted` over a list, or `none` for the empty list. -/
@[expose] def firstAcceptedOpt {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X)
    (rs : List (RawOutcome E Y W)) : Option (Except (HybridErr E) Y) :=
  List.foldr (fun r acc => some (firstAcceptedStep g x r acc)) none rs

/-- The first gate-accepted output among `rs`, in order. If none is
accepted, the last producer's rejection is reported (`producerTrapped` for
an empty list). Rejection of one producer's output never hides a later
producer's acceptable output. -/
@[expose] def firstAccepted {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X)
    (rs : List (RawOutcome E Y W)) : Except (HybridErr E) Y :=
  match firstAcceptedOpt g x rs with
  | none => .error .producerTrapped
  | some res => res

theorem firstAcceptedOpt_cons {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X)
    (r : RawOutcome E Y W) (rs : List (RawOutcome E Y W)) :
    firstAcceptedOpt g x (r :: rs) =
      some (firstAcceptedStep g x r (firstAcceptedOpt g x rs)) :=
  rfl

theorem firstAccepted_nil {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X) :
    firstAccepted (E := E) g x [] = .error .producerTrapped :=
  rfl

theorem firstAccepted_ok_iff_opt {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X)
    (rs : List (RawOutcome E Y W)) (y : Y) :
    firstAccepted g x rs = .ok y ↔ firstAcceptedOpt g x rs = some (.ok y) := by
  dsimp only [firstAccepted]
  cases firstAcceptedOpt g x rs with
  | none => exact ⟨fun h => (by cases h), fun h => by cases h⟩
  | some res =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h' : res = .ok y := h
      rw [h']
    · injection h

theorem firstAcceptedOpt_sound {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X)
    (hPre : Pre x) :
    ∀ (rs : List (RawOutcome E Y W)) (y : Y),
      firstAcceptedOpt g x rs = some (.ok y) → Spec x y
  | [], _, h => by cases h
  | r :: rs, y, h => by
    rw [firstAcceptedOpt_cons] at h
    injection h with h
    revert h
    dsimp only [firstAcceptedStep]
    cases hEv : evalGate g x r with
    | ok y' =>
      intro h
      have h' : (Except.ok y' : Except (HybridErr E) Y) = .ok y := h
      injection h' with h'
      rw [← h']
      exact evalGate_sound g x r y' hPre hEv
    | error _ =>
      cases hRest : firstAcceptedOpt g x rs with
      | none => intro h; cases h
      | some res =>
        intro h
        have h' : res = .ok y := h
        rw [h'] at hRest
        exact firstAcceptedOpt_sound g x hPre rs y hRest

/-- Every output `firstAccepted` returns satisfies the specification. -/
theorem firstAccepted_sound {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X)
    (rs : List (RawOutcome E Y W)) (y : Y) (hPre : Pre x)
    (hOk : firstAccepted g x rs = .ok y) : Spec x y :=
  firstAcceptedOpt_sound g x hPre rs y
    ((firstAccepted_ok_iff_opt g x rs y).1 hOk)

theorem firstAcceptedOpt_ok_iff_exists {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X) :
    ∀ rs : List (RawOutcome E Y W),
      (∃ y, firstAcceptedOpt g x rs = some (.ok y)) ↔
        (∃ r, r ∈ rs ∧ ∃ y, evalGate g x r = .ok y)
  | [] => ⟨fun ⟨_, h⟩ => (by cases h), fun ⟨_, hMem, _⟩ => by cases hMem⟩
  | r :: rs => by
    have ih := firstAcceptedOpt_ok_iff_exists g x rs
    rw [firstAcceptedOpt_cons]
    dsimp only [firstAcceptedStep]
    cases hEv : evalGate g x r with
    | ok y' =>
      exact ⟨fun _ => ⟨r, List.Mem.head _, y', hEv⟩, fun _ => ⟨y', rfl⟩⟩
    | error e =>
      refine ⟨fun ⟨y, h⟩ => ?_, fun ⟨r', hMem, y', hEv'⟩ => ?_⟩
      · revert h
        cases hRest : firstAcceptedOpt g x rs with
        | none => intro h; cases h
        | some res =>
          intro h
          injection h with h
          have h' : res = .ok y := h
          rw [h'] at hRest
          have ⟨r', hMem, y', hEv'⟩ := ih.1 ⟨y, hRest⟩
          exact ⟨r', List.Mem.tail _ hMem, y', hEv'⟩
      · cases hMem with
        | head =>
          rw [hEv] at hEv'
          cases hEv'
        | tail _ hTl =>
          have ⟨y, hRest⟩ := ih.2 ⟨r', hTl, y', hEv'⟩
          rw [hRest]
          exact ⟨y, rfl⟩

/-- `firstAccepted` succeeds exactly when the gate accepts some producer's
output. -/
theorem firstAccepted_ok_iff_exists {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X)
    (rs : List (RawOutcome E Y W)) :
    (∃ y, firstAccepted g x rs = .ok y) ↔
      (∃ r, r ∈ rs ∧ ∃ y, evalGate g x r = .ok y) := by
  refine Iff.trans ⟨fun ⟨y, h⟩ => ⟨y, ?_⟩, fun ⟨y, h⟩ => ⟨y, ?_⟩⟩
    (firstAcceptedOpt_ok_iff_exists g x rs)
  · exact (firstAccepted_ok_iff_opt g x rs y).1 h
  · exact (firstAccepted_ok_iff_opt g x rs y).2 h

/-! ### Verified fallbacks (`withFallback`) -/

/-- Use the gate's output if there is one and the fallback's otherwise. The
fallback's result is not passed back through the checker. -/
@[expose] def withFallback {X Y E : Type} (x : X)
    (res : Except (HybridErr E) Y) (fb : X → Y) : Y :=
  match res with
  | .ok y => y
  | .error _ => fb x

theorem withFallback_error {X Y E : Type} (x : X) (e : HybridErr E)
    (fb : X → Y) : withFallback x (.error e) fb = fb x :=
  rfl

/-- `withFallback` meets `Spec` whenever every accepted output does and the
fallback does. -/
theorem withFallback_sound_of {X Y E : Type} {Spec : X → Y → Prop} (x : X)
    (res : Except (HybridErr E) Y) (fb : X → Y)
    (hRes : ∀ y, res = .ok y → Spec x y) (hFb : Spec x (fb x)) :
    Spec x (withFallback x res fb) := by
  cases res with
  | ok y => exact hRes y rfl
  | error _ => exact hFb

/-- A gate paired with a fallback proved correct directly is total and
sound. The checker need not accept the fallback's outputs. -/
theorem withFallback_total_sound {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X)
    (raw : RawOutcome E Y W) (fb : X → Y) (hPre : Pre x)
    (hFb : ∀ x', Pre x' → Spec x' (fb x')) :
    Spec x (withFallback x (evalGate g x raw) fb) :=
  withFallback_sound_of x _ fb (fun y h => evalGate_sound g x raw y hPre h)
    (hFb x hPre)

theorem withFallback_firstAccepted_sound {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X)
    (rs : List (RawOutcome E Y W)) (fb : X → Y) (hPre : Pre x)
    (hFb : ∀ x', Pre x' → Spec x' (fb x')) :
    Spec x (withFallback x (firstAccepted g x rs) fb) :=
  withFallback_sound_of x _ fb
    (fun y h => firstAccepted_sound g x rs y hPre h) (hFb x hPre)

/-! ### Hint-guided steps (`foldHintSteps`) -/

/-- One hint-guided step: the producer's proposed next state if the gate
accepts it, and the fallback step otherwise. -/
@[expose] def hintStep {S U W E : Type} {Inv : S → Prop}
    {StepRel : S → U → S → Prop}
    (gStep : CertifiedGate (S × U) S W (fun su => Inv su.1)
      (fun su s' => Inv s' ∧ StepRel su.1 su.2 s'))
    (pStep : S → U → RawOutcome E S W) (fbStep : S × U → S)
    (s : S) (u : U) : S :=
  withFallback (s, u) (evalGate gStep (s, u) (pStep s u)) fbStep

/-- Apply `hintStep` once per hint, left to right. -/
@[expose] def foldHintSteps {S U W E : Type} {Inv : S → Prop}
    {StepRel : S → U → S → Prop}
    (gStep : CertifiedGate (S × U) S W (fun su => Inv su.1)
      (fun su s' => Inv s' ∧ StepRel su.1 su.2 s'))
    (pStep : S → U → RawOutcome E S W) (fbStep : S × U → S)
    (s0 : S) (us : List U) : S :=
  List.foldl (hintStep gStep pStep fbStep) s0 us

/-- A rejected hint leaves the producer's proposal unused: the step is the
fallback step from the current state. -/
theorem hintStep_rejected {S U W E : Type} {Inv : S → Prop}
    {StepRel : S → U → S → Prop}
    (gStep : CertifiedGate (S × U) S W (fun su => Inv su.1)
      (fun su s' => Inv s' ∧ StepRel su.1 su.2 s'))
    (pStep : S → U → RawOutcome E S W) (fbStep : S × U → S) (s : S) (u : U)
    (e : HybridErr E) (hRej : evalGate gStep (s, u) (pStep s u) = .error e) :
    hintStep gStep pStep fbStep s u = fbStep (s, u) := by
  dsimp only [hintStep]
  rw [hRej]
  rfl

/-- Each step relates the old and new states and preserves `Inv`. -/
theorem hintStep_sound {S U W E : Type} {Inv : S → Prop}
    {StepRel : S → U → S → Prop}
    (gStep : CertifiedGate (S × U) S W (fun su => Inv su.1)
      (fun su s' => Inv s' ∧ StepRel su.1 su.2 s'))
    (pStep : S → U → RawOutcome E S W) (fbStep : S × U → S)
    (hFb : ∀ su, Inv su.1 → Inv (fbStep su) ∧ StepRel su.1 su.2 (fbStep su))
    (s : S) (u : U) (hInv : Inv s) :
    Inv (hintStep gStep pStep fbStep s u) ∧
      StepRel s u (hintStep gStep pStep fbStep s u) :=
  withFallback_total_sound gStep (s, u) (pStep s u) fbStep hInv hFb

theorem foldHintSteps_preserves_inv {S U W E : Type} {Inv : S → Prop}
    {StepRel : S → U → S → Prop}
    (gStep : CertifiedGate (S × U) S W (fun su => Inv su.1)
      (fun su s' => Inv s' ∧ StepRel su.1 su.2 s'))
    (pStep : S → U → RawOutcome E S W) (fbStep : S × U → S)
    (hFb : ∀ su, Inv su.1 → Inv (fbStep su) ∧ StepRel su.1 su.2 (fbStep su)) :
    ∀ (us : List U) (s0 : S), Inv s0 →
      Inv (foldHintSteps gStep pStep fbStep s0 us)
  | [], _, hInit => hInit
  | u :: us, s0, hInit =>
    foldHintSteps_preserves_inv gStep pStep fbStep hFb us _
      (hintStep_sound gStep pStep fbStep hFb s0 u hInit).1

/-! ### Prefix-safe streams (`foldStreamPrefix`) -/

/-- Emit chunks while the gate accepts them, threading state left to right.
The first rejection ends the stream and is returned alongside the chunks
emitted before it. -/
@[expose] def foldStreamPrefix {S U C W E : Type} {AccInv : S → Prop}
    {ValidChunk : C → Prop}
    (gChunk : CertifiedGate (S × U) (S × C) W (fun su => AccInv su.1)
      (fun _ sc => AccInv sc.1 ∧ ValidChunk sc.2))
    (pChunk : S → U → RawOutcome E (S × C) W) (s0 : S) (us : List U) :
    List C × Option (HybridErr E) :=
  List.foldr
    (fun u (k : S → List C × Option (HybridErr E)) (s : S) =>
      match evalGate gChunk (s, u) (pChunk s u) with
      | .error err => ([], some err)
      | .ok sc =>
        let rest := k sc.1
        (sc.2 :: rest.1, rest.2))
    (fun _ => ([], none)) us s0

theorem foldStreamPrefix_cons {S U C W E : Type} {AccInv : S → Prop}
    {ValidChunk : C → Prop}
    (gChunk : CertifiedGate (S × U) (S × C) W (fun su => AccInv su.1)
      (fun _ sc => AccInv sc.1 ∧ ValidChunk sc.2))
    (pChunk : S → U → RawOutcome E (S × C) W) (s0 : S) (u : U)
    (us : List U) :
    foldStreamPrefix gChunk pChunk s0 (u :: us) =
      match evalGate gChunk (s0, u) (pChunk s0 u) with
      | .error err => ([], some err)
      | .ok sc =>
        let rest := foldStreamPrefix gChunk pChunk sc.1 us
        (sc.2 :: rest.1, rest.2) :=
  rfl

/-- A rejected chunk is not emitted and stops the stream. -/
theorem foldStreamPrefix_halts {S U C W E : Type} {AccInv : S → Prop}
    {ValidChunk : C → Prop}
    (gChunk : CertifiedGate (S × U) (S × C) W (fun su => AccInv su.1)
      (fun _ sc => AccInv sc.1 ∧ ValidChunk sc.2))
    (pChunk : S → U → RawOutcome E (S × C) W) (s0 : S) (u : U)
    (us : List U) (err : HybridErr E)
    (hRej : evalGate gChunk (s0, u) (pChunk s0 u) = .error err) :
    foldStreamPrefix gChunk pChunk s0 (u :: us) = ([], some err) := by
  rw [foldStreamPrefix_cons, hRej]

/-- Every emitted chunk is valid, including when the stream stops early. -/
theorem foldStreamPrefix_all_emitted_valid {S U C W E : Type}
    {AccInv : S → Prop} {ValidChunk : C → Prop}
    (gChunk : CertifiedGate (S × U) (S × C) W (fun su => AccInv su.1)
      (fun _ sc => AccInv sc.1 ∧ ValidChunk sc.2))
    (pChunk : S → U → RawOutcome E (S × C) W) :
    ∀ (us : List U) (s0 : S), AccInv s0 →
      ∀ c, c ∈ (foldStreamPrefix gChunk pChunk s0 us).1 → ValidChunk c
  | [], _, _, _, hMem => by cases hMem
  | u :: us, s0, hInit, c, hMem => by
    rw [foldStreamPrefix_cons] at hMem
    revert hMem
    cases hEv : evalGate gChunk (s0, u) (pChunk s0 u) with
    | error _ => intro hMem; cases hMem
    | ok sc =>
      intro hMem
      have hSound := evalGate_sound gChunk (s0, u) (pChunk s0 u) sc hInit hEv
      cases hMem with
      | head => exact hSound.2
      | tail _ hTl =>
        exact foldStreamPrefix_all_emitted_valid gChunk pChunk us sc.1
          hSound.1 c hTl

/-! ## Part III: Certificate cuts -/

/-- A gate's complete acceptance test (size bound and checker) on one
`(input, output, witness)` triple. -/
@[expose] def gateCheckBounded {X Y W : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec)
    (p : X × Y × W) : Bool :=
  Nat.ble (g.wSize p.2.2) (g.maxWitness p.1) && g.check p.1 p.2.1 p.2.2

/-- `gateCheckBounded` accepts exactly the candidates `evalGate` accepts. -/
theorem gateCheckBounded_iff_evalGate {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X)
    (y : Y) (w : W) :
    gateCheckBounded g (x, y, w) = true ↔
      evalGate (E := E) g x (.candidate y w) = .ok y := by
  refine Iff.trans ?_ (evalGate_candidate_ok_iff g x y w y).symm
  dsimp only [gateCheckBounded]
  cases hB : Nat.ble (g.wSize w) (g.maxWitness x) with
  | false =>
    refine ⟨fun h => (by cases h), fun h => ?_⟩
    have hLe := Nat.ble_eq_true_of_le h.2.1
    rw [hB] at hLe
    cases hLe
  | true =>
    exact ⟨fun h => ⟨rfl, Nat.le_of_ble_eq_true hB, h⟩, fun h => h.2.2⟩

/-- A certificate accepted by a sealed `BoolCertCut` over
`gateCheckBounded g` establishes the specification. A certificate computed
outside Lean can discharge `hCut` by
`Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl`, so the tool that
produced it is not trusted. -/
theorem certGateCut_sound {X Y W : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) {x : X} {y : Y}
    {w : W} (hPre : Pre x)
    (hCut : Anneal.Framework.StepWp.BoolCertCut (gateCheckBounded g)
      (x, y, w)) :
    Spec x y := by
  have h0 := Anneal.Framework.StepWp.BoolCertCut.unseal hCut
  have h : (Nat.ble (g.wSize w) (g.maxWitness x) && g.check x y w) = true :=
    h0
  cases hB : Nat.ble (g.wSize w) (g.maxWitness x) with
  | false =>
    rw [hB] at h
    cases h
  | true =>
    rw [hB] at h
    exact g.sound x y w hPre (Nat.le_of_ble_eq_true hB) h

/-- `Anneal.LinearArith` natural-number cut certificates as a gate. The
witness is the `CutStep` list, bounded by `maxSteps` steps. -/
@[expose] noncomputable def natCutGate (maxSteps : Nat) :
    CertifiedGate Anneal.LinearArith.NatCutGoal Unit
      (List Anneal.LinearArith.CutStep) (fun _ => True)
      (fun goal _ => goal.denote) :=
  { maxWitness := fun _ => maxSteps
    wSize := List.length
    check := fun goal _ steps => Anneal.LinearArith.checkNatCutGoal goal steps
    sound := fun goal _ steps _ _ h =>
      Anneal.LinearArith.checkNatCutGoal_sound goal steps h }

/-- `Anneal.LinearArith` integer cut certificates as a gate. -/
@[expose] noncomputable def intCutGate (maxSteps : Nat) :
    CertifiedGate Anneal.LinearArith.IntCutGoal Unit
      (List Anneal.LinearArith.CutStep) (fun _ => True)
      (fun goal _ => goal.denote) :=
  { maxWitness := fun _ => maxSteps
    wSize := List.length
    check := fun goal _ steps => Anneal.LinearArith.checkIntCutGoal goal steps
    sound := fun goal _ steps _ _ h =>
      Anneal.LinearArith.checkIntCutGoal_sound goal steps h }

/-- `true` exactly for `RupVerdict.unsatVerified`. -/
@[expose] def isUnsatVerified : Anneal.BitTrieLrat.RupVerdict → Bool
  | .unsatVerified => true
  | _ => false

theorem eq_unsatVerified_of_isUnsatVerified
    (v : Anneal.BitTrieLrat.RupVerdict) (h : isUnsatVerified v = true) :
    v = .unsatVerified := by
  cases v with
  | unsatVerified => rfl
  | errBadHint _ _ => cases h
  | errNoConflict _ => cases h
  | errFinalNotEmpty => cases h

/-- `Anneal.BitTrieLrat` RUP refutations as a gate over CNF formulas, with
trie depth `depth` and at most `maxSteps` proof steps. -/
@[expose] def rupGate (depth maxSteps : Nat) :
    CertifiedGate (List Anneal.BitTrieLrat.Clause) Unit
      (List Anneal.BitTrieLrat.RupStep) (fun _ => True)
      (fun cnf _ => Anneal.BitTrieLrat.UnsatCnf cnf) :=
  { maxWitness := fun _ => maxSteps
    wSize := List.length
    check := fun cnf _ steps =>
      isUnsatVerified (Anneal.BitTrieLrat.checkRupProof depth cnf steps)
    sound := fun cnf _ steps _ _ h =>
      Anneal.BitTrieLrat.checkRupProof_sound depth cnf steps
        (eq_unsatVerified_of_isUnsatVerified _ h) }

/-! ## Part IV: In-process producers -/

/-- Outcome of one run in an abstract model of a function call: a terminal
outcome in the sense of `Trusted.Framework`, divergence, or undefined
behavior. This is a denotational stand-in for a MIR execution model; it is
not connected to `Trusted.MirSemantics`. -/
inductive RunOutcome (Ret Mem : Type) where
  | terminal (o : TerminalOutcome Ret Mem)
  | diverged
  | faultUB

/-- Whether contract `c` permits outcome `o` on query `q`, following the
outcome clauses of `Trusted.Framework.BodySatisfiesEntry`. -/
@[expose] def OutcomeAllowed {Q Ret Mem : Type} (c : FnContract Q Ret Mem)
    (q : Q) : RunOutcome Ret Mem → Prop
  | .terminal (.returned r m) => c.postReturn q r m
  | .terminal (.unwound m) => c.effects.noUnwind = false ∧ c.postUnwind q m
  | .terminal (.aborted m) => c.effects.noAbort = false ∧ c.postAbort q m
  | .diverged => c.effects.terminates = false
  | .faultUB => False

/-- `run` (a relation from queries to the outcomes they may have) meets `c`:
no undefined behavior under the effective safety precondition, and only
permitted outcomes under the effective behavior precondition. -/
@[expose] def ContractHolds {Q Ret Mem : Type} (c : FnContract Q Ret Mem)
    (isUnsafe : Bool) (run : Q → RunOutcome Ret Mem → Prop) : Prop :=
  (∀ q, c.effectiveSafetyPre isUnsafe q → ¬ run q .faultUB) ∧
  (∀ q, c.effectiveBehaviorPre isUnsafe q → ∀ o, run q o →
    OutcomeAllowed c q o)

/-- Pointwise order on effect masks: `maskLe m1 m2` when `m2` guarantees
everything `m1` does. This is `Anneal.Framework.effectMaskLe`, restated to
avoid importing `Anneal.MirWp`. -/
@[expose] def maskLe (m1 m2 : EffectMask) : Prop :=
  (m1.terminates = true → m2.terminates = true) ∧
  (m1.noUnwind = true → m2.noUnwind = true) ∧
  (m1.noAbort = true → m2.noAbort = true)

theorem maskLe_refl (m : EffectMask) : maskLe m m :=
  ⟨fun h => h, fun h => h, fun h => h⟩

theorem maskLe_trans {m1 m2 m3 : EffectMask} (h12 : maskLe m1 m2)
    (h23 : maskLe m2 m3) : maskLe m1 m3 :=
  ⟨fun h => h23.1 (h12.1 h), fun h => h23.2.1 (h12.2.1 h),
    fun h => h23.2.2 (h12.2.2 h)⟩

/-- Run the checker on the producer's candidate in the memory the producer
returned, then commit or fall back. -/
@[expose] def rung15Step {Mem X Y W : Type}
    (check : Mem × X → Y → W → Bool) (commit : Mem × X → Y → Mem)
    (fb : Mem × X → Y × Mem) (x : X) :
    RunOutcome (Y × W) Mem → RunOutcome Y Mem
  | .terminal (.returned yw m) =>
    match check (m, x) yw.1 yw.2 with
    | true => .terminal (.returned yw.1 (commit (m, x) yw.1))
    | false => .terminal (.returned (fb (m, x)).1 (fb (m, x)).2)
  | .terminal (.unwound m) => .terminal (.unwound m)
  | .terminal (.aborted m) => .terminal (.aborted m)
  | .diverged => .diverged
  | .faultUB => .faultUB

/-- The outcomes of an in-process producer `f` followed by `rung15Step`. -/
@[expose] def rung15Run {Mem X Y W : Type}
    (f : Mem × X → RunOutcome (Y × W) Mem → Prop)
    (check : Mem × X → Y → W → Bool) (commit : Mem × X → Y → Mem)
    (fb : Mem × X → Y × Mem) (q : Mem × X) (out : RunOutcome Y Mem) : Prop :=
  ∃ o, f q o ∧ rung15Step check commit fb q.2 o = out

/-- The in-process producer obligation: it returns or unwinds with caller
memory unchanged and never aborts. It says nothing about the returned
candidate. -/
@[expose] def rung15ProducerContract {Mem X Ret : Type}
    (sPre bPre : Mem × X → Prop) (eff : EffectMask) :
    FnContract (Mem × X) Ret Mem :=
  { safetyPre := sPre
    behaviorPre := bPre
    postReturn := fun q _ m' => m' = q.1
    postUnwind := fun q m' => m' = q.1
    postAbort := fun _ _ => False
    effects := eff }

/-- The contract the gated composition meets. -/
@[expose] def rung15OuterContract {Mem X Y : Type}
    (sPre bPre : Mem × X → Prop) (post : Mem × X → Y → Mem → Prop)
    (eff : EffectMask) : FnContract (Mem × X) Y Mem :=
  { safetyPre := sPre
    behaviorPre := bPre
    postReturn := post
    postUnwind := fun q m' => m' = q.1
    postAbort := fun _ _ => False
    effects := eff }

/-- The effective behavior precondition shared by both contracts. -/
@[expose] def Rung15Pre {Mem X : Type} (sPre bPre : Mem × X → Prop)
    (isUnsafe : Bool) (q : Mem × X) : Prop :=
  (isUnsafe = true → sPre q) ∧ bPre q

/-- An in-process producer that is free of undefined behavior and preserves
caller memory, composed with a sound checker and a fallback proved correct,
meets the outer contract. No property of the producer's candidate is
assumed, and the outer contract may promise any effects the producer
guarantees. -/
theorem rung15_with_callerMemPreserved_sound {Mem X Y W : Type}
    (sPre bPre : Mem × X → Prop) (post : Mem × X → Y → Mem → Prop)
    (fEff outerEff : EffectMask) (isUnsafe : Bool)
    (f : Mem × X → RunOutcome (Y × W) Mem → Prop)
    (check : Mem × X → Y → W → Bool) (commit : Mem × X → Y → Mem)
    (fb : Mem × X → Y × Mem) (hMask : maskLe outerEff fEff)
    (hF : ContractHolds (rung15ProducerContract sPre bPre fEff) isUnsafe f)
    (hCheck : ∀ q y w, Rung15Pre sPre bPre isUnsafe q →
      check q y w = true → post q y (commit q y))
    (hFb : ∀ q, Rung15Pre sPre bPre isUnsafe q → post q (fb q).1 (fb q).2) :
    ContractHolds (rung15OuterContract sPre bPre post outerEff) isUnsafe
      (rung15Run f check commit fb) := by
  refine ⟨?_, ?_⟩
  · intro q hS hRun
    have ⟨o, hfo, hStep⟩ := hRun
    cases o with
    | faultUB => exact hF.1 q hS hfo
    | diverged => cases hStep
    | terminal t =>
      cases t with
      | returned yw m =>
        revert hStep
        dsimp only [rung15Step]
        cases check (m, q.2) yw.1 yw.2 with
        | true => intro h; cases h
        | false => intro h; cases h
      | unwound _ => cases hStep
      | aborted _ => cases hStep
  · intro q hB o' hRun
    have ⟨o, hfo, hStep⟩ := hRun
    rw [← hStep]
    have hA := hF.2 q hB o hfo
    cases q with
    | mk mem x =>
    cases o with
    | faultUB => exact hA.elim
    | diverged =>
      have hA' : fEff.terminates = false := hA
      change outerEff.terminates = false
      cases hO : outerEff.terminates with
      | false => rfl
      | true =>
        have hT := hMask.1 hO
        rw [hA'] at hT
        cases hT
    | terminal t =>
      cases t with
      | aborted _ => exact hA.2.elim
      | unwound m =>
        have hA' : fEff.noUnwind = false ∧ m = mem := hA
        change outerEff.noUnwind = false ∧ m = mem
        refine ⟨?_, hA'.2⟩
        cases hO : outerEff.noUnwind with
        | false => rfl
        | true =>
          have hU := hMask.2.1 hO
          rw [hA'.1] at hU
          cases hU
      | returned yw m =>
        have hA' : m = mem := hA
        rw [hA']
        dsimp only [rung15Step]
        cases hC : check (mem, x) yw.1 yw.2 with
        | true => exact hCheck (mem, x) yw.1 yw.2 hB hC
        | false => exact hFb (mem, x) hB

/-! ## Part V: Ratchets -/

/-- A component's declared effect mask and its gated result. `run` is a
total Lean function, so `mask` is a label for the effects of the component's
real implementation, not something `run` can exhibit; a contract proof for
that implementation (such as `rung15_with_callerMemPreserved_sound` with
`fEff := mask`) is what makes the label a guarantee. -/
structure HybridComponent (X E Y : Type) where
  mask : EffectMask
  run : X → Except (HybridErr E) Y

/-- Every accepted output of `f` satisfies `Spec` under `Pre`. -/
@[expose] def ResultSound {X E Y : Type} (Pre : X → Prop)
    (Spec : X → Y → Prop) (f : X → Except (HybridErr E) Y) : Prop :=
  ∀ x, Pre x → ∀ y, f x = .ok y → Spec x y

/-- `cNew` may replace `cOld`: its declared effect mask is at least as
strong, its accepted outputs are sound, and it accepts every input `cOld`
accepts. Only the masks are compared; each must still be justified by a
contract proof for its implementation. -/
@[expose] def HybridRefines {X E Y : Type} (Pre : X → Prop)
    (Spec : X → Y → Prop) (cOld cNew : HybridComponent X E Y) : Prop :=
  maskLe cOld.mask cNew.mask ∧ ResultSound Pre Spec cNew.run ∧
  (∀ x, Pre x → ∀ y, cOld.run x = .ok y → ∃ y', cNew.run x = .ok y')

theorem hybridRefines_refl {X E Y : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (c : HybridComponent X E Y)
    (hSound : ResultSound Pre Spec c.run) : HybridRefines Pre Spec c c :=
  ⟨maskLe_refl c.mask, hSound, fun _ _ y h => ⟨y, h⟩⟩

theorem hybridRefines_trans {X E Y : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} {c1 c2 c3 : HybridComponent X E Y}
    (h12 : HybridRefines Pre Spec c1 c2)
    (h23 : HybridRefines Pre Spec c2 c3) : HybridRefines Pre Spec c1 c3 := by
  refine ⟨maskLe_trans h12.1 h23.1, h23.2.1, ?_⟩
  intro x hPre y1 hOk1
  have ⟨y2, hOk2⟩ := h12.2.2 x hPre y1 hOk1
  exact h23.2.2 x hPre y2 hOk2

/-- A caller proved correct for every sound component stays correct after a
ratchet, keeps every input on which the old component succeeded, and gets a
declared effect mask at least as strong as before. -/
theorem ratchet_result_preserves_outer_safety_and_availability
    {X E Y Z E' : Type} {Pre : X → Prop} {Spec : X → Y → Prop}
    {cOld cNew : HybridComponent X E Y}
    (outer : (X → Except (HybridErr E) Y) → X → Except E' Z)
    (OuterPost : X → Z → Prop)
    (hOuter : ∀ f, ResultSound Pre Spec f →
      ∀ x, Pre x → ∀ z, outer f x = .ok z → OuterPost x z)
    (hRef : HybridRefines Pre Spec cOld cNew) :
    (∀ x, Pre x → ∀ z, outer cNew.run x = .ok z → OuterPost x z) ∧
    (∀ x, Pre x → (∃ y, cOld.run x = .ok y) → ∃ y', cNew.run x = .ok y') ∧
    maskLe cOld.mask cNew.mask :=
  ⟨hOuter cNew.run hRef.2.1,
    fun x hPre ⟨y, hOk⟩ => hRef.2.2 x hPre y hOk, hRef.1⟩

/-- When `Spec` determines the output, a ratchet from a sound component
returns the same output wherever the old one succeeded, so callers that
depend on which output they get are also preserved. -/
theorem hybridRefines_pointwise_of_deterministic {X E Y : Type}
    {Pre : X → Prop} {Spec : X → Y → Prop}
    {cOld cNew : HybridComponent X E Y}
    (hDet : Anneal.Core.ContractDeterministic Pre Spec)
    (hOld : ResultSound Pre Spec cOld.run)
    (hRef : HybridRefines Pre Spec cOld cNew) :
    ∀ x, Pre x → ∀ y, cOld.run x = .ok y → cNew.run x = .ok y := by
  intro x hPre y hOk
  have ⟨y', hNew⟩ := hRef.2.2 x hPre y hOk
  have hEq : y = y' :=
    hDet x y y' hPre (hOld x hPre y hOk) (hRef.2.1 x hPre y' hNew)
  rw [hEq]
  exact hNew

/-! ## Part VI: Anti-vacuity -/

/-- `body` is the body at `defId`, and some valid entry query satisfying the
behavior precondition returns an accepted value (`isAccepted r = true`). Pair
a fallible specification with this witness so that a body that always rejects
cannot satisfy it. Requiring `M.bodyAt prog defId = some body` keeps the
entry domain and the executed body the same, so one body's entry domain cannot
be paired with another body's accepted execution. -/
@[expose] def HasAcceptedWitness {Prog Body Sig Query Ret Mem : Type}
    (M : ExecutionModel Prog Body Sig Query Ret Mem) (prog : Prog)
    (defId : Nat) (body : Body) (c : FnContract Query Ret Mem)
    (isAccepted : Ret → Bool) : Prop :=
  M.bodyAt prog defId = some body ∧
  ∃ q r m, M.entryDom body q ∧
    c.effectiveBehaviorPre (M.bodyIsUnsafe body) q ∧
    M.produces (M.execForBody prog defId) q (.returned r m) ∧
    isAccepted r = true

/-- A body whose every normal return is rejected has no accepted
witness. -/
theorem not_hasAcceptedWitness_of_alwaysRejects
    {Prog Body Sig Query Ret Mem : Type}
    (M : ExecutionModel Prog Body Sig Query Ret Mem) (prog : Prog)
    (defId : Nat) (body : Body) (c : FnContract Query Ret Mem)
    (isAccepted : Ret → Bool)
    (hRej : ∀ q r m, M.produces (M.execForBody prog defId) q (.returned r m) →
      isAccepted r = false) :
    ¬ HasAcceptedWitness M prog defId body c isAccepted := by
  intro ⟨_, q, r, m, _, _, hProd, hAcc⟩
  rw [hRej q r m hProd] at hAcc
  cases hAcc

/-- An accepted witness names the body stored at `defId`. -/
theorem HasAcceptedWitness.bodyAt_eq {Prog Body Sig Query Ret Mem : Type}
    {M : ExecutionModel Prog Body Sig Query Ret Mem} {prog : Prog}
    {defId : Nat} {body : Body} {c : FnContract Query Ret Mem}
    {isAccepted : Ret → Bool}
    (h : HasAcceptedWitness M prog defId body c isAccepted) :
    M.bodyAt prog defId = some body :=
  h.1

/-- Lift an output specification to `Option`: `none` is always allowed. -/
@[expose] def optionLift {X Y : Type} (Spec : X → Y → Prop) (x : X) :
    Option Y → Prop
  | none => True
  | some y => Spec x y

/-- `optionLift Spec` satisfies `PostconditionDichotomy` whenever `Spec`
rejects some output, even if `Spec` accepts nothing, because `none` is always
allowed. That dichotomy therefore says nothing about accepted outputs, and
the always-`none` implementation meets `optionLift Spec` regardless. -/
theorem optionLift_dichotomy_while_none_passes {X Y : Type}
    {Pre : X → Prop} {Spec : X → Y → Prop} (x : X) (hPre : Pre x)
    (y_bad : Y) (hBad : ¬ Spec x y_bad) :
    Anneal.Core.PostconditionDichotomy Pre (optionLift Spec) ∧
      ∀ x', optionLift Spec x' none :=
  ⟨⟨x, hPre, ⟨none, True.intro⟩, ⟨some y_bad, hBad⟩⟩, fun _ => True.intro⟩

/-- Dichotomy of `optionLift Spec` inside the accepted fibre (outputs with
the same `Option.isSome`) is exactly the dichotomy of `Spec`: the rejected
output must be `some`, so the accepted one must be too. This constrains the
specification, not the implementation; `HasAcceptedWitness` constrains the
implementation. -/
theorem optionLift_acceptedDichotomy_iff {X Y : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} :
    Anneal.Core.DichotomyModuloObservation (fun _ o => Option.isSome o) Pre
        (optionLift Spec) ↔
      Anneal.Core.PostconditionDichotomy Pre Spec := by
  refine ⟨fun ⟨x, hPre, oOk, oBad, hObs, hOk, hBad⟩ => ?_,
    fun ⟨x, hPre, ⟨yOk, hOk⟩, ⟨yBad, hBad⟩⟩ =>
      ⟨x, hPre, some yOk, some yBad, rfl, hOk, hBad⟩⟩
  cases oBad with
  | none => exact absurd True.intro hBad
  | some yBad =>
    cases oOk with
    | none => cases hObs
    | some yOk => exact ⟨x, hPre, ⟨yOk, hOk⟩, ⟨yBad, hBad⟩⟩

/-- Introduction form of `optionLift_acceptedDichotomy_iff`. -/
theorem optionLift_acceptedDichotomy {X Y : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (x : X) (hPre : Pre x) (y_ok y_bad : Y)
    (hOk : Spec x y_ok) (hBad : ¬ Spec x y_bad) :
    Anneal.Core.DichotomyModuloObservation (fun _ o => Option.isSome o) Pre
      (optionLift Spec) :=
  optionLift_acceptedDichotomy_iff.2 ⟨x, hPre, ⟨y_ok, hOk⟩, ⟨y_bad, hBad⟩⟩

end Anneal.Hybrid

end
