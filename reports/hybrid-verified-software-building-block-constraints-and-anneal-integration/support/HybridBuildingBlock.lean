-- Standalone Lean v4.34.1 mechanization of Hybrid Verified Software Building-Block
-- boundaries:
--   1. EffectMask 4-outcome composition & isolation necessity (MirAssumedStub gap)
--   2. Checker completeness asymmetry (assert!(V(fb)) vs direct fb proof) & witness-bomb bounds
--   3. Streaming output-commitment hazard vs atomic/prefix-invariant checking
--   4. Cross-call stateful producer noninterference leak vs stateless reset
--   5. Result<T, E> contracts & availability-monotone ratcheting preservation
--
-- Core Init only (zero external packages, zero sorryAx).

namespace HybridBB

/-! ## 1. EffectMask, 4-Outcome Execution, and Assumed-Stub Isolation -/

structure EffectMask where
  terminates : Bool
  noUnwind   : Bool
  noAbort    : Bool

def EffectMask.totalNormal : EffectMask :=
  { terminates := true, noUnwind := true, noAbort := true }

def EffectMask.partialAnyExit : EffectMask :=
  { terminates := false, noUnwind := false, noAbort := false }

def EffectMask.le (m1 m2 : EffectMask) : Prop :=
  (m1.terminates = true → m2.terminates = true) ∧
  (m1.noUnwind   = true → m2.noUnwind   = true) ∧
  (m1.noAbort    = true → m2.noAbort    = true)

inductive EffectOutcome (S Y : Type) where
  | returned (y : Y) (st : S)
  | unwound  (st : S)
  | aborted  (st : S)
  | diverged

inductive ProducerOutcome (S Y W : Type) where
  | returned (y : Y) (w : W) (st : S)
  | unwound  (st : S)
  | aborted  (st : S)
  | diverged

def SatisfiesEffectContract {S X Y : Type}
    (pre : S → X → Prop) (post : S → X → Y → S → Prop) (mask : EffectMask)
    (f : S → X → EffectOutcome S Y) : Prop :=
  ∀ st x, pre st x →
    match f st x with
    | .returned y st' => post st x y st'
    | .unwound _      => mask.noUnwind = false
    | .aborted _      => mask.noAbort  = false
    | .diverged       => mask.terminates = false

/-- Unisolated wrapper around an unverified producer `P`: if `P` unwinds,
aborts, or diverges, control never reaches `V` or `fb` (`wrapUnisolated`). -/
def wrapUnisolated {S X Y W : Type}
    (V : S → X → Y → W → Bool)
    (P : S → X → ProducerOutcome S Y W)
    (commit : S → X → Y → S)
    (fb : S → X → Y × S)
    (st : S) (x : X) : EffectOutcome S Y :=
  match P st x with
  | .returned y w _stP =>
    if V st x y w then .returned y (commit st x y)
    else
      let res := fb st x
      .returned res.1 res.2
  | .unwound stP => .unwound stP
  | .aborted stP => .aborted stP
  | .diverged    => .diverged

/-- Counterexample 1: Even with a 100%-sound total checker `V` and a 100%-correct
total fallback `fb`, wrapping an unisolated `partialAnyExit` stub fails
`EffectMask.totalNormal` (`noUnwind = true`, `noAbort = true`, `terminates = true`). -/
theorem unisolated_assumed_stub_leaks_effects :
    let V : Unit → Nat → Nat → Unit → Bool := fun _ x y _ => Nat.beq y x
    let fb : Unit → Nat → Nat × Unit := fun _ x => (x, ())
    let P_unwind : Unit → Nat → ProducerOutcome Unit Nat Unit := fun _ _ => .unwound ()
    let P_abort  : Unit → Nat → ProducerOutcome Unit Nat Unit := fun _ _ => .aborted ()
    let P_div    : Unit → Nat → ProducerOutcome Unit Nat Unit := fun _ _ => .diverged
    let post : Unit → Nat → Nat → Unit → Prop := fun _ x y _ => y = x
    (¬ SatisfiesEffectContract (fun _ _ => True) post EffectMask.totalNormal
        (wrapUnisolated V P_unwind (fun _ _ _ => ()) fb)) ∧
    (¬ SatisfiesEffectContract (fun _ _ => True) post EffectMask.totalNormal
        (wrapUnisolated V P_abort (fun _ _ _ => ()) fb)) ∧
    (¬ SatisfiesEffectContract (fun _ _ => True) post EffectMask.totalNormal
        (wrapUnisolated V P_div (fun _ _ _ => ()) fb)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h0 := h () 0 True.intro
    exact Bool.noConfusion h0
  · intro h
    have h0 := h () 0 True.intro
    exact Bool.noConfusion h0
  · intro h
    have h0 := h () 0 True.intro
    exact Bool.noConfusion h0

/-- Contained producer outcome after OS/Wasm/snapshot+catch_unwind+fuel boundary
`Iso`: state is isolated (read-only view), and unwind/abort/diverge are caught
into `.failed`. -/
inductive IsolatedOutcome (Y W : Type) where
  | ok (y : Y) (w : W)
  | failed

def containedVerifyOrFallback {S X Y W : Type}
    (V : S → X → Y → W → Bool)
    (isoP : S → X → IsolatedOutcome Y W)
    (commit : S → X → Y → S)
    (fb : S → X → Y × S)
    (st : S) (x : X) : EffectOutcome S Y :=
  match isoP st x with
  | .ok y w =>
    if V st x y w then .returned y (commit st x y)
    else
      let res := fb st x
      .returned res.1 res.2
  | .failed =>
    let res := fb st x
    .returned res.1 res.2

theorem contained_stub_with_direct_fallback_total_normal
    {S X Y W : Type}
    (pre : S → X → Prop)
    (post : S → X → Y → S → Prop)
    (V : S → X → Y → W → Bool)
    (commit : S → X → Y → S)
    (fb : S → X → Y × S)
    (isoP : S → X → IsolatedOutcome Y W)
    (hV : ∀ st x y w, pre st x → V st x y w = true → post st x y (commit st x y))
    (hFb : ∀ st x, pre st x → post st x (fb st x).1 (fb st x).2) :
    SatisfiesEffectContract pre post EffectMask.totalNormal
      (containedVerifyOrFallback V isoP commit fb) := by
  intro st x hPre
  unfold containedVerifyOrFallback
  cases hIso : isoP st x with
  | failed =>
    exact hFb st x hPre
  | ok y w =>
    dsimp only
    cases hChk : V st x y w with
    | true =>
      simp only [↓reduceIte]
      exact hV st x y w hPre hChk
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact hFb st x hPre

/-! ## 2. Checker Completeness Asymmetry & Witness-Bomb Bounds -/

/-- Variant that runtime-checks the fallback via `V` and aborts if `V` rejects
(e.g. `assert!(V(x, fb(x), w_fb))`). -/
def runtimeCheckedFallback {S X Y W : Type}
    (V : S → X → Y → W → Bool)
    (isoP : S → X → IsolatedOutcome Y W)
    (commit : S → X → Y → S)
    (fbWithW : S → X → Y × W × S)
    (st : S) (x : X) : EffectOutcome S Y :=
  match isoP st x with
  | .ok y w =>
    if V st x y w then .returned y (commit st x y)
    else
      let res := fbWithW st x
      if V st x res.1 res.2.1 then .returned res.1 res.2.2 else .aborted st
  | .failed =>
    let res := fbWithW st x
    if V st x res.1 res.2.1 then .returned res.1 res.2.2 else .aborted st

/-- Counterexample 2: When `V` is sound (`V = true -> R`) but INCOMPLETE on a
valid fallback output (`fb`), `runtimeCheckedFallback` hits `.aborted` and FAILS
`EffectMask.totalNormal` (`noAbort = true`), whereas `containedVerifyOrFallback`
needs ONLY soundness of `V`! -/
theorem runtime_checked_fallback_requires_v_completeness :
    let R : Unit → Nat → Nat → Unit → Prop := fun _ x y _ => x ≤ y
    let incompleteV : Unit → Nat → Nat → Unit → Bool :=
      fun _ x y _ => Nat.beq y (x + 1)
    let fb : Unit → Nat → Nat × Unit × Unit := fun _ x => (x, (), ())
    let isoP : Unit → Nat → IsolatedOutcome Nat Unit := fun _ _ => .failed
    (∀ st x y w, incompleteV st x y w = true → R st x y st) ∧
    (∀ st x, R st x (fb st x).1 st) ∧
    (¬ SatisfiesEffectContract (fun _ _ => True) R EffectMask.totalNormal
        (runtimeCheckedFallback incompleteV isoP (fun _ _ _ => ()) fb)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro _ x y _ hV
    have hEq : y = x + 1 := Nat.eq_of_beq_eq_true hV
    subst hEq
    exact Nat.le_succ x
  · intro _ x
    exact Nat.le_refl x
  · intro hSat
    have h0 := hSat () 0 True.intro
    exact Bool.noConfusion h0

inductive CheckOutcome where
  | decided (ok : Bool)
  | outOfBudget

def runCheckFuel {W : Type} (step : W → Option W) (accept : W → Bool) :
    Nat → W → CheckOutcome
  | 0, _ => .outOfBudget
  | fuel + 1, w =>
    match step w with
    | none => .decided (accept w)
    | some w' => runCheckFuel step accept fuel w'

def sizeCappedCheck {W : Type} (wSize : W → Nat) (maxSize : Nat)
    (step : W → Option W) (accept : W → Bool) (fuel : Nat) (w : W) :
    CheckOutcome :=
  if Nat.ble (wSize w) maxSize then runCheckFuel step accept fuel w
  else .decided false

/-- Counterexample 3 (Witness-Bomb DoS): A sound linear-chain checker without a
witness-size cap exceeds any fixed checker budget `B` when an untrusted producer
emits a witness of length `B + 1`. -/
theorem unbounded_witness_checker_fails_totality (B : Nat) :
    let step : Nat → Option Nat := fun n => match n with | 0 => none | k + 1 => some k
    let accept : Nat → Bool := fun _ => true
    runCheckFuel step accept B (B + 1) = .outOfBudget := by
  induction B with
  | zero => rfl
  | succ k ih =>
    unfold runCheckFuel
    exact ih

/-- Capping witness size in `O(1)` (`wSize w ≤ maxSize`) before traversal
guarantees `CheckOutcome.decided _` whenever `step` strictly decreases `wSize`
and `fuel > maxSize`. -/
theorem prechecked_size_capped_checker_total {W : Type}
    (wSize : W → Nat) (maxSize : Nat)
    (step : W → Option W) (accept : W → Bool)
    (hDec : ∀ w w', step w = some w' → wSize w' < wSize w)
    (w : W) :
    ∃ b, sizeCappedCheck wSize maxSize step accept (maxSize + 1) w = .decided b := by
  unfold sizeCappedCheck
  cases hCap : Nat.ble (wSize w) maxSize with
  | false =>
    exact ⟨false, rfl⟩
  | true =>
    have hLe : wSize w ≤ maxSize := Nat.le_of_ble_eq_true hCap
    have hAux : ∀ m (v : W), wSize v ≤ m →
        ∃ b, runCheckFuel step accept (m + 1) v = .decided b := by
      intro m
      induction m with
      | zero =>
        intro v hv
        unfold runCheckFuel
        cases hSt : step v with
        | none => exact ⟨accept v, rfl⟩
        | some v' =>
          have hLt := hDec v v' hSt
          have hZero : wSize v = 0 := Nat.le_zero.mp hv
          rw [hZero] at hLt
          cases hLt
      | succ k ih =>
        intro v hv
        unfold runCheckFuel
        cases hSt : step v with
        | none => exact ⟨accept v, rfl⟩
        | some v' =>
          have hLt := hDec v v' hSt
          have hLe' : wSize v' ≤ k := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hLt hv)
          exact ih v' hLe'
    exact hAux maxSize w hLe

/-! ## 3. Streaming Output-Commitment Hazard vs. Prefix Invariant -/

/-- If a streaming pipeline forwards chunks `c₀` to an external sink before
running the end-of-stream verifier `V_full`, `c₀` can violate `PrefixSafe [c₀]`
even though `V_full` later rejects `[c₀, c₁]`. -/
theorem streaming_premature_commit_unsound :
    let PrefixSafe : List Nat → Prop := fun cs => ∀ c ∈ cs, c < 10
    let V_full : List Nat → Bool := fun cs => cs.all (fun c => Nat.blt c 10)
    let badStream : List Nat := [99, 0]
    (∀ cs, V_full cs = true → PrefixSafe cs) ∧
    (¬ PrefixSafe [99]) ∧
    (V_full badStream = false) := by
  refine ⟨?_, ?_, rfl⟩
  · intro cs hAll c hMem
    have hAllProp : ∀ x ∈ cs, Nat.blt x 10 = true := List.all_eq_true.mp hAll
    exact Nat.le_of_ble_eq_true (hAllProp c hMem)
  · intro hP
    have h99 : (99 : Nat) < 10 := hP 99 (List.Mem.head _)
    exact absurd h99 (by decide)

/-- Prefix-invariant incremental checker `V_step`: verifying `V_step c = true`
before committing each chunk preserves `PrefixSafe` on *every* emitted prefix,
even if a later chunk fails or aborts mid-stream. -/
def emitCheckedPrefix {C : Type} (V_step : C → Bool) : List C → List C
  | [] => []
  | c :: cs => if V_step c then c :: emitCheckedPrefix V_step cs else []

theorem prefix_checked_streaming_sound {C : Type}
    (ChunkSafe : C → Prop) (V_step : C → Bool)
    (hV : ∀ c, V_step c = true → ChunkSafe c)
    (stream : List C) :
    ∀ c ∈ emitCheckedPrefix V_step stream, ChunkSafe c := by
  induction stream with
  | nil =>
    intro c hMem
    cases hMem
  | cons hd tl ih =>
    intro c hMem
    unfold emitCheckedPrefix at hMem
    cases hChk : V_step hd with
    | false =>
      rw [hChk] at hMem
      cases hMem
    | true =>
      rw [hChk] at hMem
      cases hMem with
      | head => exact hV hd hChk
      | tail _ hTl => exact ih c hTl

/-! ## 4. Cross-Call Stateful Producer Noninterference -/

/-- A producer `P : S_priv → (Bool × Nat) → (Nat × Unit × S_priv)` holds private
state across calls. Even with a 100% sound checker and 100% deterministic
specification on Call 2 (so output value is uniquely forced!), Call 1 (receiving
secret `s`) can poison `S_priv`, causing Call 2 (receiving public `p`) to leak `s`
via step latency! -/
theorem stateful_producer_cross_call_leak_despite_sound_checker :
    let Spec : Nat → Nat → Prop := fun p y => y = p
    let V : Nat → Nat → Unit → Bool := fun p y _ => Nat.beq y p
    let P_call1 : Bool → Nat → (Nat × Nat) := fun s _ => (0, if s then 100 else 1)
    let P_call2 : Nat → Nat → (Nat × Nat) := fun st_priv p => (p, st_priv) -- (out, steps)
    (∀ p y (_ : Unit), V p y () = true → Spec p y) ∧
    (∀ s p, (P_call2 (P_call1 s 0).2 p).1 = p) ∧
    ((P_call2 (P_call1 true 0).2 42).2 ≠ (P_call2 (P_call1 false 0).2 42).2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p y _ h
    exact Nat.eq_of_beq_eq_true h
  · intro s p
    rfl
  · decide

/-- Resetting `S_priv := initState` at every call, bounding latency by fixed
`budget`, and checking against a unique functional spec closes multi-call NI. -/
theorem stateless_reset_plus_unique_budgeted_cross_call_ni
    {Secret Pub Y W S_priv : Type}
    (initPriv : S_priv)
    (Spec : Pub → Y → Prop)
    (hUnique : ∀ p y₁ y₂, Spec p y₁ → Spec p y₂ → y₁ = y₂)
    (V : Pub → Y → W → Bool)
    (hV : ∀ p y w, V p y w = true → Spec p y)
    (fb : Pub → Y)
    (hFb : ∀ p, Spec p (fb p))
    (P : S_priv → (Secret × Pub) → Option (Y × W) × S_priv)
    (budget : Nat) :
    let runCall := fun (s : Secret) (p : Pub) =>
      let res := (P initPriv (s, p)).1
      let y := match res with
        | some (y', w) => if V p y' w then y' else fb p
        | none => fb p
      (y, budget)
    ∀ s₁ s₂ p, runCall s₁ p = runCall s₂ p := by
  intro runCall s₁ s₂ p
  have hSpec : ∀ s, Spec p (runCall s p).1 := by
    intro s
    dsimp only [runCall]
    cases hP : (P initPriv (s, p)).1 with
    | none => exact hFb p
    | some yw =>
      dsimp only
      cases hChk : V p yw.1 yw.2 with
      | true => simp only [↓reduceIte]; exact hV p yw.1 yw.2 hChk
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact hFb p
  have hY : (runCall s₁ p).1 = (runCall s₂ p).1 :=
    hUnique p _ _ (hSpec s₁) (hSpec s₂)
  exact Prod.ext hY rfl

/-! ## 5. `Result<T, E>` Hybrid Wrapper & Availability-Monotone Ratcheting -/

def ResultContract {X Y E : Type}
    (pre : X → Prop) (R : X → Y → Prop) (onErr : X → E → Prop)
    (f : X → Except E Y) : Prop :=
  ∀ x, pre x →
    match f x with
    | .ok y    => R x y
    | .error e => onErr x e

def resultWrap {X Y W E : Type}
    (V : X → Y → W → Bool) (errReject : E)
    (P : X → Except E (Y × W)) (x : X) : Except E Y :=
  match P x with
  | .error e => .error e
  | .ok (y, w) => if V x y w then .ok y else .error errReject

theorem resultWrap_sound {X Y W E : Type}
    (pre : X → Prop) (R : X → Y → Prop)
    (V : X → Y → W → Bool) (errReject : E)
    (P : X → Except E (Y × W))
    (hV : ∀ x y w, V x y w = true → R x y) :
    ResultContract pre R (fun _ _ => True) (resultWrap V errReject P) := by
  intro x _
  unfold resultWrap
  cases P x with
  | error e => trivial
  | ok yw =>
    dsimp only
    cases hChk : V x yw.1 yw.2 with
    | true => simp only [↓reduceIte]; exact hV x yw.1 yw.2 hChk
    | false => simp only [Bool.false_eq_true, ↓reduceIte]

/-- Availability-monotone refinement between two `Result`-returning components:
`fNew` satisfies `R` whenever it succeeds and never returns `.error` on an input
where `fOld` returned `.ok`. -/
def AvailabilityRefines {X Y E : Type}
    (pre : X → Prop) (R : X → Y → Prop)
    (fOld fNew : X → Except E Y) : Prop :=
  (∀ x, pre x → ∀ y, fNew x = .ok y → R x y) ∧
  (∀ x, pre x → ∀ y, fOld x = .ok y → ∃ y', fNew x = .ok y')

theorem ratchet_result_preserves_outer_safety_and_availability
    {X Y E Z : Type}
    (pre : X → Prop) (R : X → Y → Prop)
    (fOld fNew : X → Except E Y)
    (outer : (X → Except E Y) → X → Except E Z)
    (OuterPost : X → Z → Prop)
    (hOuter : ∀ f, ResultContract pre R (fun _ _ => True) f →
      ∀ x, pre x → match outer f x with | .ok z => OuterPost x z | .error _ => True)
    (hRef : AvailabilityRefines pre R fOld fNew) :
    (∀ x, pre x → match outer fNew x with | .ok z => OuterPost x z | .error _ => True) ∧
    (∀ x, pre x → (∃ y, fOld x = .ok y) → ∃ y', fNew x = .ok y') := by
  refine ⟨?_, ?_⟩
  · apply hOuter
    intro x hPre
    cases hRes : fNew x with
    | error _ => trivial
    | ok y => exact hRef.1 x hPre y hRes
  · intro x hPre hEx
    cases hEx with
    | intro y hOk => exact hRef.2 x hPre y hOk

#print axioms unisolated_assumed_stub_leaks_effects
#print axioms contained_stub_with_direct_fallback_total_normal
#print axioms runtime_checked_fallback_requires_v_completeness
#print axioms unbounded_witness_checker_fails_totality
#print axioms prechecked_size_capped_checker_total
#print axioms streaming_premature_commit_unsound
#print axioms prefix_checked_streaming_sound
#print axioms stateful_producer_cross_call_leak_despite_sound_checker
#print axioms stateless_reset_plus_unique_budgeted_cross_call_ni
#print axioms resultWrap_sound
#print axioms ratchet_result_preserves_outer_safety_and_availability

end HybridBB
