/-
Copyright 2026 Google LLC / Contributors (Public Reference Mechanization)
Standalone Lean 4.34.1 mechanization of Hybrid Verified Software hazards:
1. Option Some/None decision channels and total fallback closure
2. Relational non-determinism witness steganography and uniqueness closure
3. Execution timing channels and fixed-budget/secret-blind padding closure
4. Derived-field trust violations (I2) and TOCTOU check-vs-use snapshot sealing
Zero Mathlib dependencies; uses core Lean Init only.
-/

namespace HybridHazards

/-! ## 1. `Some`/`None` Decision Channels and Deterministic Fallback Closure -/

section OptionChannel

def CheckerSound {L Y W : Type} (R : L → Y → Prop) (V : L → Y → W → Bool) : Prop :=
  ∀ p y w, V p y w = true → R p y

def optionWrap {L H Y W : Type}
    (V : L → Y → W → Bool) (P : L → H → Option (Y × W)) (p : L) (s : H) : Option Y :=
  match P p s with
  | none => none
  | some (y, w) => if V p y w then some y else none

def OptionContract {L H Y : Type} (R : L → Y → Prop) (f : L → H → Option Y) : Prop :=
  ∀ p s, match f p s with | none => True | some y => R p y

def NonInterferent {L H O : Type} (f : L → H → O) : Prop :=
  ∀ p s₁ s₂, f p s₁ = f p s₂

/-- **Theorem 1A (`Some`/`None` Secret Channel):** Even when `V` is 100%
sound for a secret-independent specification `R` and the producer satisfies
`OptionContract R`, an untrusted producer can exfiltrate the secret `s : Bool`
at 1 bit per invocation solely via returning `some` vs `none`. -/
theorem option_decision_channel_leaks_despite_sound_checker :
    let R : Nat → Nat → Prop := fun p y => y = p + 1
    let V : Nat → Nat → Nat → Bool := fun p y w => Nat.beq y (p + 1) && Nat.beq w 0
    let P_leak : Nat → Bool → Option (Nat × Nat) :=
      fun p s => if s then none else some (p + 1, 0)
    CheckerSound R V ∧
    OptionContract R (optionWrap V P_leak) ∧
    ¬ NonInterferent (optionWrap V P_leak) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p y w h
    simp at h
    exact h.1
  · intro p s
    dsimp [optionWrap]
    cases s with
    | true => trivial
    | false =>
      dsimp
      simp [Nat.beq_refl]
  · intro hNI
    have hEq := hNI 0 false true
    dsimp [optionWrap] at hEq
    cases hEq

/-- **Theorem 1B (Total Deterministic Fallback Closure):** Replacing `optionWrap`
with a total fallback `F : L → Y` against a deterministic secret-independent
spec `R` (`∀ p y₁ y₂, R p y₁ → R p y₂ → y₁ = y₂`) guarantees output
noninterference (`NonInterferent`) for *any* untrusted producer `P`. -/
def fallbackWrap {L H Y W : Type}
    (V : L → Y → W → Bool) (P : L → H → Option (Y × W)) (F : L → Y)
    (p : L) (s : H) : Y :=
  match P p s with
  | none => F p
  | some (y, w) => if V p y w then y else F p

theorem fallback_deterministic_closes_option_channel
    {L H Y W : Type} {R : L → Y → Prop}
    {V : L → Y → W → Bool} {F : L → Y}
    (hDet : ∀ p y₁ y₂, R p y₁ → R p y₂ → y₁ = y₂)
    (hV : CheckerSound R V)
    (hF : ∀ p, R p (F p))
    (P : L → H → Option (Y × W)) :
    NonInterferent (fallbackWrap V P F) := by
  intro p s₁ s₂
  have soundRun : ∀ s, R p (fallbackWrap V P F p s) := by
    intro s
    dsimp [fallbackWrap]
    cases hP : P p s with
    | none => exact hF p
    | some yw =>
      dsimp
      cases hChk : V p yw.1 yw.2 with
      | false =>
        dsimp
        exact hF p
      | true =>
        dsimp
        exact hV p yw.1 yw.2 hChk
  exact hDet p _ _ (soundRun s₁) (soundRun s₂)

end OptionChannel

/-! ## 2. Relational Non-Determinism and Witness Steganography -/

section WitnessSteganography

/-- **Theorem 2A (Witness Steganography Under Relational Specs):** When a spec
`RelSpec p y` admits at least two valid outputs (`y₀ ≠ y₁`) for the same
public input `p`, a total verified checker (`100%` sound, `0` fallbacks,
`100%` availability) cannot stop an untrusted producer from exfiltrating the
secret `s : Bool` through the choice of accepted output `y`. -/
theorem nondet_rel_allows_witness_steganography_despite_total_checker :
    let RelSpec : Nat → Nat → Prop := fun p y => y = p ∨ y = p + 1
    let V : Nat → Nat → Unit → Bool :=
      fun p y _ => Nat.beq y p || Nat.beq y (p + 1)
    let F : Nat → Nat := fun p => p
    let P_steg : Nat → Bool → Option (Nat × Unit) :=
      fun p s => if s then some (p + 1, ()) else some (p, ())
    CheckerSound RelSpec V ∧
    (∀ p s, RelSpec p (fallbackWrap V P_steg F p s)) ∧
    (∀ p s, ∃ y w, P_steg p s = some (y, w) ∧ V p y w = true) ∧
    ¬ NonInterferent (fallbackWrap V P_steg F) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p y _ h
    simp at h
    exact h
  · intro p s
    dsimp [fallbackWrap]
    cases s with
    | false =>
      dsimp
      simp [Nat.beq_refl]
    | true =>
      dsimp
      simp [Nat.beq_refl]
  · intro p s
    cases s with
    | false =>
      refine ⟨p, (), rfl, ?_⟩
      simp [Nat.beq_refl]
    | true =>
      refine ⟨p + 1, (), rfl, ?_⟩
      simp [Nat.beq_refl]
  · intro hNI
    have hEq := hNI 0 false true
    dsimp [fallbackWrap] at hEq
    cases hEq

/-- **Theorem 2B (Unique-Output Spec Closure):** Requiring `RelSpec` to be
functionally deterministic on public inputs closes witness steganography
completely (`fallback_deterministic_closes_option_channel`). -/
theorem unique_spec_blocks_witness_steganography
    {L H Y W : Type} {RelSpec : L → Y → Prop}
    {V : L → Y → W → Bool} {F : L → Y}
    (hUnique : ∀ p y₁ y₂, RelSpec p y₁ → RelSpec p y₂ → y₁ = y₂)
    (hV : CheckerSound RelSpec V)
    (hF : ∀ p, RelSpec p (F p))
    (P : L → H → Option (Y × W)) :
    NonInterferent (fallbackWrap V P F) :=
  fallback_deterministic_closes_option_channel hUnique hV hF P

end WitnessSteganography

/-! ## 3. Execution Timing / Resource Channels and Padded Oblivious Envelopes -/

section TimingChannel

structure TimedOut (Y : Type) where
  val   : Y
  steps : Nat
  deriving DecidableEq, Repr

structure TimedProducer (L H Y W : Type) where
  run    : L → H → Option (Y × W)
  pSteps : L → H → Nat

def runTimedHybrid {L H Y W : Type}
    (V : L → Y → W → Bool)
    (checkSteps : Nat)
    (F : L → Y)
    (fallbackSteps : Nat)
    (P : TimedProducer L H Y W)
    (p : L) (s : H) : TimedOut Y :=
  let tP := P.pSteps p s
  match P.run p s with
  | none => ⟨F p, tP + fallbackSteps⟩
  | some (y, w) =>
    if V p y w then ⟨y, tP + checkSteps⟩
    else ⟨F p, tP + checkSteps + fallbackSteps⟩

/-- **Theorem 3A (Timing Channel Under Deterministic Total Specs):** Even when
`Spec` is strictly deterministic (`y = p + 1`) and every execution produces the
exact identical functional output `y`, an unverified producer running in `1` step
on `s = false` and `100` steps on `s = true` leaks `s` via execution duration. -/
theorem timing_channel_survives_deterministic_total_spec :
    let Spec : Nat → Nat → Prop := fun p y => y = p + 1
    let V : Nat → Nat → Unit → Bool := fun p y _ => Nat.beq y (p + 1)
    let F : Nat → Nat := fun p => p + 1
    let P_timed : TimedProducer Nat Bool Nat Unit :=
      { run := fun p _ => some (p + 1, ())
        pSteps := fun _ s => if s then 100 else 1 }
    CheckerSound Spec V ∧
    (∀ p s, Spec p (runTimedHybrid V 2 F 5 P_timed p s).val) ∧
    (∀ p s₁ s₂,
      (runTimedHybrid V 2 F 5 P_timed p s₁).val =
      (runTimedHybrid V 2 F 5 P_timed p s₂).val) ∧
    ¬ NonInterferent (runTimedHybrid V 2 F 5 P_timed) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p y _ h
    simp at h
    exact h
  · intro p _
    dsimp [runTimedHybrid]
    simp [Nat.beq_refl]
  · intro p _ _
    dsimp [runTimedHybrid]
    simp [Nat.beq_refl]
  · intro hNI
    have hEq := hNI 0 false true
    dsimp [runTimedHybrid] at hEq
    cases hEq

/-- Fixed-budget padded execution envelope: runs producer up to `budget` cycles;
on timeout, or early completion, pads elapsed time to constant `budget` before
checking + deterministic fallback padding (`totalBudget`). -/
def runPaddedHybrid {L H Y W : Type}
    (V : L → Y → W → Bool)
    (budget checkSteps fallbackSteps : Nat)
    (F : L → Y)
    (P : TimedProducer L H Y W)
    (p : L) (s : H) : TimedOut Y :=
  let totalLatency := budget + checkSteps + fallbackSteps
  let raw :=
    match Nat.ble (P.pSteps p s) budget with
    | true =>
      match P.run p s with
      | none => F p
      | some (y, w) => if V p y w then y else F p
    | false =>
      F p
  ⟨raw, totalLatency⟩

/-- **Theorem 3B (Padded Budget + Deterministic Spec Closes Timing + Value):**
When `Spec` is deterministic on `L` and `runPaddedHybrid` pads execution time
to a fixed public budget `budget + checkSteps + fallbackSteps`, both the
functional value AND execution latency satisfy 2-safety noninterference. -/
theorem padded_deterministic_hybrid_noninterferent
    {L H Y W : Type} {Spec : L → Y → Prop}
    {V : L → Y → W → Bool} {F : L → Y}
    (hDet : ∀ p y₁ y₂, Spec p y₁ → Spec p y₂ → y₁ = y₂)
    (hV : CheckerSound Spec V)
    (hF : ∀ p, Spec p (F p))
    (budget checkSteps fallbackSteps : Nat)
    (P : TimedProducer L H Y W) :
    NonInterferent (runPaddedHybrid V budget checkSteps fallbackSteps F P) := by
  intro p s₁ s₂
  have hSpec : ∀ s, Spec p (runPaddedHybrid V budget checkSteps fallbackSteps F P p s).val := by
    intro s
    dsimp [runPaddedHybrid]
    cases hLe : Nat.ble (P.pSteps p s) budget with
    | false => exact hF p
    | true =>
      dsimp
      cases hP : P.run p s with
      | none => exact hF p
      | some yw =>
        dsimp
        cases hChk : V p yw.1 yw.2 with
        | false =>
          dsimp
          exact hF p
        | true =>
          dsimp
          exact hV p yw.1 yw.2 hChk
  have hvEq := hDet p _ _ (hSpec s₁) (hSpec s₂)
  dsimp [runPaddedHybrid] at hvEq ⊢
  rw [hvEq]

end TimingChannel

/-! ## 4. Derived-Field Trust (`I2`) and TOCTOU Snapshot Sealing -/

section DerivedFieldAndToctou

/-- Witness carrying both raw values and a redundant producer-computed field
`claimedSum` (the I2 derived-field hazard). -/
structure CertWithDerived where
  elems      : List Nat
  claimedSum : Nat
  deriving DecidableEq, Repr

def listSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + listSum xs

def trueSpec (bound : Nat) (c : CertWithDerived) : Prop :=
  listSum c.elems ≤ bound

/-- Buggy checker trusting the producer's `claimedSum` without recomputing. -/
def buggyTrustingChecker (bound : Nat) (c : CertWithDerived) : Bool :=
  Nat.ble c.claimedSum bound

/-- Sound checker recomputing `listSum c.elems` directly from scratch. -/
def recomputingChecker (bound : Nat) (c : CertWithDerived) : Bool :=
  Nat.ble (listSum c.elems) bound

/-- **Theorem 4A (Derived-Field Forgery vs. Recomputing Checker):** Trusting a
derived field (`claimedSum = 0` while `elems = [50, 50]`, `bound = 10`) accepts
an invalid certificate; recomputing from primary witness data guarantees `trueSpec`. -/
theorem derived_field_trust_vs_recomputing :
    let forge : CertWithDerived := ⟨[50, 50], 0⟩
    (buggyTrustingChecker 10 forge = true ∧ ¬ trueSpec 10 forge) ∧
    (∀ bound c, recomputingChecker bound c = true → trueSpec bound c) := by
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · intro h
    dsimp [trueSpec, listSum] at h
    have hBle : Nat.ble 100 10 = true := Nat.ble_eq.mpr h
    cases hBle
  · intro bound c h
    dsimp [recomputingChecker] at h
    exact Nat.le_of_ble_eq_true h

/-- TOCTOU model: an unsealed shared-cell flow checks `v0` and then uses `v1`
mutated by a post-check hook, versus snapshot-sealing (`sealChecked`) which
captures `v0` atomically into an immutable `SealedVal` before checking. -/
structure SealedVal (α : Type) where
  val : α
  deriving DecidableEq, Repr

def sealChecked (bound : Nat) (readShared : Unit → Nat) : Option (SealedVal Nat) :=
  let snap := readShared ()
  if Nat.ble snap bound then some ⟨snap⟩ else none

theorem toctou_post_check_mutation_unsound_vs_sealed :
    let checkAt : Nat → Bool := fun v => Nat.ble v 100
    (∃ v0 v1, checkAt v0 = true ∧ ¬ (v1 ≤ 100)) ∧
    (∀ bound readShared sv,
      sealChecked bound readShared = some sv → sv.val ≤ bound) := by
  refine ⟨⟨10, 999, rfl, ?_⟩, ?_⟩
  · intro h
    cases Nat.ble_eq.mpr h
  · intro bound readShared sv hSeal
    dsimp [sealChecked] at hSeal
    cases hBle : Nat.ble (readShared ()) bound with
    | false =>
      rw [hBle] at hSeal
      cases hSeal
    | true =>
      rw [hBle] at hSeal
      dsimp at hSeal
      injection hSeal with hEq
      rw [← hEq]
      exact Nat.le_of_ble_eq_true hBle

end DerivedFieldAndToctou

end HybridHazards

#print axioms HybridHazards.option_decision_channel_leaks_despite_sound_checker
#print axioms HybridHazards.fallback_deterministic_closes_option_channel
#print axioms HybridHazards.nondet_rel_allows_witness_steganography_despite_total_checker
#print axioms HybridHazards.unique_spec_blocks_witness_steganography
#print axioms HybridHazards.timing_channel_survives_deterministic_total_spec
#print axioms HybridHazards.padded_deterministic_hybrid_noninterferent
#print axioms HybridHazards.derived_field_trust_vs_recomputing
#print axioms HybridHazards.toctou_post_check_mutation_unsound_vs_sealed
