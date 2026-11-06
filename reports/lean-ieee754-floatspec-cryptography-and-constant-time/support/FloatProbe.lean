-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Probe 1: Rust RFC 3514 Dual Float Contract over Anneal's `StepResult`

This standalone Lean `v4.34.1` probe formalizes and verifies the bridge between:
1. Anneal's bit-level scalar storage representation (`#74`), where `f32`/`f64`
   values in registers and memory preserve all $2^{32}$ / $2^{64}$ IEEE-754 bit
   patterns across loads, stores, `transmute`, `to_bits`/`from_bits`, `abs`,
   `neg`, and `copysign`;
2. Rust's RFC 3514 (*Float Semantics*) operational contract for arithmetic
   operations (`+`, `-`, `*`, `/`, `rem`), where non-NaN results are
   deterministic IEEE-754 rounded values while NaN results are **demonic
   nondeterministic choices** (`.choice .demonic` in `StepResult`) over quiet
   NaN bit patterns with arbitrary sign and payload bits; and
3. Single-NaN IEEE-754 formalizations (`fp-lean`'s `PackedFloat.add` via
   `EUnpackedFloat.pack` and `FloatSpec`'s `BinarySingleNaN` / `Bplus`),
   proving that any NaN-payload-oblivious specification verified against a
   single-NaN model transfers soundly to the demonic-NaN machine, whereas
   specifications that depend on arithmetic NaN sign or payload bits are
   provably rejected.
-/

-- ============================================================================
-- Section 0: Embedded Anneal `Trusted` and `Anneal` Core Definitions
-- ============================================================================

namespace Trusted

/-- A reflexive and transitive refinement relation (`b₁ ≤ b₂`). -/
class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- Constructive partiality / undefined-behavior container (`B ∪ {UB}`). -/
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

def Partial.map {B₁ : Type u} {B₂ : Type v} (f : B₁ → B₂) (p : Partial B₁) :
    Partial B₂ where
  defined := p.defined
  val h := f (p.val h)

instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

abbrev Language.Behavior (L : Language) : Type :=
  Trusted.Behavior L.Query L.Out

def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) :
    L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

inductive ChoiceKind where
  | demonic
  | angelic

inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

inductive FailureKind where
  | ub
  | contractViolation

inductive StepResult (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (kind : ChoiceKind) (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)

inductive PrefixOutcome (Val : Type) where
  | running
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)
  | stuck

def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
  | .running => True
  | .terminated _ => True
  | .failed _ => False
  | .stuck => False

structure ExecQuery (State : Type) where
  init : State
  steps : Nat

structure ExecOut (Obs Val : Type) where
  trace : List Obs
  outcome : PrefixOutcome Val

structure SmallStepMachine (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResult State Obs Val → Prop

inductive ReachesPrefix (M : SmallStepMachine Prog State Obs Val) (p : Prog)
    (init : State) : Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefix M p init 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs)
      (out : PrefixOutcome Val) :
      M.step p s (.step obs s') →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s (obs :: tr) out
  | choice (n : Nat) (kind : ChoiceKind) (s s' : State)
      (branches : State → Prop) (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.choice kind branches) →
      branches s' →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s tr out
  | emptyChoice (n : Nat) (kind : ChoiceKind) (s : State)
      (branches : State → Prop) :
      M.step p s (.choice kind branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefix M p init (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      M.step p s (.terminated term) →
      ReachesPrefix M p init (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) (err : FailureKind) :
      M.step p s (.failed err) →
      ReachesPrefix M p init (n + 1) s [] (.failed err)
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, M.step p s r) →
      ReachesPrefix M p init (n + 1) s [] .stuck

def BehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        ∀ tr out,
          ReachesPrefix M p q.init q.steps q.init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome
  }

def SmallStepMachine.toLanguage (M : SmallStepMachine Prog State Obs Val) :
    Language where
  Prog := Prog
  Query := ExecQuery State
  Out := ExecOut Obs Val
  sem := BehaviorOf M

end Trusted

namespace Anneal

open Trusted

def TotalStep (M : SmallStepMachine Prog State Obs Val) : Prop :=
  ∀ (p : Prog) (s : State), ∃ r, M.step p s r

def InhabitedDemonic (M : SmallStepMachine Prog State Obs Val) : Prop :=
  ∀ (p : Prog) (s : State) (kind : ChoiceKind) (branches : State → Prop),
    M.step p s (.choice kind branches) → ∃ s', branches s'

theorem le_wellFormedOn_iff {L : Language} (b : L.Behavior)
    (pre : L.Query → Prop) :
    b ≤ L.WellFormedOn pre ↔ ∀ q, pre q → (b q).defined := by
  constructor
  · intro h q hpre
    exact (h q hpre).1
  · intro h q hpre
    exact ⟨h q hpre, fun _ _ => True.intro⟩

theorem le_wellFormed_iff {L : Language} (b : L.Behavior) :
    b ≤ L.WellFormed ↔ ∀ q, (b q).defined := by
  constructor
  · intro h q
    exact (le_wellFormedOn_iff b (fun _ => True)).mp h q True.intro
  · intro h
    exact (le_wellFormedOn_iff b (fun _ => True)).mpr (fun q _ => h q)

theorem behaviorOf_le_wellFormed_iff
    {M : SmallStepMachine Prog State Obs Val} {p : Prog} :
    BehaviorOf M p ≤ (M.toLanguage).WellFormed ↔
      ∀ init steps tr out,
        M.initState p init →
        ReachesPrefix M p init steps init tr out →
        out.isSafe := by
  constructor
  · intro h init steps tr out hinit hreach
    have hdef := (le_wellFormed_iff (L := M.toLanguage) (BehaviorOf M p)).mp h
      { init := init, steps := steps }
    exact hdef hinit tr out hreach
  · intro h
    refine (le_wellFormed_iff (L := M.toLanguage) (BehaviorOf M p)).mpr ?_
    intro q hinit tr out hreach
    exact h q.init q.steps tr out hinit hreach

theorem behaviorOf_le_specOn
    {M : SmallStepMachine Prog State Obs Val} {p : Prog}
    {pre : ExecQuery State → Prop}
    {Post : ExecQuery State → ExecOut Obs Val → Prop}
    (h : ∀ (q : ExecQuery State) (out : ExecOut Obs Val),
      pre q →
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome →
      out.outcome.isSafe ∧ Post q out) :
    BehaviorOf M p ≤ (M.toLanguage).SpecOn pre Post := by
  intro q hpre
  refine ⟨fun hinit tr oc hreach => (h q ⟨tr, oc⟩ hpre ⟨hinit, hreach⟩).1, ?_⟩
  intro out hval
  exact (h q out hpre hval).2

end Anneal

-- ============================================================================
-- Section 1: Bit-Preserving `binary32` Representation (`#74` Storage Contract)
-- ============================================================================

namespace Anneal.FloatProbe

open Trusted
open Anneal

/-!
## 1. Bit-Preserving `binary32` Representation (`#74` Storage Contract)

Following `fp-lean` (`Fp/PackedFloat/Basic.lean:10-17`) and `FloatSpec`
(`FloatSpec/src/IEEE754/Bits.lean:19-111`), a packed IEEE-754 `binary32`
floating-point value consists of a 1-bit sign, an 8-bit biased exponent, and a
23-bit trailing significand (mantissa). Unlike `FloatSpec`'s `StandardFloat` or
`fp-lean`'s unpacked `EUnpackedFloat`, `PackedFloat32` retains every NaN sign
and payload bit.
-/

structure PackedFloat32 where
  sign : Bool
  ex   : BitVec 8
  sig  : BitVec 23
  deriving DecidableEq, Repr

namespace PackedFloat32

/-- Canonical quiet NaN (`0x7fc00000`): `sign = false`, `ex = 0xff`, and only
the quiet bit (bit 22, the MSB of `sig`) set. This matches `fp-lean`'s
`PackedFloat.getNaN 8 23` (`Fp/Basic.lean:212-216`). -/
def canonicalQuietNaN : PackedFloat32 :=
  { sign := false, ex := 0xff#8, sig := 0x400000#23 }

/-- A distinct quiet NaN with negative sign and non-canonical payload
(`0xffc00001`), permitted as an arithmetic NaN output by Rust RFC 3514. -/
def altNegQuietNaN : PackedFloat32 :=
  { sign := true, ex := 0xff#8, sig := 0x400001#23 }

/-- Positive zero (`+0.0`). -/
def posZero : PackedFloat32 :=
  { sign := false, ex := 0x00#8, sig := 0#23 }

/-- IEEE-754 NaN test: `ex = 0xff` and `sig ≠ 0`. -/
def isNaN (x : PackedFloat32) : Bool :=
  (x.ex == 0xff#8) && (x.sig != 0#23)

/-- IEEE-754-2008 / Rust RFC 3514 quiet NaN test: `ex = 0xff` and the MSB of
`sig` (bit 22) is `1` (which also forces `sig ≠ 0`). -/
def isQuietNaN (x : PackedFloat32) : Bool :=
  (x.ex == 0xff#8) && x.sig.msb

/-- IEEE-754-2008 signaling NaN test: `ex = 0xff`, MSB of `sig` is `0`, and
`sig ≠ 0`. -/
def isSignalingNaN (x : PackedFloat32) : Bool :=
  (x.ex == 0xff#8) && (!x.sig.msb) && (x.sig != 0#23)

/-- IEEE-754 finite number test (`ex ≠ 0xff`, covering ±0, subnormals, and
normals). -/
def isFinite (x : PackedFloat32) : Bool :=
  x.ex != 0xff#8

theorem canonicalQuietNaN_isNaN : canonicalQuietNaN.isNaN = true := rfl

theorem canonicalQuietNaN_isQuietNaN : canonicalQuietNaN.isQuietNaN = true := rfl

theorem altNegQuietNaN_isNaN : altNegQuietNaN.isNaN = true := rfl

theorem altNegQuietNaN_isQuietNaN : altNegQuietNaN.isQuietNaN = true := rfl

theorem altNegQuietNaN_ne_canonicalQuietNaN :
    altNegQuietNaN ≠ canonicalQuietNaN := by
  decide

/-- Every quiet NaN is a NaN (`msb = true` implies `sig ≠ 0`). -/
theorem isNaN_of_isQuietNaN (x : PackedFloat32) (h : x.isQuietNaN = true) :
    x.isNaN = true := by
  unfold isQuietNaN at h
  unfold isNaN
  rcases Bool.and_eq_true_iff.mp h with ⟨hex, hmsb⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hex, ?_⟩
  apply bne_iff_ne.mpr
  intro hzero
  rw [hzero] at hmsb
  contradiction

/-- Equivalence up to NaN payload, matching `fp-lean`'s
`PackedFloat.EquivUptoNaN` (`Fp/Basic.lean:813-814`) and `FloatSpec`'s `B2BSN`
projection (`FloatSpec/src/IEEE754/Binary.lean:1217-1222`). -/
def EquivUptoNaN (x y : PackedFloat32) : Prop :=
  x = y ∨ (x.isNaN = true ∧ y.isNaN = true)

/-- Collapse any NaN to `canonicalQuietNaN`, modeling the single-NaN projection
performed by `fp-lean`'s `x.unpack.pack` and `FloatSpec`'s `B2BSN`. -/
def collapseNaN (x : PackedFloat32) : PackedFloat32 :=
  if x.isNaN then canonicalQuietNaN else x

theorem collapseNaN_equivUptoNaN (x : PackedFloat32) :
    EquivUptoNaN x x.collapseNaN := by
  unfold collapseNaN EquivUptoNaN
  split
  · rename_i hnan
    exact Or.inr ⟨hnan, canonicalQuietNaN_isNaN⟩
  · exact Or.inl rfl

/-!
### Bitwise Operations (`abs`, `neg`, `copysign`)

Per IEEE 754-2008 §5.5.1 and Rust RFC 3514, `f32::abs`, `f32::neg`, and
`f32::copysign` are pure bit-level operations that touch ONLY the sign bit and
preserve the exponent and all 23 significand/payload bits unchanged—even when
the input is a signaling or quiet NaN.
-/

def abs (x : PackedFloat32) : PackedFloat32 :=
  { x with sign := false }

def neg (x : PackedFloat32) : PackedFloat32 :=
  { x with sign := !x.sign }

def copysign (mag sgn : PackedFloat32) : PackedFloat32 :=
  { mag with sign := sgn.sign }

@[simp]
theorem abs_sign (x : PackedFloat32) : (abs x).sign = false := rfl

@[simp]
theorem abs_ex (x : PackedFloat32) : (abs x).ex = x.ex := rfl

@[simp]
theorem abs_sig (x : PackedFloat32) : (abs x).sig = x.sig := rfl

@[simp]
theorem abs_isNaN (x : PackedFloat32) : (abs x).isNaN = x.isNaN := rfl

@[simp]
theorem copysign_ex (mag sgn : PackedFloat32) :
    (copysign mag sgn).ex = mag.ex := rfl

@[simp]
theorem copysign_sig (mag sgn : PackedFloat32) :
    (copysign mag sgn).sig = mag.sig := rfl

/-- Pack a `PackedFloat32` into a 32-bit `BitVec 32` (`sign ++ ex ++ sig`),
matching `fp-lean`'s `PackedFloat.toBits` (`Fp/Basic.lean:845-847`) and Anneal
`#74`'s bit-level scalar representation. -/
def toBits (x : PackedFloat32) : BitVec 32 :=
  (BitVec.ofBool x.sign ++ x.ex ++ x.sig).cast (by decide)

/-- Unpack a 32-bit `BitVec 32` into a `PackedFloat32` (`sign`, `ex`, `sig`),
matching `fp-lean`'s `PackedFloat.ofBits` (`Fp/Basic.lean:837-843`). -/
def ofBits (bits : BitVec 32) : PackedFloat32 :=
  { sign := bits.getMsbD 0
    ex   := bits.extractLsb' 23 8
    sig  := bits.extractLsb' 0 23 }

end PackedFloat32

-- ============================================================================
-- Section 2: Small-Step Float Machine with RFC 3514 Demonic Arithmetic NaNs
-- ============================================================================

/-!
## 2. Small-Step Float Machine with RFC 3514 Demonic Arithmetic NaNs

We model a small-step machine executing a sequence of floating-point
instructions on an accumulator register `acc : PackedFloat32`.
- Bitwise operations (`abs`, `neg`, `copysign`, `loadConst`) execute via
  deterministic `.step` transitions, preserving exact NaN payloads.
- Arithmetic operations (`arith ieeeOp rhs`) inspect the single-NaN IEEE-754
  reference result `ieeeOp st.acc rhs`:
  - If `(ieeeOp st.acc rhs).isNaN = false`, the machine takes a deterministic
    `.step` to `ieeeOp st.acc rhs`.
  - If `(ieeeOp st.acc rhs).isNaN = true`, the machine emits a **demonic
    choice** `.choice .demonic` over all quiet NaN bit patterns
    (`nan.isQuietNaN = true`), modeling Rust RFC 3514's non-deterministic NaN
    sign and payload rule.
-/

inductive FloatInstr where
  | loadConst (val : PackedFloat32)
  | abs
  | neg
  | copysign (sgn : PackedFloat32)
  | arith (ieeeOp : PackedFloat32 → PackedFloat32 → PackedFloat32)
      (rhs : PackedFloat32)

abbrev FloatProg := List FloatInstr

structure FloatState where
  pc  : Nat
  acc : PackedFloat32

def floatStepFn (p : FloatProg) (st : FloatState) :
    StepResult FloatState Unit PackedFloat32 :=
  match p[st.pc]? with
  | none => .terminated (.normal st.acc)
  | some (.loadConst v) =>
      .step () { pc := st.pc + 1, acc := v }
  | some .abs =>
      .step () { pc := st.pc + 1, acc := st.acc.abs }
  | some .neg =>
      .step () { pc := st.pc + 1, acc := st.acc.neg }
  | some (.copysign sgn) =>
      .step () { pc := st.pc + 1, acc := st.acc.copysign sgn }
  | some (.arith ieeeOp rhs) =>
      let res := ieeeOp st.acc rhs
      if res.isNaN then
        .choice .demonic (fun st' =>
          st'.pc = st.pc + 1 ∧ st'.acc.isQuietNaN = true)
      else
        .step () { pc := st.pc + 1, acc := res }

def floatMachine : SmallStepMachine FloatProg FloatState Unit PackedFloat32 where
  initState := fun _ st => st.pc = 0
  step := fun p st r => r = floatStepFn p st

abbrev FloatLang : Language := floatMachine.toLanguage

-- ============================================================================
-- Section 3: Totality, Non-Vacuity, and Universal Well-Formedness
-- ============================================================================

/-!
## 3. Totality, Non-Vacuity, and Universal Well-Formedness

We prove that `floatMachine` satisfies `TotalStep` and `InhabitedDemonic`
(witnessed by `PackedFloat32.canonicalQuietNaN`). By `Anneal.StepResult`, every
program is non-vacuous at every step budget and universally `WellFormed`.
-/

theorem floatMachine_total : TotalStep floatMachine := by
  intro p s
  exact ⟨floatStepFn p s, rfl⟩

theorem floatMachine_inhabitedDemonic : InhabitedDemonic floatMachine := by
  intro p st kind branches hStep
  simp only [floatMachine, floatStepFn] at hStep
  cases hInstr : p[st.pc]? with
  | none => rw [hInstr] at hStep; exact nomatch hStep
  | some instr =>
    rw [hInstr] at hStep
    cases instr with
    | loadConst v => exact nomatch hStep
    | abs => exact nomatch hStep
    | neg => exact nomatch hStep
    | copysign sgn => exact nomatch hStep
    | arith ieeeOp rhs =>
      simp only at hStep
      split at hStep
      · injection hStep with _ hBranches
        subst hBranches
        exact ⟨{ pc := st.pc + 1, acc := PackedFloat32.canonicalQuietNaN },
          rfl, PackedFloat32.canonicalQuietNaN_isQuietNaN⟩
      · exact nomatch hStep

theorem floatMachine_reaches_safe
    (p : FloatProg) (init : FloatState) (steps : Nat)
    (st : FloatState) (tr : List Unit) (out : PrefixOutcome PackedFloat32)
    (hReach : ReachesPrefix floatMachine p init steps st tr out) :
    out.isSafe := by
  induction hReach with
  | zero => exact trivial
  | step _ _ _ _ _ _ _ _ ih => exact ih
  | choice _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | emptyChoice _ kind s branches hStep hEmpty =>
    exfalso
    exact hEmpty (floatMachine_inhabitedDemonic p s kind branches hStep)
  | terminated => exact trivial
  | failed _ s err hStep =>
    simp only [floatMachine, floatStepFn] at hStep
    cases hInstr : p[s.pc]? with
    | none => rw [hInstr] at hStep; exact nomatch hStep
    | some instr =>
      rw [hInstr] at hStep
      cases instr <;> simp only at hStep <;>
        (try split at hStep) <;> exact nomatch hStep
  | noStep _ s hNo =>
    exfalso
    exact hNo (floatMachine_total p s)

theorem floatMachine_wellFormed (p : FloatProg) :
    BehaviorOf floatMachine p ≤ FloatLang.WellFormed := by
  rw [behaviorOf_le_wellFormed_iff]
  intro init steps tr out _ hReach
  exact floatMachine_reaches_safe p init steps init tr out hReach

-- ============================================================================
-- Section 4: Positive Theorem 1 — Bitwise Ops Preserve Exact NaN Payloads
-- ============================================================================

/-!
## 4. Positive Theorem 1: Bitwise Operations Preserve Exact NaN Payloads

We verify that running `[.abs]` on a negative signaling or quiet NaN with custom
payload `0x401234#23` deterministically clears the sign bit while preserving the
exact 23-bit NaN payload `0x401234#23`.
-/

def customNegNaN : PackedFloat32 :=
  { sign := true, ex := 0xff#8, sig := 0x401234#23 }

def customPosNaN : PackedFloat32 :=
  { sign := false, ex := 0xff#8, sig := 0x401234#23 }

def absProg : FloatProg := [.abs]

theorem absProg_preserves_exact_nan_payload :
    BehaviorOf floatMachine absProg ≤
      FloatLang.SpecOn
        (fun q => q.init = { pc := 0, acc := customNegNaN } ∧ q.steps = 2)
        (fun _ out => out.outcome = .terminated (.normal customPosNaN)) := by
  apply behaviorOf_le_specOn
  rintro ⟨init, steps⟩ ⟨tr, oc⟩ ⟨hInitEq, hStepsEq⟩ ⟨hInit, hReach⟩
  dsimp at hInitEq hStepsEq hInit hReach
  subst hInitEq hStepsEq
  have hSafe : oc.isSafe := floatMachine_reaches_safe absProg _ 2 _ tr oc hReach
  refine ⟨hSafe, ?_⟩
  cases hReach with
  | emptyChoice => exact False.elim hSafe
  | failed => exact False.elim hSafe
  | noStep => exact False.elim hSafe
  | choice =>
    rename_i hStep1 _
    exact nomatch hStep1
  | terminated =>
    rename_i hStep1
    exact nomatch hStep1
  | step =>
    rename_i st1 obs1 tr1 hStep1 hRest1
    simp only [floatMachine, floatStepFn, absProg, List.getElem?_cons_zero]
      at hStep1
    injection hStep1 with _ hSt1
    subst hSt1
    cases hRest1 with
    | emptyChoice => exact False.elim hSafe
    | failed => exact False.elim hSafe
    | noStep => exact False.elim hSafe
    | step =>
      rename_i hStep2 _
      exact nomatch hStep2
    | choice =>
      rename_i hStep2 _
      exact nomatch hStep2
    | terminated =>
      rename_i term hStep2
      simp only [floatMachine, floatStepFn, absProg] at hStep2
      injection hStep2 with hTerm
      subst hTerm
      rfl

-- ============================================================================
-- Section 5: Positive Theorem 2 — Bridge from Single-NaN Models
-- ============================================================================

/-!
## 5. Positive Theorem 2: Bridge from Single-NaN Models (`fp-lean`/`FloatSpec`)

Any predicate `P : PackedFloat32 → Prop` that is *NaN-payload-oblivious*—meaning
it does not distinguish between two NaN bit patterns (e.g., `isNaN`, `isFinite`,
or `FloatSpec`'s real-valued error bound `x.isFinite → |B2R x - exact| ≤ err`)—
transfers soundly from a deterministic single-NaN IEEE-754 operation `ieeeOp`
to Anneal's demonic-NaN machine.
-/

def PayloadOblivious (P : PackedFloat32 → Prop) : Prop :=
  ∀ x y : PackedFloat32, x.isNaN = true → y.isNaN = true → (P x ↔ P y)

theorem payloadOblivious_isNaN :
    PayloadOblivious (fun x => x.isNaN = true) := by
  intro x y hx hy
  exact ⟨fun _ => hy, fun _ => hx⟩

theorem payloadOblivious_isFinite_bound (specOnFinite : PackedFloat32 → Prop) :
    PayloadOblivious (fun x => x.isFinite = true → specOnFinite x) := by
  intro x y hx hy
  unfold PackedFloat32.isNaN at hx hy
  rcases Bool.and_eq_true_iff.mp hx with ⟨hex_x, _⟩
  rcases Bool.and_eq_true_iff.mp hy with ⟨hex_y, _⟩
  have hfin_x : x.isFinite = false := by
    unfold PackedFloat32.isFinite
    simpa using hex_x
  have hfin_y : y.isFinite = false := by
    unfold PackedFloat32.isFinite
    simpa using hex_y
  simp [hfin_x, hfin_y]

def arithProg (ieeeOp : PackedFloat32 → PackedFloat32 → PackedFloat32)
    (rhs : PackedFloat32) : FloatProg :=
  [.arith ieeeOp rhs]

/-- **Main Bridge Theorem:** If a deterministic single-NaN model `ieeeOp a b`
satisfies a payload-oblivious property `P (ieeeOp a b)`, then the RFC 3514
demonic-NaN float machine executing `arithProg ieeeOp b` from accumulator `a`
satisfies `FloatLang.SpecOn` with postcondition `P val` on every demonic
branch. -/
theorem singleNaN_spec_sound_for_rfc3514
    (ieeeOp : PackedFloat32 → PackedFloat32 → PackedFloat32)
    (a b : PackedFloat32)
    (P : PackedFloat32 → Prop)
    (hObliv : PayloadOblivious P)
    (hModel : P (ieeeOp a b)) :
    BehaviorOf floatMachine (arithProg ieeeOp b) ≤
      FloatLang.SpecOn
        (fun q => q.init = { pc := 0, acc := a } ∧ q.steps = 2)
        (fun _ out => ∃ v, out.outcome = .terminated (.normal v) ∧ P v) := by
  apply behaviorOf_le_specOn
  rintro ⟨init, steps⟩ ⟨tr, oc⟩ ⟨hInitEq, hStepsEq⟩ ⟨hInit, hReach⟩
  dsimp at hInitEq hStepsEq hInit hReach
  subst hInitEq hStepsEq
  have hSafe : oc.isSafe :=
    floatMachine_reaches_safe (arithProg ieeeOp b) _ 2 _ tr oc hReach
  refine ⟨hSafe, ?_⟩
  cases hReach with
  | emptyChoice => exact False.elim hSafe
  | failed => exact False.elim hSafe
  | noStep => exact False.elim hSafe
  | terminated =>
    rename_i hStep1
    simp only [floatMachine, floatStepFn, arithProg, List.getElem?_cons_zero]
      at hStep1
    split at hStep1 <;> exact nomatch hStep1
  | step =>
    rename_i st1 obs1 tr1 hStep1 hRest1
    simp only [floatMachine, floatStepFn, arithProg, List.getElem?_cons_zero]
      at hStep1
    split at hStep1
    · exact nomatch hStep1
    · injection hStep1 with _ hSt1
      subst hSt1
      cases hRest1 with
      | emptyChoice => exact False.elim hSafe
      | failed => exact False.elim hSafe
      | noStep => exact False.elim hSafe
      | step =>
        rename_i hStep2 _
        exact nomatch hStep2
      | choice =>
        rename_i hStep2 _
        exact nomatch hStep2
      | terminated =>
        rename_i term hStep2
        simp only [floatMachine, floatStepFn, arithProg] at hStep2
        injection hStep2 with hTerm
        subst hTerm
        exact ⟨ieeeOp a b, rfl, hModel⟩
  | choice =>
    rename_i kind st1 branches hInS hChoice1 hRest1
    simp only [floatMachine, floatStepFn, arithProg, List.getElem?_cons_zero]
      at hChoice1
    split at hChoice1
    · rename_i hIsNaN
      injection hChoice1 with _ hBranches
      subst hBranches
      rcases hInS with ⟨hPc, hQuiet⟩
      cases hRest1 with
      | emptyChoice => exact False.elim hSafe
      | failed => exact False.elim hSafe
      | noStep => exact False.elim hSafe
      | step =>
        rename_i hStep2 _
        simp only [floatMachine, floatStepFn, arithProg, hPc] at hStep2
        exact nomatch hStep2
      | choice =>
        rename_i hStep2 _
        simp only [floatMachine, floatStepFn, arithProg, hPc] at hStep2
        exact nomatch hStep2
      | terminated =>
        rename_i term hStep2
        simp only [floatMachine, floatStepFn, arithProg, hPc] at hStep2
        injection hStep2 with hTerm
        subst hTerm
        have hStNaN : st1.acc.isNaN = true :=
          PackedFloat32.isNaN_of_isQuietNaN st1.acc hQuiet
        exact ⟨st1.acc, rfl, (hObliv (ieeeOp a b) st1.acc hIsNaN hStNaN).mp hModel⟩
    · exact nomatch hChoice1

-- ============================================================================
-- Section 6: Negative Canary (`E-EVAL-02`) — Canonical NaN Spec Rejected
-- ============================================================================

/-!
## 6. Negative Canary (`E-EVAL-02`): Arithmetic NaN Payload Spec Rejected

Unlike `absProg_preserves_exact_nan_payload` (Section 4), a specification that
asserts the output of an arithmetic operation `arithProg ieeeOp b` equals
`canonicalQuietNaN` (or has `sign = false`) when `(ieeeOp a b).isNaN = true` is
**provably false** under Rust RFC 3514's demonic NaN semantics, because the
adversary can pick `altNegQuietNaN` (`0xffc00001`).
-/

theorem rfc3514_rejects_canonical_nan_spec
    (ieeeOp : PackedFloat32 → PackedFloat32 → PackedFloat32)
    (a b : PackedFloat32)
    (hNaN : (ieeeOp a b).isNaN = true) :
    ¬ (BehaviorOf floatMachine (arithProg ieeeOp b) ≤
        FloatLang.SpecOn
          (fun q => q.init = { pc := 0, acc := a } ∧ q.steps = 2)
          (fun _ out =>
            out.outcome =
              .terminated (.normal PackedFloat32.canonicalQuietNaN))) := by
  intro hLe
  let q : ExecQuery FloatState := { init := { pc := 0, acc := a }, steps := 2 }
  let badState : FloatState := { pc := 1, acc := PackedFloat32.altNegQuietNaN }
  let badOut : ExecOut Unit PackedFloat32 :=
    { trace := [], outcome := .terminated (.normal PackedFloat32.altNegQuietNaN) }
  have hChoice1 : floatMachine.step (arithProg ieeeOp b) q.init
      (.choice .demonic (fun st' => st'.pc = 1 ∧ st'.acc.isQuietNaN = true)) := by
    simp [floatMachine, floatStepFn, arithProg, q, hNaN]
  have hInS : badState.pc = 1 ∧ badState.acc.isQuietNaN = true :=
    ⟨rfl, PackedFloat32.altNegQuietNaN_isQuietNaN⟩
  have hTerm2 : floatMachine.step (arithProg ieeeOp b) badState
      (.terminated (.normal PackedFloat32.altNegQuietNaN)) := by
    simp [floatMachine, floatStepFn, arithProg, badState]
  have hReach1 : ReachesPrefix floatMachine (arithProg ieeeOp b) q.init 1 badState
      [] (.terminated (.normal PackedFloat32.altNegQuietNaN)) :=
    ReachesPrefix.terminated 0 badState (.normal PackedFloat32.altNegQuietNaN)
      hTerm2
  have hReach2 : ReachesPrefix floatMachine (arithProg ieeeOp b) q.init 2 q.init
      badOut.trace badOut.outcome :=
    ReachesPrefix.choice 1 .demonic q.init badState
      (fun st' => st'.pc = 1 ∧ st'.acc.isQuietNaN = true)
      [] (.terminated (.normal PackedFloat32.altNegQuietNaN))
      hChoice1 hInS hReach1
  have hInit : floatMachine.initState (arithProg ieeeOp b) q.init := rfl
  have hQ := hLe q ⟨rfl, rfl⟩
  have hPost :
      badOut.outcome = .terminated (.normal PackedFloat32.canonicalQuietNaN) :=
    hQ.2 badOut ⟨hInit, hReach2⟩
  change
    PrefixOutcome.terminated (TerminationKind.normal PackedFloat32.altNegQuietNaN) =
      PrefixOutcome.terminated
        (TerminationKind.normal PackedFloat32.canonicalQuietNaN) at hPost
  injection hPost with hTermEq
  injection hTermEq with hValEq
  exact PackedFloat32.altNegQuietNaN_ne_canonicalQuietNaN hValEq

end Anneal.FloatProbe

#print axioms Anneal.FloatProbe.absProg_preserves_exact_nan_payload
#print axioms Anneal.FloatProbe.singleNaN_spec_sound_for_rfc3514
#print axioms Anneal.FloatProbe.rfc3514_rejects_canonical_nan_spec
