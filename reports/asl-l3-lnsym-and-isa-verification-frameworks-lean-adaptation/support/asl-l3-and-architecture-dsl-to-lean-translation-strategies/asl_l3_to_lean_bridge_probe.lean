/-
  ASL, L3, and Architecture DSL-to-Lean 4 Translation Strategies — Mechanized Bridge Probe
  Target toolchain: Lean 4.34.1 (`leanprover/lean4:v4.34.1`)
  Standalone probe (zero external imports beyond core `Init`) checked with:
    `lean -j1 -M768 support/asl_l3_to_lean_bridge_probe.lean`

  This file mechanizes:
  1. Verbatim copies of Anneal's core semantic types (`Preorder`, `Partial`, `Language`,
     `Compiles`, `Abstracts`, `ChoiceKind`, `TerminationKind`, `FailureKind`, `StepResult`,
     `PrefixOutcome`, `ExecQuery`, `ExecOut`, `SmallStepMachine`, `ReachesPrefix`,
     `BehaviorOf`) and `BridgeTransition`.
  2. Section A — ASL Getter/Setter Reference Lenses (`X`, `V`, `Elem`) & `CONSTRAINED UNPREDICTABLE`
     vs `UNDEFINED` mapped to Anneal's `StepResult`:
     - Formalizes lawful indexed lenses and contrasts `asl-interpreter`'s call-by-value bug on
       `Formal_InOut` (`&vector`) setter parameters (`libASL/eval.ml:595-601, 972-981`) against
       `asl_to_sail`'s pure functional return-value lowering (`lib/translate_asl.ml:1762-1784,
       3082-3117`) and `herdtools7/asllib`'s `desugar_setter` read-modify-write temporary
       lowering (`asllib/desugar.ml:126-162`).
     - Formalizes ASL's `UNDEFINED` / `UNPREDICTABLE` (`StepResult.failed .ub`) vs
       `ConstrainUnpredictable` (`StepResult.choice ChoiceKind.demonic`) and proves:
       (i) whenever `Constraint_UNDEF` or `Constraint_UNPREDICTABLE` is permitted in the
           `ConstrainUnpredictable` outcome list (as in L3's `v8-iset.spec:1178-1196` where
           `case 2 => Unallocated`), `(BehaviorOf M p).defined ⟨s, 1⟩` collapses to `False`;
       (ii) when restricted to non-faulting architectural outcomes (`Constraint_WBSUPPRESS`,
           `Constraint_NOP`, `Constraint_UNKNOWN`), `(BehaviorOf M p).defined ⟨s, 1⟩` holds
           and demonic refinement requires the postcondition across all permitted outcomes.
  3. Section B — L3-to-Lean 4 Translation Prototype & `SmallStepMachine` / `BridgeTransition`:
     - Implements an AArch64 L3 ISA fragment modeled on `coruus/L3` (`L3/Matches.sml`,
       `L3/Export.sml`, `isa-models/arm-v8/v8-base.spec`, `v8-iset.spec`) with fixed-width
       `BitVec` bit-slice decode (`decodeA64`), instruction encoder (`encodeA64`), and a
       mechanized roundtrip theorem (`decodeA64_encodeA64_roundtrip`).
     - Implements L3's monadified state-exception record (`L3State` with `exception : L3Exception`
       field and pure `L3State → α × L3State` transitions) embedded into Anneal's
       `SmallStepMachine` and `BridgeTransition`, proving `TotalStep`, `InhabitedDemonic`,
       concrete 4-instruction AArch64 program execution by kernel `rfl`, and `BehaviorOf`
       refinement with zero `sorryAx` and zero custom axioms.
-/

namespace AnnealAslL3BridgeProbe

/-! ============================================================================
    Section 1: Verbatim Core Types from Anneal's Trusted Base & Theory Layer
    (`trusted/lean/Trusted/Refinement.lean` and `trusted/lean/Trusted/StepResult.lean`)
    ============================================================================ -/

class Preorder (α : Type u) extends LE α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c

structure Partial (I : Type u) (O : Type v) where
  defined : I → Prop
  val : (i : I) → defined i → O

instance [Preorder O] : Preorder (Partial I O) where
  le f g := ∀ i (h : g.defined i), f.defined i ∧ ∀ (hf : f.defined i), f.val i hf ≤ g.val i h
  le_refl _ _ h := ⟨h, fun _ => Preorder.le_refl _⟩
  le_trans _ _ _ hab hbc i hc :=
    let ⟨hb, hbc_val⟩ := hbc i hc
    let ⟨ha, hab_val⟩ := hab i hb
    ⟨ha, fun hf => Preorder.le_trans _ _ _ (hab_val hf) (hbc_val hb)⟩

structure Language (I : Type u) (O : Type v) [Preorder O] where
  Prog : Type w
  eval : Prog → Partial I O

def Compiles {I O : Type _} [Preorder O] (L₁ L₂ : Language I O)
    (compile : L₁.Prog → Option L₂.Prog) : Prop :=
  ∀ p₁ p₂, compile p₁ = some p₂ → L₂.eval p₂ ≤ L₁.eval p₁

def Abstracts {I O : Type _} [Preorder O] (L : Language I O) (Spec : Type _)
    (embed : Spec → Partial I O) (verify : L.Prog → Spec → Prop) : Prop :=
  ∀ p s, verify p s → L.eval p ≤ embed s

inductive ChoiceKind where
  | demonic
  | angelic
  deriving DecidableEq, Repr

inductive TerminationKind where
  | returned
  | halted
  deriving DecidableEq, Repr

inductive FailureKind where
  | ub
  | error
  deriving DecidableEq, Repr

inductive StepResult (State : Type u) where
  | next (s : State)
  | terminated (k : TerminationKind) (s : State)
  | failed (k : FailureKind)
  | choice (k : ChoiceKind) (branches : List (StepResult State))
  deriving Repr

inductive PrefixOutcome (State : Type u) where
  | unfinished (s : State)
  | terminated (k : TerminationKind) (s : State)
  | failed (k : FailureKind)
  deriving Repr

structure ExecQuery (State : Type u) where
  init : State
  steps : Nat

structure ExecOut (State : Type u) where
  outcomes : PrefixOutcome State → Prop

instance : Preorder (ExecOut State) where
  le a b := ∀ o, a.outcomes o → b.outcomes o
  le_refl _ _ h := h
  le_trans _ _ _ hab hbc o ha := hbc o (hab o ha)

structure SmallStepMachine (Prog : Type w) (State : Type u) where
  step : Prog → State → StepResult State

mutual
inductive ReachesPrefix {Prog : Type w} {State : Type u}
    (M : SmallStepMachine Prog State) (p : Prog) :
    Nat → State → PrefixOutcome State → Prop where
  | zero (s : State) :
      ReachesPrefix M p 0 s (.unfinished s)
  | step_from (n : Nat) (s : State) (o : PrefixOutcome State) :
      ReachesFromResult M p n (M.step p s) o →
      ReachesPrefix M p (n + 1) s o

inductive ReachesFromResult {Prog : Type w} {State : Type u}
    (M : SmallStepMachine Prog State) (p : Prog) :
    Nat → StepResult State → PrefixOutcome State → Prop where
  | next (n : Nat) (s' : State) (o : PrefixOutcome State) :
      ReachesPrefix M p n s' o →
      ReachesFromResult M p n (.next s') o
  | terminated (n : Nat) (k : TerminationKind) (s' : State) :
      ReachesFromResult M p n (.terminated k s') (.terminated k s')
  | failed (n : Nat) (k : FailureKind) :
      ReachesFromResult M p n (.failed k) (.failed k)
  | demonic (n : Nat) (branches : List (StepResult State)) (b : StepResult State)
      (o : PrefixOutcome State) :
      b ∈ branches →
      ReachesFromResult M p n b o →
      ReachesFromResult M p n (.choice .demonic branches) o
  | angelic (n : Nat) (branches : List (StepResult State)) (o : PrefixOutcome State) :
      branches ≠ [] →
      (∀ b ∈ branches, ReachesFromResult M p n b o) →
      ReachesFromResult M p n (.choice .angelic branches) o
end

def BehaviorOf {Prog : Type w} {State : Type u}
    (M : SmallStepMachine Prog State) (p : Prog) :
    Partial (ExecQuery State) (ExecOut State) where
  defined q := ¬ ReachesPrefix M p q.steps q.init (.failed .ub)
  val q _ := ⟨fun o => ReachesPrefix M p q.steps q.init o⟩

/-- Well-formedness predicates and `BridgeTransition` from Anneal's theory layer. -/
inductive ResultProduces {Prog : Type w} {State : Type u}
    (M : SmallStepMachine Prog State) (p : Prog) (n : Nat) :
    StepResult State → Prop where
  | next (s' : State) (o : PrefixOutcome State) :
      ReachesPrefix M p n s' o → ResultProduces M p n (.next s')
  | terminated (k : TerminationKind) (s' : State) :
      ResultProduces M p n (.terminated k s')
  | failed (k : FailureKind) :
      ResultProduces M p n (.failed k)
  | demonic (branches : List (StepResult State)) (b : StepResult State) :
      b ∈ branches → ResultProduces M p n b →
      ResultProduces M p n (.choice .demonic branches)
  | angelic (branches : List (StepResult State)) (o : PrefixOutcome State) :
      branches ≠ [] →
      (∀ b ∈ branches, ReachesFromResult M p n b o) →
      ResultProduces M p n (.choice .angelic branches)

def TotalStep {Prog : Type w} {State : Type u}
    (M : SmallStepMachine Prog State) : Prop :=
  ∀ p n s, ResultProduces M p n (M.step p s)

inductive NoEmptyDemonic : StepResult State → Prop where
  | next (s : State) : NoEmptyDemonic (.next s)
  | terminated (k : TerminationKind) (s : State) : NoEmptyDemonic (.terminated k s)
  | failed (k : FailureKind) : NoEmptyDemonic (.failed k)
  | demonic (branches : List (StepResult State)) :
      branches ≠ [] →
      (∀ b ∈ branches, NoEmptyDemonic b) →
      NoEmptyDemonic (.choice .demonic branches)
  | angelic (branches : List (StepResult State)) :
      (∀ b ∈ branches, NoEmptyDemonic b) →
      NoEmptyDemonic (.choice .angelic branches)

def InhabitedDemonic {Prog : Type w} {State : Type u}
    (M : SmallStepMachine Prog State) : Prop :=
  ∀ p s, NoEmptyDemonic (M.step p s)

structure BridgeTransition (Prog : Type w) (State : Type u) where
  machine : SmallStepMachine Prog State
  total_step : TotalStep machine
  inhabited_demonic : InhabitedDemonic machine


/-! ============================================================================
    Section 2: Mechanization (a) — ASL Getter/Setter Reference Lenses &
    `CONSTRAINED UNPREDICTABLE` vs `UNDEFINED` in Anneal's `StepResult`
    ============================================================================ -/

/-- Architectural state for the ASL AArch64 lens and unpredictability study. -/
structure AslState where
  gpr  : Fin 31 → BitVec 64
  sp   : BitVec 64
  vreg : Fin 32 → BitVec 128
  mem  : BitVec 64 → BitVec 8

/-- An indexed lens family modeling ASL's `Decl_ArrayGetterDefn` and `Decl_ArraySetterDefn`
    accessor pairs (`asllib/desugar.ml:212-248` `accessor_pair`). -/
structure AslIndexedLens (S : Type) (ι : Type) (α : Type) where
  get : S → ι → α
  set : S → ι → α → S

/-- Lawful indexed lens satisfying Read-After-Write (same index & other index framing). -/
structure LawfulIndexedLens {S ι α : Type} (L : AslIndexedLens S ι α) : Prop where
  get_set_same  : ∀ (s : S) (i : ι) (v : α), L.get (L.set s i v) i = v
  get_set_other : ∀ (s : S) (i j : ι) (v : α), i ≠ j → L.get (L.set s i v) j = L.get s j

/-- ASL `X[integer n]` 64-bit getter (`mra_tools/bin/reg2asl.py`, `arch_instrs.asl`):
    reads `_R[n]` for `0 <= n < 31`, and returns `Zeros(64)` when `n == 31` (`XZR`). -/
def X_get64 (s : AslState) (n : Fin 32) : BitVec 64 :=
  if h : n.val < 31 then
    s.gpr ⟨n.val, h⟩
  else
    0#64

/-- ASL `X[integer n] = bits(width) value` 64-bit setter:
    writes `_R[n]` for `0 <= n < 31`, and is a no-op when `n == 31` (`XZR`). -/
def X_set64 (s : AslState) (n : Fin 32) (v : BitVec 64) : AslState :=
  if _h : n.val < 31 then
    { s with gpr := fun i => if i.val = n.val then v else s.gpr i }
  else
    s

theorem X_get64_set64_same_non_zr (s : AslState) (n : Fin 32) (v : BitVec 64)
    (h : n.val < 31) :
    X_get64 (X_set64 s n v) n = v := by
  simp [X_get64, X_set64, h]

theorem X_get64_zr (s : AslState) :
    X_get64 s ⟨31, by decide⟩ = 0#64 :=
  rfl

theorem X_set64_zr_noop (s : AslState) (v : BitVec 64) :
    X_set64 s ⟨31, by decide⟩ v = s :=
  rfl

theorem X_get64_set64_other (s : AslState) (i j : Fin 32) (v : BitVec 64)
    (hne : i ≠ j) :
    X_get64 (X_set64 s i v) j = X_get64 s j := by
  unfold X_get64 X_set64
  split
  · split
    · simp only
      split
      · next heq =>
        exfalso
        apply hne
        exact Fin.ext heq.symm
      · rfl
    · rfl
  · rfl

/-- ASL `V[integer n]` 128-bit SIMD register indexed lens. -/
def V_lens : AslIndexedLens AslState (Fin 32) (BitVec 128) where
  get s n := s.vreg n
  set s n v := { s with vreg := fun i => if i = n then v else s.vreg i }

theorem V_lens_lawful : LawfulIndexedLens V_lens where
  get_set_same s i v := by simp [V_lens]
  get_set_other s i j v hne := by
    simp [V_lens]
    intro heq
    exact absurd heq.symm hne

/-- ASL `Elem[bits(N) vector, integer e, integer size]` and
    `Elem[bits(N) &vector, integer e, integer size] = bits(size) value`
    from `mra_tools/prelude.asl:70-79`, specialized to 64-bit lanes `e : Fin 2` of `BitVec 128`. -/
def Elem64_lens : AslIndexedLens (BitVec 128) (Fin 2) (BitVec 64) where
  get vec e :=
    if e.val = 0 then
      vec.extractLsb' 0 64
    else
      vec.extractLsb' 64 64
  set vec e val :=
    if e.val = 0 then
      (vec.extractLsb' 64 64) ++ val
    else
      val ++ (vec.extractLsb' 0 64)

/-- General helper lemmas for `BitVec.extractLsb'` over `BitVec.append` (`++`) and `BitVec.cast`. -/
theorem extractLsb'_cast {n m : Nat} (h : n = m) (x : BitVec n) (start len : Nat) :
    (x.cast h).extractLsb' start len = x.extractLsb' start len := by
  subst h
  rfl

theorem extractLsb'_append_left {n m : Nat} (hi : BitVec n) (lo : BitVec m)
    (start len : Nat) (h : m ≤ start) :
    (hi ++ lo).extractLsb' start len = hi.extractLsb' (start - m) len := by
  ext i hi_lt
  simp only [BitVec.getElem_extractLsb']
  rw [BitVec.getLsbD_append]
  have hnot : ¬ (start + i < m) := by omega
  have hsub : start + i - m = start - m + i := by omega
  simp [hnot, hsub]

theorem extractLsb'_append_left_eq {n m : Nat} (hi : BitVec n) (lo : BitVec m)
    (start start' len : Nat) (h : m ≤ start) (hsub : start - m = start') :
    (hi ++ lo).extractLsb' start len = hi.extractLsb' start' len := by
  subst hsub
  exact extractLsb'_append_left hi lo start len h

theorem extractLsb'_append_low64 (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo :=
  BitVec.extractLsb'_append_eq_right

theorem extractLsb'_append_high64 (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi :=
  BitVec.extractLsb'_append_eq_left

theorem Elem64_lens_lawful : LawfulIndexedLens Elem64_lens where
  get_set_same vec e val := by
    rcases e with ⟨e_val, he⟩
    unfold Elem64_lens
    by_cases h0 : e_val = 0
    · simp [h0, extractLsb'_append_low64]
    · simp [h0, extractLsb'_append_high64]
  get_set_other vec i j val hne := by
    rcases i with ⟨i_val, hi⟩
    rcases j with ⟨j_val, hj⟩
    have hval_ne : i_val ≠ j_val := by
      intro heq
      apply hne
      exact Fin.ext heq
    unfold Elem64_lens
    by_cases hi0 : i_val = 0
    · have hj0 : j_val ≠ 0 := by omega
      simp [hi0, hj0, extractLsb'_append_high64]
    · have hj0 : j_val = 0 := by omega
      simp [hi0, hj0, extractLsb'_append_low64]

/-- `asl-interpreter`'s by-value `eval_proccall` behavior on `Formal_InOut`:
    mutates a local copy of `V[n]` and discards it, leaving architectural state `s` unchanged. -/
def eval_Elem_write_by_value (s : AslState) (n : Fin 32) (e : Fin 2) (rhs : BitVec 64) : AslState :=
  let local_vector := V_lens.get s n
  let _mutated_local := Elem64_lens.set local_vector e rhs
  s

/-- `asl_to_sail`'s pure return-value setter lowering (`translate_asl.ml:1762-1784, 3082-3117`). -/
def asl_to_sail_Elem_write (s : AslState) (n : Fin 32) (e : Fin 2) (rhs : BitVec 64) : AslState :=
  V_lens.set s n (Elem64_lens.set (V_lens.get s n) e rhs)

/-- `herdtools7/asllib`'s `desugar_setter` read-modify-write lowering (`desugar.ml:126-162`). -/
def asllib_desugar_rmw (s : AslState) (n : Fin 32) (e : Fin 2) (rhs : BitVec 64) : AslState :=
  let setter_v1_temporary := V_lens.get s n
  let setter_v1_temporary := Elem64_lens.set setter_v1_temporary e rhs
  V_lens.set s n setter_v1_temporary

/-- `asl_to_sail`'s functional return lowering and `asllib`'s `desugar_setter` RMW lowering
    are definitionally equal in Lean 4. -/
theorem asl_to_sail_eq_asllib_rmw (s : AslState) (n : Fin 32) (e : Fin 2) (rhs : BitVec 64) :
    asl_to_sail_Elem_write s n e rhs = asllib_desugar_rmw s n e rhs :=
  rfl

/-- Composed lens correctness for `asl_to_sail_Elem_write`: reading the written lane yields `rhs`. -/
theorem asl_to_sail_Elem_roundtrip (s : AslState) (n : Fin 32) (e : Fin 2) (rhs : BitVec 64) :
    Elem64_lens.get (V_lens.get (asl_to_sail_Elem_write s n e rhs) n) e = rhs := by
  unfold asl_to_sail_Elem_write
  rw [V_lens_lawful.get_set_same]
  exact Elem64_lens_lawful.get_set_same (V_lens.get s n) e rhs

/-- Lane-level framing: writing lane `e₁` preserves lane `e₂ ≠ e₁` of the same vector register `V[n]`. -/
theorem asl_to_sail_Elem_frame_lane (s : AslState) (n : Fin 32) (e₁ e₂ : Fin 2) (rhs : BitVec 64)
    (hne : e₁ ≠ e₂) :
    Elem64_lens.get (V_lens.get (asl_to_sail_Elem_write s n e₁ rhs) n) e₂ =
      Elem64_lens.get (V_lens.get s n) e₂ := by
  unfold asl_to_sail_Elem_write
  rw [V_lens_lawful.get_set_same]
  exact Elem64_lens_lawful.get_set_other (V_lens.get s n) e₁ e₂ rhs hne

/-- Register-level framing: writing lane `e` of `V[n₁]` preserves `V[n₂]` for `n₁ ≠ n₂`. -/
theorem asl_to_sail_Elem_frame_reg (s : AslState) (n₁ n₂ : Fin 32) (e : Fin 2) (rhs : BitVec 64)
    (hne : n₁ ≠ n₂) :
    V_lens.get (asl_to_sail_Elem_write s n₁ e rhs) n₂ = V_lens.get s n₂ := by
  unfold asl_to_sail_Elem_write
  exact V_lens_lawful.get_set_other s n₁ n₂ _ hne

/-- Witness that `asl-interpreter`'s by-value `eval_proccall` fails to update `V[n]` on
    `Formal_InOut` setter writes when `rhs` differs from the current lane value. -/
theorem asl_interpreter_by_value_bug_loses_write (s : AslState) (n : Fin 32) (e : Fin 2) :
    let rhs := (Elem64_lens.get (V_lens.get s n) e) + 1#64
    Elem64_lens.get (V_lens.get (eval_Elem_write_by_value s n e rhs) n) e ≠
      Elem64_lens.get (V_lens.get (asl_to_sail_Elem_write s n e rhs) n) e := by
  intro rhs
  rw [asl_to_sail_Elem_roundtrip]
  unfold eval_Elem_write_by_value rhs
  intro h
  have hnat := congrArg BitVec.toNat h
  simp [BitVec.toNat_add] at hnat
  omega

/-!
  ### ASL `CONSTRAINED UNPREDICTABLE` vs `UNDEFINED` in Anneal's `StepResult`
-/

inductive AslConstraint where
  | UNPREDICTABLE
  | UNDEF
  | NOP
  | WBSUPPRESS
  | UNKNOWN (val : BitVec 64)
  deriving DecidableEq, Repr

/-- Maps a single `AslConstraint` outcome for post-indexed `LDR Xt, [Xn], #imm` (`n == t && n != 31`)
    to an Anneal `StepResult AslState`. -/
def evalLdrOverlapConstraint (s : AslState) (rt rn : Fin 32)
    (wbAddr loadedVal : BitVec 64) : AslConstraint → StepResult AslState
  | .UNPREDICTABLE => .failed .ub
  | .UNDEF         => .failed .ub
  | .NOP           => .next s
  | .WBSUPPRESS    => .next (X_set64 s rt loadedVal)
  | .UNKNOWN unk   => .next (X_set64 (X_set64 s rn wbAddr) rt unk)

/-- Small-step machine parameterized by the list of `AslConstraint` outcomes permitted by
    `ConstrainUnpredictable`. -/
def ConstrainedLdrMachine (rt rn : Fin 32) (wbAddr loadedVal : BitVec 64)
    (allowed : List AslConstraint) : SmallStepMachine Unit AslState where
  step _ s := .choice .demonic (allowed.map (evalLdrOverlapConstraint s rt rn wbAddr loadedVal))

/-- L3's exact 4-way outcome list from `isa-models/arm-v8/v8-iset.spec:1178-1196`
    (`match UNKNOWN ("LoadImmediate unpredictable") :: bits(2)`). -/
def l3LoadImmUnpredAllowed (unkVal : BitVec 64) : List AslConstraint :=
  [.WBSUPPRESS, .UNKNOWN unkVal, .UNDEF, .NOP]

/-- A non-faulting profile of `ConstrainUnpredictable` that excludes `.UNDEF` and `.UNPREDICTABLE`. -/
def nonFaultingLoadImmAllowed (unkVal : BitVec 64) : List AslConstraint :=
  [.WBSUPPRESS, .UNKNOWN unkVal, .NOP]

/-- Theorem 1: If `.UNDEF` is in the `allowed` list of `ConstrainUnpredictable`, then the instruction
    can demonically choose `.UNDEF` and reach `.failed .ub` in 1 step, so `BehaviorOf.defined`
    collapses to `False`! -/
theorem constrained_unpred_with_undef_not_defined
    (s : AslState) (rt rn : Fin 32) (wbAddr loadedVal : BitVec 64)
    (allowed : List AslConstraint) (h_undef : AslConstraint.UNDEF ∈ allowed) :
    ¬ (BehaviorOf (ConstrainedLdrMachine rt rn wbAddr loadedVal allowed) ()).defined ⟨s, 1⟩ := by
  intro h_def
  apply h_def
  apply ReachesPrefix.step_from 0 s (.failed .ub)
  apply ReachesFromResult.demonic 0
    (allowed.map (evalLdrOverlapConstraint s rt rn wbAddr loadedVal))
    (.failed .ub)
    (.failed .ub)
  · rw [List.mem_map]
    exact ⟨.UNDEF, h_undef, rfl⟩
  · exact ReachesFromResult.failed 0 .ub

/-- Corollary: L3's 4-way `UNKNOWN ("LoadImmediate unpredictable") :: bits(2)` encoding in
    `isa-models/arm-v8/v8-iset.spec:1178-1196` includes `case 2 => Unallocated` (`.UNDEF`),
    so under demonic choice in Anneal its 1-step `BehaviorOf.defined` is `False`. -/
theorem l3_load_imm_unpred_not_defined
    (s : AslState) (rt rn : Fin 32) (wbAddr loadedVal unkVal : BitVec 64) :
    ¬ (BehaviorOf (ConstrainedLdrMachine rt rn wbAddr loadedVal (l3LoadImmUnpredAllowed unkVal))
        ()).defined ⟨s, 1⟩ := by
  apply constrained_unpred_with_undef_not_defined
  simp [l3LoadImmUnpredAllowed]

/-- Predicate asserting that an `AslConstraint` is a non-faulting architectural transition. -/
def IsNonFaultingConstraint : AslConstraint → Prop
  | .UNPREDICTABLE => False
  | .UNDEF         => False
  | .NOP           => True
  | .WBSUPPRESS    => True
  | .UNKNOWN _     => True

/-- Theorem 2: Whenever all outcomes in `allowed` are non-faulting (`IsNonFaultingConstraint`),
    the 1-step execution of `ConstrainedLdrMachine` is guaranteed to be defined
    (`(BehaviorOf M ()).defined ⟨s, 1⟩` holds). -/
theorem constrained_unpred_nonfaulting_is_defined
    (s : AslState) (rt rn : Fin 32) (wbAddr loadedVal : BitVec 64)
    (allowed : List AslConstraint)
    (h_nonfault : ∀ c ∈ allowed, IsNonFaultingConstraint c) :
    (BehaviorOf (ConstrainedLdrMachine rt rn wbAddr loadedVal allowed) ()).defined ⟨s, 1⟩ := by
  intro h_ub
  cases h_ub with
  | step_from _ _ _ h_res =>
    cases h_res with
    | demonic _ _ b _ hb_mem hb_reaches =>
      rw [List.mem_map] at hb_mem
      rcases hb_mem with ⟨c, hc_mem, hc_eq⟩
      have hc_ok := h_nonfault c hc_mem
      cases c <;> simp [IsNonFaultingConstraint] at hc_ok
      all_goals
        subst hc_eq
        cases hb_reaches with
        | next _ _ _ h_zero =>
          cases h_zero

/-- Corollary: Under `nonFaultingLoadImmAllowed`, `BehaviorOf.defined` holds and every
    permitted architectural outcome (`WBSUPPRESS`, `UNKNOWN unkVal`, `NOP`) is reachable. -/
theorem nonFaultingLoadImm_defined_and_reaches_all
    (s : AslState) (rt rn : Fin 32) (wbAddr loadedVal unkVal : BitVec 64) :
    let M := ConstrainedLdrMachine rt rn wbAddr loadedVal (nonFaultingLoadImmAllowed unkVal)
    (BehaviorOf M ()).defined ⟨s, 1⟩ ∧
    ReachesPrefix M () 1 s (.unfinished (X_set64 s rt loadedVal)) ∧
    ReachesPrefix M () 1 s (.unfinished (X_set64 (X_set64 s rn wbAddr) rt unkVal)) ∧
    ReachesPrefix M () 1 s (.unfinished s) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply constrained_unpred_nonfaulting_is_defined
    intro c hc
    simp [nonFaultingLoadImmAllowed] at hc
    rcases hc with rfl | rfl | rfl <;> trivial
  · apply ReachesPrefix.step_from 0 s
    apply ReachesFromResult.demonic 0 _ (.next (X_set64 s rt loadedVal))
    · simp [nonFaultingLoadImmAllowed, evalLdrOverlapConstraint]
    · exact ReachesFromResult.next 0 _ _ (ReachesPrefix.zero _)
  · apply ReachesPrefix.step_from 0 s
    apply ReachesFromResult.demonic 0 _ (.next (X_set64 (X_set64 s rn wbAddr) rt unkVal))
    · simp [nonFaultingLoadImmAllowed, evalLdrOverlapConstraint]
    · exact ReachesFromResult.next 0 _ _ (ReachesPrefix.zero _)
  · apply ReachesPrefix.step_from 0 s
    apply ReachesFromResult.demonic 0 _ (.next s)
    · simp [nonFaultingLoadImmAllowed, evalLdrOverlapConstraint]
    · exact ReachesFromResult.next 0 _ _ (ReachesPrefix.zero _)


/-! ============================================================================
    Section 3: Mechanization (b) — L3-to-Lean 4 Translation Prototype &
    Anneal `SmallStepMachine` / `BridgeTransition` Embedding
    ============================================================================ -/

inductive L3Instr where
  | AddSubImmediate (sf op S sh : BitVec 1) (imm12 : BitVec 12) (rn rd : BitVec 5)
  | LoadStoreImmediate64 (opc : BitVec 1) (imm12 : BitVec 12) (rn rt : BitVec 5)
  | BranchRegisterRet (rn : BitVec 5)
  | Unallocated (raw : BitVec 32)
  deriving DecidableEq, Repr

/-- Total 32-bit instruction decoder corresponding to L3's `DecodeA64` compiled via
    `Matches.boolifyMatches` (`L3/Matches.sml:435-483`) and `Convert.boolMatchConv`
    (`L3/Export.sml:1299-1323`). -/
def decodeA64 (w : BitVec 32) : L3Instr :=
  let op_addsub := w.extractLsb' 23 6
  let op_ldst   := w.extractLsb' 23 9
  let op_ret_hi := w.extractLsb' 10 22
  let rd_or_rt  := w.extractLsb' 0 5
  let rn        := w.extractLsb' 5 5
  let imm12     := w.extractLsb' 10 12
  let sh_or_opc := w.extractLsb' 22 1
  let S         := w.extractLsb' 29 1
  let op        := w.extractLsb' 30 1
  let sf        := w.extractLsb' 31 1
  if op_addsub == 0b100010#6 then
    .AddSubImmediate sf op S sh_or_opc imm12 rn rd_or_rt
  else if op_ldst == 0b111110010#9 then
    .LoadStoreImmediate64 sh_or_opc imm12 rn rd_or_rt
  else if op_ret_hi == 0b1101011001011111000000#22 && rd_or_rt == 0b00000#5 then
    .BranchRegisterRet rn
  else
    .Unallocated w

/-- 32-bit bit-concatenation encoder for `L3Instr`. Returns `none` for `.Unallocated`. -/
def encodeA64 : L3Instr → Option (BitVec 32)
  | .AddSubImmediate sf op S sh imm12 rn rd =>
      let w : BitVec 32 :=
        (sf ++ op ++ S ++ (0b100010#6) ++ sh ++ imm12 ++ rn ++ rd).cast (by decide)
      some w
  | .LoadStoreImmediate64 opc imm12 rn rt =>
      let w : BitVec 32 :=
        ((0b111110010#9) ++ opc ++ imm12 ++ rn ++ rt).cast (by decide)
      some w
  | .BranchRegisterRet rn =>
      let w : BitVec 32 :=
        ((0b1101011001011111000000#22) ++ rn ++ (0b00000#5)).cast (by decide)
      some w
  | .Unallocated _ => none

theorem decodeA64_encode_AddSubImmediate
    (sf op S sh : BitVec 1) (imm12 : BitVec 12) (rn rd : BitVec 5) :
    let w : BitVec 32 :=
      (sf ++ op ++ S ++ (0b100010#6) ++ sh ++ imm12 ++ rn ++ rd).cast (by decide)
    decodeA64 w = .AddSubImmediate sf op S sh imm12 rn rd := by
  intro w
  have hrd : w.extractLsb' 0 5 = rd := by
    simp only [w, extractLsb'_cast, BitVec.extractLsb'_append_eq_right]
  have hrn : w.extractLsb' 5 5 = rn := by
    simp only [w, extractLsb'_cast]
    rw [extractLsb'_append_left_eq _ _ 5 0 5 (by decide) rfl]
    exact BitVec.extractLsb'_append_eq_right
  have himm12 : w.extractLsb' 10 12 = imm12 := by
    simp only [w, extractLsb'_cast]
    rw [extractLsb'_append_left_eq _ _ 10 5 12 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 5 0 12 (by decide) rfl]
    exact BitVec.extractLsb'_append_eq_right
  have hsh : w.extractLsb' 22 1 = sh := by
    simp only [w, extractLsb'_cast]
    rw [extractLsb'_append_left_eq _ _ 22 17 1 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 17 12 1 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 12 0 1 (by decide) rfl]
    exact BitVec.extractLsb'_append_eq_right
  have hopc : w.extractLsb' 23 6 = 0b100010#6 := by
    simp only [w, extractLsb'_cast]
    rw [extractLsb'_append_left_eq _ _ 23 18 6 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 18 13 6 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 13 1 6 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 1 0 6 (by decide) rfl]
    exact BitVec.extractLsb'_append_eq_right
  have hS : w.extractLsb' 29 1 = S := by
    simp only [w, extractLsb'_cast]
    rw [extractLsb'_append_left_eq _ _ 29 24 1 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 24 19 1 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 19 7 1 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 7 6 1 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 6 0 1 (by decide) rfl]
    exact BitVec.extractLsb'_append_eq_right
  have hop : w.extractLsb' 30 1 = op := by
    simp only [w, extractLsb'_cast]
    rw [extractLsb'_append_left_eq _ _ 30 25 1 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 25 20 1 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 20 8 1 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 8 7 1 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 7 1 1 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 1 0 1 (by decide) rfl]
    exact BitVec.extractLsb'_append_eq_right
  have hsf : w.extractLsb' 31 1 = sf := by
    simp only [w, extractLsb'_cast]
    rw [extractLsb'_append_left_eq _ _ 31 26 1 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 26 21 1 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 21 9 1 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 9 8 1 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 8 2 1 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 2 1 1 (by decide) rfl]
    exact BitVec.extractLsb'_append_eq_left
  unfold decodeA64
  simp [hrd, hrn, himm12, hsh, hopc, hS, hop, hsf]

theorem decodeA64_encode_LoadStoreImmediate64
    (opc : BitVec 1) (imm12 : BitVec 12) (rn rt : BitVec 5) :
    let w : BitVec 32 :=
      ((0b111110010#9) ++ opc ++ imm12 ++ rn ++ rt).cast (by decide)
    decodeA64 w = .LoadStoreImmediate64 opc imm12 rn rt := by
  intro w
  have hrt : w.extractLsb' 0 5 = rt := by
    simp only [w, extractLsb'_cast, BitVec.extractLsb'_append_eq_right]
  have hrn : w.extractLsb' 5 5 = rn := by
    simp only [w, extractLsb'_cast]
    rw [extractLsb'_append_left_eq _ _ 5 0 5 (by decide) rfl]
    exact BitVec.extractLsb'_append_eq_right
  have himm12 : w.extractLsb' 10 12 = imm12 := by
    simp only [w, extractLsb'_cast]
    rw [extractLsb'_append_left_eq _ _ 10 5 12 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 5 0 12 (by decide) rfl]
    exact BitVec.extractLsb'_append_eq_right
  have hopc : w.extractLsb' 22 1 = opc := by
    simp only [w, extractLsb'_cast]
    rw [extractLsb'_append_left_eq _ _ 22 17 1 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 17 12 1 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 12 0 1 (by decide) rfl]
    exact BitVec.extractLsb'_append_eq_right
  have hldst : w.extractLsb' 23 9 = 0b111110010#9 := by
    simp only [w, extractLsb'_cast]
    rw [extractLsb'_append_left_eq _ _ 23 18 9 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 18 13 9 (by decide) rfl]
    rw [extractLsb'_append_left_eq _ _ 13 1 9 (by decide) rfl]
    exact BitVec.extractLsb'_append_eq_left
  have haddsub : w.extractLsb' 23 6 = 0b110010#6 := by
    have hsub : w.extractLsb' 23 6 = (w.extractLsb' 23 9).extractLsb' 0 6 := by
      ext i hi_lt
      simp [BitVec.getElem_extractLsb']
      omega
    rw [hsub, hldst]
    rfl
  unfold decodeA64
  simp [hrt, hrn, himm12, hopc, hldst, haddsub]

theorem decodeA64_encode_BranchRegisterRet (rn : BitVec 5) :
    let w : BitVec 32 :=
      ((0b1101011001011111000000#22) ++ rn ++ (0b00000#5)).cast (by decide)
    decodeA64 w = .BranchRegisterRet rn := by
  intro w
  have hrd : w.extractLsb' 0 5 = 0b00000#5 := by
    simp only [w, extractLsb'_cast, BitVec.extractLsb'_append_eq_right]
  have hrn : w.extractLsb' 5 5 = rn := by
    simp only [w, extractLsb'_cast]
    rw [extractLsb'_append_left_eq _ _ 5 0 5 (by decide) rfl]
    exact BitVec.extractLsb'_append_eq_right
  have hret_hi : w.extractLsb' 10 22 = 0b1101011001011111000000#22 := by
    simp only [w, extractLsb'_cast]
    rw [extractLsb'_append_left_eq _ _ 10 5 22 (by decide) rfl]
    exact BitVec.extractLsb'_append_eq_left
  have haddsub : w.extractLsb' 23 6 = 0b101100#6 := by
    have hsub : w.extractLsb' 23 6 = (w.extractLsb' 10 22).extractLsb' 13 6 := by
      ext i hi_lt
      have h_idx : 10 + (13 + i) = 23 + i := by omega
      simp [BitVec.getElem_extractLsb', h_idx]
      omega
    rw [hsub, hret_hi]
    rfl
  have hldst : w.extractLsb' 23 9 = 0b110101100#9 := by
    have hsub : w.extractLsb' 23 9 = (w.extractLsb' 10 22).extractLsb' 13 9 := by
      ext i hi_lt
      have h_idx : 10 + (13 + i) = 23 + i := by omega
      simp [BitVec.getElem_extractLsb', h_idx]
      omega
    rw [hsub, hret_hi]
    rfl
  unfold decodeA64
  simp [hrd, hrn, hret_hi, haddsub, hldst]

/-- Full roundtrip theorem for the L3 AArch64 decoder and encoder:
    every encodable `L3Instr` decodes back to itself (`decodeA64 w = instr`). -/
theorem decodeA64_encodeA64_roundtrip (instr : L3Instr) (w : BitVec 32)
    (h_enc : encodeA64 instr = some w) :
    decodeA64 w = instr := by
  cases instr with
  | AddSubImmediate sf op S sh imm12 rn rd =>
    simp [encodeA64] at h_enc
    subst h_enc
    exact decodeA64_encode_AddSubImmediate sf op S sh imm12 rn rd
  | LoadStoreImmediate64 opc imm12 rn rt =>
    simp [encodeA64] at h_enc
    subst h_enc
    exact decodeA64_encode_LoadStoreImmediate64 opc imm12 rn rt
  | BranchRegisterRet rn =>
    simp [encodeA64] at h_enc
    subst h_enc
    exact decodeA64_encode_BranchRegisterRet rn
  | Unallocated _ =>
    simp [encodeA64] at h_enc

/-!
  ### 3.2 L3 Lowered State-Exception Record & Monadic Semantics (`L3/Export.sml:36-74, 682-1121`)
-/

inductive L3Exception where
  | NoException
  | UNDEFINED_FAULT
  | ALIGNMENT_FAULT
  deriving DecidableEq, Repr

structure L3State where
  PC        : BitVec 64
  REG       : BitVec 5 → BitVec 64
  SP        : BitVec 64
  nzcv      : BitVec 4
  MEM       : BitVec 64 → BitVec 8
  halted    : Bool
  exception : L3Exception

/-- L3's pure state-passing monad after `Monadify.deMonadifyDefn` (`Export.sml:1026-1121`). -/
abbrev L3M (α : Type) := L3State → α × L3State

def m_const {α : Type} (x : α) : L3M α :=
  fun s => (x, s)

def m_bind {α β : Type} (m : L3M α) (f : α → L3M β) : L3M β :=
  fun s =>
    let (a, s1) := m s
    if s1.exception == .NoException then
      f a s1
    else
      ( (f a s1).1, s1 )

def m_read {α : Type} (proj : L3State → α) : L3M α :=
  fun s => (proj s, s)

def m_write (upd : L3State → L3State) : L3M Unit :=
  fun s =>
    if s.exception == .NoException then
      ((), upd s)
    else
      ((), s)

/-- `raise'exception` synthesized by `Exception.buildExceptionDatatype` (`Export.sml:43-50`). -/
def raise_exception {α : Type} (defaultVal : α) (e : L3Exception) : L3M α :=
  fun s =>
    (defaultVal, if s.exception == .NoException then { s with exception := e } else s)

/-- L3 `X(n)` 64-bit register getter (`v8-base.spec:240`): reads `REG(n)` for `n != 31`, `0` for `31`. -/
def l3_X_read (n : BitVec 5) (s : L3State) : BitVec 64 :=
  if n == 31#5 then 0#64 else s.REG n

/-- L3 `X(n) <- v` 64-bit register setter (`v8-base.spec:246`): writes `REG(n)` for `n != 31`. -/
def l3_X_write (n : BitVec 5) (v : BitVec 64) (s : L3State) : L3State :=
  if n == 31#5 then s else { s with REG := fun r => if r == n then v else s.REG r }

/-- L3 `SP` or `X(n)` base register reader (`if n == 31 then SP else X(n)` in `v8-iset.spec:1402`). -/
def l3_X_or_SP_read (n : BitVec 5) (s : L3State) : BitVec 64 :=
  if n == 31#5 then s.SP else s.REG n

/-- L3 `SP` or `X(d)` destination writer (`if d == 31 and !S then SP <- result else X(d) <- result`). -/
def l3_X_or_SP_write (d : BitVec 5) (v : BitVec 64) (s : L3State) : L3State :=
  if d == 31#5 then { s with SP := v } else l3_X_write d v s

/-- Little-endian 64-bit memory read (`Mem` in `v8-base.spec:562-612`). -/
def readMem64 (addr : BitVec 64) (s : L3State) : BitVec 64 :=
  let b0 := s.MEM (addr + 0#64)
  let b1 := s.MEM (addr + 1#64)
  let b2 := s.MEM (addr + 2#64)
  let b3 := s.MEM (addr + 3#64)
  let b4 := s.MEM (addr + 4#64)
  let b5 := s.MEM (addr + 5#64)
  let b6 := s.MEM (addr + 6#64)
  let b7 := s.MEM (addr + 7#64)
  (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).cast (by decide)

/-- Little-endian 64-bit memory write (`Mem` in `v8-base.spec:562-612`). -/
def writeMem64 (addr : BitVec 64) (val : BitVec 64) (s : L3State) : L3State :=
  let b0 := val.extractLsb' 0 8
  let b1 := val.extractLsb' 8 8
  let b2 := val.extractLsb' 16 8
  let b3 := val.extractLsb' 24 8
  let b4 := val.extractLsb' 32 8
  let b5 := val.extractLsb' 40 8
  let b6 := val.extractLsb' 48 8
  let b7 := val.extractLsb' 56 8
  { s with MEM := fun a =>
      if a == addr + 0#64 then b0
      else if a == addr + 1#64 then b1
      else if a == addr + 2#64 then b2
      else if a == addr + 3#64 then b3
      else if a == addr + 4#64 then b4
      else if a == addr + 5#64 then b5
      else if a == addr + 6#64 then b6
      else if a == addr + 7#64 then b7
      else s.MEM a }

/-- Instruction semantics `dfn'AddSubImmediate` (`isa-models/arm-v8/v8-iset.spec:1399-1413`). -/
def dfn_AddSubImmediate (sf op S sh : BitVec 1) (imm12 : BitVec 12) (rn rd : BitVec 5) : L3M Unit :=
  fun s =>
    if sf == 0#1 then
      raise_exception () .UNDEFINED_FAULT s
    else
      let imm64 : BitVec 64 :=
        if sh == 0#1 then imm12.zeroExtend 64 else (imm12.zeroExtend 64) <<< 12
      let op1 := l3_X_or_SP_read rn s
      let result := if op == 0#1 then op1 + imm64 else op1 - imm64
      let s' :=
        if S == 1#1 then
          let n_flag : BitVec 1 := result.extractLsb' 63 1
          let z_flag : BitVec 1 := if result == 0#64 then 1#1 else 0#1
          let s_flags := { s with nzcv := (n_flag ++ z_flag ++ 0#2).cast (by decide) }
          l3_X_write rd result s_flags
        else
          l3_X_or_SP_write rd result s
      ((), { s' with PC := s.PC + 4#64 })

/-- Instruction semantics `dfn'LoadStoreImmediate64` (`isa-models/arm-v8/v8-iset.spec:1145-1235`). -/
def dfn_LoadStoreImmediate64 (opc : BitVec 1) (imm12 : BitVec 12) (rn rt : BitVec 5) : L3M Unit :=
  fun s =>
    let offset : BitVec 64 := (imm12.zeroExtend 64) <<< 3
    let baseAddr := l3_X_or_SP_read rn s
    let addr := baseAddr + offset
    if addr.extractLsb' 0 3 != 0#3 then
      raise_exception () .ALIGNMENT_FAULT s
    else if opc == 0#1 then
      let data := l3_X_read rt s
      let s' := writeMem64 addr data s
      ((), { s' with PC := s.PC + 4#64 })
    else
      let data := readMem64 addr s
      let s' := l3_X_write rt data s
      ((), { s' with PC := s.PC + 4#64 })

/-- Instruction semantics `dfn'BranchRegisterRet` (`isa-models/arm-v8/v8-iset.spec:1058-1071`). -/
def dfn_BranchRegisterRet (rn : BitVec 5) : L3M Unit :=
  fun s =>
    let target := l3_X_read rn s
    ((), { s with PC := target, halted := true })

/-- Instruction semantics `dfn'Unallocated` (`isa-models/arm-v8/v8-iset.spec:952-955`). -/
def dfn_Unallocated : L3M Unit :=
  raise_exception () .UNDEFINED_FAULT

/-- L3 generated dispatcher `Run (instr : L3Instr) : L3M Unit` (`Export.sml:618-634`). -/
def l3_Run : L3Instr → L3M Unit
  | .AddSubImmediate sf op S sh imm12 rn rd => dfn_AddSubImmediate sf op S sh imm12 rn rd
  | .LoadStoreImmediate64 opc imm12 rn rt   => dfn_LoadStoreImmediate64 opc imm12 rn rt
  | .BranchRegisterRet rn                   => dfn_BranchRegisterRet rn
  | .Unallocated _                          => dfn_Unallocated

/-!
  ### 3.3 Embedding into Anneal's `SmallStepMachine` and `BridgeTransition`
-/

abbrev CodeMem := BitVec 64 → Option (BitVec 32)

def l3Step (prog : CodeMem) (s : L3State) : StepResult L3State :=
  if s.exception != .NoException then
    .failed .ub
  else if s.halted then
    .terminated .returned s
  else
    match prog s.PC with
    | none => .failed .ub
    | some word =>
        let instr := decodeA64 word
        let ((), s') := l3_Run instr s
        if s'.exception != .NoException then
          .failed .ub
        else if s'.halted then
          .terminated .returned s'
        else
          .next s'

def L3Machine : SmallStepMachine CodeMem L3State where
  step := l3Step

theorem l3Step_ne_choice (prog : CodeMem) (s : L3State) (ck : ChoiceKind)
    (branches : List (StepResult L3State)) :
    l3Step prog s ≠ .choice ck branches := by
  unfold l3Step
  split
  · intro h; nomatch h
  · split
    · intro h; nomatch h
    · cases prog s.PC with
      | none => intro h; nomatch h
      | some word =>
        dsimp only
        split
        · intro h; nomatch h
        · split
          · intro h; nomatch h
          · intro h; nomatch h

/-- Bounded multi-step fuel evaluator for `L3Machine`. -/
def runSteps (prog : CodeMem) : Nat → L3State → PrefixOutcome L3State
  | 0, s => .unfinished s
  | n + 1, s =>
      match l3Step prog s with
      | .next s' => runSteps prog n s'
      | .terminated k s' => .terminated k s'
      | .failed k => .failed k
      | .choice _ _ => .failed .error

/-- Total soundness of `runSteps`: because `l3Step` never emits `.choice`, `runSteps prog n s`
    is always a valid `ReachesPrefix` outcome for every step count `n` and state `s`. -/
theorem runSteps_sound (prog : CodeMem) :
    ∀ (n : Nat) (s : L3State),
      ReachesPrefix L3Machine prog n s (runSteps prog n s)
  | 0, s => ReachesPrefix.zero s
  | n + 1, s => by
      unfold runSteps
      have hstep : L3Machine.step prog s = l3Step prog s := rfl
      cases h : l3Step prog s with
      | next s' =>
        apply ReachesPrefix.step_from n s
        rw [hstep, h]
        exact ReachesFromResult.next n s' _ (runSteps_sound prog n s')
      | terminated k s' =>
        apply ReachesPrefix.step_from n s
        rw [hstep, h]
        exact ReachesFromResult.terminated n k s'
      | failed k =>
        apply ReachesPrefix.step_from n s
        rw [hstep, h]
        exact ReachesFromResult.failed n k
      | choice ck branches =>
        exfalso
        exact l3Step_ne_choice prog s ck branches h

theorem l3Machine_total : TotalStep L3Machine := by
  intro prog n s
  show ResultProduces L3Machine prog n (l3Step prog s)
  unfold l3Step
  split
  · exact ResultProduces.failed .ub
  · split
    · exact ResultProduces.terminated .returned s
    · cases prog s.PC with
      | none => exact ResultProduces.failed .ub
      | some word =>
        dsimp only
        split
        · exact ResultProduces.failed .ub
        · split
          · exact ResultProduces.terminated .returned _
          · exact ResultProduces.next _ _ (runSteps_sound prog n _)

theorem l3Machine_inhabited : InhabitedDemonic L3Machine := by
  intro prog s
  show NoEmptyDemonic (l3Step prog s)
  unfold l3Step
  split
  · exact NoEmptyDemonic.failed .ub
  · split
    · exact NoEmptyDemonic.terminated .returned s
    · cases prog s.PC with
      | none => exact NoEmptyDemonic.failed .ub
      | some word =>
        dsimp only
        split
        · exact NoEmptyDemonic.failed .ub
        · split
          · exact NoEmptyDemonic.terminated .returned _
          · exact NoEmptyDemonic.next _

def L3Bridge : BridgeTransition CodeMem L3State where
  machine := L3Machine
  total_step := l3Machine_total
  inhabited_demonic := l3Machine_inhabited

/-!
  ### 3.4 Concrete 4-Instruction AArch64 Program Verification by Kernel `rfl` & `BehaviorOf`
-/

def insn_add_x0_x1_42 : BitVec 32 := 0x9100A820#32
def insn_str_x0_sp_0  : BitVec 32 := 0xF90003E0#32
def insn_ldr_x2_sp_0  : BitVec 32 := 0xF94003E2#32
def insn_ret_x30      : BitVec 32 := 0xD65F03C0#32

theorem decode_insn_add_x0_x1_42 :
    decodeA64 insn_add_x0_x1_42 = .AddSubImmediate 1#1 0#1 0#1 0#1 42#12 1#5 0#5 := rfl

theorem decode_insn_str_x0_sp_0 :
    decodeA64 insn_str_x0_sp_0 = .LoadStoreImmediate64 0#1 0#12 31#5 0#5 := rfl

theorem decode_insn_ldr_x2_sp_0 :
    decodeA64 insn_ldr_x2_sp_0 = .LoadStoreImmediate64 1#1 0#12 31#5 2#5 := rfl

theorem decode_insn_ret_x30 :
    decodeA64 insn_ret_x30 = .BranchRegisterRet 30#5 := rfl

def testProg : CodeMem := fun pc =>
  if pc == 0x1000#64 then some insn_add_x0_x1_42
  else if pc == 0x1004#64 then some insn_str_x0_sp_0
  else if pc == 0x1008#64 then some insn_ldr_x2_sp_0
  else if pc == 0x100C#64 then some insn_ret_x30
  else none

def testInitState : L3State where
  PC        := 0x1000#64
  REG       := fun r =>
    if r == 1#5 then 100#64
    else if r == 30#5 then 0x2000#64
    else 0#64
  SP        := 0x8000#64
  nzcv      := 0#4
  MEM       := fun _ => 0#8
  halted    := false
  exception := .NoException

theorem l3Machine_deterministic (prog : CodeMem) :
    ∀ (n : Nat) (s : L3State) (o : PrefixOutcome L3State),
      ReachesPrefix L3Machine prog n s o →
      o = runSteps prog n s := by
  intro n
  induction n with
  | zero =>
    intro s o h
    cases h
    rfl
  | succ n ih =>
    intro s o h
    cases h with
    | step_from _ _ _ hres =>
      unfold runSteps
      change ReachesFromResult L3Machine prog n (l3Step prog s) o at hres
      cases hstep : l3Step prog s with
      | next s' =>
        rw [hstep] at hres
        cases hres with
        | next _ _ _ hnext =>
          exact ih s' o hnext
      | terminated k s' =>
        rw [hstep] at hres
        cases hres
        rfl
      | failed k =>
        rw [hstep] at hres
        cases hres
        rfl
      | choice ck branches =>
        exfalso
        exact l3Step_ne_choice prog s ck branches hstep

theorem testProg_four_step_rfl :
    let out := runSteps testProg 4 testInitState
    match out with
    | .terminated .returned s_final =>
        s_final.PC == 0x2000#64 &&
        l3_X_read 0#5 s_final == 142#64 &&
        l3_X_read 2#5 s_final == 142#64 &&
        s_final.exception == .NoException
    | _ => false :=
  rfl

def testProgSpec : Partial (ExecQuery L3State) (ExecOut L3State) where
  defined q := q.init = testInitState ∧ q.steps = 4
  val _ _ :=
    ⟨fun o =>
      match o with
      | .terminated .returned s_final =>
          s_final.PC = 0x2000#64 ∧
          l3_X_read 0#5 s_final = 142#64 ∧
          l3_X_read 2#5 s_final = 142#64 ∧
          s_final.exception = .NoException
      | _ => False⟩

theorem testProg_refines_spec :
    BehaviorOf L3Bridge.machine testProg ≤ testProgSpec := by
  intro q hdef
  rcases hdef with ⟨hinit, hsteps⟩
  refine ⟨?_, ?_⟩
  · intro hub
    change ReachesPrefix L3Machine testProg q.steps q.init (.failed .ub) at hub
    rw [hinit, hsteps] at hub
    have heq := l3Machine_deterministic testProg 4 testInitState (.failed .ub) hub
    nomatch heq
  · intro _ o hreach
    change ReachesPrefix L3Machine testProg q.steps q.init o at hreach
    rw [hinit, hsteps] at hreach
    have heq := l3Machine_deterministic testProg 4 testInitState o hreach
    subst heq
    exact ⟨rfl, rfl, rfl, rfl⟩


/-! ============================================================================
    Section 4: Axiom & Completeness Verification (`#guard_msgs in #print axioms`)
    ============================================================================ -/

/-- info: 'AnnealAslL3BridgeProbe.Elem64_lens_lawful' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Elem64_lens_lawful

/-- info: 'AnnealAslL3BridgeProbe.asl_to_sail_Elem_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms asl_to_sail_Elem_roundtrip

/-- info: 'AnnealAslL3BridgeProbe.asl_interpreter_by_value_bug_loses_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms asl_interpreter_by_value_bug_loses_write

/-- info: 'AnnealAslL3BridgeProbe.l3_load_imm_unpred_not_defined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms l3_load_imm_unpred_not_defined

/-- info: 'AnnealAslL3BridgeProbe.nonFaultingLoadImm_defined_and_reaches_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms nonFaultingLoadImm_defined_and_reaches_all

/-- info: 'AnnealAslL3BridgeProbe.decodeA64_encodeA64_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decodeA64_encodeA64_roundtrip

/-- info: 'AnnealAslL3BridgeProbe.L3Bridge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms L3Bridge

/-- info: 'AnnealAslL3BridgeProbe.testProg_four_step_rfl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms testProg_four_step_rfl

/-- info: 'AnnealAslL3BridgeProbe.testProg_refines_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms testProg_refines_spec

end AnnealAslL3BridgeProbe
