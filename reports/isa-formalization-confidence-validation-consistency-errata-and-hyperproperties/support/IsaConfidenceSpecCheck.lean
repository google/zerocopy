-- Standalone Lean 4.34.1 mechanization of ISA formalization confidence polarity laws:
-- (1) one-way hardware-to-spec refinement + demonic 1-safety transfer,
-- (2) staged Pass-1 core vs. Pass-2 reference ISA correspondence composition,
-- (3) Dual-Choice 2-safety leakage noninterference vs. McLean's Refinement Paradox,
-- (4) total decidable post-link binary certificate soundness.
-- Verified with zero `sorry`, zero `native_decide`, and zero axioms (`[]`).

namespace IsaConfidenceSpecCheck

/-- Total 4-way architectural step outcome (forbids silent stuckness / empty choice). -/
inductive IsaFault where
  | undefined   -- Architectural UB / CONSTRAINED UNPREDICTABLE fault envelope
  | unsupported -- Valid ISA encoding outside a staged core opcode subset
  deriving DecidableEq, Repr

inductive IsaStepOutcome (State Trap : Type) where
  | step (next : State)
  | trap (info : Trap)
  | halted (code : Nat)
  | fault (kind : IsaFault)
  deriving DecidableEq, Repr

/-- Nondeterministic ISA specification parameterized over legal hardware choice `Choice`. -/
structure IsaSpec (State Choice Instr Trap : Type) where
  decode : List UInt8 → Option (Instr × Nat) -- `none` means architectural `#UD`/illegal trap
  validChoice : State → Instr → Choice → Prop
  choiceNonEmpty : ∀ s i, ∃ c, validChoice s i c
  evalInst : State → Instr → Choice → IsaStepOutcome State Trap

/-- Decoder determinism and prefix-uniqueness (no two distinct `(ins, len)` match prefixes). -/
def PrefixUniqueDecode {Instr : Type} (decode : List UInt8 → Option (Instr × Nat)) : Prop :=
  ∀ b₁ b₂ ins₁ len₁ ins₂ len₂,
    decode b₁ = some (ins₁, len₁) →
    decode (b₁ ++ b₂) = some (ins₂, len₂) →
    len₁ ≤ b₁.length →
    ins₁ = ins₂ ∧ len₁ = len₂

/-- One-way hardware-to-spec refinement (`I_hw ⊆ I_spec`): every concrete outcome observed on
hardware for `(s, i)` is witnessed by some `c ∈ validChoice`. -/
def HardwareRefinesSpec {S C I T : Type} (spec : IsaSpec S C I T)
    (hwObs : S → I → IsaStepOutcome S T) : Prop :=
  ∀ s i, ∃ c, spec.validChoice s i c ∧ spec.evalInst s i c = hwObs s i

/-- Software 1-safety quantifies universally (demonically) over all admissible hardware choices,
forbidding `.fault` while permitting benign dead undefined outputs. -/
def SoftwareStepSafe {S C I T : Type} (spec : IsaSpec S C I T)
    (post : IsaStepOutcome S T → Prop) (s : S) (i : I) : Prop :=
  ∀ c, spec.validChoice s i c →
    (∀ k, spec.evalInst s i c ≠ .fault k) ∧ post (spec.evalInst s i c)

/-- Soundness of one-way hardware refinement + demonic software safety (`[]` zero axioms). -/
theorem silicon_safe_of_hardwareRefines_and_softwareSafe
    {S C I T : Type} {spec : IsaSpec S C I T}
    {hwObs : S → I → IsaStepOutcome S T} {post : IsaStepOutcome S T → Prop}
    (hHw : HardwareRefinesSpec spec hwObs)
    {s : S} {i : I} (hSw : SoftwareStepSafe spec post s i) :
    (∀ k, hwObs s i ≠ .fault k) ∧ post (hwObs s i) := by
  rcases hHw s i with ⟨c, hValid, hEq⟩
  have hStep := hSw c hValid
  rw [← hEq]
  exact hStep

/-- Staged Pass-1 core vs. Pass-2 reference ISA correspondence: `core` may fail closed to
`.fault .unsupported` outside supported opcodes, while every supported behavior over-approximates
`ref` (`I_ref ⊆ I_core`). -/
def StagedPass2Refines {S C₁ C₂ I T : Type}
    (ref : IsaSpec S C₁ I T) (core : IsaSpec S C₂ I T) : Prop :=
  ∀ s i,
    (∀ c₂, core.validChoice s i c₂ → core.evalInst s i c₂ ≠ .fault .unsupported) →
    ∀ c₁, ref.validChoice s i c₁ →
      ∃ c₂, core.validChoice s i c₂ ∧ core.evalInst s i c₂ = ref.evalInst s i c₁

/-- Transitive assurance composition across Pass-1 software safety, Pass-2 correspondence,
and hardware refinement (`[]` zero axioms). -/
theorem end_to_end_staged_isa_transfer
    {S C₁ C₂ I T : Type}
    {ref : IsaSpec S C₁ I T} {core : IsaSpec S C₂ I T}
    {hwObs : S → I → IsaStepOutcome S T} {post : IsaStepOutcome S T → Prop}
    (hPass2 : StagedPass2Refines ref core)
    (hPass3 : HardwareRefinesSpec ref hwObs)
    {s : S} {i : I} (hPass1 : SoftwareStepSafe core post s i) :
    (∀ k, hwObs s i ≠ .fault k) ∧ post (hwObs s i) := by
  have hSupported : ∀ c₂, core.validChoice s i c₂ → core.evalInst s i c₂ ≠ .fault .unsupported :=
    fun c₂ hc₂ => (hPass1 c₂ hc₂).1 .unsupported
  rcases hPass3 s i with ⟨c₁, hVal₁, hEqHw⟩
  rcases hPass2 s i hSupported c₁ hVal₁ with ⟨c₂, hVal₂, hEqCore⟩
  have hOut := hPass1 c₂ hVal₂
  rw [← hEqHw, ← hEqCore]
  exact hOut

/-- Dual-choice 2-safety leakage noninterference over `(spec, leak)`.
Quantifies independently over `c₁` and `c₂` so a refining microarchitecture cannot leak secrets
by resolving architectural nondeterminism as a function of secret state (McLean's Paradox). -/
def DualChoiceLeakNI {S C I T Pub Obs : Type}
    (spec : IsaSpec S C I T) (pubProj : S → Pub) (leak : S → I → C → Obs) (i : I) : Prop :=
  ∀ s₁ s₂ c₁ c₂,
    pubProj s₁ = pubProj s₂ →
    spec.validChoice s₁ i c₁ →
    spec.validChoice s₂ i c₂ →
    leak s₁ i c₁ = leak s₂ i c₂

/-- Deterministic hardware leakage refining `leak` preserves 2-safety noninterference whenever
`DualChoiceLeakNI` holds (`[]` zero axioms). -/
theorem hw_leak_ni_of_dualChoiceLeakNI
    {S C I T Pub Obs : Type}
    {spec : IsaSpec S C I T} {pubProj : S → Pub} {leak : S → I → C → Obs} {i : I}
    {hwLeak : S → Obs}
    (hHwLeak : ∀ s, ∃ c, spec.validChoice s i c ∧ hwLeak s = leak s i c)
    (hNI : DualChoiceLeakNI spec pubProj leak i) :
    ∀ s₁ s₂, pubProj s₁ = pubProj s₂ → hwLeak s₁ = hwLeak s₂ := by
  intro s₁ s₂ hPub
  rcases hHwLeak s₁ with ⟨c₁, hc₁, heq₁⟩
  rcases hHwLeak s₂ with ⟨c₂, hc₂, heq₂⟩
  rw [heq₁, heq₂]
  exact hNI s₁ s₂ c₁ c₂ hPub hc₁ hc₂

/-- Constructive McLean Paradox witness (`[]` zero axioms): naive same-choice 2-safety holds for
a secret-independent nondeterministic leakage spec `leak := fun _ c => c`, yet a secret-dependent
hardware refinement `hwLeak := fun secret => secret` violates constant-time noninterference. -/
theorem mclean_paradox_refutes_same_choice_ni :
    let leak : Bool → Bool → Bool := fun _ c => c
    let pubProj : Bool → Unit := fun _ => ()
    let hwLeak : Bool → Bool := fun s => s
    (∀ s₁ s₂ c, pubProj s₁ = pubProj s₂ → leak s₁ c = leak s₂ c) ∧
    (∀ s, ∃ c, hwLeak s = leak s c) ∧
    ¬ (∀ s₁ s₂, pubProj s₁ = pubProj s₂ → hwLeak s₁ = hwLeak s₂) := by
  refine ⟨fun _ _ _ _ => rfl, fun s => ⟨s, rfl⟩, ?_⟩
  intro hBad
  have hFalse : true = false := hBad true false rfl
  exact Bool.noConfusion hFalse

/-- Total decidable post-link binary certificate checker soundness (`[]` zero axioms). -/
def verifyPostLinkBytes {Bytes : Type} (check : Bytes → Bool) (safePred : Bytes → Prop)
    (_hSound : ∀ bs, check bs = true → safePred bs) (bs : Bytes) :
    Option { b : Bytes // check b = true } :=
  if h : check bs = true then some ⟨bs, h⟩ else none

theorem verifyPostLinkBytes_sound {Bytes : Type} {check : Bytes → Bool} {safePred : Bytes → Prop}
    (hSound : ∀ bs, check bs = true → safePred bs) {bs : Bytes}
    {cert : { b : Bytes // check b = true }}
    (hOk : verifyPostLinkBytes check safePred hSound bs = some cert) :
    safePred bs := by
  unfold verifyPostLinkBytes at hOk
  split at hOk
  case isTrue hCheck =>
    injection hOk with hCert
    exact hSound bs hCheck
  case isFalse =>
    contradiction

#print axioms silicon_safe_of_hardwareRefines_and_softwareSafe
#print axioms end_to_end_staged_isa_transfer
#print axioms hw_leak_ni_of_dualChoiceLeakNI
#print axioms mclean_paradox_refutes_same_choice_ni
#print axioms verifyPostLinkBytes_sound

end IsaConfidenceSpecCheck
