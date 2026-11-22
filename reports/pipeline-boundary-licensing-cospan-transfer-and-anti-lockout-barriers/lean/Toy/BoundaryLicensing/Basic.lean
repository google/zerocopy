import Toy.BoundaryLicensing.Trust

set_option autoImplicit false

namespace Toy.BoundaryLicensing

/-- Epistemic status of a claim relative to available pipeline evidence. -/
inductive Status where
  | undetermined
  | supported
  | contradicted
  deriving DecidableEq, Repr

/-- Information order on `Status`: `.undetermined` is least; definite verdicts are incomparable. -/
def Status.le : Status → Status → Prop
  | .undetermined, _ => True
  | s₁, s₂ => s₁ = s₂

instance (s₁ s₂ : Status) : Decidable (Status.le s₁ s₂) :=
  match s₁, s₂ with
  | .undetermined, _ => isTrue trivial
  | .supported, s₂ => inferInstanceAs (Decidable (Status.supported = s₂))
  | .contradicted, s₂ => inferInstanceAs (Decidable (Status.contradicted = s₂))

/-- Negation involution on epistemic `Status`. -/
def Status.flip : Status → Status
  | .undetermined => .undetermined
  | .supported => .contradicted
  | .contradicted => .supported

/-- A status is definite when it is either `.supported` or `.contradicted`. -/
def Status.Definite (st : Status) : Prop :=
  st = .supported ∨ st = .contradicted

/-- Orientation of a directional model–system morphism or simulation (`m2s` = `src → tgt`, `s2m` = `tgt → src`). -/
inductive SimDir where
  | m2s
  | s2m
  deriving DecidableEq, Repr

/-- Positive claim shapes tracked across verification pipeline boundaries. -/
inductive PosShape where
  | univSafety
  | existWitness
  | termination
  | hyperSubsetClosed
  | hyperGeneral
  deriving DecidableEq, Repr

/-- Propositional atom identifier on system states. -/
abbrev Atom := Nat

/-- Atomic valuation on a single system state. -/
abbrev Valuation := Atom → Bool

/-- Infinite discrete-time observation trace of atomic valuations. -/
abbrev Trace := Nat → Valuation

/-- Total, initialized Kripke transition structure serving as the semantic system carrier. -/
structure Sys where
  State : Type
  init : State → Prop
  step : State → State → Prop
  val : State → Valuation
  init_nonempty : ∃ s, init s
  step_total : ∀ s, ∃ s', step s s'

/-- `π` is an infinite initialized execution path of `S`. -/
def IsExec (S : Sys) (π : Nat → S.State) : Prop :=
  S.init (π 0) ∧ ∀ n, S.step (π n) (π (n + 1))

/-- `τ` is the valuation trace induced by some infinite execution of `S`. -/
def HasTrace (S : Sys) (τ : Trace) : Prop :=
  ∃ π, IsExec S π ∧ ∀ n, τ n = S.val (π n)

/-- Positive negation-free propositional state specification built from `⊤`, `⊥`, atoms, `∧`, and `∨`. -/
inductive Spec where
  | top
  | bot
  | atom (a : Atom)
  | conj (φ ψ : Spec)
  | disj (φ ψ : Spec)
  deriving DecidableEq, Repr

/-- Evaluate positive propositional formula `P` on a single state valuation `v`. -/
def evalVal : Spec → Valuation → Bool
  | .top, _ => true
  | .bot, _ => false
  | .atom a, v => v a
  | .conj φ ψ, v => evalVal φ v && evalVal ψ v
  | .disj φ ψ, v => evalVal φ v || evalVal ψ v

/-- Truth of positive claim shape `sh` on system `S` at positive formula `P`. -/
def EvalShape : PosShape → Sys → Spec → Prop
  | .univSafety, S, P =>
      ∀ τ, HasTrace S τ → ∀ n, evalVal P (τ n) = true
  | .existWitness, S, P =>
      ∃ τ, HasTrace S τ ∧ ∃ n, evalVal P (τ n) = true
  | .termination, S, P =>
      ∀ τ, HasTrace S τ → ∃ n, evalVal P (τ n) = true
  | .hyperSubsetClosed, S, P =>
      ∀ τ₁ τ₂, HasTrace S τ₁ → HasTrace S τ₂ →
        evalVal P (τ₁ 0) = evalVal P (τ₂ 0) → ∀ n, evalVal P (τ₁ n) = evalVal P (τ₂ n)
  | .hyperGeneral, S, P =>
      ∀ τ₁, HasTrace S τ₁ → ∃ τ₂, HasTrace S τ₂ ∧
        evalVal P (τ₂ 0) = evalVal P (τ₁ 0) ∧ ∃ n, evalVal P (τ₂ n) ≠ evalVal P (τ₁ n)

/-- Classical two-valued semantic status of `(sh, P)` on `S`. -/
noncomputable def statusOf (S : Sys) (sh : PosShape) (P : Spec) : Status := by
  letI := Classical.propDecidable (EvalShape sh S P)
  exact if EvalShape sh S P then .supported else .contradicted

/-- Specification `P` is non-degenerate for `sh` when both `.supported` and `.contradicted` systems exist. -/
def NonDegen (sh : PosShape) (P : Spec) : Prop :=
  (∃ S : Sys, statusOf S sh P = .supported) ∧ (∃ S : Sys, statusOf S sh P = .contradicted)

/-- Pipeline boundary relation tags across capture, model, checker, rendering, and summary links. -/
inductive BoundaryRel where
  | none
  | hom (d : SimDir)
  | surjHom (d : SimDir)
  | posBoundedMorph (d : SimDir)
  | embed (d : SimDir)
  | traceRefine (d : SimDir)
  | stutterSim (d : SimDir)
  | wfStutterSim (d : SimDir)
  | lockStepSim (d : SimDir)
  | cospanCaptureLower
  | certFaithfulSoundPinned
  | termRoundTrip
  | litEntails
  deriving DecidableEq, Repr

/-- Positive transition-structure homomorphism `A → B` preserving `init`, `step`, and `true` atoms. -/
def IsHomFrom (A B : Sys) : Prop :=
  ∃ h : A.State → B.State,
    (∀ s, A.init s → B.init (h s)) ∧
    (∀ s s', A.step s s' → B.step (h s) (h s')) ∧
    (∀ s a, A.val s a = true → B.val (h s) a = true)

/-- Standard surjective positive homomorphism `A ↠ B` (`Function.Surjective h` plus `IsHomFrom`,
with no backward `init` or `step` lifting). -/
def IsSurjHomFrom (A B : Sys) : Prop :=
  ∃ h : A.State → B.State,
    Function.Surjective h ∧
    (∀ s, A.init s → B.init (h s)) ∧
    (∀ s s', A.step s s' → B.step (h s) (h s')) ∧
    (∀ s a, A.val s a = true → B.val (h s) a = true)

/-- Positive bounded morphism (p-morphism) `A → B`: forward preservation of `init`, `step`, and
`true` atoms together with backward `init` and `step` lifting. -/
def IsPosBoundedMorphFrom (A B : Sys) : Prop :=
  ∃ h : A.State → B.State,
    (∀ s, A.init s → B.init (h s)) ∧
    (∀ t, B.init t → ∃ s, A.init s ∧ h s = t) ∧
    (∀ s s', A.step s s' → B.step (h s) (h s')) ∧
    (∀ s t', B.step (h s) t' → ∃ s', A.step s s' ∧ h s' = t') ∧
    (∀ s a, A.val s a = true → B.val (h s) a = true)

/-- Induced-substructure embedding `A ↪ B` preserving and reflecting `init`, `step`, and exact valuations. -/
def IsEmbedFrom (A B : Sys) : Prop :=
  ∃ h : A.State → B.State,
    Function.Injective h ∧
    (∀ s, B.init (h s) ↔ A.init s) ∧
    (∀ s s', B.step (h s) (h s') ↔ A.step s s') ∧
    (∀ s, B.val (h s) = A.val s)

/-- Trace-set inclusion `Traces(A) ⊆ Traces(B)`. -/
def TraceIncl (A B : Sys) : Prop :=
  ∀ τ, HasTrace A τ → HasTrace B τ

/-- Non-empty stuttering step chain in `B` from `t` staying `R`-related to `s` before landing `R`-related to `s'`. -/
inductive PlusMatch {A B : Sys} (R : A.State → B.State → Prop) (s s' : A.State) :
    B.State → Prop where
  | step_done {t t' : B.State} : R s t → B.step t t' → R s' t' → PlusMatch R s s' t
  | step_stut {t u : B.State} : R s t → B.step t u → PlusMatch R s s' u → PlusMatch R s s' t

/-- Unranked stuttering simulation from `A` to `B` preserving exact state valuations. -/
def StutterSimFrom (A B : Sys) : Prop :=
  ∃ R : A.State → B.State → Prop,
    (∀ s₀, A.init s₀ → ∃ t₀, B.init t₀ ∧ R s₀ t₀) ∧
    (∀ s t, R s t → A.val s = B.val t) ∧
    (∀ s s' t, R s t → A.step s s' → R s' t ∨ PlusMatch R s s' t)

/-- Well-founded (`Nat`-ranked) stuttering simulation from `A` to `B`. -/
def WfStutterSimFrom (A B : Sys) : Prop :=
  ∃ (R : A.State → B.State → Prop) (rank : A.State → B.State → Nat),
    (∀ s₀, A.init s₀ → ∃ t₀, B.init t₀ ∧ R s₀ t₀) ∧
    (∀ s t, R s t → A.val s = B.val t) ∧
    (∀ s s' t, R s t → A.step s s' →
      (R s' t ∧ rank s' t < rank s t) ∨ PlusMatch R s s' t)

/-- Lock-step forward simulation from `A` to `B` preserving exact state valuations. -/
def LockStepSimFrom (A B : Sys) : Prop :=
  ∃ R : A.State → B.State → Prop,
    (∀ s₀, A.init s₀ → ∃ t₀, B.init t₀ ∧ R s₀ t₀) ∧
    (∀ s t, R s t → A.val s = B.val t) ∧
    (∀ s s' t, R s t → A.step s s' → ∃ t', B.step t t' ∧ R s' t')

/-- Three-leg cospan capture-and-lowering witness `ir ←(cap ∘ pass)— s0 —(lower)→ exec` on `Sys`. -/
def CospanSysWitness (ir exec : Sys) : Prop :=
  ∃ (s0 : Sys) (pass : Sys → Sys) (cap : Sys → Except Unit Sys) (lower : Sys → Sys),
    cap (pass s0) = .ok ir ∧
    lower s0 = exec ∧
    TraceIncl s0 (pass s0) ∧
    (∀ p q, cap p = .ok q → TraceIncl p q) ∧
    TraceIncl (lower s0) s0

/-- Certificate-verified, table-pinned trace-equivalence link between `src` and `tgt`,
backed by a `CertVerifier` satisfying `CertFaithful`, `CertSemSound`, and `TablePinned`. -/
def CertPinnedLink (src tgt : Sys) : Prop :=
  ∃ (Stmt Rule Cert : Type) (V : CertVerifier Stmt Rule Cert) (R : Rule)
    (denote : Stmt → Sys × Sys) (shipped : Nat → Option Stmt) (c : Cert) (name : Nat),
    (∀ φ, V.valid φ ↔
      TraceIncl (denote φ).1 (denote φ).2 ∧ TraceIncl (denote φ).2 (denote φ).1) ∧
    (∃ φ₀, V.official name = some φ₀ ∧ denote φ₀ = (src, tgt)) ∧
    CertFaithful V R ∧
    CertSemSound V R ∧
    TablePinned V.official shipped name ∧
    acceptsNamed V R shipped c name = true

/-- Printing-elaboration round-trip link backed by a left-inverse section
`∀ d : Dom, elabTerm (print d) = some d` over syntactic presentations denoting `src` and `tgt`. -/
def RoundTripLink (src tgt : Sys) : Prop :=
  ∃ (Dom Syn : Type) (print : Dom → Syn) (elabTerm : Syn → Option Dom)
    (denote : Dom → Sys) (d_src d_tgt : Dom),
    (∀ d : Dom, elabTerm (print d) = some d) ∧
    elabTerm (print d_src) = some d_tgt ∧
    TraceIncl src (denote d_src) ∧ TraceIncl (denote d_src) src ∧
    TraceIncl tgt (denote d_tgt) ∧ TraceIncl (denote d_tgt) tgt

/-- One-way positive entailment link across all positive claim shapes and specifications. -/
def LitEntailsLink (src tgt : Sys) : Prop :=
  ∀ sh P, EvalShape sh src P → EvalShape sh tgt P

/-- Concrete semantic realization of a boundary relation `rel` from `src` to `tgt`. -/
def Realizes : BoundaryRel → Sys → Sys → Prop
  | .none, _, _ => True
  | .hom .m2s, src, tgt => IsHomFrom src tgt
  | .hom .s2m, src, tgt => IsHomFrom tgt src
  | .surjHom .m2s, src, tgt => IsSurjHomFrom src tgt
  | .surjHom .s2m, src, tgt => IsSurjHomFrom tgt src
  | .posBoundedMorph .m2s, src, tgt => IsPosBoundedMorphFrom src tgt
  | .posBoundedMorph .s2m, src, tgt => IsPosBoundedMorphFrom tgt src
  | .embed .m2s, src, tgt => IsEmbedFrom src tgt
  | .embed .s2m, src, tgt => IsEmbedFrom tgt src
  | .traceRefine .m2s, src, tgt => TraceIncl src tgt
  | .traceRefine .s2m, src, tgt => TraceIncl tgt src
  | .stutterSim .m2s, src, tgt => StutterSimFrom src tgt
  | .stutterSim .s2m, src, tgt => StutterSimFrom tgt src
  | .wfStutterSim .m2s, src, tgt => WfStutterSimFrom src tgt
  | .wfStutterSim .s2m, src, tgt => WfStutterSimFrom tgt src
  | .lockStepSim .m2s, src, tgt => LockStepSimFrom src tgt
  | .lockStepSim .s2m, src, tgt => LockStepSimFrom tgt src
  | .cospanCaptureLower, src, tgt => CospanSysWitness src tgt
  | .certFaithfulSoundPinned, src, tgt => CertPinnedLink src tgt
  | .termRoundTrip, src, tgt => RoundTripLink src tgt
  | .litEntails, src, tgt => LitEntailsLink src tgt

/-- Decidable check whether `rel` preserves definite verdict `st ∈ {.supported, .contradicted}` for `sh`. -/
def preservesDefinite : BoundaryRel → PosShape → Bool → Bool
  | .none, _, _ => false
  | .hom .m2s, .existWitness, true => true
  | .hom .m2s, _, _ => false
  | .hom .s2m, .existWitness, false => true
  | .hom .s2m, _, _ => false
  | .surjHom .m2s, .existWitness, true => true
  | .surjHom .m2s, _, _ => false
  | .surjHom .s2m, .existWitness, false => true
  | .surjHom .s2m, _, _ => false
  | .posBoundedMorph .m2s, .univSafety, true => true
  | .posBoundedMorph .m2s, .existWitness, true => true
  | .posBoundedMorph .m2s, .termination, true => true
  | .posBoundedMorph .m2s, _, _ => false
  | .posBoundedMorph .s2m, .univSafety, false => true
  | .posBoundedMorph .s2m, .existWitness, false => true
  | .posBoundedMorph .s2m, .termination, false => true
  | .posBoundedMorph .s2m, _, _ => false
  | .embed .m2s, .existWitness, true => true
  | .embed .m2s, .univSafety, false => true
  | .embed .m2s, .termination, false => true
  | .embed .m2s, .hyperSubsetClosed, false => true
  | .embed .m2s, _, _ => false
  | .embed .s2m, .univSafety, true => true
  | .embed .s2m, .existWitness, false => true
  | .embed .s2m, .termination, true => true
  | .embed .s2m, .hyperSubsetClosed, true => true
  | .embed .s2m, _, _ => false
  | .traceRefine .m2s, .existWitness, true => true
  | .traceRefine .m2s, .univSafety, false => true
  | .traceRefine .m2s, .termination, false => true
  | .traceRefine .m2s, .hyperSubsetClosed, false => true
  | .traceRefine .m2s, _, _ => false
  | .traceRefine .s2m, .univSafety, true => true
  | .traceRefine .s2m, .existWitness, false => true
  | .traceRefine .s2m, .termination, true => true
  | .traceRefine .s2m, .hyperSubsetClosed, true => true
  | .traceRefine .s2m, _, _ => false
  | .stutterSim .m2s, .existWitness, true => true
  | .stutterSim .m2s, .univSafety, false => true
  | .stutterSim .m2s, _, _ => false
  | .stutterSim .s2m, .univSafety, true => true
  | .stutterSim .s2m, .existWitness, false => true
  | .stutterSim .s2m, _, _ => false
  | .wfStutterSim .m2s, .existWitness, true => true
  | .wfStutterSim .m2s, .univSafety, false => true
  | .wfStutterSim .m2s, .termination, false => true
  | .wfStutterSim .m2s, _, _ => false
  | .wfStutterSim .s2m, .univSafety, true => true
  | .wfStutterSim .s2m, .existWitness, false => true
  | .wfStutterSim .s2m, .termination, true => true
  | .wfStutterSim .s2m, _, _ => false
  | .lockStepSim .m2s, .existWitness, true => true
  | .lockStepSim .m2s, .univSafety, false => true
  | .lockStepSim .m2s, .termination, false => true
  | .lockStepSim .m2s, .hyperSubsetClosed, false => true
  | .lockStepSim .m2s, _, _ => false
  | .lockStepSim .s2m, .univSafety, true => true
  | .lockStepSim .s2m, .existWitness, false => true
  | .lockStepSim .s2m, .termination, true => true
  | .lockStepSim .s2m, .hyperSubsetClosed, true => true
  | .lockStepSim .s2m, _, _ => false
  | .cospanCaptureLower, .univSafety, true => true
  | .cospanCaptureLower, .existWitness, false => true
  | .cospanCaptureLower, .termination, true => true
  | .cospanCaptureLower, .hyperSubsetClosed, true => true
  | .cospanCaptureLower, _, _ => false
  | .certFaithfulSoundPinned, _, _ => true
  | .termRoundTrip, _, _ => true
  | .litEntails, _, true => true
  | .litEntails, _, false => false

/-- Total decidable directional status transformer across pipeline boundary `rel` for shape `sh`. -/
def transfer (rel : BoundaryRel) (sh : PosShape) : Status → Status
  | .undetermined => .undetermined
  | .supported => if preservesDefinite rel sh true then .supported else .undetermined
  | .contradicted => if preservesDefinite rel sh false then .contradicted else .undetermined

/-- Paired directional status transformer for claim pairs represented as `PosShape × PosShape`. -/
def transferIff (rel : BoundaryRel) (sh : PosShape × PosShape) (st : Status × Status) :
    Status × Status :=
  (transfer rel sh.1 st.1, transfer rel sh.2 st.2)

/-! ### Standard Valuations, Concrete System Builders, and Basic Lemmas -/

/-- All-true valuation (`∀ a, valTrue a = true`). -/
def valTrue : Valuation := fun _ => true

/-- All-false valuation (`∀ a, valFalse a = false`). -/
def valFalse : Valuation := fun _ => false

/-- Canonical active specification inspecting atom `0`. -/
def specAtom0 : Spec := .atom 0

/-- Canonical active specification inspecting atom `1`. -/
def specAtom1 : Spec := .atom 1

/-- Canonical multi-atom positive specification `atom 0 ∧ (atom 1 ∨ atom 2)`. -/
def specMultiPos : Spec := .conj (.atom 0) (.disj (.atom 1) (.atom 2))

/-- Canonical degenerate tautological specification `⊤`. -/
def specConstTrue : Spec := .top

/-- Canonical degenerate contradictory specification `⊥`. -/
def specConstFalse : Spec := .bot

/-- One-state system self-looping forever on constant valuation `v`. -/
def constSys (v : Valuation) : Sys where
  State := Unit
  init := fun _ => True
  step := fun _ _ => True
  val := fun _ => v
  init_nonempty := ⟨(), trivial⟩
  step_total := fun _ => ⟨(), trivial⟩

/-- Two-state deterministic system starting at valuation `v₀` and stepping forever to `v₁`. -/
def stepSys (v₀ v₁ : Valuation) : Sys where
  State := Bool
  init := fun b => b = false
  step := fun _ b' => b' = true
  val := fun b => if b then v₁ else v₀
  init_nonempty := ⟨false, rfl⟩
  step_total := fun _ => ⟨true, rfl⟩

/-- Finite disjoint union of `k + 1` two-step branches `(v₀, v₁)` starting at `v₀` and looping at `v₁`. -/
def maskedBranchSys {k : Nat} (branches : Fin (k + 1) → Valuation × Valuation) : Sys where
  State := Fin (k + 1) × Bool
  init := fun p => p.2 = false
  step := fun p q => q.1 = p.1 ∧ q.2 = true
  val := fun p => if p.2 then (branches p.1).2 else (branches p.1).1
  init_nonempty := ⟨(⟨0, Nat.zero_lt_succ k⟩, false), rfl⟩
  step_total := fun p => ⟨(p.1, true), rfl, rfl⟩

/-- Two-branch system emitting `[a₀, a₁, a₁, …]` and `[b₀, b₁, b₁, …]`. -/
def twoBranchSys (a₀ a₁ b₀ b₁ : Valuation) : Sys :=
  maskedBranchSys (k := 1) (fun i => if i.1 == 0 then (a₀, a₁) else (b₀, b₁))

/-- Three-branch system emitting `[a₀, a₁, …]`, `[b₀, b₁, …]`, and `[c₀, c₁, …]`. -/
def threeBranchSys (a₀ a₁ b₀ b₁ c₀ c₁ : Valuation) : Sys :=
  maskedBranchSys (k := 2) (fun i =>
    if i.1 == 0 then (a₀, a₁)
    else if i.1 == 1 then (b₀, b₁)
    else (c₀, c₁))

/-- Three-state finite-stuttering system starting at `v₀` and reaching `v₁` in either 1 or 2 steps. -/
def finiteStutterSys (v₀ v₁ : Valuation) : Sys where
  State := Fin 3
  init := fun s => s.1 = 0
  step := fun s s' =>
    (s.1 = 0 ∧ (s'.1 = 1 ∨ s'.1 = 2)) ∨
    (s.1 = 1 ∧ s'.1 = 2) ∨
    (s.1 = 2 ∧ s'.1 = 2)
  val := fun s => if s.1 == 2 then v₁ else v₀
  init_nonempty := ⟨⟨0, by omega⟩, rfl⟩
  step_total := fun s => by
    rcases s with ⟨n, hn⟩
    refine ⟨⟨2, by omega⟩, ?_⟩
    dsimp only
    omega

theorem evalVal_mono {P : Spec} {v₁ v₂ : Valuation}
    (hmono : ∀ a, v₁ a = true → v₂ a = true) (h : evalVal P v₁ = true) :
    evalVal P v₂ = true := by
  induction P with
  | top => rfl
  | bot => cases h
  | atom a => exact hmono a h
  | conj φ ψ ihφ ihψ =>
    simp only [evalVal, Bool.and_eq_true] at h ⊢
    exact ⟨ihφ h.1, ihψ h.2⟩
  | disj φ ψ ihφ ihψ =>
    simp only [evalVal, Bool.or_eq_true] at h ⊢
    exact h.elim (fun h1 => Or.inl (ihφ h1)) (fun h2 => Or.inr (ihψ h2))

theorem evalVal_all_true_of_valFalse {P : Spec} (hf : evalVal P valFalse = true) (v : Valuation) :
    evalVal P v = true :=
  evalVal_mono (fun a ha => by cases ha) hf

theorem evalVal_all_false_of_valTrue {P : Spec} (ht : evalVal P valTrue = false) (v : Valuation) :
    evalVal P v = false := by
  cases hv : evalVal P v with
  | false => rfl
  | true =>
    have hvt : evalVal P valTrue = true := @evalVal_mono P v valTrue (fun _ _ => rfl) hv
    rw [ht] at hvt
    cases hvt

theorem hasTrace_nonempty (S : Sys) : ∃ τ, HasTrace S τ := by
  obtain ⟨s₀, hs₀⟩ := S.init_nonempty
  have hnext : ∀ s, ∃ s', S.step s s' := S.step_total
  let next : S.State → S.State := fun s => Classical.choose (hnext s)
  let π : Nat → S.State := fun n => Nat.recOn n s₀ (fun _ cur => next cur)
  refine ⟨fun n => S.val (π n), π, ⟨hs₀, ?_⟩, fun _ => rfl⟩
  intro n
  exact Classical.choose_spec (hnext (π n))

theorem hasTrace_constSys_iff (v : Valuation) (τ : Trace) :
    HasTrace (constSys v) τ ↔ ∀ n, τ n = v := by
  constructor
  · rintro ⟨π, _, hτ⟩ n
    exact hτ n
  · intro h
    exact ⟨fun _ => (), ⟨trivial, fun _ => trivial⟩, h⟩

theorem hasTrace_stepSys_iff (v₀ v₁ : Valuation) (τ : Trace) :
    HasTrace (stepSys v₀ v₁) τ ↔ τ 0 = v₀ ∧ ∀ n, τ (n + 1) = v₁ := by
  constructor
  · rintro ⟨π, ⟨h0, hstep⟩, hτ⟩
    refine ⟨?_, ?_⟩
    · rw [hτ 0, h0]; rfl
    · intro n
      have h1 : π (n + 1) = true := hstep n
      rw [hτ (n + 1), h1]; rfl
  · rintro ⟨h0, hsucc⟩
    refine ⟨fun n => match n with | 0 => false | _ + 1 => true, ⟨rfl, fun _ => rfl⟩, ?_⟩
    intro n
    cases n with
    | zero => exact h0
    | succ m => exact hsucc m

theorem statusOf_eq_supported_iff (S : Sys) (sh : PosShape) (P : Spec) :
    statusOf S sh P = .supported ↔ EvalShape sh S P := by
  unfold statusOf
  by_cases h : EvalShape sh S P <;> simp [h]

theorem statusOf_eq_contradicted_iff (S : Sys) (sh : PosShape) (P : Spec) :
    statusOf S sh P = .contradicted ↔ ¬ EvalShape sh S P := by
  unfold statusOf
  by_cases h : EvalShape sh S P <;> simp [h]

theorem statusOf_definite (S : Sys) (sh : PosShape) (P : Spec) :
    (statusOf S sh P).Definite := by
  unfold statusOf Status.Definite
  by_cases h : EvalShape sh S P <;> simp [h]

theorem statusOf_ne_undetermined (S : Sys) (sh : PosShape) (P : Spec) :
    statusOf S sh P ≠ .undetermined := by
  rcases statusOf_definite S sh P with h | h <;> simp [h]

theorem status_le_iff (s₁ s₂ : Status) :
    Status.le s₁ s₂ ↔ s₁ = .undetermined ∨ s₁ = s₂ := by
  cases s₁ <;> cases s₂ <;> simp [Status.le]

theorem status_le_refl (s : Status) : Status.le s s := by
  cases s <;> simp [Status.le]

theorem status_le_trans {s₁ s₂ s₃ : Status} (h₁ : Status.le s₁ s₂) (h₂ : Status.le s₂ s₃) :
    Status.le s₁ s₃ := by
  cases s₁ <;> cases s₂ <;> cases s₃ <;> simp_all [Status.le]

theorem transfer_undetermined (rel : BoundaryRel) (sh : PosShape) :
    transfer rel sh .undetermined = .undetermined := rfl

theorem transfer_eq_self_or_undetermined (rel : BoundaryRel) (sh : PosShape) (st : Status) :
    transfer rel sh st = st ∨ transfer rel sh st = .undetermined := by
  cases st with
  | undetermined => exact Or.inl rfl
  | supported =>
    unfold transfer
    cases preservesDefinite rel sh true <;> simp
  | contradicted =>
    unfold transfer
    cases preservesDefinite rel sh false <;> simp

/-- Exact characterization of `CertPinnedLink`: existence of a faithful, semantically sound,
table-pinned certificate verifier accepting `(src, tgt)` is equivalent to bidirectional trace inclusion. -/
theorem certPinnedLink_iff_traceEquiv (src tgt : Sys) :
    CertPinnedLink src tgt ↔ TraceIncl src tgt ∧ TraceIncl tgt src := by
  constructor
  · rintro ⟨Stmt, Rule, Cert, V, R, denote, shipped, c, name,
      hval, ⟨φ₀, hoff₀, hden₀⟩, hfaith, hsem, hpin, hacc⟩
    obtain ⟨φ, hoff, hv⟩ := cert_trust_triple_sound V R shipped c name hfaith hsem hpin hacc
    rw [hoff₀] at hoff
    injection hoff with hφ
    subst hφ
    have htr := (hval φ₀).1 hv
    rw [hden₀] at htr
    exact htr
  · rintro ⟨htr1, htr2⟩
    let denote : Bool → Sys × Sys :=
      fun b => if b then (src, tgt) else (constSys valTrue, constSys valFalse)
    let V : CertVerifier Bool Unit Unit := {
      derivable := fun _ b => b = true
      valid := fun b => TraceIncl (denote b).1 (denote b).2 ∧ TraceIncl (denote b).2 (denote b).1
      check := fun _ _ b => b
      official := fun _ => some true
    }
    refine ⟨Bool, Unit, Unit, V, (), denote, (fun _ => some true), (), 0,
      (fun _ => Iff.rfl), ⟨true, rfl, rfl⟩, (fun _ b hb => hb), ?_, ⟨true, rfl, rfl⟩, rfl⟩
    intro b hb
    subst hb
    exact ⟨htr1, htr2⟩

/-- Exact characterization of `RoundTripLink`: existence of a left-inverse print/elaboration section
connecting presentations of `src` and `tgt` up to trace equivalence reduces to bidirectional trace inclusion. -/
theorem roundTripLink_iff_traceEquiv (src tgt : Sys) :
    RoundTripLink src tgt ↔ TraceIncl src tgt ∧ TraceIncl tgt src := by
  constructor
  · rintro ⟨Dom, Syn, print, elabTerm, denote, d_src, d_tgt,
      hsect, helab, hsrc1, hsrc2, htgt1, htgt2⟩
    have hsec_src := hsect d_src
    rw [helab] at hsec_src
    injection hsec_src with hd
    subst hd
    exact ⟨fun τ hτ => htgt2 τ (hsrc1 τ hτ), fun τ hτ => hsrc2 τ (htgt1 τ hτ)⟩
  · rintro ⟨htr1, htr2⟩
    refine ⟨Unit, Nat, (fun _ => 0), (fun n => if n == 0 then some () else none),
      (fun _ => src), (), (), (fun u => by cases u; rfl), rfl,
      (fun _ h => h), (fun _ h => h), htr2, htr1⟩

/-- Every boundary relation is reflexive on `Sys`. -/
theorem realizes_refl (rel : BoundaryRel) (S : Sys) : Realizes rel S S := by
  cases rel with
  | none => trivial
  | hom d =>
    cases d <;> exact ⟨id, fun _ h => h, fun _ _ h => h, fun _ _ h => h⟩
  | surjHom d =>
    cases d <;> exact ⟨id, fun s => ⟨s, rfl⟩, fun _ h => h, fun _ _ h => h, fun _ _ h => h⟩
  | posBoundedMorph d =>
    cases d <;> refine ⟨id, fun _ h => h, fun t ht => ⟨t, ht, rfl⟩,
      fun _ _ h => h, fun _ t' ht' => ⟨t', ht', rfl⟩, fun _ _ h => h⟩
  | embed d =>
    cases d <;> exact ⟨id, fun _ _ h => h, fun _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => rfl⟩
  | traceRefine d =>
    cases d <;> exact fun _ h => h
  | stutterSim d =>
    cases d <;> refine ⟨Eq, fun s hs => ⟨s, hs, rfl⟩, fun _ _ h => h ▸ rfl, ?_⟩
    all_goals
      intro s s' t hR hstep
      subst hR
      exact Or.inr (.step_done rfl hstep rfl)
  | wfStutterSim d =>
    cases d <;> refine ⟨Eq, fun _ _ => 0, fun s hs => ⟨s, hs, rfl⟩, fun _ _ h => h ▸ rfl, ?_⟩
    all_goals
      intro s s' t hR hstep
      subst hR
      exact Or.inr (.step_done rfl hstep rfl)
  | lockStepSim d =>
    cases d <;> refine ⟨Eq, fun s hs => ⟨s, hs, rfl⟩, fun _ _ h => h ▸ rfl, ?_⟩
    all_goals
      intro s s' t hR hstep
      subst hR
      exact ⟨s', hstep, rfl⟩
  | cospanCaptureLower =>
    refine ⟨S, id, Except.ok, id, rfl, rfl, fun _ h => h, ?_, fun _ h => h⟩
    intro p q hok
    cases hok
    exact fun _ h => h
  | certFaithfulSoundPinned =>
    exact (certPinnedLink_iff_traceEquiv S S).2 ⟨fun _ h => h, fun _ h => h⟩
  | termRoundTrip =>
    exact (roundTripLink_iff_traceEquiv S S).2 ⟨fun _ h => h, fun _ h => h⟩
  | litEntails =>
    exact fun _ _ h => h

/-! ### Characterization of `NonDegen` and Core Definition Examples -/

theorem evalShape_constSys_valTrue (P : Spec) (ht : evalVal P valTrue = true) :
    EvalShape .univSafety (constSys valTrue) P ∧
    EvalShape .existWitness (constSys valTrue) P ∧
    EvalShape .termination (constSys valTrue) P ∧
    EvalShape .hyperSubsetClosed (constSys valTrue) P ∧
    ¬ EvalShape .hyperGeneral (constSys valTrue) P := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro τ hτ n
    rw [(hasTrace_constSys_iff valTrue τ).1 hτ n, ht]
  · refine ⟨fun _ => valTrue, (hasTrace_constSys_iff valTrue _).2 (fun _ => rfl), 0, ht⟩
  · intro τ hτ
    exact ⟨0, by rw [(hasTrace_constSys_iff valTrue τ).1 hτ 0, ht]⟩
  · intro τ₁ τ₂ h₁ h₂ _ n
    rw [(hasTrace_constSys_iff valTrue τ₁).1 h₁ n, (hasTrace_constSys_iff valTrue τ₂).1 h₂ n]
  · intro hgni
    have htr : HasTrace (constSys valTrue) (fun _ => valTrue) :=
      (hasTrace_constSys_iff valTrue _).2 (fun _ => rfl)
    obtain ⟨τ₂, h₂, _, n, hneq⟩ := hgni _ htr
    rw [(hasTrace_constSys_iff valTrue τ₂).1 h₂ n] at hneq
    exact hneq rfl

theorem evalShape_constSys_valFalse (P : Spec) (hf : evalVal P valFalse = false) :
    ¬ EvalShape .univSafety (constSys valFalse) P ∧
    ¬ EvalShape .existWitness (constSys valFalse) P ∧
    ¬ EvalShape .termination (constSys valFalse) P ∧
    EvalShape .hyperSubsetClosed (constSys valFalse) P ∧
    ¬ EvalShape .hyperGeneral (constSys valFalse) P := by
  have htr : HasTrace (constSys valFalse) (fun _ => valFalse) :=
    (hasTrace_constSys_iff valFalse _).2 (fun _ => rfl)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have := h _ htr 0
    simp [hf] at this
  · rintro ⟨τ, hτ, n, hn⟩
    rw [(hasTrace_constSys_iff valFalse τ).1 hτ n, hf] at hn
    cases hn
  · intro h
    obtain ⟨n, hn⟩ := h _ htr
    rw [hf] at hn
    cases hn
  · intro τ₁ τ₂ h₁ h₂ _ n
    rw [(hasTrace_constSys_iff valFalse τ₁).1 h₁ n, (hasTrace_constSys_iff valFalse τ₂).1 h₂ n]
  · intro hgni
    obtain ⟨τ₂, h₂, _, n, hneq⟩ := hgni _ htr
    rw [(hasTrace_constSys_iff valFalse τ₂).1 h₂ n] at hneq
    exact hneq rfl

theorem hasTrace_maskedBranchSys_iff {k : Nat} (branches : Fin (k + 1) → Valuation × Valuation)
    (τ : Trace) :
    HasTrace (maskedBranchSys branches) τ ↔
      ∃ i : Fin (k + 1), τ 0 = (branches i).1 ∧ ∀ n, τ (n + 1) = (branches i).2 := by
  constructor
  · rintro ⟨π, ⟨h0, hstep⟩, hτ⟩
    refine ⟨(π 0).1, ?_, ?_⟩
    · have h0' : (π 0).2 = false := h0
      rw [hτ 0]; simp [maskedBranchSys, h0']
    · intro n
      have hind : ∀ m, (π m).1 = (π 0).1 := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih => exact (hstep m).1.trans ih
      have h1 : (π (n + 1)).2 = true := (hstep n).2
      have hi : (π (n + 1)).1 = (π 0).1 := hind (n + 1)
      rw [hτ (n + 1)]
      simp [maskedBranchSys, h1, hi]
  · rintro ⟨i, h0, hsucc⟩
    refine ⟨fun n => match n with | 0 => (i, false) | _ + 1 => (i, true),
      ⟨rfl, fun n => ⟨by cases n <;> rfl, rfl⟩⟩, ?_⟩
    intro n
    cases n with
    | zero => exact h0
    | succ m => exact hsucc m

theorem evalShape_twoBranch_gni (P : Spec)
    (hf : evalVal P valFalse = false) (ht : evalVal P valTrue = true) :
    ¬ EvalShape .hyperSubsetClosed (twoBranchSys valFalse valTrue valFalse valFalse) P ∧
    EvalShape .hyperGeneral (twoBranchSys valFalse valTrue valFalse valFalse) P := by
  let τ₀ : Trace := fun n => match n with | 0 => valFalse | _ + 1 => valTrue
  let τ₁ : Trace := fun _ => valFalse
  have hτ₀ : HasTrace (twoBranchSys valFalse valTrue valFalse valFalse) τ₀ := by
    unfold twoBranchSys
    rw [hasTrace_maskedBranchSys_iff]
    exact ⟨⟨0, by omega⟩, rfl, fun _ => rfl⟩
  have hτ₁ : HasTrace (twoBranchSys valFalse valTrue valFalse valFalse) τ₁ := by
    unfold twoBranchSys
    rw [hasTrace_maskedBranchSys_iff]
    exact ⟨⟨1, by omega⟩, rfl, fun _ => rfl⟩
  refine ⟨?_, ?_⟩
  · intro hsub
    have heq := hsub τ₀ τ₁ hτ₀ hτ₁ rfl 1
    simp [τ₀, τ₁, ht, hf] at heq
  · intro τ hτ
    unfold twoBranchSys at hτ
    rw [hasTrace_maskedBranchSys_iff] at hτ
    obtain ⟨i, hi0, hi1⟩ := hτ
    by_cases hz : i.1 = 0
    · refine ⟨τ₁, hτ₁, ?_, 1, ?_⟩
      · simp [τ₁, hi0, hz]
      · have h1 := hi1 0
        simp [hz] at h1
        simp [τ₁, h1, ht, hf]
    · have hone : i.1 = 1 := by have := i.2; omega
      refine ⟨τ₀, hτ₀, ?_, 1, ?_⟩
      · simp [τ₀, hi0, hone]
      · have h1 := hi1 0
        simp [hone] at h1
        simp [τ₀, h1, ht, hf]

/-- Exact algebraic characterization of `NonDegen sh P` across all positive formulas `P` and shapes `sh`:
`P` is non-degenerate iff `P` evaluates to `false` on `valFalse` and `true` on `valTrue`. -/
theorem nonDegen_iff_evalVal_false_true (sh : PosShape) (P : Spec) :
    NonDegen sh P ↔ evalVal P valFalse = false ∧ evalVal P valTrue = true := by
  constructor
  · rintro ⟨⟨S₁, h₁⟩, ⟨S₂, h₂⟩⟩
    rw [statusOf_eq_supported_iff] at h₁
    rw [statusOf_eq_contradicted_iff] at h₂
    cases hvf : evalVal P valFalse with
    | true =>
      exfalso
      have hall : ∀ v, evalVal P v = true := evalVal_all_true_of_valFalse hvf
      cases sh with
      | univSafety => exact h₂ (fun _ _ n => hall _)
      | existWitness =>
        obtain ⟨τ, hτ⟩ := hasTrace_nonempty S₂
        exact h₂ ⟨τ, hτ, 0, hall _⟩
      | termination => exact h₂ (fun _ _ => ⟨0, hall _⟩)
      | hyperSubsetClosed => exact h₂ (fun _ _ _ _ _ n => by rw [hall, hall])
      | hyperGeneral =>
        obtain ⟨τ, hτ⟩ := hasTrace_nonempty S₁
        obtain ⟨_, _, _, n, hneq⟩ := h₁ τ hτ
        rw [hall, hall] at hneq
        exact hneq rfl
    | false =>
      cases hvt : evalVal P valTrue with
      | true => exact ⟨rfl, rfl⟩
      | false =>
        exfalso
        have hall : ∀ v, evalVal P v = false := evalVal_all_false_of_valTrue hvt
        cases sh with
        | univSafety =>
          obtain ⟨τ, hτ⟩ := hasTrace_nonempty S₁
          have := h₁ τ hτ 0
          rw [hall] at this
          cases this
        | existWitness =>
          obtain ⟨_, _, _, hn⟩ := h₁
          rw [hall] at hn
          cases hn
        | termination =>
          obtain ⟨τ, hτ⟩ := hasTrace_nonempty S₁
          obtain ⟨_, hn⟩ := h₁ τ hτ
          rw [hall] at hn
          cases hn
        | hyperSubsetClosed => exact h₂ (fun _ _ _ _ _ n => by rw [hall, hall])
        | hyperGeneral =>
          obtain ⟨τ, hτ⟩ := hasTrace_nonempty S₁
          obtain ⟨_, _, _, n, hneq⟩ := h₁ τ hτ
          rw [hall, hall] at hneq
          exact hneq rfl
  · rintro ⟨hf, ht⟩
    have hvt := evalShape_constSys_valTrue P ht
    have hvf := evalShape_constSys_valFalse P hf
    have hgni := evalShape_twoBranch_gni P hf ht
    cases sh with
    | univSafety =>
      exact ⟨⟨constSys valTrue, (statusOf_eq_supported_iff _ _ _).2 hvt.1⟩,
             ⟨constSys valFalse, (statusOf_eq_contradicted_iff _ _ _).2 hvf.1⟩⟩
    | existWitness =>
      exact ⟨⟨constSys valTrue, (statusOf_eq_supported_iff _ _ _).2 hvt.2.1⟩,
             ⟨constSys valFalse, (statusOf_eq_contradicted_iff _ _ _).2 hvf.2.1⟩⟩
    | termination =>
      exact ⟨⟨constSys valTrue, (statusOf_eq_supported_iff _ _ _).2 hvt.2.2.1⟩,
             ⟨constSys valFalse, (statusOf_eq_contradicted_iff _ _ _).2 hvf.2.2.1⟩⟩
    | hyperSubsetClosed =>
      exact ⟨⟨constSys valTrue, (statusOf_eq_supported_iff _ _ _).2 hvt.2.2.2.1⟩,
             ⟨twoBranchSys valFalse valTrue valFalse valFalse,
              (statusOf_eq_contradicted_iff _ _ _).2 hgni.1⟩⟩
    | hyperGeneral =>
      exact ⟨⟨twoBranchSys valFalse valTrue valFalse valFalse,
              (statusOf_eq_supported_iff _ _ _).2 hgni.2⟩,
             ⟨constSys valTrue, (statusOf_eq_contradicted_iff _ _ _).2 hvt.2.2.2.2⟩⟩

/-! ### Proved Positive and Negative Examples for Core Definitions in `Basic.lean` -/

theorem status_le_pos : Status.le .undetermined .supported := trivial
theorem status_le_neg : ¬ Status.le .supported .contradicted := by decide

theorem status_definite_pos : Status.Definite .supported := Or.inl rfl
theorem status_definite_neg : ¬ Status.Definite .undetermined := by
  rintro (h | h) <;> cases h

theorem evalVal_pos : evalVal specMultiPos (fun a => a == 0 || a == 2) = true := rfl
theorem evalVal_neg : evalVal specMultiPos (fun a => a == 0) = false := rfl

theorem evalShape_univSafety_pos : EvalShape .univSafety (constSys valTrue) specAtom0 :=
  (evalShape_constSys_valTrue specAtom0 rfl).1

theorem evalShape_univSafety_neg : ¬ EvalShape .univSafety (constSys valFalse) specAtom0 :=
  (evalShape_constSys_valFalse specAtom0 rfl).1

theorem statusOf_pos : statusOf (constSys valTrue) .univSafety specAtom0 = .supported :=
  (statusOf_eq_supported_iff _ _ _).2 evalShape_univSafety_pos

theorem statusOf_neg : statusOf (constSys valFalse) .univSafety specAtom0 ≠ .supported := by
  rw [Ne, statusOf_eq_supported_iff]
  exact evalShape_univSafety_neg

theorem nonDegen_pos : NonDegen .univSafety specAtom0 :=
  (nonDegen_iff_evalVal_false_true .univSafety specAtom0).2 ⟨rfl, rfl⟩

theorem nonDegen_MultiPos : NonDegen .hyperSubsetClosed specMultiPos :=
  (nonDegen_iff_evalVal_false_true .hyperSubsetClosed specMultiPos).2 ⟨rfl, rfl⟩

theorem nonDegen_neg : ¬ NonDegen .univSafety specConstTrue := by
  rw [nonDegen_iff_evalVal_false_true]
  decide

theorem isSurjHomFrom_pos : IsSurjHomFrom (constSys valFalse) (constSys valTrue) :=
  ⟨id, fun u => ⟨u, rfl⟩, fun _ h => h, fun _ _ h => h, fun _ _ h => by cases h⟩

theorem isSurjHomFrom_neg : ¬ IsSurjHomFrom (constSys valTrue) (stepSys valTrue valTrue) := by
  rintro ⟨h, hsurj, _⟩
  obtain ⟨u₁, hu₁⟩ := hsurj true
  obtain ⟨u₂, hu₂⟩ := hsurj false
  cases u₁; cases u₂
  rw [hu₁] at hu₂
  cases hu₂

theorem isPosBoundedMorphFrom_pos : IsPosBoundedMorphFrom (constSys valFalse) (constSys valTrue) :=
  ⟨fun _ => (), fun _ _ => trivial, fun _ _ => ⟨(), trivial, rfl⟩,
   fun _ _ _ => trivial, fun _ _ _ => ⟨(), trivial, rfl⟩, fun _ _ h => by cases h⟩

theorem isPosBoundedMorphFrom_neg :
    ¬ IsPosBoundedMorphFrom (stepSys valFalse valTrue) (constSys valFalse) := by
  rintro ⟨h, _, _, _, _, hval⟩
  have h1 := hval true 0 rfl
  cases h1

theorem realizes_pos : Realizes (.hom .m2s) (constSys valFalse) (constSys valTrue) :=
  ⟨id, fun _ h => h, fun _ _ h => h, fun _ _ h => by cases h⟩

theorem realizes_neg : ¬ Realizes (.embed .m2s) (constSys valFalse) (constSys valTrue) := by
  rintro ⟨h, _, _, _, hval⟩
  have h0 := congrFun (hval ()) 0
  simp [constSys, valTrue, valFalse] at h0

theorem transfer_pos : transfer (.lockStepSim .s2m) .hyperSubsetClosed .supported = .supported := rfl
theorem transfer_neg : transfer (.lockStepSim .s2m) .hyperGeneral .supported ≠ .supported := by decide

theorem transferIff_pos :
    transferIff .termRoundTrip (.univSafety, .existWitness) (.supported, .supported) =
      (.supported, .supported) := rfl

theorem transferIff_neg :
    transferIff (.lockStepSim .s2m) (.univSafety, .existWitness) (.supported, .supported) ≠
      (.supported, .supported) := by decide

end Toy.BoundaryLicensing
