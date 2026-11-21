/-!
# Abstract capture bridge

A toy model of a verification pipeline. A verifier does not read the source
program `src` directly: some source-to-source passes run first, and a partial
translation `cap : S → Except E V` (the *capture*) turns the resulting program
into the verifier's IR. This file states, over arbitrary semantic domains, when a
verdict about the captured program transfers back to `src`.

Programs denote sets of observable runs (`Den B`, a predicate on runs). A
specification is a predicate on runs, and a denotation satisfies a specification
when every run does (`Sat`).
-/

namespace Toy.Capture

instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α) := fun a b =>
  match a, b with
  | .ok x, .ok y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (fun e => h (by cases e; rfl))
  | .error x, .error y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (fun e => h (by cases e; rfl))
  | .ok _, .error _ => isFalse (fun e => by cases e)
  | .error _, .ok _ => isFalse (fun e => by cases e)

/-- A denotation: the set of observable runs a program may exhibit, as a predicate
on runs. Deterministic programs denote one run per input; a nondeterministic or
over-approximating semantics may admit several. -/
abbrev Den (B : Type) : Type := B → Prop

/-- `Sat d spec`: every run admitted by `d` satisfies `spec`. This is the property a
verifier establishes about a program (for example, `spec` = "no run is UB"). -/
def Sat {B : Type} (d : Den B) (spec : B → Prop) : Prop :=
  ∀ b, d b → spec b

/-- `DenIncl d₁ d₂`: every run of `d₁` is a run of `d₂`. -/
def DenIncl {B : Type} (d₁ d₂ : Den B) : Prop :=
  ∀ b, d₁ b → d₂ b

/-- `DenEquiv d₁ d₂`: `d₁` and `d₂` admit the same runs. -/
def DenEquiv {B : Type} (d₁ d₂ : Den B) : Prop :=
  ∀ b, d₁ b ↔ d₂ b

/-- The capture is *faithful on its ok-image*: whenever it succeeds, the captured
program has exactly the runs of the source program. -/
def FaithfulOnOk {S V E B : Type} (semS : S → Den B) (semV : V → Den B)
    (cap : S → Except E V) : Prop :=
  ∀ p q, cap p = .ok q → DenEquiv (semV q) (semS p)

/-- The capture *over-approximates on its ok-image*: whenever it succeeds, every run
of the source program is a run of the captured program (the captured program may
admit more runs). -/
def OverApproxOnOk {S V E B : Type} (semS : S → Den B) (semV : V → Den B)
    (cap : S → Except E V) : Prop :=
  ∀ p q, cap p = .ok q → DenIncl (semS p) (semV q)

/-- A verifier, given as a verdict relation `verified q spec`, is *sound* for the
verifier semantics `semV` when each verdict is true of `semV q`. This names the
verdict; the semantic property is `Sat (semV q) spec`. -/
def VerifierSound {V B : Type} (semV : V → Den B) (verified : V → (B → Prop) → Prop) :
    Prop :=
  ∀ q spec, verified q spec → Sat (semV q) spec

/-- The exact verifier for `semV`: it accepts `(q, spec)` exactly when
`Sat (semV q) spec` holds. It is sound, and every sound verifier's verdicts are
among its verdicts. -/
def exactVerifier {V B : Type} (semV : V → Den B) : V → (B → Prop) → Prop :=
  fun q spec => Sat (semV q) spec

/-- Verification transfers through the capture: every verdict about a successfully
captured program is true of the source program. -/
def TransferSound {S V E B : Type} (semS : S → Den B) (cap : S → Except E V)
    (verified : V → (B → Prop) → Prop) : Prop :=
  ∀ p q spec, cap p = .ok q → verified q spec → Sat (semS p) spec

/-! ## Pipelines -/

/-- The tag a pass carries: `equiv` (claimed to preserve the denotation of every
program) or `erasing` (a refinement that may erase UB, so that it can lose source
runs). The tag itself carries no hypothesis; `EquivTagSound` states what an
`equiv` tag promises. -/
inductive Tag where
  | equiv
  | erasing
  deriving DecidableEq, Repr

/-- A source-to-source pass with its tag. -/
structure Pass (S : Type) where
  tag : Tag
  run : S → S

/-- Run a pipeline `P₁ … Pₖ` (head first) on a program. -/
def runPipe {S : Type} : List (Pass S) → S → S
  | [], p => p
  | P :: rest, p => runPipe rest (P.run p)

/-- `P`'s `equiv` tag is sound: if `P` is tagged `equiv`, it preserves the
denotation of every program (not only of the programs it is applied to). -/
def EquivTagSound {S B : Type} (semS : S → Den B) (P : Pass S) : Prop :=
  P.tag = .equiv → ∀ p, DenEquiv (semS (P.run p)) (semS p)

/-- `f` loses no run at `p`: every run of `p` is a run of `f p`. A pass whose
erasure precondition holds at `p` (so that it acts as an equivalence there)
satisfies this. -/
def LosesNoBehaviourAt {S B : Type} (semS : S → Den B) (f : S → S) (p : S) : Prop :=
  DenIncl (semS p) (semS (f p))

/-- Index `i` is in the erasing set of the pipeline: `i < pipe.length` and the
`i`-th pass (0-based) is tagged `erasing`. For a capture taken after the pipeline,
this is the set `E_k` of erasing passes before the capture point. -/
def InErasingSet {S : Type} (pipe : List (Pass S)) (i : Nat) : Prop :=
  ∃ h : i < pipe.length, (pipe[i]'h).tag = .erasing

/-- The erasing-set precondition at `src`: every pass in the erasing set loses no
run at its actual input, the program the preceding passes produce from `src`. -/
def ErasingSetPrecondition {S B : Type} (semS : S → Den B) (pipe : List (Pass S))
    (src : S) : Prop :=
  ∀ i (h : i < pipe.length), (pipe[i]'h).tag = .erasing →
    LosesNoBehaviourAt semS (pipe[i]'h).run (runPipe (pipe.take i) src)

/-- Every pass of the pipeline loses no run at its actual input. -/
def LosesNoBehaviourAtInputs {S B : Type} (semS : S → Den B) (pipe : List (Pass S))
    (src : S) : Prop :=
  ∀ i (h : i < pipe.length),
    LosesNoBehaviourAt semS (pipe[i]'h).run (runPipe (pipe.take i) src)

/-! ## Basic lemmas -/

/-- `ErasingSetPrecondition` is the per-index form of quantifying over the erasing
set `InErasingSet`. -/
theorem erasingSetPrecondition_iff_forall_inErasingSet {S B : Type} (semS : S → Den B)
    (pipe : List (Pass S)) (src : S) :
    ErasingSetPrecondition semS pipe src ↔
      ∀ i (hi : InErasingSet pipe i),
        LosesNoBehaviourAt semS (pipe[i]'hi.1).run (runPipe (pipe.take i) src) :=
  ⟨fun h i ⟨hlt, htag⟩ => h i hlt htag, fun h i hlt htag => h i ⟨hlt, htag⟩⟩

theorem DenIncl.trans {B : Type} {d₁ d₂ d₃ : Den B} (h₁ : DenIncl d₁ d₂)
    (h₂ : DenIncl d₂ d₃) : DenIncl d₁ d₃ :=
  fun b hb => h₂ b (h₁ b hb)

theorem Sat.of_denIncl {B : Type} {d₁ d₂ : Den B} {spec : B → Prop}
    (h : DenIncl d₁ d₂) (hs : Sat d₂ spec) : Sat d₁ spec :=
  fun b hb => hs b (h b hb)

/-- Faithfulness on the ok-image implies over-approximation on the ok-image. -/
theorem FaithfulOnOk.overApproxOnOk {S V E B : Type} {semS : S → Den B}
    {semV : V → Den B} {cap : S → Except E V} (h : FaithfulOnOk semS semV cap) :
    OverApproxOnOk semS semV cap :=
  fun p q hpq b hb => (h p q hpq b).2 hb

/-- The exact verifier is sound. -/
theorem exactVerifier_sound {V B : Type} (semV : V → Den B) :
    VerifierSound semV (exactVerifier semV) :=
  fun _ _ h => h

/-- Under the pipeline hypothesis, the source's runs are among the runs of the
pipeline output. -/
theorem denIncl_runPipe_of_losesNoBehaviourAtInputs {S B : Type} (semS : S → Den B) :
    ∀ (pipe : List (Pass S)) (src : S), LosesNoBehaviourAtInputs semS pipe src →
      DenIncl (semS src) (semS (runPipe pipe src))
  | [], _, _ => fun _ hb => hb
  | P :: rest, src, h => by
    have h0 : LosesNoBehaviourAt semS P.run src := h 0 (by simp)
    have hrest : LosesNoBehaviourAtInputs semS rest (P.run src) := by
      intro i hi
      have := h (i + 1) (by simp; omega)
      simpa [runPipe] using this
    exact DenIncl.trans h0 (denIncl_runPipe_of_losesNoBehaviourAtInputs semS rest _ hrest)

/-- `equiv`-tag soundness plus the erasing-set precondition give the pipeline
hypothesis. -/
theorem losesNoBehaviourAtInputs_of_erasingSet {S B : Type} (semS : S → Den B)
    (pipe : List (Pass S)) (src : S) (hEq : ∀ P ∈ pipe, EquivTagSound semS P)
    (hE : ErasingSetPrecondition semS pipe src) :
    LosesNoBehaviourAtInputs semS pipe src := by
  intro i hi
  cases htag : (pipe[i]'hi).tag with
  | erasing => exact hE i hi htag
  | equiv =>
    intro b hb
    exact (hEq _ (List.getElem_mem hi) htag _ b).2 hb

/-! ## Transfer theorems -/

/-- **Transfer to the capture input.** If the verifier is sound for `semV` and the
capture over-approximates on its ok-image, then a verdict about a successful
capture of `p` is true of `p` itself. Applied after a pipeline, `p` is the
pipeline output, not the original source. -/
theorem transfer_to_capture_input {S V E B : Type} (semS : S → Den B)
    (semV : V → Den B) (cap : S → Except E V) (verified : V → (B → Prop) → Prop)
    (hV : VerifierSound semV verified) (hcap : OverApproxOnOk semS semV cap)
    {p : S} {q : V} {spec : B → Prop}
    (hok : cap p = .ok q) (hver : verified q spec) : Sat (semS p) spec :=
  Sat.of_denIncl (hcap p q hok) (hV q spec hver)

/-- **Transfer through exactly one pass** (the one-pass instance of
`transfer_relative_to_erasingSet`). If the verifier is sound for `semV`, the
capture over-approximates on its ok-image, `P`'s `equiv` tag (if it has one) is
sound, and, if `P` is tagged `erasing`, `P` loses no run at `src`, then
`cap (P.run src) = ok q` and `verified q spec` imply `Sat (semS src) spec`. -/
theorem transfer_single_pass {S V E B : Type} (semS : S → Den B)
    (semV : V → Den B) (cap : S → Except E V) (verified : V → (B → Prop) → Prop)
    (P : Pass S) (src : S) (q : V) (spec : B → Prop)
    (hV : VerifierSound semV verified) (hcap : OverApproxOnOk semS semV cap)
    (hEq : EquivTagSound semS P)
    (hE : P.tag = .erasing → LosesNoBehaviourAt semS P.run src)
    (hok : cap (P.run src) = .ok q) (hver : verified q spec) :
    Sat (semS src) spec := by
  have hP : LosesNoBehaviourAt semS P.run src := by
    cases htag : P.tag with
    | erasing => exact hE htag
    | equiv => intro b hb; exact (hEq htag src b).2 hb
  exact Sat.of_denIncl hP (transfer_to_capture_input semS semV cap verified hV hcap hok hver)

/-- **Transfer through a pipeline, minimal form.** If the verifier is sound for
`semV`, the capture over-approximates on its ok-image, and every pass of the
pipeline (whatever its tag) loses no run at its actual input, then
`cap (runPipe pipe src) = ok q` and `verified q spec` imply `Sat (semS src) spec`. -/
theorem transfer_of_losesNoBehaviourAtInputs {S V E B : Type} (semS : S → Den B)
    (semV : V → Den B) (cap : S → Except E V) (verified : V → (B → Prop) → Prop)
    (pipe : List (Pass S)) (src : S) (q : V) (spec : B → Prop)
    (hV : VerifierSound semV verified) (hcap : OverApproxOnOk semS semV cap)
    (hpipe : LosesNoBehaviourAtInputs semS pipe src)
    (hok : cap (runPipe pipe src) = .ok q) (hver : verified q spec) :
    Sat (semS src) spec :=
  Sat.of_denIncl (denIncl_runPipe_of_losesNoBehaviourAtInputs semS pipe src hpipe)
    (transfer_to_capture_input semS semV cap verified hV hcap hok hver)

/-- **Transfer relative to the erasing set.** If the verifier is sound for `semV`,
the capture over-approximates on its ok-image, every `equiv`-tagged pass of the
pipeline preserves the denotation of every program, and every pass in the erasing
set `E_k` loses no run at its actual input, then `cap (runPipe pipe src) = ok q` and
`verified q spec` imply `Sat (semS src) spec`. -/
theorem transfer_relative_to_erasingSet {S V E B : Type} (semS : S → Den B)
    (semV : V → Den B) (cap : S → Except E V) (verified : V → (B → Prop) → Prop)
    (pipe : List (Pass S)) (src : S) (q : V) (spec : B → Prop)
    (hV : VerifierSound semV verified) (hcap : OverApproxOnOk semS semV cap)
    (hEq : ∀ P ∈ pipe, EquivTagSound semS P)
    (hE : ErasingSetPrecondition semS pipe src)
    (hok : cap (runPipe pipe src) = .ok q) (hver : verified q spec) :
    Sat (semS src) spec :=
  transfer_of_losesNoBehaviourAtInputs semS semV cap verified pipe src q spec hV hcap
    (losesNoBehaviourAtInputs_of_erasingSet semS pipe src hEq hE) hok hver

/-! ## Injectivity up to behavioural equivalence -/

/-- The capture is faithful at the source program `p`: if it succeeds on `p`, the
captured program has exactly the runs of `p`. `FaithfulOnOk` is `FaithfulAt` at
every program (`faithfulOnOk_iff_forall_faithfulAt`). -/
def FaithfulAt {S V E B : Type} (semS : S → Den B) (semV : V → Den B)
    (cap : S → Except E V) (p : S) : Prop :=
  ∀ q, cap p = .ok q → DenEquiv (semV q) (semS p)

theorem faithfulOnOk_iff_forall_faithfulAt {S V E B : Type} (semS : S → Den B)
    (semV : V → Den B) (cap : S → Except E V) :
    FaithfulOnOk semS semV cap ↔ ∀ p, FaithfulAt semS semV cap p :=
  ⟨fun h p q hq => h p q hq, fun h p q hq => h p q hq⟩

/-- **No verifier semantics is faithful on a merged pair.** If the capture maps
`p₁` and `p₂` to the same `q` and `p₁`, `p₂` do not have the same runs, then no
verifier semantics `semV` makes the capture faithful at both `p₁` and `p₂`. -/
theorem no_semV_faithful_at_merged_pair {S V E B : Type} (semS : S → Den B)
    (cap : S → Except E V) {p₁ p₂ : S} {q : V}
    (h₁ : cap p₁ = .ok q) (h₂ : cap p₂ = .ok q)
    (hdiff : ¬ DenEquiv (semS p₁) (semS p₂)) :
    ∀ semV : V → Den B,
      ¬ (FaithfulAt semS semV cap p₁ ∧ FaithfulAt semS semV cap p₂) := by
  intro semV ⟨f₁, f₂⟩
  exact hdiff fun b => ((f₁ q h₁ b).symm.trans (f₂ q h₂ b))

/-- Corollary: under the same hypotheses no `semV` makes the capture faithful on
its ok-image. -/
theorem not_faithfulOnOk_of_merged_pair {S V E B : Type} (semS : S → Den B)
    (cap : S → Except E V) {p₁ p₂ : S} {q : V}
    (h₁ : cap p₁ = .ok q) (h₂ : cap p₂ = .ok q)
    (hdiff : ¬ DenEquiv (semS p₁) (semS p₂)) :
    ∀ semV : V → Den B, ¬ FaithfulOnOk semS semV cap :=
  fun semV hf => no_semV_faithful_at_merged_pair semS cap h₁ h₂ hdiff semV
    ⟨hf p₁, hf p₂⟩

/-- **A faithful verifier semantics exists iff the capture merges only
behaviourally equivalent programs.** For every capture `cap`, some `semV` makes
`cap` faithful on its ok-image iff any two programs captured to the same `q` have
the same runs. -/
theorem exists_faithful_semV_iff_merges_only_equivalent {S V E B : Type}
    (semS : S → Den B) (cap : S → Except E V) :
    (∃ semV : V → Den B, FaithfulOnOk semS semV cap) ↔
      ∀ p₁ p₂ q, cap p₁ = .ok q → cap p₂ = .ok q → DenEquiv (semS p₁) (semS p₂) := by
  constructor
  · intro ⟨semV, hf⟩ p₁ p₂ q h₁ h₂ b
    exact ((hf _ _ h₁ b).symm.trans (hf _ _ h₂ b))
  · intro h
    refine ⟨fun q b => ∃ p, cap p = .ok q ∧ semS p b, ?_⟩
    intro p q hpq b
    constructor
    · intro ⟨p', hp', hb⟩
      exact (h p' p q hp' hpq b).1 hb
    · intro hb
      exact ⟨p, hpq, hb⟩

/-- **A verdict on a merged capture holds for both programs.** If verification
transfers through `cap` for the verdict relation `verified`, and `cap` maps `p₁`
and `p₂` to the same `q`, then every specification verified of `q` holds of both
`p₁` and `p₂`. So a specification that one of them violates is never verified of
`q`, even if the other satisfies it. -/
theorem verdict_on_merged_capture_holds_for_both {S V E B : Type} (semS : S → Den B)
    (cap : S → Except E V) (verified : V → (B → Prop) → Prop)
    (hT : TransferSound semS cap verified) {p₁ p₂ : S} {q : V} {spec : B → Prop}
    (h₁ : cap p₁ = .ok q) (h₂ : cap p₂ = .ok q) (hv : verified q spec) :
    Sat (semS p₁) spec ∧ Sat (semS p₂) spec :=
  ⟨hT p₁ q spec h₁ hv, hT p₂ q spec h₂ hv⟩

/-! ## Transfer soundness and over-approximation on the ok-image -/

/-- **Transfer soundness for every sound verifier iff over-approximation.** For
every capture `cap` (with arbitrary error type) and verifier semantics `semV`:
verification transfers through `cap` for every verdict relation that is sound for
`semV` iff `cap` over-approximates on its ok-image. Programs on which `cap` errors
impose no obligation. -/
theorem transferSound_all_sound_verifiers_iff_overApproxOnOk {S V E B : Type}
    (semS : S → Den B) (semV : V → Den B) (cap : S → Except E V) :
    (∀ verified : V → (B → Prop) → Prop, VerifierSound semV verified →
        TransferSound semS cap verified) ↔
      OverApproxOnOk semS semV cap := by
  constructor
  · intro h p q hpq b hb
    exact h (exactVerifier semV) (exactVerifier_sound semV) p q (semV q) hpq
      (fun _ hb' => hb') b hb
  · intro hcap verified hV p q spec hpq hv
    exact transfer_to_capture_input semS semV cap verified hV hcap hpq hv

/-- **Transfer soundness for the exact verifier iff over-approximation.** -/
theorem transferSound_exactVerifier_iff_overApproxOnOk {S V E B : Type}
    (semS : S → Den B) (semV : V → Den B) (cap : S → Except E V) :
    TransferSound semS cap (exactVerifier semV) ↔ OverApproxOnOk semS semV cap := by
  constructor
  · intro h p q hpq b hb
    exact h p q (semV q) hpq (fun _ hb' => hb') b hb
  · intro hcap p q spec hpq hv
    exact transfer_to_capture_input semS semV cap _ (exactVerifier_sound semV) hcap hpq hv

/-- A verdict relation that accepts nothing makes every capture transfer-sound:
transfer soundness relative to one fixed verifier is not a property of the capture
alone. -/
theorem transferSound_of_verifier_accepts_nothing {S V E B : Type} (semS : S → Den B)
    (cap : S → Except E V) : TransferSound semS cap (fun _ _ => False) :=
  fun _ _ _ _ h => h.elim

/-- A denotation over runs `I × O` is total: every input has at least one
outcome. -/
def Total {I O : Type} (d : Den (I × O)) : Prop :=
  ∀ i, ∃ o, d (i, o)

/-- A denotation over runs `I × O` is deterministic: every input has at most one
outcome. -/
def Det {I O : Type} (d : Den (I × O)) : Prop :=
  ∀ i o o', d (i, o) → d (i, o') → o = o'

/-- **Over-approximation collapses to faithfulness for total sources and
deterministic targets.** If every successfully captured source program is total
and every captured program is deterministic, then the capture over-approximates on
its ok-image iff it is faithful on its ok-image. -/
theorem faithfulOnOk_iff_overApproxOnOk_of_total_of_det {S V E I O : Type}
    (semS : S → Den (I × O)) (semV : V → Den (I × O)) (cap : S → Except E V)
    (htot : ∀ p q, cap p = .ok q → Total (semS p))
    (hdet : ∀ p q, cap p = .ok q → Det (semV q)) :
    FaithfulOnOk semS semV cap ↔ OverApproxOnOk semS semV cap := by
  constructor
  · exact FaithfulOnOk.overApproxOnOk
  · intro hcap p q hpq ⟨i, o⟩
    constructor
    · intro hv
      obtain ⟨o', ho'⟩ := htot p q hpq i
      have hv' := hcap p q hpq _ ho'
      have := hdet p q hpq i o o' hv hv'
      subst this
      exact ho'
    · intro hs
      exact hcap p q hpq _ hs

/-! ## Fail-closed and fail-open captures built from a translation on a fragment -/

/-- The fail-closed capture built from a translation `tr` on the fragment `M`:
translate programs in `M`, return the error `e` on every other program. -/
def failClosed {S V E : Type} (M : S → Prop) [DecidablePred M] (tr : S → V) (e : E)
    (p : S) : Except E V :=
  if M p then .ok (tr p) else .error e

/-- A fail-open capture built from `tr` on `M`: programs outside `M` are mapped by
a fallback `fb` (for example: defaulting, stringifying or swallowing the construct
that `tr` does not handle) instead of being rejected. -/
def failOpen {S V E : Type} (M : S → Prop) [DecidablePred M] (tr fb : S → V)
    (p : S) : Except E V :=
  if M p then .ok (tr p) else .ok (fb p)

/-- Extend a translation `tr` on the fragment `M` by a partial fallback `rest` on
the programs outside `M`. `failClosed` and `failOpen` are the instances with a
constant error and with a total fallback (`failClosed_eq_partialExtend`,
`failOpen_eq_partialExtend`). -/
def partialExtend {S V E : Type} (M : S → Prop) [DecidablePred M] (tr : S → V)
    (rest : S → Except E V) (p : S) : Except E V :=
  if M p then .ok (tr p) else rest p

theorem failClosed_eq_partialExtend {S V E : Type} (M : S → Prop) [DecidablePred M]
    (tr : S → V) (e : E) : failClosed M tr e = partialExtend M tr (fun _ => .error e) :=
  rfl

theorem failOpen_eq_partialExtend {S V E : Type} (M : S → Prop) [DecidablePred M]
    (tr fb : S → V) : failOpen (E := E) M tr fb = partialExtend M tr (fun p => .ok (fb p)) :=
  rfl

/-- A partial extension over-approximates on its ok-image iff `tr` over-approximates
on `M` and every program outside `M` on which `rest` succeeds is over-approximated
by that result. -/
theorem partialExtend_overApproxOnOk_iff {S V E B : Type} (semS : S → Den B)
    (semV : V → Den B) (M : S → Prop) [DecidablePred M] (tr : S → V)
    (rest : S → Except E V) :
    OverApproxOnOk semS semV (partialExtend M tr rest) ↔
      (∀ p, M p → DenIncl (semS p) (semV (tr p))) ∧
        (∀ p q, ¬ M p → rest p = .ok q → DenIncl (semS p) (semV q)) := by
  constructor
  · intro h
    refine ⟨fun p hp => h p (tr p) (by simp [partialExtend, hp]), ?_⟩
    intro p q hnp hrest
    exact h p q (by simp [partialExtend, hnp, hrest])
  · rintro ⟨h₁, h₂⟩ p q hpq
    unfold partialExtend at hpq
    by_cases hp : M p
    · simp [hp] at hpq; subst hpq; exact h₁ p hp
    · simp [hp] at hpq; exact h₂ p q hp hpq

/-- The fail-closed capture over-approximates on its ok-image iff `tr`
over-approximates on `M`; no condition is placed on programs outside `M`. -/
theorem failClosed_overApproxOnOk_iff {S V E B : Type} (semS : S → Den B)
    (semV : V → Den B) (M : S → Prop) [DecidablePred M] (tr : S → V) (e : E) :
    OverApproxOnOk semS semV (failClosed M tr e) ↔
      ∀ p, M p → DenIncl (semS p) (semV (tr p)) := by
  constructor
  · intro h p hp
    exact h p (tr p) (by simp [failClosed, hp])
  · intro h p q hpq
    unfold failClosed at hpq
    by_cases hp : M p
    · simp [hp] at hpq
      subst hpq
      exact h p hp
    · simp [hp] at hpq

/-- A fail-open capture over-approximates on its ok-image iff `tr`
over-approximates on `M` and the fallback over-approximates on every program
outside `M`. -/
theorem failOpen_overApproxOnOk_iff {S V E B : Type} (semS : S → Den B)
    (semV : V → Den B) (M : S → Prop) [DecidablePred M] (tr fb : S → V) :
    OverApproxOnOk semS semV (failOpen (E := E) M tr fb) ↔
      (∀ p, M p → DenIncl (semS p) (semV (tr p))) ∧
        (∀ p, ¬ M p → DenIncl (semS p) (semV (fb p))) := by
  constructor
  · intro h
    refine ⟨fun p hp => h p (tr p) (by simp [failOpen, hp]),
      fun p hp => h p (fb p) (by simp [failOpen, hp])⟩
  · intro ⟨h₁, h₂⟩ p q hpq
    unfold failOpen at hpq
    by_cases hp : M p
    · simp [hp] at hpq
      subst hpq
      exact h₁ p hp
    · simp [hp] at hpq
      subst hpq
      exact h₂ p hp

end Toy.Capture
