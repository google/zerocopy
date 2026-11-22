/-!
# Capture bridge definitions (copied)

The definitions and lemmas in this file are copied verbatim, the namespace being the
sole change (`Toy.Capture` to `Toy.LawRewrite.CaptureBridge`), from the corpus report
`fail-closed-ir-capture-soundness-erasing-pass-sets-and-metadata-injectivity`, file
`lean/Toy/Capture/Basic.lean` (Git blob `5e5d90b0cde9fd5ef3772f2543298cad654861b3`,
SHA-256 `c7a687dcf3b6e787cf01aaa4c1da2a0b34c9c78d61d2f164a81140119aaa8123`):
`Den` (lines 26-29), `Sat` (31-34), `DenIncl` (36-38), `OverApproxOnOk` (50-55),
`VerifierSound` (57-62), `TransferSound` (70-74), `Sat.of_denIncl` (142-144),
`transfer_to_capture_input` (186-195), `failClosed` (384-388) and
`failClosed_overApproxOnOk_iff` (433-448). They are copied rather than imported so
that this package has no dependency on another package.
-/

namespace Toy.LawRewrite.CaptureBridge

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

/-- Verification transfers through the capture: every verdict about a successfully
captured program is true of the source program. -/
def TransferSound {S V E B : Type} (semS : S → Den B) (cap : S → Except E V)
    (verified : V → (B → Prop) → Prop) : Prop :=
  ∀ p q spec, cap p = .ok q → verified q spec → Sat (semS p) spec

theorem Sat.of_denIncl {B : Type} {d₁ d₂ : Den B} {spec : B → Prop}
    (h : DenIncl d₁ d₂) (hs : Sat d₂ spec) : Sat d₁ spec :=
  fun b hb => hs b (h b hb)

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

/-- The fail-closed capture built from a translation `tr` on the fragment `M`:
translate programs in `M`, return the error `e` on every other program. -/
def failClosed {S V E : Type} (M : S → Prop) [DecidablePred M] (tr : S → V) (e : E)
    (p : S) : Except E V :=
  if M p then .ok (tr p) else .error e

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

end Toy.LawRewrite.CaptureBridge
