import ToyChecker.Extensional

/-!
# Certificates: moving trust from the tool to a fixed verifier

*One-sided certification* (`certChecker`, results R4a–R4e). A certifying
tool outputs, per program, either a certificate `w : W` or nothing. A fixed
trusted verifier `V : P → W → Bool` checks the certificate, and the framework
accepts `p` iff the tool produced some `w` with `V p w = true`; no output, or
a rejected certificate, means "reject", with no evidence required for the
rejection (as in proof-carrying code). If `V` is sound
(`V p w = true → good p`), the induced checker is sound *for every tool*,
whatever the tool does internally; conversely, if `V` is unsound, some tool
yields an unsound checker. Completeness is not transferred from the verifier
alone: the induced checker is complete on a fragment `F` iff the tool emits,
for every good program of `F`, a certificate that `V` accepts, which needs
both that such certificates exist (verifier completeness on `F`) and that
the tool finds them.

*Two-sided certification* (`twoSidedChecker`, result R4f). Here the tool
answers every program with a verdict plus evidence: a certificate for
`true`, a refutation for `false`, each checked by its own trusted verifier
(the shape of certifying algorithms for decision problems). If the framework
requires checked evidence for every answer on `F`, then soundness of both
verifiers forces the induced checker to be sound and complete on `F`: a tool
that answers `false` on a good program of `F` cannot supply a valid
refutation, so it is excluded rather than admitted.

Scope: certificates change *what the tool outputs*; they do not inspect how
the tool works. As a law on the induced Boolean behavior, "is induced by
some one-sided certifying tool for `V`" is exactly soundness with respect to
the `V`-certifiability predicate `fun p => ∃ w, V p w = true` (R4e). A
lookup table that stores precomputed valid certificates has exactly the same
output as an honest tool on the same finite set
(`cachedCertTool_eq_boundedHonestTool`), so certificates rule out *unsound*
tables but not tables as such.
-/

namespace Toy.Checker

universe u v

/-- `VerifierSound good V`: every certificate the verifier accepts for `p`
witnesses `good p`. Captures the trusted checker of a proof-carrying or
certifying-algorithm design. -/
def VerifierSound {P : Type u} {W : Type v} (good : P → Prop) (V : P → W → Bool) : Prop :=
  ∀ p w, V p w = true → good p

/-- `VerifierComplete good V`: every good program has some certificate the
verifier accepts. (The certificate need not be findable by any particular
tool.) -/
def VerifierComplete {P : Type u} {W : Type v} (good : P → Prop) (V : P → W → Bool) : Prop :=
  ∀ p, good p → ∃ w, V p w = true

/-- The Boolean checker induced by a one-sided certifying tool `t` and
verifier `V`: accept `p` iff `t p = some w` and `V p w = true`. Silence
(`none`) and rejected certificates both mean "reject"; no evidence is
required for a rejection. -/
def certChecker {P : Type u} {W : Type v} (V : P → W → Bool) (t : P → Option W) : P → Bool :=
  fun p =>
    match t p with
    | some w => V p w
    | none => false

/-! ## Toy instance: certificates for evenness are halves -/

/-- Toy verifier: `w` certifies `p` iff `w + w = p`. -/
def halfV : Nat → Nat → Bool := fun p w => w + w == p

/-- An unsound verifier that accepts every certificate. -/
def trustAllV : Nat → Unit → Bool := fun _ _ => true

/-- A verifier that accepts nothing. -/
def rejectAllV : Nat → Unit → Bool := fun _ _ => false

/-- Honest certifying tool: produce `p / 2` for even `p`. -/
def honestTool : Nat → Option Nat := fun p => if p % 2 = 0 then some (p / 2) else none

/-- Silent tool: never produces a certificate. -/
def silentTool : Nat → Option Nat := fun _ => none

/-- Lying tool: always claims the certificate `7`, regardless of input. -/
def lyingTool : Nat → Option Nat := fun _ => some 7

/-- Positive example: `halfV` is sound for `evenGood`. -/
theorem verifierSound_example_halfV : VerifierSound evenGood halfV := by
  intro p w h
  simp [halfV] at h
  unfold evenGood
  omega

/-- Negative example: `trustAllV` is not sound for `evenGood`. -/
theorem not_verifierSound_example_trustAllV : ¬ VerifierSound evenGood trustAllV := by
  intro h
  have := h 1 () rfl
  simp [evenGood] at this

/-- Positive example: `halfV` is complete for `evenGood`. -/
theorem verifierComplete_example_halfV : VerifierComplete evenGood halfV := by
  intro p hp
  refine ⟨p / 2, ?_⟩
  unfold evenGood at hp
  simp [halfV]
  omega

/-- Negative example: `rejectAllV` is not complete for `evenGood`. -/
theorem not_verifierComplete_example_rejectAllV : ¬ VerifierComplete evenGood rejectAllV := by
  intro h
  obtain ⟨_, hw⟩ := h 0 rfl
  simp [rejectAllV] at hw

/-- Examples for `certChecker`: the honest tool's checker accepts `4` and
rejects `3`; the lying tool's checker accepts only `14` (where its fixed
claim happens to be a valid certificate) and rejects `4`; the silent tool's
checker rejects `4`. -/
theorem certChecker_examples :
    certChecker halfV honestTool 4 = true ∧ certChecker halfV honestTool 3 = false ∧
    certChecker halfV lyingTool 14 = true ∧ certChecker halfV lyingTool 4 = false ∧
    certChecker halfV silentTool 4 = false := by
  decide

/-! ## Main statements -/

/-- R4a. If the verifier is sound, the checker induced by *any* certifying
tool is sound. -/
theorem certChecker_sound_of_verifierSound {P : Type u} {W : Type v} {good : P → Prop}
    {V : P → W → Bool} (hV : VerifierSound good V) (t : P → Option W) :
    Sound good (certChecker V t) := by
  intro p hp
  unfold certChecker at hp
  cases ht : t p with
  | none => rw [ht] at hp; exact Bool.noConfusion hp
  | some w => rw [ht] at hp; exact hV p w hp

/-- R4b. The verifier carries the trust: every certifying tool induces a
sound checker iff the verifier is sound. -/
theorem verifierSound_iff_forall_certChecker_sound {P : Type u} {W : Type v}
    (good : P → Prop) (V : P → W → Bool) :
    VerifierSound good V ↔ ∀ t : P → Option W, Sound good (certChecker V t) :=
  ⟨fun hV t => certChecker_sound_of_verifierSound hV t,
   fun h p w hV => h (fun _ => some w) p hV⟩

/-- R4b (part), explicit witness for the converse: if `V` accepts a
certificate `w` for a bad program `p`, the tool that always outputs `w`
induces an unsound checker. -/
theorem certChecker_const_not_sound_of_bad_certificate {P : Type u} {W : Type v}
    {good : P → Prop} {V : P → W → Bool} {p : P} {w : W}
    (hVpw : V p w = true) (hp : ¬ good p) :
    ¬ Sound good (certChecker V (fun _ => some w)) :=
  fun hs => hp (hs _ hVpw)

/-- R4c. Exact condition for completeness of the induced checker: it is
complete on `F` iff for every good `p` in `F` the tool outputs some
certificate that `V` accepts. This depends on both `V` and `t`: it implies
that `V` admits a certificate for every good program of `F`
(`verifierCompleteOn_of_certChecker_completeOn`), and it is not implied by
verifier completeness (R4d). -/
theorem certChecker_completeOn_iff {P : Type u} {W : Type v} (good F : P → Prop)
    (V : P → W → Bool) (t : P → Option W) :
    CompleteOn good F (certChecker V t) ↔
      ∀ p, good p → F p → ∃ w, t p = some w ∧ V p w = true := by
  constructor
  · intro hc p hg hF
    have hp := hc p hg hF
    unfold certChecker at hp
    cases ht : t p with
    | none => rw [ht] at hp; exact Bool.noConfusion hp
    | some w => rw [ht] at hp; exact ⟨w, rfl, hp⟩
  · intro h p hg hF
    obtain ⟨w, ht, hVw⟩ := h p hg hF
    unfold certChecker
    rw [ht]
    exact hVw

/-- R4e. Boolean image of one-sided certification: a Boolean checker is
induced by some certifying tool for `V` iff it is sound for the
`V`-certifiability predicate "has a certificate accepted by `V`". (That
predicate equals `good` when `V` is sound and complete for `good`, and is
stronger than `good` when `V` is sound but incomplete.) -/
theorem exists_certChecker_eq_iff_sound_certifiable {P : Type u} {W : Type v}
    (V : P → W → Bool) (c : P → Bool) :
    (∃ t : P → Option W, certChecker V t = c) ↔ Sound (fun p => ∃ w, V p w = true) c := by
  constructor
  · rintro ⟨t, rfl⟩ p hp
    unfold certChecker at hp
    cases ht : t p with
    | none => rw [ht] at hp; exact Bool.noConfusion hp
    | some w => rw [ht] at hp; exact ⟨w, hp⟩
  · intro hs
    refine ⟨fun p => @dite _ (c p = true) (inferInstance)
        (fun h => some (Classical.choose (hs p h))) (fun _ => none), ?_⟩
    funext p
    by_cases h : c p = true
    · simp [certChecker, h, Classical.choose_spec (hs p h)]
    · cases hcp : c p with
      | false => simp [certChecker, hcp]
      | true => exact absurd hcp h

/-- Completeness of the induced checker on `F` forces the verifier to admit a
certificate for every good program of `F`: no tool can make the pipeline
complete where `V` has no accepted certificate. -/
theorem verifierCompleteOn_of_certChecker_completeOn {P : Type u} {W : Type v}
    {good F : P → Prop} {V : P → W → Bool} {t : P → Option W}
    (h : CompleteOn good F (certChecker V t)) : ∀ p, good p → F p → ∃ w, V p w = true := by
  intro p hg hF
  have hp := h p hg hF
  unfold certChecker at hp
  cases ht : t p with
  | none => rw [ht] at hp; exact Bool.noConfusion hp
  | some w => rw [ht] at hp; exact ⟨w, hp⟩

/-- Example: with the verifier `rejectAllV` (no certificate is ever accepted),
no tool yields a checker complete on `n < 10`. -/
theorem no_tool_completeOn_rejectAllV (t : Nat → Option Unit) :
    ¬ CompleteOn evenGood (fun n => n < 10) (certChecker rejectAllV t) := by
  intro h
  obtain ⟨_, hw⟩ := verifierCompleteOn_of_certChecker_completeOn h 0 rfl (by decide)
  simp [rejectAllV] at hw

/-- `verifierCompleteOn_of_certChecker_completeOn` without its hypothesis: with
`rejectAllV` the conclusion fails on the fragment `n < 10`. -/
theorem cex_verifierCompleteOn_needs_completeOn :
    ¬ (∀ p, evenGood p → (fun n => n < 10) p → ∃ w, rejectAllV p w = true) := by
  intro h
  obtain ⟨_, hw⟩ := h 0 rfl (by decide)
  simp [rejectAllV] at hw

/-- The hypothesis of `verifierCompleteOn_of_certChecker_completeOn` holds for
the honest tool and `halfV` on all programs. -/
theorem nonvacuous_verifierCompleteOn_of_certChecker_completeOn :
    CompleteOn evenGood (fun _ => True) (certChecker halfV honestTool) := by
  intro p hp _
  have he : p % 2 = 0 := hp
  simp [certChecker, honestTool, he, halfV]
  omega

/-- If `V` is sound, the `V`-certifiability predicate implies `good`. -/
theorem certifiable_imp_good_of_verifierSound {P : Type u} {W : Type v} {good : P → Prop}
    {V : P → W → Bool} (hS : VerifierSound good V) (p : P) :
    (∃ w, V p w = true) → good p :=
  fun ⟨w, hw⟩ => hS p w hw

/-- If `V` is sound and complete for `good`, the `V`-certifiability predicate
is `good` itself. -/
theorem certifiable_eq_good_of_verifierSound_of_verifierComplete {P : Type u} {W : Type v}
    {good : P → Prop} {V : P → W → Bool} (hS : VerifierSound good V)
    (hC : VerifierComplete good V) : (fun p => ∃ w, V p w = true) = good := by
  funext p
  exact propext ⟨fun ⟨w, hw⟩ => hS p w hw, hC p⟩

/-- Example: `halfV`-certifiability is exactly `evenGood`. -/
theorem halfV_certifiable_eq_evenGood : (fun p => ∃ w, halfV p w = true) = evenGood :=
  certifiable_eq_good_of_verifierSound_of_verifierComplete
    verifierSound_example_halfV verifierComplete_example_halfV

/-! ## Certificate-caching lookup tables -/

/-- A certificate-caching lookup table: it stores the valid `halfV`
certificates of `0, 2, 4, 6, 8` and is silent elsewhere. -/
def cachedCertTool : Nat → Option Nat :=
  fun p => if p ∈ [0, 2, 4, 6, 8] then some (p / 2) else none

/-- An honest bounded certifying tool: it computes the certificate `p / 2`
for every even `p < 10` and is silent elsewhere. -/
def boundedHonestTool : Nat → Option Nat :=
  fun p => if p < 10 ∧ p % 2 = 0 then some (p / 2) else none

/-- The certificate-caching table and the honest bounded tool produce
identical outputs (certificates included) on every program, so no law on
certified outputs can separate them; both induce sound checkers for `halfV`
by R4a. -/
theorem cachedCertTool_eq_boundedHonestTool : cachedCertTool = boundedHonestTool := by
  funext p
  by_cases h : p < 10
  · have hall : ∀ q, q < 10 → cachedCertTool q = boundedHonestTool q := by decide
    exact hall p h
  · have h1 : ¬ (p ∈ [0, 2, 4, 6, 8]) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    have h2 : ¬ (p < 10 ∧ p % 2 = 0) := fun hh => h hh.1
    simp [cachedCertTool, boundedHonestTool, h1, h2]

/-! ## Counterexamples -/

/-- R4a without `hV`: with the unsound verifier `trustAllV`, the tool that
always outputs `()` induces an unsound checker. -/
theorem cex_certChecker_sound_needs_verifierSound :
    ¬ Sound evenGood (certChecker trustAllV (fun _ => some ())) := by
  intro h
  have := h 1 rfl
  simp [evenGood] at this

/-- `certChecker_const_not_sound_of_bad_certificate` without `hVpw`
(`halfV` rejects the certificate `0` for the bad program `1`): `hp` holds and
the conclusion fails, since the tool that always outputs `0` induces a sound
checker. -/
theorem cex_const_not_sound_needs_accepted_certificate :
    ¬ evenGood 1 ∧ ¬ ¬ Sound evenGood (certChecker halfV (fun _ => some 0)) := by
  refine ⟨by simp [evenGood], fun hns => hns (fun p hp => ?_)⟩
  simp [certChecker, halfV] at hp
  subst hp
  rfl

/-- `certChecker_const_not_sound_of_bad_certificate` without `hp` (`halfV`
accepts the certificate `2` for the good program `4`): `hVpw` holds and the
conclusion fails, since the tool that always outputs `2` induces a sound
checker. -/
theorem cex_const_not_sound_needs_bad_program :
    halfV 4 2 = true ∧ ¬ ¬ Sound evenGood (certChecker halfV (fun _ => some 2)) := by
  refine ⟨rfl, fun hns => hns (fun p hp => ?_)⟩
  simp [certChecker, halfV] at hp
  subst hp
  rfl

/-- R4d. Verifier soundness and verifier completeness do not give a
complete checker: `halfV` is sound and complete for `evenGood`, yet the
silent tool's induced checker is not complete on any fragment containing a
good program (here: all programs). -/
theorem cex_verifierSound_verifierComplete_not_completeOn :
    VerifierSound evenGood halfV ∧ VerifierComplete evenGood halfV ∧
    ¬ CompleteOn evenGood (fun _ => True) (certChecker halfV silentTool) := by
  refine ⟨verifierSound_example_halfV, verifierComplete_example_halfV, fun h => ?_⟩
  have := h 0 rfl trivial
  simp [certChecker, silentTool] at this

/-! ## Non-vacuity witnesses -/

/-- R4a hypothesis holds (`halfV` is sound); the lying tool is a legitimate
choice of `t`, and its induced checker accepts something. -/
theorem nonvacuous_certChecker_sound :
    VerifierSound evenGood halfV ∧ certChecker halfV lyingTool 14 = true :=
  ⟨verifierSound_example_halfV, by decide⟩

/-- `verifierSound_iff_forall_certChecker_sound` is non-degenerate: `halfV` is sound and `trustAllV` is not. -/
theorem nonvacuous_verifierSound_iff :
    VerifierSound evenGood halfV ∧ ¬ VerifierSound evenGood trustAllV :=
  ⟨verifierSound_example_halfV, not_verifierSound_example_trustAllV⟩

/-- Hypotheses of `certChecker_const_not_sound_of_bad_certificate` hold: `trustAllV` accepts `()` for the bad
program `1`. -/
theorem nonvacuous_certChecker_const_not_sound :
    trustAllV 1 () = true ∧ ¬ evenGood 1 :=
  ⟨rfl, by simp [evenGood]⟩

/-- R4c is non-degenerate: the right-hand side holds for the honest tool and
fails for the silent tool (fragment: all programs). -/
theorem nonvacuous_certChecker_completeOn_iff :
    (∀ p, evenGood p → True → ∃ w, honestTool p = some w ∧ halfV p w = true) ∧
    ¬ (∀ p, evenGood p → True → ∃ w, silentTool p = some w ∧ halfV p w = true) := by
  constructor
  · intro p hp _
    refine ⟨p / 2, ?_, ?_⟩
    · simp [honestTool, show p % 2 = 0 from hp]
    · unfold evenGood at hp
      simp [halfV]
      omega
  · intro h
    obtain ⟨w, hw, _⟩ := h 0 rfl trivial
    simp [silentTool] at hw

/-- R4e is non-degenerate: `evenExact` is sound for "has a `halfV`
certificate" and `acceptAll` is not. -/
theorem nonvacuous_exists_certChecker_eq_iff :
    Sound (fun p => ∃ w, halfV p w = true) evenExact ∧
    ¬ Sound (fun p => ∃ w, halfV p w = true) (acceptAll : Nat → Bool) := by
  constructor
  · intro p hp
    exact verifierComplete_example_halfV p (sound_example_evenExact p hp)
  · intro h
    obtain ⟨w, hw⟩ := h 1 rfl
    simp [halfV] at hw
    omega

/-! ## Two-sided certification -/

/-- `TwoSidedVerifiedOn Vpos Vneg F t`: on every program of the fragment `F`,
the two-sided tool `t` returns a verdict together with evidence that the
matching trusted verifier accepts: a certificate checked by `Vpos` when the
verdict is `true`, a refutation checked by `Vneg` when it is `false`.
Captures the law "every answer on `F` must come with checked evidence". -/
def TwoSidedVerifiedOn {P : Type u} {W : Type v} (Vpos Vneg : P → W → Bool) (F : P → Prop)
    (t : P → Bool × W) : Prop :=
  ∀ p, F p → ((t p).1 = true → Vpos p (t p).2 = true) ∧ ((t p).1 = false → Vneg p (t p).2 = true)

/-- The Boolean checker induced by a two-sided tool: accept `p` iff the
verdict is `true` and its certificate is accepted by `Vpos`. -/
def twoSidedChecker {P : Type u} {W : Type v} (Vpos : P → W → Bool) (t : P → Bool × W) :
    P → Bool :=
  fun p => (t p).1 && Vpos p (t p).2

/-- Toy refutation verifier: `w` refutes evenness of `p` iff `w + w + 1 = p`. -/
def oddV : Nat → Nat → Bool := fun p w => w + w + 1 == p

/-- Honest two-sided tool: verdict "even?" with evidence `p / 2` (a half for
even `p`, the refutation `(p - 1) / 2` for odd `p`). -/
def honestTwoSidedTool : Nat → Bool × Nat := fun p => (p % 2 == 0, p / 2)

/-- Silent two-sided tool: always answers `false` with the junk evidence `0`. -/
def silentTwoSidedTool : Nat → Bool × Nat := fun _ => (false, 0)

/-- Positive example: `oddV` is a sound refutation verifier (sound for the
predicate `¬ evenGood`). -/
theorem verifierSound_example_oddV : VerifierSound (fun p => ¬ evenGood p) oddV := by
  intro p w h
  simp [oddV] at h
  unfold evenGood
  omega

/-- Negative example: `halfV` is not a sound refutation verifier (it accepts
`0` as evidence for the even program `0`). -/
theorem not_verifierSound_example_halfV_neg : ¬ VerifierSound (fun p => ¬ evenGood p) halfV := by
  intro h
  exact h 0 0 rfl rfl

/-- Positive example: the honest two-sided tool's answers are verified on all
programs. -/
theorem twoSidedVerifiedOn_example_honest :
    TwoSidedVerifiedOn halfV oddV (fun _ => True) honestTwoSidedTool := by
  intro p _
  constructor
  · intro h
    simp [honestTwoSidedTool] at h
    simp [honestTwoSidedTool, halfV]
    omega
  · intro h
    simp [honestTwoSidedTool] at h
    simp [honestTwoSidedTool, oddV]
    omega

/-- Negative example: the silent two-sided tool's answer at the good program
`0` has no valid refutation. -/
theorem not_twoSidedVerifiedOn_example_silent :
    ¬ TwoSidedVerifiedOn halfV oddV (fun _ => True) silentTwoSidedTool := by
  intro h
  have := (h 0 trivial).2 rfl
  simp [silentTwoSidedTool, oddV] at this

/-- Examples for `twoSidedChecker`: the honest tool's checker accepts `4` and
rejects `3`; the silent tool's checker rejects `4`. -/
theorem twoSidedChecker_examples :
    twoSidedChecker halfV honestTwoSidedTool 4 = true ∧
    twoSidedChecker halfV honestTwoSidedTool 3 = false ∧
    twoSidedChecker halfV silentTwoSidedTool 4 = false := by
  decide

/-- R4f. Two-sided certification with checked answers on `F`: if the
certificate verifier `Vpos` is sound for `good`, the refutation verifier
`Vneg` is sound for `¬ good`, and every answer of the tool on `F` carries
evidence its verifier accepts, then the induced checker is sound (everywhere)
and complete on `F`. -/
theorem twoSidedChecker_sound_completeOn_of_verifiedOn {P : Type u} {W : Type v}
    {good F : P → Prop} {Vpos Vneg : P → W → Bool} {t : P → Bool × W}
    (hpos : VerifierSound good Vpos) (hneg : VerifierSound (fun p => ¬ good p) Vneg)
    (hver : TwoSidedVerifiedOn Vpos Vneg F t) :
    Sound good (twoSidedChecker Vpos t) ∧ CompleteOn good F (twoSidedChecker Vpos t) := by
  refine ⟨fun p hp => ?_, fun p hg hF => ?_⟩
  · unfold twoSidedChecker at hp
    cases hb : (t p).1 with
    | false => rw [hb] at hp; exact Bool.noConfusion hp
    | true =>
      rw [hb, Bool.true_and] at hp
      exact hpos p (t p).2 hp
  · unfold twoSidedChecker
    cases hb : (t p).1 with
    | true =>
      rw [Bool.true_and]
      exact (hver p hF).1 hb
    | false =>
      have hvn : Vneg p (t p).2 = true := (hver p hF).2 hb
      exact absurd hg (hneg p (t p).2 hvn)

/-- R4f without `hpos`: the certificate verifier accepts everything, the
refutation verifier accepts nothing (hence is sound for `¬ evenGood`), the
tool always answers `true`; `hneg` and `hver` hold and the conclusion fails
(the induced checker accepts `1`). -/
theorem cex_twoSidedChecker_needs_pos_sound :
    VerifierSound (fun p => ¬ evenGood p) (fun (_ : Nat) (_ : Nat) => false) ∧
    TwoSidedVerifiedOn (fun (_ : Nat) (_ : Nat) => true) (fun (_ : Nat) (_ : Nat) => false)
      (fun _ => True) (fun _ => (true, 0)) ∧
    ¬ (Sound evenGood (twoSidedChecker (fun (_ : Nat) (_ : Nat) => true) (fun _ => (true, 0))) ∧
       CompleteOn evenGood (fun _ => True)
         (twoSidedChecker (fun (_ : Nat) (_ : Nat) => true) (fun _ => (true, 0)))) := by
  refine ⟨fun _ _ h => Bool.noConfusion h, fun _ _ => ⟨fun _ => rfl, fun h => Bool.noConfusion h⟩,
    fun h => ?_⟩
  have := h.1 1 rfl
  simp [evenGood] at this

/-- R4f without `hneg`: the refutation verifier accepts everything, the tool
always answers `false`; `hpos` and `hver` hold and the conclusion fails (the
induced checker rejects the good program `0`). -/
theorem cex_twoSidedChecker_needs_neg_sound :
    VerifierSound evenGood halfV ∧
    TwoSidedVerifiedOn halfV (fun (_ : Nat) (_ : Nat) => true) (fun _ => True)
      (fun _ => (false, 0)) ∧
    ¬ (Sound evenGood (twoSidedChecker halfV (fun _ => (false, 0))) ∧
       CompleteOn evenGood (fun _ => True) (twoSidedChecker halfV (fun _ => (false, 0)))) := by
  refine ⟨verifierSound_example_halfV, fun _ _ => ⟨fun h => Bool.noConfusion h, fun _ => rfl⟩,
    fun h => ?_⟩
  have := h.2 0 rfl trivial
  simp [twoSidedChecker] at this

/-- R4f without `hver`: both verifiers are sound and the silent tool's
induced checker rejects the good program `0`, so the conclusion fails (and
`hver` fails at `0`, by `not_twoSidedVerifiedOn_example_silent`). -/
theorem cex_twoSidedChecker_needs_verified :
    VerifierSound evenGood halfV ∧ VerifierSound (fun p => ¬ evenGood p) oddV ∧
    ¬ (Sound evenGood (twoSidedChecker halfV silentTwoSidedTool) ∧
       CompleteOn evenGood (fun _ => True) (twoSidedChecker halfV silentTwoSidedTool)) := by
  refine ⟨verifierSound_example_halfV, verifierSound_example_oddV, fun h => ?_⟩
  have := h.2 0 rfl trivial
  simp [twoSidedChecker, silentTwoSidedTool] at this

/-- R4f hypotheses hold: `halfV` and `oddV` are sound, and the honest
two-sided tool's answers are verified on all programs. -/
theorem nonvacuous_twoSidedChecker_sound_completeOn :
    VerifierSound evenGood halfV ∧ VerifierSound (fun p => ¬ evenGood p) oddV ∧
    TwoSidedVerifiedOn halfV oddV (fun _ => True) honestTwoSidedTool :=
  ⟨verifierSound_example_halfV, verifierSound_example_oddV, twoSidedVerifiedOn_example_honest⟩

end Toy.Checker
