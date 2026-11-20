/-
  Toy.KernelTrust.Rings

  K3: rings of faithfulness certificates.

  A *verifier ring* is a cycle of nodes.  Each node has an object-level checker
  and a certificate checker for claims of the form "node `j` of this ring is
  faithful to the rule table".  The ring is closed when every node accepts a
  certificate for its successor.  All nodes share one rule table `R`.
-/
import KernelTrust.Layers

namespace Toy.KernelTrust

/-- Successor of node `i` on a ring of `n` nodes: `i + 1 (mod n)`. -/
def ringNext {n : Nat} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

/-- `k` steps around the ring from node `i`. -/
def ringIter {n : Nat} (i : Fin n) : Nat → Fin n
  | 0     => i
  | k + 1 => ringNext (ringIter i k)

theorem ringIter_val {n : Nat} (i : Fin n) (k : Nat) :
    (ringIter i k).val = (i.val + k) % n := by
  induction k with
  | zero => simp [ringIter, Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    simp only [ringIter, ringNext, ih]
    rw [Nat.mod_add_mod, Nat.add_assoc]

/-- Every node is reached from every node. -/
theorem ringIter_reach {n : Nat} (i j : Fin n) :
    ringIter i (j.val + n - i.val) = j := by
  apply Fin.ext
  rw [ringIter_val]
  have hi := i.isLt
  have hsum : i.val + (j.val + n - i.val) = j.val + n := by omega
  rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]

/-- One step, then `k` steps, is `k + 1` steps. -/
theorem ringIter_succ' {n : Nat} (j : Fin n) (k : Nat) :
    ringIter j (k + 1) = ringIter (ringNext j) k := by
  apply Fin.ext
  simp only [ringIter_val, ringNext]
  rw [Nat.mod_add_mod]
  have : j.val + (k + 1) = j.val + 1 + k := by omega
  rw [this]

/-- On a ring of at least two nodes, no node is its own successor. -/
theorem ringNext_ne_self {n : Nat} (hn : 2 ≤ n) (i : Fin n) : ringNext i ≠ i := by
  intro h
  have hv : (i.val + 1) % n = i.val := congrArg Fin.val h
  have hi := i.isLt
  by_cases hlt : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have he : i.val + 1 = n := by omega
    rw [he, Nat.mod_self] at hv
    omega

/-- Strictly between `0` and `n` steps around a ring of `n` nodes, a walk has
not returned to its start. -/
theorem ringIter_ne_self_of_pos_of_lt {n : Nat} (i : Fin n) (k : Nat) (h0 : 0 < k)
    (hk : k < n) : ringIter i k ≠ i := by
  intro heq
  have hv := congrArg Fin.val heq
  rw [ringIter_val] at hv
  have hi := i.isLt
  by_cases hsum : i.val + k < n
  · rw [Nat.mod_eq_of_lt hsum] at hv
    omega
  · have hm : (i.val + k) % n = i.val + k - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- A ring of `n` verifier nodes.

* `checker i` is node `i`'s object-level proof checker.
* `acceptsCert i m j = true` means: node `i` accepts the meta-certificate `m`
  for the claim "node `j` is faithful to the rule table".

The claim language is deliberately minimal: one claim per *ring member*; there
are no claims about checkers outside the ring.  Nothing ties `acceptsCert i` to
`checker i`; whether a node's certificate checking is as trustworthy as its
object-level checking is exactly what `FaithfulImpliesMetaSound` assumes. -/
structure VerifierRing (n : Nat) where
  checker     : Fin n → Checker
  MetaCert    : Fin n → Type
  acceptsCert : (i : Fin n) → MetaCert i → Fin n → Bool

/-- Node `i` accepts some certificate that its successor is faithful. -/
def LinkCertified {n : Nat} (V : VerifierRing n) (i : Fin n) : Prop :=
  ∃ m : V.MetaCert i, V.acceptsCert i m (ringNext i) = true

/-- The ring is closed: every link `i → i+1` is certified. -/
def RingClosed {n : Nat} (V : VerifierRing n) : Prop :=
  ∀ i : Fin n, LinkCertified V i

/-- Node `i` is **meta-sound** for rule table `R`: every faithfulness claim
*about a ring member* that node `i` accepts is true.

This is soundness relative to the ring's claim language.  When every ring
member is in fact faithful, every node is meta-sound whatever its certificate
checker does, a rubber stamp included (`ring_metaSound_of_all_faithful`). -/
def MetaSound {n : Nat} (V : VerifierRing n) (R : RuleSet) (i : Fin n) : Prop :=
  ∀ (m : V.MetaCert i) (j : Fin n), V.acceptsCert i m j = true → Faithful (V.checker j) R

/-- **The faithfulness-implies-meta-soundness assumption.**  Every node whose
*object-level* checker is faithful to `R` is also meta-sound, i.e. its
*certificate* checking is sound for faithfulness claims about ring members.

This is an assumption about the ring, not a theorem: nothing in
`VerifierRing` forces it (see
`metaSound_anchor_ring_fails_without_faithfulImpliesMetaSound`).  It packages
two things a real system would have to establish: the certificate checker is as
trustworthy as the verified kernel (for instance it *is* that kernel, run on a
formal statement of the claim), and the logic in which the claim is stated
proves only true faithfulness claims (a reflection principle).  See
`faithfulImpliesMetaSound_of_selfHosted_of_claimReflection`. -/
def FaithfulImpliesMetaSound {n : Nat} (V : VerifierRing n) (R : RuleSet) : Prop :=
  ∀ i : Fin n, Faithful (V.checker i) R → MetaSound V R i

/-- **Ring-relative vacuity of `MetaSound`.**  In any verifier ring whose
members are all faithful to `R`, every node is meta-sound and
`FaithfulImpliesMetaSound` holds, for *every* certificate checker, including
one that accepts every claim. -/
theorem ring_metaSound_of_all_faithful {n : Nat} (V : VerifierRing n) (R : RuleSet)
    (hAll : ∀ j, Faithful (V.checker j) R) :
    (∀ i, MetaSound V R i) ∧ FaithfulImpliesMetaSound V R :=
  ⟨fun _ _ j _ => hAll j, fun _ _ _ j _ => hAll j⟩

/-- A **self-hosted** ring: node `i` checks a faithfulness certificate for node
`j` by running its *own* object-level checker on the formula `enc j`, read as
the object-language encoding of "node `j` is faithful".  (The toy logic cannot
actually express faithfulness; `enc` is an uninterpreted encoding.) -/
def selfHostedRing {n : Nat} (C : Fin n → Checker) (enc : Fin n → Form) : VerifierRing n where
  checker := C
  MetaCert := fun i => (C i).Wit
  acceptsCert := fun i m j => (C i).accepts m [] (enc j)

/-- **Claim reflection** for an encoding: if the rule table derives the
encoding of "node `j` is faithful", then node `j` is faithful.  This is the
semantic substance hidden inside `FaithfulImpliesMetaSound` for self-hosted
rings. -/
def ClaimReflection {n : Nat} (R : RuleSet) (C : Fin n → Checker) (enc : Fin n → Form) : Prop :=
  ∀ j : Fin n, Derivable R [] (enc j) → Faithful (C j) R

/-- How `FaithfulImpliesMetaSound` can be discharged: in a self-hosted ring it
follows from claim reflection. -/
theorem faithfulImpliesMetaSound_of_selfHosted_of_claimReflection {n : Nat}
    {R : RuleSet} {C : Fin n → Checker} {enc : Fin n → Form}
    (hRefl : ClaimReflection R C enc) :
    FaithfulImpliesMetaSound (selfHostedRing C enc) R :=
  fun _ hF m j hAcc => hRefl j (hF m [] (enc j) hAcc)

/-- Claim reflection holds trivially for an encoding that the rules never
derive. -/
theorem claimReflection_of_encodings_underivable {n : Nat} {R : RuleSet}
    (C : Fin n → Checker) {enc : Fin n → Form} (h : ∀ j, ¬ Derivable R [] (enc j)) :
    ClaimReflection R C enc :=
  fun j hd => absurd hd (h j)

/-- An inconsistent self-hosting logic cannot reflect claims about an
unfaithful member: `badRules` derives every encoding, so claim reflection for
`badRules` forces every member to be faithful. -/
theorem not_claimReflection_badRules_of_unfaithful {n : Nat} (C : Fin n → Checker)
    (enc : Fin n → Form) (j : Fin n) (hU : ¬ Faithful (C j) badRules) :
    ¬ ClaimReflection badRules C enc :=
  fun h => hU (h j (badRules_derives_every_formula _))

/-! ## K3a — propagation from one meta-sound anchor -/

/-- **K3a (main statement).**  In a closed ring (`RingClosed V`), *assuming*
`FaithfulImpliesMetaSound V R`, if at least one node is meta-sound
(`∃ i₀, MetaSound V R i₀`), then every node's object-level checker is faithful
to `R`.

Hypothesis ledger: the anchor is necessary
(`three_unfaithful_checkers_close_faithfulness_ring`);
`FaithfulImpliesMetaSound` is necessary
(`metaSound_anchor_ring_fails_without_faithfulImpliesMetaSound`);
every link is necessary (`ring_with_uncertified_link_does_not_propagate`).
The conclusion is faithfulness only: it says nothing about the rules `R`
(`ring_of_faithful_checkers_over_unsound_rules_accepts_bot`).  Conversely, for
`n ≥ 1` the conclusion implies `FaithfulImpliesMetaSound` and every anchor
(`ring_metaSound_of_all_faithful`), so under `RingClosed` the two
assumptions together are exactly as strong as the conclusion.  For `n = 0` the
anchor hypothesis is unsatisfiable; for `n = 1` `FaithfulImpliesMetaSound` is
not needed. -/
theorem ring_all_faithful_of_metaSound_anchor_of_faithfulImpliesMetaSound
    {n : Nat} (V : VerifierRing n) (R : RuleSet)
    (hClosed : RingClosed V)
    (hFaithfulImpliesMetaSound : FaithfulImpliesMetaSound V R)
    (hAnchor : ∃ i₀ : Fin n, MetaSound V R i₀) :
    ∀ j : Fin n, Faithful (V.checker j) R := by
  obtain ⟨i₀, hA⟩ := hAnchor
  -- Walking `k` steps from the anchor: the node reached is meta-sound and its
  -- successor is faithful.
  have hstep : ∀ k : Nat,
      MetaSound V R (ringIter i₀ k) ∧ Faithful (V.checker (ringIter i₀ (k + 1))) R := by
    intro k
    induction k with
    | zero =>
      obtain ⟨m, hm⟩ := hClosed i₀
      exact ⟨hA, hA m _ hm⟩
    | succ k ih =>
      have hms := hFaithfulImpliesMetaSound _ ih.2
      obtain ⟨m, hm⟩ := hClosed (ringIter i₀ (k + 1))
      exact ⟨hms, hms m _ hm⟩
  intro j
  have hi := i₀.isLt
  have hk : (j.val + n - i₀.val) - 1 + 1 = j.val + n - i₀.val := by omega
  have h := (hstep ((j.val + n - i₀.val) - 1)).2
  rw [hk, ringIter_reach] at h
  exact h

/-- **K3a, `⊥` part** (derived from the K3a main statement).  If moreover the
rules are consistent, no node of the ring accepts `⊢ ⊥`.  (`SemSound R`
implies `Consistent R`, and `Consistent` is strictly weaker:
`ex_consistent_not_semSound_anyImpRules`.) -/
theorem ring_no_node_accepts_bot_of_metaSound_anchor_of_faithfulImpliesMetaSound_of_consistent
    {n : Nat} (V : VerifierRing n) (R : RuleSet)
    (hClosed : RingClosed V)
    (hFaithfulImpliesMetaSound : FaithfulImpliesMetaSound V R)
    (hAnchor : ∃ i₀ : Fin n, MetaSound V R i₀)
    (hConsistent : Consistent R) :
    ∀ (j : Fin n) (w : (V.checker j).Wit), (V.checker j).accepts w [] .bot = false := by
  intro j w
  cases h : (V.checker j).accepts w [] .bot
  · rfl
  · exact absurd ⟨w, h⟩ (not_acceptsBot_of_faithful_of_consistent
      (ring_all_faithful_of_metaSound_anchor_of_faithfulImpliesMetaSound V R hClosed
        hFaithfulImpliesMetaSound hAnchor j) hConsistent)

/-! ## Case analysis helpers -/

theorem fin2_cases {P : Fin 2 → Prop} (h0 : P 0) (h1 : P 1) : ∀ i, P i := by
  intro i
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1

theorem fin3_cases {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i, P i := by
  intro i
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1
  | ⟨2, _⟩ => exact h2

/-! ## Concrete rings -/

/-- A ring of three faithful checkers of different designs for the rule table
`R`: the recomputing certificate re-checker, the trace checker, and their
separate-artifact quorum.  It is self-hosted, and the faithfulness claim about
any node is encoded as the formula `⊥ → ⊥`.  Because every node derives that
formula, every certificate checker in this ring accepts every claim; the nodes
are meta-sound only because every member is faithful
(`ring_metaSound_of_all_faithful`). -/
def faithfulRing (R : RuleSet) : VerifierRing 3 :=
  selfHostedRing
    (fun i => match i with
      | 0 => recheckRecompute R
      | 1 => traceChecker R
      | 2 => quorum (recheckRecompute R) (traceChecker R))
    (fun _ => Form.top)

/-- Every node of `faithfulRing R` is faithful to `R`. -/
theorem faithfulRing_faithful (R : RuleSet) : ∀ i, Faithful ((faithfulRing R).checker i) R :=
  fin3_cases (recheckRecompute_faithful R) (traceChecker_faithful R)
    (quorum_faithful_left (recheckRecompute_faithful R))

/-- Every node of `faithfulRing R` is meta-sound (all its claims are true). -/
theorem faithfulRing_metaSound (R : RuleSet) : ∀ i, MetaSound (faithfulRing R) R i :=
  (ring_metaSound_of_all_faithful _ R (faithfulRing_faithful R)).1

/-- Three *unfaithful* checkers for the standard rules, self-hosted: the
accept-all checker, the derived-field-trusting re-checker, and the
missing-guard mutant.  The claim "node `j` is faithful" is encoded as the
atom `p_j`, which the (sound) standard rules do not derive. -/
def buggyRing : VerifierRing 3 :=
  selfHostedRing
    (fun i => match i with
      | 0 => acceptAll
      | 1 => recheckTrust stdRules
      | 2 => recheckNoHypGuard stdRules)
    (fun j => Form.var j.val)

/-- A two-node ring in which node 0 has an unfaithful object-level checker but
an honest certificate checker (it accepts only the true claim about node 1),
and node 1 has a faithful object-level checker but a rubber-stamp certificate
checker.  `FaithfulImpliesMetaSound` fails at node 1. -/
def rubberStampRing : VerifierRing 2 where
  checker := fun i => match i with
    | 0 => acceptAll
    | 1 => recheckRecompute stdRules
  MetaCert := fun _ => Unit
  acceptsCert := fun i _ j => match i with
    | 0 => decide (j = 1)
    | 1 => true

/-- A two-node ring with one uncertified link: node 0 (faithful) accepts no
certificate at all; node 1 (unfaithful) accepts only the true claim about
node 0. -/
def brokenLinkRing : VerifierRing 2 where
  checker := fun i => match i with
    | 0 => recheckRecompute stdRules
    | 1 => acceptAll
  MetaCert := fun _ => Unit
  acceptsCert := fun i _ j => match i with
    | 0 => false
    | 1 => decide (j = 0)

/-! ## K3a non-vacuity -/

/-- **K3a non-vacuity.**  All hypotheses of K3a hold together, for the
semantically sound standard rules, in `faithfulRing stdRules`. -/
theorem k3a_nonvacuous :
    RingClosed (faithfulRing stdRules) ∧
    FaithfulImpliesMetaSound (faithfulRing stdRules) stdRules ∧
    (∃ i₀, MetaSound (faithfulRing stdRules) stdRules i₀) ∧
    SemSound stdRules ∧
    Consistent stdRules :=
  ⟨fin3_cases ⟨topCert, by decide⟩ ⟨topTrace, by decide⟩ ⟨(topCert, topTrace), by decide⟩,
   (ring_metaSound_of_all_faithful _ stdRules (faithfulRing_faithful stdRules)).2,
   ⟨0, faithfulRing_metaSound stdRules 0⟩,
   stdRules_semSound, stdRules_consistent⟩

/-! ## K3b — three unfaithful checkers close a ring -/

theorem buggyRing_unfaithful : ∀ i, ¬ Faithful (buggyRing.checker i) stdRules :=
  fin3_cases ex_faithful_acceptAll_neg ex_faithful_recheckTrust_neg
    ex_faithful_recheckNoHypGuard_neg

/-- **K3b.**  The ring `buggyRing` of three checkers for the semantically sound
standard rules is closed (every node accepts a faithfulness certificate for
its successor), `FaithfulImpliesMetaSound` holds, and yet no node is faithful
and every node accepts `⊢ ⊥`.  The only K3a hypothesis that fails is the
anchor: no node is meta-sound. -/
theorem three_unfaithful_checkers_close_faithfulness_ring :
    SemSound stdRules ∧
    RingClosed buggyRing ∧
    FaithfulImpliesMetaSound buggyRing stdRules ∧
    (∀ i, ¬ MetaSound buggyRing stdRules i) ∧
    (∀ i, ¬ Faithful (buggyRing.checker i) stdRules) ∧
    (∀ i, (buggyRing.checker i).AcceptsBot) := by
  have hClosed : RingClosed buggyRing :=
    fin3_cases ⟨(), rfl⟩ ⟨lyingCert (.var 2), by decide⟩ ⟨bogusHypCert (.var 0), by decide⟩
  refine ⟨stdRules_semSound, hClosed, fun i hF => absurd hF (buggyRing_unfaithful i), ?_,
    buggyRing_unfaithful, ?_⟩
  · intro i hMS
    obtain ⟨m, hm⟩ := hClosed i
    exact buggyRing_unfaithful _ (hMS m _ hm)
  · exact fin3_cases ⟨(), rfl⟩ ⟨lyingCert .bot, by decide⟩ ⟨bogusHypCert .bot, by decide⟩

/-- **K3b at `n = 1` (self-verification of faithfulness).**  A single
unfaithful checker closes a ring of length one: the derived-field-trusting
re-checker accepts a certificate, checked by itself, for the encoded claim
that it is faithful.  A checker's acceptance of its own faithfulness
certificate is no evidence of faithfulness. -/
theorem unfaithful_checker_certifies_its_own_faithfulness :
    RingClosed (selfHostedRing (fun _ : Fin 1 => recheckTrust stdRules) (fun _ => Form.var 0)) ∧
    ¬ Faithful (recheckTrust stdRules) stdRules ∧
    (recheckTrust stdRules).AcceptsBot :=
  ⟨fun _ => ⟨lyingCert (.var 0), recheckTrust_accepts_everything _⟩,
   ex_faithful_recheckTrust_neg, ⟨lyingCert .bot, by decide⟩⟩

/-! ## K3c — a ring of faithful checkers over unsound rules -/

/-- **K3c.**  In `faithfulRing badRules` every hypothesis of K3a holds: the ring
is closed, every node is meta-sound (every certified claim is true), and
`FaithfulImpliesMetaSound` holds.  Accordingly every node is faithful to
`badRules`.  Yet every node accepts `⊢ ⊥`, because `badRules` is not
semantically sound.  A faithfulness ring is blind to errors in the rules.
(The certificate checkers here accept every claim; meta-soundness holds only
because every member is faithful.) -/
theorem ring_of_faithful_checkers_over_unsound_rules_accepts_bot :
    RingClosed (faithfulRing badRules) ∧
    (∀ i, MetaSound (faithfulRing badRules) badRules i) ∧
    FaithfulImpliesMetaSound (faithfulRing badRules) badRules ∧
    (∀ i, Faithful ((faithfulRing badRules).checker i) badRules) ∧
    (∀ i, ((faithfulRing badRules).checker i).AcceptsBot) ∧
    ¬ SemSound badRules :=
  ⟨fin3_cases ⟨topCert, by decide⟩ ⟨topTrace, by decide⟩ ⟨(topCert, topTrace), by decide⟩,
   faithfulRing_metaSound badRules,
   (ring_metaSound_of_all_faithful _ badRules (faithfulRing_faithful badRules)).2,
   faithfulRing_faithful badRules,
   fin3_cases ⟨badBotCert, by decide⟩ ⟨badBotTrace, by decide⟩
     ⟨(badBotCert, badBotTrace), by decide⟩,
   ex_semSound_badRules_neg.1⟩

/-! ## Tightness of the remaining K3a hypotheses -/

/-- **`FaithfulImpliesMetaSound` is necessary for K3a.**  In `rubberStampRing`
the ring is closed and node 0 is a meta-sound anchor, but
`FaithfulImpliesMetaSound` fails (node 1 is faithful and not meta-sound), and
the conclusion of K3a fails: node 0 is not faithful and accepts `⊢ ⊥`, for the
semantically sound standard rules. -/
theorem metaSound_anchor_ring_fails_without_faithfulImpliesMetaSound :
    SemSound stdRules ∧
    RingClosed rubberStampRing ∧
    MetaSound rubberStampRing stdRules 0 ∧
    ¬ FaithfulImpliesMetaSound rubberStampRing stdRules ∧
    ¬ Faithful (rubberStampRing.checker 0) stdRules ∧
    (rubberStampRing.checker 0).AcceptsBot := by
  have hF1 : Faithful (rubberStampRing.checker 1) stdRules := recheckRecompute_faithful stdRules
  have hU0 : ¬ Faithful (rubberStampRing.checker 0) stdRules := ex_faithful_acceptAll_neg
  refine ⟨stdRules_semSound, fin2_cases ⟨(), rfl⟩ ⟨(), rfl⟩, ?_, ?_, hU0, ⟨(), rfl⟩⟩
  · intro m j hj
    have hj1 : j = 1 := of_decide_eq_true hj
    subst hj1
    exact hF1
  · intro hFIMS
    exact hU0 (hFIMS 1 hF1 () 0 rfl)

/-- **Every link is necessary for K3a.**  In `brokenLinkRing` both nodes are
meta-sound (so the anchor hypothesis and `FaithfulImpliesMetaSound` hold), the
link `1 → 0` is certified, but the link `0 → 1` is not, and the conclusion of
K3a fails: node 1 is not faithful and accepts `⊢ ⊥`.  Taking node 1 as the
anchor: the certified link out of the anchor certifies node 0, and the missing
link back into the anchor is exactly what would have certified the anchor's own
object-level checker. -/
theorem ring_with_uncertified_link_does_not_propagate :
    SemSound stdRules ∧
    (∀ i, MetaSound brokenLinkRing stdRules i) ∧
    FaithfulImpliesMetaSound brokenLinkRing stdRules ∧
    LinkCertified brokenLinkRing 1 ∧
    ¬ LinkCertified brokenLinkRing 0 ∧
    ¬ Faithful (brokenLinkRing.checker 1) stdRules ∧
    (brokenLinkRing.checker 1).AcceptsBot := by
  have hF0 : Faithful (brokenLinkRing.checker 0) stdRules := recheckRecompute_faithful stdRules
  have hMS : ∀ i, MetaSound brokenLinkRing stdRules i := by
    refine fin2_cases ?_ ?_
    · intro m j hj
      cases hj
    · intro m j hj
      have hj0 : j = 0 := of_decide_eq_true hj
      subst hj0
      exact hF0
  refine ⟨stdRules_semSound, hMS, fun i _ => hMS i, ⟨(), rfl⟩, ?_, ex_faithful_acceptAll_neg,
    ⟨(), rfl⟩⟩
  rintro ⟨m, hm⟩
  cases hm

/-! ## Examples for the definitions above -/

/-- Positive example (`ringNext`): on a 3-ring, the successor of 2 is 0. -/
theorem ex_ringNext_wrap_pos : ringNext (2 : Fin 3) = 0 := rfl

/-- Negative example (`ringNext`): on a 3-ring, the successor of 0 is not 0. -/
theorem ex_ringNext_neg : ringNext (0 : Fin 3) ≠ 0 := by decide

/-- Positive example (`ringNext`): a 1-ring is a self-loop. -/
theorem ex_ringNext_self_pos : ringNext (0 : Fin 1) = 0 := rfl

/-- Positive example (`ringIter`): two steps from node 0 on a 3-ring reach
node 2. -/
theorem ex_ringIter_pos : ringIter (0 : Fin 3) 2 = 2 := rfl

/-- Negative example (`ringIter`): three steps on a 3-ring return to the start,
not to node 1. -/
theorem ex_ringIter_neg : ringIter (0 : Fin 3) 3 ≠ 1 := by decide

/-- Positive example (`RingClosed`, `LinkCertified`): `faithfulRing stdRules`. -/
theorem ex_ringClosed_pos : RingClosed (faithfulRing stdRules) := k3a_nonvacuous.1

/-- Negative example (`RingClosed`, `LinkCertified`): `brokenLinkRing`. -/
theorem ex_ringClosed_neg : ¬ RingClosed brokenLinkRing :=
  fun h => ring_with_uncertified_link_does_not_propagate.2.2.2.2.1 (h 0)

/-- Positive example (`MetaSound`), discriminating: node 0 of `rubberStampRing`
is meta-sound and *rejects* the false claim that the unfaithful node 0 is
faithful. -/
theorem ex_metaSound_pos :
    MetaSound rubberStampRing stdRules 0 ∧
    rubberStampRing.acceptsCert 0 () 0 = false ∧
    ¬ Faithful (rubberStampRing.checker 0) stdRules :=
  ⟨metaSound_anchor_ring_fails_without_faithfulImpliesMetaSound.2.2.1, rfl,
   ex_faithful_acceptAll_neg⟩

/-- Negative example (`MetaSound`): node 1 of `rubberStampRing` accepts the
false claim that node 0 is faithful. -/
theorem ex_metaSound_neg : ¬ MetaSound rubberStampRing stdRules 1 :=
  fun h => ex_faithful_acceptAll_neg (h () 0 rfl)

/-- Positive example (`FaithfulImpliesMetaSound`): `faithfulRing stdRules`. -/
theorem ex_faithfulImpliesMetaSound_pos :
    FaithfulImpliesMetaSound (faithfulRing stdRules) stdRules := k3a_nonvacuous.2.1

/-- Negative example (`FaithfulImpliesMetaSound`): `rubberStampRing`. -/
theorem ex_faithfulImpliesMetaSound_neg :
    ¬ FaithfulImpliesMetaSound rubberStampRing stdRules :=
  metaSound_anchor_ring_fails_without_faithfulImpliesMetaSound.2.2.2.1

/-- The two nodes of the `ClaimReflection` examples: the recomputing re-checker
(faithful) and the accept-all checker (unfaithful). -/
def mixedPair : Fin 2 → Checker := fun i => match i with
  | 0 => recheckRecompute stdRules
  | 1 => acceptAll

/-- An encoding that maps the faithful node's claim to a derivable formula and
the unfaithful node's claim to an underivable atom. -/
def honestEnc : Fin 2 → Form := fun i => match i with
  | 0 => Form.top
  | 1 => Form.var 0

/-- Positive example (`ClaimReflection`, `selfHostedRing`), non-vacuous: for
`mixedPair` and `honestEnc`, the standard rules derive the claim about the
faithful node and do not derive the claim about the unfaithful node, and claim
reflection holds. -/
theorem ex_claimReflection_pos :
    ClaimReflection stdRules mixedPair honestEnc ∧
    Derivable stdRules [] (honestEnc 0) ∧
    ¬ Derivable stdRules [] (honestEnc 1) ∧
    Faithful (mixedPair 0) stdRules ∧
    ¬ Faithful (mixedPair 1) stdRules := by
  have hnot : ¬ Derivable stdRules [] (Form.var 0) := by
    intro hd
    have hv := stdRules_semSound [] (.var 0) hd (fun _ => false) rfl
    simp [evalForm] at hv
  refine ⟨?_, ex_derivable_top_pos, hnot, recheckRecompute_faithful stdRules,
    ex_faithful_acceptAll_neg⟩
  intro j hd
  match j with
  | ⟨0, _⟩ => exact recheckRecompute_faithful stdRules
  | ⟨1, _⟩ => exact absurd hd hnot

/-- Negative example (`ClaimReflection`): encoding every faithfulness claim as
the derivable formula `⊥ → ⊥` does not reflect when some node is unfaithful. -/
theorem ex_claimReflection_neg :
    ¬ ClaimReflection stdRules mixedPair (fun _ => Form.top) :=
  fun h => ex_faithful_acceptAll_neg (h 1 ex_derivable_top_pos)

end Toy.KernelTrust
