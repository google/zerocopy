import AnnealResearch.ProofCostContinuationBase
import AnnealResearch.ProofCostFrames

/-!
Compositional continuation route for the exact shared two-live-buffer subject.
Raw per-ID framing is new shared setup in ProofCostFrames; continuation rules
are route setup.  The base route remains separately frozen.  Every call rule covers every Nat
candidate; no chosen execution or WF/NoUB premise for a memory state is used.

Allocation identity, rather than numeric nonoverlap, makes B's store/free leave
A's record unchanged.  Allocator-candidate checks remain in the actual kernel.
The B-empty case is retained: its store/load are the actual zero-length calls,
and its free still changes B's separate allocation record.  The parent compiles.
-/

namespace AnnealResearch.ProofCostContinuation

open Execution MemoryExecution MiniRustReference MemoryExamples ProofCostCommon ProofCostFrames

/- Route-specific continuation rules.  Their proof shape is reused from the
earlier private rules in MemoryExamples; that earlier investment is explicit.
They inspect the actual next relation and preserve all finite bad prefixes. -/

private theorem noUB_of_successors {s : Config State} (notBad : ¬ Bad s)
    (safeNext : ∀ t, SourceStep s t → NoUB SourceStep Bad t) :
    NoUB SourceStep Bad s := by
  apply invariant_noUB (Invariant := fun t => t = s ∨ NoUB SourceStep Bad t) (Or.inl rfl)
  · intro t u invariant edge
    rcases invariant with rfl | safe
    · exact Or.inr (safeNext u edge)
    · exact Or.inr (safe.after_step edge)
  · intro t invariant bad
    rcases invariant with rfl | safe
    · exact notBad bad
    · exact safe t (Reach.refl _) bad

private theorem terminal_safe (s : Config State) (notBad : ¬ Bad s)
    (noNext : ∀ t, ¬ SourceStep s t) : NoUB SourceStep Bad s :=
  noUB_of_successors notBad (fun t edge => False.elim (noNext t edge))

theorem continuation_call_safe (memory : State) (op : Op) (k : Reply → Plan)
    (trace : List Event)
    (ready : ∀ candidate,
      match sourceExecute candidate memory op with
      | .good reply after => NoUB SourceStep Bad
          (.running after (k reply) (trace ++ [.answered op reply]))
      | .ub _ => False
      | .unsupported => False
      | .noChoice => True
      | .exit _ => True) :
    NoUB SourceStep Bad (.running memory (.call op k) trace) := by
  apply noUB_of_successors (by exact id)
  intro successor edge
  obtain ⟨candidate, edge⟩ := edge
  have premise := ready candidate
  simp only [MemoryExecution.next] at edge
  cases answer : sourceExecute candidate memory op with
  | good reply after =>
    rw [answer] at edge premise
    cases edge
    exact premise
  | ub diagnostic => simp [answer] at premise
  | unsupported => simp [answer] at premise
  | noChoice => rw [answer] at edge; cases edge
  | exit result =>
    rw [answer] at edge
    cases edge
    apply terminal_safe _ (by exact id)
    rintro t ⟨candidate, impossible⟩
    cases impossible

theorem fixed_call_safe (memory after : State) (op : Op) (reply : Reply)
    (k : Reply → Plan) (trace : List Event)
    (answer : ∀ candidate, sourceExecute candidate memory op = .good reply after)
    (safe : NoUB SourceStep Bad (.running after (k reply) (trace ++ [.answered op reply]))) :
    NoUB SourceStep Bad (.running memory (.call op k) trace) := by
  apply continuation_call_safe
  intro candidate
  rw [answer candidate]
  exact safe

theorem two_live_round_safe (bytesA bytesB : List Byte)
    (smallA : bytesA.length < sizeLimit) (smallB : bytesB.length < sizeLimit)
    (finish : Plan)
    (safeFinish : ∀ memory trace, NoUB SourceStep Bad (.running memory finish trace))
    (memory : State) (trace : List Event) :
    NoUB SourceStep Bad (.running memory (twoLiveRound bytesA bytesB finish) trace) := by
  apply continuation_call_safe
  intro candidateA
  by_cases validA : AllocationCandidate memory bytesA.length 1 candidateA
  · rw [allocate_answer memory bytesA candidateA smallA validA]
    obtain ⟨writtenA, oldFreedA, storedA, loadedA, releasedA⟩ :=
      fresh_round_facts memory bytesA candidateA
    have different : memory.next ≠ writtenA.next := by
      have nextEq := store_preserves_next storedA
      change writtenA.next = memory.next + 1 at nextEq
      omega
    apply fixed_call_safe _ writtenA _ .unit
    · intro arbitrary
      simp [sourceExecute, storedA, liftResult]
    · apply continuation_call_safe
      intro candidateB
      by_cases validB : AllocationCandidate writtenA bytesB.length 1 candidateB
      · rw [allocate_answer writtenA bytesB candidateB smallB validB]
        obtain ⟨writtenB, freedB, storedB, loadedB, releasedB⟩ :=
          fresh_round_facts writtenA bytesB candidateB
        have kept : freedB.allocations memory.next = writtenA.allocations memory.next :=
          fresh_round_preserves_other different storedB releasedB
        have loadedAfter := load_frame (first := writtenA) (second := freedB)
          (id := memory.next) rfl kept.symm loadedA
        obtain ⟨final, releasedAfter⟩ := free_frame (first := writtenA) (second := freedB)
          (id := memory.next) rfl kept.symm releasedA
        apply fixed_call_safe _ writtenB _ .unit
        · intro arbitrary
          simp [sourceExecute, storedB, liftResult]
        · apply fixed_call_safe _ writtenB _ (.bytes bytesB)
          · intro arbitrary
            simp [sourceExecute, loadedB, liftResult]
          · apply fixed_call_safe _ freedB _ .unit
            · intro arbitrary
              simp [sourceExecute, releasedB, liftResult]
            · apply fixed_call_safe _ freedB _ (.bytes bytesA)
              · intro arbitrary
                simp [sourceExecute, loadedAfter, liftResult]
              · apply fixed_call_safe _ final _ .unit
                · intro arbitrary
                  simp [sourceExecute, releasedAfter, liftResult]
                · exact safeFinish final _
      · simp [allocate_absent writtenA bytesB candidateB smallB validB]
  · simp [allocate_absent memory bytesA candidateA smallA validA]

theorem two_live_rounds_safe (bytesA bytesB : List Byte)
    (smallA : bytesA.length < sizeLimit) (smallB : bytesB.length < sizeLimit)
    (finish : Plan)
    (safeFinish : ∀ memory trace, NoUB SourceStep Bad (.running memory finish trace)) :
    ∀ n memory trace,
      NoUB SourceStep Bad (.running memory (twoLiveRounds bytesA bytesB finish n) trace) := by
  intro n
  induction n with
  | zero => exact safeFinish
  | succ n ih =>
    exact two_live_round_safe bytesA bytesB smallA smallB
      (twoLiveRounds bytesA bytesB finish n) ih

theorem extension_claim (bytesA bytesB : List Byte)
    (smallA : bytesA.length < sizeLimit) (smallB : bytesB.length < sizeLimit) (n : Nat) :
    ExtensionClaim bytesA bytesB n :=
  two_live_rounds_safe bytesA bytesB smallA smallB .spin spin_safe n empty []

theorem extension_fixture (payload : Payload) (scale : Scale) :
    ExtensionFixtureClaim payload scale :=
  extension_claim sevenBytes (payloadBytes payload) (payload_small .initialized)
    (payload_small payload) (repetitions scale)

theorem extension_suite : ExtensionSuite := extension_fixture

#print axioms continuation_call_safe
#print axioms fixed_call_safe
#print axioms two_live_round_safe
#print axioms two_live_rounds_safe
#print axioms extension_claim
#print axioms extension_fixture
#print axioms extension_suite

end AnnealResearch.ProofCostContinuation
