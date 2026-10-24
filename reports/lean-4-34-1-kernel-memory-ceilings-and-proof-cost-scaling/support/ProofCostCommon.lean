import AnnealResearch.MemoryExamples
import AnnealResearch.MemoryWitnesses

/-!
Shared subject for a bounded proof-organization pilot, at Anneal baseline
1cb1cdca8b362559bd7a04023bc546cec89b1ec1.  The parent owns compilation.

Both later routes must prove the propositions defined here using exactly the
existing SourceStep/Bad semantics.  The finite fixture set does not bound
allocator candidates or execution horizons.  No base or extension NoUB theorem
is proved here.  Enabled paths are separate nonvacuity evidence.  The only
whole-program safety conclusion below is the *negative* coverage control.

The common imports contain prior program safety theorems.  Their availability
is not permission for the direct-invariant route to invoke them.  Reuse must be
recorded separately from new route setup and client checking.  This pilot
compares proof organization within Lean, not semantic architectures or Rust.
-/

namespace AnnealResearch.ProofCostCommon

open Execution MemoryExecution MiniRustReference MemoryExamples

inductive Payload where
  | empty | uninitialized | initialized | mixed
  deriving DecidableEq, Repr

inductive Scale where
  | one | four | sixteen
  deriving DecidableEq, Repr

def emptyBytes : List Byte := []
def uninitBytes : List Byte := [.uninit]
def sevenBytes : List Byte := [seven]
def mixedBytes : List Byte := [.uninit, seven]

def payloadBytes : Payload → List Byte
  | .empty => emptyBytes
  | .uninitialized => uninitBytes
  | .initialized => sevenBytes
  | .mixed => mixedBytes

def repetitions : Scale → Nat
  | .one => 1
  | .four => 4
  | .sixteen => 16

def payloads : List Payload := [.empty, .uninitialized, .initialized, .mixed]
def scales : List Scale := [.one, .four, .sixteen]

theorem payload_small (payload : Payload) : (payloadBytes payload).length < sizeLimit := by
  cases payload <;> decide

theorem payload_admitted (memory : State) (payload : Payload) :
    BytesWF memory (payloadBytes payload) := by
  cases payload with
  | empty => exact plain_bytes_admitted memory []
  | uninitialized => exact plain_bytes_admitted memory [none]
  | initialized => exact plain_bytes_admitted memory [some ⟨7, by decide⟩]
  | mixed => exact plain_bytes_admitted memory [none, some ⟨7, by decide⟩]

def baseInitial (bytes : List Byte) (n : Nat) : Config State :=
  .running empty (rounds bytes .spin n) []

/-- The same exact proposition is the endpoint of both later proof routes. -/
def BaseClaim (bytes : List Byte) (n : Nat) : Prop :=
  NoUB SourceStep Bad (baseInitial bytes n)

def BaseFixtureClaim (payload : Payload) (scale : Scale) : Prop :=
  BaseClaim (payloadBytes payload) (repetitions scale)

def BaseSuite : Prop := ∀ payload scale, BaseFixtureClaim payload scale

/-- A primitive equation wrapper, with no program-safety conclusion. -/
theorem allocate_answer (memory : State) (bytes : List Byte) (candidate : Nat)
    (small : bytes.length < sizeLimit)
    (valid : AllocationCandidate memory bytes.length 1 candidate) :
    sourceExecute candidate memory (.allocate .heap bytes.length 1) =
      .good (.pointer (pointer memory candidate)) (freshState memory bytes candidate) := by
  simp [sourceExecute, allocateAt, Nat.not_le.mpr small, valid, liftResult,
    pointer, freshState, fresh, freshAllocation]

theorem allocate_absent (memory : State) (bytes : List Byte) (candidate : Nat)
    (small : bytes.length < sizeLimit)
    (invalid : ¬ AllocationCandidate memory bytes.length 1 candidate) :
    sourceExecute candidate memory (.allocate .heap bytes.length 1) = .noChoice := by
  simp [sourceExecute, allocateAt, Nat.not_le.mpr small, invalid, liftResult]

/-- Shared raw primitive facts; this is not the continuation safety rule. -/
theorem fresh_round_facts (memory : State) (bytes : List Byte) (candidate : Nat) :
    ∃ written freed,
      store (freshState memory bytes candidate) (pointer memory candidate) bytes 1 = .ok written ∧
      load written (pointer memory candidate) bytes.length 1 = .ok (bytes, written) ∧
      free written (pointer memory candidate) .heap bytes.length 1 = .ok freed :=
  fresh_round memory bytes candidate

/-- An equation creates one actual edge, preserving the existing trace update. -/
theorem good_edge (candidate : Nat) (memory after : State) (op : Op) (reply : Reply)
    (continuation : Reply → Plan) (trace : List Event)
    (answer : sourceExecute candidate memory op = .good reply after) :
    SourceStep (.running memory (.call op continuation) trace)
      (.running after (continuation reply) (trace ++ [.answered op reply])) := by
  refine ⟨candidate, ?_⟩
  simp only [MemoryExecution.next, answer]

theorem ub_edge (candidate : Nat) (memory : State) (op : Op)
    (continuation : Reply → Plan) (trace : List Event) (diagnostic : UB)
    (answer : sourceExecute candidate memory op = .ub diagnostic) :
    SourceStep (.running memory (.call op continuation) trace) (.bad memory diagnostic) := by
  refine ⟨candidate, ?_⟩
  simp only [MemoryExecution.next, answer]

theorem base_enabled (payload : Payload) (n : Nat) :
    ∃ final trace,
      Reach SourceStep (baseInitial (payloadBytes payload) n)
        (MemoryWitnesses.spinRun final trace 0) ∧
      (∀ k, SourceStep (MemoryWitnesses.spinRun final trace k)
        (MemoryWitnesses.spinRun final trace (k + 1))) :=
  MemoryWitnesses.empty_rounds_reach_spin (payloadBytes payload) (payload_small payload) n

/- The extension retains A while allocating and using B.  Naming its stages
lets both routes share identical higher-order continuations and control syntax.
There are eight API calls in a successful round.  No new operational rule is
introduced, and unexpected reply constructors retain the base language's done
branch.  B may be zero-sized; the concrete witness below uses two positive
one-byte allocations. -/

def finishA (bytesA : List Byte) (pA : Ptr) (after : Plan) : Plan :=
  .call (.load pA bytesA.length 1) fun _ =>
    .call (.free pA .heap bytesA.length 1) fun _ => after

def freeBThenA (bytesA bytesB : List Byte) (pA pB : Ptr) (after : Plan) : Plan :=
  .call (.free pB .heap bytesB.length 1) fun _ => finishA bytesA pA after

def loadBThenA (bytesA bytesB : List Byte) (pA pB : Ptr) (after : Plan) : Plan :=
  .call (.load pB bytesB.length 1) fun _ => freeBThenA bytesA bytesB pA pB after

def useB (bytesA bytesB : List Byte) (pA pB : Ptr) (after : Plan) : Plan :=
  .call (.store pB bytesB 1) fun _ => loadBThenA bytesA bytesB pA pB after

def allocateB (bytesA bytesB : List Byte) (pA : Ptr) (after : Plan) : Plan :=
  .call (.allocate .heap bytesB.length 1) fun reply =>
    match reply with
    | .pointer pB => useB bytesA bytesB pA pB after
    | _ => .done

def useA (bytesA bytesB : List Byte) (pA : Ptr) (after : Plan) : Plan :=
  .call (.store pA bytesA 1) fun _ => allocateB bytesA bytesB pA after

def twoLiveRound (bytesA bytesB : List Byte) (after : Plan) : Plan :=
  .call (.allocate .heap bytesA.length 1) fun reply =>
    match reply with
    | .pointer pA => useA bytesA bytesB pA after
    | _ => .done

def twoLiveRounds (bytesA bytesB : List Byte) (finish : Plan) : Nat → Plan
  | 0 => finish
  | n + 1 => twoLiveRound bytesA bytesB (twoLiveRounds bytesA bytesB finish n)

def extensionInitial (bytesA bytesB : List Byte) (n : Nat) : Config State :=
  .running empty (twoLiveRounds bytesA bytesB .spin n) []

def ExtensionClaim (bytesA bytesB : List Byte) (n : Nat) : Prop :=
  NoUB SourceStep Bad (extensionInitial bytesA bytesB n)

/-- Fixed A holds seven; B ranges over exactly the same four payload fixtures. -/
def ExtensionFixtureClaim (payload : Payload) (scale : Scale) : Prop :=
  ExtensionClaim sevenBytes (payloadBytes payload) (repetitions scale)

def ExtensionSuite : Prop := ∀ payload scale, ExtensionFixtureClaim payload scale

/- Concrete operational nonvacuity only.  State projections below have fallback
branches solely to give names to successful concrete computations.  Every use
is accompanied by an actual kernel equation; fallback behavior is not a new
transition, an assumption of success, or part of either shared claim. -/
namespace TwoLiveWitness

def pA : Ptr := ⟨1, some 0⟩
def pB : Ptr := ⟨4, some 1⟩
def allocatedA : State := freshState empty sevenBytes 1
def writtenA : State :=
  match store allocatedA pA sevenBytes 1 with
  | .ok after => after
  | _ => empty
def allocatedB : State := freshState writtenA uninitBytes 4
def writtenB : State :=
  match store allocatedB pB uninitBytes 1 with
  | .ok after => after
  | _ => empty
def freedB : State :=
  match free writtenB pB .heap 1 1 with
  | .ok after => after
  | _ => empty
def freedA : State :=
  match free freedB pA .heap 1 1 with
  | .ok after => after
  | _ => empty

def trace1 : List Event := [.answered (.allocate .heap 1 1) (.pointer pA)]
def trace2 : List Event := trace1 ++ [.answered (.store pA sevenBytes 1) .unit]
def trace3 : List Event := trace2 ++ [.answered (.allocate .heap 1 1) (.pointer pB)]
def trace4 : List Event := trace3 ++ [.answered (.store pB uninitBytes 1) .unit]
def trace5 : List Event := trace4 ++ [.answered (.load pB 1 1) (.bytes uninitBytes)]
def trace6 : List Event := trace5 ++ [.answered (.free pB .heap 1 1) .unit]
def trace7 : List Event := trace6 ++ [.answered (.load pA 1 1) (.bytes sevenBytes)]
def trace8 : List Event := trace7 ++ [.answered (.free pA .heap 1 1) .unit]

def config0 : Config State := extensionInitial sevenBytes uninitBytes 1
def config1 : Config State :=
  .running allocatedA (useA sevenBytes uninitBytes pA .spin) trace1
def config2 : Config State :=
  .running writtenA (allocateB sevenBytes uninitBytes pA .spin) trace2
def config3 : Config State :=
  .running allocatedB (useB sevenBytes uninitBytes pA pB .spin) trace3
def config4 : Config State :=
  .running writtenB (loadBThenA sevenBytes uninitBytes pA pB .spin) trace4
def config5 : Config State :=
  .running writtenB (freeBThenA sevenBytes uninitBytes pA pB .spin) trace5
def config6 : Config State := .running freedB (finishA sevenBytes pA .spin) trace6
def config7 : Config State :=
  .running freedB (.call (.free pA .heap 1 1) (fun _ => .spin)) trace7
def config8 : Config State := .running freedA .spin trace8

theorem step01 : SourceStep config0 config1 := ⟨1, rfl⟩
theorem step12 : SourceStep config1 config2 := ⟨0, rfl⟩
theorem step23 : SourceStep config2 config3 := ⟨4, rfl⟩
theorem step34 : SourceStep config3 config4 := ⟨0, rfl⟩
theorem step45 : SourceStep config4 config5 := ⟨0, rfl⟩
theorem step56 : SourceStep config5 config6 := ⟨0, rfl⟩
theorem step67 : SourceStep config6 config7 := ⟨0, rfl⟩
theorem step78 : SourceStep config7 config8 := ⟨0, rfl⟩

theorem actual_two_live_prefix : Reach SourceStep config0 config3 :=
  Reach.tail (Reach.tail (Reach.tail (Reach.refl _) step01) step12) step23

theorem both_positive_buffers_live :
    (allocatedB.allocations 0).map (fun allocation => (allocation.live, allocation.size)) =
      some (true, 1) ∧
    (allocatedB.allocations 1).map (fun allocation => (allocation.live, allocation.size)) =
      some (true, 1) := ⟨rfl, rfl⟩

theorem actual_round_reach_spin : Reach SourceStep config0 config8 :=
  Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail actual_two_live_prefix
    step34) step45) step56) step67) step78

/-- The initialized value in A survives the entire concrete use/free of B. -/
theorem read_A_after_free_B : load freedB pA 1 1 = .ok (sevenBytes, freedB) := rfl

theorem extension_fixture_enabled :
    ∃ final trace,
      Reach SourceStep (extensionInitial sevenBytes (payloadBytes .uninitialized)
        (repetitions .one)) (MemoryWitnesses.spinRun final trace 0) ∧
      (∀ k, SourceStep (MemoryWitnesses.spinRun final trace k)
        (MemoryWitnesses.spinRun final trace (k + 1))) :=
  ⟨freedA, trace8, actual_round_reach_spin, MemoryWitnesses.spinRun_steps freedA trace8⟩

end TwoLiveWitness

/- The coverage discriminator leaves every allocator candidate in SourceStep.
Address one follows a successful round.  Address two is also feasible, but its
branch frees the allocation and then performs a positive-length stale load.
The later spin continuation cannot remove that finite dead-allocation UB. -/
namespace Coverage

def ordinaryTail (p : Ptr) : Plan :=
  .call (.store p sevenBytes 1) fun _ =>
    .call (.load p 1 1) fun _ =>
      .call (.free p .heap 1 1) fun _ => .spin

def staleTail (p : Ptr) : Plan :=
  .call (.free p .heap 1 1) fun _ => .call (.load p 1 1) fun _ => .spin

def branch (p : Ptr) : Plan := if p.addr = 2 then staleTail p else ordinaryTail p

def program : Plan := .call (.allocate .heap 1 1) fun reply =>
  match reply with
  | .pointer p => branch p
  | _ => .done

def initial : Config State := .running empty program []
def pOne : Ptr := ⟨1, some 0⟩
def pTwo : Ptr := ⟨2, some 0⟩
def allocatedOne : State := freshState empty sevenBytes 1
def writtenOne : State := TwoLiveWitness.writtenA
def freedOne : State :=
  match free writtenOne pOne .heap 1 1 with
  | .ok after => after
  | _ => empty
def allocatedTwo : State := freshState empty sevenBytes 2
def freedTwo : State := replace allocatedTwo 0 { fresh sevenBytes 2 with live := false }

def oneTrace1 : List Event := [.answered (.allocate .heap 1 1) (.pointer pOne)]
def oneTrace2 : List Event := oneTrace1 ++ [.answered (.store pOne sevenBytes 1) .unit]
def oneTrace3 : List Event := oneTrace2 ++ [.answered (.load pOne 1 1) (.bytes sevenBytes)]
def oneTrace4 : List Event := oneTrace3 ++ [.answered (.free pOne .heap 1 1) .unit]
def one1 : Config State := .running allocatedOne (branch pOne) oneTrace1
def one2 : Config State := .running writtenOne
  (.call (.load pOne 1 1) fun _ => .call (.free pOne .heap 1 1) fun _ => .spin) oneTrace2
def one3 : Config State := .running writtenOne
  (.call (.free pOne .heap 1 1) fun _ => .spin) oneTrace3
def one4 : Config State := .running freedOne .spin oneTrace4

def twoTrace1 : List Event := [.answered (.allocate .heap 1 1) (.pointer pTwo)]
def twoTrace2 : List Event := twoTrace1 ++ [.answered (.free pTwo .heap 1 1) .unit]
def two1 : Config State := .running allocatedTwo (branch pTwo) twoTrace1
def two2 : Config State := .running freedTwo (.call (.load pTwo 1 1) fun _ => .spin) twoTrace2

theorem one_is_feasible : AllocationCandidate empty 1 1 1 := by decide
theorem two_is_feasible : AllocationCandidate empty 1 1 2 := by decide
theorem zero_candidate_is_absent : next sourceExecute 0 initial = none := rfl

theorem one_step01 : SourceStep initial one1 := ⟨1, rfl⟩
theorem one_step12 : SourceStep one1 one2 := ⟨0, rfl⟩
theorem one_step23 : SourceStep one2 one3 := ⟨0, rfl⟩
theorem one_step34 : SourceStep one3 one4 := ⟨0, rfl⟩

theorem address_one_reach_spin : Reach SourceStep initial one4 :=
  Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.refl _) one_step01)
    one_step12) one_step23) one_step34

theorem address_one_enabled_spin :
    ∃ final trace, Reach SourceStep initial (MemoryWitnesses.spinRun final trace 0) ∧
      (∀ k, SourceStep (MemoryWitnesses.spinRun final trace k)
        (MemoryWitnesses.spinRun final trace (k + 1))) :=
  ⟨freedOne, oneTrace4, address_one_reach_spin,
    MemoryWitnesses.spinRun_steps freedOne oneTrace4⟩

theorem two_step01 : SourceStep initial two1 := ⟨2, rfl⟩
theorem two_step12 : SourceStep two1 two2 := ⟨0, rfl⟩
theorem two_step_bad : SourceStep two2 (.bad freedTwo .dead) := ⟨0, rfl⟩

theorem address_two_bad_prefix : Reach SourceStep initial (.bad freedTwo .dead) :=
  Reach.tail (Reach.tail (Reach.tail (Reach.refl _) two_step01) two_step12) two_step_bad

theorem all_choice_claim_false : ¬ NoUB SourceStep Bad initial :=
  bad_prefix_not_noUB address_two_bad_prefix True.intro

end Coverage

#print axioms payload_small
#print axioms payload_admitted
#print axioms allocate_answer
#print axioms allocate_absent
#print axioms fresh_round_facts
#print axioms good_edge
#print axioms ub_edge
#print axioms base_enabled
#print axioms TwoLiveWitness.step01
#print axioms TwoLiveWitness.step12
#print axioms TwoLiveWitness.step23
#print axioms TwoLiveWitness.step34
#print axioms TwoLiveWitness.step45
#print axioms TwoLiveWitness.step56
#print axioms TwoLiveWitness.step67
#print axioms TwoLiveWitness.step78
#print axioms TwoLiveWitness.actual_two_live_prefix
#print axioms TwoLiveWitness.both_positive_buffers_live
#print axioms TwoLiveWitness.actual_round_reach_spin
#print axioms TwoLiveWitness.read_A_after_free_B
#print axioms TwoLiveWitness.extension_fixture_enabled
#print axioms Coverage.one_is_feasible
#print axioms Coverage.two_is_feasible
#print axioms Coverage.zero_candidate_is_absent
#print axioms Coverage.one_step01
#print axioms Coverage.one_step12
#print axioms Coverage.one_step23
#print axioms Coverage.one_step34
#print axioms Coverage.address_one_reach_spin
#print axioms Coverage.address_one_enabled_spin
#print axioms Coverage.two_step01
#print axioms Coverage.two_step12
#print axioms Coverage.two_step_bad
#print axioms Coverage.address_two_bad_prefix
#print axioms Coverage.all_choice_claim_false

end AnnealResearch.ProofCostCommon
