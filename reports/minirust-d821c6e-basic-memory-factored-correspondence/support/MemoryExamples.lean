import AnnealResearch.MemoryExecution
import AnnealResearch.ReferenceInvariants

/-!
Program-family and mutation controls for the audited raw-memory client language.
No typed Rust load, destructor, Tree Borrows, concurrency, or frontend adequacy
is inferred from these raw-byte results. The parent owns all Lean execution.
-/
namespace AnnealResearch.MemoryExamples

open Execution MemoryExecution MiniRustReference

private theorem noUB_of_successors {s : Config State}
    (notBad : ¬ Bad s) (safeNext : ∀ t, SourceStep s t → NoUB SourceStep Bad t) :
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

private theorem terminal_safe (s : Config State)
    (notBad : ¬ Bad s) (noNext : ∀ t, ¬ SourceStep s t) : NoUB SourceStep Bad s :=
  noUB_of_successors notBad (fun t edge => False.elim (noNext t edge))

theorem spin_safe (memory : State) (trace : List Event) :
    NoUB SourceStep Bad (.running memory .spin trace) := by
  apply invariant_noUB
    (Invariant := fun (s : Config State) => ∃ tr : List Event,
      s = Config.running memory .spin tr) ⟨trace, rfl⟩
  · rintro s t ⟨tr, rfl⟩ ⟨candidate, edge⟩
    change some (Config.running memory .spin (tr ++ [.spin])) = some t at edge
    cases edge
    exact ⟨tr ++ [.spin], rfl⟩
  · rintro s ⟨tr, rfl⟩ bad
    exact bad

/-- A continuation rule covering every allocator candidate. Unsupported is
deliberately rejected by this positive rule, while noChoice supplies no edge. -/
private theorem call_safe (memory : State) (op : Op) (k : Reply → Plan) (trace : List Event)
    (ready : ∀ candidate,
      match sourceExecute candidate memory op with
      | .good reply after => NoUB SourceStep Bad
          (.running after (k reply) (trace ++ [.answered op reply]))
      | .ub _ => False | .unsupported => False | .noChoice => True | .exit _ => True) :
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
  | ub diagnostic =>
    have impossible : False := by simpa [answer] using premise
    exact False.elim impossible
  | unsupported =>
    have impossible : False := by simpa [answer] using premise
    exact False.elim impossible
  | noChoice => rw [answer] at edge; cases edge
  | exit result =>
    rw [answer] at edge
    cases edge
    apply terminal_safe _ (by exact id)
    rintro t ⟨candidate, impossible⟩
    cases impossible

private theorem fixed_call_safe (memory after : State) (op : Op) (reply : Reply)
    (k : Reply → Plan) (trace : List Event)
    (answer : ∀ candidate, sourceExecute candidate memory op = .good reply after)
    (safe : NoUB SourceStep Bad (.running after (k reply) (trace ++ [.answered op reply]))) :
    NoUB SourceStep Bad (.running memory (.call op k) trace) := by
  apply call_safe
  intro candidate
  rw [answer candidate]
  exact safe

def exitPlan : Plan := .call .exit (fun _ => .done)
theorem exit_safe (memory : State) (trace : List Event) :
    NoUB SourceStep Bad (.running memory exitPlan trace) := by
  apply call_safe
  intro candidate
  trivial

def pointer (s : State) (addr : Nat) : Ptr := ⟨addr, some s.next⟩
def fresh (bytes : List Byte) (addr : Nat) : Allocation :=
  freshAllocation .heap bytes.length 1 addr
def freshState (s : State) (bytes : List Byte) (addr : Nat) : State := append s (fresh bytes addr)
def readback (bytes : List Byte) : List Byte :=
  List.ofFn (fun i : Fin bytes.length => bytes.getD i.val .uninit)

theorem readback_exact (bytes : List Byte) : readback bytes = bytes := by
  unfold readback
  have same : (fun i : Fin bytes.length => bytes.getD i.val .uninit) =
      (fun i : Fin bytes.length => bytes[i.val]) := by
    funext i
    exact (List.getElem_eq_getD (h := i.isLt) Byte.uninit).symm
  rw [same]
  exact List.ofFn_getElem

/-- Any successfully allocated fresh block supports the complete raw-byte
store/load/free chain, including an empty block. The exact payload is observed. -/
theorem fresh_round (s : State) (bytes : List Byte) (addr : Nat) :
    ∃ written freed,
      store (freshState s bytes addr) (pointer s addr) bytes 1 = .ok written ∧
      load written (pointer s addr) bytes.length 1 = .ok (bytes, written) ∧
      free written (pointer s addr) .heap bytes.length 1 = .ok freed := by
  let a := fresh bytes addr
  let allocated := freshState s bytes addr
  have lookup : allocated.allocations s.next = some a := by simp [allocated, freshState, append, a]
  by_cases zero : bytes.length = 0
  · have nil : bytes = [] := List.eq_nil_of_length_eq_zero zero
    subst bytes
    refine ⟨allocated, replace allocated s.next { a with live := false }, ?_, ?_, ?_⟩
    · simp [store, checkPtr, Nat.mod_one]
      rfl
    · simp [load, checkPtr, Nat.mod_one]
    · simp [free, pointer, lookup, a, fresh, freshAllocation]
  · let writtenAllocation : Allocation := { a with
      data := fun index => if index < bytes.length then bytes.getD index .uninit else .uninit }
    let written := replace allocated s.next writtenAllocation
    have writtenLookup : written.allocations s.next = some writtenAllocation := by
      simp [written, replace]
    refine ⟨written, replace written s.next { writtenAllocation with live := false }, ?_, ?_, ?_⟩
    · simp [store, checkPtr, pointer, zero, written, writtenAllocation,
        a, fresh, freshAllocation, freshState, append, Nat.mod_one]
      rfl
    · have observed : List.ofFn (fun i : Fin bytes.length => writtenAllocation.data i.val) = bytes := by
        calc
          _ = readback bytes := by
            apply congrArg List.ofFn
            funext i
            simp only [writtenAllocation, ite_eq_left i.isLt]
          _ = bytes := readback_exact bytes
      simpa [load, checkPtr, pointer, writtenLookup, zero, writtenAllocation,
        a, fresh, freshAllocation, Nat.mod_one] using
          congrArg (fun read => Result.ok (read, written)) observed
    · simp [free, pointer, writtenLookup, writtenAllocation, a, fresh, freshAllocation]

def oneRound (bytes : List Byte) (after : Plan) : Plan :=
  .call (.allocate .heap bytes.length 1) fun reply =>
    match reply with
    | .pointer p => .call (.store p bytes 1) fun _ =>
        .call (.load p bytes.length 1) fun _ =>
          .call (.free p .heap bytes.length 1) fun _ => after
    | _ => .done
def rounds (bytes : List Byte) (finish : Plan) : Nat → Plan
  | 0 => finish | n + 1 => oneRound bytes (rounds bytes finish n)

theorem one_round_safe (bytes : List Byte) (small : bytes.length < sizeLimit) (finish : Plan)
    (safeFinish : ∀ memory trace, NoUB SourceStep Bad (.running memory finish trace))
    (memory : State) (trace : List Event) :
    NoUB SourceStep Bad (.running memory (oneRound bytes finish) trace) := by
  apply call_safe
  intro candidate
  by_cases valid : AllocationCandidate memory bytes.length 1 candidate
  · have answer : sourceExecute candidate memory (.allocate .heap bytes.length 1) =
      .good (.pointer (pointer memory candidate)) (freshState memory bytes candidate) := by
      simp [sourceExecute, allocateAt, Nat.not_le.mpr small, valid, liftResult,
        pointer, freshState, fresh, freshAllocation]
    rw [answer]
    obtain ⟨written, freed, stored, loaded, released⟩ := fresh_round memory bytes candidate
    apply fixed_call_safe _ written _ .unit
    · intro arbitrary
      simp [sourceExecute, stored, liftResult]
    · apply fixed_call_safe _ written _ (.bytes bytes)
      · intro arbitrary
        simp [sourceExecute, loaded, liftResult]
      · apply fixed_call_safe _ freed _ .unit
        · intro arbitrary
          simp [sourceExecute, released, liftResult]
        · exact safeFinish freed _
  · simp [sourceExecute, allocateAt, Nat.not_le.mpr small, valid, liftResult]

/-- Unbounded finite repetition, every feasible numeric base, arbitrary exact
raw bytes, and arbitrary safe final client. No allocator-success premise is
used; absent branches stay absent. No termination/progress result is inferred. -/
theorem rounds_safe (bytes : List Byte) (small : bytes.length < sizeLimit) (finish : Plan)
    (safeFinish : ∀ memory trace, NoUB SourceStep Bad (.running memory finish trace)) :
    ∀ n memory trace, NoUB SourceStep Bad (.running memory (rounds bytes finish n) trace) := by
  intro n
  induction n with
  | zero => exact safeFinish
  | succ n ih => exact one_round_safe bytes small (rounds bytes finish n) ih

def sequenceRounds : List (List Byte) → Plan → Plan
  | [], finish => finish
  | bytes :: rest, finish => oneRound bytes (sequenceRounds rest finish)

/-- Varying block sizes and payloads, with no bound on sequence length. -/
theorem sequenceRounds_safe (blocks : List (List Byte)) (finish : Plan)
    (safeFinish : ∀ memory trace, NoUB SourceStep Bad (.running memory finish trace)) :
    (∀ bytes, bytes ∈ blocks → bytes.length < sizeLimit) →
    ∀ memory trace, NoUB SourceStep Bad (.running memory (sequenceRounds blocks finish) trace) := by
  induction blocks with
  | nil => intro _; exact safeFinish
  | cons bytes rest ih =>
    intro bounded
    exact one_round_safe bytes (bounded bytes (by simp)) (sequenceRounds rest finish)
      (ih (fun other member => bounded other (List.mem_cons_of_mem bytes member)))

/-- Provenance-free finite byte blocks form an admitted positive payload family.
Uninit remains allowed because these are raw byte APIs, not typed loads. -/
def plainBytes (bytes : List (Option (Fin 256))) : List Byte :=
  bytes.map (fun b => match b with | none => .uninit | some n => .init n none)
theorem plain_bytes_admitted (s : State) (bytes : List (Option (Fin 256))) :
    BytesWF s (plainBytes bytes) := by
  intro index inside
  have member : (plainBytes bytes).getD index .uninit ∈ plainBytes bytes := by
    rw [← List.getElem_eq_getD (h := inside) Byte.uninit]
    exact List.getElem_mem inside
  obtain ⟨original, _, same⟩ := List.mem_map.mp member
  rw [← same]
  cases original <;> trivial

theorem repeated_plain_blocks_spin (bytes : List (Option (Fin 256)))
    (small : (plainBytes bytes).length < sizeLimit) (n : Nat) :
    NoUB SourceStep Bad (.running empty (rounds (plainBytes bytes) .spin n) []) ∧
    NoUB TargetStep Bad (mapCfg MiniRustFactored.encode
      (.running empty (rounds (plainBytes bytes) .spin n) [])) := by
  have safe := rounds_safe (plainBytes bytes) small .spin spin_safe n empty []
  exact ⟨safe, (encoded_noUB_iff _).mp safe⟩

theorem repeated_plain_blocks_exit (bytes : List (Option (Fin 256)))
    (small : (plainBytes bytes).length < sizeLimit) (n : Nat) :
    NoUB SourceStep Bad (.running empty (rounds (plainBytes bytes) exitPlan n) []) ∧
    NoUB TargetStep Bad (mapCfg MiniRustFactored.encode
      (.running empty (rounds (plainBytes bytes) exitPlan n) [])) := by
  have safe := rounds_safe (plainBytes bytes) small exitPlan exit_safe n empty []
  exact ⟨safe, (encoded_noUB_iff _).mp safe⟩

theorem sequence_plain_blocks_safe (blocks : List (List (Option (Fin 256))))
    (bounded : ∀ bytes, bytes ∈ blocks → (plainBytes bytes).length < sizeLimit)
    (finish : Plan) (safeFinish : ∀ memory trace, NoUB SourceStep Bad (.running memory finish trace)) :
    NoUB SourceStep Bad (.running empty (sequenceRounds (blocks.map plainBytes) finish) []) ∧
    NoUB TargetStep Bad (mapCfg MiniRustFactored.encode
      (.running empty (sequenceRounds (blocks.map plainBytes) finish) [])) := by
  have small : ∀ bytes, bytes ∈ blocks.map plainBytes → bytes.length < sizeLimit := by
    intro bytes member
    obtain ⟨original, belongs, rfl⟩ := List.mem_map.mp member
    exact bounded original belongs
  have safe := sequenceRounds_safe (blocks.map plainBytes) finish safeFinish small empty []
  exact ⟨safe, (encoded_noUB_iff _).mp safe⟩

def seven : Byte := .init ⟨7, by decide⟩ none
def stale : Ptr := ⟨8, some 0⟩
def current : Ptr := ⟨8, some 1⟩
def allocation0 : Allocation := fresh [.uninit] 8
def allocated0 : State := append empty allocation0
def freed0 : State := replace allocated0 0 { allocation0 with live := false }
def allocated1 : State := append freed0 allocation0
def stored1 : State := replace allocated1 1 { allocation0 with
  data := fun index => if 0 ≤ index ∧ index < 0 + 1
    then [seven].getD (index - 0) .uninit else allocation0.data index }

/-- Deliberate mutation: choose a live allocation by numeric range and ignore
the pointer's provenance ID. This is not a claimed alternative Rust policy. -/
def addressOnlyLoad (s : State) (p : Ptr) (len : Nat) : Result (List Byte × State) :=
  match (List.range s.next).find? (fun id =>
    match s.allocations id with
    | none => false
    | some a => a.live && decide (a.base ≤ p.addr ∧ p.addr + len ≤ a.base + a.size)) with
  | none => .ub .bounds
  | some id =>
    match s.allocations id with
    | none => .unsupported
    | some a => .ok (List.ofFn (fun i : Fin len => a.data (p.addr - a.base + i.val)), s)

theorem actual_reuse_chain :
    allocateAt empty .heap 1 1 8 = .ok (stale, allocated0) ∧
    free allocated0 stale .heap 1 1 = .ok freed0 ∧
    allocateAt freed0 .heap 1 1 8 = .ok (current, allocated1) ∧
    store allocated1 current [seven] 1 = .ok stored1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem stale_identity_mutation_control :
    load stored1 stale 1 1 = .ub .dead ∧
    addressOnlyLoad stored1 stale 1 = .ok ([seven], stored1) ∧
    load stored1 stale 1 1 ≠ addressOnlyLoad stored1 stale 1 := by
  refine ⟨rfl, rfl, ?_⟩
  intro impossible
  cases impossible

theorem raw_uninit_control : load allocated0 stale 1 1 = .ok ([.uninit], allocated0) := rfl
def mintedFragmentByte : Byte := .init ⟨7, by decide⟩ (some ⟨0, 19⟩)
theorem minted_fragment_admitted : ByteWF allocated0 mintedFragmentByte := by
  change 0 < 1
  decide
theorem minted_fragment_roundtrip :
    ∃ written freed, store allocated0 stale [mintedFragmentByte] 1 = .ok written ∧
      load written stale 1 1 = .ok ([mintedFragmentByte], written) ∧
      free written stale .heap 1 1 = .ok freed := by
  simpa [freshState, pointer, allocated0, allocation0, stale, fresh, freshAllocation, empty] using
    fresh_round empty [mintedFragmentByte] 8
theorem alignment_precedes_zero_length :
    load empty ⟨1, none⟩ 0 2 = .ub .misalignedLoad ∧
    store empty ⟨1, none⟩ [] 2 = .ub .misalignedStore ∧
    dereferenceable empty ⟨1, none⟩ 0 = .ok () := ⟨rfl, rfl, rfl⟩
theorem wrong_free_order_control :
    free allocated0 ⟨9, some 0⟩ .global 99 2 = .ub .freeNotBase ∧
    free allocated0 stale .global 99 2 = .ub .freeKind := ⟨rfl, rfl⟩
theorem leak_is_distinct_from_ub :
    exit allocated0 = .memoryLeak ∧ exit freed0 = .machineStop ∧
    sourceExecute 0 allocated0 .exit = .exit .memoryLeak := ⟨rfl, rfl, rfl⟩

def badThenSpin : Plan := .call (.load stale 1 1) (fun _ => .spin)
theorem bad_prefix_before_spin :
    Reach SourceStep (.running stored1 badThenSpin []) (.bad stored1 .dead) ∧
    ¬ NoUB SourceStep Bad (.running stored1 badThenSpin []) ∧
    ¬ NoUB TargetStep Bad (mapCfg MiniRustFactored.encode (.running stored1 badThenSpin [])) := by
  have path : Reach SourceStep (.running stored1 badThenSpin []) (.bad stored1 .dead) :=
    Reach.tail (Reach.refl _) ⟨0, rfl⟩
  have notSafe : ¬ NoUB SourceStep Bad (.running stored1 badThenSpin []) :=
    bad_prefix_not_noUB path True.intro
  refine ⟨path, notSafe, ?_⟩
  intro targetSafe
  exact notSafe ((encoded_noUB_iff _).mpr targetSafe)

#print axioms fresh_round
#print axioms rounds_safe
#print axioms sequenceRounds_safe
#print axioms sequence_plain_blocks_safe
#print axioms repeated_plain_blocks_spin
#print axioms repeated_plain_blocks_exit
#print axioms actual_reuse_chain
#print axioms stale_identity_mutation_control
#print axioms alignment_precedes_zero_length
#print axioms wrong_free_order_control
#print axioms raw_uninit_control
#print axioms minted_fragment_admitted
#print axioms minted_fragment_roundtrip
#print axioms leak_is_distinct_from_ub
#print axioms bad_prefix_before_spin

end AnnealResearch.MemoryExamples
