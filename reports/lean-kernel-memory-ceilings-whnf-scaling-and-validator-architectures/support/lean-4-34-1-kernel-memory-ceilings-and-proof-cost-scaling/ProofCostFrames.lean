import AnnealResearch.ProofCostCommon

/-!
Shared extension primitive setup for the matched proof-organization pilot.
These helpers concern only the unchanged raw kernels and allocation records.
They contain no NoUB or continuation-safety theorem.  Both later routes may
reuse exactly this new shared investment.  The parent owns compiler checks.
-/
namespace AnnealResearch.ProofCostFrames

open Execution MemoryExecution MiniRustReference MemoryExamples ProofCostCommon

/- Shared primitive framing.  These lemmas inspect the unchanged raw
kernel.  They do not alter SourceStep, admission, failures, traces or choices. -/

theorem store_preserves_next {before after : State} {p : Ptr} {bytes : List Byte}
    {align : Nat} (success : store before p bytes align = .ok after) :
    after.next = before.next := by
  by_cases zeroAlign : align = 0
  · simp [store, zeroAlign] at success
  by_cases misaligned : p.addr % align ≠ 0
  · simp [store, zeroAlign, misaligned] at success
  simp only [store, ite_eq_right zeroAlign, ite_eq_right misaligned] at success
  cases checked : checkPtr before p bytes.length with
  | ub error => simp [checked] at success
  | noChoice => simp [checked] at success
  | unsupported => simp [checked] at success
  | ok span =>
    cases span with
    | none =>
      simp only [checked] at success
      have same := Result.ok.inj success
      rw [← same]
    | some span =>
      simp only [checked] at success
      have same := Result.ok.inj success
      rw [← same]
      rfl

theorem checked_id {memory : State} {p : Ptr} {len id : Nat} {span : CheckedSpan}
    (provenance : p.provenance = some id)
    (success : checkPtr memory p len = .ok (some span)) : span.id = id := by
  by_cases zero : len = 0
  · simp [checkPtr, zero] at success
  cases found : memory.allocations id with
  | none => simp [checkPtr, zero, provenance, found] at success
  | some allocation =>
    simp only [checkPtr, ite_eq_right zero, provenance, found] at success
    split at success
    · cases success
    · split at success
      · cases success
      · split at success
        · cases success
        · have same := Option.some.inj (Result.ok.inj success)
          exact (congrArg CheckedSpan.id same).symm

theorem store_preserves_other {before after : State} {p : Ptr} {bytes : List Byte}
    {align writtenId keptId : Nat} (provenance : p.provenance = some writtenId)
    (different : keptId ≠ writtenId)
    (success : store before p bytes align = .ok after) :
    after.allocations keptId = before.allocations keptId := by
  by_cases zeroAlign : align = 0
  · simp [store, zeroAlign] at success
  by_cases misaligned : p.addr % align ≠ 0
  · simp [store, zeroAlign, misaligned] at success
  simp only [store, ite_eq_right zeroAlign, ite_eq_right misaligned] at success
  cases checked : checkPtr before p bytes.length with
  | ub error => simp [checked] at success
  | noChoice => simp [checked] at success
  | unsupported => simp [checked] at success
  | ok span =>
    cases span with
    | none =>
      simp only [checked] at success
      have same := Result.ok.inj success
      rw [← same]
    | some span =>
      have selected := checked_id provenance checked
      simp only [checked] at success
      have same := Result.ok.inj success
      rw [← same]
      simp [replace, selected, different]

theorem free_preserves_other {before after : State} {p : Ptr} {kind : Kind}
    {size align freedId keptId : Nat} (provenance : p.provenance = some freedId)
    (different : keptId ≠ freedId)
    (success : free before p kind size align = .ok after) :
    after.allocations keptId = before.allocations keptId := by
  cases found : before.allocations freedId with
  | none => simp [free, provenance, found] at success
  | some allocation =>
    simp only [free, provenance, found] at success
    split at success
    · cases success
    · split at success
      · cases success
      · split at success
        · cases success
        · split at success
          · cases success
          · split at success
            · cases success
            · have same := Result.ok.inj success
              rw [← same]
              simp [replace, different]

/-- B's complete raw round preserves any old allocation record with another ID.
The conclusion includes its entire byte function, not merely its live bit. -/
theorem fresh_round_preserves_other {memory written freed : State}
    {bytes : List Byte} {candidate keptId : Nat} (different : keptId ≠ memory.next)
    (stored : store (freshState memory bytes candidate) (pointer memory candidate)
      bytes 1 = .ok written)
    (released : free written (pointer memory candidate) .heap bytes.length 1 = .ok freed) :
    freed.allocations keptId = memory.allocations keptId := by
  calc
    freed.allocations keptId = written.allocations keptId :=
      free_preserves_other rfl different released
    _ = (freshState memory bytes candidate).allocations keptId :=
      store_preserves_other rfl different stored
    _ = memory.allocations keptId := by simp [freshState, append, different]

theorem checkPtr_frame {first second : State} {p : Ptr} {id len : Nat}
    (provenance : p.provenance = some id)
    (same : first.allocations id = second.allocations id) :
    checkPtr first p len = checkPtr second p len := by
  simp [checkPtr, provenance, same]

/-- The raw bytes agree, while the reply carries the current framed memory. -/
theorem load_frame {first second : State} {p : Ptr} {id len align : Nat}
    {bytes : List Byte} (provenance : p.provenance = some id)
    (same : first.allocations id = second.allocations id)
    (success : load first p len align = .ok (bytes, first)) :
    load second p len align = .ok (bytes, second) := by
  by_cases zeroAlign : align = 0
  · simp [load, zeroAlign] at success
  by_cases misaligned : p.addr % align ≠ 0
  · simp [load, zeroAlign, misaligned] at success
  have checkedSame := checkPtr_frame (len := len) provenance same
  simp only [load, ite_eq_right zeroAlign, ite_eq_right misaligned] at success ⊢
  rw [← checkedSame]
  cases checked : checkPtr first p len with
  | ub error => simp [checked] at success
  | noChoice => simp [checked] at success
  | unsupported => simp [checked] at success
  | ok span =>
    cases span <;> simp only [checked] at success ⊢ <;>
      exact congrArg (fun read => Result.ok (read, second))
        (congrArg Prod.fst (Result.ok.inj success))

/-- Successful free remains successful when its selected allocation is framed.
The final memory is the real free result, with every other record retained. -/
theorem free_frame {first second after : State} {p : Ptr} {id size align : Nat}
    {kind : Kind} (provenance : p.provenance = some id)
    (same : first.allocations id = second.allocations id)
    (success : free first p kind size align = .ok after) :
    ∃ final, free second p kind size align = .ok final := by
  cases found : first.allocations id with
  | none => simp [free, provenance, found] at success
  | some allocation =>
    have otherFound : second.allocations id = some allocation := by
      rw [← same]
      exact found
    by_cases dead : allocation.live = false
    · simp [free, provenance, found, dead] at success
    by_cases wrongBase : p.addr ≠ allocation.base
    · simp [free, provenance, found, dead, wrongBase] at success
    by_cases wrongKind : kind ≠ allocation.kind
    · simp [free, provenance, found, dead, wrongBase, wrongKind] at success
    by_cases wrongSize : size ≠ allocation.size
    · simp [free, provenance, found, dead, wrongBase, wrongKind, wrongSize] at success
    by_cases wrongAlign : align ≠ allocation.align
    · simp [free, provenance, found, dead, wrongBase, wrongKind, wrongSize,
        wrongAlign] at success
    exact ⟨replace second id { allocation with live := false }, by
      simp [free, provenance, otherFound, dead, wrongBase, wrongKind, wrongSize,
        wrongAlign]⟩

#print axioms store_preserves_next
#print axioms checked_id
#print axioms store_preserves_other
#print axioms free_preserves_other
#print axioms fresh_round_preserves_other
#print axioms checkPtr_frame
#print axioms load_frame
#print axioms free_frame

end AnnealResearch.ProofCostFrames
