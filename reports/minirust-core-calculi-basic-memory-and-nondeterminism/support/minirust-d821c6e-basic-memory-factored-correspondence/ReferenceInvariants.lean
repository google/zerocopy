import AnnealResearch.MiniRustReference

/-!
Structural admission and preservation for the audited reference kernel. These
premises contain no NoUB, successful-access, liveness, bounds, access-alignment,
or correct-free assumption. Unsafe programs remain admitted. This file was
written without executing Lean; the parent owns compilation and diagnostics.
-/
namespace AnnealResearch.MiniRustReference

 theorem alignWF_nonzero {align : Nat} (wf : AlignWF align) : align ≠ 0 := by
  rcases wf with ⟨exponent, rfl⟩
  exact Nat.ne_of_gt (Nat.two_pow_pos exponent)

 theorem emptyStateWF : StateWF empty := by
  constructor
  · intro id
    simp [empty]
  · intro id allocation found
    simp [empty] at found
  · intro id allocation offset found inside
    simp [empty] at found
  · intro id first otherId second found otherFound different firstLive secondLive
    simp [empty] at found

 theorem byteWF_mono {s t : State} {byte : Byte}
    (nextLe : s.next ≤ t.next) (known : ByteWF s byte) : ByteWF t byte := by
  cases byte with
  | uninit => trivial
  | init number fragment =>
    cases fragment with
    | none => trivial
    | some fragment =>
      exact Nat.lt_of_lt_of_le known nextLe

 theorem checkPtr_not_unsupported {s : State} {p : Ptr} (len : Nat)
    (wf : StateWF s) (pwf : PtrWF s p) :
    checkPtr s p len ≠ .unsupported := by
  by_cases zero : len = 0
  · simp [checkPtr, zero]
  · cases provenance : p.provenance with
    | none => simp [checkPtr, zero, provenance]
    | some id =>
      have minted : id < s.next := by simpa [provenance] using pwf.2
      obtain ⟨allocation, found⟩ := (wf.domain id).2 minted
      by_cases dead : allocation.live = false <;>
        by_cases below : p.addr < allocation.base <;>
        by_cases beyond : allocation.size < p.addr - allocation.base + len <;>
        simp [checkPtr, zero, provenance, found, dead, below, beyond]

 theorem load_not_unsupported {s : State} {p : Ptr} (len align : Nat)
    (wf : StateWF s) (pwf : PtrWF s p) (awf : AlignWF align) :
    load s p len align ≠ .unsupported := by
  have nonzero := alignWF_nonzero awf
  by_cases aligned : p.addr % align = 0
  · cases checked : checkPtr s p len with
    | ok span =>
      cases span <;> simp [load, nonzero, aligned, checked]
    | ub error => simp [load, nonzero, aligned, checked]
    | noChoice => simp [load, nonzero, aligned, checked]
    | unsupported => exact False.elim (checkPtr_not_unsupported len wf pwf checked)
  · simp [load, nonzero, aligned]

 theorem store_not_unsupported {s : State} {p : Ptr} (bytes : List Byte) (align : Nat)
    (wf : StateWF s) (pwf : PtrWF s p) (awf : AlignWF align) :
    store s p bytes align ≠ .unsupported := by
  have nonzero := alignWF_nonzero awf
  by_cases aligned : p.addr % align = 0
  · cases checked : checkPtr s p bytes.length with
    | ok span =>
      cases span <;> simp [store, nonzero, aligned, checked]
    | ub error => simp [store, nonzero, aligned, checked]
    | noChoice => simp [store, nonzero, aligned, checked]
    | unsupported =>
      exact False.elim (checkPtr_not_unsupported bytes.length wf pwf checked)
  · simp [store, nonzero, aligned]

 theorem free_not_unsupported {s : State} {p : Ptr} (kind : Kind) (size align : Nat)
    (wf : StateWF s) (pwf : PtrWF s p) :
    free s p kind size align ≠ .unsupported := by
  cases provenance : p.provenance with
  | none => simp [free, provenance]
  | some id =>
    have minted : id < s.next := by simpa [provenance] using pwf.2
    obtain ⟨allocation, found⟩ := (wf.domain id).2 minted
    by_cases dead : allocation.live = false <;>
    by_cases base : p.addr = allocation.base <;>
    by_cases kindEq : kind = allocation.kind <;>
    by_cases sizeEq : size = allocation.size <;>
    by_cases alignEq : align = allocation.align <;>
    simp [free, provenance, found, dead, base, kindEq, sizeEq, alignEq]

/-- Replacing one record may change cells and deactivate it; geometry stays
    fixed. This handles store and free without assuming either operation safe. -/
 theorem replace_preserves_StateWF {s : State} {id : Nat} {old fresh : Allocation}
    (wf : StateWF s) (found : s.allocations id = some old)
    (base : fresh.base = old.base) (size : fresh.size = old.size)
    (align : fresh.align = old.align)
    (live : fresh.live = true → old.live = true)
    (known : ∀ offset, offset < fresh.size → ByteWF s (fresh.data offset)) :
    StateWF (replace s id fresh) := by
  have info : ∀ current allocation,
      (replace s id fresh).allocations current = some allocation →
      ∃ original, s.allocations current = some original ∧
        allocation.base = original.base ∧ allocation.size = original.size ∧
        allocation.align = original.align ∧
        (allocation.live = true → original.live = true) := by
    intro current allocation currentFound
    by_cases equal : current = id
    · subst current
      have same : fresh = allocation := by simpa [replace] using currentFound
      subst allocation
      exact ⟨old, found, base, size, align, live⟩
    · have original : s.allocations current = some allocation := by
        simpa [replace, equal] using currentFound
      exact ⟨allocation, original, rfl, rfl, rfl, fun h => h⟩
  constructor
  · intro current
    by_cases equal : current = id
    · subst current
      constructor
      · intro _
        exact (wf.domain id).1 ⟨old, found⟩
      · intro _
        exact ⟨fresh, by simp [replace]⟩
    · simpa [replace, equal] using wf.domain current
  · intro current allocation currentFound
    obtain ⟨original, originalFound, hb, hs, ha, _⟩ := info current allocation currentFound
    simpa only [hb, hs, ha] using wf.geometry current original originalFound
  · intro current allocation offset currentFound inside
    by_cases equal : current = id
    · subst current
      have same : fresh = allocation := by simpa [replace] using currentFound
      subst allocation
      exact known offset inside
    · have original : s.allocations current = some allocation := by
        simpa [replace, equal] using currentFound
      exact wf.knownFragments current allocation offset original inside
  · intro current first other second firstFound secondFound different firstLive secondLive
    obtain ⟨firstOld, hf, hfb, hfs, _, hfl⟩ := info current first firstFound
    obtain ⟨secondOld, hs, hsb, hss, _, hsl⟩ := info other second secondFound
    have separated := wf.liveSeparation current firstOld other secondOld hf hs
      different (hfl firstLive) (hsl secondLive)
    simpa only [overlaps, hfb, hfs, hsb, hss] using separated

 theorem free_success_shape {s after : State} {p : Ptr} {kind : Kind}
    {size align : Nat} (success : free s p kind size align = .ok after) :
    ∃ id allocation, s.allocations id = some allocation ∧
      after = replace s id { allocation with live := false } := by
  cases provenance : p.provenance with
  | none => simp [free, provenance] at success
  | some id =>
    cases found : s.allocations id with
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
              · exact ⟨id, allocation, found, (Result.ok.inj success).symm⟩

 theorem free_preserves_StateWF {s after : State} {p : Ptr} {kind : Kind}
    {size align : Nat} (wf : StateWF s)
    (success : free s p kind size align = .ok after) : StateWF after := by
  obtain ⟨id, allocation, found, rfl⟩ := free_success_shape success
  refine replace_preserves_StateWF (fresh := { allocation with live := false })
    wf found rfl rfl rfl ?_ ?_
  · intro impossible
    cases impossible
  · intro offset inside
    exact wf.knownFragments id allocation offset found inside

 theorem checkPtr_some_lookup {s : State} {p : Ptr} {len : Nat} {checked : CheckedSpan}
    (success : checkPtr s p len = .ok (some checked)) :
    s.allocations checked.id = some checked.allocation := by
  by_cases zero : len = 0
  · simp [checkPtr, zero] at success
  · cases provenance : p.provenance with
    | none => simp [checkPtr, zero, provenance] at success
    | some id =>
      cases found : s.allocations id with
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
              cases same
              exact found

/-- A finite byte register admission. It constrains provenance identities and
    deliberately permits both Uninit and arbitrary numeric byte values. -/
def BytesWF (s : State) (bytes : List Byte) : Prop :=
  ∀ index, index < bytes.length → ByteWF s (bytes.getD index .uninit)

 theorem store_preserves_StateWF {s after : State} {p : Ptr} {bytes : List Byte}
    {align : Nat} (wf : StateWF s) (bytesWF : BytesWF s bytes)
    (success : store s p bytes align = .ok after) : StateWF after := by
  by_cases zeroAlign : align = 0
  · simp [store, zeroAlign] at success
  · by_cases misaligned : p.addr % align ≠ 0
    · simp [store, zeroAlign, misaligned] at success
    · simp only [store, ite_eq_right zeroAlign, ite_eq_right misaligned] at success
      cases checked : checkPtr s p bytes.length with
      | ub error => simp [checked] at success
      | noChoice => simp [checked] at success
      | unsupported => simp [checked] at success
      | ok span =>
        cases span with
        | none =>
          simp only [checked] at success
          have same : s = after := Result.ok.inj success
          exact same ▸ wf
        | some span =>
          simp only [checked] at success
          have found := checkPtr_some_lookup checked
          have same := Result.ok.inj success
          rw [← same]
          refine replace_preserves_StateWF (fresh := { span.allocation with
            data := fun index => if span.offset ≤ index ∧ index < span.offset + bytes.length
              then bytes.getD (index - span.offset) .uninit else span.allocation.data index })
            wf found rfl rfl rfl (fun h => h) ?_
          intro index inside
          dsimp
          split
          · rename_i inRange
            exact bytesWF (index - span.offset) (by omega)
          · exact wf.knownFragments span.id span.allocation index found inside

 theorem overlaps_symmetric (first second : Allocation) :
    overlaps first second.base second.size ↔ overlaps second first.base first.size := by
  unfold overlaps
  omega

 theorem no_overlap_of_candidate {s : State} {size align addr id : Nat}
    {allocation : Allocation} (wf : StateWF s)
    (candidate : AllocationCandidate s size align addr)
    (found : s.allocations id = some allocation) (live : allocation.live = true) :
    ¬ overlaps allocation addr size := by
  have minted : id < s.next := (wf.domain id).1 ⟨allocation, found⟩
  have all := List.any_eq_false.mp candidate.2.2.2
  have absent := all id (List.mem_range.mpr minted)
  simpa [liveOverlap, found, live] using absent

/-- Geometry and identity facts yielded by a successful allocator branch. -/
def freshAllocation (kind : Kind) (size align addr : Nat) : Allocation :=
  { base := addr, size, align, kind, live := true, data := fun _ => .uninit }

 theorem allocateAt_success_shape {s after : State} {p : Ptr} {kind : Kind}
    {size align addr : Nat} (success : allocateAt s kind size align addr = .ok (p, after)) :
    p = { addr, provenance := some s.next } ∧
    after = append s (freshAllocation kind size align addr) ∧
    size < sizeLimit ∧ AllocationCandidate s size align addr := by
  by_cases large : sizeLimit ≤ size
  · simp [allocateAt, large] at success
  · by_cases zeroAlign : align = 0
    · simp [allocateAt, large, zeroAlign] at success
    · by_cases candidate : AllocationCandidate s size align addr
      · simp only [allocateAt, ite_eq_right large, ite_eq_right zeroAlign, ite_eq_left candidate] at success
        have same := Result.ok.inj success
        exact ⟨(congrArg Prod.fst same).symm, (congrArg Prod.snd same).symm,
          Nat.lt_of_not_ge large, candidate⟩
      · simp [allocateAt, large, zeroAlign, candidate] at success

 theorem append_preserves_StateWF {s : State} {fresh : Allocation} (wf : StateWF s)
    (geometry : 0 < fresh.base ∧ AlignWF fresh.align ∧ fresh.base % fresh.align = 0 ∧
      fresh.size < sizeLimit ∧ fresh.base + fresh.size < addressLimit)
    (known : ∀ offset, offset < fresh.size → ByteWF (append s fresh) (fresh.data offset))
    (separate : ∀ id old, s.allocations id = some old → old.live = true →
      ¬ overlaps old fresh.base fresh.size) : StateWF (append s fresh) := by
  have info : ∀ id allocation, (append s fresh).allocations id = some allocation →
      (id = s.next ∧ allocation = fresh) ∨
      (id ≠ s.next ∧ s.allocations id = some allocation) := by
    intro id allocation found
    by_cases equal : id = s.next
    · left
      have same : fresh = allocation := by simpa [append, equal] using found
      exact ⟨equal, same.symm⟩
    · right
      exact ⟨equal, by simpa [append, equal] using found⟩
  constructor
  · intro id
    by_cases equal : id = s.next
    · subst id
      simp [append]
    · constructor
      · rintro ⟨allocation, found⟩
        have oldFound : s.allocations id = some allocation := by
          simpa [append, equal] using found
        have minted := (wf.domain id).1 ⟨allocation, oldFound⟩
        dsimp [append]
        omega
      · intro minted
        have oldMinted : id < s.next := by
          change id < s.next + 1 at minted
          omega
        obtain ⟨allocation, found⟩ := (wf.domain id).2 oldMinted
        exact ⟨allocation, by simpa [append, equal] using found⟩
  · intro id allocation found
    rcases info id allocation found with ⟨_, rfl⟩ | ⟨_, oldFound⟩
    · exact geometry
    · exact wf.geometry id allocation oldFound
  · intro id allocation offset found inside
    rcases info id allocation found with ⟨_, rfl⟩ | ⟨_, oldFound⟩
    · exact known offset inside
    · apply byteWF_mono (by change s.next ≤ s.next + 1; omega)
      exact wf.knownFragments id allocation offset oldFound inside
  · intro id first other second firstFound secondFound different firstLive secondLive
    rcases info id first firstFound with ⟨firstId, rfl⟩ | ⟨firstOldId, firstOld⟩
    · rcases info other second secondFound with ⟨secondId, rfl⟩ | ⟨_, secondOld⟩
      · exact False.elim (different (firstId.trans secondId.symm))
      · have noOverlap := separate other second secondOld secondLive
        exact fun overlap => noOverlap ((overlaps_symmetric _ second).1 overlap)
    · rcases info other second secondFound with ⟨_, rfl⟩ | ⟨_, secondOld⟩
      · exact separate id first firstOld firstLive
      · exact wf.liveSeparation id first other second firstOld secondOld different
          firstLive secondLive

 theorem allocateAt_preserves_StateWF {s after : State} {p : Ptr} {kind : Kind}
    {size align addr : Nat} (wf : StateWF s) (awf : AlignWF align)
    (success : allocateAt s kind size align addr = .ok (p, after)) : StateWF after := by
  obtain ⟨_, rfl, small, candidate⟩ := allocateAt_success_shape success
  apply append_preserves_StateWF wf
  · exact ⟨candidate.1, awf, candidate.2.1, small, candidate.2.2.1⟩
  · intro offset inside
    trivial
  · intro id old found live
    exact no_overlap_of_candidate wf candidate found live

/-- Fresh identity is independent of numeric address reuse; freeing never
    changes next and a successful reallocation always issues the old next. -/
 theorem allocation_fresh_identity {s after : State} {p : Ptr} {kind : Kind}
    {size align addr : Nat} (success : allocateAt s kind size align addr = .ok (p, after)) :
    p.provenance = some s.next ∧ after.next = s.next + 1 := by
  obtain ⟨rfl, rfl, _, _⟩ := allocateAt_success_shape success
  exact ⟨rfl, rfl⟩

 theorem free_preserves_next {s after : State} {p : Ptr} {kind : Kind} {size align : Nat}
    (success : free s p kind size align = .ok after) : after.next = s.next := by
  obtain ⟨_, _, _, rfl⟩ := free_success_shape success
  rfl

#print axioms emptyStateWF
#print axioms checkPtr_not_unsupported
#print axioms load_not_unsupported
#print axioms store_not_unsupported
#print axioms free_not_unsupported
#print axioms free_preserves_StateWF
#print axioms store_preserves_StateWF
#print axioms allocateAt_preserves_StateWF
#print axioms allocation_fresh_identity

end AnnealResearch.MiniRustReference
