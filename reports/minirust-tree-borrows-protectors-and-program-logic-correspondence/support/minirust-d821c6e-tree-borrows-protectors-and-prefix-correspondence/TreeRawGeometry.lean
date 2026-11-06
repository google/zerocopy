import AnnealResearch.MiniRustReference

/-!
Standalone raw size-map preservation for the unchanged selected raw kernel.
None versus Some 0 distinguishes absence from a present zero-sized record.
No raw StateWF, liveness, pointer/path, NoUB or byte-provenance hypothesis is
used. Success equations below describe actual returned branches, not domain
premises requiring a future command to succeed. Raw failures return no state;
their memory-wrapper residual policy is a separate composition obligation.
-/

namespace AnnealResearch.TreeRawGeometry

def sizeMap (state : MiniRustReference.State) (id : Nat) : Option Nat :=
  (state.allocations id).map MiniRustReference.Allocation.size

def SameSizeMap (before after : MiniRustReference.State) : Prop :=
  ∀ id, sizeMap before id = sizeMap after id

theorem sameSizeMap_refl (state : MiniRustReference.State) : SameSizeMap state state :=
  fun _ => rfl

theorem sameSizeMap_symm {first second : MiniRustReference.State}
    (same : SameSizeMap first second) : SameSizeMap second first :=
  fun id => (same id).symm

theorem sameSizeMap_trans {first second third : MiniRustReference.State}
    (left : SameSizeMap first second) (right : SameSizeMap second third) :
    SameSizeMap first third := fun id => (left id).trans (right id)

/-- Presence as well as exact size transports at the same allocation ID.
Other allocation fields are deliberately not constrained by this relation. -/
theorem sameSizeMap_lookup {before after : MiniRustReference.State}
    (same : SameSizeMap before after) (id : Nat) (allocation : MiniRustReference.Allocation)
    (found : before.allocations id = some allocation) :
    ∃ other, after.allocations id = some other ∧ other.size = allocation.size := by
  cases otherFound : after.allocations id with
  | none =>
    have impossible := same id
    simp [sizeMap, found, otherFound] at impossible
  | some other =>
    have sizes : some allocation.size = some other.size := by
      simpa only [sizeMap, found, otherFound, Option.map_some] using same id
    exact ⟨other, rfl, (Option.some.inj sizes).symm⟩

theorem replace_preserves_sizeMap {before : MiniRustReference.State} {id : Nat}
    {old fresh : MiniRustReference.Allocation}
    (found : before.allocations id = some old) (sameSize : fresh.size = old.size) :
    SameSizeMap before (MiniRustReference.replace before id fresh) := by
  intro selected
  by_cases sameId : selected = id
  · subst selected
    simp [sizeMap, MiniRustReference.replace, found, sameSize]
  · simp [sizeMap, MiniRustReference.replace, sameId]

/-- Exact actual-span lookup, proved here from the frozen raw definition so
this layer imports no tree or structural-invariant proof dependency. -/
theorem checkPtr_some_lookup {state : MiniRustReference.State} {pointer : MiniRustReference.Ptr}
    {size : Nat} {span : MiniRustReference.CheckedSpan}
    (success : MiniRustReference.checkPtr state pointer size = .ok (some span)) :
    state.allocations span.id = some span.allocation := by
  by_cases zero : size = 0
  · simp [MiniRustReference.checkPtr, zero] at success
  · cases provenance : pointer.provenance with
    | none => simp [MiniRustReference.checkPtr, zero, provenance] at success
    | some id =>
      cases found : state.allocations id with
      | none => simp [MiniRustReference.checkPtr, zero, provenance, found] at success
      | some allocation =>
        simp only [MiniRustReference.checkPtr, ite_eq_right zero, provenance, found] at success
        split at success
        · cases success
        · split at success
          · cases success
          · split at success
            · cases success
            · have same := Option.some.inj (MiniRustReference.Result.ok.inj success)
              cases same
              exact found

/-- A successful raw load returns the entire original raw state, independent
of the returned bytes, requested alignment, provenance or record geometry. -/
theorem load_success_raw {before after : MiniRustReference.State}
    {pointer : MiniRustReference.Ptr} {size align : Nat} {bytes : List MiniRustReference.Byte}
    (success : MiniRustReference.load before pointer size align = .ok (bytes, after)) :
    after = before := by
  by_cases zeroAlign : align = 0
  · simp [MiniRustReference.load, zeroAlign] at success
  · by_cases misaligned : pointer.addr % align ≠ 0
    · simp [MiniRustReference.load, zeroAlign, misaligned] at success
    · simp only [MiniRustReference.load, ite_eq_right zeroAlign, ite_eq_right misaligned] at success
      cases checked : MiniRustReference.checkPtr before pointer size with
      | ub fault => simp [checked] at success
      | unsupported => simp [checked] at success
      | noChoice => simp [checked] at success
      | ok maybeSpan =>
        cases maybeSpan with
        | none =>
          simp only [checked] at success
          exact (congrArg Prod.snd (MiniRustReference.Result.ok.inj success)).symm
        | some span =>
          simp only [checked] at success
          exact (congrArg Prod.snd (MiniRustReference.Result.ok.inj success)).symm

theorem load_preserves_sizeMap {before after : MiniRustReference.State}
    {pointer : MiniRustReference.Ptr} {size align : Nat} {bytes : List MiniRustReference.Byte}
    (success : MiniRustReference.load before pointer size align = .ok (bytes, after)) :
    SameSizeMap before after := by
  rw [load_success_raw success]
  exact sameSizeMap_refl before

/-- Only the actual store-success branch is inspected; arbitrary bytes are
allowed, including Uninit and fragments without a ByteWF premise. -/
theorem store_preserves_sizeMap {before after : MiniRustReference.State}
    {pointer : MiniRustReference.Ptr} {bytes : List MiniRustReference.Byte} {align : Nat}
    (success : MiniRustReference.store before pointer bytes align = .ok after) :
    SameSizeMap before after := by
  by_cases zeroAlign : align = 0
  · simp [MiniRustReference.store, zeroAlign] at success
  · by_cases misaligned : pointer.addr % align ≠ 0
    · simp [MiniRustReference.store, zeroAlign, misaligned] at success
    · simp only [MiniRustReference.store, ite_eq_right zeroAlign, ite_eq_right misaligned] at success
      cases checked : MiniRustReference.checkPtr before pointer bytes.length with
      | ub fault => simp [checked] at success
      | unsupported => simp [checked] at success
      | noChoice => simp [checked] at success
      | ok maybeSpan =>
        cases maybeSpan with
        | none =>
          simp only [checked] at success
          have same : before = after := MiniRustReference.Result.ok.inj success
          rw [← same]
          exact sameSizeMap_refl before
        | some span =>
          simp only [checked] at success
          have found := checkPtr_some_lookup checked
          have same := MiniRustReference.Result.ok.inj success
          rw [← same]
          exact replace_preserves_sizeMap found rfl

theorem free_success_shape {before after : MiniRustReference.State}
    {pointer : MiniRustReference.Ptr} {kind : MiniRustReference.Kind} {size align : Nat}
    (success : MiniRustReference.free before pointer kind size align = .ok after) :
    ∃ id allocation, before.allocations id = some allocation ∧
      after = MiniRustReference.replace before id { allocation with live := false } := by
  cases provenance : pointer.provenance with
  | none => simp [MiniRustReference.free, provenance] at success
  | some id =>
    cases found : before.allocations id with
    | none => simp [MiniRustReference.free, provenance, found] at success
    | some allocation =>
      simp only [MiniRustReference.free, provenance, found] at success
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
              · exact ⟨id, allocation, found, (MiniRustReference.Result.ok.inj success).symm⟩

/-- Dead records remain present at the same ID and retain their old sizes. -/
theorem free_preserves_sizeMap {before after : MiniRustReference.State}
    {pointer : MiniRustReference.Ptr} {kind : MiniRustReference.Kind} {size align : Nat}
    (success : MiniRustReference.free before pointer kind size align = .ok after) :
    SameSizeMap before after := by
  obtain ⟨id, allocation, found, rfl⟩ := free_success_shape success
  exact replace_preserves_sizeMap found rfl

#print axioms sameSizeMap_refl
#print axioms sameSizeMap_symm
#print axioms sameSizeMap_trans
#print axioms sameSizeMap_lookup
#print axioms replace_preserves_sizeMap
#print axioms checkPtr_some_lookup
#print axioms load_success_raw
#print axioms load_preserves_sizeMap
#print axioms store_preserves_sizeMap
#print axioms free_success_shape
#print axioms free_preserves_sizeMap

end AnnealResearch.TreeRawGeometry
