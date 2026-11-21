import Toy.PlaceEval.Programs

/-!
# Definition examples

For each core definition, intended positive examples (instances it admits) and negative
examples (instances it must reject), all fully proved.
-/

namespace Toy.PlaceEval

/-- An example memory: allocation `0` is live at `[4, 8)`, allocation `1` is freed at
`[8, 10)`; cells `4, 5` hold the pointer `⟨some 0, 6⟩`, cell `6` holds byte `3`, cell `7`
is uninitialized. -/
def mEx : Mem :=
  ⟨[⟨4, 4, true⟩, ⟨8, 2, false⟩],
   [(4, .ptrFrag ⟨some 0, 6⟩ 0), (5, .ptrFrag ⟨some 0, 6⟩ 1), (6, .byte 3)]⟩

/-- An example state: local `0` is backed by allocation `0`; local `1` is unallocated. -/
def stEx : State := ⟨mEx, [some 0, none]⟩

/-! ### `aligned` (including the degenerate edge `al = 0`) -/
theorem aligned_ex_pos : aligned 2 4 = true := by decide
theorem aligned_ex_neg : aligned 2 5 = false := by decide
theorem aligned_zero_ex_pos : aligned 0 0 = true := by decide
theorem aligned_zero_ex_neg : aligned 0 3 = false := by decide

/-! ### `Mem.inBounds`, `Mem.dereferenceable`, `Mem.offsetInbounds` -/
theorem inBounds_ex_pos : mEx.inBounds ⟨some 0, 4⟩ 4 = true := by decide
theorem inBounds_ex_pos_end : mEx.inBounds ⟨some 0, 6⟩ 2 = true := by decide
theorem inBounds_ex_neg_past : mEx.inBounds ⟨some 0, 6⟩ 3 = false := by decide
theorem inBounds_ex_neg_freed : mEx.inBounds ⟨some 1, 8⟩ 1 = false := by decide
theorem inBounds_ex_neg_noprov : mEx.inBounds ⟨none, 4⟩ 1 = false := by decide
theorem dereferenceable_ex_pos_zero_null : mEx.dereferenceable ⟨none, 0⟩ 0 = true := by decide
theorem dereferenceable_ex_neg_freed : mEx.dereferenceable ⟨some 1, 8⟩ 1 = false := by decide
theorem offsetInbounds_ex_pos_zero_null : mEx.offsetInbounds ⟨none, 0⟩ 0 = true := by decide
theorem offsetInbounds_ex_pos_one_past_end : mEx.offsetInbounds ⟨some 0, 4⟩ 4 = true := by decide
theorem offsetInbounds_ex_neg_past_end : mEx.offsetInbounds ⟨some 0, 4⟩ 5 = false := by decide
theorem offsetInbounds_ex_neg_freed : mEx.offsetInbounds ⟨some 1, 8⟩ 1 = false := by decide
theorem offsetInbounds_ex_neg_null : mEx.offsetInbounds ⟨none, 0⟩ 2 = false := by decide

/-! ### `decodePtr` and `Ty.decode` -/
theorem decodePtr_ex_pos_frags :
    decodePtr [.ptrFrag ⟨some 0, 6⟩ 0, .ptrFrag ⟨some 0, 6⟩ 1] = some ⟨some 0, 6⟩ := by decide
theorem decodePtr_ex_pos_bytes : decodePtr [.byte 1, .byte 2] = some ⟨none, 513⟩ := by decide
theorem decodePtr_ex_neg_mismatch :
    decodePtr [.ptrFrag ⟨some 0, 6⟩ 0, .ptrFrag ⟨some 1, 6⟩ 1] = none := by decide
theorem decodePtr_ex_neg_uninit : decodePtr [.uninit, .uninit] = none := by decide
theorem decode_enum_ex_pos : bool2.decode [.byte 1] = some (.int 1) := by decide
theorem decode_enum_ex_neg_tag : bool2.decode [.byte 2] = none := by decide
theorem decode_int_ex_neg_uninit : u8.decode [.uninit] = none := by decide

/-! ### `Mem.load` -/
theorem load_ex_pos_ptr : mEx.load ⟨some 0, 4⟩ .ptr = some (.ptr ⟨some 0, 6⟩) := by decide
theorem load_ex_neg_misaligned : mEx.load ⟨some 0, 5⟩ .ptr = none := by decide
theorem load_ex_pos_int : mEx.load ⟨some 0, 6⟩ u8 = some (.int 3) := by decide
theorem load_ex_neg_uninit : mEx.load ⟨some 0, 7⟩ u8 = none := by decide
theorem load_ex_neg_freed : mEx.load ⟨some 1, 8⟩ u8 = none := by decide
/-- Degenerate edge: a zero-size integer load succeeds with `0`, even through the null
pointer. -/
theorem load_ex_pos_zero_size_null : mEx.load ⟨none, 0⟩ (.int 0 1) = some (.int 0) := by decide

/-! ### `Mem.store` -/
theorem store_ex_pos : (mEx.store ⟨some 0, 6⟩ u8 (.int 9)).isSome = true := by decide
theorem store_ex_neg_freed : mEx.store ⟨some 1, 8⟩ u8 (.int 9) = none := by decide
theorem store_ex_neg_misaligned : mEx.store ⟨some 0, 5⟩ .ptr (.int 9) = none := by decide

/-! ### `DerefLoadOk` -/
theorem derefLoadOk_ex_pos : DerefLoadOk mEx ⟨some 0, 4⟩ :=
  (loadPtr_isSome_iff _ _).1 (by decide)
theorem derefLoadOk_ex_neg_not_a_pointer : ¬ DerefLoadOk mEx ⟨some 0, 6⟩ := fun h =>
  absurd ((loadPtr_isSome_iff _ _).2 h) (by decide)

/-! ### `evalPlace` -/
theorem evalPlace_ex_pos_deref : evalPlace stEx ⟨0, [.deref]⟩ = some ⟨some 0, 6⟩ := by decide
/-- The second `deref` loads cells `6, 7` (byte, uninitialized): not a pointer. -/
theorem evalPlace_ex_neg_inner_not_pointer : evalPlace stEx ⟨0, [.deref, .deref]⟩ = none := by
  decide
theorem evalPlace_ex_neg_misaligned_load : evalPlace stEx ⟨0, [.field 1, .deref]⟩ = none := by
  decide
theorem evalPlace_ex_neg_unallocated_local : evalPlace stEx ⟨1, []⟩ = none := by decide
/-- The result of a `deref` need not be dereferenceable: here it is one past the end. -/
theorem evalPlace_ex_pos_field_one_past_end :
    evalPlace stEx ⟨0, [.deref, .field 2]⟩ = some ⟨some 0, 8⟩ := by decide
theorem evalPlace_ex_neg_field_past_end : evalPlace stEx ⟨0, [.deref, .field 3]⟩ = none := by
  decide

/-! ### `RefOk` -/
theorem refOk_ex_pos : RefOk mEx ⟨some 0, 6⟩ ⟨2, 2⟩ := by decide
theorem refOk_ex_neg_misaligned : ¬ RefOk mEx ⟨some 0, 5⟩ ⟨2, 2⟩ := by decide
theorem refOk_ex_neg_null_zero_size : ¬ RefOk mEx ⟨none, 0⟩ ⟨0, 1⟩ := by decide
theorem refOk_ex_pos_dangling_zero_size : RefOk mEx ⟨none, 8⟩ ⟨0, 1⟩ := by decide
theorem refOk_ex_neg_dangling : ¬ RefOk mEx ⟨some 1, 8⟩ ⟨2, 2⟩ := by decide
/-- Degenerate edge: with pointee alignment `0`, `RefOk` fails for every non-null address. -/
theorem refOk_ex_neg_align_zero : ¬ RefOk mEx ⟨some 0, 4⟩ ⟨0, 0⟩ := by decide

/-! ### `allocate` and `deallocate` -/
/-- Under `fresh`, a range overlapping a live allocation is refused: address `2 * (1 + 1) = 4`
overlaps `[4, 8)`. -/
theorem allocate_fresh_ex_neg_overlap :
    allocate (.fresh fun _ => 1) stEx 1 ⟨2, 2⟩ = none := by decide
/-- Under `fresh`, a range overlapping only a freed allocation is accepted (address
`2 * (4 + 1) = 10`; also `8` would be accepted, as `[8, 10)` is freed). -/
theorem allocate_fresh_ex_pos : (allocate (.fresh fun _ => 4) stEx 1 ⟨2, 2⟩).isSome = true := by
  decide
theorem allocate_fresh_ex_pos_reuse_freed :
    (allocate (.fresh fun _ => 3) stEx 1 ⟨2, 2⟩).isSome = true := by decide
/-- Under `slots`, there is no overlap check. -/
theorem allocate_slots_ex_pos_overlap :
    (allocate (.slots fun _ => 4) stEx 1 ⟨2, 2⟩).isSome = true := by decide
/-- Freshly allocated memory is uninitialized, even where an earlier write left a value. -/
theorem allocate_ex_uninit :
    (allocate (.slots fun _ => 4) stEx 1 ⟨2, 2⟩).map (fun st => st.mem.get 4) = some .uninit := by
  decide
theorem deallocate_ex : (deallocate stEx 0).basePtr 0 = none := by decide
theorem deallocate_ex_noop : deallocate (deallocate stEx 0) 0 = deallocate stEx 0 := by decide

/-! ### `Prog.hasMarkers`, `eraseMarkers`, `deleteStmt`, `setTerm`, `setStmt` -/
theorem hasMarkers_ex_pos : pStale.hasMarkers 0 = true := by decide
theorem hasMarkers_ex_neg : pAddrCmp.hasMarkers 0 = false := by decide
theorem eraseMarkers_ex : (eraseMarkers pStale 0).blocks =
    [⟨[.assign ⟨0, []⟩ u8 (.use (.const (.int 5))), .emit (.use (.copy ⟨0, []⟩ u8))], .halt⟩] := by
  decide
theorem eraseMarkers_ex_hasMarkers : (eraseMarkers pStale 0).hasMarkers 0 = false := by decide
theorem eraseMarkers_ex_other_local : eraseMarkers pAddrCmp 0 = pAddrCmp := by decide
theorem deleteStmt_ex : (deleteStmt pDerefUninit 0 2).blocks =
    [⟨[.storageLive 1, .assign ⟨0, []⟩ .ptr (.rawRef ⟨1, []⟩)], .halt⟩] := by decide
theorem deleteStmt_ex_out_of_range : deleteStmt pDerefUninit 3 0 = pDerefUninit := by decide
theorem setTerm_ex : (setTerm pSwUninit 0 (.goto 1)).blk 0 = ⟨[], .goto 1⟩ := by decide
theorem setStmt_ex : ((setStmt pRawDangling 0 3 refDerefStmt).blk 0).stmts[3]? =
    some refDerefStmt := by decide
/-- Out-of-range labels and indices leave the program unchanged. -/
theorem setTerm_ex_out_of_range : setTerm pSwUninit 9 (.goto 1) = pSwUninit := by decide
theorem setStmt_ex_out_of_range_blk : setStmt pRawDangling 9 0 refDerefStmt = pRawDangling := by
  decide
theorem setStmt_ex_out_of_range_idx : setStmt pRawDangling 0 99 refDerefStmt = pRawDangling := by
  decide

/-! ### `ImprovesPP` -/
theorem improvesPP_ex_pos : ImprovesPP (.term [1]) (.wrong []) := improvesPP_wrong_nil _
theorem improvesPP_ex_pos_prefix : ImprovesPP (.term [1, 2]) (.wrong [1]) :=
  Or.inr ⟨[1], rfl, ⟨[2], rfl⟩⟩
theorem improvesPP_ex_neg : ¬ ImprovesPP (.term [1]) (.term [0]) := by
  rintro (h | ⟨t, h, _⟩) <;> cases h
theorem improvesPP_ex_neg_ub : ¬ ImprovesPP (.wrong []) (.term []) := by
  rintro (h | ⟨t, h, _⟩) <;> cases h
theorem improvesPP_ex_neg_nonprefix : ¬ ImprovesPP (.term [1]) (.wrong [2]) := by
  rintro (h | ⟨t, h, ht⟩)
  · cases h
  · cases h
    obtain ⟨u, hu⟩ := ht
    simp at hu

/-! ### `NoAddrObs` -/
theorem noAddrObs_ex_pos : NoAddrObs pStale := by
  intro b hb s hs rv hrv
  simp [pStale] at hb
  subst hb
  simp at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp [Stmt.rvalue?] at hrv <;> subst hrv <;> rfl
theorem noAddrObs_ex_neg : ¬ NoAddrObs pAddrCmp := by
  intro h
  have := h (pAddrCmp.blk 0) (by decide)
    (.emit (.ptrEq (.copy ⟨0, []⟩ .ptr) (.copy ⟨0, [.field 2]⟩ .ptr))) (by decide) _ rfl
  exact absurd this (by decide)
/-! ### `evalPrefix`, `State.readIndex` -/
theorem evalPrefix_ex_pos : evalPrefix stEx ⟨0, [.deref, .deref]⟩ 1 = some ⟨some 0, 6⟩ := by decide
theorem evalPrefix_ex_neg_unallocated : evalPrefix stEx ⟨1, []⟩ 0 = none := by decide
/-- A state whose local `0` (allocation `0`, at `[4, 8)`) holds the byte `1` at address `4`. -/
def stIdx : State := ⟨⟨[⟨4, 4, true⟩], [(4, .byte 1)]⟩, [some 0]⟩
theorem readIndex_ex_pos : stIdx.readIndex 0 = some 1 := by decide
theorem readIndex_ex_neg_unallocated : stEx.readIndex 1 = none := by decide
theorem readIndex_ex_neg_pointer_bytes : stEx.readIndex 0 = none := by decide
theorem evalPlace_ex_pos_index : evalPlace stIdx ⟨0, [.index 0 2]⟩ = some ⟨some 0, 6⟩ := by decide
theorem evalPlace_ex_neg_index_past_end : evalPlace stIdx ⟨0, [.index 0 5]⟩ = none := by decide
/-- A state whose local `0` (allocation `0`, at `[4, 8)`) holds a pointer into the freed
allocation `1` (at `[8, 10)`), and whose local `1` (allocation `2`, at `[12, 13)`) holds the
byte `3`. -/
def stDangIdx : State :=
  ⟨⟨[⟨4, 4, true⟩, ⟨8, 2, false⟩, ⟨12, 1, true⟩],
    [(4, .ptrFrag ⟨some 1, 8⟩ 0), (5, .ptrFrag ⟨some 1, 8⟩ 1), (12, .byte 3)]⟩, [some 0, some 2]⟩
/-- Degenerate edge: an `index` with element size `0` (offset `3 * 0 = 0`) is not checked,
even on a dangling pointer. -/
theorem evalPlace_ex_pos_index_zero_size :
    evalPlace stDangIdx ⟨0, [.deref, .index 1 0]⟩ = some ⟨some 1, 8⟩ := by decide
/-- The same index with element size `1` (offset `3`) is UB on the dangling pointer. -/
theorem evalPlace_ex_neg_index_dangling :
    evalPlace stDangIdx ⟨0, [.deref, .index 1 1]⟩ = none := by decide
/-- A frame entry naming a missing allocation: `basePtr` fails. -/
def stMissingAlloc : State := ⟨⟨[], []⟩, [some 0]⟩
/-- A frame entry naming a freed allocation (not reachable by the semantics). -/
def stFreedInFrame : State := ⟨⟨[⟨4, 4, false⟩], []⟩, [some 0]⟩
theorem basePtr_missing_alloc_eq_none :
    stMissingAlloc.allocOf 0 = some 0 ∧ stMissingAlloc.basePtr 0 = none ∧
      evalPlace stMissingAlloc ⟨0, []⟩ = none := by decide
theorem basePtr_freed_in_frame_eq_some :
    stFreedInFrame.basePtr 0 = some ⟨some 0, 4⟩ ∧
      evalPlace stFreedInFrame ⟨0, []⟩ = some ⟨some 0, 4⟩ := by decide
theorem evalInt_ex_pos : (Operand.copy ⟨0, []⟩ u8).evalInt stIdx = some 1 := by decide

end Toy.PlaceEval
