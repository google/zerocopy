import Toy.PlaceEval.MarkerBehaviours

/-!
# Pointer constants that carry an allocation identifier

Allocation identifiers count the allocations made so far. Erasing the markers of a local
allocates it at entry, which shifts the identifiers of later allocations, so a pointer
constant naming an identifier can denote a different allocation after the edit. The two
programs below exhibit this under a static slot assignment and under fresh addresses.
-/

namespace Toy.PlaceEval

/-- A one-block program with a pointer constant carrying an allocation identifier, run under
the static slot assignment `SEx` (`sEx 0 = 4`, `sEx 1 = 8`, `sEx 2 = 12`). Local `0` has a
`storageDead` marker, so it is not allocated at entry, and local `1` is allocation `0` at
`[8, 9)`; `l1 := 5; l2 := const (ptr ⟨some 0, 8⟩); emit (*l2)` emits `5`. After erasing the
markers of local `0`, local `0` is allocation `0` at `[4, 5)`, and the load through
`⟨some 0, 8⟩` is out of bounds (UB). -/
def pConstProvSlots : Prog :=
  ⟨[⟨1, 1⟩, ⟨1, 1⟩, ptrL],
   [⟨[.assign ⟨1, []⟩ u8 (.use (.const (.int 5))),
      .assign ⟨2, []⟩ .ptr (.use (.const (.ptr ⟨some 0, 8⟩))),
      .emit (.use (.copy ⟨2, [.deref]⟩ u8)),
      .storageDead 0], .halt⟩]⟩

theorem pConstProvSlots_alignPos : ∀ L ∈ pConstProvSlots.locals, 1 ≤ L.align := by
  decide

theorem pConstProvSlots_beh (b : Beh) : HasBeh SEx pConstProvSlots b ↔ b = .term [5] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b

theorem pConstProvSlots_erased_beh (b : Beh) :
    HasBeh SEx (eraseMarkers pConstProvSlots 0) b ↔ b = .wrong [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b

/-- A three-block program with a pointer constant carrying an allocation identifier, for the
fresh-address semantics. Locals: `0` and `1` (one byte; `0` has a `storageDead` marker in
block `1`, so only `1` is allocated at entry, as allocation `0`), `2` (a pointer) and `3`
(one byte). Block `0` stores `&raw l1` in `l2`, stores `1` in `l3` if that pointer has address
`8` (else `0`), and switches on `l3`: on `1`, block `1` writes `5` to `l1`, loads through the
constant pointer `⟨some 0, 8⟩` and emits the byte read; otherwise block `2` emits `9`. In the
source the constant denotes `l1` exactly when `l1` is at address `8`, so every fresh run
emits `5` or `9` (`pConstProvFresh_fresh_beh`). After erasing the markers of local `0`, local
`0` is allocation `0` and the constant no longer denotes `l1`. -/
def pConstProvFresh : Prog :=
  ⟨[⟨1, 1⟩, ⟨1, 1⟩, ptrL, ⟨1, 1⟩],
   [⟨[.assign ⟨2, []⟩ .ptr (.rawRef ⟨1, []⟩),
      .assign ⟨3, []⟩ u8 (.ptrEq (.copy ⟨2, []⟩ .ptr) (.const (.ptr ⟨none, 8⟩)))],
     .switchInt (.copy ⟨3, []⟩ u8) [(1, 1)] 2⟩,
    ⟨[.assign ⟨1, []⟩ u8 (.use (.const (.int 5))),
      .assign ⟨2, []⟩ .ptr (.use (.const (.ptr ⟨some 0, 8⟩))),
      .emit (.use (.copy ⟨2, [.deref]⟩ u8)),
      .storageDead 0], .halt⟩,
    ⟨[.emit (.use (.const (.int 9)))], .halt⟩]⟩

theorem pConstProvFresh_alignPos : ∀ L ∈ pConstProvFresh.locals, 1 ≤ L.align := by
  decide

theorem pConstProvFresh_fresh_beh (ω : Nat → Nat) (b : Beh)
    (h : HasBehIn (.fresh ω) pConstProvFresh b) : b = .term [5] ∨ b = .term [9] := by
  by_cases d1 : disjointRanges (2 * (ω 1 + 1)) 2 (ω 0 + 1) 1 = true
  · by_cases d2a : disjointRanges (ω 2 + 1) 1 (ω 0 + 1) 1 = true
    · by_cases d2b : disjointRanges (ω 2 + 1) 1 (2 * (ω 1 + 1)) 2 = true
      · have d1' := d1; have d2a' := d2a; have d2b' := d2b
        simp only [disjointRanges, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at d1' d2a' d2b'
        have hne01 : ω 0 + 1 ≠ 2 * (ω 1 + 1) := by omega
        have hne01b : ω 0 + 1 ≠ 2 * (ω 1 + 1) + 1 := by omega
        have hne20 : ω 2 + 1 ≠ ω 0 + 1 := by omega
        have hne21 : ω 2 + 1 ≠ 2 * (ω 1 + 1) := by omega
        have hne21b : ω 2 + 1 ≠ 2 * (ω 1 + 1) + 1 := by omega
        have hinit : pConstProvFresh.initState (.fresh ω) = some
            ⟨⟨[⟨ω 0 + 1, 1, true⟩, ⟨2 * (ω 1 + 1), 2, true⟩, ⟨ω 2 + 1, 1, true⟩],
              [(ω 2 + 1, .uninit), (2 * (ω 1 + 1), .uninit),
               (2 * (ω 1 + 1) + 1, .uninit), (ω 0 + 1, .uninit)]⟩,
             [none, some 0, some 1, some 2]⟩ := by
          simp_run [pConstProvFresh, ptrL, d1, d2a, d2b]
        by_cases heq : ω 0 + 1 = 8
        · have hne01' : 2 * (ω 1 + 1) ≠ 8 := by omega
          have hne01b' : 2 * (ω 1 + 1) + 1 ≠ 8 := by omega
          have hne01b'' : 2 * (ω 1 + 1) ≠ 7 := by omega
          have hne20' : ω 2 + 1 ≠ 8 := by omega
          have hrun : run (.fresh ω) pConstProvFresh 9
              (pConstProvFresh.entry 0
                ⟨⟨[⟨ω 0 + 1, 1, true⟩, ⟨2 * (ω 1 + 1), 2, true⟩, ⟨ω 2 + 1, 1, true⟩],
                  [(ω 2 + 1, .uninit), (2 * (ω 1 + 1), .uninit),
                   (2 * (ω 1 + 1) + 1, .uninit), (ω 0 + 1, .uninit)]⟩,
                 [none, some 0, some 1, some 2]⟩) =
              .done [5]
                ⟨⟨[⟨8, 1, true⟩, ⟨2 * (ω 1 + 1), 2, true⟩, ⟨ω 2 + 1, 1, true⟩],
                  [(2 * (ω 1 + 1), .ptrFrag ⟨some 0, 8⟩ 0),
                   (2 * (ω 1 + 1) + 1, .ptrFrag ⟨some 0, 8⟩ 1),
                   (8, .byte 5),
                   (ω 2 + 1, .byte 1),
                   (2 * (ω 1 + 1), .ptrFrag ⟨some 0, 8⟩ 0),
                   (2 * (ω 1 + 1) + 1, .ptrFrag ⟨some 0, 8⟩ 1),
                   (ω 2 + 1, .uninit), (2 * (ω 1 + 1), .uninit),
                   (2 * (ω 1 + 1) + 1, .uninit), (8, .uninit)]⟩,
                 [none, some 0, some 1, some 2]⟩ := by
            rw [heq]
            simp_run [pConstProvFresh, u8, ptrL, hne01', hne01b', hne01b'', hne20', hne21, hne21b]
          exact Or.inl ((hasBehIn_iff_of_done hinit hrun b).1 h)
        · have hrun : run (.fresh ω) pConstProvFresh 6
              (pConstProvFresh.entry 0
                ⟨⟨[⟨ω 0 + 1, 1, true⟩, ⟨2 * (ω 1 + 1), 2, true⟩, ⟨ω 2 + 1, 1, true⟩],
                  [(ω 2 + 1, .uninit), (2 * (ω 1 + 1), .uninit),
                   (2 * (ω 1 + 1) + 1, .uninit), (ω 0 + 1, .uninit)]⟩,
                 [none, some 0, some 1, some 2]⟩) =
              .done [9]
                ⟨⟨[⟨ω 0 + 1, 1, true⟩, ⟨2 * (ω 1 + 1), 2, true⟩, ⟨ω 2 + 1, 1, true⟩],
                  [(ω 2 + 1, .byte 0),
                   (2 * (ω 1 + 1), .ptrFrag ⟨some 0, ω 0 + 1⟩ 0),
                   (2 * (ω 1 + 1) + 1, .ptrFrag ⟨some 0, ω 0 + 1⟩ 1),
                   (ω 2 + 1, .uninit), (2 * (ω 1 + 1), .uninit),
                   (2 * (ω 1 + 1) + 1, .uninit), (ω 0 + 1, .uninit)]⟩,
                 [none, some 0, some 1, some 2]⟩ := by
            simp_run [pConstProvFresh, u8, ptrL, heq, hne01, hne01b, hne20, hne21, hne21b]
          exact Or.inr ((hasBehIn_iff_of_done hinit hrun b).1 h)
      · have hinit : pConstProvFresh.initState (.fresh ω) = none := by
          simp_run [pConstProvFresh, ptrL, d1, d2a, d2b]
        rcases h with ⟨_, h0, _⟩; rw [hinit] at h0; cases h0
    · have hinit : pConstProvFresh.initState (.fresh ω) = none := by
        simp_run [pConstProvFresh, ptrL, d1, d2a]
      rcases h with ⟨_, h0, _⟩; rw [hinit] at h0; cases h0
  · have hinit : pConstProvFresh.initState (.fresh ω) = none := by
      simp_run [pConstProvFresh, ptrL, d1]
    rcases h with ⟨_, h0, _⟩; rw [hinit] at h0; cases h0

theorem pConstProvFresh_ubFree : UBFree .fresh pConstProvFresh := by
  rintro t ⟨ω, h⟩
  rcases pConstProvFresh_fresh_beh ω _ h with h | h <;> cases h

theorem pConstProvFresh_fresh_term5 : HasBeh .fresh pConstProvFresh (.term [5]) :=
  ⟨fun k => [7, 5, 15].getD k 0, (hasBehIn_iff_toBeh (n := 14) (by decide) _).2 (by rfl)⟩

theorem pConstProvFresh_erased_fresh_wrong :
    HasBeh .fresh (eraseMarkers pConstProvFresh 0) (.wrong []) :=
  ⟨fun k => [3, 7, 5, 15].getD k 0, (hasBehIn_iff_toBeh (n := 14) (by decide) _).2 (by rfl)⟩

theorem pConstProvFresh_slots_beh (b : Beh) :
    HasBeh (.slots sEx) pConstProvFresh b ↔ b = .term [5] :=
  beh_slots_eq (n := 14) (by decide) (by rfl) b

theorem pConstProvFresh_erased_slots_beh (b : Beh) :
    HasBeh (.slots sEx) (eraseMarkers pConstProvFresh 0) b ↔ b = .wrong [] :=
  beh_slots_eq (n := 14) (by decide) (by rfl) b

theorem pConstProvFresh_slots_valid :
    RefinesAcross .fresh pConstProvFresh (.slots sEx) pConstProvFresh :=
  refinesAcross_of_src_beh pConstProvFresh_fresh_term5 fun b hb => by
    rw [(pConstProvFresh_slots_beh b).1 hb]; exact improvesPP_refl _

end Toy.PlaceEval
