import ToyRelroGc.Relro.Examples
import ToyRelroGc.Relro.Basic

/-!
Results for the RELRO model: two-phase schedule soundness, placement classification,
lazy binding, page rounding, and relocation order.
-/
namespace Toy.RelroGc

/-! ## Result 1: two-phase schedule soundness -/

/-- **Two-phase schedule soundness.** For the timeline that applies the relocations of `c` in
list order, then the program operations `ops`, with `protect` inserted at position `k`: if
(H1) every relocated slot is mapped writable, (H2) `protect` sits right after the last
relocation and before the first program operation (`k = c.relocs.length`), (H3) `protect`
covers every RELRO byte, and (H4) `protect` covers no mutable byte, then no relocation faults,
the memory at `protect` is the fully relocated image, every program write to a RELRO byte
faults, and every program write to a mutable byte succeeds. -/
theorem twoPhaseGuarantees_of_slotsWritable_of_protectAfterRelocs_of_covers_of_avoids
    (c : Cfg) (sa : SymTab) (ops : List Op) (k : Nat)
    (hWr : RelocSlotsWritable c) (hOrder : k = c.relocs.length)
    (hCover : ProtCoversRelro c) (hAvoid : ProtAvoidsMut c) :
    TwoPhaseGuarantees c sa ops k := by
  subst hOrder
  have ht : timeline c ops c.relocs.length = twoPhase c ops := by
    simp [timeline, twoPhase, insertAt]
  unfold TwoPhaseGuarantees
  simp only [ht]
  rw [trace_twoPhase]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro o ho
    simp only [List.mem_map] at ho
    obtain ⟨r, hr, rfl⟩ := ho
    simp [hWr r hr]
  · simp [tryApplyAll_eq_applyAll _ _ _ _ hWr]
  · intro j a v hj hk
    rw [runT_ops_write c sa ops _ j a v hj]
    have ha : a < c.kinds.length := (List.getElem?_eq_some_iff.mp hk).1
    have hp := hCover a ha hk
    simp [postLoad, hp]
  · intro j a v hj hk
    rw [runT_ops_write c sa ops _ j a v hj]
    have ha : a < c.kinds.length := (List.getElem?_eq_some_iff.mp hk).1
    have hp := hAvoid a ha hk
    have hm : mapWr c.kinds a = true := by simp [mapWr, hk]
    simp [postLoad, hp, hm]

/-- Instance of result 1: all four hypotheses hold for `goodCfg` with `k = 1`. -/
theorem twoPhase_nonvacuity :
    RelocSlotsWritable goodCfg ∧ 1 = goodCfg.relocs.length ∧ ProtCoversRelro goodCfg ∧
      ProtAvoidsMut goodCfg := by
  decide

/-- Countermodel for (H1): the relocated slot is a `.rodata` byte. -/
def cfgSlotRo : Cfg := { goodCfg with kinds := [.ro], prot := fun _ => false }

/-- (H1) is tight: H2–H4 hold, H1 fails, and the relocation faults. -/
theorem twoPhase_cex_slot_not_writable :
    ¬ RelocSlotsWritable cfgSlotRo ∧ 1 = cfgSlotRo.relocs.length ∧ ProtCoversRelro cfgSlotRo ∧
      ProtAvoidsMut cfgSlotRo ∧ ¬ TwoPhaseGuarantees cfgSlotRo sa0 [] 1 := by
  refine ⟨by decide, rfl, by decide, by decide, fun h => ?_⟩
  exact absurd h.1 (by decide)

/-- Countermodel for (H2), first half: two RELRO slots, `protect` between the relocations. -/
def cfgTwoRelro : Cfg where
  kinds := [.relro, .relro]
  init := fun _ => 0
  relocs := [symReloc 0 0, symReloc 1 1]
  prot := rangeMask 0 2
  lazy := []
  stub := 0

/-- (H2) is tight (protect before the last relocation): H1, H3, H4 hold, `k = 1 ≠ 2`, and the
second relocation faults. -/
theorem twoPhase_cex_protect_before_last_reloc :
    RelocSlotsWritable cfgTwoRelro ∧ (1 : Nat) ≠ cfgTwoRelro.relocs.length ∧
      ProtCoversRelro cfgTwoRelro ∧ ProtAvoidsMut cfgTwoRelro ∧
      ¬ TwoPhaseGuarantees cfgTwoRelro sa0 [] 1 := by
  refine ⟨by decide, by decide, by decide, by decide, fun h => ?_⟩
  exact absurd h.1 (by decide)

/-- (H2) is tight (protect after entry): H1, H3, H4 hold for `goodCfg`, `protect` is placed
after the program write `write 0 9` (`k = 2 ≠ 1`), and that write to the RELRO byte 0
succeeds. -/
theorem twoPhase_cex_protect_after_entry :
    RelocSlotsWritable goodCfg ∧ (2 : Nat) ≠ goodCfg.relocs.length ∧
      ProtCoversRelro goodCfg ∧ ProtAvoidsMut goodCfg ∧
      ¬ TwoPhaseGuarantees goodCfg sa0 [.write 0 9] 2 := by
  refine ⟨by decide, by decide, by decide, by decide, fun h => ?_⟩
  have h3 := h.2.2.1 0 0 9 rfl rfl
  exact absurd h3 (by decide)

/-- Countermodel for (H3): `protect` covers nothing. -/
def cfgNoProt : Cfg := { goodCfg with prot := fun _ => false }

/-- (H3) is tight: H1, H2, H4 hold, `protect` misses RELRO byte 0, and a program write to it
succeeds. -/
theorem twoPhase_cex_prot_misses_relro :
    RelocSlotsWritable cfgNoProt ∧ 1 = cfgNoProt.relocs.length ∧ ¬ ProtCoversRelro cfgNoProt ∧
      ProtAvoidsMut cfgNoProt ∧ ¬ TwoPhaseGuarantees cfgNoProt sa0 [.write 0 9] 1 := by
  refine ⟨by decide, rfl, by decide, by decide, fun h => ?_⟩
  have h3 := h.2.2.1 0 0 9 rfl rfl
  exact absurd h3 (by decide)

/-- Countermodel for (H4): `protect` also covers the mutable byte 1. -/
def cfgProtMut : Cfg := { goodCfg with prot := rangeMask 0 2 }

/-- (H4) is tight: H1–H3 hold, `protect` covers mutable byte 1, and a program write to it
faults. -/
theorem twoPhase_cex_prot_covers_mut :
    RelocSlotsWritable cfgProtMut ∧ 1 = cfgProtMut.relocs.length ∧ ProtCoversRelro cfgProtMut ∧
      ¬ ProtAvoidsMut cfgProtMut ∧ ¬ TwoPhaseGuarantees cfgProtMut sa0 [.write 1 9] 1 := by
  refine ⟨by decide, rfl, by decide, by decide, fun h => ?_⟩
  have h4 := h.2.2.2 0 1 9 rfl rfl
  exact absurd h4 (by decide)

/-! ## Result 2: placement of pointer-bearing immutable statics -/

/-- **PIC, `.rodata` placement faults.** If a dynamic relocation `r` of `c` writes a `.rodata`
byte, the two-phase load faults (for every program `ops`). -/
theorem pic_rodata_slot_load_faults (c : Cfg) (sa : SymTab) (ops : List Op) (r : Reloc)
    (hr : r ∈ c.relocs) (hk : c.kinds[r.slot]? = some .ro) :
    ¬ LoadOk (trace c sa (twoPhase c ops)) := by
  rw [loadOk_twoPhase_iff]
  intro h
  have := h r hr
  simp [mapWr, hk] at this

/-- **PIC, `.data` placement of a relocated slot loads but stays writable after entry.** If `r`
is a dynamic relocation of `c` (`r ∈ c.relocs`), every relocated slot is mapped writable (H1),
`r`'s slot is a mutable byte, and `protect` covers no mutable byte (H4), then the load succeeds
and, after any program prefix, a program write of any value to `r`'s slot succeeds. -/
theorem pic_data_slot_loads_and_write_succeeds (c : Cfg) (sa : SymTab) (r : Reloc)
    (hr : r ∈ c.relocs) (hWr : RelocSlotsWritable c) (hk : c.kinds[r.slot]? = some .mutable)
    (hAvoid : ProtAvoidsMut c) :
    LoadOk (trace c sa (twoPhase c [])) ∧
      ∀ (ops : List Op) (v : Nat),
        (trace c sa (twoPhase c (ops ++ [.write r.slot v]))).opOuts[ops.length]? = some .ok := by
  -- `hr` restricts the statement to relocated slots; the conclusion does not depend on it.
  have _ := hr
  refine ⟨(loadOk_twoPhase_iff c sa []).mpr hWr, fun ops v => ?_⟩
  rw [trace_twoPhase]
  rw [runT_ops_write c sa (ops ++ [Op.write r.slot v]) (postLoad c sa) ops.length r.slot v
    (by simp)]
  have hs : r.slot < c.kinds.length := (List.getElem?_eq_some_iff.mp hk).1
  have hp := hAvoid r.slot hs hk
  have hm : mapWr c.kinds r.slot = true := by simp [mapWr, hk]
  simp [postLoad, hp, hm]

/-- **PIC, RELRO placement of a relocated slot loads and is protected.** If `r` is a dynamic
relocation of `c` (`r ∈ c.relocs`), every relocated slot is mapped writable (H1), `r`'s slot is a
RELRO byte, and `protect` covers every RELRO byte (H3), then the load succeeds and `r`'s slot has
post-entry write protection. -/
theorem pic_relro_slot_loads_and_writeFaultsAfter (c : Cfg) (sa : SymTab) (r : Reloc)
    (hr : r ∈ c.relocs) (hWr : RelocSlotsWritable c) (hk : c.kinds[r.slot]? = some .relro)
    (hCover : ProtCoversRelro c) :
    LoadOk (trace c sa (twoPhase c [])) ∧ WriteFaultsAfter c sa r.slot := by
  -- `hr` restricts the statement to relocated slots; the conclusion does not depend on it.
  have _ := hr
  refine ⟨(loadOk_twoPhase_iff c sa []).mpr hWr, ?_⟩
  rw [writeFaultsAfter_iff]
  have hs : r.slot < c.kinds.length := (List.getElem?_eq_some_iff.mp hk).1
  simp [hCover r.slot hs hk]

/-- **PIC placement classification.** Let `r` be a dynamic relocation of `c` whose other
relocations all write mapped-writable slots, and let `protect` cover every RELRO byte (H3) and
no mutable byte (H4). Then the two-phase load succeeds and `r`'s slot has post-entry write
protection iff that slot is a RELRO byte. -/
theorem pic_loadOk_and_writeFaultsAfter_iff_relro (c : Cfg) (sa : SymTab) (r : Reloc)
    (hr : r ∈ c.relocs)
    (hOthers : ∀ r' ∈ c.relocs, r'.slot ≠ r.slot → mapWr c.kinds r'.slot = true)
    (hCover : ProtCoversRelro c) (hAvoid : ProtAvoidsMut c) :
    (LoadOk (trace c sa (twoPhase c [])) ∧ WriteFaultsAfter c sa r.slot) ↔
      c.kinds[r.slot]? = some .relro := by
  rw [loadOk_twoPhase_iff, writeFaultsAfter_iff]
  have hWr_iff : RelocSlotsWritable c ↔ mapWr c.kinds r.slot = true := by
    constructor
    · intro h; exact h r hr
    · intro h r' hr'
      by_cases e : r'.slot = r.slot
      · rw [e]; exact h
      · exact hOthers r' hr' e
  rw [hWr_iff]
  cases hk : c.kinds[r.slot]? with
  | none => simp [mapWr, hk]
  | some k =>
    have hs : r.slot < c.kinds.length := (List.getElem?_eq_some_iff.mp hk).1
    cases k with
    | code => simp [mapWr, hk]
    | ro => simp [mapWr, hk]
    | relro => simp [mapWr, hk, hCover r.slot hs hk]
    | mutable => simp [mapWr, hk, hAvoid r.slot hs hk]

/-- **Positive control: link-time-resolved `.rodata`.** If the linker resolves the relocations
of `c` into the file image under a link-time symbol table `saL` (`linkResolve saL c`, which
leaves no dynamic relocation), then for every load-time symbol table `saR` a `.rodata` byte `s`
loads without fault, has post-entry write protection, and the image at `protect` equals the
link-time-resolved image `applyAll saL c.relocs c.init`. No hypothesis on `protect` is needed.
Because `saR` is arbitrary, the theorem does not check that the load-time addresses agree with
`saL`. -/
theorem linkResolved_rodata_loadOk_writeFaultsAfter_and_image (c : Cfg) (saL saR : SymTab)
    (s : Nat) (hk : c.kinds[s]? = some .ro) :
    LoadOk (trace (linkResolve saL c) saR (twoPhase (linkResolve saL c) [])) ∧
      WriteFaultsAfter (linkResolve saL c) saR s ∧
      (trace (linkResolve saL c) saR (twoPhase (linkResolve saL c) [])).memAtProtect =
        some (applyAll saL c.relocs c.init) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [loadOk_twoPhase_iff]; intro r hr; simp [linkResolve] at hr
  · rw [writeFaultsAfter_iff]; simp [linkResolve, mapWr, hk]
  · rw [trace_twoPhase]; simp [linkResolve, tryApplyAll]

/-! ## Result 3: lazy binding versus RELRO -/

/-- **A lazily bound slot cannot have both a working call and post-entry write protection**,
whatever the layout and the protected range: if `x` is lazily bound to `t`, then not (the
one-operation program `[.call x]` works and `x` has post-entry write protection). -/
theorem lazyBound_not_callWorks_and_writeFaultsAfter (c : Cfg) (sa : SymTab) (x : Nat) (t : Sym)
    (h : LazyBound c x t) : ¬ (CallWorks c sa x t ∧ WriteFaultsAfter c sa x) := by
  rintro ⟨hc, hw⟩
  rw [writeFaultsAfter_iff] at hw
  obtain ⟨hl, hinit, hnot⟩ := h
  unfold CallWorks at hc
  rw [trace_twoPhase] at hc
  have hm : (postLoad c sa).mem x = c.stub := by
    simp only [postLoad]
    rw [tryApplyAll_other sa _ x c.relocs c.init hnot, hinit]
  have hwx : (postLoad c sa).wr x = false := by simpa [postLoad] using hw
  have := hc.2
  simp only [List.map_cons, List.map_nil, runT, stepOp, hm, ite_true, hl, hwx] at this
  simp at this

/-- The canonical binding placement: every binding in `B` is either eagerly bound with its
slot in RELRO (full RELRO for that slot) or lazily bound with its slot in mutable data
(partial RELRO: the slot stays writable). -/
def EagerRelroOrLazyMut (c : Cfg) (B : List (Nat × Sym)) : Prop :=
  ∀ b ∈ B, (EagerBound c b.1 b.2 ∧ c.kinds[b.1]? = some .relro) ∨
    (LazyBound c b.1 b.2 ∧ c.kinds[b.1]? = some .mutable)

/-- Binding placement used by the integrity characterization: every binding in `B` is either
eagerly bound with its slot in RELRO, or lazily bound (with its slot anywhere). -/
def EagerRelroOrLazy (c : Cfg) (B : List (Nat × Sym)) : Prop :=
  ∀ b ∈ B, (EagerBound c b.1 b.2 ∧ c.kinds[b.1]? = some .relro) ∨ LazyBound c b.1 b.2

/-- **Integrity iff eager, for bindings whose calls work.** If every binding in `B` is eagerly
bound with a RELRO slot or lazily bound (with its slot anywhere), the call through every binding
slot in `B` works (`CallWorks`), and `protect` covers every RELRO byte (H3), then every binding
slot in `B` has post-entry write protection iff every binding in `B` is eagerly bound. The
forward direction goes through the lazy-binding semantics, by
`lazyBound_not_callWorks_and_writeFaultsAfter`. -/
theorem bindings_writeFaultsAfter_iff_eager_of_eagerRelroOrLazy_of_callWorks (c : Cfg)
    (sa : SymTab) (B : List (Nat × Sym)) (hPl : EagerRelroOrLazy c B)
    (hCalls : ∀ b ∈ B, CallWorks c sa b.1 b.2) (hCover : ProtCoversRelro c) :
    (∀ b ∈ B, WriteFaultsAfter c sa b.1) ↔ (∀ b ∈ B, EagerBound c b.1 b.2) := by
  constructor
  · intro h b hb
    rcases hPl b hb with ⟨he, _⟩ | hl
    · exact he
    · exact absurd ⟨hCalls b hb, h b hb⟩
        (lazyBound_not_callWorks_and_writeFaultsAfter c sa b.1 b.2 hl)
  · intro h b hb
    rcases hPl b hb with ⟨_, hk⟩ | hl
    · rw [writeFaultsAfter_iff]
      have hs : b.1 < c.kinds.length := (List.getElem?_eq_some_iff.mp hk).1
      simp [mapWr, hk, hCover b.1 hs hk]
    · exact absurd ((h b hb).2.2.symm.trans hl.1) (by simp)

/-- **Calls work under the canonical placement.** If every binding in `B` is eager with a
RELRO slot or lazy with a mutable slot, every relocated slot is mapped writable (H1), and
`protect` covers no mutable byte (H4), then for every binding `b` in `B` the one-operation
program `[.call b.1]` works. -/
theorem bindings_callWorks_of_eagerRelroOrLazyMut (c : Cfg) (sa : SymTab)
    (B : List (Nat × Sym)) (hPl : EagerRelroOrLazyMut c B)
    (hWr : RelocSlotsWritable c) (hAvoid : ProtAvoidsMut c) :
    ∀ b ∈ B, CallWorks c sa b.1 b.2 := by
  intro b hb
  obtain ⟨x, t⟩ := b
  unfold CallWorks
  rw [trace_twoPhase]
  refine ⟨?_, ?_⟩
  · have := (loadOk_twoPhase_iff c sa [Op.call x]).mpr hWr
    rw [trace_twoPhase] at this
    exact this
  · rcases hPl _ hb with ⟨⟨hin, hall, hnone⟩, hk⟩ | ⟨⟨hl, hinit, hnot⟩, hk⟩
    · have hwx : mapWr c.kinds x = true := by simp [mapWr, hk]
      have hm : (postLoad c sa).mem x = sa t := by
        simp only [postLoad]
        exact tryApplyAll_bind sa _ x t hwx c.relocs c.init hall (Or.inr hin)
      simp only [List.map_cons, List.map_nil, runT, stepOp, hm, hnone, ite_self]
    · have hs : x < c.kinds.length := (List.getElem?_eq_some_iff.mp hk).1
      have hm : (postLoad c sa).mem x = c.stub := by
        simp only [postLoad]
        rw [tryApplyAll_other sa _ x c.relocs c.init hnot, hinit]
      have hwx : (postLoad c sa).wr x = true := by
        simp [postLoad, mapWr, hk, hAvoid x hs hk]
      simp only [List.map_cons, List.map_nil, runT, stepOp, hm, ite_true, hl, hwx]


end Toy.RelroGc
