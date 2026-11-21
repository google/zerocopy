import ToyRelroGc.Relro.Results
import ToyRelroGc.Relro.Results2
import ToyRelroGc.Gc.Results

/-!
Non-vacuity witnesses for results 2 and 3, concrete binding configurations, and definition
examples (an intended positive and an intended negative instance for each core definition).
-/
namespace Toy.RelroGc

/-! ## Binding configurations -/

/-- Slot 0 eagerly bound to symbol 0, in RELRO, protected. -/
def eagerCfg : Cfg := ⟨[.relro], fun _ => 0, [bindReloc 0 0], rangeMask 0 1, [], 0⟩

/-- Slot 0 lazily bound to symbol 0 but placed inside the protected RELRO range. -/
def lazyRelroCfg : Cfg := ⟨[.relro], fun _ => 0, [], rangeMask 0 1, [(0, 0)], 0⟩

/-- Slot 0 lazily bound to symbol 0, in mutable data, unprotected (partial RELRO). -/
def lazyMutCfg : Cfg := ⟨[.mutable], fun _ => 0, [], fun _ => false, [(0, 0)], 0⟩

/-- Slot 0 eagerly bound to symbol 0 in RELRO; slot 1 lazily bound to symbol 1 in mutable
data; `protect` covers exactly byte 0. -/
def mixedCfg : Cfg := ⟨[.relro, .mutable], fun _ => 0, [bindReloc 0 0], rangeMask 0 1, [(1, 1)], 0⟩

theorem eagerBound_eagerCfg : EagerBound eagerCfg 0 0 := by
  refine ⟨by simp [eagerCfg], ?_, rfl⟩
  intro r hr _
  simpa [eagerCfg] using hr

theorem lazyBound_lazyRelroCfg : LazyBound lazyRelroCfg 0 0 :=
  ⟨rfl, rfl, by simp [lazyRelroCfg]⟩

theorem lazyBound_lazyMutCfg : LazyBound lazyMutCfg 0 0 :=
  ⟨rfl, rfl, by simp [lazyMutCfg]⟩

/-- **Positive control for `lazyBound_not_callWorks_and_writeFaultsAfter`:** a slot that is not
lazily bound (here eagerly bound in RELRO) has both a working call and post-entry write
protection. -/
theorem eager_relro_callWorks_and_writeFaultsAfter :
    ¬ LazyBound eagerCfg 0 0 ∧ EagerBound eagerCfg 0 0 ∧ CallWorks eagerCfg sa0 0 0 ∧
      WriteFaultsAfter eagerCfg sa0 0 := by
  refine ⟨fun h => absurd h.1 (by simp [eagerCfg]), eagerBound_eagerCfg, ?_, ?_⟩
  · unfold CallWorks; decide
  · rw [writeFaultsAfter_iff]; decide

/-- **A lazy slot inside the protected range keeps write protection, but the one-operation
program `[call 0]` faults.** -/
theorem lazy_inside_protect_writeFaultsAfter_first_call_faults :
    LazyBound lazyRelroCfg 0 0 ∧ WriteFaultsAfter lazyRelroCfg sa0 0 ∧
      (trace lazyRelroCfg sa0 (twoPhase lazyRelroCfg [.call 0])).opOuts = [.fault] := by
  refine ⟨lazyBound_lazyRelroCfg, ?_, by decide⟩
  rw [writeFaultsAfter_iff]; decide

/-- **"RELRO protects the GOT" fails for lazily bound slots (partial RELRO).** The lazy slot
is outside the protected range: the one-operation program `[call 0]` works, while the program
`[write 0 55, call 0]` jumps to `55` instead of the target's address `100`. -/
theorem partial_relro_lazy_slot_write_redirects_call :
    LazyBound lazyMutCfg 0 0 ∧ CallWorks lazyMutCfg sa0 0 0 ∧
      (trace lazyMutCfg sa0 (twoPhase lazyMutCfg [.write 0 55, .call 0])).opOuts =
        [.ok, .jump 55] ∧ sa0 0 ≠ 55 := by
  refine ⟨lazyBound_lazyMutCfg, by unfold CallWorks; decide, by decide, by decide⟩

theorem eagerRelroOrLazyMut_mixedCfg : EagerRelroOrLazyMut mixedCfg [(0, 0), (1, 1)] := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · left
    refine ⟨⟨by simp [mixedCfg], ?_, rfl⟩, rfl⟩
    intro r hr _
    simpa [mixedCfg] using hr
  · right
    exact ⟨⟨rfl, rfl, by simp [mixedCfg, bindReloc]⟩, rfl⟩

theorem eagerRelroOrLazy_of_eagerRelroOrLazyMut (c : Cfg) (B : List (Nat × Sym))
    (h : EagerRelroOrLazyMut c B) : EagerRelroOrLazy c B := by
  intro b hb
  rcases h b hb with h | h
  · exact Or.inl h
  · exact Or.inr h.1

theorem not_eagerRelroOrLazyMut_lazyRelroCfg : ¬ EagerRelroOrLazyMut lazyRelroCfg [(0, 0)] := by
  intro h
  rcases h (0, 0) (by simp) with ⟨he, _⟩ | ⟨_, hk⟩
  · exact absurd he.1 (by simp [lazyRelroCfg])
  · simp [lazyRelroCfg] at hk

/-- Instance of result 3c (`bindings_callWorks_of_eagerRelroOrLazyMut`): `mixedCfg` with
bindings `[(0, 0), (1, 1)]` satisfies the canonical placement, H1 and H4. -/
theorem bindings_callWorks_nonvacuity :
    EagerRelroOrLazyMut mixedCfg [(0, 0), (1, 1)] ∧ RelocSlotsWritable mixedCfg ∧
      ProtAvoidsMut mixedCfg :=
  ⟨eagerRelroOrLazyMut_mixedCfg, by decide, by decide⟩

/-- Instance of result 3b
(`bindings_writeFaultsAfter_iff_eager_of_eagerRelroOrLazy_of_callWorks`): `mixedCfg` with
bindings `[(0, 0), (1, 1)]` (one eager RELRO slot, one lazy slot) satisfies the placement, the
calls work, and H3 holds. -/
theorem bindings_nonvacuity :
    EagerRelroOrLazy mixedCfg [(0, 0), (1, 1)] ∧
      (∀ b ∈ [((0 : Nat), (0 : Sym)), (1, 1)], CallWorks mixedCfg sa0 b.1 b.2) ∧
      ProtCoversRelro mixedCfg :=
  ⟨eagerRelroOrLazy_of_eagerRelroOrLazyMut _ _ eagerRelroOrLazyMut_mixedCfg,
    bindings_callWorks_of_eagerRelroOrLazyMut mixedCfg sa0 _ eagerRelroOrLazyMut_mixedCfg
      (by decide) (by decide),
    by decide⟩

/-- Slot 0 eagerly bound to symbol 0 but placed in unprotected mutable data. -/
def eagerMutCfg : Cfg := ⟨[.mutable], fun _ => 0, [bindReloc 0 0], fun _ => false, [], 0⟩

/-- `bindings_writeFaultsAfter_iff_eager_of_eagerRelroOrLazy_of_callWorks`: the placement
hypothesis is tight (`eagerMutCfg`: an eager slot outside RELRO; its call works and H3 holds,
but it is eager without being write-protected). -/
theorem bindings_iff_cex_eager_outside_relro :
    ¬ EagerRelroOrLazy eagerMutCfg [(0, 0)] ∧
      (∀ b ∈ [((0 : Nat), (0 : Sym))], CallWorks eagerMutCfg sa0 b.1 b.2) ∧
      ProtCoversRelro eagerMutCfg ∧
      ¬ ((∀ b ∈ [((0 : Nat), (0 : Sym))], WriteFaultsAfter eagerMutCfg sa0 b.1) ↔
        (∀ b ∈ [((0 : Nat), (0 : Sym))], EagerBound eagerMutCfg b.1 b.2)) := by
  have he : EagerBound eagerMutCfg 0 0 := by
    refine ⟨by simp [eagerMutCfg], ?_, rfl⟩
    intro r hr _
    simpa [eagerMutCfg] using hr
  refine ⟨fun h => ?_, ?_, by decide, fun h => ?_⟩
  · rcases h (0, 0) (by simp) with ⟨_, hk⟩ | hl
    · simp [eagerMutCfg] at hk
    · exact absurd hl.1 (by simp [eagerMutCfg])
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    unfold CallWorks; decide
  · have := h.mpr (fun b hb => by simp only [List.mem_singleton] at hb; subst hb; exact he)
      (0, 0) (by simp)
    rw [writeFaultsAfter_iff] at this
    exact absurd this (by decide)

/-- `bindings_writeFaultsAfter_iff_eager_of_eagerRelroOrLazy_of_callWorks`: the call hypothesis
is tight (`lazyRelroCfg`: a lazy slot inside the protected range; the placement and H3 hold,
the slot is write-protected but not eager, and its call faults). -/
theorem bindings_iff_cex_call_faults :
    EagerRelroOrLazy lazyRelroCfg [(0, 0)] ∧
      ¬ (∀ b ∈ [((0 : Nat), (0 : Sym))], CallWorks lazyRelroCfg sa0 b.1 b.2) ∧
      ProtCoversRelro lazyRelroCfg ∧
      ¬ ((∀ b ∈ [((0 : Nat), (0 : Sym))], WriteFaultsAfter lazyRelroCfg sa0 b.1) ↔
        (∀ b ∈ [((0 : Nat), (0 : Sym))], EagerBound lazyRelroCfg b.1 b.2)) := by
  refine ⟨?_, fun h => ?_, by decide, fun h => ?_⟩
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact Or.inr lazyBound_lazyRelroCfg
  · have := h (0, 0) (by simp)
    revert this
    unfold CallWorks; decide
  · have hw : ∀ b ∈ [((0 : Nat), (0 : Sym))], WriteFaultsAfter lazyRelroCfg sa0 b.1 := by
      intro b hb
      simp only [List.mem_singleton] at hb
      subst hb
      exact lazy_inside_protect_writeFaultsAfter_first_call_faults.2.1
    have := (h.mp hw (0, 0) (by simp)).2.2
    simp [lazyRelroCfg] at this

/-- `bindings_writeFaultsAfter_iff_eager_of_eagerRelroOrLazy_of_callWorks`: H3 is tight (eager
RELRO slot, `protect` covers nothing: the call works, the slot is eager but not
write-protected). -/
theorem bindings_iff_cex_no_cover :
    EagerRelroOrLazy { eagerCfg with prot := fun _ => false } [(0, 0)] ∧
      (∀ b ∈ [((0 : Nat), (0 : Sym))],
        CallWorks { eagerCfg with prot := fun _ => false } sa0 b.1 b.2) ∧
      ¬ ProtCoversRelro { eagerCfg with prot := fun _ => false } ∧
      ¬ ((∀ b ∈ [((0 : Nat), (0 : Sym))],
            WriteFaultsAfter { eagerCfg with prot := fun _ => false } sa0 b.1) ↔
        (∀ b ∈ [((0 : Nat), (0 : Sym))],
            EagerBound { eagerCfg with prot := fun _ => false } b.1 b.2)) := by
  have he : EagerBound { eagerCfg with prot := fun _ => false } 0 0 := by
    refine ⟨by simp [eagerCfg], ?_, rfl⟩
    intro r hr _
    simpa [eagerCfg] using hr
  refine ⟨?_, ?_, by decide, fun h => ?_⟩
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact Or.inl ⟨he, rfl⟩
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    unfold CallWorks; decide
  · have := h.mpr (fun b hb => by simp only [List.mem_singleton] at hb; subst hb; exact he)
      (0, 0) (by simp)
    rw [writeFaultsAfter_iff] at this
    exact absurd this (by decide)

theorem eagerRelroOrLazyMut_lazyMutCovered :
    EagerRelroOrLazyMut { lazyMutCfg with prot := rangeMask 0 1 } [(0, 0)] := by
  intro b hb
  simp only [List.mem_singleton] at hb
  subst hb
  right
  exact ⟨⟨rfl, rfl, by simp [lazyMutCfg]⟩, rfl⟩

/-- `bindings_callWorks_of_eagerRelroOrLazyMut`: H4 is tight (the one-operation program
`[.call 0]` faults when `protect` covers the lazy slot). -/
theorem callWorks_cex_cover_mut :
    EagerRelroOrLazyMut { lazyMutCfg with prot := rangeMask 0 1 } [(0, 0)] ∧
      RelocSlotsWritable { lazyMutCfg with prot := rangeMask 0 1 } ∧
      ¬ ProtAvoidsMut { lazyMutCfg with prot := rangeMask 0 1 } ∧
      ¬ CallWorks { lazyMutCfg with prot := rangeMask 0 1 } sa0 0 0 := by
  refine ⟨eagerRelroOrLazyMut_lazyMutCovered, by decide, by decide, ?_⟩
  unfold CallWorks; decide

/-- `bindings_callWorks_of_eagerRelroOrLazyMut`: the placement hypothesis is tight
(`lazyRelroCfg`: the one-operation program `[.call 0]` faults). -/
theorem callWorks_cex_lazy_in_relro :
    ¬ EagerRelroOrLazyMut lazyRelroCfg [(0, 0)] ∧ RelocSlotsWritable lazyRelroCfg ∧
      ProtAvoidsMut lazyRelroCfg ∧ ¬ CallWorks lazyRelroCfg sa0 0 0 := by
  refine ⟨not_eagerRelroOrLazyMut_lazyRelroCfg, by decide, by decide, ?_⟩
  unfold CallWorks; decide

/-- `bindings_callWorks_of_eagerRelroOrLazyMut`: H1 is tight (an extra relocation into a
`.rodata` byte makes the load fault). -/
theorem callWorks_cex_slot_not_writable :
    EagerRelroOrLazyMut ⟨[.relro, .ro], fun _ => 0, [bindReloc 0 0, symReloc 1 0],
        rangeMask 0 1, [], 0⟩ [(0, 0)] ∧
      ¬ RelocSlotsWritable ⟨[.relro, .ro], fun _ => 0, [bindReloc 0 0, symReloc 1 0],
        rangeMask 0 1, [], 0⟩ ∧
      ProtAvoidsMut ⟨[.relro, .ro], fun _ => 0, [bindReloc 0 0, symReloc 1 0],
        rangeMask 0 1, [], 0⟩ ∧
      ¬ CallWorks ⟨[.relro, .ro], fun _ => 0, [bindReloc 0 0, symReloc 1 0],
        rangeMask 0 1, [], 0⟩ sa0 0 0 := by
  refine ⟨?_, by decide, by decide, ?_⟩
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    left
    refine ⟨⟨by simp, ?_, rfl⟩, rfl⟩
    intro r hr hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rfl
    · simp [symReloc] at hs
  · unfold CallWorks; decide

/-! ## Non-vacuity and tightness witnesses for result 2 -/

/-- Mutable slot 0 relocated by `symReloc 0 0`, nothing protected. -/
def cfgMutReloc : Cfg := ⟨[.mutable], fun _ => 0, [symReloc 0 0], fun _ => false, [], 0⟩

/-- Instances of results 2a–2d: `cfgSlotRo` (a relocation into `.rodata`: all hypotheses of
`pic_rodata_slot_load_faults`), `cfgMutReloc` (a relocated mutable slot with H1 and H4: all
hypotheses of `pic_data_slot_loads_and_write_succeeds`), and `goodCfg` (a relocated RELRO slot
with H1, H3 and H4, the other relocations writable: all hypotheses of
`pic_relro_slot_loads_and_writeFaultsAfter` and `pic_loadOk_and_writeFaultsAfter_iff_relro`). -/
theorem placement_nonvacuity :
    (symReloc 0 0 ∈ cfgSlotRo.relocs ∧ cfgSlotRo.kinds[(symReloc 0 0).slot]? = some .ro) ∧
      (symReloc 0 0 ∈ cfgMutReloc.relocs ∧ RelocSlotsWritable cfgMutReloc ∧
        cfgMutReloc.kinds[(symReloc 0 0).slot]? = some .mutable ∧ ProtAvoidsMut cfgMutReloc) ∧
      (symReloc 0 0 ∈ goodCfg.relocs ∧ RelocSlotsWritable goodCfg ∧
        goodCfg.kinds[(symReloc 0 0).slot]? = some .relro ∧ ProtCoversRelro goodCfg ∧
        ProtAvoidsMut goodCfg ∧
        (∀ r' ∈ goodCfg.relocs, r'.slot ≠ (symReloc 0 0).slot →
          mapWr goodCfg.kinds r'.slot = true)) := by
  refine ⟨⟨by simp [cfgSlotRo, goodCfg], rfl⟩, ⟨by simp [cfgMutReloc], by decide, rfl, by decide⟩,
    ⟨by simp [goodCfg], by decide, rfl, by decide, by decide, ?_⟩⟩
  intro r' hr' hne
  simp [goodCfg] at hr'
  subst hr'
  exact absurd rfl hne

/-- `pic_loadOk_and_writeFaultsAfter_iff_relro`: the hypothesis on the other relocations is
tight (slot 0 is RELRO, but another relocation writes the `.rodata` byte 1, so the load
faults). -/
theorem placement_iff_cex_other_reloc :
    symReloc 0 0 ∈ (⟨[.relro, .ro], fun _ => 0, [symReloc 0 0, symReloc 1 0], rangeMask 0 1, [], 0⟩
        : Cfg).relocs ∧
      ¬ (∀ r' ∈ (⟨[.relro, .ro], fun _ => 0, [symReloc 0 0, symReloc 1 0], rangeMask 0 1, [], 0⟩
          : Cfg).relocs, r'.slot ≠ (symReloc 0 0).slot →
            mapWr [.relro, .ro] r'.slot = true) ∧
      ProtCoversRelro ⟨[.relro, .ro], fun _ => 0, [symReloc 0 0, symReloc 1 0], rangeMask 0 1, [], 0⟩ ∧
      ProtAvoidsMut ⟨[.relro, .ro], fun _ => 0, [symReloc 0 0, symReloc 1 0], rangeMask 0 1, [], 0⟩ ∧
      ¬ ((LoadOk (trace ⟨[.relro, .ro], fun _ => 0, [symReloc 0 0, symReloc 1 0], rangeMask 0 1, [], 0⟩
            sa0 (twoPhase ⟨[.relro, .ro], fun _ => 0, [symReloc 0 0, symReloc 1 0],
              rangeMask 0 1, [], 0⟩ [])) ∧
          WriteFaultsAfter ⟨[.relro, .ro], fun _ => 0, [symReloc 0 0, symReloc 1 0],
            rangeMask 0 1, [], 0⟩ sa0 (symReloc 0 0).slot) ↔
        [Kind.relro, Kind.ro][(symReloc 0 0).slot]? = some .relro) := by
  refine ⟨by simp, fun h => ?_, by decide, by decide, fun h => ?_⟩
  · have := h (symReloc 1 0) (by simp) (by simp [symReloc])
    simp [mapWr, symReloc] at this
  · have := (h.mpr rfl).1
    exact absurd this (by decide)

/-- `pic_loadOk_and_writeFaultsAfter_iff_relro`: H3 is tight (`cfgNoProt`: `hr`, the
other-relocations hypothesis and H4 hold, but the RELRO slot is not covered, so it is not
write-protected). -/
theorem placement_iff_cex_no_cover :
    symReloc 0 0 ∈ cfgNoProt.relocs ∧
      (∀ r' ∈ cfgNoProt.relocs, r'.slot ≠ (symReloc 0 0).slot →
        mapWr cfgNoProt.kinds r'.slot = true) ∧
      ¬ ProtCoversRelro cfgNoProt ∧ ProtAvoidsMut cfgNoProt ∧
      ¬ ((LoadOk (trace cfgNoProt sa0 (twoPhase cfgNoProt [])) ∧
          WriteFaultsAfter cfgNoProt sa0 (symReloc 0 0).slot) ↔
        cfgNoProt.kinds[(symReloc 0 0).slot]? = some .relro) := by
  refine ⟨by simp [cfgNoProt, goodCfg], ?_, by decide, by decide, fun h => ?_⟩
  · intro r' hr' hne
    simp [cfgNoProt, goodCfg] at hr'
    subst hr'
    exact absurd rfl hne
  · have := (h.mpr rfl).2
    rw [writeFaultsAfter_iff] at this
    exact absurd this (by decide)

/-- Mutable slot relocated and covered by `protect`. -/
def cfgMutCovered : Cfg := ⟨[.mutable], fun _ => 0, [symReloc 0 0], rangeMask 0 1, [], 0⟩

/-- `pic_loadOk_and_writeFaultsAfter_iff_relro`: H4 is tight (`cfgMutCovered`: `hr`, the
other-relocations hypothesis and H3 hold, and a `.data` slot covered by `protect` loads and is
write-protected, though it is not RELRO). -/
theorem placement_iff_cex_cover_mut :
    symReloc 0 0 ∈ cfgMutCovered.relocs ∧
      (∀ r' ∈ cfgMutCovered.relocs, r'.slot ≠ (symReloc 0 0).slot →
        mapWr cfgMutCovered.kinds r'.slot = true) ∧
      ProtCoversRelro cfgMutCovered ∧ ¬ ProtAvoidsMut cfgMutCovered ∧
      ¬ ((LoadOk (trace cfgMutCovered sa0 (twoPhase cfgMutCovered [])) ∧
          WriteFaultsAfter cfgMutCovered sa0 (symReloc 0 0).slot) ↔
        cfgMutCovered.kinds[(symReloc 0 0).slot]? = some .relro) := by
  refine ⟨by simp [cfgMutCovered], ?_, by decide, by decide, fun h => ?_⟩
  · intro r' hr' hne
    simp [cfgMutCovered] at hr'
    subst hr'
    exact absurd rfl hne
  · have := h.mp ⟨by decide, by rw [writeFaultsAfter_iff]; decide⟩
    simp [cfgMutCovered, symReloc] at this

/-- A relocation into the `.rodata` byte 0 and one into the mutable byte 1, nothing protected. -/
def cfgRoMutReloc : Cfg :=
  ⟨[.ro, .mutable], fun _ => 0, [symReloc 0 0, symReloc 1 0], fun _ => false, [], 0⟩

/-- `pic_data_slot_loads_and_write_succeeds`, hypothesis `hWr`: the relocation of the mutable
byte 1 is accompanied by one into the `.rodata` byte 0, so the load faults. -/
theorem data_slot_cex_load_fault :
    symReloc 1 0 ∈ cfgRoMutReloc.relocs ∧ ¬ RelocSlotsWritable cfgRoMutReloc ∧
      cfgRoMutReloc.kinds[(symReloc 1 0).slot]? = some .mutable ∧ ProtAvoidsMut cfgRoMutReloc ∧
      ¬ LoadOk (trace cfgRoMutReloc sa0 (twoPhase cfgRoMutReloc [])) := by
  refine ⟨by simp [cfgRoMutReloc], by decide, rfl, by decide, by decide⟩

/-- `pic_data_slot_loads_and_write_succeeds`, hypothesis `hk`: for the relocated RELRO byte 0 of
`goodCfg` the write faults. -/
theorem data_slot_cex_relro_slot :
    symReloc 0 0 ∈ goodCfg.relocs ∧ RelocSlotsWritable goodCfg ∧
      goodCfg.kinds[(symReloc 0 0).slot]? ≠ some .mutable ∧ ProtAvoidsMut goodCfg ∧
      (trace goodCfg sa0 (twoPhase goodCfg ([] ++ [.write (symReloc 0 0).slot 9]))).opOuts[
        ([] : List Op).length]? ≠ some .ok := by
  refine ⟨by simp [goodCfg], by decide, by decide, by decide, by decide⟩

/-- `pic_data_slot_loads_and_write_succeeds`, hypothesis `hAvoid`: `protect` covers the
relocated mutable byte 0 of `cfgMutCovered`, and the write faults. -/
theorem data_slot_cex_covered :
    symReloc 0 0 ∈ cfgMutCovered.relocs ∧ RelocSlotsWritable cfgMutCovered ∧
      cfgMutCovered.kinds[(symReloc 0 0).slot]? = some .mutable ∧ ¬ ProtAvoidsMut cfgMutCovered ∧
      (trace cfgMutCovered sa0 (twoPhase cfgMutCovered ([] ++ [.write (symReloc 0 0).slot 9]))).opOuts[
        ([] : List Op).length]? ≠ some .ok := by
  refine ⟨by simp [cfgMutCovered], by decide, rfl, by decide, by decide⟩

/-- RELRO slot 0 relocated, plus a relocation into the `.rodata` byte 1. -/
def cfgRelroRo : Cfg := ⟨[.relro, .ro], fun _ => 0, [symReloc 0 0, symReloc 1 0], rangeMask 0 1, [], 0⟩

/-- `pic_relro_slot_loads_and_writeFaultsAfter`, hypothesis `hWr`. -/
theorem relro_slot_cex_load_fault :
    symReloc 0 0 ∈ cfgRelroRo.relocs ∧ ¬ RelocSlotsWritable cfgRelroRo ∧
      cfgRelroRo.kinds[(symReloc 0 0).slot]? = some .relro ∧ ProtCoversRelro cfgRelroRo ∧
      ¬ LoadOk (trace cfgRelroRo sa0 (twoPhase cfgRelroRo [])) := by
  refine ⟨by simp [cfgRelroRo], by decide, rfl, by decide, by decide⟩

/-- `pic_relro_slot_loads_and_writeFaultsAfter`, hypothesis `hk`: the relocated mutable byte 0
of `cfgMutReloc` is not write-protected. -/
theorem relro_slot_cex_mut_slot :
    symReloc 0 0 ∈ cfgMutReloc.relocs ∧ RelocSlotsWritable cfgMutReloc ∧
      cfgMutReloc.kinds[(symReloc 0 0).slot]? ≠ some .relro ∧ ProtCoversRelro cfgMutReloc ∧
      ¬ WriteFaultsAfter cfgMutReloc sa0 (symReloc 0 0).slot := by
  rw [writeFaultsAfter_iff]
  refine ⟨by simp [cfgMutReloc], by decide, by decide, by decide, by decide⟩

/-- `pic_relro_slot_loads_and_writeFaultsAfter`, hypothesis `hCover`. -/
theorem relro_slot_cex_no_cover :
    symReloc 0 0 ∈ cfgNoProt.relocs ∧ RelocSlotsWritable cfgNoProt ∧
      cfgNoProt.kinds[(symReloc 0 0).slot]? = some .relro ∧ ¬ ProtCoversRelro cfgNoProt ∧
      ¬ WriteFaultsAfter cfgNoProt sa0 (symReloc 0 0).slot := by
  rw [writeFaultsAfter_iff]
  refine ⟨by simp [cfgNoProt, goodCfg], by decide, rfl, by decide, by decide⟩

/-! ## Definition examples -/

/-- `Reloc.AddressOnly`: admits `symReloc 0 0`; rejects the resolver `rRes1`. -/
theorem addressOnly_examples : (symReloc 0 0).AddressOnly ∧ ¬ rRes1.AddressOnly :=
  ⟨fun _ _ _ => rfl, resolver_reads_unrelocated_slot_order_dependent.2.2.1 ∘
    fun h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact fun _ _ _ => rfl
      · exact h⟩

/-- `Reloc.ReadsOnly`: `rRes1` reads only slot 0, and does not read only the empty set. -/
theorem readsOnly_examples : rRes1.ReadsOnly (fun a => a = 0) ∧ ¬ rRes1.ReadsOnly (fun _ => False) := by
  refine ⟨fun _ _ _ h => h 0 rfl, fun h => ?_⟩
  have := h sa0 (fun _ => 0) (fun _ => 1) (fun _ hf => hf.elim)
  simp [rRes1] at this

/-- `mapWr`: RELRO and mutable bytes are writable at map time; `.rodata`, code and unmapped
addresses are not. -/
theorem mapWr_examples :
    mapWr [.relro, .mutable] 0 = true ∧ mapWr [.relro, .mutable] 1 = true ∧
      mapWr [.ro] 0 = false ∧ mapWr [.code] 0 = false ∧ mapWr [.relro] 5 = false := by
  decide

/-- `RelocSlotsWritable`, `ProtCoversRelro`, `ProtAvoidsMut`, `LoadOk`: positive on
`goodCfg`; negative on `cfgSlotRo`, `cfgNoProt`, `cfgProtMut`, and the faulting load of
`cfgSlotRo`. -/
theorem loader_predicate_examples :
    RelocSlotsWritable goodCfg ∧ ¬ RelocSlotsWritable cfgSlotRo ∧
      ProtCoversRelro goodCfg ∧ ¬ ProtCoversRelro cfgNoProt ∧
      ProtAvoidsMut goodCfg ∧ ¬ ProtAvoidsMut cfgProtMut ∧
      LoadOk (trace goodCfg sa0 (twoPhase goodCfg [])) ∧
      ¬ LoadOk (trace cfgSlotRo sa0 (twoPhase cfgSlotRo [])) := by
  decide

/-- `TwoPhaseGuarantees`: holds for `goodCfg` at `k = 1`; fails at `k = 2` with an earlier
program write to RELRO. -/
theorem twoPhaseGuarantees_examples :
    TwoPhaseGuarantees goodCfg sa0 [.write 0 5, .write 1 5] 1 ∧
      ¬ TwoPhaseGuarantees goodCfg sa0 [.write 0 9] 2 :=
  ⟨twoPhaseGuarantees_of_slotsWritable_of_protectAfterRelocs_of_covers_of_avoids _ _ _ _
      (by decide) rfl (by decide) (by decide),
    twoPhase_cex_protect_after_entry.2.2.2.2⟩

/-- `WriteFaultsAfter`: RELRO byte 0 of `goodCfg` is write-protected; mutable byte 1 is not. -/
theorem writeFaultsAfter_examples :
    WriteFaultsAfter goodCfg sa0 0 ∧ ¬ WriteFaultsAfter goodCfg sa0 1 := by
  rw [writeFaultsAfter_iff, writeFaultsAfter_iff]
  decide

/-- `linkResolve`: removes the dynamic relocations and writes the resolved value into the file
image (slot 0 becomes `100`, where the unlinked image held `0`). -/
theorem linkResolve_examples :
    (linkResolve sa0 goodCfg).relocs = [] ∧ (linkResolve sa0 goodCfg).init 0 = 100 ∧
      goodCfg.init 0 ≠ (linkResolve sa0 goodCfg).init 0 := by
  decide

/-- `EagerBound` / `LazyBound` / `CallWorks`: positive and negative instances. -/
theorem binding_examples :
    EagerBound eagerCfg 0 0 ∧ ¬ EagerBound lazyRelroCfg 0 0 ∧
      LazyBound lazyRelroCfg 0 0 ∧ ¬ LazyBound eagerCfg 0 0 ∧
      CallWorks eagerCfg sa0 0 0 ∧ ¬ CallWorks lazyRelroCfg sa0 0 0 := by
  refine ⟨eagerBound_eagerCfg, fun h => ?_, lazyBound_lazyRelroCfg, fun h => ?_,
    eager_relro_callWorks_and_writeFaultsAfter.2.2.1, by unfold CallWorks; decide⟩
  · exact absurd h.1 (by simp [lazyRelroCfg])
  · exact absurd (h.2.2 (bindReloc 0 0) (by simp [eagerCfg])) (by simp [bindReloc])

/-- `EagerRelroOrLazyMut`: holds for `mixedCfg`; fails for `lazyRelroCfg`. -/
theorem eagerRelroOrLazyMut_examples :
    EagerRelroOrLazyMut mixedCfg [(0, 0), (1, 1)] ∧ ¬ EagerRelroOrLazyMut lazyRelroCfg [(0, 0)] :=
  ⟨eagerRelroOrLazyMut_mixedCfg, not_eagerRelroOrLazyMut_lazyRelroCfg⟩

/-- `alignDown` / `alignUp`, including the degenerate page size `0` (floor division by `0` is
`0`) and an already-aligned address. -/
theorem align_examples :
    alignDown 4 5 = 4 ∧ alignUp 4 5 = 8 ∧ alignDown 4 8 = 8 ∧ alignUp 4 8 = 8 ∧
      alignDown 0 5 = 0 ∧ alignUp 0 5 = 0 ∧ alignUp 4 0 = 0 := by
  decide

/-- `roundedMask`: with `P = 4` and RELRO `[1, 9)`, down-down protects `[0, 8)`, down-up
protects `[0, 12)`, exact protects `[1, 9)`. -/
theorem roundedMask_examples :
    roundedMask .downDown 4 1 9 0 = true ∧ roundedMask .downDown 4 1 9 8 = false ∧
      roundedMask .downUp 4 1 9 11 = true ∧ roundedMask .downUp 4 1 9 12 = false ∧
      roundedMask .exact 4 1 9 0 = false ∧ roundedMask .exact 4 1 9 8 = true := by
  decide

/-- `RelroIs`: admits the exact range; rejects a range missing a RELRO byte and a range
containing a non-RELRO byte. -/
theorem relroIs_examples :
    RelroIs layoutRelro3 0 3 ∧ ¬ RelroIs layoutRelro3 0 2 ∧ ¬ RelroIs layoutRelro3Mut 0 4 := by
  decide

/-- `NoMutIn`: positive and negative instances. -/
theorem noMutIn_examples :
    NoMutIn layoutRelro3Mut 0 3 ∧ ¬ NoMutIn layoutRelro3Mut 3 4 := by
  decide

/-- `PageGranular`: `[0, 4)` is page-granular for `P = 2`; `[0, 3)` is not. -/
theorem pageGranular_examples : PageGranular 2 (rangeMask 0 4) ∧ ¬ PageGranular 2 (rangeMask 0 3) := by
  refine ⟨fun a b h => ?_, fun h => absurd (h 2 3 rfl) (by decide)⟩
  simp only [rangeMask, Nat.zero_le, true_and]
  have : (a < 4 ↔ b < 4) := by omega
  simp [this]

/-- `NoSharedPage`: positive and negative instances (`P = 2`). -/
theorem noSharedPage_examples :
    NoSharedPage 2 [.relro, .relro, .mutable] ∧ ¬ NoSharedPage 2 layoutRelro3Mut := by
  decide

/-! ### GC definitions -/

/-- `Sec.isRoot`: a `KEEP`-only section, a retain-only section and an exported-only section are
roots; a plain section is not. -/
theorem sec_isRoot_examples :
    (mkSec 0 false true false).isRoot = true ∧ (mkSec 0 false false true).isRoot = true ∧
      (⟨0, false, true, false, false⟩ : Sec).isRoot = true ∧
      (mkSec 0 false false false).isRoot = false := by
  decide

/-- `GcIn.Live` / `Reach`: section 1 is kept when the entry references it and removed
otherwise. -/
theorem live_examples (pol : SSPolicy) : (gcPair [(0, 1)]).Live pol 1 ∧ ¬ (gcPair []).Live pol 1 :=
  ⟨Reach.step (i := 0) (Reach.root (by decide)) (by simp [gcPair]), gcPair_not_live_one pol⟩

/-- `GcIn.ssEdges`: the conservative policy adds an edge from the referencing section to each
section named `X`; the precise policy adds none. -/
theorem ssEdges_examples :
    (0, 2) ∈ (gcReg [] false false).ssEdges .conservative ∧
      (gcReg [] false false).ssEdges .precise = [] := by
  decide

/-- `RunPreserved`: positive and negative instances. -/
theorem runPreserved_examples (pol : SSPolicy) :
    RunPreserved (gcPair [(0, 1)]) pol [.implicit 0, .edge 0 1] ∧
      ¬ RunPreserved (gcPair []) pol [.implicit 1] :=
  ⟨runPreserved_of_edgeAccessesFollowEdges_of_implicitAccessesHitRoots_of_boundsAccessesRetained
      _ _ _ (gcSoundness_nonvacuity pol).1 (gcSoundness_nonvacuity pol).2.1
      (gcSoundness_nonvacuity pol).2.2,
    (gcSoundness_cex_implicit_access_to_nonroot pol).2.2.2⟩

/-- `KeptItem`: item 1 is kept with one item per section; item 2 is not. -/
theorem keptItem_examples :
    KeptItem secFine itemEdges itemRoot 1 ∧ ¬ KeptItem secFine itemEdges itemRoot 2 :=
  ⟨coarsening_nonvacuity.2, unreferenced_item_kept_when_sharing_live_section.2.2.2.1⟩

/-- `RegistryKept` / `StartStopUndefined` / `NoEdgeIntoName`: positive and negative instances. -/
theorem registry_examples :
    RegistryKept (gcReg [] false false) .conservative 7 ∧
      ¬ RegistryKept (gcReg [(0, 1)] false false) .precise 7 ∧
      StartStopUndefined (gcReg [] false false) .precise 7 ∧
      ¬ StartStopUndefined (gcReg [(0, 1)] false false) .precise 7 ∧
      NoEdgeIntoName (gcReg [] false false) 7 ∧ ¬ NoEdgeIntoName (gcReg [(0, 1)] false false) 7 :=
  ⟨registry_precise_link_failure_conservative_kept.2, registry_precise_silent_shrink.2.2.1,
    registry_precise_link_failure_conservative_kept.1, registry_precise_silent_shrink.2.2.2.1,
    registry_nonvacuity.1, registry_iff_cex_edge_into_entry.1⟩

/-- `compileKeeps` / `Prog2.Survives`: positive and negative instances. -/
theorem twoStage_examples :
    compileKeeps stUsedOnly = true ∧ compileKeeps stRetainOnly = false ∧
      (Prog2.mk [stMain, stUsedRetained] []).Survives 1 ∧
      ¬ (Prog2.mk [stMain, stUsedOnly] []).Survives 1 :=
  ⟨rfl, rfl, twoStage_nonvacuity.2.1, compilerUsed_unretained_unreachable_removed.2⟩

/-! ## Ledger witnesses: one concrete instance per hypothesis (other hypotheses hold, the
conclusion fails) -/

/-- `pic_rodata_slot_load_faults`, hypothesis `hr`: after link-time resolution the relocation
is no longer dynamic, the slot is still `.rodata`, and the load succeeds. -/
theorem pic_rodata_cex_link_resolved :
    ¬ symReloc 0 0 ∈ (linkResolve sa0 cfgSlotRo).relocs ∧
      (linkResolve sa0 cfgSlotRo).kinds[(symReloc 0 0).slot]? = some .ro ∧
      LoadOk (trace (linkResolve sa0 cfgSlotRo) sa0 (twoPhase (linkResolve sa0 cfgSlotRo) [])) := by
  refine ⟨by simp [linkResolve], rfl, by decide⟩

/-- `pic_rodata_slot_load_faults`, hypothesis `hk`: a dynamic relocation of a RELRO slot
loads. -/
theorem pic_rodata_cex_relro_slot :
    symReloc 0 0 ∈ goodCfg.relocs ∧ goodCfg.kinds[(symReloc 0 0).slot]? ≠ some .ro ∧
      LoadOk (trace goodCfg sa0 (twoPhase goodCfg [])) := by
  refine ⟨by simp [goodCfg], by decide, by decide⟩

/-- `pic_loadOk_and_writeFaultsAfter_iff_relro`, hypothesis `hr`: with no dynamic relocations
(after link-time resolution), a `.rodata` slot loads and is write-protected although it is not
RELRO. -/
theorem placement_iff_cex_not_dynamic :
    ¬ symReloc 0 0 ∈ (linkResolve sa0 cfgSlotRo).relocs ∧
      (∀ r' ∈ (linkResolve sa0 cfgSlotRo).relocs, r'.slot ≠ (symReloc 0 0).slot →
        mapWr (linkResolve sa0 cfgSlotRo).kinds r'.slot = true) ∧
      ProtCoversRelro (linkResolve sa0 cfgSlotRo) ∧ ProtAvoidsMut (linkResolve sa0 cfgSlotRo) ∧
      ¬ ((LoadOk (trace (linkResolve sa0 cfgSlotRo) sa0 (twoPhase (linkResolve sa0 cfgSlotRo) [])) ∧
          WriteFaultsAfter (linkResolve sa0 cfgSlotRo) sa0 (symReloc 0 0).slot) ↔
        (linkResolve sa0 cfgSlotRo).kinds[(symReloc 0 0).slot]? = some .relro) := by
  refine ⟨by simp [linkResolve], by simp [linkResolve], by decide, by decide, fun h => ?_⟩
  have := h.mp ⟨by decide, by rw [writeFaultsAfter_iff]; decide⟩
  simp [linkResolve, cfgSlotRo, goodCfg, symReloc] at this

/-- `linkResolved_rodata_loadOk_writeFaultsAfter_and_image`, hypothesis `hk`: a mutable byte
is not write-protected after link-time resolution either. -/
theorem linkResolved_cex_mut_slot :
    (linkResolve sa0 goodCfg).kinds[1]? ≠ some .ro ∧ ¬ WriteFaultsAfter (linkResolve sa0 goodCfg) sa0 1 := by
  rw [writeFaultsAfter_iff]; decide

/-- `downDown_avoidsMut_of_firstPage_noMut`, hypothesis `hR`: the claimed range `[0, 4)`
contains the mutable byte 1. -/
theorem downDown_avoidsMut_cex_relroIs :
    ¬ RelroIs [.relro, .mutable] 0 4 ∧ NoMutIn [.relro, .mutable] (alignDown 2 0) 0 ∧
      ¬ AvoidsMut [.relro, .mutable] (roundedMask .downDown 2 0 4) := by
  decide

/-- `downUp_coversRelro`, hypothesis `hR`: the claimed range is empty but two bytes are
RELRO. -/
theorem downUp_coversRelro_cex_relroIs :
    0 < 2 ∧ ¬ RelroIs [.relro, .relro] 0 0 ∧
      ¬ CoversRelro [.relro, .relro] (roundedMask .downUp 2 0 0) := by
  decide

/-- `downUp_avoidsMut_iff_partialPages_noMut`, hypothesis `hR`. -/
theorem downUp_avoidsMut_iff_cex_relroIs :
    0 < 2 ∧ ¬ RelroIs [.relro, .mutable] 0 2 ∧ (0 : Nat) < 2 ∧
      ¬ (AvoidsMut [.relro, .mutable] (roundedMask .downUp 2 0 2) ↔
        NoMutIn [.relro, .mutable] (alignDown 2 0) 0 ∧ NoMutIn [.relro, .mutable] 2 (alignUp 2 2)) := by
  decide

/-- `noSharedPage_iff_partialPages_noMut`, hypothesis `hR`: RELRO byte 2 outside the claimed
range `[0, 2)` shares a page with mutable byte 3. -/
theorem noSharedPage_iff_cex_relroIs :
    0 < 2 ∧ ¬ RelroIs layoutRelro3Mut 0 2 ∧ 0 < 2 ∧
      ¬ (NoSharedPage 2 layoutRelro3Mut ↔
        NoMutIn layoutRelro3Mut (alignDown 2 0) 0 ∧ NoMutIn layoutRelro3Mut 2 (alignUp 2 2)) := by
  decide

/-- `exists_pageGranular_covers_avoids_iff_partialPages_noMut`, hypothesis `hP`. -/
theorem exists_pageGranular_iff_cex_pageZero :
    ¬ ((0 : Nat) < 0) ∧ RelroIs [.relro, .mutable] 0 1 ∧ 0 < 1 ∧
      ¬ ((∃ m, PageGranular 0 m ∧ CoversRelro [.relro, .mutable] m ∧ AvoidsMut [.relro, .mutable] m) ↔
        NoMutIn [.relro, .mutable] (alignDown 0 0) 0 ∧ NoMutIn [.relro, .mutable] 1 (alignUp 0 1)) := by
  rw [exists_pageGranular_covers_avoids_iff_noSharedPage]
  exact noSharedPage_iff_cex_pageZero

/-- `exists_pageGranular_covers_avoids_iff_partialPages_noMut`, hypothesis `hne`. -/
theorem exists_pageGranular_iff_cex_empty :
    0 < 2 ∧ RelroIs [.mutable] 1 1 ∧ ¬ ((1 : Nat) < 1) ∧
      ¬ ((∃ m, PageGranular 2 m ∧ CoversRelro [.mutable] m ∧ AvoidsMut [.mutable] m) ↔
        NoMutIn [.mutable] (alignDown 2 1) 1 ∧ NoMutIn [.mutable] 1 (alignUp 2 1)) := by
  rw [exists_pageGranular_covers_avoids_iff_noSharedPage]
  exact noSharedPage_iff_cex_empty

/-- `exists_pageGranular_covers_avoids_iff_partialPages_noMut`, hypothesis `hR`. -/
theorem exists_pageGranular_iff_cex_relroIs :
    0 < 2 ∧ ¬ RelroIs layoutRelro3Mut 0 2 ∧ 0 < 2 ∧
      ¬ ((∃ m, PageGranular 2 m ∧ CoversRelro layoutRelro3Mut m ∧ AvoidsMut layoutRelro3Mut m) ↔
        NoMutIn layoutRelro3Mut (alignDown 2 0) 0 ∧ NoMutIn layoutRelro3Mut 2 (alignUp 2 2)) := by
  rw [exists_pageGranular_covers_avoids_iff_noSharedPage]
  exact noSharedPage_iff_cex_relroIs

/-- `applyAll_perm_of_addressOnly_of_nodup_slots`, hypothesis `p`: dropping a relocation
changes the image. -/
theorem order_cex_not_perm :
    ¬ [symReloc 0 0].Perm [] ∧ (∀ r ∈ [symReloc 0 0], r.AddressOnly) ∧
      ([symReloc 0 0].map Reloc.slot).Nodup ∧
      applyAll sa0 [symReloc 0 0] (fun _ => 0) ≠ applyAll sa0 [] (fun _ => 0) := by
  refine ⟨fun h => absurd h.length_eq (by simp), ?_, by decide, fun h => ?_⟩
  · intro r hr sa m m'
    simp only [List.mem_singleton] at hr
    subst hr; rfl
  · have := congrFun h 0
    revert this
    decide

/-- `applyAll_append_perm_of_resolvers_read_no_resolver_slot`, hypothesis `pA`. -/
theorem resolverOrder_cex_not_permA :
    (∀ r ∈ [rAddr0], r.AddressOnly) ∧ ([rAddr0].map Reloc.slot).Nodup ∧
      (∀ r ∈ ([] : List Reloc), r.ReadsOnly (fun a => a ∉ ([] : List Reloc).map Reloc.slot)) ∧
      (([] : List Reloc).map Reloc.slot).Nodup ∧ ¬ ([] : List Reloc).Perm [rAddr0] ∧
      ([] : List Reloc).Perm [] ∧
      applyAll sa0 ([] ++ []) (fun _ => 0) ≠ applyAll sa0 ([rAddr0] ++ []) (fun _ => 0) := by
  refine ⟨?_, by decide, by simp, by decide, fun h => absurd h.length_eq (by simp),
    List.Perm.refl _, fun h => ?_⟩
  · intro r hr sa m m'
    simp only [List.mem_singleton] at hr
    subst hr; rfl
  · have := congrFun h 0
    revert this
    decide

/-- `applyAll_append_perm_of_resolvers_read_no_resolver_slot`, hypothesis `pR`. -/
theorem resolverOrder_cex_not_permR :
    (∀ r ∈ ([] : List Reloc), r.AddressOnly) ∧ (([] : List Reloc).map Reloc.slot).Nodup ∧
      (∀ r ∈ [rAddr0], r.ReadsOnly (fun a => a ∉ [rAddr0].map Reloc.slot)) ∧
      ([rAddr0].map Reloc.slot).Nodup ∧ ([] : List Reloc).Perm [] ∧
      ¬ ([] : List Reloc).Perm [rAddr0] ∧
      applyAll sa0 ([] ++ []) (fun _ => 0) ≠ applyAll sa0 ([] ++ [rAddr0]) (fun _ => 0) := by
  refine ⟨by simp, by decide, ?_, by decide, List.Perm.refl _,
    fun h => absurd h.length_eq (by simp), fun h => ?_⟩
  · intro r hr sa m m' _
    simp only [List.mem_singleton] at hr
    subst hr; rfl
  · have := congrFun h 0
    revert this
    decide

/-- `keptItem_of_keptItem_of_coarsening`, hypothesis `h`: with `f = id` the conclusion fails
for an item that was not kept in the first place. -/
theorem coarsening_cex_not_kept :
    (∀ i, secFine i = (fun s => s) (secFine i)) ∧ ¬ KeptItem secFine itemEdges itemRoot 2 ∧
      ¬ KeptItem secFine itemEdges itemRoot 2 :=
  ⟨fun _ => rfl, unreferenced_item_kept_when_sharing_live_section.2.2.2.1,
    unreferenced_item_kept_when_sharing_live_section.2.2.2.1⟩

/-- `keptItem_of_keptItem_of_coarsening`, hypothesis `hc`: refining `secShared` to `secFine`
(no merging map exists) loses item 2. -/
theorem coarsening_cex_refinement :
    (¬ ∃ f : Nat → Nat, ∀ i, secFine i = f (secShared i)) ∧
      KeptItem secShared itemEdges itemRoot 2 ∧ ¬ KeptItem secFine itemEdges itemRoot 2 :=
  ⟨unreferenced_item_kept_when_sharing_live_section.2.2.2.2,
    unreferenced_item_kept_when_sharing_live_section.2.2.1,
    unreferenced_item_kept_when_sharing_live_section.2.2.2.1⟩

/-- `precise_drops_unrooted_entries_of_noEdgeIntoName`, hypothesis `hN`. -/
theorem precise_drops_cex_edge_into_entry :
    ¬ NoEdgeIntoName (gcReg [(0, 1)] false false) 7 ∧
      (∀ j, (gcReg [(0, 1)] false false).nameOf j = some 7 → ¬ (gcReg [(0, 1)] false false).IsRoot j) ∧
      ¬ (∀ j, (gcReg [(0, 1)] false false).nameOf j = some 7 →
        ¬ (gcReg [(0, 1)] false false).Live .precise j) := by
  refine ⟨by decide, fun j hj => ?_, fun h => h 1 rfl registry_precise_silent_shrink.1⟩
  rcases nameOf_gcReg_eq _ _ _ j hj with rfl | rfl <;> decide

/-- `precise_drops_unrooted_entries_of_noEdgeIntoName`, hypothesis `hU`: `KEEP` entries are
kept. -/
theorem precise_drops_cex_rooted_entry :
    NoEdgeIntoName (gcReg [] true false) 7 ∧
      ¬ (∀ j, (gcReg [] true false).nameOf j = some 7 → ¬ (gcReg [] true false).IsRoot j) ∧
      ¬ (∀ j, (gcReg [] true false).nameOf j = some 7 → ¬ (gcReg [] true false).Live .precise j) := by
  refine ⟨by decide, fun h => h 1 rfl (by decide), fun h => h 1 rfl ?_⟩
  exact registry_keep_or_retain_kept_precise.1 1 rfl

/-- Registry entry 2 (name `7`) whose bounds are referenced only by the non-root section 1. -/
def gcDeadRef : GcIn := ⟨[mkSec 0 true false false, mkSec 5 false false false,
  mkSec 7 false false false], [], [(1, 7)]⟩

/-- `conservative_registryKept_of_live_reference`, hypothesis `hi`. -/
theorem conservative_cex_dead_referencer :
    ¬ gcDeadRef.Live .conservative 1 ∧ (1, 7) ∈ gcDeadRef.ss ∧
      ¬ RegistryKept gcDeadRef .conservative 7 := by
  have hdead : ∀ j, gcDeadRef.Live .conservative j → (j == 0) = true :=
    live_closed gcDeadRef .conservative (fun i => i == 0) (by decide) (by decide)
  refine ⟨fun h => absurd (hdead 1 h) (by decide), by simp [gcDeadRef], fun h => ?_⟩
  exact absurd (hdead 2 (h 2 rfl)) (by decide)

/-- `conservative_registryKept_of_live_reference`, hypothesis `hss`. -/
theorem conservative_cex_no_reference :
    (⟨(gcReg [] false false).secs, [], []⟩ : GcIn).Live .conservative 0 ∧
      ¬ (0, 7) ∈ (⟨(gcReg [] false false).secs, [], []⟩ : GcIn).ss ∧
      ¬ RegistryKept ⟨(gcReg [] false false).secs, [], []⟩ .conservative 7 := by
  refine ⟨Reach.root (by decide), by simp, fun h => ?_⟩
  have := live_closed ⟨(gcReg [] false false).secs, [], []⟩ .conservative (fun i => i == 0)
    (by decide) (by decide) 1 (h 1 rfl)
  exact absurd this (by decide)

/-- `registryKept_of_entries_rooted`, hypothesis `h`. -/
theorem rooted_cex_unrooted :
    ¬ (∀ j, (gcReg [] false false).nameOf j = some 7 → (gcReg [] false false).IsRoot j) ∧
      ¬ RegistryKept (gcReg [] false false) .precise 7 :=
  ⟨fun h => absurd (h 1 rfl) (by decide),
    fun h => registry_precise_link_failure_conservative_kept.1.2 1 rfl (h 1 rfl)⟩

/-- `live_iff_root_or_conservative_reference_of_noEdgeIntoName`, hypothesis `hj`: for a name
`9` that no section has, the no-edge hypothesis holds trivially, and section 1 (named `7`) is
kept through an edge. -/
theorem registry_iff_cex_other_name :
    NoEdgeIntoName (gcReg [(0, 1)] false false) 9 ∧ (gcReg [(0, 1)] false false).nameOf 1 ≠ some 9 ∧
      ¬ ((gcReg [(0, 1)] false false).Live .precise 1 ↔
        (gcReg [(0, 1)] false false).IsRoot 1 ∨
          ((SSPolicy.precise : SSPolicy) = .conservative ∧
            ∃ i, (gcReg [(0, 1)] false false).Live .precise i ∧
              (i, 9) ∈ (gcReg [(0, 1)] false false).ss)) := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  rcases h.mp registry_precise_silent_shrink.1 with h' | ⟨h', _⟩
  · exact absurd h' (by decide)
  · cases h'

/-- `registryKept_iff_of_noEdgeIntoName`, hypothesis `hN`: both entries are kept through edges
under the precise policy, but neither is rooted. -/
theorem registryKept_iff_cex_edges_into_entries :
    ¬ NoEdgeIntoName (gcReg [(0, 1), (0, 2)] false false) 7 ∧
      ¬ (RegistryKept (gcReg [(0, 1), (0, 2)] false false) .precise 7 ↔
        ∀ j, (gcReg [(0, 1), (0, 2)] false false).nameOf j = some 7 →
          (gcReg [(0, 1), (0, 2)] false false).IsRoot j ∨
            ((SSPolicy.precise : SSPolicy) = .conservative ∧
              ∃ i, (gcReg [(0, 1), (0, 2)] false false).Live .precise i ∧
                (i, 7) ∈ (gcReg [(0, 1), (0, 2)] false false).ss)) := by
  have hroot0 : (gcReg [(0, 1), (0, 2)] false false).IsRoot 0 := by decide
  refine ⟨by decide, fun h => ?_⟩
  have hk : RegistryKept (gcReg [(0, 1), (0, 2)] false false) .precise 7 := by
    intro j hj
    rcases nameOf_gcReg_eq _ _ _ j hj with rfl | rfl
    · exact Reach.step (Reach.root hroot0) (by simp [gcReg])
    · exact Reach.step (Reach.root hroot0) (by simp [gcReg])
  rcases h.mp hk 1 rfl with h' | ⟨h', _⟩
  · exact absurd h' (by decide)
  · cases h'



/-! ## Witnesses for results 6 and 7 that use the registry inputs -/

/-- Instance of result 6 with bounds accesses: under the conservative policy, the run "reach the
entry, then iterate the bounds of `7` to both registry entries" satisfies (A1), (A2) and (A3). -/
theorem gcSoundness_bounds_nonvacuity :
    EdgeAccessesFollowEdges (gcReg [] false false).edges (gcReg [] false false).IsRoot
        [.implicit 0, .bounds 0 7 1, .bounds 0 7 2] ∧
      ImplicitAccessesHitRoots (gcReg [] false false).IsRoot
        [.implicit 0, .bounds 0 7 1, .bounds 0 7 2] ∧
      BoundsAccessesRetained (gcReg [] false false) .conservative
        [.implicit 0, .bounds 0 7 1, .bounds 0 7 2] := by
  refine ⟨?_, ?_, ?_⟩
  · intro k i j hk
    match k, hk with
    | 0, hk => simp at hk
    | 1, hk => simp at hk
    | 2, hk => simp at hk
    | n + 3, hk => simp at hk
  · intro k j hk
    match k, hk with
    | 0, hk =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Acc.implicit.injEq] at hk
      subst hk
      decide
    | 1, hk => simp at hk
    | 2, hk => simp at hk
    | n + 3, hk => simp at hk
  · intro k i X j hk
    match k, hk with
    | 0, hk => simp at hk
    | 1, hk =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        Acc.bounds.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      exact ⟨by simp [gcReg], rfl, Or.inl (by decide), Or.inl rfl⟩
    | 2, hk =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        Acc.bounds.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      exact ⟨by simp [gcReg], rfl, Or.inl (by decide), Or.inl rfl⟩
    | n + 3, hk => simp at hk

/-- (A3) is tight: under the precise policy the run "reach the entry, then iterate the bounds of
`7` to entry 1" satisfies (A1) and (A2), violates (A3) (entry 1 is not a root), and entry 1 is
removed. -/
theorem gcSoundness_cex_bounds_access_unretained :
    EdgeAccessesFollowEdges (gcReg [] false false).edges (gcReg [] false false).IsRoot
        [.implicit 0, .bounds 0 7 1] ∧
      ImplicitAccessesHitRoots (gcReg [] false false).IsRoot [.implicit 0, .bounds 0 7 1] ∧
      ¬ BoundsAccessesRetained (gcReg [] false false) .precise [.implicit 0, .bounds 0 7 1] ∧
      ¬ RunPreserved (gcReg [] false false) .precise [.implicit 0, .bounds 0 7 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k i j hk
    match k, hk with
    | 0, hk => simp at hk
    | 1, hk => simp at hk
    | n + 2, hk => simp at hk
  · intro k j hk
    match k, hk with
    | 0, hk =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Acc.implicit.injEq] at hk
      subst hk
      decide
    | 1, hk => simp at hk
    | n + 2, hk => simp at hk
  · intro h
    rcases (h 1 0 7 1 rfl).2.2.2 with h' | h'
    · cases h'
    · exact absurd h' (by decide)
  · intro h
    exact registry_precise_link_failure_conservative_kept.1.2 1 rfl (h (.bounds 0 7 1) (by simp))

/-- Instance of `conservative_registryKept_of_live_reference`: section 0 of
`gcReg [] false false` is kept under the conservative policy and references the bounds of
`7`. -/
theorem conservative_registryKept_nonvacuity :
    (gcReg [] false false).Live .conservative 0 ∧ (0, 7) ∈ (gcReg [] false false).ss :=
  ⟨Reach.root (by decide), by simp [gcReg]⟩

/-- Instance of `registryKept_of_entries_rooted`: every section named `7` is a root when the
entries are matched by `KEEP` (`gcReg [] true false`) or carry the retain flag
(`gcReg [] false true`). -/
theorem registryKept_of_entries_rooted_nonvacuity :
    (∀ j, (gcReg [] true false).nameOf j = some 7 → (gcReg [] true false).IsRoot j) ∧
      (∀ j, (gcReg [] false true).nameOf j = some 7 → (gcReg [] false true).IsRoot j) := by
  constructor <;> (intro j hj; rcases nameOf_gcReg_eq _ _ _ j hj with rfl | rfl <;> decide)

/-- A dangling edge `0 → 99` into a two-section input. -/
def gcPhantom : GcIn where
  secs := [mkSec 0 true false false, mkSec 7 false false false]
  edges := [(0, 99)]
  ss := [(99, 7)]

/-- **An index past the end can be kept.** In `gcPhantom` the index `99` names no section, yet
it is kept along the dangling edge, and its start/stop reference keeps the registry `7` under
the conservative policy. -/
theorem phantom_section_live :
    gcPhantom.secs[99]? = none ∧ gcPhantom.Live .precise 99 ∧
      RegistryKept gcPhantom .conservative 7 := by
  have h0 : gcPhantom.IsRoot 0 := by decide
  have h99c : gcPhantom.Live .conservative 99 := Reach.step (Reach.root h0) (by simp [gcPhantom])
  refine ⟨rfl, Reach.step (Reach.root h0) (by simp [gcPhantom]), ?_⟩
  exact conservative_registryKept_of_live_reference gcPhantom 7 99 h99c (by simp [gcPhantom])

/-- An entry section referencing the bounds of `7`, with no section named `7`. -/
def gcEmptyReg : GcIn where
  secs := [mkSec 0 true false false]
  edges := []
  ss := [(0, 7)]

/-- **Empty registry.** When no section is named `7` but a kept section references its bounds,
`RegistryKept` holds vacuously and `StartStopUndefined` holds, under either policy. -/
theorem empty_registry_kept_and_undefined (pol : SSPolicy) :
    (∀ j, gcEmptyReg.nameOf j ≠ some 7) ∧ RegistryKept gcEmptyReg pol 7 ∧
      StartStopUndefined gcEmptyReg pol 7 := by
  have hno : ∀ j, gcEmptyReg.nameOf j ≠ some 7 := by
    intro j
    match j with
    | 0 => decide
    | _ + 1 => simp [GcIn.nameOf, gcEmptyReg]
  exact ⟨hno, fun j hj => absurd hj (hno j),
    ⟨⟨0, Reach.root (by decide), by simp [gcEmptyReg]⟩, fun j hj => absurd hj (hno j)⟩⟩

/-- `registryScan`: the scan of `7` from section 0 in `gcReg [] false false` visits entries 1 and
2; the scan of the absent name `9` is empty. -/
theorem registryScan_examples :
    registryScan (gcReg [] false false) 0 7 = [.bounds 0 7 1, .bounds 0 7 2] ∧
      registryScan (gcReg [] false false) 0 9 = [] := by
  decide

/-- `runPreserved_registryScan_iff_registryKept` on `gcReg [] false false`: the scan of `7` is
preserved under the conservative policy and not under the precise policy. -/
theorem registryScan_preserved_examples :
    RunPreserved (gcReg [] false false) .conservative (registryScan (gcReg [] false false) 0 7) ∧
      ¬ RunPreserved (gcReg [] false false) .precise (registryScan (gcReg [] false false) 0 7) :=
  ⟨(runPreserved_registryScan_iff_registryKept _ _ 0 7).mpr
      registry_precise_link_failure_conservative_kept.2,
    fun h => rooted_cex_unrooted.2 ((runPreserved_registryScan_iff_registryKept _ _ 0 7).mp h)⟩

/-- `ReachedBefore` and `BoundsAccessesRetained`: positive and negative instances. -/
theorem access_predicate_examples :
    ReachedBefore (gcReg [] false false).IsRoot [.implicit 0, .bounds 0 7 1] 1 0 ∧
      ¬ ReachedBefore (gcReg [] false false).IsRoot [.implicit 0, .bounds 0 7 1] 1 1 ∧
      BoundsAccessesRetained (gcReg [] false false) .conservative
        [.implicit 0, .bounds 0 7 1, .bounds 0 7 2] ∧
      ¬ BoundsAccessesRetained (gcReg [] false false) .precise [.implicit 0, .bounds 0 7 1] := by
  refine ⟨Or.inl (by decide), ?_, gcSoundness_bounds_nonvacuity.2.2,
    gcSoundness_cex_bounds_access_unretained.2.2.1⟩
  rintro (h | ⟨k', hk', a, ha, hd⟩)
  · exact absurd h (by decide)
  · match k', hk', ha with
    | 0, _, ha =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
      subst ha
      simp [Acc.dst] at hd

/-- `EagerRelroOrLazy`: holds for `mixedCfg` and for the lazy slot of `lazyRelroCfg` (lazy slots
may lie anywhere); fails for the eager slot of `eagerMutCfg` (outside RELRO). -/
theorem eagerRelroOrLazy_examples :
    EagerRelroOrLazy mixedCfg [(0, 0), (1, 1)] ∧ EagerRelroOrLazy lazyRelroCfg [(0, 0)] ∧
      ¬ EagerRelroOrLazy eagerMutCfg [(0, 0)] :=
  ⟨bindings_nonvacuity.1, bindings_iff_cex_call_faults.1, bindings_iff_cex_eager_outside_relro.1⟩

/-- `roundedMask` on an empty RELRO range: with `P = 2` and `rs = re = 1` every policy protects
nothing, in particular the down-up mask does not protect the page `[0, 2)`. -/
theorem roundedMask_empty_examples :
    roundedMask .downUp 2 1 1 0 = false ∧ roundedMask .downDown 2 1 1 0 = false ∧
      roundedMask .exact 2 1 1 1 = false ∧ roundedMask .downUp 2 1 2 0 = true := by
  decide

/-- `Prog2.CompiledPath`: static 1 of `[stMain, stUsedRetained]` has a compiler-kept path (it is
retained and compiler-used); static 2 of the program of `compileKept_and_srcReach_not_sufficient`
has none (its only source-level path passes through the dropped static 1). -/
theorem compiledPath_examples :
    (Prog2.mk [stMain, stUsedRetained] []).CompiledPath 1 ∧
      ¬ (Prog2.mk [stMain, stPlain, stUsedOnly] [(0, 1), (1, 2)]).CompiledPath 2 :=
  ⟨twoStage_nonvacuity.2.2.1, fun h =>
    compileKept_and_srcReach_not_sufficient.2.2 ((survives_iff_compiledPath _ 2).mpr h)⟩

end Toy.RelroGc
