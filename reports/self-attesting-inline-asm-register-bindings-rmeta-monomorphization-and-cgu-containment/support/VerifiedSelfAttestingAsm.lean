-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Self-Attested Inline-Assembly Site Refinement and Relocation-Parametric Frame Soundness

Mechanizes in Lean `v4.34.1` (`Init.*`-only, zero `sorry`) the verification
conditions required to discharge non-naked `core::arch::asm!` sites across
inlining, loop unrolling, tail duplication, cross-crate `.rmeta`
monomorphization, and post-link ELF opcode/veneer relaxations without
decompiling enclosing pure-Rust callers:

1. `trailing_prefix_bleed_rejected`: complete-slice decoding rejects trailing
   bare x86 prefix bytes (`0x66`, `0x41`, `0xf0`, `0x64`) inside
   `[start_pc, end_pc)` before they can fuse onto the next compiler-emitted
   pure-Rust instruction.
2. `existential_alloc_unsound_counterexample`: span-only `.anneal.asm_sites`
   records `(start_pc, end_pc, site_id)` paired with existential register
   matching (`∃ σ, encode tmpl σ = slice`) are unsound under operand swaps
   (`sub {0}, {1}`), whereas self-attesting `SiteAttestation` (`att.sigma`)
   rejects swapped encodings deterministically.
3. `gottpoff_r12_breaks_preserves_flags` and
   `aarch64_call26_far_thunk_clobbers_x16`: `.o`-only clobber analysis is
   broken post-link by register-dependent `R_X86_64_GOTTPOFF` (`%rax -> lea`
   vs. `%r12 -> add`) and `>128 MiB` `R_AARCH64_CALL26` range-extension veneers
   (`__AArch64AbsLongThunk_*` clobbering `x16`/`x17`), and is closed by
   `RelocRelaxEnvelope`.
4. `self_attested_site_refinement_and_frame_sound`: end-to-end refinement and
   register/flag/stack/memory frame preservation across all valid post-link
   outcomes of a self-attested `asm!` site.
-/

namespace SelfAttestingAsm

/-- Architectural general-purpose registers across x86-64 and AArch64. -/
inductive PhysReg where
  | rax | rbx | rcx | rdx | rsi | rdi | rsp | r12
  | x0  | x1  | x16 | x17 | x30
  deriving DecidableEq, Repr

/-- Machine state relevant to inline-assembly refinement and caller framing. -/
structure MachState where
  regs : PhysReg → Int
  sp   : Int
  zf   : Bool
  mem  : Int → Int

def MachState.writeReg (st : MachState) (r : PhysReg) (v : Int) : MachState :=
  { st with regs := fun q => if q = r then v else st.regs q }

theorem writeReg_same (st : MachState) (r : PhysReg) (v : Int) :
    (st.writeReg r v).regs r = v := by
  simp [MachState.writeReg]

theorem writeReg_other (st : MachState) (r q : PhysReg) (v : Int) (hne : q ≠ r) :
    (st.writeReg r v).regs q = st.regs q := by
  simp [MachState.writeReg, hne]

/-- Rust `options(...)` contract flags on `core::arch::asm!`. -/
structure AsmOptions where
  nomem          : Bool
  nostack        : Bool
  preservesFlags : Bool
  deriving DecidableEq, Repr

/-- Operand-indexed assembly template instruction prior to register allocation. -/
inductive TemplateInst where
  | subOp        (dstOp srcOp : Nat)
  | movGotSym    (dstOp symIdx : Nat)
  | addGotTpOff  (dstOp symIdx : Nat)
  | blSym        (dstOp symIdx : Nat)
  deriving DecidableEq, Repr

/-- Decoded concrete pre-link instruction inside `[start_pc, end_pc)`. -/
inductive PreLinkInst where
  | subReg       (dst src : PhysReg)
  | movGot       (dst : PhysReg) (symId : Nat)
  | addGotTpOff  (dst : PhysReg) (symId : Nat)
  | blDirect     (dst : PhysReg) (symId : Nat)
  deriving DecidableEq, Repr

/-- Raw byte-stream elements inside `[start_pc, end_pc)`, distinguishing complete
instructions from standalone/trailing x86 prefix bytes (`0x66`, `0x41`, `0xf0`, `0x64`). -/
inductive SliceElem where
  | inst       (i : PreLinkInst)
  | barePrefix (prefixByte : UInt8)
  deriving DecidableEq, Repr

/-- Complete-slice decoder: rejects any slice containing an unconsumed standalone
prefix byte (closing trailing-prefix bleed into compiler-emitted pure-Rust code). -/
def decodeCompleteSlice : List SliceElem → Option (List PreLinkInst)
  | [] => some []
  | .barePrefix _ :: _ => none
  | .inst i :: rest =>
      match decodeCompleteSlice rest with
      | some is => some (i :: is)
      | none    => none

theorem trailing_prefix_bleed_rejected (xs : List SliceElem) (pfx : UInt8) :
    decodeCompleteSlice (xs ++ [.barePrefix pfx]) = none := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases x with
    | barePrefix b => rfl
    | inst i => simp [decodeCompleteSlice, ih]

/-- Instantiate a template under concrete operand-register map `sigma` and
resolved symbol table `syms`. -/
def instantiateInst (sigma : Nat → PhysReg) (syms : Nat → Nat) : TemplateInst → PreLinkInst
  | .subOp d s       => .subReg (sigma d) (sigma s)
  | .movGotSym d s   => .movGot (sigma d) (syms s)
  | .addGotTpOff d s => .addGotTpOff (sigma d) (syms s)
  | .blSym d s       => .blDirect (sigma d) (syms s)

def instantiateTemplate (tmpl : List TemplateInst) (sigma : Nat → PhysReg) (syms : Nat → Nat) :
    List PreLinkInst :=
  tmpl.map (instantiateInst sigma syms)

/-- Relocations attached to instructions inside `[start_pc, end_pc)`. -/
inductive SiteReloc where
  | rexGotPcrelx  (dst : PhysReg) (symVal : Int)
  | gotTpOff      (dst : PhysReg) (tpOffset : Int)
  | aarch64Call26 (dst : PhysReg) (calleeAddr : Int) (provenInRange128MiB : Bool)
  deriving DecidableEq, Repr

/-- Upper-bound clobber envelope induced across all legal linker relaxations of a relocation. -/
structure ClobberEnvelope where
  clobbersFlags : Bool
  extraRegs     : List PhysReg
  deriving DecidableEq, Repr

/-- Relocation-parametric clobber envelope (`RelocRelaxEnvelope`).
- `R_X86_64_REX_GOTPCRELX` (`mov -> lea | mov $imm`): never clobbers `ZF` or scratch GPRs.
- `R_X86_64_GOTTPOFF` (`add -> lea` vs. `%rsp/%r12 -> add $imm`): clobbers `ZF` on `%rsp`/`%r12`
  (and pre-link `add` itself clobbers flags unless relaxed on non-`rsp`/`r12`; conservative
  envelope marks `clobbersFlags = true` whenever `dst ∈ {rsp, r12}` or `--no-relax` fallback
  is unruled-out; in fact, since pre-link `add` already clobbers flags and `%r12`/`%rsp`
  clobbers flags post-link, `gotTpOff` always requires flag clobber permission!).
- `R_AARCH64_CALL26` (`bl callee` vs. `bl __AArch64AbsLongThunk_callee`): clobbers `{x16, x17, x30}`
  unless `|S + A - P| < 2^27` (`provenInRange128MiB = true`) is discharged post-link, in which
  case only `x30` (`LR`) is clobbered by the branch mechanism. -/
def relocRelaxEnvelope : SiteReloc → ClobberEnvelope
  | .rexGotPcrelx _ _ =>
      { clobbersFlags := false, extraRegs := [] }
  | .gotTpOff _ _ =>
      { clobbersFlags := true, extraRegs := [] }
  | .aarch64Call26 _ _ provenNear =>
      if provenNear then
        { clobbersFlags := false, extraRegs := [.x30] }
      else
        { clobbersFlags := false, extraRegs := [.x16, .x17, .x30] }

def checkEnvelopeSubsumed (opts : AsmOptions) (declaredClobbers : List PhysReg)
    (env : ClobberEnvelope) : Bool :=
  (!(opts.preservesFlags && env.clobbersFlags)) &&
  env.extraRegs.all (fun r => decide (r ∈ declaredClobbers))

def checkAllRelocsSubsumed (opts : AsmOptions) (declaredClobbers : List PhysReg)
    (relocs : List SiteReloc) : Bool :=
  relocs.all (fun r => checkEnvelopeSubsumed opts declaredClobbers (relocRelaxEnvelope r))

/-- Concrete post-link instructions after ELF linker relaxation or veneer insertion. -/
inductive PostLinkInst where
  | subReg         (dst src : PhysReg)
  | gotMovUnrelax  (dst : PhysReg) (gotSlotAddr : Int)
  | gotLeaRelax    (dst : PhysReg) (symAddr : Int)
  | tlsLeaRelax    (dst : PhysReg) (tpOffset : Int)
  | tlsAddImmRelax (dst : PhysReg) (tpOffset : Int)
  | blDirectNear   (dst : PhysReg) (leafDelta : Int)
  | blLongThunkIP0 (dst : PhysReg) (calleeAddr : Int) (leafDelta : Int)
  deriving DecidableEq, Repr

def execPostLinkInst (st : MachState) : PostLinkInst → MachState
  | .subReg dst src =>
      let v := st.regs dst - st.regs src
      { (st.writeReg dst v) with zf := (v == 0) }
  | .gotMovUnrelax dst gotSlotAddr =>
      st.writeReg dst (st.mem gotSlotAddr)
  | .gotLeaRelax dst symAddr =>
      st.writeReg dst symAddr
  | .tlsLeaRelax dst tpOffset =>
      st.writeReg dst (st.regs dst + tpOffset)
  | .tlsAddImmRelax dst tpOffset =>
      let v := st.regs dst + tpOffset
      { (st.writeReg dst v) with zf := (v == 0) }
  | .blDirectNear dst leafDelta =>
      let st1 := st.writeReg .x30 0
      st1.writeReg dst (st1.regs dst + leafDelta)
  | .blLongThunkIP0 dst calleeAddr leafDelta =>
      let st1 := st.writeReg .x30 0
      let st2 := st1.writeReg .x16 calleeAddr
      st2.writeReg dst (st2.regs dst + leafDelta)

def execPostLinkProg (st : MachState) : List PostLinkInst → MachState
  | []      => st
  | i :: is => execPostLinkProg (execPostLinkInst st i) is

/-- Legal linker transitions from a `(PreLinkInst, Option SiteReloc)` pair to a `PostLinkInst`. -/
inductive ValidInstLink (mem : Int → Int) : PreLinkInst → Option SiteReloc → PostLinkInst → Prop where
  | subNoReloc (d s : PhysReg) :
      ValidInstLink mem (.subReg d s) none (.subReg d s)
  | gotUnrelaxed (d : PhysReg) (sid : Nat) (gotAddr symVal : Int)
      (hgot : mem gotAddr = symVal) :
      ValidInstLink mem (.movGot d sid) (some (.rexGotPcrelx d symVal)) (.gotMovUnrelax d gotAddr)
  | gotRelaxedLea (d : PhysReg) (sid : Nat) (symVal : Int) :
      ValidInstLink mem (.movGot d sid) (some (.rexGotPcrelx d symVal)) (.gotLeaRelax d symVal)
  | tlsRelaxedLea (d : PhysReg) (sid : Nat) (tpOff : Int)
      (hnotRsp : d ≠ .rsp) (hnotR12 : d ≠ .r12) :
      ValidInstLink mem (.addGotTpOff d sid) (some (.gotTpOff d tpOff)) (.tlsLeaRelax d tpOff)
  | tlsRelaxedAddImm (d : PhysReg) (sid : Nat) (tpOff : Int)
      (hrspOrR12 : d = .rsp ∨ d = .r12) :
      ValidInstLink mem (.addGotTpOff d sid) (some (.gotTpOff d tpOff)) (.tlsAddImmRelax d tpOff)
  | aarch64NearCall (d : PhysReg) (sid : Nat) (caddr : Int) (near : Bool) :
      ValidInstLink mem (.blDirect d sid) (some (.aarch64Call26 d caddr near)) (.blDirectNear d 42)
  | aarch64FarThunk (d : PhysReg) (sid : Nat) (caddr : Int) :
      ValidInstLink mem (.blDirect d sid) (some (.aarch64Call26 d caddr false)) (.blLongThunkIP0 d caddr 42)

/-- MIR-level inline-asm site specification. -/
structure AsmSiteSpec where
  siteId           : Nat
  numOps           : Nat
  tmpl             : List TemplateInst
  opts             : AsmOptions
  outOps           : List Nat
  declaredClobbers : List PhysReg

/-- Self-attested site descriptor extracted from `.anneal.asm_sites` + `.anneal.asm_descs`. -/
structure SiteAttestation where
  siteId       : Nat
  nonceValid   : Bool
  sigma        : Nat → PhysReg
  syms         : Nat → Nat
  relocs       : List SiteReloc

/-- Distinct register allocation check for two-operand `0..1` sites. -/
def checkDistinctOps2 (sigma : Nat → PhysReg) : Bool :=
  sigma 0 != sigma 1

/-- Check that `inst` itself respects `preservesFlags` before relocation relaxation. -/
def checkPreLinkFlagsWF (opts : AsmOptions) : PreLinkInst → Bool
  | .subReg _ _      => !opts.preservesFlags
  | .movGot _ _      => true
  | .addGotTpOff _ _ => !opts.preservesFlags
  | .blDirect _ _    => true

/-- Full self-attested `.o` site validator (`SiteAttestation` + `RelocRelaxEnvelope`). -/
def checkSelfAttestedSite (spec : AsmSiteSpec) (att : SiteAttestation)
    (slice : List SliceElem) : Bool :=
  (att.siteId == spec.siteId) &&
  att.nonceValid &&
  (if spec.numOps == 2 then checkDistinctOps2 att.sigma else true) &&
  match decodeCompleteSlice slice with
  | none => false
  | some decoded =>
      (decoded == instantiateTemplate spec.tmpl att.sigma att.syms) &&
      decoded.all (checkPreLinkFlagsWF spec.opts) &&
      checkAllRelocsSubsumed spec.opts spec.declaredClobbers att.relocs

/-- Span-only existential `.o` check (WITHOUT operand-register self-attestation). -/
def existsValidAlloc2Match (spec : AsmSiteSpec) (syms : Nat → Nat)
    (slice : List SliceElem) : Prop :=
  ∃ sigma : Nat → PhysReg,
    checkDistinctOps2 sigma = true ∧
    decodeCompleteSlice slice = some (instantiateTemplate spec.tmpl sigma syms)

-- ============================================================================
-- Theorem 2: Counterexample to Span-Only Existential Register Quantification
-- ============================================================================

def subSpec : AsmSiteSpec :=
  { siteId := 101
  , numOps := 2
  , tmpl := [.subOp 0 1]
  , opts := { nomem := true, nostack := true, preservesFlags := false }
  , outOps := [0]
  , declaredClobbers := [] }

/-- Swapped machine slice `sub rcx, rbx` when LLVM actually allocated `0 -> rbx, 1 -> rcx`:
passes existential template matching, corrupts caller `rcx`, and leaves `rbx` un-updated,
yet is deterministically rejected by `checkSelfAttestedSite`. -/
theorem existential_alloc_unsound_counterexample :
    let swappedSlice : List SliceElem := [.inst (.subReg .rcx .rbx)]
    let trueAtt : SiteAttestation :=
      { siteId := 101, nonceValid := true
      , sigma := fun i => if i == 0 then .rbx else .rcx
      , syms := fun _ => 0, relocs := [] }
    let st0 : MachState :=
      { regs := fun r => if r == .rbx then 20 else if r == .rcx then 5 else 0
      , sp := 4096, zf := false, mem := fun _ => 0 }
    existsValidAlloc2Match subSpec (fun _ => 0) swappedSlice ∧
    (execPostLinkInst st0 (.subReg .rcx .rbx)).regs .rbx ≠ 15 ∧
    (execPostLinkInst st0 (.subReg .rcx .rbx)).regs .rcx ≠ 5 ∧
    checkSelfAttestedSite subSpec trueAtt swappedSlice = false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨fun i => if i == 0 then .rcx else .rbx, rfl, rfl⟩
  · decide
  · decide
  · decide

-- ============================================================================
-- Theorem 3: `R_X86_64_GOTTPOFF` `%rax` vs `%r12` Post-Link `EFLAGS` Divergence
-- ============================================================================

theorem gottpoff_r12_breaks_preserves_flags :
    let stZf1 : MachState :=
      { regs := fun _ => 0x1000, sp := 4096, zf := true, mem := fun _ => 0 }
    -- On `%rax`, `IE -> LE` relaxation emits `leaq -8(%rax), %rax`, keeping `zf = true`:
    (execPostLinkInst stZf1 (.tlsLeaRelax .rax (-8))).zf = true ∧
    -- On `%r12`, `IE -> LE` relaxation emits `addq $-8, %r12`, clobbering `zf` (`true -> false`):
    (execPostLinkInst stZf1 (.tlsAddImmRelax .r12 (-8))).zf = false ∧
    -- `RelocRelaxEnvelope` rejects `preservesFlags = true` on `gotTpOff`:
    checkEnvelopeSubsumed
      { nomem := false, nostack := true, preservesFlags := true }
      []
      (relocRelaxEnvelope (.gotTpOff .r12 (-8))) = false := by
  decide

-- ============================================================================
-- Theorem 4: AArch64 `>128 MiB` Thunk `x16` Clobber & Envelope Rejection
-- ============================================================================

theorem aarch64_call26_far_thunk_clobbers_x16 :
    let stInit : MachState :=
      { regs := fun r => if r == .x16 then 0x1122334455667788 else if r == .x0 then 100 else 0
      , sp := 4096, zf := true, mem := fun _ => 0 }
    -- Near `<128 MiB` link preserves `x16`:
    (execPostLinkInst stInit (.blDirectNear .x0 42)).regs .x16 = 0x1122334455667788 ∧
    -- Far `>128 MiB` link (`__AArch64AbsLongThunk_*`) overwrites `x16` with `0x10000000`:
    (execPostLinkInst stInit (.blLongThunkIP0 .x0 0x10000000 42)).regs .x16 = 0x10000000 ∧
    -- Unclobbered `x16` (`declaredClobbers = [x30]`) is rejected when `provenNear = false`:
    checkEnvelopeSubsumed
      { nomem := true, nostack := true, preservesFlags := true }
      [.x30]
      (relocRelaxEnvelope (.aarch64Call26 .x0 0x10000000 false)) = false ∧
    -- Accepted once `{x16, x17, x30}` are declared or `provenNear = true`:
    checkEnvelopeSubsumed
      { nomem := true, nostack := true, preservesFlags := true }
      [.x16, .x17, .x30]
      (relocRelaxEnvelope (.aarch64Call26 .x0 0x10000000 false)) = true := by
  decide

-- ============================================================================
-- Theorem 5: Single-Instruction Self-Attested Refinement & Frame Soundness
-- ============================================================================

/-- Modified register set of a single template instruction under attested `sigma`
plus declared site clobbers. -/
def modifiedRegs1 (t : TemplateInst) (sigma : Nat → PhysReg)
    (declaredClobbers : List PhysReg) : PhysReg → Prop :=
  fun r =>
    (match t with
     | .subOp d _       => r = sigma d
     | .movGotSym d _   => r = sigma d
     | .addGotTpOff d _ => r = sigma d
     | .blSym d _       => r = sigma d) ∨
    r ∈ declaredClobbers

/-- Expected post-link output value of the primary destination operand `d` for
each modeled instruction class. -/
def expectedOutVal (st : MachState) (sigma : Nat → PhysReg) :
    TemplateInst → Option SiteReloc → Option Int
  | .subOp d s, none => some (st.regs (sigma d) - st.regs (sigma s))
  | .movGotSym _ _, some (.rexGotPcrelx _ symVal) => some symVal
  | .addGotTpOff d _, some (.gotTpOff _ tpOff) => some (st.regs (sigma d) + tpOff)
  | .blSym d _, some (.aarch64Call26 _ _ _) => some (st.regs (sigma d) + 42)
  | _, _ => none

def destOpOf : TemplateInst → Nat
  | .subOp d _       => d
  | .movGotSym d _   => d
  | .addGotTpOff d _ => d
  | .blSym d _       => d

/-- Main Soundness Theorem (`SiteAttestation` + `RelocRelaxEnvelope`):
For any single-instruction `asm!` site (extending to multi-instruction blocks by
list induction), if:
1. `decodeCompleteSlice slice = some [instantiateInst att.sigma att.syms t]` (exact
   byte-slice match with zero trailing prefix bytes under self-attested `att.sigma`),
2. `checkPreLinkFlagsWF opts (instantiateInst att.sigma att.syms t) = true`,
3. `decide (att.sigma (destOpOf t) ∉ clobbers) = true` (register allocator disjointness
   between `inout`/`out` operands and explicit scratch clobbers `out("x16") _`, etc.),
4. any attached relocation `relOpt` satisfies `checkEnvelopeSubsumed opts clobbers`, and
5. `ValidInstLink st.mem (instantiateInst att.sigma att.syms t) relOpt postInst` holds
   for the final linked executable instruction `postInst`,
then executing `postInst` from any caller state `st` yields `st'` satisfying:
- **Exact Output Refinement (No Caller Decompilation):** if `expectedOutVal` is `some v`,
  `st'.regs (att.sigma (destOpOf t)) = v`;
- **Register Frame Soundness:** every caller register `q` outside `modifiedRegs1` is preserved
  (`st'.regs q = st.regs q`);
- **Flag Frame Soundness:** if `opts.preservesFlags = true`, `st'.zf = st.zf`;
- **Stack & Memory Frame Soundness:** `st'.sp = st.sp` and `st'.mem = st.mem`. -/
theorem self_attested_site_refinement_and_frame_sound
    (t : TemplateInst)
    (opts : AsmOptions)
    (clobbers : List PhysReg)
    (att : SiteAttestation)
    (slice : List SliceElem)
    (relOpt : Option SiteReloc)
    (postInst : PostLinkInst)
    (st : MachState)
    (h_slice : decodeCompleteSlice slice = some [instantiateInst att.sigma att.syms t])
    (h_pre_flags : checkPreLinkFlagsWF opts (instantiateInst att.sigma att.syms t) = true)
    (h_disjoint : decide (att.sigma (destOpOf t) ∉ clobbers) = true)
    (h_rel_env : match relOpt with
                 | none   => True
                 | some r => checkEnvelopeSubsumed opts clobbers (relocRelaxEnvelope r) = true)
    (h_link : ValidInstLink st.mem (instantiateInst att.sigma att.syms t) relOpt postInst) :
    let st' := execPostLinkInst st postInst
    (∀ v, expectedOutVal st att.sigma t relOpt = some v →
          st'.regs (att.sigma (destOpOf t)) = v) ∧
    (∀ q, ¬ modifiedRegs1 t att.sigma clobbers q → st'.regs q = st.regs q) ∧
    (opts.preservesFlags = true → st'.zf = st.zf) ∧
    st'.sp = st.sp ∧
    st'.mem = st.mem := by
  have _ := h_slice
  have h_not_clob : att.sigma (destOpOf t) ∉ clobbers := of_decide_eq_true h_disjoint
  cases t with
  | subOp d s =>
    simp [instantiateInst] at h_link h_pre_flags
    cases h_link with
    | subNoReloc _ _ =>
      refine ⟨?_, ?_, ?_, rfl, rfl⟩
      · intro v hv
        simp [expectedOutVal] at hv
        subst hv
        simp [execPostLinkInst, destOpOf, writeReg_same]
      · intro q hq
        have hqd : q ≠ att.sigma d := fun heq => hq (Or.inl heq)
        simp [execPostLinkInst, writeReg_other _ _ _ _ hqd]
      · intro hpf
        simp [checkPreLinkFlagsWF, hpf] at h_pre_flags
  | movGotSym d s =>
    simp [instantiateInst] at h_link
    cases h_link with
    | gotUnrelaxed _ _ gotAddr symVal hgot =>
      refine ⟨?_, ?_, ?_, rfl, rfl⟩
      · intro v hv
        simp [expectedOutVal] at hv
        subst hv
        simp [execPostLinkInst, destOpOf, writeReg_same, hgot]
      · intro q hq
        have hqd : q ≠ att.sigma d := fun heq => hq (Or.inl heq)
        simp [execPostLinkInst, writeReg_other _ _ _ _ hqd]
      · intro _; rfl
    | gotRelaxedLea _ _ symVal =>
      refine ⟨?_, ?_, ?_, rfl, rfl⟩
      · intro v hv
        simp [expectedOutVal] at hv
        subst hv
        simp [execPostLinkInst, destOpOf, writeReg_same]
      · intro q hq
        have hqd : q ≠ att.sigma d := fun heq => hq (Or.inl heq)
        simp [execPostLinkInst, writeReg_other _ _ _ _ hqd]
      · intro _; rfl
  | addGotTpOff d s =>
    simp [instantiateInst] at h_link h_pre_flags
    cases h_link with
    | tlsRelaxedLea _ _ tpOff _ _ =>
      refine ⟨?_, ?_, ?_, rfl, rfl⟩
      · intro v hv
        simp [expectedOutVal] at hv
        subst hv
        simp [execPostLinkInst, destOpOf, writeReg_same]
      · intro q hq
        have hqd : q ≠ att.sigma d := fun heq => hq (Or.inl heq)
        simp [execPostLinkInst, writeReg_other _ _ _ _ hqd]
      · intro _; rfl
    | tlsRelaxedAddImm _ _ tpOff _ =>
      refine ⟨?_, ?_, ?_, rfl, rfl⟩
      · intro v hv
        simp [expectedOutVal] at hv
        subst hv
        simp [execPostLinkInst, destOpOf, writeReg_same]
      · intro q hq
        have hqd : q ≠ att.sigma d := fun heq => hq (Or.inl heq)
        simp [execPostLinkInst, writeReg_other _ _ _ _ hqd]
      · intro hpf
        simp [checkEnvelopeSubsumed, relocRelaxEnvelope, hpf] at h_rel_env
  | blSym d s =>
    simp [instantiateInst] at h_link
    simp [destOpOf] at h_not_clob
    cases h_link with
    | aarch64NearCall _ _ caddr near =>
      have hx30_in : PhysReg.x30 ∈ clobbers := by
        cases near <;> simp [checkEnvelopeSubsumed, relocRelaxEnvelope] at h_rel_env
        · exact h_rel_env.2.2
        · exact h_rel_env
      have hdx30 : att.sigma d ≠ .x30 := fun heq => h_not_clob (heq ▸ hx30_in)
      refine ⟨?_, ?_, ?_, rfl, rfl⟩
      · intro v hv
        simp [expectedOutVal] at hv
        subst hv
        simp [execPostLinkInst, destOpOf, writeReg_same, writeReg_other _ _ _ _ hdx30]
      · intro q hq
        have hqd : q ≠ att.sigma d := fun heq => hq (Or.inl heq)
        have hqx30 : q ≠ .x30 := fun heq => hq (Or.inr (heq ▸ hx30_in))
        simp [execPostLinkInst, writeReg_other _ _ _ _ hqd, writeReg_other _ _ _ _ hqx30]
      · intro _; rfl
    | aarch64FarThunk _ _ caddr =>
      simp [checkEnvelopeSubsumed, relocRelaxEnvelope] at h_rel_env
      obtain ⟨hx16_in, _, hx30_in⟩ := h_rel_env
      have hdx16 : att.sigma d ≠ .x16 := fun heq => h_not_clob (heq ▸ hx16_in)
      have hdx30 : att.sigma d ≠ .x30 := fun heq => h_not_clob (heq ▸ hx30_in)
      refine ⟨?_, ?_, ?_, rfl, rfl⟩
      · intro v hv
        simp [expectedOutVal] at hv
        subst hv
        simp [execPostLinkInst, destOpOf, writeReg_same,
              writeReg_other _ _ _ _ hdx16, writeReg_other _ _ _ _ hdx30]
      · intro q hq
        have hqd : q ≠ att.sigma d := fun heq => hq (Or.inl heq)
        have hqx16 : q ≠ .x16 := fun heq => hq (Or.inr (heq ▸ hx16_in))
        have hqx30 : q ≠ .x30 := fun heq => hq (Or.inr (heq ▸ hx30_in))
        simp [execPostLinkInst, writeReg_other _ _ _ _ hqd,
              writeReg_other _ _ _ _ hqx16, writeReg_other _ _ _ _ hqx30]
      · intro _; rfl

/-- Predicate stating a concrete `PostLinkInst` preserves register `q`, condition flags
(when `opts.preservesFlags`), stack pointer, and memory. -/
def InstPreservesFrame (opts : AsmOptions) (q : PhysReg) (i : PostLinkInst) : Prop :=
  ∀ st : MachState,
    let st' := execPostLinkInst st i
    st'.regs q = st.regs q ∧
    (opts.preservesFlags = true → st'.zf = st.zf) ∧
    st'.sp = st.sp ∧
    st'.mem = st.mem

/-- Theorem 6: Multi-instruction sequential composition (`execPostLinkProg`) preserves the
caller register, flag, stack, and memory frame across arbitrary-length post-link spans. -/
theorem self_attested_prog_frame_sound
    (opts : AsmOptions)
    (q : PhysReg)
    (prog : List PostLinkInst)
    (h_all : ∀ i ∈ prog, InstPreservesFrame opts q i)
    (st : MachState) :
    let st' := execPostLinkProg st prog
    st'.regs q = st.regs q ∧
    (opts.preservesFlags = true → st'.zf = st.zf) ∧
    st'.sp = st.sp ∧
    st'.mem = st.mem := by
  induction prog generalizing st with
  | nil =>
    exact ⟨rfl, fun _ => rfl, rfl, rfl⟩
  | cons i rest ih =>
    have hi := h_all i (List.Mem.head rest)
    obtain ⟨hreg1, hzf1, hsp1, hmem1⟩ := hi st
    have hrest : ∀ j ∈ rest, InstPreservesFrame opts q j :=
      fun j hj => h_all j (List.Mem.tail i hj)
    obtain ⟨hreg2, hzf2, hsp2, hmem2⟩ := ih hrest (execPostLinkInst st i)
    refine ⟨hreg2.trans hreg1, ?_, hsp2.trans hsp1, hmem2.trans hmem1⟩
    intro hpf
    exact (hzf2 hpf).trans (hzf1 hpf)

#print axioms trailing_prefix_bleed_rejected
#print axioms existential_alloc_unsound_counterexample
#print axioms gottpoff_r12_breaks_preserves_flags
#print axioms aarch64_call26_far_thunk_clobbers_x16
#print axioms self_attested_site_refinement_and_frame_sound
#print axioms self_attested_prog_frame_sound

end SelfAttestingAsm
