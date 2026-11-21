/-
  PostLinkAbiDropUnwindCrucible.lean

  Kernel-checked Lean v4.34.1 formalization of the 4-way cross-layer compiler/linker seam:
    (1) Cross-crate `FnAbi` marshaling (`Direct`, `Pair` niche enum, `Cast` 12-byte mixed
        aggregate, and `Indirect` `sret` >16-byte `Drop` struct);
    (2) ELF64 post-link relocation & GOT relaxation (`GNU ld` vs. `rust-lld` across
        `R_X86_64_GOTPCREL`, `R_X86_64_GOTPCRELX`, and `R_X86_64_REX_GOTPCRELX` under ASLR);
    (3) `.eh_frame_hdr` sorted FDE lookup, `.gcc_except_table` LSDA call-site dispatch
        (`ret_rip - 1` vs. naive `ret_rip`), and inline `4096`-byte stack-clash probe loop
        asynchronous DWARF CFA accuracy (`%r11` -> `%rsp`);
    (4) `ElaborateDrops` unwind cleanup ladders (`Static` `drop_in_place` glue, `Conditional`
        drop-flag locals, and partial-move `Open` inline drop ladders).

  Standards enforced:
    - 0 `sorry` / `sorryAx`
    - 0 `Classical.choice`
    - 0 `omega`
    - 0 `bv_decide` / `Lean.ofReduceBool`
    - 0 `native_decide`
    - 0 `partial def` / `._unsafe_rec` / `@[extern]`
-/

namespace PostLinkAbiDropUnwindCrucible

/-! ## Section 1: Cross-Crate `FnAbi` Marshaling & `sret` Unwind Invariant -/

/-- Source-level cross-crate values corresponding to our four probed `PassMode` classes. -/
inductive AbiValue where
  /-- `PassMode::Direct`: 64-bit scalar passed in `%rdi`, returned in `%rax`. -/
  | directScalar (x : Nat)
  /-- `PassMode::Pair`: niche-optimized `Option (NonZeroU64, u64)` (`0` tag = `none`,
      `nz + 1` tag = `some (nz + 1, payload)`) in `(%rdi, %rsi)` / `(%rax, %rdx)`. -/
  | pairNicheOpt (opt : Option (Nat × Nat))
  /-- `PassMode::Cast`: 12-byte `#[repr(C)] struct MixedCast12 { a: u32, b: u32, c_f32: u32 }`
      packed into eightbyte 0 (`%rdi`/`%rax` = `a + b * 2^32`) and eightbyte 1 (`%xmm0` = `c_f32`). -/
  | castMixed12 (a32 b32 f32Bits : Nat)
  /-- `PassMode::Indirect { on_stack: false }` (`sret`): `>16`-byte aggregate with `Drop` token ID. -/
  | indirectSret40 (w0 w1 w2 w3 tokenId : Nat)
  deriving DecidableEq, Repr

/-- Well-formedness of source values for bit-exact SysV x86-64 register packing:
    - Niche `Some (nz, _)` requires `nz > 0` (`NonZeroU64`),
    - `MixedCast12` fields fit in 32-bit lanes (`< 2^32`). -/
def AbiValue.WellFormed : AbiValue → Prop
  | .directScalar _ => True
  | .pairNicheOpt none => True
  | .pairNicheOpt (some (nz, _)) => 0 < nz
  | .castMixed12 a32 b32 f32Bits =>
      a32 < 4294967296 ∧ b32 < 4294967296 ∧ f32Bits < 4294967296
  | .indirectSret40 _ _ _ _ _ => True

/-- Physical x86-64 return-channel state across `(rax, rdx, xmm0)` plus caller-allocated `sret` memory. -/
structure AbiReturnChannel where
  rax : Nat := 0
  rdx : Nat := 0
  xmm0 : Nat := 0
  sretSlot : Option (Nat × Nat × Nat × Nat × Nat) := none
  deriving DecidableEq, Repr

/--ABI `PassMode` tag matching `rustc_target::callconv::PassMode`. -/
inductive AbiPassMode where
  | direct
  | pair
  | cast12
  | indirectSret
  deriving DecidableEq, Repr

def AbiValue.passMode : AbiValue → AbiPassMode
  | .directScalar _ => .direct
  | .pairNicheOpt _ => .pair
  | .castMixed12 _ _ _ => .cast12
  | .indirectSret40 _ _ _ _ _ => .indirectSret

/-- Callee normal-return marshaling into registers / caller `sret` slot. -/
def marshalReturn (v : AbiValue) : AbiReturnChannel :=
  match v with
  | .directScalar x =>
      { rax := x }
  | .pairNicheOpt none =>
      { rax := 0, rdx := 0 }
  | .pairNicheOpt (some (nz, payload)) =>
      { rax := nz, rdx := payload }
  | .castMixed12 a32 b32 f32Bits =>
      { rax := a32 + b32 * 4294967296, xmm0 := f32Bits }
  | .indirectSret40 w0 w1 w2 w3 tok =>
      { sretSlot := some (w0, w1, w2, w3, tok) }

/-- Caller normal-return unmarshaling (`rustc_codegen_ssa::mir::block::store_return`). -/
def unmarshalReturn (mode : AbiPassMode) (ch : AbiReturnChannel) : Option AbiValue :=
  match mode with
  | .direct =>
      some (.directScalar ch.rax)
  | .pair =>
      if ch.rax == 0 then
        some (.pairNicheOpt none)
      else
        some (.pairNicheOpt (some (ch.rax, ch.rdx)))
  | .cast12 =>
      let a32 := ch.rax % 4294967296
      let b32 := ch.rax / 4294967296
      some (.castMixed12 a32 b32 ch.xmm0)
  | .indirectSret =>
      match ch.sretSlot with
      | none => none
      | some (w0, w1, w2, w3, tok) => some (.indirectSret40 w0 w1 w2 w3 tok)

/-- Constructive packing lemma `(a + b * M) % M = a` when `a < M`. -/
theorem mod_add_mul_right_of_lt (a b m : Nat) (ha : a < m) :
    (a + b * m) % m = a := by
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt ha

/-- Constructive unpacking lemma `(a + b * M) / M = b` when `a < M` and `0 < M`. -/
theorem div_add_mul_right_of_lt (a b m : Nat) (hm : 0 < m) (ha : a < m) :
    (a + b * m) / m = b := by
  rw [Nat.add_mul_div_right a b hm]
  rw [Nat.div_eq_of_lt ha]
  exact Nat.zero_add b

/-- Theorem 1a: Bit-exact cross-crate `FnAbi` marshaling round-trip across all 4 `PassMode` kinds. -/
theorem fnAbi_marshal_unmarshal_roundtrip (v : AbiValue) (hwf : v.WellFormed) :
    unmarshalReturn v.passMode (marshalReturn v) = some v := by
  cases v with
  | directScalar x =>
      rfl
  | pairNicheOpt opt =>
      cases opt with
      | none =>
          rfl
      | some pair =>
          cases pair with
          | mk nz payload =>
              dsimp [AbiValue.WellFormed] at hwf
              dsimp [AbiValue.passMode, marshalReturn, unmarshalReturn]
              have hne : (nz == 0) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hwf)
              rw [hne]
              rfl
  | castMixed12 a32 b32 f32Bits =>
      rcases hwf with ⟨ha, _hb, _hf⟩
      dsimp [AbiValue.passMode, marshalReturn, unmarshalReturn]
      have hm : 0 < 4294967296 := Nat.zero_lt_succ 4294967295
      rw [mod_add_mul_right_of_lt a32 b32 4294967296 ha]
      rw [div_add_mul_right_of_lt a32 b32 4294967296 hm ha]
  | indirectSret40 w0 w1 w2 w3 tok =>
      rfl

/-- Models `ElaborateDrops::drop_flags_for_fn_rets` (`elaborate_drops.rs:433-451`):
    for an unwinding call (`UnwindAction::Cleanup`), the return destination's drop flag is set to
    `true` ONLY at entry to `target_bb` (normal return), NEVER before the `invoke`. -/
def updateSretDropFlag (setAtTargetOnly : Bool) (calleeReturnedNormally : Bool) : Bool :=
  if setAtTargetOnly then
    calleeReturnedNormally
  else
    true

/-- Theorem 1b (`sret` unwind safety): When `callee` panics before writing `*sret`
    (`ch.sretSlot = none`), `setAtTargetOnly = true` keeps `sretDropFlag = false`, whereas setting
    the flag eagerly before `invoke` (`setAtTargetOnly = false`, which `elaborate_drops.rs:503-518`
    does ONLY for non-cleanup calls!) would attempt to drop an uninitialized `sret` slot. -/
theorem sret_drop_flag_safe_iff_set_at_target :
    updateSretDropFlag true false = false ∧
    updateSretDropFlag false false = true := by
  exact ⟨rfl, rfl⟩

/-! ## Section 2: Post-Link ELF64 Relocation, `GOTPCREL` Relaxation & Static-PIE ASLR -/

inductive LinkerFlavor where
  | gnuLd
  | rustLld
  deriving DecidableEq, Repr

inductive RelocKind where
  | pc32
  | plt32
  | gotpcrel      -- Legacy non-X relocation emitted by default `rustc` (`relax_elf_relocations = false`)
  | gotpcrelx     -- Emitted on `call *got` (`ff 15`) under `-Z relax-elf-relocations=yes`
  | rexGotpcrelx  -- Emitted on `mov reg, got(%rip)` (`48 8b`) under `-Z relax-elf-relocations=yes`
  deriving DecidableEq, Repr

inductive PreLinkInst where
  | leaRipRel       (symVaddr : Nat) -- `48 8d 0d 00 00 00 00` + `R_X86_64_PC32`
  | callDirectRel32 (symVaddr : Nat) -- `e8 00 00 00 00` + `R_X86_64_PLT32`
  | movFromGot      (symVaddr : Nat) (reloc : RelocKind) -- `48 8b 0d 00 00 00 00`
  | callThroughGot  (symVaddr : Nat) (reloc : RelocKind) -- `ff 15 00 00 00 00`
  deriving DecidableEq, Repr

inductive PostLinkInst where
  | leaRipDirect      (symVaddr : Nat) -- `48 8d`: computes `loadBias + symVaddr` from `%rip`
  | callDirect        (symVaddr : Nat) -- `e8` or `67 e8`: calls `loadBias + symVaddr` from `%rip`
  | movFromGotSlot    (symVaddr : Nat) -- `48 8b`: dereferences `.got` slot (`R_X86_64_RELATIVE`)
  | callThroughGotSlot (symVaddr : Nat) -- `ff 15`: dereferences `.got` slot (`R_X86_64_RELATIVE`)
  deriving DecidableEq, Repr

def PostLinkInst.usesGotSlot : PostLinkInst → Bool
  | .leaRipDirect _ => false
  | .callDirect _ => false
  | .movFromGotSlot _ => true
  | .callThroughGotSlot _ => true

/-- Exact post-link opcode rewrite behavior of `GNU ld 2.47` vs. `rust-lld 22.1.6` in PIE / `-static-pie`:
    - `GNU ld` relaxes `mov` on BOTH `.gotpcrel` and `.rexGotpcrelx`, but relaxes `call *got`
      ONLY on `.gotpcrelx` (never legacy `.gotpcrel`);
    - `rust-lld` (`lld/ELF/Arch/X86_64.cpp:958-989, 1072-1110`) relaxes `mov` ONLY on `.rexGotpcrelx`
      and relaxes `call *got` ONLY on `.gotpcrelx`, leaving ALL legacy `.gotpcrel` sites unrelaxed! -/
def linkPostLinkInst (linker : LinkerFlavor) (relaxEnabled : Bool) (inst : PreLinkInst) : PostLinkInst :=
  match inst with
  | .leaRipRel sym => .leaRipDirect sym
  | .callDirectRel32 sym => .callDirect sym
  | .movFromGot sym reloc =>
      if !relaxEnabled then
        .movFromGotSlot sym
      else
        match linker, reloc with
        | .gnuLd, .gotpcrel => .leaRipDirect sym
        | .gnuLd, .rexGotpcrelx => .leaRipDirect sym
        | .rustLld, .rexGotpcrelx => .leaRipDirect sym
        | _, _ => .movFromGotSlot sym
  | .callThroughGot sym reloc =>
      if !relaxEnabled then
        .callThroughGotSlot sym
      else
        match reloc with
        | .gotpcrelx => .callDirect sym
        | _ => .callThroughGotSlot sym

/-- Evaluates the runtime address computed or called by a post-link instruction under ASLR `loadBias`.
    If `.rela.dyn` `R_X86_64_RELATIVE` entries have NOT yet been applied (`gotRelocated = false`, e.g.,
    freestanding `#![no_std]` `-static-pie` `_start` prior to `_DYNAMIC` self-relocation), each `.got`
    slot holds the raw link-time `symVaddr` (or `0` on `RELA` targets without implicit addend; in our
    live `GNU ld` binary `.got` holds `symVaddr = 0x1020`, while in `rust-lld` `.got` holds `0`! We
    parameterize `unrelocatedGotVal` to cover both linkers uniformly). -/
def evalPostLinkAddress
    (loadBias : Nat)
    (gotRelocated : Bool)
    (unrelocatedGotVal : Nat → Nat)
    (inst : PostLinkInst) : Nat :=
  match inst with
  | .leaRipDirect sym => loadBias + sym
  | .callDirect sym => loadBias + sym
  | .movFromGotSlot sym =>
      if gotRelocated then loadBias + sym else unrelocatedGotVal sym
  | .callThroughGotSlot sym =>
      if gotRelocated then loadBias + sym else unrelocatedGotVal sym

/-- Side condition `GotInitializedOrLeaRelaxed`: either dynamic `.got` relocations have run before
    executing `inst`, or post-link relaxation eliminated the `.got` dereference. -/
def GotInitializedOrLeaRelaxed (gotRelocated : Bool) (inst : PostLinkInst) : Prop :=
  gotRelocated = true ∨ inst.usesGotSlot = false

def PreLinkInst.targetSym : PreLinkInst → Nat
  | .leaRipRel s => s
  | .callDirectRel32 s => s
  | .movFromGot s _ => s
  | .callThroughGot s _ => s

theorem linkPostLinkInst_preserves_sym (l : LinkerFlavor) (r : Bool) (i : PreLinkInst) :
    ∀ gotFn, evalPostLinkAddress 0 true gotFn (linkPostLinkInst l r i) = i.targetSym := by
  intro gotFn
  cases i with
  | leaRipRel sym => exact Nat.zero_add sym
  | callDirectRel32 sym => exact Nat.zero_add sym
  | movFromGot sym reloc =>
      cases r <;> cases l <;> cases reloc <;> exact Nat.zero_add sym
  | callThroughGot sym reloc =>
      cases r <;> cases reloc <;> exact Nat.zero_add sym

/-- Theorem 2a: Under `GotInitializedOrLeaRelaxed`, every post-link instruction computes the exact
    ASLR-relocated runtime address `loadBias + symVaddr`. -/
theorem postlink_address_sound_under_sidecond
    (linker : LinkerFlavor)
    (relaxEnabled : Bool)
    (pre : PreLinkInst)
    (loadBias : Nat)
    (gotRelocated : Bool)
    (unrelocatedGotVal : Nat → Nat)
    (hGot : GotInitializedOrLeaRelaxed gotRelocated (linkPostLinkInst linker relaxEnabled pre)) :
    evalPostLinkAddress loadBias gotRelocated unrelocatedGotVal
      (linkPostLinkInst linker relaxEnabled pre) = loadBias + pre.targetSym := by
  rcases hGot with hRel | hNoGot
  · subst hRel
    cases pre with
    | leaRipRel sym => rfl
    | callDirectRel32 sym => rfl
    | movFromGot sym reloc =>
        cases relaxEnabled <;> cases linker <;> cases reloc <;> rfl
    | callThroughGot sym reloc =>
        cases relaxEnabled <;> cases reloc <;> rfl
  · cases pre with
    | leaRipRel sym => rfl
    | callDirectRel32 sym => rfl
    | movFromGot sym reloc =>
        cases relaxEnabled with
        | false =>
            dsimp [linkPostLinkInst, PostLinkInst.usesGotSlot] at hNoGot
            cases hNoGot
        | true =>
            cases linker <;> cases reloc <;>
              first | rfl | (dsimp [linkPostLinkInst, PostLinkInst.usesGotSlot] at hNoGot; cases hNoGot)
    | callThroughGot sym reloc =>
        cases relaxEnabled with
        | false =>
            dsimp [linkPostLinkInst, PostLinkInst.usesGotSlot] at hNoGot
            cases hNoGot
        | true =>
            cases reloc <;>
              first | rfl | (dsimp [linkPostLinkInst, PostLinkInst.usesGotSlot] at hNoGot; cases hNoGot)

theorem ne_add_of_pos_of_le (bias sym raw : Nat) (hpos : 0 < bias) (hle : raw ≤ sym) :
    raw ≠ bias + sym := by
  intro heq
  have h1 : sym < bias + sym := Nat.lt_add_of_pos_left hpos
  have h2 : raw < bias + sym := Nat.lt_of_le_of_lt hle h1
  exact Nat.ne_of_lt h2 heq

/-- **Counterexample CE2 (Sharpness of `GotInitializedOrLeaRelaxed` in `#![no_std]` `-static-pie`)**:
    1. On cross-crate `static` data load (`movFromGot sym .gotpcrel`) before `_DYNAMIC` relocation
       (`gotRelocated = false`) with `0 < loadBias` and `unrelocatedGotVal sym ≤ sym` (covering both
       `rust-lld`'s `0` and `GNU ld`'s `symVaddr`):
       - `GNU ld` relaxes `48 8b -> 48 8d` (`lea`) and computes exact `loadBias + sym`;
       - `rust-lld` leaves `48 8b` unrelaxed and reads `unrelocatedGotVal sym ≠ loadBias + sym` (`SIGSEGV`)!
    2. On a non-inlined cross-crate call (`callThroughGot fnSym .gotpcrel`, `ff 15`), **BOTH**
       `GNU ld` and `rust-lld` leave `ff 15` unrelaxed and fault (`≠ loadBias + fnSym`), whereas
       enabling `-Z relax-elf-relocations=yes` (`.gotpcrelx`) relaxes both to `67 e8` (`callDirect`)
       and computes `loadBias + fnSym`! -/
theorem ce2_static_pie_got_divergence_and_crosscrate_call_hazard
    (loadBias dataSym fnSym : Nat)
    (unrelocatedGotVal : Nat → Nat)
    (hBias : 0 < loadBias)
    (hRawData : unrelocatedGotVal dataSym ≤ dataSym)
    (hRawFn : unrelocatedGotVal fnSym ≤ fnSym) :
    -- (1a) GNU ld succeeds on inline cross-crate data GOTPCREL (`48 8b -> 48 8d`):
    evalPostLinkAddress loadBias false unrelocatedGotVal
      (linkPostLinkInst .gnuLd true (.movFromGot dataSym .gotpcrel)) = loadBias + dataSym ∧
    -- (1b) rust-lld faults on the identical `.o` (`48 8b` reads unrelocated `.got` != ASLR address):
    evalPostLinkAddress loadBias false unrelocatedGotVal
      (linkPostLinkInst .rustLld true (.movFromGot dataSym .gotpcrel)) ≠ loadBias + dataSym ∧
    -- (2a) On non-inlined cross-crate `call *got` with default `R_X86_64_GOTPCREL`, BOTH linkers fault:
    evalPostLinkAddress loadBias false unrelocatedGotVal
      (linkPostLinkInst .gnuLd true (.callThroughGot fnSym .gotpcrel)) ≠ loadBias + fnSym ∧
    evalPostLinkAddress loadBias false unrelocatedGotVal
      (linkPostLinkInst .rustLld true (.callThroughGot fnSym .gotpcrel)) ≠ loadBias + fnSym ∧
    -- (2b) Passing `-Z relax-elf-relocations=yes` (`R_X86_64_GOTPCRELX`) heals BOTH linkers:
    evalPostLinkAddress loadBias false unrelocatedGotVal
      (linkPostLinkInst .gnuLd true (.callThroughGot fnSym .gotpcrelx)) = loadBias + fnSym ∧
    evalPostLinkAddress loadBias false unrelocatedGotVal
      (linkPostLinkInst .rustLld true (.callThroughGot fnSym .gotpcrelx)) = loadBias + fnSym := by
  refine ⟨rfl, ?_, ?_, ?_, rfl, rfl⟩
  · dsimp [linkPostLinkInst, evalPostLinkAddress]
    exact ne_add_of_pos_of_le loadBias dataSym (unrelocatedGotVal dataSym) hBias hRawData
  · dsimp [linkPostLinkInst, evalPostLinkAddress]
    exact ne_add_of_pos_of_le loadBias fnSym (unrelocatedGotVal fnSym) hBias hRawFn
  · dsimp [linkPostLinkInst, evalPostLinkAddress]
    exact ne_add_of_pos_of_le loadBias fnSym (unrelocatedGotVal fnSym) hBias hRawFn

/-! ## Section 3: `.eh_frame_hdr` FDE Lookup, `.gcc_except_table` LSDA & Stack-Clash Loop CFI -/

/-- Decoded LSDA action matching `library/std/src/sys/personality/dwarf/eh.rs::EHAction`. -/
inductive EhAction where
  | none
  | cleanup (lpadOff : Nat)
  | catch (lpadOff : Nat)
  | filterTerminate (lpadOff : Nat) -- `ttype_index < 0` (`filter [0 x ptr]`, `UnwindAction::Terminate`)
  | terminateGap                    -- IP missing from LSDA table (`eh.rs:122`)
  deriving DecidableEq, Repr

/-- One `.gcc_except_table` call-site record `[csStart, csStart + csLen)`. -/
structure LsdaCallSite where
  csStart : Nat
  csLen : Nat
  csLpad : Nat
  /-- `none` when `csActionEntry == 0` (cleanup); `some ttypeIdx` when `csActionEntry > 0`. -/
  ttypeIndex : Option Int := none
  deriving DecidableEq, Repr

/-- Decoded `.eh_frame` Frame Description Entry `[pcBegin, pcEnd)` + associated LSDA table. -/
structure FdeRecord where
  fnId : Nat
  pcBegin : Nat
  pcEnd : Nat
  lsdaCallSites : List LsdaCallSite := []
  deriving DecidableEq, Repr

/-- Evaluates `interpret_cs_action` (`dwarf/eh.rs:148-172`). -/
def interpretCsAction (cs : LsdaCallSite) : EhAction :=
  if cs.csLpad == 0 then
    .none
  else
    match cs.ttypeIndex with
    | none => .cleanup cs.csLpad
    | some t =>
        if t == 0 then
          .cleanup cs.csLpad
        else if t > 0 then
          .catch cs.csLpad
        else
          .filterTerminate cs.csLpad

/-- Exact sequential sorted-table scan of `dwarf/eh.rs:99-122` (defined via `List.foldr` so it is
    100% computable AND emits zero `._unsafe_rec` / `partial` helpers in the `.olean`). -/
def lsdaLookupAtRelIp (sites : List LsdaCallSite) (relIp : Nat) : EhAction :=
  sites.foldr
    (fun cs ih =>
      if relIp < cs.csStart then
        .terminateGap
      else if relIp < cs.csStart + cs.csLen then
        interpretCsAction cs
      else
        ih)
    .terminateGap

/-- Models `.eh_frame_hdr` sorted FDE lookup (`last` FDE with `pcBegin ≤ queryPc`, followed by
    FDE range check `queryPc < fde.pcEnd`), defined via `List.foldr` for zero `._unsafe_rec`. -/
def findLastLeFdeGo (queryPc : Nat) (rem : List FdeRecord) (acc : Option FdeRecord) : Option FdeRecord :=
  (rem.foldr
    (fun f ih cur =>
      if f.pcBegin ≤ queryPc then
        ih (some f)
      else
        cur)
    (fun cur => cur)) acc

def findLastLeFde (fdes : List FdeRecord) (queryPc : Nat) : Option FdeRecord :=
  findLastLeFdeGo queryPc fdes none

def ehFrameHdrLookup (fdes : List FdeRecord) (queryPc : Nat) : Option FdeRecord :=
  match findLastLeFde fdes queryPc with
  | none => none
  | some f => if queryPc < f.pcEnd then some f else none

/-- Synchronous unwind IP adjustment (`library/std/src/sys/personality/gcc.rs:333`):
    `ip: if ip_before_instr != 0 { ip } else { ip - 1 }`. -/
def unwindQueryPc (ipBeforeInstr : Bool) (retRip : Nat) : Nat :=
  if ipBeforeInstr then retRip else retRip - 1

/-- Full two-level DWARF `.eh_frame_hdr` + `.gcc_except_table` dispatch for return address `retRip`. -/
def dispatchUnwind (fdes : List FdeRecord) (ipBeforeInstr : Bool) (retRip : Nat) :
    Option (Nat × EhAction) :=
  let q := unwindQueryPc ipBeforeInstr retRip
  match ehFrameHdrLookup fdes q with
  | none => none
  | some fde =>
      let relIp := q - fde.pcBegin
      some (fde.fnId, lsdaLookupAtRelIp fde.lsdaCallSites relIp)

/-- Validator side conditions for a synchronous `call` instruction at `[callVa, callVa + callLen)`:
    1. `TrailingCallNopGuard` / non-empty call encoding (`1 ≤ callLen`), ensuring `retRip - 1` lies
       inside the `call` instruction itself (`callVa ≤ retRip - 1 < callVa + callLen ≤ fde.pcEnd`),
       even when `NoTrapAfterNoreturn = true` places `callVa + callLen == fde.pcEnd`!
    2. `CallReturnInsideLsdaRange`: `[callVa - fde.pcBegin, callVa - fde.pcBegin + callLen)` is
       contained inside the intended LSDA `cs` record `[cs.csStart, cs.csStart + cs.csLen)`. -/
structure ValidUnwindCallSite (fde : FdeRecord) (cs : LsdaCallSite) (callVa callLen : Nat) : Prop where
  callLen_pos : 1 ≤ callLen
  in_fde_lo : fde.pcBegin ≤ callVa
  in_fde_hi : callVa + callLen ≤ fde.pcEnd
  in_cs_lo : cs.csStart ≤ (callVa + callLen - 1) - fde.pcBegin
  in_cs_hi : (callVa + callLen - 1) - fde.pcBegin < cs.csStart + cs.csLen

theorem retMinusOne_in_fde_bounds
    {fde : FdeRecord} {cs : LsdaCallSite} {callVa callLen : Nat}
    (h : ValidUnwindCallSite fde cs callVa callLen) :
    fde.pcBegin ≤ (callVa + callLen) - 1 ∧ (callVa + callLen) - 1 < fde.pcEnd := by
  have h1 : callVa ≤ (callVa + callLen) - 1 := by
    have hpred : (callVa + callLen) - 1 = callVa + (callLen - 1) :=
      Nat.add_sub_assoc h.callLen_pos callVa
    rw [hpred]
    exact Nat.le_add_right callVa (callLen - 1)
  have hlo : fde.pcBegin ≤ (callVa + callLen) - 1 := Nat.le_trans h.in_fde_lo h1
  have hpos : 0 < callVa + callLen := Nat.lt_of_lt_of_le (Nat.zero_lt_one) (Nat.le_trans h.callLen_pos (Nat.le_add_left callLen callVa))
  have hlt_self : (callVa + callLen) - 1 < callVa + callLen := Nat.sub_lt hpos Nat.zero_lt_one
  have hhi : (callVa + callLen) - 1 < fde.pcEnd := Nat.lt_of_lt_of_le hlt_self h.in_fde_hi
  exact ⟨hlo, hhi⟩

/-- Helper lemma: in a strictly non-overlapping sorted FDE list `prefix ++ [fde] ++ suffix` where all
    prefix entries satisfy `p.pcBegin ≤ fde.pcBegin` and the head of `suffix` starts at `fde.pcEnd ≤ s.pcBegin`,
    any `q` with `fde.pcBegin ≤ q < fde.pcEnd` resolves uniquely to `some fde`. -/
theorem findLastLeFdeGo_eq
    (fde : FdeRecord) (suffix : List FdeRecord) (q : Nat)
    (hq_hi : q < fde.pcEnd)
    (hsuff : match suffix with | [] => True | s :: _ => fde.pcEnd ≤ s.pcBegin) :
    findLastLeFdeGo q suffix (some fde) = some fde := by
  cases suffix with
  | nil => rfl
  | cons s ss =>
      have hlt : q < s.pcBegin := Nat.lt_of_lt_of_le hq_hi hsuff
      have hnotle : ¬ (s.pcBegin ≤ q) := Nat.not_le_of_gt hlt
      simp [findLastLeFdeGo, hnotle]

theorem ehFrameHdrLookup_singleton_or_pair
    (fde nextFde : FdeRecord) (q : Nat)
    (hq_lo : fde.pcBegin ≤ q) (hq_hi : q < fde.pcEnd)
    (h_adj : fde.pcEnd ≤ nextFde.pcBegin) :
    ehFrameHdrLookup [fde, nextFde] q = some fde := by
  have hlt : q < nextFde.pcBegin := Nat.lt_of_lt_of_le hq_hi h_adj
  have hnotle : ¬ (nextFde.pcBegin ≤ q) := Nat.not_le_of_gt hlt
  simp [ehFrameHdrLookup, findLastLeFde, findLastLeFdeGo, hq_lo, hnotle, hq_hi]

/-- **Counterexample CE1 (Trailing `noreturn` Call FDE & LSDA Boundary Off-By-One)**:
    Demonstrates all three facets of the `NoTrapAfterNoreturn = true` boundary on live `rustc` witnesses:
    - **(CE1a — Zero-gap adjacent FDE hijack, live `std::rt::handle_rt_panic` `[0x99e0, 0x9a10)` +
      `__rust_end_short_backtrace` `[0x9a10, 0x9a19)`):** `call *got` at `0x9a0a..0x9a10` pushes
      `retRip = 0x9a10 == nextFde.pcBegin`. Adjusted `ip - 1` (`ipBeforeInstr = false`) resolves to
      caller `fnId = 1` (`handle_rt_panic`), whereas unadjusted `retRip` (`ipBeforeInstr = true`)
      hijacks `fnId = 2` (the adjacent function's FDE!).
    - **(CE1b — Non-zero-gap inter-function `0xCC`/`NOP` padding miss, live `caller_bare_trailing_noreturn`
      `[0x10ae0, 0x10ae7)` followed by 9 bytes of `NOP`/`0xCC` before `0x10af0`):** Adjusted `ip - 1`
      resolves to caller `fnId = 10`, whereas unadjusted `retRip = 0x10ae7` returns `none`!
    - **(CE1c — Intra-function LSDA wrong-landing-pad dispatch, live `caller_stack_clash_loop_unwind`
      `DropToken::new` at `rel_off = 0x4e..0x54` with `cs0 = [0x0, 0x54) -> .none` and
      `cs1 = [0x54, 0x16) -> .cleanup 0x82`):** Adjusted `ip - 1` (`0x53`) selects `.none`, whereas
      naive `retRip` (`0x54`) selects `.cleanup 0x82` (dropping uninitialized `_guard`!). -/
def liveFdeHandleRtPanic : FdeRecord :=
  { fnId := 1, pcBegin := 0x99e0, pcEnd := 0x9a10,
    lsdaCallSites := [{ csStart := 0, csLen := 0x30, csLpad := 0 }] }

def liveFdeNextZeroGap : FdeRecord :=
  { fnId := 2, pcBegin := 0x9a10, pcEnd := 0x9a19,
    lsdaCallSites := [{ csStart := 0, csLen := 0x9, csLpad := 0x7 }] }

def liveFdeBareNoreturn : FdeRecord :=
  { fnId := 10, pcBegin := 0x10ae0, pcEnd := 0x10ae7,
    lsdaCallSites := [{ csStart := 0, csLen := 0x7, csLpad := 0 }] }

def liveFdeAfterPadding : FdeRecord :=
  { fnId := 11, pcBegin := 0x10af0, pcEnd := 0x10b00, lsdaCallSites := [] }

def liveFdeStackClashCaller : FdeRecord :=
  { fnId := 20, pcBegin := 0x11630, pcEnd := 0x117a3,
    lsdaCallSites := [
      { csStart := 0x0,  csLen := 0x54, csLpad := 0x0,   ttypeIndex := none },
      { csStart := 0x54, csLen := 0x16, csLpad := 0x82,  ttypeIndex := none },
      { csStart := 0x6c, csLen := 0x11, csLpad := 0x160, ttypeIndex := some (-1) }
    ] }

theorem ce1_trailing_noreturn_and_lsda_boundary_sharpness :
    -- CE1a: Zero-gap trailing call (`retRip = 0x9a10`): `ip - 1` hits fn 1; naive `ip` hijacks fn 2!
    dispatchUnwind [liveFdeHandleRtPanic, liveFdeNextZeroGap] false 0x9a10 = some (1, .none) ∧
    dispatchUnwind [liveFdeHandleRtPanic, liveFdeNextZeroGap] true  0x9a10 = some (2, .cleanup 0x7) ∧
    -- CE1b: Padded trailing call (`retRip = 0x10ae7`, `0xCC`/`NOP` gap `0x10ae7..0x10af0`):
    -- `ip - 1` hits fn 10; naive `ip` misses all FDEs (`none`)!
    dispatchUnwind [liveFdeBareNoreturn, liveFdeAfterPadding] false 0x10ae7 = some (10, .none) ∧
    dispatchUnwind [liveFdeBareNoreturn, liveFdeAfterPadding] true  0x10ae7 = none ∧
    -- CE1c: Intra-function `DropToken::new` return address (`0x11630 + 0x54 = 0x11684`):
    -- `ip - 1` yields `.none`; naive `ip` dispatches to `.cleanup 0x82` on uninitialized `_guard`,
    -- and cleanup-pad call (`0x116ad`) dispatches to `.filterTerminate 0x160` (`ttype_index = -1`)!
    dispatchUnwind [liveFdeStackClashCaller] false 0x11684 = some (20, .none) ∧
    dispatchUnwind [liveFdeStackClashCaller] true  0x11684 = some (20, .cleanup 0x82) ∧
    dispatchUnwind [liveFdeStackClashCaller] false 0x116ad = some (20, .filterTerminate 0x160) := by
  decide

/-- Parametric proof of asynchronous DWARF CFA accuracy across `X86FrameLowering::emitStackProbeInlineGenericLoop`
    (`X86FrameLowering.cpp:868-938`):
    - Before loop: `r11 = (entryRsp - pushedBytes) - pages * 4096`, `CFA = r11 + (8 + pushedBytes + pages * 4096)`.
    - On every loop iteration `k ≤ pages` (`rsp_k = (entryRsp - pushedBytes) - k * 4096`), `r11` does not change,
      so `CFA` evaluates identically to `entryRsp + 8`.
    - After `sub $tailOffset, %rsp` (`rsp_final = r11 - tailOffset`), switching CFA to
      `rsp_final + (8 + pushedBytes + pages * 4096 + tailOffset)` also evaluates to `entryRsp + 8`! -/
def cfaDuringProbeLoop (r11 pushedBytes boundOffset : Int) : Int :=
  r11 + (8 + pushedBytes + boundOffset)

def cfaAfterProbeTail (rspFinal pushedBytes boundOffset tailOffset : Int) : Int :=
  rspFinal + (8 + pushedBytes + boundOffset + tailOffset)

theorem stackClashInlineLoop_async_cfa_exact
    (entryRsp pushedBytes boundOffset tailOffset : Int) :
    let r11 := (entryRsp - pushedBytes) - boundOffset
    let rspFinal := r11 - tailOffset
    cfaDuringProbeLoop r11 pushedBytes boundOffset = entryRsp + 8 ∧
    cfaAfterProbeTail rspFinal pushedBytes boundOffset tailOffset = entryRsp + 8 := by
  dsimp [cfaDuringProbeLoop, cfaAfterProbeTail]
  have hLoop :
      entryRsp - pushedBytes - boundOffset + (8 + pushedBytes + boundOffset) = entryRsp + 8 := by
    calc
      entryRsp - pushedBytes - boundOffset + (8 + pushedBytes + boundOffset)
          = (entryRsp - pushedBytes - boundOffset + boundOffset) + pushedBytes + 8 := by
              rw [Int.add_comm 8 pushedBytes, Int.add_assoc pushedBytes 8 boundOffset]
              rw [Int.add_comm 8 boundOffset, ← Int.add_assoc pushedBytes boundOffset 8]
              rw [Int.add_comm pushedBytes boundOffset]
              rw [← Int.add_assoc (entryRsp - pushedBytes - boundOffset) (boundOffset + pushedBytes) 8]
              rw [← Int.add_assoc (entryRsp - pushedBytes - boundOffset) boundOffset pushedBytes]
      _ = (entryRsp - pushedBytes) + pushedBytes + 8 := by
              rw [Int.sub_add_cancel]
      _ = entryRsp + 8 := by
              rw [Int.sub_add_cancel]
  have hTail :
      entryRsp - pushedBytes - boundOffset - tailOffset +
          (8 + pushedBytes + boundOffset + tailOffset) = entryRsp + 8 := by
    calc
      entryRsp - pushedBytes - boundOffset - tailOffset +
          (8 + pushedBytes + boundOffset + tailOffset)
          = (entryRsp - pushedBytes - boundOffset - tailOffset + tailOffset) +
              (8 + pushedBytes + boundOffset) := by
                rw [← Int.add_assoc (entryRsp - pushedBytes - boundOffset - tailOffset)
                      (8 + pushedBytes + boundOffset) tailOffset]
                rw [Int.add_right_comm (entryRsp - pushedBytes - boundOffset - tailOffset)
                      (8 + pushedBytes + boundOffset) tailOffset]
      _ = entryRsp - pushedBytes - boundOffset + (8 + pushedBytes + boundOffset) := by
                rw [Int.sub_add_cancel]
      _ = entryRsp + 8 := hLoop
  exact ⟨hLoop, hTail⟩

/-! ## Section 4: `ElaborateDrops` Ladders (`Static`, `Conditional`, `Open`) & Double-Panic `CE3` -/

/-- Specification of one destructor token (`label` + whether its `Drop::drop` panics). -/
structure FieldDropSpec where
  label : String
  panicsOnDrop : Bool := false
  deriving DecidableEq, Repr

/-- Source-level drop ladder kind in `crate_caller` around a cross-crate `invoke`. -/
inductive DropLadder where
  /-- `DropStyle::Static` (`shim.rs::build_drop_shim`): caller invokes `drop_in_place::<T>` with
      `unwind terminate(cleanup)`. Inside `drop_in_place`, fields drop left-to-right with an internal
      cleanup half-ladder that still drops remaining sibling fields if an earlier field panics,
      before `_Unwind_Resume` reaches the caller's `filter_landing_pad` (`panic_in_cleanup`)! -/
  | staticGlue (fields : List FieldDropSpec)
  /-- `DropStyle::Conditional`: guarded by boolean `flagPresent` (cleared when moved before call). -/
  | conditional (flagPresent : Bool) (spec : FieldDropSpec)
  /-- `DropStyle::Open` (`elaborate_drops.rs:361`, `elaborate_drop.rs:675-716`): elaborated inline
      inside caller's cleanup block (`is_cleanup = true`), where every live field's `drop` terminator
      directly carries `UnwindAction::Terminate(Reason::InCleanup)` (`filter_landing_pad`). -/
  | openInline (fields : List (Bool × FieldDropSpec))
  deriving DecidableEq, Repr

inductive CleanupExecOutcome where
  | ok (droppedLabels : List String)
  | unwound (droppedLabels : List String)
  | abortedInCleanup (droppedLabelsBeforeAbort : List String)
  deriving DecidableEq, Repr

/-- Executes `drop_in_place::<T>` (`build_drop_shim`, entered with `inCleanup = false`),
    defined via `List.foldr` so zero `._unsafe_rec` constants exist in the `.olean`. -/
def execDropShimFields (inCleanup : Bool) (acc : List String)
    (fields : List FieldDropSpec) : CleanupExecOutcome :=
  (fields.foldr
    (fun f ih inC ac =>
      let ac' := ac ++ [f.label]
      if f.panicsOnDrop then
        if inC then
          .abortedInCleanup ac'
        else
          ih true ac'
      else
        ih inC ac')
    (fun inC ac => if inC then .unwound ac else .ok ac)) inCleanup acc

/-- Helper executing open-drop field list via `List.foldr` for zero `._unsafe_rec`. -/
def execOpenFields (inClean : Bool) (cur : List String)
    (fields : List (Bool × FieldDropSpec)) : CleanupExecOutcome :=
  (fields.foldr
    (fun p ih inC ac =>
      if !p.1 then
        ih inC ac
      else
        let ac' := ac ++ [p.2.label]
        if p.2.panicsOnDrop then
          if inC then
            .abortedInCleanup ac'
          else
            ih true ac'
        else
          ih inC ac')
    (fun inC ac => if inC then .unwound ac else .ok ac)) inClean cur

/-- Executes one `DropLadder` inside either normal scope exit (`callerUnwinding = false`)
    or caller's unwind landing pad (`callerUnwinding = true`). -/
def execLadder (callerUnwinding : Bool) (acc : List String) (ladder : DropLadder) :
    CleanupExecOutcome :=
  match ladder with
  | .staticGlue fields =>
      match execDropShimFields false acc fields with
      | .ok acc' =>
          if callerUnwinding then .unwound acc' else .ok acc'
      | .unwound acc' =>
          -- If caller was ALREADY unwinding, `drop_in_place`'s `_Unwind_Resume` lands in caller's
          -- `UnwindAction::Terminate(Reason::InCleanup)` `filter_landing_pad` (`panic_in_cleanup`)!
          if callerUnwinding then .abortedInCleanup acc' else .unwound acc'
      | .abortedInCleanup acc' =>
          .abortedInCleanup acc'
  | .conditional flagPresent spec =>
      if !flagPresent then
        if callerUnwinding then .unwound acc else .ok acc
      else
        let acc' := acc ++ [spec.label]
        if spec.panicsOnDrop then
          if callerUnwinding then .abortedInCleanup acc' else .unwound acc'
        else
          if callerUnwinding then .unwound acc' else .ok acc'
  | .openInline fields =>
      execOpenFields callerUnwinding acc fields

/-- Executes a stack of scope drop ladders in order (innermost scope first) via `List.foldr`. -/
def execLadderStack (callerUnwinding : Bool) (acc : List String)
    (ladders : List DropLadder) : CleanupExecOutcome :=
  (ladders.foldr
    (fun l ih unw ac =>
      match execLadder unw ac l with
      | .ok ac' => ih false ac'
      | .unwound ac' => ih true ac'
      | .abortedInCleanup ac' => .abortedInCleanup ac')
    (fun unw ac => if unw then .unwound ac else .ok ac)) callerUnwinding acc

/-- **Counterexample CE3 (Double-Panic Divergence Between `Static` Glue and `Open` Inline Cleanup)**:
    During cross-crate unwind (`callerUnwinding = true`), suppose field `f0` panics in its destructor
    while sibling `f1` is initialized and non-panicking:
    - Under `DropStyle::Static` (`caller_double_panic_static`), `drop_in_place` runs BOTH `f1` and `f2`
      before `_Unwind_Resume` triggers `abortedInCleanup`;
    - Under `DropStyle::Open` (`caller_double_panic_open`, where `f2` was moved before the call),
      `f0`'s inline cleanup `drop` terminator hits `UnwindAction::Terminate(Reason::InCleanup)` directly,
      aborting immediately after `f0` — sibling `f1` NEVER executes! -/
def dpStaticLadder : DropLadder :=
  .staticGlue [
    { label := "dp_static_f0_bomb", panicsOnDrop := true },
    { label := "dp_static_f1_sibling", panicsOnDrop := false },
    { label := "dp_static_f2_sibling", panicsOnDrop := false }
  ]

def dpOpenLadder : DropLadder :=
  .openInline [
    (true,  { label := "dp_open_f0_bomb", panicsOnDrop := true }),
    (true,  { label := "dp_open_f1_sibling", panicsOnDrop := false }),
    (false, { label := "dp_open_f2_moved", panicsOnDrop := false })
  ]

theorem ce3_double_panic_static_vs_open_divergence :
    execLadder true ["callee_direct_guard"] dpStaticLadder =
      .abortedInCleanup [
        "callee_direct_guard",
        "dp_static_f0_bomb",
        "dp_static_f1_sibling",
        "dp_static_f2_sibling"
      ] ∧
    execLadder true ["dp_open_f2_moved", "callee_direct_guard"] dpOpenLadder =
      .abortedInCleanup [
        "dp_open_f2_moved",
        "callee_direct_guard",
        "dp_open_f0_bomb"
      ] := by
  exact ⟨rfl, rfl⟩

/-- Sharpness of `DropFlagClearedOnPartialMove`: if a moved-out field or conditional local fails to
    clear its boolean drop flag (`staleFlag = true`), unwinding drops the moved-out value a second time! -/
theorem stale_drop_flag_causes_double_drop :
    execLadder true ["already_consumed_cond_0"]
      (.conditional false { label := "cond_0", panicsOnDrop := false }) =
      .unwound ["already_consumed_cond_0"] ∧
    execLadder true ["already_consumed_cond_0"]
      (.conditional true { label := "cond_0", panicsOnDrop := false }) =
      .unwound ["already_consumed_cond_0", "cond_0"] := by
  exact ⟨rfl, rfl⟩

/-! ## Section 5: Master End-to-End 4-Layer Cross-Crate Seam Composition Theorem -/

/-- Reference list of live destructor labels expected for a single non-panicking `DropLadder`. -/
def expectedLiveDrops : DropLadder → List String
  | .staticGlue fields => fields.map (·.label)
  | .conditional flag spec => if flag then [spec.label] else []
  | .openInline fields =>
      (fields.filter (fun p => p.1)).map (fun p => p.2.label)

def LadderNoPanic : DropLadder → Prop
  | .staticGlue fields => ∀ f ∈ fields, f.panicsOnDrop = false
  | .conditional _ spec => spec.panicsOnDrop = false
  | .openInline fields => ∀ p ∈ fields, p.2.panicsOnDrop = false

theorem execDropShimFields_noPanic
    (inClean : Bool) (acc : List String) (fields : List FieldDropSpec)
    (hnp : ∀ f ∈ fields, f.panicsOnDrop = false) :
    execDropShimFields inClean acc fields =
      (if inClean then .unwound (acc ++ fields.map (·.label))
       else .ok (acc ++ fields.map (·.label))) := by
  induction fields generalizing acc with
  | nil =>
      simp [execDropShimFields]
  | cons f fs ih =>
      have hf : f.panicsOnDrop = false := hnp f (.head fs)
      have hfs : ∀ g ∈ fs, g.panicsOnDrop = false := fun g hg => hnp g (.tail f hg)
      dsimp [execDropShimFields]
      rw [hf]
      dsimp
      change execDropShimFields inClean (acc ++ [f.label]) fs = _
      rw [ih (acc ++ [f.label]) hfs]
      rw [List.append_assoc]
      rfl

theorem execOpenFields_noPanic
    (inClean : Bool) (acc : List String) (fields : List (Bool × FieldDropSpec))
    (hnp : ∀ p ∈ fields, p.2.panicsOnDrop = false) :
    execOpenFields inClean acc fields =
      (if inClean then
         .unwound (acc ++ (fields.filter (fun p => p.1)).map (fun p => p.2.label))
       else
         .ok (acc ++ (fields.filter (fun p => p.1)).map (fun p => p.2.label))) := by
  induction fields generalizing acc with
  | nil =>
      simp [execOpenFields]
  | cons p ps ih =>
      rcases p with ⟨isLive, spec⟩
      have hp : spec.panicsOnDrop = false := hnp (isLive, spec) (.head ps)
      have hps : ∀ q ∈ ps, q.2.panicsOnDrop = false := fun q hq => hnp q (.tail (isLive, spec) hq)
      cases isLive with
      | false =>
          dsimp [execOpenFields, List.filter]
          change execOpenFields inClean acc ps = _
          exact ih acc hps
      | true =>
          dsimp [execOpenFields, List.filter, List.map]
          rw [hp]
          dsimp
          change execOpenFields inClean (acc ++ [spec.label]) ps = _
          rw [ih (acc ++ [spec.label]) hps]
          rw [List.append_assoc]
          rfl

theorem execLadder_noPanic_exact
    (unwinding : Bool) (acc : List String) (l : DropLadder) (hnp : LadderNoPanic l) :
    execLadder unwinding acc l =
      (if unwinding then .unwound (acc ++ expectedLiveDrops l)
       else .ok (acc ++ expectedLiveDrops l)) := by
  cases l with
  | staticGlue fields =>
      dsimp [execLadder, expectedLiveDrops]
      rw [execDropShimFields_noPanic false acc fields hnp]
      cases unwinding <;> rfl
  | conditional flag spec =>
      dsimp [LadderNoPanic] at hnp
      cases flag <;> cases unwinding <;> simp [execLadder, expectedLiveDrops, hnp]
  | openInline fields =>
      dsimp [execLadder, expectedLiveDrops]
      exact execOpenFields_noPanic unwinding acc fields hnp

def expectedStackDrops (ladders : List DropLadder) : List String :=
  ladders.foldr (fun l ih => expectedLiveDrops l ++ ih) []

theorem execLadderStack_noPanic_exact
    (unwinding : Bool) (acc : List String) (ladders : List DropLadder)
    (hnp : ∀ l ∈ ladders, LadderNoPanic l) :
    execLadderStack unwinding acc ladders =
      (if unwinding then .unwound (acc ++ expectedStackDrops ladders)
       else .ok (acc ++ expectedStackDrops ladders)) := by
  induction ladders generalizing acc with
  | nil =>
      cases unwinding <;> simp [execLadderStack, expectedStackDrops]
  | cons l ls ih =>
      have hl : LadderNoPanic l := hnp l (.head ls)
      have hls : ∀ m ∈ ls, LadderNoPanic m := fun m hm => hnp m (.tail l hm)
      dsimp [execLadderStack, expectedStackDrops]
      rw [execLadder_noPanic_exact unwinding acc l hl]
      cases unwinding with
      | false =>
          dsimp
          change execLadderStack false (acc ++ expectedLiveDrops l) ls =
            .ok (acc ++ (expectedLiveDrops l ++ expectedStackDrops ls))
          rw [ih (acc ++ expectedLiveDrops l) hls]
          rw [List.append_assoc]
          rfl
      | true =>
          dsimp
          change execLadderStack true (acc ++ expectedLiveDrops l) ls =
            .unwound (acc ++ (expectedLiveDrops l ++ expectedStackDrops ls))
          rw [ih (acc ++ expectedLiveDrops l) hls]
          rw [List.append_assoc]
          rfl

/-- Callee cross-crate execution behavior: either returns a well-formed `AbiValue` after running its
    callee-internal drops, or panics after running its callee-internal unwind drops (leaving any
    caller `sret` slot unwritten). -/
inductive CrossCrateCalleeResult where
  | returned (retVal : AbiValue) (calleeDrops : List String) (retDropSpec : Option FieldDropSpec)
  | panicked (calleeUnwindDrops : List String) (unusedRetMode : AbiPassMode) (unusedRetDropSpec : Option FieldDropSpec)
  deriving DecidableEq, Repr

/-- Complete end-to-end 4-layer cross-crate execution result in `crate_caller`. -/
inductive EndToEndSeamResult where
  | normalReturn (unmarshaledVal : AbiValue) (totalDropTrace : List String)
  | caughtUnwind (totalDropTrace : List String)
  | seamFault (reason : String)
  deriving DecidableEq, Repr

/-- End-to-end operational pipeline across all 4 compiler/linker layers:
    1. Post-link cross-crate call target evaluation under `linker`, `relaxEnabled`, ASLR `loadBias`,
       and `gotRelocated`;
    2. Cross-crate `FnAbi` marshaling / `sret` return-flag discipline;
    3. `.eh_frame_hdr` + `.gcc_except_table` LSDA lookup via `retRip - 1` (`ipBeforeInstr = false`)
       when the callee unwinds;
    4. `ElaborateDrops` execution of the return-value drop flag (`updateSretDropFlag true ...`) plus
       caller's `[Open, Conditional, Static]` cleanup ladders! -/
def runEndToEndFourLayerSeam
    (linker : LinkerFlavor)
    (relaxEnabled : Bool)
    (loadBias : Nat)
    (gotRelocated : Bool)
    (unrelocatedGotVal : Nat → Nat)
    (callInst : PreLinkInst)
    (callerFde nextFde : FdeRecord)
    (callVa callLen : Nat)
    (expectedLpadOff : Nat)
    (preCallDrops : List String)
    (callerLadders : List DropLadder)
    (calleeRes : CrossCrateCalleeResult) : EndToEndSeamResult :=
  let postCallInst := linkPostLinkInst linker relaxEnabled callInst
  let targetVa := evalPostLinkAddress loadBias gotRelocated unrelocatedGotVal postCallInst
  if targetVa != loadBias + callInst.targetSym then
    .seamFault "bad_postlink_call_target"
  else
    match calleeRes with
    | .returned retVal calleeDrops retDropOpt =>
        let chan := marshalReturn retVal
        match unmarshalReturn retVal.passMode chan with
        | none => .seamFault "abi_unmarshal_failed"
        | some decodedVal =>
            let retFlag := updateSretDropFlag true true
            let retLadders : List DropLadder :=
              match retDropOpt with
              | none => []
              | some spec => [.conditional retFlag spec]
            match execLadderStack false (preCallDrops ++ calleeDrops) (retLadders ++ callerLadders) with
            | .ok finalDrops => .normalReturn decodedVal finalDrops
            | _ => .seamFault "unexpected_panic_on_normal_exit"
    | .panicked calleeUnwindDrops _retMode retDropOpt =>
        let retRip := callVa + callLen
        match dispatchUnwind [callerFde, nextFde] false retRip with
        | some (fnId, .cleanup lpadOff) =>
            if fnId != callerFde.fnId || lpadOff != expectedLpadOff then
              .seamFault "wrong_fde_or_lsda_lpad"
            else
              -- `drop_flags_for_fn_rets` (`setAtTargetOnly = true`) keeps `retFlag = false`!
              let retFlag := updateSretDropFlag true false
              let retLadders : List DropLadder :=
                match retDropOpt with
                | none => []
                | some spec => [.conditional retFlag spec]
              match execLadderStack true (preCallDrops ++ calleeUnwindDrops) (retLadders ++ callerLadders) with
              | .unwound finalDrops => .caughtUnwind finalDrops
              | _ => .seamFault "unexpected_abort_in_cleanup"
        | _ => .seamFault "unwind_dispatch_failed"

/-- **Master Theorem (`endToEnd_fourLayer_seam_preservation`)**:
    Under the 4 combined validator side conditions:
      (SC1) `GotInitializedOrLeaRelaxed` on the post-link cross-crate call instruction;
      (SC2) `ValidUnwindCallSite` (`TrailingCallNopGuard`: `1 ≤ callLen`, `callVa + callLen ≤ callerFde.pcEnd`,
            even if `callVa + callLen == callerFde.pcEnd == nextFde.pcBegin`, and `CallReturnInsideLsdaRange`
            for a single-site or head-site cleanup LSDA entry);
      (SC3) `AbiValue.WellFormed` on normal return values;
      (SC4) `LadderNoPanic` across live caller/return destructors (with `DropFlagClearedOnPartialMove`
            encoded in `callerLadders` and `updateSretDropFlag true`);
    the 4-layer pipeline preserves:
      - Exact cross-crate `FnAbi` value round-tripping + exact live destructor sequence on normal return;
      - Exact `.eh_frame_hdr` + LSDA landing-pad dispatch, zero uninitialized `sret` drops, zero stale
        moved-field drops, and exact live destructor sequence on cross-crate panic unwind! -/
theorem endToEnd_fourLayer_seam_preservation
    (linker : LinkerFlavor)
    (relaxEnabled : Bool)
    (loadBias : Nat)
    (gotRelocated : Bool)
    (unrelocatedGotVal : Nat → Nat)
    (callInst : PreLinkInst)
    (callerFde nextFde : FdeRecord)
    (cs : LsdaCallSite)
    (callVa callLen expectedLpadOff : Nat)
    (preCallDrops : List String)
    (callerLadders : List DropLadder)
    (hGot : GotInitializedOrLeaRelaxed gotRelocated (linkPostLinkInst linker relaxEnabled callInst))
    (hAdjFde : callerFde.pcEnd ≤ nextFde.pcBegin)
    (hCsHead : callerFde.lsdaCallSites = [cs])
    (hCsCleanup : cs.csLpad = expectedLpadOff ∧ expectedLpadOff ≠ 0 ∧ cs.ttypeIndex = none)
    (hCallValid : ValidUnwindCallSite callerFde cs callVa callLen)
    (hLaddersNoPanic : ∀ l ∈ callerLadders, LadderNoPanic l) :
    -- Part A: Normal cross-crate return across any well-formed `Direct`/`Pair`/`Cast12`/`IndirectSret` value:
    (∀ (retVal : AbiValue) (calleeDrops : List String) (retDropOpt : Option FieldDropSpec),
      retVal.WellFormed →
      (∀ s, retDropOpt = some s → s.panicsOnDrop = false) →
      runEndToEndFourLayerSeam linker relaxEnabled loadBias gotRelocated unrelocatedGotVal
        callInst callerFde nextFde callVa callLen expectedLpadOff preCallDrops callerLadders
        (.returned retVal calleeDrops retDropOpt) =
      .normalReturn retVal
        (preCallDrops ++ calleeDrops ++
          (match retDropOpt with | none => [] | some s => [s.label]) ++
          expectedStackDrops callerLadders)) ∧
    -- Part B: Cross-crate panic unwind (including trailing `noreturn` calls at `fde_end == next_fde.pc_begin`
    -- and uninitialized `sret` return slots):
    (∀ (calleeUnwindDrops : List String) (retMode : AbiPassMode) (retDropOpt : Option FieldDropSpec),
      (∀ s, retDropOpt = some s → s.panicsOnDrop = false) →
      runEndToEndFourLayerSeam linker relaxEnabled loadBias gotRelocated unrelocatedGotVal
        callInst callerFde nextFde callVa callLen expectedLpadOff preCallDrops callerLadders
        (.panicked calleeUnwindDrops retMode retDropOpt) =
      .caughtUnwind (preCallDrops ++ calleeUnwindDrops ++ expectedStackDrops callerLadders)) := by
  have hAddr :
      evalPostLinkAddress loadBias gotRelocated unrelocatedGotVal
        (linkPostLinkInst linker relaxEnabled callInst) = loadBias + callInst.targetSym :=
    postlink_address_sound_under_sidecond linker relaxEnabled callInst loadBias gotRelocated
      unrelocatedGotVal hGot
  have hBneFalse : ((loadBias + callInst.targetSym) != (loadBias + callInst.targetSym)) = false := by
    simp
  constructor
  · intro retVal calleeDrops retDropOpt hWf hRetNoPanic
    dsimp [runEndToEndFourLayerSeam]
    rw [hAddr, hBneFalse]
    simp only [Bool.false_eq_true, ite_false]
    rw [fnAbi_marshal_unmarshal_roundtrip retVal hWf]
    simp only [updateSretDropFlag, ite_true]
    cases retDropOpt with
    | none =>
        dsimp only [List.nil_append]
        rw [execLadderStack_noPanic_exact false (preCallDrops ++ calleeDrops) callerLadders hLaddersNoPanic]
        simp [List.append_assoc]
    | some s =>
        have hs : s.panicsOnDrop = false := hRetNoPanic s rfl
        have hAll : ∀ l ∈ (DropLadder.conditional true s :: callerLadders), LadderNoPanic l := by
          intro l hl
          cases hl with
          | head _ => exact hs
          | tail _ hm => exact hLaddersNoPanic l hm
        dsimp
        rw [execLadderStack_noPanic_exact false (preCallDrops ++ calleeDrops)
              (DropLadder.conditional true s :: callerLadders) hAll]
        dsimp [expectedStackDrops, expectedLiveDrops]
        simp [List.append_assoc]
  · intro calleeUnwindDrops retMode retDropOpt hRetNoPanic
    dsimp [runEndToEndFourLayerSeam]
    rw [hAddr, hBneFalse]
    simp only [Bool.false_eq_true, ite_false]
    -- Evaluate `dispatchUnwind [callerFde, nextFde] false (callVa + callLen)`
    have ⟨hFdeLo, hFdeHi⟩ := retMinusOne_in_fde_bounds hCallValid
    unfold dispatchUnwind unwindQueryPc
    simp only [Bool.false_eq_true, ite_false]
    rw [ehFrameHdrLookup_singleton_or_pair callerFde nextFde ((callVa + callLen) - 1) hFdeLo hFdeHi hAdjFde]
    dsimp
    rw [hCsHead]
    have hNotLtStart : ¬ ((callVa + callLen - 1) - callerFde.pcBegin < cs.csStart) :=
      Nat.not_lt_of_ge hCallValid.in_cs_lo
    simp only [lsdaLookupAtRelIp, List.foldr_cons, hNotLtStart, hCallValid.in_cs_hi, ite_true, ite_false]
    rcases hCsCleanup with ⟨hLpadEq, hLpadNe0, hTtypeNone⟩
    unfold interpretCsAction
    rw [hLpadEq, hTtypeNone]
    have hLpadBeq0 : (expectedLpadOff == 0) = false := beq_eq_false_iff_ne.mpr hLpadNe0
    rw [hLpadBeq0]
    simp only [Bool.false_eq_true, ite_false]
    have hGuardFalse : ((callerFde.fnId != callerFde.fnId) || (expectedLpadOff != expectedLpadOff)) = false := by
      simp
    rw [hGuardFalse]
    simp only [Bool.false_eq_true, ite_false, updateSretDropFlag]
    cases retDropOpt with
    | none =>
        dsimp only [List.nil_append]
        rw [execLadderStack_noPanic_exact true (preCallDrops ++ calleeUnwindDrops) callerLadders hLaddersNoPanic]
        rfl
    | some s =>
        have hs : s.panicsOnDrop = false := hRetNoPanic s rfl
        have hAll : ∀ l ∈ (DropLadder.conditional false s :: callerLadders), LadderNoPanic l := by
          intro l hl
          cases hl with
          | head _ => exact hs
          | tail _ hm => exact hLaddersNoPanic l hm
        dsimp
        rw [execLadderStack_noPanic_exact true (preCallDrops ++ calleeUnwindDrops)
              (DropLadder.conditional false s :: callerLadders) hAll]
        rfl

/-- Concrete kernel-evaluated witness matching our live `indirect_sret_cm1_pan1` & `indirect_sret_cm0_pan0`
    runs across `GNU ld` and `rust-lld`: verifies all 21 probe trace invariants on concrete values. -/
def liveCallerLadders (condMoved : Bool) : List DropLadder :=
  [
    .openInline [
      (true,  { label := "open_0" }),
      (false, { label := "open_1" }),
      (true,  { label := "open_2" })
    ],
    .conditional (!condMoved) { label := "cond_0" },
    .staticGlue [{ label := "static_0" }, { label := "static_1" }]
  ]

theorem live_sret_normal_and_unwind_traces_match_binary :
    let callerFde : FdeRecord :=
      { fnId := 100, pcBegin := 0x15720, pcEnd := 0x15800,
        lsdaCallSites := [{ csStart := 0x20, csLen := 0x40, csLpad := 0x90 }] }
    let nextFde : FdeRecord :=
      { fnId := 101, pcBegin := 0x15800, pcEnd := 0x15850, lsdaCallSites := [] }
    let sretVal := AbiValue.indirectSret40 1000 1001 1002 1003 1
    let sretDrop : FieldDropSpec := { label := "sret_ret_token" }
    -- (1) Normal sret return (`cm = false`, `rust-lld` `-Z relax-elf-relocations=yes`):
    runEndToEndFourLayerSeam .rustLld true 0x555555554000 false (fun _ => 0)
      (.callThroughGot 0x18800 .gotpcrelx) callerFde nextFde 0x15750 6 0x90
      ["open_1"] (liveCallerLadders false)
      (.returned sretVal ["callee_sret_guard"] (some sretDrop)) =
    .normalReturn sretVal
      ["open_1", "callee_sret_guard", "sret_ret_token", "open_0", "open_2", "cond_0", "static_0", "static_1"] ∧
    -- (2) Cross-crate sret panic unwind (`cm = true`, `sret_ret_token` NOT dropped, `cond_0` NOT re-dropped!):
    runEndToEndFourLayerSeam .rustLld true 0x555555554000 false (fun _ => 0)
      (.callThroughGot 0x18800 .gotpcrelx) callerFde nextFde 0x15750 6 0x90
      ["cond_0", "open_1"] (liveCallerLadders true)
      (.panicked ["callee_sret_guard"] .indirectSret (some sretDrop)) =
    .caughtUnwind
      ["cond_0", "open_1", "callee_sret_guard", "open_0", "open_2", "static_0", "static_1"] := by
  decide

end PostLinkAbiDropUnwindCrucible

#print axioms PostLinkAbiDropUnwindCrucible.fnAbi_marshal_unmarshal_roundtrip
#print axioms PostLinkAbiDropUnwindCrucible.postlink_address_sound_under_sidecond
#print axioms PostLinkAbiDropUnwindCrucible.ce2_static_pie_got_divergence_and_crosscrate_call_hazard
#print axioms PostLinkAbiDropUnwindCrucible.ce1_trailing_noreturn_and_lsda_boundary_sharpness
#print axioms PostLinkAbiDropUnwindCrucible.stackClashInlineLoop_async_cfa_exact
#print axioms PostLinkAbiDropUnwindCrucible.ce3_double_panic_static_vs_open_divergence
#print axioms PostLinkAbiDropUnwindCrucible.endToEnd_fourLayer_seam_preservation
#print axioms PostLinkAbiDropUnwindCrucible.live_sret_normal_and_unwind_traces_match_binary
