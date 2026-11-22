/-!
# Machine-Code Security Hardening & Inline Stack-Probe Soundness

Self-contained, constructive Lean 4 (v4.34.1) formalization of:
1. Downward-growing stack guard-page operational semantics and inline stack-probe
   safety for both LLVM-style monotonic descent (`sub $0x1000, %rsp; movq $0, (%rsp)`)
   and Cranelift-style probe-and-restore (`sub`/`movl`/`add`/`sub`) prologues.
2. Binary-level machine-code hardening predicates covering:
   - Stack Smash Protection (`%fs:0x28` canary prologue/epilogue + `__stack_chk_fail`),
   - Intel CET (`endbr64` entry landing pads + ELF `.note.gnu.property` `IBT`/`SHSTK`
     with `GNU_PROPERTY_X86_FEATURE_1_AND` bitwise-AND linker merging),
   - x86-64 Retpoline (`__llvm_retpoline_r11` / `__x86_indirect_thunk_r11`, rejecting
     bare `call *%reg` / `jmp *%reg`),
   - AddressSanitizer (`__asan_*` instrumentation),
   - AArch64 ARMv8.5-A BTI + PAC (`hint #25` `paciasp` dual PAC+BTI-c landing pad,
     `hint #29` `autiasp`, `hint #27`/`#31` Key-B variants, `hint #34` `bti c`,
     `hint #36` `bti j`, and `br x16`/`x17` tail-call register discipline).
3. Fail-closed post-link binary attestation (`validateBinaryHardening`) catching
   silent backend flag drops (e.g. `rustc_codegen_cranelift` exiting `rc = 0` with
   zero mitigation emitted even while frontend `#154613` diagnostics fire).

Axiom & TCB discipline:
- Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`,
  zero `native_decide`, zero `partial def`, zero `._unsafe_rec`.
-/

namespace MachineHardeningAndStackProbeSoundness

/-! ## Section 1: Elementary Constructive `Nat` Arithmetic Helpers (Zero `omega`) -/

private theorem nat_sub_sub_eq (a b c : Nat) : a - b - c = a - (b + c) :=
  Nat.sub_sub a b c

private theorem nat_mul_succ_eq (k p : Nat) : (k + 1) * p = k * p + p :=
  Nat.succ_mul k p

/-- Division-remainder identity: `(n / p) * p + n % p = n`. -/
private theorem nat_div_mul_add_mod (n p : Nat) : (n / p) * p + n % p = n := by
  have h := Nat.div_add_mod n p
  rw [Nat.mul_comm] at h
  exact h

/-- If `g + p ≤ sp` and `sp - (k * p + r) < g` with `r < p`, then `sp - k * p < g + p`. -/
private theorem probe_crosses_into_guard_or_below
    {sp g p k r : Nat}
    (h_cross : sp - (k * p + r) < g)
    (h_r_lt : r < p) :
    sp - k * p < g + p := by
  have h_eq : sp - k * p - r = sp - (k * p + r) := nat_sub_sub_eq sp (k * p) r
  rw [← h_eq] at h_cross
  cases Nat.lt_or_ge (sp - k * p) r with
  | inl h_lt =>
    have h1 : sp - k * p < p := Nat.lt_trans h_lt h_r_lt
    exact Nat.lt_of_lt_of_le h1 (Nat.le_add_left p g)
  | inr h_ge =>
    have h_add : (sp - k * p - r) + r < g + r := Nat.add_lt_add_right h_cross r
    rw [Nat.sub_add_cancel h_ge] at h_add
    have h_gr : g + r < g + p := Nat.add_lt_add_left h_r_lt g
    exact Nat.lt_trans h_add h_gr

/-! ## Section 2: Downward-Growing Stack Guard-Page Operational Semantics -/

/-- Outcome of executing a stack prologue and initial body touch against a guard page. -/
inductive StackOutcome where
  | running (sp : Nat)
  | trapGuardPage (faultAddr : Nat)
  | corruptedBelowGuard (badAddr : Nat)
  deriving DecidableEq, Repr

/-- Atomic prologue / body stack operations on x86-64 / AArch64. -/
inductive StackOp where
  | subSp (delta : Nat)
  | addSp (delta : Nat)
  | probeAtSp
  | subAndProbe (step : Nat)
  | touchBottom
  deriving DecidableEq, Repr

/-- Classify a memory access at address `addr` relative to guard page `[guardLo, guardLo + pageSize)`. -/
def classifyAccess (guardLo pageSize addr : Nat) : StackOutcome :=
  if addr < guardLo then
    .corruptedBelowGuard addr
  else if addr < guardLo + pageSize then
    .trapGuardPage addr
  else
    .running addr

/-- Execute a single `StackOp` from a live stack pointer `sp`. -/
def stepStackOp (guardLo pageSize sp : Nat) : StackOp → StackOutcome
  | .subSp delta => .running (sp - delta)
  | .addSp delta => .running (sp + delta)
  | .probeAtSp => classifyAccess guardLo pageSize sp
  | .subAndProbe step => classifyAccess guardLo pageSize (sp - step)
  | .touchBottom => classifyAccess guardLo pageSize sp

/-- Total structural execution of a sequence of stack operations; stops immediately on trap or corruption. -/
def execStackOps (guardLo pageSize : Nat) : List StackOp → StackOutcome → StackOutcome
  | [], out => out
  | op :: rest, .running sp =>
    execStackOps guardLo pageSize rest (stepStackOp guardLo pageSize sp op)
  | _ :: _, .trapGuardPage a => .trapGuardPage a
  | _ :: _, .corruptedBelowGuard a => .corruptedBelowGuard a

/-- `k` repetitions of `sub $pageSize, %rsp; mov $0, (%rsp)`. -/
def repeatSubAndProbe (pageSize : Nat) : Nat → List StackOp
  | 0 => []
  | k + 1 => .subAndProbe pageSize :: repeatSubAndProbe pageSize k

/-- LLVM-style inline stack-probe prologue: monotonic descent in `pageSize` steps,
    followed by remainder `subSp (frameSize % pageSize)` and body `touchBottom`. -/
def mkLlvmInlineProbeSeq (frameSize pageSize : Nat) : List StackOp :=
  repeatSubAndProbe pageSize (frameSize / pageSize) ++
    [.subSp (frameSize % pageSize), .touchBottom]

/-- Cranelift-style inline stack-probe prologue (`cranelift/codegen/src/isa/x64/abi.rs`):
    probes down `k = frameSize / pageSize` steps by `pageSize`, restores `%rsp` by
    `add $(k * pageSize), %rsp`, then allocates `sub $frameSize, %rsp` and touches bottom. -/
def mkCraneliftInlineProbeSeq (frameSize pageSize : Nat) : List StackOp :=
  let k := frameSize / pageSize
  repeatSubAndProbe pageSize k ++
    [.addSp (k * pageSize), .subSp frameSize, .touchBottom]

/-- Unprobed stack allocation: directly subtracts `frameSize` then touches bottom. -/
def mkUnprobedSeq (frameSize : Nat) : List StackOp :=
  [.subSp frameSize, .touchBottom]

/-- Addresses probed during `k` downward `pageSize` steps starting from `sp0`. -/
def inlineProbeAddrs (sp0 pageSize : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => (sp0 - pageSize) :: inlineProbeAddrs (sp0 - pageSize) pageSize k

/-- Guard-page coverage predicate: for every guard page `[g, g + pageSize)` straddled
    by the stack frame `[sp0 - frameSize, sp0)`, at least one address in `touched`
    falls inside `[g, g + pageSize)`. -/
def touchesEveryPage (sp0 frameSize pageSize : Nat) (touched : List Nat) : Prop :=
  ∀ guardLo : Nat,
    guardLo + pageSize ≤ sp0 →
    sp0 - frameSize < guardLo →
    ∃ a : Nat, a ∈ touched ∧ guardLo ≤ a ∧ a < guardLo + pageSize

/-! ### Key Structural Lemmas for Inline Stack-Probe Execution -/

private theorem execStackOps_append
    (guardLo pageSize : Nat) (xs ys : List StackOp) (init : StackOutcome) :
    execStackOps guardLo pageSize (xs ++ ys) init =
      execStackOps guardLo pageSize ys (execStackOps guardLo pageSize xs init) := by
  induction xs generalizing init with
  | nil => rfl
  | cons op rest ih =>
    cases init with
    | running sp =>
      change execStackOps guardLo pageSize (rest ++ ys) (stepStackOp guardLo pageSize sp op) =
        execStackOps guardLo pageSize ys
          (execStackOps guardLo pageSize rest (stepStackOp guardLo pageSize sp op))
      exact ih (stepStackOp guardLo pageSize sp op)
    | trapGuardPage a =>
      cases ys <;> rfl
    | corruptedBelowGuard a =>
      cases ys <;> rfl

/-- Core stepping lemma: if `sp ≥ guardLo + pageSize` and `sp - k * pageSize < guardLo + pageSize`,
    then `k` downward `pageSize` probes strictly hit a guard-page address `a ∈ [guardLo, guardLo + pageSize)`
    inside `inlineProbeAddrs sp pageSize k`. -/
theorem repeatSubAndProbe_hits_guard_addr
    (k : Nat) :
    ∀ (sp guardLo pageSize : Nat),
      guardLo + pageSize ≤ sp →
      sp - k * pageSize < guardLo + pageSize →
      ∃ a : Nat,
        a ∈ inlineProbeAddrs sp pageSize k ∧
        guardLo ≤ a ∧ a < guardLo + pageSize := by
  induction k with
  | zero =>
    intro sp guardLo pageSize h_ge h_lt
    simp only [Nat.zero_mul, Nat.sub_zero] at h_lt
    exact False.elim (Nat.not_lt_of_ge h_ge h_lt)
  | succ k ih =>
    intro sp guardLo pageSize h_ge h_lt
    cases Nat.lt_or_ge (sp - pageSize) (guardLo + pageSize) with
    | inl h_in_guard =>
      have h_ge_lo : guardLo ≤ sp - pageSize := by
        have h1 : guardLo + pageSize - pageSize ≤ sp - pageSize :=
          Nat.sub_le_sub_right h_ge pageSize
        rw [Nat.add_sub_cancel] at h1
        exact h1
      exact ⟨sp - pageSize, List.Mem.head _, h_ge_lo, h_in_guard⟩
    | inr h_still_above =>
      have h_next_lt : (sp - pageSize) - k * pageSize < guardLo + pageSize := by
        rw [nat_sub_sub_eq]
        have h_comm : pageSize + k * pageSize = (k + 1) * pageSize := by
          rw [nat_mul_succ_eq, Nat.add_comm]
        rw [h_comm]
        exact h_lt
      match ih (sp - pageSize) guardLo pageSize h_still_above h_next_lt with
      | ⟨a, h_mem, h_lo, h_hi⟩ =>
        exact ⟨a, List.Mem.tail _ h_mem, h_lo, h_hi⟩

/-- Operational version: executing `repeatSubAndProbe pageSize k` from `sp ≥ guardLo + pageSize`
    when `sp - k * pageSize < guardLo + pageSize` terminates in `.trapGuardPage a` for some
    `a ∈ [guardLo, guardLo + pageSize)`. -/
theorem repeatSubAndProbe_traps_on_guard
    (k : Nat) :
    ∀ (sp guardLo pageSize : Nat),
      guardLo + pageSize ≤ sp →
      sp - k * pageSize < guardLo + pageSize →
      ∃ a : Nat,
        execStackOps guardLo pageSize (repeatSubAndProbe pageSize k) (.running sp) =
          .trapGuardPage a ∧
        guardLo ≤ a ∧ a < guardLo + pageSize := by
  induction k with
  | zero =>
    intro sp guardLo pageSize h_ge h_lt
    simp only [Nat.zero_mul, Nat.sub_zero] at h_lt
    exact False.elim (Nat.not_lt_of_ge h_ge h_lt)
  | succ k ih =>
    intro sp guardLo pageSize h_ge h_lt
    have h_ge_lo : guardLo ≤ sp - pageSize := by
      have h1 : guardLo + pageSize - pageSize ≤ sp - pageSize :=
        Nat.sub_le_sub_right h_ge pageSize
      rw [Nat.add_sub_cancel] at h1
      exact h1
    have h_not_below : ¬ (sp - pageSize < guardLo) := Nat.not_lt_of_ge h_ge_lo
    cases Nat.lt_or_ge (sp - pageSize) (guardLo + pageSize) with
    | inl h_in_guard =>
      have h_step : stepStackOp guardLo pageSize sp (.subAndProbe pageSize) =
          .trapGuardPage (sp - pageSize) := by
        simp only [stepStackOp, classifyAccess, h_not_below, h_in_guard, ↓reduceIte]
      refine ⟨sp - pageSize, ?_, h_ge_lo, h_in_guard⟩
      change execStackOps guardLo pageSize (repeatSubAndProbe pageSize k)
        (stepStackOp guardLo pageSize sp (.subAndProbe pageSize)) = _
      rw [h_step]
      cases repeatSubAndProbe pageSize k <;> rfl
    | inr h_still_above =>
      have h_not_in_guard : ¬ (sp - pageSize < guardLo + pageSize) :=
        Nat.not_lt_of_ge h_still_above
      have h_step : stepStackOp guardLo pageSize sp (.subAndProbe pageSize) =
          .running (sp - pageSize) := by
        simp only [stepStackOp, classifyAccess, h_not_below, h_not_in_guard, ↓reduceIte]
      have h_next_lt : (sp - pageSize) - k * pageSize < guardLo + pageSize := by
        rw [nat_sub_sub_eq]
        have h_comm : pageSize + k * pageSize = (k + 1) * pageSize := by
          rw [nat_mul_succ_eq, Nat.add_comm]
        rw [h_comm]
        exact h_lt
      change ∃ a, execStackOps guardLo pageSize (repeatSubAndProbe pageSize k)
        (stepStackOp guardLo pageSize sp (.subAndProbe pageSize)) = .trapGuardPage a ∧ _
      rw [h_step]
      exact ih (sp - pageSize) guardLo pageSize h_still_above h_next_lt

/-- **Theorem 1 (Inline Stack-Probe Guard-Page Catch Theorem):**
    For any `pageSize > 0` and any `frameSize ≥ pageSize` (in fact any `frameSize`),
    the inline stack-probe sequence touches every guard page straddled by the frame,
    and operational execution of the LLVM inline-probe prologue traps deterministically
    on the guard page (`SIGSEGV`) rather than silently jumping past it into adjacent
    memory. -/
theorem probed_frame_never_skips_guard_page
    (sp0 frameSize pageSize : Nat)
    (h_page_pos : 0 < pageSize)
    (_h_frame_ge : pageSize ≤ frameSize) :
    touchesEveryPage sp0 frameSize pageSize
      (inlineProbeAddrs sp0 pageSize (frameSize / pageSize)) ∧
    ∀ guardLo : Nat,
      guardLo + pageSize ≤ sp0 →
      sp0 - frameSize < guardLo →
      ∃ faultAddr : Nat,
        execStackOps guardLo pageSize (mkLlvmInlineProbeSeq frameSize pageSize) (.running sp0) =
          .trapGuardPage faultAddr ∧
        guardLo ≤ faultAddr ∧ faultAddr < guardLo + pageSize := by
  have h_mod_lt : frameSize % pageSize < pageSize := Nat.mod_lt frameSize h_page_pos
  have h_decomp : (frameSize / pageSize) * pageSize + frameSize % pageSize = frameSize :=
    nat_div_mul_add_mod frameSize pageSize
  constructor
  · intro guardLo h_ge h_cross
    rw [← h_decomp] at h_cross
    have h_k_lt : sp0 - (frameSize / pageSize) * pageSize < guardLo + pageSize :=
      probe_crosses_into_guard_or_below h_cross h_mod_lt
    exact repeatSubAndProbe_hits_guard_addr (frameSize / pageSize) sp0 guardLo pageSize h_ge h_k_lt
  · intro guardLo h_ge h_cross
    rw [← h_decomp] at h_cross
    have h_k_lt : sp0 - (frameSize / pageSize) * pageSize < guardLo + pageSize :=
      probe_crosses_into_guard_or_below h_cross h_mod_lt
    match repeatSubAndProbe_traps_on_guard (frameSize / pageSize) sp0 guardLo pageSize h_ge h_k_lt with
    | ⟨a, h_trap, h_lo, h_hi⟩ =>
      refine ⟨a, ?_, h_lo, h_hi⟩
      unfold mkLlvmInlineProbeSeq
      rw [execStackOps_append, h_trap]
      rfl

/-- Companion theorem for Cranelift's probe-then-restore inline sequence
    (`sub $0x1000,%rsp; movl $0,(%rsp); ...; add $(k*0x1000),%rsp; sub $frame,%rsp`):
    probing happens before the full allocation, so it also catches the guard page. -/
theorem cranelift_probed_frame_never_skips_guard_page
    (sp0 frameSize pageSize guardLo : Nat)
    (h_page_pos : 0 < pageSize)
    (h_ge : guardLo + pageSize ≤ sp0)
    (h_cross : sp0 - frameSize < guardLo) :
    ∃ faultAddr : Nat,
      execStackOps guardLo pageSize (mkCraneliftInlineProbeSeq frameSize pageSize) (.running sp0) =
        .trapGuardPage faultAddr ∧
      guardLo ≤ faultAddr ∧ faultAddr < guardLo + pageSize := by
  have h_mod_lt : frameSize % pageSize < pageSize := Nat.mod_lt frameSize h_page_pos
  have h_decomp : (frameSize / pageSize) * pageSize + frameSize % pageSize = frameSize :=
    nat_div_mul_add_mod frameSize pageSize
  rw [← h_decomp] at h_cross
  have h_k_lt : sp0 - (frameSize / pageSize) * pageSize < guardLo + pageSize :=
    probe_crosses_into_guard_or_below h_cross h_mod_lt
  match repeatSubAndProbe_traps_on_guard (frameSize / pageSize) sp0 guardLo pageSize h_ge h_k_lt with
  | ⟨a, h_trap, h_lo, h_hi⟩ =>
    refine ⟨a, ?_, h_lo, h_hi⟩
    unfold mkCraneliftInlineProbeSeq
    rw [execStackOps_append, h_trap]
    rfl

/-! ## Section 3: Machine-Code Hardening Policies, ISA Models, and Post-Link Validator -/

/-- `-Z stack-protector` policy modes in 2026 `rustc` (post-#165812 removal of `basic`). -/
inductive SspLevel where
  | none
  | strong
  | all
  deriving DecidableEq, Repr

/-- `-Z cf-protection` policy modes on x86-64. -/
inductive CetMode where
  | none
  | branch
  | ret
  | full
  deriving DecidableEq, Repr

/-- `-Z retpoline` / `-Z retpoline-external-thunk` policy modes on x86-64. -/
inductive RetpolineMode where
  | none
  | internalThunk
  | externalThunk
  deriving DecidableEq, Repr

/-- AArch64 Pointer Authentication key selection (`-Z branch-protection=pac-ret[,b-key]`). -/
inductive PacKey where
  | keyA
  | keyB
  deriving DecidableEq, Repr

/-- AArch64 `-Z branch-protection` policy configuration. -/
structure BranchProtPolicy where
  bti : Bool
  pacRet : Option (Bool × PacKey) -- `(signLeafFunctions, key)`
  deriving DecidableEq, Repr

/-- Requested compile-time security hardening policy for a binary or object. -/
structure HardeningPolicy where
  ssp : SspLevel
  cet : CetMode
  retpoline : RetpolineMode
  asan : Bool
  branchProt : Option BranchProtPolicy
  deriving DecidableEq, Repr

/-- Relevant x86-64 machine instructions for binary-level hardening attestation. -/
inductive X86Insn where
  | endbr64
  | movFs28CanaryLoad
  | cmpFs28CanaryCheck
  | callStackChkFail
  | callAsan
  | callIndirectRaw
  | jmpIndirectRaw
  | jmpRetpolineR11
  | jmpExternalThunkR11
  | other
  deriving DecidableEq, Repr

/-- Relevant AArch64 machine instructions for PAC + BTI attestation. -/
inductive AArch64Insn where
  | paciasp   -- `hint #25`: signs x30 with IA key + sp, implicit BTI c (under BT0/BT1=0)
  | pacibsp   -- `hint #27`: signs x30 with IB key + sp, implicit BTI c (under BT0/BT1=0)
  | autiasp   -- `hint #29`: authenticates x30 with IA key + sp
  | autibsp   -- `hint #31`: authenticates x30 with IB key + sp
  | btiC      -- `hint #34`: call landing pad (BLR / BR x16 / BR x17)
  | btiJ      -- `hint #36`: jump landing pad (BR xN, n ∉ {16, 17})
  | btiJC     -- `hint #38`: call + jump landing pad
  | brX16     -- tail-call indirect branch via IP0 (`x16`), sets PSTATE.BTYPE = 0b10
  | brX17     -- tail-call indirect branch via IP1 (`x17`), sets PSTATE.BTYPE = 0b10
  | brOther   -- indirect branch via arbitrary `xN` (n ∉ {16, 17}), sets PSTATE.BTYPE = 0b11
  | blr       -- indirect call, sets PSTATE.BTYPE = 0b01
  | ret
  | other
  deriving DecidableEq, Repr

/-- ELF `.note.gnu.property` feature flags (`GNU_PROPERTY_X86_FEATURE_1_AND` /
    `GNU_PROPERTY_AARCH64_FEATURE_1_AND`). -/
structure GnuPropertyNote where
  x86Ibt : Bool
  x86Shstk : Bool
  armBti : Bool
  armPac : Bool
  deriving DecidableEq, Repr

/-- ELF linker bitwise-AND merge rule for `.note.gnu.property` across object files.
    If ANY linked object (such as an unhardened `std` `.rlib`) omits a feature bit,
    the merged executable silently loses that property. -/
def GnuPropertyNote.linkAndMerge (a b : GnuPropertyNote) : GnuPropertyNote where
  x86Ibt := a.x86Ibt && b.x86Ibt
  x86Shstk := a.x86Shstk && b.x86Shstk
  armBti := a.armBti && b.armBti
  armPac := a.armPac && b.armPac

/-- Disassembled function-level image inspected by the post-link binary validator. -/
structure FnImage where
  name : String
  externallyCallable : Bool
  hasStackBufferOrAddrTaken : Bool
  hasIndirectSite : Bool
  spillsLinkReg : Bool
  x86Insns : List X86Insn
  armInsns : List AArch64Insn
  deriving DecidableEq, Repr

/-- Post-link / object-level artifact inspected by the binary validator, paired with
    frontend driver metadata (`exitCode`, `frontendWarnings`) to model silent backend drops. -/
structure BinaryImage where
  exitCode : Nat
  frontendWarnings : List String
  gnuNote : GnuPropertyNote
  functions : List FnImage
  deriving DecidableEq, Repr

/-! ### ARMv8.5-A BTI + PAC Architectural Model -/

/-- ARMv8.5-A `PSTATE.BTYPE` architectural branch-type state set by an indirect branch. -/
inductive BType where
  | b00_direct     -- direct branch / sequential execution (always permitted)
  | b01_blr        -- indirect call `BLR Xn`
  | b10_br_x16_17  -- indirect branch `BR X16` or `BR X17` (call/tail-call compatible)
  | b11_br_other   -- indirect branch `BR Xn` for `n ∉ {16, 17}` (jump-table / non-IP)
  deriving DecidableEq, Repr

/-- `SCTLR_EL1.BT0` / `BT1` control bit governing whether `PACI[AB]SP` accepts `BTYPE = 0b10` (`BR X16/X17`). -/
inductive SctlrBtMode where
  | bt0_default    -- default Linux ABI (`SCTLR_EL1.BT0 = 0`): `PACIASP`/`PACIBSP` act as `BTI c`
  | bt1_strict     -- strict mode (`BT = 1`): `PACIASP`/`PACIBSP` accept `BLR` (0b01) only, not `BR X16/X17`
  deriving DecidableEq, Repr

/-- Architectural BTI landing-pad compatibility check on a guarded memory page (`GP = 1`). -/
def btiAccepts (btMode : SctlrBtMode) (btype : BType) (insn : AArch64Insn) : Bool :=
  match btype with
  | .b00_direct => true
  | .b01_blr =>
    match insn with
    | .btiC | .btiJC | .paciasp | .pacibsp => true
    | _ => false
  | .b10_br_x16_17 =>
    match insn with
    | .btiC | .btiJC => true
    | .paciasp | .pacibsp =>
      match btMode with
      | .bt0_default => true
      | .bt1_strict => false
    | _ => false
  | .b11_br_other =>
    match insn with
    | .btiJ | .btiJC => true
    | _ => false

/-- Architectural PAC return-address signing check for key `k`. -/
def pacSignsLr (k : PacKey) (insn : AArch64Insn) : Bool :=
  match k, insn with
  | .keyA, .paciasp => true
  | .keyB, .pacibsp => true
  | _, _ => false

/-- Architectural PAC return-address authentication check for key `k`. -/
def pacAuthsLr (k : PacKey) (insn : AArch64Insn) : Bool :=
  match k, insn with
  | .keyA, .autiasp => true
  | .keyB, .autibsp => true
  | _, _ => false

/-- **Theorem 3 (AArch64 `paciasp` Dual-Landing-Pad Soundness):**
    Under the standard Linux/ELF ARMv8.5-A `SCTLR_EL1.BT0 = 0` configuration:
    1. `paciasp` (`hint #25`) signs `x30` with Key A,
    2. `paciasp` is a valid BTI-c landing pad for both `BLR` (`b01_blr`) and
       tail-call `BR X16`/`BR X17` (`b10_br_x16_17`), justifying LLVM's omission
       of a redundant `hint #34` (`bti c`),
    3. `paciasp` REJECTS `BR Xn` for `n ∉ {16, 17}` (`b11_br_other`), explaining
       why LLVM must force indirect tail calls into `x16` (`br x16`) and must emit
       explicit `bti j` (`hint #36`) on jump-table targets, and
    4. Under strict `SCTLR_EL1.BT = 1`, `paciasp` no longer accepts `b10_br_x16_17`
       (capturing the exact `AArch64BranchTargets.cpp:175` architectural boundary). -/
theorem paciasp_satisfies_both_pac_and_bti_c :
    pacSignsLr .keyA .paciasp = true ∧
    btiAccepts .bt0_default .b01_blr .paciasp = true ∧
    btiAccepts .bt0_default .b10_br_x16_17 .paciasp = true ∧
    btiAccepts .bt0_default .b11_br_other .paciasp = false ∧
    btiAccepts .bt1_strict .b10_br_x16_17 .paciasp = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### Binary-Level Hardening Predicates & Post-Link Validator -/

/-- Decidable check that `fn` contains a complete x86-64 SSP stack-canary prologue
    (`mov %fs:0x28`) and epilogue check (`cmp`/`xor %fs:0x28` + `call __stack_chk_fail`). -/
def hasCanaryPrologueEpilogue (fn : FnImage) : Bool :=
  fn.x86Insns.contains .movFs28CanaryLoad &&
  fn.x86Insns.contains .cmpFs28CanaryCheck &&
  fn.x86Insns.contains .callStackChkFail

/-- SSP requirement per function under `SspLevel`. -/
def fnSatisfiesSsp (lvl : SspLevel) (fn : FnImage) : Bool :=
  match lvl with
  | .none => true
  | .strong => !fn.hasStackBufferOrAddrTaken || hasCanaryPrologueEpilogue fn
  | .all => hasCanaryPrologueEpilogue fn

/-- Decidable check that a function starts with `endbr64` (when externally callable). -/
def fnStartsWithEndbr64 (fn : FnImage) : Bool :=
  match fn.x86Insns with
  | .endbr64 :: _ => true
  | _ => false

/-- Decidable Intel CET check: entry `endbr64` on all externally callable functions
    plus ELF `.note.gnu.property` `IBT` / `SHSTK` bits matching `cet`. -/
def hasEndbrEntryAndGnuProperty (img : BinaryImage) (cet : CetMode) : Bool :=
  match cet with
  | .none => true
  | .branch =>
    img.gnuNote.x86Ibt &&
    img.functions.all (fun fn => !fn.externallyCallable || fnStartsWithEndbr64 fn)
  | .ret =>
    img.gnuNote.x86Shstk
  | .full =>
    img.gnuNote.x86Ibt &&
    img.gnuNote.x86Shstk &&
    img.functions.all (fun fn => !fn.externallyCallable || fnStartsWithEndbr64 fn)

/-- Decidable Retpoline check: rejects raw `call *%reg` / `jmp *%reg` and requires
    the requested thunk target (`__llvm_retpoline_r11` or `__x86_indirect_thunk_r11`)
    on functions with indirect call/jump sites. -/
def noRawIndirectBranch (fn : FnImage) (mode : RetpolineMode) : Bool :=
  match mode with
  | .none => true
  | .internalThunk =>
    !fn.x86Insns.contains .callIndirectRaw &&
    !fn.x86Insns.contains .jmpIndirectRaw &&
    (!fn.hasIndirectSite || fn.x86Insns.contains .jmpRetpolineR11)
  | .externalThunk =>
    !fn.x86Insns.contains .callIndirectRaw &&
    !fn.x86Insns.contains .jmpIndirectRaw &&
    (!fn.hasIndirectSite || fn.x86Insns.contains .jmpExternalThunkR11)

/-- Decidable AddressSanitizer instrumentation check on stack-buffer functions. -/
def fnSatisfiesAsan (asan : Bool) (fn : FnImage) : Bool :=
  if asan then
    !fn.hasStackBufferOrAddrTaken || fn.x86Insns.contains .callAsan
  else
    true

/-- Decidable AArch64 PAC + BTI check on a function image and ELF `.note.gnu.property`. -/
def hasPacBtiEntry (fn : FnImage) (bp : BranchProtPolicy) (note : GnuPropertyNote) : Bool :=
  let btiOk :=
    if bp.bti then
      note.armBti &&
      !fn.armInsns.contains .brOther &&
      (!fn.externallyCallable ||
        match fn.armInsns with
        | first :: _ =>
          btiAccepts .bt0_default .b01_blr first &&
          btiAccepts .bt0_default .b10_br_x16_17 first
        | [] => false)
    else
      true
  let pacOk :=
    match bp.pacRet with
    | none => true
    | some (leaf, key) =>
      note.armPac &&
      let mustSign := leaf || fn.spillsLinkReg
      if mustSign then
        (match fn.armInsns with
         | first :: _ => pacSignsLr key first
         | [] => false) &&
        fn.armInsns.any (pacAuthsLr key)
      else
        true
  btiOk && pacOk

/-- Complete fail-closed post-link binary hardening validator (`MiniMach` attestation gate). -/
def validateBinaryHardening (pol : HardeningPolicy) (img : BinaryImage) : Bool :=
  hasEndbrEntryAndGnuProperty img pol.cet &&
  img.functions.all (fun fn =>
    fnSatisfiesSsp pol.ssp fn &&
    noRawIndirectBranch fn pol.retpoline &&
    fnSatisfiesAsan pol.asan fn &&
    match pol.branchProt with
    | none => true
    | some bp => hasPacBtiEntry fn bp img.gnuNote)

/-- Frontend acceptance predicate: `rustc` driver returned exit code `0` (regardless of
    whether warnings such as `#154613` were emitted on stderr). -/
def frontendAccepted (img : BinaryImage) : Bool :=
  img.exitCode == 0

/-- Predicate capturing an unhardened backend artifact (zero ASan, zero SSP canaries,
    zero CET `endbr64` / `.note.gnu.property`, zero Retpoline thunks, zero PAC/BTI). -/
def IsUnhardenedImage (img : BinaryImage) : Prop :=
  img.gnuNote = { x86Ibt := false, x86Shstk := false, armBti := false, armPac := false } ∧
  ∀ fn, fn ∈ img.functions →
    ¬ fn.x86Insns.contains .movFs28CanaryLoad = true ∧
    ¬ fn.x86Insns.contains .callAsan = true ∧
    ¬ fn.x86Insns.contains .jmpRetpolineR11 = true ∧
    ¬ fn.x86Insns.contains .jmpExternalThunkR11 = true ∧
    (fn.hasIndirectSite = true →
      fn.x86Insns.contains .callIndirectRaw = true ∨ fn.x86Insns.contains .jmpIndirectRaw = true) ∧
    (match fn.armInsns with
     | [] => True
     | first :: _ =>
       btiAccepts .bt0_default .b01_blr first = false ∧
       pacSignsLr .keyA first = false ∧
       pacSignsLr .keyB first = false)

/-- Predicate capturing that at least one requested mitigation in `pol` applies
    non-trivially to `img`. -/
def PolicyHasActiveObligation (pol : HardeningPolicy) (img : BinaryImage) : Prop :=
  (pol.cet ≠ .none) ∨
  (∃ fn, fn ∈ img.functions ∧ pol.ssp = .all) ∨
  (∃ fn, fn ∈ img.functions ∧ pol.ssp = .strong ∧ fn.hasStackBufferOrAddrTaken = true) ∨
  (∃ fn, fn ∈ img.functions ∧ pol.asan = true ∧ fn.hasStackBufferOrAddrTaken = true) ∨
  (∃ fn, fn ∈ img.functions ∧ pol.retpoline ≠ .none ∧ fn.hasIndirectSite = true) ∨
  (∃ fn bp, fn ∈ img.functions ∧ pol.branchProt = some bp ∧ (bp.bti = true ∨ bp.pacRet.isSome = true))

private theorem list_all_false_of_mem {α : Type} {p : α → Bool} {xs : List α} {x : α}
    (h_mem : x ∈ xs) (h_false : p x = false) :
    xs.all p = false := by
  induction xs with
  | nil => cases h_mem
  | cons y ys ih =>
    simp only [List.all_cons]
    cases h_mem with
    | head =>
      rw [h_false]
      rfl
    | tail _ h_tail =>
      rw [ih h_tail, Bool.and_false]

/-- **Theorem 2 (Post-Link Hardening Validator Completeness against Silent Backend Drops):**
    Whenever a user requests ANY active security hardening obligation in `pol` and a
    backend (such as `rustc_codegen_cranelift`) silently drops the mitigation flag
    (producing an unhardened image `img`, even with `exitCode = 0`), the fail-closed
    post-link binary validator `validateBinaryHardening pol img` is GUARANTEED to
    reject (`= false`). -/
theorem validator_catches_silent_backend_mitigation_drop
    (pol : HardeningPolicy) (img : BinaryImage)
    (h_unhardened : IsUnhardenedImage img)
    (h_active : PolicyHasActiveObligation pol img) :
    validateBinaryHardening pol img = false := by
  rcases h_unhardened with ⟨h_note, h_fns⟩
  unfold validateBinaryHardening
  rcases h_active with
    h_cet |
    ⟨fn, h_mem, h_ssp_all⟩ |
    ⟨fn, h_mem, h_ssp_strong, h_buf⟩ |
    ⟨fn, h_mem, h_asan, h_buf⟩ |
    ⟨fn, h_mem, h_retp, h_ind⟩ |
    ⟨fn, bp, h_mem, h_bp, h_bp_on⟩
  · -- Case 1: Intel CET requested (`branch`, `ret`, or `full`), note lacks IBT & SHSTK
    have h_cet_false : hasEndbrEntryAndGnuProperty img pol.cet = false := by
      cases h_c : pol.cet with
      | none => exact False.elim (h_cet h_c)
      | branch =>
        unfold hasEndbrEntryAndGnuProperty
        rw [h_note]
        rfl
      | ret =>
        unfold hasEndbrEntryAndGnuProperty
        rw [h_note]
      | full =>
        unfold hasEndbrEntryAndGnuProperty
        rw [h_note]
        rfl
    rw [h_cet_false]
    rfl
  · -- Case 2: `-Z stack-protector=all` dropped on `fn`
    have h_no_fs28 : fn.x86Insns.contains .movFs28CanaryLoad = false := by
      cases h_eq : fn.x86Insns.contains .movFs28CanaryLoad with
      | false => rfl
      | true => exact False.elim ((h_fns fn h_mem).1 h_eq)
    have h_fn_false :
        (fnSatisfiesSsp pol.ssp fn && noRawIndirectBranch fn pol.retpoline &&
         fnSatisfiesAsan pol.asan fn &&
         match pol.branchProt with | none => true | some bp => hasPacBtiEntry fn bp img.gnuNote) = false := by
      rw [h_ssp_all]
      unfold fnSatisfiesSsp hasCanaryPrologueEpilogue
      rw [h_no_fs28]
      rfl
    rw [list_all_false_of_mem h_mem h_fn_false, Bool.and_false]
  · -- Case 3: `-Z stack-protector=strong` dropped on stack-buffer `fn`
    have h_no_fs28 : fn.x86Insns.contains .movFs28CanaryLoad = false := by
      cases h_eq : fn.x86Insns.contains .movFs28CanaryLoad with
      | false => rfl
      | true => exact False.elim ((h_fns fn h_mem).1 h_eq)
    have h_fn_false :
        (fnSatisfiesSsp pol.ssp fn && noRawIndirectBranch fn pol.retpoline &&
         fnSatisfiesAsan pol.asan fn &&
         match pol.branchProt with | none => true | some bp => hasPacBtiEntry fn bp img.gnuNote) = false := by
      rw [h_ssp_strong]
      unfold fnSatisfiesSsp hasCanaryPrologueEpilogue
      rw [h_buf, h_no_fs28]
      rfl
    rw [list_all_false_of_mem h_mem h_fn_false, Bool.and_false]
  · -- Case 4: `-Z sanitizer=address` dropped on stack-buffer `fn`
    have h_no_asan : fn.x86Insns.contains .callAsan = false := by
      cases h_eq : fn.x86Insns.contains .callAsan with
      | false => rfl
      | true => exact False.elim ((h_fns fn h_mem).2.1 h_eq)
    have h_fn_false :
        (fnSatisfiesSsp pol.ssp fn && noRawIndirectBranch fn pol.retpoline &&
         fnSatisfiesAsan pol.asan fn &&
         match pol.branchProt with | none => true | some bp => hasPacBtiEntry fn bp img.gnuNote) = false := by
      rw [h_asan]
      simp only [fnSatisfiesAsan, ↓reduceIte, h_buf, h_no_asan, Bool.not_true, Bool.false_or,
        Bool.and_false, Bool.false_and]
    rw [list_all_false_of_mem h_mem h_fn_false, Bool.and_false]
  · -- Case 5: `-Z retpoline` / `-Z retpoline-external-thunk` dropped on indirect-call `fn`
    have h_no_int : fn.x86Insns.contains .jmpRetpolineR11 = false := by
      cases h_eq : fn.x86Insns.contains .jmpRetpolineR11 with
      | false => rfl
      | true => exact False.elim ((h_fns fn h_mem).2.2.1 h_eq)
    have h_no_ext : fn.x86Insns.contains .jmpExternalThunkR11 = false := by
      cases h_eq : fn.x86Insns.contains .jmpExternalThunkR11 with
      | false => rfl
      | true => exact False.elim ((h_fns fn h_mem).2.2.2.1 h_eq)
    have h_ret_false : noRawIndirectBranch fn pol.retpoline = false := by
      cases h_r : pol.retpoline with
      | none => exact False.elim (h_retp h_r)
      | internalThunk =>
        unfold noRawIndirectBranch
        rw [h_ind, h_no_int]
        simp only [Bool.not_true, Bool.false_or, Bool.and_false]
      | externalThunk =>
        unfold noRawIndirectBranch
        rw [h_ind, h_no_ext]
        simp only [Bool.not_true, Bool.false_or, Bool.and_false]
    have h_fn_false :
        (fnSatisfiesSsp pol.ssp fn && noRawIndirectBranch fn pol.retpoline &&
         fnSatisfiesAsan pol.asan fn &&
         match pol.branchProt with | none => true | some bp => hasPacBtiEntry fn bp img.gnuNote) = false := by
      rw [h_ret_false]
      simp only [Bool.and_false, Bool.false_and]
    rw [list_all_false_of_mem h_mem h_fn_false, Bool.and_false]
  · -- Case 6: AArch64 `-Z branch-protection` dropped (ELF note lacks armBti / armPac)
    have h_bp_false : hasPacBtiEntry fn bp img.gnuNote = false := by
      unfold hasPacBtiEntry
      rw [h_note]
      rcases h_bp_on with h_bti | h_pac
      · rw [h_bti]
        rfl
      · cases h_pr : bp.pacRet with
        | none =>
          rw [h_pr] at h_pac
          cases h_pac
        | some pk =>
          cases pk with
          | mk leaf key =>
            simp only [Bool.false_and, Bool.and_false]
    have h_fn_false :
        (fnSatisfiesSsp pol.ssp fn && noRawIndirectBranch fn pol.retpoline &&
         fnSatisfiesAsan pol.asan fn &&
         match pol.branchProt with | none => true | some bp => hasPacBtiEntry fn bp img.gnuNote) = false := by
      rw [h_bp]
      dsimp only
      rw [h_bp_false, Bool.and_false]
    rw [list_all_false_of_mem h_mem h_fn_false, Bool.and_false]

/-- Bonus Structural Theorem: ELF `.note.gnu.property` bitwise-AND link merge
    silently strips CET (`IBT`/`SHSTK`) from a linked executable whenever any single
    dependency (such as stock unhardened `std`) lacks CET properties, and the post-link
    validator catches the degradation even though the local object had full CET. -/
theorem cet_link_and_merge_drops_if_any_dep_unhardened
    (localNote depNote : GnuPropertyNote)
    (h_dep_no_ibt : depNote.x86Ibt = false)
    (h_dep_no_shstk : depNote.x86Shstk = false)
    (fns : List FnImage) :
    let linkedImg : BinaryImage := {
      exitCode := 0,
      frontendWarnings := [],
      gnuNote := GnuPropertyNote.linkAndMerge localNote depNote,
      functions := fns
    }
    hasEndbrEntryAndGnuProperty linkedImg .full = false := by
  dsimp only [hasEndbrEntryAndGnuProperty, GnuPropertyNote.linkAndMerge]
  rw [h_dep_no_ibt, h_dep_no_shstk, Bool.and_false]
  rfl

/-! ## Section 4: Three Constructive Counterexamples -/

/-- **Counterexample 1 (`ce1_unprobed_8kb_frame_skips_4kb_guard_page`):**
    With a standard 4,096-byte guard page at `[4096, 8192)` and initial `%rsp = 8192`,
    an unprobed 8,192-byte stack frame directly executes `sub $8192, %rsp` and touches
    `%rsp = 0`, silently jumping completely across the guard page into adjacent memory
    (`.corruptedBelowGuard 0`), whereas the LLVM inline-probe prologue deterministically
    traps on the guard page (`.trapGuardPage 4096`). -/
theorem ce1_unprobed_8kb_frame_skips_4kb_guard_page :
    execStackOps 4096 4096 (mkUnprobedSeq 8192) (.running 8192) = .corruptedBelowGuard 0 ∧
    execStackOps 4096 4096 (mkLlvmInlineProbeSeq 8192 4096) (.running 8192) = .trapGuardPage 4096 ∧
    execStackOps 4096 4096 (mkCraneliftInlineProbeSeq 8192 4096) (.running 8192) = .trapGuardPage 4096 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Concrete Cranelift output witness modeling observed `rustc_codegen_cranelift` codegen:
    compiles cleanly (`exitCode = 0`), even emits frontend `#154613` partial-mitigation
    diagnostics for `std`, yet emits zero `%fs:0x28`, zero `endbr64` / `.note.gnu.property`,
    zero `__asan_`, and bare `call *%rsi` (`callIndirectRaw`). -/
def craneliftSilentDropImage : BinaryImage := {
  exitCode := 0,
  frontendWarnings := [
    "warning: your program uses the crate `std`, that is not compiled with `stack-protector=all` enabled (#154613)"
  ],
  gnuNote := { x86Ibt := false, x86Shstk := false, armBti := false, armPac := false },
  functions := [
    {
      name := "stack_buf",
      externallyCallable := true,
      hasStackBufferOrAddrTaken := true,
      hasIndirectSite := false,
      spillsLinkReg := false,
      x86Insns := [.other],
      armInsns := []
    },
    {
      name := "indirect_call",
      externallyCallable := true,
      hasStackBufferOrAddrTaken := false,
      hasIndirectSite := true,
      spillsLinkReg := false,
      x86Insns := [.other, .callIndirectRaw],
      armInsns := []
    }
  ]
}

/-- Four individual single-flag policies corresponding to the four silent fail-open gaps
    observed in `rustc_codegen_cranelift` (`asan`, `ssp=all`, `cet=full`, `retpoline`). -/
def polAsanOnly : HardeningPolicy :=
  { ssp := .none, cet := .none, retpoline := .none, asan := true, branchProt := none }

def polSspAllOnly : HardeningPolicy :=
  { ssp := .all, cet := .none, retpoline := .none, asan := false, branchProt := none }

def polCetFullOnly : HardeningPolicy :=
  { ssp := .none, cet := .full, retpoline := .none, asan := false, branchProt := none }

def polRetpolineOnly : HardeningPolicy :=
  { ssp := .none, cet := .none, retpoline := .internalThunk, asan := false, branchProt := none }

def polAllFourFlags : HardeningPolicy :=
  { ssp := .all, cet := .full, retpoline := .internalThunk, asan := true, branchProt := none }

/-- **Counterexample 2 (`ce2_cranelift_silent_drop_of_ssp_cet_retpoline_passes_frontend_fails_binary_validator`):**
    The `rustc_codegen_cranelift` artifact passes frontend compilation (`exitCode = 0`)
    and even carries frontend `#154613` SSP warnings, yet fails the post-link binary
    validator across ALL four flags individually (`asan`, `ssp=all`, `cet=full`, `retpoline`)
    and jointly (`polAllFourFlags`). -/
theorem ce2_cranelift_silent_drop_of_ssp_cet_retpoline_passes_frontend_fails_binary_validator :
    frontendAccepted craneliftSilentDropImage = true ∧
    craneliftSilentDropImage.frontendWarnings.length = 1 ∧
    validateBinaryHardening polAsanOnly craneliftSilentDropImage = false ∧
    validateBinaryHardening polSspAllOnly craneliftSilentDropImage = false ∧
    validateBinaryHardening polCetFullOnly craneliftSilentDropImage = false ∧
    validateBinaryHardening polRetpolineOnly craneliftSilentDropImage = false ∧
    validateBinaryHardening polAllFourFlags craneliftSilentDropImage = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Concrete bare indirect-call function (Cranelift `call *%rsi`) vs LLVM `__llvm_retpoline_r11`. -/
def rawIndirectCallFn : FnImage := {
  name := "indirect_call",
  externallyCallable := true,
  hasStackBufferOrAddrTaken := false,
  hasIndirectSite := true,
  spillsLinkReg := false,
  x86Insns := [.other, .callIndirectRaw],
  armInsns := []
}

def llvmRetpolineFn : FnImage := {
  name := "indirect_call",
  externallyCallable := true,
  hasStackBufferOrAddrTaken := false,
  hasIndirectSite := true,
  spillsLinkReg := false,
  x86Insns := [.other, .jmpRetpolineR11],
  armInsns := []
}

def rawIndirectImg : BinaryImage := {
  exitCode := 0,
  frontendWarnings := [],
  gnuNote := { x86Ibt := false, x86Shstk := false, armBti := false, armPac := false },
  functions := [rawIndirectCallFn]
}

def llvmRetpolineImg : BinaryImage := {
  exitCode := 0,
  frontendWarnings := [],
  gnuNote := { x86Ibt := false, x86Shstk := false, armBti := false, armPac := false },
  functions := [llvmRetpolineFn]
}

/-- **Counterexample 3 (`ce3_raw_indirect_call_violates_retpoline_policy`):**
    A raw indirect call (`call *%rsi`) violates the `-Z retpoline` binary policy under
    both internal-thunk and external-thunk modes, whereas LLVM's `jmp __llvm_retpoline_r11`
    lowering satisfies `validateBinaryHardening polRetpolineOnly`. -/
theorem ce3_raw_indirect_call_violates_retpoline_policy :
    noRawIndirectBranch rawIndirectCallFn .internalThunk = false ∧
    noRawIndirectBranch rawIndirectCallFn .externalThunk = false ∧
    validateBinaryHardening polRetpolineOnly rawIndirectImg = false ∧
    validateBinaryHardening polRetpolineOnly llvmRetpolineImg = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Section 5: Positive Soundness & Non-Vacuity Witnesses -/

private theorem list_all_true_of_mem {α : Type} {p : α → Bool} {xs : List α} {x : α}
    (h_all : xs.all p = true) (h_mem : x ∈ xs) :
    p x = true := by
  induction xs with
  | nil => cases h_mem
  | cons y ys ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h_all
    cases h_mem with
    | head => exact h_all.1
    | tail _ h_tail => exact ih h_all.2 h_tail

/-- Positive soundness of `validateBinaryHardening`: acceptance guarantees every
    requested CET, SSP, Retpoline, ASan, and AArch64 PAC+BTI invariant across all
    functions in the image. -/
theorem validateBinaryHardening_sound
    (pol : HardeningPolicy) (img : BinaryImage)
    (h_ok : validateBinaryHardening pol img = true) :
    hasEndbrEntryAndGnuProperty img pol.cet = true ∧
    ∀ fn, fn ∈ img.functions →
      fnSatisfiesSsp pol.ssp fn = true ∧
      noRawIndirectBranch fn pol.retpoline = true ∧
      fnSatisfiesAsan pol.asan fn = true ∧
      (∀ bp, pol.branchProt = some bp → hasPacBtiEntry fn bp img.gnuNote = true) := by
  unfold validateBinaryHardening at h_ok
  rw [Bool.and_eq_true] at h_ok
  refine ⟨h_ok.1, ?_⟩
  intro fn h_mem
  have h_fn := list_all_true_of_mem h_ok.2 h_mem
  simp only [Bool.and_eq_true] at h_fn
  refine ⟨h_fn.1.1.1, h_fn.1.1.2, h_fn.1.2, ?_⟩
  intro bp h_bp
  have h_bp_ok := h_fn.2
  rw [h_bp] at h_bp_ok
  exact h_bp_ok

/-- Non-vacuity witness: a fully hardened x86-64 LLVM image (CET full + SSP all +
    Retpoline + ASan) and an AArch64 `bti,pac-ret,leaf` LLVM image (`hint #25`,
    `hint #29`, `br x16`, `.note.gnu.property` `BTI, PAC`) both satisfy
    `validateBinaryHardening`. -/
def llvmFullHardenedX86Image : BinaryImage := {
  exitCode := 0,
  frontendWarnings := [],
  gnuNote := { x86Ibt := true, x86Shstk := true, armBti := false, armPac := false },
  functions := [
    {
      name := "stack_buf",
      externallyCallable := true,
      hasStackBufferOrAddrTaken := true,
      hasIndirectSite := false,
      spillsLinkReg := false,
      x86Insns := [.endbr64, .movFs28CanaryLoad, .callAsan, .cmpFs28CanaryCheck, .callStackChkFail],
      armInsns := []
    },
    {
      name := "indirect_call",
      externallyCallable := true,
      hasStackBufferOrAddrTaken := false,
      hasIndirectSite := true,
      spillsLinkReg := false,
      x86Insns := [.endbr64, .movFs28CanaryLoad, .cmpFs28CanaryCheck, .callStackChkFail, .jmpRetpolineR11],
      armInsns := []
    }
  ]
}

def llvmPacBtiLeafAArch64Policy : HardeningPolicy := {
  ssp := .none,
  cet := .none,
  retpoline := .none,
  asan := false,
  branchProt := some { bti := true, pacRet := some (true, .keyA) }
}

def llvmPacBtiLeafAArch64Image : BinaryImage := {
  exitCode := 0,
  frontendWarnings := [],
  gnuNote := { x86Ibt := false, x86Shstk := false, armBti := true, armPac := true },
  functions := [
    {
      name := "arm_leaf",
      externallyCallable := true,
      hasStackBufferOrAddrTaken := false,
      hasIndirectSite := false,
      spillsLinkReg := false,
      x86Insns := [],
      armInsns := [.paciasp, .autiasp, .ret]
    },
    {
      name := "arm_tailcall",
      externallyCallable := true,
      hasStackBufferOrAddrTaken := false,
      hasIndirectSite := true,
      spillsLinkReg := false,
      x86Insns := [],
      armInsns := [.paciasp, .other, .autiasp, .brX16]
    }
  ]
}

theorem llvm_full_hardened_passes_validator :
    validateBinaryHardening polAllFourFlags llvmFullHardenedX86Image = true ∧
    validateBinaryHardening llvmPacBtiLeafAArch64Policy llvmPacBtiLeafAArch64Image = true := by
  exact ⟨rfl, rfl⟩

end MachineHardeningAndStackProbeSoundness
