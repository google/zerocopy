/-
  FoundationalSfiKernels.lean
  =============================================================================
  Mechanized Lean 4.34.1 Model & Counterexample Hierarchy
  for Foundational Software Fault Isolation (SFI) and Extensible Kernel
  Architectures (1993–2011).

  Primary Sources Modeled:
  - [Wahbe93] Wahbe, Lucco, Anderson & Graham, "Efficient Software-Based Fault
    Isolation", SOSP 1993 (DOI: 10.1145/168619.168635).
  - [PittSFIeld06] McCamant & Morrisett, "Evaluating SFI for a CISC
    Architecture", USENIX Security 2006 (and MIT-CSAIL-TR-2005-067 / ACL2 model
    `sfi.lisp`).
  - [Exokernel95] Engler, Kaashoek & O'Toole, "Exokernel: An Operating System
    Architecture for Application-Level Resource Management", SOSP 1995.
  - [ASH96] Wallach, Engler & Kaashoek, "ASHs: Application-Specific Handlers
    for High-Performance Messaging", SIGCOMM 1996 (and XOK `sys/kern/scode.c`).
  - [DPF96] Engler & Kaashoek, "DPF: Fast, Flexible Message Demultiplexing
    using Dynamic Code Generation", SIGCOMM 1996.
  - [XOK97] Kaashoek et al., "Application Performance and Flexibility on
    Exokernel Systems", SOSP 1997 (and XOK `sys/ubb/{udf.c,interp.c,check.c,xn.c}`).
  - [VINO96] Seltzer, Endo, Small & Smith, "Dealing With Disaster: Surviving
    Misbehaving Kernel Extensions", OSDI 1996.
  - [MiSFIT97] Small, "MiSFIT: A Tool for Constructing Safe Extensible C++
    Systems", USENIX COOTS 1997.
  - [Nooks03] Swift, Bershad & Levy, "Improving the Reliability of Commodity
    Operating Systems", SOSP 2003.
  - [XFI06] Erlingsson, Abadi, Vrable, Budiu & Necula, "XFI: Software Guards
    for System Address Spaces", OSDI 2006.
  - [BGI09] Castro et al., "Fast Byte-Granularity Software Fault Isolation",
    SOSP 2009.
  - [LXFI11] Mao et al., "Software Fault Isolation with API Integrity and
    Multi-Principal Modules", SOSP 2011.

  Axiom Discipline:
  - 0 `sorryAx`
  - 0 `Classical.choice`
  - 0 `Lean.ofReduceBool`
-/

namespace FoundationalSfiKernels

/--
  Constructive reflexivity for `Nat` boolean equality `(n == n) = true`.
  Notice that `@beq_self_eq_true Nat` in Lean 4 core pulls in `Classical.choice`
  via the `ReflBEq Nat` instance, whereas `Nat.beq_refl` is purely constructive.
-/
theorem nat_beq_self (n : Nat) : (n == n) = true :=
  beq_iff_eq.mpr rfl

/-!
===============================================================================
LAYER 1: Wahbe Segment Matching vs Address Sandboxing, Guard Zones,
         PittSFIeld CISC Chunk Alignment, and Dedicated-Register Invariants
===============================================================================
-/
namespace Layer1_WahbePittSFIeld

/--
  Wahbe et al. (SOSP 1993, §3.2, Figure 2): Bitwise address sandboxing.
  Given a power-of-two segment of size `2^k` starting at segment-aligned `base`
  (`(base &&& mask) = 0` where `mask = 2^k - 1`), the two-instruction sequence:
    1. `dedicated_reg <- target_reg & and_mask_reg`
    2. `dedicated_reg <- dedicated_reg | segment_reg`
  computes `(addr &&& mask) ||| base`.
-/
def sandboxAddr (base mask addr : Nat) : Nat :=
  (addr &&& mask) ||| base

/--
  Wahbe et al. (SOSP 1993, §3.1, Figure 1): Segment matching check.
  Shifts `addr` right by `shiftReg` (`k`) and compares the upper segment tag
  against `segmentReg` (`segId`). Traps if they differ; pinpoint diagnostics
  identify the exact offending instruction, at the cost of 4 instructions vs 2.
-/
def segmentMatch (shiftReg segId addr : Nat) : Bool :=
  (addr >>> shiftReg) == segId

/--
  Constructive recursive definition of the `k`-bit all-ones mask `2^k - 1`.
  We use this to prove `x &&& (2^k - 1) = x % 2^k` constructively without
  relying on Lean stdlib's `Nat.and_two_pow_sub_one_eq_mod` (which pulls in
  `Classical.choice` via `Nat.testBit_two_pow_sub_one`).
-/
def onesMask : Nat → Nat
  | 0 => 0
  | k + 1 => 2 * onesMask k + 1

theorem two_mul_add_one_mod_two (n : Nat) : (2 * n + 1) % 2 = 1 := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_left]

theorem two_mul_add_one_div_two (n : Nat) : (2 * n + 1) / 2 = n := by
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by decide)]
  exact Nat.zero_add n

theorem testBit_onesMask : ∀ (k i : Nat), (onesMask k).testBit i = decide (i < k)
  | 0, i => by
    simp [onesMask, Nat.zero_testBit]
  | k + 1, 0 => by
    simp [onesMask, Nat.testBit_zero, two_mul_add_one_mod_two, Nat.zero_lt_succ]
  | k + 1, i + 1 => by
    rw [onesMask, Nat.testBit_succ, two_mul_add_one_div_two, testBit_onesMask k i]
    simp [Nat.succ_lt_succ_iff]

theorem onesMask_add_one : ∀ (k : Nat), onesMask k + 1 = 2 ^ k
  | 0 => rfl
  | k + 1 => by
    rw [onesMask, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2]
    have ih := onesMask_add_one k
    calc
      2 * onesMask k + 1 + 1 = 2 * (onesMask k + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
      _ = 2 * 2 ^ k := by rw [ih]

theorem onesMask_eq_two_pow_sub_one (k : Nat) : onesMask k = 2 ^ k - 1 := by
  rw [← onesMask_add_one k, Nat.add_sub_cancel]

/--
  Constructive proof that bitwise AND with `2^k - 1` equals modulo `2^k`
  (`0 Classical.choice`).
-/
theorem and_two_pow_sub_one_eq_mod (x k : Nat) :
    x &&& (2 ^ k - 1) = x % 2 ^ k := by
  rw [← onesMask_eq_two_pow_sub_one k]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_onesMask, Nat.testBit_mod_two_pow, Bool.and_comm]

theorem and_or_distrib_right (x y z : Nat) :
    (x ||| y) &&& z = (x &&& z) ||| (y &&& z) := by
  rw [Nat.and_comm, Nat.and_or_distrib_left, Nat.and_comm z x, Nat.and_comm z y]

/--
  Low-order offset extraction: when `(base &&& mask) = 0`, masking
  `sandboxAddr base mask addr` with `mask` recovers `addr &&& mask`.
-/
theorem sandboxAddr_and_mask (base mask addr : Nat) (hDisj : base &&& mask = 0) :
    sandboxAddr base mask addr &&& mask = addr &&& mask := by
  unfold sandboxAddr
  rw [and_or_distrib_right, Nat.and_assoc, Nat.and_self, hDisj, Nat.or_zero]

/--
  Re-applying the segment-OR instruction `dedicated_reg <- dedicated_reg | base`
  to an already-sandboxed address is strictly idempotent.
-/
theorem sandboxAddr_or_base (base mask addr : Nat) :
    sandboxAddr base mask addr ||| base = sandboxAddr base mask addr := by
  unfold sandboxAddr
  rw [Nat.or_assoc, Nat.or_self]

/--
  Full sandboxing idempotence: sandboxing an already-sandboxed address leaves it
  unchanged when `(base &&& mask) = 0`.
-/
theorem sandboxAddr_idempotent (base mask addr : Nat) (hDisj : base &&& mask = 0) :
    sandboxAddr base mask (sandboxAddr base mask addr) = sandboxAddr base mask addr := by
  unfold sandboxAddr
  rw [and_or_distrib_right, Nat.and_assoc, Nat.and_self, hDisj, Nat.or_zero]

/--
  After the first instruction (`dedicated_reg <- addr &&& (2^k - 1)`), the high
  bits above bit `k` are guaranteed to be zero.
-/
theorem and_mask_shiftRight_zero (addr k : Nat) :
    (addr &&& (2 ^ k - 1)) >>> k = 0 := by
  rw [and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (Nat.mod_lt addr (Nat.two_pow_pos k))

/--
  When `(base &&& (2^k - 1)) = 0`, `base` is an exact multiple of `2^k`:
  `2^k * (base >>> k) = base`.
-/
theorem base_shiftRight_of_and_mask_zero (base k : Nat)
    (hDisj : base &&& (2 ^ k - 1) = 0) :
    2 ^ k * (base >>> k) = base := by
  have hMod : base % 2 ^ k = 0 := by
    rw [← and_two_pow_sub_one_eq_mod]
    exact hDisj
  have hDiv := Nat.div_add_mod base (2 ^ k)
  rw [hMod, Nat.add_zero, ← Nat.shiftRight_eq_div_pow] at hDiv
  exact hDiv

/--
  Fundamental Decomposition Lemma for Wahbe Address Sandboxing:
  When `(base &&& (2^k - 1)) = 0`, bitwise OR with `base` is identical to
  arithmetic addition `base + (addr &&& (2^k - 1))`.
-/
theorem sandboxAddr_eq_add (base k addr : Nat)
    (hDisj : base &&& (2 ^ k - 1) = 0) :
    sandboxAddr base (2 ^ k - 1) addr = base + (addr &&& (2 ^ k - 1)) := by
  have hDivMod := (Nat.div_add_mod (sandboxAddr base (2 ^ k - 1) addr) (2 ^ k)).symm
  rw [← Nat.shiftRight_eq_div_pow, ← and_two_pow_sub_one_eq_mod] at hDivMod
  rw [sandboxAddr_and_mask base (2 ^ k - 1) addr hDisj] at hDivMod
  have hShift : sandboxAddr base (2 ^ k - 1) addr >>> k = base >>> k := by
    unfold sandboxAddr
    rw [Nat.shiftRight_or_distrib, and_mask_shiftRight_zero, Nat.zero_or]
  rw [hShift, base_shiftRight_of_and_mask_zero base k hDisj] at hDivMod
  exact hDivMod

/--
  **Theorem 1.1 (Wahbe Bitwise Address Confinement):**
  For any segment size `size = 2^k`, mask `mask = 2^k - 1`, and aligned segment
  base `base` satisfying `(base &&& mask) = 0`, `sandboxAddr base mask addr`
  always falls within `[base, base + 2^k)` for every untrusted `addr : Nat`.
-/
theorem sandboxAddr_bounds (base k addr : Nat)
    (hDisj : base &&& (2 ^ k - 1) = 0) :
    base ≤ sandboxAddr base (2 ^ k - 1) addr ∧
      sandboxAddr base (2 ^ k - 1) addr < base + 2 ^ k := by
  rw [sandboxAddr_eq_add base k addr hDisj]
  constructor
  · exact Nat.le_add_right base (addr &&& (2 ^ k - 1))
  · rw [and_two_pow_sub_one_eq_mod]
    exact Nat.add_lt_add_left (Nat.mod_lt addr (Nat.two_pow_pos k)) base

/--
  Equivalence between Wahbe Address Sandboxing (§3.2) and Segment Matching (§3.1):
  Every address produced by `sandboxAddr base (2^k - 1) addr` passes
  `segmentMatch k (base >>> k)`.
-/
theorem sandboxAddr_satisfies_segmentMatch (base k addr : Nat) :
    segmentMatch k (base >>> k) (sandboxAddr base (2 ^ k - 1) addr) = true := by
  unfold segmentMatch sandboxAddr
  rw [Nat.shiftRight_or_distrib, and_mask_shiftRight_zero, Nat.zero_or]
  exact nat_beq_self (base >>> k)

/--
  **Theorem 1.2 (Wahbe Guard-Zone Register+Offset Optimization, §3.3, Fig. 3):**
  On RISC architectures with `load/store offset(reg)` addressing (e.g., 16-bit
  signed immediate offsets in `[-64KB, +64KB)` on MIPS/Alpha), leaving an
  unmapped guard zone of size `guardSize` at the top of the segment allows the
  sandbox to omit masking `reg + offset`: sandboxing `reg` alone guarantees that
  `sandboxAddr base (2^k - 1) addr + offset` is `< base + 2^k + guardSize`, so
  it either accesses valid segment memory `[base, base + 2^k)` or traps in the
  unmapped guard zone `[base + 2^k, base + 2^k + guardSize)`, never reaching an
  adjacent fault domain at `≥ base + 2^k + guardSize`.
-/
theorem wahbe_guard_zone_offset_confinement (base k addr offset guardSize : Nat)
    (hDisj : base &&& (2 ^ k - 1) = 0)
    (hOff : offset ≤ guardSize) :
    base ≤ sandboxAddr base (2 ^ k - 1) addr + offset ∧
      sandboxAddr base (2 ^ k - 1) addr + offset < base + 2 ^ k + guardSize := by
  have hBounds := sandboxAddr_bounds base k addr hDisj
  constructor
  · exact Nat.le_trans hBounds.1 (Nat.le_add_right _ offset)
  · exact Nat.add_lt_add_of_lt_of_le hBounds.2 hOff

/-!
### PittSFIeld Zero-Tag Single-`AND` Optimization & 16-Byte Chunk Alignment
(McCamant & Morrisett, USENIX Security 2006, §3–§4)
-/

/--
  PittSFIeld's zero-tag single-`AND` sandboxing operation (`andl $0x20ffffff, %ebx`).
  When the segment base is a single power of two `2^tagBit` (e.g. `0x10000000`
  with `tagBit = 28` for code, or `0x20000000` with `tagBit = 29` for data) and
  the zero-tag region `[0, 2^k)` is left unmapped in the page table, a single
  `AND` instruction with `(2^tagBit) ||| (2^k - 1)` suffices:
  - If bit `tagBit` of `addr` is `1`, the result is in `[2^tagBit, 2^tagBit + 2^k)`.
  - If bit `tagBit` of `addr` is `0`, the result is in the unmapped zero-tag
    guard region `[0, 2^k)` and hardware page-faults immediately.
-/
def pittsfieldSingleAnd (tagBit k addr : Nat) : Nat :=
  match addr.testBit tagBit with
  | true => 2 ^ tagBit + (addr &&& (2 ^ k - 1))
  | false => addr &&& (2 ^ k - 1)

/--
  **Theorem 1.3 (PittSFIeld Zero-Tag Single-`AND` Dichotomy, §4):**
  Every address masked by PittSFIeld's single-`AND` instruction either lands in
  the unmapped zero-tag guard region `[0, 2^k)` (causing an immediate hardware
  page fault) or lands inside the valid sandbox region `[2^tagBit, 2^tagBit + 2^k)`.
-/
theorem pittsfieldSingleAnd_dichotomy (tagBit k addr : Nat) :
    (pittsfieldSingleAnd tagBit k addr < 2 ^ k) ∨
      (2 ^ tagBit ≤ pittsfieldSingleAnd tagBit k addr ∧
        pittsfieldSingleAnd tagBit k addr < 2 ^ tagBit + 2 ^ k) := by
  unfold pittsfieldSingleAnd
  have hLow : addr &&& (2 ^ k - 1) < 2 ^ k := by
    rw [and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt addr (Nat.two_pow_pos k)
  cases addr.testBit tagBit with
  | false =>
    exact Or.inl hLow
  | true =>
    exact Or.inr ⟨Nat.le_add_right (2 ^ tagBit) (addr &&& (2 ^ k - 1)),
                  Nat.add_lt_add_left hLow (2 ^ tagBit)⟩

/--
  PittSFIeld 16-byte chunk-aligned code sandboxing (`andl $0x10fffff0, %ebx`):
  Simultaneously clears bits above the segment offset, forces the segment base
  tag, and clears the low `c` bits (`c = 4` for 16-byte chunks, `c = 5` for
  32-byte chunks) so indirect jumps can only target chunk boundaries.
-/
def sandboxCodeAligned (base k c addr : Nat) : Nat :=
  let rawOff := addr &&& (2 ^ k - 1)
  let alignedOff := rawOff - (rawOff % 2 ^ c)
  base + alignedOff

theorem alignedOff_mod_zero (x c : Nat) :
    (x - x % 2 ^ c) % 2 ^ c = 0 := by
  have hDiv := (Nat.div_add_mod x (2 ^ c)).symm
  have hSub : x - x % 2 ^ c = 2 ^ c * (x / 2 ^ c) := by
    calc
      x - x % 2 ^ c = (2 ^ c * (x / 2 ^ c) + x % 2 ^ c) - x % 2 ^ c := by
        rw [← hDiv]
      _ = 2 ^ c * (x / 2 ^ c) := Nat.add_sub_cancel _ _
  rw [hSub, Nat.mul_mod_right]

/--
  **Theorem 1.4 (PittSFIeld Chunk-Aligned Jump Confinement, §3.2):**
  For any segment base `base` that is a multiple of `2^c` (`base % 2^c = 0`),
  `sandboxCodeAligned base k c addr` lies in `[base, base + 2^k)` AND is an
  exact multiple of the chunk size `2^c` (`target % 2^c = 0`).
-/
theorem sandboxCodeAligned_confinement_and_alignment (base k c addr : Nat)
    (hBaseAlign : base % 2 ^ c = 0) :
    base ≤ sandboxCodeAligned base k c addr ∧
      sandboxCodeAligned base k c addr < base + 2 ^ k ∧
      (sandboxCodeAligned base k c addr) % 2 ^ c = 0 := by
  unfold sandboxCodeAligned
  dsimp only
  have hLow : addr &&& (2 ^ k - 1) < 2 ^ k := by
    rw [and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt addr (Nat.two_pow_pos k)
  have hSubLe : (addr &&& (2 ^ k - 1)) - (addr &&& (2 ^ k - 1)) % 2 ^ c ≤
      addr &&& (2 ^ k - 1) := Nat.sub_le _ _
  constructor
  · exact Nat.le_add_right base _
  · constructor
    · exact Nat.add_lt_add_left (Nat.lt_of_le_of_lt hSubLe hLow) base
    · rw [Nat.add_mod, hBaseAlign, Nat.zero_add, alignedOff_mod_zero, Nat.zero_mod]

/-!
### Counterexample 1A: Unaligned CISC Mid-Instruction Jump Escape
In variable-length CISC ISAs (x86), a verified multi-byte instruction starting
at a 16-byte chunk boundary `0x10000000` (e.g., `movl $0x80cd0000, %eax`, opcode
`0xb8 0x00 0x00 0xcd 0x80`) contains immediate operand bytes `0xcd 0x80` (`int $0x80`
system call) or `0xff 0xe0` (unmasked `jmp *%eax`) at interior byte offset
`0x10000003`.
-/

/-- Instruction decoded at a byte address in our CISC counterexample model. -/
inductive CiscDecodedInst where
  | safeMovImmediate   -- Legal chunk-entry instruction at 0x10000000
  | unsafeSyscallTrap  -- Unintended `int $0x80` decoded at interior offset +3
  | safeNopPadding     -- Verified NOP padding
  deriving DecidableEq, Repr

/-- CISC byte-stream decoder for the 16-byte chunk at `0x10000000`. -/
def decodeCiscByteStream (addr : Nat) : CiscDecodedInst :=
  if addr == 0x10000000 then
    .safeMovImmediate
  else if addr == 0x10000003 then
    .unsafeSyscallTrap
  else
    .safeNopPadding

/--
  **Counterexample 1A (`cisc_unaligned_jump_counterexample`):**
  1. Target `0x10000003` is invariant under raw Wahbe segment sandboxing
     (`sandboxAddr 0x10000000 0x00ffffff 0x10000003 = 0x10000003`) and lies
     inside `[0x10000000, 0x11000000)`, yet decodes `unsafeSyscallTrap` (`int $0x80`)!
  2. Under PittSFIeld 16-byte chunk-aligned sandboxing (`c = 4`), `0x10000003`
     is forced to `0x10000000`, which decodes `safeMovImmediate`.
-/
theorem cisc_unaligned_jump_counterexample :
    sandboxAddr 0x10000000 (2 ^ 24 - 1) 0x10000003 = 0x10000003 ∧
      decodeCiscByteStream (sandboxAddr 0x10000000 (2 ^ 24 - 1) 0x10000003) =
        .unsafeSyscallTrap ∧
      sandboxCodeAligned 0x10000000 24 4 0x10000003 = 0x10000000 ∧
      decodeCiscByteStream (sandboxCodeAligned 0x10000000 24 4 0x10000003) =
        .safeMovImmediate := by
  decide

/-!
### Counterexample 1B & Theorem 1.5: Dedicated-Register Atomicity vs
Non-Dedicated Scratch Register & Mid-Sequence Jump / TOCTOU Hazards
-/

/--
  **Counterexample 1B.1 (`non_dedicated_scratch_mid_sequence_escape`):**
  Suppose a compiler uses a general-purpose scratch register `r_scratch` (rather
  than a dedicated register that always holds a valid sandboxed address) for the
  two-instruction sequence:
    1. `r_scratch <- target &&& 0x00ffffff`
    2. `r_scratch <- r_scratch ||| 0x20000000`
    3. `store [r_scratch], val`
  If `r_scratch` holds an untrusted value `0xdeadbeef` and control jumps
  directly to Instruction 2 (`r_scratch ||| 0x20000000`), the resulting address
  is `0xfeadbeef`, which escapes `[0x20000000, 0x21000000)`!
-/
theorem non_dedicated_scratch_mid_sequence_escape :
    let untrustedScratch := 0xdeadbeef
    let afterOrStep := untrustedScratch ||| 0x20000000
    afterOrStep = 0xfeadbeef ∧ ¬ (afterOrStep < 0x20000000 + 2 ^ 24) := by
  decide

/--
  Wahbe Dedicated-Register State Invariant (Wahbe §3.2 & §3.6):
  At every instruction boundary, a dedicated sandbox register `dReg` is either:
  - `fullySandboxed`: already in `[base, base + 2^k)` (the normal invariant), OR
  - `maskedOnly`: equal to `raw &&& (2^k - 1) ∈ [0, 2^k)` (immediately after the
    `AND` instruction and before the `OR` instruction).
-/
inductive DedicatedRegState (base k : Nat) : Nat → Prop where
  | fullySandboxed (addr : Nat) :
      DedicatedRegState base k (sandboxAddr base (2 ^ k - 1) addr)
  | maskedOnly (addr : Nat) :
      DedicatedRegState base k (addr &&& (2 ^ k - 1))

/--
  **Theorem 1.5 (`wahbe_dedicated_reg_mid_sequence_safe`):**
  If `dReg` satisfies `DedicatedRegState base k dReg`, then executing the second
  sandboxing instruction (`dReg ||| base`) ALWAYS produces a valid address inside
  `[base, base + 2^k)`—even if control jumps straight into the `OR` instruction!
-/
theorem wahbe_dedicated_reg_mid_sequence_safe (base k dReg : Nat)
    (hDisj : base &&& (2 ^ k - 1) = 0)
    (hState : DedicatedRegState base k dReg) :
    base ≤ (dReg ||| base) ∧ (dReg ||| base) < base + 2 ^ k := by
  cases hState with
  | fullySandboxed addr =>
    rw [sandboxAddr_or_base]
    exact sandboxAddr_bounds base k addr hDisj
  | maskedOnly addr =>
    change base ≤ sandboxAddr base (2 ^ k - 1) addr ∧
      sandboxAddr base (2 ^ k - 1) addr < base + 2 ^ k
    exact sandboxAddr_bounds base k addr hDisj

/--
  **Counterexample 1B.2 (`pittsfield_inplace_ret_toctou_race`, McCamant & Morrisett §4):**
  PittSFIeld's default return sequence `andl $0x10fffff0, (%esp); ret` masks the
  return address in memory on the stack before `ret` pops it, so the CPU's Return
  Stack Buffer (RSB) remains aligned. However, in a multi-threaded sandbox where
  a second thread shares the writable data segment, an interleaving store
  `Mem[esp] := 0xdeadbeef` between `andl $0x10fffff0, (%esp)` and `ret` causes
  `ret` to jump to `0xdeadbeef` outside `[0x10000000, 0x11000000)`.
  PittSFIeld's `-threadsafe-return` (`popl %ebx; andl $0x10fffff0, %ebx; jmp *%ebx`)
  masks inside thread-local register `%ebx`, eliminating the shared-memory race.
-/
def inplaceRetWithRace (stackSlotInit concurrentWriteVal : Nat) : Nat :=
  let _maskedInMem := stackSlotInit &&& 0x10fffff0
  let racedMem := concurrentWriteVal
  racedMem

def registerRetWithRace (stackSlotInit _concurrentWriteVal : Nat) : Nat :=
  let ebx := stackSlotInit
  ebx &&& 0x10fffff0

theorem pittsfield_inplace_ret_toctou_race :
    inplaceRetWithRace 0x10000100 0xdeadbeef = 0xdeadbeef ∧
      ¬ (inplaceRetWithRace 0x10000100 0xdeadbeef < 0x11000000) ∧
      registerRetWithRace 0x10000100 0xdeadbeef = 0x10000100 ∧
      0x10000000 ≤ registerRetWithRace 0x10000100 0xdeadbeef ∧
      registerRetWithRace 0x10000100 0xdeadbeef < 0x11000000 := by
  decide

end Layer1_WahbePittSFIeld

/-!
===============================================================================
LAYER 2: Exokernel Secure Bindings, ASH Bounded Loop-Fuel Execution, and
         XOK Exodisk (`XN`) Deterministic UDF Metadata Reference Counting
===============================================================================
-/
namespace Layer2_ExokernelAshDpfxn

/-!
### 2.1 Exokernel Secure Bindings (Engler, Kaashoek & O'Toole, SOSP 1995, §3.2)
Secure bindings decouple *authorization* (performed once at bind time against
high-level ACL/filesystem policy) from *enforcement* (performed at every hardware
or software-TLB access time using only a kernel-protected capability tuple).
-/

abbrev PrincipalId := Nat
abbrev PhysResource := Nat

/-- Kernel-protected capability entry installed in the STLB / buffer registry. -/
structure SecureBinding where
  holder   : PrincipalId
  resource : PhysResource
  epoch    : Nat
  deriving DecidableEq, Repr

/-- High-level authorization policy evaluated only at bind time. -/
abbrev AuthPolicy := PrincipalId → PhysResource → Bool

/-- Bind-time authorization: checks `policy` once and mints a `SecureBinding`. -/
def bindResource (policy : AuthPolicy) (epoch : Nat)
    (p : PrincipalId) (r : PhysResource) : Option SecureBinding :=
  match policy p r with
  | true => some { holder := p, resource := r, epoch := epoch }
  | false => none

/-- Use-time enforcement check: $O(1)$ tag equality without invoking `policy`. -/
def checkBindingAtUse (b : SecureBinding) (currentEpoch : Nat)
    (p : PrincipalId) (r : PhysResource) : Bool :=
  (b.holder == p) && (b.resource == r) && (b.epoch == currentEpoch)

/--
  **Theorem 2.1 (`exokernel_secure_binding_equivalence`):**
  For any binding `b` minted by `bindResource policy epoch owner res`, the fast
  $O(1)$ use-time check `checkBindingAtUse b epoch p r` succeeds if and only if
  `owner = p`, `res = r`, and `policy owner res = true` held at bind time.
-/
theorem exokernel_secure_binding_equivalence
    (policy : AuthPolicy) (epoch : Nat) (owner p : PrincipalId) (res r : PhysResource)
    (b : SecureBinding)
    (hMint : bindResource policy epoch owner res = some b) :
    (checkBindingAtUse b epoch p r = true) ↔
      (owner = p ∧ res = r ∧ policy owner res = true) := by
  unfold bindResource at hMint
  cases hPol : policy owner res with
  | false =>
    rw [hPol] at hMint
    contradiction
  | true =>
    rw [hPol] at hMint
    injection hMint with hEq
    subst hEq
    unfold checkBindingAtUse
    dsimp only
    rw [nat_beq_self epoch, Bool.and_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
    constructor
    · intro ⟨h1, h2⟩
      exact ⟨h1, h2, rfl⟩
    · intro ⟨h1, h2, _⟩
      exact ⟨h1, h2⟩

/-!
### 2.2 ASH Bounded Backward-Branch Loop Counters
(Wallach, Engler & Kaashoek, SIGCOMM 1996, §2.2 & XOK `sys/kern/scode.c`)
Untrusted Application-Specific Handlers (ASHs) execute in the kernel at network
interrupt time. To guarantee termination without banning loops, ASH static
inspection requires forward branches to advance `pc` strictly within bounds and
instruments every backward branch to decrement a dedicated `loopCounter`
register, aborting immediately if `loopCounter == 0`.
-/

inductive AshInstruction where
  | aluSandboxedMem                  -- Normal instruction (`pc := pc + 1`)
  | forwardBranch (offset : Nat)     -- Static check ensures `pc + 1 + offset ≤ len`
  | backwardBranch (targetPc : Nat)  -- Consumes 1 unit of `loopCounter` fuel
  | ashReturn                        -- Clean handler completion
  deriving DecidableEq, Repr

structure AshState where
  pc          : Nat
  loopCounter : Nat
  halted      : Bool
  aborted     : Bool
  deriving DecidableEq, Repr

/-- Single-step operational semantics of an ASH handler with dynamic loop counter. -/
def ashStep (prog : List AshInstruction) (s : AshState) : AshState :=
  if s.halted then
    s
  else
    match prog[s.pc]? with
    | none => { s with halted := true }
    | some .aluSandboxedMem =>
        { s with pc := s.pc + 1 }
    | some (.forwardBranch offset) =>
        { s with pc := s.pc + 1 + offset }
    | some (.backwardBranch targetPc) =>
        match s.loopCounter with
        | 0 => { s with halted := true, aborted := true }
        | fuel + 1 => { s with pc := targetPc, loopCounter := fuel }
    | some .ashReturn =>
        { s with halted := true }

/--
  Run an ASH state machine for `steps` steps; when `loopCounter` is bounded by
  `maxBackBranches` and each forward sweep takes at most `prog.length + 1` steps,
  execution is guaranteed to halt in finite time.
-/
def ashRun : Nat → List AshInstruction → AshState → AshState
  | 0, _, s => s
  | n + 1, prog, s => ashRun n prog (ashStep prog s)

/--
  **Theorem 2.2 (`ash_backward_branch_exhausts_fuel`):**
  Even if an untrusted ASH contains a tight infinite backward jump at `pc = 0`
  (`0: backwardBranch 0`), the instrumented backward-branch counter aborts the
  ASH after exactly `B + 1` steps (`loopCounter = 0, halted = true, aborted = true`).
-/
theorem ash_backward_branch_exhausts_fuel :
    let infiniteLoopAsh := [AshInstruction.backwardBranch 0]
    let init := { pc := 0, loopCounter := 3, halted := false, aborted := false : AshState }
    ashRun 4 infiniteLoopAsh init =
      { pc := 0, loopCounter := 0, halted := true, aborted := true } := by
  decide

/-!
### 2.3 XOK Exodisk (`XN`) Deterministic In-Kernel UDF Metadata Ownership
(Kaashoek et al., SOSP 1997, §4 & XOK `sys/ubb/{udf.c,interp.c,check.c,xn.c}`)

In XOK's Exodisk (`XN`), each library filesystem (libFS) defines its own raw
metadata layout (`MetadataBlock`) and uploads an untrusted deterministic
bytecode function `udfOwns : MetadataBlock → List PhysBlock` (`owns-udf_T(m)`).
Instead of trusting the libFS's claim of which disk blocks were added or freed,
`meta_transaction` (`sys/ubb/udf.c:204–309`) checkpoints the metadata block,
runs `oldSet = udfOwns meta`, applies the libFS's raw byte writes to produce
`meta'`, runs `newSet = udfOwns meta'`, and verifies the exact set delta against
the kernel's physical block free-map (`db_isfree`) before committing or rolling
back (`udf_rollback`).
-/

abbrev PhysBlock := Nat
abbrev MetadataBlock := List Nat

/--
  Executable list-membership and subset/disjointness predicates so all runtime
  XN checks and proofs remain completely constructive (`0 Classical.choice`).
-/
def memBlock (b : PhysBlock) : List PhysBlock → Bool
  | [] => false
  | x :: xs => (b == x) || memBlock b xs

def subsetBlocks (xs ys : List PhysBlock) : Bool :=
  xs.all (fun x => memBlock x ys)

def setEqBlocks (xs ys : List PhysBlock) : Bool :=
  subsetBlocks xs ys && subsetBlocks ys xs

def disjointBlocks (xs ys : List PhysBlock) : Bool :=
  xs.all (fun x => !memBlock x ys)

/--
  Global XN Disk State (simplified to two libFS metadata slots `metaA` and `metaB`
  plus the kernel's authoritative allocation bitmap `isAllocated : PhysBlock → Bool`).
  In XOK `sys/ubb/xn.c`, this generalizes over the `XN` registry catalogue.
-/
structure XnDiskState where
  metaA       : MetadataBlock
  metaB       : MetadataBlock
  isAllocated : PhysBlock → Bool

/--
  **Global XN Ownership & Disjointness Invariant (`XnOwnershipInv`):**
  For a given `udfOwns : MetadataBlock → List PhysBlock`:
  1. Every physical block claimed by `udfOwns disk.metaA` is marked allocated in
     the kernel free-map (`disk.isAllocated b = true`);
  2. Every physical block claimed by `udfOwns disk.metaB` is marked allocated in
     the kernel free-map (`disk.isAllocated b = true`);
  3. `udfOwns disk.metaA` and `udfOwns disk.metaB` are strictly disjoint: no
     physical block is ever simultaneously owned by both `metaA` and `metaB`
     (no double-allocation / no cross-domain block aliasing).
-/
structure XnOwnershipInv (udfOwns : MetadataBlock → List PhysBlock)
    (disk : XnDiskState) : Prop where
  allocA   : ∀ b, memBlock b (udfOwns disk.metaA) = true → disk.isAllocated b = true
  allocB   : ∀ b, memBlock b (udfOwns disk.metaB) = true → disk.isAllocated b = true
  disjoint : ∀ b, memBlock b (udfOwns disk.metaA) = true →
               memBlock b (udfOwns disk.metaB) = false

/-- Update helper for the physical block bitmap. -/
def updateBitmap (bm : PhysBlock → Bool) (target : PhysBlock) (val : Bool)
    (x : PhysBlock) : Bool :=
  match x == target with
  | true => val
  | false => bm x

/--
  XOK `udf_alloc` transaction on `metaA` (`sys/ubb/udf.c:239–256`, `xn.c:211–263`):
  The libFS proposes an arbitrary mutated byte-vector `metaA'` and requests to
  allocate physical block `b`. XN runs `oldSet = udfOwns disk.metaA` and
  `newSet = udfOwns metaA'`, and commits `metaA'` if and only if:
  1. `disk.isAllocated b == false` (`db_isfree(b)` in `xn.c`);
  2. Every block in `newSet` is either `b` or was already in `oldSet`
     (`newSet ⊆ b :: oldSet`), and `b ∈ newSet`.
  If the check fails, XN rolls back `metaA'` (`udf_rollback`) and returns `disk`
  unchanged!
-/
def xnAllocMetaA (udfOwns : MetadataBlock → List PhysBlock)
    (disk : XnDiskState) (metaA' : MetadataBlock) (b : PhysBlock) : XnDiskState :=
  let oldSet := udfOwns disk.metaA
  let newSet := udfOwns metaA'
  if (!disk.isAllocated b) && subsetBlocks newSet (b :: oldSet) && memBlock b newSet then
    { disk with
      metaA := metaA'
      isAllocated := updateBitmap disk.isAllocated b true }
  else
    disk -- `udf_rollback`: transaction aborted, metadata unchanged

/--
  XOK `udf_write` transaction on `metaA` (`sys/ubb/udf.c:273–285`):
  Allows modifying non-pointer metadata attributes (timestamps, permissions)
  without allocating/freeing blocks if and only if `udfOwns metaA' ⊆ udfOwns metaA`.
-/
def xnWriteMetaA (udfOwns : MetadataBlock → List PhysBlock)
    (disk : XnDiskState) (metaA' : MetadataBlock) : XnDiskState :=
  let oldSet := udfOwns disk.metaA
  let newSet := udfOwns metaA'
  if subsetBlocks newSet oldSet then
    { disk with metaA := metaA' }
  else
    disk -- `udf_rollback`

/--
  XOK `udf_dealloc` transaction on `metaA` (`sys/ubb/udf.c:258–271`, `xn.c:340–385`):
  Frees physical block `b` from `metaA` if and only if `b ∈ oldSet`, `b ∉ newSet`,
  and `newSet ⊆ oldSet`.
-/
def xnDeallocMetaA (udfOwns : MetadataBlock → List PhysBlock)
    (disk : XnDiskState) (metaA' : MetadataBlock) (b : PhysBlock) : XnDiskState :=
  let oldSet := udfOwns disk.metaA
  let newSet := udfOwns metaA'
  if memBlock b oldSet && (!memBlock b newSet) && subsetBlocks newSet oldSet then
    { disk with
      metaA := metaA'
      isAllocated := updateBitmap disk.isAllocated b false }
  else
    disk -- `udf_rollback`

theorem subsetBlocks_mem {xs ys : List PhysBlock} {x : PhysBlock}
    (hSub : subsetBlocks xs ys = true) (hMem : memBlock x xs = true) :
    memBlock x ys = true := by
  unfold subsetBlocks at hSub
  induction xs with
  | nil =>
    simp [memBlock] at hMem
  | cons hd tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hSub
    simp only [memBlock, Bool.or_eq_true] at hMem
    cases hMem with
    | inl hEq =>
      have hEq' : x = hd := beq_iff_eq.mp hEq
      subst hEq'
      exact hSub.1
    | inr hInTl =>
      exact ih hSub.2 hInTl

/--
  **Theorem 2.3 (`xnAllocMetaA_preserves_inv`):**
  For ANY pure deterministic function `udfOwns : MetadataBlock → List PhysBlock`
  and ANY untrusted byte-vector `metaA'` proposed by the libFS, `xnAllocMetaA`
  strictly preserves `XnOwnershipInv`.
  Crucially, the kernel does NOT trust `udfOwns` to be "honest" about semantics;
  it relies ONLY on `udfOwns` being a pure deterministic function of its
  `MetadataBlock` argument!
-/
theorem xnAllocMetaA_preserves_inv (udfOwns : MetadataBlock → List PhysBlock)
    (disk : XnDiskState) (metaA' : MetadataBlock) (b : PhysBlock)
    (hInv : XnOwnershipInv udfOwns disk) :
    XnOwnershipInv udfOwns (xnAllocMetaA udfOwns disk metaA' b) := by
  unfold xnAllocMetaA
  dsimp only
  cases hCond : ((!disk.isAllocated b) && subsetBlocks (udfOwns metaA') (b :: udfOwns disk.metaA) &&
      memBlock b (udfOwns metaA')) with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact hInv
  | true =>
    simp only [↓reduceIte]
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hCond
    rcases hCond with ⟨⟨hFreeB, hSub⟩, _hMemB⟩
    constructor
    · intro x hx
      dsimp only at hx ⊢
      unfold updateBitmap
      have hInCons := subsetBlocks_mem hSub hx
      simp only [memBlock, Bool.or_eq_true] at hInCons
      cases hInCons with
      | inl hEq =>
        rw [hEq]
      | inr hInOld =>
        have hAllocOld := hInv.allocA x hInOld
        cases (x == b) with
        | true => rfl
        | false => exact hAllocOld
    · intro x hx
      dsimp only at hx ⊢
      unfold updateBitmap
      have hAllocB := hInv.allocB x hx
      cases (x == b) with
      | true => rfl
      | false => exact hAllocB
    · intro x hx
      dsimp only at hx ⊢
      have hInCons := subsetBlocks_mem hSub hx
      simp only [memBlock, Bool.or_eq_true] at hInCons
      cases hInCons with
      | inl hEq =>
        have hEq' : x = b := beq_iff_eq.mp hEq
        subst hEq'
        cases hInB : memBlock x (udfOwns disk.metaB) with
        | false => rfl
        | true =>
          have hAllocB := hInv.allocB x hInB
          rw [hAllocB] at hFreeB
          contradiction
      | inr hInOld =>
        exact hInv.disjoint x hInOld

/--
  **Theorem 2.4 (`xnWriteMetaA_preserves_inv`):**
  For any deterministic `udfOwns`, `xnWriteMetaA` preserves `XnOwnershipInv`.
-/
theorem xnWriteMetaA_preserves_inv (udfOwns : MetadataBlock → List PhysBlock)
    (disk : XnDiskState) (metaA' : MetadataBlock)
    (hInv : XnOwnershipInv udfOwns disk) :
    XnOwnershipInv udfOwns (xnWriteMetaA udfOwns disk metaA') := by
  unfold xnWriteMetaA
  dsimp only
  cases hSub : subsetBlocks (udfOwns metaA') (udfOwns disk.metaA) with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact hInv
  | true =>
    simp only [↓reduceIte]
    constructor
    · intro x hx
      exact hInv.allocA x (subsetBlocks_mem hSub hx)
    · exact hInv.allocB
    · intro x hx
      exact hInv.disjoint x (subsetBlocks_mem hSub hx)

/--
  **Theorem 2.5 (`xnDeallocMetaA_preserves_inv`):**
  For any deterministic `udfOwns`, `xnDeallocMetaA` preserves `XnOwnershipInv`:
  because `b ∈ udfOwns disk.metaA` and `XnOwnershipInv` guarantees `metaA` and
  `metaB` are disjoint, freeing `b` from `metaA` can NEVER unallocate a block
  still owned by `metaB`!
-/
theorem xnDeallocMetaA_preserves_inv (udfOwns : MetadataBlock → List PhysBlock)
    (disk : XnDiskState) (metaA' : MetadataBlock) (b : PhysBlock)
    (hInv : XnOwnershipInv udfOwns disk) :
    XnOwnershipInv udfOwns (xnDeallocMetaA udfOwns disk metaA' b) := by
  unfold xnDeallocMetaA
  dsimp only
  cases hCond : (memBlock b (udfOwns disk.metaA) && (!memBlock b (udfOwns metaA')) &&
      subsetBlocks (udfOwns metaA') (udfOwns disk.metaA)) with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact hInv
  | true =>
    simp only [↓reduceIte]
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hCond
    rcases hCond with ⟨⟨hInOldB, hNotInNewB⟩, hSub⟩
    constructor
    · intro x hx
      dsimp only at hx ⊢
      unfold updateBitmap
      have hInOldX := subsetBlocks_mem hSub hx
      cases hEq : (x == b) with
      | true =>
        have hEq' : x = b := beq_iff_eq.mp hEq
        subst hEq'
        rw [hx] at hNotInNewB
        contradiction
      | false =>
        exact hInv.allocA x hInOldX
    · intro x hx
      dsimp only at hx ⊢
      unfold updateBitmap
      cases hEq : (x == b) with
      | true =>
        have hEq' : x = b := beq_iff_eq.mp hEq
        subst hEq'
        have hDisj := hInv.disjoint x hInOldB
        rw [hx] at hDisj
        contradiction
      | false =>
        exact hInv.allocB x hx
    · intro x hx
      dsimp only at hx ⊢
      exact hInv.disjoint x (subsetBlocks_mem hSub hx)

/--
  **Counterexample 2A (`xn_nondeterministic_udf_breaks_disjointness`):**
  Why XOK's `udf_check` (`sys/ubb/check.c:106–185`) MUST enforce strict UDF
  determinism (forbidding access to mutable global state or uninitialized
  registers):
  Suppose a stateful/nondeterministic UDF `evilStatefulUdf (epoch : Nat) (m : MetadataBlock)`
  evaluates `metaA' = [10]` as owning `[10]` during `xnAlloc` (`epoch = 0`),
  passing XN's check (`b = 10` is free), but at `epoch = 1` evaluates the exact
  same `metaA' = [10]` as owning `[20]` (a victim block owned by `metaB = [20]`).
  Then `metaA` and `metaB` both claim physical block `20`, violating disjointness
  and allowing `metaA` to corrupt or free `metaB`'s disk block!
-/
def evilStatefulUdf (epoch : Nat) (m : MetadataBlock) : List PhysBlock :=
  if epoch == 0 then
    m
  else
    m.map (fun b => if b == 10 then 20 else b)

theorem xn_nondeterministic_udf_breaks_disjointness :
    let initDisk : XnDiskState := {
      metaA := []
      metaB := [20]
      isAllocated := fun b => b == 20
    }
    let afterAlloc := xnAllocMetaA (evilStatefulUdf 0) initDisk [10] 10
    memBlock 20 (evilStatefulUdf 1 afterAlloc.metaA) = true ∧
      memBlock 20 (evilStatefulUdf 1 afterAlloc.metaB) = true := by
  decide

/-!
### 2.4 Universal $N$-Slot Differential Determinism
Characterization & Exact Intra-LibOS vs. Inter-LibOS Isolation Boundary

We now generalize XOK's `XN` mechanism to an arbitrary $N$-slot metadata store
(`MetaSlot → MetadataBlock`) and an arbitrary pure deterministic function
`f : MetadataBlock → List PhysBlock` (even a buggy or adversarial one!).
-/

abbrev MetaSlot := Nat

structure XnGeneralDisk where
  metaStore   : MetaSlot → MetadataBlock
  isAllocated : PhysBlock → Bool

/--
  **Global $N$-Slot Pairwise Disjointness & Free-Map Invariant (`XnGeneralDisjointInv`):**
  1. `allocValid`: Every block `b ∈ f (disk.metaStore s)` is marked allocated in
     the kernel's global free-map (`disk.isAllocated b = true`).
  2. `pairwiseDisjoint`: For any two distinct metadata slots `s1 ≠ s2`, the owned
     block sets `f (disk.metaStore s1)` and `f (disk.metaStore s2)` are strictly
     disjoint (`no double-allocation / no cross-slot aliasing`).
-/
structure XnGeneralDisjointInv (f : MetadataBlock → List PhysBlock)
    (disk : XnGeneralDisk) : Prop where
  allocValid : ∀ (s : MetaSlot) (b : PhysBlock),
    memBlock b (f (disk.metaStore s)) = true → disk.isAllocated b = true
  pairwiseDisjoint : ∀ (s1 s2 : MetaSlot) (b : PhysBlock),
    (s1 == s2) = false →
    memBlock b (f (disk.metaStore s1)) = true →
    memBlock b (f (disk.metaStore s2)) = false

/--
  Initial disk state where every metadata slot starts at `mInit` (satisfying
  `f mInit = []`, checked once when initializing a zeroed metadata block) and
  all physical blocks are free (`isAllocated _ = false`).
-/
def xnInitGeneralDisk (mInit : MetadataBlock) : XnGeneralDisk :=
  { metaStore := fun _ => mInit, isAllocated := fun _ => false }

/--
  **Theorem 2.6 (`xnInitGeneralDisk_satisfies_inv`):**
  For any deterministic `f` with `f mInit = []`, `xnInitGeneralDisk mInit`
  satisfies `XnGeneralDisjointInv f`.
-/
theorem xnInitGeneralDisk_satisfies_inv (f : MetadataBlock → List PhysBlock)
    (mInit : MetadataBlock) (hEmpty : f mInit = []) :
    XnGeneralDisjointInv f (xnInitGeneralDisk mInit) := by
  constructor
  · intro s b hMem
    dsimp only [xnInitGeneralDisk] at hMem
    rw [hEmpty] at hMem
    contradiction
  · intro s1 s2 b _ hMem1
    dsimp only [xnInitGeneralDisk] at hMem1
    rw [hEmpty] at hMem1
    contradiction

/--
  Differential Admission Check (`xnDiffCheck`):
  When slot `slot` proposes to transition from `m` (`oldSet = f m`) to `m'`
  (`newSet = f m'`), every newly added block `b ∈ newSet \ oldSet` must be
  globally free (`isAlloc b == false`, corresponding to `db_isfree` in `xn.c`).
-/
def xnDiffCheck (oldSet newSet : List PhysBlock) (isAlloc : PhysBlock → Bool) : Bool :=
  newSet.all (fun b => memBlock b oldSet || !isAlloc b)

theorem xnDiffCheck_mem {oldSet newSet : List PhysBlock} {isAlloc : PhysBlock → Bool}
    {b : PhysBlock} (hCheck : xnDiffCheck oldSet newSet isAlloc = true)
    (hInNew : memBlock b newSet = true) (hNotInOld : memBlock b oldSet = false) :
    isAlloc b = false := by
  unfold xnDiffCheck at hCheck
  induction newSet with
  | nil =>
    simp [memBlock] at hInNew
  | cons hd tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hCheck
    simp only [memBlock, Bool.or_eq_true] at hInNew
    cases hInNew with
    | inl hEq =>
      have hEq' : b = hd := beq_iff_eq.mp hEq
      subst hEq'
      have hHead := hCheck.1
      rw [hNotInOld, Bool.false_or, Bool.not_eq_true'] at hHead
      exact hHead
    | inr hInTl =>
      exact ih hCheck.2 hInTl

def updateMetaStore (ms : MetaSlot → MetadataBlock) (slot : MetaSlot)
    (m' : MetadataBlock) (s : MetaSlot) : MetadataBlock :=
  match s == slot with
  | true => m'
  | false => ms s

def updateGeneralAlloc (oldSet newSet : List PhysBlock) (isAlloc : PhysBlock → Bool)
    (b : PhysBlock) : Bool :=
  match memBlock b newSet with
  | true => true
  | false =>
      match memBlock b oldSet with
      | true => false
      | false => isAlloc b

/--
  General Differential Transition (`xnGeneralStep`):
  Evaluates `oldSet = f (disk.metaStore slot)` and `newSet = f m'`. If
  `xnDiffCheck` holds, commits `m'` and updates `isAllocated` (allocating
  `newSet \ oldSet` and freeing `oldSet \ newSet`); otherwise rolls back (`disk`).
-/
def xnGeneralStep (f : MetadataBlock → List PhysBlock) (disk : XnGeneralDisk)
    (slot : MetaSlot) (m' : MetadataBlock) : XnGeneralDisk :=
  let oldSet := f (disk.metaStore slot)
  let newSet := f m'
  match xnDiffCheck oldSet newSet disk.isAllocated with
  | true =>
      { metaStore := updateMetaStore disk.metaStore slot m'
        isAllocated := updateGeneralAlloc oldSet newSet disk.isAllocated }
  | false =>
      disk

theorem nat_beq_symm (a b : Nat) : (a == b) = (b == a) := by
  cases h1 : (a == b) with
  | true =>
    have hEq : a = b := beq_iff_eq.mp h1
    subst hEq
    exact (nat_beq_self a).symm
  | false =>
    cases h2 : (b == a) with
    | false => rfl
    | true =>
      have hEq : b = a := beq_iff_eq.mp h2
      subst hEq
      rw [nat_beq_self b] at h1
      contradiction

/--
  **Theorem 2.7 (`xnGeneralStep_preserves_disjoint_inv` — Universal Differential
  Determinism Soundness):**
  For ANY pure deterministic function `f : MetadataBlock → List PhysBlock` (even
  an arbitrary/buggy one!), every `xnGeneralStep` transition on any slot `slot`
  strictly preserves `XnGeneralDisjointInv f`.
-/
theorem xnGeneralStep_preserves_disjoint_inv (f : MetadataBlock → List PhysBlock)
    (disk : XnGeneralDisk) (slot : MetaSlot) (m' : MetadataBlock)
    (hInv : XnGeneralDisjointInv f disk) :
    XnGeneralDisjointInv f (xnGeneralStep f disk slot m') := by
  unfold xnGeneralStep
  dsimp only
  cases hCheck : xnDiffCheck (f (disk.metaStore slot)) (f m') disk.isAllocated with
  | false => exact hInv
  | true =>
    constructor
    · intro s b hMem
      dsimp only [updateMetaStore, updateGeneralAlloc] at hMem ⊢
      cases hSlot : (s == slot) with
      | true =>
        rw [hSlot] at hMem
        rw [hMem]
      | false =>
        rw [hSlot] at hMem
        have hAllocOld := hInv.allocValid s b hMem
        cases memBlock b (f m') with
        | true => rfl
        | false =>
          have hNotInSlot := hInv.pairwiseDisjoint s slot b hSlot hMem
          rw [hNotInSlot]
          exact hAllocOld
    · intro s1 s2 b hNe hMem1
      dsimp only [updateMetaStore] at hMem1 ⊢
      cases hS1 : (s1 == slot) with
      | true =>
        rw [hS1] at hMem1
        have hEq1 : s1 = slot := beq_iff_eq.mp hS1
        subst hEq1
        have hS2 : (s2 == s1) = false := by
          rw [nat_beq_symm, hNe]
        rw [hS2]
        cases hInOld : memBlock b (f (disk.metaStore s1)) with
        | true =>
          exact hInv.pairwiseDisjoint s1 s2 b hNe hInOld
        | false =>
          have hFree := xnDiffCheck_mem hCheck hMem1 hInOld
          cases hInS2 : memBlock b (f (disk.metaStore s2)) with
          | false => rfl
          | true =>
            have hAllocS2 := hInv.allocValid s2 b hInS2
            rw [hAllocS2] at hFree
            contradiction
      | false =>
        rw [hS1] at hMem1
        cases hS2 : (s2 == slot) with
        | false =>
          exact hInv.pairwiseDisjoint s1 s2 b hNe hMem1
        | true =>
          have hEq2 : s2 = slot := beq_iff_eq.mp hS2
          subst hEq2
          cases hInNew : memBlock b (f m') with
          | false => rfl
          | true =>
            cases hInOld : memBlock b (f (disk.metaStore s2)) with
            | true =>
              have hDisj := hInv.pairwiseDisjoint s1 s2 b hNe hMem1
              rw [hInOld] at hDisj
              contradiction
            | false =>
              have hFree := xnDiffCheck_mem hCheck hInNew hInOld
              have hAllocS1 := hInv.allocValid s1 b hMem1
              rw [hAllocS1] at hFree
              contradiction

/-- Multi-step execution trace over arbitrary `(MetaSlot × MetadataBlock)` transitions. -/
def xnGeneralTrace (f : MetadataBlock → List PhysBlock) :
    List (MetaSlot × MetadataBlock) → XnGeneralDisk → XnGeneralDisk
  | [], disk => disk
  | (slot, m') :: rest, disk =>
      xnGeneralTrace f rest (xnGeneralStep f disk slot m')

/--
  **Theorem 2.8 (`xnGeneralTrace_preserves_disjoint_inv`):**
  Starting from `xnInitGeneralDisk mInit` (with `f mInit = []`), ANY finite
  sequence of differential transitions across any number of metadata slots
  preserves `XnGeneralDisjointInv f`.
-/
theorem xnGeneralTrace_preserves_from_any (f : MetadataBlock → List PhysBlock)
    (trace : List (MetaSlot × MetadataBlock)) (disk : XnGeneralDisk)
    (hInv : XnGeneralDisjointInv f disk) :
    XnGeneralDisjointInv f (xnGeneralTrace f trace disk) := by
  induction trace generalizing disk with
  | nil => exact hInv
  | cons step rest ih =>
    rcases step with ⟨slot, m'⟩
    unfold xnGeneralTrace
    exact ih (xnGeneralStep f disk slot m') (xnGeneralStep_preserves_disjoint_inv f disk slot m' hInv)

theorem xnGeneralTrace_preserves_disjoint_inv (f : MetadataBlock → List PhysBlock)
    (mInit : MetadataBlock) (hEmpty : f mInit = [])
    (trace : List (MetaSlot × MetadataBlock)) :
    XnGeneralDisjointInv f (xnGeneralTrace f trace (xnInitGeneralDisk mInit)) :=
  xnGeneralTrace_preserves_from_any f trace (xnInitGeneralDisk mInit)
    (xnInitGeneralDisk_satisfies_inv f mInit hEmpty)

/--
  Exact `udf_write` check (`sys/ubb/udf.c:280`, `set_eq(old_set, new_set)`):
  Requires `setEqBlocks (f m') (f m) == true` (both `f m' ⊆ f m` and `f m ⊆ f m'`).
-/
def xnStrictUdfWrite (f : MetadataBlock → List PhysBlock) (disk : XnGeneralDisk)
    (slot : MetaSlot) (m' : MetadataBlock) : XnGeneralDisk :=
  let oldSet := f (disk.metaStore slot)
  let newSet := f m'
  match setEqBlocks newSet oldSet with
  | true => { disk with metaStore := updateMetaStore disk.metaStore slot m' }
  | false => disk -- `udf_rollback`

/--
  **Theorem 2.9 (`xn_udf_write_catches_silent_block_drop`):**
  If a buggy UDF `f` silently drops an owned block `b` during a non-deallocating
  `udf_write` (`memBlock b (f m) = true` but `memBlock b (f m') = false`),
  `setEqBlocks (f m') (f m)` evaluates to `false` and `xnStrictUdfWrite` rolls
  back the metadata write (`metaStore slot` remains `m`), preventing accidental
  block leaks!
-/
theorem xn_udf_write_catches_silent_block_drop
    (f : MetadataBlock → List PhysBlock) (disk : XnGeneralDisk)
    (slot : MetaSlot) (m' : MetadataBlock) (b : PhysBlock)
    (hOwned : memBlock b (f (disk.metaStore slot)) = true)
    (hDropped : memBlock b (f m') = false) :
    setEqBlocks (f m') (f (disk.metaStore slot)) = false ∧
      xnStrictUdfWrite f disk slot m' = disk := by
  unfold xnStrictUdfWrite
  dsimp only
  cases hEq : setEqBlocks (f m') (f (disk.metaStore slot)) with
  | false => exact ⟨rfl, rfl⟩
  | true =>
    unfold setEqBlocks at hEq
    simp only [Bool.and_eq_true] at hEq
    have hInNew := subsetBlocks_mem hEq.2 hOwned
    rw [hDropped] at hInNew
    contradiction

/--
  **Theorem 2.10 (`xn_differential_determinism_intra_libos_boundary`):**
  Exact boundary of what Differential Determinism does and does NOT guarantee:
  Suppose LibOS at slot `0` has a bug where its user-space read path
  `libosUserRead : MetadataBlock → List PhysBlock` disagrees with its uploaded
  kernel UDF `f : MetadataBlock → List PhysBlock` (e.g., `f` extracts index 0 of
  `m` while `libosUserRead` extracts index 1 of `m`).
  Then after executing transitions `trace`:
  1. **Inter-LibOS Isolation Holds:** `XnGeneralDisjointInv f diskFinal` holds
     (slot `0` cannot claim or free physical block `20` owned by slot `1`);
  2. **Intra-LibOS Self-Corruption Occurs:** `libosUserRead (diskFinal.metaStore 0) ≠
     f (diskFinal.metaStore 0)` (the LibOS's own user-space view diverges from
     the kernel-enforced ownership set of slot `0`).
-/
def buggySlot0KernelUdf (m : MetadataBlock) : List PhysBlock :=
  match m with
  | b0 :: _ => [b0]
  | [] => []

def buggySlot0UserRead (m : MetadataBlock) : List PhysBlock :=
  match m with
  | _ :: b1 :: _ => [b1]
  | _ => []

theorem xn_differential_determinism_intra_libos_boundary :
    let init := xnInitGeneralDisk []
    let step1 := xnGeneralStep buggySlot0KernelUdf init 1 [20]
    let diskFinal := xnGeneralStep buggySlot0KernelUdf step1 0 [10, 99]
    -- 1. Kernel UDF for slot 0 owns [10], strictly disjoint from slot 1's [20]:
    buggySlot0KernelUdf (diskFinal.metaStore 0) = [10] ∧
    buggySlot0KernelUdf (diskFinal.metaStore 1) = [20] ∧
    disjointBlocks (buggySlot0KernelUdf (diskFinal.metaStore 0))
      (buggySlot0KernelUdf (diskFinal.metaStore 1)) = true ∧
    -- 2. Even if slot 0 tries to claim slot 1's block 20, `xnGeneralStep` rejects it:
    (xnGeneralStep buggySlot0KernelUdf diskFinal 0 [20]).metaStore 0 = [10, 99] ∧
    -- 3. Yet slot 0's user-space reader sees [99] ≠ [10] (intra-LibOS self-corruption):
    buggySlot0UserRead (diskFinal.metaStore 0) = [99] ∧
    buggySlot0UserRead (diskFinal.metaStore 0) ≠
      buggySlot0KernelUdf (diskFinal.metaStore 0) := by
  decide

end Layer2_ExokernelAshDpfxn

/-!
===============================================================================
LAYER 3: XFI Scoped Stack + Inline CFI vs BGI Dynamic Typestate (`dright`)
         and LXFI Capability-Mediated API Proxies & Writer-Set Tracking
===============================================================================
-/
namespace Layer3_XfiBgiLxfi

/-!
### 3.1 Intra-Sandbox Return-Address Corruption Under Layer-1 SFI vs XFI's
Split Scoped Stack + Allocation Stack + Inline CFI (Erlingsson et al., OSDI 2006)
-/

/--
  Under Layer-1 SFI (without XFI's split scoped stack or MiSFIT's external return
  stack), the call stack resides inside the contiguous writable data sandbox
  `[dataBase, dataBase + 2^k)`. An untrusted store to `addr` checks only that
  `addr` is sandboxed into `[dataBase, dataBase + 2^k)`.
-/
structure Layer1SandboxState where
  dataBase      : Nat
  dataMask      : Nat
  stackRetSlot  : Nat
  mem           : Nat → Nat

def layer1SandboxStore (s : Layer1SandboxState) (rawAddr val : Nat) : Layer1SandboxState :=
  let safeAddr := Layer1_WahbePittSFIeld.sandboxAddr s.dataBase s.dataMask rawAddr
  { s with mem := fun a => if a == safeAddr then val else s.mem a }

/--
  **Counterexample 3A (`layer1_sfi_intra_sandbox_ret_overwrite`):**
  Even though `layer1SandboxStore` enforces Wahbe bitwise sandboxing on the store
  address, if the saved return address lives at `stackRetSlot = 0x20000ff0`
  inside the data segment `[0x20000000, 0x21000000)`, a buffer overflow targeting
  `0x20000ff0` passes the data-sandbox mask and overwrites the saved return
  address from `0x10000040` (legitimate caller return site) to `0x10000800`
  (an unauthorized chunk-aligned function/gadget inside the code segment)!
-/
theorem layer1_sfi_intra_sandbox_ret_overwrite :
    let init : Layer1SandboxState := {
      dataBase := 0x20000000
      dataMask := 0x00ffffff
      stackRetSlot := 0x20000ff0
      mem := fun a => if a == 0x20000ff0 then 0x10000040 else 0
    }
    let corrupted := layer1SandboxStore init 0x20000ff0 0x10000800
    corrupted.mem corrupted.stackRetSlot = 0x10000800 ∧
      corrupted.mem corrupted.stackRetSlot ≠ init.mem init.stackRetSlot := by
  decide

/--
  XFI's Two-Stack + Inline-CFI Machine State (Erlingsson et al., OSDI 2006, §2.1–2.3):
  - `scopedStack`: stores return addresses and spilled locals; NEVER addressable
    via computed pointers (only pushed by `call`, popped by `ret`, or accessed
    at statically verified constant frame offsets).
  - `allocationStack`: stores address-taken variables and buffers, subject to
    XFI's memory-range guard `mrguard`.
  - `cfiLabelTable`: maps code addresses to their embedded 32-bit `prefetchnta`
    CFI target ID (`none` if the address is not a valid indirect call target).
-/
structure XfiMachineState where
  scopedStack     : List Nat
  allocLow        : Nat
  allocHigh       : Nat
  allocMem        : Nat → Nat
  cfiLabelTable   : Nat → Option Nat
  pc              : Nat
  faulted         : Bool

/-- XFI memory-range guard `mrguard`: checks `allocLow ≤ addr ∧ addr < allocHigh`. -/
def xfiWriteAllocMem (s : XfiMachineState) (addr val : Nat) : XfiMachineState :=
  match s.allocLow ≤ addr && addr < s.allocHigh with
  | true => { s with allocMem := fun a => if a == addr then val else s.allocMem a }
  | false => { s with faulted := true }

/-- XFI indirect call with inline CFI check (`Mem[target - 4] == expectedCfiId`). -/
def xfiIndirectCall (s : XfiMachineState) (target expectedCfiId returnSite : Nat) :
    XfiMachineState :=
  match s.cfiLabelTable target with
  | some id =>
      match id == expectedCfiId with
      | true => { s with scopedStack := returnSite :: s.scopedStack, pc := target }
      | false => { s with faulted := true }
  | none =>
      { s with faulted := true }

/-- XFI return instruction: pops return address directly from `scopedStack`. -/
def xfiRet (s : XfiMachineState) : XfiMachineState :=
  match s.scopedStack with
  | [] => { s with faulted := true }
  | retAddr :: rest => { s with scopedStack := rest, pc := retAddr }

/--
  **Theorem 3.1 (`xfi_scoped_stack_immune_to_alloc_writes`):**
  No sequence of arbitrary untrusted writes via `xfiWriteAllocMem` can ever
  alter `scopedStack`; hence `xfiRet` after a matching `xfiIndirectCall` and
  arbitrary intermediate buffer writes ALWAYS returns to the exact `returnSite`
  pushed by the call!
-/
theorem xfi_scoped_stack_immune_to_alloc_writes
    (s : XfiMachineState) (addr val : Nat) :
    (xfiWriteAllocMem s addr val).scopedStack = s.scopedStack := by
  unfold xfiWriteAllocMem
  cases (s.allocLow ≤ addr && addr < s.allocHigh) <;> rfl

theorem xfi_call_write_ret_exact
    (s : XfiMachineState) (target cfiId returnSite writeAddr writeVal : Nat)
    (hCfi : s.cfiLabelTable target = some cfiId)
    (hBounds : (s.allocLow ≤ writeAddr && writeAddr < s.allocHigh) = true) :
    let s1 := xfiIndirectCall s target cfiId returnSite
    let s2 := xfiWriteAllocMem s1 writeAddr writeVal
    let s3 := xfiRet s2
    s3.pc = returnSite ∧ s3.scopedStack = s.scopedStack ∧ s3.faulted = s.faulted := by
  have h1 : xfiIndirectCall s target cfiId returnSite =
      { s with scopedStack := returnSite :: s.scopedStack, pc := target } := by
    unfold xfiIndirectCall
    rw [hCfi]
    dsimp only
    rw [nat_beq_self cfiId]
  dsimp only
  rw [h1]
  unfold xfiWriteAllocMem
  dsimp only
  rw [hBounds]
  dsimp only [xfiRet]
  exact ⟨rfl, rfl, rfl⟩

/-!
### 3.2 Confused-Deputy Kernel API Calls & In-Sandbox Kernel Object Corruption
(Castro et al., BGI SOSP 2009 §2–§3; Mao et al., LXFI SOSP 2011 §1–§3)

Why XFI (SFI + Scoped Stack + Inline CFI) is STILL insufficient for monolithic
kernel extensions (Windows WDM / Linux drivers):
1. **In-Sandbox Kernel Object Corruption (BGI):** Kernel drivers allocate kernel
   synchronization/IPC objects (`KEVENT`, `KDPC`, `spinlock_t`) directly inside
   their own writable allocation stack or module heap (`[allocLow, allocHigh)`).
   After calling `KeInitializeEvent(evPtr)`, an XFI-confined driver can use a
   normal in-sandbox store to overwrite `evPtr->flink = &current->cred->uid` or
   free the memory containing the active `KDPC`!
2. **Confused-Deputy Support Routines (LXFI):** An XFI-confined driver can invoke
   a legitimate, CFI-valid kernel support routine such as `spin_lock_init(ptr)`
   passing `ptr = &current->cred->uid`. Because `spin_lock_init` executes inside
   the trusted kernel (outside the module's inline SFI checks), the kernel
   zeroes `current->cred->uid` (`uid = 0` root privilege escalation)!
-/

inductive KernelObjType where
  | kEvent
  | kDpc
  | spinLock
  deriving DecidableEq, Repr

/--
  BGI per-slot access right (`dright` in Castro et al., SOSP 2009, §3.1–3.3):
  - `rwModule`: driver has direct byte-write access to this slot.
  - `kernelOwned`: kernel data (e.g., `current->cred->uid`); driver has NO write
    or capability access.
  - `typedKernelObj t`: slot sits in the driver's memory space, but has been
    initialized as a live kernel object of type `t` via `SetType`; BGI revokes
    direct byte-write permission (`rwModule`) so neither the driver nor stack
    deallocation (`_BGI_slowRevokeAccess`) can corrupt or free it until the
    kernel destructor clears the type!
-/
inductive BgiSlotRight where
  | rwModule
  | kernelOwned
  | typedKernelObj (objType : KernelObjType)
  deriving DecidableEq, Repr

/--
  State of a driver + core kernel interaction comparing:
  - Raw XFI (checks only `allocLow ≤ addr < allocHigh` on direct driver stores,
    and checks only `cfiValid` when calling kernel support routines), vs
  - BGI + LXFI (enforces per-slot `BgiSlotRight` typestate on stores/frees and
    LXFI capability-proxy preconditions on kernel API calls).
-/
structure KernelApiState where
  allocLow       : Nat
  allocHigh      : Nat
  kernelUidAddr  : Nat
  eventSlotAddr  : Nat
  mem            : Nat → Nat
  slotRights     : Nat → BgiSlotRight
  securityFault  : Bool

/--
  Under XFI alone, calling the legitimate CFI-valid kernel support routine
  `spin_lock_init(ptr)` passes CFI and executes in the trusted kernel, which
  writes `0` to `*ptr` without checking whether the calling module principal
  owns `ptr` (`WRITE(ptr, sizeof(spinlock_t))` in LXFI §2.2).
-/
def xfiOnlySpinLockInit (s : KernelApiState) (ptr : Nat) : KernelApiState :=
  { s with mem := fun a => if a == ptr then 0 else s.mem a }

/--
  Under XFI alone, after `KeInitializeEvent(eventSlotAddr)` initializes an event
  located inside the driver's own allocation stack (`allocLow ≤ eventSlotAddr < allocHigh`),
  the driver can still directly overwrite `eventSlotAddr` via `xfiWriteAllocMem`
  because `eventSlotAddr` lies within `[allocLow, allocHigh)`!
-/
def xfiOnlyDirectDriverStore (s : KernelApiState) (addr val : Nat) : KernelApiState :=
  if s.allocLow ≤ addr && addr < s.allocHigh then
    { s with mem := fun a => if a == addr then val else s.mem a }
  else
    { s with securityFault := true }

/--
  **Counterexample 3B (`xfi_confused_deputy_and_in_sandbox_object_corruption`):**
  Demonstrates both attacks against an XFI-confined driver:
  1. Calling `xfiOnlySpinLockInit s s.kernelUidAddr` overwrites `kernelUidAddr`
     from `1000` (unprivileged user) to `0` (`root`), even though `kernelUidAddr`
     is outside `[allocLow, allocHigh)`!
  2. Overwriting `eventSlotAddr` (an active `kEvent` located inside `[allocLow, allocHigh)`)
     via `xfiOnlyDirectDriverStore` succeeds without faulting, corrupting the
     kernel event's internal wait-list pointer to `0xdeadbeef`!
-/
theorem xfi_confused_deputy_and_in_sandbox_object_corruption :
    let init : KernelApiState := {
      allocLow := 0x20000000
      allocHigh := 0x21000000
      kernelUidAddr := 0x80001000
      eventSlotAddr := 0x20000100
      mem := fun a =>
        if a == 0x80001000 then 1000
        else if a == 0x20000100 then 0x80005000 -- valid kernel list pointer
        else 0
      slotRights := fun a =>
        if a == 0x80001000 then .kernelOwned
        else if a == 0x20000100 then .typedKernelObj .kEvent
        else .rwModule
      securityFault := false
    }
    let afterConfusedDeputy := xfiOnlySpinLockInit init init.kernelUidAddr
    let afterEventCorrupt := xfiOnlyDirectDriverStore init init.eventSlotAddr 0xdeadbeef
    afterConfusedDeputy.mem init.kernelUidAddr = 0 ∧
      afterConfusedDeputy.securityFault = false ∧
      afterEventCorrupt.mem init.eventSlotAddr = 0xdeadbeef ∧
      afterEventCorrupt.securityFault = false := by
  decide

/-!
### BGI + LXFI Enforcement Operations
1. `bgiDirectDriverStore`: requires `slotRights addr == .rwModule` (`_BGI_checkWrite`);
   if `addr` holds `.typedKernelObj t` or `.kernelOwned`, the store faults!
2. `bgiLxfiSpinLockInit`: LXFI API proxy checks that the module holds write
   capability on `ptr` (`slotRights ptr == .rwModule`) before initializing the
   spinlock and transitioning `slotRights ptr` via BGI `SetType` to
   `.typedKernelObj .spinLock`.
-/

def updateMem (m : Nat → Nat) (target val a : Nat) : Nat :=
  match a == target with
  | true => val
  | false => m a

def updateSlotRight (sr : Nat → BgiSlotRight) (target : Nat) (r : BgiSlotRight)
    (a : Nat) : BgiSlotRight :=
  match a == target with
  | true => r
  | false => sr a

def bgiDirectDriverStore (s : KernelApiState) (addr val : Nat) : KernelApiState :=
  match s.slotRights addr with
  | .rwModule => { s with mem := updateMem s.mem addr val }
  | .kernelOwned => { s with securityFault := true }
  | .typedKernelObj _ => { s with securityFault := true }

def bgiLxfiSpinLockInit (s : KernelApiState) (ptr : Nat) : KernelApiState :=
  match s.slotRights ptr with
  | .rwModule =>
      { s with
        mem := updateMem s.mem ptr 0
        slotRights := updateSlotRight s.slotRights ptr (.typedKernelObj .spinLock) }
  | .kernelOwned => { s with securityFault := true }
  | .typedKernelObj _ => { s with securityFault := true }

/--
  Kernel integrity invariant protected by BGI + LXFI:
  Every slot whose `slotRights` is `.kernelOwned` or `.typedKernelObj .kEvent`
  retains its uncorrupted kernel value under all direct driver stores and
  confused-deputy `spin_lock_init` calls.
-/
def KernelObjectIntegrityInv (sInit sCur : KernelApiState) : Prop :=
  (∀ a, sInit.slotRights a = .kernelOwned →
    sCur.mem a = sInit.mem a ∧ sCur.slotRights a = .kernelOwned) ∧
  (∀ a, sInit.slotRights a = .typedKernelObj .kEvent →
    sCur.mem a = sInit.mem a ∧ sCur.slotRights a = .typedKernelObj .kEvent)

/--
  **Theorem 3.2 (`bgiDirectDriverStore_preserves_integrity` &
  `bgiLxfiSpinLockInit_preserves_integrity`):**
  Both `bgiDirectDriverStore` and `bgiLxfiSpinLockInit` preserve
  `KernelObjectIntegrityInv` for all untrusted addresses `addr` and values `val`:
  neither direct driver stores (even to the driver's own stack/heap where an
  active `kEvent` resides) nor confused-deputy `spin_lock_init` calls can ever
  mutate `.kernelOwned` memory or corrupt an initialized `.typedKernelObj .kEvent`!
-/
theorem bgiDirectDriverStore_preserves_integrity
    (sInit sCur : KernelApiState) (addr val : Nat)
    (hInv : KernelObjectIntegrityInv sInit sCur) :
    KernelObjectIntegrityInv sInit (bgiDirectDriverStore sCur addr val) := by
  unfold bgiDirectDriverStore
  cases hRight : sCur.slotRights addr with
  | kernelOwned => exact hInv
  | typedKernelObj _ => exact hInv
  | rwModule =>
    constructor
    · intro a ha
      have ⟨hMem, hSlot⟩ := hInv.1 a ha
      refine ⟨?_, hSlot⟩
      dsimp only [updateMem]
      cases hEq : (a == addr) with
      | false => exact hMem
      | true =>
        have hEq' : a = addr := beq_iff_eq.mp hEq
        subst hEq'
        rw [hSlot] at hRight
        contradiction
    · intro a ha
      have ⟨hMem, hSlot⟩ := hInv.2 a ha
      refine ⟨?_, hSlot⟩
      dsimp only [updateMem]
      cases hEq : (a == addr) with
      | false => exact hMem
      | true =>
        have hEq' : a = addr := beq_iff_eq.mp hEq
        subst hEq'
        rw [hSlot] at hRight
        contradiction

theorem bgiLxfiSpinLockInit_preserves_integrity
    (sInit sCur : KernelApiState) (ptr : Nat)
    (hInv : KernelObjectIntegrityInv sInit sCur) :
    KernelObjectIntegrityInv sInit (bgiLxfiSpinLockInit sCur ptr) := by
  unfold bgiLxfiSpinLockInit
  cases hRight : sCur.slotRights ptr with
  | kernelOwned => exact hInv
  | typedKernelObj _ => exact hInv
  | rwModule =>
    constructor
    · intro a ha
      have ⟨hMem, hSlot⟩ := hInv.1 a ha
      dsimp only [updateMem, updateSlotRight]
      cases hEq : (a == ptr) with
      | false => exact ⟨hMem, hSlot⟩
      | true =>
        have hEq' : a = ptr := beq_iff_eq.mp hEq
        subst hEq'
        rw [hSlot] at hRight
        contradiction
    · intro a ha
      have ⟨hMem, hSlot⟩ := hInv.2 a ha
      dsimp only [updateMem, updateSlotRight]
      cases hEq : (a == ptr) with
      | false => exact ⟨hMem, hSlot⟩
      | true =>
        have hEq' : a = ptr := beq_iff_eq.mp hEq
        subst hEq'
        rw [hSlot] at hRight
        contradiction

end Layer3_XfiBgiLxfi

/-!
===============================================================================
LAYER 4: VINO Transactional Kernel Graft Compensation & Lock Release
(Seltzer, Endo, Small & Smith, OSDI 1996, §2.2, §3.1–§3.2)
===============================================================================
-/
namespace Layer4_VinoTransactionalGrafts

/-!
### Why Layer 1 + Layer 2 + Layer 3 Still Fail When an In-Kernel Extension Aborts
As Seltzer et al. (OSDI 1996, §2.2 & §3.1) show, an in-kernel extension (graft)
that obeys all SFI, CFI, and capability-checked kernel API rules must still
acquire contested kernel locks and invoke legitimate kernel mutators that update
shared kernel data structures across multiple steps. If the extension:
1. Faults mid-operation (e.g., SFI/BGI trap, null dereference), OR
2. Hoards a contested lock (`lock(resourceA); while(1);`) and is preempted when
   another kernel thread times out waiting for `resourceA`,
simply terminating the extension leaves kernel locks permanently held (deadlock)
and leaves multi-part kernel state half-mutated (violating global kernel
invariants).

VINO solves this by wrapping every graft invocation in an in-memory **ACI
transaction** (Atomicity, Consistency, Isolation) using **two-phase locking**
and a **LIFO compensating undo-function stack** (`undoStack`).
-/

abbrev LockId := Nat

/--
  Authoritative shared kernel state manipulated via legitimate kernel accessors:
  - `lockHeld`: whether each contested kernel lock is currently held;
  - `primaryTable`: primary kernel resource table (e.g., open file / buffer table);
  - `shadowAccounting`: paired kernel accounting counter that MUST equal the sum
    or state of `primaryTable` at transaction boundaries (`primaryTable == shadowAccounting`).
-/
structure SharedKernelState where
  lockHeld         : LockId → Bool
  primaryTable     : Nat
  shadowAccounting : Nat

/--
  **Global Kernel Quiescent Invariant (`KernelQuiescentInv`):**
  When no graft transaction is active:
  1. `primaryTable = shadowAccounting` (structural consistency across paired
     kernel data structures);
  2. `∀ l, lockHeld l = false` (no dangling contested locks held by dead/aborted
     grafts).
-/
structure KernelQuiescentInv (k : SharedKernelState) : Prop where
  consistent : k.primaryTable = k.shadowAccounting
  locksFree  : ∀ l, k.lockHeld l = false

/--
  Legitimate, capability-checked kernel mutator operations invoked by a graft.
  Notice that updating a complex kernel subsystem requires multiple legitimate
  accessor calls (`acquireLock`, `addPrimaryTable`, `addShadowAccounting`,
  `releaseLock`) before the global invariant is re-established at commit!
-/
inductive KernelMutatorOp where
  | acquireLock (l : LockId)
  | addPrimaryTable (delta : Nat)
  | subPrimaryTable (delta : Nat)
  | addShadowAccounting (delta : Nat)
  | subShadowAccounting (delta : Nat)
  deriving DecidableEq, Repr

def updateLockMap (lm : LockId → Bool) (target : LockId) (val : Bool)
    (x : LockId) : Bool :=
  match x == target with
  | true => val
  | false => lm x

/-- Forward execution of a single legitimate kernel mutator on `SharedKernelState`. -/
def applyMutator (op : KernelMutatorOp) (k : SharedKernelState) : SharedKernelState :=
  match op with
  | .acquireLock l =>
      { k with lockHeld := updateLockMap k.lockHeld l true }
  | .addPrimaryTable d =>
      { k with primaryTable := k.primaryTable + d }
  | .subPrimaryTable d =>
      { k with primaryTable := k.primaryTable - d }
  | .addShadowAccounting d =>
      { k with shadowAccounting := k.shadowAccounting + d }
  | .subShadowAccounting d =>
      { k with shadowAccounting := k.shadowAccounting - d }

/--
  **Counterexample 4A (`sfi_cfi_api_abort_without_undo_deadlocks_and_corrupts`):**
  Suppose the kernel starts in `initKernelExample` satisfying `KernelQuiescentInv`.
  A grafted extension legitimately calls:
    1. `acquireLock 1` (acquires contested kernel lock 1), and
    2. `addPrimaryTable 50` (first half of a paired kernel state update),
  and then aborts (due to an SFI/BGI trap on its next instruction or a VINO
  resource-lock timeout before calling `addShadowAccounting 50` and releasing
  lock 1).
  Without transactional undo rollback, the resulting kernel state:
  - Still holds `lockHeld 1 = true` (permanent deadlock for all waiting threads), AND
  - Has `primaryTable = 150 ≠ 100 = shadowAccounting` (corrupted kernel invariant)!
-/
def initKernelExample : SharedKernelState :=
  { lockHeld := fun _ => false, primaryTable := 100, shadowAccounting := 100 }

theorem sfi_cfi_api_abort_without_undo_deadlocks_and_corrupts :
    let k1 := applyMutator (.acquireLock 1) initKernelExample
    let kAborted := applyMutator (.addPrimaryTable 50) k1
    kAborted.lockHeld 1 = true ∧
      kAborted.primaryTable ≠ kAborted.shadowAccounting := by
  decide

/-!
### VINO Compensating Undo-Call Stack & Two-Phase Locking Model
In VINO (Seltzer et al., OSDI 1996, §3.1.2 "Implementation of Graft
Transactions"), every kernel mutator routine invoked inside a graft transaction
pushes a compensating undo record onto the thread's LIFO transaction undo stack
and records any newly acquired lock in the transaction's two-phase lock table.
-/

/-- Compensating undo entry pushed onto VINO's transaction undo call stack. -/
inductive VinoUndoEntry where
  | restoreLock (l : LockId) (prevHeld : Bool)
  | restorePrimaryTable (prevVal : Nat)
  | restoreShadowAccounting (prevVal : Nat)
  deriving DecidableEq, Repr

/-- Execute a single VINO compensating undo function. -/
def applyUndoEntry (u : VinoUndoEntry) (k : SharedKernelState) : SharedKernelState :=
  match u with
  | .restoreLock l prevHeld =>
      { k with lockHeld := updateLockMap k.lockHeld l prevHeld }
  | .restorePrimaryTable prevVal =>
      { k with primaryTable := prevVal }
  | .restoreShadowAccounting prevVal =>
      { k with shadowAccounting := prevVal }

/--
  Generate the compensating undo entry for `op` given pre-operation state `k`.
-/
def makeUndoEntry (op : KernelMutatorOp) (k : SharedKernelState) : VinoUndoEntry :=
  match op with
  | .acquireLock l         => .restoreLock l (k.lockHeld l)
  | .addPrimaryTable _     => .restorePrimaryTable k.primaryTable
  | .subPrimaryTable _     => .restorePrimaryTable k.primaryTable
  | .addShadowAccounting _ => .restoreShadowAccounting k.shadowAccounting
  | .subShadowAccounting _ => .restoreShadowAccounting k.shadowAccounting

/--
  VINO active graft transaction state: wraps `SharedKernelState` together with
  the LIFO `undoStack` of compensating calls.
-/
structure VinoTxState where
  kernel    : SharedKernelState
  undoStack : List VinoUndoEntry

/-- Execute a kernel mutator inside a VINO transaction, pushing its undo entry. -/
def vinoExecStep (op : KernelMutatorOp) (tx : VinoTxState) : VinoTxState :=
  let u := makeUndoEntry op tx.kernel
  { kernel := applyMutator op tx.kernel
    undoStack := u :: tx.undoStack }

/-- Execute a list of kernel mutators inside a VINO transaction. -/
def vinoExecTrace : List KernelMutatorOp → VinoTxState → VinoTxState
  | [], tx => tx
  | op :: ops, tx => vinoExecTrace ops (vinoExecStep op tx)

/-- VINO transaction abort handler: unwinds the LIFO `undoStack` in order. -/
def vinoRollback : List VinoUndoEntry → SharedKernelState → SharedKernelState
  | [], k => k
  | u :: us, k => vinoRollback us (applyUndoEntry u k)

/-- Pointwise observational equivalence of `SharedKernelState`. -/
def KernelStateEq (k1 k2 : SharedKernelState) : Prop :=
  k1.primaryTable = k2.primaryTable ∧
  k1.shadowAccounting = k2.shadowAccounting ∧
  ∀ l, k1.lockHeld l = k2.lockHeld l

theorem kernelStateEq_refl (k : SharedKernelState) : KernelStateEq k k :=
  ⟨rfl, rfl, fun _ => rfl⟩

theorem kernelStateEq_trans {k1 k2 k3 : SharedKernelState}
    (h12 : KernelStateEq k1 k2) (h23 : KernelStateEq k2 k3) :
    KernelStateEq k1 k3 :=
  ⟨Eq.trans h12.1 h23.1,
   Eq.trans h12.2.1 h23.2.1,
   fun l => Eq.trans (h12.2.2 l) (h23.2.2 l)⟩

/--
  Single-step exact inversion lemma: applying `makeUndoEntry op k` immediately
  after `applyMutator op k` restores `k` up to pointwise equality.
-/
theorem applyUndo_applyMutator_cancel (op : KernelMutatorOp) (k : SharedKernelState) :
    KernelStateEq (applyUndoEntry (makeUndoEntry op k) (applyMutator op k)) k := by
  cases op with
  | acquireLock lockId =>
    refine ⟨rfl, rfl, ?_⟩
    intro l
    dsimp only [makeUndoEntry, applyMutator, applyUndoEntry, updateLockMap]
    cases hEq : (l == lockId) with
    | false => rfl
    | true =>
      have hEq' : l = lockId := beq_iff_eq.mp hEq
      subst hEq'
      rfl
  | addPrimaryTable _ => exact ⟨rfl, rfl, fun _ => rfl⟩
  | subPrimaryTable _ => exact ⟨rfl, rfl, fun _ => rfl⟩
  | addShadowAccounting _ => exact ⟨rfl, rfl, fun _ => rfl⟩
  | subShadowAccounting _ => exact ⟨rfl, rfl, fun _ => rfl⟩

theorem applyUndoEntry_congr (u : VinoUndoEntry) {k1 k2 : SharedKernelState}
    (hEq : KernelStateEq k1 k2) :
    KernelStateEq (applyUndoEntry u k1) (applyUndoEntry u k2) := by
  cases u with
  | restoreLock l prevHeld =>
    refine ⟨hEq.1, hEq.2.1, ?_⟩
    intro x
    dsimp only [applyUndoEntry, updateLockMap]
    cases (x == l) with
    | true => rfl
    | false => exact hEq.2.2 x
  | restorePrimaryTable prevVal =>
    exact ⟨rfl, hEq.2.1, hEq.2.2⟩
  | restoreShadowAccounting prevVal =>
    exact ⟨hEq.1, rfl, hEq.2.2⟩

theorem vinoRollback_congr (us : List VinoUndoEntry) {k1 k2 : SharedKernelState}
    (hEq : KernelStateEq k1 k2) :
    KernelStateEq (vinoRollback us k1) (vinoRollback us k2) := by
  induction us generalizing k1 k2 with
  | nil => exact hEq
  | cons u rest ih =>
    unfold vinoRollback
    exact ih (applyUndoEntry_congr u hEq)

/--
  **Theorem 4.1 (`vinoRollback_execTrace_exact`):**
  For ANY sequence `ops : List KernelMutatorOp` executed by an in-kernel graft
  starting from transaction state `tx`, unwinding the resulting LIFO undo stack
  via `vinoRollback` produces a kernel state equivalent to `vinoRollback tx.undoStack tx.kernel`.
-/
theorem vinoRollback_execTrace_exact (ops : List KernelMutatorOp) (tx : VinoTxState) :
    KernelStateEq
      (vinoRollback (vinoExecTrace ops tx).undoStack (vinoExecTrace ops tx).kernel)
      (vinoRollback tx.undoStack tx.kernel) := by
  induction ops generalizing tx with
  | nil =>
    exact kernelStateEq_refl _
  | cons op rest ih =>
    unfold vinoExecTrace
    have hStep := ih (vinoExecStep op tx)
    unfold vinoExecStep at hStep
    dsimp only [vinoRollback] at hStep
    have hCancel := applyUndo_applyMutator_cancel op tx.kernel
    have hCongr := vinoRollback_congr tx.undoStack hCancel
    exact kernelStateEq_trans hStep hCongr

/--
  **Theorem 4.2 (`vino_transaction_abort_restores_quiescent_invariant`):**
  If the kernel satisfies `KernelQuiescentInv kInit` when a graft transaction
  begins (`undoStack = []`), and the graft executes ANY arbitrary sequence `ops`
  of lock acquisitions and partial state mutations before faulting or timing out,
  VINO's LIFO compensating transaction rollback (`vinoRollback`) is guaranteed to
  restore `KernelQuiescentInv` (`primaryTable = shadowAccounting` and all locks
  released: `∀ l, lockHeld l = false`)!
-/
theorem vino_transaction_abort_restores_quiescent_invariant
    (kInit : SharedKernelState) (ops : List KernelMutatorOp)
    (hInit : KernelQuiescentInv kInit) :
    let txFinal := vinoExecTrace ops { kernel := kInit, undoStack := [] }
    let kRolledBack := vinoRollback txFinal.undoStack txFinal.kernel
    KernelQuiescentInv kRolledBack := by
  intro txFinal kRolledBack
  have hExact := vinoRollback_execTrace_exact ops { kernel := kInit, undoStack := [] }
  dsimp only [vinoRollback] at hExact
  constructor
  · rw [hExact.1, hExact.2.1]
    exact hInit.consistent
  · intro l
    rw [hExact.2.2 l]
    exact hInit.locksFree l

/-!
### 4.2 Four-Way Comparison of Kernel Extension Abort,
Timeout, and Cancellation Recovery
1. **Mode A (Non-unwinding thread kill inside trap handler, e.g., Nebulet
   `pfex_acquire` -> `#PF` -> `Thread::exit()`):** Leaks held kernel spinlocks
   and leaves shared kernel state half-mutated.
2. **Mode B (Linux `__ex_table` landing pad + Rust RAII `Drop` / C cleanup
   `goto`):** Redirects trapping `RIP` inside the kernel helper (`copy_from_user` /
   `fastpath_offset_ptr`) to a fixup landing pad returning `Err(EFAULT)` so
   stack-frame RAII `Drop` guards release held spinlocks cleanly—*provided* no
   shared state was mutated prior to the fallible access (check-before-mutate).
   If shared state was mutated before a subsequent fault or asynchronous timeout,
   RAII lock guards release the lock but leave shared state corrupted.
3. **Mode C (VINO dynamic LIFO compensating `undoStack` + 2PL):** Restores
   arbitrary multi-step shared-state mutations and releases locks on both
   synchronous faults and asynchronous watchdog timeout preemption.
4. **Mode D (`Typechain` PLAS 2020 / Anneal `SafeProgram` static exceptionless +
   bounded-resource admission):** Statically proves in-bounds memory access
   (`Exceptionless`) and bounded execution fuel (`ResourceBounded`), eliminating
   runtime trap/timeout aborts and undo-log overhead altogether.
-/

/--
  **Mode A (`execModeA_NonUnwindingTrapKill`):**
  Acquires spinlock `l`, then performs a fallible memory access (`addr < memBound`).
  If `addr ≥ memBound` triggers `#PF`, the trap handler kills the thread
  directly (`Thread::exit()`) without unwinding the stack or releasing `l`.
-/
def execModeA_NonUnwindingTrapKill (k : SharedKernelState) (l : LockId)
    (addr memBound delta : Nat) : SharedKernelState :=
  let kLocked := { k with lockHeld := updateLockMap k.lockHeld l true }
  match decide (addr < memBound) with
  | false =>
      kLocked
  | true =>
      let kMut := { kLocked with
        primaryTable := kLocked.primaryTable + delta
        shadowAccounting := kLocked.shadowAccounting + delta }
      { kMut with lockHeld := updateLockMap kMut.lockHeld l false }

/--
  **Theorem 4.3 (`modeA_trap_kill_leaks_lock`):**
  When `decide (addr < memBound) = false`, Mode A permanently leaks spinlock `l`
  (`lockHeld l = true`), deadlocking the kernel even when no shared-state
  mutation occurred prior to the fault!
-/
theorem modeA_trap_kill_leaks_lock (k : SharedKernelState) (l : LockId)
    (addr memBound delta : Nat)
    (hOob : decide (addr < memBound) = false) :
    (execModeA_NonUnwindingTrapKill k l addr memBound delta).lockHeld l = true := by
  unfold execModeA_NonUnwindingTrapKill
  dsimp only
  rw [hOob]
  dsimp only [updateLockMap]
  rw [nat_beq_self l]

/--
  **Mode B, Pattern 1 (`execModeB_CheckBeforeMutate`):**
  Acquires spinlock `l` via an RAII `SpinLockGuard`, performs the fallible
  access (`addr < memBound`) via an `__ex_table`-protected helper *before*
  mutating shared state, and on `#PF` (`false`) returns `Err(EFAULT)` through
  the landing pad so `SpinLockGuard::drop` releases `l`.
-/
def execModeB_CheckBeforeMutate (k : SharedKernelState) (l : LockId)
    (addr memBound delta : Nat) : SharedKernelState :=
  let kLocked := { k with lockHeld := updateLockMap k.lockHeld l true }
  match decide (addr < memBound) with
  | false =>
      { kLocked with lockHeld := updateLockMap kLocked.lockHeld l false }
  | true =>
      let kMut := { kLocked with
        primaryTable := kLocked.primaryTable + delta
        shadowAccounting := kLocked.shadowAccounting + delta }
      { kMut with lockHeld := updateLockMap kMut.lockHeld l false }

/--
  **Theorem 4.4 (`modeB_check_before_mutate_always_quiescent`):**
  When all fallible accesses precede shared-state mutations (check-before-mutate),
  `__ex_table` landing pads + RAII `Drop` preserve `KernelQuiescentInv` on both
  normal execution and `#PF` faults!
-/
theorem modeB_check_before_mutate_always_quiescent (k : SharedKernelState) (l : LockId)
    (addr memBound delta : Nat) (hInit : KernelQuiescentInv k) :
    KernelQuiescentInv (execModeB_CheckBeforeMutate k l addr memBound delta) := by
  unfold execModeB_CheckBeforeMutate
  dsimp only
  cases decide (addr < memBound) with
  | false =>
    dsimp only
    constructor
    · exact hInit.consistent
    · intro x
      dsimp only [updateLockMap]
      cases (x == l) with
      | true => rfl
      | false => exact hInit.locksFree x
  | true =>
    dsimp only
    constructor
    · rw [hInit.consistent]
    · intro x
      dsimp only [updateLockMap]
      cases (x == l) with
      | true => rfl
      | false => exact hInit.locksFree x

/--
  **Mode B, Pattern 2 (`execModeB_MutateBeforeFault`):**
  Acquires spinlock `l`, mutates `primaryTable` (`+ delta`), and then faults on
  a second fallible access (`addr2 ≥ memBound`). Even though `__ex_table` + RAII
  `Drop` releases spinlock `l`, `primaryTable` is NOT rolled back!
-/
def execModeB_MutateBeforeFault (k : SharedKernelState) (l : LockId)
    (addr2 memBound delta : Nat) : SharedKernelState :=
  let kLocked := { k with lockHeld := updateLockMap k.lockHeld l true }
  let kHalfMut := { kLocked with primaryTable := kLocked.primaryTable + delta }
  match decide (addr2 < memBound) with
  | false =>
      { kHalfMut with lockHeld := updateLockMap kHalfMut.lockHeld l false }
  | true =>
      let kFullMut := { kHalfMut with shadowAccounting := kHalfMut.shadowAccounting + delta }
      { kFullMut with lockHeld := updateLockMap kFullMut.lockHeld l false }

/--
  **Theorem 4.5 (`modeB_mutate_before_fault_releases_lock_but_corrupts_state`):**
  If a fault occurs after a partial shared-state mutation, Mode B (`__ex_table`
  + RAII `Drop`) releases the spinlock (`lockHeld 1 = false`) but leaves the
  kernel invariant violated (`primaryTable ≠ shadowAccounting`).
-/
theorem modeB_mutate_before_fault_releases_lock_but_corrupts_state :
    let out := execModeB_MutateBeforeFault initKernelExample 1 0xdeadbeef 0x1000 50
    out.lockHeld 1 = false ∧ out.primaryTable ≠ out.shadowAccounting := by
  decide

/--
  **Mode C (`execModeC_VinoCompensatingUndo2PL`):**
  Wraps lock acquisition and multi-step shared-state mutations in VINO's dynamic
  LIFO `undoStack`. If either a mid-mutation memory fault (`addr2 ≥ memBound`)
  OR an asynchronous watchdog timeout (`fuel == 0`) occurs, `vinoRollback`
  unwinds `undoStack` in LIFO order.
-/
def execModeC_VinoCompensatingUndo2PL (k : SharedKernelState) (l : LockId)
    (addr2 memBound fuel delta : Nat) : SharedKernelState :=
  let tx0 : VinoTxState := { kernel := k, undoStack := [] }
  let tx1 := vinoExecStep (.acquireLock l) tx0
  let tx2 := vinoExecStep (.addPrimaryTable delta) tx1
  match decide (addr2 < memBound) && decide (0 < fuel) with
  | false =>
      vinoRollback tx2.undoStack tx2.kernel
  | true =>
      let kDone := applyMutator (.addShadowAccounting delta) tx2.kernel
      { kDone with lockHeld := updateLockMap kDone.lockHeld l false }

/--
  **Theorem 4.6 (`modeC_vino_always_quiescent`):**
  VINO's LIFO compensating undo stack restores `KernelQuiescentInv` across both
  mid-mutation memory faults (`addr2 ≥ memBound`) and asynchronous watchdog
  timeouts (`fuel = 0`), as well as normal commits!
-/
theorem modeC_vino_always_quiescent (k : SharedKernelState) (l : LockId)
    (addr2 memBound fuel delta : Nat) (hInit : KernelQuiescentInv k) :
    KernelQuiescentInv (execModeC_VinoCompensatingUndo2PL k l addr2 memBound fuel delta) := by
  unfold execModeC_VinoCompensatingUndo2PL
  dsimp only
  cases decide (addr2 < memBound) && decide (0 < fuel) with
  | false =>
    dsimp only [vinoExecStep, makeUndoEntry, applyMutator, vinoRollback, applyUndoEntry]
    constructor
    · exact hInit.consistent
    · intro x
      dsimp only [updateLockMap]
      cases hEq : (x == l) with
      | false => exact hInit.locksFree x
      | true =>
        have hEq' : x = l := beq_iff_eq.mp hEq
        subst hEq'
        exact hInit.locksFree x
  | true =>
    dsimp only [vinoExecStep, applyMutator]
    constructor
    · rw [hInit.consistent]
    · intro x
      dsimp only [updateLockMap]
      cases (x == l) with
      | true => rfl
      | false => exact hInit.locksFree x

/--
  **Mode D (`StaticAdmissionCert` & `execModeD_StaticAdmission`, `Typechain`
  PLAS 2020 / Anneal `SafeProgram`):**
  Compile-time certificate proving that all memory accesses are in-bounds
  (`Exceptionless`) and execution fuel is sufficient (`ResourceBounded`).
-/
structure StaticAdmissionCert (addr memBound fuel : Nat) : Prop where
  inBounds    : decide (addr < memBound) = true
  fuelBounded : decide (0 < fuel) = true

structure ModeDResult where
  kernel  : SharedKernelState
  aborted : Bool

def execModeD_StaticAdmission (k : SharedKernelState) (l : LockId)
    (addr memBound fuel delta : Nat) : ModeDResult :=
  let kLocked := { k with lockHeld := updateLockMap k.lockHeld l true }
  let kHalfMut := { kLocked with primaryTable := kLocked.primaryTable + delta }
  match decide (addr < memBound), decide (0 < fuel) with
  | true, true =>
      let kFull := { kHalfMut with shadowAccounting := kHalfMut.shadowAccounting + delta }
      { kernel := { kFull with lockHeld := updateLockMap kFull.lockHeld l false }
        aborted := false }
  | _, _ =>
      { kernel := kHalfMut, aborted := true }

/--
  **Theorem 4.7 (`modeD_static_admission_never_aborts_and_quiescent`):**
  Any extension admitted with a compile-time `StaticAdmissionCert` never aborts
  at runtime (`aborted = false`) and preserves `KernelQuiescentInv` without
  needing a runtime undo stack.
-/
theorem modeD_static_admission_never_aborts_and_quiescent
    (k : SharedKernelState) (l : LockId) (addr memBound fuel delta : Nat)
    (hInit : KernelQuiescentInv k)
    (hCert : StaticAdmissionCert addr memBound fuel) :
    (execModeD_StaticAdmission k l addr memBound fuel delta).aborted = false ∧
      KernelQuiescentInv (execModeD_StaticAdmission k l addr memBound fuel delta).kernel := by
  unfold execModeD_StaticAdmission
  rw [hCert.inBounds, hCert.fuelBounded]
  refine ⟨rfl, ?_⟩
  constructor
  · rw [hInit.consistent]
  · intro x
    dsimp only [updateLockMap]
    cases (x == l) with
    | true => rfl
    | false => exact hInit.locksFree x

/--
  **Theorem 4.8 (`four_mode_extension_recovery_comparison`):**
  Unified four-way comparison across Modes A, B, C, and D:
  1. Mode A leaks held spinlocks on out-of-bounds `#PF` (`lockHeld = true`);
  2. Mode B (`__ex_table` + RAII `Drop`) preserves `KernelQuiescentInv` under
     check-before-mutate, but leaves `primaryTable ≠ shadowAccounting` if a
     fault occurs after a partial mutation;
  3. Mode C (VINO LIFO `undoStack` + 2PL) preserves `KernelQuiescentInv` across
     both mid-mutation faults and asynchronous watchdog timeouts;
  4. Mode D (`StaticAdmissionCert`) proves `aborted = false` and preserves
     `KernelQuiescentInv` statically without runtime undo logs.
-/
theorem four_mode_extension_recovery_comparison
    (k : SharedKernelState) (l : LockId)
    (addrOob addrOk memBound fuelOk fuelZero delta : Nat)
    (hInit : KernelQuiescentInv k)
    (hOob : decide (addrOob < memBound) = false)
    (hCert : StaticAdmissionCert addrOk memBound fuelOk) :
    (execModeA_NonUnwindingTrapKill k l addrOob memBound delta).lockHeld l = true ∧
    KernelQuiescentInv (execModeB_CheckBeforeMutate k l addrOob memBound delta) ∧
    (let outB2 := execModeB_MutateBeforeFault initKernelExample 1 0xdeadbeef 0x1000 50
     outB2.lockHeld 1 = false ∧ outB2.primaryTable ≠ outB2.shadowAccounting) ∧
    KernelQuiescentInv (execModeC_VinoCompensatingUndo2PL k l addrOob memBound fuelZero delta) ∧
    ((execModeD_StaticAdmission k l addrOk memBound fuelOk delta).aborted = false ∧
      KernelQuiescentInv (execModeD_StaticAdmission k l addrOk memBound fuelOk delta).kernel) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact modeA_trap_kill_leaks_lock k l addrOob memBound delta hOob
  · exact modeB_check_before_mutate_always_quiescent k l addrOob memBound delta hInit
  · exact modeB_mutate_before_fault_releases_lock_but_corrupts_state
  · exact modeC_vino_always_quiescent k l addrOob memBound fuelZero delta hInit
  · exact modeD_static_admission_never_aborts_and_quiescent k l addrOk memBound fuelOk delta hInit hCert

end Layer4_VinoTransactionalGrafts

/-!
===============================================================================
TOP-LEVEL SYNTHESIS: 4-Layer SFI & Extensible Kernel Boundary Hierarchy
===============================================================================
-/

/--
  **Master Theorem (`foundational_sfi_four_layer_hierarchy`):**
  Synthesizes the complete 4-layer mechanized hierarchy proved across this file:
  1. **Layer 1 (Wahbe & PittSFIeld):** Bitwise address sandboxing confines all
     memory accesses to `[base, base + 2^k)` (`sandboxAddr_bounds`) and
     dedicated-register idempotence protects against mid-sequence jumps
     (`wahbe_dedicated_reg_mid_sequence_safe`), while PittSFIeld's chunk-aligned
     masking (`sandboxCodeAligned_confinement_and_alignment`) prevents variable-length
     CISC mid-instruction jumps (`cisc_unaligned_jump_counterexample`).
  2. **Layer 2 (Exokernel / ASH / XN):** Secure bindings decouple bind-time
     authorization from $O(1)$ use-time checking (`exokernel_secure_binding_equivalence`),
     ASH backward-branch counters bound in-kernel execution (`ash_backward_branch_exhausts_fuel`),
     and XN's differential evaluation of deterministic UDFs (`udfOwns`) on `old`
     and `new` metadata states preserves physical disk block disjointness across
     arbitrary untrusted libFS mutations (`xnAllocMetaA_preserves_inv`,
     `xnDeallocMetaA_preserves_inv`).
  3. **Layer 3 (XFI / BGI / LXFI):** While Layer-1 data sandboxing allows
     intra-sandbox return-address corruption (`layer1_sfi_intra_sandbox_ret_overwrite`),
     XFI's split `ScopedStack` + inline CFI preserves call/return integrity
     (`xfi_scoped_stack_immune_to_alloc_writes`), and BGI's per-slot dynamic
     typestate (`BgiSlotRight`) + LXFI's capability-checking API proxies defeat
     confused-deputy kernel calls and in-sandbox kernel object corruption
     (`bgiDirectDriverStore_preserves_integrity`, `bgiLxfiSpinLockInit_preserves_integrity`).
  4. **Layer 4 (VINO Transactional Grafts):** While SFI + CFI + BGI/LXFI API
     checks still leave the kernel deadlocked and inconsistent if an extension
     aborts while holding locks after partial mutations
     (`sfi_cfi_api_abort_without_undo_deadlocks_and_corrupts`), VINO's LIFO
     compensating undo-call stack and two-phase locking restore the exact
     quiescent kernel invariant upon abort (`vino_transaction_abort_restores_quiescent_invariant`).
-/
theorem foundational_sfi_four_layer_hierarchy
    (base k addr : Nat) (hDisj : base &&& (2 ^ k - 1) = 0)
    (udfOwns : Layer2_ExokernelAshDpfxn.MetadataBlock →
      List Layer2_ExokernelAshDpfxn.PhysBlock)
    (disk : Layer2_ExokernelAshDpfxn.XnDiskState)
    (metaA' : Layer2_ExokernelAshDpfxn.MetadataBlock)
    (b : Layer2_ExokernelAshDpfxn.PhysBlock)
    (hDiskInv : Layer2_ExokernelAshDpfxn.XnOwnershipInv udfOwns disk)
    (sInit sCur : Layer3_XfiBgiLxfi.KernelApiState) (ptr : Nat)
    (hApiInv : Layer3_XfiBgiLxfi.KernelObjectIntegrityInv sInit sCur)
    (kInit : Layer4_VinoTransactionalGrafts.SharedKernelState)
    (ops : List Layer4_VinoTransactionalGrafts.KernelMutatorOp)
    (hQuiescent : Layer4_VinoTransactionalGrafts.KernelQuiescentInv kInit) :
    (base ≤ Layer1_WahbePittSFIeld.sandboxAddr base (2 ^ k - 1) addr ∧
      Layer1_WahbePittSFIeld.sandboxAddr base (2 ^ k - 1) addr < base + 2 ^ k) ∧
    Layer2_ExokernelAshDpfxn.XnOwnershipInv udfOwns
      (Layer2_ExokernelAshDpfxn.xnAllocMetaA udfOwns disk metaA' b) ∧
    Layer3_XfiBgiLxfi.KernelObjectIntegrityInv sInit
      (Layer3_XfiBgiLxfi.bgiLxfiSpinLockInit sCur ptr) ∧
    Layer4_VinoTransactionalGrafts.KernelQuiescentInv
      (let txFinal := Layer4_VinoTransactionalGrafts.vinoExecTrace ops
        { kernel := kInit, undoStack := [] }
       Layer4_VinoTransactionalGrafts.vinoRollback txFinal.undoStack txFinal.kernel) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Layer1_WahbePittSFIeld.sandboxAddr_bounds base k addr hDisj
  · exact Layer2_ExokernelAshDpfxn.xnAllocMetaA_preserves_inv udfOwns disk metaA' b hDiskInv
  · exact Layer3_XfiBgiLxfi.bgiLxfiSpinLockInit_preserves_integrity sInit sCur ptr hApiInv
  · exact Layer4_VinoTransactionalGrafts.vino_transaction_abort_restores_quiescent_invariant
      kInit ops hQuiescent

/-!
### Axiom Verification (`#print axioms`)
Every theorem in `FoundationalSfiKernels` is verified below to ensure
`0 sorryAx`, `0 Classical.choice`, and `0 Lean.ofReduceBool`.
-/
#print axioms Layer1_WahbePittSFIeld.and_two_pow_sub_one_eq_mod
#print axioms Layer1_WahbePittSFIeld.sandboxAddr_and_mask
#print axioms Layer1_WahbePittSFIeld.sandboxAddr_idempotent
#print axioms Layer1_WahbePittSFIeld.sandboxAddr_eq_add
#print axioms Layer1_WahbePittSFIeld.sandboxAddr_bounds
#print axioms Layer1_WahbePittSFIeld.sandboxAddr_satisfies_segmentMatch
#print axioms Layer1_WahbePittSFIeld.wahbe_guard_zone_offset_confinement
#print axioms Layer1_WahbePittSFIeld.pittsfieldSingleAnd_dichotomy
#print axioms Layer1_WahbePittSFIeld.sandboxCodeAligned_confinement_and_alignment
#print axioms Layer1_WahbePittSFIeld.cisc_unaligned_jump_counterexample
#print axioms Layer1_WahbePittSFIeld.non_dedicated_scratch_mid_sequence_escape
#print axioms Layer1_WahbePittSFIeld.wahbe_dedicated_reg_mid_sequence_safe
#print axioms Layer1_WahbePittSFIeld.pittsfield_inplace_ret_toctou_race
#print axioms Layer2_ExokernelAshDpfxn.exokernel_secure_binding_equivalence
#print axioms Layer2_ExokernelAshDpfxn.ash_backward_branch_exhausts_fuel
#print axioms Layer2_ExokernelAshDpfxn.xnAllocMetaA_preserves_inv
#print axioms Layer2_ExokernelAshDpfxn.xnWriteMetaA_preserves_inv
#print axioms Layer2_ExokernelAshDpfxn.xnDeallocMetaA_preserves_inv
#print axioms Layer2_ExokernelAshDpfxn.xn_nondeterministic_udf_breaks_disjointness
#print axioms Layer2_ExokernelAshDpfxn.xnInitGeneralDisk_satisfies_inv
#print axioms Layer2_ExokernelAshDpfxn.xnGeneralStep_preserves_disjoint_inv
#print axioms Layer2_ExokernelAshDpfxn.xnGeneralTrace_preserves_disjoint_inv
#print axioms Layer2_ExokernelAshDpfxn.xn_udf_write_catches_silent_block_drop
#print axioms Layer2_ExokernelAshDpfxn.xn_differential_determinism_intra_libos_boundary
#print axioms Layer3_XfiBgiLxfi.layer1_sfi_intra_sandbox_ret_overwrite
#print axioms Layer3_XfiBgiLxfi.xfi_scoped_stack_immune_to_alloc_writes
#print axioms Layer3_XfiBgiLxfi.xfi_call_write_ret_exact
#print axioms Layer3_XfiBgiLxfi.xfi_confused_deputy_and_in_sandbox_object_corruption
#print axioms Layer3_XfiBgiLxfi.bgiDirectDriverStore_preserves_integrity
#print axioms Layer3_XfiBgiLxfi.bgiLxfiSpinLockInit_preserves_integrity
#print axioms Layer4_VinoTransactionalGrafts.sfi_cfi_api_abort_without_undo_deadlocks_and_corrupts
#print axioms Layer4_VinoTransactionalGrafts.vinoRollback_execTrace_exact
#print axioms Layer4_VinoTransactionalGrafts.vino_transaction_abort_restores_quiescent_invariant
#print axioms Layer4_VinoTransactionalGrafts.modeA_trap_kill_leaks_lock
#print axioms Layer4_VinoTransactionalGrafts.modeB_check_before_mutate_always_quiescent
#print axioms Layer4_VinoTransactionalGrafts.modeB_mutate_before_fault_releases_lock_but_corrupts_state
#print axioms Layer4_VinoTransactionalGrafts.modeC_vino_always_quiescent
#print axioms Layer4_VinoTransactionalGrafts.modeD_static_admission_never_aborts_and_quiescent
#print axioms Layer4_VinoTransactionalGrafts.four_mode_extension_recovery_comparison
#print axioms foundational_sfi_four_layer_hierarchy

end FoundationalSfiKernels
