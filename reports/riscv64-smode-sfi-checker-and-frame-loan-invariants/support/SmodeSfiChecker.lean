/-!
# Certificate-free S-mode `RV64IM` SFI checker and soundness

Standalone Lean `v4.34.1` file (core library only; no Mathlib, no `sorry`, no
`axiom`, no `native_decide`, no `bv_decide`).

The file models a deliberately small fragment of the `RV64IM` unprivileged ISA
executing *natively in S-mode* with no hardware protection around it (every
address is readable and writable; the only architectural failures are
synchronous exceptions), a stateless per-instruction admission checker, and
proves:

* `safe_and_terminates` — an admitted module, entered under the kernel-side
  `Entry` contract, never raises a synchronous exception, never leaves its own
  code except by returning to the caller's `ra`, returns within at most
  `prog.length` executed instructions, preserves every register outside the
  module's temporaries, and leaves every byte outside its two sandbox regions
  unchanged.
* `sandbox_noninterference` — the module's observable behavior (step count,
  temporaries, sandbox bytes) is a function of its temporaries and sandbox
  bytes only: it does not depend on any other byte of kernel memory nor on
  `ra`, `sp`, `gp`, `tp`, or `s0`–`s11`.
* separating witnesses showing that each load/store/control-flow side
  condition is individually necessary, and the `RV64M` division table.

Register roles (fixed by the kernel calling convention the checker enforces):
`x10` (`a0`) = context base, `x11` (`a1`) = scratch base, `x6` (`t1`) =
dedicated masked index, `x7` (`t2`) = dedicated scratch address, `x1` (`ra`)
= return address; temporaries are `x5`, `x12`–`x17`, `x28`–`x31`.
-/

namespace SmodeSfiChecker

/-- `2^64`: every register value and effective address is reduced modulo it. -/
local notation "W64" => (18446744073709551616 : Nat)

/-! ## 1. Machine state and instruction fragment -/

/-- Machine state. `pc` is the byte offset of the next instruction relative to
the module's load address (address arithmetic modulo `2^64` is translation
invariant, so relative and absolute program counters step identically). -/
structure St where
  pc   : Nat
  regs : Nat → Nat
  mem  : Nat → Nat

inductive AluOp where
  | add | sub | and | or | xor | sll | srl | sra | slt | sltu
  | mul | div | divu | rem | remu | divw | divuw | remw | remuw
  deriving DecidableEq, Repr

inductive Cond where
  | eq | ne | lt | ge | ltu | geu
  deriving DecidableEq, Repr

/-- Decoded instruction. Immediate fields hold the *raw* encoded bit field
(`imm12 < 4096`, `off13 < 8192`, `off21 < 2097152`); sign extension happens in
the semantics, exactly as in hardware. `system` stands for every encoding of
major opcode `SYSTEM` (`ecall`, `ebreak`, `sret`, `mret`, `wfi`,
`sfence.vma`, all `csr*`); `other` stands for every remaining encoding
(illegal, `auipc`, `fence`/`fence.i`, `A`/`F`/`D`/`C`, unmodeled `M`/`W`
forms). -/
inductive Instr where
  | aluI   (f : AluOp) (rd rs1 imm12 : Nat)
  | alu3   (f : AluOp) (rd rs1 rs2 : Nat)
  | lui    (rd imm20 : Nat)
  | load   (w : Nat) (sgn : Bool) (rd rs1 imm12 : Nat)
  | store  (w : Nat) (rs2 rs1 imm12 : Nat)
  | branch (c : Cond) (rs1 rs2 off13 : Nat)
  | jal    (rd off21 : Nat)
  | jalr   (rd rs1 imm12 : Nat)
  | system (word : Nat)
  | other  (word : Nat)
  deriving DecidableEq, Repr

inductive Trap where
  | illegal | privileged | loadMisaligned | storeMisaligned | instrMisaligned | pcOutside
  deriving DecidableEq, Repr

/-- Outcome of one step: continue inside the module, leave it through `jalr`
to `target`, or raise a synchronous exception / fall outside the module. -/
inductive Out where
  | next (s : St)
  | ret  (target : Nat) (s : St)
  | trap (t : Trap)

/-! ## 2. Semantics -/

/-- Two's-complement interpretation of a 64-bit pattern. -/
def toS (a : Nat) : Int :=
  if a < 9223372036854775808 then (a : Int) else (a : Int) - 18446744073709551616

/-- 64-bit pattern of an integer. -/
def ofS (i : Int) : Nat := (i % 18446744073709551616).toNat

/-- Two's-complement interpretation of the low 32 bits. -/
def toS32 (a : Nat) : Int :=
  if a % 4294967296 < 2147483648 then ((a % 4294967296 : Nat) : Int)
  else ((a % 4294967296 : Nat) : Int) - 4294967296

/-- Sign-extend the low 32 bits to 64 bits. -/
def sext32 (x : Nat) : Nat :=
  if x % 4294967296 < 2147483648 then x % 4294967296
  else x % 4294967296 + 18446744069414584320

/-- Low 32 bits of an integer. -/
def ofS32 (i : Int) : Nat := (i % 4294967296).toNat

/-- Register-register / register-immediate ALU semantics, including the total
`RV64M` division and remainder operations (they have no trapping case). -/
def aluEval : AluOp → Nat → Nat → Nat
  | .add,  a, b => (a + b) % W64
  | .sub,  a, b => (a + (W64 - b % W64)) % W64
  | .and,  a, b => a &&& b
  | .or,   a, b => a ||| b
  | .xor,  a, b => a ^^^ b
  | .sll,  a, b => (a <<< (b % 64)) % W64
  | .srl,  a, b => a >>> (b % 64)
  | .sra,  a, b => ofS (toS a >>> (b % 64))
  | .slt,  a, b => if toS a < toS b then 1 else 0
  | .sltu, a, b => if a < b then 1 else 0
  | .mul,  a, b => (a * b) % W64
  | .divu, a, b => if b = 0 then 18446744073709551615 else a / b
  | .remu, a, b => if b = 0 then a else a % b
  | .div,  a, b => if b = 0 then 18446744073709551615 else ofS (Int.tdiv (toS a) (toS b))
  | .rem,  a, b => if b = 0 then a else ofS (Int.tmod (toS a) (toS b))
  | .divuw, a, b =>
      sext32 (if b % 4294967296 = 0 then 4294967295 else (a % 4294967296) / (b % 4294967296))
  | .remuw, a, b =>
      sext32 (if b % 4294967296 = 0 then a % 4294967296 else (a % 4294967296) % (b % 4294967296))
  | .divw, a, b =>
      sext32 (if b % 4294967296 = 0 then 4294967295 else ofS32 (Int.tdiv (toS32 a) (toS32 b)))
  | .remw, a, b =>
      sext32 (if b % 4294967296 = 0 then a % 4294967296 else ofS32 (Int.tmod (toS32 a) (toS32 b)))

def condEval : Cond → Nat → Nat → Bool
  | .eq,  a, b => decide (a = b)
  | .ne,  a, b => decide (a ≠ b)
  | .lt,  a, b => decide (toS a < toS b)
  | .ge,  a, b => decide (toS b ≤ toS a)
  | .ltu, a, b => decide (a < b)
  | .geu, a, b => decide (b ≤ a)

/-- Sign-extend a raw 12-bit immediate to a 64-bit pattern. -/
def sext12 (i : Nat) : Nat := if i < 2048 then i else i + (W64 - 4096)
/-- Sign-extend a raw 13-bit branch offset. -/
def sextB (i : Nat) : Nat := if i < 4096 then i else i + (W64 - 8192)
/-- Sign-extend a raw 21-bit jump offset. -/
def sextJ (i : Nat) : Nat := if i < 1048576 then i else i + (W64 - 2097152)

/-- Read register `r` (`x0` reads as zero). -/
def rdReg (s : St) (r : Nat) : Nat := if r = 0 then 0 else s.regs r

/-- Write register `r` (writes to `x0` are discarded). -/
def wrReg (regs : Nat → Nat) (r v : Nat) : Nat → Nat :=
  fun x => if x = r ∧ r ≠ 0 then v else regs x

/-- Little-endian read of `n` bytes at `a`. -/
def readBytes (mem : Nat → Nat) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => mem a % 256 + 256 * readBytes mem (a + 1) n

/-- Little-endian write of the low `n` bytes of `v` at `a`. -/
def writeBytes (mem : Nat → Nat) (a n v : Nat) : Nat → Nat :=
  fun x => if a ≤ x ∧ x < a + n then (v / 256 ^ (x - a)) % 256 else mem x

/-- Zero- or sign-extension of a loaded `w`-byte value. -/
def extLoad (w : Nat) (sgn : Bool) (raw : Nat) : Nat :=
  if sgn = true ∧ 256 ^ w ≤ 2 * raw then raw + (W64 - 256 ^ w) else raw

/-- Effective address of a load/store: `rs1 + sext(imm12)` modulo `2^64`. -/
def eaOf (s : St) (rs1 imm : Nat) : Nat := (rdReg s rs1 + sext12 imm) % W64

/-- Next `pc` of a conditional branch. -/
def brTarget (s : St) (c : Cond) (rs1 rs2 off : Nat) : Nat :=
  if condEval c (rdReg s rs1) (rdReg s rs2) = true then (s.pc + sextB off) % W64
  else (s.pc + 4) % W64

/-- `jalr` target: `(rs1 + sext(imm12)) & ~1`. -/
def jalrTarget (s : St) (rs1 imm : Nat) : Nat := (rdReg s rs1 + sext12 imm) % W64 / 2 * 2

/-- Execute one decoded instruction. A load or store whose effective address
is not naturally aligned is modeled as a trap: this is the conservative reading
of the unprivileged specification, under which the execution environment may
raise an address-misaligned or access-fault exception for such an access. A
taken control transfer to a target that is not four-byte aligned raises
instruction-address-misaligned (`IALIGN = 32`, no `C` extension). -/
def exec (s : St) : Instr → Out
  | .aluI f rd rs1 imm =>
      .next { s with pc := (s.pc + 4) % W64,
                     regs := wrReg s.regs rd (aluEval f (rdReg s rs1) (sext12 imm)) }
  | .alu3 f rd rs1 rs2 =>
      .next { s with pc := (s.pc + 4) % W64,
                     regs := wrReg s.regs rd (aluEval f (rdReg s rs1) (rdReg s rs2)) }
  | .lui rd imm20 =>
      .next { s with pc := (s.pc + 4) % W64, regs := wrReg s.regs rd (sext32 (imm20 * 4096)) }
  | .load w sgn rd rs1 imm =>
      if eaOf s rs1 imm % w = 0 then
        .next { s with pc := (s.pc + 4) % W64,
                       regs := wrReg s.regs rd (extLoad w sgn (readBytes s.mem (eaOf s rs1 imm) w)) }
      else .trap .loadMisaligned
  | .store w rs2 rs1 imm =>
      if eaOf s rs1 imm % w = 0 then
        .next { s with pc := (s.pc + 4) % W64,
                       mem := writeBytes s.mem (eaOf s rs1 imm) w (rdReg s rs2) }
      else .trap .storeMisaligned
  | .branch c rs1 rs2 off =>
      if brTarget s c rs1 rs2 off % 4 = 0 then .next { s with pc := brTarget s c rs1 rs2 off }
      else .trap .instrMisaligned
  | .jal rd off =>
      if (s.pc + sextJ off) % W64 % 4 = 0 then
        .next { s with pc := (s.pc + sextJ off) % W64,
                       regs := wrReg s.regs rd ((s.pc + 4) % W64) }
      else .trap .instrMisaligned
  | .jalr rd rs1 imm =>
      if jalrTarget s rs1 imm % 4 = 0 then
        .ret (jalrTarget s rs1 imm) { s with regs := wrReg s.regs rd ((s.pc + 4) % W64) }
      else .trap .instrMisaligned
  | .system _ => .trap .privileged
  | .other _ => .trap .illegal

/-- Fetch-execute. A misaligned `pc` or a `pc` outside the module is a failure:
natively in S-mode nothing confines control flow to the module. -/
def step (prog : List Instr) (s : St) : Out :=
  if s.pc % 4 = 0 then
    match prog[s.pc / 4]? with
    | some ins => exec s ins
    | none => .trap .pcOutside
  else .trap .instrMisaligned

/-- Run at most `k` steps, stopping at the first return or trap. -/
def run (prog : List Instr) : Nat → St → Out
  | 0, s => .next s
  | k + 1, s =>
    match step prog s with
    | .next s' => run prog k s'
    | o => o

/-! ## 3. The admission checker -/

/-- Kernel policy constants: sizes of the two sandbox regions and the largest
value the dedicated scratch index register may hold. -/
structure Cfg where
  ctxBytes : Nat
  scrBytes : Nat
  idxMask  : Nat

/-- Module temporaries: `t0`, `a2`–`a7`, `t3`–`t6`. -/
def IsTemp (r : Nat) : Prop := r = 5 ∨ (12 ≤ r ∧ r ≤ 17) ∨ (28 ≤ r ∧ r ≤ 31)

instance (r : Nat) : Decidable (IsTemp r) := by unfold IsTemp; infer_instance

/-- Registers whose *value* an instruction may consume as data: `x0`, the
temporaries, and the masked index `x6`. Base and address registers (`x10`,
`x11`, `x7`), `ra`, `sp`, `gp`, `tp`, and `s0`–`s11` are never data operands. -/
def CanRead (r : Nat) : Prop := r = 0 ∨ IsTemp r ∨ r = 6

instance (r : Nat) : Decidable (CanRead r) := by unfold CanRead; infer_instance

/-- Static load/store operand check: natural width, **non-negative** raw
immediate (so sign extension is the identity), immediate a multiple of the
width, and either `imm(x10)` inside the context region or `imm(x7)` inside the
scratch region for every admissible index. -/
def AddrOk (cfg : Cfg) (w rs1 imm : Nat) : Prop :=
  (w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8) ∧ imm < 2048 ∧ imm % w = 0 ∧
  ((rs1 = 10 ∧ imm + w ≤ cfg.ctxBytes) ∨ (rs1 = 7 ∧ cfg.idxMask + imm + w ≤ cfg.scrBytes))

instance (cfg : Cfg) (w rs1 imm : Nat) : Decidable (AddrOk cfg w rs1 imm) := by
  unfold AddrOk; infer_instance

/-- Per-instruction admission predicate for the instruction at index `i` of a
module of `n` instructions. It inspects one instruction and two integers; it
carries no state from one instruction to the next. -/
def OkInstr (cfg : Cfg) (n i : Nat) : Instr → Prop
  | .aluI f rd rs1 imm =>
      i + 1 < n ∧ CanRead rs1 ∧
      (IsTemp rd ∨ (rd = 6 ∧ f = .and ∧ imm < 2048 ∧ imm ≤ cfg.idxMask ∧ imm % 8 = 0))
  | .alu3 f rd rs1 rs2 =>
      i + 1 < n ∧
      ((IsTemp rd ∧ CanRead rs1 ∧ CanRead rs2) ∨ (f = .add ∧ rd = 7 ∧ rs1 = 11 ∧ rs2 = 6))
  | .lui rd _ => i + 1 < n ∧ IsTemp rd
  | .load w _ rd rs1 imm => i + 1 < n ∧ IsTemp rd ∧ AddrOk cfg w rs1 imm
  | .store w rs2 rs1 imm => i + 1 < n ∧ CanRead rs2 ∧ AddrOk cfg w rs1 imm
  | .branch _ rs1 rs2 off =>
      i + 1 < n ∧ CanRead rs1 ∧ CanRead rs2 ∧ 0 < off ∧ off < 4096 ∧ off % 4 = 0 ∧ i + off / 4 < n
  | .jal rd off => rd = 0 ∧ 0 < off ∧ off < 1048576 ∧ off % 4 = 0 ∧ i + off / 4 < n
  | .jalr rd rs1 imm => rd = 0 ∧ rs1 = 1 ∧ imm = 0
  | .system _ => False
  | .other _ => False

instance (cfg : Cfg) (n i : Nat) (ins : Instr) : Decidable (OkInstr cfg n i ins) := by
  cases ins <;> (unfold OkInstr; infer_instance)

/-- Single linear pass over the module. -/
def checkFrom (cfg : Cfg) (n : Nat) : Nat → List Instr → Bool
  | _, [] => true
  | i, ins :: rest => decide (OkInstr cfg n i ins) && checkFrom cfg n (i + 1) rest

/-- The complete admission check: non-empty, at most `2^20` instructions, the
index mask leaves room for a doubleword, and every instruction is admissible.
No certificate is consumed. -/
def check (cfg : Cfg) (prog : List Instr) : Bool :=
  decide (0 < prog.length) && decide (prog.length ≤ 1048576) &&
  decide (cfg.idxMask + 8 ≤ cfg.scrBytes) && checkFrom cfg prog.length 0 prog

theorem checkFrom_sound (cfg : Cfg) (n : Nat) :
    ∀ (l : List Instr) (i : Nat), checkFrom cfg n i l = true →
      ∀ j, j < l.length → ∃ ins, l[j]? = some ins ∧ OkInstr cfg n (i + j) ins
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | ins :: rest, i, h, j, hj => by
    simp only [checkFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    cases j with
    | zero => exact ⟨ins, rfl, h.1⟩
    | succ j =>
      obtain ⟨ins', h1, h2⟩ :=
        checkFrom_sound cfg n rest (i + 1) h.2 j (Nat.lt_of_succ_lt_succ hj)
      refine ⟨ins', ?_, ?_⟩
      · rw [List.getElem?_cons_succ]; exact h1
      · have e : i + (j + 1) = i + 1 + j := by omega
        rw [e]; exact h2

theorem check_spec {cfg : Cfg} {prog : List Instr} (hc : check cfg prog = true) :
    0 < prog.length ∧ prog.length ≤ 1048576 ∧ cfg.idxMask + 8 ≤ cfg.scrBytes ∧
    ∀ i, i < prog.length → ∃ ins, prog[i]? = some ins ∧ OkInstr cfg prog.length i ins := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  refine ⟨h1, h2, h3, ?_⟩
  intro i hi
  obtain ⟨ins, e1, e2⟩ := checkFrom_sound cfg prog.length prog 0 h4 i hi
  exact ⟨ins, e1, by rw [Nat.zero_add] at e2; exact e2⟩

/-! ## 4. Entry contract, sandbox, and the inductive invariant -/

/-- What the kernel trampoline guarantees when it enters a module. -/
structure Entry (cfg : Cfg) (s0 : St) : Prop where
  pc0   : s0.pc = 0
  cbAl  : s0.regs 10 % 8 = 0
  cbFit : s0.regs 10 + cfg.ctxBytes ≤ W64
  sbAl  : s0.regs 11 % 8 = 0
  sbFit : s0.regs 11 + cfg.scrBytes ≤ W64
  idx0  : s0.regs 6 ≤ cfg.idxMask ∧ s0.regs 6 % 8 = 0
  adr0  : ∃ k, k ≤ cfg.idxMask ∧ k % 8 = 0 ∧ s0.regs 7 = s0.regs 11 + k
  raAl  : s0.regs 1 % 4 = 0
  raFit : s0.regs 1 < W64

/-- Byte addresses the module is allowed to touch. -/
def InSandbox (cfg : Cfg) (s0 : St) (a : Nat) : Prop :=
  (s0.regs 10 ≤ a ∧ a < s0.regs 10 + cfg.ctxBytes) ∨
  (s0.regs 11 ≤ a ∧ a < s0.regs 11 + cfg.scrBytes)

/-- Inductive invariant relating the entry state `s0` to a reachable state. -/
structure Inv (cfg : Cfg) (n : Nat) (s0 s : St) : Prop where
  pcAl  : s.pc % 4 = 0
  pcIn  : s.pc / 4 < n
  keep  : ∀ r, ¬ IsTemp r → r ≠ 6 → r ≠ 7 → s.regs r = s0.regs r
  idx   : s.regs 6 ≤ cfg.idxMask ∧ s.regs 6 % 8 = 0
  adr   : ∃ k, k ≤ cfg.idxMask ∧ k % 8 = 0 ∧ s.regs 7 = s0.regs 11 + k
  frame : ∀ a, ¬ InSandbox cfg s0 a → s.mem a = s0.mem a

/-! ## 5. Elementary lemmas -/

theorem wrReg_ne {regs : Nat → Nat} {r v x : Nat} (h : x ≠ r) : wrReg regs r v x = regs x := by
  simp [wrReg, h]

theorem wrReg_zero (regs : Nat → Nat) (v : Nat) : wrReg regs 0 v = regs := by
  funext x; simp [wrReg]

theorem isTemp_ne {r : Nat} (h : IsTemp r) :
    r ≠ 0 ∧ r ≠ 1 ∧ r ≠ 6 ∧ r ≠ 7 ∧ r ≠ 10 ∧ r ≠ 11 := by
  unfold IsTemp at h; omega

/-- Masking with `m` bounds the result by `m` and keeps it a multiple of 8
whenever `m` is. -/
theorem and_mask_bound (a m : Nat) (hm : m % 8 = 0) : a &&& m ≤ m ∧ (a &&& m) % 8 = 0 := by
  refine ⟨Nat.and_le_right, ?_⟩
  have h : (a &&& m) % 2 ^ 3 = (a % 2 ^ 3) &&& (m % 2 ^ 3) := Nat.and_mod_two_pow
  have hm' : m % 2 ^ 3 = 0 := hm
  rw [hm', Nat.and_zero] at h
  exact h

theorem readBytes_congr {m1 m2 : Nat → Nat} :
    ∀ (n a : Nat), (∀ k, k < n → m1 (a + k) = m2 (a + k)) → readBytes m1 a n = readBytes m2 a n
  | 0, _, _ => rfl
  | n + 1, a, h => by
    have h0 : m1 a = m2 a := h 0 (Nat.succ_pos n)
    have ht : readBytes m1 (a + 1) n = readBytes m2 (a + 1) n :=
      readBytes_congr n (a + 1) (fun k hk => by
        have := h (k + 1) (Nat.succ_lt_succ hk)
        have e : a + (k + 1) = a + 1 + k := by omega
        rw [e] at this; exact this)
    show m1 a % 256 + 256 * readBytes m1 (a + 1) n = m2 a % 256 + 256 * readBytes m2 (a + 1) n
    rw [h0, ht]

theorem pc_adv {n pc : Nat} (hn : n ≤ 1048576) (ha : pc % 4 = 0) (hlt : pc / 4 + 1 < n) :
    (pc + 4) % W64 % 4 = 0 ∧ (pc + 4) % W64 / 4 < n ∧ pc < (pc + 4) % W64 := by
  omega

/-- The effective address of an admitted load/store is naturally aligned and
the accessed bytes lie inside one sandbox region. -/
theorem ea_ok {cfg : Cfg} {n : Nat} {s0 s : St} {w rs1 imm : Nat}
    (he : Entry cfg s0) (hi : Inv cfg n s0 s) (ha : AddrOk cfg w rs1 imm) :
    eaOf s rs1 imm % w = 0 ∧
    ((s0.regs 10 ≤ eaOf s rs1 imm ∧ eaOf s rs1 imm + w ≤ s0.regs 10 + cfg.ctxBytes) ∨
     (s0.regs 11 ≤ eaOf s rs1 imm ∧ eaOf s rs1 imm + w ≤ s0.regs 11 + cfg.scrBytes)) := by
  obtain ⟨hw, himm, hal, hreg⟩ := ha
  have hs : sext12 imm = imm := by simp [sext12, himm]
  unfold eaOf
  rw [hs]
  rcases hreg with ⟨rfl, hfit⟩ | ⟨rfl, hfit⟩
  · have hk := hi.keep 10 (by unfold IsTemp; omega) (by omega) (by omega)
    have h10 : rdReg s 10 = s0.regs 10 := by simp [rdReg, hk]
    rw [h10]
    have h1 := he.cbAl
    have h2 := he.cbFit
    rcases hw with rfl | rfl | rfl | rfl <;> omega
  · obtain ⟨k, hk1, hk2, hk3⟩ := hi.adr
    have h7 : rdReg s 7 = s0.regs 11 + k := by simp [rdReg, hk3]
    rw [h7]
    have h1 := he.sbAl
    have h2 := he.sbFit
    rcases hw with rfl | rfl | rfl | rfl <;> omega

/-- The only admitted `jalr` returns to the caller's `ra`. -/
theorem ret_target {cfg : Cfg} {n : Nat} {s0 s : St} (he : Entry cfg s0) (hi : Inv cfg n s0 s) :
    jalrTarget s 1 0 = s0.regs 1 ∧ jalrTarget s 1 0 % 4 = 0 := by
  have hk := hi.keep 1 (by unfold IsTemp; omega) (by omega) (by omega)
  have h1 : rdReg s 1 = s0.regs 1 := by simp [rdReg, hk]
  have h2 : sext12 0 = 0 := by simp [sext12]
  unfold jalrTarget
  rw [h1, h2]
  have h3 := he.raAl
  have h4 := he.raFit
  omega

/-- Invariant preservation for a step that only changes `pc` and registers. -/
theorem inv_regs {cfg : Cfg} {n : Nat} {s0 s : St} (hi : Inv cfg n s0 s)
    (pc' : Nat) (regs' : Nat → Nat) (h1 : pc' % 4 = 0) (h2 : pc' / 4 < n)
    (hkeep : ∀ r, ¬ IsTemp r → r ≠ 6 → r ≠ 7 → regs' r = s.regs r)
    (hidx : regs' 6 ≤ cfg.idxMask ∧ regs' 6 % 8 = 0)
    (hadr : ∃ k, k ≤ cfg.idxMask ∧ k % 8 = 0 ∧ regs' 7 = s0.regs 11 + k) :
    Inv cfg n s0 { s with pc := pc', regs := regs' } :=
  ⟨h1, h2, fun r a b c => (hkeep r a b c).trans (hi.keep r a b c), hidx, hadr, hi.frame⟩

/-- Invariant preservation for a write to a temporary. -/
theorem inv_temp {cfg : Cfg} {n : Nat} {s0 s : St} (hi : Inv cfg n s0 s)
    (pc' rd v : Nat) (h1 : pc' % 4 = 0) (h2 : pc' / 4 < n) (hrd : IsTemp rd) :
    Inv cfg n s0 { s with pc := pc', regs := wrReg s.regs rd v } := by
  have hne := isTemp_ne hrd
  refine inv_regs hi pc' _ h1 h2 ?_ ?_ ?_
  · intro r hr _ _
    exact wrReg_ne (fun e => hr (e ▸ hrd))
  · rw [wrReg_ne (Ne.symm hne.2.2.1)]; exact hi.idx
  · rw [wrReg_ne (Ne.symm hne.2.2.2.1)]; exact hi.adr

/-! ## 6. One-step safety -/

/-- An admitted instruction executed from an invariant state either continues
inside the module at a strictly larger `pc` with the invariant re-established,
or returns to the caller's `ra` without changing registers or memory. It never
traps. -/
theorem exec_ok {cfg : Cfg} {n : Nat} {s0 s : St} {ins : Instr}
    (hn : n ≤ 1048576) (hk : cfg.idxMask + 8 ≤ cfg.scrBytes)
    (he : Entry cfg s0) (hi : Inv cfg n s0 s) (ho : OkInstr cfg n (s.pc / 4) ins) :
    (∃ s', exec s ins = .next s' ∧ Inv cfg n s0 s' ∧ s.pc < s'.pc) ∨
    (∃ s', exec s ins = .ret (s0.regs 1) s' ∧ s'.regs = s.regs ∧ s'.mem = s.mem) := by
  have hpa := hi.pcAl
  have hpi := hi.pcIn
  cases ins with
  | aluI f rd rs1 imm =>
    obtain ⟨hlt, _, hrd⟩ := ho
    obtain ⟨p1, p2, p3⟩ := pc_adv hn hpa hlt
    refine Or.inl ⟨_, rfl, ?_, p3⟩
    rcases hrd with hrd | ⟨rfl, rfl, himm, hmask, hal⟩
    · exact inv_temp hi _ rd _ p1 p2 hrd
    · have hs : sext12 imm = imm := by simp [sext12, himm]
      have hb := and_mask_bound (rdReg s rs1) imm hal
      refine inv_regs hi _ _ p1 p2 ?_ ?_ ?_
      · intro r _ h6 _
        exact wrReg_ne h6
      · have e : wrReg s.regs 6 (aluEval .and (rdReg s rs1) (sext12 imm)) 6
            = rdReg s rs1 &&& imm := by
          simp [wrReg, aluEval, hs]
        rw [e]
        exact ⟨Nat.le_trans hb.1 hmask, hb.2⟩
      · rw [wrReg_ne (by omega : (7 : Nat) ≠ 6)]; exact hi.adr
  | alu3 f rd rs1 rs2 =>
    obtain ⟨hlt, hrd⟩ := ho
    obtain ⟨p1, p2, p3⟩ := pc_adv hn hpa hlt
    refine Or.inl ⟨_, rfl, ?_, p3⟩
    rcases hrd with ⟨hrd, _, _⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact inv_temp hi _ rd _ p1 p2 hrd
    · have h11 := hi.keep 11 (by unfold IsTemp; omega) (by omega) (by omega)
      have hx := hi.idx
      have hsb := he.sbFit
      refine inv_regs hi _ _ p1 p2 ?_ ?_ ?_
      · intro r _ _ h7
        exact wrReg_ne h7
      · rw [wrReg_ne (by omega : (6 : Nat) ≠ 7)]; exact hi.idx
      · refine ⟨s.regs 6, hx.1, hx.2, ?_⟩
        have e : wrReg s.regs 7 (aluEval .add (rdReg s 11) (rdReg s 6)) 7
            = (s.regs 11 + s.regs 6) % W64 := by
          simp [wrReg, aluEval, rdReg]
        rw [e, h11]
        omega
  | lui rd imm20 =>
    obtain ⟨hlt, hrd⟩ := ho
    obtain ⟨p1, p2, p3⟩ := pc_adv hn hpa hlt
    exact Or.inl ⟨_, rfl, inv_temp hi _ rd _ p1 p2 hrd, p3⟩
  | load w sgn rd rs1 imm =>
    obtain ⟨hlt, hrd, haddr⟩ := ho
    obtain ⟨p1, p2, p3⟩ := pc_adv hn hpa hlt
    obtain ⟨hal, _⟩ := ea_ok he hi haddr
    exact Or.inl ⟨_, if_pos hal, inv_temp hi _ rd _ p1 p2 hrd, p3⟩
  | store w rs2 rs1 imm =>
    obtain ⟨hlt, _, haddr⟩ := ho
    obtain ⟨p1, p2, p3⟩ := pc_adv hn hpa hlt
    obtain ⟨hal, hrange⟩ := ea_ok he hi haddr
    refine Or.inl ⟨_, if_pos hal, ⟨p1, p2, hi.keep, hi.idx, hi.adr, ?_⟩, p3⟩
    intro a ha
    show writeBytes s.mem (eaOf s rs1 imm) w (rdReg s rs2) a = s0.mem a
    have hout : ¬ (eaOf s rs1 imm ≤ a ∧ a < eaOf s rs1 imm + w) := by
      intro hin
      apply ha
      unfold InSandbox
      omega
    simp only [writeBytes, if_neg hout]
    exact hi.frame a ha
  | branch c rs1 rs2 off =>
    obtain ⟨hlt, _, _, hpos, hoff, hal, hin⟩ := ho
    have hs : sextB off = off := by simp [sextB, hoff]
    have ht : brTarget s c rs1 rs2 off % 4 = 0 ∧ brTarget s c rs1 rs2 off / 4 < n ∧
        s.pc < brTarget s c rs1 rs2 off := by
      unfold brTarget
      rw [hs]
      split <;> omega
    exact Or.inl ⟨_, if_pos ht.1, ⟨ht.1, ht.2.1, hi.keep, hi.idx, hi.adr, hi.frame⟩, ht.2.2⟩
  | jal rd off =>
    obtain ⟨rfl, hpos, hoff, hal, hin⟩ := ho
    have hs : sextJ off = off := by simp [sextJ, hoff]
    have ht : (s.pc + sextJ off) % W64 % 4 = 0 ∧ (s.pc + sextJ off) % W64 / 4 < n ∧
        s.pc < (s.pc + sextJ off) % W64 := by
      rw [hs]; omega
    refine Or.inl ⟨_, if_pos ht.1, ?_, ht.2.2⟩
    rw [wrReg_zero]
    exact ⟨ht.1, ht.2.1, hi.keep, hi.idx, hi.adr, hi.frame⟩
  | jalr rd rs1 imm =>
    obtain ⟨rfl, rfl, rfl⟩ := ho
    obtain ⟨h1, h2⟩ := ret_target he hi
    refine Or.inr ⟨{ s with regs := wrReg s.regs 0 ((s.pc + 4) % W64) }, ?_, wrReg_zero _ _, rfl⟩
    have e : exec s (.jalr 0 1 0)
        = .ret (jalrTarget s 1 0) { s with regs := wrReg s.regs 0 ((s.pc + 4) % W64) } :=
      if_pos h2
    rw [e, h1]
  | system w => exact absurd ho id
  | other w => exact absurd ho id

theorem step_eq {prog : List Instr} {s : St} {ins : Instr}
    (ha : s.pc % 4 = 0) (hg : prog[s.pc / 4]? = some ins) : step prog s = exec s ins := by
  simp [step, ha, hg]

/-- One-step safety for a checked module. -/
theorem step_ok {cfg : Cfg} {prog : List Instr} {s0 s : St}
    (hc : check cfg prog = true) (he : Entry cfg s0) (hi : Inv cfg prog.length s0 s) :
    (∃ s', step prog s = .next s' ∧ Inv cfg prog.length s0 s' ∧ s.pc < s'.pc) ∨
    (∃ s', step prog s = .ret (s0.regs 1) s' ∧ s'.regs = s.regs ∧ s'.mem = s.mem) := by
  obtain ⟨_, hn, hk, hall⟩ := check_spec hc
  obtain ⟨ins, hg, ho⟩ := hall (s.pc / 4) hi.pcIn
  rw [step_eq hi.pcAl hg]
  exact exec_ok hn hk he hi ho

theorem inv_entry {cfg : Cfg} {prog : List Instr} {s0 : St}
    (hc : check cfg prog = true) (he : Entry cfg s0) : Inv cfg prog.length s0 s0 := by
  obtain ⟨hpos, _, _, _⟩ := check_spec hc
  have h0 := he.pc0
  exact ⟨by omega, by omega, fun _ _ _ _ => rfl, he.idx0, he.adr0, fun _ _ => rfl⟩

/-! ## 7. Whole-run safety, bounded termination, ABI and frame preservation -/

/-- What the caller observes when the module returns. -/
structure Returned (cfg : Cfg) (s0 s' : St) : Prop where
  keep  : ∀ r, ¬ IsTemp r → r ≠ 6 → r ≠ 7 → s'.regs r = s0.regs r
  frame : ∀ a, ¬ InSandbox cfg s0 a → s'.mem a = s0.mem a

theorem run_from {cfg : Cfg} {prog : List Instr} {s0 : St}
    (hc : check cfg prog = true) (he : Entry cfg s0) :
    ∀ (m : Nat) (s : St), Inv cfg prog.length s0 s → prog.length - s.pc / 4 ≤ m →
      ∃ k s', k ≤ m ∧ run prog k s = .ret (s0.regs 1) s' ∧ Returned cfg s0 s'
  | 0, s, hi, hm => by
    have := hi.pcIn
    omega
  | m + 1, s, hi, hm => by
    rcases step_ok hc he hi with ⟨s', hs, hi', hlt⟩ | ⟨s', hs, hr, hmem⟩
    · have h1 := hi.pcAl
      have h2 := hi'.pcAl
      obtain ⟨k, s'', hk, hrun, hret⟩ := run_from hc he m s' hi' (by omega)
      refine ⟨k + 1, s'', by omega, ?_, hret⟩
      simp [run, hs, hrun]
    · refine ⟨1, s', by omega, by simp [run, hs], ?_⟩
      exact ⟨fun r a b c => by rw [hr]; exact hi.keep r a b c,
             fun a ha => by rw [hmem]; exact hi.frame a ha⟩

/-- **Soundness of the certificate-free checker.** A checked module entered
under the `Entry` contract returns to the caller's `ra` after at most
`prog.length` instructions, with every non-temporary register and every byte
outside the two sandbox regions unchanged. Because `run` stops at the first
trap, the statement also excludes every synchronous exception on the way. -/
theorem safe_and_terminates {cfg : Cfg} {prog : List Instr} {s0 : St}
    (hc : check cfg prog = true) (he : Entry cfg s0) :
    ∃ k s', k ≤ prog.length ∧ run prog k s0 = .ret (s0.regs 1) s' ∧ Returned cfg s0 s' := by
  have hi := inv_entry hc he
  obtain ⟨k, s', hk, hrun, hret⟩ := run_from hc he prog.length s0 hi (by omega)
  exact ⟨k, s', hk, hrun, hret⟩

/-- Every prefix of the run is trap-free. -/
theorem never_traps {cfg : Cfg} {prog : List Instr} {s0 : St}
    (hc : check cfg prog = true) (he : Entry cfg s0) :
    ∀ (k : Nat) (s : St), Inv cfg prog.length s0 s → ∀ t, run prog k s ≠ .trap t
  | 0, s, _, t => by simp [run]
  | k + 1, s, hi, t => by
    rcases step_ok hc he hi with ⟨s', hs, hi', _⟩ | ⟨s', hs, _, _⟩
    · have := never_traps hc he k s' hi' t
      simp [run, hs, this]
    · simp [run, hs]

/-! ## 8. Confidentiality: the module is a function of its sandbox -/

/-- Registers whose entry value may influence the module. -/
def Vis (r : Nat) : Prop := IsTemp r ∨ r = 6 ∨ r = 7 ∨ r = 10 ∨ r = 11

/-- Two states agree on everything the module can observe. -/
structure LowEq (cfg : Cfg) (s0 s t : St) : Prop where
  pc  : s.pc = t.pc
  reg : ∀ r, Vis r → s.regs r = t.regs r
  mem : ∀ a, InSandbox cfg s0 a → s.mem a = t.mem a

/-- Indistinguishability of two step outcomes. -/
def OutLowEq (cfg : Cfg) (s0 : St) : Out → Out → Prop
  | .next s', .next t' => LowEq cfg s0 s' t'
  | .ret _ s', .ret _ t' => LowEq cfg s0 s' t'
  | .trap a, .trap b => a = b
  | _, _ => False

theorem rdReg_lowEq {cfg : Cfg} {s0 s t : St} (hL : LowEq cfg s0 s t) {r : Nat}
    (h : CanRead r) : rdReg t r = rdReg s r := by
  unfold rdReg
  by_cases h0 : r = 0
  · simp [h0]
  · simp only [if_neg h0]
    rcases h with h | h | h
    · exact absurd h h0
    · exact (hL.reg r (Or.inl h)).symm
    · exact (hL.reg r (Or.inr (Or.inl h))).symm

theorem lowEq_wr {cfg : Cfg} {s0 s t : St} (hL : LowEq cfg s0 s t) (pc' rd v : Nat) :
    LowEq cfg s0 { s with pc := pc', regs := wrReg s.regs rd v }
      { t with pc := pc', regs := wrReg t.regs rd v } := by
  refine ⟨rfl, ?_, hL.mem⟩
  intro r hr
  show wrReg s.regs rd v r = wrReg t.regs rd v r
  by_cases h : r = rd ∧ rd ≠ 0
  · simp [wrReg, h]
  · simp only [wrReg, if_neg h]
    exact hL.reg r hr

theorem eaOf_lowEq {cfg : Cfg} {n : Nat} {s0 s t : St} (hL : LowEq cfg s0 s t)
    {w rs1 imm : Nat} (ha : AddrOk cfg w rs1 imm) : eaOf t rs1 imm = eaOf s rs1 imm := by
  obtain ⟨_, _, _, hreg⟩ := ha
  unfold eaOf rdReg
  rcases hreg with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · have := hL.reg 10 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    simp [this]
  · have := hL.reg 7 (Or.inr (Or.inr (Or.inl rfl)))
    simp [this]

/-- One-step noninterference for an admitted instruction. -/
theorem exec_lowEq {cfg : Cfg} {n : Nat} {s0 t0 s t : St} {ins : Instr}
    (he : Entry cfg s0) (het : Entry cfg t0)
    (his : Inv cfg n s0 s) (hit : Inv cfg n t0 t) (hL : LowEq cfg s0 s t)
    (ho : OkInstr cfg n (s.pc / 4) ins) :
    OutLowEq cfg s0 (exec s ins) (exec t ins) := by
  have hpc : t.pc = s.pc := hL.pc.symm
  cases ins with
  | aluI f rd rs1 imm =>
    obtain ⟨_, hr1, _⟩ := ho
    show LowEq cfg s0
      { s with pc := (s.pc + 4) % W64,
               regs := wrReg s.regs rd (aluEval f (rdReg s rs1) (sext12 imm)) }
      { t with pc := (t.pc + 4) % W64,
               regs := wrReg t.regs rd (aluEval f (rdReg t rs1) (sext12 imm)) }
    rw [hpc, rdReg_lowEq hL hr1]
    exact lowEq_wr hL _ _ _
  | alu3 f rd rs1 rs2 =>
    obtain ⟨_, hrd⟩ := ho
    show LowEq cfg s0
      { s with pc := (s.pc + 4) % W64,
               regs := wrReg s.regs rd (aluEval f (rdReg s rs1) (rdReg s rs2)) }
      { t with pc := (t.pc + 4) % W64,
               regs := wrReg t.regs rd (aluEval f (rdReg t rs1) (rdReg t rs2)) }
    rcases hrd with ⟨_, hr1, hr2⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · rw [hpc, rdReg_lowEq hL hr1, rdReg_lowEq hL hr2]
      exact lowEq_wr hL _ _ _
    · have h11 : rdReg t 11 = rdReg s 11 := by
        have := hL.reg 11 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
        simp [rdReg, this]
      have h6 : rdReg t 6 = rdReg s 6 := rdReg_lowEq hL (Or.inr (Or.inr rfl))
      rw [hpc, h11, h6]
      exact lowEq_wr hL _ _ _
  | lui rd imm20 =>
    show LowEq cfg s0
      { s with pc := (s.pc + 4) % W64, regs := wrReg s.regs rd (sext32 (imm20 * 4096)) }
      { t with pc := (t.pc + 4) % W64, regs := wrReg t.regs rd (sext32 (imm20 * 4096)) }
    rw [hpc]
    exact lowEq_wr hL _ _ _
  | load w sgn rd rs1 imm =>
    obtain ⟨_, _, haddr⟩ := ho
    obtain ⟨hal, hrange⟩ := ea_ok he his haddr
    have hea : eaOf t rs1 imm = eaOf s rs1 imm := eaOf_lowEq (n := n) hL haddr
    have hval : readBytes t.mem (eaOf s rs1 imm) w = readBytes s.mem (eaOf s rs1 imm) w := by
      apply readBytes_congr
      intro k hk
      refine (hL.mem _ ?_).symm
      unfold InSandbox
      omega
    have e1 : exec s (.load w sgn rd rs1 imm) =
        .next { s with pc := (s.pc + 4) % W64, regs := wrReg s.regs rd (extLoad w sgn (readBytes s.mem (eaOf s rs1 imm) w)) } :=
      if_pos hal
    have e2 : exec t (.load w sgn rd rs1 imm) =
        .next { t with pc := (t.pc + 4) % W64, regs := wrReg t.regs rd (extLoad w sgn (readBytes t.mem (eaOf t rs1 imm) w)) } :=
      if_pos (by rw [hea]; exact hal)
    rw [e1, e2, hea, hval, hpc]
    exact lowEq_wr hL _ _ _
  | store w rs2 rs1 imm =>
    obtain ⟨_, hr2, haddr⟩ := ho
    obtain ⟨hal, _⟩ := ea_ok he his haddr
    have hea : eaOf t rs1 imm = eaOf s rs1 imm := eaOf_lowEq (n := n) hL haddr
    have e1 : exec s (.store w rs2 rs1 imm) =
        .next { s with pc := (s.pc + 4) % W64, mem := writeBytes s.mem (eaOf s rs1 imm) w (rdReg s rs2) } :=
      if_pos hal
    have e2 : exec t (.store w rs2 rs1 imm) =
        .next { t with pc := (t.pc + 4) % W64, mem := writeBytes t.mem (eaOf t rs1 imm) w (rdReg t rs2) } :=
      if_pos (by rw [hea]; exact hal)
    rw [e1, e2, hea, rdReg_lowEq hL hr2, hpc]
    refine ⟨rfl, hL.reg, ?_⟩
    intro a ha
    show writeBytes s.mem (eaOf s rs1 imm) w (rdReg s rs2) a
      = writeBytes t.mem (eaOf s rs1 imm) w (rdReg s rs2) a
    by_cases hin : eaOf s rs1 imm ≤ a ∧ a < eaOf s rs1 imm + w
    · simp [writeBytes, hin]
    · simp only [writeBytes, if_neg hin]
      exact hL.mem a ha
  | branch c rs1 rs2 off =>
    obtain ⟨_, hr1, hr2, _⟩ := ho
    have ht : brTarget t c rs1 rs2 off = brTarget s c rs1 rs2 off := by
      unfold brTarget
      rw [rdReg_lowEq hL hr1, rdReg_lowEq hL hr2, hpc]
    by_cases hc : brTarget s c rs1 rs2 off % 4 = 0
    · have e1 : exec s (.branch c rs1 rs2 off) = .next { s with pc := brTarget s c rs1 rs2 off } :=
        if_pos hc
      have e2 : exec t (.branch c rs1 rs2 off) = .next { t with pc := brTarget t c rs1 rs2 off } :=
        if_pos (by rw [ht]; exact hc)
      rw [e1, e2, ht]
      exact ⟨rfl, hL.reg, hL.mem⟩
    · have e1 : exec s (.branch c rs1 rs2 off) = .trap .instrMisaligned := if_neg hc
      have e2 : exec t (.branch c rs1 rs2 off) = .trap .instrMisaligned :=
        if_neg (by rw [ht]; exact hc)
      rw [e1, e2]
      exact rfl
  | jal rd off =>
    obtain ⟨rfl, _⟩ := ho
    by_cases hc : (s.pc + sextJ off) % W64 % 4 = 0
    · have e1 : exec s (.jal 0 off) =
          .next { s with pc := (s.pc + sextJ off) % W64, regs := wrReg s.regs 0 ((s.pc + 4) % W64) } := if_pos hc
      have e2 : exec t (.jal 0 off) =
          .next { t with pc := (t.pc + sextJ off) % W64, regs := wrReg t.regs 0 ((t.pc + 4) % W64) } := if_pos (by rw [hpc]; exact hc)
      rw [e1, e2, hpc, wrReg_zero, wrReg_zero]
      exact ⟨rfl, hL.reg, hL.mem⟩
    · have e1 : exec s (.jal 0 off) = .trap .instrMisaligned := if_neg hc
      have e2 : exec t (.jal 0 off) = .trap .instrMisaligned := if_neg (by rw [hpc]; exact hc)
      rw [e1, e2]
      exact rfl
  | jalr rd rs1 imm =>
    obtain ⟨rfl, rfl, rfl⟩ := ho
    obtain ⟨_, h2⟩ := ret_target he his
    obtain ⟨_, h2'⟩ := ret_target het hit
    have e1 : exec s (.jalr 0 1 0)
        = .ret (jalrTarget s 1 0) { s with regs := wrReg s.regs 0 ((s.pc + 4) % W64) } :=
      if_pos h2
    have e2 : exec t (.jalr 0 1 0)
        = .ret (jalrTarget t 1 0) { t with regs := wrReg t.regs 0 ((t.pc + 4) % W64) } :=
      if_pos h2'
    rw [e1, e2, wrReg_zero, wrReg_zero]
    exact ⟨hL.pc, hL.reg, hL.mem⟩
  | system w => exact absurd ho id
  | other w => exact absurd ho id

theorem step_lowEq {cfg : Cfg} {prog : List Instr} {s0 t0 s t : St}
    (hc : check cfg prog = true) (he : Entry cfg s0) (het : Entry cfg t0)
    (his : Inv cfg prog.length s0 s) (hit : Inv cfg prog.length t0 t)
    (hL : LowEq cfg s0 s t) :
    OutLowEq cfg s0 (step prog s) (step prog t) := by
  obtain ⟨_, _, _, hall⟩ := check_spec hc
  obtain ⟨ins, hg, ho⟩ := hall (s.pc / 4) his.pcIn
  have hg' : prog[t.pc / 4]? = some ins := by rw [← hL.pc]; exact hg
  rw [step_eq his.pcAl hg, step_eq hit.pcAl hg']
  exact exec_lowEq he het his hit hL ho

theorem run_lowEq {cfg : Cfg} {prog : List Instr} {s0 t0 : St}
    (hc : check cfg prog = true) (he : Entry cfg s0) (het : Entry cfg t0) :
    ∀ (k : Nat) (s t : St), Inv cfg prog.length s0 s → Inv cfg prog.length t0 t →
      LowEq cfg s0 s t → OutLowEq cfg s0 (run prog k s) (run prog k t)
  | 0, s, t, _, _, hL => hL
  | k + 1, s, t, his, hit, hL => by
    have hstep := step_lowEq hc he het his hit hL
    rcases step_ok hc he his with ⟨s', hs, his', _⟩ | ⟨s', hs, _, _⟩
    · rcases step_ok hc het hit with ⟨t', ht, hit', _⟩ | ⟨t', ht, _, _⟩
      · rw [hs, ht] at hstep
        have e1 : run prog (k + 1) s = run prog k s' := by simp [run, hs]
        have e2 : run prog (k + 1) t = run prog k t' := by simp [run, ht]
        rw [e1, e2]
        exact run_lowEq hc he het k s' t' his' hit' hstep
      · rw [hs, ht] at hstep
        exact absurd hstep id
    · rcases step_ok hc het hit with ⟨t', ht, _, _⟩ | ⟨t', ht, _, _⟩
      · rw [hs, ht] at hstep
        exact absurd hstep id
      · rw [hs, ht] at hstep
        have e1 : run prog (k + 1) s = .ret (s0.regs 1) s' := by simp [run, hs]
        have e2 : run prog (k + 1) t = .ret (t0.regs 1) t' := by simp [run, ht]
        rw [e1, e2]
        exact hstep

/-- **Sandbox noninterference.** Let two entry states agree on the module's
temporaries, on `x6`, `x7`, `x10`, `x11`, and on the bytes of the two sandbox
regions, and differ arbitrarily everywhere else (all other memory, `ra`, `sp`,
`gp`, `tp`, `s0`–`s11`). Then after any number of steps the two runs are in
the same control state and still agree on those registers and bytes. -/
theorem sandbox_noninterference {cfg : Cfg} {prog : List Instr} {s0 t0 : St}
    (hc : check cfg prog = true) (he : Entry cfg s0) (het : Entry cfg t0)
    (hL : LowEq cfg s0 s0 t0) (k : Nat) :
    OutLowEq cfg s0 (run prog k s0) (run prog k t0) :=
  run_lowEq hc he het k s0 t0 (inv_entry hc he) (inv_entry hc het) hL

/-! ## 9. `RV64M` division and remainder: total, with the specified edge values -/

theorem divu_by_zero (x : Nat) : aluEval .divu x 0 = 18446744073709551615 := by simp [aluEval]
theorem remu_by_zero (x : Nat) : aluEval .remu x 0 = x := by simp [aluEval]
theorem div_by_zero (x : Nat) : aluEval .div x 0 = 18446744073709551615 := by simp [aluEval]
theorem rem_by_zero (x : Nat) : aluEval .rem x 0 = x := by simp [aluEval]

/-- Signed overflow: `INT64_MIN / -1 = INT64_MIN`. -/
theorem div_overflow :
    aluEval .div 9223372036854775808 18446744073709551615 = 9223372036854775808 := by decide

/-- Signed overflow: `INT64_MIN % -1 = 0`. -/
theorem rem_overflow : aluEval .rem 9223372036854775808 18446744073709551615 = 0 := by decide

/-- `divw`/`divuw` by zero: all ones, sign-extended from 32 bits. -/
theorem divw_by_zero (x : Nat) : aluEval .divw x 0 = 18446744073709551615 := by
  simp [aluEval, sext32]
theorem divuw_by_zero (x : Nat) : aluEval .divuw x 0 = 18446744073709551615 := by
  simp [aluEval, sext32]

/-- `remw`/`remuw` by zero: the 32-bit dividend, sign-extended. -/
theorem remw_by_zero (x : Nat) : aluEval .remw x 0 = sext32 x := by
  simp [aluEval, sext32]
theorem remuw_by_zero (x : Nat) : aluEval .remuw x 0 = sext32 x := by
  simp [aluEval, sext32]

/-- 32-bit signed overflow: `INT32_MIN / -1 = INT32_MIN`, sign-extended. -/
theorem divw_overflow :
    aluEval .divw 2147483648 4294967295 = 18446744071562067968 := by decide
theorem remw_overflow : aluEval .remw 2147483648 4294967295 = 0 := by decide

/-- Sanity: ordinary signed division truncates toward zero (`-7 / 2 = -3`,
`-7 % 2 = -1`). -/
theorem div_trunc :
    aluEval .div 18446744073709551609 2 = 18446744073709551613 ∧
    aluEval .rem 18446744073709551609 2 = 18446744073709551615 := by decide

/-- The Lean core signed-division operators do **not** coincide with `RV64M`
`div` on division by zero: `BitVec.smtSDiv (-1) 0 = 1` and `BitVec.sdiv (-1) 0 =
0`, whereas `div` returns all ones for every dividend. A model that reuses
either operator for `div` is wrong exactly on a negative dividend and a zero
divisor. -/
theorem lean_sdiv_differs_from_rv64m_div :
    BitVec.smtSDiv (-1#64) 0#64 = 1#64 ∧ BitVec.sdiv (-1#64) 0#64 = 0#64 ∧
    aluEval .div 18446744073709551615 0 = 18446744073709551615 := by decide

/-! ## 10. Separating witnesses: each side condition is necessary -/

/-- A concrete policy: 64-byte context, 4 KiB scratch, index mask `0x7f8`. -/
def cfgDemo : Cfg := { ctxBytes := 64, scrBytes := 4096, idxMask := 2040 }

/-- A concrete entry state: context at `0x10000`, scratch at `0x20000`,
`ra = 0x80001000`; the byte at `0xfff8` (just below the context) is a kernel
secret `0xAA`. -/
def sDemo : St :=
  { pc := 0
    regs := fun r => if r = 10 then 65536 else if r = 11 then 131072 else if r = 7 then 131072
                     else if r = 1 then 2147487744 else 0
    mem := fun a => if a = 65528 then 170 else 0 }

theorem sDemo_entry : Entry cfgDemo sDemo := by
  refine ⟨rfl, by decide, by decide, by decide, by decide, by decide, ⟨0, by decide, by decide, by decide⟩,
    by decide, by decide⟩

/-- **Signed-immediate underflow.** `ld t0, -8(a0)` (raw immediate `0xff8`) is
naturally aligned, executes without any exception, and loads the secret byte
that lies *below* the context region. The checker rejects it. -/
theorem neg_imm_reads_below_region :
    eaOf sDemo 10 4088 = 65528 ∧ eaOf sDemo 10 4088 % 8 = 0 ∧
    ¬ InSandbox cfgDemo sDemo (eaOf sDemo 10 4088) ∧
    readBytes sDemo.mem (eaOf sDemo 10 4088) 8 = 170 ∧
    ¬ OkInstr cfgDemo 2 0 (.load 8 false 5 10 4088) := by
  refine ⟨by decide, by decide, ?_, by decide, by decide⟩
  unfold InSandbox
  decide

/-- **Misalignment.** `ld t0, 4(a0)` stays inside the context region but is not
naturally aligned; the conservative machine raises load-address-misaligned. The
checker rejects it. -/
theorem misaligned_load_traps :
    (match exec sDemo (.load 8 false 5 10 4) with | .trap .loadMisaligned => True | _ => False) ∧
    ¬ OkInstr cfgDemo 2 0 (.load 8 false 5 10 4) := by
  refine ⟨?_, by decide⟩
  have h : exec sDemo (.load 8 false 5 10 4) = .trap .loadMisaligned := rfl
  rw [h]
  trivial

/-- **Region overrun.** `ld t0, 64(a0)` is aligned and non-negative but lies
just past a 64-byte context. The checker rejects it. -/
theorem overrun_rejected :
    ¬ InSandbox cfgDemo sDemo (eaOf sDemo 10 64 + 7) ∧
    ¬ OkInstr cfgDemo 2 0 (.load 8 false 5 10 64) := by
  refine ⟨?_, by decide⟩
  unfold InSandbox
  decide

/-- **Negative `andi` mask.** `andi t1, t0, -8` (raw immediate `0xff8`)
sign-extends to `0xffff_ffff_ffff_fff8`: it aligns but does not bound. With
`t0 = 2^40` the "masked" index is still `2^40`. The checker rejects it. -/
theorem neg_mask_does_not_bound :
    aluEval .and 1099511627776 (sext12 4088) = 1099511627776 ∧
    ¬ OkInstr cfgDemo 2 0 (.aluI .and 6 5 4088) := by decide

/-- **Computed `jalr`.** `jalr x0, 0(t0)` leaves the module for whatever
address `t0` holds (here `0`, not the caller's `ra`). The checker rejects it. -/
theorem computed_jalr_escapes :
    jalrTarget sDemo 5 0 = 0 ∧ sDemo.regs 1 = 2147487744 ∧
    ¬ OkInstr cfgDemo 2 0 (.jalr 0 5 0) := by decide

/-- **Backward (here: self) branch.** `beq x0, x0, 0` never leaves the module
and never returns: after any number of steps the machine is still at `pc = 0`.
The checker rejects it. -/
theorem self_branch_never_returns :
    (∀ k, ∃ s, run [.branch .eq 0 0 0] k sDemo = .next s ∧ s.pc = 0) ∧
    ¬ OkInstr cfgDemo 1 0 (.branch .eq 0 0 0) := by
  refine ⟨?_, by decide⟩
  have hstep : ∀ s : St, s.pc = 0 → ∃ s', step [.branch .eq 0 0 0] s = .next s' ∧ s'.pc = 0 := by
    intro s hs
    have hb : brTarget s .eq 0 0 0 = 0 := by
      simp [brTarget, condEval, rdReg, sextB, hs]
    refine ⟨{ s with pc := brTarget s .eq 0 0 0 }, ?_, hb⟩
    have hg : [Instr.branch .eq 0 0 0][s.pc / 4]? = some (.branch .eq 0 0 0) := by
      rw [hs]; rfl
    rw [step_eq (by omega) hg]
    exact if_pos (by rw [hb])
  have hrun : ∀ k (s : St), s.pc = 0 → ∃ s', run [.branch .eq 0 0 0] k s = .next s' ∧ s'.pc = 0 := by
    intro k
    induction k with
    | zero => intro s hs; exact ⟨s, rfl, hs⟩
    | succ k ih =>
      intro s hs
      obtain ⟨s', h1, h2⟩ := hstep s hs
      obtain ⟨s'', h3, h4⟩ := ih s' h2
      exact ⟨s'', by simp [run, h1, h3], h4⟩
  exact fun k => hrun k sDemo rfl

/-- **Wrap-around of a `bne`-on-zero loop counter.** Decrementing a counter
that is already `0` yields `2^64 - 1`, which is non-zero, so a back edge of the
form `addi c, c, -1; bne c, x0, loop` entered with `c = 0` is taken `2^64 - 1`
more times. A bounded-loop discipline must therefore test `0 < c` (signed) or
guarantee the counter is initialized on every path into the loop. -/
theorem counter_wraps :
    aluEval .add 0 (sext12 4095) = 18446744073709551615 ∧
    condEval .ne (aluEval .add 0 (sext12 4095)) 0 = true := by decide

/-- **Privileged and system encodings** trap (in a real kernel they would
instead succeed and reconfigure the machine); the checker rejects the whole
`SYSTEM` major opcode. -/
theorem system_rejected (w : Nat) :
    (match exec sDemo (.system w) with | .trap .privileged => True | _ => False) ∧
    ¬ OkInstr cfgDemo 2 0 (.system w) :=
  ⟨trivial, fun h => h⟩

/-- **Why the trampoline must define the temporaries.** `sd t0, 0(a0)` is
admitted. Two entry states that differ only in the entry value of `t0` end
with different context bytes: whatever the kernel left in a temporary is
copied into memory the module's owner can read. -/
theorem unscrubbed_temp_leaks :
    OkInstr cfgDemo 2 0 (.store 8 5 10 0) ∧
    writeBytes sDemo.mem (eaOf sDemo 10 0) 8 0 65536 = 0 ∧
    writeBytes sDemo.mem (eaOf sDemo 10 0) 8 170 65536 = 170 := by decide

/-! ## 11. A concrete admitted module -/

/-- `ld t0, 0(a0); andi t1, t0, 0x7f8; add t2, a1, t1; ld a2, 0(t2);
    div a3, a2, t0; beq a3, x0, +8; sd a3, 8(a0); ret` -/
def demoProg : List Instr :=
  [ .load 8 false 5 10 0,
    .aluI .and 6 5 2040,
    .alu3 .add 7 11 6,
    .load 8 false 12 7 0,
    .alu3 .div 13 12 5,
    .branch .eq 13 0 8,
    .store 8 13 10 8,
    .jalr 0 1 0 ]

theorem demoProg_checked : check cfgDemo demoProg = true := by decide

/-- The demo module (which divides by an attacker-controlled, possibly zero,
value) returns to `ra` within eight instructions from the demo entry state. -/
theorem demoProg_safe :
    ∃ k s', k ≤ 8 ∧ run demoProg k sDemo = .ret (sDemo.regs 1) s' ∧ Returned cfgDemo sDemo s' :=
  safe_and_terminates demoProg_checked sDemo_entry

/-! ## 12. An executable allow-list decoder for the admitted encodings -/

/-- Decode a 32-bit instruction word. Every word outside the listed encodings
of `LOAD`, `STORE`, `OP-IMM`, `OP`, `OP-32` (division only), `LUI`, `BRANCH`,
`JAL`, `JALR` decodes to `system` (major opcode `0x73`) or `other`. -/
def decode (w : Nat) : Instr :=
  let opcode := w % 128
  let rd := (w / 128) % 32
  let f3 := (w / 4096) % 8
  let rs1 := (w / 32768) % 32
  let rs2 := (w / 1048576) % 32
  let f7 := (w / 33554432) % 128
  let immI := (w / 1048576) % 4096
  let immS := f7 * 32 + rd
  let immB := ((w / 2147483648) % 2) * 4096 + ((w / 128) % 2) * 2048 +
              ((w / 33554432) % 64) * 32 + ((w / 256) % 16) * 2
  let immJ := ((w / 2147483648) % 2) * 1048576 + ((w / 4096) % 256) * 4096 +
              ((w / 1048576) % 2) * 2048 + ((w / 2097152) % 1024) * 2
  if opcode = 0x03 then
    (if f3 = 0 then .load 1 true rd rs1 immI else if f3 = 1 then .load 2 true rd rs1 immI
     else if f3 = 2 then .load 4 true rd rs1 immI else if f3 = 3 then .load 8 false rd rs1 immI
     else if f3 = 4 then .load 1 false rd rs1 immI else if f3 = 5 then .load 2 false rd rs1 immI
     else if f3 = 6 then .load 4 false rd rs1 immI else .other w)
  else if opcode = 0x23 then
    (if f3 = 0 then .store 1 rs2 rs1 immS else if f3 = 1 then .store 2 rs2 rs1 immS
     else if f3 = 2 then .store 4 rs2 rs1 immS else if f3 = 3 then .store 8 rs2 rs1 immS
     else .other w)
  else if opcode = 0x13 then
    (if f3 = 0 then .aluI .add rd rs1 immI else if f3 = 2 then .aluI .slt rd rs1 immI
     else if f3 = 3 then .aluI .sltu rd rs1 immI else if f3 = 4 then .aluI .xor rd rs1 immI
     else if f3 = 6 then .aluI .or rd rs1 immI else if f3 = 7 then .aluI .and rd rs1 immI
     else if f3 = 1 then (if immI / 64 = 0 then .aluI .sll rd rs1 (immI % 64) else .other w)
     else (if immI / 64 = 0 then .aluI .srl rd rs1 (immI % 64)
           else if immI / 64 = 16 then .aluI .sra rd rs1 (immI % 64) else .other w))
  else if opcode = 0x33 then
    (if f7 = 0 then
       (if f3 = 0 then .alu3 .add rd rs1 rs2 else if f3 = 1 then .alu3 .sll rd rs1 rs2
        else if f3 = 2 then .alu3 .slt rd rs1 rs2 else if f3 = 3 then .alu3 .sltu rd rs1 rs2
        else if f3 = 4 then .alu3 .xor rd rs1 rs2 else if f3 = 5 then .alu3 .srl rd rs1 rs2
        else if f3 = 6 then .alu3 .or rd rs1 rs2 else .alu3 .and rd rs1 rs2)
     else if f7 = 32 then
       (if f3 = 0 then .alu3 .sub rd rs1 rs2 else if f3 = 5 then .alu3 .sra rd rs1 rs2
        else .other w)
     else if f7 = 1 then
       (if f3 = 0 then .alu3 .mul rd rs1 rs2 else if f3 = 4 then .alu3 .div rd rs1 rs2
        else if f3 = 5 then .alu3 .divu rd rs1 rs2 else if f3 = 6 then .alu3 .rem rd rs1 rs2
        else if f3 = 7 then .alu3 .remu rd rs1 rs2 else .other w)
     else .other w)
  else if opcode = 0x3b then
    (if f7 = 1 then
       (if f3 = 4 then .alu3 .divw rd rs1 rs2 else if f3 = 5 then .alu3 .divuw rd rs1 rs2
        else if f3 = 6 then .alu3 .remw rd rs1 rs2 else if f3 = 7 then .alu3 .remuw rd rs1 rs2
        else .other w)
     else .other w)
  else if opcode = 0x37 then .lui rd (w / 4096)
  else if opcode = 0x63 then
    (if f3 = 0 then .branch .eq rs1 rs2 immB else if f3 = 1 then .branch .ne rs1 rs2 immB
     else if f3 = 4 then .branch .lt rs1 rs2 immB else if f3 = 5 then .branch .ge rs1 rs2 immB
     else if f3 = 6 then .branch .ltu rs1 rs2 immB else if f3 = 7 then .branch .geu rs1 rs2 immB
     else .other w)
  else if opcode = 0x6f then .jal rd immJ
  else if opcode = 0x67 then (if f3 = 0 then .jalr rd rs1 immI else .other w)
  else if opcode = 0x73 then .system w
  else .other w

/-- Admission of raw instruction words: decode, then check. -/
def checkWords (cfg : Cfg) (ws : List Nat) : Bool := check cfg (ws.map decode)

/-- Encodings of the admitted idioms decode as intended. -/
theorem decode_admitted :
    decode 0x00008067 = .jalr 0 1 0 ∧                 -- ret
    decode 0x00053283 = .load 8 false 5 10 0 ∧        -- ld   t0, 0(a0)
    decode 0xff853283 = .load 8 false 5 10 4088 ∧     -- ld   t0, -8(a0)
    decode 0x00553423 = .store 8 5 10 8 ∧             -- sd   t0, 8(a0)
    decode 0x7f82f313 = .aluI .and 6 5 2040 ∧         -- andi t1, t0, 0x7f8
    decode 0x006583b3 = .alu3 .add 7 11 6 ∧           -- add  t2, a1, t1
    decode 0x02e6c633 = .alu3 .div 12 13 14 ∧         -- div  a2, a3, a4
    decode 0x00000463 = .branch .eq 0 0 8 := by decide -- beq  x0, x0, +8

/-- Every privileged or system encoding falls in the rejected `SYSTEM` class,
and `auipc`, `fence.i`, `lr.d`, and a compressed parcel fall in `other`. -/
theorem decode_rejected :
    decode 0x00000073 = .system 0x00000073 ∧          -- ecall
    decode 0x00100073 = .system 0x00100073 ∧          -- ebreak
    decode 0x10200073 = .system 0x10200073 ∧          -- sret
    decode 0x30200073 = .system 0x30200073 ∧          -- mret
    decode 0x10500073 = .system 0x10500073 ∧          -- wfi
    decode 0x12000073 = .system 0x12000073 ∧          -- sfence.vma x0, x0
    decode 0x18051073 = .system 0x18051073 ∧          -- csrrw x0, satp, a0
    decode 0xc0002573 = .system 0xc0002573 ∧          -- rdcycle a0
    decode 0x00000297 = .other 0x00000297 ∧           -- auipc t0, 0
    decode 0x0000100f = .other 0x0000100f ∧           -- fence.i
    decode 0x1005302f = .other 0x1005302f ∧           -- lr.d x0, (a0)
    decode 0x00000001 = .other 0x00000001 := by decide -- c.nop parcel

/-- End-to-end statement over instruction words. -/
theorem words_safe_and_terminate {cfg : Cfg} {ws : List Nat} {s0 : St}
    (hc : checkWords cfg ws = true) (he : Entry cfg s0) :
    ∃ k s', k ≤ ws.length ∧ run (ws.map decode) k s0 = .ret (s0.regs 1) s' ∧
      Returned cfg s0 s' := by
  obtain ⟨k, s', hk, hrun, hret⟩ := safe_and_terminates (prog := ws.map decode) hc he
  exact ⟨k, s', by rw [List.length_map] at hk; exact hk, hrun, hret⟩

/-- The demo module as machine words is admitted. -/
theorem demoWords_checked :
    checkWords cfgDemo
      [0x00053283, 0x7f82f313, 0x006583b3, 0x0003b603, 0x025646b3, 0x00068463, 0x00d53423,
       0x00008067] = true := by decide

end SmodeSfiChecker
