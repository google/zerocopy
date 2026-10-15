// =======================================================================================
// This Sail RISC-V architecture model, comprising all files and
// directories except where otherwise noted is subject the BSD
// two-clause license in the LICENSE file.
//
// SPDX-License-Identifier: BSD-2-Clause
// =======================================================================================

// *****************************************************************
// This file specifies the instructions in the base integer set.

function clause currentlyEnabled(Ext_C) = hartSupports(Ext_C) & misa[C] == 0b1
function clause currentlyEnabled(Ext_Zca) = hartSupports(Ext_Zca) & (currentlyEnabled(Ext_C) | not(hartSupports(Ext_C)))

// *****************************************************************
union clause instruction = UTYPE : (bits(20), regidx, uop)

mapping encdec_uop : uop <-> bits(7) = {
  LUI   <-> 0b0110111,
  AUIPC <-> 0b0010111
}

mapping clause encdec = UTYPE(imm, rd, op)
  <-> imm @ encdec_reg(rd) @ encdec_uop(op)

$[split op]
function clause execute UTYPE(imm, rd, op) = {
  let off : xlenbits = sign_extend(imm @ 0x000);
  X(rd) = match op {
    LUI   => off,
    AUIPC => get_arch_pc() + off
  };
  RETIRE_SUCCESS
}

mapping utype_mnemonic : uop <-> string = {
  LUI   <-> "lui",
  AUIPC <-> "auipc"
}

mapping clause assembly = UTYPE(imm, rd, op)
  <-> utype_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_signed_20(imm)

// *****************************************************************

// Jump execution to a specified target address. This can fail
// due to the target not being 4-byte aligned, or due to extension checks.
// Callers must ensure that the target address is 2-byte aligned.
function jump_to(target : xlenbits) -> ExecutionResult = {
  // Extensions get the first checks on the prospective target address.
  match ext_control_check_pc(target) {
    Some(e) => return Ext_ControlAddr_Check_Failure(e),
    None()  => (),
  };

  // Perform standard alignment check.
  // Check target is at least 2-byte aligned (callers must ensure
  // this so it can be an assertion).
  assert(target[0] == 0b0);
  // If it is not 4-byte aligned and compressed instructions are
  // not enabled then raise an alignment exception.
  if bit_to_bool(target[1]) & not(currentlyEnabled(Ext_Zca))
  then return trap(exception_context(E_Fetch_Addr_Align(), target));

  set_next_pc(target);
  RETIRE_SUCCESS
}

// *****************************************************************
union clause instruction = JAL : (bits(21), regidx)
$[wavedrom "_ offset[20:1] _ _ dest JAL"]
mapping clause encdec = JAL(imm @ 0b0, rd)
  <-> imm[19] @ imm[9..0] @ imm[10] @ imm[18..11] @ encdec_reg(rd) @ 0b1101111

function clause execute JAL(imm, rd) = {
  let link_address = get_next_pc();
  match jump_to(PC + sign_extend(imm)) {
    Retire_Success() => { X(rd) = link_address; Retire_Success() },
    failure => failure,
  }
}

// TODO: handle 2-byte-alignment in mappings

mapping clause assembly = JAL(imm, rd)
  <-> "jal" ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_signed_21(imm)

// *****************************************************************
union clause instruction = JALR : (bits(12), regidx, regidx)

$[wavedrom "offset[11:0] base 0 dest JALR"]
mapping clause encdec = JALR(imm, rs1, rd)
  <-> imm @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1100111

mapping clause assembly = JALR(imm, rs1, rd)
  <-> "jalr" ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_signed_12(imm) ^ "(" ^ reg_name(rs1) ^ ")"

// see jalr_seq.sail or jalr_rmem.sail for the execute clause.

// *****************************************************************
union clause instruction = BTYPE : (bits(13), regidx, regidx, bop)

mapping encdec_bop : bop <-> bits(3) = {
  BEQ  <-> 0b000,
  BNE  <-> 0b001,
  BLT  <-> 0b100,
  BGE  <-> 0b101,
  BLTU <-> 0b110,
  BGEU <-> 0b111
}

mapping clause encdec = BTYPE(imm @ 0b0, rs2, rs1, op)
  <-> imm[11] @ imm[9..4] @ encdec_reg(rs2) @ encdec_reg(rs1) @ encdec_bop(op) @ imm[3..0] @ imm[10] @ 0b1100011

$[split op]
function clause execute BTYPE(imm, rs2, rs1, op) = {
  let taken : bool = match op {
    BEQ  => X(rs1) == X(rs2),
    BNE  => X(rs1) != X(rs2),
    BLT  => X(rs1) <_s X(rs2),
    BGE  => X(rs1) >=_s X(rs2),
    BLTU => X(rs1) <_u X(rs2),
    BGEU => X(rs1) >=_u X(rs2)
  };
  if taken
  then jump_to(PC + sign_extend(imm))
  else RETIRE_SUCCESS
}

mapping btype_mnemonic : bop <-> string = {
  BEQ  <-> "beq",
  BNE  <-> "bne",
  BLT  <-> "blt",
  BGE  <-> "bge",
  BLTU <-> "bltu",
  BGEU <-> "bgeu"
}

mapping clause assembly = BTYPE(imm, rs2, rs1, op)
  <-> btype_mnemonic(op) ^ spc() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) ^ sep() ^ hex_bits_signed_13(imm)

// *****************************************************************
union clause instruction = ITYPE : (bits(12), regidx, regidx, iop)

mapping encdec_iop : iop <-> bits(3) = {
  ADDI  <-> 0b000,
  SLTI  <-> 0b010,
  SLTIU <-> 0b011,
  ANDI  <-> 0b111,
  ORI   <-> 0b110,
  XORI  <-> 0b100
}

mapping clause encdec = ITYPE(imm, rs1, rd, op)
  <-> imm @ encdec_reg(rs1) @ encdec_iop(op) @ encdec_reg(rd) @ 0b0010011

$[split op]
function clause execute ITYPE(imm, rs1, rd, op) = {
  let immext : xlenbits = sign_extend(imm);
  X(rd) = match op {
    ADDI  => X(rs1) + immext,
    SLTI  => zero_extend(bool_to_bit(X(rs1) <_s immext)),
    SLTIU => zero_extend(bool_to_bit(X(rs1) <_u immext)),
    ANDI  => X(rs1) & immext,
    ORI   => X(rs1) | immext,
    XORI  => X(rs1) ^ immext
  };
  RETIRE_SUCCESS
}

mapping itype_mnemonic : iop <-> string = {
  ADDI  <-> "addi",
  SLTI  <-> "slti",
  SLTIU <-> "sltiu",
  XORI  <-> "xori",
  ORI   <-> "ori",
  ANDI  <-> "andi"
}

mapping clause assembly = ITYPE(imm, rs1, rd, op)
  <-> itype_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_signed_12(imm)

// *****************************************************************
union clause instruction = SHIFTIOP : (bits(6), regidx, regidx, sop)

mapping encdec_sop : sop <-> bits(3) = {
  SLLI <-> 0b001,
  SRLI <-> 0b101,
  SRAI <-> 0b101
}

mapping clause encdec = SHIFTIOP(shamt, rs1, rd, SLLI)
  <-> 0b000000 @ shamt @ encdec_reg(rs1) @ 0b001 @ encdec_reg(rd) @ 0b0010011
  when xlen == 64 | shamt[5] == 0b0
mapping clause encdec = SHIFTIOP(shamt, rs1, rd, SRLI)
  <-> 0b000000 @ shamt @ encdec_reg(rs1) @ 0b101 @ encdec_reg(rd) @ 0b0010011
  when xlen == 64 | shamt[5] == 0b0
mapping clause encdec = SHIFTIOP(shamt, rs1, rd, SRAI)
  <-> 0b010000 @ shamt @ encdec_reg(rs1) @ 0b101 @ encdec_reg(rd) @ 0b0010011
  when xlen == 64 | shamt[5] == 0b0

$[split op]
function clause execute SHIFTIOP(shamt, rs1, rd, op) = {
  let shamt = shamt[log2_xlen - 1 .. 0];
  X(rd) = match op {
    SLLI => X(rs1) << shamt,
    SRLI => X(rs1) >> shamt,
    SRAI => shift_bits_right_arith(X(rs1), shamt),
  };
  RETIRE_SUCCESS
}

mapping shiftiop_mnemonic : sop <-> string = {
  SLLI <-> "slli",
  SRLI <-> "srli",
  SRAI <-> "srai"
}

mapping clause assembly = SHIFTIOP(shamt, rs1, rd, op)
  <-> shiftiop_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_6(shamt)

// *****************************************************************
union clause instruction = RTYPE : (regidx, regidx, regidx, rop)

mapping clause encdec = RTYPE(rs2, rs1, rd, ADD)  <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, SLT)  <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b010 @ encdec_reg(rd) @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, SLTU) <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b011 @ encdec_reg(rd) @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, AND)  <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b111 @ encdec_reg(rd) @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, OR)   <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b110 @ encdec_reg(rd) @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, XOR)  <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b100 @ encdec_reg(rd) @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, SLL)  <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b001 @ encdec_reg(rd) @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, SRL)  <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b101 @ encdec_reg(rd) @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, SUB)  <-> 0b0100000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, SRA)  <-> 0b0100000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b101 @ encdec_reg(rd) @ 0b0110011

$[split op]
function clause execute RTYPE(rs2, rs1, rd, op) = {
  X(rd) = match op {
    ADD  => X(rs1) + X(rs2),
    SLT  => zero_extend(bool_to_bit(X(rs1) <_s X(rs2))),
    SLTU => zero_extend(bool_to_bit(X(rs1) <_u X(rs2))),
    AND  => X(rs1) & X(rs2),
    OR   => X(rs1) | X(rs2),
    XOR  => X(rs1) ^ X(rs2),
    SLL  => X(rs1) << X(rs2)[log2_xlen - 1 .. 0],
    SRL  => X(rs1) >> X(rs2)[log2_xlen - 1 .. 0],
    SUB  => X(rs1) - X(rs2),
    SRA  => shift_bits_right_arith(X(rs1), X(rs2)[log2_xlen - 1 .. 0]),
  };
  RETIRE_SUCCESS
}

mapping rtype_mnemonic : rop <-> string = {
  ADD  <-> "add",
  SLT  <-> "slt",
  SLTU <-> "sltu",
  AND  <-> "and",
  OR   <-> "or",
  XOR  <-> "xor",
  SLL  <-> "sll",
  SRL  <-> "srl",
  SUB  <-> "sub",
  SRA  <-> "sra"
}

mapping clause assembly = RTYPE(rs2, rs1, rd, op)
  <-> rtype_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

// *****************************************************************
union clause instruction = LOAD : (bits(12), regidx, regidx, bool, word_width)

// unsigned loads are only present for widths strictly less than xlen,
// signed loads also present for widths equal to xlen
function valid_load_encdec(width : word_width, is_unsigned : bool) -> bool =
  (width < xlen_bytes) | (not(is_unsigned) & width <= xlen_bytes)

val extend_value : forall 'n, 0 < 'n <= xlen. (bool, bits('n)) -> xlenbits
function extend_value(is_unsigned, value) = if is_unsigned then zero_extend(value) else sign_extend(value)

$[wavedrom "offset[11:0] base _ width dest LOAD"]
mapping clause encdec = LOAD(imm, rs1, rd, is_unsigned, width)
  <-> imm @ encdec_reg(rs1) @ bool_bit(is_unsigned) @ width_enc(width) @ encdec_reg(rd) @ 0b0000011
  when valid_load_encdec(width, is_unsigned)

function clause execute LOAD(imm, rs1, rd, is_unsigned, width) = {
  let offset : xlenbits = sign_extend(imm);

  // This is checked during decoding.
  assert(width <= xlen_bytes);

  match vmem_read(rs1, offset, width, Load(Data), false, false, false) {
    Ok(data) => {
      X(rd) = extend_value(is_unsigned, data);
      RETIRE_SUCCESS
    },
    Err(e) => e,
  }
}

mapping maybe_u : bool <-> string = {
  true  <-> "u",
  false <-> ""
}

mapping clause assembly = LOAD(imm, rs1, rd, is_unsigned, width)
  <-> "l" ^ width_mnemonic(width) ^ maybe_u(is_unsigned) ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_signed_12(imm) ^ "(" ^ reg_name(rs1) ^ ")"

// *****************************************************************
union clause instruction = STORE : (bits(12), regidx, regidx, word_width)

$[wavedrom "offset[11:5] src base _ width offset[4:0] STORE"]
mapping clause encdec = STORE(imm, rs2, rs1, width)
  <-> imm[11..5] @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b0 @ width_enc(width) @ imm[4..0] @ 0b0100011
  when width <= xlen_bytes

function clause execute STORE(imm, rs2, rs1, width) = {
  let offset : xlenbits = sign_extend(imm);

  // This is checked during decoding.
  assert(width <= xlen_bytes);

  // FIXME: the read of `rs2` should not be done before the
  // `mem_write_ea` of the effective address.
  // See https://github.com/riscv/sail-riscv/issues/1761.

  let data = X(rs2)[width * 8 - 1 .. 0];
  match vmem_write(rs1, offset, width, data, Store(Data), false, false, false) {
    Ok(_) => RETIRE_SUCCESS,
    Err(e) => e,
  }
}

mapping clause assembly = STORE(imm, rs2, rs1, width)
  <-> "s" ^ width_mnemonic(width) ^ spc() ^ reg_name(rs2) ^ sep() ^ hex_bits_signed_12(imm) ^ opt_spc() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"

// *****************************************************************
union clause instruction = ADDIW : (bits(12), regidx, regidx)

$[wavedrom "I-immediate[11:0] src ADDIW dest OP-IMM-32"]
mapping clause encdec = ADDIW(imm, rs1, rd)
  <-> imm @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0011011
  when xlen == 64

function clause execute ADDIW(imm, rs1, rd) = {
  let result = X(rs1) + sign_extend(imm);
  X(rd) = sign_extend(result[31..0]);
  RETIRE_SUCCESS
}

mapping clause assembly = ADDIW(imm, rs1, rd)
  <-> "addiw" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_signed_12(imm)
  when xlen == 64

// *****************************************************************
union clause instruction = RTYPEW : (regidx, regidx, regidx, ropw)

mapping clause encdec = RTYPEW(rs2, rs1, rd, ADDW)
  <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0111011
  when xlen == 64
mapping clause encdec = RTYPEW(rs2, rs1, rd, SUBW)
  <-> 0b0100000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0111011
  when xlen == 64
mapping clause encdec = RTYPEW(rs2, rs1, rd, SLLW)
  <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b001 @ encdec_reg(rd) @ 0b0111011
  when xlen == 64
mapping clause encdec = RTYPEW(rs2, rs1, rd, SRLW)
  <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b101 @ encdec_reg(rd) @ 0b0111011
  when xlen == 64
mapping clause encdec = RTYPEW(rs2, rs1, rd, SRAW)
  <-> 0b0100000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b101 @ encdec_reg(rd) @ 0b0111011
  when xlen == 64

$[split op]
function clause execute RTYPEW(rs2, rs1, rd, op) = {
  let rs1_val = X(rs1)[31..0];
  let rs2_val = X(rs2)[31..0];
  let result : bits(32) = match op {
    ADDW => rs1_val + rs2_val,
    SUBW => rs1_val - rs2_val,
    SLLW => rs1_val << rs2_val[4..0],
    SRLW => rs1_val >> rs2_val[4..0],
    SRAW => shift_bits_right_arith(rs1_val, rs2_val[4..0]),
  };
  X(rd) = sign_extend(result);
  RETIRE_SUCCESS
}

mapping rtypew_mnemonic : ropw <-> string = {
  ADDW <-> "addw",
  SUBW <-> "subw",
  SLLW <-> "sllw",
  SRLW <-> "srlw",
  SRAW <-> "sraw"
}

mapping clause assembly = RTYPEW(rs2, rs1, rd, op)
  <-> rtypew_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
  when xlen == 64

// *****************************************************************
union clause instruction = SHIFTIWOP : (bits(5), regidx, regidx, sopw)

mapping clause encdec = SHIFTIWOP(shamt, rs1, rd, SLLIW)
  <-> 0b0000000 @ shamt @ encdec_reg(rs1) @ 0b001 @ encdec_reg(rd) @ 0b0011011
  when xlen == 64
mapping clause encdec = SHIFTIWOP(shamt, rs1, rd, SRLIW)
  <-> 0b0000000 @ shamt @ encdec_reg(rs1) @ 0b101 @ encdec_reg(rd) @ 0b0011011
  when xlen == 64
mapping clause encdec = SHIFTIWOP(shamt, rs1, rd, SRAIW)
  <-> 0b0100000 @ shamt @ encdec_reg(rs1) @ 0b101 @ encdec_reg(rd) @ 0b0011011
  when xlen == 64

$[split op]
function clause execute SHIFTIWOP(shamt, rs1, rd, op) = {
  let rs1_val = X(rs1)[31..0];
  let result : bits(32) = match op {
    SLLIW => rs1_val << shamt,
    SRLIW => rs1_val >> shamt,
    SRAIW => shift_bits_right_arith(rs1_val, shamt),
  };
  X(rd) = sign_extend(result);
  RETIRE_SUCCESS
}

mapping shiftiwop_mnemonic : sopw <-> string = {
  SLLIW <-> "slliw",
  SRLIW <-> "srliw",
  SRAIW <-> "sraiw"
}

mapping clause assembly = SHIFTIWOP(shamt, rs1, rd, op)
  <-> shiftiwop_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_5(shamt)
  when xlen == 64

// *****************************************************************
union clause instruction = FENCE_TSO : unit

mapping clause encdec = FENCE_TSO()
  <-> 0b1000 @ 0b0011 @ 0b0011 @ 0b00000 @ 0b000 @ 0b00000 @ 0b0001111

function clause execute FENCE_TSO() = {
  sail_barrier(Barrier_RISCV_tso);
  RETIRE_SUCCESS
}

mapping clause assembly = FENCE_TSO()
  <-> "fence.tso"

// *****************************************************************
union clause instruction = FENCE : (bits(4), bits(4), bits(4), regidx, regidx)

// Note: FENCE_TSO and PAUSE are encoded as FENCE so they must come first.
mapping clause encdec = FENCE(fm, pred, succ, rs, rd)
  <-> fm : bits(4) @ pred : bits(4) @ succ : bits(4) @ encdec_reg(rs) @ 0b000 @ encdec_reg(rd) @ 0b0001111

function effective_fence_set(set : bits(4), fiom : bool) -> bits(4) = {
  // The bits are IORW. If FIOM is set then I implies R and O implies W.
  if fiom then {
    set[3 .. 2] @ (set[1 .. 0] | set[3 .. 2])
  } else set
}

function clause execute FENCE(_fm, pred, succ, _rs, _rd) = {
  // "The unused fields in the FENCE instructions - rs1 and rd - are reserved for
  // finer-grain fences in future extensions. For forward compatibility, base
  // implementations shall ignore these fields. Likewise, many fm and
  // predecessor/successor set settings are also reserved for future use.
  // Base implementations shall treat all such reserved configurations as FENCE
  // instructions (with fm=0000)."

  // If the FIOM bit in menvcfg/senvcfg is set then the I/O bits can imply R/W.
  let fiom = is_fiom_active();
  let pred = effective_fence_set(pred, fiom);
  let succ = effective_fence_set(succ, fiom);

  // Ignore I/O bits.
  match (pred[1 .. 0], succ[1 .. 0]) {
    (0b11, 0b11) => sail_barrier(Barrier_RISCV_rw_rw),
    (0b10, 0b11) => sail_barrier(Barrier_RISCV_r_rw),
    (0b10, 0b10) => sail_barrier(Barrier_RISCV_r_r),
    (0b11, 0b01) => sail_barrier(Barrier_RISCV_rw_w),
    (0b01, 0b01) => sail_barrier(Barrier_RISCV_w_w),
    (0b01, 0b11) => sail_barrier(Barrier_RISCV_w_rw),
    (0b11, 0b10) => sail_barrier(Barrier_RISCV_rw_r),
    (0b10, 0b01) => sail_barrier(Barrier_RISCV_r_w),
    (0b01, 0b10) => sail_barrier(Barrier_RISCV_w_r),

    (_   , 0b00) => (),
    (0b00, _   ) => (),
  };

  generate_event(EV_FENCE);

  RETIRE_SUCCESS
}

mapping bit_maybe_r : bits(1) <-> string = {
  0b1 <-> "r",
  0b0 <-> ""
}

mapping bit_maybe_w : bits(1) <-> string = {
  0b1 <-> "w",
  0b0 <-> ""
}

mapping bit_maybe_i : bits(1) <-> string = {
  0b1 <-> "i",
  0b0 <-> ""
}

mapping bit_maybe_o : bits(1) <-> string = {
  0b1 <-> "o",
  0b0 <-> ""
}

mapping fence_bits : bits(4) <-> string = {
  // Fences with empty predecessor or successor sets are nops.
  // Clang/LLVM's assembly supports using `0` for these.
  // Binutils/GAS does not so you would have to use `.insn` to encode these.
  0b0000 <-> "0",
  i : bits(1) @ o : bits(1) @ r : bits(1) @ w : bits(1) <-> bit_maybe_i(i) ^ bit_maybe_o(o) ^ bit_maybe_r(r) ^ bit_maybe_w(w),
}

// There's no assembly that encodes reserved fences as far as I know.
// Unfortunately we need to split forwards and backwards because there's
// no way to write a zero regidx as a literal.
mapping clause assembly =
  forwards FENCE(0b0000, pred, succ, rs, rd) => "fence" ^ spc() ^ fence_bits(pred) ^ sep() ^ fence_bits(succ)
    when rs == zreg & rd == zreg

// TODO: This hits a Sail compiler bug, https://github.com/rems-project/sail/issues/1577
// however we don't currently use the assembler direction of this mapping so
// it doesn't really matter.
// mapping clause assembly =
//   backwards "fence" ^ spc() ^ fence_bits(pred) ^ sep() ^ fence_bits(succ) => FENCE(0b0000, pred, succ, zreg, zreg)

// *****************************************************************
union clause instruction = ECALL : unit

mapping clause encdec = ECALL()
  <-> 0b000000000000 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011

function clause execute ECALL() = {
  let exc_type : ExceptionType = match cur_privilege {
    User              => E_U_EnvCall(),
    Supervisor        => E_S_EnvCall(),
    Machine           => E_M_EnvCall(),
    VirtualUser       => E_U_EnvCall(),
    VirtualSupervisor => E_VS_EnvCall(),
  };
  let c : ExceptionContext = struct {
    trap           = exc_type,
    excinfo_is_gva = false,
    excinfo        = zeros(),
    excinfo2       = None(),
    excinst        = None(),
    excinst_offset = zeros(),
    ext            = None(),
  };
  trap(c)
}

mapping clause assembly = ECALL() <-> "ecall"

// *****************************************************************

private function xret_modifies_vsstatus(prev_priv : Privilege, new_priv : Privilege) -> bool =
  currentlyEnabled(Ext_H) & read_henvcfg()[DTE] == 0b1
  & (new_priv == VirtualUser | prev_priv == VirtualSupervisor)

/// Clear the double trap bits on MRET or SRET.
function xret_clear_dbltrp(prev_priv : Privilege, new_priv : Privilege) -> unit = {
  // "executing an mret instruction, or executing an sret instruction while the
  // current privilege mode is M, has the following additional effects. The MDT
  // bit is set to 0."
  if currentlyEnabled(Ext_Smdbltrp) & prev_priv == Machine
  then mstatus[MDT] = 0b0;

  // "If the Ssdbltrp extension is also implemented, and the new privilege mode
  // is U, VS, or VU, then sstatus.SDT is also set to 0."
  // "An SRET instruction sets the SDT bit to 0."
  // The second only applies in supervisor mode, see
  // https://github.com/riscv/riscv-isa-manual/issues/2870#issuecomment-4238414283
  if currentlyEnabled(Ext_Ssdbltrp) & (match prev_priv {
    Machine    => new_priv == User | new_priv == VirtualSupervisor | new_priv == VirtualUser,
    Supervisor => true,
    _          => false,
  }) then mstatus[SDT] = 0b0;

  // "when SRET is executed in HS-mode, if the new privilege mode is VU, the
  // SRET instruction sets vsstatus.SDT to 0. When executed in VS-mode,
  // vsstatus.SDT is set to 0."
  // Same goes for MRET: "Additionally, if it is VU, then vsstatus.SDT is also set to 0."
  if currentlyEnabled(Ext_H) & read_henvcfg()[DTE] == 0b1
     & (new_priv == VirtualUser | prev_priv == VirtualSupervisor)
  then vsstatus[SDT] = 0b0;
}

union clause instruction = MRET : unit

mapping clause encdec = MRET()
  <-> 0b0011000 @ 0b00010 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011

function clause execute MRET() = {
  if   cur_privilege != Machine
  then Illegal_Instruction()
  else if not(ext_check_xret_priv(Machine))
  then Ext_XRET_Priv_Failure()
  else {
    let prev_priv = cur_privilege;

    mstatus[MIE]  = mstatus[MPIE];
    mstatus[MPIE] = 0b1;
    // MPV is ignored when MPP=3, as there is no virtual machine mode
    cur_privilege = privLevel_bits((mstatus[MPP], if mstatus[MPP] == 0b11 then 0b0 else mstatus[MPV]));

    mstatus[MPP]  = privLevel_to_bits(if currentlyEnabled(Ext_U) then User else Machine);
    mstatus[MPV]  = 0b0;

    if   cur_privilege != Machine
    then mstatus[MPRV] = 0b0;

    xret_clear_dbltrp(prev_priv, cur_privilege);

    if   hartSupports(Ext_Zicfilp)
    then zicfilp_restore_elp_on_xret(mRET, prev_priv, cur_privilege);

    if hartSupports(Ext_Sdtrig)
    then tcontrol_mret_from_mmode();

    long_csr_write_callback("mstatus", "mstatush", read_mstatus().bits);
    if   xret_modifies_vsstatus(prev_priv, cur_privilege)
    then csr_write_callback("vsstatus", vsstatus.bits[xlen - 1 .. 0]);

    if   get_config_print_exception()
    then print_log("ret-ing from " ^ to_str(prev_priv) ^ " to " ^ to_str(cur_privilege));

    set_next_pc(prepare_xret_target(Machine));
    xret_callback(true);
    RETIRE_SUCCESS
  }
}

mapping clause assembly = MRET() <-> "mret"

// *****************************************************************
union clause instruction = SRET : unit

mapping clause encdec = SRET()
  <-> 0b0001000 @ 0b00010 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011

function clause execute SRET() = {
  let sret_illegal : bool = match cur_privilege {
    User              => true,
    Supervisor        => not(currentlyEnabled(Ext_S)) | mstatus[TSR] == 0b1,
    Machine           => not(currentlyEnabled(Ext_S)),
    VirtualUser       => false,
    VirtualSupervisor => false,
  };
  let sret_virtual : bool = match cur_privilege {
    VirtualUser       => true,
    VirtualSupervisor => hstatus[VTSR] == 0b1,
    _                 => false,
  };
  if        sret_illegal
  then      Illegal_Instruction()
  else if   sret_virtual
  then      Virtual_Instruction()
  else if   not(ext_check_xret_priv(Supervisor))
  then      Ext_XRET_Priv_Failure()
  else {
    let prev_priv = cur_privilege;
    let ret =
      // SRET in VS-Mode
      if inVirtualPrivilege() then {
        let new_priv = if vsstatus[SPP] == 0b1 then VirtualSupervisor else VirtualUser;
        vsstatus[SPP]  = 0b0;
        vsstatus[SIE]  = vsstatus[SPIE];
        vsstatus[SPIE] = 0b1;
        cur_privilege  = new_priv;
        VirtualSupervisor
      } else {
        // SRET in HS-mode or M-mode
        // SPV is only meaningful when H is enabled, otherwise treat as 0
        let new_priv = privLevel_bits((0b0 @ mstatus[SPP], hstatus[SPV] & bool_to_bit(currentlyEnabled(Ext_H))));
        hstatus[SPV]  = 0b0;
        mstatus[SPP]  = 0b0;
        mstatus[SIE]  = mstatus[SPIE];
        mstatus[SPIE] = 0b1;
        if new_priv != Machine
        then mstatus[MPRV] = 0b0;
        cur_privilege = new_priv;
        Supervisor
      };

    xret_clear_dbltrp(prev_priv, cur_privilege);

    if   hartSupports(Ext_Zicfilp)
    then zicfilp_restore_elp_on_xret(sRET, prev_priv, cur_privilege);

    long_csr_write_callback("mstatus", "mstatush", read_mstatus().bits);
    if   privLevel_is_virtual(prev_priv) | xret_modifies_vsstatus(prev_priv, cur_privilege)
    then csr_write_callback("vsstatus", vsstatus.bits[xlen - 1 .. 0])
    else if currentlyEnabled(Ext_H)
    then csr_write_callback("hstatus", hstatus.bits[xlen - 1 .. 0]);

    if   get_config_print_exception()
    then print_log("ret-ing from " ^ to_str(prev_priv) ^ " to " ^ to_str(cur_privilege));

    set_next_pc(prepare_xret_target(ret));
    xret_callback(false);
    RETIRE_SUCCESS
  }
}

mapping clause assembly = SRET() <-> "sret"

// *****************************************************************
union clause instruction = EBREAK : unit

mapping clause encdec = EBREAK()
  <-> 0b000000000001 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011

function clause execute EBREAK() =
  trap(exception_context(E_Breakpoint(Brk_Software), PC))

mapping clause assembly = EBREAK() <-> "ebreak"

// *****************************************************************
union clause instruction = WFI : unit

mapping clause encdec = WFI()
  <-> 0b000100000101 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011

function clause execute WFI() =
  match cur_privilege {
    Machine           => Enter_Wait(WAIT_WFI),
    // mstatus[TW] is checked when the wait times out in
    // `run_hart_waiting()`.
    Supervisor        => Enter_Wait(WAIT_WFI),
    User              => if plat_wfi_available_to_usermode then Enter_Wait(WAIT_WFI) else Illegal_Instruction(),
    // VU never waits. Raises virtual immediately when TW=0, illegal when TW=1
    VirtualUser       => if mstatus[TW] == 0b1
                         then Illegal_Instruction()
                         else Virtual_Instruction(),
    // VS raises illegal immediately when TW=1
    // when TW=0, enters wait, VTW checked on timeout in run_hart_waiting()
    VirtualSupervisor => if mstatus[TW] == 0b1
                         then Illegal_Instruction()
                         else Enter_Wait(WAIT_WFI),
  }

mapping clause assembly = WFI() <-> "wfi"

// *****************************************************************
union clause instruction = SFENCE_VMA : (regidx, regidx)

mapping clause encdec = SFENCE_VMA(rs1, rs2)
  <-> 0b0001001 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ 0b00000 @ 0b1110011
  when virtual_memory_supported() | not(config extensions.Svbare.sfence_vma_illegal_if_svbare_only : bool)

function clause execute SFENCE_VMA(rs1, rs2) = {
  let addr = if rs1 != zreg then Some(X(rs1)) else None();
  // Note, the Sail model does not currently support Sv32 & SXLEN=32 on RV64.
  // In that case this `asidlen` may be incorrect because ASIDMAX for Sv32 is 9,
  // but `asidlen` would have been validated against the ASIDMAX for RV64.
  let asid : option(asidbits) = if rs2 != zreg then Some(if asidlen == 0 then zeros() else zero_extend(X(rs2)[asidlen - 1 .. 0])) else None();
  let vmid = if cur_privilege == VirtualSupervisor then Some(get_vmid(VS_Stage)) else None();
  match cur_privilege {
    User              => Illegal_Instruction(),
    Supervisor        => match mstatus[TVM] {
                           0b1 => Illegal_Instruction(),
                           0b0 => { flush_TLB(asid, vmid, addr, S_Stage); RETIRE_SUCCESS },
                         },
    Machine           => { flush_TLB(asid, vmid, addr, S_Stage); RETIRE_SUCCESS },
    VirtualUser       => Virtual_Instruction(),
    VirtualSupervisor => match hstatus[VTVM] {
                            0b1 => Virtual_Instruction(),
                            0b0 => { flush_TLB(asid, vmid, addr, VS_Stage); RETIRE_SUCCESS },
                         },
  }
}

mapping clause assembly = SFENCE_VMA(rs1, rs2)
  <-> "sfence.vma" ^ spc() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
