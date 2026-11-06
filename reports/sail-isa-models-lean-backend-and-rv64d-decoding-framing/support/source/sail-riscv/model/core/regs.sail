// =======================================================================================
// This Sail RISC-V architecture model, comprising all files and
// directories except where otherwise noted is subject the BSD
// two-clause license in the LICENSE file.
//
// SPDX-License-Identifier: BSD-2-Clause
// =======================================================================================

// program counter

register PC       : xlenbits
register nextPC   : xlenbits

// Mappings for encoding

mapping encdec_reg : regidx <-> bits(5) = {
  forwards Regidx(r) => zero_extend(r),
  backwards r if not(base_E_enabled) | r[4] == 0b0 => Regidx(r[regidx_bit_width - 1 .. 0]),
}

mapping encdec_creg : cregidx <-> bits(3) = { Cregidx(r) <-> r }

// mappings for assembly

mapping reg_abi_name_raw : bits(5) <-> string = {
    0b00000 <-> "zero",
    0b00001 <-> "ra",
    0b00010 <-> "sp",
    0b00011 <-> "gp",
    0b00100 <-> "tp",
    0b00101 <-> "t0",
    0b00110 <-> "t1",
    0b00111 <-> "t2",
    0b01000 <-> "s0",
    0b01000 <-> "fp",
    0b01001 <-> "s1",
    0b01010 <-> "a0",
    0b01011 <-> "a1",
    0b01100 <-> "a2",
    0b01101 <-> "a3",
    0b01110 <-> "a4",
    0b01111 <-> "a5",
    0b10000 <-> "a6",
    0b10001 <-> "a7",
    0b10010 <-> "s2",
    0b10011 <-> "s3",
    0b10100 <-> "s4",
    0b10101 <-> "s5",
    0b10110 <-> "s6",
    0b10111 <-> "s7",
    0b11000 <-> "s8",
    0b11001 <-> "s9",
    0b11010 <-> "s10",
    0b11011 <-> "s11",
    0b11100 <-> "t3",
    0b11101 <-> "t4",
    0b11110 <-> "t5",
    0b11111 <-> "t6",
}

mapping reg_arch_name_raw : bits(5) <-> string = {
    0b00000 <-> "x0",
    0b00001 <-> "x1",
    0b00010 <-> "x2",
    0b00011 <-> "x3",
    0b00100 <-> "x4",
    0b00101 <-> "x5",
    0b00110 <-> "x6",
    0b00111 <-> "x7",
    0b01000 <-> "x8",
    0b01001 <-> "x9",
    0b01010 <-> "x10",
    0b01011 <-> "x11",
    0b01100 <-> "x12",
    0b01101 <-> "x13",
    0b01110 <-> "x14",
    0b01111 <-> "x15",
    0b10000 <-> "x16",
    0b10001 <-> "x17",
    0b10010 <-> "x18",
    0b10011 <-> "x19",
    0b10100 <-> "x20",
    0b10101 <-> "x21",
    0b10110 <-> "x22",
    0b10111 <-> "x23",
    0b11000 <-> "x24",
    0b11001 <-> "x25",
    0b11010 <-> "x26",
    0b11011 <-> "x27",
    0b11100 <-> "x28",
    0b11101 <-> "x29",
    0b11110 <-> "x30",
    0b11111 <-> "x31",
}

// Mapping from 4/5 back to 5 bits here makes the name mapping much easier.
// If you call `reg_name("t6")` on an E hart you'll get a mapping failure.
mapping reg_name : regidx <-> string = {
  encdec_reg(i) if get_config_use_abi_names()      <-> reg_abi_name_raw(i),
  encdec_reg(i) if not(get_config_use_abi_names()) <-> reg_arch_name_raw(i),
}

// Special mapping for the sp register for use in assembly for sp-relative
// instructions where the argument *must* be `sp` (or `x2`).
mapping sp_reg_name : unit <-> string = {
  () if get_config_use_abi_names() <-> "sp",
  () if not(get_config_use_abi_names()) <-> "x2",
}

mapping creg_name : cregidx <-> string = { Cregidx(i) <-> reg_name(encdec_reg(0b01 @ i)) }

function xreg_write_callback(reg : regidx, value : xlenbits) -> unit = {
  let name = reg_name(reg);
  xreg_full_write_callback(name, reg, value);
}

// register file and accessors

register x1  : regtype
register x2  : regtype
register x3  : regtype
register x4  : regtype
register x5  : regtype
register x6  : regtype
register x7  : regtype
register x8  : regtype
register x9  : regtype
register x10 : regtype
register x11 : regtype
register x12 : regtype
register x13 : regtype
register x14 : regtype
register x15 : regtype
register x16 : regtype
register x17 : regtype
register x18 : regtype
register x19 : regtype
register x20 : regtype
register x21 : regtype
register x22 : regtype
register x23 : regtype
register x24 : regtype
register x25 : regtype
register x26 : regtype
register x27 : regtype
register x28 : regtype
register x29 : regtype
register x30 : regtype
register x31 : regtype

function rX (Regno(r) : regno) -> xlenbits = {
  let v : regtype =
    match r {
      0 => zero_reg,
      1 => x1,
      2 => x2,
      3 => x3,
      4 => x4,
      5 => x5,
      6 => x6,
      7 => x7,
      8 => x8,
      9 => x9,
      10 => x10,
      11 => x11,
      12 => x12,
      13 => x13,
      14 => x14,
      15 => x15,
      16 => x16,
      17 => x17,
      18 => x18,
      19 => x19,
      20 => x20,
      21 => x21,
      22 => x22,
      23 => x23,
      24 => x24,
      25 => x25,
      26 => x26,
      27 => x27,
      28 => x28,
      29 => x29,
      30 => x30,
      31 => x31,
    };
  regval_from_reg(v)
}

function wX (Regno(r) : regno, in_v : xlenbits) -> unit = {
  let v = regval_into_reg(in_v);
  match r {
    0  => (),
    1  => x1 = v,
    2  => x2 = v,
    3  => x3 = v,
    4  => x4 = v,
    5  => x5 = v,
    6  => x6 = v,
    7  => x7 = v,
    8  => x8 = v,
    9  => x9 = v,
    10 => x10 = v,
    11 => x11 = v,
    12 => x12 = v,
    13 => x13 = v,
    14 => x14 = v,
    15 => x15 = v,
    16 => x16 = v,
    17 => x17 = v,
    18 => x18 = v,
    19 => x19 = v,
    20 => x20 = v,
    21 => x21 = v,
    22 => x22 = v,
    23 => x23 = v,
    24 => x24 = v,
    25 => x25 = v,
    26 => x26 = v,
    27 => x27 = v,
    28 => x28 = v,
    29 => x29 = v,
    30 => x30 = v,
    31 => x31 = v,
  };
  if r != 0 then xreg_write_callback(Regidx(to_bits(r)), in_v)
}

function rX_bits(Regidx(i) : regidx) -> xlenbits = rX(Regno(unsigned(i)))

function wX_bits(Regidx(i) : regidx, data : xlenbits) -> unit = {
  wX(Regno(unsigned(i))) = data
}

overload X = {rX_bits, wX_bits, rX, wX}

// X_pair accesses a pair of registers. If the index is x0 then
// it acts as if both registers in the pair are x0.

function rX_pair_bits(i : regidx) -> bits(xlen * 2) =
  if i != zreg then X(i + 1) @ X(i) else zeros()

function wX_pair_bits(i : regidx, data : bits(xlen * 2)) -> unit =
  if i != zreg then {
    X(i) = data[xlen - 1 .. 0];
    X(i + 1) = data[xlen * 2 - 1 .. xlen];
  }

overload X_pair = {rX_pair_bits, wX_pair_bits}
