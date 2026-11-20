#![no_std]
#![forbid(unsafe_code)]

//! Self-contained `#![no_std]` `#![forbid(unsafe_code)]` BTL superblock +
//! sub-register allocation certificate checker in two semantically equivalent
//! Rust styles (`seed_core` vs `idiomatic_safe`) for empirical `rustc` MIR
//! subset census and `-O0` vs `-O3` execution benchmarking.

pub const STATUS_OK: u32 = 0;
pub const ERR_BAD_HEADER: u32 = 1;
pub const ERR_OUT_OF_BOUNDS: u32 = 2;
pub const ERR_INVALID_OP: u32 = 3;
pub const ERR_DISJOINT_OVERLAP: u32 = 4;
pub const ERR_NUW_UNPROVED: u32 = 5;
pub const ERR_FREEZE_DUPLICATED: u32 = 6;
pub const ERR_FARKAS_FAILED: u32 = 7;
pub const ERR_EXIT_MISMATCH: u32 = 8;
pub const ERR_UNSEEDED_SRC: u32 = 9;
pub const ERR_CLOBBER_HI_LANE: u32 = 10;
pub const ERR_DIRTY_YMM_AT_EXIT: u32 = 11;
pub const ERR_PARMOVE_CLOBBER: u32 = 12;

pub const MAX_NODES: usize = 32;
pub const MAX_EXITS: usize = 4;
pub const MAX_FARKAS: usize = 4;
pub const MAX_REGS: usize = 16;
pub const MAX_SLOTS: usize = 16;
pub const MAX_RA_OPS: usize = 32;
pub const MAX_PAR_MOVES: usize = 8;

/// Sub-register slice widths matching x86-64 / MiniMach lane partitions.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum SubRegSlice {
    Lo8 = 0,
    Hi8 = 1,
    Lo16 = 2,
    Lo32 = 3,
    Full64 = 4,
    Xmm128 = 5,
    Ymm256 = 6,
}

/// Hardware upper-lane behavior on a sub-register write.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum WriteMode {
    PreserveUpper = 0,
    ZeroExtend64 = 1,
    ZeroExtend256 = 2,
}

/// 10-lane bitmask over `[b0..b7, xmm_hi, ymm_hi]`.
pub const LANE_ALL_64: u16 = 0x00FF;
pub const LANE_ALL_128: u16 = 0x01FF;
pub const LANE_ALL_256: u16 = 0x03FF;
pub const LANE_HI32: u16 = 0x00F0;
pub const LANE_YMM_HI: u16 = 0x0200;

/// BTL superblock IR node opcodes.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum BtlOp {
    Input = 0,
    Const64 = 1,
    Freeze = 2,
    Add64 = 3,
    Sub64 = 4,
    And64 = 5,
    Or64 = 6,
    Xor64 = 7,
    Shl64 = 8,
    Lshr64 = 9,
}

/// Poison-flag modifier bitmask on a BTL node.
pub const FLAG_NUW: u8 = 0x01;
pub const FLAG_NSW: u8 = 0x02;
pub const FLAG_DISJOINT: u8 = 0x04;
pub const FLAG_NON_POISON_KNOWN: u8 = 0x08;

/// Compact BTL symbolic node (fixed 16-byte layout, zero heap allocation).
#[derive(Clone, Copy)]
pub struct BtlNode {
    pub op: u8,
    pub flags: u8,
    pub lhs: u16,
    pub rhs: u16,
    pub imm: u64,
}

/// Farkas linear certificate row: `a_x * x + a_c <= rhs` with multiplier `lambda >= 0`.
#[derive(Clone, Copy)]
pub struct FarkasRow {
    pub ax: i64,
    pub ac: i64,
    pub bound: i64,
    pub lambda: u64,
}

/// Self-contained BTL superblock equivalence & side-condition certificate.
#[derive(Clone, Copy)]
pub struct BtlSuperblockCert {
    pub src_len: usize,
    pub tgt_len: usize,
    pub num_exits: usize,
    pub num_farkas: usize,
    pub tgt_check_op: u8,
    pub tgt_elim_guard: u8,
    pub src_nodes: [BtlNode; MAX_NODES],
    pub tgt_nodes: [BtlNode; MAX_NODES],
    pub src_exits: [u16; MAX_EXITS],
    pub tgt_exits: [u16; MAX_EXITS],
    pub farkas_rows: [FarkasRow; MAX_FARKAS],
    pub src_guard_removed_flag: u8,
}

/// Register-allocation edit opcode.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum RaOpKind {
    SeedReg = 0,
    Move = 1,
    Spill = 2,
    Reload = 3,
    Remat = 4,
    DirtyYmm = 5,
    VZeroUpper = 6,
    AbiCallOrRet = 7,
    ParMoveSwap = 8,
}

/// Compact RegAlloc certificate operation.
#[derive(Clone, Copy)]
pub struct RaOp {
    pub kind: u8,
    pub dst_is_slot: u8,
    pub dst_idx: u8,
    pub src_is_slot: u8,
    pub src_idx: u8,
    pub slice: u8,
    pub write_mode: u8,
    pub vreg: u16,
    pub live_upper_mask: u16,
}

/// Self-contained RegAlloc + CFG `vzeroupper` certificate.
#[derive(Clone, Copy)]
pub struct RegAllocCertPacket {
    pub num_ops: usize,
    pub ops: [RaOp; MAX_RA_OPS],
    pub expected_final_reg0_vreg: u16,
    pub expected_final_reg0_lanes: u16,
    pub par_dst: [u8; MAX_PAR_MOVES],
    pub par_src: [u8; MAX_PAR_MOVES],
    pub par_len: usize,
    pub par_scratch: u8,
    pub par_slice: u8,
}

/// Deterministic summary returned by both checker implementations.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct CertCheckSummary {
    pub status: u32,
    pub checked_nodes: u32,
    pub checked_ra_ops: u32,
    pub digest: u64,
}

/// Restricted seed-subset implementation using scalar locals, fixed arrays,
/// `while` index loops, and explicit `u32` error codes (zero `Iterator`,
/// zero `?`, zero fat-slice projections, zero panic-heavy unwrap chains).
pub mod seed_core {
    use super::*;

    #[inline(never)]
    pub fn slice_written_lanes(slice_code: u8) -> u16 {
        if slice_code == SubRegSlice::Lo8 as u8 {
            0x0001
        } else if slice_code == SubRegSlice::Hi8 as u8 {
            0x0002
        } else if slice_code == SubRegSlice::Lo16 as u8 {
            0x0003
        } else if slice_code == SubRegSlice::Lo32 as u8 {
            0x000F
        } else if slice_code == SubRegSlice::Full64 as u8 {
            LANE_ALL_64
        } else if slice_code == SubRegSlice::Xmm128 as u8 {
            LANE_ALL_128
        } else if slice_code == SubRegSlice::Ymm256 as u8 {
            LANE_ALL_256
        } else {
            0
        }
    }

    #[inline(never)]
    pub fn mode_zeroed_lanes(slice_code: u8, mode_code: u8) -> u16 {
        if mode_code == WriteMode::PreserveUpper as u8 {
            0
        } else if mode_code == WriteMode::ZeroExtend64 as u8 {
            if slice_code == SubRegSlice::Lo32 as u8 {
                LANE_HI32
            } else {
                0
            }
        } else if mode_code == WriteMode::ZeroExtend256 as u8 {
            if slice_code <= SubRegSlice::Xmm128 as u8 {
                LANE_YMM_HI
            } else {
                0
            }
        } else {
            0xFFFF
        }
    }

    #[inline(never)]
    pub fn valid_write_mode(slice_code: u8, mode_code: u8) -> bool {
        if mode_code == WriteMode::PreserveUpper as u8 {
            slice_code != SubRegSlice::Lo32 as u8
        } else if mode_code == WriteMode::ZeroExtend64 as u8 {
            slice_code == SubRegSlice::Lo32 as u8
        } else if mode_code == WriteMode::ZeroExtend256 as u8 {
            slice_code == SubRegSlice::Xmm128 as u8 || slice_code == SubRegSlice::Ymm256 as u8
        } else {
            false
        }
    }

    /// Canonicalize algebraic forms to symbolic equivalence tags (`tag`, `k0`, `k1`, `non_poison`)
    /// so valid BTL target rewrites (e.g., `x + x` <-> `x << 1`, `or disjoint` <-> `add nuw`,
    /// redundant `freeze` elimination when `non_poison`, and Farkas-proved guard removal) unify.
    #[inline(never)]
    pub fn analyze_btl_dag(
        nodes: &[BtlNode; MAX_NODES],
        len: usize,
        out_k0: &mut [u64; MAX_NODES],
        out_k1: &mut [u64; MAX_NODES],
        out_np: &mut [u8; MAX_NODES],
        out_sem_hash: &mut [u64; MAX_NODES],
        out_freeze_count: &mut [u8; MAX_NODES],
        enforce_tgt_rules: bool,
    ) -> u32 {
        if len == 0 || len > MAX_NODES {
            return ERR_BAD_HEADER;
        }
        let mut i: usize = 0;
        while i < len {
            let n = nodes[i];
            let op = n.op;
            out_freeze_count[i] = 0;
            if op == BtlOp::Input as u8 {
                let mut k0: u64 = 0;
                if n.imm == 1 {
                    // Input slot 1 represents an aligned index (low bit 0).
                    k0 = 1;
                } else if n.imm == 2 {
                    // Input slot 2 represents a non-negative 6-bit index (< 64).
                    k0 = !0x3F_u64;
                }
                out_k0[i] = k0;
                out_k1[i] = 0;
                out_np[i] = if (n.flags & FLAG_NON_POISON_KNOWN) != 0 {
                    1
                } else {
                    0
                };
                out_sem_hash[i] = 0x1000_0001_u64.wrapping_add(n.imm.wrapping_mul(0x9E37_79B9));
            } else if op == BtlOp::Const64 as u8 {
                out_k0[i] = !n.imm;
                out_k1[i] = n.imm;
                out_np[i] = 1;
                out_sem_hash[i] = 0x2000_0003_u64 ^ n.imm.wrapping_mul(0xBF58_476D_1CE4_E5B9);
            } else if op == BtlOp::Freeze as u8 {
                let l = n.lhs as usize;
                if l >= i {
                    return ERR_OUT_OF_BOUNDS;
                }
                out_k0[i] = out_k0[l];
                out_k1[i] = out_k1[l];
                out_np[i] = 1;
                if out_np[l] != 0 {
                    out_sem_hash[i] = out_sem_hash[l];
                } else {
                    if enforce_tgt_rules {
                        let next_c = out_freeze_count[l].saturating_add(1);
                        out_freeze_count[l] = next_c;
                        if next_c > 1 {
                            return ERR_FREEZE_DUPLICATED;
                        }
                    }
                    out_sem_hash[i] = out_sem_hash[l] ^ 0xF1EA_5EED_0000_0007_u64;
                }
            } else if op == BtlOp::Add64 as u8
                || op == BtlOp::Sub64 as u8
                || op == BtlOp::And64 as u8
                || op == BtlOp::Or64 as u8
                || op == BtlOp::Xor64 as u8
                || op == BtlOp::Shl64 as u8
                || op == BtlOp::Lshr64 as u8
            {
                let l = n.lhs as usize;
                let r = n.rhs as usize;
                if l >= i || r >= i {
                    return ERR_OUT_OF_BOUNDS;
                }
                let lk0 = out_k0[l];
                let rk0 = out_k0[r];
                let lk1 = out_k1[l];
                let rk1 = out_k1[r];
                let l_poss_one = !lk0;
                let r_poss_one = !rk0;
                let both_np = if out_np[l] != 0 && out_np[r] != 0 { 1 } else { 0 };

                if op == BtlOp::Or64 as u8 && (n.flags & FLAG_DISJOINT) != 0 {
                    if enforce_tgt_rules && (l_poss_one & r_poss_one) != 0 {
                        return ERR_DISJOINT_OVERLAP;
                    }
                }
                if op == BtlOp::Add64 as u8 && (n.flags & FLAG_NUW) != 0 {
                    let l_max = !lk0;
                    let r_max = !rk0;
                    let (_, overflow) = l_max.overflowing_add(r_max);
                    if enforce_tgt_rules && overflow {
                        return ERR_NUW_UNPROVED;
                    }
                }

                // Compute forward KnownBits + poison safety.
                let mut k0: u64 = 0;
                let mut k1: u64 = 0;
                let mut np: u8 = both_np;
                let h: u64;

                if op == BtlOp::And64 as u8 {
                    k0 = lk0 | rk0;
                    k1 = lk1 & rk1;
                    h = (out_sem_hash[l] ^ out_sem_hash[r]).wrapping_add(0x31);
                } else if op == BtlOp::Or64 as u8 {
                    k0 = lk0 & rk0;
                    k1 = lk1 | rk1;
                    if (n.flags & FLAG_DISJOINT) != 0 && (l_poss_one & r_poss_one) != 0 {
                        np = 0;
                    }
                    // Disjoint OR canonicalizes to the same arithmetic sum hash as ADD when non-overlapping.
                    if (l_poss_one & r_poss_one) == 0 {
                        h = out_sem_hash[l].wrapping_add(out_sem_hash[r]).wrapping_add(0x41);
                    } else {
                        h = (out_sem_hash[l] | out_sem_hash[r]).wrapping_add(0x43);
                    }
                } else if op == BtlOp::Xor64 as u8 {
                    k0 = (lk0 & rk0) | (lk1 & rk1);
                    k1 = (lk0 & rk1) | (lk1 & rk0);
                    if out_sem_hash[l] == out_sem_hash[r] && out_np[l] != 0 {
                        k0 = u64::MAX;
                        k1 = 0;
                        h = 0x2000_0003_u64;
                    } else {
                        h = (out_sem_hash[l] ^ out_sem_hash[r]).wrapping_add(0x51);
                    }
                } else if op == BtlOp::Add64 as u8 {
                    let (_, overflow) = (!lk0).overflowing_add(!rk0);
                    if (n.flags & FLAG_NUW) != 0 && overflow {
                        np = 0;
                    }
                    if (l_poss_one & r_poss_one) == 0 {
                        k0 = lk0 & rk0;
                        k1 = lk1 | rk1;
                    }
                    // x + x canonicalizes identically to x << 1.
                    if out_sem_hash[l] == out_sem_hash[r] {
                        h = out_sem_hash[l].wrapping_mul(2).wrapping_add(0x71);
                    } else {
                        h = out_sem_hash[l].wrapping_add(out_sem_hash[r]).wrapping_add(0x41);
                    }
                } else if op == BtlOp::Sub64 as u8 {
                    if out_sem_hash[l] == out_sem_hash[r] && out_np[l] != 0 {
                        k0 = u64::MAX;
                        k1 = 0;
                        h = 0x2000_0003_u64;
                    } else {
                        h = out_sem_hash[l].wrapping_sub(out_sem_hash[r]).wrapping_add(0x61);
                    }
                } else if op == BtlOp::Shl64 as u8 {
                    if nodes[r].op == BtlOp::Const64 as u8 {
                        let sh = nodes[r].imm;
                        if sh >= 64 {
                            np = 0;
                            h = 0xDEAD_0064;
                        } else {
                            let s = sh as u32;
                            let low_mask = if s == 0 { 0 } else { (1_u64 << s) - 1 };
                            k0 = (lk0 << s) | low_mask;
                            k1 = lk1 << s;
                            if sh == 1 {
                                h = out_sem_hash[l].wrapping_mul(2).wrapping_add(0x71);
                            } else {
                                h = (out_sem_hash[l].rotate_left(s)) ^ sh.wrapping_mul(0x73);
                            }
                        }
                    } else {
                        np = 0;
                        h = out_sem_hash[l] ^ out_sem_hash[r].wrapping_add(0x79);
                    }
                } else {
                    // Lshr64
                    if nodes[r].op == BtlOp::Const64 as u8 && nodes[r].imm < 64 {
                        let s = nodes[r].imm as u32;
                        let hi_mask = if s == 0 { 0 } else { !((1_u64 << (64 - s)) - 1) };
                        k0 = (lk0 >> s) | hi_mask;
                        k1 = lk1 >> s;
                        h = (out_sem_hash[l].rotate_right(s)) ^ nodes[r].imm.wrapping_mul(0x83);
                    } else {
                        np = 0;
                        h = out_sem_hash[l] ^ out_sem_hash[r].wrapping_add(0x89);
                    }
                }

                out_k0[i] = k0;
                out_k1[i] = k1;
                out_np[i] = np;
                out_sem_hash[i] = h;
            } else {
                return ERR_INVALID_OP;
            }
            i += 1;
        }
        STATUS_OK
    }

    #[inline(never)]
    pub fn check_farkas_unsat(rows: &[FarkasRow; MAX_FARKAS], num_rows: usize) -> bool {
        if num_rows == 0 || num_rows > MAX_FARKAS {
            return false;
        }
        let mut sum_ax: i64 = 0;
        let mut sum_ac: i64 = 0;
        let mut sum_bound: i64 = 0;
        let mut i: usize = 0;
        while i < num_rows {
            let row = rows[i];
            let lam = row.lambda as i64;
            if lam < 0 {
                return false;
            }
            sum_ax = sum_ax.saturating_add(lam.saturating_mul(row.ax));
            sum_ac = sum_ac.saturating_add(lam.saturating_mul(row.ac));
            sum_bound = sum_bound.saturating_add(lam.saturating_mul(row.bound));
            i += 1;
        }
        sum_ax == 0 && sum_ac == 0 && sum_bound <= -1
    }

    #[inline(never)]
    pub fn check_btl_superblock(cert: &BtlSuperblockCert) -> (u32, u64) {
        if cert.num_exits == 0 || cert.num_exits > MAX_EXITS {
            return (ERR_BAD_HEADER, 0);
        }
        let mut sk0 = [0_u64; MAX_NODES];
        let mut sk1 = [0_u64; MAX_NODES];
        let mut snp = [0_u8; MAX_NODES];
        let mut shash = [0_u64; MAX_NODES];
        let mut sfc = [0_u8; MAX_NODES];

        let src_rc = analyze_btl_dag(
            &cert.src_nodes,
            cert.src_len,
            &mut sk0,
            &mut sk1,
            &mut snp,
            &mut shash,
            &mut sfc,
            false,
        );
        if src_rc != STATUS_OK {
            return (src_rc, 0);
        }

        let mut tk0 = [0_u64; MAX_NODES];
        let mut tk1 = [0_u64; MAX_NODES];
        let mut tnp = [0_u8; MAX_NODES];
        let mut thash = [0_u64; MAX_NODES];
        let mut tfc = [0_u8; MAX_NODES];

        let tgt_rc = analyze_btl_dag(
            &cert.tgt_nodes,
            cert.tgt_len,
            &mut tk0,
            &mut tk1,
            &mut tnp,
            &mut thash,
            &mut tfc,
            true,
        );
        if tgt_rc != STATUS_OK {
            return (tgt_rc, 0);
        }

        if cert.src_guard_removed_flag != 0 {
            if !check_farkas_unsat(&cert.farkas_rows, cert.num_farkas) {
                return (ERR_FARKAS_FAILED, 0);
            }
        }

        let mut digest: u64 = 0xCAFE_BABE_0000_0001_u64;
        let mut ex: usize = 0;
        while ex < cert.num_exits {
            let si = cert.src_exits[ex] as usize;
            let ti = cert.tgt_exits[ex] as usize;
            if si >= cert.src_len || ti >= cert.tgt_len {
                return (ERR_OUT_OF_BOUNDS, 0);
            }
            if shash[si] != thash[ti] {
                return (ERR_EXIT_MISMATCH, 0);
            }
            // Target may not introduce new poison where source was provably non-poison.
            if snp[si] != 0 && tnp[ti] == 0 {
                return (ERR_EXIT_MISMATCH, 0);
            }
            digest = digest.rotate_left(7) ^ thash[ti];
            ex += 1;
        }
        (STATUS_OK, digest)
    }

    #[inline(never)]
    pub fn check_regalloc_packet(pkt: &RegAllocCertPacket) -> (u32, u64) {
        if pkt.num_ops == 0 || pkt.num_ops > MAX_RA_OPS {
            return (ERR_BAD_HEADER, 0);
        }
        let mut reg_vreg = [0_u16; MAX_REGS];
        let mut reg_lanes = [0_u16; MAX_REGS];
        let mut slot_vreg = [0_u16; MAX_SLOTS];
        let mut slot_lanes = [0_u16; MAX_SLOTS];
        let mut dirty_ymm_mask: u16 = 0;

        let mut step: usize = 0;
        while step < pkt.num_ops {
            let op = pkt.ops[step];
            let k = op.kind;
            if k == RaOpKind::SeedReg as u8 {
                let dst = op.dst_idx as usize;
                if dst >= MAX_REGS {
                    return (ERR_OUT_OF_BOUNDS, 0);
                }
                let w_lanes = slice_written_lanes(op.slice);
                if w_lanes == 0 || !valid_write_mode(op.slice, op.write_mode) {
                    return (ERR_INVALID_OP, 0);
                }
                let z_lanes = mode_zeroed_lanes(op.slice, op.write_mode);
                if (op.live_upper_mask & z_lanes) != 0 {
                    return (ERR_CLOBBER_HI_LANE, 0);
                }
                reg_vreg[dst] = op.vreg;
                reg_lanes[dst] = w_lanes;
                if op.slice == SubRegSlice::Ymm256 as u8 {
                    dirty_ymm_mask |= 1_u16 << dst;
                }
            } else if k == RaOpKind::Move as u8
                || k == RaOpKind::Spill as u8
                || k == RaOpKind::Reload as u8
            {
                let dst_idx = op.dst_idx as usize;
                let src_idx = op.src_idx as usize;
                if op.dst_is_slot != 0 && dst_idx >= MAX_SLOTS {
                    return (ERR_OUT_OF_BOUNDS, 0);
                }
                if op.dst_is_slot == 0 && dst_idx >= MAX_REGS {
                    return (ERR_OUT_OF_BOUNDS, 0);
                }
                if op.src_is_slot != 0 && src_idx >= MAX_SLOTS {
                    return (ERR_OUT_OF_BOUNDS, 0);
                }
                if op.src_is_slot == 0 && src_idx >= MAX_REGS {
                    return (ERR_OUT_OF_BOUNDS, 0);
                }
                let w_lanes = slice_written_lanes(op.slice);
                if w_lanes == 0 || !valid_write_mode(op.slice, op.write_mode) {
                    return (ERR_INVALID_OP, 0);
                }
                let z_lanes = mode_zeroed_lanes(op.slice, op.write_mode);

                // Repaired `regalloc2` update order: kill/evict overlapping dst lanes FIRST,
                // BEFORE querying src_loc (prevents missing-else phantom value reuse).
                if op.dst_is_slot != 0 {
                    slot_lanes[dst_idx] &= !(w_lanes | z_lanes);
                } else {
                    if (op.live_upper_mask & z_lanes) != 0 {
                        return (ERR_CLOBBER_HI_LANE, 0);
                    }
                    reg_lanes[dst_idx] &= !(w_lanes | z_lanes);
                    if (z_lanes & LANE_YMM_HI) != 0 {
                        dirty_ymm_mask &= !(1_u16 << dst_idx);
                    }
                }

                let (src_v, src_l) = if op.src_is_slot != 0 {
                    (slot_vreg[src_idx], slot_lanes[src_idx])
                } else {
                    (reg_vreg[src_idx], reg_lanes[src_idx])
                };

                // Fail closed if source does not hold ALL required slice lanes.
                if (src_l & w_lanes) != w_lanes || src_v == 0 {
                    return (ERR_UNSEEDED_SRC, 0);
                }

                if op.dst_is_slot != 0 {
                    slot_vreg[dst_idx] = src_v;
                    slot_lanes[dst_idx] |= w_lanes;
                } else {
                    reg_vreg[dst_idx] = src_v;
                    reg_lanes[dst_idx] |= w_lanes;
                    if (w_lanes & LANE_YMM_HI) != 0 {
                        dirty_ymm_mask |= 1_u16 << dst_idx;
                    }
                }
            } else if k == RaOpKind::Remat as u8 {
                let dst_idx = op.dst_idx as usize;
                if op.dst_is_slot != 0 || dst_idx >= MAX_REGS {
                    return (ERR_OUT_OF_BOUNDS, 0);
                }
                let w_lanes = slice_written_lanes(op.slice);
                if w_lanes == 0 || !valid_write_mode(op.slice, op.write_mode) {
                    return (ERR_INVALID_OP, 0);
                }
                let z_lanes = mode_zeroed_lanes(op.slice, op.write_mode);
                // Enforce Invariant (B): zero-extending remat cannot clobber live upper lanes.
                if (op.live_upper_mask & z_lanes) != 0 {
                    return (ERR_CLOBBER_HI_LANE, 0);
                }
                reg_vreg[dst_idx] = op.vreg;
                reg_lanes[dst_idx] = (reg_lanes[dst_idx] & !z_lanes) | w_lanes;
                if (z_lanes & LANE_YMM_HI) != 0 {
                    dirty_ymm_mask &= !(1_u16 << dst_idx);
                }
            } else if k == RaOpKind::DirtyYmm as u8 {
                let dst_idx = op.dst_idx as usize;
                if dst_idx >= MAX_REGS {
                    return (ERR_OUT_OF_BOUNDS, 0);
                }
                dirty_ymm_mask |= 1_u16 << dst_idx;
            } else if k == RaOpKind::VZeroUpper as u8 {
                let mut r: usize = 0;
                while r < MAX_REGS {
                    reg_lanes[r] &= !LANE_YMM_HI;
                    r += 1;
                }
                dirty_ymm_mask = 0;
            } else if k == RaOpKind::AbiCallOrRet as u8 {
                if dirty_ymm_mask != 0 {
                    return (ERR_DIRTY_YMM_AT_EXIT, 0);
                }
            } else if k == RaOpKind::ParMoveSwap as u8 {
                if pkt.par_len == 0 || pkt.par_len > MAX_PAR_MOVES {
                    return (ERR_BAD_HEADER, 0);
                }
                let w_lanes = slice_written_lanes(pkt.par_slice);
                let scratch = pkt.par_scratch as usize;
                if scratch >= MAX_REGS {
                    return (ERR_OUT_OF_BOUNDS, 0);
                }
                // Scratch must not appear as any source or destination of the parallel cycle.
                let mut m: usize = 0;
                while m < pkt.par_len {
                    let pd = pkt.par_dst[m] as usize;
                    let ps = pkt.par_src[m] as usize;
                    if pd >= MAX_REGS || ps >= MAX_REGS {
                        return (ERR_OUT_OF_BOUNDS, 0);
                    }
                    if pd == scratch || ps == scratch {
                        return (ERR_PARMOVE_CLOBBER, 0);
                    }
                    if (reg_lanes[ps] & w_lanes) != w_lanes {
                        return (ERR_UNSEEDED_SRC, 0);
                    }
                    m += 1;
                }
                // Apply simultaneous snapshot update across par_len elements.
                let mut next_vreg = [0_u16; MAX_PAR_MOVES];
                let mut next_lanes = [0_u16; MAX_PAR_MOVES];
                let mut p: usize = 0;
                while p < pkt.par_len {
                    let ps = pkt.par_src[p] as usize;
                    next_vreg[p] = reg_vreg[ps];
                    next_lanes[p] = reg_lanes[ps] & w_lanes;
                    p += 1;
                }
                let mut q: usize = 0;
                while q < pkt.par_len {
                    let pd = pkt.par_dst[q] as usize;
                    reg_vreg[pd] = next_vreg[q];
                    reg_lanes[pd] = (reg_lanes[pd] & !w_lanes) | next_lanes[q];
                    q += 1;
                }
            } else {
                return (ERR_INVALID_OP, 0);
            }
            step += 1;
        }

        if reg_vreg[0] != pkt.expected_final_reg0_vreg
            || (reg_lanes[0] & pkt.expected_final_reg0_lanes) != pkt.expected_final_reg0_lanes
        {
            return (ERR_EXIT_MISMATCH, 0);
        }
        let digest = (reg_vreg[0] as u64)
            | ((reg_lanes[0] as u64) << 16)
            | ((dirty_ymm_mask as u64) << 32);
        (STATUS_OK, digest)
    }

    #[inline(never)]
    pub fn verify_bundle_seed(btl: &BtlSuperblockCert, ra: &RegAllocCertPacket) -> CertCheckSummary {
        let (b_rc, b_dig) = check_btl_superblock(btl);
        if b_rc != STATUS_OK {
            return CertCheckSummary {
                status: b_rc,
                checked_nodes: btl.src_len.saturating_add(btl.tgt_len) as u32,
                checked_ra_ops: 0,
                digest: 0,
            };
        }
        let (r_rc, r_dig) = check_regalloc_packet(ra);
        if r_rc != STATUS_OK {
            return CertCheckSummary {
                status: r_rc,
                checked_nodes: btl.src_len.saturating_add(btl.tgt_len) as u32,
                checked_ra_ops: ra.num_ops as u32,
                digest: 0,
            };
        }
        CertCheckSummary {
            status: STATUS_OK,
            checked_nodes: (btl.src_len + btl.tgt_len) as u32,
            checked_ra_ops: ra.num_ops as u32,
            digest: b_dig ^ r_dig,
        }
    }
}

/// Idiomatic safe Rust implementation of the exact same BTL + RegAlloc checker
/// using `Result`, `?`, slices, iterators, and `Option` enums, to empirically
/// quantify MIR construct divergence against `seed_core`.
pub mod idiomatic_safe {
    use super::*;

    #[derive(Clone, Copy, PartialEq, Eq)]
    pub struct CheckErr(pub u32);

    fn slice_written_lanes_id(slice_code: u8) -> Result<u16, CheckErr> {
        match slice_code {
            0 => Ok(0x0001),
            1 => Ok(0x0002),
            2 => Ok(0x0003),
            3 => Ok(0x000F),
            4 => Ok(LANE_ALL_64),
            5 => Ok(LANE_ALL_128),
            6 => Ok(LANE_ALL_256),
            _ => Err(CheckErr(ERR_INVALID_OP)),
        }
    }

    fn mode_zeroed_lanes_id(slice_code: u8, mode_code: u8) -> Result<u16, CheckErr> {
        match (mode_code, slice_code) {
            (0, s) if s != 3 => Ok(0),
            (1, 3) => Ok(LANE_HI32),
            (2, s) if s <= 5 => Ok(LANE_YMM_HI),
            (2, 6) => Ok(0),
            _ => Err(CheckErr(ERR_INVALID_OP)),
        }
    }

    fn analyze_btl_slice(
        nodes: &[BtlNode],
        enforce_tgt_rules: bool,
    ) -> Result<([u64; MAX_NODES], [u8; MAX_NODES], [u64; MAX_NODES]), CheckErr> {
        if nodes.is_empty() || nodes.len() > MAX_NODES {
            return Err(CheckErr(ERR_BAD_HEADER));
        }
        let mut k0 = [0_u64; MAX_NODES];
        let mut k1 = [0_u64; MAX_NODES];
        let mut np = [0_u8; MAX_NODES];
        let mut hash = [0_u64; MAX_NODES];
        let mut freeze_cnt = [0_u8; MAX_NODES];

        for (i, &n) in nodes.iter().enumerate() {
            match n.op {
                0 => {
                    k0[i] = match n.imm {
                        1 => 1,
                        2 => !0x3F_u64,
                        _ => 0,
                    };
                    np[i] = u8::from((n.flags & FLAG_NON_POISON_KNOWN) != 0);
                    hash[i] = 0x1000_0001_u64.wrapping_add(n.imm.wrapping_mul(0x9E37_79B9));
                }
                1 => {
                    k0[i] = !n.imm;
                    k1[i] = n.imm;
                    np[i] = 1;
                    hash[i] = 0x2000_0003_u64 ^ n.imm.wrapping_mul(0xBF58_476D_1CE4_E5B9);
                }
                2 => {
                    let l = usize::from(n.lhs);
                    if l >= i {
                        return Err(CheckErr(ERR_OUT_OF_BOUNDS));
                    }
                    k0[i] = k0[l];
                    k1[i] = k1[l];
                    np[i] = 1;
                    if np[l] != 0 {
                        hash[i] = hash[l];
                    } else {
                        if enforce_tgt_rules {
                            freeze_cnt[l] = freeze_cnt[l].saturating_add(1);
                            if freeze_cnt[l] > 1 {
                                return Err(CheckErr(ERR_FREEZE_DUPLICATED));
                            }
                        }
                        hash[i] = hash[l] ^ 0xF1EA_5EED_0000_0007_u64;
                    }
                }
                op @ 3..=9 => {
                    let (l, r) = (usize::from(n.lhs), usize::from(n.rhs));
                    if l >= i || r >= i {
                        return Err(CheckErr(ERR_OUT_OF_BOUNDS));
                    }
                    let (lk0, rk0) = (k0[l], k0[r]);
                    let (lk1, rk1) = (k1[l], k1[r]);
                    let (l_poss, r_poss) = (!lk0, !rk0);
                    let mut node_np = u8::from(np[l] != 0 && np[r] != 0);

                    if op == 6 && (n.flags & FLAG_DISJOINT) != 0 {
                        if enforce_tgt_rules && (l_poss & r_poss) != 0 {
                            return Err(CheckErr(ERR_DISJOINT_OVERLAP));
                        }
                        if (l_poss & r_poss) != 0 {
                            node_np = 0;
                        }
                    }
                    if op == 3 && (n.flags & FLAG_NUW) != 0 {
                        let (_, ov) = l_poss.overflowing_add(r_poss);
                        if enforce_tgt_rules && ov {
                            return Err(CheckErr(ERR_NUW_UNPROVED));
                        }
                        if ov {
                            node_np = 0;
                        }
                    }

                    match op {
                        5 => {
                            k0[i] = lk0 | rk0;
                            k1[i] = lk1 & rk1;
                            hash[i] = (hash[l] ^ hash[r]).wrapping_add(0x31);
                        }
                        6 => {
                            k0[i] = lk0 & rk0;
                            k1[i] = lk1 | rk1;
                            hash[i] = if (l_poss & r_poss) == 0 {
                                hash[l].wrapping_add(hash[r]).wrapping_add(0x41)
                            } else {
                                (hash[l] | hash[r]).wrapping_add(0x43)
                            };
                        }
                        7 => {
                            k0[i] = (lk0 & rk0) | (lk1 & rk1);
                            k1[i] = (lk0 & rk1) | (lk1 & rk0);
                            if hash[l] == hash[r] && np[l] != 0 {
                                k0[i] = u64::MAX;
                                k1[i] = 0;
                                hash[i] = 0x2000_0003_u64;
                            } else {
                                hash[i] = (hash[l] ^ hash[r]).wrapping_add(0x51);
                            }
                        }
                        3 => {
                            if (l_poss & r_poss) == 0 {
                                k0[i] = lk0 & rk0;
                                k1[i] = lk1 | rk1;
                            }
                            hash[i] = if hash[l] == hash[r] {
                                hash[l].wrapping_mul(2).wrapping_add(0x71)
                            } else {
                                hash[l].wrapping_add(hash[r]).wrapping_add(0x41)
                            };
                        }
                        4 => {
                            if hash[l] == hash[r] && np[l] != 0 {
                                k0[i] = u64::MAX;
                                k1[i] = 0;
                                hash[i] = 0x2000_0003_u64;
                            } else {
                                hash[i] = hash[l].wrapping_sub(hash[r]).wrapping_add(0x61);
                            }
                        }
                        8 => {
                            if nodes[r].op == 1 && nodes[r].imm < 64 {
                                let sh = nodes[r].imm as u32;
                                let low_mask = if sh == 0 { 0 } else { (1_u64 << sh) - 1 };
                                k0[i] = (lk0 << sh) | low_mask;
                                k1[i] = lk1 << sh;
                                hash[i] = if sh == 1 {
                                    hash[l].wrapping_mul(2).wrapping_add(0x71)
                                } else {
                                    hash[l].rotate_left(sh) ^ nodes[r].imm.wrapping_mul(0x73)
                                };
                            } else {
                                node_np = 0;
                                hash[i] = if nodes[r].op == 1 && nodes[r].imm >= 64 {
                                    0xDEAD_0064
                                } else {
                                    hash[l] ^ hash[r].wrapping_add(0x79)
                                };
                            }
                        }
                        _ => {
                            if nodes[r].op == 1 && nodes[r].imm < 64 {
                                let sh = nodes[r].imm as u32;
                                let hi_mask = if sh == 0 { 0 } else { !((1_u64 << (64 - sh)) - 1) };
                                k0[i] = (lk0 >> sh) | hi_mask;
                                k1[i] = lk1 >> sh;
                                hash[i] = hash[l].rotate_right(sh) ^ nodes[r].imm.wrapping_mul(0x83);
                            } else {
                                node_np = 0;
                                hash[i] = hash[l] ^ hash[r].wrapping_add(0x89);
                            }
                        }
                    }
                    np[i] = node_np;
                }
                _ => return Err(CheckErr(ERR_INVALID_OP)),
            }
        }
        Ok((k0, np, hash))
    }

    fn check_btl_idiomatic(cert: &BtlSuperblockCert) -> Result<u64, CheckErr> {
        if cert.num_exits == 0 || cert.num_exits > MAX_EXITS {
            return Err(CheckErr(ERR_BAD_HEADER));
        }
        let src_slice = cert.src_nodes.get(..cert.src_len).ok_or(CheckErr(ERR_BAD_HEADER))?;
        let tgt_slice = cert.tgt_nodes.get(..cert.tgt_len).ok_or(CheckErr(ERR_BAD_HEADER))?;
        let (_, snp, shash) = analyze_btl_slice(src_slice, false)?;
        let (_, tnp, thash) = analyze_btl_slice(tgt_slice, true)?;

        if cert.src_guard_removed_flag != 0 {
            let rows = cert.farkas_rows.get(..cert.num_farkas).ok_or(CheckErr(ERR_FARKAS_FAILED))?;
            if rows.is_empty() {
                return Err(CheckErr(ERR_FARKAS_FAILED));
            }
            let (mut sx, mut sc, mut sb) = (0_i64, 0_i64, 0_i64);
            for r in rows {
                let lam = i64::try_from(r.lambda).map_err(|_| CheckErr(ERR_FARKAS_FAILED))?;
                sx = sx.saturating_add(lam.saturating_mul(r.ax));
                sc = sc.saturating_add(lam.saturating_mul(r.ac));
                sb = sb.saturating_add(lam.saturating_mul(r.bound));
            }
            if !(sx == 0 && sc == 0 && sb <= -1) {
                return Err(CheckErr(ERR_FARKAS_FAILED));
            }
        }

        let mut digest: u64 = 0xCAFE_BABE_0000_0001_u64;
        for (&s_idx, &t_idx) in cert.src_exits[..cert.num_exits]
            .iter()
            .zip(cert.tgt_exits[..cert.num_exits].iter())
        {
            let si = usize::from(s_idx);
            let ti = usize::from(t_idx);
            let sh = *shash.get(si).ok_or(CheckErr(ERR_OUT_OF_BOUNDS))?;
            let th = *thash.get(ti).ok_or(CheckErr(ERR_OUT_OF_BOUNDS))?;
            if sh != th || (snp[si] != 0 && tnp[ti] == 0) {
                return Err(CheckErr(ERR_EXIT_MISMATCH));
            }
            digest = digest.rotate_left(7) ^ th;
        }
        Ok(digest)
    }

    fn check_regalloc_idiomatic(pkt: &RegAllocCertPacket) -> Result<u64, CheckErr> {
        let ops = pkt.ops.get(..pkt.num_ops).ok_or(CheckErr(ERR_BAD_HEADER))?;
        if ops.is_empty() {
            return Err(CheckErr(ERR_BAD_HEADER));
        }
        let mut regs: [(u16, u16); MAX_REGS] = [(0, 0); MAX_REGS];
        let mut slots: [(u16, u16); MAX_SLOTS] = [(0, 0); MAX_SLOTS];
        let mut dirty_ymm_mask: u16 = 0;

        for &op in ops {
            match op.kind {
                0 => {
                    let dst = usize::from(op.dst_idx);
                    if dst >= MAX_REGS {
                        return Err(CheckErr(ERR_OUT_OF_BOUNDS));
                    }
                    let w = slice_written_lanes_id(op.slice)?;
                    let z = mode_zeroed_lanes_id(op.slice, op.write_mode)?;
                    if (op.live_upper_mask & z) != 0 {
                        return Err(CheckErr(ERR_CLOBBER_HI_LANE));
                    }
                    regs[dst] = (op.vreg, w);
                    if op.slice == SubRegSlice::Ymm256 as u8 {
                        dirty_ymm_mask |= 1_u16 << dst;
                    }
                }
                1..=3 => {
                    let w = slice_written_lanes_id(op.slice)?;
                    let z = mode_zeroed_lanes_id(op.slice, op.write_mode)?;
                    let dst_idx = usize::from(op.dst_idx);
                    let src_idx = usize::from(op.src_idx);
                    let dst_ref = if op.dst_is_slot != 0 {
                        slots.get_mut(dst_idx).ok_or(CheckErr(ERR_OUT_OF_BOUNDS))?
                    } else {
                        if (op.live_upper_mask & z) != 0 {
                            return Err(CheckErr(ERR_CLOBBER_HI_LANE));
                        }
                        if (z & LANE_YMM_HI) != 0 && dst_idx < MAX_REGS {
                            dirty_ymm_mask &= !(1_u16 << dst_idx);
                        }
                        regs.get_mut(dst_idx).ok_or(CheckErr(ERR_OUT_OF_BOUNDS))?
                    };
                    dst_ref.1 &= !(w | z);

                    let (src_v, src_l) = if op.src_is_slot != 0 {
                        *slots.get(src_idx).ok_or(CheckErr(ERR_OUT_OF_BOUNDS))?
                    } else {
                        *regs.get(src_idx).ok_or(CheckErr(ERR_OUT_OF_BOUNDS))?
                    };
                    if (src_l & w) != w || src_v == 0 {
                        return Err(CheckErr(ERR_UNSEEDED_SRC));
                    }

                    if op.dst_is_slot != 0 {
                        slots[dst_idx].0 = src_v;
                        slots[dst_idx].1 |= w;
                    } else {
                        regs[dst_idx].0 = src_v;
                        regs[dst_idx].1 |= w;
                        if (w & LANE_YMM_HI) != 0 {
                            dirty_ymm_mask |= 1_u16 << dst_idx;
                        }
                    }
                }
                4 => {
                    if op.dst_is_slot != 0 {
                        return Err(CheckErr(ERR_OUT_OF_BOUNDS));
                    }
                    let dst_idx = usize::from(op.dst_idx);
                    let slot = regs.get_mut(dst_idx).ok_or(CheckErr(ERR_OUT_OF_BOUNDS))?;
                    let w = slice_written_lanes_id(op.slice)?;
                    let z = mode_zeroed_lanes_id(op.slice, op.write_mode)?;
                    if (op.live_upper_mask & z) != 0 {
                        return Err(CheckErr(ERR_CLOBBER_HI_LANE));
                    }
                    slot.0 = op.vreg;
                    slot.1 = (slot.1 & !z) | w;
                    if (z & LANE_YMM_HI) != 0 {
                        dirty_ymm_mask &= !(1_u16 << dst_idx);
                    }
                }
                5 => {
                    let dst = usize::from(op.dst_idx);
                    if dst >= MAX_REGS {
                        return Err(CheckErr(ERR_OUT_OF_BOUNDS));
                    }
                    dirty_ymm_mask |= 1_u16 << dst;
                }
                6 => {
                    for r in regs.iter_mut() {
                        r.1 &= !LANE_YMM_HI;
                    }
                    dirty_ymm_mask = 0;
                }
                7 => {
                    if dirty_ymm_mask != 0 {
                        return Err(CheckErr(ERR_DIRTY_YMM_AT_EXIT));
                    }
                }
                8 => {
                    if pkt.par_len == 0 || pkt.par_len > MAX_PAR_MOVES {
                        return Err(CheckErr(ERR_BAD_HEADER));
                    }
                    let w = slice_written_lanes_id(pkt.par_slice)?;
                    let scratch = usize::from(pkt.par_scratch);
                    if scratch >= MAX_REGS {
                        return Err(CheckErr(ERR_OUT_OF_BOUNDS));
                    }
                    let mut staged = [(0_u16, 0_u16); MAX_PAR_MOVES];
                    for (k, (&pd_u8, &ps_u8)) in pkt.par_dst[..pkt.par_len]
                        .iter()
                        .zip(pkt.par_src[..pkt.par_len].iter())
                        .enumerate()
                    {
                        let (pd, ps) = (usize::from(pd_u8), usize::from(ps_u8));
                        if pd >= MAX_REGS || ps >= MAX_REGS {
                            return Err(CheckErr(ERR_OUT_OF_BOUNDS));
                        }
                        if pd == scratch || ps == scratch {
                            return Err(CheckErr(ERR_PARMOVE_CLOBBER));
                        }
                        if (regs[ps].1 & w) != w {
                            return Err(CheckErr(ERR_UNSEEDED_SRC));
                        }
                        staged[k] = (regs[ps].0, regs[ps].1 & w);
                    }
                    for (k, &pd_u8) in pkt.par_dst[..pkt.par_len].iter().enumerate() {
                        let pd = usize::from(pd_u8);
                        regs[pd].0 = staged[k].0;
                        regs[pd].1 = (regs[pd].1 & !w) | staged[k].1;
                    }
                }
                _ => return Err(CheckErr(ERR_INVALID_OP)),
            }
        }

        if regs[0].0 != pkt.expected_final_reg0_vreg
            || (regs[0].1 & pkt.expected_final_reg0_lanes) != pkt.expected_final_reg0_lanes
        {
            return Err(CheckErr(ERR_EXIT_MISMATCH));
        }
        Ok((u64::from(regs[0].0))
            | (u64::from(regs[0].1) << 16)
            | (u64::from(dirty_ymm_mask) << 32))
    }

    #[inline(never)]
    pub fn verify_bundle_idiomatic(
        btl: &BtlSuperblockCert,
        ra: &RegAllocCertPacket,
    ) -> CertCheckSummary {
        match (check_btl_idiomatic(btl), check_regalloc_idiomatic(ra)) {
            (Ok(b_dig), Ok(r_dig)) => CertCheckSummary {
                status: STATUS_OK,
                checked_nodes: (btl.src_len + btl.tgt_len) as u32,
                checked_ra_ops: ra.num_ops as u32,
                digest: b_dig ^ r_dig,
            },
            (Err(e), _) => CertCheckSummary {
                status: e.0,
                checked_nodes: (btl.src_len + btl.tgt_len) as u32,
                checked_ra_ops: 0,
                digest: 0,
            },
            (Ok(_), Err(e)) => CertCheckSummary {
                status: e.0,
                checked_nodes: (btl.src_len + btl.tgt_len) as u32,
                checked_ra_ops: ra.num_ops as u32,
                digest: 0,
            },
        }
    }
}
