//! Empirical probe against unmodified upstream `bytecodealliance/regalloc2`
//! (`v0.15.3`, commit `4eb655fa745fba271af74be8495154a4b0cac56f`) compiled with
//! `--cfg feature="checker"`.
//!
//! 1. Executes positive and negative validation tests against `regalloc2::checker::Checker`,
//!    including two concrete soundness counterexamples triggered by the missing
//!    `else { self.remove_value(&into); }` branch in `CheckerState::update`
//!    (`src/checker.rs:545-562`):
//!      - Witness 1: `Edit::Move` from a clobbered physical register into a live
//!        allocated register overwrites the live value at runtime while `Checker::run()`
//!        returns `Ok(())`.
//!      - Witness 2: `MoveAndScratchResolver`-style save/restore of an unallocated
//!        borrowed scratch register leaves residual VReg Equivalence in the scratch
//!        register after restoring uninitialized stack memory, and `Checker::run()`
//!        returns `Ok(())` when a subsequent instruction reads that register.
//! 2. Measures real allocation latency (`L3`: `Algorithm::Ion` vs `Algorithm::Fastalloc`),
//!    symbolic checker latency (`L5`: `Checker::run`), linear lane-aware certificate
//!    checking latency (`L5`), and output/certificate byte footprints (`L6`) across
//!    five SSA CFG workloads and three target environments (`x86_64`, `aarch64`, `i686`).

use regalloc2::checker::Checker;
use regalloc2::{
    Algorithm, Allocation, Block, Ctx, Edit, Function, Inst, InstRange, MachineEnv, Operand,
    OperandConstraint, OperandKind, OperandPos, Output, PReg, PRegSet, ProgPoint, RegClass,
    RegallocOptions, SpillSlot, VReg,
};
use std::collections::HashMap;
use std::hint::black_box;
use std::time::Instant;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OpKind {
    Normal,
    Branch,
    Ret,
}

#[derive(Clone, Debug)]
struct TestInst {
    kind: OpKind,
    operands: Vec<Operand>,
    clobbers: PRegSet,
}

#[derive(Clone, Debug)]
struct TestFunc {
    insts: Vec<TestInst>,
    blocks: Vec<InstRange>,
    preds: Vec<Vec<Block>>,
    succs: Vec<Vec<Block>>,
    block_params: Vec<Vec<VReg>>,
    branch_args: Vec<Vec<Vec<VReg>>>,
    num_vregs: usize,
    debug_labels: Vec<(VReg, Inst, Inst, u32)>,
}

impl Function for TestFunc {
    fn num_insts(&self) -> usize {
        self.insts.len()
    }
    fn num_blocks(&self) -> usize {
        self.blocks.len()
    }
    fn entry_block(&self) -> Block {
        Block::new(0)
    }
    fn block_insns(&self, block: Block) -> InstRange {
        self.blocks[block.index()]
    }
    fn block_succs(&self, block: Block) -> &[Block] {
        &self.succs[block.index()]
    }
    fn block_preds(&self, block: Block) -> &[Block] {
        &self.preds[block.index()]
    }
    fn block_params(&self, block: Block) -> &[VReg] {
        &self.block_params[block.index()]
    }
    fn is_ret(&self, insn: Inst) -> bool {
        self.insts[insn.index()].kind == OpKind::Ret
    }
    fn is_branch(&self, insn: Inst) -> bool {
        self.insts[insn.index()].kind == OpKind::Branch
    }
    fn branch_blockparams(&self, block: Block, _insn: Inst, succ_idx: usize) -> &[VReg] {
        &self.branch_args[block.index()][succ_idx]
    }
    fn inst_operands(&self, insn: Inst) -> &[Operand] {
        &self.insts[insn.index()].operands
    }
    fn inst_clobbers(&self, insn: Inst) -> PRegSet {
        self.insts[insn.index()].clobbers
    }
    fn num_vregs(&self) -> usize {
        self.num_vregs
    }
    fn debug_value_labels(&self) -> &[(VReg, Inst, Inst, u32)] {
        &self.debug_labels
    }
    fn spillslot_size(&self, regclass: RegClass) -> usize {
        match regclass {
            RegClass::Int => 1,
            RegClass::Float => 1,
            RegClass::Vector => 2,
        }
    }
}

fn env_x86_64() -> MachineEnv {
    // SysV x86-64: 14 allocatable GPRs (excluding RSP, and R11 reserved as scratch),
    // 15 allocatable XMM regs (XMM15 scratch).
    let mut pref_int = PRegSet::empty();
    for r in [0, 1, 2, 6, 7, 8, 9, 10] {
        pref_int.add(PReg::new(r, RegClass::Int));
    }
    let mut nonpref_int = PRegSet::empty();
    for r in [3, 5, 12, 13, 14, 15] {
        nonpref_int.add(PReg::new(r, RegClass::Int));
    }
    let mut pref_flt = PRegSet::empty();
    for r in 0..15 {
        pref_flt.add(PReg::new(r, RegClass::Float));
    }
    MachineEnv {
        preferred_regs_by_class: [pref_int, pref_flt, PRegSet::empty()],
        non_preferred_regs_by_class: [nonpref_int, PRegSet::empty(), PRegSet::empty()],
        scratch_by_class: [
            Some(PReg::new(11, RegClass::Int)),
            Some(PReg::new(15, RegClass::Float)),
            None,
        ],
        fixed_stack_slots: vec![],
    }
}

fn env_aarch64() -> MachineEnv {
    // AAPCS64: X0..X15, X17 caller-saved preferred (X16 scratch, X18 platform reserved,
    // X29 FP, X30 LR), X19..X28 callee-saved non-preferred; V0..V30 (V31 scratch).
    let mut pref_int = PRegSet::empty();
    for r in (0..=15).chain(std::iter::once(17)) {
        pref_int.add(PReg::new(r, RegClass::Int));
    }
    let mut nonpref_int = PRegSet::empty();
    for r in 19..=28 {
        nonpref_int.add(PReg::new(r, RegClass::Int));
    }
    let mut pref_flt = PRegSet::empty();
    for r in 0..8 {
        pref_flt.add(PReg::new(r, RegClass::Float));
    }
    let mut nonpref_flt = PRegSet::empty();
    for r in 8..31 {
        nonpref_flt.add(PReg::new(r, RegClass::Float));
    }
    MachineEnv {
        preferred_regs_by_class: [pref_int, pref_flt, PRegSet::empty()],
        non_preferred_regs_by_class: [nonpref_int, nonpref_flt, PRegSet::empty()],
        scratch_by_class: [
            Some(PReg::new(16, RegClass::Int)),
            Some(PReg::new(31, RegClass::Float)),
            None,
        ],
        fixed_stack_slots: vec![],
    }
}

fn env_i686() -> MachineEnv {
    // 32-bit x86: EAX(0), ECX(1), EDX(2) preferred; EBX(3), ESI(6), EDI(7) non-preferred;
    // EBP(5) scratch; only hw_enc 0..4 (EAX/ECX/EDX/EBX) have 8-bit low/high subregs (`Limit(4)`).
    let mut pref_int = PRegSet::empty();
    for r in [0, 1, 2] {
        pref_int.add(PReg::new(r, RegClass::Int));
    }
    let mut nonpref_int = PRegSet::empty();
    for r in [3, 6, 7] {
        nonpref_int.add(PReg::new(r, RegClass::Int));
    }
    let mut pref_flt = PRegSet::empty();
    for r in 0..7 {
        pref_flt.add(PReg::new(r, RegClass::Float));
    }
    MachineEnv {
        preferred_regs_by_class: [pref_int, pref_flt, PRegSet::empty()],
        non_preferred_regs_by_class: [nonpref_int, PRegSet::empty(), PRegSet::empty()],
        scratch_by_class: [
            Some(PReg::new(5, RegClass::Int)),
            Some(PReg::new(7, RegClass::Float)),
            None,
        ],
        fixed_stack_slots: vec![],
    }
}

/// Concrete single-block interpreter to cross-check `Checker::run()` verdicts.
fn eval_single_block_concrete(func: &TestFunc, out: &Output) -> (u64, u64) {
    let mut ssa_vals: HashMap<VReg, u64> = HashMap::new();
    let mut loc_vals: HashMap<Allocation, u64> = HashMap::new();

    for (idx, inst) in func.insts.iter().enumerate() {
        // Execute SSA semantics
        let mut ssa_sum = 0x1000_0000u64.wrapping_add((idx as u64) * 0x1111);
        for op in &inst.operands {
            if op.kind() == OperandKind::Use {
                ssa_sum = ssa_sum.wrapping_add(*ssa_vals.get(&op.vreg()).unwrap_or(&0xDEAD_BEEF));
            }
        }
        for op in &inst.operands {
            if op.kind() == OperandKind::Def {
                ssa_vals.insert(op.vreg(), ssa_sum);
            }
        }
        if inst.kind == OpKind::Ret {
            // Now execute allocated stream across block 0 for comparison
            for item in out.block_insts_and_edits(func, Block::new(0)) {
                match item {
                    regalloc2::InstOrEdit::Edit(Edit::Move { from, to }) => {
                        let v = *loc_vals.get(from).unwrap_or(&0xBAD0_CAfe_DEAD_0000);
                        loc_vals.insert(*to, v);
                    }
                    regalloc2::InstOrEdit::Inst(ins) => {
                        let ops = func.inst_operands(ins);
                        let allocs = out.inst_allocs(ins);
                        let mut hw_sum =
                            0x1000_0000u64.wrapping_add((ins.index() as u64) * 0x1111);
                        for (op, al) in ops.iter().zip(allocs.iter()) {
                            if op.kind() == OperandKind::Use {
                                hw_sum = hw_sum.wrapping_add(
                                    *loc_vals.get(al).unwrap_or(&0xDEAD_0000_0000_0001),
                                );
                            }
                        }
                        if func.is_ret(ins) {
                            return (ssa_sum, hw_sum);
                        }
                        for clob in func.inst_clobbers(ins) {
                            loc_vals.insert(
                                Allocation::reg(clob),
                                0xC10B_BE20_0000_0000u64 | (clob.index() as u64),
                            );
                        }
                        for (op, al) in ops.iter().zip(allocs.iter()) {
                            if op.kind() == OperandKind::Def {
                                loc_vals.insert(*al, hw_sum);
                            }
                        }
                    }
                }
            }
        }
    }
    (0, 0)
}

/// Fixed sound checker for single-block/CFG checking that (a) kills `into` on untracked
/// `Edit::Move` sources (fixing `src/checker.rs:553-561`) and (b) operates over dense
/// flat bit-packed slot arrays (`RegAllocCert` linear certificate check) rather than
/// `FxHashMap<Allocation, FxHashSet<VReg>>` fixpoint iteration.
struct LinearCertChecker {
    reg_vreg: [u32; 256],
    stack_vreg: Vec<u32>,
}

impl LinearCertChecker {
    const UNTRACKED: u32 = u32::MAX;

    fn new(num_spillslots: usize) -> Self {
        Self {
            reg_vreg: [Self::UNTRACKED; 256],
            stack_vreg: vec![Self::UNTRACKED; num_spillslots + 8],
        }
    }

    #[inline(always)]
    fn get(&self, alloc: Allocation) -> u32 {
        if let Some(r) = alloc.as_reg() {
            self.reg_vreg[r.index()]
        } else if let Some(s) = alloc.as_stack() {
            self.stack_vreg.get(s.index()).copied().unwrap_or(Self::UNTRACKED)
        } else {
            Self::UNTRACKED
        }
    }

    #[inline(always)]
    fn set(&mut self, alloc: Allocation, v: u32) {
        if let Some(r) = alloc.as_reg() {
            self.reg_vreg[r.index()] = v;
        } else if let Some(s) = alloc.as_stack() {
            if s.index() < self.stack_vreg.len() {
                self.stack_vreg[s.index()] = v;
            }
        }
    }

    #[inline(always)]
    fn kill_vreg(&mut self, v: u32) {
        for slot in self.reg_vreg.iter_mut() {
            if *slot == v {
                *slot = Self::UNTRACKED;
            }
        }
        for slot in self.stack_vreg.iter_mut() {
            if *slot == v {
                *slot = Self::UNTRACKED;
            }
        }
    }

    /// Verifies an allocated function given block-entry witness maps (`block_entry_certs`),
    /// eliminating iterative dataflow fixpoint computation (`O(|I| + |E|)` single pass).
    fn verify_with_entry_witnesses(
        &mut self,
        func: &TestFunc,
        out: &Output,
        entry_witnesses: &[Vec<(Allocation, VReg)>],
    ) -> Result<(), &'static str> {
        for b_idx in 0..func.num_blocks() {
            let b = Block::new(b_idx);
            self.reg_vreg.fill(Self::UNTRACKED);
            self.stack_vreg.fill(Self::UNTRACKED);
            for &(al, vr) in &entry_witnesses[b_idx] {
                self.set(al, vr.vreg() as u32);
            }

            for item in out.block_insts_and_edits(func, b) {
                match item {
                    regalloc2::InstOrEdit::Edit(Edit::Move { from, to }) => {
                        if from.is_stack() && to.is_stack() {
                            return Err("stack-to-stack move");
                        }
                        let src_val = self.get(*from);
                        // CRITICAL FIX vs regalloc2/src/checker.rs:553-561:
                        // Always overwrite `to`, including when `src_val == UNTRACKED`!
                        self.set(*to, src_val);
                    }
                    regalloc2::InstOrEdit::Inst(inst) => {
                        let ops = func.inst_operands(inst);
                        let allocs = out.inst_allocs(inst);
                        for (op, &al) in ops.iter().zip(allocs.iter()) {
                            if op.kind() == OperandKind::Use && op.pos() == OperandPos::Early {
                                if self.get(al) != op.vreg().vreg() as u32 {
                                    return Err("early use mismatch or clobbered");
                                }
                                match op.constraint() {
                                    OperandConstraint::Reg if !al.is_reg() => {
                                        return Err("expected reg");
                                    }
                                    OperandConstraint::FixedReg(p) if al != Allocation::reg(p) => {
                                        return Err("expected fixed reg");
                                    }
                                    OperandConstraint::Limit(m) => {
                                        if let Some(p) = al.as_reg() {
                                            if p.hw_enc() >= m {
                                                return Err("limit exceeded");
                                            }
                                        }
                                    }
                                    _ => {}
                                }
                            }
                        }
                        // Early defs
                        for (op, &al) in ops.iter().zip(allocs.iter()) {
                            if op.kind() == OperandKind::Def && op.pos() == OperandPos::Early {
                                let v = op.vreg().vreg() as u32;
                                self.kill_vreg(v);
                                self.set(al, v);
                            }
                        }
                        // Late uses (skip if Reuse present, matching two-addr semantics)
                        let has_reuse = ops
                            .iter()
                            .any(|o| matches!(o.constraint(), OperandConstraint::Reuse(_)));
                        if !has_reuse {
                            for (op, &al) in ops.iter().zip(allocs.iter()) {
                                if op.kind() == OperandKind::Use && op.pos() == OperandPos::Late {
                                    if self.get(al) != op.vreg().vreg() as u32 {
                                        return Err("late use mismatch");
                                    }
                                }
                            }
                        }
                        // Clobbers + Late defs
                        for clob in func.inst_clobbers(inst) {
                            self.set(Allocation::reg(clob), Self::UNTRACKED);
                        }
                        for (op, &al) in ops.iter().zip(allocs.iter()) {
                            if op.kind() == OperandKind::Def && op.pos() == OperandPos::Late {
                                if let OperandConstraint::Reuse(idx) = op.constraint() {
                                    if al != allocs[idx] || !al.is_reg() {
                                        return Err("reuse constraint violated");
                                    }
                                }
                                if let OperandConstraint::FixedReg(p) = op.constraint() {
                                    if al != Allocation::reg(p) {
                                        return Err("fixed def violated");
                                    }
                                }
                                let v = op.vreg().vreg() as u32;
                                self.kill_vreg(v);
                                self.set(al, v);
                            }
                        }
                    }
                }
            }

            // Verify CFG edge obligations against successor entry witnesses
            let last_inst = func.block_insns(b).last();
            for (s_idx, &succ) in func.block_succs(b).iter().enumerate() {
                let args = func.branch_blockparams(b, last_inst, s_idx);
                let params = func.block_params(succ);
                for &(req_al, req_vr) in &entry_witnesses[succ.index()] {
                    let cur = self.get(req_al);
                    // Either `req_vr` flowed unchanged across the edge, or it is a blockparam
                    // whose corresponding branch arg currently resides in `req_al`.
                    let mut ok = cur == req_vr.vreg() as u32
                        && !params.iter().any(|&p| p == req_vr);
                    for (&p, &a) in params.iter().zip(args.iter()) {
                        if p == req_vr && cur == a.vreg() as u32 {
                            ok = true;
                        }
                    }
                    if !ok {
                        return Err("CFG edge witness obligation failed");
                    }
                }
            }
        }
        Ok(())
    }
}

/// Extract compact block-entry witnesses from a converged allocation so the linear
/// certificate checker never runs an iterative fixpoint at verification time.
fn build_entry_witnesses(func: &TestFunc, out: &Output) -> Vec<Vec<(Allocation, VReg)>> {
    // Run forward abstract state propagation once (on the untrusted producer side)
    // to emit explicit block-entry certificates `(Allocation, VReg)`.
    let n = func.num_blocks();
    let mut entry: Vec<Option<HashMap<Allocation, VReg>>> = vec![None; n];
    entry[0] = Some(HashMap::new());
    let mut changed = true;
    while changed {
        changed = false;
        for b_idx in 0..n {
            let Some(mut st) = entry[b_idx].clone() else {
                continue;
            };
            let b = Block::new(b_idx);
            for item in out.block_insts_and_edits(func, b) {
                match item {
                    regalloc2::InstOrEdit::Edit(Edit::Move { from, to }) => {
                        if let Some(&v) = st.get(from) {
                            st.insert(*to, v);
                        } else {
                            st.remove(to);
                        }
                    }
                    regalloc2::InstOrEdit::Inst(inst) => {
                        let ops = func.inst_operands(inst);
                        let allocs = out.inst_allocs(inst);
                        for (op, &al) in ops.iter().zip(allocs.iter()) {
                            if op.kind() == OperandKind::Def && op.pos() == OperandPos::Early {
                                st.retain(|_, v| *v != op.vreg());
                                st.insert(al, op.vreg());
                            }
                        }
                        for clob in func.inst_clobbers(inst) {
                            st.remove(&Allocation::reg(clob));
                        }
                        for (op, &al) in ops.iter().zip(allocs.iter()) {
                            if op.kind() == OperandKind::Def && op.pos() == OperandPos::Late {
                                st.retain(|_, v| *v != op.vreg());
                                st.insert(al, op.vreg());
                            }
                        }
                    }
                }
            }
            let last_inst = func.block_insns(b).last();
            for (s_idx, &succ) in func.block_succs(b).iter().enumerate() {
                let args = func.branch_blockparams(b, last_inst, s_idx);
                let params = func.block_params(succ);
                let mut edge_st: HashMap<Allocation, VReg> = HashMap::new();
                for (&al, &vr) in &st {
                    if !params.contains(&vr) {
                        edge_st.insert(al, vr);
                    }
                    for (&p, &a) in params.iter().zip(args.iter()) {
                        if vr == a {
                            edge_st.insert(al, p);
                        }
                    }
                }
                match &mut entry[succ.index()] {
                    None => {
                        entry[succ.index()] = Some(edge_st);
                        changed = true;
                    }
                    Some(cur) => {
                        let before_len = cur.len();
                        cur.retain(|k, v| edge_st.get(k) == Some(v));
                        if cur.len() != before_len {
                            changed = true;
                        }
                    }
                }
            }
        }
    }
    entry
        .into_iter()
        .map(|opt| {
            let mut v: Vec<_> = opt.unwrap_or_default().into_iter().collect();
            v.sort_by_key(|(a, r)| (a.bits(), r.bits()));
            v
        })
        .collect()
}

/// Build parameterized realistic SSA CFG with loops, diamonds, two-address reuses,
/// call clobbers, fixed registers, and i686 byte-limit constraints.
fn build_ssa_workload(
    num_loops: usize,
    live_width: usize,
    with_calls: bool,
    with_byte_limits: bool,
) -> TestFunc {
    // Structure (no critical edges, as required by regalloc2):
    // Block 0: entry -> Block 1 (header)
    // For each loop l in 0..num_loops:
    //   header (block 4*l + 1): params [acc_0 .. acc_{W-1}, iter]
    //     cond branch -> latch_prep (4*l + 2) or exit_edge (4*l + 3)
    //   body (block 4*l + 2): arithmetic, two-addr Reuse(0), optional call clobbers, Limit(4)
    //     branch -> backedge (4*l + 4)
    //   backedge (block 4*l + 4): branch -> header (4*l + 1) with updated blockparams
    //   exit (block 4*l + 3): either branches to next header or returns
    let mut insts = Vec::new();
    let mut blocks = Vec::new();
    let total_blocks = 1 + 4 * num_loops;
    let mut preds = vec![Vec::new(); total_blocks];
    let mut succs = vec![Vec::new(); total_blocks];
    let mut block_params = vec![Vec::new(); total_blocks];
    let mut branch_args = vec![Vec::new(); total_blocks];
    let mut next_vreg = 0usize;
    let mut alloc_vreg = || {
        let v = VReg::new(next_vreg, RegClass::Int);
        next_vreg += 1;
        v
    };

    // Entry block 0
    let b0_start = insts.len();
    let mut init_vals = Vec::with_capacity(live_width + 1);
    for k in 0..=live_width {
        let v = alloc_vreg();
        let constraint = if k < 2 {
            OperandConstraint::FixedReg(PReg::new(k, RegClass::Int))
        } else {
            OperandConstraint::Reg
        };
        insts.push(TestInst {
            kind: OpKind::Normal,
            operands: vec![Operand::new(
                v,
                constraint,
                OperandKind::Def,
                OperandPos::Late,
            )],
            clobbers: PRegSet::empty(),
        });
        init_vals.push(v);
    }
    insts.push(TestInst {
        kind: OpKind::Branch,
        operands: vec![],
        clobbers: PRegSet::empty(),
    });
    blocks.push(InstRange::new(Inst::new(b0_start), Inst::new(insts.len())));
    succs[0] = vec![Block::new(1)];
    preds[1].push(Block::new(0));
    branch_args[0] = vec![init_vals];

    let mut carry_params: Vec<VReg> = Vec::new();
    for l in 0..num_loops {
        let hdr = 1 + 4 * l;
        let body = hdr + 1;
        let exit = hdr + 2;
        let back = hdr + 3;

        if l > 0 {
            let prev_exit = 1 + 4 * (l - 1) + 2;
            succs[prev_exit] = vec![Block::new(hdr)];
            preds[hdr].push(Block::new(prev_exit));
            branch_args[prev_exit] = vec![carry_params.clone()];
        }

        let mut hdr_params = Vec::with_capacity(live_width + 1);
        for _ in 0..=live_width {
            hdr_params.push(alloc_vreg());
        }
        block_params[hdr] = hdr_params.clone();

        // Header block: compare counter and branch to body or exit
        let hdr_start = insts.len();
        let cmp_tmp = alloc_vreg();
        insts.push(TestInst {
            kind: OpKind::Normal,
            operands: vec![
                Operand::reg_use(hdr_params[live_width]),
                Operand::new(
                    cmp_tmp,
                    if with_byte_limits {
                        OperandConstraint::Limit(4)
                    } else {
                        OperandConstraint::Reg
                    },
                    OperandKind::Def,
                    OperandPos::Late,
                ),
            ],
            clobbers: PRegSet::empty(),
        });
        insts.push(TestInst {
            kind: OpKind::Branch,
            operands: vec![Operand::reg_use(cmp_tmp)],
            clobbers: PRegSet::empty(),
        });
        blocks.push(InstRange::new(Inst::new(hdr_start), Inst::new(insts.len())));
        succs[hdr] = vec![Block::new(body), Block::new(exit)];
        preds[body].push(Block::new(hdr));
        preds[exit].push(Block::new(hdr));
        branch_args[hdr] = vec![vec![], vec![]];

        // Body block: chain of two-address ops, optional call clobber, byte-limit ops
        let body_start = insts.len();
        let mut updated = hdr_params.clone();
        for k in 0..live_width {
            let out_v = alloc_vreg();
            let rhs = updated[(k + 1) % live_width];
            insts.push(TestInst {
                kind: OpKind::Normal,
                operands: vec![
                    Operand::reg_use(updated[k]),
                    Operand::reg_use(rhs),
                    Operand::reg_reuse_def(out_v, 0),
                ],
                clobbers: PRegSet::empty(),
            });
            updated[k] = out_v;

            if with_byte_limits && (k % 3 == 0) {
                let byte_v = alloc_vreg();
                insts.push(TestInst {
                    kind: OpKind::Normal,
                    operands: vec![
                        Operand::new(
                            updated[k],
                            OperandConstraint::Limit(4),
                            OperandKind::Use,
                            OperandPos::Early,
                        ),
                        Operand::new(
                            byte_v,
                            OperandConstraint::Limit(4),
                            OperandKind::Def,
                            OperandPos::Late,
                        ),
                    ],
                    clobbers: PRegSet::empty(),
                });
                updated[k] = byte_v;
            }
        }

        if with_calls {
            // Simulate a call that takes arg in p0i, returns result in p0i, and clobbers
            // caller-saved p1i, p2i.
            let call_ret = alloc_vreg();
            let mut clob = PRegSet::empty();
            clob.add(PReg::new(1, RegClass::Int));
            clob.add(PReg::new(2, RegClass::Int));
            insts.push(TestInst {
                kind: OpKind::Normal,
                operands: vec![
                    Operand::reg_fixed_use(updated[0], PReg::new(0, RegClass::Int)),
                    Operand::reg_fixed_def(call_ret, PReg::new(0, RegClass::Int)),
                ],
                clobbers: clob,
            });
            updated[0] = call_ret;
        }

        let next_iter = alloc_vreg();
        insts.push(TestInst {
            kind: OpKind::Normal,
            operands: vec![
                Operand::reg_use(updated[live_width]),
                Operand::reg_reuse_def(next_iter, 0),
            ],
            clobbers: PRegSet::empty(),
        });
        updated[live_width] = next_iter;

        insts.push(TestInst {
            kind: OpKind::Branch,
            operands: vec![],
            clobbers: PRegSet::empty(),
        });
        blocks.push(InstRange::new(
            Inst::new(body_start),
            Inst::new(insts.len()),
        ));

        // Exit block (hdr + 2)
        let exit_start = insts.len();
        if l + 1 == num_loops {
            // Final return reducing live values
            let mut acc = hdr_params[0];
            for k in 1..live_width {
                let next_acc = alloc_vreg();
                insts.push(TestInst {
                    kind: OpKind::Normal,
                    operands: vec![
                        Operand::reg_use(acc),
                        Operand::reg_use(hdr_params[k]),
                        Operand::reg_reuse_def(next_acc, 0),
                    ],
                    clobbers: PRegSet::empty(),
                });
                acc = next_acc;
            }
            insts.push(TestInst {
                kind: OpKind::Ret,
                operands: vec![Operand::reg_fixed_use(acc, PReg::new(0, RegClass::Int))],
                clobbers: PRegSet::empty(),
            });
        } else {
            carry_params = hdr_params.clone();
            insts.push(TestInst {
                kind: OpKind::Branch,
                operands: vec![],
                clobbers: PRegSet::empty(),
            });
        }
        blocks.push(InstRange::new(
            Inst::new(exit_start),
            Inst::new(insts.len()),
        ));

        // Backedge block (hdr + 3)
        let back_start = insts.len();
        insts.push(TestInst {
            kind: OpKind::Branch,
            operands: vec![],
            clobbers: PRegSet::empty(),
        });
        blocks.push(InstRange::new(
            Inst::new(back_start),
            Inst::new(insts.len()),
        ));

        succs[body] = vec![Block::new(back)];
        preds[back].push(Block::new(body));
        branch_args[body] = vec![vec![]];

        succs[back] = vec![Block::new(hdr)];
        preds[hdr].push(Block::new(back));
        branch_args[back] = vec![updated];
    }

    TestFunc {
        insts,
        blocks,
        preds,
        succs,
        block_params,
        branch_args,
        num_vregs: next_vreg,
        debug_labels: vec![],
    }
}

fn run_soundness_probes() -> String {
    let env = env_x86_64();
    let p0 = PReg::new(0, RegClass::Int);
    let p1 = PReg::new(1, RegClass::Int);
    let p2 = PReg::new(2, RegClass::Int);

    // Witness 1: Clobbered-source Edit::Move overwrites live p0 with clobbered p1
    let v0 = VReg::new(0, RegClass::Int);
    let mut clob1 = PRegSet::empty();
    clob1.add(p1);
    let f1 = TestFunc {
        insts: vec![
            TestInst {
                kind: OpKind::Normal,
                operands: vec![Operand::reg_def(v0)],
                clobbers: clob1,
            },
            TestInst {
                kind: OpKind::Ret,
                operands: vec![Operand::reg_use(v0)],
                clobbers: PRegSet::empty(),
            },
        ],
        blocks: vec![InstRange::new(Inst::new(0), Inst::new(2))],
        preds: vec![vec![]],
        succs: vec![vec![]],
        block_params: vec![vec![]],
        branch_args: vec![vec![]],
        num_vregs: 1,
        debug_labels: vec![],
    };
    let bad_out_1 = Output {
        num_spillslots: 0,
        edits: vec![(
            ProgPoint::before(Inst::new(1)),
            Edit::Move {
                from: Allocation::reg(p1), // clobbered by inst 0!
                to: Allocation::reg(p0),   // overwrites live v0 in p0!
            },
        )],
        allocs: vec![Allocation::reg(p0), Allocation::reg(p0)],
        inst_alloc_offsets: vec![0, 1],
        debug_locations: vec![],
        stats: Default::default(),
    };
    let mut chk1 = Checker::new(&f1, &env);
    chk1.prepare(&bad_out_1);
    let upstream_verdict_1 = chk1.run();
    let (ssa_1, hw_1) = eval_single_block_concrete(&f1, &bad_out_1);
    let mut fixed_chk_1 = LinearCertChecker::new(0);
    let fixed_verdict_1 = fixed_chk_1.verify_with_entry_witnesses(&f1, &bad_out_1, &[vec![]]);

    // Witness 2: MoveAndScratchResolver borrowed-scratch save/restore residual VReg bug
    // Unallocated p2 saved to stack0, p2 shuttles stack1(v0) -> stack2, then p2 restored
    // from uninitialized stack0; inst1 erroneously reads v0 from p2!
    let s_save = Allocation::stack(SpillSlot::new(0));
    let s_dst = Allocation::stack(SpillSlot::new(1));
    let bad_out_2 = Output {
        num_spillslots: 2,
        edits: vec![
            // Spill v0 from p0 to stack slot 1, then clobber/reuse via borrowed p2:
            (
                ProgPoint::before(Inst::new(1)),
                Edit::Move {
                    from: Allocation::reg(p2), // p2 is uninitialized!
                    to: s_save,
                },
            ),
            (
                ProgPoint::before(Inst::new(1)),
                Edit::Move {
                    from: Allocation::reg(p0), // p2 now holds {v0}
                    to: Allocation::reg(p2),
                },
            ),
            (
                ProgPoint::before(Inst::new(1)),
                Edit::Move {
                    from: Allocation::reg(p2),
                    to: s_dst,
                },
            ),
            (
                ProgPoint::before(Inst::new(1)),
                Edit::Move {
                    from: s_save,              // uninitialized save slot!
                    to: Allocation::reg(p2),   // hardware overwrites p2 with garbage,
                                               // but Checker leaves p2 -> {v0}!
                },
            ),
        ],
        allocs: vec![Allocation::reg(p0), Allocation::reg(p2)], // inst1 reads p2 instead of s_dst!
        inst_alloc_offsets: vec![0, 1],
        debug_locations: vec![],
        stats: Default::default(),
    };
    let mut chk2 = Checker::new(&f1, &env);
    chk2.prepare(&bad_out_2);
    let upstream_verdict_2 = chk2.run();
    let (ssa_2, hw_2) = eval_single_block_concrete(&f1, &bad_out_2);
    let mut fixed_chk_2 = LinearCertChecker::new(2);
    let fixed_verdict_2 = fixed_chk_2.verify_with_entry_witnesses(&f1, &bad_out_2, &[vec![]]);

    // Negative control 3: Wrong register without Edit::Move (Checker catches this)
    let neg_out_3 = Output {
        num_spillslots: 0,
        edits: vec![],
        allocs: vec![Allocation::reg(p0), Allocation::reg(p1)],
        inst_alloc_offsets: vec![0, 1],
        debug_locations: vec![],
        stats: Default::default(),
    };
    let mut chk3 = Checker::new(&f1, &env);
    chk3.prepare(&neg_out_3);
    let upstream_verdict_3 = chk3.run();

    // Negative control 4: Limit(4) violated on i686 (ESI = hw_enc 6 >= 4)
    let f_lim = TestFunc {
        insts: vec![
            TestInst {
                kind: OpKind::Normal,
                operands: vec![Operand::new(
                    v0,
                    OperandConstraint::Limit(4),
                    OperandKind::Def,
                    OperandPos::Late,
                )],
                clobbers: PRegSet::empty(),
            },
            TestInst {
                kind: OpKind::Ret,
                operands: vec![Operand::reg_use(v0)],
                clobbers: PRegSet::empty(),
            },
        ],
        blocks: vec![InstRange::new(Inst::new(0), Inst::new(2))],
        preds: vec![vec![]],
        succs: vec![vec![]],
        block_params: vec![vec![]],
        branch_args: vec![vec![]],
        num_vregs: 1,
        debug_labels: vec![],
    };
    let p_esi = PReg::new(6, RegClass::Int);
    let neg_out_4 = Output {
        num_spillslots: 0,
        edits: vec![],
        allocs: vec![Allocation::reg(p_esi), Allocation::reg(p_esi)],
        inst_alloc_offsets: vec![0, 1],
        debug_locations: vec![],
        stats: Default::default(),
    };
    let env32 = env_i686();
    let mut chk4 = Checker::new(&f_lim, &env32);
    chk4.prepare(&neg_out_4);
    let upstream_verdict_4 = chk4.run();

    format!(
        concat!(
            "{{\n",
            "  \"witness_1_clobbered_move\": {{\n",
            "    \"upstream_checker_accepted\": {},\n",
            "    \"concrete_ssa_ret_hex\": \"0x{:016x}\",\n",
            "    \"concrete_hw_ret_hex\": \"0x{:016x}\",\n",
            "    \"values_diverged_at_runtime\": {},\n",
            "    \"fixed_linear_cert_checker_accepted\": {},\n",
            "    \"fixed_linear_cert_error\": \"{}\"\n",
            "  }},\n",
            "  \"witness_2_borrowed_scratch_restore\": {{\n",
            "    \"upstream_checker_accepted\": {},\n",
            "    \"concrete_ssa_ret_hex\": \"0x{:016x}\",\n",
            "    \"concrete_hw_ret_hex\": \"0x{:016x}\",\n",
            "    \"values_diverged_at_runtime\": {},\n",
            "    \"fixed_linear_cert_checker_accepted\": {},\n",
            "    \"fixed_linear_cert_error\": \"{}\"\n",
            "  }},\n",
            "  \"negative_control_wrong_reg_rejected\": {},\n",
            "  \"negative_control_i686_limit4_esi_rejected\": {}\n",
            "}}"
        ),
        upstream_verdict_1.is_ok(),
        ssa_1,
        hw_1,
        ssa_1 != hw_1,
        fixed_verdict_1.is_ok(),
        fixed_verdict_1.err().unwrap_or("none"),
        upstream_verdict_2.is_ok(),
        ssa_2,
        hw_2,
        ssa_2 != hw_2,
        fixed_verdict_2.is_ok(),
        fixed_verdict_2.err().unwrap_or("none"),
        upstream_verdict_3.is_err(),
        upstream_verdict_4.is_err()
    )
}

fn percentile_us(samples_ns: &mut [u128], pct: usize) -> f64 {
    samples_ns.sort_unstable();
    let idx = ((samples_ns.len() - 1) * pct) / 100;
    (samples_ns[idx] as f64) / 1000.0
}

fn main() {
    let soundness_json = run_soundness_probes();

    let workloads = [
        ("small_loop_w6", build_ssa_workload(2, 6, true, false)),
        ("medium_loops_w12", build_ssa_workload(8, 12, true, false)),
        ("high_pressure_spill_w20", build_ssa_workload(8, 20, true, false)),
        ("byte_subreg_limit4_w10", build_ssa_workload(6, 10, true, true)),
        ("large_cfg_loops_w16", build_ssa_workload(24, 16, true, false)),
    ];

    let targets = [
        ("x86_64_sysv", env_x86_64()),
        ("aarch64_aapcs64", env_aarch64()),
        ("i686_cdecl", env_i686()),
    ];

    let iters = 150usize;
    let warmup = 20usize;
    let mut rows = Vec::new();

    for (w_name, func) in &workloads {
        for (t_name, env) in &targets {
            let opts_ion = RegallocOptions {
                verbose_log: false,
                validate_ssa: false,
                algorithm: Algorithm::Ion,
            };
            let opts_fast = RegallocOptions {
                verbose_log: false,
                validate_ssa: false,
                algorithm: Algorithm::Fastalloc,
            };

            let mut ctx = Ctx::default();
            for _ in 0..warmup {
                let _ = black_box(regalloc2::run_with_ctx(func, env, &opts_ion, &mut ctx).unwrap());
            }

            let mut ion_ns = Vec::with_capacity(iters);
            let mut out_ion = Output::default();
            for k in 0..iters {
                let t0 = Instant::now();
                let res = regalloc2::run_with_ctx(func, env, &opts_ion, &mut ctx).unwrap();
                ion_ns.push(t0.elapsed().as_nanos());
                if k == 0 {
                    out_ion = res.clone();
                }
                black_box(res);
            }

            // Probe whether Fastalloc supports this constraint set (e.g., `Limit(4)` panics at
            // `src/fastalloc/mod.rs:671`).
            let fast_probe = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                regalloc2::run(func, env, &opts_fast).unwrap()
            }));
            let (fast_supported, fast_med_us, fast_spills, fast_edits) = match fast_probe {
                Ok(_) => {
                    for _ in 0..warmup {
                        let _ = black_box(regalloc2::run(func, env, &opts_fast).unwrap());
                    }
                    let mut fast_ns = Vec::with_capacity(iters);
                    let mut out_fast = Output::default();
                    for k in 0..iters {
                        let t0 = Instant::now();
                        let res = regalloc2::run(func, env, &opts_fast).unwrap();
                        fast_ns.push(t0.elapsed().as_nanos());
                        if k == 0 {
                            out_fast = res;
                        } else {
                            black_box(res);
                        }
                    }
                    let mut chk_f = Checker::new(func, env);
                    chk_f.prepare(&out_fast);
                    chk_f
                        .run()
                        .expect("Fastalloc allocation must pass upstream checker");
                    (
                        true,
                        percentile_us(&mut fast_ns, 50),
                        out_fast.num_spillslots,
                        out_fast.edits.len(),
                    )
                }
                Err(_) => (false, -1.0, 0, 0),
            };

            // Upstream symbolic fixpoint Checker timing on Ion output
            for _ in 0..warmup {
                let mut chk = Checker::new(func, env);
                chk.prepare(&out_ion);
                chk.run().expect("Ion allocation must pass upstream checker");
            }
            let mut chk_ion_ns = Vec::with_capacity(iters);
            for _ in 0..iters {
                let t0 = Instant::now();
                let mut chk = Checker::new(func, env);
                chk.prepare(&out_ion);
                chk.run().unwrap();
                chk_ion_ns.push(t0.elapsed().as_nanos());
            }

            // Build block-entry witnesses once and time linear single-pass RegAllocCert checker
            let witnesses = build_entry_witnesses(func, &out_ion);
            let mut lin_chk = LinearCertChecker::new(out_ion.num_spillslots);
            for _ in 0..warmup {
                lin_chk
                    .verify_with_entry_witnesses(func, &out_ion, &witnesses)
                    .expect("Ion allocation must pass linear cert checker");
            }
            let mut lin_ns = Vec::with_capacity(iters);
            for _ in 0..iters {
                let t0 = Instant::now();
                lin_chk
                    .verify_with_entry_witnesses(func, &out_ion, &witnesses)
                    .unwrap();
                lin_ns.push(t0.elapsed().as_nanos());
            }

            // Compute exact serialized certificate byte footprint:
            // - Output stream: 4B per operand Allocation + 12B per (ProgPoint, Edit::Move)
            // - Block-entry witness stream: 4B block header + 8B per (Allocation, VReg) entry
            let witness_entries: usize = witnesses.iter().map(|w| w.len()).sum();
            let raw_output_bytes = out_ion.allocs.len() * 4 + out_ion.edits.len() * 12;
            let entry_witness_bytes = func.num_blocks() * 4 + witness_entries * 8;
            let total_cert_bytes = raw_output_bytes + entry_witness_bytes;

            rows.push(format!(
                concat!(
                    "    {{\n",
                    "      \"workload\": \"{}\",\n",
                    "      \"target\": \"{}\",\n",
                    "      \"blocks\": {},\n",
                    "      \"insts\": {},\n",
                    "      \"vregs\": {},\n",
                    "      \"ion_median_us\": {:.3},\n",
                    "      \"ion_p95_us\": {:.3},\n",
                    "      \"fastalloc_supported\": {},\n",
                    "      \"fastalloc_median_us\": {:.3},\n",
                    "      \"upstream_checker_median_us\": {:.3},\n",
                    "      \"upstream_checker_p95_us\": {:.3},\n",
                    "      \"linear_cert_checker_median_us\": {:.3},\n",
                    "      \"linear_cert_checker_p95_us\": {:.3},\n",
                    "      \"ion_spillslots\": {},\n",
                    "      \"ion_edits\": {},\n",
                    "      \"fastalloc_spillslots\": {},\n",
                    "      \"fastalloc_edits\": {},\n",
                    "      \"witness_entries\": {},\n",
                    "      \"raw_output_bytes\": {},\n",
                    "      \"entry_witness_bytes\": {},\n",
                    "      \"total_cert_bytes\": {}\n",
                    "    }}"
                ),
                w_name,
                t_name,
                func.num_blocks(),
                func.num_insts(),
                func.num_vregs(),
                percentile_us(&mut ion_ns, 50),
                percentile_us(&mut ion_ns, 95),
                fast_supported,
                fast_med_us,
                percentile_us(&mut chk_ion_ns, 50),
                percentile_us(&mut chk_ion_ns, 95),
                percentile_us(&mut lin_ns, 50),
                percentile_us(&mut lin_ns, 95),
                out_ion.num_spillslots,
                out_ion.edits.len(),
                fast_spills,
                fast_edits,
                witness_entries,
                raw_output_bytes,
                entry_witness_bytes,
                total_cert_bytes,
            ));
        }
    }

    println!(
        "{{\n  \"soundness_probes\": {},\n  \"benchmarks\": [\n{}\n  ]\n}}",
        soundness_json,
        rows.join(",\n")
    );
}
