# Minimal Verified RV64IM_Zicsr_Zifencei Trap Entry, Exit & W^X Activation
# Reference Template for Sail-Equivalence Assembly Verification.
#
# Architectural Invariants:
#   - U-mode invariant: `sscratch == TrapFrame*` (non-zero, 8-byte aligned,
#     mapped in kernel high-half); `scounteren == 0`; `sstatus.FS == 0`;
#     `sstatus.VS == 0`; `sstatus.SUM == 0`; `sstatus.MXR == 0`.
#   - S-mode invariant: `sscratch == 0`; `sstatus.SIE == 0` (non-preemptive
#     kernel; idle `wfi` wakes on `(mip & mie) != 0` even with `SIE == 0` per
#     `SysControl.lean:611-612` & ISA manual `norm:wfi_op`).
#   - Direct-mode `stvec` (`stvec[1:0] == 0b00`, 4-byte aligned).
#   - Fixed 32-bit instruction width (`-C target-feature=+zicsr,+zifencei` on
#     `riscv64im-unknown-none-elf`, zero 16-bit RVC instructions).
#
# TrapFrame layout (`#[repr(C, align(64))]`, 38 * 8 = 304 bytes):
#   offset   0: reserved / x0 slot (always 0)
#   offset   8..248: x1..x31 (offset = 8 * reg_idx)
#   offset 256 (32*8): sepc
#   offset 264 (33*8): sstatus
#   offset 272 (34*8): scause
#   offset 280 (35*8): stval
#   offset 288 (36*8): kernel_sp (per-hart kernel stack top)
#   offset 296 (37*8): padding / hart_id

    .section .text.traps, "ax"

# -----------------------------------------------------------------------------
# trap_entry: 45 instructions (straight-line except 1 S-mode trap guard)
# -----------------------------------------------------------------------------
    .global trap_entry
    .balign 4
trap_entry:
    # 1. Atomically swap user sp <-> sscratch.
    #    From U-mode: sp := TrapFrame* (!= 0), sscratch := user_sp.
    #    From S-mode: sp := 0, sscratch := kernel_sp.
    csrrw   sp, sscratch, sp
    beqz    sp, s_mode_trap_panic

    # 2. Save x1 and x3..x31 (29 stores)
    sd      x1,    (1 * 8)(sp)
    sd      x3,    (3 * 8)(sp)
    sd      x4,    (4 * 8)(sp)
    sd      x5,    (5 * 8)(sp)
    sd      x6,    (6 * 8)(sp)
    sd      x7,    (7 * 8)(sp)
    sd      x8,    (8 * 8)(sp)
    sd      x9,    (9 * 8)(sp)
    sd      x10,  (10 * 8)(sp)
    sd      x11,  (11 * 8)(sp)
    sd      x12,  (12 * 8)(sp)
    sd      x13,  (13 * 8)(sp)
    sd      x14,  (14 * 8)(sp)
    sd      x15,  (15 * 8)(sp)
    sd      x16,  (16 * 8)(sp)
    sd      x17,  (17 * 8)(sp)
    sd      x18,  (18 * 8)(sp)
    sd      x19,  (19 * 8)(sp)
    sd      x20,  (20 * 8)(sp)
    sd      x21,  (21 * 8)(sp)
    sd      x22,  (22 * 8)(sp)
    sd      x23,  (23 * 8)(sp)
    sd      x24,  (24 * 8)(sp)
    sd      x25,  (25 * 8)(sp)
    sd      x26,  (26 * 8)(sp)
    sd      x27,  (27 * 8)(sp)
    sd      x28,  (28 * 8)(sp)
    sd      x29,  (29 * 8)(sp)
    sd      x30,  (30 * 8)(sp)
    sd      x31,  (31 * 8)(sp)

    # 3. Extract user sp AND restore S-mode invariant (sscratch := 0) atomically
    csrrw   t0, sscratch, zero
    sd      t0,    (2 * 8)(sp)

    # 4. Save trap CSRs (sepc, sstatus, scause, stval)
    csrr    t0, sepc
    sd      t0,   (32 * 8)(sp)
    csrr    t0, sstatus
    sd      t0,   (33 * 8)(sp)
    csrr    t0, scause
    sd      t0,   (34 * 8)(sp)
    csrr    t0, stval
    sd      t0,   (35 * 8)(sp)

    # 5. Switch to kernel stack and enter Rust handler(a0: *mut TrapFrame) -> !
    mv      a0, sp
    ld      sp,   (36 * 8)(a0)
    tail    rust_trap_handler

# -----------------------------------------------------------------------------
# s_mode_trap_panic: recovers kernel_sp & sscratch==0 before halting
# -----------------------------------------------------------------------------
    .balign 4
s_mode_trap_panic:
    csrrw   sp, sscratch, zero
    csrr    a0, scause
    csrr    a1, sepc
    csrr    a2, stval
    tail    rust_kernel_fault_panic

# -----------------------------------------------------------------------------
# return_to_user(a0: *const TrapFrame) -> !: 37 instructions (0 branches)
# Overwrites EVERY architectural GPR x1..x31 from target thread's TrapFrame
# (zero kernel register residue across context switches for noninterference).
# Precondition: sstatus.SIE == 0; TrapFrame.sstatus has SPP=0, SPIE=1, SIE=0,
# SUM=0, MXR=0, FS=0, VS=0; TrapFrame.sepc is 4-byte aligned canonical U-VA.
# -----------------------------------------------------------------------------
    .global return_to_user
    .balign 4
return_to_user:
    ld      t0,   (32 * 8)(a0)
    csrw    sepc, t0
    ld      t0,   (33 * 8)(a0)
    csrw    sstatus, t0
    csrw    sscratch, a0

    ld      x1,    (1 * 8)(a0)
    ld      x2,    (2 * 8)(a0)
    ld      x3,    (3 * 8)(a0)
    ld      x4,    (4 * 8)(a0)
    ld      x5,    (5 * 8)(a0)
    ld      x6,    (6 * 8)(a0)
    ld      x7,    (7 * 8)(a0)
    ld      x8,    (8 * 8)(a0)
    ld      x9,    (9 * 8)(a0)
    ld      x11,  (11 * 8)(a0)
    ld      x12,  (12 * 8)(a0)
    ld      x13,  (13 * 8)(a0)
    ld      x14,  (14 * 8)(a0)
    ld      x15,  (15 * 8)(a0)
    ld      x16,  (16 * 8)(a0)
    ld      x17,  (17 * 8)(a0)
    ld      x18,  (18 * 8)(a0)
    ld      x19,  (19 * 8)(a0)
    ld      x20,  (20 * 8)(a0)
    ld      x21,  (21 * 8)(a0)
    ld      x22,  (22 * 8)(a0)
    ld      x23,  (23 * 8)(a0)
    ld      x24,  (24 * 8)(a0)
    ld      x25,  (25 * 8)(a0)
    ld      x26,  (26 * 8)(a0)
    ld      x27,  (27 * 8)(a0)
    ld      x28,  (28 * 8)(a0)
    ld      x29,  (29 * 8)(a0)
    ld      x30,  (30 * 8)(a0)
    ld      x31,  (31 * 8)(a0)
    ld      x10,  (10 * 8)(a0)   # a0 restored LAST
    sret

# -----------------------------------------------------------------------------
# wx_activate_and_call(a0: *mut u64 leaf_pte, a1: u64 rx_pte_val,
#                      a2: usize module_va, a3: u64 arg0) -> u64
# Exact single-hart W^X RW -> RX transition & invocation sequence:
#   1. Single 8-byte atomic PTE store (W=0, X=1, R=1, U=0, G=1, A=1, D=0, [63:54]=0).
#   2. `sfence.vma a2, zero` (rs2 = x0 MANDATORY for global G=1 kernel slot!).
#   3. `fence.i` (MUST follow sfence.vma; flushes I-cache & fetch pipeline).
#   4. `jalr ra, a2, 0` (4-byte aligned entry).
# -----------------------------------------------------------------------------
    .global wx_activate_and_call
    .balign 4
wx_activate_and_call:
    addi    sp, sp, -16
    sd      ra, 8(sp)
    sd      a1, 0(a0)           # atomic 64-bit leaf PTE update: RW -> RX
    sfence.vma a2, zero         # flush TLB for module_va across ALL ASIDs incl. G=1
    fence.i                     # synchronize prior code stores with instruction fetch
    mv      a0, a3              # pass verified module argument in a0
    jalr    ra, a2, 0           # invoke verified S-mode binary module
    ld      ra, 8(sp)
    addi    sp, sp, 16
    ret
