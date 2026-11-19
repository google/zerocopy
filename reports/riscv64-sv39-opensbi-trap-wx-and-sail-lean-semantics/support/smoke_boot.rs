#![feature(no_core, lang_items, rustc_attrs)]
#![no_core]
#![no_main]

//! Standalone bare-metal `RV64IM_Zicsr_Zifencei` + `Sv39` smoke-boot probe
//! targeting `qemu-system-riscv64 -M virt` over OpenSBI (`fw_dynamic`).
//!
//! Compile command (verified on `rustc 1.98.0-nightly (14210df0e 2026-05-31)`,
//! LLVM `22.1.6`, 0 compressed 16-bit instructions, `EF_RISCV_RVC = 0`,
//! `EF_RISCV_FLOAT_ABI_SOFT = 0x0`):
//!
//! ```sh
//! mkdir -p /tmp/rv64_smoke_boot
//! rustc --target riscv64im-unknown-none-elf \
//!   -C target-feature=+zicsr,+zifencei \
//!   -C link-arg=-Tsupport/link.ld \
//!   -C opt-level=2 \
//!   -o /tmp/rv64_smoke_boot/smoke_boot.elf \
//!   support/smoke_boot.rs
//! ```
//!
//! Headless non-TTY QEMU execution commands (verified on QEMU 11.0.2 +
//! OpenSBI v1.7 under both strict `Svade` and default `rv64` with `Svadu`):
//!
//! ```sh
//! # Strict ISA + Svade check (no RVC, no F/D/V, Svade enabled, Svadu disabled):
//! timeout 10s qemu-system-riscv64 \
//!   -M virt -m 128M -smp 1 \
//!   -cpu rv64,c=false,f=false,d=false,v=false,svade=true,svadu=false \
//!   -display none -serial stdio -bios default \
//!   -kernel /tmp/rv64_smoke_boot/smoke_boot.elf </dev/null
//!
//! # Default QEMU rv64 check (verifies sstatus.FS=0, scounteren=0, Svadu invariance):
//! timeout 10s qemu-system-riscv64 \
//!   -M virt -m 128M -smp 1 \
//!   -cpu rv64 \
//!   -display none -serial stdio -bios default \
//!   -kernel /tmp/rv64_smoke_boot/smoke_boot.elf </dev/null
//! ```
//!
//! Expected stdout (after OpenSBI banner) and exit code 0:
//!   RV:B
//!   SV
//!   OK
//!
//! Note: Uses `#![no_core]` only so this single-file probe compiles without
//! building `libcore`. A production kernel should use
//! `--target riscv64im-unknown-none-elf -Z build-std=core` with
//! `-C target-feature=+zicsr,+zifencei` (never precompiled `riscv64gc`
//! `libcore`, which links 16-bit RVC instructions and `EF_RISCV_FLOAT_ABI_DOUBLE`).

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}
impl Copy for u8 {}
impl Copy for u64 {}
impl Copy for usize {}
impl<T: ?Sized> Copy for *const T {}
impl<T: ?Sized> Copy for *mut T {}

#[rustc_builtin_macro]
macro_rules! global_asm {
    ($($t:tt)*) => {};
}

global_asm!(
    r#"
    .equ KERNEL_VIRT_OFF, 0xffffffc000000000
    .equ USER_CODE_VA,    0x0000000000010000
    .equ USER_STACK_VA,   0x0000000000011000
    .equ USER_STACK_TOP,  0x0000000000012000

    # Sv39 PTE flags:
    # - Leaf PTEs set A=1 always and D=1 when W=1 (Svade/Svadu deterministic).
    # - Non-leaf PTEs set V=1 ONLY (A=D=U=0, PTE[63:54]=0; mandatory!).
    .equ PTE_V, (1 << 0)
    .equ PTE_R, (1 << 1)
    .equ PTE_W, (1 << 2)
    .equ PTE_X, (1 << 3)
    .equ PTE_U, (1 << 4)
    .equ PTE_G, (1 << 5)
    .equ PTE_A, (1 << 6)
    .equ PTE_D, (1 << 7)

    .equ PTE_KERN_RWX, (PTE_V | PTE_R | PTE_W | PTE_X | PTE_G | PTE_A | PTE_D)
    .equ PTE_USER_RX,  (PTE_V | PTE_R | PTE_X | PTE_U | PTE_A)
    .equ PTE_USER_RW,  (PTE_V | PTE_R | PTE_W | PTE_U | PTE_A | PTE_D)

    # SBI v2.0 EIDs / FIDs (opensbi/include/sbi/sbi_ecall_interface.h)
    .equ SBI_EXT_DBCN,                 0x4442434e
    .equ SBI_EXT_DBCN_CONSOLE_WRITE_B, 2
    .equ SBI_EXT_SRST,                 0x53525354
    .equ SBI_EXT_SRST_RESET,           0
    .equ SBI_SRST_TYPE_SHUTDOWN,       0
    .equ SBI_SRST_REASON_NONE,         0

    # =====================================================================
    # 1. Bare S-mode Entry & Sv39 Trampoline (.text.boot @ LMA 0x8020_0000)
    # =====================================================================
    .section .text.boot, "ax"
    .global _start
    .balign 4
_start:
    mv s0, a0
    mv s1, a1

    # Override OpenSBI defaults (opensbi/lib/sbi/sbi_hart.c:36-48):
    # - OpenSBI leaves scounteren = 0x02 (TM=1) -> zero it to disable U-mode counters!
    # - OpenSBI leaves mstatus.FS = Initial on RV64GC -> zero FS/VS/SIE/SUM/MXR!
    csrw scounteren, zero
    csrw sstatus, zero
    csrw sie, zero
    csrw sscratch, zero

    # Bare-mode console marker: "RV:B\n" via SBI DBCN WRITE_BYTE
    li a0, 'R'
    call boot_sbi_putc
    li a0, 'V'
    call boot_sbi_putc
    li a0, ':'
    call boot_sbi_putc
    li a0, 'B'
    call boot_sbi_putc
    li a0, '\n'
    call boot_sbi_putc

    # PC-relative `la` yields exact physical addresses while PC is in Bare mode
    la t0, boot_l2_pt
    la t1, boot_l1_kern_pt
    la t2, boot_l1_user_pt
    la t3, boot_l0_user_pt

    # Zero all 4 page-table pages (16 KiB)
    mv t4, t0
    li t5, 16384
    add t5, t4, t5
1:
    sd zero, 0(t4)
    addi t4, t4, 8
    bltu t4, t5, 1b

    # boot_l1_kern_pt[1]: aligned 2 MiB megapage for PA 0x8020_0000..0x803F_FFFF.
    # Leaves [0x8000_0000, 0x8020_0000) (OpenSBI M-mode PMP region) UNMAPPED.
    # Production kernel replaces this boot megapage with 4 KiB W^X mappings.
    li t4, 0x80200000
    srli t4, t4, 12
    slli t4, t4, 10
    ori t4, t4, PTE_KERN_RWX
    sd t4, 8(t1)

    # Non-leaf PTE pointing to boot_l1_kern_pt: ONLY V=1 (A=D=U=0, [63:54]=0)
    srli t4, t1, 12
    slli t4, t4, 10
    ori t4, t4, PTE_V
    sd t4, (2 * 8)(t0)          # temporary identity map: VPN[2] = 2
    li t5, (258 * 8)
    add t5, t0, t5
    sd t4, 0(t5)                # high-half kernel map: VPN[2] = 258

    # User 4 KiB mappings: VA 0x10000 (RX) and VA 0x11000 (RW)
    srli t4, t2, 12
    slli t4, t4, 10
    ori t4, t4, PTE_V           # non-leaf L2[0] -> L1_user
    sd t4, 0(t0)

    srli t4, t3, 12
    slli t4, t4, 10
    ori t4, t4, PTE_V           # non-leaf L1_user[0] -> L0_user
    sd t4, 0(t2)

    la t4, _user_code_start
    srli t4, t4, 12
    slli t4, t4, 10
    ori t4, t4, PTE_USER_RX
    sd t4, (16 * 8)(t3)

    la t4, user_stack_page
    srli t4, t4, 12
    slli t4, t4, 10
    ori t4, t4, PTE_USER_RW
    sd t4, (17 * 8)(t3)

    # Compute high-half target VA before enabling Sv39
    la t6, high_half_entry
    li t5, -64
    slli t5, t5, 32             # 0xffff_ffc0_0000_0000
    add t6, t6, t5

    # satp = (8 << 60) | (PA(boot_l2_pt) >> 12)
    srli t4, t0, 12
    li t5, 8
    slli t5, t5, 60
    or t4, t4, t5

    sfence.vma zero, zero       # order PTE stores before implicit PTW reads
    csrw satp, t4               # Sv39 active immediately on next fetch
    sfence.vma zero, zero       # flush any stale TLB entries
    jr t6

boot_sbi_putc:
    li a7, SBI_EXT_DBCN
    li a6, SBI_EXT_DBCN_CONSOLE_WRITE_B
    ecall
    ret

    # =====================================================================
    # 2. High-Half Kernel Entry, Minimal Trap Entry/Exit, & Dispatch
    # =====================================================================
    .section .text, "ax"
    .balign 4
high_half_entry:
    la sp, kernel_stack_top

    # Remove temporary identity map (boot_l2_pt[2] = 0) & fence
    la t0, boot_l2_pt
    sd zero, (2 * 8)(t0)
    sfence.vma zero, zero

    # Direct-mode stvec (bits [1:0] == 00)
    la t0, trap_entry
    csrw stvec, t0

    li a0, 'S'
    call sbi_putc
    li a0, 'V'
    call sbi_putc
    li a0, '\n'
    call sbi_putc

    # Populate initial U-mode TrapFrame
    la a0, trap_frame
    li t0, USER_STACK_TOP
    sd t0, (2 * 8)(a0)
    li t0, USER_CODE_VA
    sd t0, (32 * 8)(a0)
    li t0, (1 << 5)             # sstatus: SPIE=1, SPP=0 (U), SIE=0, SUM=0, FS=0, VS=0
    sd t0, (33 * 8)(a0)
    la t0, kernel_stack_top
    sd t0, (36 * 8)(a0)

    j return_to_user

    .global trap_entry
    .balign 4
trap_entry:
    csrrw sp, sscratch, sp
    beqz sp, s_mode_trap_panic

    sd x1,   (1 * 8)(sp)
    sd x3,   (3 * 8)(sp)
    sd x4,   (4 * 8)(sp)
    sd x5,   (5 * 8)(sp)
    sd x6,   (6 * 8)(sp)
    sd x7,   (7 * 8)(sp)
    sd x8,   (8 * 8)(sp)
    sd x9,   (9 * 8)(sp)
    sd x10, (10 * 8)(sp)
    sd x11, (11 * 8)(sp)
    sd x12, (12 * 8)(sp)
    sd x13, (13 * 8)(sp)
    sd x14, (14 * 8)(sp)
    sd x15, (15 * 8)(sp)
    sd x16, (16 * 8)(sp)
    sd x17, (17 * 8)(sp)
    sd x18, (18 * 8)(sp)
    sd x19, (19 * 8)(sp)
    sd x20, (20 * 8)(sp)
    sd x21, (21 * 8)(sp)
    sd x22, (22 * 8)(sp)
    sd x23, (23 * 8)(sp)
    sd x24, (24 * 8)(sp)
    sd x25, (25 * 8)(sp)
    sd x26, (26 * 8)(sp)
    sd x27, (27 * 8)(sp)
    sd x28, (28 * 8)(sp)
    sd x29, (29 * 8)(sp)
    sd x30, (30 * 8)(sp)
    sd x31, (31 * 8)(sp)

    csrrw t0, sscratch, zero
    sd t0, (2 * 8)(sp)

    csrr t0, sepc
    sd t0, (32 * 8)(sp)
    csrr t0, sstatus
    sd t0, (33 * 8)(sp)
    csrr t0, scause
    sd t0, (34 * 8)(sp)
    csrr t0, stval
    sd t0, (35 * 8)(sp)

    mv a0, sp
    ld sp, (36 * 8)(a0)
    j trap_dispatch

s_mode_trap_panic:
    csrrw sp, sscratch, zero
    li a0, '!'
    call sbi_putc
    j sbi_shutdown_fail

    .global return_to_user
    .balign 4
return_to_user:
    ld t0, (32 * 8)(a0)
    csrw sepc, t0
    ld t0, (33 * 8)(a0)
    csrw sstatus, t0
    csrw sscratch, a0

    ld x1,   (1 * 8)(a0)
    ld x2,   (2 * 8)(a0)
    ld x3,   (3 * 8)(a0)
    ld x4,   (4 * 8)(a0)
    ld x5,   (5 * 8)(a0)
    ld x6,   (6 * 8)(a0)
    ld x7,   (7 * 8)(a0)
    ld x8,   (8 * 8)(a0)
    ld x9,   (9 * 8)(a0)
    ld x11, (11 * 8)(a0)
    ld x12, (12 * 8)(a0)
    ld x13, (13 * 8)(a0)
    ld x14, (14 * 8)(a0)
    ld x15, (15 * 8)(a0)
    ld x16, (16 * 8)(a0)
    ld x17, (17 * 8)(a0)
    ld x18, (18 * 8)(a0)
    ld x19, (19 * 8)(a0)
    ld x20, (20 * 8)(a0)
    ld x21, (21 * 8)(a0)
    ld x22, (22 * 8)(a0)
    ld x23, (23 * 8)(a0)
    ld x24, (24 * 8)(a0)
    ld x25, (25 * 8)(a0)
    ld x26, (26 * 8)(a0)
    ld x27, (27 * 8)(a0)
    ld x28, (28 * 8)(a0)
    ld x29, (29 * 8)(a0)
    ld x30, (30 * 8)(a0)
    ld x31, (31 * 8)(a0)
    ld x10, (10 * 8)(a0)
    sret

trap_dispatch:
    ld t0, (34 * 8)(a0)         # scause == 8 (CAUSE_USER_ECALL)
    li t1, 8
    bne t0, t1, sbi_shutdown_fail
    ld t0, (17 * 8)(a0)         # user a7 == 0x1234
    li t1, 0x1234
    bne t0, t1, sbi_shutdown_fail
    ld t0, (10 * 8)(a0)         # user a0 == 42
    li t1, 42
    bne t0, t1, sbi_shutdown_fail

    fence.i                     # verify Zifencei encoding (0x0000100f)

    li a0, 'O'
    call sbi_putc
    li a0, 'K'
    call sbi_putc
    li a0, '\n'
    call sbi_putc

    li a7, SBI_EXT_SRST
    li a6, SBI_EXT_SRST_RESET
    li a0, SBI_SRST_TYPE_SHUTDOWN
    li a1, SBI_SRST_REASON_NONE
    ecall
1:  wfi
    j 1b

sbi_shutdown_fail:
    li a7, SBI_EXT_SRST
    li a6, SBI_EXT_SRST_RESET
    li a0, SBI_SRST_TYPE_SHUTDOWN
    li a1, 1
    ecall
1:  wfi
    j 1b

sbi_putc:
    li a7, SBI_EXT_DBCN
    li a6, SBI_EXT_DBCN_CONSOLE_WRITE_B
    ecall
    ret

    # =====================================================================
    # 3. Isolated 4 KiB User-Mode Payload (.user_text -> VA 0x10000)
    # =====================================================================
    .section .user_text, "ax"
    .balign 4
user_entry:
    li a7, 0x1234
    li a0, 42
    ecall
    j .

    # =====================================================================
    # 4. Page-Aligned Static Buffers (.bss)
    # =====================================================================
    .section .bss
    .balign 4096
boot_l2_pt:
    .space 4096
boot_l1_kern_pt:
    .space 4096
boot_l1_user_pt:
    .space 4096
boot_l0_user_pt:
    .space 4096
user_stack_page:
    .space 4096
kernel_stack:
    .space 8192
kernel_stack_top:
    .balign 64
trap_frame:
    .space (38 * 8)
"#
);
