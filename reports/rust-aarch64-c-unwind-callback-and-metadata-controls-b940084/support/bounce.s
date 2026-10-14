// PREPARED ONLY: parent ABI/CFI review and compile/metadata gate precede execution.
// Darwin aarch64-apple-darwin, not arm64e; ordinary whole function, no asm! block.
// C-unwind ABI: x0 = extern C-unwind fn(u64)->u64, x1 = value.
// Result: callback(value).wrapping_add(1), or propagate its permitted Rust unwind.
// DWARF registers: 29=x29, 30=x30/LR, 31=SP.
.text
.p2align 2
.globl _anneal_unwind_bounce
_anneal_unwind_bounce:
    .cfi_startproc
    .cfi_def_cfa 31, 0
    .cfi_same_value 29
    .cfi_same_value 30
    stp x29, x30, [sp, #-16]!
    .cfi_def_cfa_offset 16
    .cfi_offset 29, -16
    .cfi_offset 30, -8
    mov x29, sp
    .cfi_def_cfa_register 29
    mov x16, x0
    mov x0, x1
    blr x16
    add x0, x0, #1
    ldp x29, x30, [sp], #16
    .cfi_def_cfa 31, 0
    .cfi_same_value 29
    .cfi_same_value 30
    ret
    .cfi_endproc
.globl _anneal_unwind_bounce_end
_anneal_unwind_bounce_end:
.subsections_via_symbols
