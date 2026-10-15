// E46 proposed positive source: Linux AAPCS64, little endian, EL0.
// No source in this plan has yet been assembled or executed.
.text
.p2align 2
.global pilot_mul
.type pilot_mul,%function
pilot_mul:
    mul x3, x0, x1
    umulh x4, x0, x1
    stp x3, x4, [x2]
    ret
.size pilot_mul, .-pilot_mul

.global pilot_add128
.type pilot_add128,%function
pilot_add128:
    ldp x3, x4, [x0]
    ldp x5, x6, [x1]
    adds x3, x3, x5
    adcs x4, x4, x6
    cset x0, cs
    stp x3, x4, [x2]
    ret
.size pilot_add128, .-pilot_add128

.global pilot_bswap
.type pilot_bswap,%function
pilot_bswap:
    rev x0, x0
    ret
.size pilot_bswap, .-pilot_bswap

.global pilot_load
.type pilot_load,%function
pilot_load:
    ldr x0, [x0]
    ret
.size pilot_load, .-pilot_load

.global pilot_store
.type pilot_store,%function
pilot_store:
    str x1, [x0]
    ret
.size pilot_store, .-pilot_store

.global pilot_copy16
.type pilot_copy16,%function
pilot_copy16:
    ldp x2, x3, [x1]
    stp x2, x3, [x0]
    ret
.size pilot_copy16, .-pilot_copy16

.global pilot_ptr
.type pilot_ptr,%function
pilot_ptr:
    add x0, x0, x1
    ret
.size pilot_ptr, .-pilot_ptr

.global pilot_call_helper
.type pilot_call_helper,%function
pilot_call_helper:
    .cfi_startproc
    stp x29, x30, [sp, #-16]!
    .cfi_def_cfa_offset 16
    .cfi_offset 29, -16
    .cfi_offset 30, -8
    mov x29, sp
    .cfi_def_cfa_register 29
    bl pilot_helper
    add x0, x0, #1
    ldp x29, x30, [sp], #16
    .cfi_def_cfa sp, 0
    .cfi_restore 29
    .cfi_restore 30
    ret
    .cfi_endproc
.size pilot_call_helper, .-pilot_call_helper

.global pilot_simd_copy16
.type pilot_simd_copy16,%function
pilot_simd_copy16:
    ldr q0, [x1]
    str q0, [x0]
    ret
.size pilot_simd_copy16, .-pilot_simd_copy16

.global pilot_simd_add16
.type pilot_simd_add16,%function
pilot_simd_add16:
    ldr q0, [x1]
    ldr q1, [x2]
    add v0.16b, v0.16b, v1.16b
    str q0, [x0]
    ret
.size pilot_simd_add16, .-pilot_simd_add16
.section .note.GNU-stack,"",%progbits
