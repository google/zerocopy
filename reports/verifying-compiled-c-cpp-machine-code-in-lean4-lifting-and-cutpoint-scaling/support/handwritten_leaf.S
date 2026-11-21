/*
 * Minimal hand-written x86-64 leaf kernel (s2n-bignum style) serving as baseline
 * contrast against GCC/G++-compiled C/C++ .o functions: 0 stack frame, 0 spills,
 * 0 relocations, 0 indirect jumps, 0 external calls, single tight loop.
 */
    .text
    .globl leaf_add_u64
    .type leaf_add_u64, @function
    .p2align 4
leaf_add_u64:
    endbr64
    xorl    %eax, %eax
    testq   %rcx, %rcx
    jz      .Ldone
    xorq    %r8, %r8
    clc
.Lloop:
    movq    (%rsi,%r8,8), %r9
    adcq    (%rdx,%r8,8), %r9
    movq    %r9, (%rdi,%r8,8)
    incq    %r8
    decq    %rcx
    jnz     .Lloop
    setc    %al
.Ldone:
    ret
    .size leaf_add_u64, .-leaf_add_u64
    .section .note.GNU-stack,"",@progbits
