// Copyright (c) 2017-2024 The OpenSSL Project Authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// Written by Andy Polyakov, @dot-asm, initially for use in the OpenSSL
// project.

// ----------------------------------------------------------------------------
// Keccak-f1600 permutation for SHA3
// Input a[25], rc[24]; output a[25]
//
// Keccak-f1600 permutation operation is at the core of SHA3 and SHAKE
// and is fully specified here:
//
//   https://keccak.team/files/Keccak-reference-3.0.pdf
//
//    extern void sha3_keccak_f1600(uint64_t a[25], const uint64_t rc[24]);
//
// Standard x86-64 ABI: RDI = a, RSI = rc
// Microsoft x64 ABI:   RCX = a, RDX = rc
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha3_keccak_f1600)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sha3_keccak_f1600)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha3_keccak_f1600)
        .text
        .balign 32

S2N_BN_SYMBOL(sha3_keccak_f1600):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(208)

        not    QWORD PTR [rdi+0x08]
        not    QWORD PTR [rdi+0x10]
        not    QWORD PTR [rdi+0x40]
        not    QWORD PTR [rdi+0x60]
        not    QWORD PTR [rdi+0x88]
        not    QWORD PTR [rdi+0xa0]

        lea    r15, [rsp]
        mov    rax, QWORD PTR [rdi+0xa0]
        mov    rbx, QWORD PTR [rdi+0xa8]
        mov    rcx, QWORD PTR [rdi+0xb0]
        mov    rdx, QWORD PTR [rdi+0xb8]
        mov    rbp, QWORD PTR [rdi+0xc0]
        mov r8, 0x0
Lsha3_keccak_f1600_loop:
        mov    QWORD PTR [rsp + 0xc8], r8
        mov    r8, QWORD PTR [rdi]
        mov    r9, QWORD PTR [rdi+0x30]
        mov    r10, QWORD PTR [rdi+0x60]
        mov    r11, QWORD PTR [rdi+0x90]
        xor    rcx, QWORD PTR [rdi+0x10]
        xor    rdx, QWORD PTR [rdi+0x18]
        xor    rax, r8
        xor    rbx, QWORD PTR [rdi+0x08]
        xor    rcx, QWORD PTR [rdi+0x38]
        xor    rax, QWORD PTR [rdi+0x28]
        mov    r12, rbp
        xor    rbp, QWORD PTR [rdi+0x20]
        xor    rcx, r10
        xor    rax, QWORD PTR [rdi+0x50]
        xor    rdx, QWORD PTR [rdi+0x40]
        xor    rbx, r9
        xor    rbp, QWORD PTR [rdi+0x48]
        xor    rcx, QWORD PTR [rdi+0x88]
        xor    rax, QWORD PTR [rdi+0x78]
        xor    rdx, QWORD PTR [rdi+0x68]
        xor    rbx, QWORD PTR [rdi+0x58]
        xor    rbp, QWORD PTR [rdi+0x70]
        mov    r13, rcx
        rol    rcx, 1
        xor    rcx, rax
        xor    rdx, r11
        rol    rax, 1
        xor    rax, rdx
        xor    rbx, QWORD PTR [rdi+0x80]
        rol    rdx, 1
        xor    rdx, rbx
        xor    rbp, QWORD PTR [rdi+0x98]
        rol    rbx, 1
        xor    rbx, rbp
        rol    rbp, 1
        xor    rbp, r13
        xor    r9, rcx
        xor    r10, rdx
        rol    r9, 0x2c
        xor    r11, rbp
        xor    r12, rax
        rol    r10, 0x2b
        xor    r8, rbx
        mov    r13, r9
        rol    r11, 0x15
        or     r9, r10
        xor    r9, r8
        rol    r12, 0xe
        xor    r9, QWORD PTR [rsi]
        mov    r14, r12
        and    r12, r11
        mov    QWORD PTR [r15], r9
        xor    r12, r10
        not    r10
        mov    QWORD PTR [r15+0x10], r12
        or     r10, r11
        mov    r12, QWORD PTR [rdi+0xb0]
        xor    r10, r13
        mov    QWORD PTR [r15+0x08], r10
        and    r13, r8
        mov    r9, QWORD PTR [rdi+0x48]
        xor    r13, r14
        mov    r10, QWORD PTR [rdi+0x50]
        mov    QWORD PTR [r15+0x20], r13
        or     r14, r8
        mov    r8, QWORD PTR [rdi+0x18]
        xor    r14, r11
        mov    r11, QWORD PTR [rdi+0x80]
        mov    QWORD PTR [r15+0x18], r14
        xor    r8, rbp
        xor    r12, rdx
        rol    r8, 0x1c
        xor    r11, rcx
        xor    r9, rax
        rol    r12, 0x3d
        rol    r11, 0x2d
        xor    r10, rbx
        rol    r9, 0x14
        mov    r13, r8
        or     r8, r12
        rol    r10, 0x3
        xor    r8, r11
        mov    QWORD PTR [r15+0x40], r8
        mov    r14, r9
        and    r9, r13
        mov    r8, QWORD PTR [rdi+0x08]
        xor    r9, r12
        not    r12
        mov    QWORD PTR [r15+0x48], r9
        or     r12, r11
        mov    r9, QWORD PTR [rdi+0x38]
        xor    r12, r10
        mov    QWORD PTR [r15+0x38], r12
        and    r11, r10
        mov    r12, QWORD PTR [rdi+0xa0]
        xor    r11, r14
        mov    QWORD PTR [r15+0x30], r11
        or     r14, r10
        mov    r10, QWORD PTR [rdi+0x68]
        xor    r14, r13
        mov    r11, QWORD PTR [rdi+0x98]
        mov    QWORD PTR [r15+0x28], r14
        xor    r10, rbp
        xor    r11, rax
        rol    r10, 0x19
        xor    r9, rdx
        rol    r11, 0x8
        xor    r12, rbx
        rol    r9, 0x6
        xor    r8, rcx
        rol    r12, 0x12
        mov    r13, r10
        and    r10, r11
        rol    r8, 1
        not    r11
        xor    r10, r9
        mov    QWORD PTR [r15+0x58], r10
        mov    r14, r12
        and    r12, r11
        mov    r10, QWORD PTR [rdi+0x58]
        xor    r12, r13
        mov    QWORD PTR [r15+0x60], r12
        or     r13, r9
        mov    r12, QWORD PTR [rdi+0xb8]
        xor    r13, r8
        mov    QWORD PTR [r15+0x50], r13
        and    r9, r8
        xor    r9, r14
        mov    QWORD PTR [r15+0x70], r9
        or     r14, r8
        mov    r9, QWORD PTR [rdi+0x28]
        xor    r14, r11
        mov    r11, QWORD PTR [rdi+0x88]
        mov    QWORD PTR [r15+0x68], r14
        mov    r8, QWORD PTR [rdi+0x20]
        xor    r10, rcx
        xor    r11, rdx
        rol    r10, 0xa
        xor    r9, rbx
        rol    r11, 0xf
        xor    r12, rbp
        rol    r9, 0x24
        xor    r8, rax
        rol    r12, 0x38
        mov    r13, r10
        or     r10, r11
        rol    r8, 0x1b
        not    r11
        xor    r10, r9
        mov    QWORD PTR [r15+0x80], r10
        mov    r14, r12
        or     r12, r11
        xor    r12, r13
        mov    QWORD PTR [r15+0x88], r12
        and    r13, r9
        xor    r13, r8
        mov    QWORD PTR [r15+0x78], r13
        or     r9, r8
        xor    r9, r14
        mov    QWORD PTR [r15+0x98], r9
        and    r8, r14
        xor    r8, r11
        mov    QWORD PTR [r15+0x90], r8
        xor    rdx, QWORD PTR [rdi+0x10]
        xor    rbp, QWORD PTR [rdi+0x40]
        rol    rdx, 0x3e
        xor    rcx, QWORD PTR [rdi+0xa8]
        rol    rbp, 0x37
        xor    rax, QWORD PTR [rdi+0x70]
        rol    rcx, 0x2
        xor    rbx, QWORD PTR [rdi+0x78]
        xchg   rdi, r15
        rol    rax, 0x27
        rol    rbx, 0x29
        mov    r13, rdx
        and    rdx, rbp
        not    rbp
        xor    rdx, rcx
        mov    QWORD PTR [rdi+0xc0], rdx
        mov    r14, rax
        and    rax, rbp
        xor    rax, r13
        mov    QWORD PTR [rdi+0xa0], rax
        or     r13, rcx
        xor    r13, rbx
        mov    QWORD PTR [rdi+0xb8], r13
        and    rcx, rbx
        xor    rcx, r14
        mov    QWORD PTR [rdi+0xb0], rcx
        or     rbx, r14
        xor    rbx, rbp
        mov    QWORD PTR [rdi+0xa8], rbx
        mov    rbp, rdx
        mov    rdx, r13
        lea    rsi, [rsi+0x8]
        mov    r8, QWORD PTR [rdi]
        mov    r9, QWORD PTR [rdi+0x30]
        mov    r10, QWORD PTR [rdi+0x60]
        mov    r11, QWORD PTR [rdi+0x90]
        xor    rcx, QWORD PTR [rdi+0x10]
        xor    rdx, QWORD PTR [rdi+0x18]
        xor    rax, r8
        xor    rbx, QWORD PTR [rdi+0x08]
        xor    rcx, QWORD PTR [rdi+0x38]
        xor    rax, QWORD PTR [rdi+0x28]
        mov    r12, rbp
        xor    rbp, QWORD PTR [rdi+0x20]
        xor    rcx, r10
        xor    rax, QWORD PTR [rdi+0x50]
        xor    rdx, QWORD PTR [rdi+0x40]
        xor    rbx, r9
        xor    rbp, QWORD PTR [rdi+0x48]
        xor    rcx, QWORD PTR [rdi+0x88]
        xor    rax, QWORD PTR [rdi+0x78]
        xor    rdx, QWORD PTR [rdi+0x68]
        xor    rbx, QWORD PTR [rdi+0x58]
        xor    rbp, QWORD PTR [rdi+0x70]
        mov    r13, rcx
        rol    rcx, 1
        xor    rcx, rax
        xor    rdx, r11
        rol    rax, 1
        xor    rax, rdx
        xor    rbx, QWORD PTR [rdi+0x80]
        rol    rdx, 1
        xor    rdx, rbx
        xor    rbp, QWORD PTR [rdi+0x98]
        rol    rbx, 1
        xor    rbx, rbp
        rol    rbp, 1
        xor    rbp, r13
        xor    r9, rcx
        xor    r10, rdx
        rol    r9, 0x2c
        xor    r11, rbp
        xor    r12, rax
        rol    r10, 0x2b
        xor    r8, rbx
        mov    r13, r9
        rol    r11, 0x15
        or     r9, r10
        xor    r9, r8
        rol    r12, 0xe
        xor    r9, QWORD PTR [rsi]
        mov    r14, r12
        and    r12, r11
        mov    QWORD PTR [r15], r9
        xor    r12, r10
        not    r10
        mov    QWORD PTR [r15+0x10], r12
        or     r10, r11
        mov    r12, QWORD PTR [rdi+0xb0]
        xor    r10, r13
        mov    QWORD PTR [r15+0x08], r10
        and    r13, r8
        mov    r9, QWORD PTR [rdi+0x48]
        xor    r13, r14
        mov    r10, QWORD PTR [rdi+0x50]
        mov    QWORD PTR [r15+0x20], r13
        or     r14, r8
        mov    r8, QWORD PTR [rdi+0x18]
        xor    r14, r11
        mov    r11, QWORD PTR [rdi+0x80]
        mov    QWORD PTR [r15+0x18], r14
        xor    r8, rbp
        xor    r12, rdx
        rol    r8, 0x1c
        xor    r11, rcx
        xor    r9, rax
        rol    r12, 0x3d
        rol    r11, 0x2d
        xor    r10, rbx
        rol    r9, 0x14
        mov    r13, r8
        or     r8, r12
        rol    r10, 0x3
        xor    r8, r11
        mov    QWORD PTR [r15+0x40], r8
        mov    r14, r9
        and    r9, r13
        mov    r8, QWORD PTR [rdi+0x08]
        xor    r9, r12
        not    r12
        mov    QWORD PTR [r15+0x48], r9
        or     r12, r11
        mov    r9, QWORD PTR [rdi+0x38]
        xor    r12, r10
        mov    QWORD PTR [r15+0x38], r12
        and    r11, r10
        mov    r12, QWORD PTR [rdi+0xa0]
        xor    r11, r14
        mov    QWORD PTR [r15+0x30], r11
        or     r14, r10
        mov    r10, QWORD PTR [rdi+0x68]
        xor    r14, r13
        mov    r11, QWORD PTR [rdi+0x98]
        mov    QWORD PTR [r15+0x28], r14
        xor    r10, rbp
        xor    r11, rax
        rol    r10, 0x19
        xor    r9, rdx
        rol    r11, 0x8
        xor    r12, rbx
        rol    r9, 0x6
        xor    r8, rcx
        rol    r12, 0x12
        mov    r13, r10
        and    r10, r11
        rol    r8, 1
        not    r11
        xor    r10, r9
        mov    QWORD PTR [r15+0x58], r10
        mov    r14, r12
        and    r12, r11
        mov    r10, QWORD PTR [rdi+0x58]
        xor    r12, r13
        mov    QWORD PTR [r15+0x60], r12
        or     r13, r9
        mov    r12, QWORD PTR [rdi+0xb8]
        xor    r13, r8
        mov    QWORD PTR [r15+0x50], r13
        and    r9, r8
        xor    r9, r14
        mov    QWORD PTR [r15+0x70], r9
        or     r14, r8
        mov    r9, QWORD PTR [rdi+0x28]
        xor    r14, r11
        mov    r11, QWORD PTR [rdi+0x88]
        mov    QWORD PTR [r15+0x68], r14
        mov    r8, QWORD PTR [rdi+0x20]
        xor    r10, rcx
        xor    r11, rdx
        rol    r10, 0xa
        xor    r9, rbx
        rol    r11, 0xf
        xor    r12, rbp
        rol    r9, 0x24
        xor    r8, rax
        rol    r12, 0x38
        mov    r13, r10
        or     r10, r11
        rol    r8, 0x1b
        not    r11
        xor    r10, r9
        mov    QWORD PTR [r15+0x80], r10
        mov    r14, r12
        or     r12, r11
        xor    r12, r13
        mov    QWORD PTR [r15+0x88], r12
        and    r13, r9
        xor    r13, r8
        mov    QWORD PTR [r15+0x78], r13
        or     r9, r8
        xor    r9, r14
        mov    QWORD PTR [r15+0x98], r9
        and    r8, r14
        xor    r8, r11
        mov    QWORD PTR [r15+0x90], r8
        xor    rdx, QWORD PTR [rdi+0x10]
        xor    rbp, QWORD PTR [rdi+0x40]
        rol    rdx, 0x3e
        xor    rcx, QWORD PTR [rdi+0xa8]
        rol    rbp, 0x37
        xor    rax, QWORD PTR [rdi+0x70]
        rol    rcx, 0x2
        xor    rbx, QWORD PTR [rdi+0x78]
        xchg   rdi, r15
        rol    rax, 0x27
        rol    rbx, 0x29
        mov    r13, rdx
        and    rdx, rbp
        not    rbp
        xor    rdx, rcx
        mov    QWORD PTR [rdi+0xc0], rdx
        mov    r14, rax
        and    rax, rbp
        xor    rax, r13
        mov    QWORD PTR [rdi+0xa0], rax
        or     r13, rcx
        xor    r13, rbx
        mov    QWORD PTR [rdi+0xb8], r13
        and    rcx, rbx
        xor    rcx, r14
        mov    QWORD PTR [rdi+0xb0], rcx
        or     rbx, r14
        xor    rbx, rbp
        mov    QWORD PTR [rdi+0xa8], rbx
        mov    rbp, rdx
        mov    rdx, r13
        lea    rsi, [rsi+0x8]
        mov   r8,  QWORD PTR [rsp + 0xc8]
        add r8, 0x2
        cmp r8,  24
        jne    Lsha3_keccak_f1600_loop
        lea    rsi, [rsi-0xc0]
        not    QWORD PTR [rdi+0x08]
        not    QWORD PTR [rdi+0x10]
        not    QWORD PTR [rdi+0x40]
        not    QWORD PTR [rdi+0x60]
        not    QWORD PTR [rdi+0x88]
        not    QWORD PTR [rdi+0xa0]

        CFI_INC_RSP(208)
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(sha3_keccak_f1600)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,  "",  %progbits
#endif
