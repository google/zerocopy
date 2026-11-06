// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Modular inverse modulo p_25519 = 2^255 - 19
// Input x[4]; output z[4]
//
// extern void bignum_inv_p25519(uint64_t z[static 4],const uint64_t x[static 4]);
//
// Assuming the 4-digit input x is coprime to p_25519, i.e. is not divisible
// by it, returns z < p_25519 such that x * z == 1 (mod p_25519). The input
// x does not need to be reduced modulo p_25519, but the output always is.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_inv_p25519)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_inv_p25519)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_inv_p25519)
        .text
        .balign 32

// Size in bytes of a 64-bit word

#define N 8

// Pointer-offset pairs for temporaries on stack

#define f rsp+0
#define g rsp+(4*N)
#define u rsp+(8*N)
#define v rsp+(12*N)
#define tmp QWORD PTR [rsp+(16*N)]
#define tmp2 QWORD PTR [rsp+(17*N)]
#define i QWORD PTR [rsp+(18*N)]
#define d QWORD PTR [rsp+(19*N)]

#define mat rsp+(20*N)

// Backup for the input pointer

#define res QWORD PTR [rsp+(24*N)]

// Total size to reserve on the stack

#define NSPACE 26*N

// Syntactic variants to make x86_att version simpler to generate

#define F 0
#define G (4*N)
#define U (8*N)
#define V (12*N)
#define MAT (20*N)

#define ff QWORD PTR [rsp]
#define gg QWORD PTR [rsp+(4*N)]

// Very similar to a subroutine call to the s2n-bignum word_divstep59.
// But different in register usage and returning the final matrix as
//
// [ r8   r10]
// [ r12  r14]
//
// and also returning the matrix still negated (which doesn't matter)

#define divstep59(din,fin,gin)                                          \
        mov     rsi, din;                                               \
        mov     rdx, fin;                                               \
        mov     rcx, gin;                                               \
        mov     rbx, rdx;                                               \
        and     rbx, 0xfffff;                                           \
        movabs  rax, 0xfffffe0000000000;                                \
        or      rbx, rax;                                               \
        and     rcx, 0xfffff;                                           \
        movabs  rax, 0xc000000000000000;                                \
        or      rcx, rax;                                               \
        mov     rax, 0xfffffffffffffffe;                                \
        xor     ebp, ebp;                                               \
        mov     edx, 0x2;                                               \
        mov     rdi, rbx;                                               \
        mov     r8, rax;                                                \
        test    rsi, rsi;                                               \
        cmovs   r8, rbp;                                                \
        test    rcx, 0x1;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        sar     rcx, 1;                                                 \
        mov     eax, 0x100000;                                          \
        lea     rdx, [rbx+rax];                                         \
        lea     rdi, [rcx+rax];                                         \
        shl     rdx, 0x16;                                              \
        shl     rdi, 0x16;                                              \
        sar     rdx, 0x2b;                                              \
        sar     rdi, 0x2b;                                              \
        movabs  rax, 0x20000100000;                                     \
        lea     rbx, [rbx+rax];                                         \
        lea     rcx, [rcx+rax];                                         \
        sar     rbx, 0x2a;                                              \
        sar     rcx, 0x2a;                                              \
        mov     [rsp+MAT], rdx;                                         \
        mov     [rsp+MAT+0x8], rbx;                                     \
        mov     [rsp+MAT+0x10], rdi;                                    \
        mov     [rsp+MAT+0x18], rcx;                                    \
        mov     r12, fin;                                               \
        imul    rdi, r12;                                               \
        imul    r12, rdx;                                               \
        mov     r13, gin;                                               \
        imul    rbx, r13;                                               \
        imul    r13, rcx;                                               \
        add     r12, rbx;                                               \
        add     r13, rdi;                                               \
        sar     r12, 0x14;                                              \
        sar     r13, 0x14;                                              \
        mov     rbx, r12;                                               \
        and     rbx, 0xfffff;                                           \
        movabs  rax, 0xfffffe0000000000;                                \
        or      rbx, rax;                                               \
        mov     rcx, r13;                                               \
        and     rcx, 0xfffff;                                           \
        movabs  rax, 0xc000000000000000;                                \
        or      rcx, rax;                                               \
        mov     rax, 0xfffffffffffffffe;                                \
        mov     edx, 0x2;                                               \
        mov     rdi, rbx;                                               \
        mov     r8, rax;                                                \
        test    rsi, rsi;                                               \
        cmovs   r8, rbp;                                                \
        test    rcx, 0x1;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        sar     rcx, 1;                                                 \
        mov     eax, 0x100000;                                          \
        lea     r8, [rbx+rax];                                          \
        lea     r10, [rcx+rax];                                         \
        shl     r8, 0x16;                                               \
        shl     r10, 0x16;                                              \
        sar     r8, 0x2b;                                               \
        sar     r10, 0x2b;                                              \
        movabs  rax, 0x20000100000;                                     \
        lea     r15, [rbx+rax];                                         \
        lea     r11, [rcx+rax];                                         \
        sar     r15, 0x2a;                                              \
        sar     r11, 0x2a;                                              \
        mov     rbx, r13;                                               \
        mov     rcx, r12;                                               \
        imul    r12, r8;                                                \
        imul    rbx, r15;                                               \
        add     r12, rbx;                                               \
        imul    r13, r11;                                               \
        imul    rcx, r10;                                               \
        add     r13, rcx;                                               \
        sar     r12, 0x14;                                              \
        sar     r13, 0x14;                                              \
        mov     rbx, r12;                                               \
        and     rbx, 0xfffff;                                           \
        movabs  rax, 0xfffffe0000000000;                                \
        or      rbx, rax;                                               \
        mov     rcx, r13;                                               \
        and     rcx, 0xfffff;                                           \
        movabs  rax, 0xc000000000000000;                                \
        or      rcx, rax;                                               \
        mov     rax, [rsp+MAT];                                         \
        imul    rax, r8;                                                \
        mov     rdx, [rsp+MAT+0x10];                                    \
        imul    rdx, r15;                                               \
        imul    r8, [rsp+MAT+0x8];                                      \
        imul    r15, [rsp+MAT+0x18];                                    \
        add     r15, r8;                                                \
        lea     r9, [rax+rdx];                                          \
        mov     rax, [rsp+MAT];                                         \
        imul    rax, r10;                                               \
        mov     rdx, [rsp+MAT+0x10];                                    \
        imul    rdx, r11;                                               \
        imul    r10, [rsp+MAT+0x8];                                     \
        imul    r11, [rsp+MAT+0x18];                                    \
        add     r11, r10;                                               \
        lea     r13, [rax+rdx];                                         \
        mov     rax, 0xfffffffffffffffe;                                \
        mov     edx, 0x2;                                               \
        mov     rdi, rbx;                                               \
        mov     r8, rax;                                                \
        test    rsi, rsi;                                               \
        cmovs   r8, rbp;                                                \
        test    rcx, 0x1;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        sar     rcx, 1;                                                 \
        mov     eax, 0x100000;                                          \
        lea     r8, [rbx+rax];                                          \
        lea     r12, [rcx+rax];                                         \
        shl     r8, 0x15;                                               \
        shl     r12, 0x15;                                              \
        sar     r8, 0x2b;                                               \
        sar     r12, 0x2b;                                              \
        movabs  rax, 0x20000100000;                                     \
        lea     r10, [rbx+rax];                                         \
        lea     r14, [rcx+rax];                                         \
        sar     r10, 0x2b;                                              \
        sar     r14, 0x2b;                                              \
        mov     rax, r9;                                                \
        imul    rax, r8;                                                \
        mov     rdx, r13;                                               \
        imul    rdx, r10;                                               \
        imul    r8, r15;                                                \
        imul    r10, r11;                                               \
        add     r10, r8;                                                \
        lea     r8, [rax+rdx];                                          \
        mov     rax, r9;                                                \
        imul    rax, r12;                                               \
        mov     rdx, r13;                                               \
        imul    rdx, r14;                                               \
        imul    r12, r15;                                               \
        imul    r14, r11;                                               \
        add     r14, r12;                                               \
        lea     r12, [rax+rdx]

S2N_BN_SYMBOL(bignum_inv_p25519):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Save registers and make room for temporaries

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

        CFI_DEC_RSP(NSPACE)

// Save the return pointer for the end so we can overwrite rdi later

        mov     res, rdi

// Copy the input and the prime into the main f and g variables.
// Make sure x is reduced so that g <= f as assumed in the bound proof.

        xor     eax, eax
        lea     rcx, [rax-19]
        not     rax
        mov     [rsp+F], rcx
        mov     [rsp+F+8], rax
        mov     [rsp+F+16], rax
        btr     rax, 63
        mov     [rsp+F+24], rax

        mov     rdx, [rsi]
        mov     rcx, [rsi+0x8]
        mov     r8, [rsi+0x10]
        mov     r9, [rsi+0x18]
        mov     eax, 0x1
        xor     r10d, r10d
        bts     r9, 0x3f
        adc     rax, r10
        imul    rax, rax, 19
        add     rdx, rax
        adc     rcx, r10
        adc     r8, r10
        adc     r9, r10
        mov     eax, 0x13
        cmovb   rax, r10
        sub     rdx, rax
        sbb     rcx, r10
        sbb     r8, r10
        sbb     r9, r10
        btr     r9, 0x3f
        mov     [rsp+G], rdx
        mov     [rsp+G+0x8], rcx
        mov     [rsp+G+0x10], r8
        mov     [rsp+G+0x18], r9

// Also maintain weakly reduced < 2*p_25519 vector [u,v] such that
// [f,g] == x * 2^{590-59*i} * [u,v] (mod p_25519)
// starting with [p_25519,x] == x * 2^{590-59*0} * [0,2^-590] (mod p_25519)

        xor     eax, eax
        mov     [rsp+U], rax
        mov     [rsp+U+8], rax
        mov     [rsp+U+16], rax
        mov     [rsp+U+24], rax

        mov     rax, 0xa0f99e2375022099
        mov     [rsp+V], rax
        mov     rax, 0xa8c68f3f1d132595
        mov     [rsp+V+8], rax
        mov     rax, 0x6c6c893805ac5242
        mov     [rsp+V+16], rax
        mov     rax, 0x276508b241770615
        mov     [rsp+V+24], rax

// Start of main loop. We jump into the middle so that the divstep
// portion is common to the special tenth iteration after a uniform
// first 9.

        mov     i, 10
        mov     d, 1
        jmp     Lbignum_inv_p25519_midloop

Lbignum_inv_p25519_loop:

// Separate out the matrix into sign-magnitude pairs

        mov     r9, r8
        sar     r9, 63
        xor     r8, r9
        sub     r8, r9

        mov     r11, r10
        sar     r11, 63
        xor     r10, r11
        sub     r10, r11

        mov     r13, r12
        sar     r13, 63
        xor     r12, r13
        sub     r12, r13

        mov     r15, r14
        sar     r15, 63
        xor     r14, r15
        sub     r14, r15

// Adjust the initial values to allow for complement instead of negation
// This initial offset is the same for [f,g] and [u,v] compositions.
// Save it in temporary storage for the [u,v] part and do [f,g] first.

        mov     rax, r8
        and     rax, r9
        mov     rdi, r10
        and     rdi, r11
        add     rdi, rax
        mov     tmp, rdi

        mov     rax, r12
        and     rax, r13
        mov     rsi, r14
        and     rsi, r15
        add     rsi, rax
        mov     tmp2, rsi

// Now the computation of the updated f and g values. This maintains a
// 2-word carry between stages so we can conveniently insert the shift
// right by 59 before storing back, and not overwrite digits we need
// again of the old f and g values.
//
// Digit 0 of [f,g]

        xor     ebx, ebx
        mov     rax, [rsp+F]
        xor     rax, r9
        mul     r8
        add     rdi, rax
        adc     rbx, rdx
        mov     rax, [rsp+G]
        xor     rax, r11
        mul     r10
        add     rdi, rax
        adc     rbx, rdx

        xor     ebp, ebp
        mov     rax, [rsp+F]
        xor     rax, r13
        mul     r12
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+G]
        xor     rax, r15
        mul     r14
        add     rsi, rax
        adc     rbp, rdx

// Digit 1 of [f,g]

        xor     ecx, ecx
        mov     rax, [rsp+F+N]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+G+N]
        xor     rax, r11
        mul     r10
        add     rbx, rax
        adc     rcx, rdx
        shrd    rdi, rbx, 59
        mov     [rsp+F], rdi

        xor     edi, edi
        mov     rax, [rsp+F+N]
        xor     rax, r13
        mul     r12
        add     rbp, rax
        adc     rdi, rdx
        mov     rax, [rsp+G+N]
        xor     rax, r15
        mul     r14
        add     rbp, rax
        adc     rdi, rdx
        shrd    rsi, rbp, 59
        mov     [rsp+G], rsi

// Digit 2 of [f,g]

        xor     esi, esi
        mov     rax, [rsp+F+2*N]
        xor     rax, r9
        mul     r8
        add     rcx, rax
        adc     rsi, rdx
        mov     rax, [rsp+G+2*N]
        xor     rax, r11
        mul     r10
        add     rcx, rax
        adc     rsi, rdx
        shrd    rbx, rcx, 59
        mov     [rsp+F+N], rbx

        xor     ebx, ebx
        mov     rax, [rsp+F+2*N]
        xor     rax, r13
        mul     r12
        add     rdi, rax
        adc     rbx, rdx
        mov     rax, [rsp+G+2*N]
        xor     rax, r15
        mul     r14
        add     rdi, rax
        adc     rbx, rdx
        shrd    rbp, rdi, 59
        mov     [rsp+G+N], rbp

// Digits 3 and 4 of [f,g]

        mov     rax, [rsp+F+3*N]
        xor     rax, r9
        mov     rbp, rax
        sar     rbp, 63
        and     rbp, r8
        neg     rbp
        mul     r8
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+G+3*N]
        xor     rax, r11
        mov     rdx, rax
        sar     rdx, 63
        and     rdx, r10
        sub     rbp, rdx
        mul     r10
        add     rsi, rax
        adc     rbp, rdx
        shrd    rcx, rsi, 59
        mov     [rsp+F+2*N], rcx
        shrd    rsi, rbp, 59

        mov     rax, [rsp+F+3*N]
        mov     [rsp+F+3*N], rsi

        xor     rax, r13
        mov     rsi, rax
        sar     rsi, 63
        and     rsi, r12
        neg     rsi
        mul     r12
        add     rbx, rax
        adc     rsi, rdx
        mov     rax, [rsp+G+3*N]
        xor     rax, r15
        mov     rdx, rax
        sar     rdx, 63
        and     rdx, r14
        sub     rsi, rdx
        mul     r14
        add     rbx, rax
        adc     rsi, rdx
        shrd    rdi, rbx, 59
        mov     [rsp+G+2*N], rdi
        shrd    rbx, rsi, 59
        mov     [rsp+G+3*N], rbx

// Get the initial carries back from storage and do the [u,v] accumulation

        mov     rbx, tmp
        mov     rbp, tmp2

// Digit 0 of [u,v]

        xor     ecx, ecx
        mov     rax, [rsp+U]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+V]
        xor     rax, r11
        mul     r10
        add     rbx, rax
        adc     rcx, rdx

        xor     esi, esi
        mov     rax, [rsp+U]
        xor     rax, r13
        mul     r12
        mov     [rsp+U], rbx
        add     rbp, rax
        adc     rsi, rdx
        mov     rax, [rsp+V]
        xor     rax, r15
        mul     r14
        add     rbp, rax
        adc     rsi, rdx
        mov     [rsp+V], rbp

// Digit 1 of [u,v]

        xor     ebx, ebx
        mov     rax, [rsp+U+N]
        xor     rax, r9
        mul     r8
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, [rsp+V+N]
        xor     rax, r11
        mul     r10
        add     rcx, rax
        adc     rbx, rdx

        xor     ebp, ebp
        mov     rax, [rsp+U+N]
        xor     rax, r13
        mul     r12
        mov     [rsp+U+N], rcx
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+V+N]
        xor     rax, r15
        mul     r14
        add     rsi, rax
        adc     rbp, rdx
        mov     [rsp+V+N], rsi

// Digit 2 of [u,v]

        xor     ecx, ecx
        mov     rax, [rsp+U+2*N]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+V+2*N]
        xor     rax, r11
        mul     r10
        add     rbx, rax
        adc     rcx, rdx

        xor     esi, esi
        mov     rax, [rsp+U+2*N]
        xor     rax, r13
        mul     r12
        mov     [rsp+U+2*N], rbx
        add     rbp, rax
        adc     rsi, rdx
        mov     rax, [rsp+V+2*N]
        xor     rax, r15
        mul     r14
        add     rbp, rax
        adc     rsi, rdx
        mov     [rsp+V+2*N], rbp

// Digits 3 and 4 of u (top is unsigned)

        mov     rax, [rsp+U+3*N]
        xor     rax, r9
        mov     rbx, r9
        and     rbx, r8
        neg     rbx
        mul     r8
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, [rsp+V+3*N]
        xor     rax, r11
        mov     rdx, r11
        and     rdx, r10
        sub     rbx, rdx
        mul     r10
        add     rcx, rax
        adc     rdx, rbx

// Modular reduction of u

        mov     rbx, rdx
        shld    rdx, rcx, 1
        sar     rbx, 63
        add     rdx, rbx
        mov     eax, 19
        imul    rdx
        mov     r8, [rsp+U]
        add     r8, rax
        mov     [rsp+U], r8
        mov     r8, [rsp+U+N]
        adc     r8, rdx
        mov     [rsp+U+N], r8
        mov     r8, [rsp+U+2*N]
        adc     r8, rbx
        mov     [rsp+U+2*N], r8
        adc     rcx, rbx
        shl     rax, 63
        add     rcx, rax

// Preload for last use of old u digit 3

        mov     rax, [rsp+U+3*N]
        mov     [rsp+U+3*N], rcx

// Digits 3 and 4 of v (top is unsigned)

        xor     rax, r13
        mov     rcx, r13
        and     rcx, r12
        neg     rcx
        mul     r12
        add     rsi, rax
        adc     rcx, rdx
        mov     rax, [rsp+V+3*N]
        xor     rax, r15
        mov     rdx, r15
        and     rdx, r14
        sub     rcx, rdx
        mul     r14
        add     rsi, rax
        adc     rdx, rcx

// Modular reduction of v

        mov     rcx, rdx
        shld    rdx, rsi, 1
        sar     rcx, 63
        mov     eax, 19
        add     rdx, rcx
        imul    rdx
        mov     r8, [rsp+V]
        add     r8, rax
        mov     [rsp+V], r8
        mov     r8, [rsp+V+N]
        adc     r8, rdx
        mov     [rsp+V+N], r8
        mov     r8, [rsp+V+2*N]
        adc     r8, rcx
        mov     [rsp+V+2*N], r8
        adc     rsi, rcx
        shl     rax, 63
        add     rsi, rax
        mov     [rsp+V+3*N], rsi

Lbignum_inv_p25519_midloop:

        divstep59(d,ff,gg)
        mov     d, rsi

// Next iteration

        dec     i
        jnz     Lbignum_inv_p25519_loop

// The 10th and last iteration does not need anything except the
// u value and the sign of f; the latter can be obtained from the
// lowest word of f. So it's done differently from the main loop.
// Find the sign of the new f. For this we just need one digit
// since we know (for in-scope cases) that f is either +1 or -1.
// We don't explicitly shift right by 59 either, but looking at
// bit 63 (or any bit >= 60) of the unshifted result is enough
// to distinguish -1 from +1; this is then made into a mask.

        mov     rax, [rsp+F]
        mov     rcx, [rsp+G]
        imul    rax, r8
        imul    rcx, r10
        add     rax, rcx
        sar     rax, 63

// Now separate out the matrix into sign-magnitude pairs
// and adjust each one based on the sign of f.
//
// Note that at this point we expect |f|=1 and we got its
// sign above, so then since [f,0] == x * [u,v] (mod p_25519)
// we want to flip the sign of u according to that of f.

        mov     r9, r8
        sar     r9, 63
        xor     r8, r9
        sub     r8, r9
        xor     r9, rax

        mov     r11, r10
        sar     r11, 63
        xor     r10, r11
        sub     r10, r11
        xor     r11, rax

        mov     r13, r12
        sar     r13, 63
        xor     r12, r13
        sub     r12, r13
        xor     r13, rax

        mov     r15, r14
        sar     r15, 63
        xor     r14, r15
        sub     r14, r15
        xor     r15, rax

// Adjust the initial value to allow for complement instead of negation

        mov     rax, r8
        and     rax, r9
        mov     r12, r10
        and     r12, r11
        add     r12, rax

// Digit 0 of [u]

        xor     r13d, r13d
        mov     rax, [rsp+U]
        xor     rax, r9
        mul     r8
        add     r12, rax
        adc     r13, rdx
        mov     rax, [rsp+V]
        xor     rax, r11
        mul     r10
        add     r12, rax
        adc     r13, rdx

// Digit 1 of [u]

        xor     r14d, r14d
        mov     rax, [rsp+U+N]
        xor     rax, r9
        mul     r8
        add     r13, rax
        adc     r14, rdx
        mov     rax, [rsp+V+N]
        xor     rax, r11
        mul     r10
        add     r13, rax
        adc     r14, rdx

// Digit 2 of [u]

        xor     r15d, r15d
        mov     rax, [rsp+U+2*N]
        xor     rax, r9
        mul     r8
        add     r14, rax
        adc     r15, rdx
        mov     rax, [rsp+V+2*N]
        xor     rax, r11
        mul     r10
        add     r14, rax
        adc     r15, rdx

// Digits 3 and 4 of u (top is unsigned)

        mov     rax, [rsp+U+3*N]
        xor     rax, r9
        and     r9, r8
        neg     r9
        mul     r8
        add     r15, rax
        adc     r9, rdx
        mov     rax, [rsp+V+3*N]
        xor     rax, r11
        mov     rdx, r11
        and     rdx, r10
        sub     r9, rdx
        mul     r10
        add     r15, rax
        adc     r9, rdx

// Modular reduction of u, this time strictly 2^255-19.

        mov     rax, r9
        shld    rax, r15, 1
        sar     r9, 63
        mov     ebx, 19
        lea     rax, [rax+r9+1]
        imul    rbx
        xor     ebp, ebp
        add     r12, rax
        adc     r13, rdx
        adc     r14, r9
        adc     r15, r9
        shl     rax, 63
        add     r15, rax
        cmovns  rbx, rbp
        sub     r12, rbx
        sbb     r13, rbp
        sbb     r14, rbp
        sbb     r15, rbp
        btr     r15, 0x3f

// Store it back to the final output

        mov     rdi, res
        mov     [rdi], r12
        mov     [rdi+N], r13
        mov     [rdi+2*N], r14
        mov     [rdi+3*N], r15

// Restore stack and registers

        CFI_INC_RSP(NSPACE)

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

S2N_BN_SIZE_DIRECTIVE(bignum_inv_p25519)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
