// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery inverse modulo p_384 = 2^384 - 2^128 - 2^96 + 2^32 - 1
// Input x[6]; output z[6]
//
// extern void bignum_montinv_p384(uint64_t z[static 6],
//                                 const uint64_t x[static 6]);
//
// If the 6-digit input x is coprime to p_384, i.e. is not divisible
// by it, returns z < p_384 such that x * z == 2^768 (mod p_384). This
// is effectively "Montgomery inverse" because if we consider x and z as
// Montgomery forms of X and Z, i.e. x == 2^384 * X and z == 2^384 * Z
// (both mod p_384) then X * Z == 1 (mod p_384). That is, this function
// gives the analog of the modular inverse bignum_inv_p384 but with both
// input and output in the Montgomery domain. Note that x does not need
// to be reduced modulo p_384, but the output always is. If the input
// is divisible (i.e. is 0 or p_384), then there can be no solution to
// the congruence x * z == 2^768 (mod p_384), and z = 0 is returned.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montinv_p384)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_montinv_p384)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montinv_p384)
        .text
        .balign 32

// Size in bytes of a 64-bit word

#define N 8

// Pointer-offset pairs for temporaries on stack
// The u and v variables are 6 words each as expected, but the f and g
// variables are 8 words each -- they need to have at least one extra
// word for a sign word, and to preserve alignment we "round up" to 8.
// In fact, we currently keep an extra word in u and v as well.

#define f rsp+0
#define g rsp+(8*N)
#define u rsp+(16*N)
#define v rsp+(24*N)
#define tmp QWORD PTR [rsp+(32*N)]
#define tmp2 QWORD PTR [rsp+(33*N)]
#define i QWORD PTR [rsp+(34*N)]
#define d QWORD PTR [rsp+(35*N)]

#define mat rsp+(36*N)

// Backup for the input pointer

#define res QWORD PTR [rsp+(40*N)]

// Total size to reserve on the stack

#define NSPACE 42*N

// Syntactic variants to make x86_att version simpler to generate

#define F 0
#define G (8*N)
#define U (16*N)
#define V (24*N)
#define MAT (36*N)

#define ff QWORD PTR [rsp]
#define gg QWORD PTR [rsp+(8*N)]

// ---------------------------------------------------------------------------
// Core signed almost-Montgomery reduction macro from P[6..0] to P[5..0].
// ---------------------------------------------------------------------------

#define amontred(P)                                                     \
/* We only know the input is -2^444 < x < 2^444. To do traditional  */  \
/* unsigned Montgomery reduction, start by adding 2^61 * p_384.     */  \
        mov     r8, 0xe000000000000000;                             \
        xor     eax, eax;                                           \
        add     r8, [P];                                            \
        mov     r9, 0x000000001fffffff;                             \
        lea     rax, [rax-1];                                       \
        adc     r9, [P+N];                                          \
        mov     r10, 0xdfffffffe0000000;                            \
        adc     r10, [P+2*N];                                       \
        mov     r11, [P+3*N];                                       \
        adc     r11, rax;                                           \
        mov     r12, [P+4*N];                                       \
        adc     r12, rax;                                           \
        mov     r13, [P+5*N];                                       \
        adc     r13, rax;                                           \
        mov     r14, 0x1fffffffffffffff;                            \
        adc     r14, [P+6*N];                                       \
/* Correction multiplier is rbx = w = [d0 + (d0<<32)] mod 2^64 */   \
        mov     rbx, r8;                                            \
        shl     rbx, 32;                                            \
        add     rbx, r8;                                            \
/* Construct [rbp;rdx;rax;-] = (2^384 - p_384) * w */               \
/* We know lowest word will cancel so can re-use r8 as a temp */    \
        xor     ebp, ebp;                                           \
        mov     rax, 0xffffffff00000001;                            \
        mul     rbx;                                                \
        mov     r8, rdx;                                            \
        mov     rax, 0x00000000ffffffff;                            \
        mul     rbx;                                                \
        add     rax, r8;                                            \
        adc     rdx, rbx;                                           \
        adc     ebp, ebp;                                           \
/*  Now subtract that and add 2^384 * w, catching carry in rax  */  \
        sub     r9, rax;                                            \
        sbb     r10, rdx;                                           \
        sbb     r11, rbp;                                           \
        sbb     r12, 0;                                             \
        sbb     r13, 0;                                             \
        sbb     r14, 0;                                             \
        sbb     rax, rax;                                           \
        add     r14, rbx;                                           \
        adc     rax, 0;                                             \
/* Now if top is nonzero we subtract p_384 (almost-Montgomery) */   \
        neg     rax;                                                \
        mov     rbx, 0x00000000ffffffff;                            \
        and     rbx, rax;                                           \
        mov     rcx, 0xffffffff00000000;                            \
        and     rcx, rax;                                           \
        mov     rdx, 0xfffffffffffffffe;                            \
        and     rdx, rax;                                           \
        sub     r9, rbx;                                            \
        mov     [P], r9;                                            \
        sbb     r10, rcx;                                           \
        mov     [P+N], r10;                                         \
        sbb     r11, rdx;                                           \
        mov     [P+2*N], r11;                                       \
        sbb     r12, rax;                                           \
        mov     [P+3*N], r12;                                       \
        sbb     r13, rax;                                           \
        mov     [P+4*N], r13;                                       \
        sbb     r14, rax;                                           \
        mov     [P+5*N], r14

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

S2N_BN_SYMBOL(bignum_montinv_p384):
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

// Copy the constant p_384 into f including the 7th zero digit

        mov     eax, 0xffffffff
        mov     [rsp+F], rax
        mov     rbx, rax
        not     rbx
        mov     [rsp+F+N], rbx
        xor     ebp, ebp
        lea     rcx, [rbp-2]
        mov     [rsp+F+2*N], rcx
        lea     rdx, [rbp-1]
        mov     [rsp+F+3*N], rdx
        mov     [rsp+F+4*N], rdx
        mov     [rsp+F+5*N], rdx
        mov     [rsp+F+6*N], rbp

// Copy input but to g, reduced mod p_384 so that g <= f as assumed
// in the divstep bound proof.

        mov     r8, [rsi]
        sub     r8, rax
        mov     r9, [rsi+N]
        sbb     r9, rbx
        mov     r10, [rsi+2*N]
        sbb     r10, rcx
        mov     r11, [rsi+3*N]
        sbb     r11, rdx
        mov     r12, [rsi+4*N]
        sbb     r12, rdx
        mov     r13, [rsi+5*N]
        sbb     r13, rdx

        cmovc   r8, [rsi]
        cmovc   r9, [rsi+N]
        cmovc   r10, [rsi+2*N]
        cmovc   r11, [rsi+3*N]
        cmovc   r12, [rsi+4*N]
        cmovc   r13, [rsi+5*N]

        mov     [rsp+G], r8
        mov     [rsp+G+N], r9
        mov     [rsp+G+2*N], r10
        mov     [rsp+G+3*N], r11
        mov     [rsp+G+4*N], r12
        mov     [rsp+G+5*N], r13
        mov     [rsp+G+6*N], rbp

// Also maintain reduced < 2^384 vector [u,v] such that
// [f,g] == x * 2^{5*i-843} * [u,v] (mod p_384)
// starting with [p_384,x] == x * 2^{5*0-843} * [0,2^843] (mod p_384)
// The weird-looking 5*i modifications come in because we are doing
// 64-bit word-sized Montgomery reductions at each stage, which is
// 5 bits more than the 59-bit requirement to keep things stable.
// After the 15th and last iteration and sign adjustment, when
// f == 1 for in-scope cases, we have x * 2^{75-843} * u == 1, i.e.
// x * u == 2^768 as required.

        xor     eax, eax
        mov     [rsp+U], rax
        mov     [rsp+U+N], rax
        mov     [rsp+U+2*N], rax
        mov     [rsp+U+3*N], rax
        mov     [rsp+U+4*N], rax
        mov     [rsp+U+5*N], rax

// The starting constant 2^843 mod p_384 is
// 0x0000000000000800:00001000000007ff:fffff00000000000
//  :00001000000007ff:fffff00000000800:0000000000000000
// where colons separate 64-bit subwords, least significant at the right.
// These are constructed dynamically to reduce large constant loads.

        mov     [rsp+V], rax
        mov     rcx, 0xfffff00000000800
        mov     [rsp+V+N], rcx
        mov     rdx, 0x00001000000007ff
        mov     [rsp+V+2*N], rdx
        btr     rcx, 11
        mov     [rsp+V+3*N], rcx
        mov     [rsp+V+4*N], rdx
        bts     rax, 11
        mov     [rsp+V+5*N], rax

// Start of main loop. We jump into the middle so that the divstep
// portion is common to the special fifteenth iteration after a uniform
// first 14.

        mov     i, 15
        mov     d, 1
        jmp     Lbignum_montinv_p384_midloop

Lbignum_montinv_p384_loop:

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

// Digit 3 of [f,g]

        xor     ebp, ebp
        mov     rax, [rsp+F+3*N]
        xor     rax, r9
        mul     r8
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+G+3*N]
        xor     rax, r11
        mul     r10
        add     rsi, rax
        adc     rbp, rdx
        shrd    rcx, rsi, 59
        mov     [rsp+F+2*N], rcx

        xor     ecx, ecx
        mov     rax, [rsp+F+3*N]
        xor     rax, r13
        mul     r12
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+G+3*N]
        xor     rax, r15
        mul     r14
        add     rbx, rax
        adc     rcx, rdx
        shrd    rdi, rbx, 59
        mov     [rsp+G+2*N], rdi

// Digit 4 of [f,g]

        xor     edi, edi
        mov     rax, [rsp+F+4*N]
        xor     rax, r9
        mul     r8
        add     rbp, rax
        adc     rdi, rdx
        mov     rax, [rsp+G+4*N]
        xor     rax, r11
        mul     r10
        add     rbp, rax
        adc     rdi, rdx
        shrd    rsi, rbp, 59
        mov     [rsp+F+3*N], rsi

        xor     esi, esi
        mov     rax, [rsp+F+4*N]
        xor     rax, r13
        mul     r12
        add     rcx, rax
        adc     rsi, rdx
        mov     rax, [rsp+G+4*N]
        xor     rax, r15
        mul     r14
        add     rcx, rax
        adc     rsi, rdx
        shrd    rbx, rcx, 59
        mov     [rsp+G+3*N], rbx

// Digits 5 and 6 of [f,g]

        mov     rax, [rsp+F+5*N]
        xor     rax, r9
        mov     rbx, [rsp+F+6*N]
        xor     rbx, r9
        and     rbx, r8
        neg     rbx
        mul     r8
        add     rdi, rax
        adc     rbx, rdx
        mov     rax, [rsp+G+5*N]
        xor     rax, r11
        mov     rdx, [rsp+G+6*N]
        xor     rdx, r11
        and     rdx, r10
        sub     rbx, rdx
        mul     r10
        add     rdi, rax
        adc     rbx, rdx
        shrd    rbp, rdi, 59
        mov     [rsp+F+4*N], rbp
        shrd    rdi, rbx, 59
        sar     rbx, 59

        mov     rax, [rsp+F+5*N]
        mov     [rsp+F+5*N], rdi

        mov     rdi, [rsp+F+6*N]
        mov     [rsp+F+6*N], rbx

        xor     rax, r13
        xor     rdi, r13
        and     rdi, r12
        neg     rdi
        mul     r12
        add     rsi, rax
        adc     rdi, rdx
        mov     rax, [rsp+G+5*N]
        xor     rax, r15
        mov     rdx, [rsp+G+6*N]
        xor     rdx, r15
        and     rdx, r14
        sub     rdi, rdx
        mul     r14
        add     rsi, rax
        adc     rdi, rdx
        shrd    rcx, rsi, 59
        mov     [rsp+G+4*N], rcx
        shrd    rsi, rdi, 59
        mov     [rsp+G+5*N], rsi
        sar     rdi, 59
        mov     [rsp+G+6*N], rdi

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

// Digit 3 of [u,v]

        xor     ebx, ebx
        mov     rax, [rsp+U+3*N]
        xor     rax, r9
        mul     r8
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, [rsp+V+3*N]
        xor     rax, r11
        mul     r10
        add     rcx, rax
        adc     rbx, rdx

        xor     ebp, ebp
        mov     rax, [rsp+U+3*N]
        xor     rax, r13
        mul     r12
        mov     [rsp+U+3*N], rcx
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+V+3*N]
        xor     rax, r15
        mul     r14
        add     rsi, rax
        adc     rbp, rdx
        mov     [rsp+V+3*N], rsi

// Digit 4 of [u,v]

        xor     ecx, ecx
        mov     rax, [rsp+U+4*N]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+V+4*N]
        xor     rax, r11
        mul     r10
        add     rbx, rax
        adc     rcx, rdx

        xor     esi, esi
        mov     rax, [rsp+U+4*N]
        xor     rax, r13
        mul     r12
        mov     [rsp+U+4*N], rbx
        add     rbp, rax
        adc     rsi, rdx
        mov     rax, [rsp+V+4*N]
        xor     rax, r15
        mul     r14
        add     rbp, rax
        adc     rsi, rdx
        mov     [rsp+V+4*N], rbp

// Digits 5 and 6 of u (top is unsigned)

        mov     rax, [rsp+U+5*N]
        xor     rax, r9
        mov     rbx, r9
        and     rbx, r8
        neg     rbx
        mul     r8
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, [rsp+V+5*N]
        xor     rax, r11
        mov     rdx, r11
        and     rdx, r10
        sub     rbx, rdx
        mul     r10
        add     rcx, rax
        adc     rdx, rbx

// Preload for last use of old u digit 3

        mov     rax, [rsp+U+5*N]
        mov     [rsp+U+5*N], rcx
        mov     [rsp+U+6*N], rdx

// Digits 5 and 6 of v (top is unsigned)

        xor     rax, r13
        mov     rcx, r13
        and     rcx, r12
        neg     rcx
        mul     r12
        add     rsi, rax
        adc     rcx, rdx
        mov     rax, [rsp+V+5*N]
        xor     rax, r15
        mov     rdx, r15
        and     rdx, r14
        sub     rcx, rdx
        mul     r14
        add     rsi, rax
        adc     rdx, rcx
        mov     [rsp+V+5*N], rsi
        mov     [rsp+V+6*N], rdx

// Montgomery reduction of u

        amontred(u)

// Montgomery reduction of v

        amontred(v)

Lbignum_montinv_p384_midloop:

        divstep59(d,ff,gg)
        mov     d, rsi

// Next iteration

        dec     i
        jnz     Lbignum_montinv_p384_loop

// The 15th and last iteration does not need anything except the
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
// sign above, so then since [f,0] == x * 2^{-768} [u,v] (mod p_384)
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
        mov     [rsp+U], r12
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
        mov     [rsp+U+N], r13
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
        mov     [rsp+U+2*N], r14
        adc     r15, rdx

// Digit 3 of [u]

        xor     r14d, r14d
        mov     rax, [rsp+U+3*N]
        xor     rax, r9
        mul     r8
        add     r15, rax
        adc     r14, rdx
        mov     rax, [rsp+V+3*N]
        xor     rax, r11
        mul     r10
        add     r15, rax
        mov     [rsp+U+3*N], r15
        adc     r14, rdx

// Digit 4 of [u]

        xor     r15d, r15d
        mov     rax, [rsp+U+4*N]
        xor     rax, r9
        mul     r8
        add     r14, rax
        adc     r15, rdx
        mov     rax, [rsp+V+4*N]
        xor     rax, r11
        mul     r10
        add     r14, rax
        mov     [rsp+U+4*N], r14
        adc     r15, rdx

// Digits 5 and 6 of u (top is unsigned)

        mov     rax, [rsp+U+5*N]
        xor     rax, r9
        and     r9, r8
        neg     r9
        mul     r8
        add     r15, rax
        adc     r9, rdx
        mov     rax, [rsp+V+5*N]
        xor     rax, r11
        mov     rdx, r11
        and     rdx, r10
        sub     r9, rdx
        mul     r10
        add     r15, rax
        mov     [rsp+U+5*N], r15
        adc     r9, rdx
        mov     [rsp+U+6*N], r9

// Montgomery reduce u

        amontred(u)

// Perform final strict reduction mod p_384 and copy to output

        mov     eax, 0xffffffff
        mov     rbx, rax
        not     rbx
        xor     ebp, ebp
        lea     rcx, [rbp-2]
        lea     rdx, [rbp-1]

        mov     r8, [rsp+U]
        sub     r8, rax
        mov     r9, [rsp+U+N]
        sbb     r9, rbx
        mov     r10, [rsp+U+2*N]
        sbb     r10, rcx
        mov     r11, [rsp+U+3*N]
        sbb     r11, rdx
        mov     r12, [rsp+U+4*N]
        sbb     r12, rdx
        mov     r13, [rsp+U+5*N]
        sbb     r13, rdx

        cmovc   r8, [rsp+U]
        cmovc   r9, [rsp+U+N]
        cmovc   r10, [rsp+U+2*N]
        cmovc   r11, [rsp+U+3*N]
        cmovc   r12, [rsp+U+4*N]
        cmovc   r13, [rsp+U+5*N]

        mov     rdi, res
        mov     [rdi], r8
        mov     [rdi+N], r9
        mov     [rdi+2*N], r10
        mov     [rdi+3*N], r11
        mov     [rdi+4*N], r12
        mov     [rdi+5*N], r13

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

S2N_BN_SIZE_DIRECTIVE(bignum_montinv_p384)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
