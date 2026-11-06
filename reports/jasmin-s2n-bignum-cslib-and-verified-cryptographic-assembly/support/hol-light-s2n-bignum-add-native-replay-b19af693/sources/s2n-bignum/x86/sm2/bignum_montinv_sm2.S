// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery inverse modulo p_sm2 = 2^256 - 2^224 - 2^96 + 2^64 - 1
// Input x[4]; output z[4]
//
// extern void bignum_montinv_sm2(uint64_t z[static 4],
//                                const uint64_t x[static 4]);
//
// If the 4-digit input x is coprime to p_sm2, i.e. is not divisible
// by it, returns z < p_sm2 such that x * z == 2^512 (mod p_sm2). This
// is effectively "Montgomery inverse" because if we consider x and z as
// Montgomery forms of X and Z, i.e. x == 2^256 * X and z == 2^256 * Z
// (both mod p_sm2) then X * Z == 1 (mod p_sm2). That is, this function
// gives the analog of the modular inverse bignum_inv_sm2 but with both
// input and output in the Montgomery domain. Note that x does not need
// to be reduced modulo p_sm2, but the output always is. If the input
// is divisible (i.e. is 0 or p_sm2), then there can be no solution to
// the congruence x * z == 2^512 (mod p_sm2), and z = 0 is returned.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montinv_sm2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_montinv_sm2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montinv_sm2)
        .text
        .balign 32

// Size in bytes of a 64-bit word

#define N 8

// Pointer-offset pairs for temporaries on stack

#define f rsp+0
#define g rsp+(5*N)
#define u rsp+(10*N)
#define v rsp+(15*N)
#define tmp QWORD PTR [rsp+(20*N)]
#define tmp2 QWORD PTR [rsp+(21*N)]
#define i QWORD PTR [rsp+(22*N)]
#define d QWORD PTR [rsp+(23*N)]

#define mat rsp+(24*N)

// Backup for the input pointer

#define res QWORD PTR [rsp+(28*N)]

// Total size to reserve on the stack

#define NSPACE 30*N

// Syntactic variants to make x86_att version simpler to generate

#define F 0
#define G (5*N)
#define U (10*N)
#define V (15*N)
#define MAT (24*N)

#define ff QWORD PTR [rsp]
#define gg QWORD PTR [rsp+(5*N)]

// ---------------------------------------------------------------------------
// Core signed almost-Montgomery reduction macro from u[4..0] to u[3..0].
// ---------------------------------------------------------------------------

#define amontred(P)                                                     \
/* We only know the input is -2^316 < x < 2^316. To do traditional  */  \
/* unsigned Montgomery reduction, start by adding 2^61 * p_sm2.     */  \
        mov     r8, 0xe000000000000000;                                 \
        add     r8, [P];                                                \
        mov     r9, 0x1fffffffffffffff;                                 \
        adc     r9, [P+8];                                              \
        mov     r10, 0xffffffffe0000000;                                \
        adc     r10, [P+16];                                            \
        mov     r11, 0xffffffffffffffff;                                \
        adc     r11, [P+24];                                            \
        mov     r12, 0x1fffffffdfffffff;                                \
        adc     r12, [P+32];                                            \
/* Let [rcx;rbx] = 2^32 * d0 and [rdx;rax] = (2^32-1) * d0 */           \
        mov     rbx, r8;                                                \
        mov     rcx, r8;                                                \
        shr     rcx, 32;                                                \
        shl     rbx, 32;                                                \
        mov     eax, 0xffffffff;                                        \
        mul     r8;                                                     \
/* Now [r12;r11;r10;r9] := [r8;r11;r10;r9] - [rcx;rbx;rdx;rax] */       \
        sub     r9, rax;                                                \
        sbb     r10, rdx;                                               \
        sbb     r11, rbx;                                               \
        sbb     r8, rcx;                                                \
        add     r12, r8;                                                \
/* Now capture carry and subtract p_sm2 if set (almost-Montgomery) */   \
        sbb     rax, rax;                                               \
        mov     ebx, 0xffffffff;                                        \
        not     rbx;                                                    \
        and     rbx, rax;                                               \
        mov     rdx, rax;                                               \
        btr     rdx, 32;                                                \
        sub     r9, rax;                                                \
        mov     [P], r9;                                                \
        sbb     r10, rbx;                                               \
        mov     [P+8], r10;                                             \
        sbb     r11, rax;                                               \
        mov     [P+16], r11;                                            \
        sbb     r12, rdx;                                               \
        mov     [P+24], r12

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

S2N_BN_SYMBOL(bignum_montinv_sm2):
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

// Create constant [rdx;rcx;rbx;rax] = p_sm2 and copy it into the variable f
// including the 5th zero digit

        xor     ebp, ebp
        lea     rax, [rbp-1]
        mov     ebx, 0x00000000ffffffff
        not     rbx
        mov     rcx, rax
        mov     rdx, rax
        btr     rdx, 32

        mov     [rsp+F], rax
        mov     [rsp+F+8], rbx
        mov     [rsp+F+16], rcx
        mov     [rsp+F+24], rdx
        mov     [rsp+F+32], rbp

// Now reduce the input modulo p_sm2, first negating the constant to get
// [rdx;rcx;rbx;rax] = 2^256 - p_sm2, adding it to x and hence getting
// the comparison x < p_sm2 <=> (2^256 - p_sm2) + x < 2^256 and choosing
// g accordingly.

        mov     r8, [rsi]
        mov     r9, [rsi+8]
        mov     r10, [rsi+16]
        mov     r11, [rsi+24]

        mov     eax, 1
        not     rbx
        xor     ecx, ecx
        not     rdx

        add     rax, r8
        adc     rbx, r9
        adc     rcx, r10
        adc     rdx, r11

        cmovnc  rax, r8
        cmovnc  rbx, r9
        cmovnc  rcx, r10
        cmovnc  rdx, r11

        mov     [rsp+G], rax
        mov     [rsp+G+8], rbx
        mov     [rsp+G+16], rcx
        mov     [rsp+G+24], rdx
        xor     eax, eax
        mov     [rsp+G+32], rax

// Also maintain reduced < 2^256 vector [u,v] such that
// [f,g] == x * 2^{5*i-562} * [u,v] (mod p_sm2)
// starting with [p_sm2,x] == x * 2^{5*0-562} * [0,2^562] (mod p_sm2)
// The weird-looking 5*i modifications come in because we are doing
// 64-bit word-sized Montgomery reductions at each stage, which is
// 5 bits more than the 59-bit requirement to keep things stable.
// After the 10th and last iteration and sign adjustment, when
// f == 1 for in-scope cases, we have x * 2^{50-562} * u == 1, i.e.
// x * u == 2^512 as required.

        xor     eax, eax
        mov     [rsp+U], rax
        mov     [rsp+U+8], rax
        mov     [rsp+U+16], rax
        mov     [rsp+U+24], rax

        mov     rax, 0x000c000000100000
        mov     [rsp+V], rax
        mov     rax, 0x000bfffffff80000
        mov     [rsp+V+8], rax
        mov     rax, 0x00040000000c0000
        mov     [rsp+V+16], rax
        mov     rax, 0x0018000000040000
        mov     [rsp+V+24], rax

// Start of main loop. We jump into the middle so that the divstep
// portion is common to the special tenth iteration after a uniform
// first 9.

        mov     i, 10
        mov     d, 1
        jmp     Lbignum_montinv_sm2_midloop

Lbignum_montinv_sm2_loop:

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
        mov     rbp, [rsp+F+4*N]
        xor     rbp, r9
        and     rbp, r8
        neg     rbp
        mul     r8
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+G+3*N]
        xor     rax, r11
        mov     rdx, [rsp+G+4*N]
        xor     rdx, r11
        and     rdx, r10
        sub     rbp, rdx
        mul     r10
        add     rsi, rax
        adc     rbp, rdx
        shrd    rcx, rsi, 59
        mov     [rsp+F+2*N], rcx
        shrd    rsi, rbp, 59
        sar     rbp, 59

        mov     rax, [rsp+F+3*N]
        mov     [rsp+F+3*N], rsi

        mov     rsi, [rsp+F+4*N]
        mov     [rsp+F+4*N], rbp

        xor     rax, r13
        xor     rsi, r13
        and     rsi, r12
        neg     rsi
        mul     r12
        add     rbx, rax
        adc     rsi, rdx
        mov     rax, [rsp+G+3*N]
        xor     rax, r15
        mov     rdx, [rsp+G+4*N]
        xor     rdx, r15
        and     rdx, r14
        sub     rsi, rdx
        mul     r14
        add     rbx, rax
        adc     rsi, rdx
        shrd    rdi, rbx, 59
        mov     [rsp+G+2*N], rdi
        shrd    rbx, rsi, 59
        mov     [rsp+G+3*N], rbx
        sar     rsi, 59
        mov     [rsp+G+4*N], rsi

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

// Preload for last use of old u digit 3

        mov     rax, [rsp+U+3*N]
        mov     [rsp+U+3*N], rcx
        mov     [rsp+U+4*N], rdx

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
        mov     [rsp+V+3*N], rsi
        mov     [rsp+V+4*N], rdx

// Montgomery reduction of u

        amontred(u)

// Montgomery reduction of v

        amontred(v)

Lbignum_montinv_sm2_midloop:

        divstep59(d,ff,gg)
        mov     d, rsi

// Next iteration

        dec     i
        jnz     Lbignum_montinv_sm2_loop

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
// sign above, so then since [f,0] == x * 2^{-512} [u,v] (mod p_sm2)
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

// Store back and Montgomery reduce u

        mov     [rsp+U], r12
        mov     [rsp+U+N], r13
        mov     [rsp+U+2*N], r14
        mov     [rsp+U+3*N], r15
        mov     [rsp+U+4*N], r9

        amontred(u)

// Perform final strict reduction mod p_sm2 and copy to output

        mov     r8, [rsp+U]
        mov     r9, [rsp+U+N]
        mov     r10, [rsp+U+2*N]
        mov     r11, [rsp+U+3*N]

        mov     eax, 1
        mov     ebx, 0x00000000ffffffff
        xor     ecx, ecx
        xor     edx, edx
        bts     rdx, 32

        add     rax, r8
        adc     rbx, r9
        adc     rcx, r10
        adc     rdx, r11

        cmovnc  rax, r8
        cmovnc  rbx, r9
        cmovnc  rcx, r10
        cmovnc  rdx, r11

        mov     rdi, res
        mov     [rdi], rax
        mov     [rdi+N], rbx
        mov     [rdi+2*N], rcx
        mov     [rdi+3*N], rdx

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

S2N_BN_SIZE_DIRECTIVE(bignum_montinv_sm2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
