// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point doubling on GM/T 0003-2012 curve SM2 in Montgomery-Jacobian coordinates
//
//    extern void sm2_montjdouble_alt(uint64_t p3[static 12],
//                                    const uint64_t p1[static 12]);
//
// Does p3 := 2 * p1 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_sm2.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
//
// Standard x86-64 ABI: RDI = p3, RSI = p1
// Microsoft x64 ABI:   RCX = p3, RDX = p1
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sm2_montjdouble_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sm2_montjdouble_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sm2_montjdouble_alt)
        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 32

// Pointer-offset pairs for inputs and outputs
// These assume rdi = p3, rsi = p1, which is true when the
// arguments come in initially and is not disturbed throughout.

#define x_1 rsi+0
#define y_1 rsi+NUMSIZE
#define z_1 rsi+(2*NUMSIZE)

#define x_3 rdi+0
#define y_3 rdi+NUMSIZE
#define z_3 rdi+(2*NUMSIZE)

// Pointer-offset pairs for temporaries, with some aliasing
// NSPACE is the total stack needed for these temporaries

#define z2 rsp+(NUMSIZE*0)
#define y4 rsp+(NUMSIZE*0)

#define y2 rsp+(NUMSIZE*1)

#define t1 rsp+(NUMSIZE*2)

#define t2 rsp+(NUMSIZE*3)
#define x2p rsp+(NUMSIZE*3)
#define dx2 rsp+(NUMSIZE*3)

#define xy2 rsp+(NUMSIZE*4)

#define x4p rsp+(NUMSIZE*5)
#define d rsp+(NUMSIZE*5)

#define NSPACE NUMSIZE*6

// Corresponds to bignum_montmul_sm2_alt except for registers

#define montmul_sm2(P0,P1,P2)                   \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2];                 \
        mov     r8, rax;                        \
        mov     r9, rdx;                        \
        xor     r10, r10;                       \
        xor     r11, r11;                       \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x8];             \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2];                 \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        adc     r11, r11;                       \
        xor     r12, r12;                       \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x10];            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, r12;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x8];             \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, 0x0;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2];                 \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, 0x0;                       \
        xor     r13, r13;                       \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x18];            \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        adc     r13, r13;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x10];            \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        adc     r13, 0x0;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x8];             \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        adc     r13, 0x0;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2];                 \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        adc     r13, 0x0;                       \
        xor     r14, r14;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x18];            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, r14;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x8];             \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        xor     r15, r15;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, r15;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, 0x0;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        mov     rax, r8;                        \
        shl     rax, 0x20;                      \
        mov     rcx, r8;                        \
        shr     rcx, 0x20;                      \
        mov     rdx, rax;                       \
        mov     rbx, rcx;                       \
        sub     rax, r8;                        \
        sbb     rcx, 0x0;                       \
        sub     r9, rax;                        \
        sbb     r10, rcx;                       \
        sbb     r11, rdx;                       \
        sbb     r8, rbx;                        \
        mov     rax, r9;                        \
        shl     rax, 0x20;                      \
        mov     rcx, r9;                        \
        shr     rcx, 0x20;                      \
        mov     rdx, rax;                       \
        mov     rbx, rcx;                       \
        sub     rax, r9;                        \
        sbb     rcx, 0x0;                       \
        sub     r10, rax;                       \
        sbb     r11, rcx;                       \
        sbb     r8, rdx;                        \
        sbb     r9, rbx;                        \
        mov     rax, r10;                       \
        shl     rax, 0x20;                      \
        mov     rcx, r10;                       \
        shr     rcx, 0x20;                      \
        mov     rdx, rax;                       \
        mov     rbx, rcx;                       \
        sub     rax, r10;                       \
        sbb     rcx, 0x0;                       \
        sub     r11, rax;                       \
        sbb     r8, rcx;                        \
        sbb     r9, rdx;                        \
        sbb     r10, rbx;                       \
        mov     rax, r11;                       \
        shl     rax, 0x20;                      \
        mov     rcx, r11;                       \
        shr     rcx, 0x20;                      \
        mov     rdx, rax;                       \
        mov     rbx, rcx;                       \
        sub     rax, r11;                       \
        sbb     rcx, 0x0;                       \
        sub     r8, rax;                        \
        sbb     r9, rcx;                        \
        sbb     r10, rdx;                       \
        sbb     r11, rbx;                       \
        xor     eax, eax;                       \
        add     r12, r8;                        \
        adc     r13, r9;                        \
        adc     r14, r10;                       \
        adc     r15, r11;                       \
        adc     rax, rax;                       \
        mov     ecx, 0x1;                       \
        mov     edx, 0xffffffff;                \
        xor     ebx, ebx;                       \
        add     rcx, r12;                       \
        lea     r11, [rdx+0x1];                 \
        adc     rdx, r13;                       \
        lea     r8, [rbx-0x1];                  \
        adc     rbx, r14;                       \
        adc     r11, r15;                       \
        adc     r8, rax;                        \
        cmovb   r12, rcx;                       \
        cmovb   r13, rdx;                       \
        cmovb   r14, rbx;                       \
        cmovb   r15, r11;                       \
        mov     [P0], r12;                      \
        mov     [P0+0x8], r13;                  \
        mov     [P0+0x10], r14;                 \
        mov     [P0+0x18], r15

// Corresponds to bignum_montsqr_sm2_alt except for registers

#define montsqr_sm2(P0,P1)                      \
        mov     rax, [P1];                      \
        mov     rbx, rax;                       \
        mul     rax;                            \
        mov     r8, rax;                        \
        mov     r15, rdx;                       \
        mov     rax, [P1+0x8];                  \
        mul     rbx;                            \
        mov     r9, rax;                        \
        mov     r10, rdx;                       \
        mov     rax, [P1+0x18];                 \
        mov     r13, rax;                       \
        mul     rbx;                            \
        mov     r11, rax;                       \
        mov     r12, rdx;                       \
        mov     rax, [P1+0x10];                 \
        mov     rbx, rax;                       \
        mul     r13;                            \
        mov     r13, rax;                       \
        mov     r14, rdx;                       \
        mov     rax, [P1];                      \
        mul     rbx;                            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     rcx, rcx;                       \
        mov     rax, [P1+0x8];                  \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        sbb     rcx, rcx;                       \
        mov     rbx, [P1+0x18];                 \
        mov     rax, [P1+0x8];                  \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        xor     ecx, ecx;                       \
        add     r9, r9;                         \
        adc     r10, r10;                       \
        adc     r11, r11;                       \
        adc     r12, r12;                       \
        adc     r13, r13;                       \
        adc     r14, r14;                       \
        adc     rcx, rcx;                       \
        mov     rax, [P1+0x8];                  \
        mul     rax;                            \
        add     r9, r15;                        \
        adc     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     r15, r15;                       \
        mov     rax, [P1+0x10];                 \
        mul     rax;                            \
        neg     r15;                            \
        adc     r12, rax;                       \
        adc     r13, rdx;                       \
        sbb     r15, r15;                       \
        mov     rax, [P1+0x18];                 \
        mul     rax;                            \
        neg     r15;                            \
        adc     r14, rax;                       \
        adc     rdx, rcx;                       \
        mov     r15, rdx;                       \
        mov     rax, r8;                        \
        shl     rax, 0x20;                      \
        mov     rcx, r8;                        \
        shr     rcx, 0x20;                      \
        mov     rdx, rax;                       \
        mov     rbx, rcx;                       \
        sub     rax, r8;                        \
        sbb     rcx, 0x0;                       \
        sub     r9, rax;                        \
        sbb     r10, rcx;                       \
        sbb     r11, rdx;                       \
        sbb     r8, rbx;                        \
        mov     rax, r9;                        \
        shl     rax, 0x20;                      \
        mov     rcx, r9;                        \
        shr     rcx, 0x20;                      \
        mov     rdx, rax;                       \
        mov     rbx, rcx;                       \
        sub     rax, r9;                        \
        sbb     rcx, 0x0;                       \
        sub     r10, rax;                       \
        sbb     r11, rcx;                       \
        sbb     r8, rdx;                        \
        sbb     r9, rbx;                        \
        mov     rax, r10;                       \
        shl     rax, 0x20;                      \
        mov     rcx, r10;                       \
        shr     rcx, 0x20;                      \
        mov     rdx, rax;                       \
        mov     rbx, rcx;                       \
        sub     rax, r10;                       \
        sbb     rcx, 0x0;                       \
        sub     r11, rax;                       \
        sbb     r8, rcx;                        \
        sbb     r9, rdx;                        \
        sbb     r10, rbx;                       \
        mov     rax, r11;                       \
        shl     rax, 0x20;                      \
        mov     rcx, r11;                       \
        shr     rcx, 0x20;                      \
        mov     rdx, rax;                       \
        mov     rbx, rcx;                       \
        sub     rax, r11;                       \
        sbb     rcx, 0x0;                       \
        sub     r8, rax;                        \
        sbb     r9, rcx;                        \
        sbb     r10, rdx;                       \
        sbb     r11, rbx;                       \
        xor     eax, eax;                       \
        add     r12, r8;                        \
        adc     r13, r9;                        \
        adc     r14, r10;                       \
        adc     r15, r11;                       \
        adc     rax, rax;                       \
        mov     ecx, 0x1;                       \
        mov     edx, 0xffffffff;                \
        xor     ebx, ebx;                       \
        add     rcx, r12;                       \
        lea     r11, [rdx+0x1];                 \
        adc     rdx, r13;                       \
        lea     r8, [rbx-0x1];                  \
        adc     rbx, r14;                       \
        adc     r11, r15;                       \
        adc     r8, rax;                        \
        cmovb   r12, rcx;                       \
        cmovb   r13, rdx;                       \
        cmovb   r14, rbx;                       \
        cmovb   r15, r11;                       \
        mov     [P0], r12;                      \
        mov     [P0+0x8], r13;                  \
        mov     [P0+0x10], r14;                 \
        mov     [P0+0x18], r15

// Corresponds exactly to bignum_sub_sm2

#define sub_sm2(P0,P1,P2)                       \
        mov     rax, [P1];                      \
        sub     rax, [P2];                      \
        mov     rcx, [P1+0x8];                  \
        sbb     rcx, [P2+0x8];                  \
        mov     r8, [P1+0x10];                  \
        sbb     r8, [P2+0x10];                  \
        mov     r9, [P1+0x18];                  \
        sbb     r9, [P2+0x18];                  \
        mov     r10, 0xffffffff00000000;        \
        sbb     r11, r11;                       \
        and     r10, r11;                       \
        mov     rdx, r11;                       \
        btr     rdx, 0x20;                      \
        add     rax, r11;                       \
        mov     [P0], rax;                      \
        adc     rcx, r10;                       \
        mov     [P0+0x8], rcx;                  \
        adc     r8, r11;                        \
        mov     [P0+0x10], r8;                  \
        adc     r9, rdx;                        \
        mov     [P0+0x18], r9

// Corresponds exactly to bignum_add_sm2

#define add_sm2(P0,P1,P2)                       \
        xor     r11, r11;                       \
        mov     rax, [P1];                      \
        add     rax, [P2];                      \
        mov     rcx, [P1+0x8];                  \
        adc     rcx, [P2+0x8];                  \
        mov     r8, [P1+0x10];                  \
        adc     r8, [P2+0x10];                  \
        mov     r9, [P1+0x18];                  \
        adc     r9, [P2+0x18];                  \
        adc     r11, r11;                       \
        sub     rax, 0xffffffffffffffff;        \
        mov     r10, 0xffffffff00000000;        \
        sbb     rcx, r10;                       \
        sbb     r8, 0xffffffffffffffff;         \
        mov     rdx, 0xfffffffeffffffff;        \
        sbb     r9, rdx;                        \
        sbb     r11, 0x0;                       \
        and     r10, r11;                       \
        and     rdx, r11;                       \
        add     rax, r11;                       \
        mov     [P0], rax;                      \
        adc     rcx, r10;                       \
        mov     [P0+0x8], rcx;                  \
        adc     r8, r11;                        \
        mov     [P0+0x10], r8;                  \
        adc     r9, rdx;                        \
        mov     [P0+0x18], r9

// A weak version of add that only guarantees sum in 4 digits

#define weakadd_sm2(P0,P1,P2)                   \
        mov     rax, [P1];                      \
        add     rax, [P2];                      \
        mov     rcx, [P1+0x8];                  \
        adc     rcx, [P2+0x8];                  \
        mov     r8, [P1+0x10];                  \
        adc     r8, [P2+0x10];                  \
        mov     r9, [P1+0x18];                  \
        adc     r9, [P2+0x18];                  \
        mov     r10, 0xffffffff00000000;        \
        sbb     r11, r11;                       \
        and     r10, r11;                       \
        mov     rdx, r11;                       \
        btr     rdx, 0x20;                      \
        sub     rax, r11;                       \
        mov     [P0], rax;                      \
        sbb     rcx, r10;                       \
        mov     [P0+0x8], rcx;                  \
        sbb     r8, r11;                        \
        mov     [P0+0x10], r8;                  \
        sbb     r9, rdx;                        \
        mov     [P0+0x18], r9

// P0 = C * P1 - D * P2  computed as d * (p_sm2 - P2) + c * P1
// Quotient estimation is done just as q = h + 1 as in bignum_triple_sm2
// This also applies to the other functions following.

#define cmsub_sm2(P0,C,P1,D,P2)                \
        /* First [r12;r11;r10;r9] = p_sm2 - P2 */ \
        mov     r9,0xffffffffffffffff;          \
        mov     r11, r9;                        \
        sub     r9,[P2];                        \
        mov     r10,0xffffffff00000000;         \
        sbb     r10,[P2+0x8];                   \
        sbb     r11,[P2+0x10];                  \
        mov     r12,0xfffffffeffffffff;         \
        sbb     r12,[P2+0x18];                  \
        /* [r12;r11;r10;r9;r8] = D * (p_sm2 - P2) */  \
        mov     rcx, D;                         \
        mov     rax, r9;                        \
        mul     rcx;                            \
        mov     r8, rax;                        \
        mov     r9, rdx;                        \
        mov     rax, r10;                       \
        xor     r10d, r10d;                     \
        mul     rcx;                            \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        mov     rax, r11;                       \
        xor     r11d, r11d;                     \
        mul     rcx;                            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        mov     rax, r12;                       \
        xor     r12d, r12d;                     \
        mul     rcx;                            \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        /* [rdx;r11;r10;r9;r8] = 2^256 + C * P1 + D * (p_sm2 - P2) */ \
        mov     ecx, C;                         \
        mov     rax, [P1];                      \
        mul     rcx;                            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        sbb     rbx, rbx;                       \
        mov     rax, [P1+0x8];                  \
        mul     rcx;                            \
        sub     rdx, rbx;                       \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        sbb     rbx, rbx;                       \
        mov     rax, [P1+0x10];                 \
        mul     rcx;                            \
        sub     rdx, rbx;                       \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     rbx, rbx;                       \
        mov     rax, [P1+0x18];                 \
        mul     rcx;                            \
        sub     rdx, rbx;                       \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        lea     rdx, [r12+1];                   \
        /* Now the tail for modular reduction from tripling */ \
        mov     rax, rdx;                       \
        shl     rax, 0x20;                      \
        mov     rcx, rax;                       \
        sub     rax, rdx;                       \
        add     r8, rdx;                        \
        adc     r9, rax;                        \
        adc     r10, 0x0;                       \
        adc     r11, rcx;                       \
        sbb     rdx, rdx;                       \
        not     rdx;                            \
        mov     rax, 0xffffffff00000000;        \
        and     rax, rdx;                       \
        mov     rcx, rdx;                       \
        btr     rcx, 0x20;                      \
        add     r8, rdx;                        \
        mov     [P0], r8;                       \
        adc     r9, rax;                        \
        mov     [P0+0x8], r9;                   \
        adc     r10, rdx;                       \
        mov     [P0+0x10], r10;                 \
        adc     r11, rcx;                       \
        mov     [P0+0x18], r11

// P0 = 3 * P1 - 8 * P2, computed as (p_sm2 - P2) << 3 + 3 * P1

#define cmsub38_sm2(P0,P1,P2)                  \
        /* First [r11;r10;r9;r8] = p_sm2 - P2 */ \
        mov     r8,0xffffffffffffffff;          \
        mov     r10, r8;                        \
        sub     r8,[P2];                        \
        mov     r9,0xffffffff00000000;          \
        sbb     r9,[P2+0x8];                    \
        sbb     r10,[P2+0x10];                  \
        mov     r11,0xfffffffeffffffff;         \
        sbb     r11,[P2+0x18];                  \
        /* [r12;r11;r10;r9;r8] = (p_sm2 - P2) << 3 */  \
        mov     r12, r11;                       \
        shld    r11, r10, 3;                    \
        shld    r10, r9, 3;                     \
        shld    r9, r8, 3;                      \
        shl     r8, 3;                          \
        shr     r12, 61;                        \
        /* [rdx;r11;r10;r9;r8] = 2^256 + 3 * P1 + 8 * (p_sm2 - P2) */ \
        mov     ecx, 3;                         \
        mov     rax, [P1];                      \
        mul     rcx;                            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        sbb     rbx, rbx;                       \
        mov     rax, [P1+0x8];                  \
        mul     rcx;                            \
        sub     rdx, rbx;                       \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        sbb     rbx, rbx;                       \
        mov     rax, [P1+0x10];                 \
        mul     rcx;                            \
        sub     rdx, rbx;                       \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     rbx, rbx;                       \
        mov     rax, [P1+0x18];                 \
        mul     rcx;                            \
        sub     rdx, rbx;                       \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        lea     rdx, [r12+1];                   \
        /* Now the tail for modular reduction from tripling */ \
        mov     rax, rdx;                       \
        shl     rax, 0x20;                      \
        mov     rcx, rax;                       \
        sub     rax, rdx;                       \
        add     r8, rdx;                        \
        adc     r9, rax;                        \
        adc     r10, 0x0;                       \
        adc     r11, rcx;                       \
        sbb     rdx, rdx;                       \
        not     rdx;                            \
        mov     rax, 0xffffffff00000000;        \
        and     rax, rdx;                       \
        mov     rcx, rdx;                       \
        btr     rcx, 0x20;                      \
        add     r8, rdx;                        \
        mov     [P0], r8;                       \
        adc     r9, rax;                        \
        mov     [P0+0x8], r9;                   \
        adc     r10, rdx;                       \
        mov     [P0+0x10], r10;                 \
        adc     r11, rcx;                       \
        mov     [P0+0x18], r11

// P0 = 4 * P1 - P2, by direct subtraction of P2,
// since the quotient estimate still works safely
// for initial value > -p_sm2

#define cmsub41_sm2(P0,P1,P2)                  \
        mov     r11,[P1+0x18];                  \
        mov     rdx, r11;                       \
        mov     r10,[P1+0x10];                  \
        shld    r11, r10, 2;                    \
        mov     r9,[P1+0x8];                    \
        shld    r10, r9, 2;                     \
        mov     r8,[P1];                        \
        shld    r9, r8, 2;                      \
        shl     r8, 2;                          \
        shr     rdx, 62;                        \
        add     rdx, 1;                         \
        sub     r8, [P2];                       \
        sbb     r9, [P2+0x8];                   \
        sbb     r10, [P2+0x10];                 \
        sbb     r11, [P2+0x18];                 \
        sbb     rdx, 0;                         \
        /* Now the tail for modular reduction from tripling */ \
        mov     rax, rdx;                       \
        shl     rax, 0x20;                      \
        mov     rcx, rax;                       \
        sub     rax, rdx;                       \
        add     r8, rdx;                        \
        adc     r9, rax;                        \
        adc     r10, 0x0;                       \
        adc     r11, rcx;                       \
        sbb     rdx, rdx;                       \
        not     rdx;                            \
        mov     rax, 0xffffffff00000000;        \
        and     rax, rdx;                       \
        mov     rcx, rdx;                       \
        btr     rcx, 0x20;                      \
        add     r8, rdx;                        \
        mov     [P0], r8;                       \
        adc     r9, rax;                        \
        mov     [P0+0x8], r9;                   \
        adc     r10, rdx;                       \
        mov     [P0+0x10], r10;                 \
        adc     r11, rcx;                       \
        mov     [P0+0x18], r11

S2N_BN_SYMBOL(sm2_montjdouble_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Save registers and make room on stack for temporary variables

        CFI_PUSH(rbx)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

        CFI_DEC_RSP(NSPACE)

// Main code, just a sequence of basic field operations

// z2 = z^2
// y2 = y^2

        montsqr_sm2(z2,z_1)
        montsqr_sm2(y2,y_1)

// x2p = x^2 - z^4 = (x + z^2) * (x - z^2)

        sub_sm2(t2,x_1,z2)
        weakadd_sm2(t1,x_1,z2)
        montmul_sm2(x2p,t1,t2)

// t1 = y + z
// xy2 = x * y^2
// x4p = x2p^2

        add_sm2(t1,y_1,z_1)
        montmul_sm2(xy2,x_1,y2)
        montsqr_sm2(x4p,x2p)

// t1 = (y + z)^2

        montsqr_sm2(t1,t1)

// d = 12 * xy2 - 9 * x4p
// t1 = y^2 + 2 * y * z

        cmsub_sm2(d,12,xy2,9,x4p)
        sub_sm2(t1,t1,z2)

// y4 = y^4

        montsqr_sm2(y4,y2)

// dx2 = d * x2p

        montmul_sm2(dx2,d,x2p)

// z_3' = 2 * y * z

        sub_sm2(z_3,t1,y2)

// x' = 4 * xy2 - d

        cmsub41_sm2(x_3,xy2,d)

// y' = 3 * dx2 - 8 * y4

        cmsub38_sm2(y_3,dx2,y4)

// Restore stack and registers

        CFI_INC_RSP(NSPACE)
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbx)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(sm2_montjdouble_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
