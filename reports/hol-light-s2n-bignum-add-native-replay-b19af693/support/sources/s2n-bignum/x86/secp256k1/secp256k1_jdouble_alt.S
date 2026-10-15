// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point doubling on SECG curve secp256k1 in Jacobian coordinates
//
//    extern void secp256k1_jdouble_alt(uint64_t p3[static 12],
//                                      const uint64_t p1[static 12]);
//
// Does p3 := 2 * p1 where all points are regarded as Jacobian triples.
// A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3).
// It is assumed that all coordinates of the input point are fully
// reduced mod p_256k1 and that the z coordinate is not zero.
//
// Standard x86-64 ABI: RDI = p3, RSI = p1
// Microsoft x64 ABI:   RCX = p3, RDX = p1
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(secp256k1_jdouble_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(secp256k1_jdouble_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(secp256k1_jdouble_alt)
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

#define x_2 rsp+(NUMSIZE*0)
#define y_2 rsp+(NUMSIZE*1)
#define d rsp+(NUMSIZE*2)
#define tmp rsp+(NUMSIZE*3)
#define x_4 rsp+(NUMSIZE*4)
#define y_4 rsp+(NUMSIZE*6)
#define dx2 rsp+(NUMSIZE*8)
#define xy2 rsp+(NUMSIZE*10)

#define NSPACE NUMSIZE*12

// Corresponds to bignum_mul_p256k1_alt except rsi -> rbx

#define mul_p256k1(P0,P1,P2)                    \
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
        adc     r11, 0x0;                       \
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
        mov     rbx, 0x1000003d1;               \
        mov     rax, r12;                       \
        mul     rbx;                            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        sbb     rcx, rcx;                       \
        mov     rax, r13;                       \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        sbb     rcx, rcx;                       \
        mov     rax, r14;                       \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     rcx, rcx;                       \
        mov     rax, r15;                       \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        xor     rcx, rcx;                       \
        add     r11, rax;                       \
        mov     r12, rdx;                       \
        adc     r12, rcx;                       \
        lea     rax, [r12+0x1];                 \
        mul     rbx;                            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, rcx;                       \
        adc     r11, rcx;                       \
        sbb     rax, rax;                       \
        not     rax;                            \
        and     rax, rbx;                       \
        sub     r8, rax;                        \
        sbb     r9, rcx;                        \
        sbb     r10, rcx;                       \
        sbb     r11, rcx;                       \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11

// Corresponds to bignum_sqr_p256k1_alt except for rsi -> rbx

#define sqr_p256k1(P0,P1)                       \
        mov     rax, [P1];                      \
        mul     rax;                            \
        mov     r8, rax;                        \
        mov     r9, rdx;                        \
        xor     r10, r10;                       \
        xor     r11, r11;                       \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x8];             \
        add     rax, rax;                       \
        adc     rdx, rdx;                       \
        adc     r11, 0x0;                       \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        adc     r11, 0x0;                       \
        xor     r12, r12;                       \
        mov     rax, [P1+0x8];                  \
        mul     rax;                            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, 0x0;                       \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x10];            \
        add     rax, rax;                       \
        adc     rdx, rdx;                       \
        adc     r12, 0x0;                       \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, 0x0;                       \
        xor     r13, r13;                       \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x18];            \
        add     rax, rax;                       \
        adc     rdx, rdx;                       \
        adc     r13, 0x0;                       \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        adc     r13, 0x0;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x10];            \
        add     rax, rax;                       \
        adc     rdx, rdx;                       \
        adc     r13, 0x0;                       \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        adc     r13, 0x0;                       \
        xor     r14, r14;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x18];            \
        add     rax, rax;                       \
        adc     rdx, rdx;                       \
        adc     r14, 0x0;                       \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        mov     rax, [P1+0x10];                 \
        mul     rax;                            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        xor     r15, r15;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P1+0x18];            \
        add     rax, rax;                       \
        adc     rdx, rdx;                       \
        adc     r15, 0x0;                       \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, 0x0;                       \
        mov     rax, [P1+0x18];                 \
        mul     rax;                            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        mov     rbx, 0x1000003d1;               \
        mov     rax, r12;                       \
        mul     rbx;                            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        sbb     rcx, rcx;                       \
        mov     rax, r13;                       \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        sbb     rcx, rcx;                       \
        mov     rax, r14;                       \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     rcx, rcx;                       \
        mov     rax, r15;                       \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        xor     rcx, rcx;                       \
        add     r11, rax;                       \
        mov     r12, rdx;                       \
        adc     r12, rcx;                       \
        lea     rax, [r12+0x1];                 \
        mul     rbx;                            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, rcx;                       \
        adc     r11, rcx;                       \
        sbb     rax, rax;                       \
        not     rax;                            \
        and     rax, rbx;                       \
        sub     r8, rax;                        \
        sbb     r9, rcx;                        \
        sbb     r10, rcx;                       \
        sbb     r11, rcx;                       \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11

// Rough versions producing 5-word results

#define roughmul_p256k1(P0,P1,P2)               \
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
        adc     r11, 0x0;                       \
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
        mov     rbx, 0x1000003d1;               \
        mov     rax, r12;                       \
        mul     rbx;                            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        sbb     rcx, rcx;                       \
        mov     rax, r13;                       \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        sbb     rcx, rcx;                       \
        mov     rax, r14;                       \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     rcx, rcx;                       \
        mov     rax, r15;                       \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        xor     rcx, rcx;                       \
        add     r11, rax;                       \
        mov     r12, rdx;                       \
        adc     r12, rcx;                       \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11;                 \
        mov     [P0+0x20],r12

#define roughsqr_p256k1(P0,P1)                  \
        mov     rax, [P1];                      \
        mul     rax;                            \
        mov     r8, rax;                        \
        mov     r9, rdx;                        \
        xor     r10, r10;                       \
        xor     r11, r11;                       \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x8];             \
        add     rax, rax;                       \
        adc     rdx, rdx;                       \
        adc     r11, 0x0;                       \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        adc     r11, 0x0;                       \
        xor     r12, r12;                       \
        mov     rax, [P1+0x8];                  \
        mul     rax;                            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, 0x0;                       \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x10];            \
        add     rax, rax;                       \
        adc     rdx, rdx;                       \
        adc     r12, 0x0;                       \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, 0x0;                       \
        xor     r13, r13;                       \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x18];            \
        add     rax, rax;                       \
        adc     rdx, rdx;                       \
        adc     r13, 0x0;                       \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        adc     r13, 0x0;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x10];            \
        add     rax, rax;                       \
        adc     rdx, rdx;                       \
        adc     r13, 0x0;                       \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        adc     r13, 0x0;                       \
        xor     r14, r14;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x18];            \
        add     rax, rax;                       \
        adc     rdx, rdx;                       \
        adc     r14, 0x0;                       \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        mov     rax, [P1+0x10];                 \
        mul     rax;                            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        xor     r15, r15;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P1+0x18];            \
        add     rax, rax;                       \
        adc     rdx, rdx;                       \
        adc     r15, 0x0;                       \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, 0x0;                       \
        mov     rax, [P1+0x18];                 \
        mul     rax;                            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        mov     rbx, 0x1000003d1;               \
        mov     rax, r12;                       \
        mul     rbx;                            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        sbb     rcx, rcx;                       \
        mov     rax, r13;                       \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        sbb     rcx, rcx;                       \
        mov     rax, r14;                       \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     rcx, rcx;                       \
        mov     rax, r15;                       \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        xor     rcx, rcx;                       \
        add     r11, rax;                       \
        mov     r12, rdx;                       \
        adc     r12, rcx;                       \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18],r11;                  \
        mov     [P0+0x20],r12

// Weak doubling operation, staying in 4 digits but not in general
// fully normalizing

#define weakdouble_p256k1(P0,P1)                \
        mov     r11,[P1+24];                    \
        mov     r10,[P1+16];                    \
        mov     rax, 0x1000003d1;               \
        xor     rdx, rdx;                       \
        shld    r11,r10,1;                      \
        cmovnc  rax, rdx;                       \
        mov     r9,[P1+8];                      \
        shld    r10,r9,1;                       \
        mov     r8,[P1];                        \
        shld    r9,r8,1;                        \
        shl     r8,1;                           \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, rdx;                       \
        adc     r11, rdx;                       \
        mov     [P0], r8;                       \
        mov     [P0+8], r9;                     \
        mov     [P0+16], r10;                   \
        mov     [P0+24], r11

// P0 = C * P1 - D * P2 with 5-word inputs P1 and P2
// Only used here with C = 12, D = 9, but could be used more generally.
// We actually compute C * P1 + D * (2^33 * p_256k1 - P2)

#define cmsub_p256k1(P0,C,P1,D,P2)              \
        mov     r9, 0xfffff85e00000000;         \
        sub     r9, [P2];                       \
        mov     r10, 0xfffffffffffffffd;        \
        sbb     r10, [P2+8];                    \
        mov     r11, 0xffffffffffffffff;        \
        sbb     r11, [P2+16];                   \
        mov     r12, 0xffffffffffffffff;        \
        sbb     r12, [P2+24];                   \
        mov     r13, 0x00000001ffffffff;        \
        sbb     r13, [P2+32];                   \
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
        imul    rcx, r13;                       \
        add     r12, rcx;                       \
        mov     rcx, C;                         \
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
        mov     rax, [P1+0x20];                 \
        mul     rcx;                            \
        add     r12, rax;                       \
        lea     rax,[r12+0x1];                  \
        mov     rcx,0x1000003d1;                \
        mul     rcx;                            \
        xor     ebx, ebx;                       \
        add     r8,rax;                         \
        adc     r9,rdx;                         \
        adc     r10,rbx;                        \
        adc     r11,rbx;                        \
        cmovb   rcx,rbx;                        \
        sub     r8,rcx;                         \
        mov     [P0],r8;                        \
        sbb     r9,rbx;                         \
        mov     [P0+8],r9;                      \
        sbb     r10,rbx;                        \
        mov     [P0+16],r10;                    \
        sbb     r11,rbx;                        \
        mov     [P0+24],r11;                    \

// P0 = 3 * P1 - 8 * P2 with 5-digit P1 and P2
// We actually compute 3 * P1 + (2^33 * p_256k1 - P2) << 3

#define cmsub38_p256k1(P0,P1,P2)                \
        mov     r8, 0xfffff85e00000000;         \
        sub     r8, [P2];                       \
        mov     r9, 0xfffffffffffffffd;         \
        sbb     r9, [P2+8];                     \
        mov     r10, 0xffffffffffffffff;        \
        sbb     r10, [P2+16];                   \
        mov     r11, 0xffffffffffffffff;        \
        sbb     r11, [P2+24];                   \
        mov     r12, 0x00000001ffffffff;        \
        sbb     r12, [P2+32];                   \
        shld    r12, r11, 3;                    \
        shld    r11, r10, 3;                    \
        shld    r10, r9, 3;                     \
        shld    r9, r8, 3;                      \
        shl     r8, 3;                          \
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
        mov     rax, [P1+0x20];                 \
        mul     rcx;                            \
        add     r12, rax;                       \
        lea     rax,[r12+0x1];                  \
        mov     rcx,0x1000003d1;                \
        mul     rcx;                            \
        xor     ebx, ebx;                       \
        add     r8,rax;                         \
        adc     r9,rdx;                         \
        adc     r10,rbx;                        \
        adc     r11,rbx;                        \
        cmovb   rcx,rbx;                        \
        sub     r8,rcx;                         \
        mov     [P0],r8;                        \
        sbb     r9,rbx;                         \
        mov     [P0+8],r9;                      \
        sbb     r10,rbx;                        \
        mov     [P0+16],r10;                    \
        sbb     r11,rbx;                        \
        mov     [P0+24],r11;                    \

// P0 = 4 * P1 - P2 with 5-digit P1, 4-digit P2 and result.
// This is done by direct subtraction of P2 since the method
// in bignum_cmul_p256k1 etc. for quotient estimation still
// works when the value to be reduced is negative, as
// long as it is  > -p_256k1, which is the case here.

#define cmsub41_p256k1(P0,P1,P2)                \
        mov     r12, [P1+32];                   \
        mov     r11, [P1+24];                   \
        shld    r12, r11, 2;                    \
        mov     r10, [P1+16];                   \
        shld    r11, r10, 2;                    \
        mov     r9, [P1+8];                     \
        shld    r10, r9, 2;                     \
        mov     r8, [P1];                       \
        shld    r9, r8, 2;                      \
        shl     r8, 2;                          \
        sub     r8, [P2];                       \
        sbb     r9, [P2+8];                     \
        sbb     r10, [P2+16];                   \
        sbb     r11, [P2+24];                   \
        sbb     r12, 0;                         \
        lea     rax,[r12+0x1];                  \
        mov     rcx,0x1000003d1;                \
        mul     rcx;                            \
        xor     rbx, rbx;                       \
        add     r8,rax;                         \
        adc     r9,rdx;                         \
        adc     r10,0x0;                        \
        adc     r11,0x0;                        \
        cmovb   rcx,rbx;                        \
        sub     r8,rcx;                         \
        mov     [P0],r8;                        \
        sbb     r9,rbx;                         \
        mov     [P0+8],r9;                      \
        sbb     r10,rbx;                        \
        mov     [P0+16],r10;                    \
        sbb     r11,rbx;                        \
        mov     [P0+24],r11;                    \

S2N_BN_SYMBOL(secp256k1_jdouble_alt):
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

// Main sequence of operations

        // y_2 = y^2

        sqr_p256k1(y_2,y_1)

        // x_2 = x^2

        sqr_p256k1(x_2,x_1)

        // tmp = 2 * y_1 (in 4 words but not fully normalized)

        weakdouble_p256k1(tmp,y_1)

        // xy2 = x * y^2 (5-digit partially reduced)
        // x_4 = x^4 (5-digit partially reduced)

        roughmul_p256k1(xy2,x_1,y_2)
        roughsqr_p256k1(x_4,x_2)

        // z_3 = 2 * y_1 * z_1

        mul_p256k1(z_3,z_1,tmp)

        // d = 12 * xy2 - 9 * x_4

        cmsub_p256k1(d,12,xy2,9,x_4)

        // y4 = y2^2 (5-digit partially reduced)

        roughsqr_p256k1(y_4,y_2)

        // dx2 = d * x_2 (5-digit partially reduced)

        roughmul_p256k1(dx2,x_2,d)

        // x_3 = 4 * xy2 - d

        cmsub41_p256k1(x_3,xy2,d)

        // y_3 = 3 * dx2 - 8 * y_4

        cmsub38_p256k1(y_3,dx2,y_4)

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

S2N_BN_SIZE_DIRECTIVE(secp256k1_jdouble_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
