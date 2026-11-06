// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point doubling on NIST curve P-521 in Jacobian coordinates
//
//    extern void p521_jdouble_alt(uint64_t p3[static 27],
//                                 const uint64_t p1[static 27]);
//
// Does p3 := 2 * p1 where all points are regarded as Jacobian triples.
// A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3).
// It is assumed that all coordinates of the input point are fully
// reduced mod p_521 and that the z coordinate is not zero.
//
// Standard x86-64 ABI: RDI = p3, RSI = p1
// Microsoft x64 ABI:   RCX = p3, RDX = p1
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p521_jdouble_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(p521_jdouble_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p521_jdouble_alt)
        .text

// Size of individual field elements

#define NUMSIZE 72

// Stable homes for input arguments during main code sequence
// This is actually where they come in anyway and they stay there.

#define input_z rdi
#define input_x rsi

// Pointer-offset pairs for inputs and outputs

#define x_1 input_x+0
#define y_1 input_x+NUMSIZE
#define z_1 input_x+(2*NUMSIZE)

#define x_3 input_z+0
#define y_3 input_z+NUMSIZE
#define z_3 input_z+(2*NUMSIZE)

// Pointer-offset pairs for temporaries, with some aliasing
// The tmp field is internal storage for field mul and sqr.
// NSPACE is the total stack needed for these temporaries

#define z2 rsp+(NUMSIZE*0)
#define y2 rsp+(NUMSIZE*1)
#define x2p rsp+(NUMSIZE*2)
#define xy2 rsp+(NUMSIZE*3)

#define y4 rsp+(NUMSIZE*4)
#define t2 rsp+(NUMSIZE*4)

#define dx2 rsp+(NUMSIZE*5)
#define t1 rsp+(NUMSIZE*5)

#define d rsp+(NUMSIZE*6)
#define x4p rsp+(NUMSIZE*6)

#define tmp rsp+(NUMSIZE*7)

#define NSPACE 576

// Corresponds to bignum_mul_p521_alt except temp storage location

#define mul_p521(P0,P1,P2)                      \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2];                 \
        mov     [rsp+504], rax;                 \
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
        mov     [rsp+512], r9;                  \
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
        mov     [rsp+520], r10;                 \
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
        mov     [rsp+528], r11;                 \
        xor     r14, r14;                       \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x20];            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, r14;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x18];            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
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
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P2];                 \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        mov     [rsp+536], r12;                 \
        xor     r15, r15;                       \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x28];            \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, r15;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x20];            \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, 0x0;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, 0x0;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, 0x0;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P2+0x8];             \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, 0x0;                       \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P2];                 \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, 0x0;                       \
        mov     [rsp+544], r13;                 \
        xor     r8, r8;                         \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x30];            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, r8;                         \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x28];            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, 0x0;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x20];            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, 0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, 0x0;                        \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, 0x0;                        \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P2+0x8];             \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, 0x0;                        \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P2];                 \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, 0x0;                        \
        mov     [rsp+552], r14;                 \
        xor     r9, r9;                         \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x38];            \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        adc     r9, r9;                         \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x30];            \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        adc     r9, 0x0;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x28];            \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        adc     r9, 0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x20];            \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        adc     r9, 0x0;                        \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        adc     r9, 0x0;                        \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        adc     r9, 0x0;                        \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P2+0x8];             \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        adc     r9, 0x0;                        \
        mov     rax, [P1+0x38];                 \
        mul     QWORD PTR [P2];                 \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        adc     r9, 0x0;                        \
        mov     [rsp+560], r15;                 \
        xor     r10, r10;                       \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x40];            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, r10;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x38];            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, 0x0;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x30];            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, 0x0;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x28];            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, 0x0;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P2+0x20];            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, 0x0;                       \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, 0x0;                       \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, 0x0;                       \
        mov     rax, [P1+0x38];                 \
        mul     QWORD PTR [P2+0x8];             \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, 0x0;                       \
        mov     rax, [P1+0x40];                 \
        mul     QWORD PTR [P2];                 \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, 0x0;                       \
        mov     [rsp+568], r8;                  \
        xor     r11, r11;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x40];            \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        adc     r11, r11;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x38];            \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        adc     r11, 0x0;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x30];            \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        adc     r11, 0x0;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P2+0x28];            \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        adc     r11, 0x0;                       \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P2+0x20];            \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        adc     r11, 0x0;                       \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        adc     r11, 0x0;                       \
        mov     rax, [P1+0x38];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        adc     r11, 0x0;                       \
        mov     rax, [P1+0x40];                 \
        mul     QWORD PTR [P2+0x8];             \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        adc     r11, 0x0;                       \
        xor     r12, r12;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x40];            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, r12;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x38];            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, 0x0;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P2+0x30];            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, 0x0;                       \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P2+0x28];            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, 0x0;                       \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P2+0x20];            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, 0x0;                       \
        mov     rax, [P1+0x38];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, 0x0;                       \
        mov     rax, [P1+0x40];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, 0x0;                       \
        xor     r13, r13;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x40];            \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        adc     r13, r13;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P2+0x38];            \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        adc     r13, 0x0;                       \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P2+0x30];            \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        adc     r13, 0x0;                       \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P2+0x28];            \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        adc     r13, 0x0;                       \
        mov     rax, [P1+0x38];                 \
        mul     QWORD PTR [P2+0x20];            \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        adc     r13, 0x0;                       \
        mov     rax, [P1+0x40];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        adc     r13, 0x0;                       \
        xor     r14, r14;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P2+0x40];            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, r14;                       \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P2+0x38];            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P2+0x30];            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        mov     rax, [P1+0x38];                 \
        mul     QWORD PTR [P2+0x28];            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        mov     rax, [P1+0x40];                 \
        mul     QWORD PTR [P2+0x20];            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        xor     r15, r15;                       \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P2+0x40];            \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, r15;                       \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P2+0x38];            \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, 0x0;                       \
        mov     rax, [P1+0x38];                 \
        mul     QWORD PTR [P2+0x30];            \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, 0x0;                       \
        mov     rax, [P1+0x40];                 \
        mul     QWORD PTR [P2+0x28];            \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, 0x0;                       \
        xor     r8, r8;                         \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P2+0x40];            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, r8;                         \
        mov     rax, [P1+0x38];                 \
        mul     QWORD PTR [P2+0x38];            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, 0x0;                        \
        mov     rax, [P1+0x40];                 \
        mul     QWORD PTR [P2+0x30];            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, 0x0;                        \
        mov     rax, [P1+0x38];                 \
        mul     QWORD PTR [P2+0x40];            \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        mov     rax, [P1+0x40];                 \
        mul     QWORD PTR [P2+0x38];            \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        mov     rax, [P1+0x40];                 \
        imul    rax, [P2+0x40];                 \
        add     rax, r8;                        \
        mov     r8, [rsp+568];                  \
        mov     rdx, r8;                        \
        and     rdx, 0x1ff;                     \
        shrd    r8, r9, 0x9;                    \
        shrd    r9, r10, 0x9;                   \
        shrd    r10, r11, 0x9;                  \
        shrd    r11, r12, 0x9;                  \
        shrd    r12, r13, 0x9;                  \
        shrd    r13, r14, 0x9;                  \
        shrd    r14, r15, 0x9;                  \
        shrd    r15, rax, 0x9;                  \
        shr     rax, 0x9;                       \
        add     rdx, rax;                       \
        stc;                                    \
        adc     r8, [rsp+504];                  \
        adc     r9, [rsp+512];                  \
        adc     r10, [rsp+520];                 \
        adc     r11, [rsp+528];                 \
        adc     r12, [rsp+536];                 \
        adc     r13, [rsp+544];                 \
        adc     r14, [rsp+552];                 \
        adc     r15, [rsp+560];                 \
        adc     rdx, 0xfffffffffffffe00;        \
        cmc;                                    \
        sbb     r8, 0x0;                        \
        mov     [P0], r8;                       \
        sbb     r9, 0x0;                        \
        mov     [P0+0x8], r9;                   \
        sbb     r10, 0x0;                       \
        mov     [P0+0x10], r10;                 \
        sbb     r11, 0x0;                       \
        mov     [P0+0x18], r11;                 \
        sbb     r12, 0x0;                       \
        mov     [P0+0x20], r12;                 \
        sbb     r13, 0x0;                       \
        mov     [P0+0x28], r13;                 \
        sbb     r14, 0x0;                       \
        mov     [P0+0x30], r14;                 \
        sbb     r15, 0x0;                       \
        mov     [P0+0x38], r15;                 \
        sbb     rdx, 0x0;                       \
        and     rdx, 0x1ff;                     \
        mov     [P0+0x40], rdx

// Corresponds to bignum_sqr_p521_alt except temp storage location

#define sqr_p521(P0,P1)                         \
        mov     rax, [P1];                      \
        mul     rax;                            \
        mov     [rsp+504], rax;                 \
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
        mov     [rsp+512], r9;                  \
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
        mov     [rsp+520], r10;                 \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x18];            \
        xor     r13, r13;                       \
        mov     rbx, rax;                       \
        mov     rcx, rdx;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x10];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r13, 0x0;                       \
        add     rbx, rbx;                       \
        adc     rcx, rcx;                       \
        adc     r13, r13;                       \
        add     r11, rbx;                       \
        adc     r12, rcx;                       \
        adc     r13, 0x0;                       \
        mov     [rsp+528], r11;                 \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x20];            \
        xor     r14, r14;                       \
        mov     rbx, rax;                       \
        mov     rcx, rdx;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x18];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r14, 0x0;                       \
        add     rbx, rbx;                       \
        adc     rcx, rcx;                       \
        adc     r14, r14;                       \
        add     r12, rbx;                       \
        adc     r13, rcx;                       \
        adc     r14, 0x0;                       \
        mov     rax, [P1+0x10];                 \
        mul     rax;                            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        mov     [rsp+536], r12;                 \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x28];            \
        xor     r15, r15;                       \
        mov     rbx, rax;                       \
        mov     rcx, rdx;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x20];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r15, 0x0;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P1+0x18];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r15, 0x0;                       \
        add     rbx, rbx;                       \
        adc     rcx, rcx;                       \
        adc     r15, r15;                       \
        add     r13, rbx;                       \
        adc     r14, rcx;                       \
        adc     r15, 0x0;                       \
        mov     [rsp+544], r13;                 \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x30];            \
        xor     r8, r8;                         \
        mov     rbx, rax;                       \
        mov     rcx, rdx;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x28];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r8, 0x0;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P1+0x20];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r8, 0x0;                        \
        add     rbx, rbx;                       \
        adc     rcx, rcx;                       \
        adc     r8, r8;                         \
        add     r14, rbx;                       \
        adc     r15, rcx;                       \
        adc     r8, 0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     rax;                            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, 0x0;                        \
        mov     [rsp+552], r14;                 \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x38];            \
        xor     r9, r9;                         \
        mov     rbx, rax;                       \
        mov     rcx, rdx;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x30];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r9, 0x0;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P1+0x28];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r9, 0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P1+0x20];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r9, 0x0;                        \
        add     rbx, rbx;                       \
        adc     rcx, rcx;                       \
        adc     r9, r9;                         \
        add     r15, rbx;                       \
        adc     r8, rcx;                        \
        adc     r9, 0x0;                        \
        mov     [rsp+560], r15;                 \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x40];            \
        xor     r10, r10;                       \
        mov     rbx, rax;                       \
        mov     rcx, rdx;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x38];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r10, 0x0;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P1+0x30];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r10, 0x0;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P1+0x28];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r10, 0x0;                       \
        add     rbx, rbx;                       \
        adc     rcx, rcx;                       \
        adc     r10, r10;                       \
        add     r8, rbx;                        \
        adc     r9, rcx;                        \
        adc     r10, 0x0;                       \
        mov     rax, [P1+0x20];                 \
        mul     rax;                            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, 0x0;                       \
        mov     [rsp+568], r8;                  \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x40];            \
        xor     r11, r11;                       \
        mov     rbx, rax;                       \
        mov     rcx, rdx;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P1+0x38];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r11, 0x0;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P1+0x30];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r11, 0x0;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P1+0x28];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r11, 0x0;                       \
        add     rbx, rbx;                       \
        adc     rcx, rcx;                       \
        adc     r11, r11;                       \
        add     r9, rbx;                        \
        adc     r10, rcx;                       \
        adc     r11, 0x0;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P1+0x40];            \
        xor     r12, r12;                       \
        mov     rbx, rax;                       \
        mov     rcx, rdx;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P1+0x38];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r12, 0x0;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P1+0x30];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r12, 0x0;                       \
        add     rbx, rbx;                       \
        adc     rcx, rcx;                       \
        adc     r12, r12;                       \
        add     r10, rbx;                       \
        adc     r11, rcx;                       \
        adc     r12, 0x0;                       \
        mov     rax, [P1+0x28];                 \
        mul     rax;                            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, 0x0;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P1+0x40];            \
        xor     r13, r13;                       \
        mov     rbx, rax;                       \
        mov     rcx, rdx;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P1+0x38];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r13, 0x0;                       \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P1+0x30];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r13, 0x0;                       \
        add     rbx, rbx;                       \
        adc     rcx, rcx;                       \
        adc     r13, r13;                       \
        add     r11, rbx;                       \
        adc     r12, rcx;                       \
        adc     r13, 0x0;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P1+0x40];            \
        xor     r14, r14;                       \
        mov     rbx, rax;                       \
        mov     rcx, rdx;                       \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P1+0x38];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r14, 0x0;                       \
        add     rbx, rbx;                       \
        adc     rcx, rcx;                       \
        adc     r14, r14;                       \
        add     r12, rbx;                       \
        adc     r13, rcx;                       \
        adc     r14, 0x0;                       \
        mov     rax, [P1+0x30];                 \
        mul     rax;                            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P1+0x40];            \
        xor     r15, r15;                       \
        mov     rbx, rax;                       \
        mov     rcx, rdx;                       \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P1+0x38];            \
        add     rbx, rax;                       \
        adc     rcx, rdx;                       \
        adc     r15, 0x0;                       \
        add     rbx, rbx;                       \
        adc     rcx, rcx;                       \
        adc     r15, r15;                       \
        add     r13, rbx;                       \
        adc     r14, rcx;                       \
        adc     r15, 0x0;                       \
        xor     r8, r8;                         \
        mov     rax, [P1+0x38];                 \
        mul     rax;                            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, 0x0;                        \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P1+0x40];            \
        add     rax, rax;                       \
        adc     rdx, rdx;                       \
        adc     r8, 0x0;                        \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, 0x0;                        \
        mov     rax, [P1+0x38];                 \
        mul     QWORD PTR [P1+0x40];            \
        add     rax, rax;                       \
        adc     rdx, rdx;                       \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        mov     rax, [P1+0x40];                 \
        imul    rax, rax;                       \
        add     rax, r8;                        \
        mov     r8, [rsp+568];                  \
        mov     rdx, r8;                        \
        and     rdx, 0x1ff;                     \
        shrd    r8, r9, 0x9;                    \
        shrd    r9, r10, 0x9;                   \
        shrd    r10, r11, 0x9;                  \
        shrd    r11, r12, 0x9;                  \
        shrd    r12, r13, 0x9;                  \
        shrd    r13, r14, 0x9;                  \
        shrd    r14, r15, 0x9;                  \
        shrd    r15, rax, 0x9;                  \
        shr     rax, 0x9;                       \
        add     rdx, rax;                       \
        stc;                                    \
        adc     r8, [rsp+504];                  \
        adc     r9, [rsp+512];                  \
        adc     r10, [rsp+520];                 \
        adc     r11, [rsp+528];                 \
        adc     r12, [rsp+536];                 \
        adc     r13, [rsp+544];                 \
        adc     r14, [rsp+552];                 \
        adc     r15, [rsp+560];                 \
        adc     rdx, 0xfffffffffffffe00;        \
        cmc;                                    \
        sbb     r8, 0x0;                        \
        mov     [P0], r8;                       \
        sbb     r9, 0x0;                        \
        mov     [P0+0x8], r9;                   \
        sbb     r10, 0x0;                       \
        mov     [P0+0x10], r10;                 \
        sbb     r11, 0x0;                       \
        mov     [P0+0x18], r11;                 \
        sbb     r12, 0x0;                       \
        mov     [P0+0x20], r12;                 \
        sbb     r13, 0x0;                       \
        mov     [P0+0x28], r13;                 \
        sbb     r14, 0x0;                       \
        mov     [P0+0x30], r14;                 \
        sbb     r15, 0x0;                       \
        mov     [P0+0x38], r15;                 \
        sbb     rdx, 0x0;                       \
        and     rdx, 0x1ff;                     \
        mov     [P0+0x40], rdx;                 \

// Corresponds exactly to bignum_add_p521

#define add_p521(P0,P1,P2)                      \
        stc;                                    \
        mov     rax,[P1];                       \
        adc     rax,[P2];                       \
        mov     rbx,[P1+0x8];                   \
        adc     rbx,[P2+0x8];                   \
        mov     r8,[P1+0x10];                   \
        adc     r8,[P2+0x10];                   \
        mov     r9,[P1+0x18];                   \
        adc     r9,[P2+0x18];                   \
        mov     r10,[P1+0x20];                  \
        adc     r10,[P2+0x20];                  \
        mov     r11,[P1+0x28];                  \
        adc     r11,[P2+0x28];                  \
        mov     r12,[P1+0x30];                  \
        adc     r12,[P2+0x30];                  \
        mov     r13,[P1+0x38];                  \
        adc     r13,[P2+0x38];                  \
        mov     r14,[P1+0x40];                  \
        adc     r14,[P2+0x40];                  \
        mov     rdx,0x200;                      \
        and     rdx,r14;                        \
        cmp     rdx,0x200;                      \
        sbb     rax,0x0;                        \
        mov     [P0],rax;                       \
        sbb     rbx,0x0;                        \
        mov     [P0+0x8],rbx;                   \
        sbb     r8,0x0;                         \
        mov     [P0+0x10],r8;                   \
        sbb     r9,0x0;                         \
        mov     [P0+0x18],r9;                   \
        sbb     r10,0x0;                        \
        mov     [P0+0x20],r10;                  \
        sbb     r11,0x0;                        \
        mov     [P0+0x28],r11;                  \
        sbb     r12,0x0;                        \
        mov     [P0+0x30],r12;                  \
        sbb     r13,0x0;                        \
        mov     [P0+0x38],r13;                  \
        sbb     r14,rdx;                        \
        mov     [P0+0x40],r14

// Corresponds exactly to bignum_sub_p521

#define sub_p521(P0,P1,P2)                      \
        mov     rax,[P1];                       \
        sub     rax,[P2];                       \
        mov     rdx,[P1+0x8];                   \
        sbb     rdx,[P2+0x8];                   \
        mov     r8,[P1+0x10];                   \
        sbb     r8,[P2+0x10];                   \
        mov     r9,[P1+0x18];                   \
        sbb     r9,[P2+0x18];                   \
        mov     r10,[P1+0x20];                  \
        sbb     r10,[P2+0x20];                  \
        mov     r11,[P1+0x28];                  \
        sbb     r11,[P2+0x28];                  \
        mov     r12,[P1+0x30];                  \
        sbb     r12,[P2+0x30];                  \
        mov     r13,[P1+0x38];                  \
        sbb     r13,[P2+0x38];                  \
        mov     r14,[P1+0x40];                  \
        sbb     r14,[P2+0x40];                  \
        sbb     rax,0x0;                        \
        mov     [P0],rax;                       \
        sbb     rdx,0x0;                        \
        mov     [P0+0x8],rdx;                   \
        sbb     r8,0x0;                         \
        mov     [P0+0x10],r8;                   \
        sbb     r9,0x0;                         \
        mov     [P0+0x18],r9;                   \
        sbb     r10,0x0;                        \
        mov     [P0+0x20],r10;                  \
        sbb     r11,0x0;                        \
        mov     [P0+0x28],r11;                  \
        sbb     r12,0x0;                        \
        mov     [P0+0x30],r12;                  \
        sbb     r13,0x0;                        \
        mov     [P0+0x38],r13;                  \
        sbb     r14,0x0;                        \
        and     r14,0x1ff;                      \
        mov     [P0+0x40],r14

// Weak multiplication not fully reducing

#define weakmul_p521(P0,P1,P2)                  \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2];                 \
        mov     [rsp+504], rax;                 \
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
        mov     [rsp+512], r9;                  \
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
        mov     [rsp+520], r10;                 \
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
        mov     [rsp+528], r11;                 \
        xor     r14, r14;                       \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x20];            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, r14;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x18];            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
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
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P2];                 \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        mov     [rsp+536], r12;                 \
        xor     r15, r15;                       \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x28];            \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, r15;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x20];            \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, 0x0;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, 0x0;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, 0x0;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P2+0x8];             \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, 0x0;                       \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P2];                 \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, 0x0;                       \
        mov     [rsp+544], r13;                 \
        xor     r8, r8;                         \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x30];            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, r8;                         \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x28];            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, 0x0;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x20];            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, 0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, 0x0;                        \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, 0x0;                        \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P2+0x8];             \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, 0x0;                        \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P2];                 \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, 0x0;                        \
        mov     [rsp+552], r14;                 \
        xor     r9, r9;                         \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x38];            \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        adc     r9, r9;                         \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x30];            \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        adc     r9, 0x0;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x28];            \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        adc     r9, 0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x20];            \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        adc     r9, 0x0;                        \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        adc     r9, 0x0;                        \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        adc     r9, 0x0;                        \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P2+0x8];             \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        adc     r9, 0x0;                        \
        mov     rax, [P1+0x38];                 \
        mul     QWORD PTR [P2];                 \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        adc     r9, 0x0;                        \
        mov     [rsp+560], r15;                 \
        xor     r10, r10;                       \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x40];            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, r10;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x38];            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, 0x0;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x30];            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, 0x0;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x28];            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, 0x0;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P2+0x20];            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, 0x0;                       \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, 0x0;                       \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, 0x0;                       \
        mov     rax, [P1+0x38];                 \
        mul     QWORD PTR [P2+0x8];             \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, 0x0;                       \
        mov     rax, [P1+0x40];                 \
        mul     QWORD PTR [P2];                 \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, 0x0;                       \
        mov     [rsp+568], r8;                  \
        xor     r11, r11;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x40];            \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        adc     r11, r11;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x38];            \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        adc     r11, 0x0;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x30];            \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        adc     r11, 0x0;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P2+0x28];            \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        adc     r11, 0x0;                       \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P2+0x20];            \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        adc     r11, 0x0;                       \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        adc     r11, 0x0;                       \
        mov     rax, [P1+0x38];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        adc     r11, 0x0;                       \
        mov     rax, [P1+0x40];                 \
        mul     QWORD PTR [P2+0x8];             \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        adc     r11, 0x0;                       \
        xor     r12, r12;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x40];            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, r12;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x38];            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, 0x0;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P2+0x30];            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, 0x0;                       \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P2+0x28];            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, 0x0;                       \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P2+0x20];            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, 0x0;                       \
        mov     rax, [P1+0x38];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, 0x0;                       \
        mov     rax, [P1+0x40];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        adc     r12, 0x0;                       \
        xor     r13, r13;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x40];            \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        adc     r13, r13;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P2+0x38];            \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        adc     r13, 0x0;                       \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P2+0x30];            \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        adc     r13, 0x0;                       \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P2+0x28];            \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        adc     r13, 0x0;                       \
        mov     rax, [P1+0x38];                 \
        mul     QWORD PTR [P2+0x20];            \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        adc     r13, 0x0;                       \
        mov     rax, [P1+0x40];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        adc     r13, 0x0;                       \
        xor     r14, r14;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P2+0x40];            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, r14;                       \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P2+0x38];            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P2+0x30];            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        mov     rax, [P1+0x38];                 \
        mul     QWORD PTR [P2+0x28];            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        mov     rax, [P1+0x40];                 \
        mul     QWORD PTR [P2+0x20];            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        xor     r15, r15;                       \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P2+0x40];            \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, r15;                       \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P2+0x38];            \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, 0x0;                       \
        mov     rax, [P1+0x38];                 \
        mul     QWORD PTR [P2+0x30];            \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, 0x0;                       \
        mov     rax, [P1+0x40];                 \
        mul     QWORD PTR [P2+0x28];            \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, 0x0;                       \
        xor     r8, r8;                         \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P2+0x40];            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, r8;                         \
        mov     rax, [P1+0x38];                 \
        mul     QWORD PTR [P2+0x38];            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, 0x0;                        \
        mov     rax, [P1+0x40];                 \
        mul     QWORD PTR [P2+0x30];            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, 0x0;                        \
        mov     rax, [P1+0x38];                 \
        mul     QWORD PTR [P2+0x40];            \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        mov     rax, [P1+0x40];                 \
        mul     QWORD PTR [P2+0x38];            \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        mov     rax, [P1+0x40];                 \
        imul    rax, [P2+0x40];                 \
        add     rax, r8;                        \
        mov     r8, [rsp+568];                  \
        mov     rdx, r8;                        \
        and     rdx, 0x1ff;                     \
        shrd    r8, r9, 0x9;                    \
        shrd    r9, r10, 0x9;                   \
        shrd    r10, r11, 0x9;                  \
        shrd    r11, r12, 0x9;                  \
        shrd    r12, r13, 0x9;                  \
        shrd    r13, r14, 0x9;                  \
        shrd    r14, r15, 0x9;                  \
        shrd    r15, rax, 0x9;                  \
        shr     rax, 0x9;                       \
        add     rdx, rax;                       \
        add     r8, [rsp+504];                  \
        adc     r9, [rsp+512];                  \
        adc     r10, [rsp+520];                 \
        adc     r11, [rsp+528];                 \
        adc     r12, [rsp+536];                 \
        adc     r13, [rsp+544];                 \
        adc     r14, [rsp+552];                 \
        adc     r15, [rsp+560];                 \
        adc     rdx, 0;                         \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11;                 \
        mov     [P0+0x20], r12;                 \
        mov     [P0+0x28], r13;                 \
        mov     [P0+0x30], r14;                 \
        mov     [P0+0x38], r15;                 \
        mov     [P0+0x40], rdx

// P0 = C * P1 - D * P2 == C * P1 + D * (p_521 - P2)

#define cmsub_p521(P0,C,P1,D,P2)                \
        mov     rcx, D;                         \
        mov     rax, [P2];                      \
        not     rax;                            \
        mul     rcx;                            \
        mov     r8, rax;                        \
        mov     r9, rdx;                        \
        mov     rax, [P2+8];                    \
        not     rax;                            \
        mul     rcx;                            \
        xor     r10d, r10d;                     \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        mov     rax, [P2+16];                   \
        not     rax;                            \
        mul     rcx;                            \
        xor     r11d, r11d;                     \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        mov     rax, [P2+24];                   \
        not     rax;                            \
        mul     rcx;                            \
        xor     r12d, r12d;                     \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        mov     rax, [P2+32];                   \
        not     rax;                            \
        mul     rcx;                            \
        xor     r13d, r13d;                     \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        mov     rax, [P2+40];                   \
        not     rax;                            \
        mul     rcx;                            \
        xor     r14d, r14d;                     \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        mov     rax, [P2+48];                   \
        not     rax;                            \
        mul     rcx;                            \
        xor     r15d, r15d;                     \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        mov     rax, [P2+56];                   \
        not     rax;                            \
        mul     rcx;                            \
        xor     ebx, ebx;                       \
        add     r15, rax;                       \
        adc     rbx, rdx;                       \
        mov     rax, [P2+64];                   \
        xor     rax, 0x1FF;                     \
        imul    rax, rcx;                       \
        add     rbx, rax;                       \
        xor     eax, eax;                       \
        mov     ecx, C;                         \
        mov     rax, [P1];                      \
        mul     rcx;                            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x8];                  \
        mul     rcx;                            \
        sub     rdx, rbp;                       \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x10];                 \
        mul     rcx;                            \
        sub     rdx, rbp;                       \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x18];                 \
        mul     rcx;                            \
        sub     rdx, rbp;                       \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x20];                 \
        mul     rcx;                            \
        sub     rdx, rbp;                       \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x28];                 \
        mul     rcx;                            \
        sub     rdx, rbp;                       \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x30];                 \
        mul     rcx;                            \
        sub     rdx, rbp;                       \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x38];                 \
        mul     rcx;                            \
        sub     rdx, rbp;                       \
        add     r15, rax;                       \
        adc     rbx, rdx;                       \
        mov     rax, [P1+0x40];                 \
        imul    rax, rcx;                       \
        add     rbx, rax;                       \
        mov     rax, r9;                        \
        and     rax, r10;                       \
        and     rax, r11;                       \
        and     rax, r12;                       \
        and     rax, r13;                       \
        and     rax, r14;                       \
        and     rax, r15;                       \
        mov     rdx, rbx;                       \
        shr     rdx, 9;                         \
        or      rbx, ~0x1FF;                    \
        lea     rcx, [rdx+1];                   \
        add     rcx, r8;                        \
        mov     ecx, 0;                         \
        adc     rax, rcx;                       \
        mov     rax, rbx;                       \
        adc     rax, rcx;                       \
        adc     r8, rdx;                        \
        mov     [P0], r8;                       \
        adc     r9, rcx;                        \
        mov     [P0+8], r9;                     \
        adc     r10, rcx;                       \
        mov     [P0+16], r10;                   \
        adc     r11, rcx;                       \
        mov     [P0+24], r11;                   \
        adc     r12, rcx;                       \
        mov     [P0+32], r12;                   \
        adc     r13, rcx;                       \
        mov     [P0+40], r13;                   \
        adc     r14, rcx;                       \
        mov     [P0+48], r14;                   \
        adc     r15, rcx;                       \
        mov     [P0+56], r15;                   \
        adc     rbx, rcx;                       \
        and     rbx, 0x1FF;                     \
        mov     [P0+64], rbx

// P0 = 3 * P1 - 8 * P2 == 3 * P1 + 8 * (p_521 - P2)

#define cmsub38_p521(P0,P1,P2)                  \
        mov     rbx, [P2+64];                   \
        xor     rbx, 0x1FF;                     \
        mov     r15, [P2+56];                   \
        not     r15;                            \
        shld    rbx, r15, 3;                    \
        mov     r14, [P2+48];                   \
        not     r14;                            \
        shld    r15, r14, 3;                    \
        mov     r13, [P2+40];                   \
        not     r13;                            \
        shld    r14, r13, 3;                    \
        mov     r12, [P2+32];                   \
        not     r12;                            \
        shld    r13, r12, 3;                    \
        mov     r11, [P2+24];                   \
        not     r11;                            \
        shld    r12, r11, 3;                    \
        mov     r10, [P2+16];                   \
        not     r10;                            \
        shld    r11, r10, 3;                    \
        mov     r9, [P2+8];                     \
        not     r9;                             \
        shld    r10, r9, 3;                     \
        mov     r8, [P2];                       \
        not     r8;                             \
        shld    r9, r8, 3;                      \
        shl     r8, 3;                          \
        mov     ecx, 3;                         \
        mov     rax, [P1];                      \
        mul     rcx;                            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x8];                  \
        mul     rcx;                            \
        sub     rdx, rbp;                       \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x10];                 \
        mul     rcx;                            \
        sub     rdx, rbp;                       \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x18];                 \
        mul     rcx;                            \
        sub     rdx, rbp;                       \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x20];                 \
        mul     rcx;                            \
        sub     rdx, rbp;                       \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x28];                 \
        mul     rcx;                            \
        sub     rdx, rbp;                       \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x30];                 \
        mul     rcx;                            \
        sub     rdx, rbp;                       \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x38];                 \
        mul     rcx;                            \
        sub     rdx, rbp;                       \
        add     r15, rax;                       \
        adc     rbx, rdx;                       \
        mov     rax, [P1+0x40];                 \
        imul    rax, rcx;                       \
        add     rbx, rax;                       \
        mov     rax, r9;                        \
        and     rax, r10;                       \
        and     rax, r11;                       \
        and     rax, r12;                       \
        and     rax, r13;                       \
        and     rax, r14;                       \
        and     rax, r15;                       \
        mov     rdx, rbx;                       \
        shr     rdx, 9;                         \
        or      rbx, ~0x1FF;                    \
        lea     rcx, [rdx+1];                   \
        add     rcx, r8;                        \
        mov     ecx, 0;                         \
        adc     rax, rcx;                       \
        mov     rax, rbx;                       \
        adc     rax, rcx;                       \
        adc     r8, rdx;                        \
        mov     [P0], r8;                       \
        adc     r9, rcx;                        \
        mov     [P0+8], r9;                     \
        adc     r10, rcx;                       \
        mov     [P0+16], r10;                   \
        adc     r11, rcx;                       \
        mov     [P0+24], r11;                   \
        adc     r12, rcx;                       \
        mov     [P0+32], r12;                   \
        adc     r13, rcx;                       \
        mov     [P0+40], r13;                   \
        adc     r14, rcx;                       \
        mov     [P0+48], r14;                   \
        adc     r15, rcx;                       \
        mov     [P0+56], r15;                   \
        adc     rbx, rcx;                       \
        and     rbx, 0x1FF;                     \
        mov     [P0+64], rbx

// P0 = 4 * P1 - P2 = 4 * P1 + (p_521 - P2)

#define cmsub41_p521(P0,P1,P2)                  \
        mov     rbx, [P1+64];                   \
        mov     r15, [P1+56];                   \
        shld    rbx, r15, 2;                    \
        mov     r14, [P1+48];                   \
        shld    r15, r14, 2;                    \
        mov     r13, [P1+40];                   \
        shld    r14, r13, 2;                    \
        mov     r12, [P1+32];                   \
        shld    r13, r12, 2;                    \
        mov     r11, [P1+24];                   \
        shld    r12, r11, 2;                    \
        mov     r10, [P1+16];                   \
        shld    r11, r10, 2;                    \
        mov     r9, [P1+8];                     \
        shld    r10, r9, 2;                     \
        mov     r8, [P1];                       \
        shld    r9, r8, 2;                      \
        shl     r8, 2;                          \
        mov     rcx, [P2+64];                   \
        xor     rcx, 0x1FF;                     \
        mov     rax, [P2];                      \
        not     rax;                            \
        add     r8, rax;                        \
        mov     rax, [P2+8];                    \
        not     rax;                            \
        adc     r9, rax;                        \
        mov     rax, [P2+16];                   \
        not     rax;                            \
        adc     r10, rax;                       \
        mov     rax, [P2+24];                   \
        not     rax;                            \
        adc     r11, rax;                       \
        mov     rax, [P2+32];                   \
        not     rax;                            \
        adc     r12, rax;                       \
        mov     rax, [P2+40];                   \
        not     rax;                            \
        adc     r13, rax;                       \
        mov     rax, [P2+48];                   \
        not     rax;                            \
        adc     r14, rax;                       \
        mov     rax, [P2+56];                   \
        not     rax;                            \
        adc     r15, rax;                       \
        adc     rbx, rcx;                       \
        mov     rax, r9;                        \
        and     rax, r10;                       \
        and     rax, r11;                       \
        and     rax, r12;                       \
        and     rax, r13;                       \
        and     rax, r14;                       \
        and     rax, r15;                       \
        mov     rdx, rbx;                       \
        shr     rdx, 9;                         \
        or      rbx, ~0x1FF;                    \
        lea     rcx, [rdx+1];                   \
        add     rcx, r8;                        \
        mov     ecx, 0;                         \
        adc     rax, rcx;                       \
        mov     rax, rbx;                       \
        adc     rax, rcx;                       \
        adc     r8, rdx;                        \
        mov     [P0], r8;                       \
        adc     r9, rcx;                        \
        mov     [P0+8], r9;                     \
        adc     r10, rcx;                       \
        mov     [P0+16], r10;                   \
        adc     r11, rcx;                       \
        mov     [P0+24], r11;                   \
        adc     r12, rcx;                       \
        mov     [P0+32], r12;                   \
        adc     r13, rcx;                       \
        mov     [P0+40], r13;                   \
        adc     r14, rcx;                       \
        mov     [P0+48], r14;                   \
        adc     r15, rcx;                       \
        mov     [P0+56], r15;                   \
        adc     rbx, rcx;                       \
        and     rbx, 0x1FF;                     \
        mov     [P0+64], rbx

S2N_BN_SYMBOL(p521_jdouble_alt):
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
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

        CFI_DEC_RSP(NSPACE)

// Main code, just a sequence of basic field operations

// z2 = z^2
// y2 = y^2

        sqr_p521(z2,z_1)
        sqr_p521(y2,y_1)

// x2p = x^2 - z^4 = (x + z^2) * (x - z^2)

        add_p521(t1,x_1,z2)
        sub_p521(t2,x_1,z2)
        mul_p521(x2p,t1,t2)

// t1 = y + z
// x4p = x2p^2
// xy2 = x * y^2

        add_p521(t1,y_1,z_1)
        sqr_p521(x4p,x2p)
        weakmul_p521(xy2,x_1,y2)

// t2 = (y + z)^2

        sqr_p521(t2,t1)

// d = 12 * xy2 - 9 * x4p
// t1 = y^2 + 2 * y * z

        cmsub_p521(d,12,xy2,9,x4p)
        sub_p521(t1,t2,z2)

// y4 = y^4

        sqr_p521(y4,y2)

// z_3' = 2 * y * z
// dx2 = d * x2p

        sub_p521(z_3,t1,y2)
        weakmul_p521(dx2,d,x2p)

// x' = 4 * xy2 - d

        cmsub41_p521(x_3,xy2,d)

// y' = 3 * dx2 - 8 * y4

        cmsub38_p521(y_3,dx2,y4)

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

S2N_BN_SIZE_DIRECTIVE(p521_jdouble_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
