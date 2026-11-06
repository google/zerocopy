// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point mixed addition on NIST curve P-521 in Jacobian coordinates
//
//    extern void p521_jmixadd_alt(uint64_t p3[static 27],
//                                 const uint64_t p1[static 27],
//                                 const uint64_t p2[static 18]);
//
// Does p3 := p1 + p2 where all points are regarded as Jacobian triples.
// A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3).
// The "mixed" part means that p2 only has x and y coordinates, with the
// implicit z coordinate assumed to be the identity. It is assumed that
// all the coordinates of the input points p1 and p2 are fully reduced
// mod p_521, that the z coordinate of p1 is nonzero and that neither
// p1 =~= p2 or p1 =~= -p2, where "=~=" means "represents the same affine
// point as".
//
// Standard x86-64 ABI: RDI = p3, RSI = p1, RDX = p2
// Microsoft x64 ABI:   RCX = p3, RDX = p1, R8 = p2
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p521_jmixadd_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(p521_jmixadd_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p521_jmixadd_alt)
        .text

// Size of individual field elements

#define NUMSIZE 72

// Stable homes for input arguments during main code sequence
// These are where they arrive except for input_y, initially in rdx

#define input_z rdi
#define input_x rsi
#define input_y rcx

// Pointer-offset pairs for inputs and outputs

#define x_1 input_x+0
#define y_1 input_x+NUMSIZE
#define z_1 input_x+(2*NUMSIZE)

#define x_2 input_y+0
#define y_2 input_y+NUMSIZE

#define x_3 input_z+0
#define y_3 input_z+NUMSIZE
#define z_3 input_z+(2*NUMSIZE)

// Pointer-offset pairs for temporaries, with some aliasing
// The tmp field is internal storage for field mul and sqr.
// NSPACE is the total stack needed for these temporaries

#define zp2 rsp+(NUMSIZE*0)
#define ww rsp+(NUMSIZE*0)
#define resx rsp+(NUMSIZE*0)

#define yd rsp+(NUMSIZE*1)
#define y2a rsp+(NUMSIZE*1)

#define x2a rsp+(NUMSIZE*2)
#define zzx2 rsp+(NUMSIZE*2)

#define zz rsp+(NUMSIZE*3)
#define t1 rsp+(NUMSIZE*3)

#define t2 rsp+(NUMSIZE*4)
#define zzx1 rsp+(NUMSIZE*4)
#define resy rsp+(NUMSIZE*4)

#define xd rsp+(NUMSIZE*5)
#define resz rsp+(NUMSIZE*5)

#define tmp rsp+(NUMSIZE*6)

#define NSPACE NUMSIZE*7

// Corresponds exactly to bignum_mul_p521_alt except temp storage

#define mul_p521(P0,P1,P2)                      \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2];                 \
        mov     [rsp+432], rax;                 \
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
        mov     [rsp+440], r9;                  \
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
        mov     [rsp+448], r10;                 \
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
        mov     [rsp+456], r11;                 \
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
        mov     [rsp+464], r12;                 \
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
        mov     [rsp+472], r13;                 \
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
        mov     [rsp+480], r14;                 \
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
        mov     [rsp+488], r15;                 \
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
        mov     [rsp+496], r8;                  \
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
        mov     r8, [rsp+496];                  \
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
        adc     r8, [rsp+432];                  \
        adc     r9, [rsp+440];                  \
        adc     r10, [rsp+448];                 \
        adc     r11, [rsp+456];                 \
        adc     r12, [rsp+464];                 \
        adc     r13, [rsp+472];                 \
        adc     r14, [rsp+480];                 \
        adc     r15, [rsp+488];                 \
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

// Corresponds to bignum_sqr_p521_alt except rbp is used
// in place of rcx and the output as temp storage location

#define sqr_p521(P0,P1)                         \
        mov     rax, [P1];                      \
        mul     rax;                            \
        mov     [rsp+432], rax;                 \
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
        mov     [rsp+440], r9;                  \
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
        mov     [rsp+448], r10;                 \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x18];            \
        xor     r13, r13;                       \
        mov     rbx, rax;                       \
        mov     rbp, rdx;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x10];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r13, 0x0;                       \
        add     rbx, rbx;                       \
        adc     rbp, rbp;                       \
        adc     r13, r13;                       \
        add     r11, rbx;                       \
        adc     r12, rbp;                       \
        adc     r13, 0x0;                       \
        mov     [rsp+456], r11;                 \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x20];            \
        xor     r14, r14;                       \
        mov     rbx, rax;                       \
        mov     rbp, rdx;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x18];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r14, 0x0;                       \
        add     rbx, rbx;                       \
        adc     rbp, rbp;                       \
        adc     r14, r14;                       \
        add     r12, rbx;                       \
        adc     r13, rbp;                       \
        adc     r14, 0x0;                       \
        mov     rax, [P1+0x10];                 \
        mul     rax;                            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        mov     [rsp+464], r12;                 \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x28];            \
        xor     r15, r15;                       \
        mov     rbx, rax;                       \
        mov     rbp, rdx;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x20];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r15, 0x0;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P1+0x18];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r15, 0x0;                       \
        add     rbx, rbx;                       \
        adc     rbp, rbp;                       \
        adc     r15, r15;                       \
        add     r13, rbx;                       \
        adc     r14, rbp;                       \
        adc     r15, 0x0;                       \
        mov     [rsp+472], r13;                 \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x30];            \
        xor     r8, r8;                         \
        mov     rbx, rax;                       \
        mov     rbp, rdx;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x28];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r8, 0x0;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P1+0x20];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r8, 0x0;                        \
        add     rbx, rbx;                       \
        adc     rbp, rbp;                       \
        adc     r8, r8;                         \
        add     r14, rbx;                       \
        adc     r15, rbp;                       \
        adc     r8, 0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     rax;                            \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, 0x0;                        \
        mov     [rsp+480], r14;                 \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x38];            \
        xor     r9, r9;                         \
        mov     rbx, rax;                       \
        mov     rbp, rdx;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x30];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r9, 0x0;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P1+0x28];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r9, 0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P1+0x20];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r9, 0x0;                        \
        add     rbx, rbx;                       \
        adc     rbp, rbp;                       \
        adc     r9, r9;                         \
        add     r15, rbx;                       \
        adc     r8, rbp;                        \
        adc     r9, 0x0;                        \
        mov     [rsp+488], r15;                 \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x40];            \
        xor     r10, r10;                       \
        mov     rbx, rax;                       \
        mov     rbp, rdx;                       \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x38];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r10, 0x0;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P1+0x30];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r10, 0x0;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P1+0x28];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r10, 0x0;                       \
        add     rbx, rbx;                       \
        adc     rbp, rbp;                       \
        adc     r10, r10;                       \
        add     r8, rbx;                        \
        adc     r9, rbp;                        \
        adc     r10, 0x0;                       \
        mov     rax, [P1+0x20];                 \
        mul     rax;                            \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        adc     r10, 0x0;                       \
        mov     [rsp+496], r8;                  \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x40];            \
        xor     r11, r11;                       \
        mov     rbx, rax;                       \
        mov     rbp, rdx;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P1+0x38];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r11, 0x0;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P1+0x30];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r11, 0x0;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P1+0x28];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r11, 0x0;                       \
        add     rbx, rbx;                       \
        adc     rbp, rbp;                       \
        adc     r11, r11;                       \
        add     r9, rbx;                        \
        adc     r10, rbp;                       \
        adc     r11, 0x0;                       \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P1+0x40];            \
        xor     r12, r12;                       \
        mov     rbx, rax;                       \
        mov     rbp, rdx;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P1+0x38];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r12, 0x0;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P1+0x30];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r12, 0x0;                       \
        add     rbx, rbx;                       \
        adc     rbp, rbp;                       \
        adc     r12, r12;                       \
        add     r10, rbx;                       \
        adc     r11, rbp;                       \
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
        mov     rbp, rdx;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P1+0x38];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r13, 0x0;                       \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P1+0x30];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r13, 0x0;                       \
        add     rbx, rbx;                       \
        adc     rbp, rbp;                       \
        adc     r13, r13;                       \
        add     r11, rbx;                       \
        adc     r12, rbp;                       \
        adc     r13, 0x0;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P1+0x40];            \
        xor     r14, r14;                       \
        mov     rbx, rax;                       \
        mov     rbp, rdx;                       \
        mov     rax, [P1+0x28];                 \
        mul     QWORD PTR [P1+0x38];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r14, 0x0;                       \
        add     rbx, rbx;                       \
        adc     rbp, rbp;                       \
        adc     r14, r14;                       \
        add     r12, rbx;                       \
        adc     r13, rbp;                       \
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
        mov     rbp, rdx;                       \
        mov     rax, [P1+0x30];                 \
        mul     QWORD PTR [P1+0x38];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        adc     r15, 0x0;                       \
        add     rbx, rbx;                       \
        adc     rbp, rbp;                       \
        adc     r15, r15;                       \
        add     r13, rbx;                       \
        adc     r14, rbp;                       \
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
        mov     r8, [rsp+496];                  \
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
        adc     r8, [rsp+432];                  \
        adc     r9, [rsp+440];                  \
        adc     r10, [rsp+448];                 \
        adc     r11, [rsp+456];                 \
        adc     r12, [rsp+464];                 \
        adc     r13, [rsp+472];                 \
        adc     r14, [rsp+480];                 \
        adc     r15, [rsp+488];                 \
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

// Additional macros to help with final multiplexing

#define testzero9(P)                            \
        mov     rax, [P];                       \
        mov     rbx, [P+8];                     \
        mov     rdx, [P+16];                    \
        mov     rbp, [P+24];                    \
        or      rax, [P+32];                    \
        or      rbx, [P+40];                    \
        or      rdx, [P+48];                    \
        or      rbp, [P+56];                    \
        or      rax, rbx;                       \
        or      rdx, rbp;                       \
        or      rax, [P+64];                    \
        or      rax, rdx

#define mux9(P0,PNE,PEQ)                        \
        mov     rax, [PNE];                     \
        mov     rbx, [PEQ];                     \
        cmovz   rax, rbx;                       \
        mov     [P0], rax;                      \
        mov     rax, [PNE+8];                   \
        mov     rbx, [PEQ+8];                   \
        cmovz   rax, rbx;                       \
        mov     [P0+8], rax;                    \
        mov     rax, [PNE+16];                  \
        mov     rbx, [PEQ+16];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+16], rax;                   \
        mov     rax, [PNE+24];                  \
        mov     rbx, [PEQ+24];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+24], rax;                   \
        mov     rax, [PNE+32];                  \
        mov     rbx, [PEQ+32];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+32], rax;                   \
        mov     rax, [PNE+40];                  \
        mov     rbx, [PEQ+40];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+40], rax;                   \
        mov     rax, [PNE+48];                  \
        mov     rbx, [PEQ+48];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+48], rax;                   \
        mov     rax, [PNE+56];                  \
        mov     rbx, [PEQ+56];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+56], rax;                   \
        mov     rax, [PNE+64];                  \
        mov     rbx, [PEQ+64];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+64], rax

#define mux9c(P0,PNE)                           \
        mov     rax, [PNE];                     \
        mov     ebx, 1;                         \
        cmovz   rax, rbx;                       \
        mov     [P0], rax;                      \
        mov     rax, [PNE+8];                   \
        mov     ebx, 0;                         \
        cmovz   rax, rbx;                       \
        mov     [P0+8], rax;                    \
        mov     rax, [PNE+16];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+16], rax;                   \
        mov     rax, [PNE+24];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+24], rax;                   \
        mov     rax, [PNE+32];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+32], rax;                   \
        mov     rax, [PNE+40];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+40], rax;                   \
        mov     rax, [PNE+48];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+48], rax;                   \
        mov     rax, [PNE+56];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+56], rax;                   \
        mov     rax, [PNE+64];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+64], rax

#define copy9(P0,P1)                            \
        mov     rax,[P1];                       \
        mov     [P0],rax;                       \
        mov     rax,[P1+8];                     \
        mov     [P0+8],rax;                     \
        mov     rax,[P1+16];                    \
        mov     [P0+16],rax;                    \
        mov     rax,[P1+24];                    \
        mov     [P0+24],rax;                    \
        mov     rax,[P1+32];                    \
        mov     [P0+32],rax;                    \
        mov     rax,[P1+40];                    \
        mov     [P0+40],rax;                    \
        mov     rax,[P1+48];                    \
        mov     [P0+48],rax;                    \
        mov     rax,[P1+56];                    \
        mov     [P0+56],rax;                    \
        mov     rax,[P1+64];                    \
        mov     [P0+64],rax

S2N_BN_SYMBOL(p521_jmixadd_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Save registers and make room on stack for temporary variables

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

        CFI_DEC_RSP(NSPACE)

// Move the input arguments to stable places (two are already there)

        mov     input_y, rdx

// Main code, just a sequence of basic field operations

        sqr_p521(zp2,z_1)
        mul_p521(y2a,z_1,y_2)

        mul_p521(x2a,zp2,x_2)
        mul_p521(y2a,zp2,y2a)

        sub_p521(xd,x2a,x_1)
        sub_p521(yd,y2a,y_1)

        sqr_p521(zz,xd)
        sqr_p521(ww,yd)

        mul_p521(zzx1,zz,x_1)
        mul_p521(zzx2,zz,x2a)

        sub_p521(resx,ww,zzx1)
        sub_p521(t1,zzx2,zzx1)

        mul_p521(resz,xd,z_1)

        sub_p521(resx,resx,zzx2)

        sub_p521(t2,zzx1,resx)

        mul_p521(t1,t1,y_1)
        mul_p521(t2,yd,t2)

        sub_p521(resy,t2,t1)

// Test if z_1 = 0 to decide if p1 = 0 (up to projective equivalence)

        testzero9(z_1)

// Multiplex: if p1 <> 0 just copy the computed result from the staging area.
// If p1 = 0 then return the point p2 augmented with an extra z = 1
// coordinate, hence giving 0 + p2 = p2 for the final result.

        mux9    (resx,resx,x_2)
        mux9    (resy,resy,y_2)

        copy9(x_3,resx)
        copy9(y_3,resy)

        mux9c(z_3,resz)

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

S2N_BN_SIZE_DIRECTIVE(p521_jmixadd_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
