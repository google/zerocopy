// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point addition on NIST curve P-384 in Montgomery-Jacobian coordinates
//
//    extern void p384_montjadd_alt(uint64_t p3[static 18],
//                                  const uint64_t p1[static 18],
//                                  const uint64_t p2[static 18]);
//
// Does p3 := p1 + p2 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^384 * x) mod p_384.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
//
// Standard x86-64 ABI: RDI = p3, RSI = p1, RDX = p2
// Microsoft x64 ABI:   RCX = p3, RDX = p1, R8 = p2
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p384_montjadd_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(p384_montjadd_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p384_montjadd_alt)
        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 48

// Pointer-offset pairs for inputs and outputs
// These assume rdi = p3, rsi = p1 and rcx = p2,
// which needs to be set up explicitly before use.
// The rdi value never changes, however.

#define x_1 rsi+0
#define y_1 rsi+NUMSIZE
#define z_1 rsi+(2*NUMSIZE)

#define x_2 rcx+0
#define y_2 rcx+NUMSIZE
#define z_2 rcx+(2*NUMSIZE)

#define x_3 rdi+0
#define y_3 rdi+NUMSIZE
#define z_3 rdi+(2*NUMSIZE)

// In one place it's convenient to use another register
// since the squaring function overwrites rcx

#define z_2_alt rsi+(2*NUMSIZE)

// Pointer-offset pairs for temporaries, with some aliasing
// NSPACE is the total stack needed for these temporaries

#define z1sq rsp+(NUMSIZE*0)
#define ww rsp+(NUMSIZE*0)
#define resx rsp+(NUMSIZE*0)

#define yd rsp+(NUMSIZE*1)
#define y2a rsp+(NUMSIZE*1)

#define x2a rsp+(NUMSIZE*2)
#define zzx2 rsp+(NUMSIZE*2)

#define zz rsp+(NUMSIZE*3)
#define t1 rsp+(NUMSIZE*3)

#define t2 rsp+(NUMSIZE*4)
#define x1a rsp+(NUMSIZE*4)
#define zzx1 rsp+(NUMSIZE*4)
#define resy rsp+(NUMSIZE*4)

#define xd rsp+(NUMSIZE*5)
#define z2sq rsp+(NUMSIZE*5)
#define resz rsp+(NUMSIZE*5)

#define y1a rsp+(NUMSIZE*6)

// Temporaries for the actual input pointers

#define input_x [rsp+(NUMSIZE*7)]
#define input_y [rsp+(NUMSIZE*7+8)]

#define NSPACE 352

// Corresponds exactly to bignum_montmul_p384_alt

#define montmul_p384(P0,P1,P2)                  \
        mov     rbx, [P2];                      \
        mov     rax, [P1];                      \
        mul     rbx;                            \
        mov     r8, rax;                        \
        mov     r9, rdx;                        \
        mov     rax, [P1+0x8];                  \
        mul     rbx;                            \
        xor     r10d, r10d;                     \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        mov     rax, [P1+0x10];                 \
        mul     rbx;                            \
        xor     r11d, r11d;                     \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        mov     rax, [P1+0x18];                 \
        mul     rbx;                            \
        xor     r12d, r12d;                     \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        mov     rax, [P1+0x20];                 \
        mul     rbx;                            \
        xor     r13d, r13d;                     \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        mov     rax, [P1+0x28];                 \
        mul     rbx;                            \
        xor     r14d, r14d;                     \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        xor     r15d, r15d;                     \
        mov     rbx, r8;                        \
        shl     rbx, 0x20;                      \
        add     rbx, r8;                        \
        xor     ebp, ebp;                       \
        mov     rax, 0xffffffff00000001;        \
        mul     rbx;                            \
        mov     r8, rdx;                        \
        mov     rax, 0xffffffff;                \
        mul     rbx;                            \
        add     rax, r8;                        \
        adc     rdx, rbx;                       \
        adc     ebp, ebp;                       \
        sub     r9, rax;                        \
        sbb     r10, rdx;                       \
        sbb     r11, rbp;                       \
        sbb     r12, 0x0;                       \
        sbb     r13, 0x0;                       \
        sbb     rbx, 0x0;                       \
        add     r14, rbx;                       \
        adc     r15, 0x0;                       \
        mov     rbx, [P2+0x8];                  \
        mov     rax, [P1];                      \
        mul     rbx;                            \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        sbb     r8, r8;                         \
        mov     rax, [P1+0x8];                  \
        mul     rbx;                            \
        sub     rdx, r8;                        \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     r8, r8;                         \
        mov     rax, [P1+0x10];                 \
        mul     rbx;                            \
        sub     rdx, r8;                        \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        sbb     r8, r8;                         \
        mov     rax, [P1+0x18];                 \
        mul     rbx;                            \
        sub     rdx, r8;                        \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        sbb     r8, r8;                         \
        mov     rax, [P1+0x20];                 \
        mul     rbx;                            \
        sub     rdx, r8;                        \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        sbb     r8, r8;                         \
        mov     rax, [P1+0x28];                 \
        mul     rbx;                            \
        sub     rdx, r8;                        \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        sbb     r8, r8;                         \
        neg     r8;                             \
        mov     rbx, r9;                        \
        shl     rbx, 0x20;                      \
        add     rbx, r9;                        \
        xor     ebp, ebp;                       \
        mov     rax, 0xffffffff00000001;        \
        mul     rbx;                            \
        mov     r9, rdx;                        \
        mov     rax, 0xffffffff;                \
        mul     rbx;                            \
        add     rax, r9;                        \
        adc     rdx, rbx;                       \
        adc     ebp, ebp;                       \
        sub     r10, rax;                       \
        sbb     r11, rdx;                       \
        sbb     r12, rbp;                       \
        sbb     r13, 0x0;                       \
        sbb     r14, 0x0;                       \
        sbb     rbx, 0x0;                       \
        add     r15, rbx;                       \
        adc     r8, 0x0;                        \
        mov     rbx, [P2+0x10];                 \
        mov     rax, [P1];                      \
        mul     rbx;                            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     r9, r9;                         \
        mov     rax, [P1+0x8];                  \
        mul     rbx;                            \
        sub     rdx, r9;                        \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        sbb     r9, r9;                         \
        mov     rax, [P1+0x10];                 \
        mul     rbx;                            \
        sub     rdx, r9;                        \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        sbb     r9, r9;                         \
        mov     rax, [P1+0x18];                 \
        mul     rbx;                            \
        sub     rdx, r9;                        \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        sbb     r9, r9;                         \
        mov     rax, [P1+0x20];                 \
        mul     rbx;                            \
        sub     rdx, r9;                        \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        sbb     r9, r9;                         \
        mov     rax, [P1+0x28];                 \
        mul     rbx;                            \
        sub     rdx, r9;                        \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        sbb     r9, r9;                         \
        neg     r9;                             \
        mov     rbx, r10;                       \
        shl     rbx, 0x20;                      \
        add     rbx, r10;                       \
        xor     ebp, ebp;                       \
        mov     rax, 0xffffffff00000001;        \
        mul     rbx;                            \
        mov     r10, rdx;                       \
        mov     rax, 0xffffffff;                \
        mul     rbx;                            \
        add     rax, r10;                       \
        adc     rdx, rbx;                       \
        adc     ebp, ebp;                       \
        sub     r11, rax;                       \
        sbb     r12, rdx;                       \
        sbb     r13, rbp;                       \
        sbb     r14, 0x0;                       \
        sbb     r15, 0x0;                       \
        sbb     rbx, 0x0;                       \
        add     r8, rbx;                        \
        adc     r9, 0x0;                        \
        mov     rbx, [P2+0x18];                 \
        mov     rax, [P1];                      \
        mul     rbx;                            \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        sbb     r10, r10;                       \
        mov     rax, [P1+0x8];                  \
        mul     rbx;                            \
        sub     rdx, r10;                       \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        sbb     r10, r10;                       \
        mov     rax, [P1+0x10];                 \
        mul     rbx;                            \
        sub     rdx, r10;                       \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        sbb     r10, r10;                       \
        mov     rax, [P1+0x18];                 \
        mul     rbx;                            \
        sub     rdx, r10;                       \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        sbb     r10, r10;                       \
        mov     rax, [P1+0x20];                 \
        mul     rbx;                            \
        sub     rdx, r10;                       \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        sbb     r10, r10;                       \
        mov     rax, [P1+0x28];                 \
        mul     rbx;                            \
        sub     rdx, r10;                       \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        sbb     r10, r10;                       \
        neg     r10;                            \
        mov     rbx, r11;                       \
        shl     rbx, 0x20;                      \
        add     rbx, r11;                       \
        xor     ebp, ebp;                       \
        mov     rax, 0xffffffff00000001;        \
        mul     rbx;                            \
        mov     r11, rdx;                       \
        mov     rax, 0xffffffff;                \
        mul     rbx;                            \
        add     rax, r11;                       \
        adc     rdx, rbx;                       \
        adc     ebp, ebp;                       \
        sub     r12, rax;                       \
        sbb     r13, rdx;                       \
        sbb     r14, rbp;                       \
        sbb     r15, 0x0;                       \
        sbb     r8, 0x0;                        \
        sbb     rbx, 0x0;                       \
        add     r9, rbx;                        \
        adc     r10, 0x0;                       \
        mov     rbx, [P2+0x20];                 \
        mov     rax, [P1];                      \
        mul     rbx;                            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        sbb     r11, r11;                       \
        mov     rax, [P1+0x8];                  \
        mul     rbx;                            \
        sub     rdx, r11;                       \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        sbb     r11, r11;                       \
        mov     rax, [P1+0x10];                 \
        mul     rbx;                            \
        sub     rdx, r11;                       \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        sbb     r11, r11;                       \
        mov     rax, [P1+0x18];                 \
        mul     rbx;                            \
        sub     rdx, r11;                       \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        sbb     r11, r11;                       \
        mov     rax, [P1+0x20];                 \
        mul     rbx;                            \
        sub     rdx, r11;                       \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        sbb     r11, r11;                       \
        mov     rax, [P1+0x28];                 \
        mul     rbx;                            \
        sub     rdx, r11;                       \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        sbb     r11, r11;                       \
        neg     r11;                            \
        mov     rbx, r12;                       \
        shl     rbx, 0x20;                      \
        add     rbx, r12;                       \
        xor     ebp, ebp;                       \
        mov     rax, 0xffffffff00000001;        \
        mul     rbx;                            \
        mov     r12, rdx;                       \
        mov     rax, 0xffffffff;                \
        mul     rbx;                            \
        add     rax, r12;                       \
        adc     rdx, rbx;                       \
        adc     ebp, ebp;                       \
        sub     r13, rax;                       \
        sbb     r14, rdx;                       \
        sbb     r15, rbp;                       \
        sbb     r8, 0x0;                        \
        sbb     r9, 0x0;                        \
        sbb     rbx, 0x0;                       \
        add     r10, rbx;                       \
        adc     r11, 0x0;                       \
        mov     rbx, [P2+0x28];                 \
        mov     rax, [P1];                      \
        mul     rbx;                            \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        sbb     r12, r12;                       \
        mov     rax, [P1+0x8];                  \
        mul     rbx;                            \
        sub     rdx, r12;                       \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        sbb     r12, r12;                       \
        mov     rax, [P1+0x10];                 \
        mul     rbx;                            \
        sub     rdx, r12;                       \
        add     r15, rax;                       \
        adc     r8, rdx;                        \
        sbb     r12, r12;                       \
        mov     rax, [P1+0x18];                 \
        mul     rbx;                            \
        sub     rdx, r12;                       \
        add     r8, rax;                        \
        adc     r9, rdx;                        \
        sbb     r12, r12;                       \
        mov     rax, [P1+0x20];                 \
        mul     rbx;                            \
        sub     rdx, r12;                       \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        sbb     r12, r12;                       \
        mov     rax, [P1+0x28];                 \
        mul     rbx;                            \
        sub     rdx, r12;                       \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     r12, r12;                       \
        neg     r12;                            \
        mov     rbx, r13;                       \
        shl     rbx, 0x20;                      \
        add     rbx, r13;                       \
        xor     ebp, ebp;                       \
        mov     rax, 0xffffffff00000001;        \
        mul     rbx;                            \
        mov     r13, rdx;                       \
        mov     rax, 0xffffffff;                \
        mul     rbx;                            \
        add     rax, r13;                       \
        adc     rdx, rbx;                       \
        adc     ebp, ebp;                       \
        sub     r14, rax;                       \
        sbb     r15, rdx;                       \
        sbb     r8, rbp;                        \
        sbb     r9, 0x0;                        \
        sbb     r10, 0x0;                       \
        sbb     rbx, 0x0;                       \
        add     r11, rbx;                       \
        adc     r12, 0x0;                       \
        xor     edx, edx;                       \
        xor     ebp, ebp;                       \
        xor     r13d, r13d;                     \
        mov     rax, 0xffffffff00000001;        \
        add     rax, r14;                       \
        mov     ebx, 0xffffffff;                \
        adc     rbx, r15;                       \
        mov     ecx, 0x1;                       \
        adc     rcx, r8;                        \
        adc     rdx, r9;                        \
        adc     rbp, r10;                       \
        adc     r13, r11;                       \
        adc     r12, 0x0;                       \
        cmovne  r14, rax;                       \
        cmovne  r15, rbx;                       \
        cmovne  r8, rcx;                        \
        cmovne  r9, rdx;                        \
        cmovne  r10, rbp;                       \
        cmovne  r11, r13;                       \
        mov     [P0], r14;                      \
        mov     [P0+0x8], r15;                  \
        mov     [P0+0x10], r8;                  \
        mov     [P0+0x18], r9;                  \
        mov     [P0+0x20], r10;                 \
        mov     [P0+0x28], r11

// Corresponds exactly to bignum_montsqr_p384_alt

#define montsqr_p384(P0,P1)                     \
        mov     rbx, [P1];                      \
        mov     rax, [P1+0x8];                  \
        mul     rbx;                            \
        mov     r9, rax;                        \
        mov     r10, rdx;                       \
        mov     rax, [P1+0x18];                 \
        mul     rbx;                            \
        mov     r11, rax;                       \
        mov     r12, rdx;                       \
        mov     rax, [P1+0x28];                 \
        mul     rbx;                            \
        mov     r13, rax;                       \
        mov     r14, rdx;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P1+0x20];            \
        mov     r15, rax;                       \
        mov     rcx, rdx;                       \
        mov     rbx, [P1+0x10];                 \
        mov     rax, [P1];                      \
        mul     rbx;                            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x8];                  \
        mul     rbx;                            \
        sub     rdx, rbp;                       \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rbx, [P1+0x8];                  \
        mov     rax, [P1+0x18];                 \
        mul     rbx;                            \
        sub     rdx, rbp;                       \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x20];                 \
        mul     rbx;                            \
        sub     rdx, rbp;                       \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x28];                 \
        mul     rbx;                            \
        sub     rdx, rbp;                       \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     rcx, 0x0;                       \
        mov     rbx, [P1+0x20];                 \
        mov     rax, [P1];                      \
        mul     rbx;                            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rbx, [P1+0x10];                 \
        mov     rax, [P1+0x18];                 \
        mul     rbx;                            \
        sub     rdx, rbp;                       \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x20];                 \
        mul     rbx;                            \
        sub     rdx, rbp;                       \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x28];                 \
        mul     rbx;                            \
        sub     rdx, rbp;                       \
        add     r15, rax;                       \
        adc     rcx, rdx;                       \
        sbb     rbp, rbp;                       \
        xor     ebx, ebx;                       \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P1+0x28];            \
        sub     rdx, rbp;                       \
        xor     ebp, ebp;                       \
        add     rcx, rax;                       \
        adc     rbx, rdx;                       \
        adc     ebp, ebp;                       \
        mov     rax, [P1+0x20];                 \
        mul     QWORD PTR [P1+0x28];            \
        add     rbx, rax;                       \
        adc     rbp, rdx;                       \
        xor     r8d, r8d;                       \
        add     r9, r9;                         \
        adc     r10, r10;                       \
        adc     r11, r11;                       \
        adc     r12, r12;                       \
        adc     r13, r13;                       \
        adc     r14, r14;                       \
        adc     r15, r15;                       \
        adc     rcx, rcx;                       \
        adc     rbx, rbx;                       \
        adc     rbp, rbp;                       \
        adc     r8d, r8d;                       \
        mov     rax, [P1];                      \
        mul     rax;                            \
        mov     [P0], r8;                       \
        mov     r8, rax;                        \
        mov     rax, [P1+0x8];                  \
        mov     [P0+0x8], rbp;                  \
        add     r9, rdx;                        \
        sbb     rbp, rbp;                       \
        mul     rax;                            \
        neg     rbp;                            \
        adc     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x10];                 \
        mul     rax;                            \
        neg     rbp;                            \
        adc     r12, rax;                       \
        adc     r13, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x18];                 \
        mul     rax;                            \
        neg     rbp;                            \
        adc     r14, rax;                       \
        adc     r15, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x20];                 \
        mul     rax;                            \
        neg     rbp;                            \
        adc     rcx, rax;                       \
        adc     rbx, rdx;                       \
        sbb     rbp, rbp;                       \
        mov     rax, [P1+0x28];                 \
        mul     rax;                            \
        neg     rbp;                            \
        adc     rax, [P0+0x8];                  \
        adc     rdx, [P0];                      \
        mov     rbp, rax;                       \
        mov     rsi, rdx;                       \
        mov     [P0], rbx;                      \
        mov     rbx, r8;                        \
        shl     rbx, 0x20;                      \
        add     rbx, r8;                        \
        mov     rax, 0xffffffff00000001;        \
        mul     rbx;                            \
        mov     r8, rdx;                        \
        mov     rax, 0xffffffff;                \
        mul     rbx;                            \
        add     r8, rax;                        \
        mov     eax, 0x0;                       \
        adc     rdx, rbx;                       \
        adc     eax, eax;                       \
        sub     r9, r8;                         \
        sbb     r10, rdx;                       \
        sbb     r11, rax;                       \
        sbb     r12, 0x0;                       \
        sbb     r13, 0x0;                       \
        mov     r8, rbx;                        \
        sbb     r8, 0x0;                        \
        mov     rbx, r9;                        \
        shl     rbx, 0x20;                      \
        add     rbx, r9;                        \
        mov     rax, 0xffffffff00000001;        \
        mul     rbx;                            \
        mov     r9, rdx;                        \
        mov     rax, 0xffffffff;                \
        mul     rbx;                            \
        add     r9, rax;                        \
        mov     eax, 0x0;                       \
        adc     rdx, rbx;                       \
        adc     eax, eax;                       \
        sub     r10, r9;                        \
        sbb     r11, rdx;                       \
        sbb     r12, rax;                       \
        sbb     r13, 0x0;                       \
        sbb     r8, 0x0;                        \
        mov     r9, rbx;                        \
        sbb     r9, 0x0;                        \
        mov     rbx, r10;                       \
        shl     rbx, 0x20;                      \
        add     rbx, r10;                       \
        mov     rax, 0xffffffff00000001;        \
        mul     rbx;                            \
        mov     r10, rdx;                       \
        mov     rax, 0xffffffff;                \
        mul     rbx;                            \
        add     r10, rax;                       \
        mov     eax, 0x0;                       \
        adc     rdx, rbx;                       \
        adc     eax, eax;                       \
        sub     r11, r10;                       \
        sbb     r12, rdx;                       \
        sbb     r13, rax;                       \
        sbb     r8, 0x0;                        \
        sbb     r9, 0x0;                        \
        mov     r10, rbx;                       \
        sbb     r10, 0x0;                       \
        mov     rbx, r11;                       \
        shl     rbx, 0x20;                      \
        add     rbx, r11;                       \
        mov     rax, 0xffffffff00000001;        \
        mul     rbx;                            \
        mov     r11, rdx;                       \
        mov     rax, 0xffffffff;                \
        mul     rbx;                            \
        add     r11, rax;                       \
        mov     eax, 0x0;                       \
        adc     rdx, rbx;                       \
        adc     eax, eax;                       \
        sub     r12, r11;                       \
        sbb     r13, rdx;                       \
        sbb     r8, rax;                        \
        sbb     r9, 0x0;                        \
        sbb     r10, 0x0;                       \
        mov     r11, rbx;                       \
        sbb     r11, 0x0;                       \
        mov     rbx, r12;                       \
        shl     rbx, 0x20;                      \
        add     rbx, r12;                       \
        mov     rax, 0xffffffff00000001;        \
        mul     rbx;                            \
        mov     r12, rdx;                       \
        mov     rax, 0xffffffff;                \
        mul     rbx;                            \
        add     r12, rax;                       \
        mov     eax, 0x0;                       \
        adc     rdx, rbx;                       \
        adc     eax, eax;                       \
        sub     r13, r12;                       \
        sbb     r8, rdx;                        \
        sbb     r9, rax;                        \
        sbb     r10, 0x0;                       \
        sbb     r11, 0x0;                       \
        mov     r12, rbx;                       \
        sbb     r12, 0x0;                       \
        mov     rbx, r13;                       \
        shl     rbx, 0x20;                      \
        add     rbx, r13;                       \
        mov     rax, 0xffffffff00000001;        \
        mul     rbx;                            \
        mov     r13, rdx;                       \
        mov     rax, 0xffffffff;                \
        mul     rbx;                            \
        add     r13, rax;                       \
        mov     eax, 0x0;                       \
        adc     rdx, rbx;                       \
        adc     eax, eax;                       \
        sub     r8, r13;                        \
        sbb     r9, rdx;                        \
        sbb     r10, rax;                       \
        sbb     r11, 0x0;                       \
        sbb     r12, 0x0;                       \
        mov     r13, rbx;                       \
        sbb     r13, 0x0;                       \
        mov     rbx, [P0];                      \
        add     r14, r8;                        \
        adc     r15, r9;                        \
        adc     rcx, r10;                       \
        adc     rbx, r11;                       \
        adc     rbp, r12;                       \
        adc     rsi, r13;                       \
        mov     r8d, 0x0;                       \
        adc     r8, r8;                         \
        xor     r11, r11;                       \
        xor     r12, r12;                       \
        xor     r13, r13;                       \
        mov     rax, 0xffffffff00000001;        \
        add     rax, r14;                       \
        mov     r9d, 0xffffffff;                \
        adc     r9, r15;                        \
        mov     r10d, 0x1;                      \
        adc     r10, rcx;                       \
        adc     r11, rbx;                       \
        adc     r12, rbp;                       \
        adc     r13, rsi;                       \
        adc     r8, 0x0;                        \
        cmovne  r14, rax;                       \
        cmovne  r15, r9;                        \
        cmovne  rcx, r10;                       \
        cmovne  rbx, r11;                       \
        cmovne  rbp, r12;                       \
        cmovne  rsi, r13;                       \
        mov     [P0], r14;                      \
        mov     [P0+0x8], r15;                  \
        mov     [P0+0x10], rcx;                 \
        mov     [P0+0x18], rbx;                 \
        mov     [P0+0x20], rbp;                 \
        mov     [P0+0x28], rsi

// Corresponds exactly to bignum_sub_p384

#define sub_p384(P0,P1,P2)                      \
        mov    rax,[P1];                        \
        sub    rax,[P2];                        \
        mov    rdx,[P1+0x8];                    \
        sbb    rdx,[P2+0x8];                    \
        mov    r8,[P1+0x10];                    \
        sbb    r8,[P2+0x10];                    \
        mov    r9,[P1+0x18];                    \
        sbb    r9,[P2+0x18];                    \
        mov    r10,[P1+0x20];                   \
        sbb    r10,[P2+0x20];                   \
        mov    r11,[P1+0x28];                   \
        sbb    r11,[P2+0x28];                   \
        sbb    rcx,rcx;                         \
        mov    esi,0xffffffff;                  \
        and    rcx,rsi;                         \
        xor    rsi,rsi;                         \
        sub    rsi,rcx;                         \
        sub    rax,rsi;                         \
        mov    [P0],rax;                        \
        sbb    rdx,rcx;                         \
        mov    [P0+0x8],rdx;                    \
        sbb    rax,rax;                         \
        and    rcx,rsi;                         \
        neg    rax;                             \
        sbb    r8,rcx;                          \
        mov    [P0+0x10],r8;                    \
        sbb    r9,0x0;                          \
        mov    [P0+0x18],r9;                    \
        sbb    r10,0x0;                         \
        mov    [P0+0x20],r10;                   \
        sbb    r11,0x0;                         \
        mov    [P0+0x28],r11

// Additional macros to help with final multiplexing

#define load6(r0,r1,r2,r3,r4,r5,P)              \
        mov     r0, [P];                        \
        mov     r1, [P+8];                      \
        mov     r2, [P+16];                     \
        mov     r3, [P+24];                     \
        mov     r4, [P+32];                     \
        mov     r5, [P+40]

#define store6(P,r0,r1,r2,r3,r4,r5)             \
        mov     [P], r0;                        \
        mov     [P+8], r1;                      \
        mov     [P+16], r2;                     \
        mov     [P+24], r3;                     \
        mov     [P+32], r4;                     \
        mov     [P+40], r5;                     \

#define czload6(r0,r1,r2,r3,r4,r5,P)            \
        cmovz   r0, [P];                        \
        cmovz   r1, [P+8];                      \
        cmovz   r2, [P+16];                     \
        cmovz   r3, [P+24];                     \
        cmovz   r4, [P+32];                     \
        cmovz   r5, [P+40]

#define muxload6(r0,r1,r2,r3,r4,r5,P0,P1,P2)    \
        mov     r0, [P0];                       \
        cmovb   r0, [P1];                       \
        cmovnbe r0, [P2];                       \
        mov     r1, [P0+8];                     \
        cmovb   r1, [P1+8];                     \
        cmovnbe r1, [P2+8];                     \
        mov     r2, [P0+16];                    \
        cmovb   r2, [P1+16];                    \
        cmovnbe r2, [P2+16];                    \
        mov     r3, [P0+24];                    \
        cmovb   r3, [P1+24];                    \
        cmovnbe r3, [P2+24];                    \
        mov     r4, [P0+32];                    \
        cmovb   r4, [P1+32];                    \
        cmovnbe r4, [P2+32];                    \
        mov     r5, [P0+40];                    \
        cmovb   r5, [P1+40];                    \
        cmovnbe r5, [P2+40]

S2N_BN_SYMBOL(p384_montjadd_alt):
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
// Put the input arguments in non-volatile places on the stack

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

        CFI_DEC_RSP(NSPACE)

        mov     input_x, rsi
        mov     input_y, rdx

// Main code, just a sequence of basic field operations
// 8 * multiply + 3 * square + 7 * subtract

        montsqr_p384(z1sq,z_1)
        mov     rsi, input_y
        montsqr_p384(z2sq,z_2_alt)

        mov     rsi, input_x
        mov     rcx, input_y
        montmul_p384(y1a,z_2,y_1)
        mov     rsi, input_x
        mov     rcx, input_y
        montmul_p384(y2a,z_1,y_2)

        mov     rcx, input_y
        montmul_p384(x2a,z1sq,x_2)
        mov     rsi, input_x
        montmul_p384(x1a,z2sq,x_1)
        montmul_p384(y2a,z1sq,y2a)
        montmul_p384(y1a,z2sq,y1a)

        sub_p384(xd,x2a,x1a)
        sub_p384(yd,y2a,y1a)

        montsqr_p384(zz,xd)
        montsqr_p384(ww,yd)

        montmul_p384(zzx1,zz,x1a)
        montmul_p384(zzx2,zz,x2a)

        sub_p384(resx,ww,zzx1)
        sub_p384(t1,zzx2,zzx1)

        mov     rsi, input_x
        montmul_p384(xd,xd,z_1)

        sub_p384(resx,resx,zzx2)

        sub_p384(t2,zzx1,resx)

        montmul_p384(t1,t1,y1a)

        mov     rcx, input_y
        montmul_p384(resz,xd,z_2)
        montmul_p384(t2,yd,t2)

        sub_p384(resy,t2,t1)

// Load in the z coordinates of the inputs to check for P1 = 0 and P2 = 0
// The condition codes get set by a comparison (P2 != 0) - (P1 != 0)
// So "NBE" <=> ~(CF \/ ZF) <=> P1 = 0 /\ ~(P2 = 0)
// and "B"  <=> CF          <=> ~(P1 = 0) /\ P2 = 0
// and "Z"  <=> ZF          <=> (P1 = 0 <=> P2 = 0)
// Multiplex the z outputs accordingly and re-store in resz

        mov     rcx, input_y
        load6(r8,r9,r10,r11,rbx,rbp,z_2)
        mov     rax, r8
        mov     rdx, r9
        or      rax, r10
        or      rdx, r11
        or      rax, rbx
        or      rdx, rbp
        or      rax, rdx
        neg     rax
        sbb     rax, rax

        mov     rsi, input_x
        load6(r12,r13,r14,r15,rdx,rcx,z_1)
        cmovz   r8, r12
        cmovz   r9, r13
        cmovz   r10, r14
        cmovz   r11, r15
        cmovz   rbx, rdx
        cmovz   rbp, rcx
        or      r12, r13
        or      r14, r15
        or      rdx, rcx
        or      r12, r14
        or      rdx, r12
        neg     rdx
        sbb     rdx, rdx

        cmp     rax, rdx

        czload6(r8,r9,r10,r11,rbx,rbp,resz)
        store6(resz,r8,r9,r10,r11,rbx,rbp)

// Multiplex the x and y outputs too, keeping the results in registers

        mov     rcx, input_y
        mov     rsi, input_x
        muxload6(r8,r9,r10,r11,rbx,rbp,resx,x_1,x_2)
        muxload6(r12,r13,r14,r15,rdx,rax,resy,y_1,y_2)

// Finally store back the multiplexed values

        store6(x_3,r8,r9,r10,r11,rbx,rbp)
        load6(r8,r9,r10,r11,rbx,rbp,resz)
        store6(y_3,r12,r13,r14,r15,rdx,rax)
        store6(z_3,r8,r9,r10,r11,rbx,rbp)

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

S2N_BN_SIZE_DIRECTIVE(p384_montjadd_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
