// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point doubling on NIST curve P-384 in Montgomery-Jacobian coordinates
//
//    extern void p384_montjdouble_alt(uint64_t p3[static 18],
//                                     const uint64_t p1[static 18]);
//
// Does p3 := 2 * p1 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^384 * x) mod p_384.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
//
// Standard x86-64 ABI: RDI = p3, RSI = p1
// Microsoft x64 ABI:   RCX = p3, RDX = p1
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p384_montjdouble_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(p384_montjdouble_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p384_montjdouble_alt)
        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 48

// Pointer-offset pairs for inputs and outputs
// These assume rdi = p3, rsi = p1. The latter stays true
// but montsqr below modifies rdi as well. Thus, we need
// to save rdi and restore it before the writes to outputs.

#define x_1 rsi+0
#define y_1 rsi+NUMSIZE
#define z_1 rsi+(2*NUMSIZE)

#define x_3 rdi+0
#define y_3 rdi+NUMSIZE
#define z_3 rdi+(2*NUMSIZE)

// Pointer-offset pairs for temporaries, with some aliasing
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

// Safe place for pointer to the output

#define input_z [rsp+(NUMSIZE*7)]

#define NSPACE 344

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

// Corresponds exactly to bignum_montsqr_p384_alt except rsi -> rdi

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
        mov     rdi, rdx;                       \
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
        adc     rdi, r13;                       \
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
        adc     r13, rdi;                       \
        adc     r8, 0x0;                        \
        cmovne  r14, rax;                       \
        cmovne  r15, r9;                        \
        cmovne  rcx, r10;                       \
        cmovne  rbx, r11;                       \
        cmovne  rbp, r12;                       \
        cmovne  rdi, r13;                       \
        mov     [P0], r14;                      \
        mov     [P0+0x8], r15;                  \
        mov     [P0+0x10], rcx;                 \
        mov     [P0+0x18], rbx;                 \
        mov     [P0+0x20], rbp;                 \
        mov     [P0+0x28], rdi

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
        mov    ebx,0xffffffff;                  \
        and    rcx,rbx;                         \
        xor    rbx,rbx;                         \
        sub    rbx,rcx;                         \
        sub    rax,rbx;                         \
        mov    [P0],rax;                        \
        sbb    rdx,rcx;                         \
        mov    [P0+0x8],rdx;                    \
        sbb    rax,rax;                         \
        and    rcx,rbx;                         \
        neg    rax;                             \
        sbb    r8,rcx;                          \
        mov    [P0+0x10],r8;                    \
        sbb    r9,0x0;                          \
        mov    [P0+0x18],r9;                    \
        sbb    r10,0x0;                         \
        mov    [P0+0x20],r10;                   \
        sbb    r11,0x0;                         \
        mov    [P0+0x28],r11

// Simplified bignum_add_p384, without carry chain suspension

#define add_p384(P0,P1,P2)                      \
        mov    rax,[P1];                        \
        add    rax,[P2];                        \
        mov    rcx,[P1+0x8];                    \
        adc    rcx,[P2+0x8];                    \
        mov    r8,[P1+0x10];                    \
        adc    r8,[P2+0x10];                    \
        mov    r9,[P1+0x18];                    \
        adc    r9,[P2+0x18];                    \
        mov    r10,[P1+0x20];                   \
        adc    r10,[P2+0x20];                   \
        mov    r11,[P1+0x28];                   \
        adc    r11,[P2+0x28];                   \
        mov    edx,0x0;                         \
        adc    rdx,rdx;                         \
        mov    rbp,0xffffffff00000001;          \
        add    rax,rbp;                         \
        mov    ebp,0xffffffff;                  \
        adc    rcx,rbp;                         \
        adc    r8,0x1;                          \
        adc    r9,0x0;                          \
        adc    r10,0x0;                         \
        adc    r11,0x0;                         \
        adc    rdx,0xffffffffffffffff;          \
        mov    ebx,1;                           \
        and    rbx,rdx;                         \
        and    rdx,rbp;                         \
        xor    rbp,rbp;                         \
        sub    rbp,rdx;                         \
        sub    rax,rbp;                         \
        mov    [P0],rax;                        \
        sbb    rcx,rdx;                         \
        mov    [P0+0x8],rcx;                    \
        sbb    r8,rbx;                          \
        mov    [P0+0x10],r8;                    \
        sbb    r9,0x0;                          \
        mov    [P0+0x18],r9;                    \
        sbb    r10,0x0;                         \
        mov    [P0+0x20],r10;                   \
        sbb    r11,0x0;                         \
        mov    [P0+0x28],r11

// P0 = 4 * P1 - P2

#define cmsub41_p384(P0,P1,P2)                  \
        mov     rcx, [P1+40];                   \
        mov     r13, rcx;                       \
        shr     rcx, 62;                        \
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
        add     rcx, 1;                         \
        sub     r8, [P2];                       \
        sbb     r9, [P2+0x8];                   \
        sbb     r10, [P2+0x10];                 \
        sbb     r11, [P2+0x18];                 \
        sbb     r12, [P2+0x20];                 \
        sbb     r13, [P2+0x28];                 \
        sbb     rcx,0;                          \
        mov     rax,0xffffffff00000001;         \
        mul     rcx;                            \
        add     r8,rax;                         \
        adc     r9,rdx;                         \
        adc     r10,rcx;                        \
        mov     rax,rcx;                        \
        sbb     rcx,rcx;                        \
        mov     edx,0xffffffff;                 \
        neg     rcx;                            \
        mul     rdx;                            \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        adc     r11,rcx;                        \
        adc     r12,0x0;                        \
        adc     r13,0x0;                        \
        sbb     rcx,rcx;                        \
        not     rcx;                            \
        mov     edx,0xffffffff;                 \
        xor     rax,rax;                        \
        and     rdx,rcx;                        \
        sub     rax,rdx;                        \
        and     rcx,0x1;                        \
        sub     r8,rax;                         \
        mov     [P0],r8;                        \
        sbb     r9,rdx;                         \
        mov     [P0+0x8],r9;                    \
        sbb     r10,rcx;                        \
        mov     [P0+0x10],r10;                  \
        sbb     r11,0x0;                        \
        mov     [P0+0x18],r11;                  \
        sbb     r12,0x0;                        \
        mov     [P0+0x20],r12;                  \
        sbb     r13,0x0;                        \
        mov     [P0+0x28],r13

// P0 = C * P1 - D * P2

#define cmsub_p384(P0,C,P1,D,P2)                \
        mov     r9, 0x00000000ffffffff;         \
        sub     r9, [P2];                       \
        mov     r10, 0xffffffff00000000;         \
        sbb     r10, [P2+8];                     \
        mov     r11, 0xfffffffffffffffe;        \
        sbb     r11, [P2+16];                   \
        mov     r12, 0xffffffffffffffff;        \
        sbb     r12, [P2+24];                   \
        mov     r13, 0xffffffffffffffff;        \
        sbb     r13, [P2+32];                   \
        mov     r14, 0xffffffffffffffff;        \
        sbb     r14, [P2+40];                   \
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
        mov     rax, r13;                       \
        xor     r13d, r13d;                     \
        mul     rcx;                            \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        mov     rax, r14;                       \
        mov     r14d, 1;                        \
        mul     rcx;                            \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
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
        sbb     rbx, rbx;                       \
        mov     rax, [P1+0x20];                 \
        mul     rcx;                            \
        sub     rdx, rbx;                       \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        sbb     rbx, rbx;                       \
        mov     rax, [P1+0x28];                 \
        mul     rcx;                            \
        sub     rdx, rbx;                       \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        mov     rax,0xffffffff00000001;         \
        mul     r14;                            \
        add     r8,rax;                         \
        adc     r9,rdx;                         \
        adc     r10,r14;                        \
        mov     rax,r14;                        \
        sbb     rcx,rcx;                        \
        mov     edx,0xffffffff;                 \
        neg     rcx;                            \
        mul     rdx;                            \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        adc     r11,rcx;                        \
        adc     r12,0x0;                        \
        adc     r13,0x0;                        \
        sbb     rcx,rcx;                        \
        not     rcx;                            \
        mov     edx,0xffffffff;                 \
        xor     rax,rax;                        \
        and     rdx,rcx;                        \
        sub     rax,rdx;                        \
        and     rcx,0x1;                        \
        sub     r8,rax;                         \
        mov     [P0],r8;                        \
        sbb     r9,rdx;                         \
        mov     [P0+0x8],r9;                    \
        sbb     r10,rcx;                        \
        mov     [P0+0x10],r10;                  \
        sbb     r11,0x0;                        \
        mov     [P0+0x18],r11;                  \
        sbb     r12,0x0;                        \
        mov     [P0+0x20],r12;                  \
        sbb     r13,0x0;                        \
        mov     [P0+0x28],r13

// A weak version of add that only guarantees sum in 6 digits

#define weakadd_p384(P0,P1,P2)                  \
        mov    rax,[P1];                        \
        add    rax,[P2];                        \
        mov    rcx,[P1+0x8];                    \
        adc    rcx,[P2+0x8];                    \
        mov    r8,[P1+0x10];                    \
        adc    r8,[P2+0x10];                    \
        mov    r9,[P1+0x18];                    \
        adc    r9,[P2+0x18];                    \
        mov    r10,[P1+0x20];                   \
        adc    r10,[P2+0x20];                   \
        mov    r11,[P1+0x28];                   \
        adc    r11,[P2+0x28];                   \
        sbb    rdx,rdx;                         \
        mov    ebx,1;                           \
        and    rbx,rdx;                         \
        mov    ebp,0xffffffff;                  \
        and    rdx,rbp;                         \
        xor    rbp,rbp;                         \
        sub    rbp,rdx;                         \
        add    rax,rbp;                         \
        mov    [P0],rax;                        \
        adc    rcx,rdx;                         \
        mov    [P0+0x8],rcx;                    \
        adc    r8,rbx;                          \
        mov    [P0+0x10],r8;                    \
        adc    r9,0x0;                          \
        mov    [P0+0x18],r9;                    \
        adc    r10,0x0;                         \
        mov    [P0+0x20],r10;                   \
        adc    r11,0x0;                         \
        mov    [P0+0x28],r11

// P0 = 3 * P1 - 8 * P2

#define cmsub38_p384(P0,P1,P2)                  \
        mov     r8, 0x00000000ffffffff;         \
        sub     r8, [P2];                       \
        mov     r9, 0xffffffff00000000;         \
        sbb     r9, [P2+8];                     \
        mov     r10, 0xfffffffffffffffe;        \
        sbb     r10, [P2+16];                   \
        mov     r11, 0xffffffffffffffff;        \
        sbb     r11, [P2+24];                   \
        mov     r12, 0xffffffffffffffff;        \
        sbb     r12, [P2+32];                   \
        mov     r13, 0xffffffffffffffff;        \
        sbb     r13, [P2+40];                   \
        mov     r14, r13;                       \
        shr     r14, 61;                        \
        shld    r13, r12, 3;                    \
        shld    r12, r11, 3;                    \
        shld    r11, r10, 3;                    \
        shld    r10, r9, 3;                     \
        shld    r9, r8, 3;                      \
        shl     r8, 3;                          \
        add     r14, 1;                         \
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
        sbb     rbx, rbx;                       \
        mov     rax, [P1+0x20];                 \
        mul     rcx;                            \
        sub     rdx, rbx;                       \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        sbb     rbx, rbx;                       \
        mov     rax, [P1+0x28];                 \
        mul     rcx;                            \
        sub     rdx, rbx;                       \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        mov     rax,0xffffffff00000001;         \
        mul     r14;                            \
        add     r8,rax;                         \
        adc     r9,rdx;                         \
        adc     r10,r14;                        \
        mov     rax,r14;                        \
        sbb     rcx,rcx;                        \
        mov     edx,0xffffffff;                 \
        neg     rcx;                            \
        mul     rdx;                            \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        adc     r11,rcx;                        \
        adc     r12,0x0;                        \
        adc     r13,0x0;                        \
        sbb     rcx,rcx;                        \
        not     rcx;                            \
        mov     edx,0xffffffff;                 \
        xor     rax,rax;                        \
        and     rdx,rcx;                        \
        sub     rax,rdx;                        \
        and     rcx,0x1;                        \
        sub     r8,rax;                         \
        mov     [P0],r8;                        \
        sbb     r9,rdx;                         \
        mov     [P0+0x8],r9;                    \
        sbb     r10,rcx;                        \
        mov     [P0+0x10],r10;                  \
        sbb     r11,0x0;                        \
        mov     [P0+0x18],r11;                  \
        sbb     r12,0x0;                        \
        mov     [P0+0x20],r12;                  \
        sbb     r13,0x0;                        \
        mov     [P0+0x28],r13

S2N_BN_SYMBOL(p384_montjdouble_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Save registers and make room on stack for temporary variables
// Save the output pointer rdi which gets overwritten in earlier
// operations before it is used.

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

        CFI_DEC_RSP(NSPACE)

        mov     input_z, rdi

// Main code, just a sequence of basic field operations

// z2 = z^2
// y2 = y^2

        montsqr_p384(z2,z_1)
        montsqr_p384(y2,y_1)

// x2p = x^2 - z^4 = (x + z^2) * (x - z^2)

        weakadd_p384(t1,x_1,z2)
        sub_p384(t2,x_1,z2)
        montmul_p384(x2p,t1,t2)

// t1 = y + z
// x4p = x2p^2
// xy2 = x * y^2

        add_p384(t1,y_1,z_1)
        montsqr_p384(x4p,x2p)
        montmul_p384(xy2,x_1,y2)

// t2 = (y + z)^2

        montsqr_p384(t2,t1)

// d = 12 * xy2 - 9 * x4p
// t1 = y^2 + 2 * y * z

        cmsub_p384(d,12,xy2,9,x4p)
        sub_p384(t1,t2,z2)

// y4 = y^4

        montsqr_p384(y4,y2)

// Restore the output pointer to write to x_3, y_3 and z_3.

        mov     rdi, input_z

// z_3' = 2 * y * z
// dx2 = d * x2p

        sub_p384(z_3,t1,y2)
        montmul_p384(dx2,d,x2p)

// x' = 4 * xy2 - d

        cmsub41_p384(x_3,xy2,d)

// y' = 3 * dx2 - 8 * y4

        cmsub38_p384(y_3,dx2,y4)

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

S2N_BN_SIZE_DIRECTIVE(p384_montjdouble_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
