// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery ladder step on pairs of (X,Z)-projective curve25519 points
//
// extern void curve25519_ladderstep_alt
//   (uint64_t rr[16],const uint64_t point[8],const uint64_t pp[16],uint64_t b);
//
// If point = (X,1) and pp = (n * (X,1),[n+1] * (X,1)) then the output
// rr = (n' * (X,1),[n'+1] * (X,1)) where n' = 2 * n + b, with input
// b assumed to be 0 or 1; in this setting, each pair (X,Z) is assumed to
// be a projective y-free representation of an affine curve25519 point
// (X/Z,y), with the initial "differential" point having Z = 1 and X its
// affine x coordinate. In other words, the ladderstep operation is a
// combination of doubling, differential addition and optional swapping.
//
// Standard x86-64 ABI: RDI = rr, RSI = point, RDX = pp, RCX = b
// Microsoft x64 ABI:   RCX = rr, RDX = point, R8 = pp, R9 = b
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(curve25519_ladderstep_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(curve25519_ladderstep_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(curve25519_ladderstep_alt)
        .text

// Size of individual field elements

#define NUMSIZE 32

// The single field of the input point used (z assumed 1)

#define point_x rbp+0

// Pointer-offset pairs for pp fields
// These use the initial register rdx as the offset.
// We then never need it again so it can be ephemeral

#define xn rdx+0
#define zn rdx+NUMSIZE
#define xm rdx+(2*NUMSIZE)
#define zm rdx+(3*NUMSIZE)

// Result fields

#define res0 rbp+0
#define res1 rbp+NUMSIZE
#define res2 rbp+(2*NUMSIZE)
#define res3 rbp+(3*NUMSIZE)

// Pointer-offset pairs for temporaries on stack
// dmsn and dnsm need space for >= 5 digits, and we allocate 8

#define sm rsp+(0*NUMSIZE)
#define sn rsp+(1*NUMSIZE)
#define dm rsp+(2*NUMSIZE)
#define dn rsp+(3*NUMSIZE)
#define dmsn rsp+(4*NUMSIZE)
#define dnsm rsp+(6*NUMSIZE)
#define s rsp+(8*NUMSIZE)
#define d rsp+(9*NUMSIZE)
#define p rsp+(10*NUMSIZE)

// Preserved inputs

#define rr [rsp+(12*NUMSIZE)]
#define point [rsp+(12*NUMSIZE)+8]
#define pp [rsp+(12*NUMSIZE)+16]
#define bb QWORD PTR [rsp+(12*NUMSIZE)+24]

// More, but aliases to above

#define sumx sm
#define sumz sn
#define dubx dm
#define dubz dn
#define e dubz
#define spro dnsm
#define dpro sumz

// Total size to reserve on the stack

#define NSPACE 13*NUMSIZE

// Macros wrapping up the basic field operation calls
// bignum_mul_p25519_alt and bignum_sqr_p25519_alt.
// These two are only trivially different from pure
// function calls to those subroutines.

#define mul_p25519(P0,P1,P2)                    \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2];                 \
        mov     r8,rax;                         \
        mov     r9,rdx;                         \
        xor     r10,r10;                        \
        xor     r11,r11;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x8];             \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2];                 \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        adc     r11,0x0;                        \
        xor     r12,r12;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x10];            \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        adc     r12,r12;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x8];             \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        adc     r12,0x0;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2];                 \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        adc     r12,0x0;                        \
        xor     r13,r13;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x18];            \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,r13;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x10];            \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,0x0;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x8];             \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2];                 \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,0x0;                        \
        xor     r14,r14;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x18];            \
        add     r12,rax;                        \
        adc     r13,rdx;                        \
        adc     r14,r14;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r12,rax;                        \
        adc     r13,rdx;                        \
        adc     r14,0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x8];             \
        add     r12,rax;                        \
        adc     r13,rdx;                        \
        adc     r14,0x0;                        \
        xor     r15,r15;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r13,rax;                        \
        adc     r14,rdx;                        \
        adc     r15,r15;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r13,rax;                        \
        adc     r14,rdx;                        \
        adc     r15,0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r14,rax;                        \
        adc     r15,rdx;                        \
        mov     esi,0x26;                       \
        mov     rax,r12;                        \
        mul     rsi;                            \
        add     r8,rax;                         \
        adc     r9,rdx;                         \
        sbb     rcx,rcx;                        \
        mov     rax,r13;                        \
        mul     rsi;                            \
        sub     rdx,rcx;                        \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        sbb     rcx,rcx;                        \
        mov     rax,r14;                        \
        mul     rsi;                            \
        sub     rdx,rcx;                        \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        sbb     rcx,rcx;                        \
        mov     rax,r15;                        \
        mul     rsi;                            \
        sub     rdx,rcx;                        \
        xor     rcx,rcx;                        \
        add     r11,rax;                        \
        mov     r12,rdx;                        \
        adc     r12,rcx;                        \
        shld    r12,r11,0x1;                    \
        lea     rax,[r12+0x1];                  \
        mov     esi,0x13;                       \
        bts     r11,63;                         \
        imul    rax,rsi;                        \
        add     r8,rax;                         \
        adc     r9,rcx;                         \
        adc     r10,rcx;                        \
        adc     r11,rcx;                        \
        sbb     rax,rax;                        \
        not     rax;                            \
        and     rax,rsi;                        \
        sub     r8,rax;                         \
        sbb     r9,rcx;                         \
        sbb     r10,rcx;                        \
        sbb     r11,rcx;                        \
        btr     r11,63;                         \
        mov     [P0],r8;                        \
        mov     [P0+0x8],r9;                    \
        mov     [P0+0x10],r10;                  \
        mov     [P0+0x18],r11

#define sqr_p25519(P0,P1)                       \
        mov     rax, [P1];                      \
        mul     rax;                            \
        mov     r8,rax;                         \
        mov     r9,rdx;                         \
        xor     r10,r10;                        \
        xor     r11,r11;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x8];             \
        add     rax,rax;                        \
        adc     rdx,rdx;                        \
        adc     r11,0x0;                        \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        adc     r11,0x0;                        \
        xor     r12,r12;                        \
        mov     rax, [P1+0x8];                  \
        mul     rax;                            \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        adc     r12,0x0;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x10];            \
        add     rax,rax;                        \
        adc     rdx,rdx;                        \
        adc     r12,0x0;                        \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        adc     r12,0x0;                        \
        xor     r13,r13;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x18];            \
        add     rax,rax;                        \
        adc     rdx,rdx;                        \
        adc     r13,0x0;                        \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,0x0;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x10];            \
        add     rax,rax;                        \
        adc     rdx,rdx;                        \
        adc     r13,0x0;                        \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,0x0;                        \
        xor     r14,r14;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x18];            \
        add     rax,rax;                        \
        adc     rdx,rdx;                        \
        adc     r14,0x0;                        \
        add     r12,rax;                        \
        adc     r13,rdx;                        \
        adc     r14,0x0;                        \
        mov     rax, [P1+0x10];                 \
        mul     rax;                            \
        add     r12,rax;                        \
        adc     r13,rdx;                        \
        adc     r14,0x0;                        \
        xor     r15,r15;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P1+0x18];            \
        add     rax,rax;                        \
        adc     rdx,rdx;                        \
        adc     r15,0x0;                        \
        add     r13,rax;                        \
        adc     r14,rdx;                        \
        adc     r15,0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     rax;                            \
        add     r14,rax;                        \
        adc     r15,rdx;                        \
        mov     esi,0x26;                       \
        mov     rax,r12;                        \
        mul     rsi;                            \
        add     r8,rax;                         \
        adc     r9,rdx;                         \
        sbb     rcx,rcx;                        \
        mov     rax,r13;                        \
        mul     rsi;                            \
        sub     rdx,rcx;                        \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        sbb     rcx,rcx;                        \
        mov     rax,r14;                        \
        mul     rsi;                            \
        sub     rdx,rcx;                        \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        sbb     rcx,rcx;                        \
        mov     rax,r15;                        \
        mul     rsi;                            \
        sub     rdx,rcx;                        \
        xor     rcx,rcx;                        \
        add     r11,rax;                        \
        mov     r12,rdx;                        \
        adc     r12,rcx;                        \
        shld    r12,r11,0x1;                    \
        lea     rax,[r12+0x1];                  \
        mov     esi,0x13;                       \
        bts     r11,63;                         \
        imul    rax,rsi;                        \
        add     r8,rax;                         \
        adc     r9,rcx;                         \
        adc     r10,rcx;                        \
        adc     r11,rcx;                        \
        sbb     rax,rax;                        \
        not     rax;                            \
        and     rax,rsi;                        \
        sub     r8,rax;                         \
        sbb     r9,rcx;                         \
        sbb     r10,rcx;                        \
        sbb     r11,rcx;                        \
        btr     r11,63;                         \
        mov     [P0],r8;                        \
        mov     [P0+0x8],r9;                    \
        mov     [P0+0x10],r10;                  \
        mov     [P0+0x18],r11

// Multiplication just giving a 5-digit result (actually < 39 * p_25519)
// by not doing anything beyond the first stage of reduction

#define mul_5(P0,P1,P2)                         \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2];                 \
        mov     r8,rax;                         \
        mov     r9,rdx;                         \
        xor     r10,r10;                        \
        xor     r11,r11;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x8];             \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2];                 \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        adc     r11,0x0;                        \
        xor     r12,r12;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x10];            \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        adc     r12,r12;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x8];             \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        adc     r12,0x0;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2];                 \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        adc     r12,0x0;                        \
        xor     r13,r13;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x18];            \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,r13;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x10];            \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,0x0;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x8];             \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2];                 \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,0x0;                        \
        xor     r14,r14;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x18];            \
        add     r12,rax;                        \
        adc     r13,rdx;                        \
        adc     r14,r14;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r12,rax;                        \
        adc     r13,rdx;                        \
        adc     r14,0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x8];             \
        add     r12,rax;                        \
        adc     r13,rdx;                        \
        adc     r14,0x0;                        \
        xor     r15,r15;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r13,rax;                        \
        adc     r14,rdx;                        \
        adc     r15,r15;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r13,rax;                        \
        adc     r14,rdx;                        \
        adc     r15,0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r14,rax;                        \
        adc     r15,rdx;                        \
        mov     esi,0x26;                       \
        mov     rax,r12;                        \
        mul     rsi;                            \
        add     r8,rax;                         \
        adc     r9,rdx;                         \
        sbb     rcx,rcx;                        \
        mov     rax,r13;                        \
        mul     rsi;                            \
        sub     rdx,rcx;                        \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        sbb     rcx,rcx;                        \
        mov     rax,r14;                        \
        mul     rsi;                            \
        sub     rdx,rcx;                        \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        sbb     rcx,rcx;                        \
        mov     rax,r15;                        \
        mul     rsi;                            \
        sub     rdx,rcx;                        \
        xor     rcx,rcx;                        \
        add     r11,rax;                        \
        mov     r12,rdx;                        \
        adc     r12,rcx;                        \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11;                 \
        mov     [P0+0x20], r12

// Squaring just giving a result < 2 * p_25519, which is done by
// basically skipping the +1 in the quotient estimate and the final
// optional correction.

#define sqr_4(P0,P1)                            \
        mov     rax, [P1];                      \
        mul     rax;                            \
        mov     r8,rax;                         \
        mov     r9,rdx;                         \
        xor     r10,r10;                        \
        xor     r11,r11;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x8];             \
        add     rax,rax;                        \
        adc     rdx,rdx;                        \
        adc     r11,0x0;                        \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        adc     r11,0x0;                        \
        xor     r12,r12;                        \
        mov     rax, [P1+0x8];                  \
        mul     rax;                            \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        adc     r12,0x0;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x10];            \
        add     rax,rax;                        \
        adc     rdx,rdx;                        \
        adc     r12,0x0;                        \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        adc     r12,0x0;                        \
        xor     r13,r13;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x18];            \
        add     rax,rax;                        \
        adc     rdx,rdx;                        \
        adc     r13,0x0;                        \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,0x0;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x10];            \
        add     rax,rax;                        \
        adc     rdx,rdx;                        \
        adc     r13,0x0;                        \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,0x0;                        \
        xor     r14,r14;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x18];            \
        add     rax,rax;                        \
        adc     rdx,rdx;                        \
        adc     r14,0x0;                        \
        add     r12,rax;                        \
        adc     r13,rdx;                        \
        adc     r14,0x0;                        \
        mov     rax, [P1+0x10];                 \
        mul     rax;                            \
        add     r12,rax;                        \
        adc     r13,rdx;                        \
        adc     r14,0x0;                        \
        xor     r15,r15;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P1+0x18];            \
        add     rax,rax;                        \
        adc     rdx,rdx;                        \
        adc     r15,0x0;                        \
        add     r13,rax;                        \
        adc     r14,rdx;                        \
        adc     r15,0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     rax;                            \
        add     r14,rax;                        \
        adc     r15,rdx;                        \
        mov     esi,0x26;                       \
        mov     rax,r12;                        \
        mul     rsi;                            \
        add     r8,rax;                         \
        adc     r9,rdx;                         \
        sbb     rcx,rcx;                        \
        mov     rax,r13;                        \
        mul     rsi;                            \
        sub     rdx,rcx;                        \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        sbb     rcx,rcx;                        \
        mov     rax,r14;                        \
        mul     rsi;                            \
        sub     rdx,rcx;                        \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        sbb     rcx,rcx;                        \
        mov     rax,r15;                        \
        mul     rsi;                            \
        sub     rdx,rcx;                        \
        xor     rcx,rcx;                        \
        add     r11,rax;                        \
        mov     r12,rdx;                        \
        adc     r12,rcx;                        \
        shld    r12, r11, 0x1;                  \
        btr     r11, 0x3f;                      \
        mov     edx, 0x13;                      \
        imul    rdx, r12;                       \
        add     r8, rdx;                        \
        adc     r9, rcx;                        \
        adc     r10, rcx;                       \
        adc     r11, rcx;                       \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11

// Plain 4-digit add without any normalization
// With inputs < p_25519 (indeed < 2^255) it still gives a 4-digit result

#define add_4(P0,P1,P2)                         \
        mov     rax, [P1];                      \
        add     rax, [P2];                      \
        mov     [P0], rax;                      \
        mov     rax, [P1+8];                    \
        adc     rax, [P2+8];                    \
        mov     [P0+8], rax;                    \
        mov     rax, [P1+16];                   \
        adc     rax, [P2+16];                   \
        mov     [P0+16], rax;                   \
        mov     rax, [P1+24];                   \
        adc     rax, [P2+24];                   \
        mov     [P0+24], rax

// Add 5-digit inputs and normalize to 4 digits

#define add5_4(P0,P1,P2)                        \
        mov     r8, [P1];                       \
        add     r8, [P2];                       \
        mov     r9, [P1+8];                     \
        adc     r9, [P2+8];                     \
        mov     r10, [P1+16];                   \
        adc     r10, [P2+16];                   \
        mov     r11, [P1+24];                   \
        adc     r11, [P2+24];                   \
        mov     r12, [P1+32];                   \
        adc     r12, [P2+32];                   \
        xor     ebx, ebx;                       \
        shld   r12, r11, 0x1;                   \
        btr    r11, 0x3f;                       \
        mov    edx, 0x13;                       \
        imul   rdx, r12;                        \
        add    r8, rdx;                         \
        adc    r9, rbx;                         \
        adc    r10, rbx;                        \
        adc    r11, rbx;                        \
        mov    [P0], r8;                        \
        mov    [P0+0x8], r9;                    \
        mov    [P0+0x10], r10;                  \
        mov    [P0+0x18], r11

// Subtraction of a pair of numbers < p_25519 just sufficient
// to give a 4-digit result. It actually always does (x - z) + (2^255-19)
// which in turn is done by (x - z) - (2^255+19) discarding the 2^256
// implicitly

#define sub_4(P0,P1,P2)                         \
        mov     r8, [P1];                       \
        sub     r8, [P2];                       \
        mov     r9, [P1+8];                     \
        sbb     r9, [P2+8];                     \
        mov     r10, [P1+16];                   \
        sbb     r10, [P2+16];                   \
        mov     rax, [P1+24];                   \
        sbb     rax, [P2+24];                   \
        sub     r8, 19;                         \
        mov     [P0], r8;                       \
        sbb     r9, 0;                          \
        mov     [P0+8], r9;                     \
        sbb     r10, 0;                         \
        mov     [P0+16], r10;                   \
        sbb     rax, 0;                         \
        btc     rax, 63;                        \
        mov     [P0+24], rax

// Modular subtraction with double modulus 2 * p_25519 = 2^256 - 38

#define sub_twice4(P0,P1,P2)                    \
        mov     r8, [P1];                       \
        xor     ebx, ebx;                       \
        sub     r8, [P2];                       \
        mov     r9, [P1+8];                     \
        sbb     r9, [P2+8];                     \
        mov     ecx, 38;                        \
        mov     r10, [P1+16];                   \
        sbb     r10, [P2+16];                   \
        mov     rax, [P1+24];                   \
        sbb     rax, [P2+24];                   \
        cmovnc  rcx, rbx;                       \
        sub     r8, rcx;                        \
        sbb     r9, rbx;                        \
        sbb     r10, rbx;                       \
        sbb     rax, rbx;                       \
        mov     [P0], r8;                       \
        mov     [P0+8], r9;                     \
        mov     [P0+16], r10;                   \
        mov     [P0+24], rax

// 5-digit subtraction with upward bias to make it positive, adding
// 1000 * (2^255 - 19) = 2^256 * 500 - 19000, then normalizing to 4 digits

#define sub5_4(P0,P1,P2)                        \
        mov     r8, [P1];                       \
        sub     r8, [P2];                       \
        mov     r9, [P1+8];                     \
        sbb     r9, [P2+8];                     \
        mov     r10, [P1+16];                   \
        sbb     r10, [P2+16];                   \
        mov     r11, [P1+24];                   \
        sbb     r11, [P2+24];                   \
        mov     r12, [P1+32];                   \
        sbb     r12, [P2+32];                   \
        xor     ebx, ebx;                       \
        sub     r8, 19000;                      \
        sbb     r9, rbx;                        \
        sbb     r10, rbx;                       \
        sbb     r11, rbx;                       \
        sbb     r12, rbx;                       \
        add     r12, 500;                       \
        shld    r12, r11, 0x1;                  \
        btr     r11, 0x3f;                      \
        mov     edx, 0x13;                      \
        imul    rdx, r12;                       \
        add     r8, rdx;                        \
        adc     r9, rbx;                        \
        adc     r10, rbx;                       \
        adc     r11, rbx;                       \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11

// Combined z = c * x + y with reduction only < 2 * p_25519
// It is assumed that 19 * (c * x + y) < 2^60 * 2^256 so we
// don't need a high mul in the final part.

#define cmadd_4(P0,C1,P2,P3)                    \
        mov     rsi,C1;                         \
        mov     rax,[P2];                       \
        mul     rsi;                            \
        mov     r8,rax;                         \
        mov     r9,rdx;                         \
        mov     rax,[P2+0x8];                   \
        xor     r10,r10;                        \
        mul     rsi;                            \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        mov     rax,[P2+0x10];                  \
        mul     rsi;                            \
        add     r10,rax;                        \
        adc     rdx,0x0;                        \
        mov     rax,[P2+0x18];                  \
        mov     r11,rdx;                        \
        mul     rsi;                            \
        xor     esi,esi;                        \
        add     r11,rax;                        \
        adc     rdx,rsi;                        \
        add     r8,[P3];                        \
        adc     r9,[P3+0x8];                    \
        adc     r10,[P3+0x10];                  \
        adc     r11,[P3+0x18];                  \
        adc     rdx,rsi;                        \
        shld    rdx, r11, 0x1;                  \
        btr     r11, 63;                        \
        mov     ebx, 0x13;                      \
        imul    rdx, rbx;                       \
        add     r8, rdx;                        \
        adc     r9, rsi;                        \
        adc     r10, rsi;                       \
        adc     r11, rsi;                       \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11

// Multiplex: z := if NZ then x else y

#define mux_4(P0,P1,P2)                         \
        mov     rax, [P1];                      \
        mov     rcx, [P2];                      \
        cmovz   rax, rcx;                       \
        mov     [P0], rax;                      \
        mov     rax, [P1+8];                    \
        mov     rcx, [P2+8];                    \
        cmovz   rax, rcx;                       \
        mov     [P0+8], rax;                    \
        mov     rax, [P1+16];                   \
        mov     rcx, [P2+16];                   \
        cmovz   rax, rcx;                       \
        mov     [P0+16], rax;                   \
        mov     rax, [P1+24];                   \
        mov     rcx, [P2+24];                   \
        cmovz   rax, rcx;                       \
        mov     [P0+24], rax

// Paired multiplex: (w,z) := if NZ then (y,x) else (x,y)

#define muxpair_4(P0,P1,P2,P3)                  \
        mov     rax, [P2];                      \
        mov     rcx, [P3];                      \
        mov     rdx, rax;                       \
        cmovnz  rax, rcx;                       \
        cmovnz  rcx, rdx;                       \
        mov     [P0], rax;                      \
        mov     [P1], rcx;                      \
        mov     rax, [P2+8];                    \
        mov     rcx, [P3+8];                    \
        mov     rdx, rax;                       \
        cmovnz  rax, rcx;                       \
        cmovnz  rcx, rdx;                       \
        mov     [P0+8], rax;                    \
        mov     [P1+8], rcx;                    \
        mov     rax, [P2+16];                   \
        mov     rcx, [P3+16];                   \
        mov     rdx, rax;                       \
        cmovnz  rax, rcx;                       \
        cmovnz  rcx, rdx;                       \
        mov     [P0+16], rax;                   \
        mov     [P1+16], rcx;                   \
        mov     rax, [P2+24];                   \
        mov     rcx, [P3+24];                   \
        mov     rdx, rax;                       \
        cmovnz  rax, rcx;                       \
        cmovnz  rcx, rdx;                       \
        mov     [P0+24], rax;                   \
        mov     [P1+24], rcx

S2N_BN_SYMBOL(curve25519_ladderstep_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
#endif

// Save registers, make room for temps, preserve input arguments.

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

        CFI_DEC_RSP(NSPACE)

        mov     rr, rdi
        mov     point, rsi
        mov     bb, rcx

// sm = xm + zm; sn = xn + zn; dm = xm - zm; dn = xn - zn
// The adds don't need any normalization as they're fed to muls
// Just make sure the subs fit in 4 digits. Keep pp in rdx
// here, after which we can forget about it.

        sub_4(dm,xm,zm)
        add_4(sn,xn,zn)
        sub_4(dn,xn,zn)
        add_4(sm,xm,zm)

// ADDING: dmsn = dm * sn; dnsm = sm * dn
// DOUBLING: mux d = xt - zt and s = xt + zt for appropriate choice of (xt,zt)

        mul_5(dmsn,dm,sn)

        mov     rax, bb
        test    rax, rax
        mux_4(d,dm,dn)
        mux_4(s,sm,sn)

        mul_5(dnsm,sm,dn)

// DOUBLING: d = (xt - zt)^2 normalized only to 4 digits

        sqr_4(d,d)

// ADDING: dpro = (dmsn - dnsm)^2, spro = (dmsn + dnsm)^2
// DOUBLING: s = (xt + zt)^2, normalized only to 4 digits

        sub5_4(dpro,dmsn,dnsm)
        sqr_4(s,s)
        add5_4(spro,dmsn,dnsm)
        sqr_4(dpro,dpro)

// DOUBLING: p = 4 * xt * zt = s - d

        sub_twice4(p,s,d)

// ADDING: sumx = (dmsn + dnsm)^2

        sqr_p25519(sumx,spro)

// DOUBLING: e = 121666 * p + d

        cmadd_4(e,0x1db42,p,d)

// DOUBLING: dubx = (xt + zt)^2 * (xt - zt)^2 = s * d

        mul_p25519(dubx,s,d)

// ADDING: sumz = x * (dmsn - dnsm)^2

        mov     rbp, point
        mul_p25519(sumz,dpro,point_x)

// DOUBLING: dubz = (4 * xt * zt) * ((xt - zt)^2 + 121666 * (4 * xt * zt))
//                = p * (d + 121666 * p)

        mul_p25519(dubz,p,e)

// Multiplex the outputs

        mov     rax, bb
        mov     rbp, rr
        test    rax, rax
        muxpair_4(res0,res2,dubx,sumx)
        muxpair_4(res1,res3,dubz,sumz)

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

S2N_BN_SIZE_DIRECTIVE(curve25519_ladderstep_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
