// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Projective doubling for edwards25519
// Input p1[12]; output p3[12]
//
// extern void edwards25519_pdouble_alt
//   (uint64_t p3[static 12],const uint64_t p1[static 12]);
//
// If p1 is a point on edwards25519, returns its double p3 = 2 * p1.
// Input and output are in pure projective coordinates, representing
// an affine (x,y) by a triple (X,Y,Z) where x = X / Z, y = Y / Z.
//
// Standard x86-64 ABI: RDI = p3, RSI = p1
// Microsoft x64 ABI:   RCX = p3, RDX = p1
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(edwards25519_pdouble_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(edwards25519_pdouble_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(edwards25519_pdouble_alt)
        .text

// Size of individual field elements

#define NUMSIZE 32

// Registers used for inputs and outputs within basic operations.
// Here p1 and p3 are where the parameters come in anyway.

#define p3 rdi
#define p1 rsi

// Pointers to input and output coordinates

#define x_1 p1+0
#define y_1 p1+NUMSIZE
#define z_1 p1+(2*NUMSIZE)

#define x_3 p3+0
#define y_3 p3+NUMSIZE
#define z_3 p3+(2*NUMSIZE)

// Pointer-offset pairs for temporaries on stack

#define t0 rsp+(0*NUMSIZE)
#define t1 rsp+(1*NUMSIZE)
#define t2 rsp+(2*NUMSIZE)
#define t3 rsp+(3*NUMSIZE)
#define t4 rsp+(4*NUMSIZE)

// Total size to reserve on the stack

#define NSPACE 5*NUMSIZE

// Macro wrapping up the basic field multiplication, only trivially
// different from a pure function call to bignum_mul_p25519_alt.

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
        mov     ebx,0x26;                       \
        mov     rax,r12;                        \
        mul     rbx;                            \
        add     r8,rax;                         \
        adc     r9,rdx;                         \
        sbb     rcx,rcx;                        \
        mov     rax,r13;                        \
        mul     rbx;                            \
        sub     rdx,rcx;                        \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        sbb     rcx,rcx;                        \
        mov     rax,r14;                        \
        mul     rbx;                            \
        sub     rdx,rcx;                        \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        sbb     rcx,rcx;                        \
        mov     rax,r15;                        \
        mul     rbx;                            \
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
// With inputs < p_25519 (indeed < 2^255) it still gives a 4-digit result,
// indeed one < 2 * p_25519 for normalized inputs.

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

// Modular addition and doubling with double modulus 2 * p_25519 = 2^256 - 38.
// This only ensures that the result fits in 4 digits, not that it is reduced
// even w.r.t. double modulus. The result is always correct modulo provided
// the sum of the inputs is < 2^256 + 2^256 - 38, so in particular provided
// at least one of them is reduced double modulo.

#define add_twice4(P0,P1,P2)                    \
        mov     r8, [P1];                       \
        xor     ecx, ecx;                       \
        add     r8, [P2];                       \
        mov     r9, [P1+0x8];                   \
        adc     r9, [P2+0x8];                   \
        mov     r10, [P1+0x10];                 \
        adc     r10, [P2+0x10];                 \
        mov     r11, [P1+0x18];                 \
        adc     r11, [P2+0x18];                 \
        mov     eax, 38;                        \
        cmovnc  rax, rcx;                       \
        add     r8, rax;                        \
        adc     r9, rcx;                        \
        adc     r10, rcx;                       \
        adc     r11, rcx;                       \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11

#define double_twice4(P0,P1)                    \
        mov     r8, [P1];                       \
        xor     ecx, ecx;                       \
        add     r8, r8;                         \
        mov     r9, [P1+0x8];                   \
        adc     r9, r9;                         \
        mov     r10, [P1+0x10];                 \
        adc     r10, r10;                       \
        mov     r11, [P1+0x18];                 \
        adc     r11, r11;                       \
        mov     eax, 38;                        \
        cmovnc  rax, rcx;                       \
        add     r8, rax;                        \
        adc     r9, rcx;                        \
        adc     r10, rcx;                       \
        adc     r11, rcx;                       \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11

S2N_BN_SYMBOL(edwards25519_pdouble_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Save registers, make room for temps, preserve input arguments.

        CFI_PUSH(rbx)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

        CFI_DEC_RSP(NSPACE)

// Main sequence

        add_4(t0,x_1,y_1)
        sqr_4(t1,z_1)
        sqr_4(t2,x_1)
        sqr_4(t3,y_1)
        double_twice4(t1,t1)
        sqr_4(t0,t0)
        add_twice4(t4,t2,t3)
        sub_twice4(t2,t2,t3)
        add_twice4(t3,t1,t2)
        sub_twice4(t1,t4,t0)
        mul_p25519(y_3,t2,t4)
        mul_p25519(z_3,t3,t2)
        mul_p25519(x_3,t1,t3)

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

S2N_BN_SIZE_DIRECTIVE(edwards25519_pdouble_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
