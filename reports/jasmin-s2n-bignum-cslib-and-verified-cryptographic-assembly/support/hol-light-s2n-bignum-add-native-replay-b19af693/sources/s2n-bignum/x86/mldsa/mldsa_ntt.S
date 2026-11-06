// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Forward number-theoretic transform for ML-DSA
// Input a[256], zetas (all signed 32-bit words); output a[256] (signed 32-bit words)
//
// The transform is in-place with input and output a[256], with the output
// in bitreversed order. Computes the forward NTT of a polynomial in place,
// transforming from coefficient representation to NTT representation. The input
// polynomial a is a 256-element array of signed 32-bit integers representing
// coefficients in normal order, assumed to be coefficient-wise bound by MLDSA_Q
// (8380417) in absolute value. The zetas parameter points to precomputed twiddle
// factors (roots of unity and their Montgomery inverses) required for the NTT
// computation. The output polynomial is in bitreversed order and coefficient-wise
// bound by 42035261 (just over 5*Q) in absolute value. Output coefficients are
// congruent to the mathematical NTT result modulo Q but are not fully reduced.
//
// The implementation uses Montgomery arithmetic for efficient modular reduction
// modulo Q = 8380417, maintaining constant-time execution for side-channel
// resistance. The transform operates in the ring R_Q = Z_Q[x]/(x^256 + 1).
//
// extern void mldsa_ntt(int32_t a[static 256], const int32_t zetas[static 624]);
//
// Standard x86-64 ABI: RDI = a, RSI = zetas
// Microsoft x64 ABI:   RCX = a, RDX = zetas
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_ntt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mldsa_ntt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_ntt)
        .text

#define a rdi
#define zetas rsi

#define MLD_AVX2_BACKEND_DATA_OFFSET_8XQ 0
#define MLD_AVX2_BACKEND_DATA_OFFSET_8XQINV 8
#define MLD_AVX2_BACKEND_DATA_OFFSET_8XDIV_QINV 16
#define MLD_AVX2_BACKEND_DATA_OFFSET_8XDIV 24
#define MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV 32
#define MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS 328

.macro shuffle8 r0,r1,r2,r3
        vperm2i128      \r2,\r0,\r1,0x20
        vperm2i128      \r3,\r0,\r1,0x31
.endm

.macro shuffle4 r0,r1,r2,r3
        vpunpcklqdq     \r2,\r0,\r1
        vpunpckhqdq     \r3,\r0,\r1
.endm

.macro shuffle2 r0,r1,r2,r3
        vmovsldup       \r2,\r1
        vpblendd        \r2,\r0,\r2,0xAA
        vpsrlq          \r0,\r0,32
        vpblendd        \r3,\r0,\r1,0xAA
.endm

.macro butterfly l,h,zl0=ymm1,zl1=ymm1,zh0=ymm2,zh1=ymm2
        vpmuldq         ymm13,\h,\zl0
        vmovshdup       ymm12,\h
        vpmuldq         ymm14,ymm12,\zl1

        vpmuldq         \h,\h,\zh0
        vpmuldq         ymm12,ymm12,\zh1

        vpmuldq         ymm13,ymm13,ymm0
        vpmuldq         ymm14,ymm14,ymm0

        vmovshdup       \h,\h
        vpblendd        \h,\h,ymm12,0xAA

        vpsubd          ymm12,\l,\h
        vpaddd          \l,\l,\h

        vmovshdup       ymm13,ymm13
        vpblendd        ymm13,ymm13,ymm14,0xAA

        vpaddd          \h,ymm12,ymm13
        vpsubd          \l,\l,ymm13
.endm

.macro levels0t1 off
        /* level 0 */
        vpbroadcastd    ymm1, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+1))]
        vpbroadcastd    ymm2, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+1))]

        vmovdqa         ymm4, [rdi+0+32*\off]
        vmovdqa         ymm5, [rdi+128+32*\off]
        vmovdqa         ymm6, [rdi+256+32*\off]
        vmovdqa         ymm7, [rdi+384+32*\off]
        vmovdqa         ymm8, [rdi+512+32*\off]
        vmovdqa         ymm9, [rdi+640+32*\off]
        vmovdqa         ymm10, [rdi+768+32*\off]
        vmovdqa         ymm11, [rdi+896+32*\off]

        butterfly       ymm4,ymm8
        butterfly       ymm5,ymm9
        butterfly       ymm6,ymm10
        butterfly       ymm7,ymm11

        /* level 1 */
        vpbroadcastd    ymm1, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+2))]
        vpbroadcastd    ymm2, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+2))]
        butterfly       ymm4,ymm6
        butterfly       ymm5,ymm7

        vpbroadcastd    ymm1, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+3))]
        vpbroadcastd    ymm2, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+3))]
        butterfly       ymm8,ymm10
        butterfly       ymm9,ymm11

        vmovdqa         [rdi+0+32*\off],ymm4
        vmovdqa         [rdi+128+32*\off],ymm5
        vmovdqa         [rdi+256+32*\off],ymm6
        vmovdqa         [rdi+384+32*\off],ymm7
        vmovdqa         [rdi+512+32*\off],ymm8
        vmovdqa         [rdi+640+32*\off],ymm9
        vmovdqa         [rdi+768+32*\off],ymm10
        vmovdqa         [rdi+896+32*\off],ymm11
.endm

.macro levels2t7 off
        /* level 2 */
        vmovdqa         ymm4, [rdi+0+256*\off]
        vmovdqa         ymm5, [rdi+32+256*\off]
        vmovdqa         ymm6, [rdi+64+256*\off]
        vmovdqa         ymm7, [rdi+96+256*\off]
        vmovdqa         ymm8, [rdi+128+256*\off]
        vmovdqa         ymm9, [rdi+160+256*\off]
        vmovdqa         ymm10, [rdi+192+256*\off]
        vmovdqa         ymm11, [rdi+224+256*\off]
        vpbroadcastd    ymm1, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+4+\off))]
        vpbroadcastd    ymm2, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+4+\off))]

        butterfly       ymm4,ymm8
        butterfly       ymm5,ymm9
        butterfly       ymm6,ymm10
        butterfly       ymm7,ymm11

        shuffle8        ymm4,ymm8,ymm3,ymm8
        shuffle8        ymm5,ymm9,ymm4,ymm9
        shuffle8        ymm6,ymm10,ymm5,ymm10
        shuffle8        ymm7,ymm11,ymm6,ymm11

        /* level 3 */
        vmovdqa         ymm1, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+8+8*\off))]
        vmovdqa         ymm2, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+8+8*\off))]

        butterfly       ymm3,ymm5
        butterfly       ymm8,ymm10
        butterfly       ymm4,ymm6
        butterfly       ymm9,ymm11

        shuffle4        ymm3,ymm5,ymm7,ymm5
        shuffle4        ymm8,ymm10,ymm3,ymm10
        shuffle4        ymm4,ymm6,ymm8,ymm6
        shuffle4        ymm9,ymm11,ymm4,ymm11

        /* level 4 */
        vmovdqa         ymm1, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+40+8*\off))]
        vmovdqa         ymm2, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+40+8*\off))]

        butterfly       ymm7,ymm8
        butterfly       ymm5,ymm6
        butterfly       ymm3,ymm4
        butterfly       ymm10,ymm11

        shuffle2        ymm7,ymm8,ymm9,ymm8
        shuffle2        ymm5,ymm6,ymm7,ymm6
        shuffle2        ymm3,ymm4,ymm5,ymm4
        shuffle2        ymm10,ymm11,ymm3,ymm11

        /* level 5 */
        vmovdqa         ymm1, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+72+8*\off))]
        vmovdqa         ymm2, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+72+8*\off))]
        vpsrlq          ymm10,ymm1,32
        vmovshdup       ymm15,ymm2

        butterfly       ymm9,ymm5,ymm1,ymm10,ymm2,ymm15
        butterfly       ymm8,ymm4,ymm1,ymm10,ymm2,ymm15
        butterfly       ymm7,ymm3,ymm1,ymm10,ymm2,ymm15
        butterfly       ymm6,ymm11,ymm1,ymm10,ymm2,ymm15

        /* level 6 */
        vmovdqa         ymm1, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+104+8*\off))]
        vmovdqa         ymm2, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+104+8*\off))]
        vpsrlq          ymm10,ymm1,32
        vmovshdup       ymm15,ymm2
        butterfly       ymm9,ymm7,ymm1,ymm10,ymm2,ymm15
        butterfly       ymm8,ymm6,ymm1,ymm10,ymm2,ymm15

        vmovdqa         ymm1, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+104+8*\off+32))]
        vmovdqa         ymm2, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+104+8*\off+32))]
        vpsrlq          ymm10,ymm1,32
        vmovshdup       ymm15,ymm2
        butterfly       ymm5,ymm3,ymm1,ymm10,ymm2,ymm15
        butterfly       ymm4,ymm11,ymm1,ymm10,ymm2,ymm15

        /* level 7 */
        vmovdqa         ymm1, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+168+8*\off))]
        vmovdqa         ymm2, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+168+8*\off))]
        vpsrlq          ymm10,ymm1,32
        vmovshdup       ymm15,ymm2
        butterfly       ymm9,ymm8,ymm1,ymm10,ymm2,ymm15

        vmovdqa         ymm1, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+168+8*\off+32))]
        vmovdqa         ymm2, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+168+8*\off+32))]
        vpsrlq          ymm10,ymm1,32
        vmovshdup       ymm15,ymm2
        butterfly       ymm7,ymm6,ymm1,ymm10,ymm2,ymm15

        vmovdqa         ymm1, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+168+8*\off+64))]
        vmovdqa         ymm2, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+168+8*\off+64))]
        vpsrlq          ymm10,ymm1,32
        vmovshdup       ymm15,ymm2
        butterfly       ymm5,ymm4,ymm1,ymm10,ymm2,ymm15

        vmovdqa         ymm1, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+168+8*\off+96))]
        vmovdqa         ymm2, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+168+8*\off+96))]
        vpsrlq          ymm10,ymm1,32
        vmovshdup       ymm15,ymm2
        butterfly       ymm3,ymm11,ymm1,ymm10,ymm2,ymm15

        vmovdqa         [rdi+0+256*\off],ymm9
        vmovdqa         [rdi+32+256*\off],ymm8
        vmovdqa         [rdi+64+256*\off],ymm7
        vmovdqa         [rdi+96+256*\off],ymm6
        vmovdqa         [rdi+128+256*\off],ymm5
        vmovdqa         [rdi+160+256*\off],ymm4
        vmovdqa         [rdi+192+256*\off],ymm3
        vmovdqa         [rdi+224+256*\off],ymm11
.endm

S2N_BN_SYMBOL(mldsa_ntt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(176)
        CFI_STACKSAVEU(xmm6,0)
        CFI_STACKSAVEU(xmm7,16)
        CFI_STACKSAVEU(xmm8,32)
        CFI_STACKSAVEU(xmm9,48)
        CFI_STACKSAVEU(xmm10,64)
        CFI_STACKSAVEU(xmm11,80)
        CFI_STACKSAVEU(xmm12,96)
        CFI_STACKSAVEU(xmm13,112)
        CFI_STACKSAVEU(xmm14,128)
        CFI_STACKSAVEU(xmm15,144)
        CFI_STACKSAVE(rdi,160)
        CFI_STACKSAVE(rsi,168)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

        vmovdqa ymm0, [rsi+MLD_AVX2_BACKEND_DATA_OFFSET_8XQ*4]

        levels0t1 0
        levels0t1 1
        levels0t1 2
        levels0t1 3

        levels2t7 0
        levels2t7 1
        levels2t7 2
        levels2t7 3

#if WINDOWS_ABI
        CFI_STACKLOADU(xmm6,0)
        CFI_STACKLOADU(xmm7,16)
        CFI_STACKLOADU(xmm8,32)
        CFI_STACKLOADU(xmm9,48)
        CFI_STACKLOADU(xmm10,64)
        CFI_STACKLOADU(xmm11,80)
        CFI_STACKLOADU(xmm12,96)
        CFI_STACKLOADU(xmm13,112)
        CFI_STACKLOADU(xmm14,128)
        CFI_STACKLOADU(xmm15,144)
        CFI_STACKLOAD(rdi,160)
        CFI_STACKLOAD(rsi,168)
        CFI_INC_RSP(176)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mldsa_ntt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
