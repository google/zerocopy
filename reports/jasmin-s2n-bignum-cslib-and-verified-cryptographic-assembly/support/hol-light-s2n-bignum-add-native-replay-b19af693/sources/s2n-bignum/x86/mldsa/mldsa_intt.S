// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Inverse number-theoretic transform for ML-DSA
// Input a[256], zetas (all signed 32-bit words); output a[256] (signed 32-bit words)
//
// The transform is in-place with input and output a[256]. Computes the inverse
// NTT of a polynomial in place, transforming from NTT representation to coefficient
// representation. The input polynomial a is a 256-element array of signed 32-bit
// integers representing coefficients in NTT domain, with each coefficient bounded
// by |a[i]| < Q. The zetas parameter points to precomputed twiddle factors
// (roots of unity and their Montgomery inverses) required for the inverse NTT
// computation.
//
// The output polynomial is in coefficient representation (normal order) with
// coefficients in Montgomery form, each bounded by |a[i]| < Q.
// The inverse NTT includes the division by 256 (the transform size) and maps the
// result to Montgomery domain via multiplication by 2^32/256 = 2^24.
//
// The implementation uses Montgomery arithmetic for efficient modular reduction
// modulo Q = 8380417, maintaining constant-time execution for side-channel
// resistance. The transform operates in the ring R_Q = Z_Q[x]/(x^256 + 1).
//
// extern void mldsa_intt(int32_t a[static 256], const int32_t zetas[static 624]);
//
// Standard x86-64 ABI: RDI = a, RSI = zetas
// Microsoft x64 ABI:   RCX = a, RDX = zetas
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_intt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mldsa_intt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_intt)
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

/*
 * Compute l' = l + h, h' = montmul(h - l, zh)
 *
 * Bounds: |l'| <= |l| + |h|
 *         |h'| < MONTMUL_BOUND
 *         (See the end of this file for the exact value of MONTMUL_BOUND)
 *
 * The flip parameter controls VEX encoding optimization for platform-independent
 * code. Set flip=1 when h is in ymm0-7 and l is in ymm8-15 to enable the 2-byte
 * VEX encoding; otherwise set flip=0.
 *
 * VEX Encoding Optimization for Platform-Independent Code
 *
 * Some assemblers (notably clang) will automatically swap operands of
 * commutative instructions like VPADDD to use shorter encodings, while others
 * (like gcc) may not. This causes different machine code across platforms.
 *
 * VEX prefixes come in two forms:
 * - 2-byte VEX (0xC5): Can only be used when the ModR/M.rm operand is ymm0-7
 * - 3-byte VEX (0xC4): Required when ModR/M.rm operand is ymm8-15
 *
 * When one operand is in ymm0-7 and another is in ymm8-15, we explicitly
 * place the lower-numbered register (ymm0-7) as the second source operand
 * to enable the 2-byte VEX encoding. Since VPADDD is commutative, this
 * produces identical results while ensuring consistent machine code across
 * different assemblers.
 *
 * Example:
 *   VPADDD ymm4, ymm4, ymm8  -> 3-byte VEX (0xC4 0xC1 0x5D 0xFE 0xE0)
 *   VPADDD ymm4, ymm8, ymm4  -> 2-byte VEX (0xC5 0xBD 0xFE 0xE4) preferred
 */
.macro butterfly flip,l,h,zl0=ymm1,zl1=ymm1,zh0=ymm2,zh1=ymm2
        vpsubd          ymm12,\h,\l
.if \flip
        vpaddd          \l,\l,\h
.else
        vpaddd          \l,\h,\l
.endif

        vpmuldq         ymm13,ymm12,\zl0
        vmovshdup       \h,ymm12
        vpmuldq         ymm14,\h,\zl1

        vpmuldq         ymm12,ymm12,\zh0
        vpmuldq         \h,\h,\zh1

        vpmuldq         ymm13,ymm13,ymm0
        vpmuldq         ymm14,ymm14,ymm0

        vpsubd          ymm12,ymm12,ymm13
        vpsubd          \h,\h,ymm14

        vmovshdup       ymm12,ymm12
        vpblendd        \h,ymm12,\h,0xAA
.endm

.macro levels0t5 off
        vmovdqa         ymm4, [rdi+256*\off+0]
        vmovdqa         ymm5, [rdi+256*\off+32]
        vmovdqa         ymm6, [rdi+256*\off+64]
        vmovdqa         ymm7, [rdi+256*\off+96]
        vmovdqa         ymm8, [rdi+256*\off+128]
        vmovdqa         ymm9, [rdi+256*\off+160]
        vmovdqa         ymm10, [rdi+256*\off+192]
        vmovdqa         ymm11, [rdi+256*\off+224]

        /* Bounds: |ymm{i}| < q for i in 4...11 */

        /* level 0 */
        vpermq          ymm3, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+296-8*\off-8))], 0x1B
        vpermq          ymm15, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+296-8*\off-8))], 0x1B
        vmovshdup       ymm1,ymm3
        vmovshdup       ymm2,ymm15
        butterfly       0,ymm4,ymm5,ymm1,ymm3,ymm2,ymm15

        vpermq          ymm3, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+296-8*\off-40))], 0x1B
        vpermq          ymm15, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+296-8*\off-40))], 0x1B
        vmovshdup       ymm1,ymm3
        vmovshdup       ymm2,ymm15
        butterfly       0,ymm6,ymm7,ymm1,ymm3,ymm2,ymm15

        vpermq          ymm3, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+296-8*\off-72))], 0x1B
        vpermq          ymm15, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+296-8*\off-72))], 0x1B
        vmovshdup       ymm1,ymm3
        vmovshdup       ymm2,ymm15
        butterfly       0,ymm8,ymm9,ymm1,ymm3,ymm2,ymm15

        vpermq          ymm3, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+296-8*\off-104))], 0x1B
        vpermq          ymm15, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+296-8*\off-104))], 0x1B
        vmovshdup       ymm1,ymm3
        vmovshdup       ymm2,ymm15
        butterfly       0,ymm10,ymm11,ymm1,ymm3,ymm2,ymm15

        /*
         * Bounds: |ymm{i}| < 2q            for i in 4, 6, 8, 10
         *                  < MONTMUL_BOUND for i in 5, 7, 9, 11
         *
         * Note that since 2^31 / q > 256, the sum of all 256 coefficients does not
         * overflow. This allows us to greatly simplify the range analysis by relaxing
         * and unifying the bounds of all coefficients on the same layer. As a concrete
         * example, here we relax the bounds on 5, 7, 9, 11 and conclude that (for all
         * relevant i)
         *
         * Bounds: |ymm{i}| < 2q
         *
         * In all but last of the following levels of butterflies, we do the same
         * relaxation without explicit mention.
         */

        /* level 1 */
        vpermq          ymm3, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+168-8*\off-8))], 0x1B
        vpermq          ymm15, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+168-8*\off-8))], 0x1B
        vmovshdup       ymm1,ymm3
        vmovshdup       ymm2,ymm15
        butterfly       0,ymm4,ymm6,ymm1,ymm3,ymm2,ymm15
        butterfly       0,ymm5,ymm7,ymm1,ymm3,ymm2,ymm15

        vpermq          ymm3, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+168-8*\off-40))], 0x1B
        vpermq          ymm15, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+168-8*\off-40))], 0x1B
        vmovshdup       ymm1,ymm3
        vmovshdup       ymm2,ymm15
        butterfly       0,ymm8,ymm10,ymm1,ymm3,ymm2,ymm15
        butterfly       0,ymm9,ymm11,ymm1,ymm3,ymm2,ymm15

        /* Bounds: |ymm{i}| < 4q */

        /* level 2 */
        vpermq          ymm3, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+104-8*\off-8))], 0x1B
        vpermq          ymm15, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+104-8*\off-8))], 0x1B
        vmovshdup       ymm1,ymm3
        vmovshdup       ymm2,ymm15
        butterfly       0,ymm4,ymm8,ymm1,ymm3,ymm2,ymm15
        butterfly       0,ymm5,ymm9,ymm1,ymm3,ymm2,ymm15
        butterfly       0,ymm6,ymm10,ymm1,ymm3,ymm2,ymm15
        butterfly       0,ymm7,ymm11,ymm1,ymm3,ymm2,ymm15

        /* Bounds: |ymm{i}| < 8q */

        /* level 3 */
        shuffle2        ymm4,ymm5,ymm3,ymm5
        shuffle2        ymm6,ymm7,ymm4,ymm7
        shuffle2        ymm8,ymm9,ymm6,ymm9
        shuffle2        ymm10,ymm11,ymm8,ymm11

        vpermq          ymm1, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+72-8*\off-8))], 0x1B
        vpermq          ymm2, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+72-8*\off-8))], 0x1B
        butterfly       0,ymm3,ymm5
        butterfly       0,ymm4,ymm7
        butterfly       0,ymm6,ymm9
        butterfly       0,ymm8,ymm11

        /* Bounds: |ymm{i}| < 16q */

        /* level 4 */
        shuffle4        ymm3,ymm4,ymm10,ymm4
        shuffle4        ymm6,ymm8,ymm3,ymm8
        shuffle4        ymm5,ymm7,ymm6,ymm7
        shuffle4        ymm9,ymm11,ymm5,ymm11

        vpermq          ymm1, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+40-8*\off-8))], 0x1B
        vpermq          ymm2, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+40-8*\off-8))], 0x1B
        butterfly       1,ymm10,ymm4
        butterfly       0,ymm3,ymm8
        butterfly       0,ymm6,ymm7
        butterfly       0,ymm5,ymm11

        /* Bounds: |ymm{i}| < 32q */

        /* level 5 */
        shuffle8        ymm10,ymm3,ymm9,ymm3
        shuffle8        ymm6,ymm5,ymm10,ymm5
        shuffle8        ymm4,ymm8,ymm6,ymm8
        shuffle8        ymm7,ymm11,ymm4,ymm11

        vpbroadcastd    ymm1, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+7-\off))]
        vpbroadcastd    ymm2, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+7-\off))]
        butterfly       1,ymm9,ymm3
        butterfly       1,ymm10,ymm5
        butterfly       0,ymm6,ymm8
        butterfly       0,ymm4,ymm11

        /* Bounds: |ymm{i}| < 64q */

        vmovdqa         [rdi+256*\off+0],ymm9
        vmovdqa         [rdi+256*\off+32],ymm10
        vmovdqa         [rdi+256*\off+64],ymm6
        vmovdqa         [rdi+256*\off+96],ymm4
        vmovdqa         [rdi+256*\off+128],ymm3
        vmovdqa         [rdi+256*\off+160],ymm5
        vmovdqa         [rdi+256*\off+192],ymm8
        vmovdqa         [rdi+256*\off+224],ymm11
.endm

.macro levels6t7 off
        vmovdqa         ymm4, [rdi+0+32*\off]
        vmovdqa         ymm5, [rdi+128+32*\off]
        vmovdqa         ymm6, [rdi+256+32*\off]
        vmovdqa         ymm7, [rdi+384+32*\off]
        vmovdqa         ymm8, [rdi+512+32*\off]
        vmovdqa         ymm9, [rdi+640+32*\off]
        vmovdqa         ymm10, [rdi+768+32*\off]
        vmovdqa         ymm11, [rdi+896+32*\off]

        /* level 6 */
        vpbroadcastd    ymm1, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+3))]
        vpbroadcastd    ymm2, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+3))]
        butterfly       0,ymm4,ymm6
        butterfly       0,ymm5,ymm7

        vpbroadcastd    ymm1, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+2))]
        vpbroadcastd    ymm2, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+2))]
        butterfly       0,ymm8,ymm10
        butterfly       0,ymm9,ymm11

        /* Bounds: |ymm{i}| < 128q */

        /* level 7 */
        vpbroadcastd    ymm1, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+0))]
        vpbroadcastd    ymm2, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+0))]

        butterfly       0,ymm4,ymm8
        butterfly       0,ymm5,ymm9
        butterfly       0,ymm6,ymm10
        butterfly       0,ymm7,ymm11

        /*
         * Bounds: |ymm{i}| < 256q          for i in 4...7
         *                  < MONTMUL_BOUND for i in 8...11
         */

        vmovdqa         [rdi+512+32*\off],ymm8
        vmovdqa         [rdi+640+32*\off],ymm9
        vmovdqa         [rdi+768+32*\off],ymm10
        vmovdqa         [rdi+896+32*\off],ymm11

        /*
         * In order to (a) remove the factor of 256 arising from the 256-point INTT
         * butterflies and (b) transform the output into Montgomery domain, we need to
         * multiply all coefficients by 2^32/256.
         *
         * For ymm{8,9,10,11}, the scaling has been merged into the last butterfly, so
         * only ymm{4,5,6,7} need to be scaled explicitly.
         *
         * The scaling is achieved by computing montmul(-, MLD_AVX2_DIV).
         *
         * Bounds: |ymm{i}| < 256q for i in 4...7
         */

        vmovdqa         ymm1, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_8XDIV_QINV))]
        vmovdqa         ymm2, [rsi+(4*(MLD_AVX2_BACKEND_DATA_OFFSET_8XDIV))]
        vpmuldq         ymm12,ymm4,ymm1
        vpmuldq         ymm13,ymm5,ymm1
        vmovshdup       ymm8,ymm4
        vmovshdup       ymm9,ymm5
        vpmuldq         ymm14,ymm8,ymm1
        vpmuldq         ymm15,ymm9,ymm1
        vpmuldq         ymm4,ymm4,ymm2
        vpmuldq         ymm5,ymm5,ymm2
        vpmuldq         ymm8,ymm8,ymm2
        vpmuldq         ymm9,ymm9,ymm2
        vpmuldq         ymm12,ymm12,ymm0
        vpmuldq         ymm13,ymm13,ymm0
        vpmuldq         ymm14,ymm14,ymm0
        vpmuldq         ymm15,ymm15,ymm0
        vpsubd          ymm4,ymm4,ymm12
        vpsubd          ymm5,ymm5,ymm13
        vpsubd          ymm8,ymm8,ymm14
        vpsubd          ymm9,ymm9,ymm15
        vmovshdup       ymm4,ymm4
        vmovshdup       ymm5,ymm5
        vpblendd        ymm4,ymm4,ymm8,0xAA
        vpblendd        ymm5,ymm5,ymm9,0xAA

        vpmuldq         ymm12,ymm6,ymm1
        vpmuldq         ymm13,ymm7,ymm1
        vmovshdup       ymm8,ymm6
        vmovshdup       ymm9,ymm7
        vpmuldq         ymm14,ymm8,ymm1
        vpmuldq         ymm15,ymm9,ymm1
        vpmuldq         ymm6,ymm6,ymm2
        vpmuldq         ymm7,ymm7,ymm2
        vpmuldq         ymm8,ymm8,ymm2
        vpmuldq         ymm9,ymm9,ymm2
        vpmuldq         ymm12,ymm12,ymm0
        vpmuldq         ymm13,ymm13,ymm0
        vpmuldq         ymm14,ymm14,ymm0
        vpmuldq         ymm15,ymm15,ymm0
        vpsubd          ymm6,ymm6,ymm12
        vpsubd          ymm7,ymm7,ymm13
        vpsubd          ymm8,ymm8,ymm14
        vpsubd          ymm9,ymm9,ymm15
        vmovshdup       ymm6,ymm6
        vmovshdup       ymm7,ymm7
        vpblendd        ymm6,ymm6,ymm8,0xAA
        vpblendd        ymm7,ymm7,ymm9,0xAA

        /* Bounds: |ymm{i}| < MONTMUL_BOUND for i in 4...7 */

        /*
         * In the following we show that |montmul(a, b)| < MONTMUL_BOUND := ceil(3q/4),
         * given that a fits inside int32_t (thus |a| <= R/2) and b is signed canonical
         * (in the range -(Q-1)/2...(Q-1)/2).
         *
         * In Section 2.2 of https://eprint.iacr.org/2023/1962, they showed that b being
         * signed canonical implies:
         *
         *   |montmul(a, b)| <= (|a| (q/2) + (R/2) q) / R = (q/2) (1 + |a|/R).
         *
         * From this, simple computation gives |montmul(a, b)| <= 3q/4 < ceil(3q/4).
         *
         * See test/test_bounds.py for more empirical evidence (and some minor technical
         * details).
         *
         * TODO: Use proper citation. Currently, citations within asm can cause linter
         *       to complain about unused citation, because comments are not preserved
         *       after simpasm.
         */

        vmovdqa         [rdi+0+32*\off],ymm4
        vmovdqa         [rdi+128+32*\off],ymm5
        vmovdqa         [rdi+256+32*\off],ymm6
        vmovdqa         [rdi+384+32*\off],ymm7
.endm

S2N_BN_SYMBOL(mldsa_intt):
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

        levels0t5 0
        levels0t5 1
        levels0t5 2
        levels0t5 3

        levels6t7 0
        levels6t7 1
        levels6t7 2
        levels6t7 3

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

S2N_BN_SIZE_DIRECTIVE(mldsa_intt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
