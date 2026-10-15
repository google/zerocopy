// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Pointwise multiplication with accumulation for ML-DSA L4
// Inputs c[256], a[4*256], b[4*256], qdata (all signed 32-bit words); output c[256]
//
// Performs pointwise multiplication with accumulation across four polynomial
// vectors in NTT domain with Montgomery reduction. Given four pairs of
// polynomials (a0,b0), (a1,b1), (a2,b2), (a3,b3) each with 256 coefficients
// in NTT representation, computes c = a0*b0 + a1*b1 + a2*b2 + a3*b3
// (coefficient-wise) in NTT domain. Each coefficient multiplication and
// accumulation is followed by Montgomery reduction modulo Q = 8380417.
//
// This function is specifically optimized for ML-DSA Level 4 parameter set
// which requires accumulating 4 polynomial products. The input polynomials
// a and b are laid out sequentially with a stride of 1024 bytes (256 * 4).
//
// Input bounds (per coefficient, absolute value):
//   |a[i]| < Q
//   |b[i]| < 9*Q
// The output polynomial c will have coefficients bounded by Q in absolute
// value after Montgomery reduction.
//
// The qdata parameter points to precomputed constants required for Montgomery
// arithmetic:
//   - 8xQINV: Eight copies of Q^(-1) mod 2^32 for Montgomery multiplication
//   - 8xQ: Eight copies of Q for the reduction step
//
// extern void mldsa_pointwise_acc_l4_x86(
//     int32_t c[static 256],
//     const int32_t a[static 1024],
//     const int32_t b[static 1024],
//     const int32_t qdata[static 16]
// );
//
// Standard x86-64 ABI: RDI = c, RSI = a, RDX = b, RCX = qdata
// Microsoft x64 ABI:   RCX = c, RDX = a, R8 = b, R9 = qdata
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_pointwise_acc_l4_x86)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mldsa_pointwise_acc_l4_x86)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_pointwise_acc_l4_x86)
        .text
        .balign 32

#define c rdi
#define a rsi
#define b rdx
#define qdata rcx

#define MLD_AVX2_BACKEND_DATA_OFFSET_8XQ 0
#define MLD_AVX2_BACKEND_DATA_OFFSET_8XQINV 8

.macro pointwise off
// Load a's coefficients
        vmovdqa ymm6, [a + \off]
        vmovdqa ymm8, [a + \off + 32]
// Load b's coefficients
        vmovdqa ymm10, [b + \off]
        vmovdqa ymm12, [b + \off + 32]
// Extract high 32-bit parts for Montgomery multiplication
        vpsrlq  ymm7, ymm6, 32
        vpsrlq  ymm9, ymm8, 32
        vmovshdup ymm11, ymm10
        vmovshdup ymm13, ymm12
        /*
         * ymm{i} stores a's coefficients for i in 6...9, and b's coefficients
         * for i in 10...13.
         *
         * Bounds: |ymm{i}| < q  for i in 6...9
         *                  < 9q for i in 10...13
         */

// Multiply coefficients
        vpmuldq ymm6, ymm6, ymm10
        vpmuldq ymm7, ymm7, ymm11
        vpmuldq ymm8, ymm8, ymm12
        vpmuldq ymm9, ymm9, ymm13
        /* Bounds: |ymm{i}| < 9q^2 for i in 6...9 */
.endm

.macro acc
        vpaddq  ymm2, ymm6, ymm2
        vpaddq  ymm3, ymm7, ymm3
        vpaddq  ymm4, ymm8, ymm4
        vpaddq  ymm5, ymm9, ymm5
.endm

S2N_BN_SYMBOL(mldsa_pointwise_acc_l4_x86):
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
        mov     rdx, r8
        mov     rcx, r9
#endif

// Load constants from qdata
        vmovdqa ymm0, [qdata + (MLD_AVX2_BACKEND_DATA_OFFSET_8XQINV)*4]
        vmovdqa ymm1, [qdata + (MLD_AVX2_BACKEND_DATA_OFFSET_8XQ)*4]

        xor     eax, eax
Lpointwise_acc_l4_looptop:
        pointwise 0

// Move first product
        vmovdqa ymm2, ymm6
        vmovdqa ymm3, ymm7
        vmovdqa ymm4, ymm8
        vmovdqa ymm5, ymm9
        /* Bounds: |ymm{i}| < 9q^2 */

        pointwise 1024
        acc
        /* Bounds: |ymm{i}| < 18q^2 */

        pointwise 2048
        acc
        /* Bounds: |ymm{i}| < 27q^2 */

        pointwise 3072
        acc
        /* Bounds: |ymm{i}| < 36q^2 < MONTGOMERY_REDUCE_STRONG_DOMAIN_MAX */

// Montgomery reduction
        vpmuldq ymm6, ymm0, ymm2
        vpmuldq ymm7, ymm0, ymm3
        vpmuldq ymm8, ymm0, ymm4
        vpmuldq ymm9, ymm0, ymm5
        vpmuldq ymm6, ymm1, ymm6
        vpmuldq ymm7, ymm1, ymm7
        vpmuldq ymm8, ymm1, ymm8
        vpmuldq ymm9, ymm1, ymm9
        vpsubq  ymm2, ymm2, ymm6
        vpsubq  ymm3, ymm3, ymm7
        vpsubq  ymm4, ymm4, ymm8
        vpsubq  ymm5, ymm5, ymm9
        /*
         * All coefficients are Montgomery-reduced, resulting in
         *
         * Bounds: |ymm{i}| < q for i in 2...5
         *
         * See description of mld_montgomery_reduce() in mldsa/src/reduce.h.
         */

// Repack and store results
        vpsrlq  ymm2, ymm2, 32
        vmovshdup ymm4, ymm4
        vpblendd ymm2, ymm2, ymm3, 0xAA
        vpblendd ymm4, ymm4, ymm5, 0xAA

        vmovdqa [c], ymm2
        vmovdqa [c + 32], ymm4

        add     a, 64
        add     b, 64
        add     c, 64
        add     eax, 1
        cmp     eax, 16
        jb      Lpointwise_acc_l4_looptop

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

S2N_BN_SIZE_DIRECTIVE(mldsa_pointwise_acc_l4_x86)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif