// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Pointwise multiplication of polynomials in NTT domain for ML-DSA
// Inputs c[256], a[256], b[256], qdata (all signed 32-bit words); output c[256]
//
// Performs pointwise multiplication of two polynomials in NTT domain with
// Montgomery reduction. Given two polynomials a and b in NTT representation
// (256 coefficients each), computes c = a * b (coefficient-wise) in NTT domain.
// Each coefficient multiplication is followed by Montgomery reduction modulo
// Q = 8380417.
//
// The input polynomials a and b are assumed to have coefficients bounded by
// 9*Q in absolute value. The output polynomial c will have coefficients bounded
// by Q in absolute value after Montgomery reduction.
//
// The qdata parameter points to precomputed constants required for Montgomery
// arithmetic:
//   - 8xQINV: Eight copies of Q^(-1) mod 2^32 for Montgomery multiplication
//   - 8xQ: Eight copies of Q for the reduction step
//
// extern void mldsa_pointwise_x86(
//     int32_t c[static 256],
//     const int32_t a[static 256],
//     const int32_t b[static 256],
//     const int32_t qdata[static 16]
// );
//
// Standard x86-64 ABI: RDI = c, RSI = a, RDX = b, RCX = qdata
// Microsoft x64 ABI:   RCX = c, RDX = a, R8 = b, R9 = qdata
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_pointwise_x86)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mldsa_pointwise_x86)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_pointwise_x86)
        .text
        .balign 32

#define c rdi
#define a rsi
#define b rdx
#define qdata rcx

#define MLD_AVX2_BACKEND_DATA_OFFSET_8XQINV 0
#define MLD_AVX2_BACKEND_DATA_OFFSET_8XQ 8

S2N_BN_SYMBOL(mldsa_pointwise_x86):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(192)
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
        CFI_STACKSAVE(rdx,176)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
#endif

// Load constants from qdata
        vmovdqa ymm0, [qdata + (MLD_AVX2_BACKEND_DATA_OFFSET_8XQINV)*4]
        vmovdqa ymm1, [qdata + (MLD_AVX2_BACKEND_DATA_OFFSET_8XQ)*4]

        xor     eax, eax
Lpointwise_looptop1:
// Handle 24 = 3*8 coefficients per iteration

// Load a's coefficients
        vmovdqa ymm2, [a]
        vmovdqa ymm4, [a + 32]
        vmovdqa ymm6, [a + 64]
// Load b's coefficients
        vmovdqa ymm10, [b]
        vmovdqa ymm12, [b + 32]
        vmovdqa ymm14, [b + 64]

// Extract high 32-bit parts for Montgomery multiplication
        vpsrlq  ymm3, ymm2, 32
        vpsrlq  ymm5, ymm4, 32
        vmovshdup ymm7, ymm6
        vpsrlq  ymm11, ymm10, 32
        vpsrlq  ymm13, ymm12, 32
        vmovshdup ymm15, ymm14
        /*
         * ymm{i} stores a's coefficients for i in 2...7, and b's coefficients
         * for i in 10...15.
         *
         * Bounds: |ymm{i}| < 9q for i in 2...7, 10...15
         */

// Multiply coefficients
        vpmuldq ymm2, ymm2, ymm10
        vpmuldq ymm3, ymm3, ymm11
        vpmuldq ymm4, ymm4, ymm12
        vpmuldq ymm5, ymm5, ymm13
        vpmuldq ymm6, ymm6, ymm14
        vpmuldq ymm7, ymm7, ymm15
        /*
         * Bounds: |ymm{i}| < 81q^2 < MONTGOMERY_REDUCE_STRONG_DOMAIN_MAX
         *             for i in 2...7
         */

// Montgomery reduction
        vpmuldq ymm10, ymm0, ymm2
        vpmuldq ymm11, ymm0, ymm3
        vpmuldq ymm12, ymm0, ymm4
        vpmuldq ymm13, ymm0, ymm5
        vpmuldq ymm14, ymm0, ymm6
        vpmuldq ymm15, ymm0, ymm7
        vpmuldq ymm10, ymm1, ymm10
        vpmuldq ymm11, ymm1, ymm11
        vpmuldq ymm12, ymm1, ymm12
        vpmuldq ymm13, ymm1, ymm13
        vpmuldq ymm14, ymm1, ymm14
        vpmuldq ymm15, ymm1, ymm15
        vpsubq  ymm2, ymm2, ymm10
        vpsubq  ymm3, ymm3, ymm11
        vpsubq  ymm4, ymm4, ymm12
        vpsubq  ymm5, ymm5, ymm13
        vpsubq  ymm6, ymm6, ymm14
        vpsubq  ymm7, ymm7, ymm15
        /*
         * All coefficients are Montgomery-reduced, resulting in
         *
         * Bounds: |ymm{i}| < q for i in 2...7
         *
         * See description of mld_montgomery_reduce() in mldsa/src/reduce.h.
         */

// Repack and store results
        vpsrlq  ymm2, ymm2, 32
        vpsrlq  ymm4, ymm4, 32
        vmovshdup ymm6, ymm6
        vpblendd ymm2, ymm2, ymm3, 0xAA
        vpblendd ymm4, ymm4, ymm5, 0xAA
        vpblendd ymm6, ymm6, ymm7, 0xAA
        vmovdqa [c], ymm2
        vmovdqa [c + 32], ymm4
        vmovdqa [c + 64], ymm6

        add     c, 96
        add     a, 96
        add     b, 96
        add     eax, 1
        cmp     eax, 10
        jb      Lpointwise_looptop1


// Handle the last 256 % 24 = 16 = 2*8 coefficients, left over by the loop

// Load remaining a's coefficients
        vmovdqa ymm2, [a]
        vmovdqa ymm4, [a + 32]
// Load remaining b's coefficients
        vmovdqa ymm10, [b]
        vmovdqa ymm12, [b + 32]

// Extract high 32-bit parts
        vpsrlq  ymm3, ymm2, 32
        vpsrlq  ymm5, ymm4, 32
        vmovshdup ymm11, ymm10
        vmovshdup ymm13, ymm12
        /*
         * ymm{i} stores a's coefficients for i in 2...5, and b's coefficients
         * for i in 10...13.
         *
         * Bounds: |ymm{i}| < 9q for i in 2...5, 10...13
         */

// Multiply remaining coefficients
        vpmuldq ymm2, ymm2, ymm10
        vpmuldq ymm3, ymm3, ymm11
        vpmuldq ymm4, ymm4, ymm12
        vpmuldq ymm5, ymm5, ymm13
        /*
         * Bounds: |ymm{i}| < 81q^2 < MONTGOMERY_REDUCE_STRONG_DOMAIN_MAX
         *             for i in 2...5
         */

// Montgomery reduction for remaining coefficients
        vpmuldq ymm10, ymm0, ymm2
        vpmuldq ymm11, ymm0, ymm3
        vpmuldq ymm12, ymm0, ymm4
        vpmuldq ymm13, ymm0, ymm5
        vpmuldq ymm10, ymm1, ymm10
        vpmuldq ymm11, ymm1, ymm11
        vpmuldq ymm12, ymm1, ymm12
        vpmuldq ymm13, ymm1, ymm13
        vpsubq  ymm2, ymm2, ymm10
        vpsubq  ymm3, ymm3, ymm11
        vpsubq  ymm4, ymm4, ymm12
        vpsubq  ymm5, ymm5, ymm13
        /*
         * As explained in the loop.
         *
         * Bounds: |ymm{i}| < q for i in 2...5
         */

// Repack and store final results
        vpsrlq  ymm2, ymm2, 32
        vmovshdup ymm4, ymm4
        vpblendd ymm2, ymm3, ymm2, 0x55
        vpblendd ymm4, ymm5, ymm4, 0x55
        vmovdqa [c], ymm2
        vmovdqa [c + 32], ymm4

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
        CFI_STACKLOAD(rdx,176)
        CFI_INC_RSP(192)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mldsa_pointwise_x86)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
