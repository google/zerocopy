// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Coefficient decomposition for ML-DSA-44 (GAMMA2 = (Q-1)/88 = 95232)
//
// For each coefficient c of the input polynomial (assumed to be a standard
// unsigned canonical representative, i.e. 0 <= c < Q), compute high and low
// bits c1, c0 such that c = c1*ALPHA + c0 with -ALPHA/2 < c0 <= ALPHA/2,
// except if c1 = (Q-1)/ALPHA where we set c1 = 0 and -ALPHA/2 <= c0 = c-Q < 0.
// Here ALPHA = 2*GAMMA2 = 190464.
//
// The high-bits array a1 receives the 256 high parts; the array a0 is both
// the input polynomial and the output low-part array (read/write).
//
// extern void mldsa_decompose_88(int32_t a1[static 256],
//                                int32_t a0[static 256]);
//
// Standard x86-64 ABI: RDI = a1, RSI = a0
// Microsoft x64 ABI:   RCX = a1, RDX = a0
// ----------------------------------------------------------------------------

// This implementation is derived from the public domain AVX2 Dilithium
// implementation (pq-crystals/dilithium) via the mldsa-native project.

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_decompose_88)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mldsa_decompose_88)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_decompose_88)
        .text
        .balign 4

.macro decompose_vector offset
        vmovdqa   ymm0, [rsi + \offset]
        vpaddd    ymm1, ymm0, ymm10
        vpsrld    ymm1, ymm1, 0x7
        vpmulhuw  ymm1, ymm1, ymm11
        vpmulhrsw ymm1, ymm1, ymm12
        vpcmpgtd  ymm3, ymm0, ymm13
        vpmulld   ymm2, ymm1, ymm14
        vpsubd    ymm2, ymm0, ymm2
        vpandn    ymm1, ymm3, ymm1
        vpaddd    ymm2, ymm2, ymm3
        vmovdqa   [rdi + \offset], ymm1
        vmovdqa   [rsi + \offset], ymm2
.endm

S2N_BN_SYMBOL(mldsa_decompose_88):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(96)
        CFI_STACKSAVEU(xmm10,0)
        CFI_STACKSAVEU(xmm11,16)
        CFI_STACKSAVEU(xmm12,32)
        CFI_STACKSAVEU(xmm13,48)
        CFI_STACKSAVEU(xmm14,64)
        CFI_STACKSAVE(rdi,80)
        CFI_STACKSAVE(rsi,88)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Set up broadcast constants for the Barrett high-bits sequence.
        mov     eax, 0x7f
        vmovd   xmm10, eax
        vpbroadcastd ymm10, xmm10
        mov     eax, 0x2c0b
        vmovd   xmm11, eax
        vpbroadcastd ymm11, xmm11
        mov     eax, 0x80
        vmovd   xmm12, eax
        vpbroadcastd ymm12, xmm12
        mov     eax, 0x7e6c00
        vmovd   xmm13, eax
        vpbroadcastd ymm13, xmm13
        mov     eax, 0x2e800
        vmovd   xmm14, eax
        vpbroadcastd ymm14, xmm14

// Process all 256 coefficients (32 vectors of 8 int32 each).
        decompose_vector 0
        decompose_vector 0x20
        decompose_vector 0x40
        decompose_vector 0x60
        decompose_vector 0x80
        decompose_vector 0xa0
        decompose_vector 0xc0
        decompose_vector 0xe0
        decompose_vector 0x100
        decompose_vector 0x120
        decompose_vector 0x140
        decompose_vector 0x160
        decompose_vector 0x180
        decompose_vector 0x1a0
        decompose_vector 0x1c0
        decompose_vector 0x1e0
        decompose_vector 0x200
        decompose_vector 0x220
        decompose_vector 0x240
        decompose_vector 0x260
        decompose_vector 0x280
        decompose_vector 0x2a0
        decompose_vector 0x2c0
        decompose_vector 0x2e0
        decompose_vector 0x300
        decompose_vector 0x320
        decompose_vector 0x340
        decompose_vector 0x360
        decompose_vector 0x380
        decompose_vector 0x3a0
        decompose_vector 0x3c0
        decompose_vector 0x3e0

#if WINDOWS_ABI
        CFI_STACKLOADU(xmm10,0)
        CFI_STACKLOADU(xmm11,16)
        CFI_STACKLOADU(xmm12,32)
        CFI_STACKLOADU(xmm13,48)
        CFI_STACKLOADU(xmm14,64)
        CFI_STACKLOAD(rdi,80)
        CFI_STACKLOAD(rsi,88)
        CFI_INC_RSP(96)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mldsa_decompose_88)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
