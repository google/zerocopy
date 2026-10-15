// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Use the hint to correct the high bits of a polynomial for ML-DSA
// (GAMMA2 = (Q-1)/88, ML-DSA-44). Operates in place on a[256].
//
// For each coefficient a of the input polynomial (a standard canonical
// representative, 0 <= a < Q) and hint bit h in {0,1}, compute UseHint(h, a):
// the high part of the decomposition of a, adjusted up or down by one modulo
// 44 when h = 1. The corrected high part (in [0,44)) is written back in place.
//
// extern void mldsa_poly_use_hint_88(int32_t a[static 256],
//                                    const int32_t h[static 256]);
//
// Standard x86-64 ABI: RDI = a, RSI = h
// Microsoft x64 ABI:   RCX = a, RDX = h
// ----------------------------------------------------------------------------

// This implementation is derived from the public domain AVX2 Dilithium
// implementation (pq-crystals/dilithium) via the mldsa-native project.

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_poly_use_hint_88)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mldsa_poly_use_hint_88)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_poly_use_hint_88)
        .text
        .balign 4

S2N_BN_SYMBOL(mldsa_poly_use_hint_88):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(128)
        CFI_STACKSAVEU(xmm6,0)
        CFI_STACKSAVEU(xmm7,16)
        CFI_STACKSAVEU(xmm8,32)
        CFI_STACKSAVEU(xmm9,48)
        CFI_STACKSAVEU(xmm10,64)
        CFI_STACKSAVEU(xmm11,80)
        CFI_STACKSAVEU(xmm12,96)
        CFI_STACKSAVE(rdi,112)
        CFI_STACKSAVE(rsi,120)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Set up broadcast constants used by the Barrett high-bits sequence.
        mov     ecx, 0x7f
        xor     eax, eax
        vpxor   xmm5, xmm5, xmm5
        mov     r8d, 0x2c0b
        vmovd   xmm8, r8d
        vpbroadcastd ymm8, xmm8
        vmovd   xmm4, ecx
        mov     ecx, 0x7e6c00
        mov     r9d, 0x80
        vmovd   xmm7, r9d
        vpbroadcastd ymm7, xmm7
        mov     r10d, 0x2b
        vmovd   xmm6, r10d
        vpbroadcastd ymm6, xmm6
        vmovd   xmm3, ecx
        vpbroadcastd ymm4, xmm4
        vpbroadcastd ymm3, xmm3

Lmldsa_poly_use_hint_88_loop:
        vmovdqa   ymm0, [rdi]
        vmovdqa   ymm1, [rsi]
        vpaddd    ymm10, ymm4, ymm0
        vpsrld    ymm10, ymm10, 0x7
        vpmulhuw  ymm10, ymm10, ymm8
        vpmulhrsw ymm10, ymm10, ymm7
        vpcmpgtd  ymm11, ymm0, ymm3
        vpandn    ymm9, ymm11, ymm10
        vpslld    ymm12, ymm10, 0x1
        vpaddd    ymm12, ymm12, ymm10
        vpslld    ymm10, ymm12, 0x5
        vpsubd    ymm10, ymm10, ymm12
        vpslld    ymm10, ymm10, 0xb
        vpsubd    ymm0, ymm0, ymm10
        vpaddd    ymm0, ymm0, ymm11
        vpcmpgtd  ymm0, ymm0, ymm5
        vpandn    ymm0, ymm0, ymm1
        vpslld    ymm0, ymm0, 0x1
        vpsubd    ymm0, ymm1, ymm0
        vpaddd    ymm0, ymm0, ymm9
        vpblendvb ymm0, ymm0, ymm6, ymm0
        vpcmpgtd  ymm1, ymm0, ymm6
        vpandn    ymm0, ymm1, ymm0
        vmovdqa   [rdi], ymm0
        add       rdi, 0x20
        add       rsi, 0x20
        add       rax, 0x20
        cmp       rax, 0x400
        jne       Lmldsa_poly_use_hint_88_loop

#if WINDOWS_ABI
        CFI_STACKLOADU(xmm6,0)
        CFI_STACKLOADU(xmm7,16)
        CFI_STACKLOADU(xmm8,32)
        CFI_STACKLOADU(xmm9,48)
        CFI_STACKLOADU(xmm10,64)
        CFI_STACKLOADU(xmm11,80)
        CFI_STACKLOADU(xmm12,96)
        CFI_STACKLOAD(rdi,112)
        CFI_STACKLOAD(rsi,120)
        CFI_INC_RSP(128)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mldsa_poly_use_hint_88)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
