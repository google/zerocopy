// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Use the hint to correct the high bits of a polynomial for ML-DSA
// (GAMMA2 = (Q-1)/32, ML-DSA-65/87). Operates in place on a[256].
//
// For each coefficient a of the input polynomial (a standard canonical
// representative, 0 <= a < Q) and hint bit h in {0,1}, compute UseHint(h, a):
// the high part of the decomposition of a, adjusted up or down by one modulo
// 16 when h = 1. The corrected high part (in [0,16)) is written back in place.
//
// extern void mldsa_poly_use_hint_32(int32_t a[static 256],
//                                    const int32_t h[static 256]);
//
// Standard x86-64 ABI: RDI = a, RSI = h
// Microsoft x64 ABI:   RCX = a, RDX = h
// ----------------------------------------------------------------------------

// This implementation is derived from the public domain AVX2 Dilithium
// implementation (pq-crystals/dilithium) via the mldsa-native project.

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_poly_use_hint_32)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mldsa_poly_use_hint_32)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_poly_use_hint_32)
        .text
        .balign 4

S2N_BN_SYMBOL(mldsa_poly_use_hint_32):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(112)
        CFI_STACKSAVEU(xmm6,0)
        CFI_STACKSAVEU(xmm7,16)
        CFI_STACKSAVEU(xmm8,32)
        CFI_STACKSAVEU(xmm9,48)
        CFI_STACKSAVEU(xmm10,64)
        CFI_STACKSAVEU(xmm11,80)
        CFI_STACKSAVE(rdi,96)
        CFI_STACKSAVE(rsi,104)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Set up broadcast constants used by the Barrett high-bits sequence.
        mov     ecx, 0x7f
        mov     r8d, 0x401
        vmovd   xmm8, r8d
        vpbroadcastd ymm8, xmm8
        xor     eax, eax
        vpxor   xmm6, xmm6, xmm6
        vmovd   xmm5, ecx
        mov     ecx, 0x7be100
        mov     r9d, 0x200
        vmovd   xmm7, r9d
        vpbroadcastd ymm7, xmm7
        vmovd   xmm4, ecx
        mov     ecx, 0xf
        vpbroadcastd ymm5, xmm5
        vmovd   xmm3, ecx
        vpbroadcastd ymm4, xmm4
        vpbroadcastd ymm3, xmm3

Lmldsa_poly_use_hint_32_loop:
        vmovdqa   ymm0, [rdi]
        vmovdqa   ymm2, [rsi]
        vpaddd    ymm1, ymm5, ymm0
        vpsrld    ymm1, ymm1, 0x7
        vpmulhuw  ymm1, ymm1, ymm8
        vpmulhrsw ymm1, ymm1, ymm7
        vpcmpgtd  ymm11, ymm0, ymm4
        vpandn    ymm9, ymm11, ymm1
        vpslld    ymm10, ymm1, 0xa
        vpsubd    ymm1, ymm10, ymm1
        vpslld    ymm1, ymm1, 0x9
        vpsubd    ymm0, ymm0, ymm1
        vpaddd    ymm0, ymm0, ymm11
        vpcmpgtd  ymm0, ymm0, ymm6
        vpandn    ymm0, ymm0, ymm2
        vpslld    ymm0, ymm0, 0x1
        vpsubd    ymm2, ymm2, ymm0
        vpaddd    ymm2, ymm2, ymm9
        vpand     ymm2, ymm2, ymm3
        vmovdqa   [rdi], ymm2
        add       rdi, 0x20
        add       rsi, 0x20
        add       rax, 0x20
        cmp       rax, 0x400
        jne       Lmldsa_poly_use_hint_32_loop

#if WINDOWS_ABI
        CFI_STACKLOADU(xmm6,0)
        CFI_STACKLOADU(xmm7,16)
        CFI_STACKLOADU(xmm8,32)
        CFI_STACKLOADU(xmm9,48)
        CFI_STACKLOADU(xmm10,64)
        CFI_STACKLOADU(xmm11,80)
        CFI_STACKLOAD(rdi,96)
        CFI_STACKLOAD(rsi,104)
        CFI_INC_RSP(112)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mldsa_poly_use_hint_32)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
