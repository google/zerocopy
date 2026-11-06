// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Canonical reduction of polynomial coefficients for ML-KEM
// Input a[256] (signed 16-bit words); output a[256] (signed 16-bit words)
//
// This reduces each element of the 256-element array of 16-bit signed
// integers modulo 3329 with the result being 0 <= r < 3329, in-place.
// This is intended for use when that array represents polynomial
// coefficients for ML-KEM, but that is not relevant to its operation.
//
// extern void mlkem_reduce(int16_t a[static 256]);
//
// Standard x86-64 ABI: RDI = a
// Microsoft x64 ABI:   RCX = a
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

.intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_reduce)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_reduce)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_reduce)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_reduce):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(96)
        CFI_STACKSAVEU(xmm6,0)
        CFI_STACKSAVEU(xmm7,16)
        CFI_STACKSAVEU(xmm8,32)
        CFI_STACKSAVEU(xmm9,48)
        CFI_STACKSAVEU(xmm12,64)
        CFI_STACKSAVE(rdi,80)
        mov     rdi, rcx
#endif

        // Load 3329 (0x0D01) into all elements of ymm0:
        mov  eax, 0x0D010D01
        movd xmm0, eax
        vpbroadcastd ymm0, xmm0

        // Load 20159 (0x4EBF) into all elements of ymm1:
        mov  eax, 0x4EBF4EBF
        movd xmm1, eax
        vpbroadcastd ymm1, xmm1

        // We process 128 coefficients (8 ymm regs) at once.
        // Reduce the fist 128 coefficients:
        vmovdqa ymm2, [rdi+0x00]
        vmovdqa ymm3, [rdi+0x20]
        vmovdqa ymm4, [rdi+0x40]
        vmovdqa ymm5, [rdi+0x60]
        vmovdqa ymm6, [rdi+0x80]
        vmovdqa ymm7, [rdi+0xa0]
        vmovdqa ymm8, [rdi+0xc0]
        vmovdqa ymm9, [rdi+0xe0]

        vpmulhw ymm12, ymm2, ymm1
        vpsraw  ymm12, ymm12, 0xa
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm2, ymm2, ymm12
        vpmulhw ymm12, ymm3, ymm1
        vpsraw  ymm12, ymm12, 0xa
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm3, ymm3, ymm12
        vpmulhw ymm12, ymm4, ymm1
        vpsraw  ymm12, ymm12, 0xa
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm4, ymm4, ymm12
        vpmulhw ymm12, ymm5, ymm1
        vpsraw  ymm12, ymm12, 0xa
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm5, ymm5, ymm12
        vpmulhw ymm12, ymm6, ymm1
        vpsraw  ymm12, ymm12, 0xa
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm6, ymm6, ymm12
        vpmulhw ymm12, ymm7, ymm1
        vpsraw  ymm12, ymm12, 0xa
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm7, ymm7, ymm12
        vpmulhw ymm12, ymm8, ymm1
        vpsraw  ymm12, ymm12, 0xa
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm8, ymm8, ymm12
        vpmulhw ymm12, ymm9, ymm1
        vpsraw  ymm12, ymm12, 0xa
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm9, ymm9, ymm12

        vpsubw  ymm2, ymm2, ymm0
        vpsraw  ymm12, ymm2, 0xf
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm2, ymm2, ymm12
        vpsubw  ymm3, ymm3, ymm0
        vpsraw  ymm12, ymm3, 0xf
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm3, ymm3, ymm12
        vpsubw  ymm4, ymm4, ymm0
        vpsraw  ymm12, ymm4, 0xf
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm4, ymm4, ymm12
        vpsubw  ymm5, ymm5, ymm0
        vpsraw  ymm12, ymm5, 0xf
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm5, ymm5, ymm12
        vpsubw  ymm6, ymm6, ymm0
        vpsraw  ymm12, ymm6, 0xf
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm6, ymm6, ymm12
        vpsubw  ymm7, ymm7, ymm0
        vpsraw  ymm12, ymm7, 0xf
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm7, ymm7, ymm12
        vpsubw  ymm8, ymm8, ymm0
        vpsraw  ymm12, ymm8, 0xf
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm8, ymm8, ymm12
        vpsubw  ymm9, ymm9, ymm0
        vpsraw  ymm12, ymm9, 0xf
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm9, ymm9, ymm12

        vmovdqa [rdi+0x00], ymm2
        vmovdqa [rdi+0x20], ymm3
        vmovdqa [rdi+0x40], ymm4
        vmovdqa [rdi+0x60], ymm5
        vmovdqa [rdi+0x80], ymm6
        vmovdqa [rdi+0xa0], ymm7
        vmovdqa [rdi+0xc0], ymm8
        vmovdqa [rdi+0xe0], ymm9

        // Reduce the second 128 coefficients:
        vmovdqa ymm2, [rdi+0x100]
        vmovdqa ymm3, [rdi+0x120]
        vmovdqa ymm4, [rdi+0x140]
        vmovdqa ymm5, [rdi+0x160]
        vmovdqa ymm6, [rdi+0x180]
        vmovdqa ymm7, [rdi+0x1a0]
        vmovdqa ymm8, [rdi+0x1c0]
        vmovdqa ymm9, [rdi+0x1e0]

        vpmulhw ymm12, ymm2, ymm1
        vpsraw  ymm12, ymm12, 0xa
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm2, ymm2, ymm12
        vpmulhw ymm12, ymm3, ymm1
        vpsraw  ymm12, ymm12, 0xa
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm3, ymm3, ymm12
        vpmulhw ymm12, ymm4, ymm1
        vpsraw  ymm12, ymm12, 0xa
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm4, ymm4, ymm12
        vpmulhw ymm12, ymm5, ymm1
        vpsraw  ymm12, ymm12, 0xa
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm5, ymm5, ymm12
        vpmulhw ymm12, ymm6, ymm1
        vpsraw  ymm12, ymm12, 0xa
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm6, ymm6, ymm12
        vpmulhw ymm12, ymm7, ymm1
        vpsraw  ymm12, ymm12, 0xa
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm7, ymm7, ymm12
        vpmulhw ymm12, ymm8, ymm1
        vpsraw  ymm12, ymm12, 0xa
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm8, ymm8, ymm12
        vpmulhw ymm12, ymm9, ymm1
        vpsraw  ymm12, ymm12, 0xa
        vpmullw ymm12, ymm12, ymm0
        vpsubw  ymm9, ymm9, ymm12

        vpsubw  ymm2, ymm2, ymm0
        vpsraw  ymm12, ymm2, 0xf
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm2, ymm2, ymm12
        vpsubw  ymm3, ymm3, ymm0
        vpsraw  ymm12, ymm3, 0xf
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm3, ymm3, ymm12
        vpsubw  ymm4, ymm4, ymm0
        vpsraw  ymm12, ymm4, 0xf
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm4, ymm4, ymm12
        vpsubw  ymm5, ymm5, ymm0
        vpsraw  ymm12, ymm5, 0xf
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm5, ymm5, ymm12
        vpsubw  ymm6, ymm6, ymm0
        vpsraw  ymm12, ymm6, 0xf
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm6, ymm6, ymm12
        vpsubw  ymm7, ymm7, ymm0
        vpsraw  ymm12, ymm7, 0xf
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm7, ymm7, ymm12
        vpsubw  ymm8, ymm8, ymm0
        vpsraw  ymm12, ymm8, 0xf
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm8, ymm8, ymm12
        vpsubw  ymm9, ymm9, ymm0
        vpsraw  ymm12, ymm9, 0xf
        vpand   ymm12, ymm12, ymm0
        vpaddw  ymm9, ymm9, ymm12

        vmovdqa [rdi+0x100], ymm2
        vmovdqa [rdi+0x120], ymm3
        vmovdqa [rdi+0x140], ymm4
        vmovdqa [rdi+0x160], ymm5
        vmovdqa [rdi+0x180], ymm6
        vmovdqa [rdi+0x1a0], ymm7
        vmovdqa [rdi+0x1c0], ymm8
        vmovdqa [rdi+0x1e0], ymm9

#if WINDOWS_ABI
        CFI_STACKLOADU(xmm6,0)
        CFI_STACKLOADU(xmm7,16)
        CFI_STACKLOADU(xmm8,32)
        CFI_STACKLOADU(xmm9,48)
        CFI_STACKLOADU(xmm12,64)
        CFI_STACKLOAD(rdi,80)
        CFI_INC_RSP(96)
#endif
        CFI_RET


S2N_BN_SIZE_DIRECTIVE(mlkem_reduce)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
