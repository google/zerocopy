// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// NTT unpack for ML-DSA
// Input a[256] (signed 32-bit words); output a[256] (signed 32-bit words)
//
// This function performs the unpacking transformation on NTT-domain polynomial
// coefficients, converting from a packed representation to a standard layout.
// The operation is performed in-place on a 256-element array of signed 32-bit
// integers. This is a supporting operation for ML-DSA signature operations.
//
// This implementation is derived from the public domain AVX2 Dilithium
// implementation from CRYSTALS-Dilithium optimized AVX2 implementation by
// Bai, Ducas, Kiltz, Lepoint, Lyubashevsky, Schwabe, Seiler, Stehlé
// (https://github.com/pq-crystals/dilithium/tree/master/avx2)
//
// extern void mldsa_nttunpack(int32_t a[static 256]);
//
// Standard x86-64 ABI: RDI = a
// Microsoft x64 ABI:   RCX = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_nttunpack)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mldsa_nttunpack)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_nttunpack)
        .text

#define a rdi

.macro shuffle8 r0, r1, r2, r3
        vperm2i128      \r2,\r0,\r1,0x20
        vperm2i128      \r3,\r0,\r1,0x31
.endm

.macro shuffle4 r0, r1, r2, r3
        vpunpcklqdq     \r2,\r0,\r1
        vpunpckhqdq     \r3,\r0,\r1
.endm

.macro shuffle2 r0, r1, r2, r3
        vmovsldup       \r2,\r1
        vpblendd        \r2,\r0,\r2,0xAA
        vpsrlq          \r0,\r0,32
        vpblendd        \r3,\r0,\r1,0xAA
.endm

.macro nttunpack_64_coefficients offset
        /* load */
        vmovdqa         ymm4, [rdi+(\offset+0)]
        vmovdqa         ymm5, [rdi+(\offset+32)]
        vmovdqa         ymm6, [rdi+(\offset+64)]
        vmovdqa         ymm7, [rdi+(\offset+96)]
        vmovdqa         ymm8, [rdi+(\offset+128)]
        vmovdqa         ymm9, [rdi+(\offset+160)]
        vmovdqa         ymm10, [rdi+(\offset+192)]
        vmovdqa         ymm11, [rdi+(\offset+224)]

        shuffle8        ymm4,ymm8,ymm3,ymm8
        shuffle8        ymm5,ymm9,ymm4,ymm9
        shuffle8        ymm6,ymm10,ymm5,ymm10
        shuffle8        ymm7,ymm11,ymm6,ymm11

        shuffle4        ymm3,ymm5,ymm7,ymm5
        shuffle4        ymm8,ymm10,ymm3,ymm10
        shuffle4        ymm4,ymm6,ymm8,ymm6
        shuffle4        ymm9,ymm11,ymm4,ymm11

        shuffle2        ymm7,ymm8,ymm9,ymm8
        shuffle2        ymm5,ymm6,ymm7,ymm6
        shuffle2        ymm3,ymm4,ymm5,ymm4
        shuffle2        ymm10,ymm11,ymm3,ymm11

        /* store */
        vmovdqa         [rdi+(\offset+0)],ymm9
        vmovdqa         [rdi+(\offset+32)],ymm8
        vmovdqa         [rdi+(\offset+64)],ymm7
        vmovdqa         [rdi+(\offset+96)],ymm6
        vmovdqa         [rdi+(\offset+128)],ymm5
        vmovdqa         [rdi+(\offset+160)],ymm4
        vmovdqa         [rdi+(\offset+192)],ymm3
        vmovdqa         [rdi+(\offset+224)],ymm11
.endm

        .balign 4
S2N_BN_SYMBOL(mldsa_nttunpack):
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
        mov     rdi, rcx
#endif

        nttunpack_64_coefficients 0
        nttunpack_64_coefficients 256
        nttunpack_64_coefficients 512
        nttunpack_64_coefficients 768

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
        CFI_INC_RSP(176)
#endif

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mldsa_nttunpack)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
