// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Unpacking of 17-bit packed z polynomial coefficients for ML-DSA
// Output r[256] (signed 32-bit words), input b[576] (packed bytes)
//
// Unpacks polynomial z with 18-bit packed coefficients (GAMMA1 = 2^17),
// mapping packed [0, 2^18-1] to signed [-(2^17-1), 2^17] via GAMMA1 - x.
//
// extern void mldsa_polyz_unpack_17_x86(int32_t r[static 256], const uint8_t b[static 576]);
//
// Standard x86-64 ABI: RDI = r, RSI = b
// Microsoft x64 ABI:   RCX = r, RDX = b
// ----------------------------------------------------------------------------

// This implementation is derived from the public domain AVX2 Dilithium
// implementation (pq-crystals/dilithium) via the mldsa-native project.

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_polyz_unpack_17_x86)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mldsa_polyz_unpack_17_x86)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_polyz_unpack_17_x86)
        .text

// Unpack one block of 8 coefficients: gather two overlapping 128-bit loads
// from the packed input, byte-shuffle into 32-bit lanes, variable-shift and
// mask off the 18-bit fields, then form GAMMA1 - x and store the 256-bit
// result.
.macro zunpack17_block in_off, out_off
        vmovdqu xmm0, [rsi + \in_off]
        vmovdqu xmm5, [rsi + \in_off + 2]
        vinserti128 ymm0, ymm0, xmm5, 1
        vpshufb ymm0, ymm0, ymm1
        vpsrlvd ymm0, ymm0, ymm2
        vpand   ymm0, ymm0, ymm3
        vpsubd  ymm0, ymm4, ymm0
        vmovdqa [rdi + \out_off], ymm0
.endm

S2N_BN_SYMBOL(mldsa_polyz_unpack_17_x86):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Set up the shuffle table (ymm1), the per-lane shift counts (ymm2), the
// 18-bit field mask (ymm3), and the GAMMA1 = 2^17 broadcast (ymm4).
        movabs  rax, 0xff040302ff020100
        vmovq   xmm1, rax
        movabs  rax, 0xff080706ff060504
        vpinsrq xmm1, xmm1, rax, 1
        movabs  rax, 0xff1b1a19ff191817
        vmovq   xmm5, rax
        movabs  rax, 0xff1f1e1dff1d1c1b
        vpinsrq xmm5, xmm5, rax, 1
        vinserti128 ymm1, ymm1, xmm5, 1
        movabs  rax, 0x200000000
        vmovq   xmm2, rax
        movabs  rax, 0x600000004
        vpinsrq xmm2, xmm2, rax, 1
        vinserti128 ymm2, ymm2, xmm2, 1
        mov     eax, 0x3ffff
        vmovd   xmm3, eax
        vpbroadcastd ymm3, xmm3
        mov     eax, 0x20000
        vmovd   xmm4, eax
        vpbroadcastd ymm4, xmm4

// Process all 256 coefficients (32 blocks of 8 int32 each). Each input block
// is 18 bytes; each output block is 32 bytes.
        zunpack17_block 0, 0
        zunpack17_block 18, 32
        zunpack17_block 36, 64
        zunpack17_block 54, 96
        zunpack17_block 72, 128
        zunpack17_block 90, 160
        zunpack17_block 108, 192
        zunpack17_block 126, 224
        zunpack17_block 144, 256
        zunpack17_block 162, 288
        zunpack17_block 180, 320
        zunpack17_block 198, 352
        zunpack17_block 216, 384
        zunpack17_block 234, 416
        zunpack17_block 252, 448
        zunpack17_block 270, 480
        zunpack17_block 288, 512
        zunpack17_block 306, 544
        zunpack17_block 324, 576
        zunpack17_block 342, 608
        zunpack17_block 360, 640
        zunpack17_block 378, 672
        zunpack17_block 396, 704
        zunpack17_block 414, 736
        zunpack17_block 432, 768
        zunpack17_block 450, 800
        zunpack17_block 468, 832
        zunpack17_block 486, 864
        zunpack17_block 504, 896
        zunpack17_block 522, 928
        zunpack17_block 540, 960
        zunpack17_block 558, 992

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mldsa_polyz_unpack_17_x86)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif
