// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Reorder ML-KEM polynomial coefficients for x86 implementation
// Input a[256] (signed 16-bit words); output a[256] (signed 16-bit words)
//
// This accepts an array of 256 16-bit numbers and reorders them.
//
// extern void mlkem_unpack(int16_t a[static 256]);

// Standard x86-64 ABI: RDI = a
// Microsoft x64 ABI:   RCX = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

.intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_unpack)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_unpack)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_unpack)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_unpack):
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
 mov rdi, rcx
 mov rsi, rdx
#endif

 vmovdqa ymm4,[rdi]
 vmovdqa ymm5,[32+rdi]
 vmovdqa ymm6,[64+rdi]
 vmovdqa ymm7,[96+rdi]
 vmovdqa ymm8,[128+rdi]
 vmovdqa ymm9,[160+rdi]
 vmovdqa ymm10,[192+rdi]
 vmovdqa ymm11,[224+rdi]
 vperm2i128 ymm3,ymm4,ymm8,0x20
 vperm2i128 ymm8,ymm4,ymm8,0x31
 vperm2i128 ymm4,ymm5,ymm9,0x20
 vperm2i128 ymm9,ymm5,ymm9,0x31
 vperm2i128 ymm5,ymm6,ymm10,0x20
 vperm2i128 ymm10,ymm6,ymm10,0x31
 vperm2i128 ymm6,ymm7,ymm11,0x20
 vperm2i128 ymm11,ymm7,ymm11,0x31
 vpunpcklqdq ymm7,ymm3,ymm5
 vpunpckhqdq ymm5,ymm3,ymm5
 vpunpcklqdq ymm3,ymm8,ymm10
 vpunpckhqdq ymm10,ymm8,ymm10
 vpunpcklqdq ymm8,ymm4,ymm6
 vpunpckhqdq ymm6,ymm4,ymm6
 vpunpcklqdq ymm4,ymm9,ymm11
 vpunpckhqdq ymm11,ymm9,ymm11
 vmovsldup ymm9,ymm8
 vpblendd ymm9,ymm7,ymm9,0xaa
 vpsrlq ymm7,ymm7,0x20
 vpblendd ymm8,ymm7,ymm8,0xaa
 vmovsldup ymm7,ymm6
 vpblendd ymm7,ymm5,ymm7,0xaa
 vpsrlq ymm5,ymm5,0x20
 vpblendd ymm6,ymm5,ymm6,0xaa
 vmovsldup ymm5,ymm4
 vpblendd ymm5,ymm3,ymm5,0xaa
 vpsrlq ymm3,ymm3,0x20
 vpblendd ymm4,ymm3,ymm4,0xaa
 vmovsldup ymm3,ymm11
 vpblendd ymm3,ymm10,ymm3,0xaa
 vpsrlq ymm10,ymm10,0x20
 vpblendd ymm11,ymm10,ymm11,0xaa
 vpslld ymm10,ymm5,0x10
 vpblendw ymm10,ymm9,ymm10,0xaa
 vpsrld ymm9,ymm9,0x10
 vpblendw ymm5,ymm9,ymm5,0xaa
 vpslld ymm9,ymm4,0x10
 vpblendw ymm9,ymm8,ymm9,0xaa
 vpsrld ymm8,ymm8,0x10
 vpblendw ymm4,ymm8,ymm4,0xaa
 vpslld ymm8,ymm3,0x10
 vpblendw ymm8,ymm7,ymm8,0xaa
 vpsrld ymm7,ymm7,0x10
 vpblendw ymm3,ymm7,ymm3,0xaa
 vpslld ymm7,ymm11,0x10
 vpblendw ymm7,ymm6,ymm7,0xaa
 vpsrld ymm6,ymm6,0x10
 vpblendw ymm11,ymm6,ymm11,0xaa
 vmovdqa [rdi],ymm10
 vmovdqa [32+rdi],ymm5
 vmovdqa [64+rdi],ymm9
 vmovdqa [96+rdi],ymm4
 vmovdqa [128+rdi],ymm8
 vmovdqa [160+rdi],ymm3
 vmovdqa [192+rdi],ymm7
 vmovdqa [224+rdi],ymm11
 vmovdqa ymm4,[256+rdi]
 vmovdqa ymm5,[288+rdi]
 vmovdqa ymm6,[320+rdi]
 vmovdqa ymm7,[352+rdi]
 vmovdqa ymm8,[384+rdi]
 vmovdqa ymm9,[416+rdi]
 vmovdqa ymm10,[448+rdi]
 vmovdqa ymm11,[480+rdi]
 vperm2i128 ymm3,ymm4,ymm8,0x20
 vperm2i128 ymm8,ymm4,ymm8,0x31
 vperm2i128 ymm4,ymm5,ymm9,0x20
 vperm2i128 ymm9,ymm5,ymm9,0x31
 vperm2i128 ymm5,ymm6,ymm10,0x20
 vperm2i128 ymm10,ymm6,ymm10,0x31
 vperm2i128 ymm6,ymm7,ymm11,0x20
 vperm2i128 ymm11,ymm7,ymm11,0x31
 vpunpcklqdq ymm7,ymm3,ymm5
 vpunpckhqdq ymm5,ymm3,ymm5
 vpunpcklqdq ymm3,ymm8,ymm10
 vpunpckhqdq ymm10,ymm8,ymm10
 vpunpcklqdq ymm8,ymm4,ymm6
 vpunpckhqdq ymm6,ymm4,ymm6
 vpunpcklqdq ymm4,ymm9,ymm11
 vpunpckhqdq ymm11,ymm9,ymm11
 vmovsldup ymm9,ymm8
 vpblendd ymm9,ymm7,ymm9,0xaa
 vpsrlq ymm7,ymm7,0x20
 vpblendd ymm8,ymm7,ymm8,0xaa
 vmovsldup ymm7,ymm6
 vpblendd ymm7,ymm5,ymm7,0xaa
 vpsrlq ymm5,ymm5,0x20
 vpblendd ymm6,ymm5,ymm6,0xaa
 vmovsldup ymm5,ymm4
 vpblendd ymm5,ymm3,ymm5,0xaa
 vpsrlq ymm3,ymm3,0x20
 vpblendd ymm4,ymm3,ymm4,0xaa
 vmovsldup ymm3,ymm11
 vpblendd ymm3,ymm10,ymm3,0xaa
 vpsrlq ymm10,ymm10,0x20
 vpblendd ymm11,ymm10,ymm11,0xaa
 vpslld ymm10,ymm5,0x10
 vpblendw ymm10,ymm9,ymm10,0xaa
 vpsrld ymm9,ymm9,0x10
 vpblendw ymm5,ymm9,ymm5,0xaa
 vpslld ymm9,ymm4,0x10
 vpblendw ymm9,ymm8,ymm9,0xaa
 vpsrld ymm8,ymm8,0x10
 vpblendw ymm4,ymm8,ymm4,0xaa
 vpslld ymm8,ymm3,0x10
 vpblendw ymm8,ymm7,ymm8,0xaa
 vpsrld ymm7,ymm7,0x10
 vpblendw ymm3,ymm7,ymm3,0xaa
 vpslld ymm7,ymm11,0x10
 vpblendw ymm7,ymm6,ymm7,0xaa
 vpsrld ymm6,ymm6,0x10
 vpblendw ymm11,ymm6,ymm11,0xaa
 vmovdqa [256+rdi],ymm10
 vmovdqa [288+rdi],ymm5
 vmovdqa [320+rdi],ymm9
 vmovdqa [352+rdi],ymm4
 vmovdqa [384+rdi],ymm8
 vmovdqa [416+rdi],ymm3
 vmovdqa [448+rdi],ymm7
 vmovdqa [480+rdi],ymm11

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

S2N_BN_SIZE_DIRECTIVE(mlkem_unpack)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
