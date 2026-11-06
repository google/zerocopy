// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Pack ML-KEM polynomial coefficients as 12-bit numbers
// Input a[256] (signed 16-bit words); output r[384] (bytes)
//
// This accepts an array of 256 16-bit numbers assumed to be in the range
// 0 <= a[i] < 2^12 (typically they will be < 3329, the ML-KEM prime).
// It packs them into the output array as 12-bit unsigned numbers.
//
// extern void mlkem_tobytes(uint8_t r[static 384],const int16_t a[static 256]);

// Standard x86-64 ABI: RDI = r, RSI = a
// Microsoft x64 ABI:   RCX = r, RDX = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

.intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_tobytes)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_tobytes)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_tobytes)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_tobytes):
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
  mov rdi, rcx
  mov rsi, rdx
#endif

 mov eax,0xd010d01
 vmovd xmm0,eax
 vpbroadcastd ymm0,xmm0
 vmovdqa ymm5,[rsi]
 vmovdqa ymm6,[32+rsi]
 vmovdqa ymm7,[64+rsi]
 vmovdqa ymm8,[96+rsi]
 vmovdqa ymm9,[128+rsi]
 vmovdqa ymm10,[160+rsi]
 vmovdqa ymm11,[192+rsi]
 vmovdqa ymm12,[224+rsi]
 vpsllw ymm4,ymm6,0xc
 vpor ymm4,ymm5,ymm4
 vpsrlw ymm5,ymm6,0x4
 vpsllw ymm6,ymm7,0x8
 vpor ymm5,ymm6,ymm5
 vpsrlw ymm6,ymm7,0x8
 vpsllw ymm7,ymm8,0x4
 vpor ymm6,ymm7,ymm6
 vpsllw ymm7,ymm10,0xc
 vpor ymm7,ymm9,ymm7
 vpsrlw ymm8,ymm10,0x4
 vpsllw ymm9,ymm11,0x8
 vpor ymm8,ymm9,ymm8
 vpsrlw ymm9,ymm11,0x8
 vpsllw ymm10,ymm12,0x4
 vpor ymm9,ymm10,ymm9
 vpslld ymm3,ymm5,0x10
 vpblendw ymm3,ymm4,ymm3,0xaa
 vpsrld ymm4,ymm4,0x10
 vpblendw ymm5,ymm4,ymm5,0xaa
 vpslld ymm4,ymm7,0x10
 vpblendw ymm4,ymm6,ymm4,0xaa
 vpsrld ymm6,ymm6,0x10
 vpblendw ymm7,ymm6,ymm7,0xaa
 vpslld ymm6,ymm9,0x10
 vpblendw ymm6,ymm8,ymm6,0xaa
 vpsrld ymm8,ymm8,0x10
 vpblendw ymm9,ymm8,ymm9,0xaa
 vmovsldup ymm8,ymm4
 vpblendd ymm8,ymm3,ymm8,0xaa
 vpsrlq ymm3,ymm3,0x20
 vpblendd ymm4,ymm3,ymm4,0xaa
 vmovsldup ymm3,ymm5
 vpblendd ymm3,ymm6,ymm3,0xaa
 vpsrlq ymm6,ymm6,0x20
 vpblendd ymm5,ymm6,ymm5,0xaa
 vmovsldup ymm6,ymm9
 vpblendd ymm6,ymm7,ymm6,0xaa
 vpsrlq ymm7,ymm7,0x20
 vpblendd ymm9,ymm7,ymm9,0xaa
 vpunpcklqdq ymm7,ymm8,ymm3
 vpunpckhqdq ymm3,ymm8,ymm3
 vpunpcklqdq ymm8,ymm6,ymm4
 vpunpckhqdq ymm4,ymm6,ymm4
 vpunpcklqdq ymm6,ymm5,ymm9
 vpunpckhqdq ymm9,ymm5,ymm9
 vperm2i128 ymm5,ymm7,ymm8,0x20
 vperm2i128 ymm8,ymm7,ymm8,0x31
 vperm2i128 ymm7,ymm6,ymm3,0x20
 vperm2i128 ymm3,ymm6,ymm3,0x31
 vperm2i128 ymm6,ymm4,ymm9,0x20
 vperm2i128 ymm9,ymm4,ymm9,0x31
 vmovdqu [rdi],ymm5
 vmovdqu [32+rdi],ymm7
 vmovdqu [64+rdi],ymm6
 vmovdqu [96+rdi],ymm8
 vmovdqu [128+rdi],ymm3
 vmovdqu [160+rdi],ymm9
 vmovdqa ymm5,[256+rsi]
 vmovdqa ymm6,[288+rsi]
 vmovdqa ymm7,[320+rsi]
 vmovdqa ymm8,[352+rsi]
 vmovdqa ymm9,[384+rsi]
 vmovdqa ymm10,[416+rsi]
 vmovdqa ymm11,[448+rsi]
 vmovdqa ymm12,[480+rsi]
 vpsllw ymm4,ymm6,0xc
 vpor ymm4,ymm5,ymm4
 vpsrlw ymm5,ymm6,0x4
 vpsllw ymm6,ymm7,0x8
 vpor ymm5,ymm6,ymm5
 vpsrlw ymm6,ymm7,0x8
 vpsllw ymm7,ymm8,0x4
 vpor ymm6,ymm7,ymm6
 vpsllw ymm7,ymm10,0xc
 vpor ymm7,ymm9,ymm7
 vpsrlw ymm8,ymm10,0x4
 vpsllw ymm9,ymm11,0x8
 vpor ymm8,ymm9,ymm8
 vpsrlw ymm9,ymm11,0x8
 vpsllw ymm10,ymm12,0x4
 vpor ymm9,ymm10,ymm9
 vpslld ymm3,ymm5,0x10
 vpblendw ymm3,ymm4,ymm3,0xaa
 vpsrld ymm4,ymm4,0x10
 vpblendw ymm5,ymm4,ymm5,0xaa
 vpslld ymm4,ymm7,0x10
 vpblendw ymm4,ymm6,ymm4,0xaa
 vpsrld ymm6,ymm6,0x10
 vpblendw ymm7,ymm6,ymm7,0xaa
 vpslld ymm6,ymm9,0x10
 vpblendw ymm6,ymm8,ymm6,0xaa
 vpsrld ymm8,ymm8,0x10
 vpblendw ymm9,ymm8,ymm9,0xaa
 vmovsldup ymm8,ymm4
 vpblendd ymm8,ymm3,ymm8,0xaa
 vpsrlq ymm3,ymm3,0x20
 vpblendd ymm4,ymm3,ymm4,0xaa
 vmovsldup ymm3,ymm5
 vpblendd ymm3,ymm6,ymm3,0xaa
 vpsrlq ymm6,ymm6,0x20
 vpblendd ymm5,ymm6,ymm5,0xaa
 vmovsldup ymm6,ymm9
 vpblendd ymm6,ymm7,ymm6,0xaa
 vpsrlq ymm7,ymm7,0x20
 vpblendd ymm9,ymm7,ymm9,0xaa
 vpunpcklqdq ymm7,ymm8,ymm3
 vpunpckhqdq ymm3,ymm8,ymm3
 vpunpcklqdq ymm8,ymm6,ymm4
 vpunpckhqdq ymm4,ymm6,ymm4
 vpunpcklqdq ymm6,ymm5,ymm9
 vpunpckhqdq ymm9,ymm5,ymm9
 vperm2i128 ymm5,ymm7,ymm8,0x20
 vperm2i128 ymm8,ymm7,ymm8,0x31
 vperm2i128 ymm7,ymm6,ymm3,0x20
 vperm2i128 ymm3,ymm6,ymm3,0x31
 vperm2i128 ymm6,ymm4,ymm9,0x20
 vperm2i128 ymm9,ymm4,ymm9,0x31
 vmovdqu [192+rdi],ymm5
 vmovdqu [224+rdi],ymm7
 vmovdqu [256+rdi],ymm6
 vmovdqu [288+rdi],ymm8
 vmovdqu [320+rdi],ymm3
 vmovdqu [352+rdi],ymm9

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


S2N_BN_SIZE_DIRECTIVE(mlkem_tobytes)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
