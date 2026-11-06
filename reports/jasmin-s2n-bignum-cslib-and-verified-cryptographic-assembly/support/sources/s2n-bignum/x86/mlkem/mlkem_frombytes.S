// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Unpack ML-KEM polynomial coefficients as 12-bit numbers
// Input a[384] (bytes); output r[256] (signed 16-bit words)
//
// This accepts an array of 384 bytes and unpacks them into 256 16-bit numbers
// in the range 0 <= a[i] < 2^12 (typically they will be < 3329, the ML-KEM prime).
//
// extern void mlkem_frombytes(int16_t r[static 256],const uint8_t a[static 384]);

// Standard x86-64 ABI: RDI = r, RSI = a
// Microsoft x64 ABI:   RCX = r, RDX = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

.intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_frombytes)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_frombytes)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_frombytes)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_frombytes):
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

 mov eax,0xfff0fff
 vmovd xmm0,eax
 vpbroadcastd ymm0,xmm0
 vmovdqu ymm4,[rsi]
 vmovdqu ymm5,[32+rsi]
 vmovdqu ymm6,[64+rsi]
 vmovdqu ymm7,[96+rsi]
 vmovdqu ymm8,[128+rsi]
 vmovdqu ymm9,[160+rsi]
 vperm2i128 ymm3,ymm4,ymm7,0x20
 vperm2i128 ymm7,ymm4,ymm7,0x31
 vperm2i128 ymm4,ymm5,ymm8,0x20
 vperm2i128 ymm8,ymm5,ymm8,0x31
 vperm2i128 ymm5,ymm6,ymm9,0x20
 vperm2i128 ymm9,ymm6,ymm9,0x31
 vpunpcklqdq ymm6,ymm3,ymm8
 vpunpckhqdq ymm8,ymm3,ymm8
 vpunpcklqdq ymm3,ymm7,ymm5
 vpunpckhqdq ymm5,ymm7,ymm5
 vpunpcklqdq ymm7,ymm4,ymm9
 vpunpckhqdq ymm9,ymm4,ymm9
 vmovsldup ymm4,ymm5
 vpblendd ymm4,ymm6,ymm4,0xaa
 vpsrlq ymm6,ymm6,0x20
 vpblendd ymm5,ymm6,ymm5,0xaa
 vmovsldup ymm6,ymm7
 vpblendd ymm6,ymm8,ymm6,0xaa
 vpsrlq ymm8,ymm8,0x20
 vpblendd ymm7,ymm8,ymm7,0xaa
 vmovsldup ymm8,ymm9
 vpblendd ymm8,ymm3,ymm8,0xaa
 vpsrlq ymm3,ymm3,0x20
 vpblendd ymm9,ymm3,ymm9,0xaa
 vpslld ymm10,ymm7,0x10
 vpblendw ymm10,ymm4,ymm10,0xaa
 vpsrld ymm4,ymm4,0x10
 vpblendw ymm7,ymm4,ymm7,0xaa
 vpslld ymm4,ymm8,0x10
 vpblendw ymm4,ymm5,ymm4,0xaa
 vpsrld ymm5,ymm5,0x10
 vpblendw ymm8,ymm5,ymm8,0xaa
 vpslld ymm5,ymm9,0x10
 vpblendw ymm5,ymm6,ymm5,0xaa
 vpsrld ymm6,ymm6,0x10
 vpblendw ymm9,ymm6,ymm9,0xaa
 vpsrlw ymm11,ymm10,0xc
 vpsllw ymm12,ymm7,0x4
 vpor ymm11,ymm12,ymm11
 vpand ymm10,ymm10,ymm0
 vpand ymm11,ymm11,ymm0
 vpsrlw ymm12,ymm7,0x8
 vpsllw ymm13,ymm4,0x8
 vpor ymm12,ymm13,ymm12
 vpand ymm12,ymm12,ymm0
 vpsrlw ymm13,ymm4,0x4
 vpand ymm13,ymm13,ymm0
 vpsrlw ymm14,ymm8,0xc
 vpsllw ymm15,ymm5,0x4
 vpor ymm14,ymm15,ymm14
 vpand ymm8,ymm8,ymm0
 vpand ymm14,ymm14,ymm0
 vpsrlw ymm15,ymm5,0x8
 vpsllw ymm1,ymm9,0x8
 vpor ymm15,ymm1,ymm15
 vpand ymm15,ymm15,ymm0
 vpsrlw ymm1,ymm9,0x4
 vpand ymm1,ymm1,ymm0
 vmovdqa [rdi],ymm10
 vmovdqa [32+rdi],ymm11
 vmovdqa [64+rdi],ymm12
 vmovdqa [96+rdi],ymm13
 vmovdqa [128+rdi],ymm8
 vmovdqa [160+rdi],ymm14
 vmovdqa [192+rdi],ymm15
 vmovdqa [224+rdi],ymm1
 vmovdqu ymm4,[192+rsi]
 vmovdqu ymm5,[224+rsi]
 vmovdqu ymm6,[256+rsi]
 vmovdqu ymm7,[288+rsi]
 vmovdqu ymm8,[320+rsi]
 vmovdqu ymm9,[352+rsi]
 vperm2i128 ymm3,ymm4,ymm7,0x20
 vperm2i128 ymm7,ymm4,ymm7,0x31
 vperm2i128 ymm4,ymm5,ymm8,0x20
 vperm2i128 ymm8,ymm5,ymm8,0x31
 vperm2i128 ymm5,ymm6,ymm9,0x20
 vperm2i128 ymm9,ymm6,ymm9,0x31
 vpunpcklqdq ymm6,ymm3,ymm8
 vpunpckhqdq ymm8,ymm3,ymm8
 vpunpcklqdq ymm3,ymm7,ymm5
 vpunpckhqdq ymm5,ymm7,ymm5
 vpunpcklqdq ymm7,ymm4,ymm9
 vpunpckhqdq ymm9,ymm4,ymm9
 vmovsldup ymm4,ymm5
 vpblendd ymm4,ymm6,ymm4,0xaa
 vpsrlq ymm6,ymm6,0x20
 vpblendd ymm5,ymm6,ymm5,0xaa
 vmovsldup ymm6,ymm7
 vpblendd ymm6,ymm8,ymm6,0xaa
 vpsrlq ymm8,ymm8,0x20
 vpblendd ymm7,ymm8,ymm7,0xaa
 vmovsldup ymm8,ymm9
 vpblendd ymm8,ymm3,ymm8,0xaa
 vpsrlq ymm3,ymm3,0x20
 vpblendd ymm9,ymm3,ymm9,0xaa
 vpslld ymm10,ymm7,0x10
 vpblendw ymm10,ymm4,ymm10,0xaa
 vpsrld ymm4,ymm4,0x10
 vpblendw ymm7,ymm4,ymm7,0xaa
 vpslld ymm4,ymm8,0x10
 vpblendw ymm4,ymm5,ymm4,0xaa
 vpsrld ymm5,ymm5,0x10
 vpblendw ymm8,ymm5,ymm8,0xaa
 vpslld ymm5,ymm9,0x10
 vpblendw ymm5,ymm6,ymm5,0xaa
 vpsrld ymm6,ymm6,0x10
 vpblendw ymm9,ymm6,ymm9,0xaa
 vpsrlw ymm11,ymm10,0xc
 vpsllw ymm12,ymm7,0x4
 vpor ymm11,ymm12,ymm11
 vpand ymm10,ymm10,ymm0
 vpand ymm11,ymm11,ymm0
 vpsrlw ymm12,ymm7,0x8
 vpsllw ymm13,ymm4,0x8
 vpor ymm12,ymm13,ymm12
 vpand ymm12,ymm12,ymm0
 vpsrlw ymm13,ymm4,0x4
 vpand ymm13,ymm13,ymm0
 vpsrlw ymm14,ymm8,0xc
 vpsllw ymm15,ymm5,0x4
 vpor ymm14,ymm15,ymm14
 vpand ymm8,ymm8,ymm0
 vpand ymm14,ymm14,ymm0
 vpsrlw ymm15,ymm5,0x8
 vpsllw ymm1,ymm9,0x8
 vpor ymm15,ymm1,ymm15
 vpand ymm15,ymm15,ymm0
 vpsrlw ymm1,ymm9,0x4
 vpand ymm1,ymm1,ymm0
 vmovdqa [256+rdi],ymm10
 vmovdqa [288+rdi],ymm11
 vmovdqa [320+rdi],ymm12
 vmovdqa [352+rdi],ymm13
 vmovdqa [384+rdi],ymm8
 vmovdqa [416+rdi],ymm14
 vmovdqa [448+rdi],ymm15
 vmovdqa [480+rdi],ymm1

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


S2N_BN_SIZE_DIRECTIVE(mlkem_frombytes)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
