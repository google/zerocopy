// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Conversion of ML-KEM polynomial coefficients to Montgomery form
// Input a[256] (signed 16-bit words); output a[256] (signed 16-bit words)
//
// This converts each element of the 256-element array of 16-bit signed
// integers modulo 3329 into Montgomery form, giving a signed result
// satisfying (output[i] == 2^16 * input[i]) (mod 3329), without full
// modular reduction but with |output[i]| < 3329 guaranteed.
//
// extern void mlkem_tomont(int16_t a[static 256]);
//
// Standard x86 ABI: RDI = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

.intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_tomont)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_tomont)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_tomont)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_tomont):
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

 mov eax,0xd010d01
 vmovd xmm0,eax
 vpbroadcastd ymm0,xmm0
 mov eax,0x50495049
 vmovd xmm1,eax
 vpbroadcastd ymm1,xmm1
 mov eax,0x5490549
 vmovd xmm2,eax
 vpbroadcastd ymm2,xmm2
 vmovdqa ymm3,[rdi]
 vmovdqa ymm4,[32+rdi]
 vmovdqa ymm5,[64+rdi]
 vmovdqa ymm6,[96+rdi]
 vmovdqa ymm7,[128+rdi]
 vmovdqa ymm8,[160+rdi]
 vmovdqa ymm9,[192+rdi]
 vmovdqa ymm10,[224+rdi]
 vpmullw ymm11,ymm3,ymm1
 vpmulhw ymm3,ymm3,ymm2
 vpmulhw ymm11,ymm11,ymm0
 vpsubw ymm3,ymm3,ymm11
 vpmullw ymm12,ymm4,ymm1
 vpmulhw ymm4,ymm4,ymm2
 vpmulhw ymm12,ymm12,ymm0
 vpsubw ymm4,ymm4,ymm12
 vpmullw ymm13,ymm5,ymm1
 vpmulhw ymm5,ymm5,ymm2
 vpmulhw ymm13,ymm13,ymm0
 vpsubw ymm5,ymm5,ymm13
 vpmullw ymm14,ymm6,ymm1
 vpmulhw ymm6,ymm6,ymm2
 vpmulhw ymm14,ymm14,ymm0
 vpsubw ymm6,ymm6,ymm14
 vpmullw ymm15,ymm7,ymm1
 vpmulhw ymm7,ymm7,ymm2
 vpmulhw ymm15,ymm15,ymm0
 vpsubw ymm7,ymm7,ymm15
 vpmullw ymm11,ymm8,ymm1
 vpmulhw ymm8,ymm8,ymm2
 vpmulhw ymm11,ymm11,ymm0
 vpsubw ymm8,ymm8,ymm11
 vpmullw ymm12,ymm9,ymm1
 vpmulhw ymm9,ymm9,ymm2
 vpmulhw ymm12,ymm12,ymm0
 vpsubw ymm9,ymm9,ymm12
 vpmullw ymm13,ymm10,ymm1
 vpmulhw ymm10,ymm10,ymm2
 vpmulhw ymm13,ymm13,ymm0
 vpsubw ymm10,ymm10,ymm13
 vmovdqa [rdi],ymm3
 vmovdqa [32+rdi],ymm4
 vmovdqa [64+rdi],ymm5
 vmovdqa [96+rdi],ymm6
 vmovdqa [128+rdi],ymm7
 vmovdqa [160+rdi],ymm8
 vmovdqa [192+rdi],ymm9
 vmovdqa [224+rdi],ymm10
 vmovdqa ymm3,[256+rdi]
 vmovdqa ymm4,[288+rdi]
 vmovdqa ymm5,[320+rdi]
 vmovdqa ymm6,[352+rdi]
 vmovdqa ymm7,[384+rdi]
 vmovdqa ymm8,[416+rdi]
 vmovdqa ymm9,[448+rdi]
 vmovdqa ymm10,[480+rdi]
 vpmullw ymm11,ymm3,ymm1
 vpmulhw ymm3,ymm3,ymm2
 vpmulhw ymm11,ymm11,ymm0
 vpsubw ymm3,ymm3,ymm11
 vpmullw ymm12,ymm4,ymm1
 vpmulhw ymm4,ymm4,ymm2
 vpmulhw ymm12,ymm12,ymm0
 vpsubw ymm4,ymm4,ymm12
 vpmullw ymm13,ymm5,ymm1
 vpmulhw ymm5,ymm5,ymm2
 vpmulhw ymm13,ymm13,ymm0
 vpsubw ymm5,ymm5,ymm13
 vpmullw ymm14,ymm6,ymm1
 vpmulhw ymm6,ymm6,ymm2
 vpmulhw ymm14,ymm14,ymm0
 vpsubw ymm6,ymm6,ymm14
 vpmullw ymm15,ymm7,ymm1
 vpmulhw ymm7,ymm7,ymm2
 vpmulhw ymm15,ymm15,ymm0
 vpsubw ymm7,ymm7,ymm15
 vpmullw ymm11,ymm8,ymm1
 vpmulhw ymm8,ymm8,ymm2
 vpmulhw ymm11,ymm11,ymm0
 vpsubw ymm8,ymm8,ymm11
 vpmullw ymm12,ymm9,ymm1
 vpmulhw ymm9,ymm9,ymm2
 vpmulhw ymm12,ymm12,ymm0
 vpsubw ymm9,ymm9,ymm12
 vpmullw ymm13,ymm10,ymm1
 vpmulhw ymm10,ymm10,ymm2
 vpmulhw ymm13,ymm13,ymm0
 vpsubw ymm10,ymm10,ymm13
 vmovdqa [256+rdi],ymm3
 vmovdqa [288+rdi],ymm4
 vmovdqa [320+rdi],ymm5
 vmovdqa [352+rdi],ymm6
 vmovdqa [384+rdi],ymm7
 vmovdqa [416+rdi],ymm8
 vmovdqa [448+rdi],ymm9
 vmovdqa [480+rdi],ymm10

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

S2N_BN_SIZE_DIRECTIVE(mlkem_tomont)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
