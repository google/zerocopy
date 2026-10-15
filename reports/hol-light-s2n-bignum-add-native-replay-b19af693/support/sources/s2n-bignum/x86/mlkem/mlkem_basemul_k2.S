// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Scalar product of 2-element polynomial vectors in NTT domain, with mulcache
// Inputs a[512], b[512], bt[256] (signed 16-bit words); output r[256] (signed 16-bit words)
//
// The inputs a and b are considered as 2-element vectors of linear
// polynomials in the NTT domain (in Montgomery form), and the bt
// argument an analogous 2-element vector of mulcaches for the bi:
//
//   a0 = a[0..255], a1 = a[256..511]
//   b0 = b[0..255], b1 = b[256..511]
//   bt0 = bt[0..127], bt1 = bt[128..255]
//
// Scalar multiplication of those 2-element vectors is performed,
// with base multiplication in Fq[X]/(X^2-zeta^i'), with zeta^i'
// being a power of zeta = 17, with i bit-reversed as used for NTTs,
// making use of the mulcache for optimization.
//
// Coefficients of a0 and a1 are assumed <= 2^12 and the bts are
// assumed to be as computed by mlkem_mulcache_compute.
//
// extern void mlkem_basemul_k2
//      (int16_t r[static 256],const int16_t a[static 512],
//       const int16_t b[static 512], const int16_t bt[static 256]);
//
// Standard x86-64 ABI: RDI = a
// Microsoft x64 ABI:   RCX = a
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

.intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_basemul_k2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_basemul_k2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_basemul_k2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_basemul_k2):
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
        CFI_STACKSAVE(rdi,144)
        CFI_STACKSAVE(rsi,152)
        CFI_STACKSAVE(rdx,160)
        CFI_STACKSAVE(rcx,168)
        mov rdi, rcx
        mov rsi, rdx
        mov rdx, r8
        mov rcx, r9
#endif

        mov eax,0xd010d01
        vmovd xmm0,eax
        vpbroadcastd ymm0,xmm0
        mov eax,0xf301f301
        vmovd xmm1,eax
        vpbroadcastd ymm1,xmm1
        vmovdqa ymm2,[rsi]
        vmovdqa ymm3,[32+rsi]
        vmovdqa ymm4,[rdx]
        vmovdqa ymm5,[32+rdx]
        vmovdqa ymm6,[rcx]
        vpmullw ymm13,ymm1,ymm2
        vpmullw ymm14,ymm1,ymm3
        vpmullw ymm7,ymm4,ymm13
        vpmullw ymm9,ymm5,ymm13
        vpmullw ymm8,ymm6,ymm14
        vpmullw ymm10,ymm4,ymm14
        vpmulhw ymm7,ymm0,ymm7
        vpmulhw ymm9,ymm0,ymm9
        vpmulhw ymm8,ymm0,ymm8
        vpmulhw ymm10,ymm0,ymm10
        vpmulhw ymm11,ymm4,ymm2
        vpmulhw ymm12,ymm5,ymm2
        vpmulhw ymm13,ymm6,ymm3
        vpmulhw ymm14,ymm4,ymm3
        vpsubw ymm7,ymm11,ymm7
        vpsubw ymm9,ymm12,ymm9
        vpsubw ymm8,ymm13,ymm8
        vpsubw ymm10,ymm14,ymm10
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa [rdi],ymm7
        vmovdqa [32+rdi],ymm9
        vmovdqa ymm2,[64+rsi]
        vmovdqa ymm3,[96+rsi]
        vmovdqa ymm4,[64+rdx]
        vmovdqa ymm5,[96+rdx]
        vmovdqa ymm6,[32+rcx]
        vpmullw ymm13,ymm1,ymm2
        vpmullw ymm14,ymm1,ymm3
        vpmullw ymm7,ymm4,ymm13
        vpmullw ymm9,ymm5,ymm13
        vpmullw ymm8,ymm6,ymm14
        vpmullw ymm10,ymm4,ymm14
        vpmulhw ymm7,ymm0,ymm7
        vpmulhw ymm9,ymm0,ymm9
        vpmulhw ymm8,ymm0,ymm8
        vpmulhw ymm10,ymm0,ymm10
        vpmulhw ymm11,ymm4,ymm2
        vpmulhw ymm12,ymm5,ymm2
        vpmulhw ymm13,ymm6,ymm3
        vpmulhw ymm14,ymm4,ymm3
        vpsubw ymm7,ymm11,ymm7
        vpsubw ymm9,ymm12,ymm9
        vpsubw ymm8,ymm8,ymm13
        vpsubw ymm10,ymm14,ymm10
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa [64+rdi],ymm7
        vmovdqa [96+rdi],ymm9
        vmovdqa ymm2,[128+rsi]
        vmovdqa ymm3,[160+rsi]
        vmovdqa ymm4,[128+rdx]
        vmovdqa ymm5,[160+rdx]
        vmovdqa ymm6,[64+rcx]
        vpmullw ymm13,ymm1,ymm2
        vpmullw ymm14,ymm1,ymm3
        vpmullw ymm7,ymm4,ymm13
        vpmullw ymm9,ymm5,ymm13
        vpmullw ymm8,ymm6,ymm14
        vpmullw ymm10,ymm4,ymm14
        vpmulhw ymm7,ymm0,ymm7
        vpmulhw ymm9,ymm0,ymm9
        vpmulhw ymm8,ymm0,ymm8
        vpmulhw ymm10,ymm0,ymm10
        vpmulhw ymm11,ymm4,ymm2
        vpmulhw ymm12,ymm5,ymm2
        vpmulhw ymm13,ymm6,ymm3
        vpmulhw ymm14,ymm4,ymm3
        vpsubw ymm7,ymm11,ymm7
        vpsubw ymm9,ymm12,ymm9
        vpsubw ymm8,ymm13,ymm8
        vpsubw ymm10,ymm14,ymm10
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa [128+rdi],ymm7
        vmovdqa [160+rdi],ymm9
        vmovdqa ymm2,[192+rsi]
        vmovdqa ymm3,[224+rsi]
        vmovdqa ymm4,[192+rdx]
        vmovdqa ymm5,[224+rdx]
        vmovdqa ymm6,[96+rcx]
        vpmullw ymm13,ymm1,ymm2
        vpmullw ymm14,ymm1,ymm3
        vpmullw ymm7,ymm4,ymm13
        vpmullw ymm9,ymm5,ymm13
        vpmullw ymm8,ymm6,ymm14
        vpmullw ymm10,ymm4,ymm14
        vpmulhw ymm7,ymm0,ymm7
        vpmulhw ymm9,ymm0,ymm9
        vpmulhw ymm8,ymm0,ymm8
        vpmulhw ymm10,ymm0,ymm10
        vpmulhw ymm11,ymm4,ymm2
        vpmulhw ymm12,ymm5,ymm2
        vpmulhw ymm13,ymm6,ymm3
        vpmulhw ymm14,ymm4,ymm3
        vpsubw ymm7,ymm11,ymm7
        vpsubw ymm9,ymm12,ymm9
        vpsubw ymm8,ymm8,ymm13
        vpsubw ymm10,ymm14,ymm10
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa [192+rdi],ymm7
        vmovdqa [224+rdi],ymm9
        vmovdqa ymm2,[256+rsi]
        vmovdqa ymm3,[288+rsi]
        vmovdqa ymm4,[256+rdx]
        vmovdqa ymm5,[288+rdx]
        vmovdqa ymm6,[128+rcx]
        vpmullw ymm13,ymm1,ymm2
        vpmullw ymm14,ymm1,ymm3
        vpmullw ymm7,ymm4,ymm13
        vpmullw ymm9,ymm5,ymm13
        vpmullw ymm8,ymm6,ymm14
        vpmullw ymm10,ymm4,ymm14
        vpmulhw ymm7,ymm0,ymm7
        vpmulhw ymm9,ymm0,ymm9
        vpmulhw ymm8,ymm0,ymm8
        vpmulhw ymm10,ymm0,ymm10
        vpmulhw ymm11,ymm4,ymm2
        vpmulhw ymm12,ymm5,ymm2
        vpmulhw ymm13,ymm6,ymm3
        vpmulhw ymm14,ymm4,ymm3
        vpsubw ymm7,ymm11,ymm7
        vpsubw ymm9,ymm12,ymm9
        vpsubw ymm8,ymm13,ymm8
        vpsubw ymm10,ymm14,ymm10
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa [256+rdi],ymm7
        vmovdqa [288+rdi],ymm9
        vmovdqa ymm2,[320+rsi]
        vmovdqa ymm3,[352+rsi]
        vmovdqa ymm4,[320+rdx]
        vmovdqa ymm5,[352+rdx]
        vmovdqa ymm6,[160+rcx]
        vpmullw ymm13,ymm1,ymm2
        vpmullw ymm14,ymm1,ymm3
        vpmullw ymm7,ymm4,ymm13
        vpmullw ymm9,ymm5,ymm13
        vpmullw ymm8,ymm6,ymm14
        vpmullw ymm10,ymm4,ymm14
        vpmulhw ymm7,ymm0,ymm7
        vpmulhw ymm9,ymm0,ymm9
        vpmulhw ymm8,ymm0,ymm8
        vpmulhw ymm10,ymm0,ymm10
        vpmulhw ymm11,ymm4,ymm2
        vpmulhw ymm12,ymm5,ymm2
        vpmulhw ymm13,ymm6,ymm3
        vpmulhw ymm14,ymm4,ymm3
        vpsubw ymm7,ymm11,ymm7
        vpsubw ymm9,ymm12,ymm9
        vpsubw ymm8,ymm8,ymm13
        vpsubw ymm10,ymm14,ymm10
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa [320+rdi],ymm7
        vmovdqa [352+rdi],ymm9
        vmovdqa ymm2,[384+rsi]
        vmovdqa ymm3,[416+rsi]
        vmovdqa ymm4,[384+rdx]
        vmovdqa ymm5,[416+rdx]
        vmovdqa ymm6,[192+rcx]
        vpmullw ymm13,ymm1,ymm2
        vpmullw ymm14,ymm1,ymm3
        vpmullw ymm7,ymm4,ymm13
        vpmullw ymm9,ymm5,ymm13
        vpmullw ymm8,ymm6,ymm14
        vpmullw ymm10,ymm4,ymm14
        vpmulhw ymm7,ymm0,ymm7
        vpmulhw ymm9,ymm0,ymm9
        vpmulhw ymm8,ymm0,ymm8
        vpmulhw ymm10,ymm0,ymm10
        vpmulhw ymm11,ymm4,ymm2
        vpmulhw ymm12,ymm5,ymm2
        vpmulhw ymm13,ymm6,ymm3
        vpmulhw ymm14,ymm4,ymm3
        vpsubw ymm7,ymm11,ymm7
        vpsubw ymm9,ymm12,ymm9
        vpsubw ymm8,ymm13,ymm8
        vpsubw ymm10,ymm14,ymm10
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa [384+rdi],ymm7
        vmovdqa [416+rdi],ymm9
        vmovdqa ymm2,[448+rsi]
        vmovdqa ymm3,[480+rsi]
        vmovdqa ymm4,[448+rdx]
        vmovdqa ymm5,[480+rdx]
        vmovdqa ymm6,[224+rcx]
        vpmullw ymm13,ymm1,ymm2
        vpmullw ymm14,ymm1,ymm3
        vpmullw ymm7,ymm4,ymm13
        vpmullw ymm9,ymm5,ymm13
        vpmullw ymm8,ymm6,ymm14
        vpmullw ymm10,ymm4,ymm14
        vpmulhw ymm7,ymm0,ymm7
        vpmulhw ymm9,ymm0,ymm9
        vpmulhw ymm8,ymm0,ymm8
        vpmulhw ymm10,ymm0,ymm10
        vpmulhw ymm11,ymm4,ymm2
        vpmulhw ymm12,ymm5,ymm2
        vpmulhw ymm13,ymm6,ymm3
        vpmulhw ymm14,ymm4,ymm3
        vpsubw ymm7,ymm11,ymm7
        vpsubw ymm9,ymm12,ymm9
        vpsubw ymm8,ymm8,ymm13
        vpsubw ymm10,ymm14,ymm10
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa [448+rdi],ymm7
        vmovdqa [480+rdi],ymm9
        vmovdqa ymm2,[512+rsi]
        vmovdqa ymm3,[544+rsi]
        vmovdqa ymm4,[512+rdx]
        vmovdqa ymm5,[544+rdx]
        vmovdqa ymm6,[256+rcx]
        vpmullw ymm13,ymm1,ymm2
        vpmullw ymm14,ymm1,ymm3
        vpmullw ymm7,ymm4,ymm13
        vpmullw ymm9,ymm5,ymm13
        vpmullw ymm8,ymm6,ymm14
        vpmullw ymm10,ymm4,ymm14
        vpmulhw ymm7,ymm0,ymm7
        vpmulhw ymm9,ymm0,ymm9
        vpmulhw ymm8,ymm0,ymm8
        vpmulhw ymm10,ymm0,ymm10
        vpmulhw ymm11,ymm4,ymm2
        vpmulhw ymm12,ymm5,ymm2
        vpmulhw ymm13,ymm6,ymm3
        vpmulhw ymm14,ymm4,ymm3
        vpsubw ymm7,ymm11,ymm7
        vpsubw ymm9,ymm12,ymm9
        vpsubw ymm8,ymm13,ymm8
        vpsubw ymm10,ymm14,ymm10
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa ymm8,[rdi]
        vmovdqa ymm10,[32+rdi]
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa [rdi],ymm7
        vmovdqa [32+rdi],ymm9
        vmovdqa ymm2,[576+rsi]
        vmovdqa ymm3,[608+rsi]
        vmovdqa ymm4,[576+rdx]
        vmovdqa ymm5,[608+rdx]
        vmovdqa ymm6,[288+rcx]
        vpmullw ymm13,ymm1,ymm2
        vpmullw ymm14,ymm1,ymm3
        vpmullw ymm7,ymm4,ymm13
        vpmullw ymm9,ymm5,ymm13
        vpmullw ymm8,ymm6,ymm14
        vpmullw ymm10,ymm4,ymm14
        vpmulhw ymm7,ymm0,ymm7
        vpmulhw ymm9,ymm0,ymm9
        vpmulhw ymm8,ymm0,ymm8
        vpmulhw ymm10,ymm0,ymm10
        vpmulhw ymm11,ymm4,ymm2
        vpmulhw ymm12,ymm5,ymm2
        vpmulhw ymm13,ymm6,ymm3
        vpmulhw ymm14,ymm4,ymm3
        vpsubw ymm7,ymm11,ymm7
        vpsubw ymm9,ymm12,ymm9
        vpsubw ymm8,ymm8,ymm13
        vpsubw ymm10,ymm14,ymm10
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa ymm8,[64+rdi]
        vmovdqa ymm10,[96+rdi]
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa [64+rdi],ymm7
        vmovdqa [96+rdi],ymm9
        vmovdqa ymm2,[640+rsi]
        vmovdqa ymm3,[672+rsi]
        vmovdqa ymm4,[640+rdx]
        vmovdqa ymm5,[672+rdx]
        vmovdqa ymm6,[320+rcx]
        vpmullw ymm13,ymm1,ymm2
        vpmullw ymm14,ymm1,ymm3
        vpmullw ymm7,ymm4,ymm13
        vpmullw ymm9,ymm5,ymm13
        vpmullw ymm8,ymm6,ymm14
        vpmullw ymm10,ymm4,ymm14
        vpmulhw ymm7,ymm0,ymm7
        vpmulhw ymm9,ymm0,ymm9
        vpmulhw ymm8,ymm0,ymm8
        vpmulhw ymm10,ymm0,ymm10
        vpmulhw ymm11,ymm4,ymm2
        vpmulhw ymm12,ymm5,ymm2
        vpmulhw ymm13,ymm6,ymm3
        vpmulhw ymm14,ymm4,ymm3
        vpsubw ymm7,ymm11,ymm7
        vpsubw ymm9,ymm12,ymm9
        vpsubw ymm8,ymm13,ymm8
        vpsubw ymm10,ymm14,ymm10
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa ymm8,[128+rdi]
        vmovdqa ymm10,[160+rdi]
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa [128+rdi],ymm7
        vmovdqa [160+rdi],ymm9
        vmovdqa ymm2,[704+rsi]
        vmovdqa ymm3,[736+rsi]
        vmovdqa ymm4,[704+rdx]
        vmovdqa ymm5,[736+rdx]
        vmovdqa ymm6,[352+rcx]
        vpmullw ymm13,ymm1,ymm2
        vpmullw ymm14,ymm1,ymm3
        vpmullw ymm7,ymm4,ymm13
        vpmullw ymm9,ymm5,ymm13
        vpmullw ymm8,ymm6,ymm14
        vpmullw ymm10,ymm4,ymm14
        vpmulhw ymm7,ymm0,ymm7
        vpmulhw ymm9,ymm0,ymm9
        vpmulhw ymm8,ymm0,ymm8
        vpmulhw ymm10,ymm0,ymm10
        vpmulhw ymm11,ymm4,ymm2
        vpmulhw ymm12,ymm5,ymm2
        vpmulhw ymm13,ymm6,ymm3
        vpmulhw ymm14,ymm4,ymm3
        vpsubw ymm7,ymm11,ymm7
        vpsubw ymm9,ymm12,ymm9
        vpsubw ymm8,ymm8,ymm13
        vpsubw ymm10,ymm14,ymm10
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa ymm8,[192+rdi]
        vmovdqa ymm10,[224+rdi]
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa [192+rdi],ymm7
        vmovdqa [224+rdi],ymm9
        vmovdqa ymm2,[768+rsi]
        vmovdqa ymm3,[800+rsi]
        vmovdqa ymm4,[768+rdx]
        vmovdqa ymm5,[800+rdx]
        vmovdqa ymm6,[384+rcx]
        vpmullw ymm13,ymm1,ymm2
        vpmullw ymm14,ymm1,ymm3
        vpmullw ymm7,ymm4,ymm13
        vpmullw ymm9,ymm5,ymm13
        vpmullw ymm8,ymm6,ymm14
        vpmullw ymm10,ymm4,ymm14
        vpmulhw ymm7,ymm0,ymm7
        vpmulhw ymm9,ymm0,ymm9
        vpmulhw ymm8,ymm0,ymm8
        vpmulhw ymm10,ymm0,ymm10
        vpmulhw ymm11,ymm4,ymm2
        vpmulhw ymm12,ymm5,ymm2
        vpmulhw ymm13,ymm6,ymm3
        vpmulhw ymm14,ymm4,ymm3
        vpsubw ymm7,ymm11,ymm7
        vpsubw ymm9,ymm12,ymm9
        vpsubw ymm8,ymm13,ymm8
        vpsubw ymm10,ymm14,ymm10
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa ymm8,[256+rdi]
        vmovdqa ymm10,[288+rdi]
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa [256+rdi],ymm7
        vmovdqa [288+rdi],ymm9
        vmovdqa ymm2,[832+rsi]
        vmovdqa ymm3,[864+rsi]
        vmovdqa ymm4,[832+rdx]
        vmovdqa ymm5,[864+rdx]
        vmovdqa ymm6,[416+rcx]
        vpmullw ymm13,ymm1,ymm2
        vpmullw ymm14,ymm1,ymm3
        vpmullw ymm7,ymm4,ymm13
        vpmullw ymm9,ymm5,ymm13
        vpmullw ymm8,ymm6,ymm14
        vpmullw ymm10,ymm4,ymm14
        vpmulhw ymm7,ymm0,ymm7
        vpmulhw ymm9,ymm0,ymm9
        vpmulhw ymm8,ymm0,ymm8
        vpmulhw ymm10,ymm0,ymm10
        vpmulhw ymm11,ymm4,ymm2
        vpmulhw ymm12,ymm5,ymm2
        vpmulhw ymm13,ymm6,ymm3
        vpmulhw ymm14,ymm4,ymm3
        vpsubw ymm7,ymm11,ymm7
        vpsubw ymm9,ymm12,ymm9
        vpsubw ymm8,ymm8,ymm13
        vpsubw ymm10,ymm14,ymm10
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa ymm8,[320+rdi]
        vmovdqa ymm10,[352+rdi]
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa [320+rdi],ymm7
        vmovdqa [352+rdi],ymm9
        vmovdqa ymm2,[896+rsi]
        vmovdqa ymm3,[928+rsi]
        vmovdqa ymm4,[896+rdx]
        vmovdqa ymm5,[928+rdx]
        vmovdqa ymm6,[448+rcx]
        vpmullw ymm13,ymm1,ymm2
        vpmullw ymm14,ymm1,ymm3
        vpmullw ymm7,ymm4,ymm13
        vpmullw ymm9,ymm5,ymm13
        vpmullw ymm8,ymm6,ymm14
        vpmullw ymm10,ymm4,ymm14
        vpmulhw ymm7,ymm0,ymm7
        vpmulhw ymm9,ymm0,ymm9
        vpmulhw ymm8,ymm0,ymm8
        vpmulhw ymm10,ymm0,ymm10
        vpmulhw ymm11,ymm4,ymm2
        vpmulhw ymm12,ymm5,ymm2
        vpmulhw ymm13,ymm6,ymm3
        vpmulhw ymm14,ymm4,ymm3
        vpsubw ymm7,ymm11,ymm7
        vpsubw ymm9,ymm12,ymm9
        vpsubw ymm8,ymm13,ymm8
        vpsubw ymm10,ymm14,ymm10
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa ymm8,[384+rdi]
        vmovdqa ymm10,[416+rdi]
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa [384+rdi],ymm7
        vmovdqa [416+rdi],ymm9
        vmovdqa ymm2,[960+rsi]
        vmovdqa ymm3,[992+rsi]
        vmovdqa ymm4,[960+rdx]
        vmovdqa ymm5,[992+rdx]
        vmovdqa ymm6,[480+rcx]
        vpmullw ymm13,ymm1,ymm2
        vpmullw ymm14,ymm1,ymm3
        vpmullw ymm7,ymm4,ymm13
        vpmullw ymm9,ymm5,ymm13
        vpmullw ymm8,ymm6,ymm14
        vpmullw ymm10,ymm4,ymm14
        vpmulhw ymm7,ymm0,ymm7
        vpmulhw ymm9,ymm0,ymm9
        vpmulhw ymm8,ymm0,ymm8
        vpmulhw ymm10,ymm0,ymm10
        vpmulhw ymm11,ymm4,ymm2
        vpmulhw ymm12,ymm5,ymm2
        vpmulhw ymm13,ymm6,ymm3
        vpmulhw ymm14,ymm4,ymm3
        vpsubw ymm7,ymm11,ymm7
        vpsubw ymm9,ymm12,ymm9
        vpsubw ymm8,ymm8,ymm13
        vpsubw ymm10,ymm14,ymm10
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa ymm8,[448+rdi]
        vmovdqa ymm10,[480+rdi]
        vpaddw ymm7,ymm8,ymm7
        vpaddw ymm9,ymm10,ymm9
        vmovdqa [448+rdi],ymm7
        vmovdqa [480+rdi],ymm9

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
        CFI_STACKLOAD(rdi,144)
        CFI_STACKLOAD(rsi,152)
        CFI_STACKLOAD(rdx,160)
        CFI_STACKLOAD(rcx,168)
        CFI_INC_RSP(176)
#endif

 CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_basemul_k2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
