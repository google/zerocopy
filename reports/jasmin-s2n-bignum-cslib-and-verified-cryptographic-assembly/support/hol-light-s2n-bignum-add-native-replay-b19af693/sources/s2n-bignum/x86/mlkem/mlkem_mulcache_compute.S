// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Precompute the mulcache data for a polynomial in the NTT domain
// Inputs a[256], qdata[624] (all signed 16-bit words); output x[128] (signed 16-bit words)
//
// The input array a is assumed to represent 128 linear polynomials
// in the NTT domain, p_i = a[f(i)] + a[g(i)] * X where each p_i is in
// Fq[X]/(X^2-zeta^i'), with zeta^i' being a power of zeta = 17, with i
// bit-reversed as used for NTTs, and f(i) and g(i) are ordering functions
// that map the coefficients per the specific order used in the AVX2
// implementation. For each such polynomial, the mulcache value is
// a[g(i)] * zeta^i' (modulo 3329 as usual), a value useful to
// perform base multiplication of polynomials efficiently. The The second
// parameter is expected to point to a table of constants whose definitions
// can be found in the mlkem-native repo or our "tests/test.c".
//
// extern void mlkem_mulcache_compute_x86
//      (int16_t x[static 128],const int16_t a[static 256],
//       const int16_t qdata[static 624]);
//
// Standard x86-64 ABI: RDI = x, RSI = a, RDX = qdata
// Microsoft x64 ABI:   RCX = x, RDX = a, R8 = qdata
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

.intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_mulcache_compute_x86)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_mulcache_compute_x86)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_mulcache_compute_x86)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_mulcache_compute_x86):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
  CFI_DEC_RSP(104)
  CFI_STACKSAVEU(xmm6,0)
  CFI_STACKSAVEU(xmm7,16)
  CFI_STACKSAVEU(xmm8,32)
  CFI_STACKSAVEU(xmm9,48)
  CFI_STACKSAVEU(xmm10,64)
  CFI_STACKSAVE(rdi,80)
  CFI_STACKSAVE(rsi,88)
  CFI_STACKSAVE(rdx,96)
  mov rdi, rcx
  mov rsi, rdx
  mov rdx, r8
#endif

 mov eax,0xd010d01
 vmovd xmm0,eax
 vpbroadcastd ymm0,xmm0
 vmovdqa ymm2,[32+rsi]
 vmovdqa ymm3,[96+rsi]
 vmovdqa ymm4,[992+rdx]
 vmovdqa ymm1,[1120+rdx]
 vpmullw ymm5,ymm1,ymm2
 vpmullw ymm6,ymm1,ymm3
 vpmulhw ymm7,ymm4,ymm2
 vpmulhw ymm8,ymm4,ymm3
 vpmulhw ymm9,ymm0,ymm5
 vpmulhw ymm10,ymm0,ymm6
 vpsubw ymm7,ymm7,ymm9
 vpsubw ymm8,ymm8,ymm10
 vmovdqa [rdi],ymm7
 vmovdqa [32+rdi],ymm8
 vmovdqa ymm2,[160+rsi]
 vmovdqa ymm3,[224+rsi]
 vmovdqa ymm4,[1024+rdx]
 vmovdqa ymm1,[1152+rdx]
 vpmullw ymm5,ymm1,ymm2
 vpmullw ymm6,ymm1,ymm3
 vpmulhw ymm7,ymm4,ymm2
 vpmulhw ymm8,ymm4,ymm3
 vpmulhw ymm9,ymm0,ymm5
 vpmulhw ymm10,ymm0,ymm6
 vpsubw ymm7,ymm7,ymm9
 vpsubw ymm8,ymm8,ymm10
 vmovdqa [64+rdi],ymm7
 vmovdqa [96+rdi],ymm8
 vmovdqa ymm2,[288+rsi]
 vmovdqa ymm3,[352+rsi]
 vmovdqa ymm4,[1056+rdx]
 vmovdqa ymm1,[1184+rdx]
 vpmullw ymm5,ymm1,ymm2
 vpmullw ymm6,ymm1,ymm3
 vpmulhw ymm7,ymm4,ymm2
 vpmulhw ymm8,ymm4,ymm3
 vpmulhw ymm9,ymm0,ymm5
 vpmulhw ymm10,ymm0,ymm6
 vpsubw ymm7,ymm7,ymm9
 vpsubw ymm8,ymm8,ymm10
 vmovdqa [128+rdi],ymm7
 vmovdqa [160+rdi],ymm8
 vmovdqa ymm2,[416+rsi]
 vmovdqa ymm3,[480+rsi]
 vmovdqa ymm4,[1088+rdx]
 vmovdqa ymm1,[1216+rdx]
 vpmullw ymm5,ymm1,ymm2
 vpmullw ymm6,ymm1,ymm3
 vpmulhw ymm7,ymm4,ymm2
 vpmulhw ymm8,ymm4,ymm3
 vpmulhw ymm9,ymm0,ymm5
 vpmulhw ymm10,ymm0,ymm6
 vpsubw ymm7,ymm7,ymm9
 vpsubw ymm8,ymm8,ymm10
 vmovdqa [192+rdi],ymm7
 vmovdqa [224+rdi],ymm8

#if WINDOWS_ABI
  CFI_STACKLOADU(xmm6,0)
  CFI_STACKLOADU(xmm7,16)
  CFI_STACKLOADU(xmm8,32)
  CFI_STACKLOADU(xmm9,48)
  CFI_STACKLOADU(xmm10,64)
  CFI_STACKLOAD(rdi,80)
  CFI_STACKLOAD(rsi,88)
  CFI_STACKLOAD(rdx,96)
  CFI_INC_RSP(104)
#endif

        CFI_RET


S2N_BN_SIZE_DIRECTIVE(mlkem_mulcache_compute_x86)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
