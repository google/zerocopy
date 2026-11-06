// Copyright (c) The mldsa-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Rejection sampling of eta=2 secret coefficients for ML-DSA (x86_64 AVX2)
//
// Extracts 4-bit nibbles from the input byte buffer, accepts those < 15, and
// maps an accepted nibble n to the coefficient 2 - (n mod 5) via a centered
// modulo-5 reduction, producing values in [-2, 2]. Fills the output array
// r[256] with the accepted coefficients in order of appearance, returning the
// total number written (max 256).
//
// extern uint64_t mldsa_rej_uniform_eta2_VARIABLE_TIME_x86
//                     (int32_t r[static 256],
//                      const uint8_t buf[static 136],
//                      const uint8_t table[static 2048]);
//
// The input buffer buf is a fixed MLD_AVX2_REJ_UNIFORM_ETA2_BUFLEN = 136
// bytes; the table argument is a specific precomputed 256x8 = 2048-byte table
// (mldsa_rej_uniform_table), defined in the proof / test code.
//
// Like mlkem_rej_uniform, this is *not* a constant-time function: the time
// taken depends on how many buffer elements pass the < 15 filter.
//
// Standard x86-64 ABI: RDI = r, RSI = buf, RDX = table
// Microsoft x64 ABI:   RCX = r, RDX = buf, R8 = table
// ----------------------------------------------------------------------------

// This implementation is derived from the public domain AVX2 Dilithium
// implementation (pq-crystals/dilithium) via the mldsa-native project.

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_rej_uniform_eta2_VARIABLE_TIME_x86)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mldsa_rej_uniform_eta2_VARIABLE_TIME_x86)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_rej_uniform_eta2_VARIABLE_TIME_x86)
        .text
        .balign 4

S2N_BN_SYMBOL(mldsa_rej_uniform_eta2_VARIABLE_TIME_x86):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        // Windows ABI: preserve the nonvolatile xmm6-xmm9 (used below) and the
        // nonvolatile GPRs rdi/rsi that hold the mapped SysV arguments.
        CFI_DEC_RSP(80)
        CFI_STACKSAVEU(xmm6,0)
        CFI_STACKSAVEU(xmm7,16)
        CFI_STACKSAVEU(xmm8,32)
        CFI_STACKSAVEU(xmm9,48)
        CFI_STACKSAVE(rdi,64)
        CFI_STACKSAVE(rsi,72)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

        mov     r8d, 0xf0f0f0f
        vmovd   xmm3, r8d
        vpbroadcastd ymm3, xmm3
        mov     r8d, 0x2020202
        vmovd   xmm4, r8d
        vpbroadcastd ymm4, xmm4
        mov     r8d, 0xf0f0f0f
        vmovd   xmm5, r8d
        vpbroadcastd ymm5, xmm5
        mov     r8d, 0xffffe660
        vpinsrw xmm6, xmm6, r8d, 0x0
        vpbroadcastw ymm6, xmm6
        mov     r8d, 0x5
        vpinsrw xmm7, xmm7, r8d, 0x0
        vpbroadcastw ymm7, xmm7
        xor     eax, eax
        xor     ecx, ecx

Lmldsa_rej_uniform_eta2_x86_loop:
        cmp     eax, 0xf8
        ja      Lmldsa_rej_uniform_eta2_x86_scalar
        cmp     ecx, 0x78
        ja      Lmldsa_rej_uniform_eta2_x86_scalar
        vpmovzxbw ymm0, [rsi+rcx]
        vpsllw  ymm1, ymm0, 0x4
        vpor    ymm0, ymm0, ymm1
        vpand   ymm0, ymm0, ymm3
        vpsubb  ymm1, ymm0, ymm5
        vpsubb  ymm0, ymm4, ymm0
        vpmovmskb r8d, ymm1
        vextracti128 xmm8, ymm0, 0x0
        movzx   r10d, r8b
        vmovq   xmm9, [rdx+8*r10]
        vpshufb xmm9, xmm8, xmm9
        vpmovsxbd ymm1, xmm9
        vpmulhrsw ymm2, ymm1, ymm6
        vpmullw ymm2, ymm2, ymm7
        vpaddd  ymm1, ymm1, ymm2
        vmovdqu [rdi+4*rax], ymm1
        popcnt  r9d, r10d
        add     eax, r9d
        shr     r8d, 0x8
        add     ecx, 0x4
        cmp     eax, 0xf8
        ja      Lmldsa_rej_uniform_eta2_x86_scalar
        vpsrldq xmm8, xmm8, 0x8
        movzx   r10d, r8b
        vmovq   xmm9, [rdx+8*r10]
        vpshufb xmm9, xmm8, xmm9
        vpmovsxbd ymm1, xmm9
        vpmulhrsw ymm2, ymm1, ymm6
        vpmullw ymm2, ymm2, ymm7
        vpaddd  ymm1, ymm1, ymm2
        vmovdqu [rdi+4*rax], ymm1
        popcnt  r9d, r10d
        add     eax, r9d
        shr     r8d, 0x8
        add     ecx, 0x4
        cmp     eax, 0xf8
        ja      Lmldsa_rej_uniform_eta2_x86_scalar
        vextracti128 xmm8, ymm0, 0x1
        movzx   r10d, r8b
        vmovq   xmm9, [rdx+8*r10]
        vpshufb xmm9, xmm8, xmm9
        vpmovsxbd ymm1, xmm9
        vpmulhrsw ymm2, ymm1, ymm6
        vpmullw ymm2, ymm2, ymm7
        vpaddd  ymm1, ymm1, ymm2
        vmovdqu [rdi+4*rax], ymm1
        popcnt  r9d, r10d
        add     eax, r9d
        shr     r8d, 0x8
        add     ecx, 0x4
        cmp     eax, 0xf8
        ja      Lmldsa_rej_uniform_eta2_x86_scalar
        vpsrldq xmm8, xmm8, 0x8
        movzx   r10d, r8b
        vmovq   xmm9, [rdx+8*r10]
        vpshufb xmm9, xmm8, xmm9
        vpmovsxbd ymm1, xmm9
        vpmulhrsw ymm2, ymm1, ymm6
        vpmullw ymm2, ymm2, ymm7
        vpaddd  ymm1, ymm1, ymm2
        vmovdqu [rdi+4*rax], ymm1
        popcnt  r9d, r10d
        add     eax, r9d
        add     ecx, 0x4
        jmp     Lmldsa_rej_uniform_eta2_x86_loop

Lmldsa_rej_uniform_eta2_x86_scalar:
        cmp     eax, 0x100
        jae     Lmldsa_rej_uniform_eta2_x86_done
        cmp     ecx, 0x88
        jae     Lmldsa_rej_uniform_eta2_x86_done
        movzx   r11d, BYTE PTR [rsi+rcx]
        inc     ecx
        mov     r10d, r11d
        and     r10d, 0xf
        cmp     r10d, 0xf
        jae     Lmldsa_rej_uniform_eta2_x86_high_nibble
        mov     r11d, r10d
        imul    r11d, r11d, 0xcd
        shr     r11d, 0xa
        imul    r11d, r11d, 0x5
        sub     r10d, r11d
        mov     r11d, 0x2
        sub     r11d, r10d
        mov     [rdi+4*rax], r11d
        inc     eax
        cmp     eax, 0x100
        jae     Lmldsa_rej_uniform_eta2_x86_done

Lmldsa_rej_uniform_eta2_x86_high_nibble:
        movzx   r11d, BYTE PTR [rsi+rcx-0x1]
        shr     r11d, 0x4
        and     r11d, 0xf
        cmp     r11d, 0xf
        jae     Lmldsa_rej_uniform_eta2_x86_scalar
        mov     r10d, r11d
        imul    r10d, r10d, 0xcd
        shr     r10d, 0xa
        imul    r10d, r10d, 0x5
        sub     r11d, r10d
        mov     r10d, 0x2
        sub     r10d, r11d
        mov     [rdi+4*rax], r10d
        inc     eax
        jmp     Lmldsa_rej_uniform_eta2_x86_scalar

Lmldsa_rej_uniform_eta2_x86_done:

#if WINDOWS_ABI
        CFI_STACKLOADU(xmm6,0)
        CFI_STACKLOADU(xmm7,16)
        CFI_STACKLOADU(xmm8,32)
        CFI_STACKLOADU(xmm9,48)
        CFI_STACKLOAD(rdi,64)
        CFI_STACKLOAD(rsi,72)
        CFI_INC_RSP(80)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mldsa_rej_uniform_eta2_VARIABLE_TIME_x86)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
