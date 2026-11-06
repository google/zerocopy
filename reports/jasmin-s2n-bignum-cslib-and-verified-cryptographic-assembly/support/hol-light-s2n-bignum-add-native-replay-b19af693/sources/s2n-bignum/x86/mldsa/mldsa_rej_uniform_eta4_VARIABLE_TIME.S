// Copyright (c) The mldsa-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Rejection sampling of eta=4 secret coefficients for ML-DSA (x86_64 AVX2)
//
// Extracts 4-bit nibbles from the input byte buffer, accepts those < 9, and
// maps an accepted nibble n to the coefficient 4 - n, producing values in
// [-4, 4]. Fills the output array r[256] with the accepted coefficients in
// order of appearance, returning the total number written (max 256).
//
// extern uint64_t mldsa_rej_uniform_eta4_VARIABLE_TIME_x86
//                     (int32_t r[static 256],
//                      const uint8_t buf[static 272],
//                      const uint8_t table[static 2048]);
//
// The input buffer buf is a fixed MLD_AVX2_REJ_UNIFORM_ETA4_BUFLEN = 272
// bytes; the table argument is a specific precomputed 256x8 = 2048-byte table
// (mldsa_rej_uniform_table), defined in the proof / test code.
//
// Like mlkem_rej_uniform, this is *not* a constant-time function: the time
// taken depends on how many buffer elements pass the < 9 filter.
//
// Standard x86-64 ABI: RDI = r, RSI = buf, RDX = table
// Microsoft x64 ABI:   RCX = r, RDX = buf, R8 = table
// ----------------------------------------------------------------------------

// This implementation is derived from the public domain AVX2 Dilithium
// implementation (pq-crystals/dilithium) via the mldsa-native project.

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_rej_uniform_eta4_VARIABLE_TIME_x86)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mldsa_rej_uniform_eta4_VARIABLE_TIME_x86)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_rej_uniform_eta4_VARIABLE_TIME_x86)
        .text
        .balign 4

S2N_BN_SYMBOL(mldsa_rej_uniform_eta4_VARIABLE_TIME_x86):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        // Windows ABI: preserve xmm6 (nonvolatile, used below) and the
        // nonvolatile GPRs rdi/rsi that hold the mapped SysV arguments.
        CFI_DEC_RSP(40)
        CFI_STACKSAVEU(xmm6,0)
        CFI_STACKSAVE(rdi,16)
        CFI_STACKSAVE(rsi,24)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

        mov     r8d, 0xf0f0f0f
        vmovd   xmm2, r8d
        vpbroadcastd ymm2, xmm2
        mov     r8d, 0x4040404
        vmovd   xmm3, r8d
        vpbroadcastd ymm3, xmm3
        mov     r8d, 0x9090909
        vmovd   xmm4, r8d
        vpbroadcastd ymm4, xmm4
        xor     eax, eax
        xor     ecx, ecx

Lmldsa_rej_uniform_eta4_x86_loop:
        cmp     eax, 0xf8
        ja      Lmldsa_rej_uniform_eta4_x86_scalar
        cmp     ecx, 0x100
        ja      Lmldsa_rej_uniform_eta4_x86_scalar
        vpmovzxbw ymm0, [rsi+rcx]
        vpsllw  ymm1, ymm0, 0x4
        vpor    ymm0, ymm0, ymm1
        vpand   ymm0, ymm0, ymm2
        vpsubb  ymm1, ymm0, ymm4
        vpsubb  ymm0, ymm3, ymm0
        vpmovmskb r8d, ymm1
        vextracti128 xmm5, ymm0, 0x0
        movzx   r10d, r8b
        vmovq   xmm6, [rdx+8*r10]
        vpshufb xmm6, xmm5, xmm6
        vpmovsxbd ymm1, xmm6
        vmovdqu [rdi+4*rax], ymm1
        popcnt  r9d, r10d
        add     eax, r9d
        shr     r8d, 0x8
        add     ecx, 0x4
        cmp     eax, 0xf8
        ja      Lmldsa_rej_uniform_eta4_x86_scalar
        vpsrldq xmm5, xmm5, 0x8
        movzx   r10d, r8b
        vmovq   xmm6, [rdx+8*r10]
        vpshufb xmm6, xmm5, xmm6
        vpmovsxbd ymm1, xmm6
        vmovdqu [rdi+4*rax], ymm1
        popcnt  r9d, r10d
        add     eax, r9d
        shr     r8d, 0x8
        add     ecx, 0x4
        cmp     eax, 0xf8
        ja      Lmldsa_rej_uniform_eta4_x86_scalar
        vextracti128 xmm5, ymm0, 0x1
        movzx   r10d, r8b
        vmovq   xmm6, [rdx+8*r10]
        vpshufb xmm6, xmm5, xmm6
        vpmovsxbd ymm1, xmm6
        vmovdqu [rdi+4*rax], ymm1
        popcnt  r9d, r10d
        add     eax, r9d
        shr     r8d, 0x8
        add     ecx, 0x4
        cmp     eax, 0xf8
        ja      Lmldsa_rej_uniform_eta4_x86_scalar
        vpsrldq xmm5, xmm5, 0x8
        movzx   r10d, r8b
        vmovq   xmm6, [rdx+8*r10]
        vpshufb xmm6, xmm5, xmm6
        vpmovsxbd ymm1, xmm6
        vmovdqu [rdi+4*rax], ymm1
        popcnt  r9d, r10d
        add     eax, r9d
        add     ecx, 0x4
        jmp     Lmldsa_rej_uniform_eta4_x86_loop

Lmldsa_rej_uniform_eta4_x86_scalar:
        cmp     eax, 0x100
        jae     Lmldsa_rej_uniform_eta4_x86_done
        cmp     ecx, 0x110
        jae     Lmldsa_rej_uniform_eta4_x86_done
        movzx   r11d, BYTE PTR [rsi+rcx]
        inc     ecx
        mov     r10d, r11d
        and     r10d, 0xf
        cmp     r10d, 0x9
        jae     Lmldsa_rej_uniform_eta4_x86_high_nibble
        mov     r9d, 0x4
        sub     r9d, r10d
        mov     [rdi+4*rax], r9d
        inc     eax
        cmp     eax, 0x100
        jae     Lmldsa_rej_uniform_eta4_x86_done

Lmldsa_rej_uniform_eta4_x86_high_nibble:
        shr     r11d, 0x4
        and     r11d, 0xf
        cmp     r11d, 0x9
        jae     Lmldsa_rej_uniform_eta4_x86_scalar
        mov     r10d, 0x4
        sub     r10d, r11d
        mov     [rdi+4*rax], r10d
        inc     eax
        jmp     Lmldsa_rej_uniform_eta4_x86_scalar

Lmldsa_rej_uniform_eta4_x86_done:

#if WINDOWS_ABI
        CFI_STACKLOADU(xmm6,0)
        CFI_STACKLOAD(rdi,16)
        CFI_STACKLOAD(rsi,24)
        CFI_INC_RSP(40)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mldsa_rej_uniform_eta4_VARIABLE_TIME_x86)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
