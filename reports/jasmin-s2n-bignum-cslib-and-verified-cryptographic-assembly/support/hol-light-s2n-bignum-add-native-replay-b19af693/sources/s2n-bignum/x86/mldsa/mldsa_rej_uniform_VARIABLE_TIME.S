// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Uniform rejection sampling for ML-DSA
// Input buf[840] (uint8_t); output r[256] (int32_t); table[2048] (uint64_t)
// Returns: number of valid coefficients in r (at most 256)
//
// This function implements the rejection-sampling loop for ML-DSA, extracting
// 23-bit coefficients from packed 24-bit input bytes and keeping only those
// strictly less than q = 8380417. A main AVX2 loop processes 24 bytes (8
// coefficients) per iteration using VPERMQ+VPSHUFB extraction, VPAND masking,
// VPSUBD+VMOVMSKPS rejection, and VPERMD+table compaction. A scalar tail
// handles any remaining bytes after the main loop exits.
//
// This implementation is derived from the public domain AVX2 Dilithium
// implementation from CRYSTALS-Dilithium optimized AVX2 implementation by
// Bai, Ducas, Kiltz, Lepoint, Lyubashevsky, Schwabe, Seiler, Stehlé
// (https://github.com/pq-crystals/dilithium/tree/master/avx2)
//
// extern uint32_t mldsa_rej_uniform_VARIABLE_TIME_x86
//   (int32_t r[static 256],
//    const uint8_t buf[static 840],
//    const uint64_t table[static 256]);
//
// Standard x86-64 ABI: RDI = r, RSI = buf, RDX = table
// Microsoft x64 ABI:   RCX = r, RDX = buf, R8 = table
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_rej_uniform_VARIABLE_TIME_x86)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mldsa_rej_uniform_VARIABLE_TIME_x86)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_rej_uniform_VARIABLE_TIME_x86)
        .text
        .balign 32

S2N_BN_SYMBOL(mldsa_rej_uniform_VARIABLE_TIME_x86):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        // The body only uses the volatile registers xmm0-xmm4 (ymm0-ymm4) and
        // writes results directly to the output buffer, so none of the
        // nonvolatile xmm6-xmm15 need saving. We only preserve rdi/rsi, which
        // hold the mapped SysV argument pointers.
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

        // Shuffle mask: expand 24 bytes (8 x 3-byte coefficients) into
        // 8 x 4-byte lanes (with a zero high byte in each).
        mov     r10, 0xff050403ff020100
        vmovq   xmm0, r10
        mov     r10, 0xff0b0a09ff080706
        vpinsrq xmm0, xmm0, r10, 0x1
        mov     r10, 0xff090807ff060504
        vmovq   xmm3, r10
        mov     r10, 0xff0f0e0dff0c0b0a
        vpinsrq xmm3, xmm3, r10, 0x1
        vinserti128 ymm0, ymm0, xmm3, 0x1

        // Mask 0x7fffff in all 8 lanes (keep low 23 bits)
        mov     r8d, 0x7fffff
        vmovd   xmm1, r8d
        vpbroadcastd ymm1, xmm1

        // Threshold q = 0x7fe001 in all 8 lanes
        mov     r8d, 0x7fe001
        vmovd   xmm2, r8d
        vpbroadcastd ymm2, xmm2

        // rax = accepted count, rcx = byte offset into buf
        xor     eax, eax
        xor     ecx, ecx

Lmldsa_rej_uniform_VARIABLE_TIME_x86_loop:
        // Exit to scalar tail if we have 248 or more accepted (next 8 might
        // overflow) or if byte offset is past 808 (would read past buf+840-24).
        cmp     eax, 0xf8
        ja      Lmldsa_rej_uniform_VARIABLE_TIME_x86_scalar
        cmp     ecx, 0x328
        ja      Lmldsa_rej_uniform_VARIABLE_TIME_x86_scalar

        vmovdqu ymm3, YMMWORD PTR [rsi+rcx]
        add     ecx, 0x18
        vpermq  ymm3, ymm3, 0x94
        vpshufb ymm3, ymm3, ymm0
        vpand   ymm3, ymm3, ymm1
        vpsubd  ymm4, ymm3, ymm2
        vmovmskps r8d, ymm4
        popcnt  r9d, r8d
        vmovq   xmm4, QWORD PTR [rdx+8*r8]
        vpmovzxbd ymm4, xmm4
        vpermd  ymm3, ymm4, ymm3
        vmovdqu YMMWORD PTR [rdi+4*rax], ymm3
        add     eax, r9d
        jmp     Lmldsa_rej_uniform_VARIABLE_TIME_x86_loop

Lmldsa_rej_uniform_VARIABLE_TIME_x86_scalar:
        cmp     eax, 0x100
        jae     Lmldsa_rej_uniform_VARIABLE_TIME_x86_done
        cmp     ecx, 0x345
        ja      Lmldsa_rej_uniform_VARIABLE_TIME_x86_done
        movzx   r8d, WORD PTR [rsi+rcx]
        movzx   r9d, BYTE PTR [rsi+rcx+2]
        shl     r9d, 0x10
        or      r8d, r9d
        and     r8d, 0x7fffff
        add     ecx, 0x3
        cmp     r8d, 0x7fe001
        jae     Lmldsa_rej_uniform_VARIABLE_TIME_x86_scalar
        mov     DWORD PTR [rdi+4*rax], r8d
        add     eax, 0x1
        jmp     Lmldsa_rej_uniform_VARIABLE_TIME_x86_scalar

Lmldsa_rej_uniform_VARIABLE_TIME_x86_done:
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mldsa_rej_uniform_VARIABLE_TIME_x86)

#if defined(__linux__) && defined(__ELF__)
        .section .note.GNU-stack,"",%progbits
#endif
