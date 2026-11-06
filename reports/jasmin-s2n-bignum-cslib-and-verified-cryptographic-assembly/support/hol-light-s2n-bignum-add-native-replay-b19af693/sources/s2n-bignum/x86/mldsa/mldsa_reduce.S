// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Canonical reduction of polynomial coefficients for ML-DSA
// Input a[256] (signed 32-bit words); output a[256] (signed 32-bit words)
//
// This reduces each element of the 256-element array of 32-bit signed
// integers modulo 8380417 with the result being centered around zero,
// specifically -6283009 <= r <= 6283008, in-place.
//
// Each input coefficient must satisfy a <= 0x7fbfffff (2143289343); this
// rules out the top 0x400000 positive values, for which the internal
// "+ 4194304" rounding step would overflow a signed 32-bit word and give
// an incorrect (non-congruent) result. Every input in the standard ML-DSA
// coefficient range comfortably satisfies this.
//
// extern void mldsa_reduce(int32_t a[static 256]);
//
// Standard x86-64 ABI: RDI = a
// Microsoft x64 ABI:   RCX = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_reduce)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mldsa_reduce)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_reduce)
        .text

#define a rdi

S2N_BN_SYMBOL(mldsa_reduce):
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
        mov     rdi, rcx
#endif

// Load constants - poly_reduce only takes one parameter (the polynomial)
        mov     eax, 8380417                      // MLDSA_Q
        movd    xmm0, eax
        vpbroadcastd ymm0, xmm0                   // q in all lanes

        // Load offset constant inline to avoid PIE issues
        mov     eax, 4194304                      // 1 << 22
        movd    xmm1, eax
        vpbroadcastd ymm1, xmm1                   // off = _mm256_set1_epi32(1<<22)

// Process all 32 vectors (256 coefficients) using NTT-style block processing
// First batch: vectors 0-7
        vmovdqa ymm4,   [rdi+0]                   // Load f0
        vmovdqa ymm5,  [rdi+32]                   // Load f1
        vmovdqa ymm6,  [rdi+64]                   // Load f2
        vmovdqa ymm7,  [rdi+96]                   // Load f3
        vmovdqa ymm8, [rdi+128]                   // Load f4
        vmovdqa ymm9, [rdi+160]                   // Load f5
        vmovdqa ymm10,[rdi+192]                   // Load f6
        vmovdqa ymm11,[rdi+224]                   // Load f7

// Process all 8 vectors in parallel - first half of pipeline
        vpaddd  ymm12, ymm4, ymm1                 // g0 = f0 + off
        vpaddd  ymm13, ymm5, ymm1                 // g1 = f1 + off
        vpaddd  ymm14, ymm6, ymm1                 // g2 = f2 + off
        vpaddd  ymm15, ymm7, ymm1                 // g3 = f3 + off
        vpsrad  ymm12, ymm12, 23                  // g0 >>= 23
        vpsrad  ymm13, ymm13, 23                  // g1 >>= 23
        vpsrad  ymm14, ymm14, 23                  // g2 >>= 23
        vpsrad  ymm15, ymm15, 23                  // g3 >>= 23
        vpmulld ymm12, ymm12, ymm0                // g0 *= q
        vpmulld ymm13, ymm13, ymm0                // g1 *= q
        vpmulld ymm14, ymm14, ymm0                // g2 *= q
        vpmulld ymm15, ymm15, ymm0                // g3 *= q
        vpsubd  ymm4, ymm4, ymm12                 // f0 -= g0
        vpsubd  ymm5, ymm5, ymm13                 // f1 -= g1
        vpsubd  ymm6, ymm6, ymm14                 // f2 -= g2
        vpsubd  ymm7, ymm7, ymm15                 // f3 -= g3

// Process second half of vectors
        vpaddd  ymm12, ymm8, ymm1                 // g4 = f4 + off
        vpaddd  ymm13, ymm9, ymm1                 // g5 = f5 + off
        vpaddd  ymm14, ymm10, ymm1                // g6 = f6 + off
        vpaddd  ymm15, ymm11, ymm1                // g7 = f7 + off
        vpsrad  ymm12, ymm12, 23                  // g4 >>= 23
        vpsrad  ymm13, ymm13, 23                  // g5 >>= 23
        vpsrad  ymm14, ymm14, 23                  // g6 >>= 23
        vpsrad  ymm15, ymm15, 23                  // g7 >>= 23
        vpmulld ymm12, ymm12, ymm0                // g4 *= q
        vpmulld ymm13, ymm13, ymm0                // g5 *= q
        vpmulld ymm14, ymm14, ymm0                // g6 *= q
        vpmulld ymm15, ymm15, ymm0                // g7 *= q
        vpsubd  ymm8, ymm8, ymm12                 // f4 -= g4
        vpsubd  ymm9, ymm9, ymm13                 // f5 -= g5
        vpsubd  ymm10, ymm10, ymm14               // f6 -= g6
        vpsubd  ymm11, ymm11, ymm15               // f7 -= g7

// Store first batch results
        vmovdqa   [rdi+0], ymm4                   // Store f0
        vmovdqa  [rdi+32], ymm5                   // Store f1
        vmovdqa  [rdi+64], ymm6                   // Store f2
        vmovdqa  [rdi+96], ymm7                   // Store f3
        vmovdqa [rdi+128], ymm8                   // Store f4
        vmovdqa [rdi+160], ymm9                   // Store f5
        vmovdqa [rdi+192], ymm10                  // Store f6
        vmovdqa [rdi+224], ymm11                  // Store f7

// Second batch: vectors 8-15
        vmovdqa ymm4, [rdi+256]                   // Load f8
        vmovdqa ymm5, [rdi+288]                   // Load f9
        vmovdqa ymm6, [rdi+320]                   // Load f10
        vmovdqa ymm7, [rdi+352]                   // Load f11
        vmovdqa ymm8, [rdi+384]                   // Load f12
        vmovdqa ymm9, [rdi+416]                   // Load f13
        vmovdqa ymm10,[rdi+448]                   // Load f14
        vmovdqa ymm11,[rdi+480]                   // Load f15

// Process second batch in parallel
        vpaddd  ymm12, ymm4, ymm1                 // g8 = f8 + off
        vpaddd  ymm13, ymm5, ymm1                 // g9 = f9 + off
        vpaddd  ymm14, ymm6, ymm1                 // g10 = f10 + off
        vpaddd  ymm15, ymm7, ymm1                 // g11 = f11 + off
        vpsrad  ymm12, ymm12, 23                  // g8 >>= 23
        vpsrad  ymm13, ymm13, 23                  // g9 >>= 23
        vpsrad  ymm14, ymm14, 23                  // g10 >>= 23
        vpsrad  ymm15, ymm15, 23                  // g11 >>= 23
        vpmulld ymm12, ymm12, ymm0                // g8 *= q
        vpmulld ymm13, ymm13, ymm0                // g9 *= q
        vpmulld ymm14, ymm14, ymm0                // g10 *= q
        vpmulld ymm15, ymm15, ymm0                // g11 *= q
        vpsubd  ymm4, ymm4, ymm12                 // f8 -= g8
        vpsubd  ymm5, ymm5, ymm13                 // f9 -= g9
        vpsubd  ymm6, ymm6, ymm14                 // f10 -= g10
        vpsubd  ymm7, ymm7, ymm15                 // f11 -= g11

        vpaddd  ymm12, ymm8, ymm1                 // g12 = f12 + off
        vpaddd  ymm13, ymm9, ymm1                 // g13 = f13 + off
        vpaddd  ymm14, ymm10, ymm1                // g14 = f14 + off
        vpaddd  ymm15, ymm11, ymm1                // g15 = f15 + off
        vpsrad  ymm12, ymm12, 23                  // g12 >>= 23
        vpsrad  ymm13, ymm13, 23                  // g13 >>= 23
        vpsrad  ymm14, ymm14, 23                  // g14 >>= 23
        vpsrad  ymm15, ymm15, 23                  // g15 >>= 23
        vpmulld ymm12, ymm12, ymm0                // g12 *= q
        vpmulld ymm13, ymm13, ymm0                // g13 *= q
        vpmulld ymm14, ymm14, ymm0                // g14 *= q
        vpmulld ymm15, ymm15, ymm0                // g15 *= q
        vpsubd  ymm8, ymm8, ymm12                 // f12 -= g12
        vpsubd  ymm9, ymm9, ymm13                 // f13 -= g13
        vpsubd  ymm10, ymm10, ymm14               // f14 -= g14
        vpsubd  ymm11, ymm11, ymm15               // f15 -= g15

// Store second batch
        vmovdqa [rdi+256], ymm4                   // Store f8
        vmovdqa [rdi+288], ymm5                   // Store f9
        vmovdqa [rdi+320], ymm6                   // Store f10
        vmovdqa [rdi+352], ymm7                   // Store f11
        vmovdqa [rdi+384], ymm8                   // Store f12
        vmovdqa [rdi+416], ymm9                   // Store f13
        vmovdqa [rdi+448], ymm10                  // Store f14
        vmovdqa [rdi+480], ymm11                  // Store f15

// Third batch: vectors 16-23
        vmovdqa ymm4, [rdi+512]                   // Load f16
        vmovdqa ymm5, [rdi+544]                   // Load f17
        vmovdqa ymm6, [rdi+576]                   // Load f18
        vmovdqa ymm7, [rdi+608]                   // Load f19
        vmovdqa ymm8, [rdi+640]                   // Load f20
        vmovdqa ymm9, [rdi+672]                   // Load f21
        vmovdqa ymm10,[rdi+704]                   // Load f22
        vmovdqa ymm11,[rdi+736]                   // Load f23

// Process third batch
        vpaddd  ymm12, ymm4, ymm1                 // g16 = f16 + off
        vpaddd  ymm13, ymm5, ymm1                 // g17 = f17 + off
        vpaddd  ymm14, ymm6, ymm1                 // g18 = f18 + off
        vpaddd  ymm15, ymm7, ymm1                 // g19 = f19 + off
        vpsrad  ymm12, ymm12, 23                  // g16 >>= 23
        vpsrad  ymm13, ymm13, 23                  // g17 >>= 23
        vpsrad  ymm14, ymm14, 23                  // g18 >>= 23
        vpsrad  ymm15, ymm15, 23                  // g19 >>= 23
        vpmulld ymm12, ymm12, ymm0                // g16 *= q
        vpmulld ymm13, ymm13, ymm0                // g17 *= q
        vpmulld ymm14, ymm14, ymm0                // g18 *= q
        vpmulld ymm15, ymm15, ymm0                // g19 *= q
        vpsubd  ymm4, ymm4, ymm12                 // f16 -= g16
        vpsubd  ymm5, ymm5, ymm13                 // f17 -= g17
        vpsubd  ymm6, ymm6, ymm14                 // f18 -= g18
        vpsubd  ymm7, ymm7, ymm15                 // f19 -= g19

        vpaddd  ymm12, ymm8, ymm1                 // g20 = f20 + off
        vpaddd  ymm13, ymm9, ymm1                 // g21 = f21 + off
        vpaddd  ymm14, ymm10, ymm1                // g22 = f22 + off
        vpaddd  ymm15, ymm11, ymm1                // g23 = f23 + off
        vpsrad  ymm12, ymm12, 23                  // g20 >>= 23
        vpsrad  ymm13, ymm13, 23                  // g21 >>= 23
        vpsrad  ymm14, ymm14, 23                  // g22 >>= 23
        vpsrad  ymm15, ymm15, 23                  // g23 >>= 23
        vpmulld ymm12, ymm12, ymm0                // g20 *= q
        vpmulld ymm13, ymm13, ymm0                // g21 *= q
        vpmulld ymm14, ymm14, ymm0                // g22 *= q
        vpmulld ymm15, ymm15, ymm0                // g23 *= q
        vpsubd  ymm8, ymm8, ymm12                 // f20 -= g20
        vpsubd  ymm9, ymm9, ymm13                 // f21 -= g21
        vpsubd  ymm10, ymm10, ymm14               // f22 -= g22
        vpsubd  ymm11, ymm11, ymm15               // f23 -= g23

// Store third batch
        vmovdqa [rdi+512], ymm4                   // Store f16
        vmovdqa [rdi+544], ymm5                   // Store f17
        vmovdqa [rdi+576], ymm6                   // Store f18
        vmovdqa [rdi+608], ymm7                   // Store f19
        vmovdqa [rdi+640], ymm8                   // Store f20
        vmovdqa [rdi+672], ymm9                   // Store f21
        vmovdqa [rdi+704], ymm10                  // Store f22
        vmovdqa [rdi+736], ymm11                  // Store f23

// Fourth batch: vectors 24-31
        vmovdqa ymm4, [rdi+768]                   // Load f24
        vmovdqa ymm5, [rdi+800]                   // Load f25
        vmovdqa ymm6, [rdi+832]                   // Load f26
        vmovdqa ymm7, [rdi+864]                   // Load f27
        vmovdqa ymm8, [rdi+896]                   // Load f28
        vmovdqa ymm9, [rdi+928]                   // Load f29
        vmovdqa ymm10,[rdi+960]                   // Load f30
        vmovdqa ymm11,[rdi+992]                   // Load f31

// Process final batch
        vpaddd  ymm12, ymm4, ymm1                 // g24 = f24 + off
        vpaddd  ymm13, ymm5, ymm1                 // g25 = f25 + off
        vpaddd  ymm14, ymm6, ymm1                 // g26 = f26 + off
        vpaddd  ymm15, ymm7, ymm1                 // g27 = f27 + off
        vpsrad  ymm12, ymm12, 23                  // g24 >>= 23
        vpsrad  ymm13, ymm13, 23                  // g25 >>= 23
        vpsrad  ymm14, ymm14, 23                  // g26 >>= 23
        vpsrad  ymm15, ymm15, 23                  // g27 >>= 23
        vpmulld ymm12, ymm12, ymm0                // g24 *= q
        vpmulld ymm13, ymm13, ymm0                // g25 *= q
        vpmulld ymm14, ymm14, ymm0                // g26 *= q
        vpmulld ymm15, ymm15, ymm0                // g27 *= q
        vpsubd  ymm4, ymm4, ymm12                 // f24 -= g24
        vpsubd  ymm5, ymm5, ymm13                 // f25 -= g25
        vpsubd  ymm6, ymm6, ymm14                 // f26 -= g26
        vpsubd  ymm7, ymm7, ymm15                 // f27 -= g27

        vpaddd  ymm12, ymm8, ymm1                 // g28 = f28 + off
        vpaddd  ymm13, ymm9, ymm1                 // g29 = f29 + off
        vpaddd  ymm14, ymm10, ymm1                // g30 = f30 + off
        vpaddd  ymm15, ymm11, ymm1                // g31 = f31 + off
        vpsrad  ymm12, ymm12, 23                  // g28 >>= 23
        vpsrad  ymm13, ymm13, 23                  // g29 >>= 23
        vpsrad  ymm14, ymm14, 23                  // g30 >>= 23
        vpsrad  ymm15, ymm15, 23                  // g31 >>= 23
        vpmulld ymm12, ymm12, ymm0                // g28 *= q
        vpmulld ymm13, ymm13, ymm0                // g29 *= q
        vpmulld ymm14, ymm14, ymm0                // g30 *= q
        vpmulld ymm15, ymm15, ymm0                // g31 *= q
        vpsubd  ymm8, ymm8, ymm12                 // f28 -= g28
        vpsubd  ymm9, ymm9, ymm13                 // f29 -= g29
        vpsubd  ymm10, ymm10, ymm14               // f30 -= g30
        vpsubd  ymm11, ymm11, ymm15               // f31 -= g31

// Store final batch
        vmovdqa [rdi+768], ymm4                   // Store f24
        vmovdqa [rdi+800], ymm5                   // Store f25
        vmovdqa [rdi+832], ymm6                   // Store f26
        vmovdqa [rdi+864], ymm7                   // Store f27
        vmovdqa [rdi+896], ymm8                   // Store f28
        vmovdqa [rdi+928], ymm9                   // Store f29
        vmovdqa [rdi+960], ymm10                  // Store f30
        vmovdqa [rdi+992], ymm11                  // Store f31

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
        CFI_INC_RSP(176)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mldsa_reduce)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
