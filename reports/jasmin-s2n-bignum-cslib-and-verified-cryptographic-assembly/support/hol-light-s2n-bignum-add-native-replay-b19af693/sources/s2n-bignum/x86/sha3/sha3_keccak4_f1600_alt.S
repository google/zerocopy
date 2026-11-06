// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Keccak-f1600 permutation for SHA3, batch of four independent operations
// Input a[100], rc[24], rho8[4], rho56[4]; output a[100]
//
// The input/output argument is in effect four 25-element Keccak arrays
// a[0...24], a[25..49], a[50..74] and a[75..99], which could be considered
// as type a[25][4].
//
// Keccak-f1600 permutation operation is at the core of SHA3 and SHAKE
// and is fully specified here:
//
//   https://keccak.team/files/Keccak-reference-3.0.pdf
//
//    extern void sha3_keccak4_f1600_alt(uint64_t a[100], const uint64_t rc[24], const uint64_t rho8[4], const uint64_t rho56[4]);
//
// Standard x86-64 ABI: RDI = a, RSI = rc, RDX = rho8, RCX = rho56
// Microsoft x64 ABI:   RCX = a, RDX = rc, R8 = rho8, R9 = rho56
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha3_keccak4_f1600_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sha3_keccak4_f1600_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha3_keccak4_f1600_alt)
        .text
        .balign 32

S2N_BN_SYMBOL(sha3_keccak4_f1600_alt):
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
    mov rdx, r8
    mov rcx, r9
#endif

   // **** Bitstates Allocation Map **** //
   // 0x0(%rsp)     A[0]    [state0[0], state1[0], state2[0], state3[0]]     Input (%rdi) offsets: 0x00, 0xC8, 0x190, 0x258
   // 0x20(%rsp)    A[1]    [state0[1], state1[1], state2[1], state3[1]]     Input (%rdi) offsets: 0x08, 0xD0, 0x198, 0x260
   // 0x40(%rsp)    A[2]    [state0[2], state1[2], state2[2], state3[2]]     Input (%rdi) offsets: 0x10, 0xD8, 0x1A0, 0x268
   // 0x60(%rsp)    A[3]    [state0[3], state1[3], state2[3], state3[3]]     Input (%rdi) offsets: 0x18, 0xE0, 0x1A8, 0x270
   // 0x80(%rsp)    A[4]    [state0[4], state1[4], state2[4], state3[4]]     Input (%rdi) offsets: 0x20, 0xE8, 0x1B0, 0x278
   // 0xa0(%rsp)    A[5]    [state0[5], state1[5], state2[5], state3[5]]     Input (%rdi) offsets: 0x28, 0xF0, 0x1B8, 0x280
   // 0xc0(%rsp)    A[6]    [state0[6], state1[6], state2[6], state3[6]]     Input (%rdi) offsets: 0x30, 0xF8, 0x1C0, 0x288
   // ymm10         A[7]    [state0[7], state1[7], state2[7], state3[7]]     Input (%rdi) offsets: 0x38, 0x100, 0x1C8, 0x290
   // ymm14         A[8]    [state0[8], state1[8], state2[8], state3[8]]     Input (%rdi) offsets: 0x40, 0x108, 0x1D0, 0x298
   // 0xe0(%rsp)    A[9]    [state0[9], state1[9], state2[9], state3[9]]     Input (%rdi) offsets: 0x48, 0x110, 0x1D8, 0x2A0
   // 0x100(%rsp)   A[10]   [state0[10], state1[10], state2[10], state3[10]] Input (%rdi) offsets: 0x50, 0x118, 0x1E0, 0x2A8
   // ymm8          A[11]   [state0[11], state1[11], state2[11], state3[11]] Input (%rdi) offsets: 0x58, 0x120, 0x1E8, 0x2B0
   // ymm15         A[12]   [state0[12], state1[12], state2[12], state3[12]] Input (%rdi) offsets: 0x60, 0x128, 0x1F0, 0x2B8
   // 0x120(%rsp)   A[13]   [state0[13], state1[13], state2[13], state3[13]] Input (%rdi) offsets: 0x68, 0x130, 0x1F8, 0x2C0
   // 0x140(%rsp)   A[14]   [state0[14], state1[14], state2[14], state3[14]] Input (%rdi) offsets: 0x70, 0x138, 0x200, 0x2C8
   // ymm9          A[15]   [state0[15], state1[15], state2[15], state3[15]] Input (%rdi) offsets: 0x78, 0x140, 0x208, 0x2D0
   // 0x160(%rsp)   A[16]   [state0[16], state1[16], state2[16], state3[16]] Input (%rdi) offsets: 0x80, 0x148, 0x210, 0x2D8
   // 0x180(%rsp)   A[17]   [state0[17], state1[17], state2[17], state3[17]] Input (%rdi) offsets: 0x88, 0x150, 0x218, 0x2E0
   // ymm13         A[18]   [state0[18], state1[18], state2[18], state3[18]] Input (%rdi) offsets: 0x90, 0x158, 0x220, 0x2E8
   // 0x1a0(%rsp)   A[19]   [state0[19], state1[19], state2[19], state3[19]] Input (%rdi) offsets: 0x98, 0x160, 0x228, 0x2F0
   // 0x1c0(%rsp)   A[20]   [state0[20], state1[20], state2[20], state3[20]] Input (%rdi) offsets: 0xA0, 0x168, 0x230, 0x2F8
   // ymm3          A[21]   [state0[21], state1[21], state2[21], state3[21]] Input (%rdi) offsets: 0xA8, 0x170, 0x238, 0x300
   // ymm7          A[22]   [state0[22], state1[22], state2[22], state3[22]] Input (%rdi) offsets: 0xB0, 0x178, 0x240, 0x308
   // 0x1e0(%rsp)   A[23]   [state0[23], state1[23], state2[23], state3[23]] Input (%rdi) offsets: 0xB8, 0x180, 0x248, 0x310
   // ymm2          A[24]   [state0[24], state1[24], state2[24], state3[24]] Input (%rdi) offsets: 0xC0, 0x188, 0x250, 0x318

     mov    r11, rsp
     and    rsp,0xffffffffffffffe0
     .cfi_register rsp, r11
     sub    rsp,0x300

     // Load 32 bytes from each of the 4 states (A[0-3])
     vmovdqu ymm0,[rdi]                            // Load state0[0, 1, 2, 3] (32 bytes from Input (%rdi) offset: 0x00)
     vmovdqu ymm3,[rdi+0xc8]                       // Load state1[0, 1, 2, 3] (32 bytes from Input (%rdi) offset: 0xC8)
     vmovdqu ymm1,[rdi+0x190]                      // Load state2[0, 1, 2, 3] (32 bytes from Input (%rdi) offset: 0x190)
     vmovdqu ymm4,[rdi+0x258]                      // Load state3[0, 1, 2, 3] (32 bytes from Input (%rdi) offset: 0x258)

     // Interleave low and high qwords from ymm0(state0[0,1,2,3]) and ymm3(state1[0,1,2,3])
     vpunpcklqdq ymm2,ymm0,ymm3                    // ymm2 = [state0[0] | state1[0] | state0[2] | state1[2]]
     vpunpckhqdq ymm0,ymm0,ymm3                    // ymm0 = [state0[1] | state1[1] | state0[3] | state1[3]]

     // Interleave low and high qwords from ymm1(state2[0,1,2,3]) and ymm4(state3[0,1,2,3])
     vpunpcklqdq ymm3,ymm1,ymm4                    // ymm3 = [state2[0] | state3[0] | state2[2] | state3[2]]

     // Permute 128-bit lanes to complete the interleave for A[0] and A[2]
     vperm2i128 ymm7,ymm2,ymm3,0x20                // A[0] = ymm7 = [state0[0] | state1[0] | state2[0] | state3[0]]
     vpunpckhqdq ymm1,ymm1,ymm4                    // ymm1 = [state2[1] | state3[1] | state2[3] | state3[3]]
     vperm2i128 ymm3,ymm2,ymm3,0x31                // A[2] = ymm3 = [state0[2] | state1[2] | state2[2] | state3[2]]
     vmovdqu ymm4,[rdi+0x278]                      // Pre-load state3[4, 5, 6, 7] for next group
     vmovdqu [rsp+0x40],ymm3                      // store A[2] -> on stack

     // Permute 128-bit lanes to complete the interleave for A[3] and A[1]
     vperm2i128 ymm3,ymm0,ymm1,0x31                // A[3] = ymm3 = [state0[3] | state1[3] | state2[3] | state3[3]]
     vmovdqu [rsp+0x0],ymm7                      // store A[0] -> on stack
     vperm2i128 ymm7,ymm0,ymm1,0x20                // A[1] = ymm7 = [state0[1] | state1[1] | state2[1] | state3[1]]

     vmovdqu ymm0,[rdi+0x20]
     vmovdqu ymm1,[rdi+0x1b0]
     vmovdqu [rsp+0x60],ymm3                      // store A[3]
     vmovdqu ymm3,[rdi+0xe8]
     vmovdqu [rsp+0x20],ymm7                      // store A[1]

     // Load, Interleave, and Store 32 bytes from each of the 4 states (A[4-7])
     vpunpcklqdq ymm2,ymm0,ymm3
     vpunpckhqdq ymm0,ymm0,ymm3
     vpunpcklqdq ymm3,ymm1,ymm4
     vperm2i128 ymm7,ymm2,ymm3,0x20
     vpunpckhqdq ymm1,ymm1,ymm4
     vperm2i128 ymm3,ymm2,ymm3,0x31
     vmovdqu ymm4,[rdi+0x298]
     vperm2i128 ymm14,ymm0,ymm1,0x31
     vmovdqu [rsp+0x80],ymm7
     vperm2i128 ymm7,ymm0,ymm1,0x20
     vmovdqu ymm0,[rdi+0x40]
     vmovdqu ymm1,[rdi+0x1d0]
     vmovdqu [rsp+0xc0],ymm3
     vmovdqu ymm3,[rdi+0x108]
     vmovdqu ymm10,ymm14
     vmovdqu [rsp+0xa0],ymm7

     // Load, Interleave, and Store 32 bytes from each of the 4 states (A[8-11])
     vpunpcklqdq ymm2,ymm0,ymm3
     vpunpckhqdq ymm0,ymm0,ymm3
     vpunpcklqdq ymm3,ymm1,ymm4
     vpunpckhqdq ymm1,ymm1,ymm4
     vperm2i128 ymm11,ymm2,ymm3,0x20
     vperm2i128 ymm3,ymm2,ymm3,0x31
     vperm2i128 ymm7,ymm0,ymm1,0x20
     vmovdqu [rsp+0x100],ymm3
     vperm2i128 ymm8,ymm0,ymm1,0x31
     vmovdqu ymm3,[rdi+0x128]
     vmovdqu ymm0,[rdi+0x60]
     vmovdqu ymm1,[rdi+0x1f0]
     vmovdqu [rsp+0xe0],ymm7
     vmovdqu ymm14,ymm11
     vmovdqu ymm4,[rdi+0x2b8]
     vmovdqu ymm5,[rdi+0x2f8]

     // Load, Interleave, and Store 32 bytes from each of the 4 states (A[12-15])
     vpunpcklqdq ymm2,ymm0,ymm3
     vpunpckhqdq ymm0,ymm0,ymm3
     vpunpcklqdq ymm3,ymm1,ymm4
     vpunpckhqdq ymm1,ymm1,ymm4
     vmovdqu ymm4,[rdi+0x2d8]
     vperm2i128 ymm15,ymm2,ymm3,0x20
     vperm2i128 ymm3,ymm2,ymm3,0x31
     vperm2i128 ymm7,ymm0,ymm1,0x20
     vperm2i128 ymm9,ymm0,ymm1,0x31
     vmovdqu [rsp+0x140],ymm3
     vmovdqu ymm0,[rdi+0x80]
     vmovdqu ymm3,[rdi+0x148]
     vmovdqu ymm1,[rdi+0x210]
     vmovdqu [rsp+0x120],ymm7

     // Load, Interleave, and Store 32 bytes from each of the 4 states (A[16-19])
     vpunpcklqdq ymm2,ymm0,ymm3
     vpunpckhqdq ymm0,ymm0,ymm3
     vpunpcklqdq ymm3,ymm1,ymm4
     vpunpckhqdq ymm1,ymm1,ymm4
     vperm2i128 ymm7,ymm2,ymm3,0x20
     vperm2i128 ymm13,ymm2,ymm3,0x31
     vperm2i128 ymm3,ymm0,ymm1,0x31
     vmovdqu [rsp+0x160],ymm7
     vperm2i128 ymm7,ymm0,ymm1,0x20
     vmovdqu ymm0,[rdi+0xa0]
     vmovdqu ymm1,[rdi+0x230]
     vmovdqu [rsp+0x1a0],ymm3
     vmovdqu ymm3,[rdi+0x168]

     // Load, Interleave, and Store 32 bytes from each of the 4 states (A[20-23])
     vpunpcklqdq ymm4,ymm1,ymm5
     vpunpckhqdq ymm1,ymm1,ymm5
     vmovdqu [rsp+0x180],ymm7
     vpunpcklqdq ymm2,ymm0,ymm3
     vpunpckhqdq ymm0,ymm0,ymm3
     vperm2i128 ymm12,ymm2,ymm4,0x20
     vperm2i128 ymm3,ymm0,ymm1,0x20
     vperm2i128 ymm7,ymm2,ymm4,0x31
     vperm2i128 ymm4,ymm0,ymm1,0x31

     // Load, Interleave, and Store 8 bytes from each of the 4 states (A[24])
     // A[24] is the last element (only 8 bytes per state)
     vmovq  xmm0,[rdi+0x250]                       // Load state2[24] into lower 64 bits of xmm0
     vmovq  xmm1,[rdi+0xc0]                        // Load state0[24] into lower 64 bits of xmm1
     vmovdqu [rsp+0x1c0],ymm12
     vmovdqu [rsp+0x1e0],ymm4
     vpinsrq xmm0,xmm0,[rdi+0x318],0x1             // Insert state3[24] into upper 64 bits of xmm0 = [state2[24] | state3[24]]
     vpinsrq xmm1,xmm1,[rdi+0x188],0x1             // Insert state1[24] into upper 64 bits of xmm1 = [state0[24] | state1[24]]
     vinserti128 ymm2,ymm1,xmm0,0x1                // Interleave into ymm2 = A[24] = [state0[24] | state1[24] | state2[24] | state3[24]]

     // Initialize the loop counter
     mov r10, 0

Lsha3_keccak4_f1600_alt:

     // =====================================================================
     // Theta Step
     // =====================================================================
     // Compute the column parities C[x] = A[x,0] xor A[x,1] xor A[x,2] xor A[x,3] xor A[x,4]
     // Then D[x] = C[x-1] xor ROL(C[x+1], 1)
     // Then A'[x,y] = A[x,y] xor D[x]

     // Theta step
     vmovdqu ymm4,[rsp+0xa0]
     vpxor  ymm0,ymm9,[rsp+0x1c0]                  // A[0,3] xor A[0,4] (A[15] xor A[20])
     vmovdqu [rsp+0x200],ymm9
     vmovdqu ymm9,ymm10
     vmovdqu ymm11,[rsp+0xc0]
     vmovdqu ymm12,[rsp+0x160]
     vmovdqu [rsp+0x240],ymm3
     vpxor  ymm1,ymm4,[rsp+0x100]                  // A[0,1] xor A[0,2] (A[5] xor A[10])
     vmovdqu ymm10,[rsp+0x40]
     vmovdqu [rsp+0x220],ymm4
     vpxor  ymm12,ymm12,ymm3                       // A[1,3] xor A[1,4] (A[16] xor A[21])
     vmovdqu ymm6,[rsp+0x20]
     vmovdqu ymm4,[rsp+0x140]
     vmovdqu [rsp+0x2a0],ymm14
     vpxor  ymm0,ymm0,ymm1                         // (A[0,3] xor A[0,4]) xor (A[0,1] xor A[0,2]) ((A[15] xor A[20]) xor (A[5] xor A[10]))
     vpxor  ymm1,ymm11,ymm8                        // A[1,1] xor A[1,2] (A[6] xor A[11])
     vpxor  ymm11,ymm7,[rsp+0x180]                 // A[2,4] xor A[2,3] (A[22] xor A[17])
     vmovdqu [rsp+0x280],ymm10
     vpxor  ymm12,ymm12,ymm1                       // (A[1,3] xor A[1,4]) xor (A[1,1] xor A[1,2]) ((A[16] xor A[21]) xor (A[6] xor A[11]))
     vpxor  ymm1,ymm9,ymm15                        // A[2,1] xor A[2,2] (A[7] xor A[12])
     vmovdqu ymm3,[rsp+0xe0]
     vmovdqu [rsp+0x260],ymm8
     vpxor  ymm11,ymm11,ymm1                       // (A[2,4] xor A[2,3]) xor (A[2,1] xor A[2,2]) ((A[22] xor A[17]) xor (A[7] xor A[12]))
     vpxor  ymm1,ymm14,[rsp+0x120]                 // A[3,1] xor A[3,2] (A[8] xor A[13])
     vpxor  ymm12,ymm12,ymm6                       // C[1] = A[1,0] xor A[1,1] xor A[1,2] xor A[1,3] xor A[1,4] (A[1] xor A[6] xor A[11] xor A[16] xor A[21])
     vmovdqu ymm8,[rsp+0x60]
     vpxor  ymm11,ymm11,ymm10                      // C[2] = A[2,0] xor A[2,1] xor A[2,2] xor A[2,3] xor A[2,4] (A[2] xor A[7] xor A[12] xor A[17] xor A[22])
     vpxor  ymm10,ymm13,[rsp+0x1e0]                // A[3,3] xor A[3,4] (A[18] xor A[23])
     vpxor  ymm3,ymm3,ymm4                         // A[4,1] xor A[4,2] (A[9] xor A[14])
     vmovdqu [rsp+0x2c0],ymm4
     vpsrlq ymm4,ymm12,0x3f
     vpsrlq ymm5,ymm11,0x3f
     vpxor  ymm0,ymm0,[rsp+0x0]                  // C[0] = A[0,0] xor A[0,1] xor A[0,2] xor A[0,3] xor A[0,4] (A[0] xor A[5] xor A[10] xor A[15] xor A[20])
     vpxor  ymm10,ymm10,ymm1                       // (A[3,3] xor A[3,4]) xor (A[3,1] xor A[3,2]) ((A[18] xor A[23]) xor (A[8] xor A[13]))
     vmovdqu ymm1,[rsp+0x80]
     vpxor  ymm10,ymm10,ymm8                       // C[3] = A[3,0] xor A[3,1] xor A[3,2] xor A[3,3] xor A[3,4] (A[3] xor A[8] xor A[13] xor A[18] xor A[23])
     vmovdqu ymm14,ymm1
     vpxor  ymm1,ymm2,[rsp+0x1a0]                  // A[4,4] xor A[4,3] (A[24] xor A[19])
     vmovdqu [rsp+0x2e0],ymm14
     vpxor  ymm1,ymm1,ymm3                         // (A[4,4] xor A[4,3]) xor (A[4,1] xor A[4,2]) ((A[24] xor A[19]) xor (A[9] xor A[14]))
     vpsllq ymm3,ymm12,0x1
     vpor   ymm3,ymm3,ymm4                         // ROL(C[1], 1)
     vpsllq ymm4,ymm11,0x1
     vpxor  ymm1,ymm1,ymm14                        // C[4] = A[4,0] xor A[4,1] xor A[4,2] xor A[4,3] xor A[4,4] (A[4] xor A[9] xor A[14] xor A[19] xor A[24])

     // C[0] = ymm0
     // C[1] = ymm12
     // C[2] = ymm11
     // C[3] = ymm10
     // C[4] = ymm1

     vpor   ymm4,ymm4,ymm5                         // ROL(C[2], 1)
     vpsrlq ymm14,ymm10,0x3f
     vpxor  ymm3,ymm3,ymm1                         // D[0] = C[4] xor ROL(C[1], 1)
     vpsllq ymm5,ymm10,0x1
     vpxor  ymm4,ymm4,ymm0                         // D[1] = C[0] xor ROL(C[2], 1)
     vpor   ymm5,ymm5,ymm14                        // ROL(C[3], 1)
     vpxor  ymm6,ymm4,ymm6                         // A'[1,0] (A'[1]) = A[1,0] (A[1]) xor D[1]
     vpxor  ymm5,ymm5,ymm12                        // D[2] = C[1] xor ROL(C[3], 1)
     vpsrlq ymm12,ymm1,0x3f
     vpsllq ymm1,ymm1,0x1
     vpxor  ymm7,ymm5,ymm7                         // A'[2,4] (A'[22]) = A[2,4] (A[22]) xor D[2]
     vpxor  ymm9,ymm5,ymm9                         // A'[2,1] (A'[7]) = A[2,1] (A[7]) xor D[2]
     vpor   ymm1,ymm1,ymm12                        // ROL(C[4], 1)
     vpxor  ymm12,ymm3,[rsp+0x0]                 // A'[0,0] (A'[0]) = A[0,0] (A[0]) xor D[0]
     vpxor  ymm1,ymm1,ymm11                        // D[3] = C[2] xor ROL(C[4], 1)
     vpsrlq ymm11,ymm0,0x3f
     vpsllq ymm0,ymm0,0x1
     vpxor  ymm13,ymm1,ymm13                       // A'[3,3] (A'[18]) = A[3,3] (A[18]) xor D[3]
     vpxor  ymm8,ymm1,ymm8                         // A'[3,0] (A'[3]) = A[3,0] (A[3]) xor D[3]
     vpor   ymm0,ymm0,ymm11                        // ROL(C[0], 1)
     vpxor  ymm0,ymm0,ymm10                        // D[4] = C[3] xor ROL(C[0], 1)

     // D[0] = ymm3
     // D[1] = ymm4
     // D[2] = ymm5
     // D[3] = ymm1
     // D[4] = ymm0

     vpxor  ymm10,ymm4,[rsp+0xc0]                 // A'[1,1] (A'[6]) = A[1,1] (A[6]) xor D[1]
     vpxor  ymm2,ymm0,ymm2                         // A'[4,4] (A'[24]) = A[4,4] (A[24]) xor D[4]

     // Rho, Pi, and Chi Steps (interleaved for performance)
     // B[x,y] = ROL(A'[...], rotation_constant) placed at position determined by Pi
     // A''[x,y] = B[x,y] XOR ((NOT B[x+1,y]) AND B[x+2,y])

     vpsrlq ymm11,ymm10,0x14
     vpsllq ymm10,ymm10,0x2c
     vpor   ymm10,ymm10,ymm11                      // B[1,0] (B[1]) = ROL(A'[1,1] (A'[6]), 44)

     vpxor  ymm11,ymm5,ymm15                       // A'[12] = A'[2,2] = A[2,2] (A[12]) xor D[2]
     vpbroadcastq ymm15,[rsi]                      // Load Round Constant (RC)
     vpsrlq ymm14,ymm11,0x15
     vpsllq ymm11,ymm11,0x2b
     vpor   ymm11,ymm11,ymm14                      // B[2,0] (B[2]) = ROL(A'[2,2] (A'[12]), 43)

     vpandn ymm14,ymm10,ymm11
     vpxor  ymm14,ymm14,ymm15
     vpxor  ymm15,ymm14,ymm12                      // (A''[0]) A''[0,0] = B[0,0] xor ((not B[1,0]) and B[2,0]) xor RC

     vpsrlq ymm14,ymm13,0x2b
     vpsllq ymm13,ymm13,0x15
     vmovdqu [rsp+0x0],ymm15                     // store A''[0,0] (A''[0]) -> on stack
     vpor   ymm13,ymm13,ymm14                      // B[3,0] (B[3]) = ROL(A'[3,3] (A'[18]), 21)

     vpandn ymm14,ymm11,ymm13
     vpxor  ymm15,ymm14,ymm10                      // (A''[1]) A''[1,0] = B[1,0] xor ((not B[2,0]) and B[3,0])

     vpsrlq ymm14,ymm2,0x32
     vpsllq ymm2,ymm2,0xe
     vmovdqu [rsp+0x20],ymm15                     // store A''[1,0] (A''[1]) -> on stack
     vpor   ymm2,ymm2,ymm14                        // B[4,0] (B[4]) = ROL(A'[4,4] (A'[24]), 14)

     // **** B[0]-B[4] Register Allocation Map ****
     // B[0]  (B[0,0])    ymm12   (A'[0,0] (A'[0]) unchanged, no rotation)
     // B[1]  (B[1,0])    ymm10   ROL(A'[1,1] (A'[6]),  44)
     // B[2]  (B[2,0])    ymm11   ROL(A'[2,2] (A'[12]), 43)
     // B[3]  (B[3,0])    ymm13   ROL(A'[3,3] (A'[18]), 21)
     // B[4]  (B[4,0])    ymm2    ROL(A'[4,4] (A'[24]), 14)

     vpandn ymm14,ymm13,ymm2
     vpxor  ymm11,ymm14,ymm11                      // (A''[2]) A''[2,0] = B[2,0] xor ((not B[3,0]) and B[4,0])
     vmovdqu [rsp+0x40],ymm11                     // store A''[2,0] (A''[2]) -> on stack
     vpandn ymm11,ymm2,ymm12
     vpandn ymm12,ymm12,ymm10
     vpxor  ymm11,ymm11,ymm13                      // (A''[3]) A''[3,0] = B[3,0] xor ((not B[4,0]) and B[0,0])
     vmovdqu [rsp+0x60],ymm11                     // store A''[3,0] (A''[3]) -> on stack
     vpxor  ymm11,ymm12,ymm2                       // (A''[4]) A''[4,0] = B[4,0] xor ((not B[0,0]) and B[1,0])

     vpsrlq ymm2,ymm8,0x24
     vpsllq ymm8,ymm8,0x1c
     vmovdqu [rsp+0x80],ymm11                     // store A''[4,0] (A''[4]) -> on stack
     vpor   ymm8,ymm8,ymm2                         // B[0,1] (B[5]) = ROL(A'[3,0] (A'[3]), 28)

     vpxor  ymm2,ymm0,[rsp+0xe0]                  // A'[9] = A'[4,1] = A[4,1] (A[9]) xor D[4]
     vpsrlq ymm10,ymm2,0x2c
     vpsllq ymm2,ymm2,0x14
     vpor   ymm2,ymm2,ymm10                        // B[1,1] (B[6]) = ROL(A'[4,1] (A'[9]), 20)

     vpxor  ymm10,ymm3,[rsp+0x100]                 // A'[10] = A'[0,2] = A[0,2] (A[10]) xor D[0]
     vpsrlq ymm11,ymm10,0x3d
     vpsllq ymm10,ymm10,0x3
     vpor   ymm10,ymm10,ymm11                      // B[2,1] (B[7]) = ROL(A'[0,2] (A'[10]), 3)

     vpandn ymm11,ymm2,ymm10
     vpxor  ymm11,ymm11,ymm8                       // (A''[5]) A''[0,1] = B[0,1] xor ((not B[1,1]) and B[2,1])
     vmovdqu [rsp+0xa0],ymm11                     // store A''[0,1] (A''[5]) -> on stack

     vpxor  ymm11,ymm4,[rsp+0x160]                 // A'[16] = A'[1,3] = A[1,3] (A[16]) xor D[1]
     vpsrlq ymm12,ymm11,0x13
     vpsllq ymm11,ymm11,0x2d
     vpor   ymm11,ymm11,ymm12                      // B[3,1] (B[8]) = ROL(A'[1,3] (A'[16]), 45)

     vpandn ymm12,ymm10,ymm11
     vpxor  ymm12,ymm12,ymm2                       // (A''[6]) A''[1,1] = B[1,1] xor ((not B[2,1]) and B[3,1])
     vmovdqu [rsp+0xc0],ymm12                     // store A''[1,1] (A''[6]) -> on stack

     vpsrlq ymm12,ymm7,0x3
     vpsllq ymm7,ymm7,0x3d
     vpor   ymm7,ymm7,ymm12                        // B[4,1] (B[9]) = ROL(A'[2,4] (A'[22]), 61)

     // **** B[5]-B[9] Register Allocation Map ****
     // B[5]  (B[0,1])    ymm8    ROL(A'[3,0] (A'[3]), 28)
     // B[6]  (B[1,1])    ymm2    ROL(A'[4,1] (A'[9]), 20)
     // B[7]  (B[2,1])    ymm10   ROL(A'[0,2] (A'[10]), 3)
     // B[8]  (B[3,1])    ymm11   ROL(A'[1,3] (A'[16]), 45)
     // B[9]  (B[4,1])    ymm7    ROL(A'[2,4] (A'[22]), 61)

     vpandn ymm12,ymm11,ymm7
     vpxor  ymm10,ymm12,ymm10                      // (A''[7]) A''[2,1] = B[2,1] xor ((not B[3,1]) and B[4,1])

     vpandn ymm12,ymm7,ymm8
     vpandn ymm8,ymm8,ymm2

     vpsrlq ymm2,ymm6,0x3f
     vpsllq ymm6,ymm6,0x1
     vpxor  ymm14,ymm12,ymm11                      // (A''[8]) A''[3,1] = B[3,1] xor ((not B[4,1]) and B[0,1])
     vpor   ymm6,ymm6,ymm2                         // B[0,2] (B[10]) = ROL(A'[1,0] (A'[1]), 1)

     vpsrlq ymm2,ymm9,0x3a
     vpxor  ymm12,ymm8,ymm7                        // (A''[9]) A''[4,1] = B[4,1] xor ((not B[0,1]) and B[1,1])
     vpsllq ymm9,ymm9,0x6
     vmovdqu [rsp+0xe0],ymm12                     // store A''[4,1] (A''[9]) -> on stack

     vpxor  ymm7,ymm0,[rsp+0x1a0]                  // A'[19] = A'[4,3] = A[4,3] (A[19]) xor D[4]
     vpor   ymm9,ymm9,ymm2                         // B[1,2] (B[11]) = ROL(A'[2,1] (A'[7]), 6)

     vpxor  ymm2,ymm1,[rsp+0x120]                  // A'[13] = A'[3,2] = A[3,2] (A[13]) xor D[3]
     vpshufb ymm7,ymm7,[rdx]                       // B[4,3] (B[19]) = ROL(A'[4,3] (A'[19]), 8)
     vpsrlq ymm11,ymm2,0x27
     vpsllq ymm2,ymm2,0x19
     vpor   ymm11,ymm11,ymm2                       // B[3,2] (B[13]) = ROL(A'[3,2] (A'[13]), 25)

     vpandn ymm2,ymm9,ymm11
     vpandn ymm8,ymm11,ymm7
     vpxor  ymm12,ymm2,ymm6                        // (A''[10]) A''[0,2] = B[0,2] xor ((not B[1,2]) and B[2,2])

     vpxor  ymm2,ymm3,[rsp+0x1c0]                  // A'[20] = A'[0,4] = A[0,4] (A[20]) xor D[0]
     vpxor  ymm8,ymm8,ymm9                         // (A''[12]) A''[2,2] partial
     vmovdqu [rsp+0x100],ymm12                     // store A''[0,2] (A''[10]) -> on stack
     vpsrlq ymm12,ymm2,0x2e
     vpsllq ymm2,ymm2,0x12
     vpor   ymm2,ymm12,ymm2                        // B[4,2] (B[14]) = ROL(A'[0,4] (A'[20]), 18)

     // **** B[10]-B[14] Register Allocation Map ****
     // B[10] (B[0,2])    ymm6    ROL(A'[1,0] (A'[1]), 1)
     // B[11] (B[1,2])    ymm9    ROL(A'[2,1] (A'[7]), 6)
     // B[12] (B[2,2])    ymm11   ROL(A'[3,2] (A'[13]), 25)
     // B[13] (B[3,2])    ymm7    ROL(A'[4,3] (A'[19]), 8)
     // B[14] (B[4,2])    ymm2    ROL(A'[0,4] (A'[20]), 18)

     vpandn ymm12,ymm7,ymm2
     vpxor  ymm15,ymm12,ymm11                      // (A''[12]) A''[2,2] = B[2,2] xor ((not B[3,2]) and B[4,2])

     vpandn ymm11,ymm2,ymm6
     vpandn ymm6,ymm6,ymm9
     vpxor  ymm12,ymm11,ymm7                       // (A''[13]) A''[3,2] = B[3,2] xor ((not B[4,2]) and B[0,2])
     vmovdqu [rsp+0x120],ymm12                     // store A''[3,2] (A''[13]) -> on stack

     vpxor  ymm12,ymm6,ymm2                        // (A''[14]) A''[4,2] = B[4,2] xor ((not B[0,2]) and B[1,2])

     vpxor  ymm6,ymm0,[rsp+0x2e0]                   // A'[4] = A'[4,0] = A[4,0] (A[4]) xor D[4]
     vpxor  ymm0,ymm0,[rsp+0x2c0]                   // A'[14] = A'[4,2] = A[4,2] (A[14]) xor D[4]
     vmovdqu [rsp+0x140],ymm12                     // store A''[4,2] (A''[14]) -> on stack
     vpsrlq ymm2,ymm6,0x25
     vpsllq ymm6,ymm6,0x1b
     vpor   ymm2,ymm2,ymm6                         // B[0,3] (B[15]) = ROL(A'[4,0] (A'[4]), 27)

     vpxor  ymm6,ymm3,[rsp+0x220]                   // A'[5] = A'[0,1] = A[0,1] (A[5]) xor D[0]
     vpxor  ymm3,ymm3,[rsp+0x200]                    // A'[15] = A'[0,3] = A[0,3] (A[15]) xor D[0]
     vpsrlq ymm7,ymm6,0x1c
     vpsllq ymm6,ymm6,0x24
     vpor   ymm7,ymm7,ymm6                         // B[1,3] (B[16]) = ROL(A'[0,1] (A'[5]), 36)

     vpxor  ymm6,ymm4,[rsp+0x260]                   // A'[11] = A'[1,2] = A[1,2] (A[11]) xor D[1]
     vpxor  ymm4,ymm4,[rsp+0x240]                   // A'[21] = A'[1,4] = A[1,4] (A[21]) xor D[1]
     vpsrlq ymm12,ymm6,0x36
     vpsllq ymm6,ymm6,0xa
     vpor   ymm12,ymm12,ymm6                       // B[2,3] (B[17]) = ROL(A'[1,2] (A'[11]), 10)

     vpxor  ymm6,ymm5,[rsp+0x180]                  // A'[17] = A'[2,3] = A[2,3] (A[17]) xor D[2]
     vpxor  ymm5,ymm5,[rsp+0x280]                   // A'[2] = A'[2,0] = A[2,0] (A[2]) xor D[2]

     vpandn ymm9,ymm7,ymm12
     vpsrlq ymm11,ymm6,0x31
     vpsllq ymm6,ymm6,0xf
     vpxor  ymm9,ymm9,ymm2                         // (A''[15]) A''[0,3] = B[0,3] xor ((not B[1,3]) and B[2,3])
     vpor   ymm11,ymm11,ymm6                       // B[3,3] (B[18]) = ROL(A'[2,3] (A'[17]), 15)

     vpandn ymm6,ymm12,ymm11
     vpxor  ymm6,ymm6,ymm7                         // (A''[16]) A''[1,3] = B[1,3] xor ((not B[2,3]) and B[3,3])
     vmovdqu [rsp+0x160],ymm6                      // store A''[1,3] (A''[16]) -> on stack

     vpxor  ymm6,ymm1,[rsp+0x1e0]                  // A'[23] = A'[3,4] = A[3,4] (A[23]) xor D[3]
     vpxor  ymm1,ymm1,[rsp+0x2a0]                   // A'[8] = A'[3,1] = A[3,1] (A[8]) xor D[3]
     vpshufb ymm6,ymm6,[rcx]                       // B[4,3] (B[19]) = ROL(A'[3,4] (A'[23]), 56)

     // **** B[15]-B[19] Register Allocation Map ****
     // B[15] (B[0,3])    ymm2    ROL(A'[4,0] (A'[4]), 27)
     // B[16] (B[1,3])    ymm7    ROL(A'[0,1] (A'[5]), 36)
     // B[17] (B[2,3])    ymm12   ROL(A'[1,2] (A'[11]), 10)
     // B[18] (B[3,3])    ymm11   ROL(A'[2,3] (A'[17]), 15)
     // B[19] (B[4,3])    ymm6    ROL(A'[3,4] (A'[23]), 56)

     vpandn ymm13,ymm11,ymm6
     vpxor  ymm13,ymm13,ymm12                      // (A''[17]) A''[2,3] = B[2,3] xor ((not B[3,3]) and B[4,3])
     vmovdqu [rsp+0x180],ymm13                     // store A''[2,3] (A''[17]) -> on stack

     vpandn ymm13,ymm6,ymm2
     vpandn ymm2,ymm2,ymm7
     vpxor  ymm2,ymm2,ymm6                         // (A''[19]) A''[4,3] = B[4,3] xor ((not B[0,3]) and B[1,3])

     vpsrlq ymm6,ymm4,0x3e
     vpxor  ymm13,ymm13,ymm11                      // (A''[18]) A''[3,3] = B[3,3] xor ((not B[4,3]) and B[0,3])
     vmovdqu [rsp+0x1a0],ymm2                      // store A''[4,3] (A''[19]) -> on stack
     vpsrlq ymm2,ymm5,0x2
     vpsllq ymm5,ymm5,0x3e
     vpor   ymm2,ymm2,ymm5                         // B[0,4] (B[20]) = ROL(A'[2,0] (A'[2]), 62)

     vpsrlq ymm5,ymm1,0x9
     vpsllq ymm1,ymm1,0x37

     vpsllq ymm4,ymm4,0x2
     vpor   ymm1,ymm5,ymm1                         // B[1,4] (B[21]) = ROL(A'[3,1] (A'[8]), 55)

     vpsrlq ymm5,ymm0,0x19
     vpor   ymm4,ymm6,ymm4                         // B[3,4] (B[23]) = ROL(A'[1,4] (A'[21]), 2)
     vpsllq ymm0,ymm0,0x27
     vpor   ymm5,ymm5,ymm0                         // B[2,4] (B[22]) = ROL(A'[4,2] (A'[14]), 39)

     vpandn ymm0,ymm1,ymm5
     vpxor  ymm0,ymm0,ymm2                         // (A''[20]) A''[0,4] = B[0,4] xor ((not B[1,4]) and B[2,4])
     vmovdqu [rsp+0x1c0],ymm0                      // store A''[0,4] (A''[20]) -> on stack

     vpsrlq ymm0,ymm3,0x17
     vpsllq ymm3,ymm3,0x29
     vpor   ymm0,ymm0,ymm3                         // B[4,4] (B[24]) = ROL(A'[0,3] (A'[15]), 41)

     // **** B[20]-B[24] Register Allocation Map ****
     // B[20] (B[0,4])    ymm2    ROL(A'[2,0] (A'[2]), 62)
     // B[21] (B[1,4])    ymm1    ROL(A'[3,1] (A'[8]), 55)
     // B[22] (B[2,4])    ymm5    ROL(A'[4,2] (A'[14]), 39)
     // B[23] (B[3,4])    ymm4    ROL(A'[1,4] (A'[21]), 2)
     // B[24] (B[4,4])    ymm0    ROL(A'[0,3] (A'[15]), 41)

     vpandn ymm7,ymm0,ymm4
     vpandn ymm3,ymm5,ymm0
     vpxor  ymm7,ymm7,ymm5                         // (A''[22]) A''[2,4] = B[2,4] xor ((not B[4,4]) and B[3,4])

     vpandn ymm5,ymm4,ymm2
     vpandn ymm2,ymm2,ymm1
     vpxor  ymm5,ymm5,ymm0                         // (A''[23]) A''[3,4] = B[3,4] xor ((not B[4,4]) and B[0,4])

     vpxor  ymm3,ymm3,ymm1                         // (A''[21]) A''[1,4] = B[1,4] xor ((not B[2,4]) and B[3,4])

     vpxor  ymm2,ymm2,ymm4                         // (A''[24]) A''[4,4] = B[4,4] xor ((not B[0,4]) and B[1,4])
     vmovdqu [rsp+0x1e0],ymm5                      // store A''[3,4] (A''[23]) -> on stack

     add rsi, 8
     add r10, 1
     cmp r10, 0x18
     jne Lsha3_keccak4_f1600_alt

     // Load, De-interleave, and Store 32 bytes to each of the 4 states (A[0-3])
     vmovdqu ymm4,[rsp+0x0]                      // Load A[0] from stack
     vmovdqu ymm5,[rsp+0x40]                      // Load A[2] from stack
     vmovdqu ymm0,[rsp+0x20]                      // Load A[1] from stack
     vmovdqu ymm1,[rsp+0x60]                      // Load A[3] from stack
     vmovdqu ymm12,[rsp+0x1c0]
     vmovdqu [rsp+0x1c0],ymm2

     // De-interleave ymm4(A[0]) and ymm0(A[1])
     vpunpcklqdq ymm2,ymm4,ymm0                    // ymm2 = [state0[0] | state0[1] | state2[0] | state2[1]]
     vpunpckhqdq ymm0,ymm4,ymm0                    // ymm0 = [state1[0] | state1[1] | state3[0] | state3[1]]
     // De-interleave ymm5(A[2]) and ymm1(A[3])
     vpunpcklqdq ymm4,ymm5,ymm1                    // ymm4 = [state0[2] | state0[3] | state2[2] | state2[3]]
     vpunpckhqdq ymm1,ymm5,ymm1                    // ymm1 = [state1[2] | state1[3] | state3[2] | state3[3]]

     // Permute 128-bit lanes to complete the de-interleave
     vperm2i128 ymm6,ymm2,ymm4,0x20                // ymm6 = [state0[0] | state0[1] | state0[2] | state0[3]]
     vperm2i128 ymm2,ymm2,ymm4,0x31                // ymm2 = [state2[0] | state2[1] | state2[2] | state2[3]]
     vmovdqu ymm4,[rsp+0x80]
     vperm2i128 ymm5,ymm0,ymm1,0x20                // ymm5 = [state1[0] | state1[1] | state1[2] | state1[3]]
     vperm2i128 ymm0,ymm0,ymm1,0x31                // ymm0 = [state3[0] | state3[1] | state3[2] | state3[3]]

     // Store de-interleaved results back to output
     vmovdqu [rdi],ymm6                            // Store state0[0, 1, 2, 3] (32 bytes to Output (%rdi) offset: 0x00)
     vmovdqu [rdi+0xc8],ymm5                       // Store state1[0, 1, 2, 3] (32 bytes to Output (%rdi) offset: 0xC8)
     vmovdqu [rdi+0x190],ymm2                      // Store state2[0, 1, 2, 3] (32 bytes to Output (%rdi) offset: 0x190)
     vmovdqu [rdi+0x258],ymm0                      // Store state3[0, 1, 2, 3] (32 bytes to Output (%rdi) offset: 0x258)

     // Load, De-interleave, and Store 32 bytes to each of the 4 states (A[4-7])
     vmovdqu ymm0,[rsp+0xa0]
     vpunpcklqdq ymm2,ymm4,ymm0
     vpunpckhqdq ymm1,ymm4,ymm0
     vmovdqu ymm0,[rsp+0xc0]
     vpunpcklqdq ymm4,ymm0,ymm10
     vpunpckhqdq ymm0,ymm0,ymm10
     vperm2i128 ymm6,ymm2,ymm4,0x20
     vperm2i128 ymm5,ymm1,ymm0,0x20
     vperm2i128 ymm2,ymm2,ymm4,0x31
     vmovdqu ymm4,[rsp+0xe0]
     vperm2i128 ymm1,ymm1,ymm0,0x31
     vmovdqu ymm0,[rsp+0x100]
     vmovdqu [rdi+0x1b0],ymm2
     vmovdqu [rdi+0x278],ymm1

     // Load, De-interleave, and Store 32 bytes to each of the 4 states (A[8-11])
     vpunpcklqdq ymm2,ymm14,ymm4
     vpunpckhqdq ymm1,ymm14,ymm4
     vpunpcklqdq ymm4,ymm0,ymm8
     vpunpckhqdq ymm0,ymm0,ymm8
     vmovdqu [rdi+0x20],ymm6
     vmovdqu [rdi+0xe8],ymm5
     vperm2i128 ymm6,ymm2,ymm4,0x20
     vperm2i128 ymm5,ymm1,ymm0,0x20
     vperm2i128 ymm2,ymm2,ymm4,0x31
     vperm2i128 ymm1,ymm1,ymm0,0x31
     vmovdqu ymm4,[rsp+0x120]
     vmovdqu ymm0,[rsp+0x140]
     vmovdqu [rdi+0x1d0],ymm2
     vmovdqu [rdi+0x298],ymm1

     // Load, De-interleave, and Store 32 bytes to each of the 4 states (A[12-15])
     vpunpcklqdq ymm2,ymm15,ymm4
     vpunpckhqdq ymm1,ymm15,ymm4
     vpunpcklqdq ymm4,ymm0,ymm9
     vmovdqu [rdi+0x108],ymm5
     vpunpckhqdq ymm0,ymm0,ymm9
     vmovdqu [rdi+0x40],ymm6
     vperm2i128 ymm6,ymm2,ymm4,0x20
     vperm2i128 ymm2,ymm2,ymm4,0x31
     vperm2i128 ymm5,ymm1,ymm0,0x20
     vmovdqu ymm4,[rsp+0x160]
     vperm2i128 ymm1,ymm1,ymm0,0x31
     vmovdqu ymm0,[rsp+0x180]
     vmovdqu [rdi+0x128],ymm5
     vmovdqu ymm5,[rsp+0x1a0]
     vmovdqu [rdi+0x1f0],ymm2

     // Load, De-interleave, and Store 32 bytes to each of the 4 states (A[16-19])
     vpunpcklqdq ymm2,ymm4,ymm0
     vpunpckhqdq ymm0,ymm4,ymm0
     vpunpcklqdq ymm4,ymm13,ymm5
     vmovdqu [rdi+0x60],ymm6
     vperm2i128 ymm6,ymm2,ymm4,0x20
     vmovdqu [rdi+0x2b8],ymm1
     vperm2i128 ymm2,ymm2,ymm4,0x31
     vpunpckhqdq ymm1,ymm13,ymm5
     vmovdqu [rdi+0x80],ymm6
     vmovdqu ymm4,[rsp+0x1e0]
     vperm2i128 ymm5,ymm0,ymm1,0x20
     vperm2i128 ymm0,ymm0,ymm1,0x31
     vmovdqu [rdi+0x210],ymm2

     // Load, De-interleave, and Store 32 bytes to each of the 4 states (A[20-23])
     vpunpcklqdq ymm2,ymm12,ymm3
     vmovdqu [rdi+0x2d8],ymm0
     vpunpckhqdq ymm0,ymm12,ymm3
     vpunpcklqdq ymm3,ymm7,ymm4
     vpunpckhqdq ymm1,ymm7,ymm4
     vmovdqu [rdi+0x148],ymm5
     vperm2i128 ymm5,ymm2,ymm3,0x20
     vperm2i128 ymm2,ymm2,ymm3,0x31
     vmovdqu ymm3,[rsp+0x1c0]
     vperm2i128 ymm4,ymm0,ymm1,0x20
     vperm2i128 ymm0,ymm0,ymm1,0x31

     // Store de-interleaved results back to output
     vmovdqu [rdi+0xa0],ymm5
     vextracti128 xmm15,ymm3,0x1
     vmovdqu [rdi+0x168],ymm4
     vmovdqu [rdi+0x230],ymm2
     vmovdqu [rdi+0x2f8],ymm0

     // Load, De-interleave, and Store 8 bytes to each of the 4 states (A[24])
     // A[24] is the last element (only 8 bytes per state)
     vmovq [rdi+0xc0],xmm3
     vmovhpd [rdi+0x188],xmm3
     vmovq [rdi+0x250],xmm15
     vmovhpd [rdi+0x318],xmm15
     mov  rsp, r11
     .cfi_same_value r11
     .cfi_same_value rsp

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

S2N_BN_SIZE_DIRECTIVE(sha3_keccak4_f1600_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,  "",  %progbits
#endif
