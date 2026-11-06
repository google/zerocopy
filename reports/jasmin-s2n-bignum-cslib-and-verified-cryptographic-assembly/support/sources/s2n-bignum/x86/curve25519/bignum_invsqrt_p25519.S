// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Inverse square root modulo p_25519 = 2^255 - 19
// Input x[4]; output function return (Legendre symbol) and z[4]
//
// extern int64_t bignum_invsqrt_p25519(uint64_t z[static 4],
//                                      const uint64_t x[static 4]);
//
// Given a 4-digit input x, returns a modular inverse square root mod p_25519,
// i.e. a z such that x * z^2 == 1 (mod p_25519), whenever one exists. The
// inverse square root z is chosen so that its LSB is even (note that p_25519-z
// is another possibility). The function return is the Legendre/Jacobi symbol
// (x//p_25519), which indicates whether indeed x has a modular inverse square
// root and hence whether the result is meaningful:
//
//   0: x is divisible by p_25519 so trivially there is no inverse square root
//  +1: x is coprime to p_25519 and z is indeed an inverse square root
//  -1: x is coprime to p_25519 but there is no (inverse or direct) square root
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_invsqrt_p25519)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_invsqrt_p25519)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_invsqrt_p25519)


        .text
        .balign 32

// Size in bytes of a 64-bit word

#define N 8

// Pointer-offset pairs for temporaries on stack

#define a rsp+0
#define b rsp+(4*N)
#define s rsp+(8*N)
#define t rsp+(12*N)
#define u rsp+(16*N)
#define res QWORD PTR [rsp+(20*N)]

// Total size to reserve on the stack

#define NSPACE 22*N

// Corrupted versions when stack is down 8 more

#define u8 rsp+(17*N)

// Syntactic variants to make x86_att version simpler to generate

#define A 0
#define B (4*N)
#define S (8*N)
#define T (12*N)
#define U (16*N)
#define U8 (17*N)

S2N_BN_SYMBOL(bignum_invsqrt_p25519):
        CFI_START
        _CET_ENDBR

// In this case the Windows form literally makes a subroutine call.
// This avoids hassle arising from subroutine offsets

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        CFI_CALL(Lbignum_invsqrt_p25519_standard)
        CFI_POP(rsi)
        CFI_POP(rdi)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_invsqrt_p25519)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lbignum_invsqrt_p25519_standard)

Lbignum_invsqrt_p25519_standard:
        CFI_START
#endif

// Save registers and make room for temporaries

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

        CFI_DEC_RSP(NSPACE)

// Save the return pointer for the end so we can overwrite rdi later

        mov     res, rdi

// Set up reduced version of the input argument a = x mod p_25519. Then
// get the candidate inverse square root s = a^{252-3}

        mov     rdx, [rsi]
        mov     rcx, [rsi+0x8]
        mov     r8, [rsi+0x10]
        mov     r9, [rsi+0x18]
        mov     eax, 0x1
        xor     r10d, r10d
        bts     r9, 0x3f
        adc     rax, r10
        imul    rax, rax, 0x13
        add     rdx, rax
        adc     rcx, r10
        adc     r8, r10
        adc     r9, r10
        mov     eax, 0x13
        cmovb   rax, r10
        sub     rdx, rax
        sbb     rcx, r10
        sbb     r8, r10
        sbb     r9, r10
        btr     r9, 0x3f
        mov     [rsp+A], rdx
        mov     [rsp+A+0x8], rcx
        mov     [rsp+A+0x10], r8
        mov     [rsp+A+0x18], r9

  // Power 2^2 - 1 = 3

        lea     rdi, [rsp+T]
        mov     rsi, 1
        lea     rdx, [rsp+A]
        CFI_CALL(Lbignum_invsqrt_p25519_nsqr_p25519)

        lea     rdi, [rsp+T]
        lea     rsi, [rsp+T]
        lea     rdx, [rsp+A]
        CFI_CALL(Lbignum_invsqrt_p25519_mul_p25519)

  // Power 2^4 - 1 = 15

        lea     rdi, [rsp+S]
        mov     rsi, 2
        lea     rdx, [rsp+T]
        CFI_CALL(Lbignum_invsqrt_p25519_nsqr_p25519)

        lea     rdi, [rsp+T]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+T]
        CFI_CALL(Lbignum_invsqrt_p25519_mul_p25519)

  // Power 2^5 - 1 = 31

        lea     rdi, [rsp+S]
        mov     rsi, 1
        lea     rdx, [rsp+T]
        CFI_CALL(Lbignum_invsqrt_p25519_nsqr_p25519)

        lea     rdi, [rsp+B]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+A]
        CFI_CALL(Lbignum_invsqrt_p25519_mul_p25519)

  // Power 2^10 - 1

        lea     rdi, [rsp+S]
        mov     rsi, 5
        lea     rdx, [rsp+B]
        CFI_CALL(Lbignum_invsqrt_p25519_nsqr_p25519)

        lea     rdi, [rsp+T]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+B]
        CFI_CALL(Lbignum_invsqrt_p25519_mul_p25519)

  // Power 2^20 - 1

        lea     rdi, [rsp+S]
        mov     rsi, 10
        lea     rdx, [rsp+T]
        CFI_CALL(Lbignum_invsqrt_p25519_nsqr_p25519)

        lea     rdi, [rsp+T]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+T]
        CFI_CALL(Lbignum_invsqrt_p25519_mul_p25519)

  // Power 2^25 - 1

        lea     rdi, [rsp+S]
        mov     rsi, 5
        lea     rdx, [rsp+T]
        CFI_CALL(Lbignum_invsqrt_p25519_nsqr_p25519)

        lea     rdi, [rsp+B]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+B]
        CFI_CALL(Lbignum_invsqrt_p25519_mul_p25519)

  // Power 2^50 - 1

        lea     rdi, [rsp+S]
        mov     rsi, 25
        lea     rdx, [rsp+B]
        CFI_CALL(Lbignum_invsqrt_p25519_nsqr_p25519)

        lea     rdi, [rsp+T]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+B]
        CFI_CALL(Lbignum_invsqrt_p25519_mul_p25519)

  // Power 2^100 - 1

        lea     rdi, [rsp+S]
        mov     rsi, 50
        lea     rdx, [rsp+T]
        CFI_CALL(Lbignum_invsqrt_p25519_nsqr_p25519)

        lea     rdi, [rsp+T]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+T]
        CFI_CALL(Lbignum_invsqrt_p25519_mul_p25519)

  // Power 2^125 - 1

        lea     rdi, [rsp+S]
        mov     rsi, 25
        lea     rdx, [rsp+T]
        CFI_CALL(Lbignum_invsqrt_p25519_nsqr_p25519)

        lea     rdi, [rsp+B]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+B]
        CFI_CALL(Lbignum_invsqrt_p25519_mul_p25519)

  // Power 2^250 - 1

        lea     rdi, [rsp+S]
        mov     rsi, 125
        lea     rdx, [rsp+B]
        CFI_CALL(Lbignum_invsqrt_p25519_nsqr_p25519)

        lea     rdi, [rsp+B]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+B]
        CFI_CALL(Lbignum_invsqrt_p25519_mul_p25519)

  // Power 2^252 - 3

        lea     rdi, [rsp+S]
        mov     rsi, 2
        lea     rdx, [rsp+B]
        CFI_CALL(Lbignum_invsqrt_p25519_nsqr_p25519)

        lea     rdi, [rsp+S]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+A]
        CFI_CALL(Lbignum_invsqrt_p25519_mul_p25519)

// s = a^{2^252-3} is now one candidate inverse square root.
// Generate the other one t = s * j_25519 where j_25519 = sqrt(-1)

        mov     rax, 0xc4ee1b274a0ea0b0
        mov     [rsp+T], rax
        mov     rax, 0x2f431806ad2fe478
        mov     [rsp+T+8], rax
        mov     rax, 0x2b4d00993dfbd7a7
        mov     [rsp+T+16], rax
        mov     rax, 0x2b8324804fc1df0b
        mov     [rsp+T+24], rax

        lea     rdi, [rsp+T]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+T]
        CFI_CALL(Lbignum_invsqrt_p25519_mul_p25519)

// Now multiplex between them according to whether a * s^2 = 1

        lea     rdi, [rsp+B]
        mov     rsi, 1
        lea     rdx, [rsp+S]
        CFI_CALL(Lbignum_invsqrt_p25519_nsqr_p25519)

        lea     rdi, [rsp+B]
        lea     rsi, [rsp+A]
        lea     rdx, [rsp+B]
        CFI_CALL(Lbignum_invsqrt_p25519_mul_p25519)

        mov     rax, [rsp+B]
        xor     rax, 1
        mov     rbx, [rsp+B+8]
        or      rax, rbx
        mov     rcx, [rsp+B+16]
        mov     rdx, [rsp+B+24]
        or      rcx, rdx
        or      rax, rcx

        mov     rax, [rsp+S]
        mov     rbx, [rsp+T]
        cmovnz  rax, rbx
        mov     rbx, [rsp+S+8]
        mov     rcx, [rsp+T+8]
        cmovnz  rbx, rcx
        mov     rcx, [rsp+S+16]
        mov     rdx, [rsp+T+16]
        cmovnz  rcx, rdx
        mov     rbp, [rsp+S+24]
        mov     rdx, [rsp+T+24]
        cmovnz  rbp, rdx

// For definiteness, choose "positive" (LSB=0) inverse square root

        xor     edx, edx
        lea     r8, [rdx-19]
        lea     r11, [rdx-1]
        mov     r9, r11
        mov     r10, r11
        btr     r11, 63

        sub     r8, rax
        sbb     r9, rbx
        sbb     r10, rcx
        sbb     r11, rbp

        mov     rdx, res
        test    rax, 1
        cmovnz  rax, r8
        mov     [rdx], rax
        cmovnz  rbx, r9
        mov     [rdx+8], rbx
        cmovnz  rcx, r10
        mov     [rdx+16], rcx
        cmovnz  rbp, r11
        mov     [rdx+24], rbp

// Determine if it is indeed an inverse square root, also distinguishing
// the degenerate x * z^2 == 0 (mod p_25519) case, which is equivalent to
// x == 0 (mod p_25519). Hence return the Legendre-Jacobi symbol as required.

        lea     rdi, [rsp+B]
        mov     rsi, 1
        CFI_CALL(Lbignum_invsqrt_p25519_nsqr_p25519)

        lea     rdi, [rsp+B]
        lea     rsi, [rsp+A]
        lea     rdx, [rsp+B]
        CFI_CALL(Lbignum_invsqrt_p25519_mul_p25519)

        mov     rax, 1
        mov     rbp, [rsp+B]
        xor     rax, rbp
        mov     rbx, [rsp+B+8]
        or      rax, rbx
        or      rbp, rbx
        mov     rcx, [rsp+B+16]
        mov     rdx, [rsp+B+24]
        or      rcx, rdx
        or      rax, rcx
        or      rbp, rcx

        neg     rax
        sbb     rax, rax
        lea     rax, [rax+rax+1]

        test    rbp, rbp
        cmovz   rax, rbp

// Restore stack and registers

        CFI_INC_RSP(NSPACE)

        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)
        CFI_RET

#if WINDOWS_ABI
S2N_BN_SIZE_DIRECTIVE(Lbignum_invsqrt_p25519_standard)
#else
S2N_BN_SIZE_DIRECTIVE(bignum_invsqrt_p25519)
#endif

// *************************************************************
// Local z = x * y
// *************************************************************

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lbignum_invsqrt_p25519_mul_p25519)

Lbignum_invsqrt_p25519_mul_p25519:
        CFI_START
        mov     rcx, rdx
        xor     ebp, ebp
        mov     rdx, [rcx]
        mulx    r9, r8, [rsi]
        mulx    r10, rax, [rsi+0x8]
        add     r9, rax
        mulx    r11, rax, [rsi+0x10]
        adc     r10, rax
        mulx    r12, rax, [rsi+0x18]
        adc     r11, rax
        adc     r12, rbp
        xor     ebp, ebp
        mov     rdx, [rcx+0x8]
        mulx    rbx, rax, [rsi]
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, [rsi+0x8]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsi+0x10]
        adcx    r11, rax
        adox    r12, rbx
        mulx    r13, rax, [rsi+0x18]
        adcx    r12, rax
        adox    r13, rbp
        adc     r13, rbp
        xor     ebp, ebp
        mov     rdx, [rcx+0x10]
        mulx    rbx, rax, [rsi]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsi+0x8]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsi+0x10]
        adcx    r12, rax
        adox    r13, rbx
        mulx    r14, rax, [rsi+0x18]
        adcx    r13, rax
        adox    r14, rbp
        adc     r14, rbp
        xor     ebp, ebp
        mov     rdx, [rcx+0x18]
        mulx    rbx, rax, [rsi]
        adcx    r11, rax
        adox    r12, rbx
        mulx    r15, rcx, [rsi+0x18]
        mulx    rbx, rax, [rsi+0x8]
        adcx    r12, rax
        adox    r13, rbx
        mulx    rbx, rax, [rsi+0x10]
        adcx    r13, rax
        adox    r14, rbx
        mov     edx, 0x26
        mulx    rbx, rax, r15
        adcx    r14, rcx
        adox    r15, rbp
        adc     r15, rbp
        add     rax, r11
        adc     rbx, rbp
        bt      rax, 0x3f
        adc     rbx, rbx
        lea     rcx, [rbx+0x1]
        imul    rcx, rcx, 0x13
        xor     ebp, ebp
        adox    r8, rcx
        mulx    rbx, rax, r12
        adcx    r8, rax
        adox    r9, rbx
        mulx    rbx, rax, r13
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r14
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, r15
        adc     r11, rax
        shl     rcx, 0x3f
        cmp     r11, rcx
        mov     eax, 0x13
        cmovns  rax, rbp
        sub     r8, rax
        sbb     r9, rbp
        sbb     r10, rbp
        sbb     r11, rbp
        btr     r11, 0x3f
        mov     [rdi], r8
        mov     [rdi+0x8], r9
        mov     [rdi+0x10], r10
        mov     [rdi+0x18], r11
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Lbignum_invsqrt_p25519_mul_p25519)

// *************************************************************
// Local z = 2^n * x
// *************************************************************

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lbignum_invsqrt_p25519_nsqr_p25519)

Lbignum_invsqrt_p25519_nsqr_p25519:
        CFI_START

// Copy input argument into u

        mov     rax, [rdx]
        mov     rbx, [rdx+8]
        mov     rcx, [rdx+16]
        mov     rdx, [rdx+24]
        mov     [rsp+U8], rax
        mov     [rsp+U8+8], rbx
        mov     [rsp+U8+16], rcx
        mov     [rsp+U8+24], rdx

// Main squaring loop, accumulating in u consistently  and
// only ensuring the intermediates are < 2 * p_25519 = 2^256 - 38

Lbignum_invsqrt_p25519_loop:
        mov    rdx, [rsp+U8]
        mulx   r15, r8, rdx
        mulx   r10, r9, [rsp+U8+0x8]
        mulx   r12, r11, [rsp+U8+0x18]
        mov    rdx, [rsp+U8+0x10]
        mulx   r14, r13, [rsp+U8+0x18]
        xor    ebx, ebx
        mulx   rcx, rax, [rsp+U8]
        adcx   r10, rax
        adox   r11, rcx
        mulx   rcx, rax, [rsp+U8+0x8]
        adcx   r11, rax
        adox   r12, rcx
        mov    rdx, [rsp+U8+0x18]
        mulx   rcx, rax, [rsp+U8+0x8]
        adcx   r12, rax
        adox   r13, rcx
        adcx   r13, rbx
        adox   r14, rbx
        adc    r14, rbx
        xor    ebx, ebx
        adcx   r9, r9
        adox   r9, r15
        mov    rdx, [rsp+U8+0x8]
        mulx   rdx, rax, rdx
        adcx   r10, r10
        adox   r10, rax
        adcx   r11, r11
        adox   r11, rdx
        mov    rdx, [rsp+U8+0x10]
        mulx   rdx, rax, rdx
        adcx   r12, r12
        adox   r12, rax
        adcx   r13, r13
        adox   r13, rdx
        mov    rdx, [rsp+U8+0x18]
        mulx   r15, rax, rdx
        adcx   r14, r14
        adox   r14, rax
        adcx   r15, rbx
        adox   r15, rbx
        mov    edx, 0x26
        xor    ebx, ebx
        mulx   rcx, rax, r12
        adcx   r8, rax
        adox   r9, rcx
        mulx   rcx, rax, r13
        adcx   r9, rax
        adox   r10, rcx
        mulx   rcx, rax, r14
        adcx   r10, rax
        adox   r11, rcx
        mulx   r12, rax, r15
        adcx   r11, rax
        adox   r12, rbx
        adcx   r12, rbx
        shld   r12, r11, 0x1
        btr    r11, 0x3f
        mov    edx, 0x13
        imul   rdx, r12
        add    r8, rdx
        adc    r9, rbx
        adc    r10, rbx
        adc    r11, rbx
        mov    [rsp+U8], r8
        mov    [rsp+U8+0x8], r9
        mov    [rsp+U8+0x10], r10
        mov    [rsp+U8+0x18], r11

// Loop as applicable

        dec     rsi
        jnz     Lbignum_invsqrt_p25519_loop

// We know the intermediate result x < 2^256 - 38, and now we do strict
// modular reduction mod 2^255 - 19. Note x < 2^255 - 19 <=> x + 19 < 2^255
// which is equivalent to a "ns" condition. We just use the results where
// they were in registers [r11;r10;r9;r8] instead of re-loading them.

        mov     eax, 19
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        add     rax, r8
        adc     rbx, r9
        adc     rcx, r10
        adc     rdx, r11

        cmovns  rax, r8
        cmovns  rbx, r9
        cmovns  rcx, r10
        cmovns  rdx, r11
        btr     rdx, 63
        mov     [rdi], rax
        mov     [rdi+8], rbx
        mov     [rdi+16], rcx
        mov     [rdi+24], rdx
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Lbignum_invsqrt_p25519_nsqr_p25519)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
