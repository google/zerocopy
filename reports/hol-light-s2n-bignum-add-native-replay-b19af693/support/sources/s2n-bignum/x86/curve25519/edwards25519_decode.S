// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Decode compressed 256-bit form of edwards25519 point
// Input c[32] (bytes); output function return and z[8]
//
// extern uint64_t edwards25519_decode(uint64_t z[static 8], const uint8_t c[static 32]);
//
// This interprets the input byte string as a little-endian number
// representing a point (x,y) on the edwards25519 curve, encoded as
// 2^255 * x_0 + y where x_0 is the least significant bit of x. It
// returns the full pair of coordinates x (at z) and y (at z+4). The
// return code is 0 for success and 1 for failure, which means that
// the input does not correspond to the encoding of any edwards25519
// point. This can happen for three reasons, where y = the lowest
// 255 bits of the input:
//
//  * y >= p_25519
//    Input y coordinate is not reduced
//  * (y^2 - 1) * (1 + d_25519 * y^2) has no modular square root
//    There is no x such that (x,y) is on the curve
//  * y^2 = 1 and top bit of input is set
//    Cannot be the canonical encoding of (0,1) or (0,-1)
//
// Standard x86-64 ABI: RDI = z, RSI = c
// Microsoft x64 ABI:   RCX = z, RDX = c
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(edwards25519_decode)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(edwards25519_decode)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(edwards25519_decode)


        .text
        .balign 32

// Size in bytes of a 64-bit word

#define N 8

// Pointer-offset pairs for temporaries on stack

#define y rsp+0
#define s rsp+(4*N)
#define t rsp+(8*N)
#define u rsp+(12*N)
#define v rsp+(16*N)
#define w rsp+(20*N)
#define q rsp+(24*N)
#define res QWORD PTR [rsp+(28*N)]
#define sgnbit QWORD PTR [rsp+(29*N)]
#define badun QWORD PTR [rsp+(30*N)]

// Total size to reserve on the stack

#define NSPACE 32*N

// Corrupted versions when stack is down 8 more

#define q8 rsp+(25*N)

// Syntactic variants to make x86_att version simpler to generate

#define Y 0
#define S (4*N)
#define T (8*N)
#define U (12*N)
#define V (16*N)
#define W (20*N)
#define Q8 (25*N)

S2N_BN_SYMBOL(edwards25519_decode):
        CFI_START
        _CET_ENDBR

// In this case the Windows form literally makes a subroutine call.
// This avoids hassle arising from subroutine offsets

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        CFI_CALL(Ledwards25519_decode_standard)
        CFI_POP(rsi)
        CFI_POP(rdi)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(edwards25519_decode)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Ledwards25519_decode_standard)

Ledwards25519_decode_standard:
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

// Load the inputs, which can be done word-wise since x86 is little-endian.
// Let y be the lowest 255 bits of the input and sgnbit the desired parity.
// If y >= p_25519 then already flag the input as invalid (badun = 1).

        mov     rax, [rsi]
        mov     [rsp+Y], rax
        mov     rbx, [rsi+8]
        mov     [rsp+Y+8], rbx
        xor     ebp, ebp
        mov     rcx, [rsi+16]
        mov     [rsp+Y+16], rcx
        mov     rdx, [rsi+24]
        btr     rdx, 63
        mov     [rsp+Y+24], rdx
        adc     rbp, rbp
        mov     sgnbit, rbp

        add     rax, 19
        adc     rbx, 0
        adc     rcx, 0
        adc     rdx, 0
        shr     rdx, 63
        mov     badun, rdx

// u = y^2 - 1 (actually y + 2^255-20, not reduced modulo)
// v = 1 + d * y^2 (not reduced modulo from the +1)
// w = u * v

        lea     rdi, [rsp+V]
        mov     rsi, 1
        lea     rdx, [rsp+Y]
        CFI_CALL(Ledwards25519_decode_nsqr_p25519)
        mov     rax, [rsp+V]
        sub     rax, 20
        mov     rbx, [rsp+V+8]
        sbb     rbx, 0
        mov     rcx, [rsp+V+16]
        sbb     rcx, 0
        mov     rdx, [rsp+V+24]
        sbb     rdx, 0
        btc     rdx, 63
        mov     [rsp+U], rax
        mov     [rsp+U+8], rbx
        mov     [rsp+U+16], rcx
        mov     [rsp+U+24], rdx

        mov     rax, 0x75eb4dca135978a3
        mov     [rsp+W], rax
        mov     rax, 0x00700a4d4141d8ab
        mov     [rsp+W+8], rax
        mov     rax, 0x8cc740797779e898
        mov     [rsp+W+16], rax
        mov     rax, 0x52036cee2b6ffe73
        mov     [rsp+W+24], rax
        lea     rdi, [rsp+V]
        lea     rsi, [rsp+W]
        lea     rdx, [rsp+V]
        CFI_CALL(Ledwards25519_decode_mul_p25519)
        mov     rax, [rsp+V]
        add     rax, 1
        mov     rbx, [rsp+V+8]
        adc     rbx, 0
        mov     rcx, [rsp+V+16]
        adc     rcx, 0
        mov     rdx, [rsp+V+24]
        adc     rdx, 0
        mov     [rsp+V], rax
        mov     [rsp+V+8], rbx
        mov     [rsp+V+16], rcx
        mov     [rsp+V+24], rdx

        lea     rdi, [rsp+W]
        lea     rsi, [rsp+U]
        lea     rdx, [rsp+V]
        CFI_CALL(Ledwards25519_decode_mul_p25519)

// Get s = w^{252-3} as a candidate inverse square root 1/sqrt(w).
// This power tower computation is the same as bignum_invsqrt_p25519

        lea     rdi, [rsp+T]
        mov     rsi, 1
        lea     rdx, [rsp+W]
        CFI_CALL(Ledwards25519_decode_nsqr_p25519)

        lea     rdi, [rsp+T]
        lea     rsi, [rsp+T]
        lea     rdx, [rsp+W]
        CFI_CALL(Ledwards25519_decode_mul_p25519)

        lea     rdi, [rsp+S]
        mov     rsi, 2
        lea     rdx, [rsp+T]
        CFI_CALL(Ledwards25519_decode_nsqr_p25519)

        lea     rdi, [rsp+T]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+T]
        CFI_CALL(Ledwards25519_decode_mul_p25519)

        lea     rdi, [rsp+S]
        mov     rsi, 1
        lea     rdx, [rsp+T]
        CFI_CALL(Ledwards25519_decode_nsqr_p25519)

        lea     rdi, [rsp+V]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+W]
        CFI_CALL(Ledwards25519_decode_mul_p25519)

        lea     rdi, [rsp+S]
        mov     rsi, 5
        lea     rdx, [rsp+V]
        CFI_CALL(Ledwards25519_decode_nsqr_p25519)

        lea     rdi, [rsp+T]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+V]
        CFI_CALL(Ledwards25519_decode_mul_p25519)

        lea     rdi, [rsp+S]
        mov     rsi, 10
        lea     rdx, [rsp+T]
        CFI_CALL(Ledwards25519_decode_nsqr_p25519)

        lea     rdi, [rsp+T]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+T]
        CFI_CALL(Ledwards25519_decode_mul_p25519)

        lea     rdi, [rsp+S]
        mov     rsi, 5
        lea     rdx, [rsp+T]
        CFI_CALL(Ledwards25519_decode_nsqr_p25519)

        lea     rdi, [rsp+V]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+V]
        CFI_CALL(Ledwards25519_decode_mul_p25519)

        lea     rdi, [rsp+S]
        mov     rsi, 25
        lea     rdx, [rsp+V]
        CFI_CALL(Ledwards25519_decode_nsqr_p25519)

        lea     rdi, [rsp+T]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+V]
        CFI_CALL(Ledwards25519_decode_mul_p25519)

        lea     rdi, [rsp+S]
        mov     rsi, 50
        lea     rdx, [rsp+T]
        CFI_CALL(Ledwards25519_decode_nsqr_p25519)

        lea     rdi, [rsp+T]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+T]
        CFI_CALL(Ledwards25519_decode_mul_p25519)

        lea     rdi, [rsp+S]
        mov     rsi, 25
        lea     rdx, [rsp+T]
        CFI_CALL(Ledwards25519_decode_nsqr_p25519)

        lea     rdi, [rsp+V]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+V]
        CFI_CALL(Ledwards25519_decode_mul_p25519)

        lea     rdi, [rsp+S]
        mov     rsi, 125
        lea     rdx, [rsp+V]
        CFI_CALL(Ledwards25519_decode_nsqr_p25519)

        lea     rdi, [rsp+V]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+V]
        CFI_CALL(Ledwards25519_decode_mul_p25519)

        lea     rdi, [rsp+S]
        mov     rsi, 2
        lea     rdx, [rsp+V]
        CFI_CALL(Ledwards25519_decode_nsqr_p25519)

        lea     rdi, [rsp+S]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+W]
        CFI_CALL(Ledwards25519_decode_mul_p25519)

// Compute v' = s^2 * w to discriminate whether the square root sqrt(u/v)
// exists, in which case we should get 0, 1 or -1.

        lea     rdi, [rsp+V]
        mov     rsi, 1
        lea     rdx, [rsp+S]
        CFI_CALL(Ledwards25519_decode_nsqr_p25519)

        lea     rdi, [rsp+V]
        lea     rsi, [rsp+V]
        lea     rdx, [rsp+W]
        CFI_CALL(Ledwards25519_decode_mul_p25519)

// Get the two candidates for sqrt(u / v), one being s = u * w^{252-3}
// and the other being t = s * j_25519 where j_25519 = sqrt(-1).

        lea     rdi, [rsp+S]
        lea     rsi, [rsp+U]
        lea     rdx, [rsp+S]
        CFI_CALL(Ledwards25519_decode_mul_p25519)
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
        CFI_CALL(Ledwards25519_decode_mul_p25519)

// rax = 0 <=> s^2 * w = 0 or 1

        mov     r8, [rsp+V]
        mov     r9, [rsp+V+8]
        mov     r10, [rsp+V+16]
        mov     r11, [rsp+V+24]
        mov     eax, 1
        not     rax
        and     rax, r8
        or      rax, r9
        or      rax, r10
        or      rax, r11

// r8 = 0 <=> s^2 * w = -1 (mod p_25519, i.e. s^2 * w = 2^255 - 20)

        add     r8, 20
        not     r9
        not     r10
        bts     r11, 63
        add     r11, 1
        or      r8, r9
        or      r10, r11
        or      r8, r10

// If s^2 * w is not 0 or 1 then replace s by t

        test    rax, rax

        mov     r12, [rsp+S]
        mov     rbx, [rsp+T]
        cmovnz  r12, rbx
        mov     r13, [rsp+S+8]
        mov     rbx, [rsp+T+8]
        cmovnz  r13, rbx
        mov     r14, [rsp+S+16]
        mov     rbx, [rsp+T+16]
        cmovnz  r14, rbx
        mov     r15, [rsp+S+24]
        mov     rbx, [rsp+T+24]
        cmovnz  r15, rbx
        mov     [rsp+S], r12
        mov     [rsp+S+8], r13
        mov     [rsp+S+16], r14
        mov     [rsp+S+24], r15

// Check invalidity, occurring if s^2 * w is not in {0,1,-1}

        cmovz   r8, rax
        neg     r8
        sbb     r8, r8
        neg     r8
        or      badun, r8

// Let [r11;r10;r9;r8] = s and [r15;r14;r13;r12] = p_25519 - s

        mov     r8, [rsp+S]
        mov     r12, -19
        sub     r12, r8
        mov     r9, [rsp+S+8]
        mov     r13, -1
        sbb     r13, r9
        mov     r10, [rsp+S+16]
        mov     r14, -1
        sbb     r14, r10
        mov     r11, [rsp+S+24]
        mov     r15, 0x7FFFFFFFFFFFFFFF
        sbb     r15, r11

// Decide whether a flip is apparently indicated, s_0 <=> sgnbit
// Decide also if s = 0 by OR-ing its digits. Now if a flip is indicated:
//  - if s = 0 then mark as invalid
//  - if s <> 0 then indeed flip

        mov     ecx, 1
        and     rcx, r8
        xor     rcx, sgnbit
        mov     rdx, badun
        mov     rsi, rdx
        or      rdx, rcx
        xor     ebp, ebp
        mov     rax, r8
        mov     rbx, r9
        or      rax, r10
        or      rbx, r11
        or      rax, rbx
        cmovz   rcx, rbp
        cmovnz  rdx, rsi

// Actual selection of x as s or -s, copying of y and return of validity

        test    rcx, rcx

        cmovnz  r8, r12
        cmovnz  r9, r13
        cmovnz  r10, r14
        cmovnz  r11, r15

        mov     rdi, res
        mov     [rdi], r8
        mov     [rdi+8], r9
        mov     [rdi+16], r10
        mov     [rdi+24], r11
        mov     rcx, [rsp+Y]
        mov     [rdi+32], rcx
        mov     rcx, [rsp+Y+8]
        mov     [rdi+40], rcx
        mov     rcx, [rsp+Y+16]
        mov     [rdi+48], rcx
        mov     rcx, [rsp+Y+24]
        mov     [rdi+56], rcx

        mov     rax, rdx

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
S2N_BN_SIZE_DIRECTIVE(Ledwards25519_decode_standard)
#else
S2N_BN_SIZE_DIRECTIVE(edwards25519_decode)
#endif

// *************************************************************
// Local z = x * y
// *************************************************************

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Ledwards25519_decode_mul_p25519)

Ledwards25519_decode_mul_p25519:
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

S2N_BN_SIZE_DIRECTIVE(Ledwards25519_decode_mul_p25519)

// *************************************************************
// Local z = 2^n * x
// *************************************************************

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Ledwards25519_decode_nsqr_p25519)

Ledwards25519_decode_nsqr_p25519:
        CFI_START

// Copy input argument into q

        mov     rax, [rdx]
        mov     rbx, [rdx+8]
        mov     rcx, [rdx+16]
        mov     rdx, [rdx+24]
        mov     [rsp+Q8], rax
        mov     [rsp+Q8+8], rbx
        mov     [rsp+Q8+16], rcx
        mov     [rsp+Q8+24], rdx

// Main squaring loop, accumulating in u consistently  and
// only ensuring the intermediates are < 2 * p_25519 = 2^256 - 38

Ledwards25519_decode_loop:
        mov    rdx, [rsp+Q8]
        mulx   r15, r8, rdx
        mulx   r10, r9, [rsp+Q8+0x8]
        mulx   r12, r11, [rsp+Q8+0x18]
        mov    rdx, [rsp+Q8+0x10]
        mulx   r14, r13, [rsp+Q8+0x18]
        xor    ebx, ebx
        mulx   rcx, rax, [rsp+Q8]
        adcx   r10, rax
        adox   r11, rcx
        mulx   rcx, rax, [rsp+Q8+0x8]
        adcx   r11, rax
        adox   r12, rcx
        mov    rdx, [rsp+Q8+0x18]
        mulx   rcx, rax, [rsp+Q8+0x8]
        adcx   r12, rax
        adox   r13, rcx
        adcx   r13, rbx
        adox   r14, rbx
        adc    r14, rbx
        xor    ebx, ebx
        adcx   r9, r9
        adox   r9, r15
        mov    rdx, [rsp+Q8+0x8]
        mulx   rdx, rax, rdx
        adcx   r10, r10
        adox   r10, rax
        adcx   r11, r11
        adox   r11, rdx
        mov    rdx, [rsp+Q8+0x10]
        mulx   rdx, rax, rdx
        adcx   r12, r12
        adox   r12, rax
        adcx   r13, r13
        adox   r13, rdx
        mov    rdx, [rsp+Q8+0x18]
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
        mov    [rsp+Q8], r8
        mov    [rsp+Q8+0x8], r9
        mov    [rsp+Q8+0x10], r10
        mov    [rsp+Q8+0x18], r11

// Loop as applicable

        dec     rsi
        jnz     Ledwards25519_decode_loop

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

S2N_BN_SIZE_DIRECTIVE(Ledwards25519_decode_nsqr_p25519)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
