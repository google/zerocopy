// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Extended Montgomery reduce in 8-digit blocks, results in input-output buffer
// Inputs z[2*k], m[k], w; outputs function return (extra result bit) and z[2*k]
//
//    extern uint64_t bignum_emontredc_8n(uint64_t k, uint64_t *z, const uint64_t *m,
//                                        uint64_t w);
//
// Functionally equivalent to bignum_emontredc (see that file for more detail).
// But in general assumes that the input k is a multiple of 8.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = m, RCX = w, returns RAX
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = m, R9 = w, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_emontredc_8n)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_emontredc_8n)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_emontredc_8n)
        .text
        .balign 32

// Original input parameters are here

#define z rsi
#define w rcx

// This is copied in early once we stash away k

#define m rdi

// A variable z pointer

#define zz rbp

// Stack-based variables

#define carry QWORD PTR [rsp]
#define innercount QWORD PTR [rsp+8]
#define outercount QWORD PTR [rsp+16]
#define k8m1 QWORD PTR [rsp+24]

// -----------------------------------------------------------------------------
// Standard macros as used in pure multiplier arrays
// -----------------------------------------------------------------------------

// mulpadd i, j adds z[i] * rdx (now assumed = m[j]) into the window at i+j

.macro mulpadd arg1,arg2
        mulx    rbx, rax, [z+8*\arg1]
.if ((\arg1 + \arg2) % 8 == 0)
        adcx    r8, rax
        adox    r9, rbx
.elseif ((\arg1 + \arg2) % 8 == 1)
        adcx    r9, rax
        adox    r10, rbx
.elseif ((\arg1 + \arg2) % 8 == 2)
        adcx    r10, rax
        adox    r11, rbx
.elseif ((\arg1 + \arg2) % 8 == 3)
        adcx    r11, rax
        adox    r12, rbx
.elseif ((\arg1 + \arg2) % 8 == 4)
        adcx    r12, rax
        adox    r13, rbx
.elseif ((\arg1 + \arg2) % 8 == 5)
        adcx    r13, rax
        adox    r14, rbx
.elseif ((\arg1 + \arg2) % 8 == 6)
        adcx    r14, rax
        adox    r15, rbx
.elseif ((\arg1 + \arg2) % 8 == 7)
        adcx    r15, rax
        adox    r8, rbx
.endif

.endm

// addrow i adds z[i] + zz[0..7] * m[j] into the window

.macro addrow arg1
        mov     rdx, [m+8*\arg1]
        xor     eax, eax         // Get a known flag state

.if (\arg1 % 8 == 0)
        adox    r8, [zz+8*\arg1]
.elseif (\arg1 % 8 == 1)
        adox    r9, [zz+8*\arg1]
.elseif (\arg1 % 8 == 2)
        adox    r10, [zz+8*\arg1]
.elseif (\arg1 % 8 == 3)
        adox    r11, [zz+8*\arg1]
.elseif (\arg1 % 8 == 4)
        adox    r12, [zz+8*\arg1]
.elseif (\arg1 % 8 == 5)
        adox    r13, [zz+8*\arg1]
.elseif (\arg1 % 8 == 6)
        adox    r14, [zz+8*\arg1]
.elseif (\arg1 % 8 == 7)
        adox    r15, [zz+8*\arg1]
.endif

        mulpadd 0, \arg1

.if (\arg1 % 8 == 0)
        mov     [zz+8*\arg1], r8
        mov     r8d, 0
.elseif (\arg1 % 8 == 1)
        mov     [zz+8*\arg1], r9
        mov     r9d, 0
.elseif (\arg1 % 8 == 2)
        mov     [zz+8*\arg1], r10
        mov     r10d, 0
.elseif (\arg1 % 8 == 3)
        mov     [zz+8*\arg1], r11
        mov     r11d, 0
.elseif (\arg1 % 8 == 4)
        mov     [zz+8*\arg1], r12
        mov     r12d, 0
.elseif (\arg1 % 8 == 5)
        mov     [zz+8*\arg1], r13
        mov     r13d, 0
.elseif (\arg1 % 8 == 6)
        mov     [zz+8*\arg1], r14
        mov     r14d, 0
.elseif (\arg1 % 8 == 7)
        mov     [zz+8*\arg1], r15
        mov     r15d, 0
.endif

        mulpadd 1, \arg1
        mulpadd 2, \arg1
        mulpadd 3, \arg1
        mulpadd 4, \arg1
        mulpadd 5, \arg1
        mulpadd 6, \arg1
        mulpadd 7, \arg1

.if (\arg1 % 8 == 0)
        adc     r8, 0
.elseif (\arg1 % 8 == 1)
        adc     r9, 0
.elseif (\arg1 % 8 == 2)
        adc     r10, 0
.elseif (\arg1 % 8 == 3)
        adc     r11, 0
.elseif (\arg1 % 8 == 4)
        adc     r12, 0
.elseif (\arg1 % 8 == 5)
        adc     r13, 0
.elseif (\arg1 % 8 == 6)
        adc     r14, 0
.elseif (\arg1 % 8 == 7)
        adc     r15, 0
.endif


.endm

// -----------------------------------------------------------------------------
// Anti-matter versions with z and m switched, and also not writing back the z
// words, but the inverses instead, *and* also adding in the z[0..7] at the
// beginning. The aim is to use this in Montgomery where we discover z[j]
// entries as we go along.
// -----------------------------------------------------------------------------

.macro mulpadda arg1,arg2
        mulx    rbx, rax, [m+8*\arg1]
.if ((\arg1 + \arg2) % 8 == 0)
        adcx    r8, rax
        adox    r9, rbx
.elseif ((\arg1 + \arg2) % 8 == 1)
        adcx    r9, rax
        adox    r10, rbx
.elseif ((\arg1 + \arg2) % 8 == 2)
        adcx    r10, rax
        adox    r11, rbx
.elseif ((\arg1 + \arg2) % 8 == 3)
        adcx    r11, rax
        adox    r12, rbx
.elseif ((\arg1 + \arg2) % 8 == 4)
        adcx    r12, rax
        adox    r13, rbx
.elseif ((\arg1 + \arg2) % 8 == 5)
        adcx    r13, rax
        adox    r14, rbx
.elseif ((\arg1 + \arg2) % 8 == 6)
        adcx    r14, rax
        adox    r15, rbx
.elseif ((\arg1 + \arg2) % 8 == 7)
        adcx    r15, rax
        adox    r8, rbx
.endif

.endm

.macro adurowa arg1
        mov     rdx, w          // Get the word-level modular inverse
        xor     eax, eax        // Get a known flag state
.if (\arg1 % 8 == 0)
        mulx    rax, rdx, r8
.elseif (\arg1 % 8 == 1)
        mulx    rax, rdx, r9
.elseif (\arg1 % 8 == 2)
        mulx    rax, rdx, r10
.elseif (\arg1 % 8 == 3)
        mulx    rax, rdx, r11
.elseif (\arg1 % 8 == 4)
        mulx    rax, rdx, r12
.elseif (\arg1 % 8 == 5)
        mulx    rax, rdx, r13
.elseif (\arg1 % 8 == 6)
        mulx    rax, rdx, r14
.elseif (\arg1 % 8 == 7)
        mulx    rax, rdx, r15
.endif

        mov     [z+8*\arg1], rdx   // Store multiplier word

        mulpadda 0, \arg1

        // Note that the bottom reg of the window is zero by construction
        // So it's safe just to use "mulpadda 7" here

        mulpadda 1, \arg1
        mulpadda 2, \arg1
        mulpadda 3, \arg1
        mulpadda 4, \arg1
        mulpadda 5, \arg1
        mulpadda 6, \arg1
        mulpadda 7, \arg1          // window lowest = 0 beforehand by construction

.if (\arg1 % 8 == 0)
        adc     r8, 0
.elseif (\arg1 % 8 == 1)
        adc     r9, 0
.elseif (\arg1 % 8 == 2)
        adc     r10, 0
.elseif (\arg1 % 8 == 3)
        adc     r11, 0
.elseif (\arg1 % 8 == 4)
        adc     r12, 0
.elseif (\arg1 % 8 == 5)
        adc     r13, 0
.elseif (\arg1 % 8 == 6)
        adc     r14, 0
.elseif (\arg1 % 8 == 7)
        adc     r15, 0
.endif

.endm

.macro adurowza
        mov     rdx, w          // Get the word-level modular inverse
        xor     eax, eax        // Get a known flag state

        mov     r8, [z]         // r8 = zeroth word
        mulx    rax, rdx, r8    // Compute multiplier word
        mov     [z], rdx        // Store multiplier word
        mov     r9, [z+8]

        mulpadda 0, 0
        mov     r10, [z+16]
        mulpadda 1, 0
        mov     r11, [z+24]
        mulpadda 2, 0
        mov     r12, [z+32]
        mulpadda 3, 0
        mov     r13, [z+40]
        mulpadda 4, 0
        mov     r14, [z+48]
        mulpadda 5, 0
        mov     r15, [z+56]
        mulpadda 6, 0
        mulpadda 7, 0           // r8 = 0 beforehand by construction
        adc     r8, 0
.endm

// -----------------------------------------------------------------------------
// Hybrid top, doing an 8 block specially then multiple additional 8 blocks
// -----------------------------------------------------------------------------

// Multiply-add: z := z + x[i...i+7] * m

.macro addrows

        adurowza
        adurowa 1
        adurowa 2
        adurowa 3
        adurowa 4
        adurowa 5
        adurowa 6
        adurowa 7

        mov     zz, z

        mov     rax, k8m1
        test    rax, rax
        jz      Lbignum_emontredc_8n_innerend
        mov     innercount, rax
Lbignum_emontredc_8n_innerloop:
        add     zz, 64
        add     m, 64
        addrow 0
        addrow 1
        addrow 2
        addrow 3
        addrow 4
        addrow 5
        addrow 6
        addrow 7
        sub     innercount, 64
        jnz     Lbignum_emontredc_8n_innerloop

        mov     rax, k8m1
Lbignum_emontredc_8n_innerend:
        sub     m, rax

        mov     rbx, carry
        neg     rbx
        adc     [z+rax+64], r8
        adc     [z+rax+72], r9
        adc     [z+rax+80], r10
        adc     [z+rax+88], r11
        adc     [z+rax+96], r12
        adc     [z+rax+104], r13
        adc     [z+rax+112], r14
        adc     [z+rax+120], r15
        mov     eax, 0
        adc     rax, 0
        mov     carry, rax
.endm

// -----------------------------------------------------------------------------
// Main code.
// -----------------------------------------------------------------------------

S2N_BN_SYMBOL(bignum_emontredc_8n):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
#endif

// Save more registers to play with

        CFI_PUSH(rbp)
        CFI_PUSH(rbx)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

// Pre-initialize the return value to 0 just in case of early exit below

        xor     eax, eax

// Divide the input k by 8, and push k8m1 = (k/8 - 1)<<6 which is used as
// the scaled inner loop counter / pointer adjustment repeatedly. Also push
// k/8 itself which is here initializing the outer loop count.

        shr     rdi, 3
        jz      Lbignum_emontredc_8n_end

        lea     rbx, [rdi-1]
        shl     rbx, 6
        CFI_PUSH(rbx)
        CFI_PUSH(rdi)

// Make space for two more variables, and set between-stages carry to 0

        CFI_DEC_RSP(16)
        mov     carry, 0

// Copy m into its main home

        mov     m, rdx

// Now just systematically add in the rows

Lbignum_emontredc_8n_outerloop:
        addrows
        add     z, 64
        sub     outercount, 1
        jnz     Lbignum_emontredc_8n_outerloop

// Pop the carry-out "p", which was stored at [rsp], put in rax for return

        CFI_POP(rax)

// Adjust the stack

        CFI_INC_RSP(24)

// Reset of epilog

Lbignum_emontredc_8n_end:

        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbx)
        CFI_POP(rbp)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_emontredc_8n)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
