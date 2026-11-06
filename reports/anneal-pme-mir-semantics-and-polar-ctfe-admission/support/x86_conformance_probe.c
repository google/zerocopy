// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Hardware differential probe for x86_64-unknown-linux-gnu against Anneal's
// Trusted/X86Semantics.lean and trusted/rustc-capture/src/lib.rs at commit
// 4f45f0a391a921ced9c9dc773b9a040dbc215d14.

#define _GNU_SOURCE
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static sigjmp_buf jmp_env;
static volatile sig_atomic_t caught_sig = 0;
static volatile sig_atomic_t caught_sicode = 0;

static void fault_handler(int sig, siginfo_t *info, void *ucontext) {
  (void)ucontext;
  caught_sig = sig;
  caught_sicode = info ? info->si_code : 0;
  siglongjmp(jmp_env, 1);
}

static void install_handlers(void) {
  struct sigaction sa;
  memset(&sa, 0, sizeof(sa));
  sa.sa_sigaction = fault_handler;
  sa.sa_flags = SA_SIGINFO | SA_NODEFER;
  sigemptyset(&sa.sa_mask);
  if (sigaction(SIGFPE, &sa, NULL) != 0 || sigaction(SIGILL, &sa, NULL) != 0) {
    perror("sigaction");
    exit(1);
  }
}

// RFLAGS bit masks
#define RFLAGS_CF (1ULL << 0)
#define RFLAGS_PF (1ULL << 2)
#define RFLAGS_AF (1ULL << 4)
#define RFLAGS_ZF (1ULL << 6)
#define RFLAGS_SF (1ULL << 7)
#define RFLAGS_OF (1ULL << 11)
#define RFLAGS_ARITH_MASK \
  (RFLAGS_CF | RFLAGS_PF | RFLAGS_AF | RFLAGS_ZF | RFLAGS_SF | RFLAGS_OF)

static void test_subregister_writes(void) {
  uint64_t out_w8 = 0, out_w16 = 0, out_w32 = 0;
  uint64_t seed = 0x1122334455667788ULL;

  __asm__ volatile(
      "movq %[seed], %%rax\n\t"
      "movb $0xaa, %%al\n\t"
      "movq %%rax, %[out_w8]\n\t"
      "movq %[seed], %%rax\n\t"
      "movw $0xbbcc, %%ax\n\t"
      "movq %%rax, %[out_w16]\n\t"
      "movq %[seed], %%rax\n\t"
      "movl $0xddeeff00, %%eax\n\t"
      "movq %%rax, %[out_w32]\n\t"
      : [out_w8] "=r"(out_w8), [out_w16] "=r"(out_w16), [out_w32] "=r"(out_w32)
      : [seed] "r"(seed)
      : "rax", "cc");

  printf("[TEST 1: SUB-REGISTER WRITES]\n");
  printf("  seed     = 0x%016llx\n", (unsigned long long)seed);
  printf("  movb al  = 0x%016llx (expected 0x11223344556677aa: low 8 merged)\n",
         (unsigned long long)out_w8);
  printf("  movw ax  = 0x%016llx (expected 0x112233445566bbcc: low 16 merged)\n",
         (unsigned long long)out_w16);
  printf("  movl eax = 0x%016llx (expected 0x00000000ddeeff00: upper 32 zeroed)\n",
         (unsigned long long)out_w32);
}

static void test_modular_alu_vs_lean_nat(void) {
  uint64_t add_res = 0, add_flags = 0;
  uint64_t sub_res = 0, sub_flags = 0;
  uint64_t mul_res = 0, mul_flags = 0;

  __asm__ volatile(
      "movq $0xffffffffffffffff, %%rax\n\t"
      "movq $1, %%rcx\n\t"
      "addq %%rcx, %%rax\n\t"
      "pushfq\n\t"
      "popq %[add_flags]\n\t"
      "movq %%rax, %[add_res]\n\t"
      : [add_res] "=r"(add_res), [add_flags] "=r"(add_flags)
      :
      : "rax", "rcx", "cc");

  __asm__ volatile(
      "movq $0, %%rax\n\t"
      "movq $1, %%rcx\n\t"
      "subq %%rcx, %%rax\n\t"
      "pushfq\n\t"
      "popq %[sub_flags]\n\t"
      "movq %%rax, %[sub_res]\n\t"
      : [sub_res] "=r"(sub_res), [sub_flags] "=r"(sub_flags)
      :
      : "rax", "rcx", "cc");

  __asm__ volatile(
      "movabsq $0x0000000100000000, %%rax\n\t"
      "movabsq $0x0000000100000000, %%rcx\n\t"
      "imulq %%rcx, %%rax\n\t"
      "pushfq\n\t"
      "popq %[mul_flags]\n\t"
      "movq %%rax, %[mul_res]\n\t"
      : [mul_res] "=r"(mul_res), [mul_flags] "=r"(mul_flags)
      :
      : "rax", "rcx", "cc");

  printf("[TEST 2: 64-BIT MODULAR ALU VS X86Semantics.lean UNBOUNDED Nat]\n");
  printf("  addq(UINT64_MAX, 1) -> hw=0x%016llx CF=%d ZF=%d OF=%d | X86Semantics.lean=2^64 (0x10000000000000000)\n",
         (unsigned long long)add_res, !!(add_flags & RFLAGS_CF),
         !!(add_flags & RFLAGS_ZF), !!(add_flags & RFLAGS_OF));
  printf("  subq(0, 1)          -> hw=0x%016llx CF=%d ZF=%d SF=%d | X86Semantics.lean=0 (Nat truncating sub!)\n",
         (unsigned long long)sub_res, !!(sub_flags & RFLAGS_CF),
         !!(sub_flags & RFLAGS_ZF), !!(sub_flags & RFLAGS_SF));
  printf("  imulq(2^32, 2^32)   -> hw=0x%016llx CF=%d OF=%d      | X86Semantics.lean=2^64 (unbounded Nat mul!)\n",
         (unsigned long long)mul_res, !!(mul_flags & RFLAGS_CF),
         !!(mul_flags & RFLAGS_OF));
}

static void test_shifts_and_flags(void) {
  uint64_t shl64_res = 0, shr64_res = 0, shl32_res = 0, sar_neg_res = 0;
  uint64_t flags_before_0 = 0, flags_after_0 = 0;
  uint64_t shl1_flags = 0;

  // Shift by 64 on 64-bit operand masks count with 0x3f -> shift by 0
  __asm__ volatile(
      "movq $1, %%rax\n\t"
      "movb $64, %%cl\n\t"
      "shlq %%cl, %%rax\n\t"
      "movq %%rax, %[shl64_res]\n\t"
      "movq $1, %%rax\n\t"
      "movb $64, %%cl\n\t"
      "shrq %%cl, %%rax\n\t"
      "movq %%rax, %[shr64_res]\n\t"
      "movl $1, %%eax\n\t"
      "movb $32, %%cl\n\t"
      "shll %%cl, %%eax\n\t"
      "movq %%rax, %[shl32_res]\n\t"
      "movabsq $0x8000000000000000, %%rax\n\t"
      "movb $63, %%cl\n\t"
      "sarq %%cl, %%rax\n\t"
      "movq %%rax, %[sar_neg_res]\n\t"
      : [shl64_res] "=r"(shl64_res), [shr64_res] "=r"(shr64_res),
        [shl32_res] "=r"(shl32_res), [sar_neg_res] "=r"(sar_neg_res)
      :
      : "rax", "rcx", "cc");

  // Shift by 0 preserves all arithmetic flags
  __asm__ volatile(
      "movq $0xffffffffffffffff, %%rax\n\t"
      "addq $1, %%rax\n\t"  // sets CF=1, ZF=1
      "pushfq\n\t"
      "popq %[before]\n\t"
      "movq $0x12345678, %%rax\n\t"
      "movb $0, %%cl\n\t"
      "shlq %%cl, %%rax\n\t"
      "pushfq\n\t"
      "popq %[after]\n\t"
      : [before] "=r"(flags_before_0), [after] "=r"(flags_after_0)
      :
      : "rax", "rcx", "cc");

  // 1-bit shift sets OF = MSB(result) ^ CF
  __asm__ volatile(
      "movabsq $0x4000000000000000, %%rax\n\t"
      "shlq $1, %%rax\n\t"  // result=0x8000000000000000 (MSB=1), CF=0 => OF=1
      "pushfq\n\t"
      "popq %[shl1_flags]\n\t"
      : [shl1_flags] "=r"(shl1_flags)
      :
      : "rax", "cc");

  printf("[TEST 3: SHIFT MASKING & FLAG SEMANTICS]\n");
  printf("  shlq(1, 64)  -> hw=0x%016llx (cl & 0x3f = 0) | X86Semantics.lean=2^64 (1 <<< 64)\n",
         (unsigned long long)shl64_res);
  printf("  shrq(1, 64)  -> hw=0x%016llx (cl & 0x3f = 0) | X86Semantics.lean=0 (1 >>> 64)\n",
         (unsigned long long)shr64_res);
  printf("  shll(1, 32)  -> hw=0x%016llx (cl & 0x1f = 0)\n",
         (unsigned long long)shl32_res);
  printf("  sarq(INT64_MIN, 63) -> hw=0x%016llx (sign-extended)\n",
         (unsigned long long)sar_neg_res);
  printf("  shlq(x, 0) arith flags unchanged: %s (before=0x%03llx, after=0x%03llx)\n",
         ((flags_before_0 & RFLAGS_ARITH_MASK) ==
          (flags_after_0 & RFLAGS_ARITH_MASK))
             ? "YES"
             : "NO",
         (unsigned long long)(flags_before_0 & RFLAGS_ARITH_MASK),
         (unsigned long long)(flags_after_0 & RFLAGS_ARITH_MASK));
  printf("  shlq(0x4000..00, 1) -> CF=%d OF=%d SF=%d (OF = MSB(res) ^ CF = 1)\n",
         !!(shl1_flags & RFLAGS_CF), !!(shl1_flags & RFLAGS_OF),
         !!(shl1_flags & RFLAGS_SF));
}

static void test_inc_dec_mov_lea_flags(void) {
  uint64_t inc_cf0_flags = 0, inc_cf1_flags = 0;
  uint64_t dec_cf0_flags = 0, dec_cf1_flags = 0;
  uint64_t mov_lea_before = 0, mov_lea_after = 0;

  __asm__ volatile(
      "clc\n\t"
      "movq $0xffffffffffffffff, %%rax\n\t"
      "incq %%rax\n\t"
      "pushfq\n\t"
      "popq %[inc_cf0]\n\t"
      "stc\n\t"
      "movq $0xffffffffffffffff, %%rax\n\t"
      "incq %%rax\n\t"
      "pushfq\n\t"
      "popq %[inc_cf1]\n\t"
      "clc\n\t"
      "movq $0, %%rax\n\t"
      "decq %%rax\n\t"
      "pushfq\n\t"
      "popq %[dec_cf0]\n\t"
      "stc\n\t"
      "movq $0, %%rax\n\t"
      "decq %%rax\n\t"
      "pushfq\n\t"
      "popq %[dec_cf1]\n\t"
      : [inc_cf0] "=r"(inc_cf0_flags), [inc_cf1] "=r"(inc_cf1_flags),
        [dec_cf0] "=r"(dec_cf0_flags), [dec_cf1] "=r"(dec_cf1_flags)
      :
      : "rax", "cc");

  __asm__ volatile(
      "stc\n\t"
      "movq $0x7fffffffffffffff, %%rax\n\t"
      "addq $1, %%rax\n\t"  // OF=1, SF=1, ZF=0, CF=0
      "stc\n\t"             // force CF=1 as well
      "pushfq\n\t"
      "popq %[before]\n\t"
      "movq $0, %%rcx\n\t"
      "leaq 16(%%rax,%%rcx,8), %%rdx\n\t"
      "pushfq\n\t"
      "popq %[after]\n\t"
      : [before] "=r"(mov_lea_before), [after] "=r"(mov_lea_after)
      :
      : "rax", "rcx", "rdx", "cc");

  printf("[TEST 4: INC/DEC CF PRESERVATION & MOV/LEA FLAG INVARIANCE]\n");
  printf("  incq(UINT64_MAX): CF_in=0 -> CF_out=%d ZF=%d | CF_in=1 -> CF_out=%d ZF=%d\n",
         !!(inc_cf0_flags & RFLAGS_CF), !!(inc_cf0_flags & RFLAGS_ZF),
         !!(inc_cf1_flags & RFLAGS_CF), !!(inc_cf1_flags & RFLAGS_ZF));
  printf("  decq(0):          CF_in=0 -> CF_out=%d SF=%d | CF_in=1 -> CF_out=%d SF=%d\n",
         !!(dec_cf0_flags & RFLAGS_CF), !!(dec_cf0_flags & RFLAGS_SF),
         !!(dec_cf1_flags & RFLAGS_CF), !!(dec_cf1_flags & RFLAGS_SF));
  printf("  movq + leaq arith flags unchanged: %s\n",
         ((mov_lea_before & RFLAGS_ARITH_MASK) ==
          (mov_lea_after & RFLAGS_ARITH_MASK))
             ? "YES"
             : "NO");
}

static void test_div_idiv_ud2_traps(void) {
  printf("[TEST 5: HARDWARE #DE (DIV/IDIV) AND #UD (UD2) TRAPS]\n");

  // 5a: divq by 0
  caught_sig = 0;
  caught_sicode = 0;
  if (sigsetjmp(jmp_env, 1) == 0) {
    __asm__ volatile(
        "xorq %%rdx, %%rdx\n\t"
        "movq $42, %%rax\n\t"
        "xorq %%rcx, %%rcx\n\t"
        "divq %%rcx\n\t"
        :
        :
        : "rax", "rdx", "rcx", "cc");
    printf("  divq by 0: DID NOT TRAP (unexpected)\n");
  } else {
    printf("  divq by 0: trapped with signal=%d (SIGFPE=%d) si_code=%d\n",
           caught_sig, SIGFPE, caught_sicode);
  }

  // 5b: idivq INT64_MIN / -1 signed overflow
  caught_sig = 0;
  caught_sicode = 0;
  if (sigsetjmp(jmp_env, 1) == 0) {
    __asm__ volatile(
        "movabsq $0x8000000000000000, %%rax\n\t"
        "cqto\n\t"
        "movq $-1, %%rcx\n\t"
        "idivq %%rcx\n\t"
        :
        :
        : "rax", "rdx", "rcx", "cc");
    printf("  idivq(INT64_MIN, -1): DID NOT TRAP (unexpected)\n");
  } else {
    printf("  idivq(INT64_MIN, -1): trapped with signal=%d (SIGFPE=%d) si_code=%d\n",
           caught_sig, SIGFPE, caught_sicode);
  }

  // 5c: divq 128-bit dividend quotient overflow (rdx=1, rax=0, rcx=1 -> q=2^64)
  caught_sig = 0;
  caught_sicode = 0;
  if (sigsetjmp(jmp_env, 1) == 0) {
    __asm__ volatile(
        "movq $1, %%rdx\n\t"
        "xorq %%rax, %%rax\n\t"
        "movq $1, %%rcx\n\t"
        "divq %%rcx\n\t"
        :
        :
        : "rax", "rdx", "rcx", "cc");
    printf("  divq(2^64, 1) overflow: DID NOT TRAP (unexpected)\n");
  } else {
    printf("  divq(2^64, 1) overflow: trapped with signal=%d (SIGFPE=%d) si_code=%d\n",
           caught_sig, SIGFPE, caught_sicode);
  }

  // 5d: ud2 (emitted for both Panic and Unreachable in render_x86_assembly)
  caught_sig = 0;
  caught_sicode = 0;
  if (sigsetjmp(jmp_env, 1) == 0) {
    __asm__ volatile("ud2\n\t");
    printf("  ud2: DID NOT TRAP (unexpected)\n");
  } else {
    printf("  ud2: trapped with signal=%d (SIGILL=%d) si_code=%d\n",
           caught_sig, SIGILL, caught_sicode);
  }
}

static void test_codegen_transmute_copy_truncation(void) {
  // Demonstrates trusted/rustc-capture/src/lib.rs:1782-1797 bug where
  // CallTransmuteCopy emits a single 8-byte `mov rax, QWORD PTR [rsi];
  // mov QWORD PTR [rbp - dst_off], rax` instead of copying sizeof(Src) bytes.
  uint64_t src[2] = {0x1111222233334444ULL, 0x5555666677778888ULL};
  uint64_t dst_codegen[2] = {0xdeadbeefdeadbeefULL, 0xdeadbeefdeadbeefULL};
  uint64_t dst_repmovsb[2] = {0xdeadbeefdeadbeefULL, 0xdeadbeefdeadbeefULL};

  // What render_x86_assembly emits for CallTransmuteCopy:
  __asm__ volatile(
      "movq (%[src]), %%rax\n\t"
      "movq %%rax, (%[dst])\n\t"
      :
      : [src] "r"(src), [dst] "r"(dst_codegen)
      : "rax", "memory");

  // What X86Semantics.lean (repMovsbJmp) claims happens for 16-byte type:
  void *rdi = dst_repmovsb;
  const void *rsi = src;
  size_t rcx = 16;
  __asm__ volatile("rep movsb\n\t"
                   : "+D"(rdi), "+S"(rsi), "+c"(rcx)
                   :
                   : "memory");

  printf("[TEST 6: CallTransmuteCopy 8-BYTE MOV VS REP MOVSB (16-BYTE TYPE)]\n");
  printf("  render_x86_assembly 8B mov: lo=0x%016llx hi=0x%016llx (hi word uncopied!)\n",
         (unsigned long long)dst_codegen[0],
         (unsigned long long)dst_codegen[1]);
  printf("  X86Semantics rep movsb 16B: lo=0x%016llx hi=0x%016llx (both words copied)\n",
         (unsigned long long)dst_repmovsb[0],
         (unsigned long long)dst_repmovsb[1]);
}

int main(void) {
  install_handlers();
  test_subregister_writes();
  test_modular_alu_vs_lean_nat();
  test_shifts_and_flags();
  test_inc_dec_mov_lea_flags();
  test_div_idiv_ud2_traps();
  test_codegen_transmute_copy_truncation();
  return 0;
}
