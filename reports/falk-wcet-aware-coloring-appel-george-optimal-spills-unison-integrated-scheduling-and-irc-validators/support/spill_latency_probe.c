/* spill_latency_probe.c -- dependency-chain latency of register-resident vs
 * memory-resident values on the host x86-64 core.
 *
 * Each variant runs a loop whose body is 8 links of one dependency chain on
 * %rax.  Wall time is read with RDTSCP (constant-rate TSC).  Variants are run
 * round-robin for TRIALS rounds; for each variant the minimum and the 10th
 * percentile of TSC ticks over all rounds are kept (filtering preemption and
 * co-runner interference on a shared host).  Core cycles are recovered by
 * calibrating against variant A (8 x `add %rbx,%rax`, 1-cycle latency on every
 * x86-64 core listed by uops.info):  cycles/link(X) = ticks(X) / ticks(A).
 * Variant G (8 x `imul %rbx,%rax`, 3-cycle latency per uops.info) is a
 * cross-check of that calibration.
 *
 * Build/run:  gcc -O2 -o /tmp/spill_latency_probe spill_latency_probe.c
 *             taskset -c 3 /tmp/spill_latency_probe   (TRIALS defaults to 101)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <x86intrin.h>

#define ITERS 2000000ULL
#ifndef TRIALS
#define TRIALS 101
#endif

static uint64_t buf[64] __attribute__((aligned(64)));

static inline uint64_t tsc(void) { unsigned aux; return __rdtscp(&aux); }

#define REP8(x) x x x x x x x x

static uint64_t run(int v) {
  uint64_t n = ITERS, t0, t1;
  uint64_t a = 1, b = 1;
  uint64_t *p = buf;
  buf[0] = (uint64_t)(uintptr_t)buf; /* self-pointer for the pointer chase */
  if (v == 'D') a = (uint64_t)(uintptr_t)buf;
  t0 = tsc();
  switch (v) {
  case 'A': /* register-resident value: 1-cycle ALU op on the chain */
    __asm__ volatile("1:\n" REP8("add %%rbx, %%rax\n") "dec %%rcx\n jnz 1b\n"
                     : "+a"(a), "+c"(n) : "b"(b) : "cc");
    break;
  case 'G': /* calibration cross-check: 3-cycle IMUL on the chain */
    __asm__ volatile("1:\n" REP8("imul %%rbx, %%rax\n") "dec %%rcx\n jnz 1b\n"
                     : "+a"(a), "+c"(n) : "b"(b) : "cc");
    break;
  case 'B': /* spill + reload through an %rsp-relative slot, then the ALU op */
    __asm__ volatile("sub $128, %%rsp\n"
                     "1:\n" REP8("mov %%rax, 64(%%rsp)\n mov 64(%%rsp), %%rax\n add %%rbx, %%rax\n")
                     "dec %%rcx\n jnz 1b\n add $128, %%rsp\n"
                     : "+a"(a), "+c"(n) : "b"(b) : "cc", "memory");
    break;
  case 'S': /* spill + reload through a non-stack base register (%rdi) */
    __asm__ volatile("1:\n" REP8("mov %%rax, (%%rdi)\n mov (%%rdi), %%rax\n add %%rbx, %%rax\n")
                     "dec %%rcx\n jnz 1b\n"
                     : "+a"(a), "+c"(n) : "b"(b), "D"(p + 8) : "cc", "memory");
    break;
  case 'C': /* memory source operand whose address is off the chain */
    __asm__ volatile("1:\n" REP8("add 64(%%rdi), %%rax\n") "dec %%rcx\n jnz 1b\n"
                     : "+a"(a), "+c"(n) : "D"(p) : "cc", "memory");
    break;
  case 'D': /* pointer chase: L1-hit load-to-use latency */
    __asm__ volatile("1:\n" REP8("mov (%%rax), %%rax\n") "dec %%rcx\n jnz 1b\n"
                     : "+a"(a), "+c"(n) : : "cc", "memory");
    break;
  case 'M': /* value lives only in memory: read-modify-write destination */
    __asm__ volatile("1:\n" REP8("add %%rbx, 128(%%rdi)\n") "dec %%rcx\n jnz 1b\n"
                     : "+c"(n) : "b"(b), "D"(p) : "cc", "memory");
    break;
  case 'L': /* value lives only in memory: explicit load, op, store */
    __asm__ volatile("1:\n" REP8("mov 192(%%rdi), %%rax\n add %%rbx, %%rax\n mov %%rax, 192(%%rdi)\n")
                     "dec %%rcx\n jnz 1b\n"
                     : "+a"(a), "+c"(n) : "b"(b), "D"(p) : "cc", "memory");
    break;
  }
  t1 = tsc();
  if (a == 42 && buf[1] == 42) puts("");
  return t1 - t0;
}

static int cmp(const void *x, const void *y) {
  double a = *(const double *)x, b = *(const double *)y;
  return (a > b) - (a < b);
}

int main(void) {
  const char *vs = "AGBSCDML";
  const char *desc[] = {
      "A reg-reg add (calibration, 1 cycle by definition)",
      "G reg-reg imul (cross-check; uops.info: 3 cycles)",
      "B spill+reload via [rsp+64] then add, per link",
      "S spill+reload via [rdi] then add, per link",
      "C add r64,[mem] with address off the chain, per link",
      "D pointer chase mov rax,[rax], per link",
      "M add [mem],rbx read-modify-write chain, per link",
      "L load/add/store memory-resident value, per link"};
  static double ticks[8][TRIALS];
  for (int t = 0; t < TRIALS; t++)
    for (int i = 0; i < 8; i++)
      ticks[i][t] = (double)run(vs[i]);
  for (int i = 0; i < 8; i++)
    qsort(ticks[i], TRIALS, sizeof(double), cmp);
  int p10 = TRIALS / 10;
  printf("iters=%llu links/iter=8 rounds=%d\n", (unsigned long long)ITERS, TRIALS);
  for (int i = 0; i < 8; i++)
    printf("%-55s cycles/link: min-ratio %.2f  p10-ratio %.2f  median-ratio %.2f\n", desc[i],
           ticks[i][0] / ticks[0][0], ticks[i][p10] / ticks[0][p10],
           ticks[i][TRIALS / 2] / ticks[0][TRIALS / 2]);
  return 0;
}
