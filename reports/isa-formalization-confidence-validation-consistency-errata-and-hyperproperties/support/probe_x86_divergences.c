/* Reproducible x86-64 hardware vs. QEMU differential probe.
 * Build: gcc -O2 -mavx512f probe_x86_divergences.c -o /tmp/probe_x86_divergences
 * Run host: /tmp/probe_x86_divergences
 * Run QEMU: qemu-x86_64 -cpu max /tmp/probe_x86_divergences
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <signal.h>
#include <setjmp.h>

static sigjmp_buf g_env;
static void on_sigill(int sig) { siglongjmp(g_env, sig); }

static uint32_t f2u(float x) { uint32_t u; memcpy(&u, &x, 4); return u; }

int main(void) {
    uint32_t dst_bsf = 0xdeadbeefu, dst_bsr = 0xdeadbeefu, zero = 0u;
    __asm__ volatile("bsfl %1, %0" : "+r"(dst_bsf) : "r"(zero) : "cc");
    __asm__ volatile("bsrl %1, %0" : "+r"(dst_bsr) : "r"(zero) : "cc");
    printf("bsf(0xdeadbeef, 0) = 0x%08x\n", dst_bsf);
    printf("bsr(0xdeadbeef, 0) = 0x%08x\n", dst_bsr);

    float in = 3.0f, out_rcpss = 0.0f;
    __asm__ volatile("rcpss %1, %0" : "=x"(out_rcpss) : "x"(in));
    printf("rcpss(3.0f)        = 0x%08x\n", f2u(out_rcpss));

    signal(SIGILL, on_sigill);
    if (sigsetjmp(g_env, 1) == 0) {
        float out_vrcp14 = 0.0f;
        __asm__ volatile("vrcp14ss %1, %1, %0" : "=x"(out_vrcp14) : "x"(in));
        printf("vrcp14ss(3.0f)     = 0x%08x\n", f2u(out_vrcp14));
    } else {
        printf("vrcp14ss(3.0f)     = SIGILL (signal %d)\n", SIGILL);
    }
    return 0;
}
