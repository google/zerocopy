/* Probe: x86-64 MXCSR / x87 control word across thread creation, signal
   delivery, and dlopen() on Linux. Build: cc -O1 -pthread fpenv_boundaries.c -ldl */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <xmmintrin.h>

static unsigned get_mxcsr(void) { return _mm_getcsr(); }
static void set_mxcsr(unsigned v) { _mm_setcsr(v); }
static unsigned short get_x87cw(void) { unsigned short cw; __asm__ volatile("fnstcw %0" : "=m"(cw)); return cw; }
static void set_x87cw(unsigned short cw) { __asm__ volatile("fldcw %0" :: "m"(cw)); }

static volatile unsigned in_handler_mxcsr, in_handler_cw;
static void handler(int sig) {
  (void)sig;
  in_handler_mxcsr = get_mxcsr();
  in_handler_cw = get_x87cw();
  /* Handler changes its own MXCSR; does it leak back to the interrupted code? */
  set_mxcsr(0x1f80 | 0x6000); /* round toward zero */
}
static void *thread_fn(void *arg) {
  unsigned *out = arg;
  out[0] = get_mxcsr();
  out[1] = get_x87cw();
  return NULL;
}
int main(int argc, char **argv) {
  printf("startup:        MXCSR=0x%04x x87CW=0x%04x\n", get_mxcsr(), get_x87cw());
  /* Non-default control state: FTZ(15) | DAZ(6) | RC=down (13) | unmask nothing; set a sticky flag (PE bit 5) too */
  unsigned custom = 0x1f80 | 0x8000 | 0x0040 | 0x2000 | 0x0020;
  set_mxcsr(custom);
  set_x87cw(0x027f | 0x0400); /* 53-bit precision, round down */
  printf("parent set:     MXCSR=0x%04x x87CW=0x%04x\n", get_mxcsr(), get_x87cw());
  unsigned t[2];
  pthread_t th; pthread_create(&th, NULL, thread_fn, t); pthread_join(th, NULL);
  printf("new pthread:    MXCSR=0x%04x x87CW=0x%04x\n", t[0], t[1]);
  signal(SIGUSR1, handler);
  raise(SIGUSR1);
  printf("in handler:     MXCSR=0x%04x x87CW=0x%04x\n", in_handler_mxcsr, in_handler_cw);
  printf("after sigreturn:MXCSR=0x%04x x87CW=0x%04x\n", get_mxcsr(), get_x87cw());
  set_mxcsr(0x1f80); set_x87cw(0x037f);
  for (int i = 1; i < argc; i++) {
    unsigned before = get_mxcsr();
    void *h = dlopen(argv[i], RTLD_NOW);
    const char *base = strrchr(argv[i], '/') ? strrchr(argv[i], '/') + 1 : argv[i];
    printf("dlopen %-34s %s: MXCSR before=0x%04x after=0x%04x\n", base, h ? "ok" : dlerror(), before, get_mxcsr());
    set_mxcsr(0x1f80);
  }
  return 0;
}
