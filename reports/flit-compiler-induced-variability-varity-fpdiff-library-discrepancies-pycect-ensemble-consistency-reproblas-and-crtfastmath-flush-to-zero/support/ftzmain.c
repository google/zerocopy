#include <pthread.h>
#include <stdio.h>
#include <dlfcn.h>
double half(double), scale_up(double);
static unsigned csr(void) { return __builtin_ia32_stmxcsr(); }
static void report(const char *who) {
  volatile double min_normal = 0x1p-1022, sub = 0x1p-1060;
  unsigned m = csr();
  printf("%-28s MXCSR=%#06x FTZ=%d DAZ=%d half(2^-1022)=%a scale_up(2^-1060)=%a\n", who, m,
         !!(m & 0x8000), !!(m & 0x40), half(min_normal), scale_up(sub));
}
static void *thread_main(void *arg) {
  (void)arg;
  report("new thread (inherited)");
  __builtin_ia32_ldmxcsr(csr() & ~0x8040u); /* clear FTZ and DAZ in this thread only */
  report("new thread after clearing");
  return 0;
}
int main(int argc, char **argv) {
  report("main thread at entry");
  if (argc > 1) { /* dlopen a library named on the command line */
    void *h = dlopen(argv[1], RTLD_NOW);
    printf("dlopen(%s) -> %s\n", argv[1], h ? "ok" : dlerror());
    report("main thread after dlopen");
  }
  pthread_t t;
  pthread_create(&t, 0, thread_main, 0);
  pthread_join(t, 0);
  report("main thread after join");
  return 0;
}
