/* Probe: the rounding mode is per-thread state; worker threads created before a
 * fesetround() call keep their own mode.
 *
 * glibc/POSIX: a thread created with pthread_create inherits the creating thread's
 * floating-point environment at creation time; later fesetround calls affect only the
 * calling thread. A library that dispatches work to a pre-created pool (as threaded
 * BLAS implementations do) therefore does not see a caller's directed rounding mode
 * unless it propagates it explicitly.
 *
 * Build/run: gcc -O2 -frounding-math -pthread round_threads.c -lm -o round_threads && ./round_threads
 */
#include <fenv.h>
#include <pthread.h>
#include <stdio.h>

static volatile double one = 1.0, tiny = 0x1p-60;   /* 1 + 2^-60 is not representable */
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t cv = PTHREAD_COND_INITIALIZER;
static int go = 0;
static double pool_result;

static void *pool_worker(void *arg) {   /* created BEFORE fesetround in main */
    (void)arg;
    pthread_mutex_lock(&mu);
    while (!go) pthread_cond_wait(&cv, &mu);
    pthread_mutex_unlock(&mu);
    pool_result = one + tiny;
    return NULL;
}

static double late_result;
static void *late_worker(void *arg) {   /* created AFTER fesetround in main */
    (void)arg;
    late_result = one + tiny;
    return NULL;
}

int main(void) {
    pthread_t a, b;
    pthread_create(&a, NULL, pool_worker, NULL);
    fesetround(FE_UPWARD);
    double main_result = one + tiny;
    pthread_create(&b, NULL, late_worker, NULL);
    pthread_join(b, NULL);
    pthread_mutex_lock(&mu);
    go = 1;
    pthread_cond_signal(&cv);
    pthread_mutex_unlock(&mu);
    pthread_join(a, NULL);
    fesetround(FE_TONEAREST);
    printf("main thread (FE_UPWARD set):          1 + 2^-60 = %a\n", main_result);
    printf("thread created after fesetround:      1 + 2^-60 = %a\n", late_result);
    printf("pool thread created before fesetround: 1 + 2^-60 = %a\n", pool_result);
    return 0;
}
