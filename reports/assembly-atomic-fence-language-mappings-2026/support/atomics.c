/* Owned header-free C11 compilation witnesses. These functions are never run. */
typedef unsigned long long U;
typedef _Atomic(U) AU;
#define LOAD(name, order) U name(const AU *p) { return __c11_atomic_load(p, order); }
#define STORE(name, order) void name(AU *p, U v) { __c11_atomic_store(p, v, order); }
#define ADD(name, order) U name(AU *p, U v) { return __c11_atomic_fetch_add(p, v, order); }
#define TF(name, order) void name(void) { __c11_atomic_thread_fence(order); }
LOAD(load_relaxed, __ATOMIC_RELAXED)
LOAD(load_acquire, __ATOMIC_ACQUIRE)
LOAD(load_seq_cst, __ATOMIC_SEQ_CST)
STORE(store_relaxed, __ATOMIC_RELAXED)
STORE(store_release, __ATOMIC_RELEASE)
STORE(store_seq_cst, __ATOMIC_SEQ_CST)
ADD(add_relaxed, __ATOMIC_RELAXED)
ADD(add_acq_rel, __ATOMIC_ACQ_REL)
ADD(add_seq_cst, __ATOMIC_SEQ_CST)
_Bool cas_acq_rel(AU *p, U *expected, U desired) {
    return __c11_atomic_compare_exchange_strong(p, expected, desired,
                                               __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE);
}
TF(fence_acquire, __ATOMIC_ACQUIRE)
TF(fence_release, __ATOMIC_RELEASE)
TF(fence_acq_rel, __ATOMIC_ACQ_REL)
TF(fence_seq_cst, __ATOMIC_SEQ_CST)
void signal_seq_cst(void) { __c11_atomic_signal_fence(__ATOMIC_SEQ_CST); }
void compiler_barrier(void) { __asm__ __volatile__("" ::: "memory"); }
void explicit_hw_fence(void) {
#if defined(__aarch64__)
    __asm__ __volatile__("dmb ish" ::: "memory");
#elif defined(__x86_64__)
    __asm__ __volatile__("mfence" ::: "memory");
#else
#error unsupported target
#endif
}
