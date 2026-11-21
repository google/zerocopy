// Self-contained C++17 specimen for cross-language unwinding, __int128 SysV ABI,
// ELF symbol visibility, and cross-language ThinLTO probes.
// Deliberately avoids C++ standard-library headers so it compiles identically
// under both clang -x c++ -std=c++17 and g++ -std=c++17.

typedef unsigned char u8_t;
typedef unsigned int u32_t;
typedef unsigned long long u64_t;
typedef __int128 i128_t;
typedef unsigned __int128 u128_t;

extern "C" {
long write(int fd, const void* buf, unsigned long count);
}

static void trace_str(const char* s) {
    unsigned long n = 0;
    while (s[n] != '\0') {
        n++;
    }
    (void)write(2, s, n);
}

static void trace_event(const char* tag) {
    trace_str("[TRACE] ");
    trace_str(tag);
    trace_str("\n");
}

struct CppEx {
    int code;
    bool trace_dtor;
    CppEx(int c, bool t) : code(c), trace_dtor(t) {}
    CppEx(const CppEx& other) : code(other.code), trace_dtor(other.trace_dtor) {}
    ~CppEx() {
        if (trace_dtor) {
            trace_event("cpp_ex_dtor");
        }
    }
};

struct CppGuard {
    int* counter;
    const char* tag;
    ~CppGuard() {
        if (counter) {
            (*counter) += 1;
        }
        if (tag) {
            trace_event(tag);
        }
    }
};

extern "C" __attribute__((noinline)) void cpp_throw_code(int code, int trace_dtor) {
    trace_event("cpp_throwing");
    throw CppEx(code, trace_dtor != 0);
}

extern "C" __attribute__((noinline)) int cpp_try_call_rust(
    int (*fn)(int*),
    int* rust_drops
) {
    try {
        return fn(rust_drops);
    } catch (const CppEx& ex) {
        trace_event("cpp_caught_ex");
        return 100 + ex.code;
    } catch (...) {
        trace_event("cpp_caught_unknown");
        return -999;
    }
}

extern "C" __attribute__((noinline)) void cpp_raii_then_rust_panic(
    void (*rust_fn)(),
    int* cpp_dtors
) {
    CppGuard g{cpp_dtors, "cpp_raii_guard_dtor"};
    rust_fn();
}

extern "C" __attribute__((noinline)) void cpp_raii_then_throw(
    int code,
    int* cpp_dtors
) {
    CppGuard g{cpp_dtors, "cpp_inner_guard_dtor"};
    cpp_throw_code(code, 1);
}

extern "C" __attribute__((noinline)) int cpp_try_rust_catch_unwind(
    int (*rust_fn)(int*, int*),
    int* rust_drops,
    int* cpp_dtors
) {
    try {
        return rust_fn(rust_drops, cpp_dtors);
    } catch (const CppEx& ex) {
        trace_event("cpp_outer_caught_ex");
        return 200 + ex.code;
    } catch (...) {
        trace_event("cpp_outer_caught_unknown");
        return -777;
    }
}

// --- SysV x86-64 __int128 / i128 ABI parity definitions ---

struct Pair48 {
    u8_t tag;
    u128_t big;
    u64_t tail;
};

struct Mixed64 {
    u8_t a;
    u128_t u;
    u32_t b;
    i128_t s;
};

struct LayoutReport {
    u64_t size;
    u64_t align;
    u64_t off0;
    u64_t off1;
    u64_t off2;
    u64_t off3;
};

extern "C" __attribute__((noinline)) LayoutReport cpp_inspect_pair48_layout() {
    LayoutReport r;
    r.size = sizeof(Pair48);
    r.align = alignof(Pair48);
    r.off0 = __builtin_offsetof(Pair48, tag);
    r.off1 = __builtin_offsetof(Pair48, big);
    r.off2 = __builtin_offsetof(Pair48, tail);
    r.off3 = 0;
    return r;
}

extern "C" __attribute__((noinline)) LayoutReport cpp_inspect_mixed64_layout() {
    LayoutReport r;
    r.size = sizeof(Mixed64);
    r.align = alignof(Mixed64);
    r.off0 = __builtin_offsetof(Mixed64, a);
    r.off1 = __builtin_offsetof(Mixed64, u);
    r.off2 = __builtin_offsetof(Mixed64, b);
    r.off3 = __builtin_offsetof(Mixed64, s);
    return r;
}

extern "C" __attribute__((noinline)) u128_t cpp_pass_pair48_byval(Pair48 p) {
    return p.big + (u128_t)p.tag + (u128_t)p.tail;
}

extern "C" __attribute__((noinline)) Pair48 cpp_ret_pair48_sret(u8_t tag, u128_t big, u64_t tail) {
    Pair48 p;
    p.tag = tag;
    p.big = big ^ ((u128_t)0x55aaULL << 64);
    p.tail = tail + 11;
    return p;
}

extern "C" __attribute__((noinline)) u128_t cpp_pass_mixed64_byval(Mixed64 m) {
    return m.u ^ (u128_t)m.s ^ (((u128_t)m.b << 64) | (u128_t)m.a);
}

extern "C" __attribute__((noinline)) Mixed64 cpp_ret_mixed64_sret(
    u8_t a, u128_t u, u32_t b, i128_t s
) {
    Mixed64 m;
    m.a = a;
    m.u = u + 3;
    m.b = b + 5;
    m.s = s - 7;
    return m;
}

extern "C" __attribute__((noinline)) u128_t cpp_add_pair_128(u128_t a, i128_t b) {
    return a + (u128_t)b + 7;
}

extern "C" __attribute__((noinline)) i128_t cpp_unaligned_gpr_128(
    u8_t tag, u128_t a, i128_t b
) {
    return (i128_t)(a ^ (u128_t)tag) - b;
}

// 5 scalar integer args use %rdi, %rsi, %rdx, %rcx, %r8 (leaving 1 GPR %r9).
// SysV AMD64 requires 16-byte __int128 to pass in two contiguous GPRs, so `stack_val`
// spills entirely onto the 16-byte-aligned stack slot while `r9_tail` remains in %r9!
extern "C" __attribute__((noinline)) u128_t cpp_spill_5gpr_128(
    u64_t g0, u64_t g1, u64_t g2, u64_t g3, u64_t g4,
    u128_t stack_val, u64_t r9_tail
) {
    return stack_val + (u128_t)(g0 ^ g1 ^ g2 ^ g3 ^ g4 ^ r9_tail);
}

// --- ELF Symbol Visibility & Cross-Language ThinLTO Inlining Targets ---

extern "C" __attribute__((visibility("default"), noinline)) u64_t cpp_vis_default_fn(u64_t x) {
    return x * 3 + 17;
}

extern "C" __attribute__((visibility("hidden"), noinline)) u64_t cpp_vis_hidden_fn(u64_t x) {
    return x * 5 + 29;
}

// Intentionally inlineable across ThinLTO bitcode boundary (no `noinline`).
extern "C" u128_t cpp_thinlto_leaf_mul_add128(u128_t a, u128_t b) {
    return (a * 3) + (b ^ (u128_t)0x55aaULL);
}
