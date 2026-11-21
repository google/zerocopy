// C17 companion specimen compiled with GCC to cross-check __int128 / unsigned __int128
// SysV x86-64 struct layout, 5-GPR straddle stack spilling, and STV_DEFAULT/STV_HIDDEN
// visibility parity across gcc, clang, and rustc.

#include <stdint.h>
#include <stddef.h>

typedef __int128 c17_i128;
typedef unsigned __int128 c17_u128;

struct C17Pair48 {
    uint8_t tag;
    c17_u128 big;
    uint64_t tail;
};

struct C17Mixed64 {
    uint8_t a;
    c17_u128 u;
    uint32_t b;
    c17_i128 s;
};

struct C17LayoutReport {
    uint64_t size;
    uint64_t align;
    uint64_t off0;
    uint64_t off1;
    uint64_t off2;
    uint64_t off3;
};

__attribute__((noinline)) struct C17LayoutReport gcc_inspect_pair48_layout(void) {
    struct C17LayoutReport r = {
        sizeof(struct C17Pair48),
        _Alignof(struct C17Pair48),
        offsetof(struct C17Pair48, tag),
        offsetof(struct C17Pair48, big),
        offsetof(struct C17Pair48, tail),
        0
    };
    return r;
}

__attribute__((noinline)) struct C17LayoutReport gcc_inspect_mixed64_layout(void) {
    struct C17LayoutReport r = {
        sizeof(struct C17Mixed64),
        _Alignof(struct C17Mixed64),
        offsetof(struct C17Mixed64, a),
        offsetof(struct C17Mixed64, u),
        offsetof(struct C17Mixed64, b),
        offsetof(struct C17Mixed64, s)
    };
    return r;
}

__attribute__((noinline)) c17_u128 gcc_spill_5gpr_128(
    uint64_t g0, uint64_t g1, uint64_t g2, uint64_t g3, uint64_t g4,
    c17_u128 stack_val, uint64_t r9_tail
) {
    return stack_val + (c17_u128)(g0 ^ g1 ^ g2 ^ g3 ^ g4 ^ r9_tail);
}

__attribute__((noinline)) c17_i128 gcc_unaligned_gpr_128(
    uint8_t tag, c17_u128 a, c17_i128 b
) {
    return (c17_i128)(a ^ (c17_u128)tag) - b;
}

__attribute__((visibility("default"), noinline)) uint64_t gcc_vis_default_fn(uint64_t x) {
    return x * 7 + 41;
}

__attribute__((visibility("hidden"), noinline)) uint64_t gcc_vis_hidden_fn(uint64_t x) {
    return x * 11 + 53;
}
