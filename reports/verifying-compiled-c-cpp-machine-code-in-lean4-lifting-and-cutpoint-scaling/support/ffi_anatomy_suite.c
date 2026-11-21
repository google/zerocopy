/*
 * Realistic C FFI benchmark suite exposing compiler-generated x86-64 machine-code
 * structures (GCC 15.2.0) that distinguish compiled .o objects from hand-written .S.
 */
#include <stddef.h>
#include <stdint.h>

/* External declarations used to prevent whole-program inlining and expose relocations. */
extern uint64_t ext_sink_fn(uint64_t a, uint64_t b);
extern void ext_consume_buf(const uint8_t *buf, size_t len);

/*
 * (a) Pointer/buffer TLV parsing loop with heavy live state forcing callee-saved
 *     pushes and stack register spills even at -O2.
 */
uint64_t tlv_parse_checksum(
    const uint8_t *buf,
    size_t len,
    uint64_t seed0,
    uint64_t seed1,
    uint64_t *out_counts
) {
    size_t pos = 0;
    uint64_t h0 = seed0 ^ 0x9e3779b97f4a7c15ULL;
    uint64_t h1 = seed1 ^ 0xbf58476d1ce4e5b9ULL;
    uint64_t h2 = seed0 + 0x94d049bb133111ebULL;
    uint64_t h3 = seed1 + 0x2545f4914f6cdd1dULL;
    uint64_t h4 = (seed0 >> 13) ^ (seed1 << 7);
    uint64_t h5 = (seed1 >> 17) ^ (seed0 << 11);
    uint64_t h6 = seed0 * 0x100000001b3ULL;
    uint64_t h7 = seed1 * 0x517cc1b727220a95ULL;
    uint64_t h8 = h0 ^ h4;
    uint64_t h9 = h1 + h5;
    uint64_t frames = 0;
    uint64_t payload_bytes = 0;

    while (pos + 4 <= len) {
        uint8_t tag = buf[pos];
        uint8_t flags = buf[pos + 1];
        uint16_t flen = (uint16_t)buf[pos + 2] | ((uint16_t)buf[pos + 3] << 8);
        pos += 4;
        if (flen > len - pos) {
            break;
        }
        const uint8_t *p = buf + pos;
        for (size_t i = 0; i < (size_t)flen; ++i) {
            uint64_t b = (uint64_t)p[i];
            h0 = (h0 ^ b) * 0x100000001b3ULL + h9;
            h1 = ((h1 << 5) | (h1 >> 59)) ^ (b + tag);
            h2 = h2 + (h0 ^ (uint64_t)flags) + i;
            h3 = (h3 * 33ULL) ^ (h1 + b);
            h4 = h4 ^ ((h2 >> 7) + (h3 << 3));
            h5 = (h5 + h4) ^ (b * 0x9e3779b9ULL);
            h6 = ((h6 << 11) | (h6 >> 53)) + h5 + tag;
            h7 = (h7 ^ h6) + (flags * 17ULL) + i;
            h8 = (h8 + h7) ^ (h0 >> 19);
            h9 = ((h9 << 13) | (h9 >> 51)) + (h8 ^ h2);
        }
        /* Interleave a call so live accumulators must survive across ABI clobbers. */
        if ((flags & 0x80U) != 0) {
            h0 ^= ext_sink_fn(h1 ^ h2, h3 + h4);
            h5 += ext_sink_fn(h6 ^ h7, h8 + h9);
        }
        pos += (size_t)flen;
        frames += 1;
        payload_bytes += (uint64_t)flen;
    }

    if (out_counts != NULL) {
        out_counts[0] = frames;
        out_counts[1] = payload_bytes;
        out_counts[2] = h0 ^ h1 ^ h2 ^ h3 ^ h4;
        out_counts[3] = h5 ^ h6 ^ h7 ^ h8 ^ h9;
    }
    return (h0 ^ h2 ^ h4 ^ h6 ^ h8) + (h1 ^ h3 ^ h5 ^ h7 ^ h9) + frames;
}

/*
 * (b) Dense 16-case switch generating a .rodata PC-relative indirect jump table.
 */
uint64_t opcode_dispatch_16(uint32_t op, uint64_t x, uint64_t y, uint64_t *state) {
    uint64_t acc = *state;
    switch (op) {
        case 0:  acc = (acc + x) ^ (y * 3ULL); break;
        case 1:  acc = (acc - y) + ((x << 7) | (x >> 57)); break;
        case 2:  acc = (acc * 0x100000001b3ULL) ^ x; break;
        case 3:  acc = ext_sink_fn(acc ^ x, y); break;
        case 4:  acc = (x + y + 17ULL) * (acc | 1ULL); break;
        case 5:  acc = ((acc >> 11) | (acc << 53)) + (x & y); break;
        case 6:  acc = ext_sink_fn(x + 5ULL, acc - y); break;
        case 7:  acc = (acc ^ 0xdeadbeefcafebabeULL) + (x / (y | 1ULL)); break;
        case 8:  acc = (acc + (x * y)) ^ (x >> 3); break;
        case 9:  acc = (acc - (x ^ y)) * 29ULL; break;
        case 10: acc = ext_sink_fn(y, acc ^ 0x5555555555555555ULL); break;
        case 11: acc = ((x << 13) ^ (y >> 9)) + acc; break;
        case 12: acc = (acc | x) - (acc & y) + 101ULL; break;
        case 13: acc = (acc * 65599ULL) + (x % ((y & 0xFFULL) + 1ULL)); break;
        case 14: acc = ext_sink_fn(acc, x ^ (y << 1)); break;
        case 15: acc = ~(acc + x + y); break;
        default: return 0xFFFFFFFFFFFFFFFFULL;
    }
    *state = acc;
    return acc ^ (uint64_t)op;
}

/*
 * (c1) Auto-vectorized loop WITHOUT restrict: forces runtime alias check +
 *      prolog/main SSE2 or AVX2 vector loop + scalar epilog tail.
 */
void vec_add_aliased(uint32_t *dst, const uint32_t *a, const uint32_t *b, size_t n) {
    for (size_t i = 0; i < n; ++i) {
        dst[i] = a[i] + b[i];
    }
}

/*
 * (c2) Auto-vectorized loop WITH restrict: removes pointer-overlap guard but
 *      still emits vector main loop + scalar/vector epilog tails.
 */
void vec_add_restrict(
    uint32_t * __restrict dst,
    const uint32_t * __restrict a,
    const uint32_t * __restrict b,
    size_t n
) {
    for (size_t i = 0; i < n; ++i) {
        dst[i] = a[i] + b[i];
    }
}

/*
 * (d) Sibling tail calls: direct PLT jump (jmp ext_sink_fn@PLT) and indirect
 *     function-pointer tail call (jmp *%rdx), with zero ret instruction on tail paths.
 */
typedef uint64_t (*tail_cb_t)(uint64_t, uint64_t);

uint64_t sibling_tail_dispatch(uint64_t a, uint64_t b, tail_cb_t cb, int mode) {
    if (mode == 0) {
        return ext_sink_fn(a + 1ULL, b ^ 3ULL);
    }
    if (mode == 1) {
        return cb(a * 7ULL, b + 11ULL);
    }
    return a ^ b;
}

/*
 * (e1) Compiler-synthesized libc calls: hand-written loops that GCC
 *      -ftree-loop-distribute-patterns lowers into calls to memset and memcpy/memmove.
 */
void synth_zero_and_copy(uint8_t * __restrict dst, const uint8_t * __restrict src, size_t n) {
    for (size_t i = 0; i < n; ++i) {
        dst[i] = 0;
    }
    ext_consume_buf(dst, n);
    for (size_t i = 0; i < n; ++i) {
        dst[i] = src[i];
    }
}

/*
 * (e2) Stack canary (-fstack-protector-strong) via small stack buffer whose address escapes.
 */
uint64_t stack_buf_hash_small(const uint8_t *in, size_t n) {
    uint8_t scratch[128];
    size_t m = n < sizeof(scratch) ? n : sizeof(scratch);
    for (size_t i = 0; i < m; ++i) {
        scratch[i] = (uint8_t)(in[i] ^ (uint8_t)i);
    }
    ext_consume_buf(scratch, m);
    uint64_t sum = 0;
    for (size_t i = 0; i < m; ++i) {
        sum = sum * 131ULL + scratch[i];
    }
    return sum;
}

/*
 * (e3) Large stack buffer (>4096 bytes) triggering both -fstack-protector-strong
 *      (%fs:0x28 canary + __stack_chk_fail) AND -fstack-clash-protection probing loop.
 */
uint64_t stack_buf_hash_large(const uint8_t *in, size_t n) {
    uint8_t scratch[8192];
    size_t m = n < sizeof(scratch) ? n : sizeof(scratch);
    for (size_t i = 0; i < m; ++i) {
        scratch[i] = (uint8_t)(in[i] + 1U);
    }
    ext_consume_buf(scratch, m);
    return (uint64_t)scratch[0] | ((uint64_t)scratch[m > 0 ? m - 1 : 0] << 8);
}
