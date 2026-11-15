// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#ifndef ANNEAL_SUBSTRATE_SHIM_H
#define ANNEAL_SUBSTRATE_SHIM_H
#include <lean/lean.h>
#include <stdint.h>
#define ANNEAL_INLINE static inline __attribute__((always_inline, unused))

ANNEAL_INLINE lean_obj_res anneal_ba_alloc_zero(uint32_t n_bytes) {
    lean_obj_res r = lean_alloc_sarray(1, (size_t)n_bytes, (size_t)n_bytes);
    __builtin_memset(lean_sarray_cptr(r), 0, (size_t)n_bytes);
    return r;
}
ANNEAL_INLINE uint8_t anneal_ba_uget8(b_lean_obj_arg ba, uint32_t idx) { return lean_sarray_cptr(ba)[idx]; }
ANNEAL_INLINE uint32_t anneal_ba_uget32(b_lean_obj_arg ba, uint32_t idx) { return ((const uint32_t *)lean_sarray_cptr(ba))[idx]; }
ANNEAL_INLINE lean_obj_res anneal_ba_uset32(lean_obj_arg ba, uint32_t idx, uint32_t val) {
    lean_obj_res r = LEAN_LIKELY(lean_is_exclusive(ba)) ? ba : lean_copy_byte_array(ba);
    ((uint32_t *)lean_sarray_cptr(r))[idx] = val;
    return r;
}
ANNEAL_INLINE uint64_t anneal_ba_uget64(b_lean_obj_arg ba, uint64_t idx) { return ((const uint64_t *)lean_sarray_cptr(ba))[idx]; }
ANNEAL_INLINE lean_obj_res anneal_ba_uset64(lean_obj_arg ba, uint64_t idx, uint64_t val) {
    lean_obj_res r = LEAN_LIKELY(lean_is_exclusive(ba)) ? ba : lean_copy_byte_array(ba);
    ((uint64_t *)lean_sarray_cptr(r))[idx] = val;
    return r;
}
ANNEAL_INLINE uint32_t anneal_ba_uf_find_halving(b_lean_obj_arg ba, uint32_t x) {
    uint32_t *arr = (uint32_t *)lean_sarray_cptr(ba);
    for (uint32_t cur = x;;) {
        uint32_t ex = arr[cur], p = ex & 0xFFFFFFu;
        if (p == cur) return cur;
        arr[cur] = (ex & 0xFF000000u) | (arr[p] & 0xFFFFFFu);
        cur = p;
    }
}
ANNEAL_INLINE uint32_t anneal_ba_uf_union_mut(b_lean_obj_arg ba, uint32_t a, uint32_t b) {
    uint32_t *arr = (uint32_t *)lean_sarray_cptr(ba);
    uint32_t ra = anneal_ba_uf_find_halving(ba, a), rb = anneal_ba_uf_find_halving(ba, b);
    if (ra != rb) {
        uint32_t ea = arr[ra], eb = arr[rb], rka = ea >> 24, rkb = eb >> 24;
        if (rka < rkb) arr[ra] = (rka << 24) | rb;
        else if (rka > rkb) arr[rb] = (rkb << 24) | ra;
        else { arr[rb] = (rkb << 24) | ra; arr[ra] = ((rka + 1u) << 24) | ra; }
    }
    return ra;
}
ANNEAL_INLINE uint64_t anneal_ba_regalloc_arena(b_lean_obj_arg ba, uint32_t n_vregs) {
    uint32_t *pe = (uint32_t *)lean_sarray_cptr(ba), next_spill = 0;
    uint64_t checksum = 0;
    for (uint32_t i = 0; i < n_vregs; ++i) {
        uint32_t start = i * 2u, stop = start + ((i * 37u + 11u) & 63u) + 4u, alloc = 16;
        for (uint32_t r = 0; r < 16; ++r) if (pe[r] <= start) { alloc = r; break; }
        if (LEAN_LIKELY(alloc < 16)) { pe[alloc] = stop; checksum += (uint64_t)alloc; }
        else {
            uint32_t max_reg = 0, max_val = pe[0];
            for (uint32_t r = 1; r < 16; ++r) if (pe[r] > max_val) { max_val = pe[r]; max_reg = r; }
            next_spill += 1u;
            if (max_val > stop) pe[max_reg] = stop;
            checksum += ((uint64_t)next_spill << 8);
        }
    }
    return checksum;
}
#endif
