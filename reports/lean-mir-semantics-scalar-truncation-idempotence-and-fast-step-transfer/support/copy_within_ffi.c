/*
 * Copyright 2026 The Fuchsia Authors
 *
 * Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
 * <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
 * license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
 * This file may not be copied, modified, or distributed except according to
 * those terms.
 */

/* Single-owned ByteArray self-append primitive (`probe_byte_array_copy_within`).
 * Uses `-nostdinc`-safe `__builtin_memcpy` and forward-declares
 * `lean_sarray_ensure_capacity`, avoiding `<string.h>` and Perceus `@&` aliasing. */

#include <lean/lean.h>
#include <stdint.h>

extern lean_object *lean_sarray_ensure_capacity(lean_object *a, size_t min_cap,
                                                int exact);

LEAN_EXPORT lean_object *probe_byte_array_copy_within(
        lean_object *a, b_lean_obj_arg o_src_off, b_lean_obj_arg o_len) {
    size_t src_off = lean_usize_of_nat(o_src_off);
    size_t oldsz   = lean_sarray_size(a);
    if (src_off > oldsz) return a;
    size_t len = lean_usize_of_nat(o_len);
    if (len > oldsz - src_off) len = oldsz - src_off;
    size_t newsz = oldsz + len;

    lean_object *r = lean_sarray_ensure_capacity(a, newsz, 0);
    if (!lean_is_exclusive(r)) {
        size_t cap = lean_sarray_capacity(r);
        if (cap < newsz) cap = newsz;
        lean_object *c = lean_alloc_sarray(1, oldsz, cap);
        __builtin_memcpy(lean_sarray_cptr(c), lean_sarray_cptr(r), oldsz);
        lean_dec(r);
        r = c;
    }
    lean_sarray_set_size(r, newsz);

    uint8_t *p = lean_sarray_cptr(r);
    __builtin_memcpy(p + oldsz, p + src_off, len);
    return r;
}
