// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#include <assert.h>
#include <stdint.h>
#include <stdio.h>

extern uint64_t anneal_double_u64(uint64_t x);

int main(void) {
    assert(anneal_double_u64(0ULL) == 0ULL);
    assert(anneal_double_u64(21ULL) == 42ULL);
    assert(anneal_double_u64(0x8000000000000001ULL) == 2ULL);
    printf("cpu_exec: ok (anneal_double_u64 passed all 64-bit modular tests)\n");
    return 0;
}
