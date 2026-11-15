// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

/*
 * anneal_procmacro_det.c — Hermetic LD_PRELOAD Determinism Shim for rustc Proc-Macro Servers
 *
 * Intercepts non-deterministic host entropy and wall-clock syscalls/libc entrypoints
 * inside procedural-macro server processes (`rustc --proc-macro` / `rust-analyzer-proc-macro-srv`):
 *   1. `getrandom(void *buf, size_t buflen, unsigned int flags)`:
 *      Replaces kernel `/dev/urandom` entropy with a deterministic SplitMix64 stream
 *      seeded by `ANNEAL_PROCMACRO_SEED` (default `0x414E4E45414C5F31ULL`), ensuring
 *      `std::collections::HashMap` / `HashSet` (`RandomState`) iteration order inside
 *      proc-macros (`#[derive(...)]`) is 100% deterministic across builds and machines.
 *   2. `clock_gettime(clockid_t clk_id, struct timespec *tp)`:
 *      Virtualizes `CLOCK_REALTIME` and `CLOCK_REALTIME_COARSE` to `SOURCE_DATE_EPOCH`
 *      (default `1700000000`, `tv_nsec = 0`), preventing `SystemTime::now()` inside
 *      proc-macros from perturbing `TokenStream` outputs and Tier 1 `MirItemKey` digests.
 *   3. `getpid(void)`:
 *      When `ANNEAL_VIRTUALIZE_PID=1` is set, returns a fixed synthetic PID (`4242`).
 */

#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

static uint64_t splitmix64_next(uint64_t *state) {
    uint64_t z = (*state += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t get_configured_seed(void) {
    const char *env = getenv("ANNEAL_PROCMACRO_SEED");
    if (env && *env) {
        return strtoull(env, NULL, 0);
    }
    return 0x414E4E45414C5F31ULL;
}

ssize_t getrandom(void *buf, size_t buflen, unsigned int flags) {
    (void)flags;
    if (!buf) {
        return -1;
    }
    uint64_t state = get_configured_seed();
    uint8_t *out = (uint8_t *)buf;
    size_t offset = 0;
    while (offset < buflen) {
        uint64_t word = splitmix64_next(&state);
        size_t chunk = (buflen - offset < sizeof(uint64_t)) ? (buflen - offset) : sizeof(uint64_t);
        memcpy(out + offset, &word, chunk);
        offset += chunk;
    }
    return (ssize_t)buflen;
}

int getentropy(void *buffer, size_t length) {
    if (length > 256) {
        return -1;
    }
    return (getrandom(buffer, length, 0) == (ssize_t)length) ? 0 : -1;
}

int clock_gettime(clockid_t clk_id, struct timespec *tp) {
    if (!tp) {
        return -1;
    }
    if (clk_id == CLOCK_REALTIME || clk_id == CLOCK_REALTIME_COARSE) {
        const char *sde = getenv("SOURCE_DATE_EPOCH");
        time_t fixed_sec = (sde && *sde) ? (time_t)strtoll(sde, NULL, 10) : (time_t)1700000000;
        tp->tv_sec = fixed_sec;
        tp->tv_nsec = 0;
        return 0;
    }
    int (*real_clock_gettime)(clockid_t, struct timespec *) =
        (int (*)(clockid_t, struct timespec *))dlsym(RTLD_NEXT, "clock_gettime");
    if (real_clock_gettime) {
        return real_clock_gettime(clk_id, tp);
    }
    tp->tv_sec = 0;
    tp->tv_nsec = 0;
    return 0;
}

pid_t getpid(void) {
    const char *vpid = getenv("ANNEAL_VIRTUALIZE_PID");
    if (vpid && strcmp(vpid, "1") == 0) {
        return (pid_t)4242;
    }
    pid_t (*real_getpid)(void) = (pid_t (*)(void))dlsym(RTLD_NEXT, "getpid");
    return real_getpid ? real_getpid() : 4242;
}
