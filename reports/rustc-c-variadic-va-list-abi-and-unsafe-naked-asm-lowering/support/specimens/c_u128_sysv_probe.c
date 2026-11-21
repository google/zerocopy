#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>

typedef unsigned __int128 u128;

__attribute__((noinline))
u128 read_1gp_then_u128_then_u64(uint64_t a0, ...) {
    va_list ap;
    va_start(ap, a0);
    u128 x = va_arg(ap, u128);
    uint64_t tail = va_arg(ap, uint64_t);
    va_end(ap);
    return x + tail;
}

__attribute__((noinline))
u128 read_5gp_then_u128_then_u64(uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3, uint64_t a4, ...) {
    va_list ap;
    va_start(ap, a4);
    u128 x = va_arg(ap, u128);
    uint64_t tail = va_arg(ap, uint64_t);
    va_end(ap);
    return x + tail;
}

__attribute__((noinline))
u128 read_7gp_then_u128(uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3, uint64_t a4, uint64_t a5, ...) {
    va_list ap;
    va_start(ap, a5);
    uint64_t s0 = va_arg(ap, uint64_t);
    u128 x = va_arg(ap, u128);
    va_end(ap);
    return x + s0;
}

int main(void) {
    u128 v = (((u128)0x1122334455667788ULL) << 64) | 0x99AABBCCDDEEFF00ULL;
    u128 r1 = read_1gp_then_u128_then_u64(1, v, (uint64_t)7);
    u128 r2 = read_5gp_then_u128_then_u64(1, 2, 3, 4, 5, v, (uint64_t)9);
    u128 r3 = read_7gp_then_u128(1, 2, 3, 4, 5, 6, (uint64_t)11, v);
    printf("U128_ODD_GP_OK=%d U128_SPILL_R9_BACKFILL_OK=%d U128_OVERFLOW_ALIGN16_OK=%d\n",
           r1 == v + 7, r2 == v + 9, r3 == v + 11);
    return 0;
}
