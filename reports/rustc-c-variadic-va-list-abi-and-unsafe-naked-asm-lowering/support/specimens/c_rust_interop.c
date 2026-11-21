#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>

extern uint64_t rust_variadic_mixed(size_t tag_count, ...);
extern uint64_t rust_vsum_indirect_valist(size_t tag_count, va_list ap);
extern uint64_t rust_calls_c_valist_twice(size_t count, ...);

uint64_t c_vsum_takes_valist(size_t count, va_list ap) {
    uint64_t s = 0;
    for (size_t i = 0; i < count; i++) {
        s += va_arg(ap, uint64_t);
    }
    return s;
}

static uint64_t forward_va_list(size_t tag_count, ...) {
    va_list ap;
    va_start(ap, tag_count);
    uint64_t r = rust_vsum_indirect_valist(tag_count, ap);
    va_end(ap);
    return r;
}

int main(void) {
    uint64_t direct = rust_variadic_mixed(
        1, (int32_t)10, 20.0, (int32_t)30, (uint64_t)40, 50.0, (uint64_t)60, (uint64_t)10, (uint64_t)1000
    );
    uint64_t decay = forward_va_list(
        1, (int32_t)10, 20.0, (int32_t)30, (uint64_t)40, 50.0, (uint64_t)60, (uint64_t)10, (uint64_t)1000
    );
    uint64_t r2c = rust_calls_c_valist_twice(3, (uint64_t)100, (uint64_t)200, (uint64_t)300);
    printf("C_TO_RUST_VA=%llu C_VA_LIST_DECAY=%llu RUST_TO_C_VA_DECAY=%llu\n",
           (unsigned long long)direct,
           (unsigned long long)decay,
           (unsigned long long)r2c);
    return 0;
}
