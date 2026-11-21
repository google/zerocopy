// Bounded probe: C malloc, C++ throwing new, and C++ nothrow new under an
// address-space limit that the probe sets for itself with setrlimit(RLIMIT_AS).
// Modes: malloc | new | nothrow
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <new>
#include <sys/resource.h>

int main(int argc, char** argv) {
    if (argc < 2) return 2;
    struct rlimit rl;
    rl.rlim_cur = rl.rlim_max = 256UL << 20;  // 256 MiB of address space
    if (setrlimit(RLIMIT_AS, &rl) != 0) { perror("setrlimit"); return 2; }
    const size_t chunk = 16UL << 20;  // 16 MiB per request
    size_t n = 0;
    if (!strcmp(argv[1], "malloc")) {
        for (;;) {
            void* p = malloc(chunk);
            if (!p) { printf("malloc returned NULL after %zu x 16 MiB\n", n); break; }
            memset(p, 1, chunk);
            n++;
        }
    } else if (!strcmp(argv[1], "new")) {
        try {
            for (;;) { char* p = new char[chunk]; memset(p, 1, chunk); n++; }
        } catch (const std::bad_alloc& e) {
            printf("new threw std::bad_alloc (what=%s) after %zu x 16 MiB\n", e.what(), n);
        }
    } else if (!strcmp(argv[1], "nothrow")) {
        for (;;) {
            char* p = new (std::nothrow) char[chunk];
            if (!p) { printf("nothrow new returned nullptr after %zu x 16 MiB\n", n); break; }
            memset(p, 1, chunk);
            n++;
        }
    } else {
        return 2;
    }
    printf("CONTINUED\n");
    return 0;
}
