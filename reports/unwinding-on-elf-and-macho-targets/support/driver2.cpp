#include <cstdio>
#include <cstdlib>
#include <cstring>

extern "C" {
    void rust_c_unwind_nested(void (*f)());
    int rust_catch_foreign(void (*f)());
    unsigned int get_drop_log();
}

static void throw_cpp() {
    throw 42;
}

int main(int argc, char** argv) {
    if (argc < 2) return 1;
    if (std::strcmp(argv[1], "cpp_through_c_unwind") == 0) {
        try {
            rust_c_unwind_nested(throw_cpp);
        } catch (int x) {
            std::printf("CAUGHT_CPP=%d drop_log=%u\n", x, get_drop_log());
        }
    } else if (std::strcmp(argv[1], "rust_catch_cpp") == 0) {
        int r = rust_catch_foreign(throw_cpp);
        std::printf("RUST_CATCH_RET=%d\n", r);
    }
    return 0;
}
