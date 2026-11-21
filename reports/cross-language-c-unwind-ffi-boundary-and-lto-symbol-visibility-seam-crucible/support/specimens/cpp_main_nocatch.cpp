// C++17 main() driver with NO surrounding try/catch calling a `-C panic=abort`
// Rust staticlib `extern "C-unwind"` boundary. Demonstrates that because
// `AbortUnwindingCalls` converts `resume;` -> `terminate(abi);` inside a MIR cleanup
// block lowered to `landingpad ... cleanup` (`EHAction::Cleanup`, cs_action = 0),
// an uncaught C++ stack hits `_URC_END_OF_STACK` (`std::terminate()`) in step 1
// rather than entering step 2 to run Rust `Drop` or `panic_cannot_unwind()`.

struct BareCppEx {
    int code;
};

extern "C" {
long write(int fd, const void* buf, unsigned long count);
void rust_staticlib_c_unwind_with_guard();
void rust_staticlib_c_unwind_no_guard();
}

extern "C" __attribute__((noinline)) void cpp_throw_nocatch() {
    const char msg[] = "[TRACE] cpp_throwing_bare\n";
    (void)write(2, msg, sizeof(msg) - 1);
    throw BareCppEx{99};
}

int main(int argc, char** argv) {
    if (argc > 1 && argv[1][0] == 'g') {
        rust_staticlib_c_unwind_with_guard();
    } else {
        rust_staticlib_c_unwind_no_guard();
    }
    return 0;
}
