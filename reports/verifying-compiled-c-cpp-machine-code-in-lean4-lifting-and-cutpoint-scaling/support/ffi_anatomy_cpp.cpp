/*
 * C++ small-class FFI benchmark exposing vptr/vtable indirect calls, Itanium C++ ABI
 * symbols (_ZTV, _ZTI), and exception-handling metadata (.eh_frame / .gcc_except_table /
 * __gxx_personality_v0 / _Unwind_Resume).
 */
#include <cstddef>
#include <cstdint>

extern "C" void ext_cpp_log(uint64_t code);

struct ScopedGuard {
    uint64_t tag;
    explicit ScopedGuard(uint64_t t) : tag(t) {}
    ~ScopedGuard() { ext_cpp_log(tag); }
};

struct CodecBase {
    virtual ~CodecBase() = default;
    virtual uint64_t process(const uint8_t *buf, size_t len) const = 0;
    virtual uint64_t flush(uint64_t acc) const = 0;
};

struct XorCodec : CodecBase {
    uint64_t seed;
    explicit XorCodec(uint64_t s) : seed(s) {}

    uint64_t process(const uint8_t *buf, size_t len) const override {
        uint64_t acc = seed;
        for (size_t i = 0; i < len; ++i) {
            acc = ((acc << 3) | (acc >> 61)) ^ static_cast<uint64_t>(buf[i]);
        }
        return acc;
    }

    uint64_t flush(uint64_t acc) const override {
        return acc ^ (seed * 0x9e3779b97f4a7c15ULL);
    }
};

extern "C" uint64_t cpp_codec_invoke(const CodecBase *codec, const uint8_t *buf, size_t len) {
    ScopedGuard guard(0xC0DEC0DEULL);
    uint64_t mid = codec->process(buf, len);
    return codec->flush(mid);
}

extern "C" uint64_t cpp_xor_direct(uint64_t seed, const uint8_t *buf, size_t len) {
    XorCodec c(seed);
    return c.process(buf, len);
}
