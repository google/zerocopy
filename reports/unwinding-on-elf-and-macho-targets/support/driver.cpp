#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <exception>
#include <pthread.h>

extern "C" {
    void c_boundary_no_drop(void (*f)());
    void c_boundary_with_drop(void (*f)());
    unsigned int get_drop_log();
}

static void throw_cpp() {
    throw 42;
}

static void do_pthread_exit() {
    pthread_exit(nullptr);
}

static void* thread_no_drop(void*) {
    c_boundary_no_drop(do_pthread_exit);
    return nullptr;
}

static void* thread_with_drop(void*) {
    c_boundary_with_drop(do_pthread_exit);
    return nullptr;
}

int main(int argc, char** argv) {
    std::set_terminate([]() {
        std::printf("TERMINATE_HANDLER drop_log=%u\n", get_drop_log());
        std::fflush(stdout);
        std::_Exit(99);
    });
    if (argc < 2) return 1;
    if (std::strcmp(argv[1], "cpp_no_drop") == 0) {
        c_boundary_no_drop(throw_cpp);
    } else if (std::strcmp(argv[1], "cpp_with_drop") == 0) {
        c_boundary_with_drop(throw_cpp);
    } else if (std::strcmp(argv[1], "pthread_no_drop") == 0) {
        pthread_t th;
        pthread_create(&th, nullptr, thread_no_drop, nullptr);
        pthread_join(th, nullptr);
        std::printf("PTHREAD_JOIN_OK drop_log=%u\n", get_drop_log());
    } else if (std::strcmp(argv[1], "pthread_with_drop") == 0) {
        pthread_t th;
        pthread_create(&th, nullptr, thread_with_drop, nullptr);
        pthread_join(th, nullptr);
        std::printf("PTHREAD_JOIN_OK drop_log=%u\n", get_drop_log());
    }
    return 0;
}
