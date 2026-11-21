// Allocation-elision probe (C++ new-expression; [expr.new] permits omission).
#include <cstdio>
#include <cstddef>
#include <new>
int main() {
  try {
    char *p = new char[std::size_t(1) << 50];
    delete[] p;
    std::puts("new char[2^50]: returned");
    return 0;
  } catch (const std::bad_alloc &) {
    std::puts("new char[2^50]: std::bad_alloc");
    return 1;
  }
}
