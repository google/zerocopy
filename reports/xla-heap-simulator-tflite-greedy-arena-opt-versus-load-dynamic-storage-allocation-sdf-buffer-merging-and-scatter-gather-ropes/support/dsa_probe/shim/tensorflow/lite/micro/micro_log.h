// Minimal shim: route MicroPrintf to stderr.
#ifndef PROBE_SHIM_MICRO_LOG_H_
#define PROBE_SHIM_MICRO_LOG_H_
#include <cstdarg>
#include <cstdio>
inline void MicroPrintf(const char* fmt, ...) {
  va_list ap; va_start(ap, fmt); std::vfprintf(stderr, fmt, ap); va_end(ap);
  std::fputc('\n', stderr);
}
#endif
