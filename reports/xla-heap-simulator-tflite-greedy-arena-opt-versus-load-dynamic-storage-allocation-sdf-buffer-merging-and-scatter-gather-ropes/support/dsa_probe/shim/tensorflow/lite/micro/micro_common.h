// Minimal shim replacing the upstream header for a standalone probe build.
// Supplies only the status type used by the memory planner interface.
#ifndef PROBE_SHIM_MICRO_COMMON_H_
#define PROBE_SHIM_MICRO_COMMON_H_
#include <cstddef>
typedef enum { kTfLiteOk = 0, kTfLiteError = 1 } TfLiteStatus;
#endif
