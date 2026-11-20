// Prints representation sizes of segmented-data types on this target.
#include <sys/uio.h>
#include <cstdio>
#include "absl/strings/cord.h"
#include "absl/strings/internal/cord_internal.h"
#include "absl/strings/internal/cord_rep_btree.h"
int main() {
  namespace ci = absl::cord_internal;
  std::printf("sizeof(struct iovec)=%zu\n", sizeof(struct iovec));
  std::printf("IOV_MAX=%d\n", IOV_MAX);
  std::printf("sizeof(absl::Cord)=%zu\n", sizeof(absl::Cord));
  std::printf("sizeof(CordRep)=%zu\n", sizeof(ci::CordRep));
  std::printf("sizeof(CordRepSubstring)=%zu\n", sizeof(ci::CordRepSubstring));
  std::printf("sizeof(CordRepExternal)=%zu\n", sizeof(ci::CordRepExternal));
  std::printf("CordRepBtree::kMaxCapacity=%zu\n", static_cast<size_t>(ci::CordRepBtree::kMaxCapacity));
  std::printf("sizeof(CordRepBtree)=%zu\n", sizeof(ci::CordRepBtree));
  std::printf("kMaxInline=%d kMaxBytesToCopy=%d\n", static_cast<int>(ci::kMaxInline), static_cast<int>(ci::kMaxBytesToCopy));
  return 0;
}
