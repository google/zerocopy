// Probe of HL::ZoneHeap (Heap-Layers) vs glibc malloc/free.
// Measures: bytes obtained from the super-heap, per-object overhead,
// peak footprint under FIFO ("asynchronous death") workloads, and timing.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <chrono>
#include <vector>
#include <malloc.h>
#include "heaplayers.h"

struct CountingHeap {
  enum { Alignment = 16 };
  static size_t outstanding, peak, calls;
  void* malloc(size_t sz) { outstanding += sz; if (outstanding > peak) peak = outstanding; calls++; return ::malloc(sz); }
  void free(void* p, size_t sz) { outstanding -= sz; ::free(p); }
};
size_t CountingHeap::outstanding = 0, CountingHeap::peak = 0, CountingHeap::calls = 0;

template <size_t Chunk> using Zone = HL::ZoneHeap<CountingHeap, Chunk>;
static double now() { return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count(); }

template <size_t Chunk>
void zone_bulk(size_t n, size_t s, const char* label) {
  CountingHeap::outstanding = CountingHeap::peak = CountingHeap::calls = 0;
  double t0 = now();
  {
    Zone<Chunk> z;
    for (size_t i = 0; i < n; i++) { char* p = (char*)z.malloc(s); p[0] = (char)i; }
    double t1 = now();
    size_t peak = CountingHeap::peak, calls = CountingHeap::calls;
    z.clear();
    double t2 = now();
    printf("zone  %-14s chunk=%zu n=%zu s=%zu superheap_peak=%zu bytes_per_obj=%.3f superheap_calls=%zu alloc_ns=%.2f clear_ms=%.3f\n",
           label, Chunk, n, s, peak, (double)peak / n, calls, (t1 - t0) * 1e9 / n, (t2 - t1) * 1e3);
  }
}

void malloc_bulk(size_t n, size_t s) {
  std::vector<void*> v(n);
  struct mallinfo2 m0 = mallinfo2();
  double t0 = now();
  for (size_t i = 0; i < n; i++) { v[i] = ::malloc(s); ((char*)v[i])[0] = (char)i; }
  double t1 = now();
  struct mallinfo2 m1 = mallinfo2();
  size_t usable = malloc_usable_size(v[0]);
  for (size_t i = 0; i < n; i++) ::free(v[i]);
  double t2 = now();
  printf("glibc bulk           n=%zu s=%zu arena_in_use_delta=%zu bytes_per_obj=%.3f usable=%zu alloc_ns=%.2f free_all_ms=%.3f\n",
         n, s, (size_t)(m1.uordblks - m0.uordblks), (double)(m1.uordblks - m0.uordblks) / n, usable, (t1 - t0) * 1e9 / n, (t2 - t1) * 1e3);
}

// FIFO with window w: allocate n objects, each dies w allocations later.
template <size_t Chunk>
void zone_fifo(size_t n, size_t w, size_t s) {
  CountingHeap::outstanding = CountingHeap::peak = CountingHeap::calls = 0;
  Zone<Chunk> z;
  std::vector<char*> ring(w, nullptr);
  for (size_t i = 0; i < n; i++) { size_t k = i % w; if (ring[k]) z.free(ring[k]); ring[k] = (char*)z.malloc(s); ring[k][0] = 1; }
  printf("zone  fifo chunk=%zu n=%zu w=%zu s=%zu superheap_peak=%zu live_payload=%zu ratio=%.1f\n",
         Chunk, n, w, s, CountingHeap::peak, w * s, (double)CountingHeap::peak / (w * s));
}
void malloc_fifo(size_t n, size_t w, size_t s) {
  struct mallinfo2 m0 = mallinfo2();
  std::vector<char*> ring(w, nullptr);
  size_t peak = 0;
  for (size_t i = 0; i < n; i++) {
    size_t k = i % w; if (ring[k]) ::free(ring[k]); ring[k] = (char*)::malloc(s); ring[k][0] = 1;
    if ((i & 1023) == 0) { struct mallinfo2 m = mallinfo2(); size_t u = m.uordblks - m0.uordblks; if (u > peak) peak = u; }
  }
  printf("glibc fifo n=%zu w=%zu s=%zu sampled_peak_in_use=%zu live_payload=%zu ratio=%.2f\n", n, w, s, peak, w * s, (double)peak / (w * s));
  for (auto p : ring) ::free(p);
}

// Mixed sizes: tail waste when a request does not fit the current arena.
template <size_t Chunk>
void zone_mixed(size_t n) {
  CountingHeap::outstanding = CountingHeap::peak = CountingHeap::calls = 0;
  Zone<Chunk> z; size_t req = 0; unsigned x = 12345;
  for (size_t i = 0; i < n; i++) { x = x * 1103515245u + 12345u; size_t s = 16 + (x >> 8) % 4081; req += s; z.malloc(s); }
  printf("zone  mixed chunk=%zu n=%zu requested=%zu superheap_peak=%zu overhead=%.2f%%\n", Chunk, n, req, CountingHeap::peak, 100.0 * (CountingHeap::peak - req) / req);
}

int main() {
  const size_t N = 10000000;
  for (size_t s : {8, 16, 24, 40}) { zone_bulk<65536>(N, s, "64KiB"); malloc_bulk(N, s); }
  zone_bulk<8192>(N, 24, "8KiB");
  zone_bulk<1048576>(N, 24, "1MiB");
  zone_fifo<65536>(N, 1000, 24);
  malloc_fifo(N, 1000, 24);
  zone_mixed<8192>(200000); zone_mixed<65536>(200000); zone_mixed<1048576>(200000);
  return 0;
}
