// Dynamic-storage-allocation probe.
//
// Compares, on small synthetic instances:
//   LOAD  - max over time of the summed sizes of simultaneously live buffers
//           (for interval instances) or the maximum-weight clique of the
//           conflict graph (for the fork-join model);
//   OPT   - exact optimum, computed as the minimum over all placement orders
//           of first-fit placement (see the argument in REPORT.md);
//   TFLM  - the upstream tflite-micro GreedyMemoryPlanner (size-descending
//           first fit), compiled unmodified from the pinned revision;
//   BFD   - a re-implementation of the size-descending best-fit gap rule
//           (the rule used by the TFLite CPU arena planner, the TFLite GPU
//           greedy-by-size offset planner and XLA's spatial heap ordering);
//   BFS   - the same best-fit gap rule applied in start-time order (the order
//           in which IREE packs static slices).
// BFD and BFS are re-implementations, not the upstream code.
//
// Usage: dsa_probe stats | examples | timing
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <numeric>
#include <string>
#include <vector>

#include "tensorflow/lite/micro/memory_planner/greedy_memory_planner.h"

namespace {

struct Rng {  // splitmix64
  uint64_t s;
  explicit Rng(uint64_t seed) : s(seed) {}
  uint64_t next() {
    uint64_t z = (s += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
  }
  int range(int lo, int hi) {  // inclusive
    return lo + static_cast<int>(next() % static_cast<uint64_t>(hi - lo + 1));
  }
};

struct Buf {
  int size;
  int start;  // inclusive
  int end;    // inclusive
};

using Conflict = std::vector<std::vector<bool>>;

Conflict IntervalConflicts(const std::vector<Buf>& b) {
  const int n = static_cast<int>(b.size());
  Conflict c(n, std::vector<bool>(n, false));
  for (int i = 0; i < n; ++i)
    for (int j = 0; j < n; ++j)
      c[i][j] = i != j && b[i].start <= b[j].end && b[j].start <= b[i].end;
  return c;
}

long IntervalLoad(const std::vector<Buf>& b) {
  int tmax = 0;
  for (const Buf& x : b) tmax = std::max(tmax, x.end);
  long best = 0;
  for (int t = 0; t <= tmax; ++t) {
    long s = 0;
    for (const Buf& x : b)
      if (x.start <= t && t <= x.end) s += x.size;
    best = std::max(best, s);
  }
  return best;
}

long MaxWeightClique(const std::vector<int>& sz, const Conflict& c) {
  const int n = static_cast<int>(sz.size());
  long best = 0;
  for (uint32_t m = 1; m < (1u << n); ++m) {
    bool ok = true;
    long s = 0;
    for (int i = 0; i < n && ok; ++i) {
      if (!(m >> i & 1)) continue;
      s += sz[i];
      for (int j = i + 1; j < n; ++j)
        if ((m >> j & 1) && !c[i][j]) { ok = false; break; }
    }
    if (ok) best = std::max(best, s);
  }
  return best;
}

// Places items in `order` at the lowest offset that avoids every
// already-placed conflicting item. Returns the makespan.
long FirstFit(const std::vector<int>& order, const std::vector<int>& sz,
              const Conflict& c, std::vector<long>* off_out = nullptr,
              long cutoff = -1) {
  const int n = static_cast<int>(sz.size());
  std::vector<long> off(n, -1);
  long makespan = 0;
  std::vector<std::pair<long, long>> used;
  for (int i : order) {
    used.clear();
    for (int j = 0; j < n; ++j)
      if (off[j] >= 0 && c[i][j]) used.push_back({off[j], off[j] + sz[j]});
    std::sort(used.begin(), used.end());
    long cand = 0;
    for (const auto& u : used) {
      if (u.first - cand >= sz[i]) break;
      cand = std::max(cand, u.second);
    }
    off[i] = cand;
    makespan = std::max(makespan, cand + sz[i]);
    if (cutoff >= 0 && makespan >= cutoff) return makespan;
  }
  if (off_out) *off_out = off;
  return makespan;
}

long Opt(const std::vector<int>& sz, const Conflict& c,
         std::vector<long>* off_out = nullptr) {
  std::vector<int> order(sz.size());
  std::iota(order.begin(), order.end(), 0);
  long best = -1;
  do {
    std::vector<long> off;
    long m = FirstFit(order, sz, c, &off, best);
    if (best < 0 || m < best) {
      best = m;
      if (off_out && !off.empty()) *off_out = off;
    }
  } while (std::next_permutation(order.begin(), order.end()));
  return best;
}

// Best-fit gap rule: among gaps between conflicting placed items (ordered by
// offset) that fit, choose the smallest; otherwise place after the highest
// conflicting item.
long BestFit(const std::vector<int>& order, const std::vector<int>& sz,
             const Conflict& c, std::vector<long>* off_out = nullptr) {
  const int n = static_cast<int>(sz.size());
  std::vector<long> off(n, -1);
  long makespan = 0;
  for (int i : order) {
    std::vector<std::pair<long, long>> used;
    for (int j = 0; j < n; ++j)
      if (off[j] >= 0 && c[i][j]) used.push_back({off[j], off[j] + sz[j]});
    std::sort(used.begin(), used.end());
    long cur = 0, best = -1, best_gap = -1;
    for (const auto& u : used) {
      if (u.first >= cur) {
        long gap = u.first - cur;
        if (gap >= sz[i] && (best_gap < 0 || gap < best_gap)) {
          best_gap = gap;
          best = cur;
        }
      }
      cur = std::max(cur, u.second);
    }
    if (best < 0) best = cur;
    off[i] = best;
    makespan = std::max(makespan, best + sz[i]);
  }
  if (off_out) *off_out = off;
  return makespan;
}

std::vector<int> Sizes(const std::vector<Buf>& b) {
  std::vector<int> s;
  for (const Buf& x : b) s.push_back(x.size);
  return s;
}

std::vector<int> OrderBySizeDesc(const std::vector<Buf>& b) {
  std::vector<int> o(b.size());
  std::iota(o.begin(), o.end(), 0);
  std::stable_sort(o.begin(), o.end(), [&](int x, int y) {
    if (b[x].size != b[y].size) return b[x].size > b[y].size;
    return (b[x].end - b[x].start) > (b[y].end - b[y].start);
  });
  return o;
}

std::vector<int> OrderByStart(const std::vector<Buf>& b) {
  std::vector<int> o(b.size());
  std::iota(o.begin(), o.end(), 0);
  std::stable_sort(o.begin(), o.end(), [&](int x, int y) {
    if (b[x].start != b[y].start) return b[x].start < b[y].start;
    return b[x].end < b[y].end;
  });
  return o;
}

// Runs the upstream planner and checks its own overlap validator.
long Tflm(const std::vector<Buf>& b, std::vector<long>* off_out = nullptr,
          bool* overlap = nullptr) {
  const size_t need = b.size() * tflite::GreedyMemoryPlanner::per_buffer_size();
  std::vector<unsigned char> scratch(need + 64);
  tflite::GreedyMemoryPlanner p;
  if (p.Init(scratch.data(), static_cast<int>(scratch.size())) != kTfLiteOk)
    std::abort();
  for (const Buf& x : b)
    if (p.AddBuffer(x.size, x.start, x.end) != kTfLiteOk) std::abort();
  long m = static_cast<long>(p.GetMaximumMemorySize());
  if (off_out) {
    off_out->assign(b.size(), 0);
    for (size_t i = 0; i < b.size(); ++i) {
      int o = 0;
      p.GetOffsetForBuffer(static_cast<int>(i), &o);
      (*off_out)[i] = o;
    }
  }
  if (overlap) *overlap = p.DoAnyBuffersOverlap();
  return m;
}

// True if the graph contains an induced path on four vertices (so it is not
// a cograph).
bool HasInducedP4(const Conflict& c) {
  const int n = static_cast<int>(c.size());
  for (int a = 0; a < n; ++a)
    for (int b = 0; b < n; ++b)
      for (int d = 0; d < n; ++d)
        for (int e = 0; e < n; ++e) {
          if (a == b || a == d || a == e || b == d || b == e || d == e) continue;
          if (c[a][b] && c[b][d] && c[d][e] && !c[a][d] && !c[a][e] && !c[b][e])
            return true;
        }
  return false;
}

bool ValidUnder(const std::vector<long>& off, const std::vector<int>& sz,
                const Conflict& c) {
  const int n = static_cast<int>(sz.size());
  for (int i = 0; i < n; ++i)
    for (int j = i + 1; j < n; ++j)
      if (c[i][j] && off[i] < off[j] + sz[j] && off[j] < off[i] + sz[i])
        return false;
  return true;
}

// ---- instance families -------------------------------------------------

int Size(Rng& r) { return r.range(1, 100); }

std::vector<Buf> RandomIntervals(Rng& r, int n, int T) {
  std::vector<Buf> b;
  for (int i = 0; i < n; ++i) {
    int s = r.range(0, T - 1);
    int e = std::min(T - 1, s + r.range(0, T / 2));
    b.push_back({Size(r), s, e});
  }
  return b;
}

// Laminar family: every pair of intervals is nested or disjoint.
void LaminarRec(Rng& r, int lo, int hi, int& left, std::vector<Buf>& out) {
  if (left <= 0 || lo > hi) return;
  out.push_back({Size(r), lo, hi});
  --left;
  if (hi - lo < 1 || left <= 0) return;
  int k = r.range(1, 3);
  int cur = lo;
  for (int c = 0; c < k && cur <= hi && left > 0; ++c) {
    int s = r.range(cur, hi);
    int e = r.range(s, hi);
    if (s == lo && e == hi) { if (s < e) e--; else break; }
    LaminarRec(r, s, e, left, out);
    cur = e + 1;
  }
}
std::vector<Buf> Laminar(Rng& r, int n, int T) {
  std::vector<Buf> b;
  while (static_cast<int>(b.size()) < n) {
    int left = n - static_cast<int>(b.size());
    int s = r.range(0, T - 1), e = r.range(s, T - 1);
    std::vector<Buf> add;
    LaminarRec(r, s, e, left, add);
    // keep laminarity w.r.t. existing roots: accept only if each new interval
    // is nested in or disjoint from every existing one
    bool ok = true;
    for (const Buf& x : add)
      for (const Buf& y : b) {
        bool disj = x.end < y.start || y.end < x.start;
        bool nest = (x.start >= y.start && x.end <= y.end) ||
                    (y.start >= x.start && y.end <= x.end);
        if (!disj && !nest) ok = false;
      }
    if (ok) b.insert(b.end(), add.begin(), add.end());
  }
  b.resize(n);
  return b;
}

// Chain with skip connections: buffer i is produced at step i and last used
// at step i+1, or at step i+k for a residual edge.
std::vector<Buf> ChainSkip(Rng& r, int n) {
  std::vector<Buf> b;
  for (int i = 0; i < n; ++i) {
    int k = (r.range(0, 3) == 0) ? r.range(2, 4) : 1;
    b.push_back({Size(r), i, i + k});
  }
  return b;
}

// Fork-join (series-parallel) task graph with m tasks. Returns reachability.
struct SP {
  int m = 0;
  std::vector<std::vector<bool>> lt;  // lt[a][b]: a strictly precedes b
};
// Builds an SP graph recursively; returns (sources, sinks) of the sub-graph.
std::pair<std::vector<int>, std::vector<int>> SpRec(Rng& r, int tasks, SP& g,
                                                    std::vector<std::pair<int,int>>& edges) {
  if (tasks == 1) {
    int id = g.m++;
    return {{id}, {id}};
  }
  int a = r.range(1, tasks - 1);
  auto L = SpRec(r, a, g, edges);
  auto R = SpRec(r, tasks - a, g, edges);
  if (r.range(0, 1) == 0) {  // series
    for (int x : L.second)
      for (int y : R.first) edges.push_back({x, y});
    return {L.first, R.second};
  }
  std::vector<int> src = L.first, snk = L.second;  // parallel
  src.insert(src.end(), R.first.begin(), R.first.end());
  snk.insert(snk.end(), R.second.begin(), R.second.end());
  return {src, snk};
}
SP RandomSP(Rng& r, int tasks) {
  SP g;
  std::vector<std::pair<int, int>> edges;
  SpRec(r, tasks, g, edges);
  g.lt.assign(g.m, std::vector<bool>(g.m, false));
  for (auto e : edges) g.lt[e.first][e.second] = true;
  for (int k = 0; k < g.m; ++k)
    for (int i = 0; i < g.m; ++i)
      for (int j = 0; j < g.m; ++j)
        if (g.lt[i][k] && g.lt[k][j]) g.lt[i][j] = true;
  return g;
}
std::vector<int> TopoOrder(Rng& r, const SP& g) {  // random linear extension
  std::vector<int> order, indeg(g.m, 0);
  std::vector<bool> done(g.m, false);
  while (static_cast<int>(order.size()) < g.m) {
    std::vector<int> ready;
    for (int v = 0; v < g.m; ++v) {
      if (done[v]) continue;
      bool ok = true;
      for (int u = 0; u < g.m; ++u)
        if (!done[u] && g.lt[u][v]) ok = false;
      if (ok) ready.push_back(v);
    }
    int v = ready[r.range(0, static_cast<int>(ready.size()) - 1)];
    done[v] = true;
    order.push_back(v);
  }
  return order;
}

struct Stat {
  int count = 0, opt_eq_load = 0, tflm_eq_opt = 0, bfd_eq_opt = 0,
      bfs_eq_opt = 0, tflm_invalid = 0;
  double sum_opt_load = 0, max_opt_load = 0, sum_tflm = 0, max_tflm = 0,
         sum_bfd = 0, max_bfd = 0, sum_bfs = 0, max_bfs = 0;
  void Add(long load, long opt, long tflm, long bfd, long bfs) {
    ++count;
    double ol = double(opt) / load, t = double(tflm) / opt,
           d = double(bfd) / opt, s = double(bfs) / opt;
    opt_eq_load += opt == load;
    tflm_eq_opt += tflm == opt;
    bfd_eq_opt += bfd == opt;
    bfs_eq_opt += bfs == opt;
    sum_opt_load += ol; max_opt_load = std::max(max_opt_load, ol);
    sum_tflm += t; max_tflm = std::max(max_tflm, t);
    sum_bfd += d; max_bfd = std::max(max_bfd, d);
    sum_bfs += s; max_bfs = std::max(max_bfs, s);
  }
  void Print(const char* name) const {
    std::printf(
        "%-18s n=%d  OPT==LOAD %d/%d  OPT/LOAD mean %.4f max %.4f | "
        "TFLM==OPT %d  TFLM/OPT mean %.4f max %.4f | BFD==OPT %d  BFD/OPT "
        "mean %.4f max %.4f | BFS==OPT %d  BFS/OPT mean %.4f max %.4f | "
        "TFLM self-overlap %d\n",
        name, count, opt_eq_load, count, sum_opt_load / count, max_opt_load,
        tflm_eq_opt, sum_tflm / count, max_tflm, bfd_eq_opt, sum_bfd / count,
        max_bfd, bfs_eq_opt, sum_bfs / count, max_bfs, tflm_invalid);
  }
};

void RunInterval(const char* name, int N, int n, uint64_t seed, int family) {
  Rng r(seed);
  Stat st;
  for (int k = 0; k < N; ++k) {
    std::vector<Buf> b = family == 0   ? RandomIntervals(r, n, 12)
                         : family == 1 ? Laminar(r, n, 16)
                                       : ChainSkip(r, n);
    Conflict c = IntervalConflicts(b);
    std::vector<int> sz = Sizes(b);
    long load = IntervalLoad(b);
    long opt = Opt(sz, c);
    bool overlap = false;
    std::vector<long> toff;
    long tflm = Tflm(b, &toff, &overlap);
    if (overlap || !ValidUnder(toff, sz, c)) st.tflm_invalid++;
    long bfd = BestFit(OrderBySizeDesc(b), sz, c);
    long bfs = BestFit(OrderByStart(b), sz, c);
    if (opt < load) std::printf("BUG: opt < load\n");
    st.Add(load, opt, tflm, bfd, bfs);
  }
  st.Print(name);
}

void RunForkJoin(int N, int n, int tasks, uint64_t seed) {
  Rng r(seed);
  int invalid = 0, opt_par_eq_mwc = 0, tflm_par_valid_eq = 0, non_cograph = 0;
  double sum_cost = 0, max_cost = 0, sum_om = 0, max_om = 0;
  for (int k = 0; k < N; ++k) {
    SP g = RandomSP(r, tasks);
    // buffers: producer p, last consumer c with p == c or p < c
    std::vector<int> prod, cons, sz;
    for (int i = 0; i < n; ++i) {
      int p = r.range(0, g.m - 1);
      std::vector<int> cands = {p};
      for (int v = 0; v < g.m; ++v)
        if (g.lt[p][v]) cands.push_back(v);
      int c = cands[r.range(0, static_cast<int>(cands.size()) - 1)];
      prod.push_back(p); cons.push_back(c); sz.push_back(Size(r));
    }
    // conflict under parallel execution with arbitrary task durations
    Conflict par(n, std::vector<bool>(n, false));
    for (int i = 0; i < n; ++i)
      for (int j = 0; j < n; ++j)
        par[i][j] = i != j && !g.lt[cons[i]][prod[j]] && !g.lt[cons[j]][prod[i]];
    // one sequential schedule (random linear extension, atomic tasks)
    std::vector<int> topo = TopoOrder(r, g), pos(g.m);
    for (int t = 0; t < g.m; ++t) pos[topo[t]] = t;
    std::vector<Buf> seq;
    for (int i = 0; i < n; ++i) seq.push_back({sz[i], pos[prod[i]], pos[cons[i]]});
    Conflict sc = IntervalConflicts(seq);
    std::vector<long> toff;
    long tflm_seq = Tflm(seq, &toff);
    if (!ValidUnder(toff, sz, par)) invalid++;
    long opt_seq = Opt(sz, sc);
    long opt_par = Opt(sz, par);
    long mwc = MaxWeightClique(sz, par);
    non_cograph += HasInducedP4(par);
    opt_par_eq_mwc += opt_par == mwc;
    double cost = double(opt_par) / opt_seq, om = double(opt_par) / mwc;
    sum_cost += cost; max_cost = std::max(max_cost, cost);
    sum_om += om; max_om = std::max(max_om, om);
    (void)tflm_seq; (void)tflm_par_valid_eq;
  }
  std::printf(
      "fork-join          n=%d tasks=%d  single-schedule TFLM plan invalid "
      "under parallel execution: %d/%d | OPT_par/OPT_seq mean %.4f max %.4f | "
      "OPT_par==MWC %d/%d  OPT_par/MWC mean %.4f max %.4f | parallel conflict "
      "graph not a cograph (has induced P4): %d/%d\n",
      N, tasks, invalid, N, sum_cost / N, max_cost, opt_par_eq_mwc, N,
      sum_om / N, max_om, non_cograph, N);
}

void PrintInst(const char* label, const std::vector<Buf>& b) {
  std::printf("%s:", label);
  for (const Buf& x : b) std::printf(" (size=%d,[%d,%d])", x.size, x.start, x.end);
  std::printf("\n");
}

void Examples() {
  // Smallest random interval instance (fewest buffers, then smallest total
  // size) found with OPT > LOAD; then one where TFLM > OPT; then BFD > OPT.
  Rng r(7);
  bool found[3] = {false, false, false};
  for (int n = 3; n <= 6; ++n) {
    for (int k = 0; k < 400000 && !(found[0] && found[1] && found[2]); ++k) {
      std::vector<Buf> b;
      for (int i = 0; i < n; ++i) {
        int s = r.range(0, 5), e = r.range(s, 5);
        b.push_back({r.range(1, 6), s, e});
      }
      Conflict c = IntervalConflicts(b);
      std::vector<int> sz = Sizes(b);
      long load = IntervalLoad(b), opt = Opt(sz, c);
      long tflm = Tflm(b), bfd = BestFit(OrderBySizeDesc(b), sz, c);
      if (!found[0] && opt > load) {
        found[0] = true;
        PrintInst("OPT>LOAD", b);
        std::printf("  LOAD=%ld OPT=%ld TFLM=%ld BFD=%ld\n", load, opt, tflm, bfd);
      }
      if (!found[1] && tflm > opt) {
        found[1] = true;
        PrintInst("TFLM>OPT", b);
        std::printf("  LOAD=%ld OPT=%ld TFLM=%ld BFD=%ld\n", load, opt, tflm, bfd);
      }
      if (!found[2] && bfd > opt) {
        found[2] = true;
        PrintInst("BFD>OPT", b);
        std::printf("  LOAD=%ld OPT=%ld TFLM=%ld BFD=%ld\n", load, opt, tflm, bfd);
      }
    }
  }
}

void Timing() {
  std::printf("per_buffer_size (bytes of planner scratch per buffer): %zu\n",
              tflite::GreedyMemoryPlanner::per_buffer_size());
  for (int n : {250, 1000, 4000}) {
    Rng r(1000 + n);
    std::vector<Buf> b = RandomIntervals(r, n, n);
    for (Buf& x : b) x.size = r.range(1, 1 << 20);
    auto t0 = std::chrono::steady_clock::now();
    long m = Tflm(b);
    auto t1 = std::chrono::steady_clock::now();
    std::vector<int> sz = Sizes(b);
    std::printf("TFLM n=%d  plan_ms=%.2f  arena=%ld  LOAD=%ld  ratio=%.4f\n", n,
                std::chrono::duration<double, std::milli>(t1 - t0).count(), m,
                IntervalLoad(b), double(m) / IntervalLoad(b));
  }
}

}  // namespace

int main(int argc, char** argv) {
  std::string mode = argc > 1 ? argv[1] : "stats";
  if (mode == "stats") {
    RunInterval("random-intervals", 2000, 8, 1, 0);
    RunInterval("laminar", 2000, 8, 2, 1);
    RunInterval("chain+skip", 2000, 8, 3, 2);
    RunForkJoin(2000, 7, 6, 4);
  } else if (mode == "forkjoin") {
    RunForkJoin(2000, 7, 6, 4);
  } else if (mode == "examples") {
    Examples();
  } else if (mode == "timing") {
    Timing();
  }
  return 0;
}
