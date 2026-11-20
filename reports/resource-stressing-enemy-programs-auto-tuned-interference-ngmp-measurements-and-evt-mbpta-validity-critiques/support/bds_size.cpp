// Empirical size (false-rejection rate under H0: i.i.d. data) of chronovise's
// TestBDS at alpha = 0.05.  Links against either the unmodified library built
// from federeghe/chronovise @ 4b332f10669af73f33e00f8749040eed9601bfb2, or a
// library whose src/statistical/test_bds.cpp was patched with
// bds_patch_coefficient_only.diff (embedding_dimension_1 normaliser) or
// bds_patch.diff (normaliser + embedding_dimension starting at s = m).
// Data: i.i.d. Gamma(shape 4, scale 5) + 1000, N(0,1), or N(0,1) + 1000, drawn
// with std::mt19937_64 and fixed seeds (synthetic; not timing measurements).
//
// Usage: ./bds_size <n> <replicates> [gamma|normal|normal1000]   (default gamma)
//        ./bds_size unit                               (the 100-value i.i.d. normal
//          sample from tests/test_test_bds.cpp, test DistributionACCEPT)
#include "measures_pool.hpp"
#include "statistical/test_bds.hpp"
#include <cstdio>
#include <cstdlib>
#include <random>
#include <string>

using namespace chronovise;

static const double kUnit[100] = {
1.8339,-2.2588,0.8622,0.3188,-1.3077,-0.4336,0.3426,3.5784,2.7694,-1.3499,3.0349,0.7254,-0.0631,0.7147,-0.2050,-0.1241,1.4897,1.4090,1.4172,0.6715,-1.2075,0.7172,1.6302,0.4889,1.0347,0.7269,-0.3034,0.2939,-0.7873,0.8884,-1.1471,-1.0689,-0.8095,-2.9443,1.4384,0.3252,-0.7549,1.3703,-1.7115,-0.1022,-0.2414,0.3192,0.3129,-0.8649,-0.0301,-0.1649,0.6277,1.0933,1.1093,-0.8637,0.0774,-1.2141,-1.1135,-0.0068,1.5326,-0.7697,0.3714,-0.2256,1.1174,-1.0891,0.0326,0.5525,1.1006,1.5442,0.0859,-1.4916,-0.7423,-1.0616,2.3505,-0.6156,0.7481,-0.1924,0.8886,-0.7648,-1.4023,-1.4224,0.4882,-0.1774,-0.1961,1.4193,0.2916,0.1978,1.5877,-0.8045,0.6966,0.8351,-0.2437,0.2157,-1.1658,-1.1480,0.1049,0.7223,2.5855,-0.6669,0.1873,-0.0825,-1.9330,-0.4390,-1.7947,0.8404};

int main(int argc, char** argv) {
    if (std::string(argv[1]) == "unit") {
        MeasuresPool<unsigned int, double> mp;
        for (int i = 0; i < 100; i++) mp.push(i, kUnit[i]);
        TestBDS<unsigned int, double> bds(0.05);
        bds.run(mp);
        std::printf("unit-test sample: W=%.4f reject=%s\n", bds.get_statistic(), bds.is_reject() ? "YES" : "no");
        return 0;
    }
    const std::string dist = argc > 3 ? argv[3] : "gamma";
    const bool normal = dist != "gamma";
    const double shift = dist == "normal1000" ? 1000.0 : 0.0;
    const unsigned n = std::atoi(argv[1]);
    const unsigned reps = std::atoi(argv[2]);
    unsigned rejections = 0;
    double sum_stat = 0.0;
    for (unsigned r = 0; r < reps; ++r) {
        std::mt19937_64 gen(1000003ULL * (r + 1));
        std::gamma_distribution<double> g(4.0, 5.0);
        std::normal_distribution<double> nd(0.0, 1.0);
        MeasuresPool<int, double> mp;
        for (unsigned i = 0; i < n; ++i) mp.push(0, normal ? shift + nd(gen) : 1000.0 + g(gen));
        TestBDS<int, double> bds(0.05);
        bds.run(mp);
        rejections += bds.is_reject() ? 1 : 0;
        sum_stat += bds.get_statistic();
    }
    std::printf("%s n=%u reps=%u rejections=%u rate=%.3f mean|W|=%.3f\n", dist.c_str(), n, reps, rejections,
                double(rejections) / reps, sum_stat / reps);
    return 0;
}
