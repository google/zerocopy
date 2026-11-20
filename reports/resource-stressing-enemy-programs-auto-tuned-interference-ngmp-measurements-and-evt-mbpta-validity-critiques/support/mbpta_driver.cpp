// Driver for chronovise (federeghe/chronovise @ 4b332f10669af73f33e00f8749040eed9601bfb2):
// runs the library's own i.i.d./stationarity tests, block-maxima + PWM GEV fit and
// post-EVT goodness-of-fit tests on a column of synthetic "execution times" read
// from a text file.  Inputs are synthetic (see gen_samples.py); nothing here is a
// hardware measurement.
//
// Build (no ceres-solver; PWM estimator only):
//   g++ -std=c++14 -O2 -include cstdint -I<chronovise>/include mbpta_driver.cpp libchronovise.a
// Usage: ./mbpta_driver <file> <block_size> <exceedance-per-block>
#include "measures_pool.hpp"
#include "statistical/test_ljung_box.hpp"
#include "statistical/test_kpss.hpp"
#include "statistical/test_rs.hpp"
#include "statistical/test_bds.hpp"
#include "statistical/test_ks.hpp"
#include "statistical/test_cvm.hpp"
#include "statistical/test_ad.hpp"
#include "statistical/estimator_pwm.hpp"
#include "evt/evtapproach_bm.hpp"
#include "evt/gev_distribution.hpp"

#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <memory>
#include <string>

using namespace chronovise;

template <class T>
static void report(const char* name, T& t, const MeasuresPool<int, double>& mp) {
    try {
        t.run(mp);
        std::printf("  %-22s stat=%12.5g crit=%12.5g reject=%s\n", name, t.get_statistic(),
                    t.get_critical_value(), t.is_reject() ? "YES" : "no");
    } catch (const std::exception& e) {
        std::printf("  %-22s EXCEPTION: %s\n", name, e.what());
    }
}

int main(int argc, char** argv) {
    if (argc < 4) { std::fprintf(stderr, "usage: %s file block_size p\n", argv[0]); return 2; }
    const size_t bs = std::strtoul(argv[2], nullptr, 10);
    const double p = std::strtod(argv[3], nullptr);
    MeasuresPool<int, double> mp;
    std::ifstream in(argv[1]);
    double v;
    while (in >> v) mp.push(0, v);
    std::printf("file=%s n=%zu max_observed=%.6g block=%zu\n", argv[1], mp.size(), mp.max(), bs);

    std::printf(" sample tests (alpha=0.05):\n");
    TestLjungBox<int, double> lb(0.05, 20);   report("Ljung-Box(lags=20)", lb, mp);
    TestKPSS<int, double> kpss(0.05, 20);     report("KPSS(level,lags=20)", kpss, mp);
    TestRS<int, double> rs(0.05);             report("R/S", rs, mp);
    if (mp.size() <= 1000) { TestBDS<int, double> bds(0.05); report("BDS", bds, mp); }
    else std::printf("  %-22s skipped (TestBDS::k is an O(n^3) triple loop; n>1000)\n", "BDS");

    MeasuresPoolSet<int, double> mps(mp, 0.5f);
    EVTApproach_BM<int, double> bm(bs);
    bm.perform(mps);
    auto& train = bm.get_training_pool();
    auto& test = bm.get_test_pool();
    Estimator_PWM<int, double> est;
    est.set_source_evt_approach(&typeid(bm));  // as AbstractExecutionContext does (src/aec.cpp:40)
    if (!est.run(train)) { std::printf(" PWM estimator failed\n"); return 1; }
    auto dist = est.get_result();
    auto gev = std::dynamic_pointer_cast<GEV_Distribution>(dist);
    std::printf(" GEV(PWM) on %zu block maxima: loc=%.6g scale=%.6g shape(xi)=%.4g\n", train.size(),
                gev->get_location(), gev->get_scale(), gev->get_shape());
    std::printf(" post-EVT tests on %zu held-out block maxima (alpha=0.05):\n", test.size());
    {
        TestKS<int, double> ks(0.05, distribution_t::EVT_GEV);
        ks.set_ref_distribution(dist); report("KS", ks, test);
        TestCvM<int, double> cvm(0.05, distribution_t::EVT_GEV);
        cvm.set_ref_distribution(dist); report("CvM", cvm, test);
        TestAD<int, double> ad(0.05, distribution_t::EVT_GEV, false);
        ad.set_ref_distribution(dist); report("AD", ad, test);
    }
    std::printf(" pWCET at per-block exceedance %.1e : %.6g\n", p, dist->quantile(1.0 - p));
    return 0;
}
