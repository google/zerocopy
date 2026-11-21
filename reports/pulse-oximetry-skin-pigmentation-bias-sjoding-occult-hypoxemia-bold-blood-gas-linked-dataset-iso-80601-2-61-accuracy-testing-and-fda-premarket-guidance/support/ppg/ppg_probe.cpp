// Host harness: feeds synthetic photoplethysmograms with a known ratio-of-ratios R to the
// two unmodified SpO2 routines of aromring/MAX30102_by_RF @ 553ba61952012ad6e895532bb2bfda0e790a3beb
// (algorithm.cpp: maxim_heart_rate_and_oxygen_saturation; algorithm_by_RF.cpp:
// rf_heart_rate_and_oxygen_saturation). Inputs are SYNTHETIC; no human data is used.
//
// Signal model (per sample i, FS = 25 Hz, 100 samples = 4 s):
//   p(t)   = pulse shape in [0,1]: 0.5*(1-cos(2*pi*f*t)) + 0.25*max(0, sin(4*pi*f*t)) normalised
//   IR(t)  = DC_ir  * (1 - PI      * p(t)) + drift(t) + noise
//   RED(t) = DC_red * (1 - R * PI  * p(t)) + drift(t)*DC_red/DC_ir + noise
// so (AC_red/DC_red)/(AC_ir/DC_ir) = R exactly for the noiseless, drift-free signal.
// Reference curve shared by both routines: f(R) = -45.060 R^2 + 30.354 R + 94.845.
//
// Usage: ppg_probe <R> <PI> <noise_sd_counts> <drift_amp_over_AC> <hr_bpm> <dc_ir> <batches> <seed>
#include <cstdio>
#include <cstdlib>
#include <cmath>
#include <cstdint>
#include <random>
#include <string>

void maxim_heart_rate_and_oxygen_saturation(uint32_t *pun_ir_buffer, int32_t n_ir_buffer_length, uint32_t *pun_red_buffer,
                                            float *pn_spo2, int8_t *pch_spo2_valid, int32_t *pn_heart_rate, int8_t *pch_hr_valid);
void rf_heart_rate_and_oxygen_saturation(uint32_t *pun_ir_buffer, int32_t n_ir_buffer_length, uint32_t *pun_red_buffer,
                                         float *pn_spo2, int8_t *pch_spo2_valid, int32_t *pn_heart_rate, int8_t *pch_hr_valid,
                                         float *ratio, float *correl);

int main(int argc, char **argv) {
  if (argc != 9) { std::fprintf(stderr, "usage\n"); return 2; }
  const double R = atof(argv[1]), PI_ = atof(argv[2]), sd = atof(argv[3]), drift = atof(argv[4]);
  const double hr = atof(argv[5]), dc_ir = atof(argv[6]);
  const int batches = atoi(argv[7]);
  const unsigned seed = (unsigned)atoi(argv[8]);
  const double dc_red = dc_ir * 118545.0 / 131500.0;  // ratio of the first row of ExpectedGoodQualitySignals.csv
  const int N = 100, FSR = 25;
  const double f = hr / 60.0, PIx = 3.14159265358979323846;
  std::mt19937 rng(seed);
  std::normal_distribution<double> g(0.0, 1.0);
  // normalise pulse shape to [0,1]
  double pmin = 1e9, pmax = -1e9;
  for (int i = 0; i < 1000; ++i) {
    double t = i / 1000.0 / f;
    double p = 0.5 * (1 - cos(2 * PIx * f * t)) + 0.25 * fmax(0.0, sin(4 * PIx * f * t));
    pmin = fmin(pmin, p); pmax = fmax(pmax, p);
  }
  const double fR = (-45.060 * R + 30.354) * R + 94.845;
  int m_valid = 0, r_valid = 0, m_neg = 0, r_neg = 0;
  double m_abs = 0, r_abs = 0;
  uint32_t ir[100], red[100];
  double t0 = 0;
  for (int b = 0; b < batches; ++b) {
    for (int i = 0; i < N; ++i) {
      double t = t0 + (double)i / FSR;
      double p = (0.5 * (1 - cos(2 * PIx * f * t)) + 0.25 * fmax(0.0, sin(4 * PIx * f * t)) - pmin) / (pmax - pmin);
      double ac = dc_ir * PI_;
      double d = drift * ac * sin(2 * PIx * 0.3 * t);
      double vi = dc_ir * (1 - PI_ * p) + d + sd * g(rng);
      double vr = dc_red * (1 - R * PI_ * p) + d * dc_red / dc_ir + sd * g(rng);
      ir[i] = (uint32_t)llround(fmax(0.0, vi));
      red[i] = (uint32_t)llround(fmax(0.0, vr));
    }
    t0 += (double)N / FSR;
    float s1, s2, ratio = 0, correl = 0; int8_t v1, v2, h1, h2; int32_t hr1, hr2;
    maxim_heart_rate_and_oxygen_saturation(ir, N, red, &s1, &v1, &hr1, &h1);
    rf_heart_rate_and_oxygen_saturation(ir, N, red, &s2, &v2, &hr2, &h2, &ratio, &correl);
    if (v1 == 1) { ++m_valid; m_abs += fabs(s1 - fR); if (s1 < 0) ++m_neg; }
    if (v2 == 1) { ++r_valid; r_abs += fabs(s2 - fR); if (s2 < 0) ++r_neg; }
    if (b == 0) {
      std::printf("first_batch maxim spo2=%.3f valid=%d hr=%d hr_valid=%d | rf spo2=%.3f valid=%d hr=%d hr_valid=%d correl=%.3f\n",
                  s1, v1, hr1, h1, s2, v2, hr2, h2, correl);
    }
  }
  std::printf("R=%.3f PI=%.4f sd=%.1f drift=%.2f hr=%.0f dc_ir=%.0f f(R)=%.3f | maxim valid=%d/%d mae=%s neg=%d | rf valid=%d/%d mae=%s neg=%d\n",
              R, PI_, sd, drift, hr, dc_ir, fR, m_valid, batches,
              m_valid ? std::to_string(m_abs / m_valid).c_str() : "n/a", m_neg,
              r_valid, batches, r_valid ? std::to_string(r_abs / r_valid).c_str() : "n/a", r_neg);
  return 0;
}
