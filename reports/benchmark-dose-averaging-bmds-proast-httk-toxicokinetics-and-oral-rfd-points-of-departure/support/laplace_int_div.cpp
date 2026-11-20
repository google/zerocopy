// Expression-semantics probe for the Laplace log-evidence term used in
// USEPA/BMDS revision 0018abea713f61b0bcc9dd30821af18b61a77e77,
// src/bmdscore/dichotomous_entry_code.cpp lines 612-613:
//
//     temp = res->models[i]->nparms / 2 * log(2 * M_PI) - res->models[i]->max +
//            0.5 * log(max(0.0, cov.determinant()));
//
// where src/bmdscore/bmdStruct.h line 109 declares `int nparms;`.
// Contrast src/bmdscore/bmds_helper.cpp line 1148 (BIC_equiv), which writes
// `res->nparms / 2.0 * log(2.0 * M_PI)`.
//
// This program does NOT build or run BMDS. It only evaluates the same C++
// expression shapes with the same operand types, to show the value of the
// k/2*log(2*pi) term under integer versus floating division.
#include <cmath>
#include <cstdio>

int main() {
  for (int nparms = 1; nparms <= 4; ++nparms) {
    double int_div = nparms / 2 * log(2 * M_PI);      // shape at line 612
    double flt_div = nparms / 2.0 * log(2.0 * M_PI);  // shape at bmds_helper.cpp:1148
    std::printf("nparms=%d  int_div=%.6f  float_div=%.6f  deficit=%.6f  weight_factor=exp(-deficit)=%.6f\n",
                nparms, int_div, flt_div, flt_div - int_div, std::exp(-(flt_div - int_div)));
  }
  return 0;
}
