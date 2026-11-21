# Probe: Weibull-Mafart dynamic prediction with dense output times vs a fine
# Riemann sum of the same rate law (bioinactivation, pinned source tree).
suppressPackageStartupMessages(library(bioinactivation))
prof0 <- data.frame(time = c(0, 10, 15, 20), temperature = c(20, 70, 70, 30))
profS <- data.frame(time = c(0, 30, 40, 45, 50), temperature = c(20, 20, 70, 70, 30))
p <- c(delta_ref = 1, z = 7, p = 1.5, temp_ref = 70, N0 = 1e6)
a <- predict_inactivation("Mafart", seq(0, 20, by = 1), p, prof0)$simulation
print(a[, c("time", "logS")])
b <- predict_inactivation("Mafart", seq(0, 50, by = 2), p, profS)$simulation
print(b[, c("time", "N", "logS")])
## Analytic check of the package's ODE for a profile: integrate
## dlnN/dt = -ln(10) p delta(T(t))^-p t^(p-1) with a fine Riemann sum
Tf <- approxfun(prof0$time, prof0$temperature)
tt <- seq(1e-6, 20, length.out = 200001); dt <- diff(tt)[1]
rate <- p[["p"]] * (1 / (1 * 10^(-(Tf(tt) - 70) / 7)))^p[["p"]] * tt^(p[["p"]] - 1)
cat("Riemann-sum log10 S (no hold, p=1.5):", -sum(rate) * dt, "\n")
for (pp in c(0.5, 1.5)) {
  for (pr in list(prof0, profS)) {
    Tf <- approxfun(pr$time, pr$temperature); tend <- max(pr$time)
    tt <- seq(1e-6, tend, length.out = 400001); dt <- diff(tt)[1]
    rate <- pp * (10^((Tf(tt) - 70) / 7))^pp * tt^(pp - 1)
    cat(sprintf("Riemann log10 S p=%.1f end=%d: %.4f\n", pp, tend, -sum(rate) * dt))
  }
}
