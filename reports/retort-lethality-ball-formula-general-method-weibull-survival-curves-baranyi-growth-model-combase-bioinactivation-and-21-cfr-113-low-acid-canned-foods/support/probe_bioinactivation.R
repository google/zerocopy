# Probe: bioinactivation (pinned source tree) -- dynamic Weibull formulation,
# log-linear vs Weibull fits to the package's example data, and a
# misspecification coverage experiment on SYNTHETIC data.
#
# Run (R >= 4.4, packages installed from the pinned source trees):
#   Rscript probe_bioinactivation.R
suppressPackageStartupMessages(library(bioinactivation))
set.seed(20261121)
cat("bioinactivation", as.character(packageVersion("bioinactivation")), "\n")

## ---- A: dependence on the time origin under a dynamic profile ------------
## The same heat treatment is applied either at t = 0 or after a 30 min hold
## at 20 C (where every model below predicts ~zero inactivation).
prof0 <- data.frame(time = c(0, 10, 15, 20), temperature = c(20, 70, 70, 30))
profS <- data.frame(time = c(0, 30, 40, 45, 50), temperature = c(20, 20, 70, 70, 30))
end0 <- 20; endS <- 50
run <- function(model, parms) {
  a <- predict_inactivation(model, c(0, end0), parms, prof0)$simulation
  b <- predict_inactivation(model, c(0, endS), parms, profS)$simulation
  c(no_hold = tail(a$logS, 1), with_hold = tail(b$logS, 1))
}
resA <- rbind(
  Bigelow        = run("Bigelow", c(D_R = 1, z = 7, temp_ref = 70, N0 = 1e6)),
  Mafart_p0.5    = run("Mafart", c(delta_ref = 1, z = 7, p = 0.5, temp_ref = 70, N0 = 1e6)),
  Mafart_p1.0    = run("Mafart", c(delta_ref = 1, z = 7, p = 1.0, temp_ref = 70, N0 = 1e6)),
  Mafart_p1.5    = run("Mafart", c(delta_ref = 1, z = 7, p = 1.5, temp_ref = 70, N0 = 1e6)),
  Peleg_n0.5     = run("Peleg", c(n = 0.5, k_b = 0.3, temp_crit = 60, N0 = 1e6)),
  Peleg_n1.5     = run("Peleg", c(n = 1.5, k_b = 0.3, temp_crit = 60, N0 = 1e6))
)
cat("\n== A: final log10(N/N0), same thermal treatment with/without a 30 min cold lead-in ==\n")
print(round(cbind(resA, delta = resA[, 2] - resA[, 1]), 4))

## ---- B: log-linear vs Weibull fitted to the shipped example data ----------
data("isothermal_inactivation")
d <- isothermal_inactivation
cat("\n== B: dataset isothermal_inactivation:", nrow(d), "rows; temps:",
    paste(sort(unique(d$temp)), collapse = ","), "\n")
fB <- fit_isothermal_inactivation("Bigelow", d, list(z = 10, D_R = 1), list(temp_ref = 100))
fW <- fit_isothermal_inactivation("Mafart", d, list(delta_ref = 1, z = 10, p = 1), list(temp_ref = 100))
print(summary(fB$nls)$coefficients)
print(summary(fW$nls)$coefficients)
rssB <- sum(resid(fB$nls)^2); rssW <- sum(resid(fW$nls)^2); n <- nrow(d)
aic <- function(rss, k) n * log(rss / n) + 2 * k
cat(sprintf("RSS Bigelow=%.4f  Mafart=%.4f ; AIC Bigelow=%.2f Mafart=%.2f\n",
            rssB, rssW, aic(rssB, 2), aic(rssW, 3)))
## Computed log reduction for the same reference process under each fit
ref_prof <- data.frame(time = c(0, 5, 15, 20), temperature = c(80, 100, 100, 80))
pB <- predict_inactivation("Bigelow", c(0, 20), c(fB$parameters, N0 = 1e6), ref_prof)$simulation
pW <- predict_inactivation("Mafart", c(0, 20), c(fW$parameters, N0 = 1e6), ref_prof)$simulation
cat(sprintf("reference process (80->100 C 5 min, 10 min hold, 100->80 C 5 min): log10 S Bigelow=%.3f Mafart=%.3f\n",
            tail(pB$logS, 1), tail(pW$logS, 1)))
for (target in c(1, 3, 6, 12)) {
  tB <- target * fB$parameters$D_R
  tW <- fW$parameters$delta_ref * target^(1 / fW$parameters$p)
  cat(sprintf("  isothermal time at 100 C for %2d log reductions: Bigelow=%.3f  Mafart=%.3f (ratio %.3f)\n",
              target, tB, tW, tW / tB))
}

## ---- C: misspecification coverage on synthetic Weibull data --------------
## Truth: Weibull-Mafart isothermal, delta_ref = 2 min at 70 C, z = 7, p = 0.6.
## Observations: log_diff + N(0, 0.3^2) at 3 temperatures x 6 times.
## Fit: Bigelow (log-linear) by nls. Question: do 95% prediction bands from
## the fitted model's asymptotic covariance cover the true log reduction?
truth <- function(t, T) WeibullMafart_iso_wrap(t, T)
WeibullMafart_iso_wrap <- function(t, T) -(t / (2 * 10^(-(T - 70) / 7)))^0.6
design <- expand.grid(time = c(0.5, 1, 2, 4, 6, 8), temp = c(66, 70, 74))
eval_pts <- data.frame(time = c(0.25, 1, 4, 8, 16), temp = 70)
reps <- 300
cover <- matrix(NA, reps, nrow(eval_pts)); bias <- cover
coverW <- cover
for (r in seq_len(reps)) {
  dd <- design; dd$log_diff <- truth(dd$time, dd$temp) + rnorm(nrow(dd), 0, 0.3)
  fit <- try(fit_isothermal_inactivation("Bigelow", dd, list(z = 7, D_R = 2), list(temp_ref = 70)), silent = TRUE)
  fitw <- try(fit_isothermal_inactivation("Mafart", dd, list(delta_ref = 2, z = 7, p = 0.7), list(temp_ref = 70)), silent = TRUE)
  tv <- truth(eval_pts$time, eval_pts$temp)
  if (!inherits(fit, "try-error")) {
    cf <- coef(fit$nls); V <- vcov(fit$nls)
    sims <- MASS::mvrnorm(2000, cf, V)
    pred <- sapply(seq_len(nrow(eval_pts)), function(i)
      -eval_pts$time[i] / (sims[, "D_R"] * 10^((70 - eval_pts$temp[i]) / sims[, "z"])))
    lo <- apply(pred, 2, quantile, 0.025); hi <- apply(pred, 2, quantile, 0.975)
    cover[r, ] <- (tv >= lo & tv <= hi)
    bias[r, ] <- -eval_pts$time / (cf["D_R"] * 10^((70 - eval_pts$temp) / cf["z"])) - tv
  }
  if (!inherits(fitw, "try-error")) {
    cf <- coef(fitw$nls); V <- vcov(fitw$nls)
    sims <- MASS::mvrnorm(2000, cf, V)
    pred <- sapply(seq_len(nrow(eval_pts)), function(i)
      -(eval_pts$time[i] / (sims[, "delta_ref"] * 10^(-(eval_pts$temp[i] - 70) / sims[, "z"])))^sims[, "p"])
    lo <- apply(pred, 2, quantile, 0.025); hi <- apply(pred, 2, quantile, 0.975)
    coverW[r, ] <- (tv >= lo & tv <= hi)
  }
}
cat("\n== C: 95% band coverage of the TRUE log reduction at 70 C (", reps, "replicates) ==\n")
out <- data.frame(time = eval_pts$time,
                  true_log_diff = round(truth(eval_pts$time, 70), 3),
                  bigelow_fit_coverage = round(colMeans(cover, na.rm = TRUE), 3),
                  bigelow_mean_bias = round(colMeans(bias, na.rm = TRUE), 3),
                  weibull_fit_coverage = round(colMeans(coverW, na.rm = TRUE), 3))
print(out)
cat("failed fits: Bigelow", sum(is.na(cover[, 1])), " Mafart", sum(is.na(coverW[, 1])), "\n")
cat("elapsed (s):", round(proc.time()[["elapsed"]], 1), "\n")
