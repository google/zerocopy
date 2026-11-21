# Probe: biogrowth (pinned source tree) -- primary-model disagreement under
# identical parameters, growth-rate log-base convention, isothermal vs
# fluctuating temperature, and a misspecification coverage experiment on
# SYNTHETIC data.
suppressPackageStartupMessages(library(biogrowth))
set.seed(20261121)
cat("biogrowth", as.character(packageVersion("biogrowth")), "\n")

## ---- A: same (logN0, logNmax|C, mu, lambda), different primary models ----
tt <- c(0, 5, 10, 15, 20, 30)
common <- list(logN0 = 2, mu = 0.4, lambda = 8)
mods <- list(
  Baranyi     = c(common, model = "Baranyi", logNmax = 8),
  modGompertz = c(common, model = "modGompertz", C = 6),
  Logistic    = c(common, model = "Logistic", C = 6),
  Trilinear   = c(common, model = "Trilinear", logNmax = 8)
)
tab <- sapply(mods, function(m) predict_growth(tt, m)$simulation$logN)
rownames(tab) <- paste0("t=", tt)
cat("\n== A: log10 N predicted with logN0=2, max=8 (C=6), mu=0.4 log10/h, lambda=8 h ==\n")
print(round(tab, 3))
t_at <- function(m, level) uniroot(function(t) predict_growth(c(0, t), m)$simulation$logN[2] - level, c(0.01, 200))$root
cat("time (h) to reach log10 N = 5:\n")
print(round(sapply(mods, t_at, level = 5), 2))

## ---- B: the same numbers read as ln-based vs log10-based mu ---------------
b10 <- predict_growth(tt, mods$Baranyi, logbase_mu = 10)$simulation$logN
bln <- predict_growth(tt, mods$Baranyi, logbase_mu = exp(1))$simulation$logN
cat("\n== B: Baranyi, mu = 0.4 interpreted as log10/h vs ln/h ==\n")
print(round(rbind(log10_mu = b10, ln_mu = bln), 3))

## ---- C: dynamic temperature vs constant mean temperature ------------------
sec <- list(temperature = list(model = "CPM", xmin = 2, xopt = 35, xmax = 40, n = 2))
prim_dyn <- list(mu_opt = 1.2, Nmax = 1e8, N0 = 1e2, Q0 = 1e-3)
ttd <- seq(0, 96, by = 0.5)
fluct <- data.frame(time = seq(0, 96, by = 1), temperature = 7 + 5 * sin(2 * pi * seq(0, 96, by = 1) / 24))
mean_env <- data.frame(time = c(0, 96), temperature = c(7, 7))
pd <- predict_growth(ttd, prim_dyn, environment = "dynamic", secondary_models = sec, env_conditions = fluct)$simulation
pm <- predict_growth(ttd, prim_dyn, environment = "dynamic", secondary_models = sec, env_conditions = mean_env)$simulation
cat("\n== C: Baranyi + CPM(T), 7 +/- 5 C daily sinusoid vs constant 7 C ==\n")
idx <- match(c(24, 48, 72, 96), ttd)
print(round(data.frame(time = ttd[idx], logN_fluct = pd$logN[idx], logN_const7 = pm$logN[idx]), 3))

## ---- D: misspecification coverage --------------------------------------
## Truth: modified Gompertz logN0=2, C=6, mu=0.4 log10/h, lambda=8 h.
## Data: 13 times (0..48 h by 4 h), N(0, 0.25^2) noise on log10 N.
## Fits: Baranyi (misspecified) and modGompertz (correct), by regression.
## Targets: time to reach log10 N = 4 (mid-curve) and 7.5 (near the
## asymptote); 95% interval from MVN draws of the reported covariance (vcov()).
truth_m <- mods$modGompertz
times <- seq(0, 48, by = 4)
true_logN <- predict_growth(times, truth_m)$simulation$logN
iso_B <- biogrowth:::iso_Baranyi; iso_G <- biogrowth:::iso_repGompertz
tB <- function(p, lev) uniroot(function(t) iso_B(t, p[["logN0"]], p[["mu"]], p[["lambda"]], p[["logNmax"]]) - lev, c(1e-3, 500))$root
tG <- function(p, lev) uniroot(function(t) iso_G(t, p[["logN0"]], p[["C"]], p[["mu"]], p[["lambda"]]) - lev, c(1e-3, 500))$root
reps <- 150
for (lev in c(4, 7.5)) {
  t_true <- t_at(truth_m, lev)
  set.seed(20261121)
  res <- data.frame(covB = NA, estB = NA, covG = NA, estG = NA)[rep(1, reps), ]
  for (r in seq_len(reps)) {
    dd <- data.frame(time = times, logN = true_logN + rnorm(length(times), 0, 0.25))
    for (which in c("B", "G")) {
      fit <- try(suppressWarnings(fit_growth(dd,
        model_keys = list(primary = if (which == "B") "Baranyi" else "modGompertz"),
        start = if (which == "B") c(logN0 = 2, logNmax = 8, mu = 0.3, lambda = 5) else c(logN0 = 2, C = 6, mu = 0.3, lambda = 5),
        known = c(), environment = "constant", algorithm = "regression", approach = "single")), silent = TRUE)
      if (inherits(fit, "try-error")) next
      est <- coef(fit); V <- vcov(fit)
      if (any(!is.finite(V))) next
      draws <- MASS::mvrnorm(1000, est, V)
      f <- if (which == "B") tB else tG
      tt_d <- apply(draws, 1, function(p) tryCatch(f(as.list(p), lev), error = function(e) NA))
      ci <- quantile(tt_d, c(0.025, 0.975), na.rm = TRUE)
      res[r, paste0("cov", which)] <- (t_true >= ci[1] & t_true <= ci[2])
      res[r, paste0("est", which)] <- tryCatch(f(as.list(est), lev), error = function(e) NA)
    }
  }
  cat("\n== D: coverage of true time-to-log10N=", lev, " (", round(t_true, 3), "h ) over", reps, "replicates ==\n")
  cat(sprintf("Baranyi fit (misspecified): coverage=%.3f mean_estimate=%.3f h  (n ok=%d)\n",
              mean(res$covB, na.rm = TRUE), mean(res$estB, na.rm = TRUE), sum(!is.na(res$covB))))
  cat(sprintf("modGompertz fit (correct):  coverage=%.3f mean_estimate=%.3f h  (n ok=%d)\n",
              mean(res$covG, na.rm = TRUE), mean(res$estG, na.rm = TRUE), sum(!is.na(res$covG))))
}
cat("elapsed (s):", round(proc.time()[["elapsed"]], 1), "\n")
