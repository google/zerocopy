# Probe: numerical robustness of bioinactivation::predict_inactivation for
# large log reductions and sparse output times (pinned source tree).
# Reference values: fine Riemann sums of the same rate laws the package's ODE
# right-hand sides implement (R/bigelow_model.R, R/weibull-mafart_model.R).
suppressPackageStartupMessages(library(bioinactivation))
cat("bioinactivation", as.character(packageVersion("bioinactivation")),
    " deSolve", as.character(packageVersion("deSolve")), "\n")
riemann <- function(prof, rate_fun) {
  Tf <- approxfun(prof$time, prof$temperature); tend <- max(prof$time)
  tt <- seq(1e-6, tend, length.out = 400001); dt <- diff(tt)[1]
  -sum(rate_fun(tt, Tf(tt))) * dt
}
mk <- function(hold) data.frame(time = c(0, 10, 10 + hold, 20 + hold),
                                temperature = c(20, 70, 70, 30))
rows <- list()
for (hold in c(1, 3, 6, 12)) {
  prof <- mk(hold); tend <- max(prof$time)
  big <- c(D_R = 1, z = 7, temp_ref = 70, N0 = 1e6)
  maf <- c(delta_ref = 1, z = 7, p = 1.5, temp_ref = 70, N0 = 1e6)
  exB <- riemann(prof, function(t, T) 1 / (1 * 10^((70 - T) / 7)))
  exM <- riemann(prof, function(t, T) 1.5 * (10^((T - 70) / 7))^1.5 * t^0.5)
  for (spec in list(list("Bigelow", big, exB), list("Mafart_p1.5", maf, exM))) {
    nm <- spec[[1]]; model <- if (nm == "Bigelow") "Bigelow" else "Mafart"
    two <- tail(predict_inactivation(model, c(0, tend), spec[[2]], prof)$simulation$logS, 1)
    dense <- tail(predict_inactivation(model, seq(0, tend, length.out = 101), spec[[2]], prof)$simulation$logS, 1)
    hmax <- tail(predict_inactivation(model, c(0, tend), spec[[2]], prof, hmax = 0.05)$simulation$logS, 1)
    rows[[length(rows) + 1]] <- data.frame(model = nm, hold_min = hold, exact = round(spec[[3]], 3),
      two_output_times = round(two, 3), dense_101 = round(dense, 3), two_times_hmax0.05 = round(hmax, 3))
  }
}
res <- do.call(rbind, rows)
print(res, row.names = FALSE)
