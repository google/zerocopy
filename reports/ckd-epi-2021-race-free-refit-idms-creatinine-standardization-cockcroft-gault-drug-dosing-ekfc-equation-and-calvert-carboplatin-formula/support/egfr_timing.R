# Throughput probe: vectorised eGFR evaluation in kidney.epi 1.4.0 vs nephro 1.5 (sourced, not installed).
# Usage: KIDNEY_EPI_DIR=... NEPHRO_DIR=... Rscript egfr_timing.R
ke <- Sys.getenv("KIDNEY_EPI_DIR"); ne <- Sys.getenv("NEPHRO_DIR")
for (f in c("service.general.R", "service.check_plausibility.R", "egfr_ckdepi2021.R")) source(file.path(ke, "R", f))
source(file.path(ne, "R", "nephro.R"))
set.seed(1)
for (n in c(1e4, 1e5, 1e6)) {
  scr <- exp(rnorm(n, log(0.9), 0.35)); age <- runif(n, 19, 95); sx <- rbinom(n, 1, 0.5)
  lab <- ifelse(sx == 1, "Male", "Female")
  g <- gc(reset = TRUE)
  t1 <- system.time(a <- egfr.ckdepi.cr.2021(scr, age, lab, creatinine_units = "mg/dl"))[["elapsed"]]
  m1 <- sum(gc()[, 6])
  g <- gc(reset = TRUE)
  t2 <- system.time(b <- as.numeric(CKDEpi2021.creat(scr, sx, age)))[["elapsed"]]
  m2 <- sum(gc()[, 6])
  cat(sprintf("n=%d kidney.epi %.3fs (%.0f/s, max-mem %.0f MB) | nephro %.3fs (%.0f/s, max-mem %.0f MB) | max|diff| after kidney.epi rounding %.4f\n",
              as.integer(n), t1, n / t1, m1, t2, n / t2, m2, max(abs(a - b))))
}
