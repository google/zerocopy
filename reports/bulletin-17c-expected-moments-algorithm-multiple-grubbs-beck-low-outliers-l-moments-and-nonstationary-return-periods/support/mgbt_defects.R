# Two source-level defects in R package MGBT 1.1.8
# (cran/MGBT@0994615648a373bd7beb3cf7ebecb19e9edd948c, file R/MGBT.R), exercised directly.
.libPaths(c(Sys.getenv("PINNED_R_LIB", "."), .libPaths()))  # library holding the pinned MGBT, lmomco, lmom builds
suppressPackageStartupMessages(library(MGBT))

cat("== (1) R operator precedence in mgbt.sweeper(): `for(i in j1+1:n2)` ==\n")
j1 <- 2; n2 <- 4
cat("j1+1:n2 evaluates to:", j1 + 1:n2, " (intended (j1+1):n2 =", (j1 + 1):n2, ")\n")
pv <- c(0.001, 0.002, 0.008, 0.009)  # n2 = 4 p-values, smallest observation first
cat("default alphain = 0: ")
print(unlist(MGBT:::mgbt.sweeper(pv, alphaout = 0.005, alphain = 0, alphazeroin = 0.10)))
cat("alphain = 0.01 (every p-value after the outward-sweep index is < alphain):\n")
r <- tryCatch(MGBT:::mgbt.sweeper(pv, alphaout = 0.005, alphain = 0.01, alphazeroin = 0.10),
              error = function(e) paste("ERROR:", conditionMessage(e)))
print(r)

cat("\n== (1b) inward sweep j3 stays 0 when no p-value reaches alphazeroin ==\n")
# Single-loop rule used by MGBTcohn2016/MGBTcohn2013 (R/MGBT.R lines 76 and 87, 177-178)
tac_sweep <- function(pv, alphaout = 0.005, alphazeroin = 0.10) {
  j1 <- j2 <- 0
  for (i in seq_along(pv)) {
    if (pv[i] < alphaout) { j1 <- i; j2 <- i }
    if ((pv[i] < alphazeroin) & (j2 == i - 1)) j2 <- i
  }
  j2
}
for (pvx in list(c(0.001, 0.002, 0.008, 0.009), c(0.001, 0.002, 0.03, 0.05), c(0.03, 0.04, 0.05, 0.2))) {
  s <- MGBT:::mgbt.sweeper(pvx)
  cat("p =", format(pvx), "| mgbt.sweeper index =", s$index, "sweeps =", s$sweeps,
      "| single-loop rule =", tac_sweep(pvx), "\n")
}

cat("\n== (2) MGBT17c.verb() when the most central tested order statistic is significant ==\n")
# Data quoted in a comment inside mgbt.sweeper() (labelled station 08020500)
Q <- c(19500, 17400, 9350, 3760, 8410, 15200, 5370, 22300, 21500, 6590, 17300)
a <- suppressMessages(MGBT17c(Q)); b <- suppressMessages(MGBT17c.verb(Q))
cat("n =", length(Q), " n2 =", floor(length(Q) / 2), "\n")
cat("p-values (smallest obs first):", signif(a$pvalues, 4), "\n")
cat("MGBT17c      : klow =", a$klow, " LOThresh =", a$LOThresh, " sweeps =", a$index[3:5], "\n")
cat("MGBT17c.verb : klow =", b$klow, " LOThresh =", b$LOThresh, " sweeps =", b$index[3:5], "\n")
cat("MGBTcohn2016 : klow =", suppressMessages(MGBTcohn2016(Q))$klow, "\n")

cat("\n== (3) Single-loop rule vs MGBT17c on the record labelled 08165300 in MGBT-package.Rd ==\n")
# Documented there: USGS-PeakFQ v7.1 reports 16 PILFs, threshold 1110 cfs.
Peaks <- c(3200, 44, 5270, 26300, 1230, 55, 38400, 8710, 143, 23200, 39300, 1890,
  27800, 21000, 21000, 124, 21, 21500, 57000, 53700, 5720, 50, 10700, 4050, 4890, 1110,
  10500, 475, 1590, 26300, 16600, 2370, 53, 20900, 21400, 313, 10800, 51, 35, 8910,
  57.4, 617, 6360, 59, 2640, 164, 297, 3150, 2690)
for (f in c("MGBT17c", "MGBT17c.verb", "MGBTcohn2016", "MGBTcohn2013", "MGBTnb")) {
  r <- suppressMessages(get(f)(Peaks))
  cat(sprintf("%-13s klow = %2d  LOThresh = %s\n", f, r$klow, format(r$LOThresh)))
}
