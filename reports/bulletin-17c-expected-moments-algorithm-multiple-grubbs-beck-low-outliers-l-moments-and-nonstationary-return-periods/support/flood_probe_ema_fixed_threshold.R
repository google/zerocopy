# EMA (Cohn's P3_089) with PILFs censored at the threshold returned by MGBT 1.1.8's
# user-level MGBT17c() (the rule that matches the USGS-PeakFQ v7.1 examples quoted in
# the MGBT documentation), instead of P3_089's own single-loop MGBT. The censoring
# replicates P3_089's MGBTest() slot edits exactly, with only the threshold changed.
# Usage: Rscript flood_probe_ema_fixed_threshold.R <P3_089(R).txt> <flood_out dir>
args <- commandArgs(trailingOnly = TRUE)
invisible(suppressWarnings(capture.output(source(args[1]))))   # silence the embedded example
outdir <- args[2]
res <- read.csv(file.path(outdir, "flood_probe_results.csv"), colClasses = c(site = "character"))
censorAt <- function(o_in, thr) {               # same edits as MGBTest() in P3_089
  test <- (o_in@qu < thr)
  o <- as(o_in, "EMAresult")
  o@PILFOutlierCritValue <- thr; o@PILFOutlierThreshold <- thr
  o@nPILFOutlier <- sum(test); o@LowOutlier <- test
  o@qu <- ifelse(test, thr, o@qu); o@ql <- ifelse(test, 1e-99, o@ql)
  o@logqu <- log(ifelse(test, thr, o@qu)); o@logql <- log(ifelse(test, 1e-99, o@ql))
  o
}
for (i in seq_len(nrow(res))) {
  site <- res$site[i]; thr <- res$LOT_17c[i]
  if (thr <= 0 || site == "08385600") next
  q <- read.csv(file.path(outdir, paste0("peaks_", site, ".csv")))$q
  o <- censorAt(makeFLOODdata(ql = q, qu = q), thr)
  e <- suppressWarnings(makeEMAresult(o, pq = c(0.99, 0.998), LowOutlierTest = "none"))
  cat(sprintf("%s  MGBT17c K=%d T=%g  ->  EMA Q(AEP 0.01) = %.1f  [90%%: %.1f, %.1f]  skew = %.4f\n",
              site, o@nPILFOutlier, thr, e@QestP[1], e@CI[1, 1], e@CI[1, 2], e@moms[3]))
}
