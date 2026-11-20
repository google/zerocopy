# EMA + MGBT (Bulletin 17C procedure, station skew only, systematic record only)
# using T. A. Cohn's R source shipped in cran/MGBT@0994615648a373bd7beb3cf7ebecb19e9edd948c
# as inst/sources/P3_089(R).txt. Run in a fresh R session WITHOUT the MGBT package
# loaded: sourcing the file defines its own MGBT(), peta(), etc. and, at the end,
# runs its embedded "Big Sandy Test Dataset" example (printed first).
# Usage: Rscript flood_probe_ema.R <P3_089(R).txt> <flood_out dir>
args <- commandArgs(trailingOnly = TRUE)
.libPaths(c(Sys.getenv("PINNED_R_LIB", "."), .libPaths()))  # library holding the pinned MGBT, lmomco, lmom builds
cat("=== embedded example output from sourcing P3_089 ===\n")
suppressWarnings(source(args[1]))
outdir <- args[2]
aep <- c(0.01, 0.002)
NAS <- c(q100 = NA, lo = NA, hi = NA, q500 = NA, npilf = NA, thr = NA, g = NA)
run <- function(q, test, label = "") {
  tryCatch(suppressWarnings({
    o <- makeFLOODdata(ql = pmax(q, 1e-20), qu = pmax(q, 1e-20))
    # makeEMAresult(..., LowOutlierTest = "none") assigns o@LowOutlierTest on the
    # FLOODdata input, which lacks that slot (P3_089 lines 462-465); coerce first.
    if (test == "none") o <- as(o, "EMAresult")
    e <- makeEMAresult(o, pq = 1 - aep, LowOutlierTest = test)
    # pq is sorted ascending inside makeEMAresult: row 1 = 0.99 (AEP 0.01), row 2 = 0.998
    c(q100 = e@QestP[1], lo = e@CI[1, 1], hi = e@CI[1, 2], q500 = e@QestP[2],
      npilf = if (test == "none") 0 else e@nPILFOutlier,
      thr = if (test == "none") NA else e@PILFOutlierThreshold,
      g = e@moms[3])
  }), error = function(err) { message("EMA error [", label, " ", test, "]: ", conditionMessage(err)); NAS })
}
rows <- list()
for (f in sort(Sys.glob(file.path(outdir, "peaks_*.csv")))) {
  site <- sub("peaks_(.*)\\.csv", "\\1", basename(f))
  q <- read.csv(f)$q
  q2 <- q; i <- which.min(q); q2[i] <- q[i] / 10
  t0 <- proc.time()[["elapsed"]]
  a <- run(q, "MGBT", site); b <- run(q, "none", site)
  c2 <- run(q2, "MGBT", paste0(site, "/perturbed")); d2 <- run(q2, "none", paste0(site, "/perturbed"))
  rows[[site]] <- data.frame(site = site, n = length(q),
    ema_mgbt_npilf = a[["npilf"]], ema_mgbt_thr = a[["thr"]], ema_mgbt_skew = round(a[["g"]], 4),
    ema_mgbt_q100 = a[["q100"]], ema_mgbt_lo90 = a[["lo"]], ema_mgbt_hi90 = a[["hi"]], ema_mgbt_q500 = a[["q500"]],
    ema_none_q100 = b[["q100"]], ema_none_skew = round(b[["g"]], 4),
    pert_ema_mgbt_q100 = c2[["q100"]], pert_ema_mgbt_npilf = c2[["npilf"]], pert_ema_none_q100 = d2[["q100"]],
    secs = round(proc.time()[["elapsed"]] - t0, 2))
}
tab <- do.call(rbind, rows)
write.csv(tab, file.path(outdir, "flood_probe_ema_results.csv"), row.names = FALSE)
options(width = 250)
cat("\n=== EMA results (Q in cfs; CI = 90% two-sided from makeEMAresult default eps=0.90) ===\n")
print(tab, row.names = FALSE)
