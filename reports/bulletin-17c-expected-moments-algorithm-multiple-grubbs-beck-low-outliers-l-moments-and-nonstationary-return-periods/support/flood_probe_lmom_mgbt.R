# Flood-frequency cross-implementation probe (MGBT variants and L-moment fits).
#
# Runs, on the same annual-peak records:
#   * the MGBT low-outlier test variants shipped in R package MGBT
#     (cran/MGBT@0994615648a373bd7beb3cf7ebecb19e9edd948c, version 1.1.8);
#   * a plain method-of-moments log-Pearson III fit (station skew, no low-outlier
#     treatment) evaluated with lmomco's Pearson III quantile function;
#   * L-moment GEV fits from lmomco (wasquith/lmomco@9d49f0a2e6fe1d687af82efe63d4a73caca82b04,
#     2.5.8) and lmom (cran/lmom@252d9635c3acaf452d4d497fab2da01fa1edfcd8, 3.3), and an
#     L-moment Pearson III fit to log10 flows (lmomco).
# It also writes peaks_<site>.csv (the exact inputs) for flood_probe_ema.R and
# lmoments3_probe.py. EMA is run separately (flood_probe_ema.R) because sourcing
# Cohn's P3_089 file defines functions that clash with the MGBT package.
# Usage: PINNED_R_LIB=<lib> Rscript flood_probe_lmom_mgbt.R <outdir>
args <- commandArgs(trailingOnly = TRUE)
.libPaths(c(Sys.getenv("PINNED_R_LIB", "."), .libPaths()))  # library holding the pinned MGBT, lmomco, lmom builds
suppressPackageStartupMessages({library(MGBT); library(lmomco); library(lmom)})
outdir <- args[1]

recs <- list()
# Records quoted verbatim in MGBT's MGBT.Rd (systematic peaks, cfs)
recs[["08066300"]] <- c(3530, 284, 1810, 9660,  489,  292, 1000,  2640, 2910, 1900,  1120, 1020,
   632, 7160, 1750,  2730,  1630, 8210, 4270, 1730, 13200, 2550,  915, 11000, 2370,
  2230, 4650, 2750,  1860, 13700, 2290, 3390, 5160, 13200,  410, 1890,  4120, 3930,
  4290, 1890, 1480, 10300,  1190, 2320, 2480, 55.0,  7480,  351,  738,  2430, 6700)
recs[["08385600"]] <- c(  8100, 3300,  680, 14800,  25.0, 7310, 2150, 1110, 5200, 900, 1150,
   1050,  880, 2100, 2280, 2620,   830,  4900,  970,  560,  790, 1900, 830,  255,
   2900, 2100,    0,  550, 1200,  1300,   246,  700,  870, 4350,  870, 435, 3000,
    880, 2650,  185,  620, 1650,   680, 22900, 3290,  584, 7290, 1690, 2220, 217,
   4110,  853,  275, 1780, 1330,  3170,  7070, 2660)
# Peak-flow datasets bundled in lmomco (systematic peaks: non-missing, not code 7)
for (nm in c("USGSsta01515000peaks", "USGSsta02366500peaks", "USGSsta05405000peaks",
             "USGSsta08151500peaks", "USGSsta08167000peaks", "USGSsta08190000peaks",
             "USGSsta09442000peaks", "USGSsta14321000peaks")) {
  e <- new.env(); data(list = nm, package = "lmomco", envir = e); d <- get(nm, envir = e)
  if ("peak_va" %in% names(d)) { v <- d$peak_va; cd <- as.character(d$peak_cd) }
  else { v <- d$Streamflow; cd <- as.character(d$Flags) }
  # drop missing values and historical peaks (NWIS peak qualification code 7)
  keep <- !is.na(v) & !(grepl("(^|,)7(,|$)", cd) %in% TRUE)
  recs[[sub("USGSsta(\\d+)peaks", "\\1", nm)]] <- as.numeric(v[keep])
}

aep <- 0.01
q_mom_lp3 <- function(q) {
  x <- log10(q[q > 0]); n <- length(x); m <- mean(x); s <- sd(x)
  g <- n * sum((x - m)^3) / ((n - 1) * (n - 2) * s^3)
  10^lmomco::quape3(1 - aep, lmomco::vec2par(c(m, s, g), type = "pe3"))
}
q_lmomco_gev <- function(q) lmomco::quagev(1 - aep, lmomco::pargev(lmomco::lmoms(q)))
q_lmom_gev   <- function(q) lmom::quagev(1 - aep, lmom::pelgev(lmom::samlmu(q)))
q_lmomco_lp3 <- function(q) { x <- log10(q[q > 0]); 10^lmomco::quape3(1 - aep, lmomco::parpe3(lmomco::lmoms(x))) }
klow <- function(f, q) tryCatch(suppressMessages(f(q)$klow), error = function(e) NA)

rows <- list()
for (nm in names(recs)) {
  q <- recs[[nm]]
  t0 <- proc.time()[["elapsed"]]
  m17 <- suppressMessages(MGBT17c(q))
  q2 <- q; i <- which.min(q); q2[i] <- q[i] / 10   # perturb the smallest flood
  rows[[nm]] <- data.frame(
    site = nm, n = length(q), min = min(q), max = max(q),
    klow_17c = m17$klow, LOT_17c = m17$LOThresh,
    klow_17c_verb = klow(MGBT17c.verb, q), klow_cohn2016 = klow(MGBTcohn2016, q),
    klow_cohn2013 = klow(MGBTcohn2013, q), klow_nb = klow(MGBTnb, q),
    mom_lp3_q100 = q_mom_lp3(q),
    lmomco_gev_q100 = q_lmomco_gev(q), lmom_gev_q100 = q_lmom_gev(q), lmomco_lp3_q100 = q_lmomco_lp3(q),
    pert_mom_lp3_q100 = q_mom_lp3(q2),
    pert_lmomco_gev_q100 = q_lmomco_gev(q2), pert_lmomco_lp3_q100 = q_lmomco_lp3(q2),
    secs = round(proc.time()[["elapsed"]] - t0, 2))
  write.csv(data.frame(q = q), file.path(outdir, paste0("peaks_", nm, ".csv")), row.names = FALSE)
}
tab <- do.call(rbind, rows)
write.csv(tab, file.path(outdir, "flood_probe_results.csv"), row.names = FALSE)
options(width = 250)
print(tab[, c("site", "n", "min", "klow_17c", "LOT_17c", "klow_17c_verb", "klow_cohn2016", "klow_cohn2013", "klow_nb")], row.names = FALSE)
fmt <- function(v) formatC(v, format = "g", digits = 5)
print(data.frame(site = tab$site, mom_lp3 = fmt(tab$mom_lp3_q100), lmomco_gev = fmt(tab$lmomco_gev_q100),
                 lmom_gev = fmt(tab$lmom_gev_q100), lmomco_lp3 = fmt(tab$lmomco_lp3_q100)), row.names = FALSE)
pct <- function(a, b) sprintf("%+.1f%%", 100 * (a / b - 1))
print(data.frame(site = tab$site, d_mom_lp3 = pct(tab$pert_mom_lp3_q100, tab$mom_lp3_q100),
                 d_lmomco_gev = pct(tab$pert_lmomco_gev_q100, tab$lmomco_gev_q100),
                 d_lmomco_lp3 = pct(tab$pert_lmomco_lp3_q100, tab$lmomco_lp3_q100), secs = tab$secs), row.names = FALSE)
cat("max |lmomco GEV / lmom GEV - 1|:", max(abs(tab$lmomco_gev_q100 / tab$lmom_gev_q100 - 1)), "\n")
