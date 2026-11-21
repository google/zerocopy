# Sensor-side reproduction of the NowCast + AQI-category step of the FASM category-agreement analysis.
# Uses the internal .nowcast()/.weightFactor() functions from MazamaScience/AirMonitor R/monitor_nowcast.R
# (pinned revision) and the category breaks copied verbatim from USEPA/FASM-sensor-AQI-analysis
# R/functions_for_AQI_barplots.R (create_AQI_unlisted). Monitor-side data are NOT used (not available offline).
# Usage: Rscript fasm_sensor_nowcast.R <monitor_nowcast.R> <purpleair_data.csv> <n_sensors> <outdir>
args <- commandArgs(trailingOnly = TRUE)
source(args[1])                      # defines monitor_nowcast, .nowcast, .weightFactor (no side effects)
d <- read.csv(args[2], check.names = FALSE)
n <- as.integer(args[3]); outdir <- args[4]
X <- as.matrix(d[, 2:(n + 1)])
t0 <- proc.time()
NC <- apply(X, 2, function(x) .nowcast(x, 12, 0.5, TRUE))   # version "pm", includeShortTerm = TRUE
NC <- trunc(NC * 10^1) / 10^1                                # monitor_nowcast line: trunc(newData*10^digits)/10^digits
el <- (proc.time() - t0)[["elapsed"]]
breaks <- c(-Inf, 9.0, 35.5, 55.5, 125.5, 225.5, Inf)          # verbatim from create_AQI_unlisted
fasm <- .bincode(NC, breaks)
tad <- ifelse(is.na(NC), NA, ifelse(NC <= 9.0, 1L, ifelse(NC <= 35.4, 2L, ifelse(NC <= 55.4, 3L,
         ifelse(NC <= 125.4, 4L, ifelse(NC <= 225.4, 5L, 6L))))))
ok <- !is.na(fasm) & !is.na(tad)
cat("sensors:", n, " hours:", nrow(X), " nowcast_elapsed_s:", round(el, 2), "\n")
cat("valid NowCast sensor-hours:", sum(ok), "\n")
cat("FASM category != TAD category:", sum(fasm[ok] != tad[ok]), "\n")
for (b in c(35.5, 55.5, 125.5, 225.5)) cat("NowCast exactly", b, ":", sum(NC == b, na.rm = TRUE), "\n")
print(table(FASM = fasm[ok], TAD = tad[ok]))
write.csv(data.frame(NC, check.names = FALSE), file.path(outdir, "r_nowcast_subset.csv"), row.names = FALSE)
