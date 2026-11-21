# Evaluate con2aqi (cran/con2aqi R/con2aqi.R, version 0.1.0) on grid.csv.
# Usage: Rscript run_con2aqi.R <con2aqi.R path> <outdir>
args <- commandArgs(trailingOnly = TRUE)
source(args[1])
outdir <- args[2]
g <- read.csv(file.path(outdir, "grid.csv"), colClasses = c("character", "character"))
map_pol <- c(pm25 = "pm25", pm10 = "pm10", co = "co", so2 = "so2", no2 = "no2", o3_8h = "o3", o3_1h = "o3")
map_typ <- c(pm25 = NA, pm10 = NA, co = NA, so2 = NA, no2 = NA, o3_8h = "8h", o3_1h = "1h")
res <- character(nrow(g))
for (i in seq_len(nrow(g))) {
  p <- g$pollutant[i]
  v <- as.numeric(g$conc[i])
  typ <- if (is.na(map_typ[[p]])) NULL else map_typ[[p]]
  res[i] <- tryCatch({
    a <- con2aqi(map_pol[[p]], v, typ)
    if (is.na(a)) "NA" else format(a, scientific = FALSE)
  }, error = function(e) paste0("ERROR:", gsub("[,\n]", ";", conditionMessage(e))))
}
write.csv(data.frame(pollutant = g$pollutant, conc = g$conc, con2aqi = res), file.path(outdir, "con2aqi.csv"), row.names = FALSE)
cat("rows:", nrow(g), "\n")
