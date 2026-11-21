# Band-edge and special-input probe of con2aqi (cran/con2aqi R/con2aqi.R).
# Usage: Rscript edge_con2aqi.R <con2aqi.R path>
args <- commandArgs(trailingOnly = TRUE)
source(args[1])
show <- function(p, v, t = NULL) {
  r <- tryCatch(format(con2aqi(p, v, t)), error = function(e) paste("ERROR:", conditionMessage(e)))
  cat(sprintf("%-5s %-4s %-10s -> %s\n", p, ifelse(is.null(t), "", t), format(v, digits = 17), r))
}
# band tops and bottoms of PM2.5 (pre-2024 table)
for (v in c(12.0, 12.05, 12.1, 35.4, 35.45, 35.5, 55.4, 55.5, 150.4, 150.5, 250.4, 250.5, 350.4, 350.5, 500.4, 500.5)) show("pm25", v)
for (v in c(54, 54.5, 55, 154, 155, 424, 425, 504, 505, 604)) show("pm10", v)
for (v in c(4.4, 4.45, 4.5, 9.4, 9.5, 12.4, 15.4, 30.4, 40.4, 50.4)) show("co", v)
for (v in c(0.054, 0.0545, 0.055, 0.070, 0.071, 0.085, 0.105, 0.2)) show("o3", v, "8h")
for (v in c(0, 0.05, 0.1, 0.124, 0.125, 0.164, 0.165)) show("o3", v, "1h")
for (v in c(-5, -0.1)) show("pm25", v)
show("o3", 0.05)          # type omitted
show("no2", 2050)         # error message names the wrong pollutant
# floating-point view of breakpoints as constructed by bpl[-1]-step
bpl <- c(0, 12.1, 35.5, 55.5, 150.5, 250.5, 350.5); bph <- c(bpl[-1] - 0.1, 500.4)
cat("pm25 bph == literal:", paste(bph == c(12.0, 35.4, 55.4, 150.4, 250.4, 350.4, 500.4), collapse = " "), "\n")
cat("pm25 bph (17 sig digits):", paste(format(bph, digits = 17), collapse = " "), "\n")
bpl <- c(0, 0.055, 0.071, 0.086, 0.106); bph <- c(bpl[-1] - 0.001, 0.2)
cat("o3_8h bph == literal:", paste(bph == c(0.054, 0.070, 0.085, 0.105, 0.2), collapse = " "), "\n")
bpl <- c(0, 4.5, 9.5, 12.5, 15.5, 30.5, 40.5); bph <- c(bpl[-1] - 0.1, 50.4)
cat("co bph == literal:", paste(bph == c(4.4, 9.4, 12.4, 15.4, 30.4, 40.4, 50.4), collapse = " "), "\n")
