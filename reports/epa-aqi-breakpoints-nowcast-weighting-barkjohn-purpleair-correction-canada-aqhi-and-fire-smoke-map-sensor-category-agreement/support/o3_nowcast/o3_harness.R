# Harness for USEPA/O3-Nowcast at 5d3c32c04eeaae3a1ca1bc487c311ca7bf46bf6f.
# Usage: Rscript o3_harness.R <repo_dir> <variant: upd|orig>
args <- commandArgs(trailingOnly = TRUE)
repo <- args[1]; variant <- args[2]
suppressMessages({
  source(file.path(repo, if (variant == "upd") "NowcastFun_Upd.r" else "NowcastFun.r"))
  source(file.path(repo, "GetNowcast.r"))
})
d <- read.table(file.path(repo, "ExampleData.csv"), header = TRUE, fill = TRUE, sep = ",", stringsAsFactors = FALSE)
d$Value <- suppressWarnings(as.numeric(d$Value))
# The upstream runner uses format "%m/%d/%Y %H:%M", which does not match the ISO timestamps in ExampleData.csv:
cat("upstream-format parse NA count:", sum(is.na(as.POSIXct(d$LST, tz = "UTC", format = "%m/%d/%Y %H:%M"))), "of", nrow(d), "\n")
d$LST <- as.POSIXct(d$LST, tz = "UTC", format = "%Y-%m-%d %H:%M:%S")
tdata <- d[, c("Value", "LST")]
cat("rows:", nrow(tdata), " non-NA:", sum(!is.na(tdata$Value)), " max NA run:", get.max.na.stream(tdata$Value), "\n")
rm8 <- zoo::rollapply(tdata$Value, list(-4:3), fill = 'NA', align = 'center', FUN = function(x) {
  if (length(grep(T, is.na(x))) / length(x) <= 0.25) mean(x, na.rm = T) else NA })
cat("class of rolling 8-h mean vector with fill='NA':", class(rm8), " is.na count:", sum(is.na(rm8)), "\n")
t0 <- proc.time()
res <- tryCatch(GetNowcast(tdata, sum(!is.na(tdata$Value)), dataStreamId = 1, op.mode = FALSE),
                error = function(e) { cat("GetNowcast ERROR:", conditionMessage(e), "\n"); NULL })
el <- proc.time() - t0
if (!is.null(res)) { cat("NowCast:", format(res$NowCast, digits = 10), " MethodID:", res$MethodID, " Message:", res$Message, "\n") }
cat("elapsed_s:", round(el[["elapsed"]], 3), "\n")
if (variant == "orig" && !is.null(res)) {
  # Equivalence check: pls::mvr with default ncomp uses all components; compare with OLS (lm) on the same design.
  x <- imputeTS::na_ma(tdata$Value)
  y <- as.numeric(rm8)
  M <- t(sapply(96:336, function(r) x[(r - 95):r]))
  df <- data.frame(M, Mean8Hr = y[96:336]); colnames(df) <- c(paste0("Hr", 1:96), "Mean8Hr")
  train <- df[!is.na(df$Mean8Hr), ]
  f <- as.formula(paste("Mean8Hr ~", paste(paste0("Hr", 1:96), collapse = "+")))
  m <- pls::mvr(f, data = train)
  cat("training rows:", nrow(train), " mvr ncomp used:", m$ncomp, " method:", m$method, "\n")
  p_pls <- predict(m, newdata = df)[, , m$ncomp]
  l <- lm(f, data = train)
  p_lm <- predict(l, newdata = df)
  cat("last-row PLS(all comps):", format(tail(p_pls, 1), digits = 10), " OLS:", format(tail(p_lm, 1), digits = 10),
      " max|diff| over rows:", format(max(abs(p_pls - p_lm)), digits = 3), "\n")
  for (k in c(1, 2, 3, 5, 10, 20)) {
    mk <- pls::mvr(f, ncomp = k, data = train)
    cat(sprintf("ncomp=%d last-row prediction=%.4f\n", k, tail(predict(mk, newdata = df)[, , k], 1)))
  }
  cat("surrogate 0.85*last+4.5 =", 0.85 * tail(tdata$Value, 1) + 4.5, "  last hourly value:", tail(tdata$Value, 1), "\n")
}
