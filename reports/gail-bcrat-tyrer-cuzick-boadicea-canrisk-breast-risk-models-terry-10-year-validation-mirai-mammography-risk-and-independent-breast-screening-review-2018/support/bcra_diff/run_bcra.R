# Run the BCRA R package on shared profiles.
# Usage: Rscript run_bcra.R <profiles.csv> <out_r.csv> [<R library dir>]
args <- commandArgs(trailingOnly = TRUE)
if (length(args) >= 3) .libPaths(c(args[3], .libPaths()))
suppressPackageStartupMessages(library(BCRA))
cat("BCRA version:", as.character(packageVersion("BCRA")), "\n")
p <- read.csv(args[1], stringsAsFactors = FALSE)
cols <- c("ID", "T1", "T2", "N_Biop", "HypPlas", "AgeMen", "Age1st", "N_Rels", "Race")

run_frame <- function(d) {
  rc <- recode.check(d, Raw_Ind = 1)
  rr <- relative.risk(d, Raw_Ind = 1)
  ab <- absolute.risk(d, Raw_Ind = 1, Avg_White = 0)
  av <- absolute.risk(d, Raw_Ind = 1, Avg_White = 1)
  data.frame(ID = d$ID, Mode = "frame",
             Error_Ind = as.character(rc$Error_Ind), NB_Cat = as.character(rc$NB_Cat),
             AM_Cat = as.character(rc$AM_Cat), AF_Cat = as.character(rc$AF_Cat),
             NR_Cat = as.character(rc$NR_Cat), R_Hyp = as.character(rc$R_Hyp),
             CharRace = as.character(rc$CharRace),
             RR1 = sprintf("%.12g", rr$RR_Star1), RR2 = sprintf("%.12g", rr$RR_Star2),
             AbsRisk = sprintf("%.12g", ab), AvgRisk = sprintf("%.12g", av),
             RError = "", stringsAsFactors = FALSE)
}

# All rows together in one data frame (the usual batch use).
t0 <- proc.time()[["elapsed"]]
res <- run_frame(p[, cols])
t1 <- proc.time()[["elapsed"]]
rnd <- p[p$Set == "random", cols]
t2 <- proc.time()[["elapsed"]]
invisible(absolute.risk(rnd, Raw_Ind = 1, Avg_White = 0))
t3 <- proc.time()[["elapsed"]]
cat(sprintf("TIMING all-rows frame (recode+RR+abs+avg): n=%d elapsed=%.3f s\n", nrow(p), t1 - t0))
cat(sprintf("TIMING absolute.risk on random set: n=%d elapsed=%.3f s (%.1f us/profile)\n",
            nrow(rnd), t3 - t2, 1e6 * (t3 - t2) / nrow(rnd)))

# Solo rows: each run as a one-row data frame; errors captured.
solo <- p[p$Solo == 1, cols]
for (i in seq_len(nrow(solo))) {
  d <- solo[i, , drop = FALSE]
  rc <- recode.check(d, Raw_Ind = 1)
  ab <- tryCatch(sprintf("%.12g", absolute.risk(d, Raw_Ind = 1, Avg_White = 0)),
                 error = function(e) paste("ERROR:", conditionMessage(e)))
  rr <- tryCatch(relative.risk(d, Raw_Ind = 1), error = function(e) NULL)
  res <- rbind(res, data.frame(ID = d$ID, Mode = "solo",
    Error_Ind = as.character(rc$Error_Ind), NB_Cat = as.character(rc$NB_Cat),
    AM_Cat = as.character(rc$AM_Cat), AF_Cat = as.character(rc$AF_Cat),
    NR_Cat = as.character(rc$NR_Cat), R_Hyp = as.character(rc$R_Hyp),
    CharRace = as.character(rc$CharRace),
    RR1 = if (is.null(rr)) "" else sprintf("%.12g", rr$RR_Star1),
    RR2 = if (is.null(rr)) "" else sprintf("%.12g", rr$RR_Star2),
    AbsRisk = if (startsWith(ab, "ERROR")) "" else ab, AvgRisk = "",
    RError = if (startsWith(ab, "ERROR")) ab else "", stringsAsFactors = FALSE))
}
write.csv(res, args[2], row.names = FALSE)
cat("wrote", nrow(res), "rows\n")
