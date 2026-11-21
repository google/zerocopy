# Installs CRAN dependencies and the two packages from source trees checked
# out at the pinned revisions (albgarre/bioinactivation@3ca6bffa464897bebc233ef32f1bd79748ace674,
# albgarre/biogrowth@63fabbdde5ccb76c94f60a4382d140f8cd5e1b69). Set SRC to the directory
# holding both checkouts. Observed with R 4.4.2 (rocker/r-ver:4.4.2 image).
SRC <- Sys.getenv("SRC", ".")
options(Ncpus = 4)
deps <- c("dplyr", "deSolve", "FME", "lazyeval", "ggplot2", "MASS", "rlang", "purrr",
          "tidyr", "tibble", "cowplot", "formula.tools", "lamW", "scales")
install.packages(setdiff(deps, rownames(installed.packages())))
desc <- read.dcf(file.path(SRC, "biogrowth", "DESCRIPTION"))
imp <- trimws(gsub("\\(.*\\)", "", strsplit(desc[, "Imports"], ",")[[1]]))
imp <- setdiff(imp[imp != ""], c(rownames(installed.packages()), "stats", "graphics", "utils", "methods", "grDevices"))
if (length(imp)) install.packages(imp)
install.packages(file.path(SRC, "bioinactivation"), repos = NULL, type = "source")
install.packages(file.path(SRC, "biogrowth"), repos = NULL, type = "source")
cat("bioinactivation", as.character(packageVersion("bioinactivation")),
    "biogrowth", as.character(packageVersion("biogrowth")),
    "deSolve", as.character(packageVersion("deSolve")),
    "FME", as.character(packageVersion("FME")), R.version.string, "\n")
