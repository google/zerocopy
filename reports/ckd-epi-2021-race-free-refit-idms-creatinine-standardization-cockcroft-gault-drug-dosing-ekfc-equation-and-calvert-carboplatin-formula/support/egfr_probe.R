# Differential probe: kidney.epi 1.4.0 vs nephro 1.5 eGFR functions on shared synthetic inputs.
# Usage: KIDNEY_EPI_DIR=<extracted kidney.epi tree> NEPHRO_DIR=<extracted nephro tree> Rscript egfr_probe.R
# Sources the packages' own R files (no installation), so the exact upstream function bodies execute.
ke <- Sys.getenv("KIDNEY_EPI_DIR"); ne <- Sys.getenv("NEPHRO_DIR")
for (f in c("service.general.R", "service.check_plausibility.R", "egfr_ckdepi2021.R", "egfr_ckdepi2009.R",
            "egfr_ekfc.R", "egfr_mdrd.R", "egfr_other_adults.R")) source(file.path(ke, "R", f))
source(file.path(ne, "R", "nephro.R"))
options(width = 200, digits = 10, warn = 1)
cat("R:", R.version.string, "\n")

q <- function(expr) tryCatch(suppressWarnings(expr), error = function(e) paste0("ERROR:", conditionMessage(e)))
fmt <- function(x) if (is.character(x)) x else formatC(as.numeric(x), digits = 6, format = "f")

cat("\n## GRID (Scr in mg/dL; ke = kidney.epi, ne = nephro)\n")
cat("sex,age,scr,ke2021,ne2021,ke2009,ne2009,keEKFC,neEKFC,keMDRDdefault,keMDRDidms,neMDRDdefault,neMDRDlower_idms,keCG70,neCG70\n")
for (sx in c(0, 1)) for (age in c(20, 40, 60, 80)) for (scr in c(0.5, 0.7, 0.9, 1.2, 2.0, 4.0)) {
  s <- ifelse(sx == 1, "Male", "Female")
  v <- c(
    q(egfr.ckdepi.cr.2021(creatinine = scr, age = age, sex = s, creatinine_units = "mg/dl")),
    q(as.numeric(CKDEpi2021.creat(scr, sx, age))),
    q(egfr.ckdepi.cr.2009(creatinine = scr, age = age, sex = s, creatinine_units = "mg/dl")),
    q(as.numeric(CKDEpi.creat(scr, sx, age, 0))),
    q(egfr.ekfc.cr(creatinine = scr, age = age, sex = s, creatinine_units = "mg/dl")),
    q(as.numeric(EKFC.creat(scr, sx, age))),
    q(egfr.mdrd4(creatinine = scr, age = age, sex = s, ethnicity = "none", creatinine_units = "mg/dl")),
    q(egfr.mdrd4(creatinine = scr, age = age, sex = s, ethnicity = "none", creatinine_units = "mg/dl", creatinine_method = "IDMS")),
    q(as.numeric(MDRD4(scr, sx, age, 0))),
    q(as.numeric(MDRD4(scr, sx, age, 0, method = "idms"))),
    q(egfr.cg.cr(creatinine = scr, age = age, sex = s, weight = 70, creatinine_units = "mg/dl")),
    q(as.numeric(CG(scr, sx, age, 70)))
  )
  cat(paste(c(sx, age, scr, sapply(v, fmt)), collapse = ","), "\n")
}

cat("\n## EDGE CASES (one row per case: label | kidney.epi | nephro)\n")
edge <- function(label, kexpr, nexpr) cat(sprintf("%-58s | %-22s | %s\n", label, paste(sapply(q(kexpr), fmt), collapse = " "),
                                                  paste(sapply(q(nexpr), fmt), collapse = " ")))
edge("2021 F age40 scr=0", egfr.ckdepi.cr.2021(0, 40, "Female", creatinine_units = "mg/dl"), CKDEpi2021.creat(0, 0, 40))
edge("2021 F age40 scr=-1", egfr.ckdepi.cr.2021(-1, 40, "Female", creatinine_units = "mg/dl"), CKDEpi2021.creat(-1, 0, 40))
edge("2021 F age40 scr=NA", egfr.ckdepi.cr.2021(NA_real_, 40, "Female", creatinine_units = "mg/dl"), CKDEpi2021.creat(NA, 0, 40))
edge("2021 F age=18.0 scr=0.8", egfr.ckdepi.cr.2021(0.8, 18, "Female", creatinine_units = "mg/dl"), CKDEpi2021.creat(0.8, 0, 18))
edge("2021 F age=18.5 scr=0.8", egfr.ckdepi.cr.2021(0.8, 18.5, "Female", creatinine_units = "mg/dl"), CKDEpi2021.creat(0.8, 0, 18.5))
edge("2021 F age=10 scr=0.8", egfr.ckdepi.cr.2021(0.8, 10, "Female", creatinine_units = "mg/dl"), CKDEpi2021.creat(0.8, 0, 10))
edge("2021 F age=99.9 scr=0.8", egfr.ckdepi.cr.2021(0.8, 99.9, "Female", creatinine_units = "mg/dl"), CKDEpi2021.creat(0.8, 0, 99.9))
edge("2021 F age=100 scr=0.8", egfr.ckdepi.cr.2021(0.8, 100, "Female", creatinine_units = "mg/dl"), CKDEpi2021.creat(0.8, 0, 100))
edge("2021 F age=150 scr=0.8", egfr.ckdepi.cr.2021(0.8, 150, "Female", creatinine_units = "mg/dl"), CKDEpi2021.creat(0.8, 0, 150))
edge("2021 sex unknown ('X' / code 2) age40 scr=0.8", egfr.ckdepi.cr.2021(0.8, 40, "X", creatinine_units = "mg/dl"), CKDEpi2021.creat(0.8, 2, 40))
edge("2021 F age40 value 1.0 entered without units arg", egfr.ckdepi.cr.2021(1.0, 40, "Female"), CKDEpi2021.creat(1.0, 0, 40))
edge("2021 F age40 88.4 umol/L (units given)", egfr.ckdepi.cr.2021(88.4, 40, "Female", creatinine_units = "micromol/l"), CKDEpi2021.creat(1.0, 0, 40))
edge("2021 F age40 88.4 passed to mg/dL-only nephro", egfr.ckdepi.cr.2021(88.4, 40, "Female", creatinine_units = "micromol/l"), CKDEpi2021.creat(88.4, 0, 40))
edge("EKFC F age=2.0 scr=0.3", egfr.ekfc.cr(0.3, 2, "Female", creatinine_units = "mg/dl"), EKFC.creat(0.3, 0, 2))
edge("EKFC F age=1.5 scr=0.3", egfr.ekfc.cr(0.3, 1.5, "Female", creatinine_units = "mg/dl"), EKFC.creat(0.3, 0, 1.5))
edge("EKFC F age=10 scr=0.5", egfr.ekfc.cr(0.5, 10, "Female", creatinine_units = "mg/dl"), EKFC.creat(0.5, 0, 10))
edge("EKFC sex unknown ('X' / code 2) age40 scr=0.8", egfr.ekfc.cr(0.8, 40, "X", creatinine_units = "mg/dl"), EKFC.creat(0.8, 2, 40))
edge("EKFC M age40 scr=0.0", egfr.ekfc.cr(0, 40, "Male", creatinine_units = "mg/dl"), EKFC.creat(0, 1, 40))
edge("CG F age=150 wt70 scr=1.0", egfr.cg.cr(1.0, 150, "Female", 70, creatinine_units = "mg/dl"), CG(1.0, 0, 150, 70))
edge("CG M age40 wt=0 scr=1.0", egfr.cg.cr(1.0, 40, "Male", 0, creatinine_units = "mg/dl"), CG(1.0, 1, 40, 0))
edge("MDRD4 M age40 scr1.0 method default", egfr.mdrd4(1.0, 40, "Male", ethnicity = "none", creatinine_units = "mg/dl"), MDRD4(1.0, 1, 40, 0))
edge("MDRD4 M age40 scr1.0 method 'idms' (lowercase)", egfr.mdrd4(1.0, 40, "Male", ethnicity = "none", creatinine_units = "mg/dl", creatinine_method = "idms"), MDRD4(1.0, 1, 40, 0, method = "idms"))
cat("\n## TYPE OF RETURN VALUE\n")
cat("class(nephro EKFC.creat) =", class(EKFC.creat(c(0.8, 1.0), c(0, 1), c(40, 50))), "; dim =", dim(EKFC.creat(c(0.8, 1.0), c(0, 1), c(40, 50))), "\n")
cat("class(kidney.epi egfr.ekfc.cr) =", class(egfr.ekfc.cr(c(0.8, 1.0), c(40, 50), c("Female", "Male"), creatinine_units = "mg/dl")), "\n")
cat("\n## WARNINGS EMITTED BY kidney.epi FOR AGE 18.0\n")
withCallingHandlers(egfr.ckdepi.cr.2021(0.8, 18, "Female", creatinine_units = "mg/dl"),
  warning = function(w) { cat("WARNING:", conditionMessage(w), "\n"); invokeRestart("muffleWarning") })
