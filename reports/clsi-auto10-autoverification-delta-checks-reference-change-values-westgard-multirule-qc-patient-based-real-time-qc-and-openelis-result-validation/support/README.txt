Support material for the laboratory autoverification / QC report (text only).

oe_java/build_and_run.sh  Downloads 11 OpenELIS Global 2 classes (unmodified) at the commit pinned in REPORT.json,
                          compiles them with oe_java/stubs/ (annotation, data-holder and verbatim-copied helper stubs)
                          and oe_java/Probe.java, then runs the boundary probe. Needs curl and JDK >= 17.
                          Run: WORK=<scratch dir> bash oe_java/build_and_run.sh
oe_probe.out              Output (OpenJDK 27.0.1), including SHA-256 of each downloaded upstream file.
lab_qc_sim.py             TOY MODELS (synthetic parameters): reference change values, delta checks, multirule QC
                          power, rolling-statistics absorption, moving-average patient-based QC.
                          Run: python3 lab_qc_sim.py 20261121   (Python >= 3.10, numpy). Output: lab_qc_sim.out.
Toy-model numbers describe rule definitions, not any laboratory, analyser or deployed system.
