Support material for this report (text only).

c/*.c                 Self-written C programs with correlated branches over a heap cell.
                      Names: corr_* (safe), uaf_bug/leak_bug (bugs), param2_* (branch
                      conditions are formal parameters), nd2_*/ndtrue_*/ndfalse_*/ndmixed_*
                      (branch conditions are results of an unknown function nondet()).
java/Corr.java        Self-written Java methods closing a FileInputStream under correlated
                      branches (*Safe methods never leak; leakBug leaks).
run_infer_c.sh        Usage: run_infer_c.sh <infer-binary> <workdir>. Runs Infer Pulse on
                      every c/*.c with --pulse-max-disjuncts in {1,2,4,8,16,20,64,256}.
run_java.sh           Usage: run_java.sh <checker-framework-dir> <infer-binary> <workdir>.
                      Runs the Resource Leak Checker and Infer Pulse on java/Corr.java.
output/infer_pulse_c_sweep.txt     Output of run_infer_c.sh (Infer v1.3.0 release binary).
output/infer_pulse_corr_java.txt   Infer v1.3.0 report.txt for java/Corr.java.
output/rlc_corr_java.txt           Checker Framework 4.4.0 -processor resourceleak output
                                   for java/Corr.java, followed by /usr/bin/time output.
