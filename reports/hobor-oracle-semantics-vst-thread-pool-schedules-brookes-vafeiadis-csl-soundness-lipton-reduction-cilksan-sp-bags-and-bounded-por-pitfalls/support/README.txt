Support material for this report (text only).

toy/nested_par_schedulers.py   Self-written toy model comparing three ways of resolving
                               nondeterminism in nested parallel composition
                               (full interleaving, one bit per step, per-node path
                               selector). Standard library only.
toy/output.txt                 Output of: python3 toy/nested_par_schedulers.py

spin/indep.pml                 N processes with purely local increments (POR best case).
spin/ignoring.pml              Infinite local loop in parallel with a failing global
                               assertion (exercises the cycle proviso).
spin/nexttime.pml              Two processes and the non-stutter-invariant property
                               X (g == 0).
spin/run_spin.sh               Usage: run_spin.sh <spin-binary> <outdir>. Builds each
                               model with and without -DNOREDUCE and records pan output.
spin/output/                   Raw spin -a and pan outputs, and summary.txt.

loom/Cargo.toml, loom/src/main.rs
                               Two-thread probe whose failing interleaving needs two
                               preemptions; Loom is pinned by git rev.
loom/run.sh                    Builds and runs the probe for LOOM_MAX_PREEMPTIONS in
                               {0,1,2,3,unset}, with the assertion on and off.
loom/output.txt                Recorded output (with rustc and cargo versions).
