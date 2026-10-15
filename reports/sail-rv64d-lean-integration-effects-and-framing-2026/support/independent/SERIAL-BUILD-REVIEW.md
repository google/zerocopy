# Serial Sail/Lean adapter review

Read-only source review, 2026-10-15. Reviewed `serial-build.py` (4,679 bytes,
SHA256 `3a3da71abe164bffee5cb48f355263e4e968c24161860ecc6afee6b39ff7e8e4`)
against `serial-build-brief.md` and the two frozen local source roots. No adapter,
Lean, Docker, installation, network or build execution occurred. A separate
Python source-inspection script enumerated imports and computed their graph;
it neither imported the adapter nor wrote build state.

Disposition: suitable for the bounded serial compilation attempt, conditional
on the parent's stated outer timeout, cgroup and disk controls and its existing
byte-frozen runtime/toolchain provenance. No semantic rewriting, surrogate model,
parallel Lake invocation or unintended explicit filesystem write was found.
This is a build-orchestration review, not theorem correctness or axiom closure.

The inspected roots contain 185 `.lean` modules and 996 simple import lines;
all detected import lines satisfy the adapter's exact single-module grammar.
No public/meta/multiline import form or `prelude`/`module` header was found.
For `LeanRV64D` plus `Sail.ArchSemSequential`, the graph has 143 source modules,
no duplicate names and no dependency cycle. It starts with Sail support modules
and ends with `LeanRV64D.InstsEnd`, `DecodeExt`, `Step`, `Main`, `LeanRV64D`.
External imports are exactly `Lean`, `Lean.Elab.Term`, `Lean.Meta.Reduce`,
`Std.Data.ExtDHashMap`, `Std.Data.ExtHashMap`, `Std.Tactic.BVDecide`.
The adapter checks that corresponding core `.olean` files exist. Implicit Init
and their recursive core imports remain the official installation boundary.
The independent text scan found no top-level `initialize`, `builtin_initialize`,
`run_cmd`, `#eval`, or explicit `IO.FS`/`IO.Process` occurrence in these roots.
This supports the intended fixed-input scope, not a sandbox guarantee for
arbitrary future Lean source or imported metaprograms.

Identity handling is appropriate as a continuation of the parent's prior byte
freeze: the compiler executable has a fixed expected SHA256, each source is
hashed into the plan and rechecked immediately before its compilation, and
`LEAN_PATH` is replaced with the fresh artifact directory. The script itself
does not compare source hashes with a preexisting immutable manifest or hash
the toolchain libraries. Therefore retain the parent's frozen source/toolchain
manifest alongside this adapter hash; the adapter's self-generated hash list
alone cannot establish an upstream identity. Run against the intended frozen
container paths, with no concurrent source/toolchain mutation.

The command awaits each Lean process, uses `-j1`, a 4,500 MiB Lean memory limit,
and GNU timeout 300 seconds plus ten seconds termination grace per module.
The internal 1,800-second check runs between modules, so it can overshoot by one
module plus grace. The brief's strict outer 1,800-second timeout must be applied
by the parent; its 6 GiB cgroup and 4 GiB output ceiling are also external,
not enforced by this Python file. The Lean heap limit alone is not a process
RSS limit. `--tstack=400000` does not remove the external memory requirement.

All explicit writes are under newly created `OUT/serial-build`: plan, artifacts,
per-phase stdout/stderr and receipts. Initial `mkdir()` fails if this directory
already exists, preventing partial-build reuse; the script performs no source
rewrite, cleanup or installation. Internal receipt replacement is intentional.
`-o` requests `.olean` output beneath that directory; there is no native/C output
request. The selected working directories are source roots, but no adapter
write targets them. Runtime compiler effects are trusted within the reviewed
official/frozen-source scope rather than prevented by a read-only mount.

Three result qualifications should remain explicit. First, `complete.json`
means all subprocesses returned zero; the adapter does not additionally require
every requested `.olean` to exist or match a separately expected artifact hash.
The parent should verify artifact presence from the receipt before treating
compilation as complete. Second, raw nonzero statuses and exact streams are
retained, but the universal message “compiler rejected module” also covers
timeout, kill and launch errors; classify those operationally from status and
streams, not as proof rejection. A missing `timeout` executable would raise
before a normal result receipt, leaving the plan/streams for diagnosis.
Third, `results.json` replacement is not atomic and abrupt interruption can
leave a partial JSON file; preserved per-phase streams and outer process status
are the fallback evidence. None warrants automatic retry or reuse.

Stop at the first assertion/invariant/unsupported-input failure or nonzero
compiler status and diagnose before a changed run. A successful build checks
these actual generated definitions/imports in the selected Lean installation;
it does not establish a selected ISA theorem, absence of `sorry`/axioms, or a
source-to-generated semantic bridge. Those remain subsequent reviews.
