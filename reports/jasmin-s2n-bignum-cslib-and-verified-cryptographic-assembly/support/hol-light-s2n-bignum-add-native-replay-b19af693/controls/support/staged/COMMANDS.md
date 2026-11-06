# Exact proposed operations; none staged, compiled or executed

All runtime commands below are inside the already-assigned container, after a new explicit parent grant. Parent/worker must stage the frozen control-plan data/source/scripts under the new controls subtree, verify every hash and preserve the original positive subject. Variables are literal future task roots:

```sh
TASK_HOL=/home/opam/anneal-cross-sources/hol-light
TASK_S2N=/home/opam/anneal-cross-sources/s2n-bignum
CTRL_ROOT=/home/opam/anneal-cross-output/controls
export TASK_HOL TASK_S2N CTRL_ROOT
export OPAMROOT=/home/opam/anneal-hol-opam LC_ALL=C
export HOLLIGHT_DIR="$TASK_HOL" HOLLIGHT_LOAD_PATH=
```

Three sequential producer invocations, each captured separately and consumed only after its actual source/artifact gate passes. Do not run the module make or original full bignum-add proof:

```sh
opam exec --switch=hol54 -- timeout --signal=KILL 300 \
  bash "$CTRL_ROOT/build-one-control.sh" ImporterControl
opam exec --switch=hol54 -- timeout --signal=KILL 300 \
  bash "$CTRL_ROOT/build-one-control.sh" ArithmeticObservation
opam exec --switch=hol54 -- timeout --signal=KILL 300 \
  bash "$CTRL_ROOT/build-one-control.sh" AxiomPolicyNegative
```

The **combined** producer allowance is300s, not300s each. These exact commands do not authorize proceeding after any producer failure. All listed native invocations are separate processes, run sequentially from `$TASK_S2N`, with their own complete stdout/stderr and status receipts:

```sh
cd "$TASK_S2N"
opam exec --switch=hol54 -- timeout --signal=KILL 120 \
  "$CTRL_ROOT/ImporterControl.native" C0 "$CTRL_ROOT/objects/original.o"
opam exec --switch=hol54 -- timeout --signal=KILL 120 \
  "$CTRL_ROOT/ImporterControl.native" C1 "$CTRL_ROOT/objects/original.o"
opam exec --switch=hol54 -- timeout --signal=KILL 120 \
  "$CTRL_ROOT/ImporterControl.native" C2 "$CTRL_ROOT/objects/bad-text.o"
opam exec --switch=hol54 -- timeout --signal=KILL 120 \
  "$CTRL_ROOT/ImporterControl.native" C3 "$CTRL_ROOT/objects/wrong-machine.o"
opam exec --switch=hol54 -- timeout --signal=KILL 120 \
  "$CTRL_ROOT/ImporterControl.native" C4 "$CTRL_ROOT/objects/renamed-symbol.o"
opam exec --switch=hol54 -- timeout --signal=KILL 120 \
  "$CTRL_ROOT/ArithmeticObservation.native"
opam exec --switch=hol54 -- timeout --signal=KILL 120 \
  "$CTRL_ROOT/AxiomPolicyNegative.native"
# First observe that objects/missing.o does not exist; never create/delete it.
opam exec --switch=hol54 -- timeout --signal=KILL 120 \
  "$CTRL_ROOT/ImporterControl.native" C9 "$CTRL_ROOT/objects/missing.o"
```

The core-only negative process remains separate; never concatenate its ML or load it into a positive/importer process. A baseline import, and the expected marker for each positive/negative case, must establish that failures occur at the intended operation rather than setup.

Separate ordinary data observations (no HOL process), each with explicit status and full stream capture:

```sh
python3 -B "$CTRL_ROOT/require_symbol.py" "$CTRL_ROOT/objects/original.o"
python3 -B "$CTRL_ROOT/require_symbol.py" "$CTRL_ROOT/objects/renamed-symbol.o"
python3 -B "$CTRL_ROOT/check_shadow_fixture.py" \
  "$CTRL_ROOT/fixtures/forbidden-checker-definition.txt"
```

C8 is a **host** copied-log check, with a newly authorized owned destination. `FROZEN_POSITIVE` names the frozen positive report package, and `NEW_LOG_FIXTURE` must not exist and must be outside that package:

```sh
python3 -B /owned/control-plan/prepare_log_control.py \
  "$FROZEN_POSITIVE" "$NEW_LOG_FIXTURE"
python3 -B "$NEW_LOG_FIXTURE/verify_positive.py"
```

Expect the unchanged verifier's final nonzero due to `outer_end_once=false`, with all other positive acceptance checks true. Its copied receipt deliberately rebinds the truncated stream hash while asserting exit0, so the intended discriminator is completeness rather than a stale SHA. It writes only the new fixture's verification/theorem JSON files. Preserve these outputs and the original positive stream/hash. No positive native program is called for C8.

No line invokes `selected.native`, `native_once.py`, a package manager, network, cleanup or a new runtime. These are proposed commands, not a shell script to execute wholesale; the owner must check each phase result before its dependents.
