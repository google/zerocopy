# Support material

Everything here is evidence for `../REPORT.md`, not instructions. File names carry the first
eight hex digits of the `rust-lang/rust` commit they describe.

| File | What it is | How it was produced |
|---|---|---|
| `probe_boxraw_call_guards_and_pipeline_closure.py` | Self-contained `rustc` + Miri probe (Rust sources embedded) | hand-written |
| `probe_results_rustc_14210df0e.json` | Output of the probe on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` with its Miri | **executed** for this report |
| `recorded_observation_rustc_3ef0c22c.json` | Output of an earlier, similar probe on `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` | **retained record, not re-executed**; inputs not preserved |
| `extract_pass_pipeline.py` | Extracts every pass list and every pass policy from `rustc_mir_transform` source | hand-written |
| `pass_pipeline_rustc_bdf712ee.json`, `…_3ef0c22c.json`, `…_14210df0e.json` | Its output at the three examined commits | generated from source |
| `render_pass_table.py` | Renders the table in the report from a pipeline JSON; compares a probe's dump order with source order | hand-written |
| `locate_source_anchors.py`, `source_anchors.json` | Line numbers of every cited source line at the three commits, plus file hashes | generated from source |
| `BoxDerefCallGuardsAndReturnDupSoundness.lean` | The mechanized model (Lean core only, no imports) | hand-written |
| `verify_lean.py`, `lean_verification_result.json` | Checker harness and its recorded output on Lean v4.34.1 | **executed** for this report |

## Re-running

Probe (any nightly; Miri optional, and skipped checks are reported as skipped, never as passed):

```sh
python3 probe_boxraw_call_guards_and_pipeline_closure.py \
    --rustc "$TOOLCHAIN/bin/rustc" \
    --miri "$TOOLCHAIN/bin/miri" --miri-sysroot "$(cargo +nightly miri setup --print-sysroot)" \
    --out probe_results_new.json
```

Pass pipeline at another commit (downloads `compiler/rustc_mir_transform/src` first):

```sh
python3 extract_pass_pipeline.py --fetch <40-hex-commit> --root ./rust-src --out pipeline.json
python3 render_pass_table.py pipeline.json
```

The extractor fails closed (exit status 3, no output file) if any pass-list line is not accounted
for or has a shape it does not recognise.

Lean file:

```sh
python3 verify_lean.py --lean "$(elan which lean)"       # toolchain leanprover/lean4:v4.34.1
```

This runs three checks: the plain file; an environment walk over every constant the file adds
(axioms used; `unsafe`, `partial`, `axiom`, `opaque` and `*._unsafe_rec` constants); and a negative
control (a false theorem appended to a copy must be rejected).

## What the two execution files do and do not show

`probe_results_rustc_14210df0e.json` was produced by a toolchain that predates both
`CastKind::BoxDerefTransmute` and `BoxRaw`. It therefore shows the *older* Box-deref lowering
(`Transmute` of `Unique<T>.0: NonNull<T>`). The newer lowering was not executed for this report;
the only execution trace of it here is the retained record, whose inputs are not preserved.
