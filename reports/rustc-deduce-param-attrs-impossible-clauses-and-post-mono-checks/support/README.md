# Support material

Everything in this directory is evidence for `../REPORT.md`. Nothing here is an
instruction to a reader or to a tool; scripts are provided so that the
observations can be repeated.

## Differential probe (real compiler execution)

| Path | Content |
| --- | --- |
| `probe_deduce_param_attrs_impossible_clauses_and_mono_checks.py` | Standard-library-only Python script. Compiles the embedded Rust sources with the `rustc` given by `--rustc`, parses the emitted LLVM IR signatures, MIR and diagnostics, and writes one JSON document. Its `PREDICTED_*` tables are expectations derived from reading rustc source at `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`; they are compared with, never substituted for, what the compiler produced. |
| `results/local_rustc-1.98.0-nightly-14210df0e.json` | Output of the probe run on 2026-11-22 with `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, LLVM 22.1.6, host `x86_64-unknown-linux-gnu`. A second run produced a byte-identical file. |
| `results/recorded_rustc-1.102.0-nightly-3ef0c22cd.json` | A record of an earlier, smaller probe executed with `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, LLVM 23.1.5. It was **not** produced or re-run by the investigation that wrote this package and it does not contain the Rust sources it compiled; it is kept byte-for-byte as received. Its `probe_id` field is an opaque label of the harness that produced it. `../REPORT.md` explains how far it can be relied on. |
| `specimens/rust/` | The Rust sources embedded in the probe, written out by `--dump-sources`. |
| `specimens/mir/` | Optimized MIR of the upstream crate (non-incremental and incremental) and of the two auxiliary crates, as emitted by the 1.98.0-nightly run (`--dump-mir`). |

Repeat with any nightly toolchain:

```sh
python3 probe_deduce_param_attrs_impossible_clauses_and_mono_checks.py \
  --rustc "$(rustup which --toolchain nightly rustc)" \
  --baseline results/recorded_rustc-1.102.0-nightly-3ef0c22cd.json \
  --out /tmp/probe_results.json
```

The probe needs a target on which a 64-byte aggregate is passed by hidden
pointer under the Rust ABI and on which `avx` gates 256-bit vector registers
(it was only run on `x86_64-unknown-linux-gnu`).

## Lean development (kernel-checked model)

| Path | Content |
| --- | --- |
| `DeduceParamAttrsImpossibleClausesAndMonoChecksSoundness.lean` | Single-file Lean 4 development; the header comment states what is modelled and what is not. |
| `lean_check.sh` | Runs the exact check command. |
| `lean_audit_negative_controls.sh` | Checks two deliberately broken copies and expects both to be rejected. |
| `lean_check_transcript.txt` | Output of both scripts' commands with Lean 4.34.1 on 2026-11-22. |

```sh
bash lean_check.sh "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
bash lean_audit_negative_controls.sh "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
```

## Upstream source excerpts

`upstream/rust-lang-rust-<commit>/…` holds unmodified copies of the rustc source
files the report quotes most heavily, fetched from
`https://raw.githubusercontent.com/rust-lang/rust/<commit>/<path>`. They are
part of the Rust project and are distributed under its MIT/Apache-2.0 dual
licence; they are included so that the quoted line numbers can be checked
without a checkout.

| Commit | Files |
| --- | --- |
| `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `compiler/rustc_mir_transform/src/deduce_param_attrs.rs`, `compiler/rustc_middle/src/middle/deduced_param_attrs.rs`, `compiler/rustc_mir_transform/src/impossible_clauses.rs`, `compiler/rustc_monomorphize/src/mono_checks/{mod.rs,abi_check.rs,move_check.rs}` |
| `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_mir_transform/src/deduce_param_attrs.rs`, `compiler/rustc_mir_transform/src/impossible_predicates.rs` |

## Integrity

`SHA256SUMS` lists the SHA-256 of every other file in this directory
(`sha256sum -c SHA256SUMS` from here).
