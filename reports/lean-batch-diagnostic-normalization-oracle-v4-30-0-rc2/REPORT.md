# Lean batch diagnostic normalization against relocation and semantic controls

## Summary

On Lean 4.30.0-rc2, changing the input path of a tiny identical module changes its raw JSON diagnostic filename and its `.olean` bytes. Replacing only the known filename field makes those diagnostics equal, and a fixed import query reports the same theorem and axiom dependencies from both artifacts. Yet a different, valid theorem gives the **same normalized compilation diagnostics** while the import query reports a different proposition. Normalized diagnostic equality alone is therefore an unsound oracle for equality of the checked theorem. For this fixture, the combination of exit status, warning/error messages, and a relevant import query accepts the relocated and informationally changed cases and rejects the false or changed theorem cases.

This is executed evidence for #3725 recommendations R34 and R36.

## Applicability

The executed subject is `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, release `v4.30.0-rc2`, on `arm64-apple-darwin24.6.0`. The direct batch compiler binary has SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. The probe invokes `lean --json -o ...` on package-relative Lean filenames and then imports each successful `Probe.olean` through a case-specific `LEAN_PATH`. It does not use Lake, a Lean language server, or Anneal-generated files.

The five retained modules have one `#check` command and one theorem named `arithmetic`. Cases `a` and `b` have byte-identical source in different input directories. Case `c` changes only the `#check` subject. Case `d` asserts a false arithmetic proposition. Case `e` proves a different true arithmetic proposition. The consumer query is identical in each successful case: `import Probe`, `#check arithmetic`, and `#print axioms arithmetic`.

## Findings

| Case | Input difference from `a` | Compile | Normalized full diagnostics vs `a` | `.olean` bytes vs `a` | Fixed consumer query vs `a` |
| --- | --- | --- | --- | --- | --- |
| `b` | Same source, different input path | exit 0 | equal | different | equal |
| `c` | `#check Nat.succ` replaces `#check Nat.zero` | exit 0 | different information message | different | equal |
| `d` | False theorem `1 + 1 = 3` | exit 1 | extra error | absent | unavailable |
| `e` | True theorem `2 + 2 = 4` | exit 0 | equal | different | different |

All comparisons are from **execution**. `support/results/observations.json` retains input and output hashes, exit codes, and boolean comparisons; the five raw JSON streams and successful consumer-query streams are beside it. The `.olean` specimens are retained under `support/results/<case>/Probe.olean`.

### Path normalization needs an independent semantic control

The raw `a` and `b` diagnostic objects differ in `fileName` (`support/a/Probe.lean` versus `support/b/Probe.lean`) and agree after `support/run-probe.py` replaces exactly that field with a common logical name. No diagnostic text, severity, position, or other field is removed. Their source SHA-256 values are equal. The compiled `.olean` hashes differ (`cfad98ad...` versus `f5d53027...`), while the fixed consumer JSON streams are byte-identical. Both report `arithmetic : 1 + 1 = 2` and no axiom dependencies.

The same input path and output path compiled twice yielded the same `.olean` hash. Compiling the same input path to a second output path also yielded that hash. In this small controlled run, the changed input path is therefore sufficient to explain a byte change that output placement alone did not cause. The experiment does not decode the exact differing `.olean` fields.

Basis: **execution**. See `support/results/a.jsonl`, `b.jsonl`, `a-consumer.jsonl`, `b-consumer.jsonl`, and `observations.json`.

### Equal normalized diagnostics can conceal a changed theorem

Case `e` retains `#check Nat.zero`, so its sole compilation information message becomes identical to `a` after filename normalization. Both compilations exit 0, but the fixed consumer query reports `arithmetic : 2 + 2 = 4` for `e` versus `arithmetic : 1 + 1 = 2` for `a`. This is a concrete false positive for any semantic-equivalence oracle consisting only of process success plus normalized compilation diagnostics.

Case `c` shows the converse distinction: its information message differs, but its fixed consumer query agrees with `a`. The report's bounded verification oracle compares exit code, normalized warning/error messages, and the fixed consumer stream. It accepts `a`, `b`, and `c` as equal on those observations and rejects `d` and `e`. It is a deliberately narrow observation contract, not a proof of full module equivalence.

Case `d` provides a failure control: `lean` exits 1, emits a `decide` error explaining that `1 + 1 = 3` is false, and does not write a `.olean` in its clean case output directory.

Basis: **execution** + **derived**. The false-positive conclusion follows directly from equal normalized compilation messages and unequal theorem types observed after importing the compiled modules. See `support/results/e.jsonl`, `e-consumer.jsonl`, `d.jsonl`, and `observations.json`.

## Boundaries

- The consumer query checks one exported theorem's printed type and axiom list. Equal query output does not establish equality of all declarations, proof terms, imports, traces, server setup, or runtime behavior.
- The `.olean` bytes differ under input-path relocation here; this experiment does not determine the internal field responsible or establish the same behavior for all Lean modules and options.
- Only one same-path repeat and one alternate output location were tested. This is a control for this observation, not a characterization of general compiler nondeterminism.
- No `.ilean`, native artifact, Lake trace, cache-seeded build, LSP diagnostic, or cross-platform run was compared.
- The normalization rule is tied to the controlled `support/<case>/Probe.lean` fixture. Applying it to arbitrary paths without a source-identity map could conflate distinct files.

## Evidence

The report contains all source inputs (`support/{a,b,c,d,e}/Probe.lean`), the fixed consumer (`support/query/Query.lean`), a replay script (`support/run-probe.py`), raw relative-path JSON diagnostics, compiled `.olean` specimens for the four successful cases plus the alternate output location, fixed consumer outputs, and `support/results/observations.json`. The latter records the exact local binary SHA-256, version string, per-case source and artifact hashes, exit codes, and comparison outcomes. The command patterns are:

```console
LEAN_BIN=/path/to/pinned/lean python3 support/run-probe.py
lean --json -o support/results/<case>/Probe.olean support/<case>/Probe.lean
LEAN_PATH=support/results/<case> lean --json support/query/Query.lean
```

The script runs from this report package and records package-relative paths in raw messages. It uses Python 3 standard library modules and an already installed Lean binary. Evidence was acquired on 2026-09-28.

## Revalidation

Run `support/run-probe.py` with the intended Lean binary through `LEAN_BIN`, then inspect `support/results/observations.json`. Confirm that the binary revision and hash are the subject being compared. For a newer Lean revision, compare `a` with `b` for relocation, `a` with `e` for a changed but still compiling theorem, and `a` with `d` for rejection. Preserve raw and normalized diagnostic fields, artifact hashes, and the fixed import-query output. If any equality changes, inspect that pair before treating a normalization rule as a cache or verification oracle.
