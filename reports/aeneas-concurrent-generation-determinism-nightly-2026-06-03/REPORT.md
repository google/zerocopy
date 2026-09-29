# Concurrent Aeneas generation on split Lean output

## Summary

Four concurrent Aeneas processes translating the same fixed LLBC fixture with `-sequential -split-files -gen-lib-entry` wrote byte-identical three-file inventories to independent destinations. Three additional concurrent processes wrote to one precreated shared destination; all exited successfully and the final files matched the isolated-output hashes. The tested processes overlapped in time.

This is a narrow same-input, no-failure case. It shows that this tiny run completed deterministically under external process concurrency, including a shared output directory. It does not establish same-process Aeneas library reentrancy, safe sharing of Lake `.lake` build trees, cancellation/crash consistency, or safety when writers have different inputs.

## Applicability

- Aeneas release binary SHA-256: `f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03`; source revision `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, release label `nightly-2026.06.03`.
- Input: fixed serialized LLBC, SHA-256 `b98023ca3d222796ed4f08e9331e8ffa750c8971daeb786fea37a888b8c8d098`, 19,827 bytes.
- Flags: Lean backend, no progress bar, sequential internal processing, split files, generated library entry.
- Host: macOS arm64. Each parallel run uses an independent Aeneas process. “Concurrent” means measured process intervals overlap; this does not assert simultaneous execution on every CPU core.

## Findings

### Independent destinations produce matching split artifacts

Four Aeneas processes started from a barrier and used four distinct output directories. All exited 0 and overlapped in time. Each wrote `Funs.lean`, `Types.lean`, and `Probe.lean` with identical inventory and hashes:

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `Funs.lean` | 1,260 | `9fdb9d4781b4754efe0bd15153605dd2fb306bd186c5e2ff1e3390521de2ac25` |
| `Probe.lean` | 18 | `88d15c5183e48c512f4ecfb38c430356859b255fe1dcf6a613fd51c7ba36820d` |
| `Types.lean` | 506 | `6451d177e48eacec9f29fd8557abbfb0fbbd8091164a1758465fe839d45083cd` |

Basis: **execution** in `support/concurrency-transcript.json`.

### Same-input writers to one generated-source destination completed cleanly

Three additional Aeneas processes used the same already-created output directory and ran concurrently. All exited 0. The final three files were nonempty and matched the hashes from each independent destination. This does not test writer interruption or differing contents; identical-input last-writer overlap may mask races that would be visible with different generations.

Basis: **execution** in `support/concurrency-transcript.json`.

### The result does not cover Lake's mutable build products

Aeneas writes generated Lean source files to its `-dest` output. The experiment does not ask Lake or Lean to compile those files and does not share `.lake/build`, package configuration, `.olean`, trace/hash caches, or a prepared dependency archive. It therefore cannot be used to claim that multiple consumers may safely write one Lake package/build directory.

Basis: **execution scope** plus **derived** distinction between generator output and compiled build state.

## Boundaries

- One fixed three-function serialized input and one binary/flag tuple were used. There were four isolated-output processes and three shared-destination processes, with no injected delays or failures inside file writes.
- The processes used `-sequential`; this does not test Aeneas internal parallel scheduling or in-process concurrent library requests.
- Same-input writers cannot show how different generations interleave. No output-directory locking, atomic tree publication, rollback, or retry protocol was tested.
- Generated files were not Lean-compiled in this experiment. It establishes neither generated-source semantic equivalence nor Rust-to-Lean correspondence.
- Existing sequential repeat-run and broader Charon/Aeneas fixture reports cover different cells; this report adds one concurrent process cell only.

## Evidence

- `support/probe.py` — executable barrier-started independent and shared-destination runs; set `AENEAS_BIN` to the pinned release binary.
- `support/fixture/probe.llbc` — fixed serialized input.
- `support/concurrency-transcript.json` — run intervals, exit codes, stdout/stderr, inventories, hashes, and overlap checks, with local absolute paths scrubbed.
- `support/parallel-independent/worker-*/` — generated files from four independent destinations.
- `support/parallel-shared-dest/` — final shared-destination output.

Related reports: `aeneas-generated-source-repeat-run-probe-nightly-2026-06-03` tests repeated sequential runs; `rust-llbc-lean-golden-and-aeneas-revision-probes-2026-09-28` records sequential and split-file translation controls; `aeneas-library-process-architecture-nightly-2026-06-03` covers source-level process/library boundaries. These are not replaced by this experiment.

Issue alignment: partial evidence for #3730 D05/E06 and #3731 I081/I148/I151/I159 N05. Different-input shared writers, mid-write termination, process-level cancellation, and same-process concurrent requests remain untested.

## Revalidation

From the package directory, set `AENEAS_BIN` to the binary identified above and run:

```console
AENEAS_BIN=/absolute/path/to/aeneas python3 support/probe.py
```

The script removes and reconstructs only its `parallel-independent/` and `parallel-shared-dest/` fixture directories. Confirm the input/binary hashes, all process exit statuses, interval overlap, file inventory, and byte hashes. Add different-input and injected-failure cases in separate fresh destinations before drawing conclusions about shared-writer safety.
