# Lean 4.29 versus 4.30-rc2 Unicode LSP encoding-offer boundary

## Summary

The exact Unicode fixture and coordinate oracle from the [Lean 4.30.0-rc2 UTF-8-only/UTF-16-only report](../anneal-3731-i062-utf8-only-unicode-lsp-2026-09-30/REPORT.md) were replayed once under locally installed **Lean 4.29.0**, with two sequential direct server sessions and two fresh batch checks. The **diagnostic ranges, incremental-edit outcomes, wait responses and batch JSON messages were the same** at the two pins in this one fixture. Both servers omitted an explicit `positionEncoding`, both emitted the initial error at UTF-16 characters **16–27** despite one UTF-8-only offer, the UTF-8-counted edit led to an unexpected-end error, and the UTF-16-counted edit cleared it. Original/patched batch exits were 1/0 at both pins.

One initialize-capability field **did differ**: Lean 4.30.0-rc2 advertised `experimental.rpcProvider.rpcWireFormat: "v1"`; Lean 4.29.0 did not contain that field. No RPC operation was requested, so this is a capability-object difference, not tested RPC behavior. This is bounded version evidence for #3731 **I062**; the product gate and prerequisite remain unchanged.

## Applicability

The observed older binary was installed locally as Lean **4.29.0** on arm64 macOS, executable SHA-256 `2974847fff2e2621502841f4c2dbac4035b4847d6060a4f2087cbc0d04005e37`. Its version label was read during preflight; this package retains the executable hash as the firm identity but no raw `lean --version` transcript. The published comparison binary was Lean **4.30.0-rc2**, executable SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. The latter's exact acquired [results](baseline-v430-results.json) and batch JSON stdout are retained here as byte-for-byte copies; their hashes match the published package.

The [original](fixture/Encoding.lean), [intended patch](fixture/EncodingPatched.lean), [oracle generator](oracle.py) and [oracle](oracle.json) are byte-identical to the 4.30.0-rc2 report. The source contains `😀é` before `unknownName`, whose start is scalar 15, UTF-16 unit 16 and UTF-8 byte 19. The older-version [runner](probe.py) changed only the pinned Lean executable path/hash, work location and its own result bytes; it recorded the oracle SHA-256 `7f7aac75610935a82f2382381ca0fbab519eaee9abb26767dcd90ab8cabe4cc7` before launching either server. Both sessions offered a single encoding (`utf-8` or `utf-16`) and used `LEAN_NUM_THREADS=1`, private directories and one stdio client. No installation, network, Lake environment, Anneal projection, editor or MCP adapter was used.

## Findings

| Observation | Lean 4.29.0 | Lean 4.30.0-rc2 |
| --- | --- | --- |
| UTF-8-only and UTF-16-only initialize `positionEncoding` | absent | absent |
| Both initial `unknownName` diagnostic ranges | line 0, chars 16–27 | line 0, chars 16–27 |
| UTF-8-byte range 19–30 incremental replacement | unexpected end of input | unexpected end of input |
| UTF-16 range 16–27 incremental replacement | no error; `Nat.zero` information message | same |
| Original/patched batch exits | 1/0 | 1/0 |
| Batch JSON messages, excluding absolute `fileName` | same | same |
| Initialize `/experimental/rpcProvider/rpcWireFormat` | absent | `"v1"` |

The [checker](check.py) reparses this run's raw client/server frames and compares both versions' full initial/post-edit diagnostic arrays, both `waitForDiagnostics` responses and both shutdown responses. It compares the initialize capabilities after removing the 4.30.0-rc2-only `rpcWireFormat` key; no other decoded capability field differs in either session. The UTF-8-only older server produced one more transient `$/lean/fileProgress` notification than the prior run (eight versus seven); diagnostic publications, responses and final classifications match. Notification counts are schedule observations, not a version contract. **Basis: execution at 4.29.0 and exact retained published 4.30.0-rc2 evidence.**

The single run's initial preflight measured **36.5541%** estimated reclaimable host memory and **18,709,319,680 bytes** free disk. Both server launch preflights exceeded 30% and 10 GiB. The UTF-8-only server's maximum sampled process-group RSS was **197,744 KiB**, minimum reclaimable estimate **34.1024%**, minimum free disk **18,703,355,904 bytes**, maximum scratch **9,332 bytes**; the UTF-16-only server's corresponding values were **120,720 KiB**, **34.6121%**, **18,705,031,168 bytes** and **16,426 bytes**. Both server exits were 0 with zero postrun process-group RSS, and the first ended before the second began. Fresh batch original/patched exits were 1/0, with maximum sampled RSS **105,920 KiB**. The private work tree was removed. No 20%-memory, 10-GiB-disk, 1.2-GiB-RSS, 100-MiB-scratch or 30-second/session guard fired. Sampling can miss shorter peaks. **Basis: execution.**

## Boundaries

This is one file, two offered encodings, one incremental replacement and two locally installed versions on one host. It establishes neither a general Lean version contract nor behavior of a newer release. The missing explicit `positionEncoding` and the failed UTF-8-counted edit are observations, not a protocol-conformance judgment; the server did not return the complete post-edit document text. The changed RPC capability field was not exercised by an RPC request.

There is no Rust-hosted Anneal projection, real editor, generated obligation, cross-tool source map or independent operator. I062 remains **partial** at its existing **product** gate. B03 and I025 can use this only as bounded coordinate context; their residuals, statuses, gates and prerequisites remain unchanged. A future upgrade test should repeat the same wire controls against a selected later compatible Lean release before deleting any workaround.

## Evidence

[probe.py](probe.py) is the exact guarded one-shot acquisition script. [results.json](results.json) retains full argv, selected environment, PIDs, timing, decoded messages, resource samples and cleanup. [raw/](raw/) retains complete framed client/server bytes and batch stdout/stderr. [comparison.json](comparison.json) lists the cross-version assertions and measured resource summaries. [baseline-v430-results.json](baseline-v430-results.json) and the two retained baseline batch stdout files anchor the published comparison with exact hashes.

## Revalidation

Run `python3 -B check.py` from this package. It compares the retained results without starting Lean. A fresh execution requires a clean copy without `results.json`, `raw/` or `work/`, and a new resource admission. The result does not change I062's Anneal/editor prerequisite.
