# Unicode positions under UTF-8-only and UTF-16-only Lean LSP offers

## Summary

Two **sequential** direct Lean 4.30.0-rc2 server sessions opened the same one-line Unicode error. One client offered only `utf-8`; the other offered only `utf-16`. Both initialize responses omitted an explicit `positionEncoding` choice, and both initial diagnostic ranges used characters **16–27**, matching the independent UTF-16 coordinates of `unknownName` after `😀é`. The UTF-8 byte coordinates are **19–30**, and scalar coordinates are **15–26**. Thus the UTF-8-only *offer* did not establish UTF-8 wire positions in this fixture.

Each client then sent one position-sensitive incremental `didChange` intended to replace `unknownName` with `Nat.zero`, using its offered coordinate units. The UTF-16 range **16–27** cleared the error; the UTF-8 range **19–30** left an `unexpected end of input` error. Fresh batch `lean --json` confirmed the retained original source fails and the intended patched source succeeds. This is a bounded direct Lean protocol observation for #3731 **I062**, with #3730 **B03** and #3731 **I025** context. It is not an Anneal/editor integration result or a protocol-conformance judgment.

## Applicability

The observed Lean binary is the locally installed `leanprover/lean4` **v4.30.0-rc2** executable, SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, on macOS arm64. The [original fixture](fixture/Encoding.lean) is `#check ("😀é", unknownName)` and the [intended patched fixture](fixture/EncodingPatched.lean) substitutes `Nat.zero`. The decomposed combining mark and supplementary emoji give three distinct token starts: scalar 15, UTF-16 16, UTF-8 byte 19. [oracle.json](oracle.json) retains these endpoints and both edit ranges. Its SHA-256 `7f7aac75610935a82f2382381ca0fbab519eaee9abb26767dcd90ab8cabe4cc7` was recorded in [results.json](results.json) before either server launch.

The one-shot [runner](probe.py) used direct `lean --server`, `LEAN_NUM_THREADS=1`, a private directory for each session and one stdio JSON-RPC client. It shut down the UTF-8-only process before starting the UTF-16-only process, then ran separate fresh batch checks. Complete framed client/server bytes and raw batch output are in [raw/](raw/); the decoded messages, exact argv, selected environment, PIDs, timing and resource samples are in [results.json](results.json). No Lake project, generated Aeneas model, Rust compiler, Anneal projection, editor extension, MCP adapter or network service participated.

The earlier [Lean LSP projection/code-actions report](../anneal-3730-lean-lsp-projection-code-actions-2026-09-29/REPORT.md) offered both encodings in opposite orders and found a UTF-16 Unicode diagnostic. The [two-logical-client report](../anneal-3730-multiclient-editor-contract-2026-09-29/REPORT.md) offered UTF-8 alone but used ASCII positions. Neither combined a UTF-8-only offer with a non-ASCII range and incremental edit.

## Findings

| Cell | Initialize choice | Initial error range | Incremental edit range | Post-edit error | Exit |
| --- | --- | --- | --- | --- | ---: |
| UTF-8-only offer | `positionEncoding` absent | line 0, chars 16–27 | line 0, chars 19–30 | `unexpected end of input` | 0 |
| UTF-16-only offer | `positionEncoding` absent | line 0, chars 16–27 | line 0, chars 16–27 | none; `Nat.zero` information message | 0 |
| Fresh batch original | n/a | line 1, scalar cols 15–26 | n/a | `unknownName` | 1 |
| Fresh batch intended patch | n/a | n/a | n/a | none; `Nat.zero` information message | 0 |

The UTF-8-only session's emitted initial range matched UTF-16, not UTF-8, despite the offer. The UTF-8-counted edit did not produce the intended patched source behavior. The retained protocol does not return the complete post-edit document text, so the precise resulting buffer is **not independently observed**; the unexpected-end diagnostic is the observed outcome. A client must inspect the server's actual position-encoding behavior rather than infer acceptance solely from its own offer. **Basis: execution and independently calculated coordinates.**

The runner's initial preflight measured **34.9060%** estimated reclaimable host memory and **18,846,994,432 bytes** free disk. Both server launch preflights exceeded 30% and 10 GiB. Maximum sampled process-group RSS was **196,880 KiB** for UTF-8-only and **115,824 KiB** for UTF-16-only; minimum sampled reclaimable memory was **33.8657%** and **34.3344%**, respectively. Minimum sampled free disk was **18,843,561,984** and **18,843,697,152** bytes, and maximum scratch was **8,814** and **15,934** bytes. Both server exits were 0, their postrun process-group RSS was 0, and the first ended before the second started. Batch original/patched exits were 1/0, with maximum sampled RSS at most **98,016 KiB**. The private work tree was removed. No 20%-memory, 10-GiB-disk, 1.2-GiB-RSS, 100-MiB-scratch or 30-second/session guard fired. Sampling can miss shorter peaks. **Basis: execution.**

## Boundaries

This fixture distinguishes wire coordinates and one incremental edit under two capability offers for one Lean binary. The absence of an explicit `positionEncoding` is part of the observed initialize response; the report does not claim a negotiated UTF-8 choice, a Lean protocol violation, or behavior across clients and versions. The UTF-8-range edit is a negative control for assuming an offer alone selects that encoding. It is not a conforming editor workflow demonstration.

There is no Rust-hosted Anneal projection, real editor, generated Lean obligation, negotiated cross-tool source map, or source-to-proof mapping. I062 remains **partial** at its existing **product** gate; B03 and I025 retain their existing residuals, statuses, gates and prerequisites. This experiment does not decide feature fallback, completion, navigation or multi-client ownership.

## Evidence

[check.py](check.py) independently reparses the retained wire frames, verifies all request/response IDs, offers, versioned diagnostic publications, change ranges, original/patched batch messages, hashes, resource limits and sequential cleanup. [comparison.json](comparison.json) lists the exact observed classifications. The checker does not restart Lean.

## Revalidation

Run `python3 -B check.py` from this package. A new execution requires a clean copy without `results.json`, `raw/` or `work/` and a fresh resource admission. A future Anneal/editor test must negotiate actual client/server capabilities and map the selected wire units through real Rust-hosted projections and unsaved revisions before changing I062's product gate.
