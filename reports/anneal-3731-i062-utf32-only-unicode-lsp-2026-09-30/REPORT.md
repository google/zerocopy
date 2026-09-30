# Lean LSP Unicode positions under a UTF-32-only client offer

## Summary

One direct Lean 4.30.0-rc2 server session opened a Unicode error file while the client advertised only `utf-32`. The initialize response omitted `positionEncoding`; the diagnostic range for `unknownName` was line 0, characters **16–27**, matching UTF-16 code units rather than UTF-32/scalar columns **15–26** or UTF-8 bytes **19–30**. A version-2 incremental edit sent at the scalar range left an `Unknown constant Nat.zeroe` diagnostic. Fresh batch checks on the exact original and intended patched bytes exited 1 and 0. This adds bounded **I062** evidence, with **I025** coordinate context only. No Anneal product gate, status or prerequisite changes.

## Applicability and novelty

The observed binary is locally installed `leanprover/lean4` v4.30.0-rc2, SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, on macOS arm64. The original source is `#check ("😀é", unknownName)`; the intended patch substitutes `Nat.zero`. `oracle.py` independently calculated scalar 15–26, UTF-16 16–27 and UTF-8 byte 19–30 for that token, and pinned the exact fixture hashes before launch. The oracle SHA-256 `c7bf9661e8ebef39410aa24e898949fc16614770cc2477ce601f2c14a68cc894` is recorded in acquisition results.

The published [UTF-8-only/UTF-16-only Lean report](../anneal-3731-i062-utf8-only-unicode-lsp-2026-09-30/REPORT.md) tested those two offers on the same source; the [Lean 4.29 comparison](../anneal-3731-i062-lean429-version-diff-2026-09-30/REPORT.md) repeated them at one older pin. Neither sent a UTF-32-only offer and scalar-counted incremental range. This report tests that remaining offer/range cell only. No Lake project, Rust compiler, generated Aeneas model, Anneal projection, real editor or MCP adapter participated.

## Method and result

The one-shot runner launched `lean --server` with `LEAN_NUM_THREADS=1` in a private work directory. It retained complete framed client/server bytes, decoded messages, argv/environment, PIDs, timestamps and resource samples. The client initialized with `general.positionEncodings: ["utf-32"]`, opened disk v1 of the file, awaited diagnostics, then sent a version-2 incremental `didChange` replacing range line 0 characters 15–26 with `Nat.zero`. It awaited post-change diagnostics, shut down and exited cleanly. Fresh `lean --json` processes separately checked exact original and intended patched bytes.

The initialize result had no explicit `positionEncoding` field. The first error was `Unknown identifier unknownName` at line 0, characters 16–27, matching the predeclared UTF-16 oracle. After the scalar-range edit, the server reported `Unknown constant Nat.zeroe` at line 0, characters 15–24. The intended patch was clean in fresh batch Lean, while the original gave its expected unknown-identifier error. The protocol did not return the complete post-edit document text, so the exact in-memory buffer after the scalar edit is **not independently observed**; `Nat.zeroe` is only the retained diagnostic message. The server process exited 0 and both batch processes exited 1/0 as expected.

The normative [LSP 3.17 position types](https://github.com/microsoft/language-server-protocol/blob/gh-pages/_specifications/lsp/3.17/types/position.md) define UTF-32 columns as Unicode code points. Its [initialize contract](https://github.com/microsoft/language-server-protocol/blob/gh-pages/_specifications/lsp/3.17/general/initialize.md) says clients must support UTF-16 even when it is absent from `positionEncodings`, and an omitted server `positionEncoding` defaults to UTF-16. A UTF-32-only offer therefore does not establish a negotiated UTF-32 wire encoding or a protocol violation. The observed diagnostic and edit behavior are consistent with the default UTF-16 interpretation for this fixture. A client intending to send scalar positions must establish a selected UTF-32 encoding first.

## Evidence and bounds

`fixture/`, `oracle.py`, `oracle.json`, `probe.py`, `results.json` and `raw/` retain the exact source, coordinate oracle, request/response frames, diagnostics, batch output and resource observations. `check.py` reparses every retained wire frame, checks request/response IDs and versioned diagnostic publications, exact offer and edit range, source hashes, batch messages, resource limits and cleanup. `python3 -B check.py` passes offline; `comparison.json` records its checked projection. The results file SHA-256 is `15bbeb7d5ae7f7c0d7e5f9016363214d3ef02558fd280069134333a850ab05ac`.

Initial admission measured 31.7915% estimated reclaimable memory and 18,597,441,536 free disk bytes. Minimum sampled server reclaimable was 30.8069%; maximum server group RSS was 188,192 KiB and maximum scratch was 8,272 bytes. Both batch runs used at most 97,248 KiB sampled group RSS. All processes ended with zero post-run group RSS, and the private work tree was removed. Guards required above 30% reclaimable and above 10 GiB disk at each launch, and would stop below 20% reclaimable, below 10 GiB disk, above 1.2 GiB group RSS, above 100 MiB scratch or beyond 30 seconds per process. Sampled maxima can miss brief peaks.

One source line, one UTF-32-only offer and one Lean release candidate do not establish behavior of other editors, capability combinations, versions or real Anneal projected documents. The offered list deliberately omits mandatory UTF-16, which the protocol still permits the server to assume. No source-to-proof mapping, format/save interaction, or cross-client coordination was tested. I062 remains partial at its product gate; I025 receives context only.

## Revalidation

Run `python3 -B check.py` from this package. For a new run, copy `fixture/`, `oracle.py`, `probe.py`, `check.py` and `oracle.json` into a fresh private package with no acquired outputs, then run `python3 -B probe.py` after fresh resource admission. The runner refuses to overwrite its prior acquisition.
