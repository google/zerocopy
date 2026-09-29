# Compiler-backed Rust and Lean coordinates over exact copied doc-comment bytes

## Summary

A tiny Rust file with CRLF, an emoji, a combining mark, and a tab produced a real rustc JSON error whose byte span and scalar column disagree numerically. A byte-for-byte copied Rust doc-comment payload produced a real Lean batch error and Lean LSP diagnostic on the same `missingLean` token. The bridge mapped both Lean ranges back to the exact Rust source bytes, round-tripped 28 valid scalar boundaries in the copied payload, and rejected seven invalid or unowned cases. The bridge is an explicit test harness, not Anneal V2's source map. This narrows [#3731 I025](https://github.com/google/zerocopy/issues/3731); its actual Rust-hosted projection and editor encoding negotiation remain open.

## Applicability

The active `anneal/src/main.rs` at `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988` declares scanner, resolver, setup, and utility modules. The current V2 `anneal/src/` has no projection/source-map module or callable position-conversion API; `anneal/DESIGN.md` leaves annotation syntax and proof encoding undecided. This is a scoped source inspection, not a claim about historical V1 or future Anneal. The experiment therefore uses a transparent bridge: strip only the four exact bytes `/// ` from one real Rust doc-comment line, prepend `import Lean\r\n`, and copy the 31 payload bytes unchanged into a Lean file. Both files preserve CRLF. The Rust compiler ignores the Lean payload as documentation; no claim connects the Rust and Lean errors semantically.

The executed local binaries were nightly-2026-05-31 rustc on macOS arm64 and Lean 4.30.0-rc2, identified by full source revisions and executable SHA-256 values in `REPORT.json`. Rustc ran `--error-format=json --emit=metadata`; Lean ran `--json` and one direct `--server` session with `LEAN_NUM_THREADS=1`. There was no Lake project, Charon, Aeneas, dependency install, or Anneal invocation. This is intentionally distinct from the larger [source-owned diagnostic matrix](../anneal-3730-source-owned-projection-diagnostic-matrix-2026-09-29/REPORT.md): it isolates the CRLF, tab, exact byte bridge, and inverse-domain checks, while that package covers broader stage provenance and patch ownership. The earlier [coordinate report](../cross-tool-utf8-span-columns-2026-09-27/REPORT.md) established pinned source-level unit rules; the [projection property suite](../anneal-3730-projection-properties-2026-09-29/REPORT.md) exercised many illustrative strings without these paired compiler outputs.

## Findings

### Real coordinate specimens

| Evidence | Native coordinate | Same byte boundary under the bridge |
| --- | --- | --- |
| rustc primary `missingRust` span | `Host.rs` bytes 112–123; one-based line 3, one-based scalar columns 34–45 | Start is zero-based scalar column 33 and UTF-16 column 34 on the Rust line. Emoji, combining mark, and tab precede it. |
| Lean batch `Unknown identifier missingLean` | `Projected.lean` one-based line 2, zero-based scalar columns 15–26 | Projected UTF-8 bytes 32–43; copied Rust source bytes 61–72. |
| Lean LSP `Unknown identifier missingLean` | Zero-based line 1, UTF-16 characters 16–27 | Converts to the same projected bytes 32–43 and Rust bytes 61–72. |

Rustc and Lean batch exited 1 for their deliberately invalid inputs. The Lean server's settled diagnostic included the `missingLean` range above and exited 0 after clean shutdown. The one-column difference between Lean batch scalar column 15 and LSP UTF-16 character 16 is caused by the supplementary emoji before the token. Rustc's one-based scalar column 34 happens to equal the Rust line's zero-based UTF-16 column 34 here; that equality is a coincidence of the one-column base difference and one supplementary scalar. The tab contributes one scalar and one UTF-16 unit; this report does not infer terminal display width from rustc JSON. **Basis: execution**, retained rustc JSON, Lean batch JSON, LSP notifications, exact source bytes, and `support/check.py`.

### Exact copied interval and inverse domain

The harness records an authored byte interval starting at `Host.rs` byte 42 and a projected interval starting at `Projected.lean` byte 13, both 31 bytes long. Within those copied intervals, its only mapping is `projected = host - 42 + 13`; synthetic `import Lean` and stripped `/// ` have no reverse edit origin. It enumerated 28 UTF-8 scalar boundaries in the payload. Every boundary round-tripped through source and projected bytes and through zero-based scalar and UTF-16 line columns. The count excludes four byte offsets inside multibyte encodings. **Basis: execution** for the enumeration and round trips; **derived** for the restricted mapping rule from the exact-copy construction.

Seven negative controls rejected a host or projected interior UTF-8 byte, a host or projected UTF-16 surrogate interior, an interior CRLF byte, the synthetic Lean header, and a Rust location outside the copied payload. The tab is retained in the Rust code line and affects rustc's observed span; Lean's copied payload itself contains the emoji and combining mark but no tab. **Basis: execution** for the seven controls and compiler results.

## Boundaries

- **Not examined:** a production Anneal parser, its source map, generated proof obligations, cross-file mapping, edits, client encoding negotiation, or source identity through unsaved changes. I025 remains **partial** and would require an implemented Rust-hosted Anneal projection and real client round trips to close.
- **Not examined:** Charon's lossy display-width columns, Aeneas locations, Unicode normalization by editors, invalid UTF-8 source, grapheme/display-cell coordinates, or a byte-order mark. The bridge intentionally starts with valid, exact UTF-8 bytes.
- **Known not to apply:** the copied-interval inverse does not apply to the synthetic Lean header, stripped Rust doc-comment prefix, CRLF interior, or unrelated Rust code. The seven rejection controls test examples of those boundaries.
- The Rust `missingRust` error and Lean `missingLean` error are separate injected failures. Their successful coordinate conversion is not a Rust-to-Lean proof correspondence or diagnostic ownership claim for Anneal.

## Evidence

- `support/Host.rs` SHA-256 `64dbfcf5bcbd82a399770d6a2d6f303989fde875cd08130b80e9388d1f9134dd` and `support/Projected.lean` SHA-256 `e489c64eb703e56718f2239f26896398177344f0d07b499b21abc7d1f218dec5` preserve the exact CRLF source bytes.
- `support/probe.py` SHA-256 `d0c9ff54eb1bc6707ecdd4e235c842bcaed59e83dd7f1c5ed54f39cde1684e9c` runs rustc, Lean batch, and direct Lean LSP, then writes raw evidence. `support/transcript.json` SHA-256 `977df1e88f8308ce3abfdd2c16a2b70e428ca21d802b0a56827ea8f4b1345653` retains complete compiler stdout/stderr, server messages, diagnostic notifications, versions, and exit status with local paths tokenized.
- `support/results.json` SHA-256 `bd5a66e7bc667850d2e51cef40931a84fbbf8505e8c356438cbfc534b5e36922` indexes compiler and LSP records, all 28 boundary conversions, and seven rejected cases. `support/check.py` SHA-256 `63130713e39b0ac1004afbe838e0bf5eb47513fbbbd0206504f87ca31d79ad8c` independently checks the retained bytes, native ranges, mapped token, inverse domain, transcript, and clean shutdown.
- Source inspection: `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988`, `anneal/src/main.rs` module declarations and the five files under `anneal/src/`; `anneal/DESIGN.md` opening scope and deliberate non-decisions. The inspected snapshot has no V2 projection API to substitute for the bridge.

## Revalidation

Run `python3 support/check.py` to check the preserved evidence without installed compilers. For a fresh tool run, set `RUSTC_BIN` and `LEAN_BIN` to the pinned binaries and run `python3 support/probe.py`, then the checker. Compare binary hashes and exact source hashes before interpreting a replay as the same subject. For an Anneal implementation, replace only the bridge with its actual source map and feed the same retained host bytes through the production batch/live path and negotiated editor encodings; require the corresponding real source intervals and explicit rejections before closing I025.
