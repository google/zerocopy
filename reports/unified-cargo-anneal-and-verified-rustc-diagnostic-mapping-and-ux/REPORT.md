# Unified `cargo anneal` and Verified `rustc` (`-Zcodegen-backend=anneal`) Span Provenance, Diagnostic Mapping, and Developer UX

## Summary

The prior incremental proof cache
(`incremental-function-and-thinlto-summary-proof-cache-architecture`) strips all
source `Span` byte offsets from `MirItemKey(f)` so that comment and whitespace
edits achieve a `100.0%` cache hit rate (`0` re-verified steps). However,
stripping `Span`s from the canonical MIR digest raises a fundamental developer-UX
question: when a verification obligation, `HybridTrace` step, `asm!` contract
check, `const_eval_select` equivalence check, proc-macro determinism check, or
Soundness Quarantine fallback triggers inside `-Zcodegen-backend=anneal` or
`cargo anneal`, how does the toolchain report an exact, `rust-analyzer`-compatible
`rustc` span (`file:line:col` + multi-frame `ThinLTO` inlining backtrace) and
OASIS SARIF 2.1.0 security report without re-introducing line-number sensitivity
into `MirItemKey`?

Mechanizing the **Out-of-Key `StmtOrd` Sideband Span-Provenance Architecture**
in Lean `v4.34.1` ([`support/SpanProvenance.lean`](support/SpanProvenance.lean))
and implementing a live `rustc 1.99.1` sideband extraction and multi-format
diagnostic engine
([`support/anneal_diag_engine.py`](support/anneal_diag_engine.py),
[`support/run_k8_ux_tests.py`](support/run_k8_ux_tests.py),
[`support/sample_diagnostics.json`](support/sample_diagnostics.json),
[`support/sample_audit.sarif.json`](support/sample_audit.sarif.json),
[`support/k8_metrics.json`](support/k8_metrics.json)) establishes three core
results:

1. **Decoupling Function-Local `StmtOrd` Indices from Out-of-Key
   `SidebandSpanTable` Preserves `100.0%` `MirItemKey` Cache Hits Across Line
   Shifts while Delivering `100.0%` Exact Post-Shift Spans:**
   - Every `CoreMIR` statement and `MiniSSA`/`MiniMach` instruction carries a
     dense, function-local ordinal index (`StmtOrd : Nat`) instead of a byte
     span, while `.anneal-mir` stores an out-of-key `SidebandSpanTable`
     (`StmtOrd → SpanData { fileId, loLine, loCol, hiLine, hiCol, inlinedFrom :
     Option StmtOrd }`).
   - Theorems `mirItemKey_invariant_under_line_shift` (`[]` axioms),
     `shifted_diagnostic_span_exact` (`[propext]`), and
     `backtrace_length_preserved_under_line_shift` (`[]` axioms) in
     [`support/SpanProvenance.lean:69-154`](support/SpanProvenance.lean#L69-L154)
     prove that shifting source lines by `deltaLines` leaves `computeMirItemKey`
     identical while shifting every emitted diagnostic's `loLine` and `hiLine`
     by `+deltaLines` and preserving `ThinLTO` inlining backtrace depth.
   - Tested on live `rustc +1.99.1 -Copt-level=3 -Zmir-include-spans --emit=mir`
     output ([`support/run_k8_ux_tests.py`](support/run_k8_ux_tests.py)),
     inserting `50` lines of leading comments yields the exact same `MirItemKey`
     digest (`d670059b00aa937a...`), shifts all `44 / 44` (`100.0%`) local
     statement ordinals by exactly `+50` lines (e.g., `StmtOrd #3` at
     `src/checksum.rs:5:15 -> src/checksum.rs:55:15`), and preserves all `2 / 2`
     (`100.0%`) cross-crate inlined `core` statement spans untouched.
2. **Unified Six-Code Diagnostic Taxonomy (`W_ANNEAL_0101`–`E_ANNEAL_0301`)
   Across Drop-In Compilation (`Mode 1`) and Proof Auditing (`Mode 2`):**
   - A single diagnostic schema bridges `-Zcodegen-backend=anneal` and
     `cargo anneal` across `--error-format=human`, `--error-format=json`
     (`$message_type: "diagnostic"` for `cargo` and `rust-analyzer`), and OASIS
     **SARIF 2.1.0** ([`support/sample_diagnostics.json`](support/sample_diagnostics.json),
     [`support/sample_audit.sarif.json`](support/sample_audit.sarif.json)):
     - `W_ANNEAL_0101`: Soundness Quarantine fallback notice (`RuleFamily_k`
       quarantined; function verified at `0` `sorryAx` via `StmtDeriv.refl`);
     - `E_ANNEAL_0102`: Unannotated `TerminatorKind::InlineAsm` block under
       `-Zanneal-strict-asm`;
     - `E_ANNEAL_0103`: `const_eval_select` call site lacking an
       `ObsEquivOnValid` proof for `MirConstFoldCert`;
     - `E_ANNEAL_0104`: `anneal-audit-daemon` certificate mismatch trap with
       automatic `.anneal-repro` minidump generation;
     - `I_ANNEAL_0201`: ELF/Mach-O/PE `.note.anneal.manifest` binary attestation
       verification receipt;
     - `E_ANNEAL_0301`: Procedural-macro non-determinism caught by dual-seed
       `TokenStream` expansion (`K5_`).
3. **Sub-2ms Self-Contained `.anneal-repro` Minidump Generation on `E_ANNEAL_0104`:**
   - When `E_ANNEAL_0104` fires, `anneal_diag_engine.py` packages the minimal
     reproducer (`manifest.json`, `core_mir_slice.json`,
     `failed_hybrid_step.json`, and standalone `ReplayRepro.lean`) into a
     compressed `513`-byte archive in **`1.078 ms`** (well inside the `< 5.0 ms`
     budget).

## Applicability

This report applies to `rustc 1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`), `Lean 4 v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`), and Anneal
(`joshlf/anneal@d4ca2c861f664f200b69cdced9f6af38b5b1175a`) when emitting
diagnostics, IDE annotations, and CI security attestations from `cargo anneal`
and `-Zcodegen-backend=anneal`.

It extends three corpus reports:
- `rustc-build-system-and-consumer-invocation-contracts`
- `verified-rustc-delivered-toolchain-trusted-component-inventory`
- `compiler-upgrade-soundness-quarantine-and-proof-invalidation-bounds`

Created: 2026-11-14 · Updated: 2026-11-14

## Findings

### 1. Lean `v4.34.1` Mechanization of Sideband `StmtOrd` Span Provenance

Basis: source + execution

In [`support/SpanProvenance.lean`](support/SpanProvenance.lean),
`PackagedMirFunction` separates `stmts : List (StmtOrd × CanonicalMirOp)` from
`sidebandSpans : StmtOrd → SpanData`. All three theorems verify in Lean
`v4.34.1` with zero `sorryAx` and zero `Lean.ofReduceBool`:

| Theorem Name | Lines | Axiom Footprint | Verified Contract |
| :--- | :---: | :---: | :--- |
| `mirItemKey_invariant_under_line_shift` | `69-72` | `[]` (none) | `computeMirItemKey (applyCommentLineShift pkg deltaLines) = computeMirItemKey pkg` for any line offset `deltaLines`. |
| `shifted_diagnostic_span_exact` | `124-136` | `[propext]` | Resolving any cached `VerificationEvent` after `applyCommentLineShift pkg deltaLines` yields `loLine + deltaLines` and `hiLine + deltaLines` while preserving `code`, `fileId`, `loCol`, and `hiCol`. |
| `backtrace_length_preserved_under_line_shift` | `140-154` | `[]` (none) | Inductive proof over `fuel : Nat` that shifting `sidebandSpans` preserves the exact frame count of `resolveInliningBacktrace` across `ThinLTO` inlined calls. |

### 2. Unified Diagnostic Taxonomy and Live `rustc 1.99.1` Span-Shift Validation

Basis: source + execution

Table 1 summarizes the six canonical diagnostic codes validated in
[`support/anneal_diag_engine.py`](support/anneal_diag_engine.py) and
[`support/run_k8_ux_tests.py`](support/run_k8_ux_tests.py)
([`support/sample_diagnostics.json`](support/sample_diagnostics.json),
[`support/sample_audit.sarif.json`](support/sample_audit.sarif.json),
[`support/k8_metrics.json`](support/k8_metrics.json)):

| Diagnostic Code | Severity (`rustc` / SARIF) | Operating Mode | Trigger Condition | Primary Span & Inlining Backtrace Resolution (`+50` Line Shift Test) | Actionable `help:` Remediation |
| :--- | :---: | :--- | :--- | :--- | :--- |
| `W_ANNEAL_0101` | `warning` / `warning` | Mode 1 (`-Zcodegen-backend=anneal`) | Rule family `R_k` active in `X10` Soundness Quarantine | `src/HotLoop.rs:42:13 -> 92:13` + `note:` inlined from `src/lib.rs:88:9 -> 138:9` (`StmtOrd #14 -> #3`) | Pass `-Zanneal-unquarantine=RuleFamily_34` or `-Zanneal-deny-quarantine` |
| `E_ANNEAL_0102` | `error` / `error` | Mode 1 & Mode 2 (`-Zanneal-strict-asm`) | Inline `asm!` block without `#[anneal::asm_spec(...)]` | `src/arch_x86.rs:19:9 -> 69:9` (`StmtOrd #7`) | Add `#[anneal::asm_spec(clobbers = "...", memory = "...")]` |
| `E_ANNEAL_0103` | `error` / `error` | Mode 1 & Mode 2 (`MirConstFoldCert`) | Custom `const_eval_select` without `ObsEquivOnValid` proof | `src/ctfe_custom.rs:54:5 -> 104:5` (`StmtOrd #11`) | Attach `#[anneal::const_select_proof(theorem = "...")]` |
| `E_ANNEAL_0104` | `error` / `error` | Mode 1 (`anneal-audit-daemon`) | Kernel / `nanoda_lib` rejected `HybridTrace` step `#14` | `src/crypto.rs:103:14 -> 153:14` (`StmtOrd #14`) | Emits `513`-byte `.anneal-repro` bundle in `1.078 ms` (`cargo anneal minimize-repro`) |
| `I_ANNEAL_0201` | `note` / `note` | Mode 2 (`cargo anneal audit-binary`) | `.note.anneal.manifest` ELF/Mach-O/PE section verified | `src/main.rs:1:1 -> 51:1` (`13,683 / 13,683` fns, `0` `sorryAx`) | Run `cargo anneal audit-binary --format=sarif` for CI upload |
| `E_ANNEAL_0301` | `error` / `error` | Mode 1 (`-Zanneal-verify-procmacro-determinism`) | Dual-seed proc-macro `TokenStream` digest mismatch (`K5_`) | `src/schema.rs:12:10 -> 62:10` (`#[derive(HashMapOrderDerive)]`) | Enable `LD_PRELOAD=libanneal_procmacro_det.so` or replace `HashMap` with `BTreeMap` |

## Boundaries

1. **Column Shifts Within the Same Line (`known not to apply` for line-only shift deltas):**
   - `applyCommentLineShift` models inserting or deleting lines *above* a
     function (`loLine + deltaLines`). If a user edits whitespace *inside* an
     expression on the same line, `rustc` updates `lo_col`/`hi_col` in the
     local crate's `SidebandSpanTable` in $O(\text{stmts})$ during MIR capture
     without re-running `MiniSSA` optimization or `anneal-audit-daemon` because
     `computeMirItemKey` remains unchanged.
2. **Stripped Release Binaries Without `.note.anneal.manifest`:**
   - If an external post-link tool runs `strip --remove-section=.note.anneal.manifest`,
     `cargo anneal audit-binary` cannot extract the embedded Merkle root and
     requires the detached `.anneal-manifest.json` build artifact instead.

## Evidence

1. **Lean `v4.34.1` Mechanization (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`):**
   - [`support/SpanProvenance.lean`](support/SpanProvenance.lean):
     `PackagedMirFunction`, `computeMirItemKey`,
     `mirItemKey_invariant_under_line_shift`, `shifted_diagnostic_span_exact`,
     and `backtrace_length_preserved_under_line_shift` (zero `sorryAx`, zero
     `Lean.ofReduceBool`).
2. **Sideband `StmtOrd` Engine, `rustc` JSON / SARIF 2.1.0 Emitters, and Live `rustc 1.99.1` Test Suite:**
   - [`support/anneal_diag_engine.py`](support/anneal_diag_engine.py)
   - [`support/run_k8_ux_tests.py`](support/run_k8_ux_tests.py)
   - [`support/sample_diagnostics.json`](support/sample_diagnostics.json)
   - [`support/sample_audit.sarif.json`](support/sample_audit.sarif.json)
   - [`support/k8_metrics.json`](support/k8_metrics.json)

## Revalidation

```bash
anneal-lean-run --mode file --concurrency 4 -- lean \
  reports/unified-cargo-anneal-and-verified-rustc-diagnostic-mapping-and-ux/support/SpanProvenance.lean
python3 reports/unified-cargo-anneal-and-verified-rustc-diagnostic-mapping-and-ux/support/run_k8_ux_tests.py \
  --sample-diags-out /tmp/sample_diagnostics.json \
  --sample-sarif-out /tmp/sample_audit.sarif.json \
  --metrics-out /tmp/k8_metrics.json
```
