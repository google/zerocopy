# Human-Readable TTY Output vs. Machine-Readable Output for Formal Verification CLIs

## Summary

Command-line formal verification and security tools must serve two incompatible consumers simultaneously: human engineers reading interactive terminals or CI logs, and automated harnesses parsing machine-readable receipts (`jq`, CI artifact gates, IDE/MCP wrappers). Primary-source inspection and execution probes across 21 specifications, systems CLIs, and formal-verification tools establish six governing invariants:

1. **Stream separation and dual-destination export:** Primary structured results (`JSON`, `SARIF`) belong strictly on `stdout`, while progress indicators, phase timings, and operational logs belong on `stderr` (`clig.dev`, `cargo`, `cargo-audit`, `cargo-vet`, `zizmor`, `verus`). Routing machine JSON to `stderr` breaks standard pipelines (`cargo-deny` had to add `--audit-compatible-output` specifically to move JSON back to `stdout`). To prevent CI jobs from having to choose between readable human logs and machine-verifiable receipts, mature tools (`cargo-vet --output-file`, `kani --export-json`, `dafny --verification-logger`, `hyperfine --export-json`) provide an explicit file-export flag alongside console output.
2. **Format selection vs. `isatty(stdout)` auto-switching:** None of the examined verification or security CLIs (`kani`, `verus`, `dafny`, `creusot`, `cargo-audit`, `cargo-deny`, `cargo-vet`, `zizmor`) auto-switch *data syntax* between human prose and JSON based on `stdout.is_terminal()`. When piped, they emit plain uncolored human text (never JSON) unless `--format json` / `--output-json` is passed explicitly, preserving `cmd | less`, `cmd | tee build.log`, and non-TTY CI logs. Conversely, migrating a historically JSON-on-`stdout` CLI (such as `cargo-anneal` at `google/zerocopy@d3362d9a65`) requires either an explicit `--format human|json` contract break with caller updates, or a transitional TTY-gated mode paired with `--receipt-out <path>`.
3. **Independent per-stream capability and color precedence:** `stdout` and `stderr` terminal status must be queried independently (`cargo`, `gh`, `nix`, `zizmor` via `anstream::AutoStream`); checking `stdout.is_terminal()` to gate `stderr` ANSI escapes is a recurring implementation bug found in both `creusot` (`cargo-creusot/src/main.rs:379`) and `kani` (`kani-driver/src/session.rs:423`) that strips `stderr` colors during `cmd > receipt.json`. The cross-tool precedence order is: explicit `--color=always|never|auto` > non-empty `NO_COLOR` (`no-color.org`, overriding `CLICOLOR_FORCE`) > `TERM=dumb` (disabling both color and cursor motion) > non-zero `CLICOLOR_FORCE` / `FORCE_COLOR` > `CLICOLOR=0` > per-stream `is_terminal()`.
4. **End-of-output 3-tier assurance hierarchy (tainted vs. scoped vs. whole-crate):** Printing taint warnings only at startup (`cargo-anneal` `verify.rs:2152-2155`) lets warnings scroll off-screen above a clean-looking final output. Best-in-class verifiers (`kani`, `verus`, `dafny`, `cargo-vet`, `zizmor`) encode caveats directly into the **closing** verdict and distinguish three assurance tiers: (a) **Hard taint / unproven assumptions** (`sorry`, `--allow-*`, `UNDETERMINED`, exemptions — never rendered as bare green `VERIFIED`), (b) **Scoped / partial verification** (`--select` / `--verify-module` `K of M` items or degraded containment), and (c) **Untainted whole-crate verification**.
5. **Untrusted-input terminal sanitization vs. lossless JSON:** Verifiers ingest untrusted proof, specification, and source identifiers. `rustc` (`emitter.rs:470-535`) replaces ASCII C0/DEL controls (`0x01..=0x1F`, `0x7F`) with Unicode Control Pictures (`U+2401..U+2421`) and replaces all 9 Trojan-Source bidirectional controls (`U+202A..=U+202E`, `U+2066..=U+2069`) with `U+FFFD`, **but leaves 8-bit C1 controls (`U+0080..=U+009F`, including CSI `U+009B`) raw**. Combining `rustc`'s C0/DEL/Bidi table with `cli/go-gh`'s C1 neutralization (`asciisanitizer/sanitizer.go:106-174`) closes terminal escape/spoofing vectors on human streams while keeping RFC 8259 JSON fields byte-exact.
6. **`BrokenPipe` safety without exit-code masking and deterministic snapshots:** Because Rust ignores `SIGPIPE` by default, `println!` panics (`exit 101`) on `| head`. Writing via `writeln!` and catching `io::ErrorKind::BrokenPipe` (`ripgrep`, `ruff`, `cargo`) avoids panics while preserving any already-computed non-zero verification exit code (`1` or `2`). Deterministic snapshot tests (`cargo`, `cargo-deny`) decouple wall-clock `timing_ms` from default human text, clamp non-TTY width to `80` columns, and force `ColorChoice::Never`.

## Applicability

- **Examined subjects and relationship:** This report synthesizes CLI stream routing, format selection, terminal capability detection, progress rendering, assurance-caveat hierarchy, terminal sanitization, `BrokenPipe` handling, and exit-code contracts across the 21 specifications and toolchains pinned in `REPORT.json`, using `cargo-anneal` (`google/zerocopy@d3362d9a657e2f943d25a0812f7b13b93e60af4d`) as the target consumer baseline.
- **Direct execution vs. source/specification inspection:**
  - *Normative/community specifications:* `no-color.org` (`jcs/no_color@278b6afc`) and `clig.dev` (`cli-guidelines/cli-guidelines@697d6a29`).
  - *Source + live execution on Linux `x86_64`:* `ripgrep 15.1.0` (`BurntSushi/ripgrep@4a51093f`), `zizmor 1.23.1` (`zizmorcore/zizmor@0af0be98`), plus `--help` CLI contract verification on `cargo 1.102.0-nightly`, `gh 2.103.3`, `nix 2.33.3`, `lake 5.0.0`, `cargo-deny 0.14.3`, `cargo-vet 0.8.0`, and `cargo-kani 0.67.0`, alongside the standalone Python 3.13 PTY/pipe/sanitization probe in [`support/probe_tty_pipe_and_sanitization.py`](support/probe_tty_pipe_and_sanitization.py). Note where executed release binaries (`zizmor 1.23.1`) differ from newer source `HEAD` (`zizmor@0af0be98`).
  - *Pinned source inspection:* `rust-lang/cargo@930a674d`, `rust-lang/rust@5debe6a1`, `astral-sh/uv@264d8b4a`, `astral-sh/ruff@3c06ae6c`, `cli/cli@de06af2c`, `cli/go-gh@4e83b33c`, `NixOS/nix@7dc6d7f2`, `sharkdp/hyperfine@c5161524`, `model-checking/kani@87c87010`, `verus-lang/verus@1ce6a59b`, `dafny-lang/dafny@427892ac`, `creusot-rs/creusot@faeb61f5`, `rustsec/rustsec@bafea68f`, `EmbarkStudios/cargo-deny@6d512893`, `mozilla/cargo-vet@a9bde859`, `leanprover/lean4@231ef9a2`, and `google/zerocopy@d3362d9a`.
- **Relationship to other corpus reports:** Extends `unified-cargo-anneal-and-verified-rustc-diagnostic-mapping-and-ux` (which covers `StmtOrd` sideband spans and diagnostic schemas) and `type-error-localization-compiler-diagnostics-and-verification-ux` (constraint localization and counterexamples), and complements `receipt-attestation-audit-cli-inspection-and-anti-spoofing` (which covers offline receipt `inspect`/`diff` subcommands and `serde_json` duplicate-key parsing). This report covers **live verification command execution UX, stream separation, TTY/pipe format negotiation, progress indicators, and human-vs-JSON output contracts**.

## Findings

### 1. Stream Routing (`stdout` vs. `stderr`), `--format` Selection, and Dual Output

Basis: documentation (`cli-guidelines@697d6a29`) + source (`cargo@930a674d`, `uv@264d8b4a`, `cargo-audit@bafea68f`, `cargo-deny@6d512893`, `cargo-vet@a9bde859`, `zizmor@0af0be98`, `verus@1ce6a59b`, `kani@87c87010`, `dafny@427892ac`, `hyperfine@c5161524`, `zerocopy@d3362d9a`) + execution (`ripgrep 15.1.0`, `zizmor 1.23.1`)

#### 1.1 Stream Allocation Across Modern Systems and Verification CLIs

| Tool & Pinned Source | Format Flag & Default | `stdout` Payload | `stderr` Payload | Secondary File-Export Flag |
| :--- | :--- | :--- | :--- | :--- |
| `cargo` (`rust-lang/cargo@930a674d`, `shell.rs:140-155, 436-470`) | `--message-format human\|short\|json\|...` (default: `human`) | Empty in `human`/`short`; NDJSON compiler/artifact events in `json` | Right-aligned status (`12` cols), progress bar, `rustc` human reports | `--timings` (HTML/JSON build report) |
| `uv` (`astral-sh/uv@264d8b4a`, `output_format.rs:1-93`, `uv-cli/src/lib.rs:181-211`) | Per-subcommand `--output-format text\|json[\|sarif]` (default: `text`) | Primary query/audit/tree output (`text`, `json`, or `sarif`) | Download/resolution spinners, warnings, interactive prompts (`Term::stderr()`) | `-o` / `--output-file <PATH>` on compile/export subcommands |
| `ripgrep` (`BurntSushi/ripgrep@4a51093f`, `hiargs.rs:155-330`) | Default text (`--heading` on TTY, `file:line` on pipe) vs. `--json` | Matched lines or NDJSON match stream | Error messages (`eprintln_locked!`) | None |
| `cargo-audit` (`rustsec/rustsec@bafea68f`, `config.rs:124-128, 296-298`, `presenter.rs:134-156`) | `--json` or `--format terminal\|json\|sarif` (default: `terminal`) | Vulnerability report (`terminal` text, `json`, or `sarif`) | `"Fetching"`, `"Loaded"`, `"Scanning"` status lines (suppressed when `json`/`sarif`/`-q`) | None |
| `cargo-deny` (`EmbarkStudios/cargo-deny@6d512893`, `main.rs:42-53, 295-330`, `check.rs:111`, `stats.rs:35-72`) | `-f` / `--format human\|json\|sarif` (default: `human`) | Summary table in `human`; SARIF in `sarif`; **empty** in default `json` unless `--audit-compatible-output` | `codespan-reporting` human diagnostics, **and** NDJSON diagnostics/summary in default `json` | `-g` / `--graph <DIR>` |
| `cargo-vet` (`mozilla/cargo-vet@a9bde859`, `main.rs:256-340, 2114-2254`) | `--output-format human\|json` (default: `human`) | Human vetting report or `serde_json::to_writer_pretty` report (including JSON errors in `json` mode) | `indicatif` `ProgressDrawTarget::stderr()`, `tracing` logs, `miette` human errors | `--output-file <PATH>` (`Arc<dyn Out>`) + `--log-file <PATH>` |
| `zizmor` (`zizmorcore/zizmor@0af0be98`, `main.rs:213-247, 395-413`) | `--format plain\|json\|json-v1\|sarif\|github` (default: `plain`) | `annotate-snippets` report (`plain`), JSON array (`json`), SARIF (`sarif`), GHA commands (`github`) | `tracing_indicatif` progress bar + `tracing` logs | None |
| `kani` (`model-checking/kani@87c87010`, `args/mod.rs:260, 347-357, 535-555`) | `--output-format regular\|terse\|old` (default: `regular`, or `terse` for `autoharness`/`--jobs`) | Per-check results, counterexample locations, `VERIFICATION:- SUCCESSFUL\|FAILED` | `tracing` logs (`KANI_LOG` / `--debug`), `cargo` build output | `-Z export-json --export-json <FILE>`, `--sarif <FILE>`, `--log-file <FILE>` |
| `verus` (`verus-lang/verus@1ce6a59b`, `main.rs:531-568`, `verifier.rs:3334-3349`) | `--output-json` boolean flag (default: human) | `"verification results:: X verified, Y errors"` (human) or pretty JSON object (`--output-json`) | `rustc` / VIR diagnostics (`ErrorOutputType`), debug-build warnings | `--log-dir` / `-V log-all` (AIR/SMT logs) |
| `dafny` (`dafny-lang/dafny@427892ac`, `CliCompilation.cs:108-112`, `VerifyCommand.cs:142-183`, `VerificationResultLogger.cs:36-72`) | `--diagnostics-format text\|json` (default: `text`) | Diagnostics + trailer (`"Dafny finished with X verified, Y errors..."`) | Tool/CLI errors (`ErrWriter`) | `--verification-logger:{json,csv,trx,text}` (`LogFileName=...`) |
| `cargo-anneal` baseline (`google/zerocopy@d3362d9a`, `verify.rs:2129-2255`) | None (unconditional JSON) | Pretty JSON receipt (`ExitCode::SUCCESS`) or single-line `FailureReceipt` JSON (`exit 1` or `2`) | Startup `WARNING: ... TAINTED` banners + raw `capture.stderr` on compiler failure; `clap` usage errors (`exit 2`) | `--artifacts <DIR>` (retained staging directory) |

#### 1.2 Cautionary Precedent: Never Route Primary JSON to `stderr`

In `EmbarkStudios/cargo-deny@6d512893` (`src/cargo-deny/common.rs:528-545` and `src/cargo-deny/stats.rs:54-67`), `StdioStream::Out` is commented out so `--format json` writes NDJSON diagnostics and summaries to `stderr` instead of `stdout`. Downstream CI wrappers expecting `cmd --format json | jq` could not consume `stdout`, forcing `cargo-deny` to add `--audit-compatible-output` (`src/cargo-deny/check.rs:111`: *"output the exact same output as cargo-audit would, to `stdout` instead of `stderr`"*). Primary machine output must always be emitted on `stdout` (or an explicit file path).

#### 1.3 Format Auto-Detection vs. Explicit `--format` Migration Trade-Offs

A recurring design question when adding human TTY output to a historically JSON-only CLI (`cargo-anneal` at `d3362d9a65`) is whether default output syntax should switch automatically on `std::io::stdout().is_terminal()`:

- **Empirical invariant across benchmarks:** Live PTY vs. pipe execution (`support/probe_tty_pipe_and_sanitization.py`) and source inspection confirm that **zero** examined verification or security CLIs auto-switch syntax between human prose and JSON when `stdout` is piped. `ripgrep` adapts *line layout* (`path\n1:match` on TTY vs. `path:match` on pipe, `hiargs.rs:232, 299`), and all tools strip ANSI escapes and spinners when piped, **but human text remains human text on pipes** (`zizmor --format=plain` piped emits `"No findings to report. Good job! (1 suppressed)\n"`). Auto-switching `!stdout.is_terminal()` to JSON surprises humans running `cargo anneal verify | less`, `cargo anneal verify | tee verify.log`, and non-TTY CI steps where engineers read step logs directly.
- **Migration tension for existing JSON callers:** Flipping the unconditional default of `verify` from JSON to `human` breaks existing non-TTY scripts that run `cargo anneal verify ... > receipt.json` or `json.loads(proc.stdout)` without `--format json`. Two clean migration strategies exist:
  1. **Clean pre-1.0 flag contract (`--format human|json`, default `human`) + `--receipt-out <path>`:** Matches `uv`, `cargo-vet`, `cargo-deny`, `zizmor`, `verus`, and `dafny`. All automated callers pass `--format json` (or `--receipt-out receipt.json` when CI wants both human console logs and a saved JSON receipt).
  2. **Explicit 3-valued `--format auto|human|json`:** If `auto` is retained temporarily for backwards compatibility, its contract must be documented explicitly (`human` iff `stdout.is_terminal()`, `json` otherwise), while still providing `--format human` for CI log steps and `--receipt-out <path>` for dual emission.

#### 1.4 The `(format × verbosity)` Stream Matrix

Across `cargo-audit` (`config.rs:296-298`), `cargo-vet` (`main.rs:326-340`), `zizmor` (`main.rs:220-245, 395-413`), and `uv`:

- **`--format json` + default or `--quiet`:** `stdout` **always** receives the complete, schema-valid JSON document (both on `0` success and non-zero structured `FailureReceipt` exits). `--format json` implicitly suppresses informational/progress chatter on `stderr` (`cargo-audit`: `self.quiet || self.format == OutputFormat::Json`), so `2>&1 | jq` is not polluted by progress lines.
- *Implementation pitfall observed in live execution (`zizmor 1.23.1` vs. `zizmor@0af0be98`):* Running `zizmor -qq --format json` on released `zizmor 1.23.1` still wrote `"🌈 zizmor v1.23.1\n"` to `stderr` because an unconditional `eprintln!` bypassed the `tracing` subscriber; `zizmor@0af0be98` (`src/main.rs:247`) fixed this by routing the banner through `tracing::info!`. All `stderr` operational messages must pass through the central verbosity gate rather than ad-hoc `eprintln!` calls.
- **`--format human` + `--quiet`:** Suppresses `stderr` phase progress and spinners, **but never suppresses failure diagnostics or taint/partial-scope caveats** in the primary verdict (`cargo-vet`, `zizmor`, `kani`).
- **Global vs. subcommand flag scoping (`uv`, `cargo-deny`):** `-q`/`--quiet`, `-v`/`--verbose`, and `--color <auto|always|never>` belong globally (`global = true`), whereas `--format` / `--receipt-out` are scoped to subcommands that emit structured reports (`verify`, `inspect`), avoiding meaningless `--format json` combinations on raw text subcommands (`skill`).

---

### 2. Per-Stream Terminal Capabilities, Color Precedence, and CI Environments

Basis: normative (`jcs/no_color@278b6afc`) + documentation (`cli-guidelines@697d6a29`) + source (`cargo@930a674d`, `nix@7dc6d7f2`, `gh@de06af2c`, `zizmor@0af0be98`, `creusot@faeb61f5`, `kani@87c87010`, `lean4@231ef9a2`) + execution (`support/probe_tty_pipe_and_sanitization.py`)

#### 2.1 The Cross-Stream `isatty` Bug (`creusot` and `kani` vs. `cargo`, `gh`, `nix`, `lake`)

When a user runs `cargo anneal verify --format json > receipt.json`, `stdout` is a regular file (`!stdout.is_terminal()`) while `stderr` remains attached to the interactive terminal (`stderr.is_terminal() == true`).

- **Buggy pattern:** `creusot` (`cargo-creusot/src/main.rs:378-385`, `let is_tty = std::io::stdout().is_terminal(); if is_tty { eprint!("\x1b[33mWarning\x1b[0m"); }`) and `kani` (`kani-driver/src/session.rs:423-429`, `let use_colors = std::io::stdout().is_terminal(); ... .with_writer(std::io::stderr).with_ansi(use_colors)`) test `stdout` to configure `stderr`! Redirecting `stdout` silently disables color on `stderr`, and redirecting `stderr` (`2> err.log`) while leaving `stdout` on a TTY leaks raw `\x1b[...` escapes into `err.log`.
- **Sound per-stream pattern:** `cargo` (`shell.rs:49-62`, separate `AutoStream::new(stdout, ...)` and `AutoStream::new(stderr, ...)`), `gh` (`pkg/iostreams/iostreams.go:182-207`, independent `IsStdoutTTY()` and `IsStderrTTY()`), `nix` (`src/libutil/terminal.cc:78-101`, `cached[2]` indexed by `StandardOutputStream::Stdout` vs. `Stderr`), and `lake` (`src/lake/Lake/Util/Log.lean:48-51, 223-229`, `AnsiMode.isEnabled out` calling `out.isTty` on the target `IO.FS.Stream`) evaluate TTY and ANSI support independently per stream.

#### 2.2 Canonical Color and Animation Precedence Hierarchy

Synthesizing `no-color.org` (`jcs/no_color@278b6afc`, `index.md:20-55`), `clig.dev` (`content/_index.md:637-651`), `cargo` (`shell.rs:369-381`), `nix` (`terminal.cc:84-101`), and `zizmor` (`main.rs:155-189`):

1. **Explicit CLI flag (`--color=always|never|auto`, or `CARGO_TERM_COLOR`):** Highest priority; `always` forces ANSI on the target human stream, `never` strips all ANSI styling. (Machine JSON streams **never** contain raw ANSI outside explicitly opted-in string fields such as Cargo's `json-diagnostic-rendered-ansi`.)
2. **Non-empty `NO_COLOR` (`std::env::var_os("NO_COLOR").is_some_and(|v| !v.is_empty())`):** Disables ANSI color even when `CLICOLOR_FORCE` is set (`no-color.org` specifies *"when present and not an empty string"*; note `nix` `terminal.cc:94` and `zizmor` `main.rs:161` check mere presence `.has_value()` / `.is_ok()`, which diverges from `no-color.org` when a user overrides a parent shell via `NO_COLOR="" cmd`).
3. **`TERM=dumb`:** Disables both ANSI color and all cursor/line-erase control sequences (`nix` `terminal.cc:81`, `cargo` `shell.rs:374`).
4. **Forced color env (`CLICOLOR_FORCE` or `FORCE_COLOR` non-empty and `!= "0"`):** Enables ANSI color on non-TTY human output (useful for `| less -R` or CI renderers).
5. **`CLICOLOR=0`:** Disables auto-detected TTY color.
6. **Stream-local `stream.is_terminal()`:** Default under `--color=auto`.

#### 2.3 Dynamic Progress Bars vs. CI Log Hygiene

In `cargo` (`shell.rs:141-162, 369-381, 673-678`), `zizmor` (`main.rs:187-189`), and `nix` (`progress-bar.cc:110-167`):

- **Animated progress (`\r`, `\x1b[K`, cursor hide `\x1b[?25l`):** Enabled **only** when `stderr.is_terminal() && TERM != "dumb" && !is_ci() && !quiet && color != Never`. `cargo` (`cargo_util::is_ci()`, checking `CI` / `GITHUB_ACTIONS` / etc.) explicitly disables progress bars in CI so carriage-return redraws do not turn CI logs into thousands of garbled lines (`shell.rs:370-377`).
- **Erase-before-print discipline:** `cargo::Shell` tracks `needs_clear: bool` (`shell.rs:25, 91-93, 141-154`): before writing *anything* to either `stdout` or `stderr`, if a transient status line is active on `stderr`, it emits `\x1b[K` (`EL - Erase in Line`) so `stdout` receipts and `stderr` warnings never interleave mid-line with a spinner.
- **Signal safety (`nix/src/libmain/progress-bar.cc:126-156`):** If cursor hiding (`\x1b[?25l`) is used, `SIGINT` and `SIGTSTP` (`Ctrl-Z`) handlers must restore `\x1b[?25h` before exiting or suspending; avoiding cursor hiding in favor of `\r...\x1b[K` eliminates orphaned invisible cursors if the process is killed via `SIGKILL`.

---

### 3. Three-Tier Assurance Hierarchy and Failure Presentation in Formal Verifiers

Basis: source (`kani@87c87010`, `verus@1ce6a59b`, `dafny@427892ac`, `cargo-vet@a9bde859`, `zizmor@0af0be98`, `zerocopy@d3362d9a`) + derived

Formal verification tools face a domain-specific UX hazard absent from ordinary build tools: **an exit-code-`0` run with relaxed soundness flags, `sorry` axioms, or `--select` single-function scope must never look visually identical to an untainted whole-crate proof.**

| Verifier / Auditor | How Unproven Assumptions, Vacuity, and Partial Scope Are Surfaced |
| :--- | :--- |
| **`kani`** (`cbmc_property_renderer.rs:410-451, 524-588, 668-678`) | `postprocess_result` rewrites every `CheckStatus::Success` property to `CheckStatus::Undetermined` (styled yellow) if any reachable unsupported Rust construct, unwinding assertion failure, or missing function definition failed. Emits `Vacuous harness: no generated input reaches <fn>` and `** WARNING: A Rust construct that is not currently supported by Kani was found to be reachable` adjacent to the final `VERIFICATION:-` line. |
| **`verus`** (`verifier.rs:3334-3349`, `main.rs:543-558`, `no_cheating.rs:1-151`) | Human trailer appends `" (partial verification with \`--verify-*\`)"` whenever `!is_verifying_entire_crate(&verifier)` (`--verify-function`, `--verify-module`, `--verify-only-module`, `--verify-root`). In `--output-json`, omits `"success": true` entirely on partial runs (`main.rs:543-547`). `--no-cheating` rejects both partial flags and `assume`/`admit`/`external_body`. |
| **`dafny`** (`VerifyCommand.cs:154-183`, `CliCompilation.cs:301-312`) | Final trailer (`WriteTrailer`) reports `"Dafny finished with X verified, Y errors"` and explicitly appends separate non-zero counts for `inconclusive`, `time out`, `out of memory`, `out of resource`, and `solver exceptions` rather than folding non-error solver stops into `"verified"`. |
| **`cargo-vet`** (`resolver.rs:2204-2254`) | `Success::print_human` never emits an unqualified success string; it formats `"Vetting Succeeded (X fully audited, Y partially audited, Z exempted)"`. |
| **`zizmor`** (`output/plain.rs:113-155`) | Even when `findings().is_empty()`, appends bold/bright-yellow parenthesized qualifiers to the final summary line: `"No findings to report. Good job! (1 ignored, 2 suppressed)"`. |

**Closing-verdict invariant for `cargo-anneal`:** In `google/zerocopy@d3362d9a65` (`verify.rs:2152-2155`), taint banners (`--allow-sorry-in-proof`, `--allow-unpinned-lean`, `--allow-unsandboxed-elaboration`) are printed to `stderr` only *before* compilation and Lean elaboration begin. Following `clig.dev` (*"Put the most important information at the end of the output"*, `content/_index.md:712-714`) and the `kani`/`verus`/`cargo-vet`/`zizmor` precedents, human output must distinguish three distinct closing states at the **bottom** of the output:

1. **Tier 1 — Tainted (`!taint_reasons.is_empty()` or `!sorry_declarations.is_empty()`):** Styled **amber/yellow** (`VERIFIED (TAINTED)` — never green), enumerating every active `taint_reasons` atom and `sorry_declarations` count right in the closing block.
2. **Tier 2 — Scoped or Degraded-Environment Verification (`taint_reasons.is_empty()`, but `selected_unit_verified` `K of M` items, non-primary sandbox tier, or `experimental: true`):** Explicitly qualified verdict (`VERIFIED (scoped: K/M items)`), preventing a 1-function proof from appearing to verify the whole crate.
3. **Tier 3 — Clean Whole-Crate Verification (`crate_verified`, `taint_reasons.is_empty()`):** Restrained green `VERIFIED` summary with verified item count and retained artifact path (when present).

On failure (`proof_failed`, `unsupported`, `compiler_failed`, `tool_failed`), human mode renders the phase, status, bounded diagnostic excerpt, and actionable `hint:`/`help:` remediation (`zizmor` `main.rs:457-598`, `rustc` `emitter.rs:130-145`), pointing to `--verbose` or `--artifacts <dir>` when multi-error Lean/compiler output is truncated, while `--format json` / `--receipt-out` preserves the untruncated `detail` string.

---

### 4. Untrusted-String Terminal Sanitization vs. Lossless JSON Encoding

Basis: source (`rust-lang/rust@5debe6a1`, `cli/cli@de06af2c`, `cli/go-gh@4e83b33c`) + execution (`support/probe_tty_pipe_and_sanitization.py`)

Verification CLIs format untrusted strings originating from user/third-party source files and proof scripts (Lean declaration identifiers including `«...»` raw guillemet names, `#error` messages in `detail`, crate/item paths, and relative file paths). Without sanitization, an untrusted `#error "\x1b[2J\x1b[32mVERIFIED\x1b[0m"` or `\r` overwrite can spoof a green terminal verdict.

- **`rustc` (`compiler/rustc_errors/src/emitter.rs:470-535`, `OUTPUT_REPLACEMENTS` + `normalize_whitespace`):**
  - Replaces ASCII C0 `0x01..=0x1F` (except `\n`, with `\t` expanded to 4 spaces and `\r` mapped to `␍` `U+240D`) and `0x7F` (`DEL` -> `␡` `U+2421`) with visible Unicode Control Pictures (`U+2401..U+241F`).
  - Strips `U+200D` (Zero Width Joiner) and replaces all 9 Trojan-Source bidirectional flow controls (`U+202A..=U+202E` LRE/RLE/PDF/LRO/RLO and `U+2066..=U+2069` LRI/RLI/FSI/PDI) with `U+FFFD` (``).
  - **Gap verified by execution (`support/probe_tty_pipe_and_sanitization.py`):** `OUTPUT_REPLACEMENTS` omits `U+0000` (`NUL`) and **all 32 C1 control characters (`U+0080..=U+009F`)**, allowing 8-bit CSI (`\u{009b}32m`), OSC (`\u{009d}`), and ST (`\u{009c}`) through untouched on terminals that interpret C1 controls.
- **`gh` / `go-gh` (`cli/cli@de06af2c`, `pkg/iostreams/iostreams.go:59-65`; `cli/go-gh@4e83b33c`, `pkg/asciisanitizer/sanitizer.go:106-174`):**
  - Wraps external byte streams in `ContentOut`, mapping both C0 and **C1 (`128..=159`)** to inert caret sequences (`^[` for both `0x1B` and `0x9B`), **but** leaves `\r` (`13`) and Unicode Bidi controls untouched (`sanitizer.go:107`).
- **Complete sanitizer composition:** Combining both tables for every untrusted string rendered to human `stdout` or `stderr` — neutralizing `U+0000..=U+001F` (preserving `\n` only inside indented multi-line diagnostic gutters, mapping `\r` -> `␍` so line-overwrite spoofing is impossible), `U+007F`, `U+0080..=U+009F`, and Bidi/invisible formatting controls (`U+061C`, `U+200B..=U+200F`, `U+202A..=U+202E`, `U+2066..=U+2069`, `U+FEFF`) — closes C0, `\r`, C1, OSC 8/52, and Trojan-Source terminal spoofing simultaneously, while RFC 8259 JSON serialization (`serde_json`) preserves exact codepoints losslessly for programmatic callers.

---

### 5. `BrokenPipe` Hygiene, Deterministic Snapshots, Width, and Exit Codes

Basis: source (`ripgrep@4a51093f`, `ruff@3c06ae6c`, `cargo@930a674d`, `cargo-deny@6d512893`, `zizmor@0af0be98`, `dafny@427892ac`, `zerocopy@d3362d9a`)

1. **`SIGPIPE` / `BrokenPipe` without masking verification failures:**
   - Rust sets `SIGPIPE` to `SIG_IGN` at startup, causing `println!` to panic (`exit 101` + panic message) when downstream `head` closes the pipe (`BurntSushi/ripgrep@4a51093f`, `crates/core/main.rs:47-61`; `astral-sh/ruff@3c06ae6c`, `crates/ruff/src/main.rs:51-65`).
   - Writing all output via `writeln!` (never `println!`) and treating `io::ErrorKind::BrokenPipe` on `stdout` as a clean early-close prevents panics (`cargo` `shell.rs:436-442`: `drop(writeln!(self.out(), "{}", encoded))`).
   - **Critical verification invariant:** For informational commands (`skill`, `--help`, `--version`) or `0`-exit verified runs, `BrokenPipe` exits `0`. For a failed `verify` run whose exit code is already `1` or `2`, swallowing `BrokenPipe` must **preserve the non-zero exit code (`1` or `2`)** rather than rewriting it to `0` (otherwise `cargo anneal verify | head -n 1` in a `set -o pipefail` script would falsely report `0` on a failed proof!).
2. **Terminal width, ASCII fallback, and deterministic snapshot tests:**
   - `cargo` (`shell.rs:453-466, 549-569, 657-671`) queries `ioctl(STDERR_FILENO, TIOCGWINSZ)` **only** when `stderr_tty` is `true`; when piped (`TtyWidth::NoTty`), it falls back to `annotate_snippets::renderer::DEFAULT_TERM_WIDTH` (`80`), supports `__CARGO_TEST_TTY_WIDTH_DO_NOT_USE_THIS` for deterministic width tests, and defaults `annotate_snippets` box-drawing to `DecorStyle::Ascii` unless Unicode support is confirmed (`supports_unicode`).
   - To keep human-mode CLI snapshot tests (`cargo-deny` `main.rs:450-520`) byte-deterministic across machines, wall-clock phase timings (`timing_ms`) should either appear only under `--verbose` / interactive progress or be injected into a pure formatting function in unit tests alongside `ColorChoice::Never` and fixed `80`-column width.
3. **Exit-code contracts:**
   - `cargo-anneal` (`verify.rs:365, 2125-2127`), `cargo-audit` (`0` clean, `1` vulnerability/policy failure, `2` CLI/tool error), and `ripgrep` (`main.rs:94-100`: `0` match, `1` no match, `2` error) align on the 3-code POSIX convention:
     - `0`: Verification succeeded (note: if CI requires untainted whole-crate proofs without `jq`, a strict gate flag such as `--deny-taint` / Verus `--no-cheating` should map tainted runs to exit `1`);
     - `1`: Verification or domain failure (`proof_failed`, `unsupported`);
     - `2`: CLI argument error (`clap` usage error on `stderr` with empty `stdout`) or operational/infrastructure failure (`tool_failed`, `compiler_failed`).
   - Note on SARIF (`zizmor` `main.rs:428-429`): `zizmor` forces `ExitCode::SUCCESS` under `--format=sarif` (or provides `--no-exit-codes`) because GitHub `upload-sarif` workflow steps otherwise abort before uploading findings if the scanner step exits non-zero. Primary `json` and `human` verification modes must **not** suppress non-zero exit codes.

## Boundaries

- **Windows Console APIs and ConPTY (`not examined` dynamically):** Windows `GetConsoleMode` / `GetConsoleScreenBufferInfo` and mintty/cygwin fallback paths (`cargo` `shell.rs:681-740`, `nix` `terminal.cc:73-75`) were read in source only and not executed; all live probes ran on Linux `x86_64`.
- **Terminal-emulator-specific `wcwidth` and C1 interpretation (`not examined`):** While C1 control neutralization (`U+0080..=U+009F`) was verified at the byte/codepoint level, differences in 8-bit C1 active-by-default behavior and grapheme cluster widths across individual terminal emulators (xterm, VTE, Kitty, Alacritty, iTerm2, Windows Terminal) were not empirically matrix-tested.
- **Interactive full-screen TUIs (`known not to apply`):** Alternate-screen (`\x1b[?1049h`) interactive proof explorers (such as Why3 IDE launched by `cargo creusot why3`) follow interactive application conventions rather than batch CLI stdout/stderr contracts.
- **Cryptographic/disk integrity from terminal rendering alone (`unsupported`):** Human TTY taint banners and sanitizers render the in-memory verification outcome honestly, but cannot substitute for offline cryptographic or filesystem artifact re-verification when inspecting a saved JSON receipt from disk (covered in `receipt-attestation-audit-cli-inspection-and-anti-spoofing`).

## Evidence

- **Normative and design specifications:**
  - `jcs/no_color@278b6afc683b38452a7b462c13aae5f0f89cee48`: `index.md:20-55` (non-empty `NO_COLOR` specification and precedence).
  - `cli-guidelines/cli-guidelines@697d6a29fc8c93d3981a755c0c7683507ad39c3e`: `content/_index.md:531-800` (TTY vs. pipe output, `--json`/`--plain`/`-q`, color/animation suppression, end-of-output error placement).
- **Modern systems and Rust CLI sources:**
  - `rust-lang/cargo@930a674da900a73c1dfbe16be62c42e75bdfdfc0`: `crates/cargo-util-terminal/src/shell.rs:17-268, 368-679` (`Shell`, per-stream `AutoStream`, `needs_clear` + `\x1b[K`, `progress_supported`, `TtyWidth`, `DecorStyle::Ascii`, `BrokenPipe`-tolerant `print_json`), `src/bin/cargo/main.rs:62-80`.
  - `rust-lang/rust@5debe6a1244452beced762385f88a51857a915fc`: `compiler/rustc_errors/src/emitter.rs:470-535` (`OUTPUT_REPLACEMENTS` and `normalize_whitespace` C0/DEL/ZWJ/Bidi replacement table).
  - `astral-sh/uv@264d8b4a5e10d195d2cc2a34dffa807cfbe6298c`: `crates/uv-console/src/lib.rs:22-98` (`Term::stderr()` prompts/confirmations, `Ctrl-C` cursor restore + exit `130`), `crates/uv-configuration/src/output_format.rs:1-93`, `crates/uv-cli/src/lib.rs:181-211`.
  - `astral-sh/ruff@3c06ae6c84b54b5eb4cc1bc611043d5b978bfa7f`: `crates/ruff/src/main.rs:51-78` (`BrokenPipe` graceful `ExitCode::from(0)` and `writeln!` on `stderr`), `crates/ruff/src/printer.rs:1-120`.
  - `BurntSushi/ripgrep@4a51093f78bfbef86d89275f4916fd6b6039fe9e`: `crates/core/main.rs:45-101` (`BrokenPipe` handling and `0`/`1`/`2` exit codes), `crates/core/flags/hiargs.rs:155-330` (`is_terminal_stdout` layout adaptation).
  - `cli/cli@de06af2c2ea536d5722fda35dc2001565f9b9f64` & `cli/go-gh@4e83b33c301de3d1d4d30df34db06648f898c389`: `pkg/iostreams/iostreams.go:52-208` (`ContentOut` sanitization, separate `IsStdoutTTY`/`IsStderrTTY`), `pkg/iostreams/color.go:44-210`, `pkg/asciisanitizer/sanitizer.go:28-253` (C0 and C1 `0x80..=0x9F` caret sanitization).
  - `NixOS/nix@7dc6d7f2144c509b70c08c011d0adf76d2153927`: `src/libutil/terminal.cc:68-140` (`isOutputARealTerminal`, `shouldANSI` per-fd `NO_COLOR`/`CLICOLOR_FORCE`), `src/libutil/logging.cc:54-136`, `src/libmain/progress-bar.cc:110-180` (`SIGINT`/`SIGTSTP`/`SIGCONT`/`SIGWINCH` cursor hygiene).
  - `sharkdp/hyperfine@c5161524980522320c7d3425e714cc0965a869a5`: `src/cli.rs:312-354` (`--style` and `--export-json <FILE>`).
- **Formal verification and Rust security CLI sources:**
  - `model-checking/kani@87c87010eda7797d7fa14033ca68bcbe17184a63`: `kani-driver/src/args/common.rs:11-33, 82-112`, `kani-driver/src/args/mod.rs:260, 347-357, 535-555, 857-940`, `kani-driver/src/session.rs:414-432` (cross-stream `stdout().is_terminal()` bug), `kani-driver/src/cbmc_property_renderer.rs:380-452, 524-678` (`UNDETERMINED` downgrade and vacuity warnings).
  - `verus-lang/verus@1ce6a59bd72713cf486a7660097fe5ac57519617`: `source/rust_verify/src/main.rs:120-147, 430-574` (`--output-json`, omission of `"success"` on partial runs, `--time` breakdown), `source/rust_verify/src/verifier.rs:3334-3350` (`(partial verification with --verify-*)`), `source/rust_verify/src/no_cheating.rs:1-151`.
  - `dafny-lang/dafny@427892ac6f36204c6a1c760b328b74e0715a0efa`: `Source/DafnyDriver/CliCompilation.cs:55-149, 185-312` (`ExitValue`, `DiagnosticsFormat`), `Source/DafnyDriver/Commands/VerifyCommand.cs:84-183` (`WriteTrailer`), `Source/DafnyDriver/VerificationResultLogger.cs:36-72`.
  - `creusot-rs/creusot@faeb61f5b5a8ffda94fde1f100ef96a1d798088b`: `cargo-creusot/src/main.rs:335-385` (`stdout().is_terminal()` gating `eprint!` warning color).
  - `rustsec/rustsec@bafea68f94f3b9587f826c5b7ceda78955c5ba84`: `cargo-audit/src/config.rs:118-129, 275-299` (`is_quiet` implied by `Json`/`Sarif`), `cargo-audit/src/presenter.rs:71-156`, `cargo-audit/src/terminal.rs:42-171`.
  - `EmbarkStudios/cargo-deny@6d512893fcfea934e8e69c5df44132a4970c42d0`: `src/cargo-deny/main.rs:42-67, 191-196, 226-350, 446-521`, `src/cargo-deny/check.rs:111` (`--audit-compatible-output`), `src/cargo-deny/common.rs:494-546`, `src/cargo-deny/stats.rs:25-91`.
  - `mozilla/cargo-vet@a9bde85910409be3d2d61e6f6ff6ba7a521f0412`: `src/main.rs:256-340` (`ProgressDrawTarget::stderr()`, `--output-file`, JSON error hook), `src/resolver.rs:2114-2254` (qualified `"Vetting Succeeded (...)"`).
  - `zizmorcore/zizmor@0af0be985a4cae71ecfaa64ef574a94b35dc722a`: `crates/zizmor/src/main.rs:155-248, 395-615`, `crates/zizmor/src/cli.rs:137-190`, `crates/zizmor/src/output/plain.rs:101-249`.
  - `leanprover/lean4@231ef9a28b27a9a7ebabdbfa40c84cfb22744c24`: `src/lake/Lake/Util/Log.lean:21-249` (`Verbosity`, `AnsiMode.isEnabled` per `IO.FS.Stream`, `LogLevel`).
  - `google/zerocopy@d3362d9a657e2f943d25a0812f7b13b93e60af4d`: `anneal/trusted/cargo-anneal/src/main.rs:21-180`, `anneal/trusted/cargo-anneal/src/verify.rs:48-180, 2125-2256`.
- **Preserved executable probe (observed `2026-11-23` on Linux `x86_64`, Python `3.13`, `ripgrep 15.1.0`, `zizmor 1.23.1`):**
  - [`support/probe_tty_pipe_and_sanitization.py`](support/probe_tty_pipe_and_sanitization.py)

## Revalidation

Run the self-contained standard-library probe from the corpus root to verify the color-precedence truth table, the `rustc` vs. C1 `0x80..=0x9F` sanitization differential, lossless RFC 8259 JSON round-tripping, and live PTY vs. pipe behavior on `rg` and `zizmor` (when installed on `PATH`):

```bash
python3 reports/cli-tty-human-and-machine-output-for-verification-tools/support/probe_tty_pipe_and_sanitization.py
```

To check whether upstream `rustc` has added C1 (`U+0080..=U+009F`) handling to its diagnostic normalizer or whether `cargo`'s terminal width/progress invariants have changed, diff `compiler/rustc_errors/src/emitter.rs` (`OUTPUT_REPLACEMENTS`) against `rust-lang/rust@5debe6a1244452beced762385f88a51857a915fc` and `crates/cargo-util-terminal/src/shell.rs` against `rust-lang/cargo@930a674da900a73c1dfbe16be62c42e75bdfdfc0`.
