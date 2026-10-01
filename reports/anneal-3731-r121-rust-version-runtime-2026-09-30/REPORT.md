# R121: local annotation discovery across installed Rust compilers

## Scope and subject

The published [R121 annotation gap probe](../anneal-3730-annotation-gap-probes-2026-09-29/REPORT.md) used an invented `//%` line-comment scanner and rustc 1.98.1. The [v85 residual audit](../anneal-3730-3731-residual-38-source-audit-2026-09-30-v85/REPORT.md) retained R121 as contextual: the scanner's text discovery is local code, while the Rust parser can affect whether the containing source compiles and what diagnostic it emits. This report isolates that boundary with the original compiler, the 2026-05-31 nightly, and the exact newer Rust nightly 2026-09-17 named by v85.

## Method

`run_probe.py` imports the published scanner byte-for-byte (SHA-256 `c80616ee85dcb6437eff17c18e1cf1a03b6f3037c61238ea7f47d1e5c5ee8b7b`). It copies the `baseline` and `rust_incomplete` source strings from the published `raw-results.json` (SHA-256 `dc81039a29949d647c4594a2ca1f73658a077378ce7acca87a654c9b0e036cbe`) into local CRLF-preserving fixtures. It asserts exact agreement with the published scanner blocks, mapped intervals, and projection, then invokes each rustc with `--crate-type lib --emit metadata -o <local-output> <fixture>`. It removes any prior output file immediately before each compiler invocation, so a failed compile cannot inherit stale metadata.

The compiler identities are:

| Compiler | Commit | Executable SHA-256 |
| --- | --- | --- |
| `rustc 1.98.0-nightly`, toolchain dated 2026-05-31 | `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` | `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc` |
| `rustc 1.98.1`, Homebrew, the original probe's compiler | `48a229ceaefd4985c50990b14116b6d856af0985` | `2814fb55fb9cfb3eef5848a8104d77e3de7fd95394661144a12ee90cd4405340` |
| `rustc 1.100.0-nightly`, toolchain dated 2026-09-17 | `923c95cdf5ba65cea505aa2ea829f578e1506ed8` | `25f765e04b0d2cea011e4e85b9d48e1587ea449786259e16b17f01cabc848c3b` |

## Observation

The baseline source (`74e1732c32004df0e0c6c9af6626f571235480fa47128a7e0db94a4a979d0aa5`) compiled successfully under all three compilers. The malformed source (`41010e6f5c2229314abc201dc5f61eca18b4f66003ffcb11125a54b2b445ae02`) exited 1 under all three. Their diagnostic text was byte-identical in this run: `this file contains an unclosed delimiter`, with the opening `(` at line 1 and the caret at line 5's `//% end`. No compiler emitted metadata for the malformed file.

The unchanged scanner found a complete annotation block in both sources. Its projected Lean hash was identical for both (`50563baaac37c3657259adb3659365b4c2857b3030a2a80a933e176f9aa6dd49`). Thus this fixture again demonstrates text discovery despite Rust parse failure. It does not attach the text to a compiler-backed Rust subject. The exact newer target showed **no compile-status or diagnostic difference in this specific fixture**; successful baseline `.rmeta` bytes differed across compilers, which is outside the scanner/diagnostic claim and is not interpreted here.

The v85 source audit found a Rust parser source difference at its September target. This executed fixture narrows its consequence: the selected malformed comment has the same acceptance status and diagnostic at that target. It does not establish parser equivalence across other malformed inputs. It also does not test newer Lean/Aeneas, actual Anneal annotations, a full parser recovery corpus, or production editor integration. The local scanner claim remains contextual because an implemented Anneal parser/attachment path was not exercised.

## Reproduce and evidence

From this directory, run `python3 run_probe.py`. The script writes only `fixtures/` and `evidence.json` here. `evidence.json` (SHA-256 `e1d6821847e7da81520a5c506efc57348bce52189f098f450b9fe9faf2f41ad9`) stores the full `rustc -Vv`, exact compiler commands, exit codes, stdout, stderr, source and executable hashes, scanner blocks, projection hashes, and metadata hashes. The independent reviewer first ran the exact 2026-09-17 compiler on these fixtures and confirmed the result; the final author replay captured all three compilers in one record. `run_probe.py` has SHA-256 `8d21b766f27234b58da8a929536c15b0e9cb664908be3fdcbc24f1ba385fc876`.
