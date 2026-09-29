# Aeneas declaration manifest and fresh Lean batch oracle on an independent Rust fixture

## Summary

On one new three-function Rust crate, pinned Charon and one-shot Aeneas generated Lean modules that the cached Lean 4.30.0-rc2 batch checker accepted. Changing only the body of `inc` from wrapping `+1` to wrapping `+2` changed the generated `Funs.lean` and the checked Lean results: `inc 0`/`twice 0` evaluated to `1`/`2` before and `2`/`4` after. Each matching theorem compiled, and each deliberately wrong result theorem failed with an `rfl` error. A forged LLBC `charon_version` marker was rejected by Aeneas before it emitted files. This extends the earlier [Aeneas identity/manifest report](../anneal-3730-aeneas-identity-manifest-2026-09-29/REPORT.md) with an independently authored small Rust input and a fresh Lean consumer; it does not establish Rust-level translation correctness beyond these selected executable examples.

An `extern "C"` Rust function produced `FunsExternal_Template.lean` containing an axiom and made generated `Funs.lean` import a separate `FunsExternal` module. Lean failed without that module. With the axiom template supplied, the call compiled and `#print axioms` named `external_double`. With a concrete user-authored Lean model supplied against the **same generated Aeneas bytes**, `call 1` evaluated to `ok 2`, its theorem compiled, and Lean reported no axioms for `call`. Thus generated Lean file hashes alone do not identify the accepted external-model environment. The concrete model is a test assumption about the external Rust function, not a verification of its implementation.

## Applicability

The commands ran on macOS arm64 with installed Charon 0.1.210 (`51bb6d23…`), Aeneas nightly-2026.06.03 (`f476001e…`, whose `-version` reports `unknown`), Lean 4.30.0-rc2 (`b48bc5ab…`), and the existing prebuilt Aeneas Lean library (`Aeneas.olean` SHA-256 `67701a9e…`). Full hashes are in `REPORT.json` and `support/results.json`. `support/probe.py` uses only these installed executables, existing local Lean dependency artifacts, and Python's standard library; it checks at least 10 GiB free disk and runs one Lean process at a time. No global install, download, source rebuild, or Aeneas in-process library call occurred.

The new `oracle_probe` Rust fixture contains `inc`, `twice`, and `choose` as ordinary Rust functions. A second fixture contains an unsafe foreign declaration `external_double` and a `call` wrapper. `support/work/` retains exact `.rs`, `.llbc`, generated `.lean`, two user-model `.lean` files and tiny compiled `.olean` outputs. Generated source comments contain this checkout's absolute path; after relocation, source-comment and output byte hashes may change even when the translated body is the same. These fixtures are distinct from the earlier identity report's type/trait/recursive example, so they add a fresh consumer check rather than rerunning its preserved output.

## Findings

### Schema, declaration set and controlled body mutation

The script ran pinned `charon rustc --preset aeneas` over each saved Rust source, then one independent `aeneas -backend lean -no-progress-bar -sequential -split-files -gen-lib-entry -print-unknown-externals` process per LLBC in private output directories. The base and mutated LLBCs both declared the same three local functions. The external case declared the foreign function and wrapper. `support/declaration-manifest.json` records the complete Charon local declaration IDs/spans, Aeneas-generated declaration heads/file/line and nearest source comments for all three inputs. The observed base generated set was `Base.lean`, `Types.lean`, `Funs.lean`; the external set additionally had `FunsExternal_Template.lean`. **Basis: execution plus parsed artifacts.** A nearest source comment is a lexical hint; the manifest intentionally leaves `proven_def_id_to_lean_range` and `anneal_obligation_mapping` null.

| Control | Charon/Aeneas result | Independent Lean result |
| --- | --- | --- |
| `inc` uses `wrapping_add(1)` | LLBC SHA-256 `c25b76cd…`; `Funs.lean` `ae306b7a…` | Fresh batch compiled generated modules; `inc 0 = ok 1`, `twice 0 = ok 2`; matching `rfl` proofs passed; `inc 0 = ok 2` failed. |
| `inc` uses `wrapping_add(2)` | LLBC `359f1ad1…`; `Funs.lean` `97ef3a43…`; `Types.lean` byte-identical to base | Fresh batch compiled; `inc 0 = ok 2`, `twice 0 = ok 4`; matching proofs passed; `inc 0 = ok 3` failed. |
| Base LLBC with forged `charon_version=0.1.999` | Aeneas exited 1 with explicit incompatible-version error; output directory empty | No generated modules submitted as current. |

The `twice` Rust text itself was unchanged across the body mutation, yet its Lean evaluation changed because it calls `inc`. This is a concrete whole-translation dependency witness for I083. It does not prove a minimal invalidation graph, translation correctness for every input, or equivalence of byte-different generated files. The base `#print axioms oracle_probe.inc` reported Lean's `[propext, Classical.choice, Quot.sound]`; the script specifically checks no `sorryAx` in the accepted result, and does not claim axiom-free foundational Lean acceptance. The wrong-theorem controls demonstrate checker sensitivity at this small claim, not a full Rust obligation oracle. **Basis: execution.**

### External-model identity and missing-input boundary

For the foreign declaration, Aeneas emitted an `External.Funs` import of `External.FunsExternal` and an `FunsExternal_Template.lean` with `axiom external_double : Std.U32 → Result Std.U32`. The generated `External`/`Types`/`Funs`/template file hashes were held fixed while each consumer got a different separately authored `FunsExternal.lean`. When none was supplied, batch Lean failed on the missing object. Copying the template into the expected module allowed compilation, but `#print axioms oracle_probe.call` listed `[external_double]`. Replacing only that user model with `def external_double (x : Std.U32) : Result Std.U32 := ok (core.num.U32.wrapping_add x x)` produced a compiled `call` whose `call 1 = ok 2` theorem passed and whose axiom print said it did not depend on any axioms. The two model-source hashes were `20c41bce…` and `8685ca7f…`. **Basis: execution, exact generated/model inventories and batch transcripts.**

This is an external *Lean model supplied after Aeneas generation*. It is not a mutation of the Aeneas executable's compiled external-definition registry. The foreign Rust declaration has no linked executable implementation in this fixture; the concrete Lean definition is an assumption whose relation to a real foreign function was not checked. Consequently, the evidence supports an import/model-identity requirement and a trust distinction, but it cannot certify Rust-to-Lean soundness for `call` or answer the original I082 registry-change question.

### Exact residuals for #3731

| Item | Added evidence in this package | Remaining distinguishing work |
| --- | --- | --- |
| I082 | CLI schema mismatch, selected builtin `wrapping_add`, unknown external template, two user-model hashes with fixed generated bytes | Mutate the **compiled** external-model registry and test normalization/tool revision collisions with a source-to-binary build witness; the installed CLI cannot exercise that mutation alone. |
| I083 | Changed `inc` body changes unchanged caller `twice`'s checked result | Trait/external-model dependency closure, finer-grained cache prototype and broad semantic oracle. |
| I084 | Complete three-function declaration heads, file/line and source-comment inventory before/after body edit | Reorder/module moves, name/signature stability under more structural changes, and full proof-context comparison. |
| I085 | Explicit generated set and missing/axiom/concrete external model consumer states | Registered user-maintained external model, overwrite collision, stale-output shrink and atomic publication; earlier identity report covers selected file-set failures. |
| I086 | File-based LLBC/Lean handoff and actual batch consumer | In-memory or structured-stream implementation and measured cost; same-process Aeneas remains dependency-gated. |
| I087 | Charon def IDs/spans and generated declaration lines/comments retained together | Authenticated item→declaration/range map, completeness for many-to-one output and comparison with a newer `translation.json`; lexical comment association is insufficient. |
| I088 | Explicit schema rejection and missing external Lean import | Warnings, Aeneas crash/cancellation, structured diagnostic provenance and same-process error reset. |
| I148 | One-shot body mutation and generated/Lean semantic response; schema control | Concurrent/parallel modes, harmless text/path/order/flag variations with a calibrated comparator and downstream cost. |
| I149 | Complete fixture manifest with exact input/generated/model hashes and nullable proven links | Rust→Charon→Aeneas→Lean→obligation correspondence consumed by navigation/editing, including one-to-many mappings. |

No row is claimed complete. In particular, Aeneas source code in the local checkout is not authenticated as the exact build input of this `-version unknown` binary, and the external user model is not the executable's compiled registry. These boundaries were retained from the earlier report rather than erased by the fresh batch check.

## Boundaries

- **Not examined:** same-process Aeneas library reset or concurrency; in-memory LLBC/Lean handoff; a second Aeneas release; actual compiled external-registry change; nontrivial Rust model correspondence proof; Lean LSP/MCP; an Anneal obligation map. Installed one-shot CLI use cannot settle those claims.
- **Not established:** that batch success for a few generated examples implies all Rust semantics are preserved, or that an axiom-free concrete external Lean definition matches a foreign Rust implementation. The foreign declaration lacks an implementation here.
- **Source ranges:** Charon spans and Aeneas comments/Lean lines coexist in the manifest, but no producer-issued authenticated mapping joins their IDs. Generated absolute source paths and LLBC locators can affect bytes after relocation.
- **Environment:** the batch checker imported prebuilt Aeneas and Mathlib dependency artifacts already on this machine. It did not rebuild that environment from source or attest all transitive artifact hashes; only the top-level `Aeneas.olean` and executable hashes are recorded here.

## Evidence

- `support/probe.py` SHA-256 `2ff31ce81b1a85295b34c3f9aaf80e2e9f36379b4a7da4d266030e34ccd8bb56`: constructs the two Rust fixtures, runs Charon/Aeneas in private destinations, creates the three external-model consumer states, compiles generated modules in import order, and asserts the positive/negative Lean oracles. **Basis: executable procedure.**
- `support/results.json` SHA-256 `e5da18ed41a366760621b10a8bbfe0350104493706e997fb1633221e3fc1bba1`: all 29 commands, exit codes, stdout/stderr, subject hashes, source/LLBC/generated file hashes, model hashes and explicit unsupported dimensions. Four expected failures are schema mismatch, two wrong theorem proofs and missing external model.
- `support/declaration-manifest.json` SHA-256 `a3a20c859da78e1ecf0a893d674e2e7fa2f6e582ed1bb463cbca9915e1411f9c`: complete Charon and generated Lean declaration inventories with explicit null proven links. `support/work/` preserves source, LLBC, generated, model and compiled artifacts for all cases; it is about 316 KiB.
- The adjacent [`anneal-3730-aeneas-identity-manifest-2026-09-29`](../anneal-3730-aeneas-identity-manifest-2026-09-29/REPORT.md) report has a different Rust type/trait/recursive fixture and more one-shot option/file-set controls. This package extends its evidence without rerunning or modifying it.

## Revalidation

From this package, run `python3 support/probe.py` while the exact installed binaries and cached Lean dependencies remain at the paths recorded in the script. The script replaces only its own `support/work`, manifest and results; it neither installs dependencies nor invokes `lake update`. Verify the 29 command records, four expected failures, accepted base/mutated theorem outputs, empty schema-output directory, and fixed generated external files under both user-model variants. Recompute source/output identities after relocation because generated comments contain absolute paths. For a future Aeneas release or an actual compiled registry change, use a separate version-pinned package and compare complete generated/Lean/import/model manifests rather than carrying this binary's conclusion forward.
