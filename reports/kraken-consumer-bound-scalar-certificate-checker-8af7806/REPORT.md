# Consumer-bound scalar certificate checker

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

A pure Lean checker now has universal parsing, artifact/request binding and acceptance-soundness proofs for one serialized AArch64 leaf certificate language. For every consumer request, candidate image and raw certificate, successful checking implies the fixed consumer machine contract using actual Kraken effects and separated resources. The producer supplies data only. It cannot choose an AST, property, imports or resource authority.

The checker and positive/negative instances have been checked by ordinary kernel reduction on Lean 4.34.1. This is bounded E44 prototype evidence and an E45 proof reduction for the admitted pure grammar. Compiled consumer execution, filesystem/importer/loader correspondence, formal Arm reference adequacy and actual Rust/MiniRust resource linkage remain open. No execution milestone checkbox is closed by this package itself.

## Applicability

The imported model is [Kraken 8af78062037bc237b341d20252aafd1797c1bcb7](https://github.com/AeneasVerif/kraken/tree/8af78062037bc237b341d20252aafd1797c1bcb7), using the existing Lean 4.34.1 library. Lean's commit is `5045d0056413266e57c625dcd7c365b10e377c52`. The unchanged [Adapter.lean](support/Adapter.lean) is copied from frozen companion package `kraken-checked-aarch64-byte-leaf-resource-adapter-8af7806`; its exact manifest/source and imported-library identities are in [source-evidence.json](source-evidence.json). Frozen inputs were not edited.

The consumer's complete initial raw image is `00004039c0035fd6`: eight bytes for `ldrb w0,[x0]; ret`. Its typed request independently fixes that entire image, entry offset zero, PC 4096, AArch64 target, the pinned Kraken model selector and the full byte-read/frame claim. The owned [raw image](artifacts/read-byte-a64.bin) and [certificate](artifacts/read-byte-frame.cert) are transport artifacts; the proved subject is their explicit pure Lean byte values and serialization. There is no theorem connecting arbitrary filesystem reads to those values.

## Findings

### Exact finite data grammar

[Consumer.lean](support/Consumer.lean) implements the parser and checker. The certificate has exactly 19 bytes:

| Bytes | Meaning |
|---|---|
| 0–2 | Magic `KRC` |
| 3 | Format version 1 |
| 4 | AArch64 target tag 1 |
| 5 | Selected Kraken model tag 1 |
| 6 | Read-byte/full-modeled-frame claim tag 1 |
| 7–10 | Unsigned little-endian 32-bit entry offset |
| 11–18 | Unsigned little-endian 64-bit PC, restricted below `2^63` |

`parse_iff` proves, for every raw list and parsed field value, that successful parsing is equivalent to exact serialization with entry below `2^32` and PC below `2^63`. Its proof includes byte-field bounds, reconstruction, a round trip under those bounds and exact exhaustion. Unknown magic/version/target/model/claim values fail the fixed header. Missing and trailing bytes fail the length requirement. Serialization of out-of-range natural-number fields is not claimed injective; the round-trip theorem states its bounds explicitly.

The parsed type contains only two natural numbers. The exact serialized language has no expression, proof term, declaration, imported theorem name, axiom, native-evaluation request, SMT obligation, external callee reference or arbitrary postcondition. `closed_grammar` connects every successful checker input to that complete data grammar. This is complete dependency coverage for this language, not a general Lean/SMT dependency checker.

### Consumer binding is structural and universal

`check_binding` quantifies over arbitrary consumer requests, candidate images, raw certificates and returned executables. Success establishes:

- Structural equality of the whole candidate image and consumer-owned image.
- The consumer-selected supported target, model and full-frame claim.
- Equality of certificate entry/PC fields with the consumer's independently selected entry/PC, and an in-bounds eight-byte slice.
- The existing adapter's `LayoutOK` condition, canonical extracted bytes, and exact generated Kraken executable at the consumer's PC.

The checker obtains these facts by parsing raw producer data, comparing full image values, checking fields/span and invoking the actual frozen adapter certificate on the extracted slice. It does not assume an earlier stage accepted or that a quoted AST describes the bytes. No hash-equality or collision-resistance premise appears in the theorem. SHA256 values in [artifact-data.json](artifact-data.json) are transport receipts only.

The caller must select `Request` independently of producer data. Changing both the trusted request image and candidate image legitimately changes the certified subject. Independent kernel controls demonstrate this: the fixed request rejects a candidate tail, while a deliberately changed trusted request accepts that different complete image. Even that changed request rejects the unsupported result-only claim. The all-request theorem proves soundness relative to the selected request; it does not authenticate who selected it.

### Acceptance implies the fixed actual machine contract

`consumer_sound` and its Boolean acceptance corollary `accepted_sound` establish the fixed consumer `Meaning`. This directly names actual Kraken execution and the literal full-frame postcondition. For arbitrary MachineData `d`, byte `v`, address `base`, disjoint frame predicate `R` and execution predicate, callers must supply these logical premises:

- X0 contains the complete 64-bit `base` address.
- Actual data memory satisfies `Eq(v.At base) ⋆ R`.
- The two instruction ranges have execution permission.

No certificate field can manufacture those premises. Acceptance is a conditional resource contract; it does not test runtime ownership or prove a load safe without the premises. The map-cell witness is not a MiniRust allocation/provenance/borrow interpretation or a fractional Rust shared-reference resource.

Composing the parsed binding with the actual adapter proves strict read/execute permission checking, the complete ordered effect trace, the whole modeled final state and separated frame, return through original X30, each individual instruction step, and mathematical PC endpoints. Only X0 changes, to the zero-extended byte. Memory, X1–X30, SP and NZCV are preserved. Data addresses retain all 64 bits; the existing non-wrapping one-byte span proof is reused.

### Positive execution and rejection evidence

`concrete_accept` checks the fixed consumer request and certificate by ordinary `rfl` reduction; `concrete_meaning` instantiates the universal theorem. Fourteen named reductions reject changed byte 0, an extra byte in the full candidate image, missing/trailing certificate input, different entry/PC, target/model/claim tags, format version, a PC with the top bit set, wrong consumer target/model and a weaker result-only request. The full-image tail case retains the same valid first eight instruction bytes, so it specifically checks whole-subject binding rather than slice equality alone.

Universal rejection theorems cover wrong full images, arbitrary wrong lengths/headers, every trailing byte, unsupported requests and parsed entry/PC mismatches. Accepted wrong-span, wrong-return and wrong-X19-frame specifications are separately refuted using actual separated resources and Kraken execution. The weaker request is unsupported and rejected; it is never counted as proving the original full-frame contract. The frozen adapter's universal changed-code rejection remains available and is not replaced with a finite mutation-only claim.

## Boundaries

The pure checker theorem is about explicit Lean values. Lean parsing/elaboration, selected imports, kernel computation and kernel checking remain trusted. A compiled standalone checker, its compiler/runtime, file reader and OS loader require additional correspondence theorems. This package performs no compiled consumer execution and no native Rust execution.

The model selector identifies the selected imported definitions through the recorded source/library identities; it is not a cryptographic model-import checker. The raw image is not the whole Mach-O artifact or deployed process image. General source assembly, preprocessing, relocations, linking, arbitrary claims/instructions and dynamic code changes are outside this grammar.

The inherited hardware/model boundary remains explicit: Kraken omits Arm GCS-related RET accesses, branch-type/system state, tags, translation and relevant fault machinery. The complete trace claim is for actual Kraken effects under the stated machine resource premises. Formal reference adequacy (E29), actual Rust/MiniRust provenance/borrow/continuation adequacy (E35), broader byte/source/loader proofs (E28), generic access/resource authority (E30) and broader E45 remain open.

## Evidence

[replay-results.json](logs/replay-results.json) records the successful pure proof replay. All 37 new audited declarations and 32 audited copied-adapter declarations depend only on subsets of `propext`, `Classical.choice` and `Quot.sound`, or have no axioms. No successful declaration depends on `sorryAx` or a native-evaluation axiom. See [Consumer.log](logs/Consumer.log) and [Adapter.log](logs/Adapter.log).

Independent replay checked exact copied adapter/consumer sources and their 69 declaration closures against the same pinned library. Four additional [review controls](support/ReviewControls.lean) bind the actual 8/19-byte transport literals and exercise the request-ownership distinction above; their [captured output](logs/independent-request-controls.stdout) has only foundational axiom subsets. These observations do not prove filesystem-reader adequacy.

[replay-commands.json](logs/replay-commands.json) records three serial commands: version, copied adapter proof and consumer proof. `LEAN_NUM_THREADS=1` bounds these owned builds; no installation, upstream build, network/Git/canonical mutation or compiled consumer run was performed. [development-status.json](development-status.json) distinguishes ordinary failed elaboration attempts from final proof results. No unexpected panic, assertion failure or semantic disagreement occurred.

## Revalidation

With the exact existing Kraken library and Lean 4.34.1, run from the package directory:

```sh
python3 support/replay.py --lean /path/to/lean --kraken-lib /path/to/kraken/.lake/build/lib/lean
```

The helper rebuilds the unchanged owned adapter copy and consumer proof serially, captures all commands/closures, and stops on command failure, panic/assertion diagnostics or extra proof axioms. This replays the pure kernel proofs and fixed request reductions. It does not run or prove an executable file-consuming application.

The additional `support/ReviewControls.lean` can be checked after the helper with the same Lean and `LEAN_PATH` (the pinned Kraken library plus this package's `support` directory). It adds four request/literal controls without changing the checker or its claim.
