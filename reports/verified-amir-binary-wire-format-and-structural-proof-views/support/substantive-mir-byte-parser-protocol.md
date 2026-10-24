# Protocol: Substantive MIR/ULLBC Byte Parser and Trusted-Frontend Boundary (`FD-02` / `FE-F4`)

*Authored by an AI agent acting on joshlf's behalf.*

## 1. Objective and Hypotheses

This experiment (`experiments/opsem/substantive-mir-byte-parser`, Task `FD-02` / `FE-F4` of `#56`, `#45`, and `#36`) executes the pre-registered scope in [`docs/rust-opsem/substantive-mir-byte-parser-scope.md`](../../../docs/rust-opsem/substantive-mir-byte-parser-scope.md):

1. **Substantive Binary Wire Grammar (`AMIR` v2)**: Defines a non-trivial binary wire format emitted by `direct_mir_driver_v3.rs` on `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` with an 8-byte package header (`"AMIR"`, version `2`, default `MirPhaseTag`, `preserveUb` flag byte, `bodyCount`), variable-length `WireBody` records carrying per-body `(BodyOriginKind, MirPhaseTag)` headers, and variable-length basic blocks with 3-byte statements and 4-byte terminators.
2. **Independent Byte-Level Specification (`specEncodePackage`) and Total Parser (`parseWirePackage`)**: Separates the inductive byte specification `specEncodePackage : WirePackage → List Nat` from the recursive byte-stream parser `parseWirePackage : List Nat → ParseOutcome WirePackage` and Layer 2 structural checker `checkPackageWellFormed : WirePackage → Bool`.
3. **Universal Accepted-Byte Soundness and Canonical Uniqueness**: Mechanizes universal theorems (`universal_accepted_byte_soundness` and `universal_accepted_package_canonical_unique`) proving over all `bytes : List Nat` and `pkg : WirePackage` that `parseWirePackage bytes = .accepted pkg` implies `specEncodePackage pkg = bytes`, `checkPackageWellFormed pkg = true`, and `unconsumedTrailingBytes bytes = 0`.
4. **5-Layer Trusted-Frontend Boundary**: Mechanizes and empirically separates Layer 1 (wire syntax, framing, trailing bytes, unsupported opcodes), Layer 2 (structural body well-formedness), Layer 3 (untrusted sidecar metadata isolation), Layer 4 (trusted compiler provenance digest), and Layer 5 (semantic phase and flag adequacy).

## 2. Real Compiler-Emitted `.amir` v2 Artifacts (`artifacts/v3/`)

| File | Size (Bytes) | SHA-256 | Parser Outcome |
| --- | --- | --- | --- |
| `place_mention_preserve_ub.amir` | `176` | `c972e1cefcc58ef20f4832c8c995cd31cf54db34cdb8e1e941fff66ebf374380` | `.accepted` (`3` `LocalOwner` bodies at `runtimePostCleanup`; all `3` preserve `PlaceMention`) |
| `place_mention_default.amir` | `167` | `408bd28d0c990cf47b38d3b10e80bedb4c0993edb03906e8f3f524ac862cabd7` | `.accepted` (`3` `LocalOwner` bodies at `runtimePostCleanup`; `0` `PlaceMention`, fails Layer 5 raw-pointer validity adequacy) |
| `cleanup_subject_preserve_ub.amir` | `806` | `455bbb33f94cd63f9449f3adea660f23d2bb39bf975917b0b01914c6f2942e32` | `.accepted` (`8` bodies: `6` `LocalOwner` at `runtimePostCleanup` + `2` `CompilerShim` `DropGlue` at `runtimeOptimized`) |
| `feature_ladder_sync.amir` | `458` | `8f213187ff6a0a514a65345c398201ea31e9ab6508eb93bc4f517d486cf6a0df` | `.accepted` (`8` bodies, exact round-trip) |
| `zerocopy_layout_holdout.amir` | `1,409` | `ed948d8954321f13247477d25c64fe94e6726b079fa006e146138b61b6a13041` | `.accepted` (`10` `LocalOwner` bodies, exact round-trip) |
| `control_layer1_truncated.amir` | `174` | `7a98756497c7e7c2ca9b783d1be5b9a1bee3c2b5ca43a82dcc4354231ae39400` | `.rejectedMalformedSyntax` (Layer 1a) |
| `control_layer1_trailing.amir` | `177` | `ebc85715bd0d721e0d46804f7e9b4e2a3d3160e8a1662ab21a49a3df22403ff0` | `.rejectedTrailingBytes 1` (Layer 1b) |
| `control_layer1_unsupported_asm.amir` | `176` | `08d90df456753712bdd725ec0dfb8221d63445954453017aab508952d1f3e2b3` | `.rejectedUnsupportedFeature 224` (`0xE0` `InlineAsm`, Layer 1c) |
| `control_layer2_oob_local.amir` | `176` | `16c3a63108fa8a6434d7d6398e2e136c671e34e1c7f2429039e4d05cfdd18065` | `.rejectedIllFormedBody` (`StorageLive(6)` where `6 >= localCount = 6`, Layer 2) |

## 3. Checked Lean 4 Artifacts (`leanprover/lean4:v4.34.1`, `lean -j1 -M768`)

Recorded in `check-results.json` (`sha256: b149cf54769f39484e31e3ca216717f5ec42b9c7ffe03c3dd17fc5010f2cc693`):

- `experiments/opsem/AnnealResearch/SubstantiveMirByteParser.lean`: `sha256: 0464c2c1866dec85a6391fbc580607bd62f1005b6fd7930d7193246dbd446918`, `olean_sha256: 7263422260fa6abce14bcc5db8e1e3354e3b39fcfeecf9a53c47dcfab3b5c28e`, `exit_code: 0`, `wall_clock_ms: 5137`, `max_rss_bytes: 700022784`.
- `experiments/opsem/AnnealResearch/SubstantiveMirByteParserControls.lean`: `sha256: 209090f50262d238a63b7fb5f997ff6a2f6178253f02193da4ab08c0deeca41e`, `olean_sha256: 6b6ea5d423d2b2ec1f82e6021037855c456bee875e92bdb587d9a0be98c6428b`, `exit_code: 0`, `wall_clock_ms: 860`, `max_rss_bytes: 554807296`.

## 4. Issue `#61` Continuation Update (`Milestone C1` — Faithful, Fail-Closed `.amir` v3 Wire Format)

*Updated by an AI agent acting on joshlf's behalf.*

Sections 1–3 above preserve the historical `#56` `.amir` v2 baseline (`artifacts/v3/`). Under Milestone `C1` of [`joshlf/anneal#61`](https://github.com/joshlf/anneal/issues/61), [`direct_mir_driver_v4.rs`](../real-mir-ullbc-capture/direct_mir_driver_v4.rs) (`artifacts/v4/`, `capture-v4-ledger.json` SHA-256 `9846338162a0cbe47ae9870315689f6f0b20f455adca94846dd3eac4c772b2b3`), `SubstantiveMirByteParser.lean`, and `SubstantiveMirByteParserControls.lean` (16 `#print axioms` audits) upgrade the wire grammar to `.amir` v3 (`version = 3`, `maxSupportedBlocks = 32`, `physicalBytesValid` byte-range guard `b <= 255`, zero block truncation, zero target clamping, and 5-boundary negative controls). See [`check-results.json`](check-results.json) for updated `.lean`/`.olean` SHA-256 digests.
