# Zerocopy public byte APIs, cross-target layout controls (`aarch64` vs. `wasm32`), and packet/SMT certificate architectures

## Summary

Across `google/zerocopy@8fb35253fbc703cb2cd0997f4efcda76cf9062b6` (crate version `0.8.63`, with public `TryFromBytes`, `FromBytes`, `IntoBytes`, and byte-order implementations shared with `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`), native `aarch64-apple-darwin` and standalone `wasm32-unknown-unknown` execution controls combined with Lean 4 (`v4.31.0` and `v4.34.1`) and SMT (`cvc5 1.4.2` $\rightarrow$ Alethe $\rightarrow$ `Carcara 1.1.0`) certificate experiments establish five core reference results:

1. **Exhaustive finite byte-domain and write-preservation controls across `aarch64` and `wasm32`:** Calling `bool::try_read_from_bytes` across all `256` one-byte inputs accepts only `0` (`false`) and `1` (`true`), and calling `[bool; 2]::try_read_from_bytes` across all `65,536` ordered two-byte inputs accepts only the `4` pairs in `{0, 1} × {0, 1}`. Eighteen additional controls verify scalar/unit-array width mismatches, `U16<LE>` vs. `U16<BE>` endian decoding, 8-offset alignment checks via `u16::ref_from_bytes`, prefix/suffix write preservation of unselected destination bytes, and full destination preservation on short-write rejection. Both targets pass identically (`0.0075 s` native in-process loop vs. `0.0251 s` Node/V8 WebAssembly loop).
2. **Target-dependent `#[repr(C)]` and `#[repr(C, packed)]` layout divergence (`aarch64` vs. `wasm32`):** Because `size_of::<usize>()` and `align_of::<usize>()` are `8` bytes on `aarch64-apple-darwin` and `4` bytes on `wasm32-unknown-unknown`, `#[repr(C)] struct { a: u8, b: usize }` has `(size, align, b_offset) = (16, 8, 8)` on `aarch64` versus `(8, 4, 4)` on `wasm32`, while its `#[repr(C, packed)]` counterpart has `(size, align, b_offset) = (9, 1, 1)` on `aarch64` versus `(5, 1, 1)` on `wasm32`. Similarly, `#[repr(C)] struct PacketRecord { word: usize, flags: [bool; 4], header: [u8; 2] }` has `(size, align, flags_offset, header_offset) = (16, 8, 8, 12)` on `aarch64` and `(12, 4, 4, 8)` on `wasm32`. Layout certificates specialized to a 64-bit host cannot be reused unmodified on a 32-bit target.
3. **Composed packet API (`decode_write`) and Lean 4 certificate reuse costs:** A composed packet decoder/writer (`decode_write`) combining `[bool; 4]` validation, `U16<LE>` payload-length decoding, slice bounds checking, and `write_to_prefix` passed all `58,240` structured test cases and `1,024` single-flag byte controls on both `aarch64` and `wasm32`. Checking target-instantiated Lean 4 (`v4.34.1`) receipts against a precompiled shared list model (`PacketModel.lean`, `1.200 s` build, `64,008`-byte `.olean`) takes `351–367 ms` per `aarch64` receipt (`972` source bytes) and `332–337 ms` per `wasm32` receipt (`962` source bytes), while deliberately mismatched target/width (`wrong_target.lean`) and field-count (`wrong_type.lean`) receipts are rejected by the Lean kernel.
4. **Shared `Rust.Layout` geometry instantiation and negative layout discrimination (`LayoutBridge.lean`):** Instantiating `Rust.reprCSliceDstSize_aligned` and `Rust.roundUpToAlign_ge` in `LayoutBridge.lean` over 5-field primitive vectors (`[8, 4, 1, 2, 1]` on `aarch64`, `[4, 4, 1, 2, 1]` on `wasm32`) and 12-field aggregate vectors (`[16, 8, 8, 12, 1, 1, 4, 1, 2, 1, 8, 8]` on `aarch64`, `[12, 4, 4, 8, 1, 1, 4, 1, 2, 1, 4, 4]` on `wasm32`) proves alignment divisibility and non-shrinking padded bounds while rejecting 8 negative mutations. Crucially, `different_count_same_aggregate_size` proves that `[bool; 3]` and `[bool; 4]` both round to a `16`-byte native aggregate, demonstrating that checking only total struct size misses field-count errors that full field-vector checking catches; conversely, `same_layout_type_not_distinguished` shows that layout geometry alone cannot distinguish `[u8; 4]` from `[bool; 4]`.
5. **Matched four-law byte comparison across direct Lean, reflected Lean (`decide`), and `cvc5` $\rightarrow$ Alethe $\rightarrow$ strict `Carcara`:** On a padding-free two-byte finite memory model (`ByteLaws.lean`) encoding four guarded laws (`IntoLaw`, `WriteLaw`, `BoolLaw`, `ArrayLaw`), both direct Lean 4 (`264.1 ms` median) and kernel-reflected `decide` (`271.5 ms` median) verify all four universal laws and four concrete instances, and refute all five SAT counterexample mutants reified from `cvc5` models (`SolverWitnesses.lean`). Although `cvc5 1.4.2` proves the negation of all four laws `unsat` (`9.69–11.47 ms` median), strict `Carcara 1.1.0` (`carcara check --strict`) accepts only the `IntoLaw` byte-view admission proof (`valid`, exit `0`) and the isolated outside-byte frame conjunct of `WriteLaw`; the full `WriteLaw`, `BoolLaw`, and `ArrayLaw` Alethe certificates are rejected (`holey` under `--proof-granularity=theory-rewrite`, or `invalid` exit `1` under `--proof-granularity=dsl-rewrite-strict` due to missing `array-read-over-write` and `bool-double-not-elim` rules in `rare_rewrite`).

## Applicability

This report covers public byte-conversion and write APIs, cross-target layout probes, and formal certificate architectures across the following pinned subjects in `REPORT.json`:

- **`google/zerocopy` source revisions (`8fb35253fbc7` and `41f5b37afe70`):**
  - `google/zerocopy@8fb35253fbc703cb2cd0997f4efcda76cf9062b6` (crate version `0.8.63`). The examined public `TryFromBytes::try_read_from_bytes`, `FromBytes::ref_from_bytes`, `IntoBytes::write_to_prefix`, `IntoBytes::write_to_suffix`, `byteorder::U16<LE>`, `byteorder::U16<BE>`, and `util::validity::bool_encoding` (`zerocopy/src/impls.rs` blob `4df786fd2104854e1fa259a63c29cd8781f8a404`, lines 103–117) behaviors are shared with `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`0.8.59`), while `8fb35253fbc7` includes the expanded slice-DST layout definitions modeled by `Rust.Layout`.
  - Owned harness bundle SHA-256 `073ba3f230343ad94a0a90d352949acee6f269b965e81253e73d9169f486dfaa` and materialized `zerocopy` source archive SHA-256 `5097beee2b15db9c83171f75feacd857a4529392f926531792c4655f8ac1c48f`.
- **Multi-target Rust compilation and execution substrates (`aarch64-apple-darwin` vs. `wasm32-unknown-unknown`):**
  - `rust-lang/rust@b940084d7eb6a299eb4bfeb8e34901bc051e7ac4` (`rustc 1.99.0`, LLVM `23.1.1`, edition 2024, offline Cargo builds, default debug profile for API/packet harnesses and `-C opt-level=2` for the standalone 12-field `PacketRecord` aggregate probe).
  - **Host target (`aarch64-apple-darwin`):** Executed natively on Darwin `arm64`.
  - **Second target (`wasm32-unknown-unknown`):** Compiled against the official `rust-std-1.99.0-wasm32-unknown-unknown.tar.xz` component (`23,152,600` bytes, SHA-256 `b760b0c9b08a6843c05de0098bd6802e23178ff473c4715ae57c1d679125bf22`) into zero-import standalone WebAssembly modules (`WebAssembly.Module.imports(mod).length === 0`) and executed under Node `24.21.0` / V8 `13.6.233.17-node.53` (Darwin `arm64` binary SHA-256 `04c217abd4908a35a63cb3d329246323e4268e7e33bb9856d2667fb909b7b96e`).
- **Lean 4 and SMT/Alethe certificate-checking toolchains:**
  - `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, which includes the nested-inductive kernel validation fix) for `PacketModel.lean` receipt checking (`support/zerocopy-packet-api-target-certificates-and-reuse-costs/certificates/`) and the matched 4-law byte comparison (`support/zerocopy-packet-api-target-certificates-and-reuse-costs/matched-byte-laws/`).
  - `leanprover/lean4@68218e876d2a38b1985b8590fff244a83c321783` (`v4.31.0`, conditional observation on a pre-`v4.32.2` kernel) for the `Rust.Layout` / `LayoutBridge.lean` geometry instantiation (`support/zerocopy-packet-api-target-certificates-and-reuse-costs/shared-pr-layout/`).
  - `cvc5/cvc5@282d5e0c84baf49c780704c532f87ba66d8b513d` (`v1.4.2`) and `ufmg-smite/carcara@20bf49c5ce31089ac83118574c888669355aaae1` (`v1.1.0`) for Alethe SMT proof generation and strict external certificate checking.
  - Note on translation boundaries: Unlike single-target Charon/Aeneas extraction (which pins a single host target configuration per LLBC export), the experiments in this report evaluate target-parameterized Lean models (`PacketModel.lean`, `LayoutBridge.lean`, `ByteLaws.lean`) instantiated with concrete multi-target layout observations (`aarch64` vs. `wasm32`) and compared against SMT/Alethe external proof checking.

## Findings

### 1. Exhaustive Small-Domain Byte Validation and Write Preservation Across `aarch64` and `wasm32`

#### 1.1 Exhaustive `bool` (256 inputs) and `[bool; 2]` (65,536 inputs) domain enumeration

In both the native `aarch64-apple-darwin` harness (`support/zerocopy-byte-domain-and-write-controls/main.rs`) and the dual-target `aarch64` + `wasm32-unknown-unknown` harness (`support/zerocopy-two-target-byte-and-layout-controls/lib.rs`, `main.rs`, `check-wasm.mjs`), the test drivers pass ordinary initialized byte slices directly to `zerocopy`'s safe public conversion APIs and compare the outcomes against an independently authored expected predicate (`byte <= 1`):

- **`bool::try_read_from_bytes(&[b])` over all `b` in `0..=255` (`256` cases):**
  - Succeeds (`Ok(false)` for `0`, `Ok(true)` for `1`) on exactly `2` inputs and returns `Err(ValidityError)` on all `254` invalid byte encodings (`2..=255`).
  - Internally, `zerocopy/src/impls.rs:103–117` validates the candidate byte through a byte-level `Ptr` view using `util::validity::bool_encoding` (`byte < 2`) before constructing a Rust `bool`, avoiding immediate undefined behavior from materializing an invalid `bool` value.
- **`[bool; 2]::try_read_from_bytes(&[b0, b1])` over all `(b0, b1)` in `(0..=255) × (0..=255)` (`65,536` cases):**
  - Succeeds on `4` exact pairs—`[0, 0]`, `[0, 1]`, `[1, 0]`, and `[1, 1]`—preserving element order, and rejects all `65,532` pairs containing any byte $\ge 2$.
- **Out-of-domain wrapper challenges (`2` controls per target):**
  - In the FFI/Wasm export wrapper (`support/zerocopy-two-target-byte-and-layout-controls/lib.rs`), `u32` inputs outside the valid `0..256` or `0..65536` index domains (`256` for 1-byte and `65536` for 2-byte) return the distinguished sentinel status `99`, verifying that the test harness itself does not silently truncate out-of-range test indices.

Basis: **execution** + **source** (`zerocopy/src/impls.rs:103–117`, `support/zerocopy-byte-domain-and-write-controls/results.json`, `support/zerocopy-two-target-byte-and-layout-controls/results.json`).

#### 1.2 Eighteen width, ZST, endianness, alignment, and write-preservation controls

On both `aarch64-apple-darwin` and `wasm32-unknown-unknown`, 18 deterministic controls verify representation boundaries beyond scalar value validity:

1. **Width vs. element count (`4` controls):**
   - `bool::try_read_from_bytes(&[])` (0 bytes) and `bool::try_read_from_bytes(&[0, 0])` (2 bytes) both fail with `SizeError`.
   - `[(); 3]::try_read_from_bytes(&[])` (0 bytes for three ZST elements) succeeds (`Ok([(), (), ()])`), whereas `[(); 3]::try_read_from_bytes(&[0])` (1 byte) fails with `SizeError`.
2. **Byte-order decoding (`2` controls):**
   - `U16::<LE>::read_from_bytes(&[1, 0]).unwrap().get() == 1`.
   - `U16::<BE>::read_from_bytes(&[1, 0]).unwrap().get() == 256`.
3. **Runtime address alignment (`8` controls):**
   - Starting from an 8-byte-aligned `[u64; 2]` buffer viewed as bytes, calling `u16::ref_from_bytes(&bytes[offset..offset + 2])` for `offset` in `0..8` succeeds if and only if the runtime slice base address is divisible by `align_of::<u16>()` (`2`), i.e., even offsets succeed (`0, 2, 4, 6`) and odd offsets fail with `AlignmentError` (`1, 3, 5, 7`).
4. **Prefix/suffix write framing and failed-write preservation (`4` controls):**
   - Writing `0x01020304_u32.to_le_bytes()` into a 6-byte destination `[9, 9, 9, 9, 9, 9]` via `write_to_prefix` yields `[1, 2, 3, 4, 9, 9]`, preserving the unselected 2-byte suffix.
   - Writing the same 4-byte source into `[9, 9, 9, 9, 9, 9]` via `write_to_suffix` yields `[9, 9, 1, 2, 3, 4]`, preserving the unselected 2-byte prefix.
   - Attempting `write_to_prefix` of a 4-byte `[u8; 4]` into a 3-byte destination `[7, 8, 9]` returns `Err(SizeError)` and preserves all three destination bytes `[7, 8, 9]` unchanged.

Basis: **execution** + **derived** (`support/zerocopy-byte-domain-and-write-controls/main.rs`, `support/zerocopy-two-target-byte-and-layout-controls/lib.rs`).

---

### 2. Cross-Target Layout Divergence and Execution Costs (`aarch64` vs. `wasm32`)

#### 2.1 `#[repr(C)]` and `#[repr(C, packed)]` layout divergence between 64-bit `aarch64` and 32-bit `wasm32`

Using `size_of`, `align_of`, and `offset_of!` (which computes field offsets without forming unaligned references) on `rustc 1.99.0` (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`), the two targets produce distinct concrete layout facts whenever word-sized (`usize`) fields participate in an aggregate:

| Layout observation | `aarch64-apple-darwin` (64-bit) | `wasm32-unknown-unknown` (32-bit) |
| --- | ---: | ---: |
| `size_of::<usize>()` / `align_of::<usize>()` | `8` / `8` | `4` / `4` |
| `#[repr(C)] struct { a: u8, b: usize }` size | `16` | `8` |
| `#[repr(C)] struct { a: u8, b: usize }` alignment | `8` | `4` |
| `#[repr(C)] struct { a: u8, b: usize }` offset of `b` | `8` | `4` |
| `#[repr(C, packed)] struct { a: u8, b: usize }` size | `9` | `5` |
| `#[repr(C, packed)] struct { a: u8, b: usize }` alignment | `1` | `1` |
| `#[repr(C, packed)] struct { a: u8, b: usize }` offset of `b` | `1` | `1` |
| `#[repr(C)] PacketRecord { word: usize, flags: [bool; 4], header: [u8; 2] }` size / align | `16` / `8` | `12` / `4` |
| `PacketRecord` `(flags_offset, header_offset)` | `(8, 12)` | `(4, 8)` |
| `PacketRecord` primitive `(bool, [bool; 4], [u8; 2])` size/align | `(1/1, 4/1, 2/1)` | `(1/1, 4/1, 2/1)` |

Consequently, a layout certificate or offset proof specialized to `aarch64` word width (`8` bytes) is unsound for `wasm32` (`4` bytes). A portable verification architecture must keep word width and alignment parameterized in the shared mathematical model and instantiate them per target via explicit target receipts.

Basis: **execution** + **derived** (`support/zerocopy-two-target-byte-and-layout-controls/results.json`, `support/zerocopy-packet-api-target-certificates-and-reuse-costs/shared-pr-layout/aggregate-results.json`).

#### 2.2 Two-target build and execution timings for the 65,812-case byte-API suite

| Phase (`zerocopy-two-target-byte-and-layout-controls`) | Observed elapsed time | Artifact / output note |
| --- | ---: | --- |
| Native `aarch64-apple-darwin` Cargo build | `2.318 s` | Default debug profile, offline |
| Native process startup + all `65,812` controls | `0.062 s` | Exit `0` |
| Native in-process case loop (`256` + `65,536` + `18` + `2`) | `0.0075 s` | Direct Rust loop |
| `wasm32-unknown-unknown` Cargo build | `1.884 s` | Debug `.wasm` size `2,141,436` bytes; `0` imports |
| Node `24.21.0` process startup + Wasm compilation + controls | `0.104 s` | Exit `0` |
| JavaScript-to-Wasm export loop (`65,812` calls) | `0.0251 s` | V8 `13.6.233.17-node.53` |

Note: An initial probe on the `arm64` macOS host attempted to execute an `x86_64-apple-darwin` binary directly and failed with OS error `Bad CPU type in executable` (exit `1`, preserved in `support/zerocopy-two-target-byte-and-layout-controls/x86-execution-attempt.json` and `x86-execution-attempt.stderr`), motivating `wasm32-unknown-unknown` under Node/V8 as the second hermetic executable target.

Basis: **execution** (`support/zerocopy-two-target-byte-and-layout-controls/results.json`).

---

### 3. Composed Packet API (`decode_write`), Shared Lean 4 Model (`PacketModel.lean`), and Target Receipt Reuse Costs

#### 3.1 Composed packet API workload (`58,240` structured cases + `1,024` flag controls per target)

In `support/zerocopy-packet-api-target-certificates-and-reuse-costs/lib.rs`, `decode_write(source: &[u8], destination: &mut [u8])` composes three `zerocopy` operations on a 6-byte header (`4` flag bytes followed by a 2-byte little-endian payload length) and variable-length payload:
1. Checks `source.len() >= 6` (returning header error `-1` if shorter).
2. Validates `&source[0..4]` via `[bool; 4]::try_read_from_bytes` (returning flag validity error `-2` if any flag byte is $\ge 2$).
3. Decodes `&source[4..6]` via `U16::<LE>::read_from_bytes`, checks that `source[6..]` contains at least `len` payload bytes (returning truncated-payload error `-3` if not), and writes `&source[6..6 + len]` into `destination` via `[u8]::write_to_prefix` (returning destination-capacity error `-4` if `destination.len() < len`, or packing `(mask << 16) | len` on success).

On both `aarch64-apple-darwin` and `wasm32-unknown-unknown`, the test driver (`support/zerocopy-packet-api-target-certificates-and-reuse-costs/main.rs` and `check-wasm.mjs`) executes:
- **`58,240` structured cases:** `32` flag-byte seeds $\times$ `65` payload lengths (`0..=64`) $\times$ `7` destination capacities $\times$ `4` modes (valid input, invalid flag byte, truncated payload, truncated header).
- **`1,024` single-flag byte controls:** Each of the `4` flag positions tested across all `256` byte values (`0..=255`) with the remaining three flags and length set to `0`.
- **`2` out-of-domain adapter controls:** Returning sentinel `99`.
- **Full 128-byte backing-buffer frame check:** Verifies that successful writes update only `destination[0..len]` while preserving `destination[len..]` and all backing array bytes outside the passed destination slice, and that all four error paths (`-1, -2, -3, -4`) leave all `128` backing bytes untouched.

Basis: **source** + **execution** (`support/zerocopy-packet-api-target-certificates-and-reuse-costs/results.json`).

#### 3.2 Shared Lean 4 packet specification (`PacketModel.lean`) and target receipt reuse measurements

`support/zerocopy-packet-api-target-certificates-and-reuse-costs/PacketModel.lean` formalizes the pure list-level packet laws in Lean 4 (`v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`):

```lean
import Std
namespace Packet
abbrev Byte := Fin 256

def writePayload (payload destination : List Byte) : Option (List Byte) :=
  if payload.length ≤ destination.length then some (payload ++ destination.drop payload.length) else none

theorem write_success (payload destination : List Byte) (capacity : payload.length ≤ destination.length) :
    writePayload payload destination = some (payload ++ destination.drop payload.length) := by
  simp [writePayload, capacity]

theorem write_short (payload destination : List Byte) (capacity : ¬ payload.length ≤ destination.length) :
    writePayload payload destination = none := by simp [writePayload, capacity]

theorem write_frame (payload destination : List Byte) :
    (payload ++ destination.drop payload.length).drop payload.length = destination.drop payload.length := by simp

def validFlags (flags : List Byte) : Bool := flags.length == 4 && flags.all (fun b => b.val < 2)
def process (flags payload destination : List Byte) (available : Bool) : Option (List Byte) :=
  if validFlags flags && available then writePayload payload destination else none

theorem invalid_flags_no_write (flags payload destination : List Byte) (invalid : validFlags flags = false) :
    process flags payload destination available = none := by simp [process, invalid]

theorem missing_payload_no_write (flags payload destination : List Byte) :
    process flags payload destination false = none := by simp [process]

theorem pipeline_success (flags payload destination : List Byte) (valid : validFlags flags = true)
    (capacity : payload.length ≤ destination.length) :
    process flags payload destination true = some (payload ++ destination.drop payload.length) := by
  simp [process, valid, writePayload, capacity]

def expectedLayout (wordBytes : Nat) : List Nat := [wordBytes, 4, 1, 2, 1]
end Packet
```

All six theorems in `PacketModel.lean` check with `propext` as their sole axiom (`support/zerocopy-packet-api-target-certificates-and-reuse-costs/certificates/results.json`). Each per-target receipt (`aarch64_apple_darwin_1.lean`..`3.lean` and `wasm32_unknown_unknown_1.lean`..`3.lean`) imports the compiled `PacketModel.olean`, checks `layout_agrees` (`[8, 4, 1, 2, 1] = expectedLayout 8` on `aarch64`; `[4, 4, 1, 2, 1] = expectedLayout 4` on `wasm32`), proves `bounded_machine_length` (`∀ n ≤ 64, 6 + n < 2 ^ (wordBytes * 8)`), and instantiates `pipeline_success` and `write_frame`:

| Artifact / Phase (`support/zerocopy-packet-api-target-certificates-and-reuse-costs/certificates/results.json`) | Size (bytes) | Observed timing | Kernel / status outcome |
| --- | ---: | ---: | --- |
| Shared `PacketModel.lean` $\rightarrow$ `PacketModel.olean` | `1,440` src / `64,008` `.olean` | `1.200 s` | Exit `0`; axioms: `propext` |
| `aarch64_apple_darwin_{1,2,3}.lean` receipt check (reusing `.olean`) | `972` src / `46,096` `.olean` | `364 ms`, `367 ms`, `351 ms` | Exit `0`; axioms: `propext`, `Quot.sound` |
| `wasm32_unknown_unknown_{1,2,3}.lean` receipt check (reusing `.olean`) | `962` src / `44,904` `.olean` | `335 ms`, `332 ms`, `337 ms` | Exit `0`; axioms: `propext`, `Quot.sound` |
| Receipt template generation (`measure_certificates.py`) | `962–972` src | `0.11–0.16 ms` | Python template instantiation |
| Negative control: `wrong_target.lean` (`[8, 4, 1, 2, 1]` vs. `expectedLayout 4`) | `460` src | Rejected | Exit `1` (kernel `rfl` / `decide` type mismatch) |
| Negative control: `wrong_type.lean` (`[8, 8, 1, 2, 1]` vs. `expectedLayout 8`) | `460` src | Rejected | Exit `1` (kernel `rfl` / `decide` type mismatch) |

Basis: **source** + **execution** + **derived** (`support/zerocopy-packet-api-target-certificates-and-reuse-costs/certificates/results.json`).

#### 3.3 Shared `Rust.Layout` geometry instantiation and 12-field aggregate controls (`LayoutBridge.lean`)

To connect observed target layouts to `Rust.Layout`'s general alignment and rounding theorems (`reprCSliceDstSize_aligned` and `roundUpToAlign_ge`) rather than merely comparing literal lists with `rfl`, `support/zerocopy-packet-api-target-certificates-and-reuse-costs/shared-pr-layout/LayoutBridge.lean` imports `Rust.Layout` and defines:

```lean
import Rust.Layout

namespace LayoutBridge

inductive ABI where | native64 | wasm32 deriving DecidableEq, Repr
def wordBytes : ABI → Nat | .native64 => 8 | .wasm32 => 4
theorem wordAlignment (abi : ABI) : Rust.IsAlignment (wordBytes abi) := by
  cases abi
  · exact ⟨by decide, 3, by decide⟩
  · exact ⟨by decide, 2, by decide⟩

def boolLayout : Rust.Layout := ⟨1, 1, Rust.alignment_one, by decide⟩
def byteSequence : Rust.SliceDstLayout := ⟨0, boolLayout.size, 1, Rust.alignment_one⟩
def flagsSize (count : Nat) : Nat := Rust.reprCSliceDstSize byteSequence count
def headerSize : Nat := Rust.reprCSliceDstSize byteSequence 2

def recordInfo (abi : ABI) : Rust.SliceDstLayout :=
  ⟨wordBytes abi + flagsSize 4, headerSize, wordBytes abi, wordAlignment abi⟩
def recordSize (abi : ABI) : Nat := Rust.reprCSliceDstSize (recordInfo abi) 1
def recordLayout (abi : ABI) : Rust.Layout where
  size := recordSize abi
  align := wordBytes abi
  isAlignment := wordAlignment abi
  sizeAligned := Rust.reprCSliceDstSize_aligned (recordInfo abi) 1

theorem record_aligned (abi : ABI) : wordBytes abi ∣ recordSize abi :=
  Rust.reprCSliceDstSize_aligned (recordInfo abi) 1

theorem record_not_smaller (abi : ABI) :
    wordBytes abi + flagsSize 4 + headerSize ≤ recordSize abi := by
  have h := Rust.roundUpToAlign_ge
    ((recordInfo abi).trailingOffset + 1 * (recordInfo abi).elementSize)
    (recordInfo abi).align (wordAlignment abi).1
  simpa [recordSize, Rust.reprCSliceDstSize, recordInfo] using h
```

`LayoutBridge.lean` proves both 5-field (`admitted_geometry`) and 12-field (`admitted_aggregate_geometry`) admission theorems, accepting all `4` valid `aarch64` and `wasm32` observation vectors and rejecting `8` negative controls (`wrong-abi`, `wrong-array-length`, `wrong-header-type`, `missing-field`, `extra-field`, `aggregate-wrong-abi`, `aggregate-wrong-offset`, `aggregate-wrong-type`). Two theorems in `LayoutBridge.lean` capture key verification boundaries:
- **Padding masks field-length errors unless per-field vectors are checked (`different_count_same_aggregate_size`):** On 64-bit `native64`, a record with 3 flag bytes (`8 + 3 + 2 = 13`, rounded up to alignment `8` $\rightarrow 16$) has the exact same 16-byte total size as a record with 4 flag bytes (`8 + 4 + 2 = 14`, rounded up to alignment `8` $\rightarrow 16`). Checking only total aggregate size misses the `[bool; 3]` vs. `[bool; 4]` mismatch, whereas `admit .native64 3 nativeObserved = false` (`wrong_array_length`) rejects it.
- **Layout geometry cannot distinguish same-layout types with different validity invariants (`same_layout_type_not_distinguished`):** `[u8; 4]` and `[bool; 4]` have identical size (`4`) and alignment (`1`), so `[8, 4, 1, 2, 1]` passes `admit .native64 4` for both; bit-validity predicates must be bound separately from layout geometry.

Basis: **source** + **execution** + **derived** (`support/zerocopy-packet-api-target-certificates-and-reuse-costs/shared-pr-layout/LayoutBridge.lean`, `support/zerocopy-packet-api-target-certificates-and-reuse-costs/shared-pr-layout/results.json`, `support/zerocopy-packet-api-target-certificates-and-reuse-costs/shared-pr-layout/parent-replay.json`).

---

### 4. Matched Four-Law Byte Certificate Comparison: Direct Lean 4, Reflected Lean (`decide`), and `cvc5` $\rightarrow$ Alethe $\rightarrow$ Strict `Carcara`

#### 4.1 Unified two-byte finite memory model (`ByteLaws.lean`)

To compare Lean kernel proof checking against SMT/Alethe proof export and strict `Carcara` verification on identical semantic obligations, `support/zerocopy-packet-api-target-certificates-and-reuse-costs/matched-byte-laws/ByteLaws.lean` defines a padding-free two-byte memory state `Memory` with explicit per-byte initialization (`init0`, `init1`), read permission (`read0`, `read1`), and write permission (`write0`, `write1`) flags, together with four guarded laws:

```lean
abbrev Byte := Fin 256
abbrev Addr := Bool

structure Memory where
  b0 : Byte
  b1 : Byte
  init0 : Bool
  init1 : Bool
  read0 : Bool
  read1 : Bool
  write0 : Bool
  write1 : Bool
  deriving DecidableEq, Repr

def byteAt (s : Memory) (a : Addr) : Byte := if a then s.b1 else s.b0
def initialized (s : Memory) (a : Addr) : Bool := if a then s.init1 else s.init0
def readable (s : Memory) (a : Addr) : Bool := if a then s.read1 else s.read0
def writable (s : Memory) (a : Addr) : Bool := if a then s.write1 else s.write0
def ready (s : Memory) (a : Addr) : Prop := initialized s a = true ∧ readable s a = true
def allReady (s : Memory) : Prop := ready s false ∧ ready s true
def stable (s t : Memory) (a : Addr) : Prop := byteAt s a = byteAt t a
def boolValid (b : Byte) : Prop := b.val < 2
def bothValid (s : Memory) : Prop := boolValid s.b0 ∧ boolValid s.b1

def observe (s : Memory) : Option (Byte × Byte) :=
  if allReady s then some (s.b0, s.b1) else none

def store (s : Memory) (a : Addr) (v : Byte) : Memory :=
  if a then { s with b1 := v, init1 := true }
  else { s with b0 := v, init0 := true }

def writeByte (s : Memory) (a : Addr) (v : Byte) : Option Memory :=
  if writable s a then some (store s a v) else none

def IntoLaw (s : Memory) : Prop :=
  allReady s → observe s = some (s.b0, s.b1)

def WriteLaw (s : Memory) (a frame : Addr) (v : Byte) : Prop :=
  writable s a = true → a ≠ frame →
    writeByte s a v = some (store s a v) ∧
    byteAt (store s a v) a = v ∧ initialized (store s a v) a = true ∧
    byteAt (store s a v) frame = byteAt s frame ∧
    initialized (store s a v) frame = initialized s frame

def BoolLaw (s t : Memory) (a : Addr) : Prop :=
  ready s a → ready t a → stable s t a → boolValid (byteAt s a) →
    ready t a ∧ boolValid (byteAt t a)

def ArrayLaw (s t : Memory) : Prop :=
  allReady s → allReady t → stable s t false → stable s t true →
    bothValid s → allReady t ∧ bothValid t
```

#### 4.2 Comparative certificate verdicts and the `cvc5` $\rightarrow$ `Carcara` export boundary

| Guarded law (`ByteLaws.lean` / SMT-LIB2) | Direct Lean 4 (`v4.34.1`) | Reflected Lean 4 (`check` / `decide`) | `cvc5 1.4.2` (`--produce-proofs`) | `Carcara 1.1.0` (`theory-rewrite` Alethe) | `Carcara 1.1.0` (`dsl-rewrite-strict` / normal form) |
| --- | --- | --- | --- | --- | --- |
| 1. `IntoLaw`: `IntoBytes`-style byte-view admission | Checked (`into_direct`, `propext`) | Checked (`all_reflected`, `check_sound`) | `unsat` (`9.69 ms` median, `834` B proof) | `valid`, exit `0` | `valid`, exit `0` (`3.32 ms` median) |
| 2. `WriteLaw`: byte write, written value/init, and disjoint frame preservation | Checked (`write_direct`, `propext`) | Checked (`all_reflected`, `check_sound`) | `unsat` (`10.49 ms` median, `4,495` B proof) | `holey`, exit `0` (denied under strict policy) | `invalid`, exit `1` (`array-read-over-write` missing in `rare_rewrite`; outside-byte frame conjunct alone checks `valid`) |
| 3. `BoolLaw`: scalar `bool` validation-to-use under stability | Checked (`bool_direct`, `propext`) | Checked (`all_reflected`, `check_sound`) | `unsat` (`10.85 ms` median, `10,946` B proof) | `holey`, exit `0` (denied under strict policy) | `invalid`, exit `1` (`bool-double-not-elim` missing in `rare_rewrite`, `3.44 ms` rejection) |
| 4. `ArrayLaw`: `[bool; 2]` validation-to-use under stability | Checked (`array_direct`, `propext`) | Checked (`all_reflected`, `check_sound`) | `unsat` (`11.47 ms` median, `11,275` B proof) | `holey`, exit `0` (denied under strict policy) | `invalid`, exit `1` (`bool-double-not-elim` missing in `rare_rewrite`, `3.60 ms` rejection) |

Across three process-inclusive timing samples (`support/zerocopy-packet-api-target-certificates-and-reuse-costs/matched-byte-laws/measurements.json`), checking all four universal plus four concrete propositions takes a median of `264.1 ms` in direct Lean (`895` source bytes) and `271.5 ms` in reflected Lean (`1,134` source bytes). In the SMT pipeline, `cvc5 1.4.2` proves all four negated formulas `unsat`, but strict `Carcara 1.1.0` (requiring exit `0` and exact `valid\n` output, rejecting `holey` proofs) only accepts `IntoLaw` and the decomposed outside-byte frame conjunct of `WriteLaw` because `cvc5`'s Alethe export emits coarse `hole` steps under `theory-rewrite` and references `array-read-over-write`, `bool-double-not-elim`, and `eq-symm` rules not present in `Carcara`'s built-in `rare_rewrite` database under `dsl-rewrite-strict`.

Basis: **source** + **execution** (`support/zerocopy-packet-api-target-certificates-and-reuse-costs/matched-byte-laws/verdict-matrix.json`, `support/zerocopy-packet-api-target-certificates-and-reuse-costs/matched-byte-laws/smt-results.json`, `support/zerocopy-packet-api-target-certificates-and-reuse-costs/matched-byte-laws/dsl-smt-results.json`, `support/zerocopy-packet-api-target-certificates-and-reuse-costs/matched-byte-laws/measurements.json`).

#### 4.3 Negative-mutant discrimination and SAT-witness reification (`SolverWitnesses.lean`)

Six deliberately weakened or narrowed variants in `ByteLaws.lean` and `SolverWitnesses.lean` verify that the specifications do not vacuously accept broken memory or validity preconditions:

| Mutant / Variant | `cvc5 1.4.2` outcome | Lean 4 (`v4.34.1`) refutation / domain theorem |
| --- | --- | --- |
| 1. `missing_init` (`init0 = false` in `IntoLaw`) | `sat` (countermodel extracted) | Refuted by `missing_init_bad` (`ByteLaws.lean`) and reified witness in `SolverWitnesses.lean` |
| 2. `alias_frame` (dropped `a ≠ frame` disjointness in `WriteLaw`) | `sat` (`a = frame` overwrites framed byte) | Refuted by `aliased_frame_bad` (`ByteLaws.lean`) and reified witness in `SolverWitnesses.lean` |
| 3. `bool_widened` (widened Boolean guard `< 3` accepting byte `2`) | `sat` (`source[0] = 2`, `current[0] = 2`) | Refuted by `bool_two_bad` / `original_domain_exposes` (`ByteLaws.lean`) and `SolverWitnesses.lean` |
| 4. `bool_narrowed_domain` (input domain restricted to `b < 2` while testing guard `< 3`) | `unsat` locally on narrowed domain (`holey` Alethe export); rejected against full-domain assumption `< source[0] 2` | `narrow_domain_hides` proves `guardClaim 2 3 b` holds vacuously when `b < 2` is assumed at entry, whereas `original_domain_exposes` refutes `guardClaim 256 3 2` on the full `u8` caller domain |
| 5. `array_index_omission` (validating only index `0` of `[bool; 2]`) | `sat` (`b0 = 0`, `b1 = 2`) | Refuted by `missing_array_index_bad` (`ByteLaws.lean`) and reified witness in `SolverWitnesses.lean` |
| 6. `missing_stability` (dropping `stable s t a` between validation `s` and use `t`) | `sat` (`s.b0 = 0` at check, mutated to `t.b0 = 2` at use) | Refuted by `missing_stability_bad` (`ByteLaws.lean`) and reified witness in `SolverWitnesses.lean` |

Basis: **source** + **execution** (`support/zerocopy-packet-api-target-certificates-and-reuse-costs/matched-byte-laws/countermodels.json`, `support/zerocopy-packet-api-target-certificates-and-reuse-costs/matched-byte-laws/SolverWitnesses.lean`).

## Boundaries

- **Finite API tests are not formal proofs of `rustc` or internal `unsafe` pointer authority (`not established`):** Exhaustively testing all `256` `bool` encodings and `65,536` `[bool; 2]` encodings through safe public slices confirms input-output conformance on `aarch64-apple-darwin` and `wasm32-unknown-unknown`, but does not formally verify `rustc 1.99.0`, LLVM `23.1.1`, Node/V8, uninitialized padding/poison bytes, concurrent interior mutation, or arbitrary caller pointer provenance.
- **Manual source-to-model bridge in `PacketModel.lean`, `LayoutBridge.lean`, and `ByteLaws.lean` (`not examined` / manual trust boundary):** The Lean models (`PacketModel.lean`, `LayoutBridge.lean`, `ByteLaws.lean`) do not parse Rust source or extract MIR/LLBC automatically. The correspondence between `decode_write` / `PacketRecord` and the Lean list/layout/memory definitions—as well as the insertion of observed stdout layout vectors (`[8, 4, 1, 2, 1]` and `[4, 4, 1, 2, 1]`) into target receipt templates—remains an explicit trusted bridge. Furthermore, a self-reported source-hash equation (`source_hash = source_hash`) inside a producer-generated receipt does not authenticate the consumer's target or source revision unless the consumer supplies the expected specification independently.
- **Layout agreement does not establish type validity or access permission (`known not to apply`):** As proved by `LayoutBridge.same_layout_type_not_distinguished`, `[u8; 4]` and `[bool; 4]` share identical size and alignment vectors. Layout certificates must always be paired with bit-validity and aliasing/authority obligations.
- **Incomplete Alethe/Carcara coverage on array-write and Boolean-negation rewrites (`unsupported` in current export configuration):** Under `cvc5 1.4.2` and `Carcara 1.1.0` (`--strict`), `WriteLaw`, `BoolLaw`, and `ArrayLaw` fail strict Alethe check due to untranslated `theory-rewrite` holes or missing `array-read-over-write` / `bool-double-not-elim` rules in `rare_rewrite`.
- **Lean kernel version difference (`v4.31.0` vs. `v4.34.1`):** The `LayoutBridge.lean` checks under `support/zerocopy-packet-api-target-certificates-and-reuse-costs/shared-pr-layout/` used `leanprover/lean4@68218e876d2a38b1985b8590fff244a83c321783` (`v4.31.0`), which predates the `v4.32.2` nested-inductive parameter check fix, whereas `PacketModel.lean` and `ByteLaws.lean` were checked under `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`).

## Evidence

All experimental evidence in this package was acquired and revalidated on `2026-10-14`:

- **Single-target exhaustive byte-domain and write controls (`support/zerocopy-byte-domain-and-write-controls/`):**
  - `support/zerocopy-byte-domain-and-write-controls/main.rs`, `Cargo.lock`, `run_probe.py`, `results.json`, `cargo-run.stdout.txt`, `cargo-run.stderr.txt`, `rust-version.stdout.txt`, and `rust-version.stderr.txt`.
- **Two-target (`aarch64-apple-darwin` and `wasm32-unknown-unknown`) byte and layout controls (`support/zerocopy-two-target-byte-and-layout-controls/`):**
  - `support/zerocopy-two-target-byte-and-layout-controls/lib.rs`, `main.rs`, `check-wasm.mjs`, `run_cross.py`, `results.json`, `native-build.stdout`, `native-build.stderr`, `native-check.stdout`, `native-check.stderr`, `wasm-build.stdout`, `wasm-build.stderr`, `wasm-check.stdout`, `wasm-check.stderr`, `rust-version.stdout`, `node-version.stdout`, and `x86-execution-attempt.json`.
- **Composed packet API (`decode_write`), `PacketModel.lean`, and target receipt reuse measurements (`support/zerocopy-packet-api-target-certificates-and-reuse-costs/`):**
  - `support/zerocopy-packet-api-target-certificates-and-reuse-costs/lib.rs`, `main.rs`, `check-wasm.mjs`, `run_cross.py`, `PacketModel.lean`, `measure_certificates.py`, `results.json`, `artifact-identities.json`, `certificates/results.json`, `certificates/aarch64_apple_darwin_1.lean`, `certificates/wasm32_unknown_unknown_1.lean`, `certificates/wrong_target.lean`, `certificates/wrong_type.lean`, and `initial-extern-fn-compile-rejection/results.json`.
- **Shared `Rust.Layout` geometry instantiation and 12-field `PacketRecord` aggregate controls (`support/zerocopy-packet-api-target-certificates-and-reuse-costs/shared-pr-layout/`):**
  - `support/zerocopy-packet-api-target-certificates-and-reuse-costs/shared-pr-layout/LayoutBridge.lean`, `results.json`, `aggregate-results.json`, `bridge-result.json`, `parent-replay.json`, `aggregate-native-positive.stdout`, `aggregate-wasm-positive.stdout`, `wrong-array-length.stdout`, and `aggregate-wrong-offset.stdout`.
- **Matched four-law byte comparison across Lean 4 (`v4.34.1`), `cvc5 1.4.2`, and `Carcara 1.1.0` (`support/zerocopy-packet-api-target-certificates-and-reuse-costs/matched-byte-laws/`):**
  - `support/zerocopy-packet-api-target-certificates-and-reuse-costs/matched-byte-laws/ByteLaws.lean`, `SolverWitnesses.lean`, `run_smt.py`, `verify_and_measure.py`, `replay_case.py`, `verdict-matrix.json`, `predicate-map.json`, `countermodels.json`, `measurements.json`, `smt-results.json`, `dsl-smt-results.json`, `initial-smt-results.json`, `identities.json`, `parent-replay.json`, and `APPENDIX.md`.

## Revalidation

1. **Single-target byte-domain probe:** Run `python3 -B support/zerocopy-byte-domain-and-write-controls/run_probe.py <path-to-zerocopy-repo>` with `rustc 1.99.0` (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`) and verify exit `0` and matching assertions in `support/zerocopy-byte-domain-and-write-controls/results.json`.
2. **Two-target (`aarch64` + `wasm32`) byte and layout controls:** Extract the official `rust-std-1.99.0-wasm32-unknown-unknown` component (`b760b0c9b08a6843c05de0098bd6802e23178ff473c4715ae57c1d679125bf22`) and run `python3 support/zerocopy-two-target-byte-and-layout-controls/run_cross.py <path-to-zerocopy-repo> <path-to-wasm32-std>`, confirming all `65,812` cases pass on both targets, zero Wasm module imports, and matching `arm64` vs. `wasm32` layout tables.
3. **Packet API cross-target suite and Lean 4 receipt reuse:** Run `python3 support/zerocopy-packet-api-target-certificates-and-reuse-costs/run_cross.py` (`58,240` structured cases + `1,024` flag controls on `aarch64` and `wasm32`) and `python3 support/zerocopy-packet-api-target-certificates-and-reuse-costs/measure_certificates.py` with Lean `4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), verifying that all `6` positive target receipts pass (`propext`, `Quot.sound`) and both negative controls (`wrong_target.lean`, `wrong_type.lean`) fail with exit `1`.
4. **Shared `Rust.Layout` bridge and matched 4-law SMT/Carcara replay:** Compile `Rust/Layout.lean` and `support/zerocopy-packet-api-target-certificates-and-reuse-costs/shared-pr-layout/LayoutBridge.lean` to verify the `4` positive and `8` negative layout controls (`support/zerocopy-packet-api-target-certificates-and-reuse-costs/shared-pr-layout/parent-replay.json`). Run `python3 -B support/zerocopy-packet-api-target-certificates-and-reuse-costs/matched-byte-laws/replay_case.py --lean <lean-4.34.1> --cvc5 <cvc5-1.4.2> --carcara <carcara-1.1.0> --out <scratch-dir>` to reproduce the 4 direct/reflected Lean proofs, the 5 SAT countermodel reifications in `SolverWitnesses.lean`, and the `cvc5`/`Carcara` verdict matrix in `support/zerocopy-packet-api-target-certificates-and-reuse-costs/matched-byte-laws/verdict-matrix.json`.
