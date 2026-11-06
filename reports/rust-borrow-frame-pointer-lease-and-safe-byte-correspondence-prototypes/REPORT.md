# Rust Borrow-Frame, Pointer-Lease, and Safe-Byte Correspondence Prototypes

## Summary

Across seven bounded Lean and Rust verification prototypes and contract analyses, mathematical value equality, byte-level representation decoding, initialized storage, and runtime access authority require distinct certificate propositions:

1. **Two-field and length-two slice borrow, update, and frame certificates:** A kernel-checked Lean certificate (`support/experiments/BorrowModel.lean`, `support/experiments/BorrowCertificate.lean`) updates a selected byte field, preserves the sibling field, and restores modeled root authority (`Authority.root → splitFields → root`). A length-two slice model (`Slice2 : Fin 2 → Byte`) preserves every distinct cell (`j ≠ i`) and returns `none` outside bounds (`index ≥ 2`). Safe native Rust controls (`support/experiments/borrow_native.rs`) pass all 65,536 two-byte field states and 196,608 two-byte slice/index cases at fixed delta `3` (FNV-64 digest `f2ed1041187b6325`). A negative control (`support/experiments/BorrowWrongField.lean`) that writes the right field while claiming the left-field endpoint fails kernel `decide` with exit `1`.
2. **Finite pointer lease and reconstruction control:** A four-cell lease protocol (`PointerLease.lean`, checked under both Lean 4.31.0 and Lean 4.34.1) models allocation identity, allocation-death time, per-cell owner tickets, and a live capability registry covering half-open ranges, expiry, alignment, initialization, and validity. Positive theorems verify construction, disjoint splitting (`[0, k)` and `[k, 4)` for `k : Fin 5`), single-cell projection, byte framing, consumption, and four-byte-aligned word reconstruction. Negative controls reject stale parent tickets, duplicate reconstruction after consumption, lifetime extension past allocation death, expired leases, overlapping alias claims, and unaligned word casts. Removing the allocation-death premise (`weakened_gate_accepts_extension`) causes an invalid lifetime extension (expiry `20` used at time `11` after allocation death at time `10`) to pass, demonstrating that numerical range geometry alone omits temporal liveness. Safe and negative Rust compiler controls (`pointer_safe.rs`, `packed_reference_rejected.rs`, `lifetime_rejected.rs`, `alias_rejected.rs`) corroborate the separation between raw addresses (`addr_of!` + `read_unaligned`) and aligned, lifetime-bounded, non-aliasing reference creation (`E0793`, `E0499`).
3. **Three checked correspondence routes for a captured safe-byte fragment:** Over a captured unary `u8` wrapping-arithmetic fixture (`support/experiments/subject.rs`, computing `scale(x + 3) + 7` with `scale(y) = y * 5` modulo 256), three independent certificate routes in `support/experiments/ArithmeticModel.lean` prove the same consumer-selected `Claim expectedSourceHash actualSourceHash capturedSource proposedIR` (`evalIR proposedIR x = evalSource capturedSource x` for all `x : Fin 256`, depending only on `propext`): (a) **Instrumented** (`support/experiments/Arithmetic-instrumented.lean`, checking all 256 native `input/a/b/output` trace rows via `checkInstrumented` and `instrumented_sound`), (b) **Post-hoc** (`support/experiments/Arithmetic-posthoc.lean`, checking structural equality `decode(proposedIR) = capturedSource` via `checkPosthoc`, `decode_eval`, and `posthoc_sound`), and (c) **Constructive** (`support/experiments/Arithmetic-constructive.lean`, checking `proposedIR = construct(capturedSource)` against inductive `construct_eval`).
4. **Complete safe API over an unsafe Boolean representation operation:** For `checked_bool(u8) -> Option<bool>` (`support/api.rs`), which guards `byte < 2` before calling `core::mem::transmute::<u8, bool>(byte)`, the state-machine certificate (`support/ApiCertificate.lean`) retains the full `Fin 256` caller domain, models invalid Boolean representations via an explicit `bad` outcome, and proves `all_inputs` and `no_bad` across `entry`, `pending` cast, and terminal states. Negative logical witnesses show that widening the guard to `byte < 3` (`wider_guard_bad`) or omitting the guard (`unguarded_bad`) reaches `bad` on input `2`, while restricting the model carrier to `Fin 2` (`narrowed_model_hides`) hides the bug completely.
5. **Scalars, values, storage, and access side conditions:** Normative Rust Reference and `core` library contracts, Charon MIR cast translation (`translate_bodies.rs`), Aeneas `BitVec`-backed scalar models (`Scalar/Core.lean`, `Ops/Div.lean`, `Scalar/Casts.lean`), and pure mathematical memory/storage models separate three bridge stages: (1) physical storage state and access authority to permitted abstract bytes, (2) abstract bytes and type validity to raw logical carriers, and (3) raw carriers to consumer ghost domains. The four MIR pointer-cast kinds (`PtrToPtr`, `FnPtrToPtr`, `PointerExposeProvenance`, `PointerWithExposedProvenance`) remain distinguishable in Charon via their retained `(source_type, target_type)` pairs despite sharing a `CastKind::RawPtr` constructor.
6. **Pinning, async progress, and foreign/hardware resource contracts:** `core::pin` drop guarantees protect in-place validity until `Drop::drop` returns or panics, not merely numerical addresses. Pending futures retain resources across suspensions, and cancellation drops the future without running its success continuation (`async_drop_probe.rs`). Recent formal frameworks—LART (`arXiv:2610.09198v1`) and LAGC (`arXiv:2610.06003v1`)—establish conditional responsiveness or scheduler fairness under explicit runtime premises, while a derived transition-system counterexample (`s → s` and `s → unit` mapped to strongly normalizing `m → unit`) shows that finite-result agreement does not reflect divergence or liveness when erased steps stutter infinitely. FFI callbacks, `read_volatile`/`write_volatile`, inline assembly, and DMA require explicit temporal ABI, ownership, MMIO-vs-RAM, and cache-coherence contracts.
7. **Pure mathematical layout/storage models and their Lean version boundary:** Nine pure mathematical Lean modules (`Rust.Layout`, `Rust.Memory`, `Rust.Bytes`, `Rust.Storage`, `Rust.Arithmetic`, `Rust`, and three test suites auditing 252 library declarations against `propext`, `Classical.choice`, and `Quot.sound`) pass under Lean 4.31.0 (`support/lean431/`), while `BoundaryProbe.lean` and `support/layout_probe.rs` demonstrate that unindexed numerical layouts (`size = 1, align = 1` vs native `u64` `size = 8, align = 8`), empty-footprint `FitsInAllocation` witnesses at arbitrary addresses, vacuous `noInputs` decoders, and permissive `allInputs` decoders require independent physical binding. Under Lean 4.34.1 (`support/lean434/`), unmodified `Rust/Storage.lean:86` (`BitDecoder.run_map`) fails elaboration because `split` leaves an `if` term that is no longer definitionally equal to `Option.map` under `rfl`.

## Applicability

The prototypes and source analyses in this package are bound to the exact subject revisions and artifact hashes recorded in `REPORT.json` and `support/artifact-index.json`:

- **Lean checkers:**
  - Lean `4.31.0` at `leanprover/lean4@68218e876d2a38b1985b8590fff244a83c321783` (`lean` executable SHA-256 `1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554`; shared library SHA-256 `a695a9aa68481c42b99619e0103537e6b433c6fa7021927b184e19a686d03989`; `Init.olean` SHA-256 `9e6e77b58b46742b93b7de481229698d853595479a6e154e9c6fcfdf63b485c8`; release archive `lean-4.31.0-darwin_aarch64.tar.zst` SHA-256 `264105500c8abdf37b68ffe03390a783ed259807807222698da8dd92d6ce0a27`).
  - Lean `4.34.1` at `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (shared library SHA-256 `6588b7e38450ea749006dcd90bbaea9393a5ca1b64727a2e7138f3c9427c2b50`; `Init.olean` SHA-256 `e350f457fb746028d5761304fd7df55a83b46ea56cdd7702fdee32600b57db22`).
  - Lean nested-inductive kernel validation fix at `leanprover/lean4@a39eab69e1eee9ad38f4efe507907b1026a77808` (PR `14577`).
- **Rust compilers and normative/library sources:**
  - Rust `1.99.0` at `rust-lang/rust@b940084d7eb6a299eb4bfeb8e34901bc051e7ac4` (`rustc` executable SHA-256 `dd6f58440b3418aa9157ae3f05d71eecff741ca41bc4eec120e7e8f2d933b9a0`, `aarch64-apple-darwin`).
  - Rust `1.101.0-nightly` control compiler at `rust-lang/rust@1d81eb4ad9cd207e3e638bd32b17ec4fce8412a6` (`rustc` SHA-256 `eb3147b0fd9629eba4886d6c4072d0ba21ae493b43b776871c1645f0e977916e`, `aarch64-apple-darwin`).
  - Rust standard-library contract snapshot at `rust-lang/rust@d8ef4f3fe7031514cbd7d056b7b058814987ecec` (`core::pin`, `core::future::Future`, `core::ptr::read_volatile`).
  - Rust Reference at `rust-lang/reference@2dafab96d919d6ab2884488e970bf95610ff83eb`.
- **Charon, Aeneas, and async verification preprints:**
  - Charon at `AeneasVerif/charon@cf02e3f228f97ee7be3a415be56989053063326d`.
  - Aeneas at `AeneasVerif/aeneas@ca282ec2312a96f6a985a4d23a663690816d3f3e`.
  - *Modular Responsiveness Verification of Rust Async Runtimes*, `arXiv:2610.09198v1` (submitted 2026-10-06, PDF SHA-256 `d22755eaee7f4a07725adda27711ea1e1b1f275760b9f46de060e69df2d32c30`).
  - *A Complete Formal Semantics for Rust Source Code*, `arXiv:2610.06003v1` (submitted 2026-10-05, PDF SHA-256 `1f8421bb193e351a0a10443478a2dde25c3c1b34493f7540a54a0c1977c3d16d`).

All native executions were recorded on `aarch64-apple-darwin` (Darwin 27 arm64). Each finite prototype scopes its claims strictly to the modeled carrier (`Byte = Fin 256`, two-field `Pair`, `Slice2 : Fin 2 → Byte`, four-cell `PointerLease`, unary wrapping arithmetic, or by-value `u8 → Option<bool>`). The source-to-model capture bridges in these prototypes are explicit trusted frontiers, not verified Rust parsers or full compiler correctness proofs.

## Findings

### Two-Field and Length-Two Slice Borrow, Update, and Frame Certificates

#### Replayable field plan preserves endpoint and authority

Basis: **source** + **execution**.

`support/experiments/BorrowModel.lean` (SHA-256 `ef9bd759fbd48e59dc05202347e67ea8a37fbf7a0b8516f5324225df9d400fe3`) defines `Byte = Fin 256`, modulo-256 addition, `Pair`, `Authority`, `FieldState`, `FieldOp`, and `runField`. `Authority` has `root`, `splitFields`, and selected `sliceCell` states: splitting requires `root`, while field writes and restoration require `splitFields`.

The captured functional field operation updates `left` via `wrapping_add` and preserves `right`. The certificate plan `split; writeLeft(delta); restore` is replayed by `runField`. Theorem `field_correspondence` proves that under the explicit entry premise `entryOwn : entry = Authority.root`, replay returns the exact captured update with `Authority.root` restored. Theorem `field_frame` proves that `right` is unchanged.

`fieldConsumerAccepted` binds the selected native source-hash index (`996f70f543d0bad10d09464b2f4f8df566bc556c8a8f0fdcc8c4b9f796f7797b`) and universally quantifies correspondence over all modeled states, deltas, and root entries with an empty axiom dependency list. `support/experiments/field-certificate.json` records the data-only plan emitted as `providedPlan` in `support/experiments/BorrowCertificate.lean`, where `providedCertificate` is kernel-checked with no axioms and no `sorryAx`.

#### Slice certificate exposes bounds and frame preservation

Basis: **source** + **execution**.

In `support/experiments/BorrowModel.lean`, `updateCell` mutates only the selected `Fin 2` cell, and `slice_frame` proves that every `j ≠ i` is unchanged. `capturedSlice` checks `index < 2`. `transformedSlice` borrows from `root`, writes under `sliceCell(index)`, and restores `root` (persisted as data in `support/experiments/slice-certificate.json`). Theorem `slice_correspondence` proves exact agreement with `capturedSlice` paired with `root` under the root-entry premise.

Theorem `slice_oob` proves that indices outside `[0, 2)` return `none`. Theorem `wrong_authority` proves that attempting a write under `root` without first acquiring the selected child permission returns `none`. `sliceConsumerAccepted` binds the source-hash index and universal correspondence, depending only on `propext`.

#### Exhaustive native finite-domain controls and wrong-field negative control

Basis: **execution** + **derived**.

`support/experiments/borrow_native.rs` (SHA-256 `996f70f543d0bad10d09464b2f4f8df566bc556c8a8f0fdcc8c4b9f796f7797b`) tests the safe Rust functions across all `256 × 256 = 65,536` two-byte field states and all `65,536 × 3 = 196,608` two-byte slice/index cases (`index ∈ {0, 1, 2}`, fixed `delta = 3`). Valid slice indices verify the selected element update and frame preservation of the other element; index `2` verifies `None` and an unchanged slice. The native run (`support/experiments/execution-results.json`, `support/experiments/borrow-certificate-results.json`) exits `0` with `field_cases = 65536`, `slice_cases = 196608`, `fixed_delta = 3`, and FNV-64 digest `f2ed1041187b6325` across three process samples (`0.0565 s`, `0.00642 s`, `0.00615 s`; compilation `0.382 s`).

Conversely, `support/experiments/BorrowWrongField.lean` substitutes `writeRight` while claiming the `left`-update endpoint: starting from `(0, 0)` with `delta = 1`, it requests `(1, 0)` against the plan's actual output `(0, 1)`. Kernel `decide` rejects the proof and Lean exits `1`.

This authority state tracks local entry, splitting, child write, and restoration for the replayed plan; it is not a global separation algebra because ordinary Lean values can duplicate tags unless constrained by a linear/spatial resource interpretation.

---

### Finite Pointer Lease and Reconstruction Control

#### Registered lease obligations beyond numerical range geometry

Basis: **source** + **execution** + **derived**.

`PointerLease.lean` (SHA-256 `9be4abb255fea836a0a2df97c2bf7088c0b681876fb759c30fb4ab95af328e00`, importing `Std` only and checked with exit `0` under both Lean 4.31.0 and Lean 4.34.1 in `lean-execution.json`) models four byte cells (`Fin 256`), an allocation identity, an allocation-death timestamp, a per-cell owner ticket, and a registry of live capability records. Each capability stores its ticket, allocation ID, half-open range `[start, stop)`, expiry time, alignment, initialization flag, and validity flag.

- `Owned` checks exact registry membership, allocation identity, in-bounds range `[0, 4]`, expiry no later than allocation death (`cap.expiry ≤ state.allocDeath`), and ticket ownership across every covered cell.
- `reconstructByte` requires `Owned`, current time strictly before expiry (`now < cap.expiry`), and `initialized ∧ valid ∧ align ≥ 1`.
- `reconstructWord` additionally requires `align ≥ 4`, aligned start offset `start % 4 = 0`, and full four-cell extent (`stop - start = 4`).
- Theorem `construction` proves `Owned` for any four-byte initial state.
- Theorem `geometry_misses_lifetime` proves that a lease whose expiry (`20`) exceeds allocation death (`10`) still satisfies all allocation and range-geometry predicates.
- Theorem `weakened_gate_accepts_extension` shows that omitting the `cap.expiry ≤ state.allocDeath` conjunct admits reconstructing a byte at time `11` after the allocation died at time `10`, whereas the full `Owned` gate rejects that same lease (`lifetime_extension_rejected`).

#### Splitting, projection, consumption, and negative capability controls

Basis: **source** + **execution**.

- **Splitting and consumption:** For every split point `k : Fin 5`, splitting retires parent ticket `1` and registers child tickets `2` (`[0, k)`) and `3` (`[k, 4)`). Theorems `split_left`, `split_right`, `split_disjoint`, and `split_covers` verify the child capabilities and range partition (including empty endpoint ranges). `stale_parent_rejected` proves parent ticket `1` is rejected in the split registry. `consume` deletes a ticket from the registry, and `duplicate_reconstruction_rejected` proves a consumed ticket cannot reconstruct a reference.
- **Projection and restoration:** `projection` registers a single-cell ticket and proves `Owned`; `projection_preserves_bytes` proves all four cells retain their exact byte values (`no axioms`). `restoration` registers whole-range ticket `4` and rejects the retired child ticket.
- **Negative controls for lifetime, aliasing, and alignment:** `expired_rejected` rejects reconstruction at `now = cap.expiry`; `alias_overlap_rejected` constructs overlapping ranges and rejects the second owner's claim on shared cell `2`; `cast_without_alignment_rejected` rejects `reconstructWord` from a 1-byte-aligned capability; `reconstructed_byte` and `reconstructed_word_after_alignment_evidence` succeed when the required alignment (`1` or `4`) and validity premises hold. All 19 checked theorems in `PointerLease.lean` depend only on `propext` and/or `Quot.sound` (with zero axioms for `projection_preserves_bytes`) and zero `sorryAx`.

#### Comparison with `zerocopy::Ptr` and safe/negative Rust compiler controls

Basis: **source** + **normative** + **execution** + **derived**.

In `google/zerocopy` (`zerocopy/src/pointer/ptr.rs`, `zerocopy/src/pointer/inner.rs`, `zerocopy/src/pointer/mod.rs`, recorded in `source-identities.json`), `Ptr<'a, T, I>` layers aliasing, alignment, and validity invariants over `PtrInner<'a, T>`, with lifetime covariance and type invariance:

- `from_ref` and `from_mut` establish shared/exclusive aligned valid pointers; `as_ref` and `as_mut` require the corresponding invariant states; `reborrow` narrows exclusive lifetime; `cast` and `project` require unsafe trait laws (`Cast`, `Project`) and reset alignment to `Unaligned` until re-proved.
- Because `Ptr::as_inner(&self)` returns a copyable `PtrInner`, consuming an outer `Ptr` does not automatically erase escaped raw copies; a sound capability model must track all derived access paths.
- `PtrInner::split_at_unchecked` (lines 283–324) requires an in-bounds split index and guarantees non-overlapping byte ranges only when the left part has no trailing padding (which holds for `[T]` slices, whereas a general trailing-slice DST can have trailing padding that overlaps the right slice).

The four Rust control programs (`native-execution.json`) demonstrate these boundaries under `rustc 1.101.0-nightly`:

1. `pointer_safe.rs` exercises all 5 split indices (`0..=4`) of a `[u8; 4]` array via `split_at_mut`, mutates both disjoint halves, ends the child borrows, reads the restored array, checks a non-dereferenced `u8 → () → u8` pointer-equality roundtrip, and reads an unaligned `#[repr(C, packed)]` `u32` field using `core::ptr::addr_of!` and `core::ptr::read_unaligned`, printing `12345678` with exit `0`.
2. `packed_reference_rejected.rs` attempts to form `&u32` directly to the packed field and is rejected by `rustc` with `E0793` (unaligned reference creation is undefined behavior under the Rust Reference `src/behavior-considered-undefined.md` even without a load).
3. `lifetime_rejected.rs` attempts to return a `'static` mutable slice from a local borrow and is rejected by the borrow checker.
4. `alias_rejected.rs` attempts to hold two simultaneous `&mut` borrows of the same slice and is rejected with `E0499`.

---

### Three Checked Correspondence Routes for a Captured Safe-Byte Fragment

#### Shared semantics, consumer-owned claim, and three verification routes

Basis: **source** + **execution**.

In `support/experiments/ArithmeticModel.lean` (SHA-256 `23f05b95266742c0064b749a533dea5363aef439a9f5081df1e400e5634c75e3`), `Byte` is `Fin 256`, wrapping addition and multiplication are modulo-256 arithmetic, and `Source` and `IR` are separate expression datatypes with total evaluators `evalSource` and `evalIR`. For the safe Rust fixture `support/experiments/subject.rs` (SHA-256 `e3a37308bc49b9ed0308dbcbc6e63890b74a22de29abdf7030673b7ad6c642e8`, where `scale(x: u8) -> u8 { x.wrapping_mul(5) }` and `subject(x: u8) -> u8 { scale(x.wrapping_add(3)).wrapping_add(7) }`), `support/bootstrap.py` validates candidate data against the consumer challenge (`support/experiments/challenge.json`, `support/experiments/baseline-candidate.json`) before emitting a Lean file that proves:

$$\text{Claim}(\text{expectedSourceHash}, \text{actualSourceHash}, \text{capturedSource}, \text{proposedIR}) \iff (\text{expectedSourceHash} = \text{actualSourceHash}) \wedge (\forall x : \text{Fin } 256,\; \text{evalIR}(\text{proposedIR}, x) = \text{evalSource}(\text{capturedSource}, x))$$

| Route | Lean Fixture | Witness & Checking Endpoint | Resulting Theorem | Median Check Time ($n=3$) | Min–Max Seconds | Fixture Size (Bytes) |
| --- | --- | --- | --- | ---: | ---: | ---: |
| **Instrumented** | `support/experiments/Arithmetic-instrumented.lean` | Rust emits 256 `input/a/b/output` rows (`support/experiments/native-rows.json`); `checkInstrumented` verifies all 256 inputs, intermediates (`x + 3`, `(x + 3) * 5`), source output, and IR output | `instrumented_sound` yields all-input evaluator equality | `2.411 s` | `2.353–6.369 s` | `10,659` |
| **Post-hoc** | `support/experiments/Arithmetic-posthoc.lean` | `checkPosthoc` checks structural equality `decode(proposedIR) = capturedSource` | `decode_eval` and `posthoc_sound` yield all-input evaluator equality | `0.809 s` | `0.775–0.812 s` | `4,442` |
| **Constructive** | `support/experiments/Arithmetic-constructive.lean` | Kernel checks `proposedIR = construct(capturedSource)` | `construct_eval` (proved by induction on `Source`) yields all-input evaluator equality | `0.785 s` | `0.729–0.800 s` | `4,433` |

All three `consumerAccepted` theorems exit `0` under Lean 4.31.0 and depend only on `propext`, with no `native_decide` or `sorryAx` (`support/experiments/execution-results.json`). Native execution of `support/experiments/arithmetic_native.rs` (`support/experiments/native-observation.json`) confirms that the uninstrumented and instrumented Rust functions agree on all 256 `u8` inputs and match modulo-256 arithmetic.

---

### Complete Small Safe API over an Unsafe Boolean Representation Operation

#### Public `Fin 256` caller domain vs narrowed `Fin 2` carrier

Basis: **source** + **normative** + **execution** + **derived**.

`support/api.rs` (SHA-256 `416eded2d8d38c4de7212091446c16ffca3bd49f7aa266d02ec718d07c1038fa`) defines `pub fn checked_bool(byte: u8) -> Option<bool>`, which checks `if byte < 2 { Some(unsafe { core::mem::transmute::<u8, bool>(byte) }) } else { None }`. Under the [Rust Reference validity rules](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/behavior-considered-undefined.md#L115) and [`core::intrinsics::transmute` contract](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/intrinsics/mod.rs), constructing a `bool` from any byte outside `{0, 1}` is immediate undefined behavior. Because `checked_bool` is a safe public function taking `u8`, its caller domain is all 256 byte values (`Fin 256`), not merely `{0, 1}`.

In `support/ApiCertificate.lean` (SHA-256 `64d5e8b8df69fe8a6874a32d6d19e6cab6253af1c186ba5238a6e428d652f914`, recorded in `support/input-identities.json` and `support/results.json`), `castResult` maps `0 ↦ ok false`, `1 ↦ ok true`, and `2..255 ↦ bad`. `Step` models `entry`, `pending` transmutation, and terminal states:

- `entry_covers_all` (`no axioms`) proves the entry invariant holds for every `Byte : Fin 256`.
- `step_preserves`, `all_inputs`, and `no_bad` (depending only on `propext` and `Quot.sound`, with zero `sorryAx`) prove that every step preserves the state invariant, the pending cast state is entered only when `byte < 2`, and `bad` is unreachable from any `Fin 256` entry.
- Negative logical witnesses prove that widening the guard to `byte < 3` (`wider_guard_bad`) or removing the guard (`unguarded_bad`) reaches `bad` on byte `2`.
- Discriminating domain witness `narrowed_model_hides` proves that the buggy `byte < 3` implementation still agrees with `checked_bool` on every `Fin 2` input (`0` and `1`), demonstrating that a producer-narrowed carrier hides real undefined behavior on valid safe-caller inputs.
- Native execution (`support/native.rs`, `support/native.stdout`) tests `checked_bool` with `black_box` across all 256 `u8` inputs and exits `0` with `all_native_u8_inputs=256; accepted=2; rejected=254`.

---

### Scalars, Values, Storage, and Access Side Conditions

#### Concrete scalar endpoints and Charon MIR pointer-cast preservation

Basis: **normative** + **source** + **derived**.

Under the [Rust Reference operator expressions specification](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/expressions/operator-expr.md#L25), integer overflow is mode-dependent, division or remainder by zero panics, signed `MIN / -1` panics on overflow, numeric `as` casts truncate/extend or apply IEEE-754 float conversions, and `&&`/`||` short-circuit. Aeneas (`AeneasVerif/aeneas@ca282ec2312a96f6a985a4d23a663690816d3f3e`) models scalars in [`backends/lean/Aeneas/Std/Scalar/Core.lean` (lines 50–84, blob `e066fff573f3bc51b18c26a8c770c79ea67b7173`)](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/backends/lean/Aeneas/Std/Scalar/Core.lean#L50) via `BitVec` with `System.Platform.numBits` for `isize`/`usize`, models division/remainder zero and overflow failures in [`Ops/Div.lean` (lines 17–25, 405–428, blob `7a99c7e89c5778956ec4d4d2c62b8f5326dcc7e4`)](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/backends/lean/Aeneas/Std/Scalar/Ops/Div.lean#L17), and models scalar casts in [`Scalar/Casts.lean` (lines 18–44, 110–148, blob `5047d34876b38b9c9443f4a906501e27dc58ac99`)](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/backends/lean/Aeneas/Std/Scalar/Casts.lean#L18).

In Charon (`AeneasVerif/charon@cf02e3f228f97ee7be3a415be56989053063326d`), [`translate_bodies.rs` (lines 1272–1338)](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/bin/charon-driver/translate/translate_bodies.rs#L1272) lowers four MIR pointer-cast kinds into `CastKind::RawPtr(src_ty, tgt_ty)` ([`expressions.rs` line 179](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/ast/bodies/expressions.rs#L179)) while [`TyKind` (`types.rs` line 22)](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/ast/type_level/types.rs#L22) keeps scalar integers, raw pointers, and function pointers distinct:

| Named MIR Operation | Retained `(source, target)` Type-Class Pair in Charon `CastKind::RawPtr` |
| --- | --- |
| `PtrToPtr` | `raw pointer → raw pointer` |
| `FnPtrToPtr` | `function pointer → raw pointer` |
| `PointerExposeProvenance` | `pointer → integer` (`Literal(Usize)`) |
| `PointerWithExposedProvenance` | `integer` (`Literal(Usize)`) `→ raw pointer` |

Thus sharing the `CastKind::RawPtr` variant does not lose the semantic distinction among these four casts on well-typed MIR. Downstream, Aeneas [`SymbolicToPureExpressions.ml` (lines 568–598, blob `5d575dfd639cfb243c32a467759c5482c165a1cf`)](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/symbolic/SymbolicToPureExpressions.ml#L568) supports raw casts only between pointers to scalar types and explicitly rejects function-pointer casts, `transmute`, and `dyn` concretization.

#### Typed transfer, byte copying, `MaybeUninit`, `UnsafeCell`, and state/heap obligation matrix

Basis: **normative** + **source** + **derived**.

At `rust-lang/rust@b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`:

- [`core::ptr::read` (lines 1606–1620, blob `8b8a65d630189dbd98fa8ccfaa54d89665f5e291`)](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/ptr/mod.rs#L1606) requires an aligned, initialized, valid `T` (including ZST alignment) and leaves source memory unchanged.
- [`core::ptr::copy_nonoverlapping` (lines 466–495)](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/ptr/mod.rs#L466) performs an untyped byte copy preserving initialization state across non-overlapping aligned ranges without duplicating logical ownership of non-`Copy` values.
- [`core::ptr::read_unaligned` (lines 1759–1785)](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/ptr/mod.rs#L1759) reads unaligned initialized storage directly without permitting intermediate unaligned `&T` creation.
- [`core::mem::MaybeUninit` (lines 205–225, 269–317, blob `6275d7cd59a2c2fc82514082f4e87bf2cc7990db`)](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/mem/maybe_uninit.rs#L205) permits uninitialized storage, warns that typed moves/copies may strip initialized padding, requires `assume_init` callers to establish `T`'s validity invariant, and does not run `T`'s destructor unless unpacked.
- [`core::cell::UnsafeCell` (lines 2149–2162, 2221–2229, blob `2dc2c5981cafddb5cb7ceeabdadb269d52416ac7`)](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/cell.rs#L2149) permits shared interior mutation without relaxing `&mut` exclusivity or data-race rules, and its inner-layout guarantee does not automatically extend through niche-optimizing outer enums.

| Transformation Class | Required State and Representation Certificate |
| --- | --- |
| Pointer/address exposure, arithmetic, cast | Preserve allocation ID, lifetime, and selected provenance semantics; justify in-bounds offsets, target width, and metadata beyond numeric address equality. |
| Erase permission/borrow structure | Preserve read/write authority and every forbidden access prefix; ghost permissions cannot be synthesized from a valid final return value. |
| Layout/ABI normalization | Bind size, alignment, field offsets, discriminant/niche encoding, and target ABI to the exact instantiated Rust type (`src/type-layout.md` blob `9d56ea757019745702ab5b50c04e129a073bee5d`). |
| Packed field and unaligned access | Preserve exact raw unaligned primitive operations (`addr_of!` + `read_unaligned`) and forbid intermediate unaligned reference creation. |
| Initialization and padding abstraction | Track per-byte initialization (`AMByte` uninit/init) and permitted padding loss during typed moves; a byte decoder is not a physical memory load. |
| Logical ADT / niche conversion | Relate valid discriminants, active fields, and niche encodings; reject invalid bit patterns before entering a total Lean inductive carrier. |
| Move, copy, assignment, call/return | Preserve source/destination storage effects, ownership transfer, validity, and destructor obligations. |
| Allocate, free, reuse, failure | Track allocation epochs, live extents, allocation failure, and deallocation ownership so address reuse never revives dangling authority. |
| Slice/DST/ZST conversion | Relate wide-pointer metadata, dynamic bounds, alignment, and empty ZST byte footprints explicitly. |
| Heap restructuring / alias collapse | Relate all observable aliases, frame permissions, and disjointness so pure functional values never duplicate exclusive mutable resources. |
| Interior mutation / projections | Preserve `UnsafeCell` shared-mutation permissions and require validity at every projection even when the projected value is unused. |
| Scalars, ADTs, builtin replacement | Bind mathematical operations to exact machine widths, overflow/panic modes, short-circuit evaluation, and full caller domains. |

---

### Pinning, Async Progress, and Foreign or Hardware Resource Contracts

#### Pin drop guarantee, Future polling, and native async-drop observation

Basis: **normative** + **execution** + **derived**.

- **`core::pin` drop guarantee:** At `rust-lang/rust@d8ef4f3fe7031514cbd7d056b7b058814987ecec` ([`library/core/src/pin.rs` line 510](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/library/core/src/pin.rs#L510)), once a `!Unpin` value is pinned, its memory must remain valid and must not be overwritten or repurposed until `Drop::drop` is called and returns (or panics); leaking storage without reuse is permitted. A certificate for pinned resources must therefore track allocation liveness, the pinned place, self-referential invariants, pin projections, and terminal drop completion.
- **`Future::poll` and `await` suspension:** [`library/core/src/future/future.rs` (line 37)](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/library/core/src/future/future.rs#L37) and [`src/expressions/await-expr.md`](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/expressions/await-expr.md) specify that `poll` takes `Pin<&mut Self>` and `&mut Context<'_>`, registers the latest waker when returning `Poll::Pending`, and may panic or block if repolled after `Poll::Ready` but must never cause undefined behavior. Cancellation drops a suspended future at an `await` point without executing its resumption continuation.
- **Native async drop probe (`async_drop_probe.rs`, `probe-results.json`):** Executed under `rustc 1.99.0`, the probe drops one unpolled future and polls a second boxed pinned future to `Poll::Pending` before dropping it. It prints `unpolled=1; suspended_before_drop=1; suspended_after_drop=2` and exits `0`, confirming distinct cleanup paths for unpolled vs suspended futures.

#### Async responsiveness (LART), scheduler fairness (LAGC), and stuttering non-termination

Basis: **documentation** + **derived**.

- **LART responsiveness (`arXiv:2610.09198v1`, §§3.2, 4–5):** Models responsiveness obligations pairing wakers with monotonic predicates transferred through repositories. Theorem 1 requires pollables to preserve obligations across yields and reactors to be responsive; Theorem 4 requires repeated reactor iterations (or invocation-ordering extensions for terminating reactors); Theorem 5 requires faithful async compilation, fair scheduling, and eventual external events to conclude task progress.
- **LAGC fairness (`arXiv:2610.06003v1`, §§5.5, 7):** Models safe source-like Rust (explicitly excluding `unsafe` Rust and assuming borrow/type safety) via locally abstract, globally concrete traces. Theorem 5.7 assumes no locally infinite computations and relates scheduler executions via translation `trans` to quiescent-fair traces; Theorem 5.9 establishes its Tokio-fair execution relation.
- **Stuttering transition-system counterexample:** Agreement on finite terminal results does not preserve termination or responsiveness if erased steps stutter infinitely. Specifically, a source system with transitions $s \to s$ and $s \to \text{unit}$ and a model with only $m \to \text{unit}$ have identical finite-result sets $\{\text{unit}\}$, yet the source admits an infinite self-loop while the model strongly normalizes. Progress transfer requires an explicit stuttering rank or divergence-preserving simulation plus preserved wake/cancellation events.

#### Foreign callbacks, volatile I/O, inline assembly, and DMA contracts

Basis: **normative** + **derived**.

- **FFI and callbacks ([`src/behavior-considered-undefined.md` line 55](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/behavior-considered-undefined.md#L55)):** Calling across mismatched ABIs or unwinding across disallowed foreign frames is undefined behavior. Foreign callback contracts must specify calling convention, layout validity, pointer retention duration, reentrancy, concurrency, and explicit callback unregistration/join before borrowed or pinned Rust storage expires.
- **Volatile accesses ([`library/core/src/ptr/mod.rs` line 2056](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/library/core/src/ptr/mod.rs#L2056)):** `read_volatile` and `write_volatile` remain subject to ordinary validity and provenance rules when targeting Rust-allocated memory. Their MMIO exception applies only to non-Rust-allocated hardware memory whose side effects do not mutate Rust-allocated memory, and volatile accesses provide no inter-thread synchronization.
- **Inline assembly ([`src/inline-assembly.md` line 1320](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/inline-assembly.md#L1320)) and DMA:** Inline assembly contracts must match declared register clobbers and options (`pure`, `nomem`, `readonly`, `preserves_flags`). Device DMA into Rust-allocated buffers falls outside the MMIO exception and requires a phase-ownership protocol governing CPU-to-device transfer, cache coherence/barriers, completion notification, and buffer lifetime before Rust references resume access.

---

### Pure Mathematical Layout and Storage Models and Lean Version Compatibility

#### Checked mathematical laws vs unindexed physical interpretation (`BoundaryProbe.lean`, `support/layout_probe.rs`)

Basis: **source** + **execution** + **derived**.

Nine pure mathematical model modules (`Rust.Layout`, `Rust.Memory`, `Rust.Bytes`, `Rust.Storage`, `Rust.Arithmetic`, umbrella `Rust`, and test modules `RustBytesTests`, `RustStorageTests`, `RustTests`) were compiled under Lean 4.31.0 (`support/lean431/results.json`). `RustTests` (`support/lean431/RustTests.stdout.txt`) audits all 252 declarations in the six-module library and verifies that every declaration depends only on `propext`, `Classical.choice`, and `Quot.sound` (with geometric bound transfer using zero axioms).

`support/BoundaryProbe.lean` (`support/lean431/owned-boundary.stdout.txt`) and `support/layout_probe.rs` (`support/lean431/rust-build.stdout.txt`) prove concrete model-boundary witnesses:

1. **Unindexed `Layout`:** `Rust.Layout` stores `size`, `align`, positivity, and divisibility without a Rust type index. `BoundaryProbe.lean` constructs a valid `Layout` with `size = 1, align = 1` alongside native `u64` (`size = 8, align = 8`).
2. **Geometric `Allocation` and `FitsInAllocation`:** `Allocation` and `Referent` bound address intervals without proving allocation liveness or provenance. `BoundaryProbe.lean` constructs an empty-footprint referent fitting at address `100` with no live allocation premise.
3. **Vacuous and permissive `BitDecoder` instances:** `BitDecoder.run` checks byte length (`run_length`), and `Initialized` requires accepted byte lists to contain initialized `AMByte` elements (`boolDecoder` rejects byte `2` and uninitialized bytes; `arrayDecoder_initialized` lifts element initialization across arrays, including zero-sized elements). However, `BoundaryProbe.lean` constructs `allInputs` (which accepts uninitialized bytes and fails `Initialized`) and `noInputs` (which rejects every input and satisfies `Initialized` vacuously), proving that `Initialized` alone establishes neither completeness nor non-emptiness.
4. **Native target layout discriminations (`support/layout_probe.rs`):** On `aarch64-apple-darwin` under `rustc 1.99.0`, `#[repr(C)] struct { u8, u32 }` has `size = 8, align = 4` (offsets `0, 4`); nesting it after a `u8` yields `size = 12` (inner offset `4`); `#[repr(C, packed)]` yields `size = 5, align = 1` (word offset `1`); `#[repr(align(16))] struct Align16Zst;` has `size = 0, align = 16` and `[Align16Zst; 3]` has `size = 0`; `Option<NonZeroU8>` has `size = 1`; and `usize::MAX.checked_add(1)` is `None` while `wrapping_add(1)` is `0`.

#### Lean 4.31.0 vs 4.34.1 elaboration compatibility boundary

Basis: **execution**.

While all nine pure model modules compile unmodified under Lean 4.31.0 (`support/lean431/`), compiling the exact same immutable module sources under Lean 4.34.1 (`support/lean434/results.json`, `support/lean434/Rust-Storage.stdout.txt`) succeeds on `Rust.Layout`, `Rust.Memory`, and `Rust.Bytes` but fails at `Rust/Storage.lean:86` in `BitDecoder.run_map`: after `split`, the residual `if` expression is no longer definitionally reducible by `rfl` to the expected `Option.map` application.

## Boundaries

- **Lean 4.31.0 nested-inductive kernel soundness boundary (source reviewed 2026-10-14):** The recorded Lean `4.31.0` (`68218e876d2a38b1985b8590fff244a83c321783`) and `v4.30.0-rc2` runs are conditional on checker soundness. Direct comparison of `src/kernel/inductive.cpp` between Lean 4.31.0 (blob `7a09077a769a0a21a6a8820bc6277b20cc753d65`) and Lean 4.34.1 (blob `438f92d3f6df654dbd6bb1a131fd5a15997620e6`, lines 1316–1323) and `kernel-fix-identity.json` confirms that Lean 4.31.0 lacks the final nested-inductive parameter `tc.check` validation added by [`leanprover/lean4@a39eab69e1eee9ad38f4efe507907b1026a77808`](https://github.com/leanprover/lean4/commit/a39eab69e1eee9ad38f4efe507907b1026a77808) ([PR 14577](https://github.com/leanprover/lean4/pull/14577), documented in the [Lean 4.32.2 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.32.2/)). While `PointerLease.lean` was re-verified under Lean 4.34.1, exit `0` and an empty/standard axiom list on Lean 4.31.0 do not by themselves guarantee sound acceptance of arbitrary untrusted producer proofs.
- **Trusted source-capture frontier:** None of the prototypes verifies a general Rust parser, Charon, Aeneas, `rustc`, or LLVM code generation. Source-hash indices and state-machine captures are bound by external wrapper scripts (`support/bootstrap.py`, `support/revalidate.py`, `support/run_probe.py`) or manual inspection.
- **Finite model scope:** Two-byte `Pair`/`Slice2` and four-cell `PointerLease` models do not prove general separation-logic adequacy (Iris/RustBelt), full Stacked Borrows or Tree Borrows, integer-to-pointer exposed provenance, arbitrary DST trailing-padding splits, or concurrent weak-memory semantics.
- **Unexamined external artifacts:** The Jackdaw and Rust-LAGC companion implementation artifacts cited by `arXiv:2610.09198v1` and `arXiv:2610.06003v1` were not executed or audited at source level.

## Evidence

- **Field and slice borrow prototype (`support/field-slice-borrow-frame-prototype-lean4-31-rust1-99/` and `support/experiments/`):**
  - Lean models and certificates: `support/experiments/BorrowModel.lean`, `support/experiments/BorrowCertificate.lean`, `support/experiments/BorrowWrongField.lean`, `support/experiments/field-certificate.json`, `support/experiments/slice-certificate.json`, `support/experiments/borrow-certificate-results.json`.
  - Native Rust harness and logs: `support/experiments/borrow_native.rs`, `support/experiments/borrow_compile.stdout`, `support/experiments/borrow_compile.stderr`, `support/experiments/borrow_native.stdout`, `support/experiments/borrow_native.stderr`.
- **Finite pointer lease control (`PointerLease.lean` and `support/finite-pointer-lease-and-reconstruction-control-2026/`):**
  - Lean proof and dual-toolchain logs: `PointerLease.lean`, `lean-execution.json`, `kernel-fix-identity.json`, `source-identities.json`, `coverage.json`.
  - Rust positive and negative controls: `pointer_safe.rs`, `packed_reference_rejected.rs`, `lifetime_rejected.rs`, `alias_rejected.rs`, `native-execution.json`.
- **Three safe-byte correspondence routes (`support/safe-byte-correspondence-three-routes-lean4-31-rust1-99/` and `support/experiments/`):**
  - Lean models and route proofs: `support/experiments/ArithmeticModel.lean`, `support/experiments/Arithmetic-instrumented.lean`, `support/experiments/Arithmetic-posthoc.lean`, `support/experiments/Arithmetic-constructive.lean`, `support/experiments/challenge.json`, `support/experiments/baseline-candidate.json`.
  - Native Rust subject and trace rows: `support/experiments/subject.rs`, `support/experiments/instrumented.rs`, `support/experiments/arithmetic_native.rs`, `support/experiments/native-rows.json`, `support/experiments/native-observation.json`, `support/experiments/execution-results.json`, `support/bootstrap.py`.
- **Safe/unsafe Boolean domain certificate (`support/safe-unsafe-bool-domain-certificate/` and `support/`):**
  - `support/api.rs`, `support/ApiCertificate.lean`, `support/native.rs`, `support/input-identities.json`, `support/results.json`, `support/revalidate.py`, `support/lean.stdout`, `support/lean.stderr`, `support/native.stdout`, `support/native.stderr`.
- **Scalars, values, storage, and access side conditions:**
  - Primary files and Git blobs recorded inline: Rust `library/core/src/ptr/mod.rs` (`8b8a65d630189dbd98fa8ccfaa54d89665f5e291`), `library/core/src/mem/maybe_uninit.rs` (`6275d7cd59a2c2fc82514082f4e87bf2cc7990db`), `library/core/src/cell.rs` (`2dc2c5981cafddb5cb7ceeabdadb269d52416ac7`); Rust Reference `src/type-layout.md` (`9d56ea757019745702ab5b50c04e129a073bee5d`), `src/behavior-considered-undefined.md` (`ff34d0af28ca3ec42f548abf6cd3bce5840a6798`), `src/expressions/operator-expr.md` (`3b63884a5e445787078c19422fe627105e2a4933`); Aeneas `Scalar/Core.lean` (`e066fff573f3bc51b18c26a8c770c79ea67b7173`), `Ops/Div.lean` (`7a99c7e89c5778956ec4d4d2c62b8f5326dcc7e4`), `Scalar/Casts.lean` (`5047d34876b38b9c9443f4a906501e27dc58ac99`), and `SymbolicToPureExpressions.ml` (`5d575dfd639cfb243c32a467759c5482c165a1cf`).
- **Pin, async, and external resource contracts (`support/pin-async-and-external-resource-contracts-2026/`):**
  - `async_drop_probe.rs`, `probe-results.json`, `source-evidence.json`, `support/pin-async-and-external-resource-contracts-2026/async_drop_probe.rs`, `support/pin-async-and-external-resource-contracts-2026/probe-results.json`, `support/pin-async-and-external-resource-contracts-2026/source-evidence.json`.
- **Pure mathematical model boundaries (`support/pr-stack-pure-model-boundaries/`, `support/lean431/`, `support/lean434/`):**
  - `support/BoundaryProbe.lean`, `support/layout_probe.rs`, `support/run_probe.py`, `support/lean431/results.json`, `support/lean431/RustTests.stdout.txt`, `support/lean431/owned-boundary.stdout.txt`, `support/lean434/results.json`, `support/lean434/Rust-Storage.stdout.txt`.

## Revalidation

1. **Field and slice borrow prototype:** Run Lean `4.31.0` (`68218e876d2a38b1985b8590fff244a83c321783`) on `support/experiments/BorrowModel.lean` and `support/experiments/BorrowCertificate.lean` (expecting exit `0` and empty/`propext`-only axiom lists) and on `support/experiments/BorrowWrongField.lean` (expecting exit `1`). Compile and run `support/experiments/borrow_native.rs` under `rustc 1.99.0` (`--edition 2024 -C opt-level=0`) and verify `field_cases = 65536`, `slice_cases = 196608`, and FNV-64 digest `f2ed1041187b6325`.
2. **Finite pointer lease control:** Run both Lean `4.31.0` and Lean `4.34.1` on `PointerLease.lean` and verify exit `0`, zero `sorryAx`, and all 19 `#print axioms` outputs matching `lean-execution.json`. Compile and run `pointer_safe.rs` (expecting exit `0` and output `12345678`), and compile `packed_reference_rejected.rs` (`E0793`), `lifetime_rejected.rs`, and `alias_rejected.rs` (`E0499`) expecting compile-time rejection.
3. **Safe-byte correspondence routes:** Run `LEAN_BINARY=/path/to/lean-4.31.0/bin/lean python3 -B support/bootstrap.py` or invoke Lean `4.31.0` directly on `support/experiments/Arithmetic-instrumented.lean`, `support/experiments/Arithmetic-posthoc.lean`, and `support/experiments/Arithmetic-constructive.lean` (expecting exit `0` and `propext`-only dependencies), and run `support/experiments/arithmetic_native.rs` to verify all 256 trace rows.
4. **Boolean domain certificate:** Run `python3 -B support/revalidate.py --lean-bin /path/to/lean-4.31.0/bin/lean --rustc /path/to/rust-1.99.0/bin/rustc --out <scratch-dir>` to verify all positive/negative state-machine theorems in `support/ApiCertificate.lean` and all 256 native `u8` inputs in `support/native.rs`.
5. **Async drop and pure-model boundary probes:** Compile and run `async_drop_probe.rs` under `rustc 1.99.0` (`unpolled=1; suspended_before_drop=1; suspended_after_drop=2`), and run `support/run_probe.py` against Lean `4.31.0` (expecting 252 audited declarations in `RustTests` and passing `support/BoundaryProbe.lean`) and Lean `4.34.1` (confirming whether `BitDecoder.run_map` still requires proof adaptation after `split`).
