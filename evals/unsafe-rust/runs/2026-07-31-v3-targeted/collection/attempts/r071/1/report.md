# Multi-release unsafe Rust source review

## Claim and result

Snapshot: the submitted `lib.rs`, `SUPPORT.md`, `EVIDENCE.md`, and `TCB.md`; audit cutoff 2026-07-31. For each exported unsafe function, the independent claim is: every call satisfying its documented caller obligations is free of Rust undefined behavior and establishes each documented postcondition, for every required release, every target on which the item exists, and ordinary debug/release profiles, relative only to the accepted TCB below.

Let:

- `A = C = L = {1.80.0, 1.80.1, 1.81.0, 1.82.0}`;
- `S = {1.80.0, 1.81.0}`;
- `E = {1.80.0, 1.82.0}` and `M = {1.80.1, 1.81.0}`.

`Covered` is the exact release region on which all premises consumed by a derivation apply.

| API | Required | Covered | Soundness | Documented postconditions | Strongest combined verdict |
|---|---|---|---|---|---|
| `acknowledge` | `A` | `A` | `PROVED` on `A` | Normal return is `()` (`Q-A`): `PROVED` on `A`; no other postcondition is documented. | **PROVED** on Required, relative to `SEM-EMPTY-BLOCK-180-182`. |
| `store_word` | `S` | `S` | `PROVED` on `S` | `Q-S1`: stores `value`; `Q-S2`: does not read the old `u16`; `Q-S3`: does not drop it. Each is `PROVED` on `S`. | **PROVED** on Required. |
| `copy_byte` | `C` | `C` | `PROVED` on `C` | `Q-C1`: destination becomes the source byte; `Q-C2`: source byte is preserved. Each is `PROVED` on `C`. | **PROVED** on Required, relative to `COMPAT-COPY-180-182`. |
| `load_word` | `L` | `E` | `PROVED` on `E`; `UNPROVED` on `M` | `Q-L1`: return equals the initialized source `u32`; `Q-L2`: source remains unchanged. Each is `PROVED` on `E`, `UNPROVED` on `M`. | **UNPROVED** on Required; endpoint region `E` is **PROVED**. |

Thus the combined result for all four requested claims is **UNPROVED** solely because `load_word` is uncovered on `M`. No `UNSOUND` or `CONTRACT-BROKEN` witness is established.

## Boundary and configuration closure

The complete exported surface is four public unsafe free functions; there are no public fields, constructors, safe wrappers or methods, traits, callbacks, macros, hidden items, dependencies, generated artifacts, `cfg` branches, or invariant-bearing state in the submitted source. The only unsafe operations are one `ptr::write`, one `copy_nonoverlapping`, and one `ptr::read`; the empty function has none. Target/profile axes are proof-parametric: source selection and arguments do not vary, the versioned standard-library contracts apply wherever each item exists, and both admitted entries expressly quantify over the stated target/profile domain. No tests or tool-derived evidence were used.

## Obligation ledger and derivations

**A — `acknowledge`.** Local inspection establishes a zero-parameter, unit-returning function whose body is exactly `{}`. Accepted `SEM-EMPTY-BLOCK-180-182` applies exactly to that fact over `A`, entails defined callee evaluation and `()`, and therefore proves soundness and `Q-A`. “Has no additional safety requirements” leaves no hidden caller premise.

**S — `store_word`.** At both required releases, the submitted [`ptr::write` 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.write.html) and [`ptr::write` 1.81.0](https://doc.rust-lang.org/1.81.0/std/ptr/fn.write.html) pages say it overwrites with the given value “without reading or dropping the old value”; each requires `dst` to be valid for writes and properly aligned. The function's Safety clauses supply those exact requirements for `T = u16`. The single call therefore satisfies its callee contract and the description entails `Q-S1`–`Q-S3` on each member of `S`.

**C — `copy_byte`.** The [`copy_nonoverlapping` 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.copy_nonoverlapping.html) contract requires readable/writable `count * size_of::<T>()` regions, alignment, and non-overlap, and says it copies that many bytes. The [1.80.0 layout table](https://doc.rust-lang.org/1.80.0/reference/type-layout.html#primitive-data-layout) gives `size_of::<u8>() = 1`; [`u8: Copy`](https://doc.rust-lang.org/1.80.0/std/primitive.u8.html#impl-Copy-for-u8) and the [`Copy` semantics](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html) establish bit-copy rather than move semantics. Locally, `T = u8` and `count = 1`, so the documented caller clauses entail every callee clause. Accepted `COMPAT-COPY-180-182` preserves precisely these propositions, including `Q-C1` and `Q-C2`, over all `C`; no cross-operation transfer occurs.

**L — `load_word`.** Both submitted [`ptr::read` 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.read.html) and [`ptr::read` 1.82.0](https://doc.rust-lang.org/1.82.0/std/ptr/fn.read.html) pages require readable, aligned, properly initialized storage and say the value is read without moving it while source memory remains unchanged. The caller contract supplies the three requirements. At each endpoint, [`u32: Copy` 1.80.0](https://doc.rust-lang.org/1.80.0/std/primitive.u32.html#impl-Copy-for-u32), [`Copy` 1.80.0](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html), [`u32: Copy` 1.82.0](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#impl-Copy-for-u32), and [`Copy` 1.82.0](https://doc.rust-lang.org/1.82.0/std/marker/trait.Copy.html) establish copy semantics, closing soundness and both postconditions on `E`.

## TCB audit

| Entry | Exact admitted proposition/domain | Consumer | Disposition |
|---|---|---|---|
| `SEM-EMPTY-BLOCK-180-182` | Defined evaluation and unit return for the exact empty-function shape, all `A` targets/profiles. | `acknowledge` only | Accepted; local shape verified. |
| `COMPAT-COPY-180-182` | Preserves the enumerated 1.80.0 one-`u8` copy contract, safety, size, Copy semantics, and both results over `C`. | `copy_byte` only | Accepted; base pages and local type/count verified. |

There are no other admitted premises, pending entries, or dependencies. Re-audit each entry on its stated source, contract, domain, or disposition trigger.

## Findings

**F-L-COVERAGE — `UNPROVED`.** On `M`, the smallest missing proposition is: `ptr::read::<u32>` has the stated three safety requirements and read/unchanged postconditions, and `u32` has the required Copy semantics. Endpoint documentation does not propagate inward or backward, and neither accepted entry applies to `ptr::read`. No UB witness and no UB-free postcondition refutation is established. Resolution requires admissible release-specific authorities or an accepted compatibility proposition covering exactly `M`; then re-audit all `load_word` obligations.

**F-C-PROOF-DOC — proof artifact deficient; implementation proved.** The adjacent `copy_byte` comment omits the material `T = u8`, `count = 1`, `size = 1`, Copy/source-preservation, and compatibility derivation reconstructed above. Suitable replacement: “For `T=u8,count=1`, the caller's one-byte read/write, alignment, and non-overlap clauses satisfy the callee contract; `COMPAT-COPY-180-182` supplies the applicable one-byte copy and source-preservation result.” This does not change the implementation verdict.

Residual scope excludes releases outside Required and binary/backend correctness. Re-audit on source or contract changes, support-set expansion, relevant Rust-documentation changes, or either TCB trigger.
