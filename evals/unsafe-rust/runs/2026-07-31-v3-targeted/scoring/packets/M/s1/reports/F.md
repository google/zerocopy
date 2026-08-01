# Unsafe Rust source audit: four exported APIs

## Claim, snapshot, and strongest results

This review covers exactly `lib.rs` in the submitted packet, independently for the four exported unsafe free functions. For each API, the claim is: every call satisfying its documented safety obligations has defined source-level Rust evaluation and establishes every stated normal-return postcondition, for every release in its `Required` set, every target on which the item exists, and ordinary debug and release profiles. The audit cutoff is 2026-07-31. Results are relative to the exact submitted authorities and accepted `TCB.md`; no compiler-backend or binary theorem is claimed.

| API | `Required` | Exact evidence-backed `Covered` | Soundness | Documented postconditions | Strongest combined verdict |
|---|---|---|---|---|---|
| `acknowledge` | `{1.80.0, 1.80.1, 1.81.0, 1.82.0}` | same set | **PROVED** throughout | Normal return yields `()`: **PROVED** throughout | **PROVED** |
| `store_word` | `{1.80.0, 1.81.0}` | same set | **PROVED** throughout | Stores `value`: **PROVED**; does not read the old `u16`: **PROVED**; does not drop it: **PROVED**, each throughout | **PROVED** |
| `copy_byte` | `{1.80.0, 1.80.1, 1.81.0, 1.82.0}` | same set | **PROVED** throughout | Destination receives the source byte: **PROVED**; source byte remains unchanged: **PROVED**, each throughout | **PROVED** |
| `load_word` | `{1.80.0, 1.80.1, 1.81.0, 1.82.0}` | `{1.80.0, 1.82.0}` | **PROVED** on `Covered`; **UNPROVED** on `{1.80.1, 1.81.0}`, hence **UNPROVED** for `Required` | Returns the initialized source `u32`: endpoint **PROVED**, interior **UNPROVED**; leaves source unchanged: endpoint **PROVED**, interior **UNPROVED** | **UNPROVED** for `Required`; **PROVED** on `Covered` |

No valid UB witness or UB-free postcondition refutation is established. Thus no result is `UNSOUND` or `CONTRACT-BROKEN`.

## Obligation ledger and proofs

**ACK-S/ACK-Q (`lib.rs:3-4`).** The function has no caller safety precondition beyond making an unsafe call, and its exact body is `{}`. Accepted `SEM-EMPTY-BLOCK-180-182` applies to precisely this body, signature, all four required releases, applicable targets, and both profile classes. Its proposition entails defined evaluation and the unit return. Nothing is transferred to another API.

**STORE-S/STORE-Q (`lib.rs:6-13`).** At both required releases, the call is exactly `ptr::write::<u16>(dst, value)`. The caller contract supplies the two [1.80.0 `write`](https://doc.rust-lang.org/1.80.0/std/ptr/fn.write.html) / [1.81.0 `write`](https://doc.rust-lang.org/1.81.0/std/ptr/fn.write.html) safety conjuncts: write-validity for one `u16` and proper alignment. `value` is a well-typed `u16`. Each versioned description states that `write` overwrites with the supplied value without reading or dropping the old value; this proves all three postconditions. The two singleton authority regions exhaust `Required`.

**COPY-S/COPY-Q (`lib.rs:16-25`).** The call fixes `T = u8`, `count = 1`. The [1.80.0 layout table](https://doc.rust-lang.org/1.80.0/reference/type-layout.html#primitive-data-layout) gives `size_of::<u8>() = 1`; therefore the [1.80.0 `copy_nonoverlapping`](https://doc.rust-lang.org/1.80.0/std/ptr/fn.copy_nonoverlapping.html) read-validity, write-validity, alignment, and nonoverlap regions reduce exactly to the one-byte obligations documented at lines 20-22. [`u8: Copy`](https://doc.rust-lang.org/1.80.0/std/primitive.u8.html#impl-Copy-for-u8) and [1.80.0 `Copy` semantics](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html) establish that duplicating this byte does not move ownership. The operation copies exactly that byte and preserves source initialization/state. Accepted `COMPAT-COPY-180-182` explicitly preserves this complete safety and postcondition proposition over every release in `Required`, target, and profile. Its four-release region exhausts `Required`.

**LOAD-S/LOAD-Q (`lib.rs:28-36`).** At each covered endpoint, the call is `ptr::read::<u32>(src)`. The [1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.read.html) and [1.82.0](https://doc.rust-lang.org/1.82.0/std/ptr/fn.read.html) contracts require read-validity, alignment, and a properly initialized `u32`, exactly supplied at lines 32-33. Their descriptions establish reading/returning the value while leaving source memory unchanged. Endpoint [`u32: Copy` 1.80.0](https://doc.rust-lang.org/1.80.0/std/primitive.u32.html#impl-Copy-for-u32), [`Copy` semantics 1.80.0](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html), [`u32: Copy` 1.82.0](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#impl-Copy-for-u32), and [`Copy` semantics 1.82.0](https://doc.rust-lang.org/1.82.0/std/marker/trait.Copy.html) discharge duplicate-ownership concerns. For 1.80.1 and 1.81.0 the smallest missing proposition is that these exact `ptr::read` safety, return-value, source-preservation, and `u32: Copy` propositions apply. Endpoint documentation does not cover interior releases, and neither accepted TCB entry permits that transfer. This blocks every interior obligation.

## Boundary, configuration, and trust closure

The complete source surface is the four unsafe functions above. There are no safe APIs, fields, constructors, traits/impls, macros, hidden items, FFI, generated artifacts, dependencies, callbacks, persistent invariants, or configuration branches in the submitted source. Target and profile coverage is parametric: the source has one path, and each consumed authority or TCB proposition applies without a target/profile branch over its stated region. No tests or tool-derived evidence were used.

TCB identity is the exact submitted `TCB.md` (no external revision was supplied). Both entries are accepted OUT-OF-BAND propositions: `SEM-EMPTY-BLOCK-180-182`, consumed only by ACK-S/ACK-Q, and `COMPAT-COPY-180-182`, consumed only by COPY-S/COPY-Q. Their identities, quantifiers, consumers, exclusions, and re-audit triggers were checked. There are no admitted dependency, platform, implementation, deployment, or probabilistic premises. The absent `load_word` compatibility proposition is not silently added.

## Finding DOC-1: local proof comments are deficient

The three pointer-operation comments merely assert that the caller supplies “exactly/every” callee precondition. They omit the material type/count/size and ownership derivations above and cite no applicable authority. This is proof-documentation debt, not an implementation defect in each API's `Covered` region. Minimal replacements should state: for `store_word`, `T=u16` and lines 10-13 discharge write-validity/alignment; for `copy_byte`, `T=u8`, `count=1`, `size=1`, lines 20-22 discharge all four regional obligations, and `u8: Copy` makes duplication ownership-safe; for `load_word`, `T=u32`, lines 32-33 discharge read-validity/alignment/initialization, and `u32: Copy` permits the returned copy while the source remains. The latter wording must cite only a release region actually covered.

## Residual scope and re-audit triggers

Excluded are releases outside `Required`, nonordinary profiles, targets where an item does not exist, compiler correctness, code generation, and binary/platform behavior. To close `load_word`, supply accepted claim-specific authority or compatibility evidence for both missing releases (or change the support contract); `COMPAT-COPY-180-182` cannot be reused. Re-audit on any source/signature/contract change, change to a required set or configuration scope, material authority change, or change in either accepted TCB entry or its disposition.

Final attestation: every in-scope soundness and documented-postcondition obligation has a regional status; every `PROVED` region has a complete derivation relative to the stated TCB; uncovered regions remain conspicuously `UNPROVED`.
