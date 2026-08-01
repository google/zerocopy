Adjudication against only `z6b1`:

- Confirmed — applicability: [`Cargo.toml`](/tmp/unsafe-rust-legacy-20260731.53beM9/z6b1/Cargo.toml:30) supports Rust 1.56. Later documentation does not by itself establish an older compiler contract. This is decisive for the zero representation of NPO `Option`s: the [1.56 Option contract](https://doc.rust-lang.org/1.56.0/std/option/index.html#representation) lacks the zero-byte guarantee added in [1.89](https://doc.rust-lang.org/1.89.0/core/option/index.html#representation). Thus the 1.56–1.88 `FromZeros`/zero-only validators at [`impls.rs:310`](/tmp/unsafe-rust-legacy-20260731.53beM9/z6b1/src/impls.rs:310) are unproved. `b1z6` is correct; `t4c9` incorrectly applies 1.89 globally.

- Overclaim — primitives: the 1.81 citation is inapplicable to 1.56, but `b1z6` goes too far in declaring all stable numerics unresolved. Exact-1.56 total safe conversions such as integer `from_ne_bytes` and `f32`/`f64::from_bits`, combined with fixed sizes/representations, reconstruct all-initialized-pattern validity and absence of padding. The unstable `f16`/`f128` case remains unproved by the cited 1.81 text.

- Ambiguous/unresolved — atomics: the earliest admitted version’s “same in-memory representation” wording is plausibly intended to transfer representation, but neither report supplies a version-1.60 derivation of the exact equal-bit-validity proposition. Later explicit atomic wording cannot simply be projected backward. `b1z6` is defensible in withholding proof, but this is an ambiguity/proof-closure issue, not evidence of unsoundness.

- Confirmed — literal contract: [`HasField`](/tmp/unsafe-rust-legacy-20260731.53beM9/z6b1/src/lib.rs:1214) requires `Field` to have the same visibility as the represented field. The implementation declares a `pub` marker while expressly admitting `ManuallyDrop`’s field is not literally public ([`impls.rs:751`](/tmp/unsafe-rust-legacy-20260731.53beM9/z6b1/src/impls.rs:751)). “Effectively public” methods do not satisfy that clause, and the private field name is not a stable public contract. `b1z6` is correct; `t4c9`’s approval is false.

- False positive — indirect `Immutable` proofs: `Option<fn(...)>` and `NonNull<T>` are `Copy`; exact-version `Copy` rules require every contained component to be `Copy`, while `UnsafeCell` is not `Copy`. Together with this crate’s stated sufficient condition for `Immutable`, that closes both impls. `b1z6` wrongly leaves them unproved. `t4c9` reaches the right result but does not show this proof chain.

- Confirmed — `Box<T>: Immutable`: the source itself admits the official proof is incomplete and relies on UCG consensus ([`impls.rs:297`](/tmp/unsafe-rust-legacy-20260731.53beM9/z6b1/src/impls.rs:297)). Official pointer-layout facts do not exclude a semantically interior-mutable private representation. `b1z6` is correct; `t4c9`’s blanket “outside SIMD” approval is unsupported.

- Confirmed — SIMD: [`impls.rs:1226`](/tmp/unsafe-rust-legacy-20260731.53beM9/z6b1/src/impls.rs:1226) explicitly relies on UCG text that says it is not guaranteed. Both reports correctly identify a universal configuration-closure gap. Some later type-specific guarantees or AArch64 `repr(C)` aggregates narrow the gap, but do not prove every emitted family across Rust 1.56+.

- Confirmed — `KnownLayout`: [`impl_known_layout!`](/tmp/unsafe-rust-legacy-20260731.53beM9/z6b1/src/util/macros.rs:461) promises that `NonNull::cast` preserves provenance while recording a FIXME for that documentation. The 1.56+ exact “same provenance” postcondition is not visibly closed. `b1z6` is correct; `t4c9` misses it.

- Confirmed, test-only — [`assume_initialized`](/tmp/unsafe-rust-legacy-20260731.53beM9/z6b1/src/impls.rs:1798): the stated generic proof is invalid because a valid non-`IntoBytes` value may have uninitialized padding. No concrete failing finite instantiation was established, so this is an unproved `cfg(test)` obligation, not a demonstrated production UB. `b1z6` classifies it correctly.

- Confirmed latent issue — transmute macro: [`TransmuteFrom`](/tmp/unsafe-rust-legacy-20260731.53beM9/z6b1/src/pointer/transmute.rs:287) explicitly provides no guarantee for unequal referent sizes, while [`impl_for_transmute_from!`](/tmp/unsafe-rust-legacy-20260731.53beM9/z6b1/src/util/macros.rs:169) checks only reciprocal `TransmuteFrom` bounds. `t4c9` is correct that the macro’s “safe to call” claim omits size equality. All visible current invocations independently pair equal-size representations, so this is latent, not a current emitted-impl defect.

- Incomplete scope: `t4c9` says it audited `c9t4`, not `z6b1`; its target-wide bottom line is therefore non-transferable. The fixture also omits declared derive/path dependencies, so neither report can prove whole-crate/derive closure.

Hypothesis result, on report-visible evidence:

- Applicability: **passes for `b1z6`**, though its primitive conclusion overreaches.
- Literal contract closure: **passes for `b1z6`**.
- Indirect multi-premise proof: **fails**; `b1z6` produces false positives, while `t4c9` gives no visible Copy/UnsafeCell derivation.
- Visible reconstructed proof: **fails overall**; neither report visibly closes every accepted family. `t4c9` is especially conclusory and also targets the wrong fixture.
