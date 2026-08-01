# Unsafe Rust source audit: supplied `conflicting-domain-target` snapshot

## Claim and verdict

**Combined mandatory result: PROVED.** For every well-typed safe call to
`value_or_zero` in every configuration in `Required` below, the supplied source
is free of Rust undefined behavior and returns the contained byte for `Some(b)`
and zero for `None`. This is a source-level theorem for Rust/stdlib 1.84.0,
1.85.0, and 1.86.0, relative only to accepted `BUILD-MAP-C`; it is not a
backend/binary theorem. The soundness claim and the documented postcondition
are each **PROVED**. No `UNSOUND`, `CONTRACT-BROKEN`, or unresolved mandatory
obligation was found.

Snapshot: the supplied `Cargo.toml`, `src/lib.rs`, two policies, `TCB.md`, and
request; edition 2021, `#![no_std]`, no dependencies, build scripts, generated
code, or prior audit. No build, execution, expansion, or test evidence was used.
Audit cutoff: this supplied snapshot and its three exact releases.

## Domain recovery and closure

Let `V={1.84.0,1.85.0,1.86.0}`, `T={X,A,W}` as defined by the policies, and
`f,h` range over Booleans. Preserve the controlling expressions literally:

```text
S = v∈V ∧ t∈T ∧ [¬f ∨ (f∧t=X∧(¬h∨v≥1.85.0)) ∨ (f∧t=A∧h)]
I = v∈V ∧ t∈T ∧ [¬f ∨ (f∧t=X∧(h∨v≥1.86.0))
                  ∨ (f∧t=A∧¬h∧v≥1.85.0)]
Required = (S ∨ I) ∧ p∈CargoProfiles ∧ d∈{false,true}
```

`S` and `I` are Scarlet and Indigo respectively. Because both are current and
no precedence is authorized, `S ∪ I` is used only as a conservative audit
domain: `S⊆S∪I` and `I⊆S∪I` by union introduction. This does **not** resolve or
restate the project's support promise.

Define
`Covered = v∈V ∧ t∈T ∧ f,h∈Bool ∧ p∈CargoProfiles ∧ d∈Bool ∧ ¬(f∧t=W)`.
Each `f` clause of both policies names only `X` or `A`, while each `¬f` clause
has `f=false`; hence `Required⊆Covered`. The implementation proof below is
parametric over all of `Covered`, so policy overlap and disagreement need not
be enumerated. `h`, profile, and debug-assertion state select no source and
affect no proof premise.

For all three releases, the Reference says `cfg` conditionally includes its
attached construct according to its predicate and defines `all` as conjunction
([1.84](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#conditional-compilation),
[1.85](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#conditional-compilation),
[1.86](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#conditional-compilation);
[cfg attribute 1.84](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute),
[1.85](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute),
[1.86](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute)).
The versioned macro docs state that `compile_error!` causes compilation to fail
with its message when encountered ([1.84](https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html),
[1.85](https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html),
[1.86](https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html)). With
`BUILD-MAP-C`, `f∧t=W` therefore includes lines 3–4 and cannot produce a library
artifact. This is effective rejection, not an audit-only exclusion. Both
policies already exclude that region. On every remaining case, the complementary
`cfg(feature="turbo")`/`cfg(not(...))` attributes include exactly one function.

## Boundary, invariant, and obligation ledger

The complete crate-owned reachable surface is one safe free function,
`value_or_zero(Option<u8>) -> u8`, with two configuration-selected bodies.
There are no public fields/types, unsafe APIs/traits/impls, callbacks, statics,
FFI, macros exported by the crate, hidden APIs, custom drop behavior, or
invariant-bearing representation.

The only local invariant is `INV-SOME`: after the `is_none()` branch falls
through at lines 15–17, `value` is not `None`, and this remains true until it is
immediately consumed at line 20. The check/branch produces it; there is no
intervening mutation, call, callback, unwind point, or alias; `unwrap_unchecked`
consumes it.

Version-matched std contracts are identical here: `is_none` “Returns `true` if
the option is a `None` value” ([1.84](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none),
[1.85](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.is_none),
[1.86](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.is_none));
`unwrap_unchecked` returns the contained `Some` value and calling it on `None`
is undefined behavior ([1.84](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked),
[1.85](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked),
[1.86](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked));
and `unwrap_or` returns the contained `Some` value or the supplied default
([1.84](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or),
[1.85](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or),
[1.86](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or)).

- **OBL-CFG — PROVED:** the partition and rejection are established above.
- **OBL-NORMAL — PROVED:** for `¬f`, `unwrap_or(0)` is a safe call and its
  contract gives `Some(b)→b`, `None→0`.
- **OBL-UNSAFE — PROVED:** for `f`, `is_none()==true` returns zero. Fallthrough
  means the same value is not `None`, establishing the exact precondition at
  `unwrap_unchecked`; the call returns the contained byte.
- **OBL-API/POST — PROVED:** the two input cases and two exhaustive feature
  cases establish safe-API soundness with no caller precondition and establish
  the documented result. Their proof is independent of every remaining axis,
  giving aggregate `Covered` and the closure `Required⊆Covered`.

## TCB audit log

**`BUILD-MAP-C` (accepted human premise, conspicuous and sole additional
assumption):** for the three exact bundled Cargo releases, supplied manifest,
named targets, all supported profiles, and this library compilation, feature
enablement maps exactly to the corresponding feature `cfg`, and `X/A/W` map to
`target_arch=x86_64/aarch64/wasm32`. It is consumed only by OBL-CFG. It admits no
Rust semantics, branch correctness, other versions, or backend correctness.
Re-audit on any identity, manifest/source-cfg, feature/target, or disposition
change. The versioned Reference/std propositions quoted above are authoritative
Rust axioms, not expanded build-tool trust. No other TCB entry is consumed.

## Finding: deficient adjacent proof artifact

Implementation status remains **PROVED**, but the line 19 comment compresses
the material bridge from the exact `is_none` result through fallthrough to the
unsafe precondition and supplies no contract citation. Suggested replacement:

```rust
// SAFETY: `Option::is_none` returns true exactly for `None`. Reaching this
// point means that check returned false for this unchanged `value`, so this
// `unwrap_unchecked` call is not on `None` and returns its contained byte.
```

This is a proof-documentation repair only, not a hidden caller condition or a
current implementation defect.

## Residual scope and triggers

Excluded: compiler/backend/linker/binary correctness, toolchains outside `V`,
targets outside `T`, unstable/custom-toolchain behavior, and behavior of the
intentionally rejected `f∧t=W` non-artifact. Re-audit on source, manifest,
policy or conflict-resolution changes; expansion of versions/targets/features;
changes to any cited contract or `BUILD-MAP-C`; or introduction of generated
code, dependencies, unsafe operations, or new public surfaces.

No independent reviewer participated. All in-scope surfaces, obligations,
postconditions, domain transformations, exclusions, and consumed premises have
the dispositions above.
