# Unsafe Rust source audit: conflicting-policy snapshot

## Claim and verdict

For the exact supplied `Cargo.toml`, policies, `TCB.md`, and `src/lib.rs`, let
`V={1.84.0,1.85.0,1.86.0}`, `T={X,A,W}` as defined by the policies, and let
`f`/`h` denote `turbo`/`hardened`. Define the conservative **audit envelope**

```text
E(v,t,f,h) = v in V and t in T and not(f and t=W).
```

`E` includes both feature states, every Cargo profile, and both debug-assertion
states. It is an audit domain, not a newly selected support policy.

- **Rust soundness: PROVED over E**, relative to the TCB below: every well-typed
  safe call of the selected `value_or_zero` is free of Rust undefined behavior.
- **Documented postcondition: PROVED over E**: the result is the contained byte
  for `Some(byte)`, and zero for `None`.
- **Effective rejection: PROVED** for every `(v,W,true,h)` in the common axes:
  compilation fails, so no library artifact from that configuration enters the
  execution theorem.
- **Combined mandatory result: PROVED over E, relative to BUILD-MAP-C and the
  version-matched Rust axioms below.** No `UNSOUND` or `CONTRACT-BROKEN` witness
  is established.
- **Exact project support predicate: UNPROVED.** Scarlet and Indigo each says
  “exactly” but selects a different set, and no resolution is authorized. This
  governance ambiguity does not block the stronger source theorem: both
  Scarlet and Indigo are subsets of `E` because both exclude `turbo` on `W`.

This is a source-level Rust-abstract-semantics result, not a compiler-backend,
binary, platform, or security claim.

## Snapshot, boundaries, and coverage

The crate is edition 2021, `#![no_std]`, declares Rust 1.84 as `rust-version`,
has no dependencies, and has only the two named empty features. No generated
artifacts, build scripts, FFI, assembly, concurrency, allocation, traits,
fields, representation invariants, hidden items, or macros generating public
API exist in the supplied target.

The complete language-reachable API surface is one safe public free function,
`value_or_zero(Option<u8>) -> u8`, with mutually exclusive non-`turbo`
(`src/lib.rs:7-10`) and `turbo` (`:13-21`) definitions and the same documented
contract. The sole unsafe operation is `Option::unwrap_unchecked` at line 20.
The crate-level `compile_error!` at lines 3-4 is the only target-dependent
obligation. There is no unsafe caller-facing contract and no persistent state
or invariant inventory.

No build, execution, test, or macro expansion was used. Profiles, debug
assertions, and `hardened` do not occur in source selection or computation, so
the proof is parametric over them.

## Authoritative premises and TCB audit log

The following version-matched pages were opened and checked; no compatibility
extrapolation is used.

- **AXIOM-OPTION-{184,185,186}.** For each exact version, `is_none` “Returns
  `true` if the option is a `None` value”; `unwrap_unchecked` returns the
  contained `Some` value and calling it on `None` is undefined behavior;
  `unwrap_or` returns the contained `Some` value or its provided default:
  [1.84 is_none](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none),
  [unchecked](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked),
  [or](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or);
  [1.85 is_none](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.is_none),
  [unchecked](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked),
  [or](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or);
  [1.86 is_none](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.is_none),
  [unchecked](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked),
  [or](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or).
- **AXIOM-CFG-{184,185,186}.** A configuration option is true exactly when set;
  `all` is true when all operands are true; `not` negates; a false `cfg`
  predicate removes its item and a true predicate includes it:
  [1.84 predicates](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#conditional-compilation),
  [attribute](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute);
  [1.85 predicates](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#conditional-compilation),
  [attribute](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute);
  [1.86 predicates](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#conditional-compilation),
  [attribute](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute).
- **AXIOM-COMPILE-{184,185,186}.** `compile_error!` “Causes compilation to fail
  with the given error message when encountered”: [1.84](https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html),
  [1.85](https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html),
  [1.86](https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html).
- **BUILD-MAP-C — ACCEPTED HUMAN TRUST DECISION, CONSPICUOUS TCB.** For exactly
  the bundled Cargo releases for Rust 1.84.0/1.85.0/1.86.0, the supplied
  manifest/source, every supported Cargo profile, the two named features, and
  targets X/A/W, Cargo maps feature enablement and target triples to the source
  `cfg` predicates exactly as stated in `TCB.md`. It is consumed only by branch
  reachability and rejection proofs. It supplies no Rust semantic,
  implementation, compatibility, backend, or binary-correctness premise.

The Rust entries are authoritative axioms requested for this audit;
BUILD-MAP-C is the only additional admitted premise. Re-audit is required on
any identity, source, cfg, feature, target, version, disposition, or consumed
documentation change.

## Obligation ledger and derivations

| ID | Obligation and complete derivation | Status |
|---|---|---|
| CFG-1 | If `f` and `t=W`, BUILD-MAP-C makes both operands of line 3's `all` true; AXIOM-CFG includes `compile_error!`; AXIOM-COMPILE makes compilation fail. Otherwise that item is removed. | PROVED |
| CFG-2 | BUILD-MAP-C plus AXIOM-CFG makes exactly one function definition present: `not(feature="turbo")` when `!f`, and `feature="turbo"` when `f`. | PROVED |
| SAFE-1 | With `!f`, `unwrap_or(0)` is safe and AXIOM-OPTION returns the contained byte or the supplied zero. | PROVED |
| UNSAFE-1 | With `f`, `is_none()==true` returns zero. Reaching line 20 means the immediately preceding result was false. AXIOM-OPTION says `None` implies true, so contraposition gives “not `None`.” No operation intervenes or mutates the owned `Option<u8>`. Thus the call is not in `unwrap_unchecked`'s documented UB case, and its postcondition yields the contained byte. | PROVED |
| API-1 | `None` and non-`None` paths exhaust every safe `Option<u8>` input; SAFE-1/UNSAFE-1 cover the cfg partition, all three exact version axioms agree, and other supported axes are computation-independent. | PROVED |

## Findings and residual scope

**F-1 — support-policy identity (`UNPROVED`, governance only).** The two exact
predicates conflict. Minimum resolution: an authorized precedence,
supersession, or replacement policy. A resolution contained in `E` needs no
new implementation proof; expanding beyond `E` requires fresh coverage.

**F-2 — local proof comment deficient; implementation proved.** Line 19 does
not name `is_none`'s contract, the contraposition, preservation of `value`, or
the exact unsafe precondition. Proposed replacement:

```rust
// SAFETY: `is_none` returns true for `None`. Reaching here means that result
// was false; by contraposition `value` is not `None`, and no mutation intervened.
// Therefore `unwrap_unchecked` is not called on its documented UB case and
// returns the contained byte.
```

No authoritative-documentation gap, tool-derived evidence, prior audit, or
additional robustness claim is in scope. Unsupported versions, other targets,
custom toolchains, and binary/backend correctness remain excluded.
