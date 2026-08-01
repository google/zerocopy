# Focused unsafe-Rust audit: `classify`

## Claims and verdicts

This review covers the exact `lib.rs` identified below, compiled with Rust and standard library 1.80.0, on every target where that source and `std::hint::unreachable_unchecked` exist, in every ordinary debug or release profile. A valid use is any well-typed safe call `classify(input)` for a valid `u8`; there is no caller safety precondition.

1. **Freedom from undefined behavior for every valid safe call: `UNSOUND`.** The valid safe call `classify(0u8)` reaches `unreachable_unchecked`, which Rust 1.80.0 defines as UB.
2. **If `input == 0`, the call panics: `UNPROVED`.** The only source path for zero contains UB. That UB-containing execution proves unsoundness, but cannot establish a UB-free nonpanic witness and therefore cannot establish `CONTRACT-BROKEN`.
3. **On normal return, the result equals `input`: `CONTRACT-BROKEN`.** The independent, UB-free call `classify(1u8)` normally returns `2u8`, not `1u8`.

The combined mandatory claim is not proved: it has the component results `UNSOUND`, `UNPROVED`, and `CONTRACT-BROKEN` above. These results hold throughout the supported configuration set, relative to TCB `TCB-R1`.

## Snapshot, boundary, and configuration closure

- Source: `target/lib.rs`, SHA-256 `705278735813eeafd774bc4b032994b7727d5e6740c836f0f7236aa2fc06bde1`.
- Scope: the sole language-reachable safe surface, public safe free function `pub fn classify(u8) -> u8`, and its sole unsafe obligation site, the zero arm's call to `unreachable_unchecked`.
- No fields, constructors, traits/impls, callbacks, macros, generated artifacts, FFI, dependencies other than the named standard-library item, concurrency, allocation, or configuration attributes appear in the supplied source.
- Supported predicate: exactly Rust/stdlib 1.80.0; any target on which the exact source and item exist; ordinary debug or release. Target and profile do not select different source. The submitted authority states that both axioms below cover this domain. The proof partitions all valid `u8` inputs into `0`, `1`, and `2..=255`; the same control flow and contracts apply parametrically on every supported target/profile. No build or test evidence was used.

## TCB-R1 audit log

Both entries are `AXIOM`s, accepted for this review because `EVIDENCE.md` selected these exact versioned Rust authorities and their wording and applicability were directly verified. They have no dependency, implementation, tool, external-specification, deployment, or probabilistic trust extension.

- **AXIOM-UU.** Rust 1.80.0 documents: “Reaching this function is *Undefined Behavior*.” [Standard-library Safety contract](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety). Scope: the submitted supported predicate. Consumer: `OBL-UU`. Re-audit on source, version, supported-domain, item-contract, or applicability change.
- **AXIOM-SOUND.** Rust 1.80.0 says unsafe code that safe code can misuse to exhibit UB “is *unsound*,” and that unsafe does not permit UB. [Reference UB chapter](https://doc.rust-lang.org/1.80.0/reference/behavior-considered-undefined.html). Scope: Rust 1.80.0 source semantics. Consumer: `OBL-SOUND`. Same re-audit triggers.

TCB disposition: accepted and complete for the propositions consumed here. This is a source-level result, not a theorem about any compiler backend or produced binary.

## Invariant and obligation ledger

| ID | Exact proposition and derivation | Status |
|---|---|---|
| `INV-UNREACHABLE` | The safety comment claims the zero branch is unreachable. It has no producer or enforcement boundary; `match input` selects that branch exactly when the safe caller supplies zero. | **REFUTED** |
| `OBL-UU` | Calling `unreachable_unchecked` requires that execution not reach it. For `input = 0`, evaluation selects the first arm, evaluates the harmless local assignments, then reaches the call. By `AXIOM-UU`, that execution has UB. | **UNSOUND** |
| `OBL-SOUND` | Every valid safe call must be UB-free. The in-scope witness `classify(0u8)` satisfies all safe-API conditions and reaches the UB in `OBL-UU`; by `AXIOM-SOUND`, it refutes the universal theorem. | **UNSOUND** |
| `OBL-PANIC-0` | For zero, the documented outcome is panic. The source instead reaches UB. Because the execution as a whole contains UB, it supplies no defined behavioral observation and cannot be the required UB-free postcondition refutation. No independent UB-free zero execution is established. | **UNPROVED** |
| `OBL-RETURN` | For `1`, the second arm normally returns literal `2`; it executes no unsafe operation. Thus `classify(1u8) == 2u8 != 1u8` is a valid UB-free witness. For every `2..=255`, `_ => input` normally returns the input and executes no unsafe operation. For zero, UB prevents a behavioral conclusion. | Overall **CONTRACT-BROKEN**; regional results: `1` **CONTRACT-BROKEN**, `2..=255` **PROVED**, `0` **UNPROVED** |

The three input regions are disjoint and exhaustive, so this ledger covers every valid safe call. The zero-only panic condition is inapplicable for the other two regions.

## Findings and minimum resolutions

**F-1 — reachable `unreachable_unchecked` (`UNSOUND`).** The existing comment merely assumes the exact fact it must prove, and source control flow falsifies it. The zero witness establishes only unsoundness; it does not also establish a broken panic guarantee. Minimum resolution: replace the unsafe call with an actual panic-producing safe path and replace the false safety comment; then audit the changed snapshot.

**F-2 — wrong normal result for one (`CONTRACT-BROKEN`).** `classify(1u8)` is the separate UB-free witness establishing this theorem. Minimum resolution: make the `1` arm return `1`/`input`, or deliberately change the public contract with compatibility analysis, then re-audit.

## Residual scope and attestation

Excluded: binary/backend correctness and behavior outside the supplied file and three requested claims. No design change was implemented, and no target was built, tested, executed, or expanded. There are no authoritative-documentation or skill-guidance gaps needed to decide these claims. Re-audit on changes to source or documentation, Rust/stdlib version, supported targets/profiles, generated inputs, dependencies, or either consumed authority.

Every in-scope API, unsafe site, input region, requested postcondition, configuration class, and consumed TCB proposition has a stated disposition. Auditor: source-review agent; date: 2026-08-01. Independent review: not performed.
