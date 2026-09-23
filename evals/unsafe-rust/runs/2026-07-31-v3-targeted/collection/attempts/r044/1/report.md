# Focused unsafe-Rust source review

## Claims, scope, and verdicts

**Snapshot.** The artifact is exactly the inspected `target/lib.rs`; `REQUEST.md` and `EVIDENCE.md` control scope and evidence. No repository, generated output, dependencies, manifests, expansions, or build artifacts were inspected or assumed. This was a source-only review: nothing was built, tested, executed, or edited. Audit date: 2026-08-01. Skill identity: the submitted `unsafe-rust` package, with no revision identifier supplied.

Let `T` be every target on which this exact source and Rust 1.80.0's `std::hint::unreachable_unchecked` exist. The exact required configuration domain is

`D = {exact lib.rs} × {Rust and std 1.80.0} × T × {ordinary debug, ordinary release}`,

and inputs are all `u8` values. This preserves the request's symbolic target predicate; no finite target inventory is inferred. Valid use means every well-typed safe call to the public safe function, with no hidden caller obligation.

| Claim | Exact theorem over `D` | Verdict |
|---|---|---|
| `SOUND` | For every input and every permitted execution of `classify(input)`, the execution is free from Rust undefined behavior. | **UNSOUND** (`F-UB-0`) |
| `PANIC-0` | Every valid call `classify(0)` panics. | **UNPROVED** (`F-PANIC-0`) |
| `RETURN` | Whenever `classify(input)` returns normally, its result equals `input`. | **CONTRACT-BROKEN** (`F-RETURN-1`) |

The combined mandatory result is therefore not proved. These verdicts are source-level Rust results, not claims about a compiler backend or binary.

## Boundary and obligation inventory

The complete language-reachable API surface in the supplied source is the safe public free function `classify(u8) -> u8` (`lib.rs:6-17`) and its two documented guarantees (`lib.rs:3-5`). There are no exposed fields, constructors, types, traits or impls, macros, reexports, hidden items, callbacks, FFI, statics, operators, or generated APIs. The sole unsafe obligation site is `unreachable_unchecked` at line 12. The local `marker` assignments neither exit nor establish an invariant.

The callee's exact safety requirement is that its site not be reached. No invariant owns or establishes that proposition. Instead, source control flow gives this exhaustive input partition:

| Input | Soundness | Zero-panic guarantee | Normal-return guarantee |
|---|---|---|---|
| `0` | **UNSOUND**: reaches the unsafe call. | **UNPROVED**: the same UB-containing execution is not a contract-refutation witness. | **UNPROVED for this case**: UB prevents a postcondition certificate or UB-free refutation. |
| `1` | **PROVED for this case**: branch returns the valid `u8` literal `2`; no unsafe site is reached. | Not applicable; antecedent `input == 0` is false. | **CONTRACT-BROKEN**: normal result `2 != 1`. |
| `2..=255` | **PROVED for this case**: `_` returns the valid input and no unsafe site is reached. | Not applicable. | **PROVED for this case**: the returned expression is exactly `input`. |

This partition is exhaustive because `u8` values are `0`, `1`, or `2..=255`. It is parametric over `T` and both profiles: the source has no `cfg`, profile-dependent assertion, arithmetic, allocation, panic-mode branch, target feature, generated code, or target-dependent operation. Thus the regional affirmative proofs cover all of `D` for their stated input regions. Claim-level `SOUND` is refuted by the `0` region; `PANIC-0` has no covered proof region; `RETURN` is independently refuted by the `1` region.

## Proof certificates and findings

### `F-UB-0` — reachable `unreachable_unchecked`

- **Valid in-scope use:** `classify(0)` is a call to a safe public function with a valid `u8`; it has no caller safety precondition.
- **Reachability:** matching `0` selects the first arm. The two `marker` statements complete, and evaluation reaches line 12 on every configuration in `D`.
- **False safety proposition:** the call site must be unreachable, but the preceding derivation proves it reachable.
- **UB consequence:** Rust 1.80.0 documents: “Reaching this function is Undefined Behavior.” ([standard-library Safety section](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety)). The Rust 1.80.0 Reference explains that unsafe code triggerable by safe code to exhibit UB is unsound ([UB chapter](https://doc.rust-lang.org/1.80.0/reference/behavior-considered-undefined.html)).

All existential links are established, so this witness proves `SOUND` **UNSOUND**. The existing comment merely assumes the negation of demonstrated control flow; its proof-artifact classification is deficient and its implementation classification is unsound. Minimum repair: make the zero arm perform a defined panic, not `unreachable_unchecked`.

### `F-PANIC-0` — UB is not a panic-contract witness

The exact candidate is `classify(0)`, but its execution reaches UB. A whole execution containing UB may establish unsoundness; it cannot establish `CONTRACT-BROKEN`, which requires a valid UB-free execution falsifying the postcondition. No independent UB-free zero-input execution or proof that zero input panics exists in the inspected source. Therefore the panic guarantee is **UNPROVED**, not `CONTRACT-BROKEN`. Replacing line 12 with a defined panic would establish it.

### `F-RETURN-1` — wrong defined normal result

`classify(1)` is a valid safe call. The `1 => 2` arm returns normally without reaching any unsafe operation, so the whole witness is UB-free. Its result is `2`, while the documented result is the unchanged input `1`. This complete witness proves `RETURN` **CONTRACT-BROKEN** over every configuration in `D`. It proves no unsoundness. Minimum repair: return `input` (or `1`) from this arm.

## TCB audit log (`TCB-1`)

| ID | Category and exact proposition | Identity/scope | Disposition; consumers |
|---|---|---|---|
| `AX-UU` | Rust axiom: reaching `unreachable_unchecked` is UB. | Linked Rust 1.80.0 std page; all `D` per supplied applicability statement. | Accepted after direct verification; `F-UB-0`. |
| `AX-SOUND` | Rust axiom: unsafe code that safe code can trigger to exhibit UB is unsound. | Linked Rust 1.80.0 Reference; all `D` per supplied applicability statement. | Accepted after direct verification; `SOUND`. |

No dependency, implementation, tool, environment, probabilistic, or compiler-backend premise is consumed. The exact supplied proposition that both pages apply throughout `D` is accepted as the task's scope premise. Re-audit is required if source/docs, Rust or std version, target/item-existence predicate, profile set, or either consumed authority changes. Binary behavior, other toolchains/profiles, and targets outside `T` remain excluded. No authoritative-documentation or skill-guidance gap blocked these conclusions.

**Attestation:** every in-scope surface, input case, unsafe obligation, requested postcondition, configuration axis, premise, negative certificate, and residual exclusion has a disposition above. No test result or absence of a counterexample is used.
