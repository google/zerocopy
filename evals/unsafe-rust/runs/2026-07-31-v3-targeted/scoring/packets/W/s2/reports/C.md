# Focused source-only audit of `classify`

## Claims and verdicts

| Claim | Exact theorem over `Required` | Verdict | Certificate |
|---|---|---|---|
| C-SOUND | Every valid safe call `classify(input)` is free from Rust undefined behavior. | **UNSOUND** | W0 below: the valid safe call with `input = 0` reaches `unreachable_unchecked`. |
| C-PANIC | Every call with `input = 0` panics. | **UNPROVED** | The only source path reaches UB. That execution cannot certify a behavioral contract refutation, and there is no UB-free witness. |
| C-RESULT | Whenever the call returns normally, its result equals `input`. | **CONTRACT-BROKEN** | W1 below: the UB-free call with `input = 1` normally returns `2`. |

The combined mandatory result is therefore not `PROVED`; its component results are **UNSOUND**, **UNPROVED**, and **CONTRACT-BROKEN**, respectively.

## Snapshot, scope, and domain closure

The artifact is the submitted `lib.rs`, SHA-256 `705278735813eeafd774bc4b032994b7727d5e6740c836f0f7236aa2fc06bde1`. Scope is its sole language-reachable API, safe public free function `pub fn classify(u8) -> u8`, including its internal unsafe call. There are no fields, traits, macros, generated artifacts, dependencies, callbacks, FFI, concurrency, allocators, or representation invariants in the submitted source.

Audit cutoff: 2026-08-01. The controlling request defines

`Required = {exact source} × {Rust compiler and standard library 1.80.0} × {targets where this exact source and the used item exist} × {ordinary debug, ordinary release} × {every valid u8 input}`.

The source contains no `cfg`, feature, target, or profile-dependent selection. Partition the input domain exactly by the exhaustive match patterns: `D0 = {0}`, `D1 = {1}`, and `D_ = {valid u8 values other than 0 and 1}`. Thus `Required = D0 ∪ D1 ∪ D_` for every required target/profile. The proofs below are parametric in target and profile: neither axis changes the selected source arm, and the submitted authoritative propositions expressly apply throughout that target/profile domain. This proves configuration coverage for each regional result; C-SOUND and C-RESULT are globally refuted by covered witnesses, while C-PANIC has the stated unresolved obligation on all of `D0`. No compilation or test evidence was used.

## Authority and TCB

TCB revision `TCB-classify-1` contains only the two requester-submitted Rust 1.80.0 axioms, independently opened and accepted for this review:

- **AXIOM-UU:** the Rust 1.80.0 standard-library Safety section says, “Reaching this function is *Undefined Behavior*.” It applies to `std::hint::unreachable_unchecked` over every required target/profile. [Official item documentation](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety).
- **AXIOM-SOUND:** the Rust 1.80.0 Reference says that if unsafe code “can be misused by safe code to exhibit undefined behavior, it is *unsound*.” It controls the source-level classification here. [Official UB chapter](https://doc.rust-lang.org/1.80.0/reference/behavior-considered-undefined.html).

All other premises below are direct control/value-flow facts from the exact source. No compiler-backend, binary, platform-implementation, tool, or dependency proposition is admitted.

## Obligation ledger and case proofs

| ID | Obligation | Case disposition |
|---|---|---|
| O-UNREACHABLE | A reached call to `unreachable_unchecked` must in fact be unreachable. | False on `D0`; the match selects that arm and execution reaches the call. The call is absent on `D1` and `D_`. |
| O-SOUND | No valid safe call may reach UB. | Refuted by W0. On `D1` and `D_`, the unsafe site is not reached; each arm directly returns a valid `u8`. |
| O-PANIC | On `D0`, the call must panic. | Unproved: the path reaches UB rather than a panic operation, but its UB prevents a `CONTRACT-BROKEN` certificate. |
| O-RESULT | On every UB-free normal return, result equals input. | Refuted by W1 on `D1`; proved locally on `D_` because that arm evaluates to `input`. `D0` supplies no UB-free normal-return witness. |

### W0: exact UB witness (`input = 0`)

1. `classify(0)` is well-typed safe use of a safe public function; it has no caller safety precondition.
2. Pattern `0` is selected. The local `marker` operations complete, then the unsafe call to `std::hint::unreachable_unchecked()` is reached.
3. Therefore the call's required proposition—its site is unreachable—is false.
4. AXIOM-UU entails UB, and AXIOM-SOUND classifies a safe API permitting this witness as unsound.

This complete witness establishes **UNSOUND** for C-SOUND on every required target/profile. It does **not** establish `CONTRACT-BROKEN` for C-PANIC: an execution containing UB cannot be the required UB-free behavioral counterexample, nor can its behavior after UB prove the panic guarantee.

### W1: exact defined contract witness (`input = 1`)

Pattern `1` is selected and directly evaluates to valid `u8` value `2`; the unsafe arm is not entered and no other UB-producing operation exists on this path. The call therefore returns normally and UB-free with `result = 2`, while `input = 1`. Since `2 != 1`, W1 establishes **CONTRACT-BROKEN** for C-RESULT. It does not establish unsoundness.

### Other inputs

For every valid `u8` other than `0` and `1`, the wildcard arm directly returns `input`. The unsafe site is unreachable on these calls, so this region is sound and satisfies C-RESULT. These regional proofs do not erase either existential witness.

## Findings and repairs

**F1 — implementation unsoundness and false proof comment.** The comment “This branch is assumed to be unreachable” neither derives the unsafe precondition nor states a true fact: `input = 0` makes the branch reachable. No replacement safety proof can validate the current operation. To meet C-PANIC, replace the unsafe call with an unconditional panic on that arm. Re-audit the changed source.

**F2 — normal-result contract defect.** Arm `1 => 2` contradicts the documented unchanged-result guarantee. Return `1`/`input`, or deliberately revise the public contract with compatibility review. This repair is independent of F1.

Residual scope excludes other Rust releases, targets where the source/item does not exist, nonordinary profiles, backend/binary correctness, and properties not requested. Re-audit on any source or documentation change, Rust/standard-library version change, support-domain expansion, or material change to either consumed official contract.
