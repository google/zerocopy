# Focused unsafe-Rust source review

## Claim, snapshot, and verdicts

Audited artifact: exact `lib.rs`, SHA-256
`705278735813eeafd774bc4b032994b7727d5e6740c836f0f7236aa2fc06bde1`.
Scope is the sole public safe function `classify(u8) -> u8` and its internal
unsafe call. This is a source-level review only; no compiler, backend, binary,
test, generated artifact, dependency, or prior audit is in scope. Audit cutoff:
2026-08-01. TCB: `TCB-R009-v1` below.

Let `C` be exactly: Rust and standard library 1.80.0, any target on which this
exact source and `std::hint::unreachable_unchecked` exist, and either ordinary
debug or ordinary release profile. `Required = C × {input | input: u8}`; every
such call is a valid safe use, with no caller-side safety precondition.

| Claim | Verdict | Certificate |
|---|---|---|
| Every valid safe call is free from Rust UB | **UNSOUND** | `classify(0)` reaches `unreachable_unchecked`; its Rust 1.80.0 contract makes reaching it UB. |
| If `input == 0`, the call panics | **UNPROVED** | The only source path reaches UB, so it cannot be a UB-free contract-refutation witness or establish a panic. |
| On normal return, the result equals `input` | **CONTRACT-BROKEN** | `classify(1)` has a UB-free normal return of `2`, and `2 != 1`. |

The combined mandatory result is therefore not `PROVED`.

## Boundary, cases, and obligation ledger

The complete language-reachable surface is the safe free function at lines
6–17. There are no public fields, types, constructors, trait implementations,
callbacks, macros, hidden APIs, dependencies, or invariant-bearing state. The
only unsafe obligation site is line 12.

The partition `{0} ∪ {1} ∪ {2..=255}` equals the complete `u8` input set:

- **Input 0.** A well-typed safe caller may invoke `classify(0)`. The `0`
  pattern selects lines 8–13; the two local assignments do not alter control
  flow, and line 12 is reached. Rust 1.80.0 documents: “Reaching this function
  is Undefined Behavior.” Thus the required safety proposition at line 12
  (“this call site is unreachable”) is false, and the documented consequence
  is UB. This completes the existential `UNSOUND` certificate in every `C`.
  The same execution cannot establish `CONTRACT-BROKEN` for the panic promise:
  it contains UB as a whole. No separate UB-free zero-input execution or panic
  derivation exists in the inspected source, so that promise is `UNPROVED`.
  Likewise, this execution supplies no normal-return result witness.
- **Input 1.** Line 14 returns `2` without executing the unsafe site. This is a
  UB-free normal return, but the input is `1`; it therefore completes the
  existential `CONTRACT-BROKEN` certificate for the unchanged-result promise.
  It is not a soundness counterexample and the zero-input promise is
  inapplicable.
- **Inputs 2 through 255.** Line 15 returns the input itself and the unsafe site
  is not executed. These calls are UB-free and satisfy the normal-return
  promise. The zero-input promise is inapplicable.

| ID | Exact obligation | Status |
|---|---|---|
| O-S0 | Safe `classify(0)` must not reach UB | **UNSOUND**, witness above |
| O-SNZ | Safe calls for `1..=255` must avoid UB | **PROVED**, exhaustive nonzero branches above |
| O-P0 | `classify(0)` must panic | **UNPROVED**, UB occurs with no panic proof |
| O-R0 | Result clause for input 0, if normally returning | No UB-free normal-return instance established; not a refutation witness |
| O-R1 | A normal return for input 1 must equal 1 | **CONTRACT-BROKEN**, UB-free result 2 |
| O-RN | Normal returns for `2..=255` equal their inputs | **PROVED** |

## Domain and configuration closure

The request's predicate is retained verbatim as `C`; no version interval was
invented. The source contains no `cfg`, feature selection, generated code,
arithmetic, debug assertion, allocation, FFI, target feature, or panic-mode
branch. Target and profile therefore do not change the match partition or
dataflow. Both consumed Rust pages are versioned 1.80.0 and their relevant
propositions have no narrower target/profile qualification. The proofs and
witnesses above are consequently parametric over all `C`; debug/release and
optimization do not rescue a source-level UB execution. Thus every required
configuration is covered by the case analysis. There are no enforced or
report-only exclusions and no uncovered configuration remainder.

## TCB-R009-v1

| ID | Accepted Rust 1.80.0 proposition | Scope and consumer |
|---|---|---|
| AXIOM-UU | [`unreachable_unchecked` Safety](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety): “Reaching this function is Undefined Behavior.” | Every `C`; O-S0 |
| AXIOM-UB | [Reference: behavior considered undefined](https://doc.rust-lang.org/1.80.0/reference/behavior-considered-undefined.html): safe-client-triggerable UB makes unsafe code unsound; `unsafe` does not permit UB. | Every `C`; soundness classification |

Both exact URLs were opened and their wording, version, and applicability were
verified. They are accepted as versioned Rust authorities under the audit trust
policy. No additional assumption, tool-derived fact, implementation premise,
or safe/unsafe dependency is consumed. This does not claim binary-level
compiler correctness.

## Findings and resolution

**F-1 — implementation unsound; proof comment false.** The line-11 comment
merely assumes the exact property the callee requires and is contradicted by
the dominating `0` match arm. A stronger comment cannot repair the code.
Replace the zero arm's unsafe call with an operation that actually panics (for
example `panic!`) and freshly audit the edited artifact.

**F-2 — normal-return contract broken.** Line 14 must return `input` (therefore
`1`) if the documented guarantee is retained. This UB-free witness is
independent of F-1.

There is no authoritative-documentation gap. Re-audit on any source or contract
change, Rust/standard-library version change, support-domain expansion, or
material change to either consumed authority. Every in-scope obligation and
each distinct input region has a disposition; no test result or absence of a
counterexample supports a verdict.
