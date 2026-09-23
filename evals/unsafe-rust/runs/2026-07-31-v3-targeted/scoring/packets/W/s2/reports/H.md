# Focused unsafe-Rust source review

## Claim, snapshot, and verdicts

Audited artifact: target/lib.rs, SHA-256
705278735813eeafd774bc4b032994b7727d5e6740c836f0f7236aa2fc06bde1.
The only API in scope is the public safe free function classify at lib.rs:6–17.
The audit is source-only; no build, execution, test, expansion, or source change
was performed.

Supported(configuration) means: this exact source; Rust compiler and standard
library 1.80.0; every target on which this source and
std::hint::unreachable_unchecked exist; and either ordinary debug or release
profile. The claims quantify over every u8 input to a well-typed safe call.

1. **Freedom from undefined behavior: UNSOUND.** The valid safe call
   classify(0) reaches undefined behavior.
2. **Input-zero panic guarantee: UNPROVED.** The zero-input execution contains
   UB. It therefore cannot prove the documented panic, and that same execution
   cannot serve as a UB-free witness for CONTRACT-BROKEN.
3. **Normal-return result guarantee: CONTRACT-BROKEN.** The independent,
   UB-free call classify(1) returns 2, not its input 1.

The combined mandatory result is therefore not PROVED. These verdicts are
source-level Rust conclusions relative to TCB-C1 below; they make no claim that
a particular compiler backend emits a correct binary.

## Contracts and complete API boundary

- SND: every valid safe call is free of Rust UB.
- PANIC: when input equals 0, the call panics.
- RESULT: on normal return with value r, r equals input.

classify is the complete language-reachable boundary: there are no public
fields, types, constructors, methods, trait implementations, macros, hidden
items, callbacks, FFI surfaces, dependencies, or generated artifacts. The only
unsafe obligation site is lib.rs:12. No representation invariant exists. Its
local precondition is that control must not reach
std::hint::unreachable_unchecked.

## Exhaustive derivation and witness classification

The match at lib.rs:7 partitions all u8 inputs into disjoint, exhaustive cases.
The proof is parametric over every supported target and both profiles because
there is no conditional compilation, target-dependent operation, checked
arithmetic, debug assertion, allocation, panic-mode-dependent cleanup, or
generated code.

| Input | Source path | Whole-execution result | Obligations |
|---|---|---|---|
| 0 | The 0 arm at line 8 performs two ordinary local operations, then necessarily calls the intrinsic at line 12. | Reaching that call is UB by AXIOM-UU. | Refutes SND and establishes UNSOUND. It does not establish CONTRACT-BROKEN for PANIC or RESULT because the execution as a whole contains UB; it also does not return normally. PANIC remains UNPROVED. |
| 1 | The arm at line 14 directly evaluates to 2; the unsafe arm is not executed. | UB-free normal return of 2 through ordinary typed control flow. | SND holds for this input, PANIC is inapplicable, and 2 ≠ 1 gives the UB-free witness required to establish CONTRACT-BROKEN for RESULT. |
| 2 through 255 | The wildcard arm at line 15 evaluates to input; the unsafe arm is not executed. | UB-free normal return of the original u8. | SND and RESULT are proved for every input in this range; PANIC is inapplicable. |

Thus W0 = classify(0) is exactly an UNSOUND witness, while W1 = classify(1)
is exactly a defined postcondition-refutation witness. Keeping them distinct is
necessary: observations from W0 cannot establish a defined behavioral breach.

## Unsafe-call proof review

The safety comment at lib.rs:11 says the branch is “assumed to be unreachable.”
That is not a proof and is false: the immediately controlling match selects the
branch precisely for the valid value 0. Because classify is safe, no prose-only
caller obligation may exclude that value. The required implication
“input is 0 implies this program point is unreachable” is contradicted by the
local control flow. This is both an implementation defect and a deficient proof
artifact; no replacement SAFETY comment can justify the current reachable
intrinsic.

Minimal resolution: replace the zero arm with an actual panic and make the
one arm return input (or remove that special arm). The resulting source would
be a new artifact requiring fresh review.

## TCB-C1

Both entries were opened at their exact submitted Rust 1.80.0 URLs and accepted
as authoritative axioms for the stated source/configuration domain.

- **AXIOM-UU — accepted.** Rust 1.80.0 standard-library Safety text states:
  “Reaching this function is Undefined Behavior.”
  [Exact page](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety).
  Consumer: the line-12 obligation and W0. Re-audit on Rust/stdlib version,
  item contract, source, target-domain, or support-policy change.
- **AXIOM-UB — accepted.** The Rust 1.80.0 Reference identifies invoking UB via
  compiler intrinsics as undefined behavior and defines unsafe code that safe
  code can use to exhibit UB as unsound.
  [Exact chapter](https://doc.rust-lang.org/1.80.0/reference/behavior-considered-undefined.html).
  Consumer: SND classification and whole-execution witness rule. Re-audit on
  Reference, Rust version, source, or claim change.

There are no safe/unsafe dependency, external-specification, implementation,
tool, deployment, or probabilistic premises. No tool-derived evidence was
used. TCB identity is this embedded TCB-C1; the supplied unsafe-rust package had
no visible revision identifier.

## Residual scope and review triggers

Excluded are backend/binary correctness, configurations outside
Supported(configuration), and behavior of any surrounding crate not supplied.
There are no authoritative-documentation or skill-guidance gaps needed for
these conclusions. Re-audit if lib.rs or its documentation changes, the exact
Rust/stdlib version or supported target/profile set changes, either cited
contract changes, or the function is placed in a materially different
generated or external context.

