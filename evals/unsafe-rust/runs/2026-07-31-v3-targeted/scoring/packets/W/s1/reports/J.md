# Focused source-only review of `classify`

## Claims and verdicts

Audited artifact: `lib.rs`, SHA-256
`705278735813eeafd774bc4b032994b7727d5e6740c836f0f7236aa2fc06bde1`.
The only language-reachable API surface is the safe public function
`classify(u8) -> u8` (`lib.rs:6`). There are no fields, traits, macros,
callbacks, dependencies, generated artifacts, mutable invariants, or other
source files contributing code.

| Claim | Verdict | Certificate |
|---|---|---|
| Every valid safe call is free from Rust undefined behavior | **UNSOUND** | The valid safe call `classify(0)` reaches `unreachable_unchecked` at line 12. Its required proposition—this site is unreachable—is false, and Rust 1.80.0 documents reaching it as UB. |
| When `input == 0`, the function panics | **UNPROVED**, not `CONTRACT-BROKEN` | The exact obstructing case is `classify(0)`, but its execution contains UB. It therefore cannot be an UB-free witness that the panic postcondition is false. No independent UB-free zero-input execution or equivalent existence proof is available. |
| On normal return, the result equals `input` | **CONTRACT-BROKEN** | The valid call `classify(1)` takes line 14 and normally returns `2`; this path never enters the unsafe block, is UB-free as a whole, and `2 != 1`. |

Combined mandatory result: **UNSOUND** for safe-API soundness, **UNPROVED**
for the zero-input panic guarantee, and **CONTRACT-BROKEN** for the
normal-return result guarantee.

## Exact domain and configuration closure

Let `T` be exactly the targets on which this source and the Rust 1.80.0
standard-library item exist, and let `P = {ordinary-debug,
ordinary-release}`. The request defines

`Required = {0..=255} × T × P`.

This is preserved symbolically; no target inventory is inferred. The source
contains no `cfg`, target feature, arithmetic whose overflow checks differ,
debug assertion, allocation, FFI, concurrency, panic-mode selection, or
generated code. Thus the source case split and all local facts below are
parametric in every `(target, profile) in T × P`. `EVIDENCE.md` expressly
supplies applicability of both Rust 1.80.0 authority pages throughout that
same target/profile domain. Accordingly:

- positive soundness coverage is `{1..=255} × T × P`; `{0} × T × P` has the
  parametric UB witness;
- panic coverage has the unresolved region `{0} × T × P`;
- positive result coverage is `{2..=255} × T × P`, the broken region is
  `{1} × T × P`, and the UB-containing zero case remains unproved for that
  postcondition.

These regions exhaust `Required` because `{0}`, `{1}`, and `{2..=255}` are an
exact partition of `u8`. Profile optimization cannot rescue an abstract
execution that reaches documented UB. This is a source-level conclusion; no
compiler-backend or binary-correctness claim is made.

## Case proof and obligation ledger

### `input = 0`

The safe signature imposes no caller safety precondition, and `0` is a valid
`u8`. The match selects line 8; the local `marker` operations do not alter
control flow; execution reaches line 12. The safety comment at line 11 merely
assumes unreachability, while the dominating match arm proves reachability for
this input. Rust 1.80.0's standard-library Safety section states: “Reaching
this function is Undefined Behavior.” Therefore the exact unsafe-call
precondition is false and this valid safe call reaches UB. The Rust Reference
classifies unsafe code that safe code can use to exhibit UB as unsound. This
closes every link of the `UNSOUND` certificate for every `(target, profile)`.

The same execution cannot certify `CONTRACT-BROKEN` for “panics”: the execution
as a whole contains UB. It also supplies no proof that a panic occurs. The
smallest missing proposition is an UB-free theorem that every zero-input call
panics; none follows from this source. For the conditional normal-return
guarantee, the zero case likewise supplies neither a defined normal return nor
an UB-free refutation, so its regional status is `UNPROVED`.

### `input = 1`

The match selects line 14 and returns the literal `2`; it executes no unsafe
operation. This establishes UB freedom for this case and, independently, the
UB-free witness `classify(1) == 2 != 1`. Thus it proves
`CONTRACT-BROKEN` for the normal-return guarantee. The zero-only panic contract
is inapplicable.

### `input in 2..=255`

The wildcard arm at line 15 returns the bound value `input` and executes no
unsafe operation. Hence these calls are UB-free and satisfy the normal-return
result guarantee. The zero-only panic contract is inapplicable.

## TCB audit log

TCB ID: `TCB-source-review-v1`; all entries are accepted because the request
submitted and authorized these exact versioned official sources.

| ID | Category | Exact proposition and scope | Consumer |
|---|---|---|---|
| A1 | AXIOM | On Rust 1.80.0, reaching `std::hint::unreachable_unchecked` is UB, throughout `T × P`. [Rust 1.80.0 std Safety section](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety) | zero-input UB certificate |
| A2 | AXIOM | Rust code must not cause UB; unsafe code triggerable by a safe client to exhibit UB is unsound. [Rust 1.80.0 Reference](https://doc.rust-lang.org/1.80.0/reference/behavior-considered-undefined.html) | soundness classification |
| D1 | submitted domain premise | `EVIDENCE.md` states A1 and A2 apply to every requested target and ordinary profile. | configuration closure |

Both pages were opened and their quoted/consumed propositions verified. No
test, tool result, compiler implementation, dependency, external specification,
or deployment assumption is consumed.

## Findings and remediation

`F-UB-0`: line 11's proof artifact is false and deficient; line 12's
implementation is unsound behind a safe API. Replace the zero arm with a real
panic (for example, an explicit panic or a safe unreachable panic) and remove
the unsupported safety claim.

`F-RESULT-1`: line 14 violates the documented normal-return result. Return
`input` (or otherwise return `1`) if the existing contract is retained.
Neither proposed repair changes the current-snapshot verdict; repaired source
requires a fresh audit.

Residual scope is limited to backend/binary correctness and configurations
outside the exact request. Re-audit on any source, contract, Rust version,
target/profile domain, standard-library documentation, or TCB-applicability
change.
