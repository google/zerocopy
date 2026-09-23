# Focused source-only unsafe Rust audit

## Claim, snapshot, and verdicts

Audited artifact: `lib.rs`, SHA-256
`705278735813eeafd774bc4b032994b7727d5e6740c836f0f7236aa2fc06bde1`.
Scope is solely the public safe function `classify` in lines 6–17. No generated
artifacts, dependencies, macros, callbacks, traits, fields, or other public
surfaces exist in the submitted source. This review did not build, execute,
test, or expand the target.

Let `Required(t,p,i)` mean: the exact source above; Rust compiler and standard
library 1.80.0; a target `t` on which this source and the used 1.80.0
`std::hint::unreachable_unchecked` item exist; ordinary debug or ordinary
release profile `p`; and a well-typed safe call `classify(i)` for `i: u8`.

| Claim | Verdict | Certificate |
|---|---|---|
| Every valid safe call in `Required` is free from Rust undefined behavior | **UNSOUND** | For every required `t,p`, the valid safe call `classify(0)` reaches `unreachable_unchecked`; AX-1 says reaching it is UB. |
| When `input == 0`, the call panics | **UNPROVED**, not `CONTRACT-BROKEN` | The source reaches UB before establishing a panic. That execution proves unsoundness, but an execution containing UB cannot certify a broken behavioral contract. No independent UB-free zero-input witness was supplied or derivable. |
| On normal return, the result equals `input` | **CONTRACT-BROKEN** | For every required `t,p`, `classify(1)` takes line 14 and normally returns the valid `u8` value `2`; `2 != 1`. This path never enters the unsafe block and consists only of the matched safe return, so the whole witness is UB-free. |

The combined requested result is therefore not proved: it has the component
statuses `UNSOUND`, `UNPROVED`, and `CONTRACT-BROKEN` above.

## Authority and TCB (`TCB-R1`)

Both entries were opened at their exact versioned URLs and checked in context.
They are accepted Rust-authority premises for this source-level review, with the
target/profile applicability expressly supplied by `EVIDENCE.md`.

* **AX-1 (Rust 1.80.0 std):** The Safety section for
  [`unreachable_unchecked`](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety)
  states: “Reaching this function is Undefined Behavior.” Consumer: OBL-UB.
* **AX-2 (Rust 1.80.0 Reference):** The
  [undefined-behavior chapter](https://doc.rust-lang.org/1.80.0/reference/behavior-considered-undefined.html)
  says unsafe code that safe code can misuse to exhibit UB is unsound, and that
  `unsafe` does not permit Rust programs to cause UB. Consumer: the safe-wrapper
  soundness classification.

No compiler-backend correctness, tested behavior, platform implementation, or
tool result is assumed: these are source-level conclusions under documented
Rust 1.80.0 abstract semantics. The Reference warns that its general UB list is
not exhaustive; the UB certificate does not rely on that list being exhaustive,
because AX-1 directly classifies the reached operation.

## Boundary, cases, and obligation ledger

The sole safe boundary is `pub fn classify(input: u8) -> u8`. Its documentation
supplies the two behavioral contracts at lines 3 and 5. The sole unsafe
consumer is the call at line 12. It requires that control never reach it. The
comment at line 11 merely assumes that proposition and does not prove it.

The input partition is exhaustive by equality: `i = 0`, `i = 1`, or
`i != 0 && i != 1`.

| Case | Control/data-flow proof | Disposition |
|---|---|---|
| `i = 0` | The `match` selects lines 8–13; the harmless `marker` statements do not alter `input` or control flow; line 12 is reached. | OBL-UB false by AX-1; safe-call soundness is `UNSOUND`. The panic theorem remains `UNPROVED`. This case supplies no UB-free normal return and therefore does not refute the conditional result theorem. |
| `i = 1` | The `match` selects `1 => 2`; it reaches no unsafe operation and normally returns `2`. | Sound for this execution; panic contract inapplicable; exact UB-free witness for `CONTRACT-BROKEN` result guarantee. |
| `i != 0 && i != 1` | The wildcard arm normally returns `input` and reaches no unsafe operation. | Sound for these executions and the normal-return result guarantee holds. Panic contract inapplicable. |

The local invariant suggested by the safety comment—“the zero arm is
unreachable”—has no enforcing owner or producer and is directly falsified by
`i = 0`. The implementation defect and proof-comment defect are therefore
separate: reconstruction cannot repair the false premise.

## Configuration closure

`REQUEST.md` directly defines the symbolic target set, exact Rust version, and
two profiles; no target enumeration or widening is used. The source contains
no `cfg`, feature gate, target-specific operation, arithmetic, debug assertion,
generated code, allocation, concurrency, FFI, or profile-dependent branch.
Branch selection depends only on `i`. AX-1's applicability over the declared
target/profile domain is supplied by `EVIDENCE.md`. Consequently each case
derivation is parametric in `t,p`, and the three input predicates exhaust every
`i: u8`. The zero and one witnesses therefore exist on every member of the
required configuration domain; optimization cannot turn their source-level UB
or defined `1 => 2` return into the opposite theorem.

Because the two universal claims have complete existential refutations (UB for
soundness, a UB-free wrong result for normal return), they do not require a
positive `Required ⊆ Covered` certificate. The zero-input panic claim lacks
the UB-free evidence required for either a proof or a `CONTRACT-BROKEN`
certificate and is intentionally left `UNPROVED`.

## Findings and remediation

1. **F-UB0 — critical, `UNSOUND`:** a caller needs no unsafe act or undocumented
   precondition to call `classify(0)`. The selected arm executes line 12, whose
   exact safety proposition (“must not be reached”) is false; AX-1 supplies the
   UB consequence. Replace that arm with a real panic (for example `panic!` or
   `unreachable!`) and remove the false safety proof.
2. **F-RESULT1 — `CONTRACT-BROKEN`:** the independent UB-free call
   `classify(1)` normally returns `2`, falsifying line 5. Return `input` in this
   arm or remove the special arm.

Residual scope is exactly what the request excludes: other Rust releases,
targets where the source/item do not exist, nonordinary profiles, binaries,
backend correctness, and any source other than the submitted file. Re-audit on
source or contract changes, Rust/stdlib version changes, target/profile-domain
changes, or material changes to either cited authority.
