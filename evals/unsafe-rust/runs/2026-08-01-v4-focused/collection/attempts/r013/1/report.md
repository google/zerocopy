# Focused source-only unsafe Rust review

## Claim, snapshot, and domain

Audited artifacts are `lib.rs` (SHA-256
`778d644359b84bc0e519ed7220bfcadfbba578e2c9fd4c474ce742c4b0021ceb`) and
`Cargo.toml` (SHA-256
`57b66359b9447d371fa68a2cfdc04f49176b1a3ce815bb96027b2f76d917d0a7`),
package `quantifier-target` 0.1.0, edition 2021. The manifest exactly pins
`peer-unsafe-dep =3.4.5`; the submitted declaration/contract is available, but
its source, generated output, build behavior, prior audit, and binary are not.

Let `T = { t | this source and the exact peer dependency resolve for target t }`
and `P = {ordinary-debug, ordinary-release}`. The exact configuration domain is
`Required_cfg = {Rust 1.80.0} × T × P`, directly from `REQUEST.md`; no finite
enumeration of `T` is asserted. There are no features, `cfg` branches,
generators, build scripts, macros, target operations, or profile-sensitive
checks in the submitted crate source. Thus the local source is selected
uniformly and the arguments below are parametric in `(t,p) ∈ T×P`. Unknown
dependency configuration remains material to the second claim.

The full valid-use domains are:

* `F`: each `(t,p)` above and every otherwise-valid, well-typed safe execution
  that invokes `force_unreachable()`; a safe API has no hidden caller safety
  precondition.
* `D`: each `(t,p)` above, every `value ∈ 1..=255`, and every execution whose
  caller invokes unsafe `delegated_nonzero(value)` while satisfying its sole
  documented safety obligation, `value != 0`.

The claims concern source-level freedom from Rust undefined behavior under Rust
1.80.0 abstract semantics. Compiler/backend correctness and broader behavior
not documented by these APIs are excluded. No test, build, execution, or tool
result is evidence.

## Evidence and TCB log

TCB identity is the supplied `TCB.md`, SHA-256
`86796b85804436595c0f6ffbfa773dac4fce5cbfe28e02223c802a055037d0f4`.

* **AXIOM-UU (accepted, Rust authority):** Rust 1.80.0 documents
  `unreachable_unchecked` as: “Reaching this function is *Undefined Behavior*.”
  The exact [Safety section](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety)
  was opened and verified. The supplied authority makes this applicable to all
  `(t,p) ∈ T×P`. Consumer: `F-UB`. Re-audit on Rust version or cited-contract
  change.
* **PEER-IMPL (expressly unaccepted):** no proposition about what
  `peer-unsafe-dep` 3.4.5 executes is admitted. In particular, the human
  reviewer declined an `UNSAFE-DEP` entry. Its exact pin freezes a version; its
  documentation establishes the caller contract, not implementation
  correctness. Consumers blocked: `D-SOUND` and, if relied upon, `D-RET`.
  Re-audit on dependency identity, source/features/generated output, contract,
  implementation audit, or trust decision change.

There are no other admitted implementation, compatibility, deployment, or tool
premises.

## Boundary and obligation inventory

The complete exported surface is the safe free function `force_unreachable`
and unsafe free function `delegated_nonzero`. There are no exported fields,
types, constructors, methods, traits/impls, statics, macros, hidden APIs,
callbacks, FFI items, or owned representation invariants. Nonzeroness in `D`
is a per-call precondition, not a type invariant.

| ID | Site | Exact obligation | Disposition |
|---|---|---|---|
| `F-UB` | `lib.rs:6` | Execution must not reach `unreachable_unchecked`. | False on every invocation. |
| `D-CALL` | `lib.rs:17` | The value passed to the peer must be nonzero. | PROVED for all `D`. |
| `D-SOUND` | peer call | The exact peer implementation must be UB-free for every valid call. | UNPROVED. |
| `D-RET` | peer contract | The exact peer implementation returns its input for every valid returning call. | UNPROVED; not needed for wrapper soundness. |

## Claim F — `force_unreachable`

**Verdict: UNSOUND** over `F`, relative to `AXIOM-UU`.

Existential UB certificate (indeed parametric over every supported
configuration):

1. `force_unreachable()` is public and safe, so calling it from an
   otherwise-valid safe execution is a valid in-scope use.
2. Its body has no condition or earlier exit; that call reaches line 6 and
   executes `std::hint::unreachable_unchecked()`.
3. That site's required proposition—“the site is unreachable”—is false in this
   execution precisely because step 2 reaches it.
4. `AXIOM-UU`, applicable to Rust 1.80.0 on every `(t,p)`, entails undefined
   behavior. This closes the required witness chain.

The existing safety comment merely assumes the needed conclusion and is false
for every invocation; it is both proof-artifact deficient and accompanies an
implementation defect. Replacing the operation with defined safe behavior
(for example, a panic), or changing the API and contract so invocation itself
has an enforceable unsafe obligation, requires a new audit. No UB-containing
execution establishes `CONTRACT-BROKEN`, and none is claimed.

## Claim D — `delegated_nonzero`

**Verdict: UNPROVED** for soundness over `D`, relative to the supplied TCB.

The local call obligation is complete: valid use gives `value != 0`; line 17
passes that same unmodified `u8` to `duplicate_nonzero`; the submitted peer
contract requires exactly `value != 0`. Thus `D-CALL` covers all of `D`, and
the adjacent safety comment correctly explains this caller-side step.

That is insufficient for a third-party unsafe API. The smallest missing
soundness proposition is:

> For the exact `peer-unsafe-dep` 3.4.5 implementation selected in every
> `(t,p) ∈ T×P`, and every `v ∈ 1..=255`, executing
> `duplicate_nonzero(v)` is free of Rust undefined behavior.

Neither submitted source/evidence proves this proposition nor an accepted
`UNSAFE-DEP` entry admits it. Therefore aggregate `Covered` lacks `D-SOUND` and
`Required_D ⊆ Covered_D` cannot be derived. Absence of the implementation also
provides no valid execution, false safety proposition, or UB consequence, so
`UNSOUND` is not established.

The wrapper does not explicitly promise that its return equals `value`; the
peer documentation does. If that provider guarantee is intended to be exposed
or consumed, the additionally missing proposition is that the exact peer
implementation returns `v` for every valid returning call. No UB-free
counterexample is supplied, so `CONTRACT-BROKEN` is not established.

## Aggregate result and review triggers

The two claims remain separate: `F` is **UNSOUND** and `D` is **UNPROVED**; no
combined `PROVED` result exists. Re-audit on any audited-source or contract
change, Rust/toolchain or target/profile-policy change, dependency resolution,
feature/source/generated-artifact change, accepted TCB change, or newly
available peer implementation audit.
