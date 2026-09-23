# Focused unsafe-Rust audit: `classify`

## Claim, scope, and verdicts

Snapshot: the exact submitted `lib.rs`, whose only public item is `pub fn classify(input: u8) -> u8`. This is a source-level review under the documented Rust abstract semantics. Let **S** be Rust compiler and standard library 1.80.0, every edition and target on which this exact source and `std::hint::unreachable_unchecked` exist, and every ordinary debug or release profile. The proof is parametric over S. A valid use is any well-typed safe call with any `u8`; there is no caller safety precondition.

| Claim | Verdict over S | Decisive reason |
|---|---|---|
| Every valid safe call is free of UB | **UNSOUND** | `classify(0)` reaches `unreachable_unchecked`. |
| Every call with `input == 0` panics | **UNPROVED** | The only source path reaches UB. That execution cannot establish a defined behavioral refutation. |
| On normal return, the result equals `input` | **CONTRACT-BROKEN** | The separate UB-free call `classify(1)` normally returns `2`. |

The combined mandatory result is therefore **UNSOUND**, **UNPROVED** for the zero-input panic guarantee, and **CONTRACT-BROKEN** for the normal-return result guarantee, relative to TCB `TCB-1` below.

## Authority and TCB (`TCB-1`)

`AXIOM-UB-1` (AXIOM, accepted): for Rust 1.80.0, the Safety section of [`unreachable_unchecked`](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety) states: “Reaching this function is Undefined Behavior.” The submitted evidence states that this proposition applies throughout S. The Rust 1.80.0 [undefined-behavior chapter](https://doc.rust-lang.org/1.80.0/reference/behavior-considered-undefined.html) is the controlling Reference context for the source-level classification. Consumer: obligation `O-UB-0`. Re-audit on source, Rust/stdlib version, supported-set, or cited-contract change.

No dependency, external, deployment, compiler-backend, tool, probabilistic, or implementation premise is consumed. No tests or tool-derived evidence were used. This TCB supports only a source-level result, not correctness of a particular emitted binary.

## Surface and configuration coverage

The complete language-reachable surface in the supplied source is safe free function `classify`; it accepts every `u8`. Its sole unsafe site is the call to `unreachable_unchecked` in the `0` arm. There are no public fields, types, traits, callbacks, macros, FFI, generated artifacts, dependencies, invariants, concurrency, allocation, or target-conditioned items.

The `match` partitions all `u8` values exhaustively into `0`, `1`, and `2..=255`. No `cfg`, arithmetic, debug assertion, layout, target feature, or profile-dependent operation affects selection or results. Thus the same control-flow proof covers every member of S: optimization cannot repair a source-level execution that reaches an operation whose contract declares that reach UB, and debug/release differences do not alter either defined return arm.

## Obligation ledger and proofs

### `O-UB-0` — safe-call soundness, `input = 0`: **UNSOUND**

Local facts: `0` selects the first arm; the two `marker` statements complete without changing `input` or control flow; execution then reaches the unsafe call. By `AXIOM-UB-1`, that reach is UB. Hence the valid safe invocation `classify(0)` is an in-scope UB-containing execution on every S configuration and refutes the universal soundness theorem.

The adjacent comment, “This branch is assumed to be unreachable,” is a false and circular proof artifact: the immediately enclosing match arm itself establishes reachability when `input == 0`. A safe caller is permitted to supply zero, and the documentation affirmatively specifies its behavior. No caller obligation can be inferred.

### `O-PANIC-0` — zero-input panic: **UNPROVED**

Witness considered: `classify(0)` follows the path above and reaches UB; no panic operation occurs before that point. This witness proves `O-UB-0`, but an execution containing UB cannot prove the existence of an UB-free execution falsifying a documented postcondition. Therefore it cannot establish **CONTRACT-BROKEN**. Conversely, source execution through `unreachable_unchecked` supplies no defined panic postcondition, so the panic guarantee is not proved. No independent UB-free zero-input witness or equivalent proof was established.

### `O-RESULT-1` — normal return, `input = 1`: **CONTRACT-BROKEN**

`1` selects the second arm, so the unsafe first arm is not executed. The arm evaluates the valid `u8` literal `2` and normally returns it. The complete execution is UB-free, while `2 != 1`; it is therefore the required defined witness falsifying “returns `input` unchanged.” This witness is independent of the zero-input UB witness.

### `O-RESULT-REST` — normal return, `input = 2..=255`: **PROVED**

Every such value selects `_ => input`, does not execute the unsafe arm, and normally returns the copied input unchanged. For `input = 0`, the normal-return guarantee remains **UNPROVED** because its only source path contains UB; that case supplies neither a defined return nor a contract-breaking witness. The input-zero panic condition is inapplicable to all nonzero inputs. Soundness is locally proved for `1..=255` because those paths contain only the inspected ordinary match/literal/copy/return operations and never reach the unsafe site; this regional result does not change the aggregate **UNSOUND** verdict.

## Findings and required resolution

`F-1` is an implementation soundness defect and a deficient safety comment. Replace the zero arm with an actual panic; no revised `SAFETY` comment can justify the current call while zero remains accepted by the safe signature. `F-2` is an independent behavioral defect: return `input` rather than `2` in the `1` arm. Removing the unsafe call and applying both changes requires a fresh audit of the new snapshot.

Residual scope is limited to backend/binary correctness and configurations outside S. Re-audit is required if the source, public documentation, Rust/stdlib version, cited authority, item availability, or supported configuration predicate changes.
