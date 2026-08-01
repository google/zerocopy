# Focused source-only review of `classify`

## Claims, scope, and verdicts

The audited artifact is exactly the supplied 17-line `lib.rs`. The only API surface is the safe public function `classify(input: u8) -> u8`; all 256 `u8` values are valid safe inputs. No fields, traits, macros, generated code, dependencies, callbacks, mutable state, or representation invariants exist.

`Supported(c)` means: Rust and standard library 1.80.0; any target on which this exact source and `std::hint::unreachable_unchecked` exist; and an ordinary debug or release profile. The proof is source-level and relative to the Rust abstract semantics.

| Requested theorem | Verdict | Reason |
|---|---|---|
| Every valid safe call is free from undefined behavior | **UNSOUND** | `classify(0)` reaches `unreachable_unchecked` (F-UB0). |
| If `input == 0`, the call panics | **UNPROVED**, not `CONTRACT-BROKEN` | The only relevant source path contains UB; it cannot witness a defined failure to panic (F-PANIC0). |
| On normal return, the result equals `input` | **CONTRACT-BROKEN** | The independent UB-free call `classify(1)` normally returns `2` (F-RET1). |

The combined result is therefore **UNSOUND** with one **UNPROVED** documented guarantee and one **CONTRACT-BROKEN** documented guarantee.

## Authority and TCB

TCB revision `TCB-R1` has two accepted Rust 1.80.0 axioms, submitted for this review and independently opened at the exact supplied URLs:

- **AXIOM-UU:** The Safety section for [`unreachable_unchecked`](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety) states: “Reaching this function is Undefined Behavior.”
- **AXIOM-UB:** The [Rust Reference UB chapter](https://doc.rust-lang.org/1.80.0/reference/behavior-considered-undefined.html) states that `unsafe` does not relax the requirement that programs never cause UB and calls unsafe code *unsound* when safe code can trigger UB.

Both axioms apply throughout `Supported(c)` as stipulated by `EVIDENCE.md`. No additional assumption, dependency, tool result, test, compiler-backend claim, or deployment restriction is consumed.

## Complete case and obligation proof

| Input | Executed path | UB freedom | Zero panic | Normal-return equality |
|---|---|---|---|---|
| `0` | Lines 8–12, reaching `unreachable_unchecked()` | **UNSOUND** | **UNPROVED** | **UNPROVED** for this input; no UB-free normal-return witness |
| `1` | Line 14, returns literal `2` | **PROVED** | Not applicable | **CONTRACT-BROKEN** |
| `2..=255` | Line 15, returns `input` | **PROVED** | Not applicable | **PROVED** |

This partition is exhaustive for `u8`. It is unchanged by target or ordinary profile: the source has no `cfg`, target-dependent operation, generated artifact, arithmetic, allocation, concurrency, FFI, panic-mode-dependent cleanup, or debug-only assertion. The same match-arm reasoning therefore covers every supported configuration parametrically.

### F-UB0 — valid safe call reaches UB

Witness: call the safe API as `classify(0)`. The `0` pattern selects lines 8–12. The local `u8` assignment and discard do not alter control flow; execution then reaches the unsafe call. AXIOM-UU makes that reach UB. Because the API is safe and enforces no caller obligation excluding zero, this is a valid safe call. AXIOM-UB therefore entails **UNSOUND** for the universal UB-freedom theorem on every supported target/profile.

The adjacent comment, “This branch is assumed to be unreachable,” supplies no fact: the controlling match condition proves the opposite. The smallest missing implication would be `input == 0 implies the 0 arm is unreachable`, which is false.

### F-PANIC0 — UB cannot refute a behavioral contract

The same input `0` does **not** establish `CONTRACT-BROKEN` for “Panics when `input == 0`.” Undefined behavior is classified over the execution as a whole. A UB-containing execution cannot serve as the required UB-free witness that the function fails to panic, and observations from its pre-UB prefix are insufficient. No distinct input can refute this conditional promise because its premise is specifically `input == 0`. Thus the panic guarantee is **UNPROVED**. Repair requires a defined panic on the zero arm; merely changing the safety comment cannot repair it.

### F-RET1 — independent defined contract refutation

Witness: `classify(1)`. Line 14 is selected and normally returns `2`; the zero arm and its unsafe call are not executed. This path performs only the match and a `u8` return, so it is UB-free. Since `2 != 1`, this whole defined execution falsifies “On normal return, returns `input` unchanged.” It therefore establishes **CONTRACT-BROKEN**, independently of F-UB0. For every `input` in `2..=255`, line 15 instead returns that exact input and proves the guarantee for that class. Repair line 14 to return `input` (or deliberately revise the public contract with compatibility review).

## Residual scope and review triggers

No build, execution, test, expansion, backend correctness, or binary/platform behavior was reviewed. Re-audit is required if the source or either documented guarantee changes; if Rust/stdlib differs from 1.80.0; if the supported target/profile set changes; or if either consumed authority changes materially.

