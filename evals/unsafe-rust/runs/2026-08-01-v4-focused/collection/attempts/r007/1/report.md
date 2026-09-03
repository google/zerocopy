# Audit of `last`

## Claim, scope, and verdict

**Implementation soundness: PROVED.** For the exact `lib.rs` supplied, Rust and standard library 1.82.0, every target on which this source and the used standard-library items exist, every ordinary profile, and every well-typed safe call `last(bytes)` with any valid shared slice, execution introduces no Rust undefined behavior. The proof is relative only to the Rust 1.82.0 authoritative axioms inventoried below; there are no additional TCB assumptions.

**Existing `SAFETY` comment: deficient.** “The returned reference cannot outlive `bytes`” does not establish the only documented safety obligation of the executed `get_unchecked(index)`: that `index` is not out of bounds. A material bounds derivation had to be reconstructed. This is a proof-artifact defect, not an implementation defect.

No caller safety precondition is permitted or needed. `last` has no documented postcondition, so there is no separate mandatory postcondition verdict. No tests, builds, execution, expansion, prior audit, dependency claim, or tool-derived evidence is used.

## Domain and surface closure

Let

`Required = { (this exact source, Rust/std 1.82.0, target t, ordinary profile p, valid &[u8] value B, permitted execution e) | the source and its used std items exist on t }`.

This is the request's controlling expression, preserved without enumeration or exclusion. Its configuration projection fixes Rust/std to 1.82.0 and otherwise quantifies over those `t` and `p`. The complete language-reachable in-scope surface is the safe public free function `last`; it accepts a caller-controlled shared slice. The sole unsafe site is `bytes.get_unchecked(index)`. There are no fields, constructors, traits or impls, callbacks, macros, generated items, dependencies, `cfg`s, FFI, concurrency, allocators, or invariant-bearing state in the supplied source.

The two Boolean outcomes of `bytes.is_empty()` are exhaustive. The proof below is parametric in target and profile: the same source is selected, no target fact is used, and the subtraction is proved non-overflowing rather than relying on profile overflow behavior. Thus each required configuration fiber is covered. With `Covered` equal to the union of the two branch cases for the sole unsafe-backed safe surface, `Required ⊆ Covered`.

## Reconstructed local proof and obligation ledger

Fix an arbitrary required case and write `L = bytes.len()`.

1. If `bytes.is_empty()` is true, the `if` consequent executes and returns `None`; the unsafe call is not reached.
2. If it is false, the `else` executes. AX-EMPTY states that length zero implies `is_empty() == true`; contraposition gives `L ≠ 0`. AX-LEN identifies `L` as the number of slice elements, hence a natural count, so `L ≥ 1`.
3. Therefore `I = L - 1` is representable, cannot underflow, and satisfies `0 ≤ I < L`. This is ordinary predecessor arithmetic applied to the locally obtained element count; it is independent of overflow-check and optimization settings.
4. Consequently `I` denotes the last of the `L` elements and is not out of bounds for this same slice. This discharges AX-UNCHECKED's exact safety condition before the call. No operation can change the slice or `L` between the check, length reads, and call.
5. `get_unchecked`'s expression type is a shared reference, and the enclosing well-typed safe function returns it inside `Option`; no caller-supplied behavior or hidden obligation intervenes.

Obligation dispositions: branch reachability—proved by AX-IF; nonzero length—proved by AX-EMPTY and AX-LEN; subtraction representability and `I < L`—proved by the local facts plus predecessor arithmetic; `get_unchecked` in-bounds precondition—proved; safe-surface soundness—proved by the exhaustive branch union. There are no remaining obligations or uncovered cases.

## Authoritative-premise inventory and reconciliation

All entries apply exactly to Rust/std 1.82.0, all targets where the cited item exists, and every ordinary profile. Each is accepted as authoritative Rust documentation, consumed exactly where identified above, and must be rechecked if Rust/std or the cited text changes.

- **AX-LEN.** [`slice::len`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len): “number of elements in the slice”. Verified proposition: `bytes.len()` returns the slice's element count as `usize`. Consumer: steps 2–3.
- **AX-EMPTY.** [`slice::is_empty`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty): “true if the slice has a length of 0”. Verified proposition: if `L = 0`, `bytes.is_empty()` evaluates to true. Consumer: step 2.
- **AX-IF.** [Reference, `if` expressions](https://doc.rust-lang.org/1.82.0/reference/expressions/if-expr.html#if-expressions): “If all `if` and `else if` conditions evaluate to `false` then any `else` block is executed.” Verified proposition: this `else` body, and hence the unsafe call, is reached only in the false-condition case; the true case executes the consequent instead. Consumers: steps 1–2 and branch exhaustiveness.
- **AX-UNCHECKED.** [`slice::get_unchecked`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked): “with an out-of-bounds index is undefined behavior”. Verified proposition: the call requires its `usize` index not to be out of bounds for the receiver slice. Consumer: step 4.

The remaining inputs are inspected-source facts and elementary logic/arithmetic: the dominating branch, assignments `L` and `I`, absence of intervening mutation/calls, contraposition, and the predecessor lemma for a positive element count. No other Rust semantic or standard-library proposition is consumed. In particular, the existing lifetime sentence is not used to discharge `get_unchecked`'s safety condition.

## Required proof-artifact repair

Replace the existing comment with:

```rust
// SAFETY: This `else` executes only when `bytes.is_empty()` is false.
// Since `is_empty()` returns true for a zero-length slice, `bytes.len()` is
// nonzero. Thus `index = bytes.len() - 1` is representable and is strictly
// less than `bytes.len()`, so it is in bounds for this same slice.
```

This states the operation's controlling obligation, the dominating local fact, the derivation, and the resulting in-bounds proposition adjacent to the unsafe call.

## Residual scope and review triggers

Excluded because the request does not include them: undocumented behavioral robustness, compiler/backend or binary correctness, nonordinary profiles, other Rust/std versions, and targets where the source or used items do not exist. Re-audit on any change to `last`, its signature or documentation, the supported version/configuration predicate, or any consumed Rust/std contract. Independent review was not performed.
