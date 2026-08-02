# Focused literal audit and redesign

## Claim, domain, and verdicts

**Snapshot and scope.** This reviews exactly the supplied `target/lib.rs`: `Slot`, `Tail`, its `Slot` implementation, `increment`, and the one `get_unchecked_mut` call. `Required(c)` is exactly: `c` uses Rust and standard library 1.82.0, is any target on which this exact source and its used 1.82.0 standard-library items exist, and uses any ordinary profile. There are no dependencies, `cfg`s, features, generated artifacts, macros, FFI, concurrency, allocators, or other source-level configuration branches.

**Soundness theorem.** Every well-typed safe call to the public safe API must be free of Rust undefined behavior, without an undocumented caller or implementer safety condition.

**Verdict: UNSOUND.** The current public generic `increment<S: Slot>` has a valid entirely-safe downstream use that necessarily calls `get_unchecked_mut` out of bounds. This verdict is independent of the redesign below.

**Required `Tail` behavior: PROVED.** For every `c` in `Required` and every initial `pair`, `increment::<Tail>` returns with element 0 unchanged and element 1 equal to its old value plus one modulo `2^32`. This user-required behavior is not documentation found in `lib.rs`; it is an explicit review requirement.

**Trust boundary `TCB-R182`.** No additional TCB assumptions are admitted. The only semantic premises are the exact Rust 1.82.0 Reference and standard-library contracts cited below. No compiler-binary, platform-implementation, test, or tool result is trusted.

## Boundary and obligation coverage

The complete relevant surface is: public safe trait `Slot`; its public safe associated function `index`; public constructible unit struct `Tail`; the crate-owned `impl Slot for Tail`; public safe generic function `increment`; and its private unsafe operation. There are no unsafe declarations, fields, constructors with state, callbacks other than caller-selected `Slot` implementations, hidden items, or generated surfaces. There is no owned invariant: `S::index() < 2` is merely the missing proposition consumed by the unsafe call.

The [visibility rules](https://doc.rust-lang.org/1.82.0/reference/visibility-and-privacy.html#visibility-and-privacy) say a `pub` item is accessible externally and associated items in a public trait are public by default. Under the [orphan rules](https://doc.rust-lang.org/1.82.0/reference/items/implementations.html#trait-implementations), a downstream crate may implement a foreign trait for its own local type. `Slot` does not use `unsafe trait`; the [unsafe-trait rule](https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits) reserves the implementer-side unsafe obligation for traits whose declaration begins with `unsafe`.

### UNSOUND certificate

A downstream crate can write only safe Rust:

```rust
use audited_crate::{increment, Slot};

struct OutOfBounds;
impl Slot for OutOfBounds {
    fn index() -> usize { 2 }
}

let mut pair = [0u32; 2];
increment::<OutOfBounds>(&mut pair);
```

1. **Valid use:** Both imported items are public; `OutOfBounds` is local, so its safe `Slot` implementation is coherent. Neither the implementation nor `increment` requires an `unsafe` context or documents a safety obligation.
2. **Reachability:** `increment` unconditionally evaluates `S::index()` and passes the result, `2`, to `pair.get_unchecked_mut`.
3. **False required proposition:** `pair` has exactly two elements, so valid element indices are `0` and `1`; `2` is out of bounds.
4. **UB consequence:** Rust 1.82 documents for [`get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut): “Calling this method with an out-of-bounds index is undefined behavior even if the resulting reference is not used.” UB therefore occurs at the call itself.

This certificate applies parametrically on every `c` in `Required`: the source has no target/profile selection and the cited 1.82 contract is the same premise for the whole requested target/profile predicate. The UB-containing witness does not establish a separate `CONTRACT-BROKEN` result.

For `Tail`, `index()` is locally fixed at `1`; `1 < 2`, so the unchecked call returns a mutable reference to element 1. The assignment touches only that element, and Rust 1.82 [`wrapping_add`](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add) specifies modular addition. Thus `Covered_Tail = Required` and `Required ⊆ Covered_Tail`. The same derivation is profile- and target-parametric.

The unsafe block has no adjacent `SAFETY` proof. A valid local proof can be reconstructed only for `S = Tail`; it cannot prove the universal generic call. Adding a comment or prose requirement to this safe trait would not repair the implementation defect.

## Preferred design

Replace the generic abstraction with the exact required capability, using only safe operations:

```rust
pub fn increment(pair: &mut [u32; 2]) {
    pair[1] = pair[1].wrapping_add(1);
}
```

Its safe contract is: for every input, return with element 0 unchanged and element 1 equal to its prior value plus one modulo `2^32`; there are no caller safety preconditions. The array type establishes length two, literal index `1` supplies the bounds fact at the use site, and safe indexing enforces it. There is no representation invariant, unsafe surface, implementer capability, or additional TCB premise.

This is preferable to sealing or making `Slot` unsafe because no required polymorphism remains. Remove `Slot`, its implementations, and `Tail` if it has no independent nominal purpose; change `increment<S: Slot>` to the non-generic signature above. Migrate `increment::<Tail>(&mut pair)` to `increment(&mut pair)` and delete trait bounds/implementations. Downstream `Slot` implementations and generic calls intentionally cease to be supported, as authorized for this unreleased abstraction.

This is a design proposal, not a verdict for a new artifact. After implementation, audit the exact new snapshot: enumerate its exported surface and all callers/documentation; confirm the intended removals; prove both-element postconditions for all inputs; confirm no conditional/generated variants; and re-establish `Required ⊆ Covered` for the same Rust/target/profile predicate. Re-audit on any source, contract, Rust version, target/profile-support, or generation change.
