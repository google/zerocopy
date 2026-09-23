# Focused unsafe-Rust audit and redesign

## Claim, domain, and results

**Snapshot.** The artifact is exactly the supplied `lib.rs`; there are no other target sources, dependencies, generated artifacts, `cfg` branches, build scripts, macros, FFI, or prior results. Audit cutoff: 2026-08-01. Source-level Rust abstract semantics only.

Let `E` be the request's exact set of targets “on which this exact source and its used Rust 1.82.0 standard-library items exist,” and `P` its symbolic set of ordinary profiles. `Required` contains every well-typed safe use of every language-reachable safe surface, with every input/state/execution, for `(Rust, target, profile) in {1.82.0} × E × P`. Thus `Required_cfg = {1.82.0} × E × P`. This is an exact restatement, not an enumeration. The source has no selection mechanism, and the proof below is parametric in `E` and `P`: target and profile cannot change the constants `2` and `1`, trait openness, or the specified operations. There are no exclusions.

- **Safe-API soundness: UNSOUND.** A valid safe downstream implementation can return an out-of-bounds index and make `increment` execute documented undefined behavior. This certificate is independent of the redesign.
- **Requested `Tail` behavior: PROVED.** For every input array and required configuration, `increment::<Tail>` returns with element 0 unchanged and element 1 equal to its old value plus one modulo `2^32`, without UB.
- **Combined current-artifact result: UNSOUND.** The positive `Tail` result does not repair the universally quantified public safe API.

No additional robustness or documented unsafe-API postcondition is in scope.

## Boundary and obligation inventory

All surfaces are public and safe: `Slot`; its associated function `index`; public unit type/constructor `Tail`; its `Slot` implementation; and generic free function `increment`. The sole unsafe site is `pair.get_unchecked_mut(S::index())`. There are no fields, unsafe declarations/impls, named representation invariants, destructors, callbacks after index selection, or hidden/generated surfaces. `S::index()` may also panic; that exits before the unsafe call and before mutation.

The Rust 1.82 authority set (TCB `R82-A`, no admitted non-Rust assumptions) is:

- `AX-PUBLIC/IMPL`: public accessibility and trait-implementation/coherence rules. A downstream crate may name this public trait and implement it for its own local type; the local self type satisfies the orphan rule. [Visibility](https://doc.rust-lang.org/1.82.0/reference/visibility-and-privacy.html#visibility-and-privacy), [trait implementations](https://doc.rust-lang.org/1.82.0/reference/items/implementations.html#trait-implementations).
- `AX-SAFE-BOUNDARY`: unsafe traits and functions require their respective `unsafe` declarations/obligations. Here `Slot` is not an unsafe trait and `increment` is not an unsafe function, so neither implementation nor call carries a caller safety obligation. [Unsafe traits](https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits), [unsafe functions](https://doc.rust-lang.org/1.82.0/reference/unsafe-keyword.html#unsafe-functions-unsafe-fn).
- `AX-GET`: Rust 1.82 documents for `get_unchecked_mut`: “Calling this method with an out-of-bounds index is undefined behavior even if the resulting reference is not used.” [Slice method](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut).
- `AX-WRAP`: `u32::wrapping_add` performs modular addition, wrapping at the type boundary. [Integer method](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add).

No dependency or tool result is consumed. Re-audit `R82-A` if any cited Rust 1.82 text is corrected materially.

| ID | Exact obligation | Disposition |
|---|---|---|
| O1 | At every executed `get_unchecked_mut(i)`, `i < 2`. | **False** for the public generic safe API; existential certificate below. |
| O2 | For `Tail`, establish O1 and the requested state transition. | **Proved:** `Tail::index()` unconditionally returns `1`; `1 < 2`; `AX-GET` therefore admits the returned reference to element 1. Assignment touches only that element. `AX-WRAP` gives the exact modulo-`2^32` result, including `u32::MAX -> 0`. |
| O3 | Existing adjacent proof explains the unsafe call. | **Deficient:** there is no `SAFETY` comment, and no sound derivation exists for arbitrary `S`. |

For O2, the same source and argument cover every input fiber and every `(target, profile) in E × P`; no premise is configuration-specific. Hence the requested `Tail` domain is contained in its covered domain.

## F-1 — safe generic API reaches UB

Severity/classification: **UNSOUND implementation defect**, plus missing proof documentation.

**Valid safe witness:** in a downstream crate, entirely safe Rust may write:

```rust
struct Bad;
impl Slot for Bad { fn index() -> usize { 2 } }
let mut pair = [0_u32; 2];
increment::<Bad>(&mut pair);
```

`Bad` is downstream-local, so `AX-PUBLIC/IMPL` permits the implementation. Neither boundary is unsafe (`AX-SAFE-BOUNDARY`), and the current API documents no precondition; this is therefore a valid in-scope safe use.

**Reachability and falsity:** monomorphization calls `Bad::index()`, which returns `2`, then executes `get_unchecked_mut(2)` on the two-element receiver. Its valid element indices are `0` and `1`, so `2` is out of bounds. **UB consequence:** `AX-GET` states that the call itself is UB even before the reference is used. This completes every existential link on every required configuration and establishes `UNSOUND`; it is not merely a missing universal proof. The execution cannot separately witness `CONTRACT-BROKEN` because it contains UB. No generic behavioral postcondition was documented.

Minimum repair of the current generic design would require checking the index before any unchecked access (and defining the failure behavior), or making/sealing an implementer contract and auditing every implementation. Neither complexity serves the stated requirement.

## Preferred provable abstraction

Specialize to the only required capability and remove unsafe code, the trait, the marker type, and genericity:

```rust
pub fn increment(pair: &mut [u32; 2]) {
    pair[1] = pair[1].wrapping_add(1);
}
```

**Proposed contract:** this is a safe function with no precondition beyond its type. On normal return, `pair[0] == old(pair[0])` and `pair[1] == old(pair[1]).wrapping_add(1)`; it returns `()`. The fixed array type makes index 1 in bounds. Safe indexing enforces its own bounds in any event, and `AX-WRAP` supplies the required arithmetic. There is no unsafe surface, implementer promise, or representation invariant. Retaining `Tail` would add nominal machinery without supplying a required capability.

**Migration delta:** remove public `Slot` and `Tail`; change `increment::<Tail>(&mut pair)` to `increment(&mut pair)`. Downstream `Slot` impls and generic invocations cease to compile. The request expressly authorizes all of these unreleased contract/representation breaks. The wrapping result and mutation of element 1 are unchanged for the required case.

**Fresh audit after implementation:** treat it as a new snapshot. Verify the exact exported surface and removal of old implementations/callers; prove both element postconditions for all `u32` values (especially `u32::MAX`); recheck the safe indexing and wrapping contracts against Rust 1.82; repeat the symbolic `E × P` configuration-closure argument; inventory any newly introduced code/generation; and confirm there is no remaining unsafe site. The proposal itself has no artifact verdict.

Residual scope is exactly what the request excludes: other Rust releases, targets outside `E`, nonordinary configurations, binaries/backend correctness, and behavior of the intentionally removed generic API. Re-audit on source/API changes, support-domain changes, or material changes to the cited Rust 1.82 contracts.
