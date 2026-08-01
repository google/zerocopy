# Focused unsafe-Rust audit and redesign

## Claim, snapshot, and verdicts

**Snapshot.** Exact supplied `lib.rs` (18 lines) under Rust/standard library 1.82.0; no generated code, dependencies, build scripts, `cfg`, features, FFI, concurrency, or prior audit is present in the supplied artifact. Audit cutoff: 2026-08-01. Report/TCB ID: `R029-1` / `R029-TCB-1`.

`Required(c)` is exactly: Rust 1.82.0, every target `c.target` on which this source and the two used standard-library items exist, and every ordinary profile, for every well-typed safe use of the public surfaces. This preserves the request's symbolic target and profile predicates rather than inventing an enumeration.

| Claim | Verdict | Certificate |
|---|---|---|
| All well-typed safe uses of the current public API avoid Rust UB | **UNSOUND** | `F-1` gives a valid safe use, reaches the unchecked call with a false bounds precondition, and the applicable Rust 1.82 contract declares UB. |
| For `increment::<Tail>` and every initial `[a,b]`, normal return is UB-free and produces `[a, b.wrapping_add(1)]` | **PROVED** | `P-TAIL` below, over all `Required(c)`, relative only to the two Rust 1.82 axioms in `R029-TCB-1`. |

The combined current-artifact result is **UNSOUND**. The Tail-specific proof does not repair or narrow the safe generic API's claim.

## Boundary, invariant, and obligation inventory

Safe public surfaces are: downstream-implementable trait `Slot` and its safe associated function `index` (lines 3–5); publicly constructible unit struct `Tail` (line 7); its safe `Slot` implementation (lines 9–13); and safe generic function `increment<S: Slot>` (lines 15–18). There are no public fields, unsafe declarations, macros, hidden APIs, callbacks, custom destruction, or other source surfaces. The sole unsafe operation is `get_unchecked_mut` at line 16.

The unsafe call requires `INV-INDEX(S): S::index() < 2`. No type, privacy boundary, validation, or trait contract establishes that proposition for all `S: Slot`. `Tail::index() == 1` is only a local fact about `Tail`; it cannot be promoted to an invariant of every implementation of the public safe trait.

| ID | Exact obligation | Required domain | Status |
|---|---|---|---|
| `O-BOUNDS` | At line 16, the `usize` index is in bounds for the length-2 receiver | Every safe `S: Slot` call in `Required` | **Refuted (`F-1`)** |
| `O-TAIL` | The same bound when `S = Tail` | All inputs/configurations in `Required` | **PROVED:** source gives `1 < 2` |
| `O-WRAP` | Tail element 1 becomes its old value plus one modulo `2^32`; element 0 is unchanged | All inputs/configurations in `Required` | **PROVED (`P-TAIL`)** |
| `O-PROOF` | Adjacent proof derives every unsafe-call precondition | Line 16 | **Missing**; there is no `SAFETY` comment, and the needed generic premise is false |

### `P-TAIL`

For an input `[a,b]`, the inspected `Tail` implementation returns literal `1`; the array has length 2, hence the unchecked index is in bounds. Rust 1.82 documents that this method returns a mutable reference to the indexed element without bounds checking, while its safety clause says: “Calling this method with an out-of-bounds index is undefined behavior even if the resulting reference is not used.” ([`get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut)). Thus the Tail call obtains the exclusive reference to element 1 permitted by the input `&mut` borrow. Rust 1.82 specifies `wrapping_add` as: “Wrapping (modular) addition. Computes `self + rhs`, wrapping around at the boundary of the type.” ([`u32::wrapping_add`](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add)). The assignment therefore changes only element 1 to `b + 1 mod 2^32`; element 0 remains `a`. No branch, panic, unwind, or profile-dependent arithmetic exists on this path.

Both proofs are parametric in target and ordinary profile: the source has no conditional selection, target operation, debug assertion, ordinary `+`, generator, or build input, and consumes the same Rust 1.82 contracts everywhere in `Required`. Therefore `Covered(O-TAIL) = Covered(O-WRAP) = Required`, and their intersection contains `Required`.

## `F-1` — safe trait implementation makes `increment` UB

**Implementation defect; proof artifact missing.** A downstream crate can use only safe Rust:

```rust
struct Oob;
impl Slot for Oob { fn index() -> usize { 2 } }
let mut pair = [0, 0];
increment::<Oob>(&mut pair);
```

This is a well-typed, valid use: `Slot` is a public safe trait, its method has no contract or enforced range, and the safe `increment` signature imposes no safety precondition. The call reaches line 16; `Oob::index()` is 2, while the receiver length is 2, so the exact required proposition `index < len` is false. The quoted Rust 1.82 safety clause entails UB at the call itself. Literal `2`, array length 2, and the unconditional source path make the same witness available on every `Required` target/profile. This completes the existential **UNSOUND** certificate; it is not merely a failed universal proof. No UB-free postcondition refutation is needed or claimed. A comment or undocumented request to implementors cannot resolve it.

## TCB and evidence

`R029-TCB-1` contains only verified authoritative Rust 1.82 standard-library axioms: `AX-BOUNDS`, the quoted out-of-bounds UB clause consumed by `F-1`/`P-TAIL`; and `AX-WRAP`, the quoted modular-addition guarantee consumed by `P-TAIL`. Exact identities are the two versioned links above; scope is every target where those items exist. There are no admitted dependency, implementation, tool, environment, compatibility, or external assumptions. No tests, execution, compilation, expansion, or tool-derived evidence was used. Re-audit either axiom if its cited contract or the Rust version changes.

## Preferred redesign (not a verdict on implemented code)

The minimum required capability is one fixed operation, not an implementer-selected index. Delete `Slot` and `Tail`, remove the type parameter, and implement a concrete safe function:

```rust
pub fn increment(pair: &mut [u32; 2]) {
    pair[1] = pair[1].wrapping_add(1);
}
```

Its proposed contract is: for every input `[a,b]`, normal return yields `[a, b.wrapping_add(1)]`; it has no caller safety precondition. The fixed array type and literal index keep selection local, safe indexing removes the unsafe contract entirely, and `wrapping_add` supplies the required overflow behavior. There is no invariant-bearing representation or implementer boundary to trust. Removing the nominal `Tail` type is intentional: the stated requirement retains only its operation, not nominal identity.

Migration changes `increment::<Tail>(&mut pair)` to `increment(&mut pair)`. Generic calls, downstream `Slot` implementations, and references to `Slot`/`Tail` stop compiling; the request explicitly authorizes all of those public-contract changes and says the abstraction is unreleased. Required Tail-observable behavior is unchanged.

This candidate is **not implemented and has no audit verdict**. After implementation, audit the exact new snapshot independently: confirm the old trait/type/generic and unchecked call are absent; inventory any actual reexports or callers; verify the stated normal-return postcondition and no hidden panic path for the fixed length; re-establish the same target/profile closure under Rust 1.82; and recheck the `wrapping_add` citation. Source, contract, Rust version, support predicate, or newly introduced configuration/build machinery triggers re-audit. Binary/backend correctness and material not supplied in the target remain outside this source-level review.
