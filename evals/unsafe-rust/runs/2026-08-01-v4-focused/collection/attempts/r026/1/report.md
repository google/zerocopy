# Focused unsafe-Rust audit and redesign

## Claim, snapshot, and verdicts

**Snapshot.** Exactly the supplied 18-line `target/lib.rs`, audited as source under Rust and standard-library 1.82.0 abstract semantics. No generated source, dependencies, build machinery, features, `cfg`, FFI, assembly, allocator choice, concurrency, or prior audit appears in the supplied artifact. Nothing was executed or expanded.

Let `E` be exactly the targets named by the request: targets on which this source and its used Rust 1.82.0 standard-library items exist. Let `P` be every ordinary profile. Then

`Required_cfg = {Rust 1.82.0} × E × P`.

For soundness, `Required` additionally quantifies over every well-typed safe call, every valid `&mut [u32; 2]`, every caller-provided `S: Slot`, and every permitted execution. For the requested behavior, `Required_Tail` is every call with `S = Tail` and every initial array. The source has no configuration selector, and neither proof below consumes target- or profile-specific facts; both are parametric over `E × P`. Thus no finite target/profile inventory is asserted or needed.

| Claim | Verdict | Certificate |
|---|---|---|
| Every valid safe use of the current public API is UB-free | **UNSOUND** | Witness `W1` below is valid, reaches the unsafe operation, falsifies its exact precondition, and the Rust 1.82 contract says the call is UB. |
| `increment::<Tail>` increments element 1 modulo `2^32` and leaves element 0 unchanged | **PROVED** | `TAIL-PROOF` below covers all `Required_Tail`. |

The current-artifact soundness verdict is independent of the proposal.

## Boundary and obligation inventory

The complete language-reachable surface in this source is: public safe trait `Slot` and its required safe associated function `index` (lines 3–5); constructible public unit struct `Tail` (line 7); safe `Slot for Tail` implementation returning `1` (lines 9–13); and public safe generic function `increment` (lines 15–18). There are no fields, inherent methods, macros, hidden items, callbacks, unsafe declarations/traits/impls, or destructors in the artifact.

The sole unsafe operation is `pair.get_unchecked_mut(S::index())` (line 16). Its obligation is `S::index() < pair.len() = 2` at the call. There is no enforced invariant or check supplying that fact. The subsequent operation (line 17) must write the referenced element's old value plus one with wrapping arithmetic. The unsafe block has no adjacent `SAFETY` proof; that proof artifact is missing independently of implementation correctness.

### `W1`: existential UB certificate

Downstream safe code can write:

```rust
struct Outside;
impl Slot for Outside { fn index() -> usize { 2 } }
let mut pair = [0u32, 0u32];
increment::<Outside>(&mut pair);
```

1. `Slot` and `increment` are `pub`; Rust 1.82 says a `pub` item is accessible outside, and associated items of a public trait are public by default ([visibility](https://doc.rust-lang.org/1.82.0/reference/visibility-and-privacy.html#visibility-and-privacy)).
2. `Outside` is local to the downstream crate, so this implementation satisfies the orphan-rule alternative requiring a local implementing type. It defines the sole required item ([trait implementations](https://doc.rust-lang.org/1.82.0/reference/items/implementations.html#trait-implementations)). `Slot` is not `unsafe`; only an unsafe trait establishes compiler-recognized extra implementation safety conditions and requires `unsafe impl` ([unsafe traits](https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits), [unsafe keyword](https://doc.rust-lang.org/1.82.0/reference/unsafe-keyword.html#unsafe-functions-unsafe-fn)). The source documents no behavioral restriction. Therefore returning `2` is a valid safe implementation and the entire witness contains no caller-side `unsafe`.
3. The safe generic call reaches line 16; `S::index()` returns `2`. A two-element array has length `2`, so `2` is out of bounds.
4. Rust 1.82 states: “Calling this method with an out-of-bounds index is undefined behavior” even if the reference is unused ([`get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut)).

This same source-level witness applies for each `E × P`; one witness suffices to refute the universal claim. A comment cannot repair it. The minimum current-shape repairs would enforce the bound, seal/control every implementation, or create an honest unsafe implementer boundary. The requested specialization makes all three unnecessary.

### `TAIL-PROOF`: requested current behavior

For `Tail`, the inspected implementation returns `1`. Since `1 < 2`, line 16 satisfies the only stated safety condition and returns a mutable reference to element 1. Line 17 reads and writes only through that reference, so element 0 is unchanged. Rust 1.82 defines `wrapping_add(1)` as modular addition that wraps at the type boundary ([`u32::wrapping_add`](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add)). Therefore element 1 becomes `(old element 1 + 1) mod 2^32` for every input. There are no alternative source paths. This reconstruction proves the `Tail` implementation obligation but does not cure the missing local proof or generic unsoundness.

## Trust and evidence

**TCB-R182/revision 1.** No additional assumption is admitted. The only consumed semantic premises are the exact Rust 1.82 authoritative propositions linked above: public accessibility, trait-implementation/orphan and unsafe-boundary rules, out-of-bounds `get_unchecked_mut` UB, and wrapping addition. Their scope is exactly Rust/std 1.82.0 and `E × P`; consumers are `W1` and `TAIL-PROOF`. All other premises are inspected local syntax or arithmetic. No dependency, tool result, external specification, implementation/backend assumption, deployment restriction, or probabilistic premise is consumed. Re-audit on any source/public-contract change, Rust/std version change, scope expansion, or material change to a cited proposition.

## Preferred redesign

The minimum required capability is one fixed operation, not caller-selected indexing. Retain nominal `Tail` only if that name is desired, remove `Slot`, remove genericity, and use safe indexing:

```rust
pub struct Tail;

impl Tail {
    pub fn increment(pair: &mut [u32; 2]) {
        pair[1] = pair[1].wrapping_add(1);
    }
}
```

**Proposed contract.** For every valid `&mut [u32; 2]`, `Tail::increment` has no caller safety precondition, returns normally, leaves element 0 unchanged, and replaces element 1 by its old value plus one modulo `2^32`. It exposes no representation invariant and contains no unsafe operation or implementer obligation.

**Why preferred.** It directly supplies the only required consumer proposition. A checked generic function would preserve unneeded variability; sealing would retain an unneeded trait; making `Slot` unsafe would export an unnecessary obligation. The proposal removes the false bound premise, unsafe block, generic consumer, and implementer surface rather than relocating their proofs.

**Migration/contract delta.** Delete public `Slot`, its `Tail` impl, and `increment<S: Slot>`. Change crate-owned calls from `increment::<Tail>(&mut pair)` to `Tail::increment(&mut pair)`. Downstream `Slot` implementations and generic calls cease to compile, as expressly authorized; the abstraction is unreleased. The required `Tail` result is unchanged.

**Fresh-audit status.** This is an unimplemented design, not a verdict on a new snapshot. After implementation, audit the exact source anew: enumerate its public surfaces; verify safe indexing selects element 1 and cannot panic for `[u32; 2]`; reprove wrapping arithmetic and nonmutation of element 0 on every exit; confirm no generated/configuration-dependent alternative; and re-establish parametric coverage of Rust 1.82.0 over `E × P`. No unsafe-code TCB entry or safety comment should remain.

## Residual scope

Repository history, manifests, packaging, downstream code, compiler/backend correctness, binaries, and any source other than the two supplied target files were neither provided nor part of this exact source-level claim. No whole-crate or later-snapshot verdict is implied.
