# Focused unsafe-Rust audit and redesign

## Claim, domain, and verdicts

**Snapshot.** The complete supplied `lib.rs` (lines 1–18), with no generated artifacts or third-party dependencies in scope. Audit cutoff: 2026-08-01.

Let `T` be exactly “every target on which this exact source and its used Rust 1.82.0 standard-library items exist,” and `P` exactly “every ordinary profile.” `Required(case)` is the given source, Rust/compiler/stdlib 1.82.0, target in `T`, profile in `P`, every input/state/type and execution of every well-typed safe use of its public safe surfaces. The separately required behavioral domain is every valid `&mut [u32; 2]` passed to `increment::<Tail>`.

| Claim | Verdict | Certificate |
|---|---|---|
| Every required safe use is free of Rust UB | **UNSOUND** | `F-UB` below gives a valid safe use, reaches `get_unchecked_mut`, falsifies its bounds requirement, and the applicable Rust 1.82.0 contract expressly entails UB. |
| For initial `[a,b]`, `increment::<Tail>` returns with `[a, b.wrapping_add(1)]` | **PROVED** | `P-TAIL` covers every `a,b: u32`, target in `T`, and profile in `P`. |
| Existing local unsafe-proof documentation | **DEFICIENT** | The unsafe block has no adjacent `SAFETY` proof, and its needed universal premise is false. |

The redesign below does not participate in these current-artifact verdicts.

## Boundary and obligation inventory

All language-reachable surfaces are: public safe trait `Slot` and its public safe associated function `index` (3–5); public unit struct and constructor `Tail` (7); its safe `Slot` implementation (9–13); and public safe generic function `increment` (15–18). There are no unsafe declarations, fields, macros, callbacks, FFI, concurrency, allocation, generated code, `cfg`, or configuration-selected paths. The sole unsafe operation is `pair.get_unchecked_mut(S::index())` (16); its result is consumed by wrapping addition and assignment (17). The only proposed invariant—`S::index() < 2` for every `S: Slot`—has no owner or enforcement boundary and is false.

The source is identical across the symbolic `T × P` domain. Its explicit `wrapping_add` is profile-independent; no target fact, layout, panic strategy, or code-generation premise enters either certificate. Thus the proofs below are parametric over every configuration fiber, not sampled. No build or test evidence was used.

## Checked Rust 1.82.0 axioms

TCB `R82-AUTH-1` contains only these exact authoritative Rust 1.82.0 propositions; there are no additional assumptions.

- `AX-VIS`: a `pub` item is accessible externally, subject to accessible ancestors ([Reference](https://doc.rust-lang.org/1.82.0/reference/visibility-and-privacy.html#visibility-and-privacy)).
- `AX-IMPL`: a trait implementation is valid under the orphan rules when the implementing type is local; unsafe traits require `unsafe impl` ([trait implementations](https://doc.rust-lang.org/1.82.0/reference/items/implementations.html#trait-implementations)). Rust describes an unsafe trait as one whose implementation may be unsafe and whose impl must use `unsafe` ([unsafe traits](https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits)). `Slot` is not declared unsafe.
- `AX-BOUNDARY`: extra unchecked safety conditions belong on `unsafe fn`; an unsafe block asserts that all called-operation obligations were discharged ([unsafe functions and blocks](https://doc.rust-lang.org/1.82.0/reference/unsafe-keyword.html#unsafe-functions-unsafe-fn)). `increment` is a safe `fn`.
- `AX-GET`: `get_unchecked_mut` returns the selected mutable element without checking bounds, and: “Calling this method with an out-of-bounds index is undefined behavior even if the resulting reference is not used.” ([standard library](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut)).
- `AX-WRAP`: `u32::wrapping_add` performs modular addition, wrapping at the type boundary ([standard library](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add)).

## Proofs and finding

### F-UB — caller-controlled safe trait breaks the unchecked access

A downstream crate may write the entirely safe witness:

```rust
struct Bad;
impl Slot for Bad { fn index() -> usize { 2 } }
let mut pair = [0, 0];
increment::<Bad>(&mut pair);
```

Validity: `Slot` and `increment` are public (`AX-VIS`); `Bad` is local to that downstream crate, satisfying the orphan alternative in `AX-IMPL`; neither the impl nor call accepts an unsafe obligation (`AX-IMPL`, `AX-BOUNDARY`). Reachability: `Bad::index()` returns 2, after which line 16 necessarily calls `get_unchecked_mut(2)` on the two-element array viewed as a length-two slice. False proposition: valid indices are below 2, so 2 is out of bounds. Consequence: `AX-GET` directly classifies that executed call as UB, even before line 17 uses the reference. The witness uses only values representable wherever this source exists, so it applies throughout `T × P`. This completes the existential `UNSOUND` certificate. There is no UB-free postcondition counterexample in scope from this witness.

The smallest current implementation resolution is to stop passing unchecked memory-safety authority through a caller-controlled safe trait. Documentation alone cannot repair the safe API.

### P-TAIL — required crate-owned behavior

For arbitrary initial `[a,b]`, the inspected `Tail::index` returns 1. Since `1 < 2`, line 16 satisfies `AX-GET` and obtains the unique mutable reference to element 1. Line 17 computes `b + 1` modulo the `u32` range by `AX-WRAP` and stores it through that reference; element 0 is not accessed or assigned. Hence normal return yields exactly `[a, b.wrapping_add(1)]`. These source facts and axioms are independent of target and ordinary profile, so `Required_tail ⊆ Covered_tail` over all `T × P`.

## Preferred provable abstraction

Specialize to the sole required operation and remove both the implementer boundary and unsafe code:

```rust
pub fn increment(pair: &mut [u32; 2]) {
    pair[1] = pair[1].wrapping_add(1);
}
```

**Contract.** This safe function has no caller safety precondition beyond a valid exclusive array reference. For every initial `[a,b]`, it returns `[a, b.wrapping_add(1)]`. The fixed array type supplies length two, constant index 1 is in bounds, and the only arithmetic uses the documented modular operation. No representation invariant, unsafe implementer promise, or extra TCB entry remains.

**Migration delta.** Delete public `Slot`, `Tail`, their impl, and the generic parameter. Change crate-owned calls from `increment::<Tail>(&mut pair)` to `increment(&mut pair)`. Downstream `Slot` impls and generic calls cease to compile; the request expressly authorizes that break because the abstraction is unreleased and only the Tail operation must survive. The observable required mutation is unchanged.

**Fresh audit after implementation.** Treat the edit as a new snapshot. Re-inventory exports and all call sites; verify the exact implementation and any documentation; prove constant index 1 is in bounds for `[u32; 2]`, the wrapping postcondition, unchanged element 0, and absence of alternate exits for every `T × P` case; rescan conditional/generated surfaces and residual unsafe code. Any source, API contract, Rust version, target/profile policy, or generated/build input change triggers re-audit. No verdict is assigned to the unimplemented proposal.

## Residual scope

No broader safe-API behavior, binary/backend correctness, other source, or future version is claimed. Source execution, building, testing, and macro expansion were excluded by instruction and supply no premise. No authoritative-documentation or skill-guidance gap blocked either certificate.
