# Internal Kani contract macros

This private crate is never published. The Kani runner copies the repository to
an isolated temporary directory and injects this crate into that copy's manifest
as a `cfg(kani)` dependency. The checked-in manifests and published crates have
no dependency on it. Normal builds do not expand the attributes. CI also injects the dependency
for the no-features Kani build check; that matrix entry compiles and inspects
proof metadata without claiming verification.

`contract` emits Kani contract attributes and an unrestricted proof function next
to a free function, or an associated proof function next to a method in a
concrete inherent impl. Use it only under `cfg(kani)`:

```rust
#[cfg_attr(kani, zerocopy_kani_macros::contract(
    method, target = Example::increment,
    requires(x < u8::MAX),
    ensures(|result| *result == x + 1),
    solver = kissat,
))]
fn increment(x: u8) -> u8 { x + 1 }
```

Methods require the `method` option and a concrete owner in the target path. A
compile-time owner-type check rejects accidental use inside a generic impl; use
`contracts` for that case. Free-function proofs are placed in a sibling module,
which makes accidentally using that form inside an impl a compile error.

Free-function targets are inferred from the decorated function. An explicit
method target must resolve to the annotated method; placing `contracts` on
the whole impl instead infers its owner and every annotated method target.
Each argument is
created independently with `kani::any` and passed without modification. Immutable
references borrow an arbitrary owned value. Input patterns, preconditions and
postconditions remain on the original function. Multiple `requires` and `ensures`
clauses are supported, as are `solver` and `unwind` options. Unwinding checks must
remain enabled. Unsupported inputs produce compile errors; there is no bounded
fallback for slices, pointers, mutable references or opaque input types.

For a generic inherent impl, `contracts` knows the enclosing type and emits
non-generic proof functions outside the impl:

```rust
#[cfg_attr(kani, zerocopy_kani_macros::contracts(
    instances(byte(E = u8), word(E = u16))
))]
impl<E: Copy> Example<E> {
    #[cfg_attr(kani, contract(ensures(|r| *r == core::mem::size_of::<E>())))]
    fn width(&self) -> usize { core::mem::size_of::<E>() }
}
```

Generic functions use the same `instances(label(T = ConcreteType))` option on
`contract`. Each case must bind every type parameter exactly once. Generic
methods inside generic impls form the Cartesian product of the impl cases and
method cases. Lifetime and const parameters and trait impls are unsupported.
The `__kani_contract_` proof-name prefix is reserved for these generators.

## Verification obligations

CI must discover and successfully verify every generated harness, with contract
assertions, memory-safety, overflow, undefined-function and unwinding checks
retained. Failed, missing, undiscovered and timed-out proofs establish nothing.
The compiled-inventory check in `tools/kani/check_generated.py` rejects replacement
stubs, verified stubs, expected-panic proofs and recursive contract assumptions in
generated proofs, including attributes introduced by another macro. Handwritten
caller harnesses may use substitutions. CI verifies the complete, unfiltered
suite in one configuration; every generated contract proof must succeed. Proof
ordering adds no guarantee to this conjunction. Kani does not enforce that a
contract was proved before `stub_verified` uses it: filtered local caller runs
must separately verify every required full-domain contract proof in the same
configuration. A passing substituted caller alone establishes nothing about
the replaced implementation. Cyclic-dependency support is deferred.

The instances list generates proofs; it does **not** restrict Kani's substitution
scope. Whenever relying on a generic contract via `stub_verified`, the user must
ensure every replaced concrete instance reachable in the harness, including
transitive calls, is in the list and has a successful full-domain proof in the
same configuration. Naming one instance in `stub_verified` does not establish
this: Kani 0.60.0 can replace other instances of the same generic function.
Unlisted calls executing the implementation without substitution are permitted.
Automatic type-list enforcement is deferred.

`Arbitrary` models must cover every valid input in the contract's domain. A
custom `Arbitrary` implementation that excludes values narrows the proof. Owned
reference generation is suitable for these value-only functions; it does not
establish coverage of arbitrary heap graphs, alias relationships or external
state. Contract expressions and their helpers must not narrow proof execution
through hidden assumptions. Unsafe calls require all Rust safety preconditions
to be captured by the declared preconditions or established by argument creation.
The macro cannot infer English safety obligations or specification adequacy.

These are conditional proofs in the selected Kani model/configuration, not an
all-target Rust soundness certification. Existing tool/model/solver trust remains.

## Tests

Run `cargo test --manifest-path tools/Cargo.toml -p zerocopy-kani-macros` for the
parser and generator tests. With Kani 0.60.0 installed, run
`python3 tools/kani-macros/tests/verify.py` for real compiler inventory checks and
positive/negative verification. The false contract differs only at `u8::MAX`,
checking that argument generation retains the full input domain.
