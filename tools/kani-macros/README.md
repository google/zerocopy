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
`contracts` for that case. Free-function proofs are sibling functions in the
same lexical scope, so their calls cannot bind to a same-named function in a
parent module. An empty sibling module rejects use of that form inside an impl.
Block-local contracted functions are unsupported by Kani's target resolver;
code generation or the compiled-inventory check must reject them.

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

CI must discover and inspect every generated harness, and successfully verify
every enabled harness, with contract
assertions, memory-safety, overflow, undefined-function and unwinding checks
retained. Failed, missing, undiscovered and timed-out proofs establish nothing.
The compiled-inventory check requires every compiled contracted function to own
at least one discovered generated proof and every generated proof to be linked
to exactly one contracted function. This catches undiscovered contracts and
incorrect target resolution.

Generated proofs may use `stub_verified(path)` clauses to replace dependencies
with their contracts. After fresh code generation, `tools/kani/check_generated.py`
binds each reachable replacement to a generated proof using its actual compiled
function symbol, including its concrete generic arguments. Missing providers,
duplicate providers and cyclic dependencies fail the check. Dependencies hidden
in preconditions, postconditions, input generators and function pointers are
included. The checker conservatively includes unreachable call-graph edges, so
it can reject some harmless programs. Plain stubs, expected-panic proofs and
recursive contract assumptions remain forbidden, including attributes introduced
by another macro.

Each generated proof must execute its selected implementation. Pinned Kani
selects Check by function definition, so nested invocations of that definition
assume its preconditions. The checker rejects direct, indirect and callback
reentry, including calls to another concrete generic instance. It also rejects
argument generation or cleanup which invokes the selected checking dispatcher:
such a call could assume false and suppress the actual proof. Missing or
unrecognized graph markers fail the check.

CI compiles and checks the complete inventory in one configuration, then
verifies every enabled harness. Every selected generated proof and its
transitive dependency providers must succeed. An acyclic graph makes the conjunction of these
proofs usable inductively; proof ordering alone adds no guarantee. Kani does not
itself enforce that a contract was proved before `stub_verified` uses it. A
filtered local caller run must separately verify all transitive providers in the
same configuration and run the graph checker over the complete generated
inventory. A passing substituted caller alone establishes nothing about the
replaced implementation. Handwritten caller harnesses may use substitutions;
they still require successful full-domain proofs for every replaced instance.

The instances list generates proofs; it does not restrict Kani's substitution
scope. Kani 0.60.0 may replace other instances of the same generic function when
one instance is named in `stub_verified`. The compiled graph checker enforces
provider coverage for generated proofs and handwritten harnesses that use
verified stubs. Selection includes every transitive provider in the same run.
Those providers must all succeed in the same configuration. Unlisted calls executing the implementation without
substitution are permitted.

`Arbitrary` models must cover every valid input in the contract's domain. A
custom `Arbitrary` implementation that excludes values narrows the proof. Kani
also uses `Arbitrary` to generate substituted return values. Those models must
include every value the implementation can return (covering every valid value
of the type is the simplest sufficient obligation). A narrowed return model can
make a caller pass incorrectly even when its callee's contract was proved. The
graph checker cannot establish model completeness. Owned
reference generation is suitable for these value-only functions; it does not
establish coverage of arbitrary heap graphs, alias relationships or external
state. Contract expressions and their helpers must not narrow proof execution
through hidden assumptions. Unsafe calls require all Rust safety preconditions
to be captured by the declared preconditions or established by argument creation.
The macro cannot infer English safety obligations or specification adequacy.

These are conditional proofs in the selected Kani model/configuration, not an
all-target Rust soundness certification. Existing tool/model/solver trust remains.

## Ignored contracts and manual verification

Add `ignore = "reason"` to an individual `contract` annotation to keep its
proof available without running it in the default CI suite:

```rust
#[cfg_attr(kani, zerocopy_kani_macros::contract(
    ensures(|r| *r == x),
    ignore = "Solver resources; #3792",
))]
fn identity(x: u8) -> u8 { x }
```

The reason must be a nonblank string literal of at most 32 UTF-8 bytes.
Keep it brief and link the issue: Kani uses mangled proof names as filenames,
so a long encoded reason can exceed filesystem basename limits. Long enclosing
paths can still exceed Kani's limit; such compilation failures establish no proof. On generic contracts, every
explicit concrete proof instance is ignored. This option does not change the
function body, contract clauses, input generation or Kani checking attributes.
Ignored means unverified; a skipped proof establishes nothing about its contract.

Pinned Kani does not retain arbitrary annotation metadata. The macro appends a
reserved `__zerocopy_ignore_` suffix containing the reason's UTF-8 bytes as
lowercase hexadecimal to each proof identifier. The runner reads only the fresh
compiled inventory; it rejects malformed reasons and missing or undiscovered
proofs, including ignored ones. The marker is reserved for generated proof
names. Ignored proofs still undergo all compiled contract and dependency checks.

Run the default suite, every proof, or only ignored proofs respectively:

```sh
python3 tools/kani/check_crate.py
python3 tools/kani/check_crate.py --include-ignored
python3 tools/kani/check_crate.py --ignored
```

The default suite prints each skipped proof and reason. The two ignore switches
are mutually exclusive. `--ignored` also runs any enabled dependency providers
needed by its ignored roots. An empty selection fails rather than reporting a
vacuous success. `--check-no-features-build` inspects models without running
verification and reports that distinction explicitly.

`--harness FULL_COMPILED_NAME` selects an exact proof name from the compiled
inventory and automatically includes all its transitive providers. The option
is repeatable; unknown names fail. Selecting an ignored proof explicitly opts
into its ignored dependency closure. Selecting an enabled proof does not: an
enabled root which substitutes an ignored contract is rejected unless
`--include-ignored` is also supplied. With explicit names, `--include-ignored`
authorizes ignored providers rather than adding unrelated proofs. Combining
`--ignored` with explicit names requires those roots to be ignored.

The runner rejects any enabled default proof that relies on an ignored contract,
including indirect dependencies, pre/postcondition helpers and handwritten
verified-stub harnesses. Merely calling the original implementation is allowed;
it does not assume that implementation satisfies the skipped contract. Manual
runs retain the same safety checks and must successfully verify their entire
selected dependency conjunction. A passing substituted caller with a failed
provider is never an accepted result.

## Tests

Run `cargo test --manifest-path tools/Cargo.toml -p zerocopy-kani-macros` for the
parser and generator tests. With Kani 0.60.0 installed, run
`python3 tools/kani-macros/tests/verify.py` for real compiler inventory checks and
positive/negative verification. Boundary-only failures check the full input
domain and all four impl/method instance combinations. Compile rejection cases
cover wrong owners, unsupported inputs and block-local homonyms.

Run `python3 tools/kani-macros/tests/verify_dependencies.py` for real dependency
checks and verification controls, including missing concrete providers, cycles,
invalid preconditions and incomplete return models.

Run `python3 tools/kani-macros/tests/verify_ignored.py` for real compiled ignore
metadata, default/manual selection, failed-provider propagation and enabled
generated/handwritten caller rejection, cross-instance generic replacement
coverage and execution of ignored callees without substitution.
