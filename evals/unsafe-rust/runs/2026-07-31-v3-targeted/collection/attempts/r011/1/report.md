# Focused unsafe-Rust audit and redesign

## Claim, snapshot, and verdicts

**Audited artifact.** Exact `lib.rs` with SHA-256
`b2d9d02f117745925aa24c5b09461c200c3f36f1d1e026c1f289f971711dc122`,
under `REQUEST.md` SHA-256
`2d044b4aa4dca16c51aeedd3bd9db58d182a0929e6b73a98478fdc2710094b8f`.
No generated source, dependencies, macros, FFI, or configuration branches occur
in the inspected artifact. Audit date: 2026-08-01. Unsafe-Rust skill identity:
`SKILL.md` SHA-256
`a0a75ef8a14497aa78b50b459981097ee99605c57fec95c637cf59aaa20fe766`.

**Supported set.** Exactly Rust and standard library 1.82.0; every target on
which this source and its used standard-library items exist; every ordinary
profile. This predicate comes directly from `REQUEST.md`. The proof and witness
below are parametric in target and profile: the source has no `cfg`, profile,
layout, pointer-width, panic-strategy, or generated-code branch relevant to
them.

**Soundness theorem.** Every well-typed safe use of the public surfaces is free
of Rust undefined behavior under Rust 1.82's documented abstract semantics,
with no caller-side safety precondition and no additional TCB assumptions.

**Verdicts.**

- Current-artifact soundness: **UNSOUND** over the entire supported set
  (`F-1`).
- Requested restricted behavior: **PROVED** for
  `increment::<Tail>(&mut pair)`: if the input is `[a, b]`, normal return leaves
  `[a, b.wrapping_add(1)]`, over the entire supported set (`P-2`).
- Source-documented postconditions: none. Consequently there is no
  `CONTRACT-BROKEN` finding. The user-requested `Tail` behavior is a separate
  reviewed requirement, not a retroactive restriction on the current generic
  safe API.
- Combined current-artifact result: **UNSOUND**, irrespective of the redesign.
  There is no conditional application claim.

## Boundary and configuration coverage

The complete public surface is: safe, downstream-implementable trait `Slot`
and its safe associated function `index` (`lib.rs:3-5`); constructible unit
struct `Tail` (`lib.rs:7`); the crate-owned safe `Slot for Tail` implementation
returning `1` (`lib.rs:9-13`); and safe generic function `increment`
(`lib.rs:15-18`). `increment` contains the sole unsafe operation. There are no
fields, unsafe declarations/impls, hidden items, callbacks, reexports, or
generated APIs. `Tail` carries no representation invariant. The relevant
cross-call proposition would have to be an invariant of every `S: Slot`, but
the safe trait boundary enforces none.

Because both the counterexample and the `Tail` proof depend only on a
two-element array, integer indices `1`/`2`, and the cited 1.82 contracts, they
cover every target/profile in the supported predicate without enumeration.
No test, build, execution, or tool-derived evidence was used.

## TCB audit log `TCB-R011-1`

No additional assumptions are admitted. These two accepted Rust 1.82
authoritative axioms are the complete consumed TCB:

- **AXIOM-GET.** For `slice::get_unchecked_mut`, an in-bounds index selects and
  returns a mutable reference to that element; the Safety section states:
  “Calling this method with an out-of-bounds index is undefined behavior even
  if the resulting reference is not used.”
  [Rust 1.82 documentation](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut).
  Consumers: `P-1`, `P-2`. Re-audit if the Rust version or contract changes.
- **AXIOM-WRAP.** `u32::wrapping_add` performs modular addition, wrapping at the
  type boundary.
  [Rust 1.82 documentation](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add).
  Consumer: `P-2`. Re-audit if the Rust version or contract changes.

Both exact pages were opened and their wording and version checked. There are
no dependency, environment, implementation, probabilistic, or tool entries;
no rejected or pending premises; and no prior audit was reused.

## Obligation ledger and proofs

**P-1 — unsafe call precondition: FAILED / UNSOUND.** At `lib.rs:16`, every
executed `S::index()` must be in `0..2`; AXIOM-GET makes an out-of-bounds call
UB. Neither `S: Slot` nor the safe trait contract constrains the result. A
well-typed, entirely safe downstream witness is:

```rust
struct Bad;
impl Slot for Bad { fn index() -> usize { 2 } }
let mut pair = [0, 0];
increment::<Bad>(&mut pair);
```

The call reaches `get_unchecked_mut(2)` on a length-two array, hence UB by
AXIOM-GET. The smallest false implication is
`S: Slot => S::index() < 2`. A safe caller cannot be assigned this undocumented
obligation.

**P-2 — crate-owned `Tail` behavior: PROVED.** `Tail::index()` returns `1`
(`lib.rs:11`); a `[u32; 2]` has indices `0` and `1`, so AXIOM-GET's bound is
satisfied and the returned reference designates element 1. The only write is
through that reference. AXIOM-WRAP proves the new value is the old value plus
one modulo `2^32`; element 0 is untouched. This derivation is target- and
profile-independent.

**Proof artifact.** The unsafe block has no adjacent `SAFETY` proof. This is a
missing proof artifact as well as an implementation defect: no truthful local
comment can derive P-1 for the current generic safe contract. Documentation
alone cannot repair it.

## F-1 — unconstrained safe implementer controls an unsafe index

- **Status/severity:** **UNSOUND / critical**; affects `increment` and the
  aggregate safe-surface theorem on every supported configuration.
- **Defect:** a caller-provided implementation of a safe trait supplies the
  safety-critical bound without validation, sealing, or an unsafe implementer
  contract.
- **UB witness:** the safe `Bad` program above. **Defined postcondition
  refutation:** not established or needed; the witness contains UB.
- **Minimum resolution:** eliminate the unchecked operation, validate the
  index, or enforce an implementer boundary. Merely adding a comment is
  insufficient.

## Recommended redesign

The most parsimonious abstraction is no generic abstraction at all:

```rust
pub fn increment(pair: &mut [u32; 2]) {
    pair[1] = pair[1].wrapping_add(1);
}
```

Its proposed safe contract has no precondition beyond a well-typed mutable
borrow. For input `[a, b]`, it returns with `[a, b + 1 mod 2^32]`. The fixed
array type and constant safe index enforce selection locally; AXIOM-WRAP
supplies the arithmetic result. It removes the unsafe block, the behavioral
implementer premise, the invariant fan-out, and all need for `Slot` and `Tail`.

**Migration delta.** Delete public `Slot` and `Tail`; change
`increment::<Tail>(&mut pair)` to `increment(&mut pair)`. Generic calls and
downstream `Slot` implementations cease to exist. This is a public breaking
change, expressly authorized because the abstraction is unreleased and those
uses need not be preserved. Required `Tail` behavior is unchanged.

The proposal is not implemented and has no artifact verdict. After
implementation, freshly audit the exact snapshot: enumerate its public
surface; verify the fixed index, modular result, and preservation of element
0; confirm absence of unsafe/generated/configuration-dependent paths; and
re-establish Rust-1.82 target/profile closure. Re-audit on any source, API,
support-predicate, or consumed standard-library-contract change.

## Residual scope

This is a source-level review of exactly the supplied files, not a compiler,
backend, binary, or broader-crate certification. No authoritative-documentation
or skill-guidance gap blocked the result. The unimplemented redesign remains
outside the current-artifact verdict.
