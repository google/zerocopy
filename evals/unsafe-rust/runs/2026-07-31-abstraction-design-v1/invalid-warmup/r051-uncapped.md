# Unsafe Rust Audit: `r051::View`

## Claims and verdicts

- **Soundness claim requested:** for the exact 23-line `lib.rs` snapshot, every
  well-typed safe use of `View<'a, T>` is free of Rust undefined behavior on
  Rust 1.70+, on every target and in every ordinary profile.
- **Soundness verdict: `UNSOUND` (FINDING-1).** A well-typed, entirely safe
  client can obtain two simultaneously live `&mut` references to the same
  `i32` and pass both to one safe function. Rust 1.70 classifies breaking the
  pointer-aliasing rules as undefined behavior and states that references
  passed to a function are live for at least that call. One in-domain Rust
  version and execution refutes the requested universal Rust-1.70+ theorem;
  the witness is otherwise target- and ordinary-profile-independent.
- **Documented-postcondition claim:** there are no unsafe public APIs or
  separately documented postconditions in the supplied snapshot.
- **Documented-postcondition verdict:** not applicable. The invalid references
  are accounted for by the soundness verdict, not relabeled as a mere
  postcondition failure.
- **Combined mandatory result:** `UNSOUND`.
- **Conditional application claim:** none.
- **Scope:** `View`, its private representation, `new`, `get`, `get_mut`, and
  language-supplied move/drop/auto-trait behavior visible from this source.
- **Supported configurations:** Rust 1.70 or later; every target on which this
  source is accepted; ordinary debug/release profiles and panic strategies.
- **TCB:** `TCB-r051-2026-07-31`, embedded below. No dependency, platform,
  compiler-backend, deployment, or tool-result assumption is consumed.

## Audited snapshot

- **Source:** `/tmp/unsafe-rust-design-20260731.1RGvAj/targets/r051/lib.rs`,
  exactly as supplied (23 lines).
- **Request:** `REQUEST.md`, lines 3–8.
- **Prior result reused:** none. `DESIGN-NOTE.md` was read only as context; its
  conditional sketch verdict was not inherited.
- **Rust/standard library:** source-level abstract semantics, with the
  counterexample grounded directly in Rust 1.70 documentation.
- **Dependencies, generated artifacts, build scripts, macros, FFI, assembly:**
  none in the supplied artifact.
- **Execution evidence:** none; the target was not built, tested, expanded, or
  executed.
- **Audit date:** 2026-07-31.

## Boundary and API coverage

| ID | Surface | Kind | Disposition |
|---|---|---|---|
| API-1 | `pub struct View<'a, T>` (line 5) | safe public type | Representation fields are private, but safe methods expose the invariant incorrectly. |
| API-2 | `ptr: *mut T` (line 6) | private invariant-bearing field | Constructed only by `new`; consumed by both unsafe blocks. |
| API-3 | `PhantomData<&'a mut T>` (line 7) | private marker field | Ties the view's type to the unique borrow/lifetime, but does not tie method results to receiver borrows. |
| API-4 | `View::new` (lines 11–13) | safe constructor | Constructor itself is sound and establishes the intended pointer/lifetime relationship. |
| API-5 | `View::get` (lines 15–17) | safe method backed by unsafe | `UNSOUND` in composition: it can create a shared reference while a prior `get_mut` result is live. |
| API-6 | `View::get_mut` (lines 19–21) | safe method backed by unsafe | `UNSOUND`: repeat calls can create simultaneously live sibling mutable references. |
| API-7 | move/drop and implicit traits | safe language surface | No custom impl or drop code exists. These surfaces do not repair or hide API-5/API-6. |

There are no public fields, trait impls, callbacks, reexports, hidden items,
operators, macros, generated APIs, free functions, statics, or FFI entrypoints
in the supplied source.

## Invariant inventory

**INV-1 — borrowed target.** For a `View<'a, T>` produced by `new`, `ptr` is the
raw pointer obtained from the input `&'a mut T`, and the private
`PhantomData<&'a mut T>` makes the type act as though it carries that borrow.
The fields are private, so safe clients cannot replace either component.

**INV-2 — reference discipline.** Whenever an unsafe block converts `ptr` to a
reference, the target must still satisfy the reference's lifetime, validity,
and aliasing requirements for the entire time that reference is live. `new`
and INV-1 address target identity/lifetime. They do **not** serialize references
returned by the methods, because both return lifetime `'a` rather than the
lifetime of the receiver borrow. INV-2 is therefore false for permitted safe
transitions.

## Obligation ledger

| ID | Site | Exact obligation | Status |
|---|---|---|---|
| OBL-1 | `new`, lines 11–13 | Safe construction must establish pointer identity and keep the source borrow represented for `'a`. | `PROVED` for values constructed through this private-field constructor, using AXIOM-PHANTOM and ordinary typed coercion. |
| OBL-2 | `get`, line 16 | `&*ptr` must create a valid shared reference, including absence of a simultaneously live conflicting mutable reference. | `UNSOUND`; a prior `get_mut` result may remain live while `get` is called. |
| OBL-3 | `get_mut`, line 20 | `&mut *ptr` must create a valid unique mutable reference, including absence of another live reference to the target. | `UNSOUND`; FINDING-1 supplies a safe witness with two live results. |
| OBL-4 | every safe transition | INV-2 must be preserved across arbitrary call sequences. | `UNSOUND`; method-result lifetimes are detached from receiver borrows. |
| OBL-5 | unsafe proof artifacts, lines 16 and 20 | Each raw-pointer-to-reference conversion needs an adjacent derivation of all validity, lifetime, and aliasing obligations. | Missing/deficient; FINDING-2. Comments cannot repair FINDING-1. |

## Material derivation and counterexample

The method signature at line 19 is effectively
`for<'s> fn(&'s mut View<'a, T>) -> &'a mut T`: the returned lifetime is `'a`,
not `'s`. Consequently the temporary mutable borrow of `view` can end after
each call while its result remains live. This safe client is admitted by the
public signatures:

```rust
fn touch(x: &mut i32, y: &mut i32) {
    *x += 1;
    *y += 1;
}

let mut value = 0;
let mut view = View::new(&mut value);
let first = view.get_mut();
let second = view.get_mut();
touch(first, second);
```

Both results come from the same unchanged `ptr`. During `touch`, both mutable
references are live and point to the same `i32`. The
[Rust 1.70 Reference](https://doc.rust-lang.org/1.70.0/reference/behavior-considered-undefined.html#behavior-considered-undefined)
lists violation of pointer-aliasing rules as undefined behavior, applies the
scoped no-alias rule to `&mut T`, and states: “When a reference ... is passed
to a function, it is live at least as long as that function call.” Thus the
safe witness reaches undefined behavior. No concrete execution is needed.

The same lifetime detachment also permits `get` and `get_mut` results to
overlap, so changing only one method is insufficient.

## Findings

### FINDING-1 — receiver-independent result lifetimes permit aliased references

- **Status/severity:** `UNSOUND`; refutes the requested safe-API theorem.
- **Source:** `lib.rs` lines 15–20, especially both explicit `-> &'a ...`
  return types.
- **Required proposition:** every reference created from `ptr` must obey Rust's
  lifetime and aliasing rules for its full liveness interval.
- **Defect:** `PhantomData<&'a mut T>` constrains the lifetime of the `View`, but
  it does not make a borrow of the `View` last for `'a`. The return types allow
  a safe caller to end the receiver borrow and create another reference while
  the first result remains live.
- **Counterexample:** the safe `touch(first, second)` witness above.
- **Affected configurations:** at least Rust 1.70 on every accepting target and
  ordinary profile; this is sufficient to falsify the quantified Rust-1.70+
  claim. The defect is source-semantic and has no `cfg` or profile branch.
- **Minimum resolution:** tie both return values to their receiver borrow (and
  re-audit the implemented snapshot), or consume the view when returning a
  reference with lifetime `'a`.
- **Compatibility:** shortening the public result lifetimes rejects call
  patterns previously accepted by the type checker and is an API/contract
  change, even though it closes a soundness defect. Affected releases should be
  treated as defective rather than retroactively reinterpreted.

### FINDING-2 — both unsafe blocks lack local safety proofs

- **Status:** proof-artifact defect; the implementation is already `UNSOUND`
  independently of this documentation finding.
- **Source:** lines 16 and 20.
- **Missing derivation:** pointer identity, allocation liveness, alignment,
  initialized/valid `T`, provenance/accessibility, and the complete shared or
  unique aliasing interval are not stated or proved.
- **Authority:** Rust 1.70
  [`core::ptr` safety documentation](https://doc.rust-lang.org/1.70.0/core/ptr/index.html#safety)
  and the Reference page cited above.
- **Resolution:** first repair the API. If a raw pointer remains, add adjacent
  `SAFETY` proofs for the newly implemented receiver-bound methods and audit
  them afresh. A comment on the current signatures cannot establish the false
  uniqueness premise.

## Configuration closure

- **Axes found:** Rust version; target; optimization/debug assertions; panic
  strategy. There is no conditional compilation, feature gate, target-specific
  code, generated code, allocation, concurrency primitive, FFI, or assembly.
- **Coverage argument:** the counterexample uses `i32`, private-field-preserving
  safe calls, and language reference semantics only. No code selection or
  profile behavior affects the duplicate raw-pointer conversion. It therefore
  refutes the all-target/all-ordinary-profile claim at Rust 1.70.
- **Open-ended version range:** proving every later release separately is not
  necessary to reject a universal range containing 1.70. No affirmative
  `PROVED` claim is made for an open-ended future range.
- **Test coverage:** none, by instruction; none is needed for the refutation.

## TCB audit log — `TCB-r051-2026-07-31`

| ID | Category | Exact proposition | Identity/scope | Consumers | Disposition / trigger |
|---|---|---|---|---|---|
| AXIOM-UB-170 | AXIOM | Breaking Rust pointer-aliasing rules is UB; `&mut T` uses scoped no-alias semantics; references passed to a function are live during that call. | Rust Reference 1.70, [Behavior considered undefined](https://doc.rust-lang.org/1.70.0/reference/behavior-considered-undefined.html#behavior-considered-undefined); all targets/profiles covered by that page. | OBL-2–4, FINDING-1 | Exact official page inspected and accepted as Rust authority. Re-audit if the supported Rust floor or cited semantics change. |
| AXIOM-PTR-170 | AXIOM | A raw pointer used to produce a reference must satisfy applicable validity and aliasing requirements. | Rust 1.70 `core::ptr`, [Safety](https://doc.rust-lang.org/1.70.0/core/ptr/index.html#safety). | OBL-1–3, FINDING-2 | Exact official page inspected. Re-audit on contract change. |
| AXIOM-PHANTOM-170 | AXIOM | `PhantomData<T>` tells the compiler that the containing type acts as though it stores a `T`; its lifetime example makes a pointer wrapper act as if it contained the indicated reference. | Rust 1.70 [`PhantomData`](https://doc.rust-lang.org/1.70.0/core/marker/struct.PhantomData.html). | INV-1, OBL-1 | Exact official page inspected. It does not imply dynamic uniqueness of method results. Re-audit on contract change. |

No safe/unsafe dependencies, external specifications, implementation claims,
tools, deployment restrictions, probabilistic assumptions, or out-of-band
premises are admitted. There are no rejected or pending premises used to reach
the `UNSOUND` verdict.

## Recommended redesign (unimplemented)

The current finding above is unchanged by this proposal. With no stated need
for a raw representation, prefer eliminating the unsafe code:

```rust
pub struct View<'a, T> {
    value: &'a mut T,
}

impl<'a, T> View<'a, T> {
    pub fn new(value: &'a mut T) -> Self {
        Self { value }
    }

    pub fn get(&self) -> &T {
        &*self.value
    }

    pub fn get_mut(&mut self) -> &mut T {
        &mut *self.value
    }
}
```

The elided output lifetimes are tied to the receiver borrows. Shared results
may coexist; a live result prevents the conflicting mutable receiver borrow,
and a mutable result prevents another receiver borrow. The representation also
lets safe Rust carry target lifetime/validity directly, eliminating both unsafe
blocks and their raw-pointer TCB surface.

If retaining the raw pointer is a binding representation requirement, the
minimum candidate is to keep the private fields but change the signatures to
`fn get(&self) -> &T` and `fn get_mut(&mut self) -> &mut T`, then add complete
adjacent `SAFETY` derivations. If consumers genuinely require an `&'a mut T`, a
separate consuming operation such as `fn into_mut(self) -> &'a mut T` can return
it only after consuming the sole view capability.

- **Behavior delta:** target identity and read/write access remain; the ability
  to retain a result while borrowing the same `View` again is intentionally
  removed. A consuming `into_mut` can preserve legitimate long-lived mutable
  access.
- **Migration:** update callers to scope results to receiver borrows or consume
  the view. Review any public compatibility policy and affected-release
  disclosure.
- **Fresh-audit status:** **not implemented; no verdict.** Audit the exact new
  source independently after implementation, including all exposed methods and
  implicit traits.

## Documentation/skill gaps, residual scope, and triggers

- **Authoritative documentation gap:** none needed for this refutation. Rust
  1.70's exact text supplies the required aliasing/liveness proposition.
- **Skill guidance gap:** none observed.
- **Residual scope:** no crate metadata, edition declaration, Cargo features,
  downstream uses, compatibility policy, or later-release source was supplied;
  no whole-crate or binary claim is made. This does not limit the in-source safe
  counterexample.
- **Re-audit triggers:** any implementation or signature change; adding fields,
  constructors, trait impls, macros, `cfg`, dependencies, or unsafe operations;
  changing the Rust support floor; or material changes to the cited Rust
  contracts.

## Final attestation

Every in-scope surface and unsafe operation has a disposition; the supported
configuration claim is refuted by an in-domain parametric witness; every
consumed authority was inspected at its exact Rust 1.70 URL; no clean-test or
absence-of-counterexample reasoning is used. Independent review was not
performed.
