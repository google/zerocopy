# Unsafe Rust Audit: `r053` implemented candidate

## Claim and verdict

- **Soundness claim:** For the exact `lib.rs` snapshot identified below, every well-typed safe use is free of Rust undefined behavior on Rust 1.70 and later, on every target and in every ordinary profile, relative only to the stated Rust-language TCB.
- **Soundness verdict:** **UNSOUND.** `View::get` and `View::get_mut` return references for the stored lifetime `'a`, not for the lifetime of their receiver borrow. Entirely safe client code can consequently obtain a live `&T` and an aliased live `&mut T`, then mutate through the latter.
- **Documented-postcondition result:** There is no separate unsafe API or prose postcondition. The validity and aliasing guarantees embodied by the safe reference return types are part of the soundness claim and are violated by FINDING-001.
- **Combined mandatory result:** **UNSOUND** (FINDING-001). FINDING-002 separately records missing local proof documentation.
- **Conditional application claim:** None.
- **Prior result reused:** None. `DESIGN-NOTE.md` was treated only as history, as required by `REQUEST.md`.
- **TCB log:** `TCB-r053-1`, embedded below.

Rust 1.70.0 is itself a member of the requested `1.70+` range, so the Rust 1.70 counterexample refutes the universal range claim. No backwards-compatibility premise about later Rust versions is needed. The defect is source-level and uses no target-, optimizer-, panic-, or profile-specific behavior.

## Audited snapshot and scope

- `lib.rs` SHA-256: `ac762e6e2bd87884bbbcfbe7bbf706e5b9dae9b078e82d01252111a9a6ad84e8`
- `REQUEST.md` SHA-256: `5dfbf15c9d36ddead0fa5d694549c70bd67fa971f89799640b6d886dfbd131c3`
- `DESIGN-NOTE.md` SHA-256: `7e40f341429ae1711132d4660a0fa2aaa105045309c03b09e28a837c7b6176fc`
- **Source scope:** all items in the supplied `lib.rs` and their language-reachable safe uses.
- **Rust scope:** Rust 1.70 and later, as requested. The decisive authority and witness are scoped to 1.70.0.
- **Configuration scope:** every target and ordinary profile. The source contains no `cfg`, feature selection, build script, generated code, FFI, assembly, allocation, concurrency, or profile-dependent branch.
- **Dependencies:** only `core::marker::PhantomData`; no third-party dependency.
- **Execution evidence:** none. The target was not built, tested, expanded, or executed. The verdict is a source derivation.
- **Auditor/date:** Codex source review, 2026-07-31.

## Boundary and API coverage

| ID | Surface | Classification | Disposition |
|---|---|---|---|
| API-01 | `pub struct View<'a, T>` (`lib.rs:5`) | Public safe type; fields private | Downstream safe code cannot forge or replace `ptr` or `borrow` directly. Move and ordinary drop do not dereference `ptr`. |
| API-02 | `View::new(&'a mut T) -> View<'a, T>` (`lib.rs:11`) | Safe constructor | Creates the raw pointer from the supplied mutable reference and stores the lifetime marker. It performs no unsafe operation, but its intended exclusivity invariant is not preserved by the accessors. |
| API-03 | `View::get(&self) -> &'a T` (`lib.rs:15`) | Safe method backed by unsafe dereference | **UNSOUND in composition with API-04.** Its return lifetime is not tied to the `&self` borrow. |
| API-04 | `View::get_mut(&mut self) -> &'a mut T` (`lib.rs:19`) | Safe method backed by unsafe dereference | **UNSOUND.** Its return lifetime is not tied to the `&mut self` borrow, so the same `View` remains callable while the returned reference is live. |
| API-05 | Implicit move/drop and auto-trait behavior | Language-generated behavior | No destructor, trait impl, macro, callback, or cross-thread behavior is needed by the counterexample. Moving/dropping the two fields performs no pointee access. |

There are no public fields, explicit trait implementations, free functions, statics, macros, generated APIs, reexports, hidden items, FFI entrypoints, callbacks, operators, or custom destruction behavior in the supplied source.

## Invariant inventory

### INV-VIEW — intended uniquely borrowed view

While a `View<'a, T>` can be used, `ptr` is intended to designate the initialized `T` originally borrowed by `new`, and every reference produced from `ptr` must obey Rust's lifetime and aliasing rules. The type and its private fields own this invariant. `new` is the producer; `get` and `get_mut` are consumers and reference producers; move/drop terminate or transfer the representation without dereferencing it.

**Status: BROKEN.** Privacy prevents pointer forgery, and the marker records `'a`, but neither accessor couples its returned reference to its receiver borrow. After either accessor returns a long-lived reference, safe code can call another accessor through the still-usable `View`. Thus the representation has no enforced transition that suspends use of `View` for the returned reference's lifetime.

## Authoritative premises and derivation

`AXIOM-170-ELISION` is the Rust 1.70.0 Reference's [lifetime-elision rule](https://doc.rust-lang.org/1.70.0/reference/lifetime-elision.html#lifetime-elision-in-functions). It says the receiver lifetime is “assigned to all elided output lifetime parameters.” In the candidate, the receiver lifetimes are elided, but each output lifetime is explicitly the impl parameter `'a`. Therefore that rule does not tie either output to the temporary `&self`/`&mut self` borrow. By contrast, an output written as `&T` or `&mut T` would be elided and would be tied to the receiver.

`AXIOM-170-UB` is the Rust 1.70.0 Reference's [undefined-behavior list](https://doc.rust-lang.org/1.70.0/reference/behavior-considered-undefined.html). For a reference passed to a function, it guarantees liveness “at least as long as that function call.” It also classifies mutation of ordinary data reached through a shared reference as mutation of immutable data; its stated exception is data contained in `UnsafeCell`, which does not apply to `u8`.

The following is a well-typed downstream use containing no `unsafe` operation:

```rust
fn collide(shared: &u8, unique: &mut u8) -> u8 {
    *unique = 1;
    *shared
}

fn safe_witness() -> u8 {
    let mut value = 0u8;
    let mut view = View::new(&mut value);
    let shared = view.get();
    let unique = view.get_mut();
    collide(shared, unique)
}
```

Derivation:

1. `new` stores a raw pointer to `value`.
2. `get` returns `shared` with lifetime `'a`. Because that output is explicitly `'a`, its lifetime is not the receiver borrow, so the borrow of `view` used for this call does not prevent the later mutable receiver call.
3. `get_mut` returns `unique`, also with lifetime `'a`; both references designate the same `u8` through the same stored pointer.
4. `collide` receives both references. Under `AXIOM-170-UB`, both are live for that call.
5. `*unique = 1` mutates the non-`UnsafeCell` bytes reached through the live shared reference. This is listed undefined behavior.

This is a concrete valid safe-use UB witness, so lack of testing or a more complete formal aliasing model cannot weaken the verdict to `UNPROVED`.

## Obligation ledger

| ID | Site | Exact obligation | Status |
|---|---|---|---|
| OBL-01 | `View::new` | Safe construction itself must not cause UB and must establish the initial pointer/lifetime relationship consumed by accessors. | **PROVED for immediate construction only.** It contains no unsafe operation and derives `ptr` directly from the input reference. It does not establish the missing future-access discipline. |
| OBL-02 | `get` unsafe block | Creating and returning `&'a T` must preserve validity and shared-reference aliasing for all of `'a`, for every safe call sequence. | **UNSOUND** via FINDING-001: a later safe `get_mut` permits mutation during the returned shared reference's liveness. |
| OBL-03 | `get_mut` unsafe block | Creating and returning `&'a mut T` must provide exclusive access for all of `'a`, for every safe call sequence. | **UNSOUND** via FINDING-001: the receiver becomes usable before the returned reference ends; repeated `get_mut`, or `get` followed by `get_mut`, creates conflicting aliases. |
| OBL-04 | Field privacy | Safe callers must not forge or replace the invariant-bearing raw pointer/marker. | **PROVED for the supplied artifact.** Both fields are private and there is no other source in the target. |
| OBL-05 | Move/drop | Moving or dropping `View` must not access an invalid pointee or duplicate ownership. | **PROVED for the supplied source.** There is no `Drop` implementation; the raw pointer and marker fields do not own or dereference the pointee during ordinary field drop. |
| OBL-06 | Local proof artifacts | Each unsafe reference construction needs an adjacent derivation of pointer validity, lifetime, and aliasing obligations. | **UNPROVED / missing documentation** via FINDING-002. Neither unsafe block has a `SAFETY` comment or named-invariant citation. |

## Findings

### FINDING-001 — accessor return lifetimes permit safe aliasing UB

- **Status/severity:** **UNSOUND / critical**.
- **Affected claim:** universal safe-use soundness.
- **Source:** `get` at `lib.rs:15-16`; `get_mut` at `lib.rs:19-20`; all requested targets and ordinary profiles are source-equivalent.
- **Required proposition:** every reference formed from `ptr` must have an alias-compatible lifetime, and a mutable reference must exclude every conflicting reference while live.
- **Defect:** both outputs use the stored lifetime `'a`; neither uses the receiver-borrow lifetime. `PhantomData<&'a mut T>` constrains the `View`'s relationship to the original borrow, but it does not make an explicitly `'a` method result borrow `self` for `'a`.
- **Counterexample:** `safe_witness` above. It is entirely safe and reaches UB under the Rust 1.70 Reference premises.
- **Minimum resolution:** bind both outputs to their receiver borrows, for example:

  ```rust
  pub fn get<'s>(&'s self) -> &'s T { /* ... */ }
  pub fn get_mut<'s>(&'s mut self) -> &'s mut T { /* ... */ }
  ```

  The equivalent elided signatures are `get(&self) -> &T` and `get_mut(&mut self) -> &mut T`. If a raw pointer is unnecessary, the smaller safety boundary is to store `&'a mut T` directly and remove both unsafe blocks.
- **Proposal status:** **UNIMPLEMENTED AND NOT AUDITED.** The signatures above directly address this counterexample, but they are not a verdict on a changed snapshot. A fresh audit must verify the complete raw-pointer invariant, variance/drop behavior, all safe surfaces, and adjacent proofs after implementation.
- **Compatibility:** changing these return lifetimes can reject callers that relied on retaining a result while reusing or dropping the `View`. That behavior is currently unsound; remediation still requires normal affected-version and compatibility handling.

### FINDING-002 — both unsafe blocks lack local safety proofs

- **Status/severity:** proof artifact **UNPROVED / missing**; implementation independently **UNSOUND** by FINDING-001.
- **Source:** `lib.rs:16` and `lib.rs:20`.
- **Required proof:** identify the reference-construction obligations; establish that `ptr` remains aligned, non-dangling, and points to initialized `T`; derive alias permission for the precise returned lifetime; and state how INV-VIEW is preserved.
- **Existing proof:** none.
- **Resolution:** after correcting the API, state INV-VIEW next to the representation and add an adjacent `SAFETY` proof to each dereference. No truthful comment can prove the current `'a` signatures sound, so documentation-only repair is insufficient.

## Configuration closure

The supported predicate is the exact source compiled by Rust 1.70 or later for any target and ordinary profile. There are no conditional or generated paths. The lifetime signatures and the two unsafe dereferences are identical across the set; debug assertions, overflow behavior, optimization, panic mode, allocator, and target layout do not participate. The witness uses only one `u8` and ordinary references. In any event, the required theorem universally quantifies over Rust versions/configurations, and its Rust 1.70.0 member is refuted, which is sufficient to establish the combined `UNSOUND` verdict.

## TCB audit log: `TCB-r053-1`

| ID | Category | Exact proposition consumed | Identity/scope | Disposition | Consumer |
|---|---|---|---|---|---|
| AXIOM-170-ELISION | AXIOM | Receiver-lifetime substitution applies to elided output lifetimes; it does not rewrite the candidate's explicit `'a` output. | Rust 1.70.0 Reference, lifetime elision | Verified authoritative premise for this refutation | FINDING-001 steps 2-3 |
| AXIOM-170-UB | AXIOM | References passed to a function are live for that call; mutating non-`UnsafeCell` data reached through a shared reference is UB. | Rust 1.70.0 Reference, behavior considered undefined | Verified authoritative premise for this refutation | FINDING-001 steps 4-5 |

No safe/unsafe third-party dependency, external specification, compiler implementation, tool theorem, deployment condition, probabilistic premise, or backwards-compatibility premise is consumed. These entries support an `UNSOUND` refutation, not a `PROVED` certification. Re-audit is required if the source, contracts, supported lower Rust bound, or relevant authoritative text changes.

## Residual scope, documentation gaps, and review triggers

- No authoritative-documentation gap blocks the counterexample.
- No broader behavioral property such as panic freedom, performance, or SemVer compatibility was requested or proved.
- No binary/backend correctness claim is made.
- The proposed repair remains outside the audited snapshot and has no verdict.
- Re-audit after any accessor-signature, representation, visibility, constructor, trait-implementation, Rust-support, or configuration change. Re-audit the complete changed source rather than inheriting this report or the prior design note.

## Final attestation

Every source-visible unsafe operation, invariant producer/consumer, and safe API surface in the supplied artifact has a disposition above. The final verdict rests on a valid safe-use source counterexample and checked Rust 1.70.0 authoritative premises, not on testing or absence of failures. No independent review was performed.
