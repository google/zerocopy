# Mode L Frozen Blind-Scoring Rubric

> **Evaluator-only material. Never expose this file to a report agent.**

> Evaluator-only material. Never expose this file, its atom labels, expected
> result, or hard-error rules to an evaluated report agent.

## Exact result

Within the scope in `REQUEST.md`, `last` is sound. On the `else` branch,
`bytes.is_empty()` evaluated to false. The documented relation between
`is_empty` and slice length therefore gives `bytes.len() != 0`. Slice length has
type `usize`, whose values are nonnegative, so `bytes.len() > 0`. Consequently
`bytes.len() - 1` neither underflows nor overflows and mathematical subtraction
gives `index < bytes.len()`. This is precisely the in-bounds fact required by
`get_unchecked` for a `usize` index.

The existing comment states only a lifetime fact. It does not address the
unsafe callee's in-bounds obligation, the facts which establish it, or the
derivation between them. It is therefore a deficient proof artifact even though
the implementation obligation can be reconstructed. A replacement must expose
that chain locally and must link or unambiguously refer to the checked,
version-matched authority entries it consumes.

## Atoms

- **L1 — Callee obligation:** State that the executed `get_unchecked(index)`
  requires `index` to be in bounds, equivalently `index < bytes.len()` for this
  `usize` index, and that an out-of-bounds call is UB.
  - `scope_basis`: `lib.rs` contains this unsafe call and `REQUEST.md` asks for
    an implementation soundness audit.
  - `dependencies`: none.
- **L2 — Branch fact:** Establish from the actual `if`/`else` control flow that
  `bytes.is_empty()` is false on the unsafe-call path, then use the exact
  `is_empty` contract to conclude `bytes.len() != 0`.
  - `scope_basis`: necessary source-path premise for the requested local proof.
  - `dependencies`: none.
- **L3 — Unsigned-domain step:** Establish that the slice length is a `usize`
  and, using its nonnegative value domain, derive `bytes.len() > 0` from L2.
  - `scope_basis`: necessary material bridge from nonemptiness to safe
    subtraction in every supported pointer width.
  - `dependencies`: L2.
- **L4 — Defined subtraction:** Establish that `bytes.len() - 1` has no integer
  overflow or underflow on this path, including in every ordinary profile.
  - `scope_basis`: the source performs built-in integer subtraction before the
    unsafe call; its definedness is part of the requested soundness proof.
  - `dependencies`: L3.
- **L5 — In-bounds derivation:** Use the assignment
  `index = bytes.len() - 1` and ordinary integer arithmetic to derive
  `index < bytes.len()`.
  - `scope_basis`: the exact proposition needed to discharge L1.
  - `dependencies`: L3, L4.
- **L6 — Implementation closure:** Connect L2–L5 to L1 and report the
  implementation obligation `PROVED` over the entire stated Rust/target/profile
  scope; do not infer implementation failure from comment failure.
  - `scope_basis`: `REQUEST.md` explicitly asks for an implementation verdict
    over its full scope.
  - `dependencies`: L1, L2, L3, L4, L5.
- **L7 — Artifact verdict:** Separately report the existing `SAFETY` comment
  materially deficient because its lifetime statement does not address either
  the exact in-bounds obligation or the material derivation which discharges
  that obligation.
  - `scope_basis`: `REQUEST.md` explicitly asks for a separate comment-adequacy
    determination.
  - `dependencies`: L1, L2, L3, L4, L5.
- **L8 — Replacement proof artifact:** Supply proposed adjacent comment text
  which identifies the `get_unchecked` obligation and exposes the L2–L5 chain,
  with unambiguous references to the checked authority propositions.
  - `scope_basis`: `REQUEST.md` explicitly requests replacement wording when
    material reconstruction is needed.
  - `dependencies`: L1, L2, L3, L4, L5.
- **L9 — Complete premise inventory:** Inventory every materially consumed
  Rust/std premise: `if` branch selection, `is_empty`/length equivalence,
  `len`'s type/meaning, `usize`'s value domain, built-in
  subtraction/overflow, and `get_unchecked`'s safety contract. Classify the
  immediate placement and assignment observations as source facts and the
  remaining integer implications as mathematics rather than inventing
  authority for them.
  - `scope_basis`: `REQUEST.md` explicitly requires a complete Rust-premise
    inventory and reconciliation; distinguishing source facts and mathematics
    identifies which proof leaves require Rust/std authority.
  - `dependencies`: L1, L2, L3, L4, L5.
- **L10 — Exact checked authority:** For every Rust/std entry in L9, give the
  matching Rust 1.82.0 narrow URL, quote the exact prose which supplies the
  premise, state the verified proposition, and qualify its applicability. Page
  identity or an unexamined citation alone does not pass.
  - `scope_basis`: `REQUEST.md` explicitly requires version-matched checked
    authority and exact extracted propositions.
  - `dependencies`: L9.
- **L11 — Reconciliation:** Explicitly reconcile proof to inventory: every
  materially consumed Rust/std premise has an L10 entry, every listed entry is
  actually consumed, and no TCB assumption or uncited Rust fact silently fills
  a link.
  - `scope_basis`: `REQUEST.md` explicitly requires this reconciliation and
    states that the TCB is empty.
  - `dependencies`: L1, L2, L3, L4, L5, L9, L10.

Score atoms independently. Mathematical implications between stated integer
facts need derivation but no Rust citation. Immediate source syntax may be cited
by source location rather than external authority.

## Hard errors

- **LH1:** Report the implementation `UNSOUND` or `UNPROVED` solely because the
  existing comment is deficient, despite reconstructing L1–L5 correctly.
- **LH2:** Explicitly call the existing comment adequate.
- **LH3:** Claim the requested implementation proof complete while omitting a
  material link from L1–L5.
- **LH4:** Claim the requested authority/premise reconciliation complete while
  silently consuming a Rust/std premise, using an inapplicable version, or
  treating a page URL as proof without checking the proposition.
- **LH5:** Use build, test, execution, lint, or dynamic-analysis success as a
  universal proof of this obligation.

An omitted artifact verdict fails L7 but is not independently a hard error
unless the report also makes an affirmative false claim covered above.

## Checked authority

- Rust 1.82.0 slice `get_unchecked`:
  `https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked`
  — for a `usize` element index, an out-of-bounds call is UB even when the
  result is unused; the proof consumes the corresponding `index < len`
  requirement.
- Rust 1.82.0 slice `len`:
  `https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len`
  — returns the number of elements as `usize`.
- Rust 1.82.0 slice `is_empty`:
  `https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty`
  — returns true exactly when the slice has length zero.
- Rust 1.82.0 Reference, `if` expressions:
  `https://doc.rust-lang.org/1.82.0/reference/expressions/if-expr.html#if-expressions`
  — when the condition evaluates to false, the consequent block is skipped and
  the trailing `else` block is executed.
- Rust 1.82.0 Reference, arithmetic operators:
  `https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators`
  — `-` is built-in subtraction for integer operands.
- Rust 1.82.0 Reference, integer overflow:
  `https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#overflow`
  — identifies overflow for built-in integer operators and its profile/context
  behavior; L3 proves the exceptional case absent here.
- Rust 1.82.0 Reference, unsigned integer value domains:
  `https://doc.rust-lang.org/1.82.0/reference/types/numeric.html#integer-types`
  — `usize` is an unsigned integer type and its values are nonnegative.

There is no accepted TCB entry for this mode.
