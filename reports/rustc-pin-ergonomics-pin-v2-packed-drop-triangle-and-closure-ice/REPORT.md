# rustc structural pinning (`pin_ergonomics`, `#[pin_v2]`): type identity, projection gates, packed and drop soundness, and the capture-analysis ICE

## Summary

- **`&pin mut T` is `Pin<&mut T>`.** Under `#![feature(pin_ergonomics)]`, rustc lowers the type
  syntax `&pin mut T` / `&pin const T` at AST-to-HIR lowering to the lang-item path
  `Pin<&mut T>` / `Pin<&T>`. There is one type, not two: `TypeId`s are equal, either spelling is
  accepted where the other is expected, a pinned reference is implicitly reborrowed at coercion
  sites and method calls (no `.as_mut()`), and patterns can project through it
  (`let &pin mut S { ref pin mut a, ref mut b } = p;`, or by match ergonomics `let S { a, b } = p;`).
- **Safe projection is sound only because of a set of compile-time gates.** The source of the
  two later revisions examined (2026-11-11 and 2026-11-22) contains checks that enforce: (1) *opt-in*: destructuring
  below a pinned reference requires the struct to be `#[pin_v2]`, an unpinned `ref`/`ref mut`
  binding below a pinned reference requires the field type to be `Unpin`, and a `#[pin_v2]`
  type may not have an explicit `Unpin` impl; (2) *packed*: a `#[pin_v2]` type may not be
  `#[repr(packed)]`, because the drop glue of a packed type moves under-aligned fields before
  destroying them; (3) *drop*: a `#[pin_v2]` type may not implement `Drop::drop(&mut self)`,
  only `Drop::pin_drop(&pin mut self)`, and no type may implement both. A value that is dropped
  without ever having been pinned still reaches `pin_drop`, because the provided body of
  `Drop::drop` is `unsafe { Drop::pin_drop(Pin::new_unchecked(self)) }`.
- **The 2026-05-31 nightly lacks two of these checks and is unsound in safe code.** At
  `rust-lang/rust` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` the packed gate does not exist and
  the opt-in check is applied only to match-ergonomics patterns, not to explicit `&pin` patterns.
  Programs with `#![forbid(unsafe_code)]` were executed on that compiler that (a) observe a
  pinned `!Unpin` field being destroyed at a different address than the one it was pinned at
  and (b) poll a self-referential future, move it, free its old storage and poll it again, which
  Miri reports as a use-after-free under both Stacked Borrows and Tree Borrows. Both holes were
  closed upstream in June 2026 (`rust-lang/rust` pull requests 157542 and 157680); the checks
  are present in the source of the two later revisions.
- **Closure and coroutine bodies that use an explicit `&pin` pattern or a pinned reborrow do
  not compile.**
  `ExprUseVisitor`, which rustc runs for closure and coroutine capture analysis, calls
  `cat_deref` on a place of type `Pin<&T>` without first projecting field 0 of `Pin`. It does so
  at two sites: the `PatKind::Ref` arm of `cat_pattern` (explicit `&pin` patterns) and the
  `Adjust::Deref` arm of `cat_expr_adjusted_with` (the implicit pinned reborrow). The result is
  the delayed bug "explicit deref of non-derefable type", which surfaces as an internal
  compiler error with exit status 101, as a spurious E0381, or as the immediate ICE "could not
  resolve upvar", depending on the program. On the 2026-05-31 nightly, once the feature is
  enabled, a bare `.await`, a `Pin<&mut Self>` method call inside a closure, or an explicit
  `&pin` pattern inside a closure or `async fn` is enough to trigger it; plain `fn` bodies and
  match-ergonomics patterns do not. The responsible source file is byte-identical at the
  2026-11-11 nightly and at the tip of `main` on 2026-11-22, and three upstream issues about it
  were open on that date. No accepted-but-miscompiled program results: compilation always
  fails.
- **A kernel-checked Lean model states the argument and its sharpness.** With all gates on, the
  destructor of a projected `!Unpin` field runs at the address it was pinned at; switching off
  any single gate admits a concrete counterexample; the `Drop::drop` shim is sound for values
  dropped before their first pin; projecting field 0 before the dereference repairs both
  categorization sites. All 31 theorems are free of axioms.
- **Anneal's trusted MIR fragment currently sits entirely outside this feature.** At
  `joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613` struct types (including `Pin<_>`),
  closure and coroutine types, and `Drop` terminators are all classified as unsupported and
  fail closed, and the compiler revision it names for MIR capture predates both soundness
  fixes.

## Applicability

**Subjects and how they relate.** `REPORT.json` lists five subjects.

| Subject | Role in this report | How it was examined |
| --- | --- | --- |
| `rust-lang/rust` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, distributed as `nightly-2026-06-01`, with the Miri of the same toolchain) | Older revision; the only one executed | source read at that commit; every probe executed on 2026-11-22 on `x86_64-unknown-linux-gnu` |
| `rust-lang/rust` `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`) | Newer revision containing both soundness fixes | source read at that commit; execution only through a preserved record of an earlier run (2026-11-21) that was not repeated |
| `rust-lang/rust` `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (tip of `main` when resolved on 2026-11-22) | Checks whether the newer findings still hold at the tip | source only |
| `joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613` | A verification toolchain whose trusted MIR semantics is compared with what this feature needs | source only |
| `leanprover/lean4` `5045d0056413266e57c625dcd7c365b10e377c52` (tag `v4.34.1`) | Kernel that checks the model in `support/PinErgonomicsSoundnessTriangle.lean` | executed |

The three `rust-lang/rust` revisions lie on one line of history: the GitHub compare API reports
`3ef0c22c` as 18,861 commits ahead of and 0 behind `14210df0`, and `342d7446` as 2,474 ahead of
and 0 behind `3ef0c22c`. The merge commits of the two soundness fixes
(`e43ec0c183b65f9f73d943ce470c4e6d0f6dc971` and `927b226fcaccff5452ce68c7dcf20baad5f68571`) are
descendants of `14210df0` and ancestors of `3ef0c22c`. The report is therefore a comparison of
one evolving subject at three points, plus one consumer of it.

**Configuration.** Everything concerns crates that enable `#![feature(pin_ergonomics)]`, which
rustc declares as an *incomplete* feature (`(incomplete, pin_ergonomics, "1.83.0", Some(130494))`
in `compiler/rustc_feature/src/unstable.rs`). Probes were compiled with `--edition 2024` and
`--cap-lints allow`, default (debug) code generation, and run under Miri with default flags
(Stacked Borrows) and with `-Zmiri-tree-borrows`. Without the feature gate neither the syntax
nor the attribute is accepted, and the compile failures described here do not occur (two
control probes confirm this).

**Exact observation versus extension.**

- Statements labelled *execution* are about `14210df0` on `x86_64-unknown-linux-gnu` only, unless
  they explicitly cite the preserved record for `3ef0c22c`.
- Statements about `3ef0c22c` and `342d7446` are *source* statements, or *derived* from source,
  unless they cite that record. The toolchain for `3ef0c22c` could not be installed on the
  authoring host (the distribution server was unreachable from it), so none of the probes in
  this package was run on it.
- For `342d7446`, a finding is extended from `3ef0c22c` only where the relevant file is
  byte-identical at both commits (stated per file under Evidence) or where the relevant lines
  were read at `342d7446` as well.
- Nothing here is a claim about stable Rust, about other targets, or about revisions between
  the three examined ones other than what the dated upstream pull requests establish.

## Findings

### F1. `&pin mut T` and `&pin const T` are spellings of `Pin<&mut T>` and `Pin<&T>`

AST lowering turns the syntactic type `TyKind::PinnedRef(region, ty, mutbl)` into an ordinary
HIR path to the `Pin` lang item with a single type argument that is an ordinary reference:

```rust
TyKind::PinnedRef(region, ty, mutbl) => {
    let lifetime = self.lower_ty_direct_lifetime(t, *region);
    let kind = hir::TyKind::Ref(lifetime, self.lower_ty_alloc(ty, itctx), *mutbl);
    let span = self.lower_span(t.span);
    let arg = hir::Ty { kind, span, hir_id: self.next_id() };
    let args = self.arena.alloc(hir::GenericArgs {
        args: self.arena.alloc([hir::GenericArg::Type(self.arena.alloc(arg))]),
        constraints: &[],
        parenthesized: hir::GenericArgsParentheses::No,
        span_ext: span,
    });
    let path = self.make_lang_item_qpath(LangItem::Pin, span, Some(args));
    hir::TyKind::Path(path)
}
```

(`compiler/rustc_ast_lowering/src/lib.rs:1544-1557` at `3ef0c22c`; the same arm is at
`1407-1420` at `14210df0`, where the AST node still carries a `MutTy`, and at `1581-1594` at
`342d7446`.) After lowering, the type is simply the `Pin` ADT applied to a reference; later
phases have no separate representation for the `&pin` spelling. The type-level helpers used by the rest of the compiler work on the `Pin` ADT: `Ty::pinned_ty` returns the type
argument of `Pin`, and `Ty::maybe_pinned_ref` recognises `Pin<&T>` / `Pin<&mut T>` alongside
plain references (`compiler/rustc_middle/src/ty/sty.rs`, `pinned_ty` at line 1405 and
`maybe_pinned_ref` at line 1420 at `3ef0c22c`).

Execution on `14210df0` (probe `a1_structural_projection_reborrow_drop`): the program prints
`SAME_TID=true`, where the flag is the conjunction of
`TypeId::of::<&'static pin mut Leaf>() == TypeId::of::<Pin<&'static mut Leaf>>()` and the same
comparison for `&pin const` / `Pin<&Leaf>`; a function declared with a `Pin<&mut Pair>` parameter
passes its argument unchanged to one declared with `&pin mut Pair`. The preserved record for
`3ef0c22c` also contains `SAME_TID=true`.

Basis: source + execution.

### F2. Pinned references are reborrowed implicitly

At a coercion site whose source and target are both pinned references, `coerce_to_pin_ref`
records the adjustments `[Adjust::Deref(DerefAdjustKind::Pin), Adjust::Borrow(AutoBorrow::Pin(m))]`
and imposes no `Unpin` obligation; when the source is an unpinned reference it uses
`DerefAdjustKind::Builtin` and adds an `Unpin` obligation
(`compiler/rustc_hir_typeck/src/coercion.rs:943-981` at `3ef0c22c` and `342d7446`, where the file
is byte-identical; `926-964` at `14210df0`). For method calls, a by-value pick whose receiver is
`Pin<&_>` gets `AutorefOrPtrAdjustment::ReborrowPin` when the feature is enabled
(`compiler/rustc_hir_typeck/src/method/probe.rs:1591-1600` at `3ef0c22c`, `1544-1553` at
`14210df0`), so `q.poll(cx)` reborrows `q` instead of moving it.

Execution on `14210df0`: `c05_fn_item_pinned_reborrow` (two sequential uses of the same
`&pin mut u32` as a function argument, then a read) is accepted, and `a1` uses one
`&pin mut Pair` three times. `c16_fn_item_overlapping_pinned_reborrows` keeps two reborrows alive
at once and is rejected with
``error[E0499]: cannot borrow `*q.pointer` as mutable more than once at a time`` — a borrow
error rather than a use-after-move error, and one that names the reborrowed place as the
dereference of `Pin`'s pointer field.

Basis: source + execution.

### F3. Patterns project through pinned references along two paths

There are two ways a pattern gets below a pinned reference, and they are implemented in
different places.

- **Implicit (match ergonomics).** When the scrutinee type is a pinned reference and the
  pattern is not a reference pattern, pattern checking peels the reference, records the pattern
  adjustment `PatAdjust::PinDeref` ("An implicit dereference before matching a `&pin` reference
  (under feature `pin_ergonomics`), which will be lowered as a builtin deref of the private
  field `__pointer` in `Pin`", `compiler/rustc_middle/src/ty/adjustment.rs:251-253` at
  `3ef0c22c`) and switches the default binding mode to pinned, so `let Pair { a, b } = p;` binds
  `a` and `b` as pinned references (`compiler/rustc_hir_typeck/src/pat.rs:532-559` at `3ef0c22c`,
  `535-575` at `14210df0`).
- **Explicit.** `&pin mut P` / `&pin const P` is a reference pattern handled by `check_pat_ref`
  (`pat.rs`, starting at line 2792 at `3ef0c22c`, 2755 at `14210df0`). When it matches a pinned
  reference type it sets `pat_info.max_pinnedness = PinnednessCap::Pinned` for the subpattern.
  Bindings inside are written explicitly as `ref pin mut x`, `ref pin const x`, `ref mut x`,
  `ref x`.

Both forms become the same THIR node, `PatKind::Deref { pin, subpattern }`
(`compiler/rustc_mir_build/src/thir/pattern/mod.rs:147-149` for the adjustment and `344-352`
for the explicit pattern at `3ef0c22c`), and MIR building lowers a pinned `Deref` by projecting
the field of `Pin` and then dereferencing:

```rust
PatKind::Deref { pin: Pinnedness::Pinned, ref subpattern } => {
    let pinned_ref_ty = match pattern.ty.pinned_ty() {
        Some(p_ty) if p_ty.is_ref() => p_ty,
        _ => span_bug!(pattern.span, "bad type for pinned deref: {:?}", pattern.ty),
    };
    let subpat = InterPat::lower_thir_pat(
        cx,
        // Project into the `Pin(_)` struct, then deref the inner `&` or `&mut`.
        place_builder.field(FieldIdx::ZERO, pinned_ref_ty).deref(),
        subpattern,
    );
```

(`compiler/rustc_mir_build/src/builder/matches/match_pair.rs:417-430` at `3ef0c22c` and
`342d7446`; the same arm starts at line 294 at `14210df0`, with the projection at line 301.) This "field 0, then deref" shape
is the reference point for F8.

Execution on `14210df0`: probe `a1` uses both forms on a `#[pin_v2]` struct with a `!Unpin`
field and a `u32` field, natively and under Miri with Stacked Borrows and with Tree Borrows. All
three runs exit 0 with no diagnostic and print
`SAME_TID=true PROJ_SUM=24 RIGHT_AFTER=12 DROP_PINNED_IN_PLACE=1 DROP_PINNED_MOVED=0 DROP_NEVER_PINNED=1`.
(`PROJ_SUM` and `RIGHT_AFTER` check that the three reborrowed calls mutated the `u32` field
through the projections as written; the `DROP_*` counters are explained in F5.)

Basis: source + execution.

### F4. The gates, and which revision has which

The table lists every compile-time check found that the soundness of safe projection depends
on. "exec" means the corresponding probe was run on `14210df0`; "record" means the outcome is in
the preserved 2026-11-21 record for `3ef0c22c`.

| Check | Diagnostic (first line) | `14210df0` (2026-05-31) | `3ef0c22c` (2026-11-11) | `342d7446` (2026-11-22) |
| --- | --- | --- | --- | --- |
| implicit projection requires `#[pin_v2]` | ``error: cannot project on type that is not `#[pin_v2]` `` | present, inline in the peeling arm (`pat.rs:546-560`); exec: `b02` rejected | present via `check_pin_projection` (`pat.rs:1529-1560`) | present (`pat.rs`, `check_pin_projection` at 1541) |
| explicit projection requires `#[pin_v2]` | same | **absent**; exec: `b01` accepted | present, same function; record: rejected | present, same function |
| unpinned by-reference binding below a pinned reference requires `Unpin` | ``error[E0277]: `PhantomPinned` cannot be unpinned`` | present (`pat.rs:1224-1234`); exec: `b03` rejected, `b04` (an `Unpin` field) accepted | present (`pat.rs:1228-1238`); record: rejected | present (`pat.rs`, starting at 1232) |
| no explicit `Unpin` impl for a `#[pin_v2]` type | ``error: explicit impls for the `Unpin` trait are not permitted for structurally pinned types`` | present (`coherence/builtin.rs:142-175`); exec: `b12` rejected | present (`coherence/builtin.rs:133-168`) | file byte-identical to `3ef0c22c` |
| `#[pin_v2]` type may not be `#[repr(packed)]` | ``error: `#[pin_v2]` types may not have `#[repr(packed)]` `` | **absent**; exec: `b10` (`packed`) and `b11` (`C, packed(2)`) accepted | present (`check/check.rs:1666-1679`); record: `#[repr(packed)]` rejected | present (`check/check.rs:1668-1681`) |
| `#[pin_v2]` type must implement `pin_drop`, not `drop` | ``error: `OnlyDrop` must implement `pin_drop` `` | present (`check/always_applicable.rs:374-435`); exec: `b05` rejected, `b06` accepted | present (`always_applicable.rs:373-435`); record: rejected / accepted | file byte-identical to `3ef0c22c` |
| no type may implement both `drop` and `pin_drop` | ``error: conflicting implementations of `Drop::drop` and `Drop::pin_drop` `` | present, same function; exec: `b07` (`#[pin_v2]`) and `b08` (unmarked) rejected | present; record: rejected | same |
| `pin_drop` may not be called explicitly | `error[E0040]: explicit use of destructor method` | present (`rustc_hir_typeck/src/callee.rs:37-60`); exec: `b13` rejected | present (`callee.rs:51-76`) | file byte-identical to `3ef0c22c` |

The paths are relative to `compiler/rustc_hir_typeck/src/` for `pat.rs` and to
`compiler/rustc_hir_analysis/src/` for `coherence/builtin.rs` and `check/*.rs`.

Source text that states the purpose of each check:

- `PinnednessCap` (`pat.rs:244-255` at `3ef0c22c`): "`ref` or `ref mut` bindings (not pinned,
  explicitly or match-ergonomics) are only allowed behind an `&pin` reference if the binding's
  type is `Unpin`. Normally, the borrow checker enforces this (not implemented yet), but we
  track it here for better diagnostics." The obligation is registered where a binding is
  checked: `if pat_info.max_pinnedness == PinnednessCap::Pinned && matches!(bm.0, ByRef::Yes(Pinnedness::Not, _)) { self.register_bound(expected, <Unpin lang item>, ..) }`.
- `check_pin_projection` (`pat.rs:1529-1560` at `3ef0c22c`): "Destructuring an ADT underneath a
  `&pin` reference projects its fields as pinned references. This is only sound if the type
  opted into structural pinning with `#[pin_v2]`; otherwise it would let safe code form a
  `Pin<&mut Field>` for a type that should never be pinned, breaking the `Pin` guarantee (see
  #157634). This covers both explicit (`&pin mut`/`&pin const`) and implicit (match-ergonomics)
  projection. `max_pinnedness` is only set for `&pin mut`, so the implicit shared (`&pin const`)
  case is instead recognized through its pinned binding mode, hence both are checked." It is
  called from `check_pat_struct` (line 1572) and `check_pat_tuple_struct` (line 1844).
- `visit_implementation_of_unpin` (`coherence/builtin.rs:133-168` at `3ef0c22c`): "a type `T`
  annotated with `#[pin_v2]` is allowed to project `Pin<&mut T>` to its field `Pin<&mut U>`
  safely (even if `U: !Unpin`). If `T` is allowed to impl `Unpin` manually (note that `Unpin` is
  a safe trait, which cannot carry safety properties), then `&mut U` could be obtained from
  `&mut T` that dereferenced by `Pin<&mut T>`, which breaks the safety contract of
  `Pin<&mut U>` for `U: !Unpin`."
- `check_packed` (`check/check.rs:1666-1679` at `3ef0c22c`): "`#[pin_v2]` on a packed type is
  unsound: drop glue for a packed type moves an over-aligned field to an aligned location before
  running its destructor, which would move a structurally pinned field out from under a
  `Pin<&mut _>` that was handed out." The test is `repr.packed()` on the type definition, so it
  does not depend on layout or on generic arguments.
- `check_drop_xor_pin_drop` (`check/always_applicable.rs:373-435` at `3ef0c22c`): "This function
  checks at least and at most one of `Drop::drop` and `Drop::pin_drop` is implemented. It also
  checks that `Drop::pin_drop` must be implemented if `#[pin_v2]` is present on the type."

The "triangle" in this report's title is the usual three-way summary (opt-in, packed, drop).
The source shows that the opt-in leg has three parts (the attribute check on projection, the
`Unpin` obligation on unpinned bindings, and the ban on explicit `Unpin` impls), and the
mechanized model in F9 shows that the ban on explicit `Unpin` impls is individually necessary.

Additional execution facts on `14210df0`: a type that is not `#[pin_v2]` may implement only
`pin_drop` (`b09` accepted); a reference to an under-aligned field of a packed struct is
rejected with E0793 on stable syntax (`b14`); without the feature gate both the `&pin mut`
syntax and the attribute are rejected with E0658 (`b15`).

Basis: source + execution (first column) / source + prior execution record (second column) /
source (third column).

### F5. `Drop::pin_drop`, and how values that were never pinned reach it

The `Drop` trait has the same text at all three revisions (`library/core/src/ops/drop.rs`,
byte-identical, SHA-256 `1d91c5e4e5868e8d2e6860da6fb5353f69172623a8ea7b9d7969e1ebd0fe7055`):

```rust
#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_default_body_unstable(feature = "pin_ergonomics", issue = "130494")]
fn drop(&mut self) {
    // SAFETY: `self` is pinned till after dropped.
    unsafe { Drop::pin_drop(Pin::new_unchecked(self)) }
}
...
#[unstable(feature = "pin_ergonomics", issue = "130494")]
fn pin_drop(self: Pin<&mut Self>) {}
```

(lines 241-246 and 266-267). An impl may write the receiver as `fn pin_drop(&pin mut self)`.
The drop glue is not specialised: it calls `Drop::drop`, and for a type that implements only
`pin_drop` that is the provided body above, which pins the value where it currently is and
calls `pin_drop`.

Execution on `14210df0`: probe `a5_drop_glue_forwarding` compiles a `pin_drop`-only type to LLVM
IR and finds the call chain `core::ptr::drop_glue::<OnlyPinDrop>` →
`<OnlyPinDrop as core::ops::drop::Drop>::drop` → `<OnlyPinDrop as core::ops::drop::Drop>::pin_drop`.
Probe `a1` exercises both lifetimes of a value whose destructor is `pin_drop`: a value pinned
on the stack with `pin!`, projected, and dropped in place (`DROP_PINNED_IN_PLACE=1`,
`DROP_PINNED_MOVED=0`), and a value that is never pinned, is moved to the heap and back, and is
then dropped (`DROP_NEVER_PINNED=1`): `pin_drop` runs for it as well, through the shim.

Why the shim's `Pin::new_unchecked` is justified (derived): the pin created by the shim is the
first pin of a never-pinned value, the drop glue owns the value exclusively, and after
`pin_drop` returns the value's fields are destroyed and its storage released without another
move — *provided* the drop glue itself does not move fields (F6) and the destructor body
cannot (the drop gate). For a value that was already pinned, the shim pins it again at the same
address. F9 states this as a theorem about event traces.

`rust-lang/rust` pull request 156495 ("Emit either mono item of `Drop::drop` or `Drop::pin_drop`
depending on which was implemented") would make the glue call `pin_drop` directly; it was open
and unmerged on 2026-11-22. Together with the identical trait text, the forwarding described
here is therefore taken to be the behaviour of the two later revisions as well (derived; the
glue's call chain was inspected by execution only on `14210df0`).

Basis: source + execution + derived.

### F6. Packed drop glue moves under-aligned fields, with or without structural pinning

`AddMovesForPackedDrops` is a required MIR pass (at `3ef0c22c` its policy is
`PassPolicy::Required` with the comment "Implements part of MIR semantics by making implicit
packed-drop handling explicit"; at `14210df0` it reports `is_required() == true`). For every `Drop` terminator whose place is
under-aligned inside a packed struct it rewrites `drop(place)` into
`drop_temp = move place; drop(drop_temp)`
(`compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs`, pass at lines 40-76 and
`add_move_for_packed_drop` from line 78 at `3ef0c22c`). The library documentation of `core::pin`
says the same at all three revisions: "if your type is `#[repr(packed)]`, the compiler will
automatically move fields around to be able to drop them. It might even do that for fields that
happen to be sufficiently aligned. As a consequence, you cannot use pinning with a
`#[repr(packed)]` type." (`library/core/src/pin.rs:630-633`).

Execution on `14210df0`, probe `a3_plain_packed_drop_moves_field` (no structural pinning
involved, so it is accepted by any compiler that has `pin_drop`): an alignment-8 leaf whose
`pin_drop` records its own address is placed in a `#[repr(packed)]` owner and in an identical
unpacked owner. Output, natively and under Miri with both borrow models:
`PACKED_OWNER_FIELD_DROPPED_INSIDE_OWNER=false PLAIN_OWNER_FIELD_DROPPED_INSIDE_OWNER=true`.
This is sound: the leaf was never pinned, so the move precedes its first pin (F5).

Basis: source + documentation + execution.

### F7. On the 2026-05-31 nightly the two missing gates are exploitable from safe code

Both programs below are `#![forbid(unsafe_code)]` and were accepted by `14210df0`.

**Packed (`a2_packed_pinned_field_moved_on_drop`).** `Outer` is `#[pin_v2] #[repr(packed)]` and
contains `mid: Mid` (alignment 8, hence under-aligned); `Mid` is `#[pin_v2]` and contains
`node: Node` (alignment 1, `!Unpin`). The pattern
`let &pin mut Outer { mid: Mid { ref pin mut node, .. }, .. } = outer.as_mut();` is accepted
because a reference to the alignment-1 `node` is not an unaligned reference. `Node` records its
address when first reached through the pinned reference and again in `pin_drop`. Output,
natively and under Miri with both borrow models: `PACKED_PINNED_FIELD_DROPPED_IN_PLACE=false`.
A `!Unpin` value was moved between being pinned and being destroyed. Miri reports no error for
this program: the pin guarantee is a library-level contract, and this execution has no
language-level undefined behaviour. The upstream report of this hole (`rust-lang/rust` issue
157011, "Unsoundness due to `#[pin_v2]` incorrectly handles packed structs.") uses the same
mechanism with `packed(4)` and an over-aligned generic argument.

**Unmarked projection (`a4_unmarked_projection_uaf` with helper crate `a4_selfref_future`).**
`struct Wrapper<F>(F); impl<F> Unpin for Wrapper<F> {}` is not `#[pin_v2]`, so the explicit
`Unpin` impl is legal. Because `Wrapper<F>: Unpin`, `Pin::new(&mut wrapper)` is safe; the
explicit pattern `let &pin mut Wrapper(ref pin mut f) = p;` then yields `Pin<&mut F>` for an
arbitrary `F`. The probe polls a compiler-generated self-referential future once through that
projection while it lives in a `Box`, moves it out of the box (which frees the allocation), and
polls it again. Results on `14210df0`:

- native: exit 0, printing `UNMARKED_PROJECTION_RESULT=<n>` with a value that changed between
  runs (109, 150, 232 and 252 were seen; the future computes 7);
- Miri, Stacked Borrows and Tree Borrows alike: exit 1 with
  `error: Undefined Behavior: constructing invalid value of type &[u8; 32]: encountered a dangling reference (use-after-free)`,
  located at the read through the self-reference inside the future.

The future is defined in a separate crate compiled *without* the feature gate, because on this
compiler any `.await` in a crate that enables the feature hits the failure of F8. The upstream
report (`rust-lang/rust` issue 157634, "`ref pin mut` pattern unsoundly allows pin-projecting
arbitrary types") demonstrates the address change and remarks that async code would turn it
into undefined behaviour if it compiled; the two-crate arrangement here is what makes that
observable.

**Status at the later revisions.** `rust-lang/rust` pull request 157542 ("Reject
`#[repr(packed)]` on `#[pin_v2]` types", merged 2026-06-09) added the packed gate and pull
request 157680 ("Require `#[pin_v2]` for explicit pin-projection patterns", merged 2026-06-12)
moved the opt-in check to the destructuring site so that it covers explicit patterns. Both
checks are in the source of `3ef0c22c` and `342d7446` (F4), and the preserved record for
`3ef0c22c` shows the two corresponding one-line reproducers rejected. Whether probes `a2` and
`a4` themselves are rejected there was not executed; that they are is derived from the checks:
`a2` defines a `#[pin_v2] #[repr(packed)]` struct, and `a4` destructures a tuple struct that is
not `#[pin_v2]` below `&pin mut`.

Basis: execution (`14210df0`) + source and prior execution record (`3ef0c22c`) + derived.

### F8. Capture analysis dereferences `Pin<&T>` places without projecting field 0

**Where.** `ExprUseVisitor` (`compiler/rustc_hir_typeck/src/expr_use_visitor.rs`; "In the
compiler, this is only used for upvar inference and diagnostics") walks closure and coroutine
bodies to decide what they capture. `compiler/rustc_hir_typeck/src/upvar.rs` invokes it as
`let _ = euv::ExprUseVisitor::new(&closure_fcx, &mut delegate).consume_body(body);` (lines 131
and 291 at `3ef0c22c`) and, in the handling of coroutine-closures, with `consume_expr` (line
687); at all three call sites the `Result` is discarded with `let _ =`. Plain function bodies
are not walked for capture analysis (probes `c01`, `c05` and `c14` compile).

**The helper that fails** (lines 1499-1519 at `3ef0c22c` and `342d7446`; 1506-1526 at
`14210df0`):

```rust
fn cat_deref(&self, node: HirId, base_place: PlaceWithHirId<'tcx>)
    -> Result<PlaceWithHirId<'tcx>, Cx::Error> {
    let base_curr_ty = base_place.place.ty();
    let Some(deref_ty) = self.cx
        .structurally_resolve_type(self.cx.tcx().hir_span(base_place.hir_id), base_curr_ty)
        .builtin_deref(true)
    else {
        debug!("explicit deref of non-derefable type: {:?}", base_curr_ty);
        return Err(self.cx
            .report_bug(self.cx.tcx().hir_span(node), "explicit deref of non-derefable type"));
    };
    ...
}
```

`Ty::builtin_deref(true)` returns `Some` for `Box`, for references and for raw pointers and
`None` otherwise (`compiler/rustc_middle/src/ty/sty.rs:1598-1609` at `3ef0c22c`); `Pin<&T>` is a
struct, so the result is `None`. For the type checker's context, `report_bug` is
`self.dcx().span_delayed_bug(span, msg.to_string())` (line 199 at `3ef0c22c`, line 200 at
`14210df0`).

**The one arm that handles pinned references correctly** is the pattern-adjustment arm
(lines 1654-1665 at `3ef0c22c`; 1661-1672 at `14210df0`):

```rust
adjustment::PatAdjust::PinDeref => {
    let target_ty = adjust.source.pinned_ty().ok_or_else(|| { /* report_bug */ })?;
    let kind = ProjectionKind::Field(FieldIdx::ZERO, FIRST_VARIANT);
    place_with_id = self.cat_projection(pat.hir_id, place_with_id, target_ty, kind);
    self.cat_deref(pat.hir_id, place_with_id)?
}
```

**The two arms that do not.**

1. Explicit reference patterns (lines 1763-1769 at `3ef0c22c`; at `14210df0` the arm is
   `PatKind::Box(subpat) | PatKind::Ref(subpat, _, _)` at lines 1770-1776). The second component
   of `PatKind::Ref`, the pinnedness, is ignored:

   ```rust
   PatKind::Ref(subpat, _, _) => {
       // &p1, &mut p1. we can ignore the mutability of
       // PatKind::Ref since that information is already contained
       // in the type.
       let subplace = self.cat_deref(pat.hir_id, place_with_id)?;
       self.cat_pattern(subplace, subpat, op)?;
   }
   ```

2. Expression adjustments (`cat_expr_adjusted_with`, lines 1269-1283 at `3ef0c22c`; 1276-1290 at
   `14210df0`). Only the overloaded kind is treated specially; `DerefAdjustKind::Pin` — the
   adjustment that the implicit pinned reborrow of F2 records — falls into the `else` branch and
   dereferences the previous place, whose type is `Pin<&T>`:

   ```rust
   adjustment::Adjust::Deref(deref_kind) => {
       let base = if let DerefAdjustKind::Overloaded(deref) = deref_kind {
           /* fresh rvalue of type `&target` */
       } else {
           previous()?
       };
       self.cat_deref(expr.hir_id, base)
   }
   ```

**Observed behaviour on `14210df0`** (execution; every probe is a library crate with
`#![forbid(unsafe_code)]`; "ICE" means exit status 101 with
`error: internal compiler error: explicit deref of non-derefable type`, preceded by
`note: no errors encountered even though delayed bugs were created` and carrying
`note: delayed at /rustc-dev/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_hir_typeck/src/expr_use_visitor.rs:200:20`):

| Probe | Body | Outcome |
| --- | --- | --- |
| `c01` | explicit `&pin mut Pair { ref pin mut a, ref mut b }` in a `fn` | accepted |
| `c02` | the same statement in a closure, scrutinee is a closure parameter | ICE (site 1) |
| `c03` | explicit `&pin const` pattern in a closure | ICE (site 1) |
| `c04` | match-ergonomics `let Pair { a, b } = q;` in a closure | accepted |
| `c05` | implicit pinned reborrows in a `fn` | accepted |
| `c06` | `let r: &pin mut u32 = q;` in a closure | ICE (site 2); the span is the coerced expression |
| `c07` | `q.poll(cx)` on `q: Pin<&mut F>` in a closure | ICE (site 2) |
| `c08` | `other().await` in an `async fn` | ICE (site 2); the span is `.await` |
| `c09` | the statement of `c01` in an `async fn` | ICE (site 1) |
| `c10` | the statement of `c02` applied to a captured variable | rejected: ``error[E0381]: used binding `b` isn't initialized`` (and the same for `a`) |
| `c11` | `take(p)` with a captured `p: &pin mut Pair` in a closure | immediate ICE: `.../compiler/rustc_mir_build/src/builder/expr/as_place.rs:263:67: could not resolve upvar: ... + [Field(0, &'{erased} mut Pair), Deref]` |
| `c12` | `c02` plus an unrelated type error | rejected with only `error[E0308]: mismatched types` |
| `c13` | `c07` without the feature gate | accepted |
| `c14` | `&pin` patterns in `fn` parameters | accepted |
| `c15` | `x.as_mut().poll(cx)` on a captured `x` inside `core::future::poll_fn` | immediate ICE `could not resolve upvar: ... + []` |

What the matrix establishes for `14210df0`:

- Function bodies are unaffected (`c01`, `c05`, `c14`); closures and coroutines are affected.
- The implicit pattern form works in closures (`c04`) because it goes through the
  `PatAdjust::PinDeref` arm; the explicit form does not.
- The expression site makes the feature unusable with ordinary async code: a single
  `other().await` is enough (`c08`; the span of the error is the `.await`, whose expansion
  passes a pinned reference to `Future::poll`), as is a single `Pin<&mut Self>` method call in
  a closure (`c07`). The same closure without the feature compiles (`c13`). That *every*
  `.await` fails is the expected generalisation, not something a finite set of probes shows.
- The failure is a delayed bug, so it is reported as an ICE only when no other error is
  (`c12`).
- When the dereferenced place is rooted in a captured variable, the aborted walk leaves capture
  information incomplete and the failure appears later in a different guise: a spurious borrow
  error (`c10`) or MIR building's `span_bug!` for an upvar it cannot resolve (`c11`, `c15`). The
  projection list printed for `c11`, `[Field(0, &mut Pair), Deref]`, is the place MIR building
  wanted — exactly "field 0, then deref".
- No accepted-but-wrong program can result (derived): once the delayed bug is recorded, the
  compilation session ends either with a real error or with the ICE.

**Status at the later revisions.**

- `expr_use_visitor.rs` is byte-identical at `3ef0c22c` and `342d7446` (SHA-256
  `597fb71bf13b02bbbc6912d8628c6188f15754c5ec78fa771c07fff2c884bb82`) and contains both arms as
  quoted; `coercion.rs` is byte-identical at those two commits as well and still records
  `DerefAdjustKind::Pin` for pinned reborrows. So both sites exist unchanged in the source of
  the two later revisions.
- The preserved record for `3ef0c22c` contains site 1: a closure with the statement of `c02`
  fails with exit status 101,
  `error: internal compiler error: explicit deref of non-derefable type`, and
  `note: delayed at /rustc-dev/3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1/compiler/rustc_hir_typeck/src/expr_use_visitor.rs:199:20`,
  while the same statement in a `fn` item compiles. Line 199, column 20 is the
  `span_delayed_bug` call at that commit, which agrees with the source read independently.
- Site 2 was not executed on either later revision; that it still fails there is derived from
  the source.
- Three upstream issues describe these failures and were open when queried on 2026-11-22:
  `rust-lang/rust` issue 149225 ("ICE `explicit deref of non-derefable type`", opened
  2025-11-19; its reproducer uses `&pin` patterns in `fn` parameters, which `14210df0` accepts,
  probe `c14`), issue 153733 ("[ICE]: `explicit deref of non-derefable type`", opened 2026-03-11;
  its reduced reproducer is the pair of `async fn`s of `c08`), and issue 154782 ("[ICE]: could
  not resolve upvar: ...", opened 2026-04-03; its reduced reproducer is the function of `c15`).

**Repair shape** (derived; not an upstream patch): at both sites, when the place has type
`Pin<&T>` and the dereference is a pinned one, first `cat_projection` with
`ProjectionKind::Field(FieldIdx::ZERO, FIRST_VARIANT)` and the pointer type, then `cat_deref` —
what the `PatAdjust::PinDeref` arm and MIR building already do. F9 proves that this yields the
same place as those two and leaves unpinned patterns unchanged.

Basis: source + execution (`14210df0`) + prior execution record (`3ef0c22c`, site 1 only) +
derived.

### F9. Mechanized model (Lean 4, no axioms)

`support/PinErgonomicsSoundnessTriangle.lean` (about 700 lines, imports only `Lean`) is checked
by Lean `v4.34.1` with warnings as errors. Its final command inspects the module and fails
unless every stated theorem depends on no axiom at all and no compiler-generated recursion
helper exists in the module; the recorded run reports
`audit ok: 408 module constants, 31 stated theorems, no axioms, no recursion helpers`. The model
has three parts.

**Part 1: where the destructor of a projected field runs.** A root value is pinned at
`inPlace 0`. A *path* is the list of nested structs from the root to a `!Unpin` leaf; each
`Level` records `pinV2`, `packed`, `fieldUnderAligned`, the destructor flavour (`none`,
`dropMut` for `drop(&mut self)`, `pinDrop`), whether the destructor body moves the field out,
whether there is an explicit `Unpin` impl, and the field offset. `pinnedAddr path` is the
address safe projection observes; `dropAddr path` is the address at which the drop glue
destroys the leaf, where a level relocates its field to a fresh temporary if the struct is
packed with an under-aligned field or if its destructor body moved the field. Addresses are an
inductive type with constructors `inPlace off` and `temp level off`, so storage of temporaries
is distinct from the pinned storage by construction. `accepts g leafUnpin path` is a Boolean
checker parameterised by which gates `g` are enforced (`optIn`, `noManualUnpin`, `packed`,
`drop`); two rules are always on: a destructor body can move the field only where safe Rust
gives it `&mut` to the field (always for `drop(&mut self)`; for `pin_drop` only if the field
type is `Unpin` or `Self: Unpin`), and the innermost projected field must not be under-aligned
(E0793).

- `pinV2_three_gate_preserves_pinned_address_through_drop`:
  `accepts Gates.all false path = true → dropAddr path = pinnedAddr path`.
- Sharpness — for each gate a concrete path that the checker accepts with exactly that gate
  off, that the full checker rejects, and for which `dropAddr ≠ pinnedAddr`:
  `ce1_packed_drop_copy_invalidates_self_ptr` (the layout of probe `a2`: pinned at
  `inPlace 9`, destroyed at `temp 0 8`),
  `ce2_unpinned_drop_mem_replace_invalidates_pinned_field` (a `#[pin_v2]` type whose
  `drop(&mut self)` moves the field out),
  `ce3_unmarked_struct_projection_violates_private_pin_invariant` (an unmarked struct with an
  explicit `Unpin` impl and an ordinary `Drop`, the situation of probe `a4`), and
  `ce5_manual_unpin_impl_lets_pin_drop_move_pinned_field` (a `#[pin_v2]` type with an explicit
  `Unpin` impl whose `pin_drop` reaches `&mut Self`).
- `explicit_patterns_at_14210df0e_accept_ce1_and_ce3`: with the gate set that F4 finds for
  explicit patterns at `14210df0` (no opt-in check on that path, no packed gate), the checker
  accepts both of those counterexamples, matching F7.
- `unpin_leaf_may_move_under_all_gates`: the theorem is about `!Unpin` leaves; an `Unpin` leaf
  may legitimately be moved by a `pin_drop` body.

**Part 2: the pin contract on a value's lifetime.** A lifetime is a list of events `move dst`,
`pin`, `destroy`; `pinContract start trace` holds when no `move` follows the first `pin` and
the value is destroyed where it was pinned. `dropShim = [pin, destroy]` is what the provided
`Drop::drop` body does.

- `unpinned_drop_shim_sound_before_first_pin`: for every start address and every list of moves,
  `pinContract start (moves.map move ++ dropShim) = true`.
- `pinned_then_dropped_in_place_sound` and `move_after_pin_violates_contract`.
- `never_pinned_leaf_always_sound` (a leaf that was never pinned satisfies the contract on every
  path, including packed ones — F6), `pinned_leaf_sound_iff_address_stable` (for a projected
  leaf the contract holds iff `dropAddr = pinnedAddr`), and their combination
  `three_gates_give_pin_contract`.

**Part 3: place categorization.** Types are `scalar`, `adt`, `ref`, `pin`; a place is a base
type with a list of `deref` / `field i` projections; `catDeref` fails with
`explicitDerefOfNonDerefableType` unless the place's type is a reference; `catPinDeref` is the
`PatAdjust::PinDeref` arm; `catRefPatUpstream` is the `PatKind::Ref` arm as quoted in F8 and
`catRefPatRepaired` adds the pinned case; `mirDerefPattern` is the MIR-building rule of F3.

- `ce4_expr_use_visitor_cat_deref_fails_without_field0`: for every place whose type is
  `Pin<&T>` or `Pin<&mut T>`, the upstream arm returns the error.
- `cat_pattern_ref_pinned_projects_field0_before_deref`: on such a place the repaired arm
  returns the place extended by `field 0 : &T` and then `deref : T`; this equals the result of
  the `PinDeref` arm and of MIR building.
- `repaired_agrees_with_upstream_on_unpinned_patterns`.
- `adjust_pin_deref_upstream_fails` and `adjust_pin_deref_repaired_projects_field0`: the same
  two statements for the expression-adjustment site.
- `delayed_bug_without_errors_is_ice` and `delayed_bug_is_masked_by_any_error`: the reporting
  rule seen in `c02` versus `c12`.

What the model is and is not: it is an abstraction written for this report, not an extraction
from rustc. Its fidelity to the compiler rests on the source quoted in F3-F8 and on the probes;
its limits are listed under Boundaries.

Basis: execution (Lean kernel) for the theorems; derived for the correspondence to rustc.

### F10. Relation to Anneal's trusted MIR semantics

At `joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/lean/Trusted/MirAst.lean`
defines the MIR fragment the trusted semantics accepts:

- `MirTy` (declared at line 312) has the constructors `bool`, `int`, `unit`, `never`, `enum`
  (fieldless enums only), `tuple`, `ref`, `rawPtr` and `unsupported`. Its documentation states
  that `.unsupported` "represents all other `TyKind` variants (`Char`, `Float`,
  non-fieldless-enum `Adt`, `Foreign`, `Str`, `Array`, `Pat`, `Slice`, `FnDef`, `FnPtr`,
  `Dynamic`, `Closure`, `CoroutineClosure`, `Coroutine`, etc.)" and that these make the
  semantics "fail closed with `FaultKind.unsupported`". `Pin<&mut T>` is a struct ADT and
  therefore unsupported, as are closure and coroutine types.
- `TerminatorKind` (declared at line 785) models `goto`, `switchInt`, `return_`, `unreachable`,
  `unwindResume`, `assert` and direct `call`; its documentation lists `Drop` among the variants
  that `.unsupported` represents.
- `ProjectionElem` (declared at line 472) models `deref` and `field`.
- `FaultKind` (`trusted/lean/Trusted/MirSemantics.lean:332-334`) has the two constructors
  `undefined` and `unsupported`.
- `MirAst.lean` also names the compiler revision used for MIR capture: "`anneal-rustc-capture`'s
  pinned `rustc` commit `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`" (lines 47-48, repeated at
  line 909), next to the reference revision `8144389c895da997dbdecaa635e41d6a50be6ffd` for the
  vendored interpreter model.

Consequences (derived):

- Every ingredient of this report — values of type `Pin<_>`, drop glue, closures, coroutines —
  is outside that fragment. A body that mentions any of them is not given a meaning; it faults
  as unsupported. The fragment therefore cannot currently express the pin contract, the
  forwarding shim, or packed drop moves, and nothing in this report contradicts a statement it
  can make.
- `f8a08b68` (committed 2026-05-30) is an ancestor of both fix commits: the GitHub compare API
  reports it 1,154 commits behind `e43ec0c1` and 1,590 behind `927b226f`, 0 ahead of either. A
  crate that enables `pin_ergonomics` and is compiled with that revision is thus exposed to both
  holes of F7 at the source level, independent of whether the MIR is later accepted for
  verification. `8144389c` was committed on 2026-10-20, four months after both fixes were
  merged; its ancestry relative to them was not queried.
- If the fragment is extended to struct ADTs and `Drop` terminators, the facts that matter are:
  `&pin mut T` has no MIR-level identity of its own (F1); a pinned dereference is the place
  projection "field 0 of `Pin`, then deref" (F3); drop glue reaches `pin_drop` through the
  provided `Drop::drop` body (F5); and `AddMovesForPackedDrops` changes addresses before
  destructors run (F6).

Basis: source + derived.

### F11. Incidental: `&pin mut self` triggers `unused_mut`

On `14210df0`, `fn pin_drop(&pin mut self) {}` compiled with lints enabled produces
`warning: variable does not need to be mutable` with the suggestion to "remove this `mut`",
pointing at the receiver (probe `d01_pin_mut_self_unused_mut_lint`). The source contains no
removable `mut` binding; following the suggestion would change the receiver type. All other
probes are compiled with `--cap-lints allow`.

Basis: execution.

## Boundaries

**Not examined.**

- No probe from this package was executed on `3ef0c22c` or `342d7446`. In particular the
  expression-adjustment site of F8 at those revisions, the rejection of probes `a2` and `a4`
  there, and `#[repr(C, packed(2))]` with `#[pin_v2]` there (probe `b11`; the source test is
  `repr.packed()`, which is not specific to `packed(1)`) rest on source reading.
- Enums and unions marked `#[pin_v2]`, generic packed types, `Pin<Box<T>>` and other pinned
  pointers in patterns (the source says they are "handled as a deref pattern"), `&pin const`
  projection beyond one accepted pattern, cross-crate use of `#[pin_v2]`, unwinding (cleanup)
  paths of the drop glue, async drop, and targets other than `x86_64-unknown-linux-gnu`.
- The borrow-expression form `&pin mut place`, beyond one probe on `14210df0`
  (`e01_pin_borrow_expression_then_use`): after `observe(&pin mut x)`, a later use of `x` is
  rejected with ``error[E0382]: use of moved value: `x` ``, with "value moved here" on the
  borrow expression — on that compiler the expression consumes the place. A pull request
  implementing borrow checking for that form (`rust-lang/rust` 153693) was closed without
  merging on 2026-08-05; what the later revisions do was not examined.
- Clippy and other out-of-tree users of `ExprUseVisitor`.

**Unknown.**

- Why probe `c10` reports E0381 rather than an ICE. That capture analysis was cut short is
  established; the path from there to "binding declared here but left uninitialized" was not
  traced in the source.
- What the two numeric fields in the preserved record's Part A output
  (`DROP_PINNED=67 DROP_MOVED_UNPINNED=108`) measure. The program that printed them was not
  preserved, so the record supports only `SAME_TID=true` and the absence of Miri diagnostics for
  that program. The `a1` probe of this package prints differently named, documented counters.
- Whether any revision between `14210df0` and the two fix commits has other pin-related
  differences.

**Known not to apply.**

- The compile failures of F8 do not occur in plain `fn` bodies (`c01`, `c05`, `c14`), for
  match-ergonomics patterns in closures (`c04`), or in crates that do not enable the feature
  (`c13`).
- The fn-parameter reproducer of upstream issue 149225 does not fail on `14210df0` (`c14`),
  although the issue was still open on 2026-11-22.
- The unsoundness of F7 needs the feature gate; stable Rust is not affected.
- F8 cannot produce a miscompiled program; it only prevents compilation.

**Stronger conclusions the evidence does not establish.**

- *That the gates make the real compiler sound.* The theorem in F9 is about a model with a
  single field path, no enums, no unwinding, no concurrency and one over-approximated rule for
  what a destructor body may do. It shows that the argument is coherent and that each gate is
  needed; it is not a proof about rustc.
- *That Miri validates structural pinning.* Miri with Stacked Borrows and with Tree Borrows
  reports nothing for `a1`, which shows only that those executions are free of undefined
  behaviour. It also reports nothing for `a2`, in which the pin guarantee is violated: Miri does
  not check the library-level pin contract, only undefined behaviour that follows from breaking
  it (as in `a4`). Stacked Borrows and Tree Borrows gave identical verdicts on every probe, so
  nothing here discriminates between them.
- *That `main` is free of pin-related unsoundness.* Only the two specific holes were followed to
  their fixes.
- *That the repair in F8 is what upstream will adopt.* It is the minimal change consistent with
  the other two places in the compiler that lower a pinned dereference.

## Evidence

All source, API and execution evidence was acquired on 2026-11-22, except the preserved record
for `3ef0c22c`, which is dated 2026-11-21 and was not repeated.

### Commits (each full hash was resolved through the GitHub REST API on 2026-11-22)

| Repository | Commit | Committer date | What it is |
| --- | --- | --- | --- |
| `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | 2026-05-31 | "Auto merge of #157219"; `commit-hash` of the executed toolchain |
| `rust-lang/rust` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | 2026-11-11 | "Auto merge of #165821"; `commit-hash` in the preserved record |
| `rust-lang/rust` | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | 2026-11-22 | `commits/main` at query time, "Auto merge of #166268" |
| `rust-lang/rust` | `e43ec0c183b65f9f73d943ce470c4e6d0f6dc971` | merged 2026-06-09 | merge commit recorded for pull request 157542 |
| `rust-lang/rust` | `927b226fcaccff5452ce68c7dcf20baad5f68571` | merged 2026-06-12 | merge commit recorded for pull request 157680 |
| `rust-lang/rust` | `e8f92f576974f7d1d5ef5dfafc56eae303b4c73e` | merged 2026-05-10 | merge commit recorded for pull request 144537 ("Add `Drop::pin_drop` for pinned drops"); ancestor of `14210df0` (compare `e8f92f57...14210df0`: ahead 1,783, behind 0) |
| `rust-lang/rust` | `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` | 2026-05-30 | capture-compiler revision named by Anneal (F10) |
| `rust-lang/rust` | `8144389c895da997dbdecaa635e41d6a50be6ffd` | 2026-10-20 | interpreter-model reference revision named by Anneal (F10) |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | 2026-11-19 | "[theory] Bridge PureLift onto Trusted MIR semantics (#266)" |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` | 2026-09-24 | object of tag `v4.34.1`; also printed by `lean --version` |

Ancestry was checked with `repos/rust-lang/rust/compare/<base>...<head>`: `14210df0...3ef0c22c`
(ahead 18,861, behind 0), `3ef0c22c...342d7446` (ahead 2,474, behind 0), `14210df0...e43ec0c1`
(ahead 1,085, behind 0), `e43ec0c1...3ef0c22c` (ahead 17,776, behind 0), `14210df0...927b226f`
(ahead 1,521, behind 0), `927b226f...3ef0c22c` (ahead 17,340, behind 0), `e43ec0c1...f8a08b68`
and `927b226f...f8a08b68` (behind 1,154 and 1,590, ahead 0).

### Upstream issues and pull requests (`rust-lang/rust`, state when queried on 2026-11-22)

| Number | Kind | Title | State |
| --- | --- | --- | --- |
| 130494 | issue | Tracking issue for pin ergonomics | open (opened 2024-09-17) |
| 139751 | pull request | Implement pin-project in pattern matching for `&pin mut\|const T` | merged 2025-11-01 |
| 148397 | pull request | Implement `&pin` patterns and `ref pin` binding modes | merged 2025-11-10 |
| 149263 | pull request | Forbid manual `Unpin` impls for structurally pinned types | merged 2026-02-03 |
| 144537 | pull request | Add `Drop::pin_drop` for pinned drops | merged 2026-05-10 |
| 156452 | pull request | Implement pinned drop sugar | merged 2026-05-16 |
| 156495 | pull request | Emit either mono item of `Drop::drop` or `Drop::pin_drop` depending on which was implemented | open |
| 153693 | pull request | Implement borrowck for `&pin mut\|const $place` | closed unmerged 2026-08-05 |
| 157011 | issue | Unsoundness due to `#[pin_v2]` incorrectly handles packed structs. | closed 2026-06-09 |
| 157542 | pull request | Reject `#[repr(packed)]` on `#[pin_v2]` types | merged 2026-06-09 |
| 157615 | issue | Unsoundness: explicit pin projection into a `#[repr(packed)]` field breaks `Pin` without `#[pin_v2]` | closed 2026-06-19 |
| 157634 | issue | `ref pin mut` pattern unsoundly allows pin-projecting arbitrary types | closed 2026-06-12 |
| 157680 | pull request | Require `#[pin_v2]` for explicit pin-projection patterns | merged 2026-06-12 |
| 149225 | issue | ICE `explicit deref of non-derefable type` | open (opened 2025-11-19) |
| 153733 | issue | [ICE]: `explicit deref of non-derefable type` | open (opened 2026-03-11) |
| 154782 | issue | [ICE]: could not resolve upvar: LocalVarId(HirId(DefId( | open (opened 2026-04-03) |

### Source locations

Files were read from `raw.githubusercontent.com/rust-lang/rust/<commit>/<path>`; for `14210df0`
the copy shipped in the toolchain's `rustc-dev` component was compared byte for byte with the
upstream file for `expr_use_visitor.rs`. Line numbers are given as `14210df0` / `3ef0c22c` /
`342d7446`; "=" means the file is byte-identical to the one at `3ef0c22c`.

| Path | Item | Lines |
| --- | --- | --- |
| `compiler/rustc_ast_lowering/src/lib.rs` | `TyKind::PinnedRef` arm of `lower_ty` | 1407-1420 / 1544-1557 / 1581-1594 |
| `compiler/rustc_feature/src/unstable.rs` | `(incomplete, pin_ergonomics, "1.83.0", Some(130494))` | 686 / 700 / 700 |
| `compiler/rustc_middle/src/ty/adjustment.rs` | `DerefAdjustKind::Pin`; `AutoBorrow::Pin`; `PatAdjust::PinDeref` | 120, 207, 253 / 120, 207, 253 / 120, 207, 262 |
| `compiler/rustc_middle/src/ty/adt.rs` | `AdtFlags::IS_PIN_PROJECT` set from `PinV2`; `is_pin_project` | 355, 525 / 384, 543 / 384, 543 |
| `compiler/rustc_hir_typeck/src/coercion.rs` | `coerce_to_pin_ref` | 926-964 / 943-981 / = |
| `compiler/rustc_hir_typeck/src/method/probe.rs` | `ReborrowPin` for by-value picks | 1544-1553 / 1591-1600 / 1621 (assignment) |
| `compiler/rustc_hir_typeck/src/pat.rs` | implicit peel recording `PatAdjust::PinDeref` | 535-575 / 532-559 / 538 (guard) |
| `compiler/rustc_hir_typeck/src/pat.rs` | `Unpin` obligation for unpinned bindings | 1224-1234 / 1228-1238 / from 1232 |
| `compiler/rustc_hir_typeck/src/pat.rs` | `check_pin_projection` and its two call sites | absent / 1529-1560, 1572, 1844 / from 1541, 1574, 1846 |
| `compiler/rustc_hir_typeck/src/pat.rs` | `check_pat_ref`; `max_pinnedness = Pinned` | 2755, 2912 / 2792, 2949 / 2794, 2951 |
| `compiler/rustc_hir_analysis/src/coherence/builtin.rs` | `visit_implementation_of_unpin` | 142-175 / 133-168 / = |
| `compiler/rustc_hir_analysis/src/check/check.rs` | pin check at the head of `check_packed` | absent / 1666-1679 / 1668-1681 |
| `compiler/rustc_hir_analysis/src/check/always_applicable.rs` | `check_drop_xor_pin_drop` | 374-435 / 373-435 / = |
| `compiler/rustc_hir_typeck/src/callee.rs` | `check_legal_trait_for_method_call` | 37-60 / 51-76 / = |
| `library/core/src/ops/drop.rs` | `Drop::drop` provided body; `Drop::pin_drop` | 241-246, 266-267 at all three (identical file) |
| `library/core/src/pin.rs` | packed-type paragraph | 630-633 / 630-633 / = |
| `compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs` | pass and `add_move_for_packed_drop` | 40-, 77- / 40-76, 78- / 40-, 76- |
| `compiler/rustc_mir_build/src/thir/pattern/mod.rs` | `PinDeref` adjustment; explicit `Ref` pattern | 148-150, 345-353 / 147-149, 344-352 / not compared |
| `compiler/rustc_mir_build/src/builder/matches/match_pair.rs` | pinned `Deref` lowering | from 294 / 417-430 / = |
| `compiler/rustc_mir_build/src/builder/expr/as_place.rs` | `span_bug!("could not resolve upvar ...")` | 263-267 at all three |
| `compiler/rustc_hir_typeck/src/expr_use_visitor.rs` | `report_bug` for the type checker | 199-201 / 198-200 / = |
| `compiler/rustc_hir_typeck/src/expr_use_visitor.rs` | `Adjust::Deref` arm of `cat_expr_adjusted_with` | 1276-1290 / 1269-1283 / = |
| `compiler/rustc_hir_typeck/src/expr_use_visitor.rs` | `cat_deref` | 1506-1526 / 1499-1519 / = |
| `compiler/rustc_hir_typeck/src/expr_use_visitor.rs` | `PatAdjust::PinDeref` arm | 1661-1672 / 1654-1665 / = |
| `compiler/rustc_hir_typeck/src/expr_use_visitor.rs` | reference-pattern arm of `cat_pattern` | 1770-1776 / 1763-1769 / = |
| `compiler/rustc_hir_typeck/src/upvar.rs` | `ExprUseVisitor` call sites | 213, 583 / 131, 291, 687 / 131, 291, 687 |

SHA-256 of `expr_use_visitor.rs`: `c86e1fb9b3eac8587fe9c7172a3e67eacca6546d9485b54c30be3f0f1cc32bc5`
at `14210df0`; `597fb71bf13b02bbbc6912d8628c6188f15754c5ec78fa771c07fff2c884bb82` at `3ef0c22c`
and `342d7446`. SHA-256 of `coercion.rs` at `3ef0c22c` and `342d7446`:
`cd21a78bdfaa99bcbca666cd06daaffab69582e57e371c4f3b0ce61930024fee`.

The diagnostic structs were in `compiler/rustc_hir_analysis/src/errors.rs` and
`compiler/rustc_hir_typeck/src/errors.rs` at `14210df0`; at `3ef0c22c` the same structs
(plus `PinV2OnPacked`) are in files named `diagnostics.rs` in the same directories.

Anneal locations are given in F10 (`trusted/lean/Trusted/MirAst.lean` lines 47-48, 312, 472,
785, 909; `trusted/lean/Trusted/MirSemantics.lean` lines 332-334), read from a checkout of the
commit.

### Execution environment

- `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, host `x86_64-unknown-linux-gnu`, LLVM 22.1.6;
  Miri from the same toolchain (`miri 0.1.0 (14210df0e2 2026-05-31)`), using an existing Miri
  sysroot for that toolchain in the default location `~/.cache/miri` (the location
  `cargo miri setup` uses).
- Compile-only probes: `rustc --edition 2024 --cap-lints allow <probe>.rs --emit=metadata`.
  Runnable probes: `rustc --edition 2024 --cap-lints allow <probe>.rs`, then the executable.
  Miri: `miri --sysroot <dir> --edition 2024 --cap-lints allow <probe>.rs`, and the same with
  `-Zmiri-tree-borrows`. For `a4` the helper crate is built first as an `rlib`
  (for Miri with `MIRI_BE_RUSTC=target`) and passed with `--extern`. Environment: `RUSTC_ICE=0`
  (no ICE dump files), `RUST_BACKTRACE=0`, `LC_ALL=C`.
- Lean: `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`
  on the model file, `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`.

### Preserved material in this package

| File | Content |
| --- | --- |
| `support/probe_pin_ergonomics_pin_v2_and_ice.py` | driver (Python standard library only): compiles and runs every probe, records outcomes as JSON, `--check` compares with a stored record |
| `support/probes/a*.rs` | runnable probes (F1-F7); `a4_selfref_future.rs` is the helper crate of `a4_unmarked_projection_uaf.rs` |
| `support/probes/b*.rs` | gate probes (F4) |
| `support/probes/c*.rs` | capture-analysis matrix (F2, F8) |
| `support/probes/d01_pin_mut_self_unused_mut_lint.rs` | F11 |
| `support/probes/e01_pin_borrow_expression_then_use.rs` | the borrow-expression observation under Boundaries |
| `support/results/observed_rustc_nightly_2026-05-31_14210df0e.json` | complete record of the 38 probes on `14210df0` (17 accepted, 13 rejected, 8 ICE), with compiler and Miri output |
| `support/results/prior_recorded_rustc_nightly_2026-11-11_3ef0c22cd.json` | the preserved record for `3ef0c22c`: compiler and Miri outputs of an earlier run of a different probe, verbatim, with a provenance note. The inputs of that run survive only as the source excerpts inside its diagnostics. Two metadata keys of the original were dropped: a task label, and a checkout revision that is not a commit on `main` of `rust-lang/rust` |
| `support/PinErgonomicsSoundnessTriangle.lean` | the model of F9 |
| `support/results/lean_check_v4.34.1.txt` | output of the Lean run (audit line and per-theorem axiom reports) |

The record for `3ef0c22c` contains, for that compiler: the Part A line
`SAME_TID=true DROP_PINNED=67 DROP_MOVED_UNPINNED=108` natively and under Miri with both borrow
models (exit 0, empty stderr); five rejections whose first lines are
``error: cannot project on type that is not `#[pin_v2]` `` (for
`let &pin mut Plain(ref pin mut x) = p;` with an unmarked `Plain`),
``error[E0277]: `PhantomPinned` cannot be unpinned``,
``error: conflicting implementations of `Drop::drop` and `Drop::pin_drop` ``,
``error: `OnlyDrop` must implement `pin_drop` `` and
``error: `#[pin_v2]` types may not have `#[repr(packed)]` `` (with the note "fields of a
`#[repr(packed)]` type can be under-aligned, so a structurally pinned field may be moved to a
properly aligned location, which `Pin` does not allow"); one acceptance (a `pin_drop`-only
impl); and the closure ICE and `fn`-item acceptance cited in F8. Every one of those diagnostic
strings was found in the source at `3ef0c22c`.

Two cross-checks on the driver and the model: running the driver twice on `14210df0` gives
identical stable fields (`--check` passes; the native output of `a4` is excluded because it
reads freed memory), and the Lean audit command was confirmed to fail both when a theorem using
`propext` and when a directly recursive definition is added to the module.

## Revalidation

**Is the compile failure of F8 still present in a given rustc revision?** Cheapest first:

1. Compare the SHA-256 of `compiler/rustc_hir_typeck/src/expr_use_visitor.rs` with
   `597fb71bf13b02bbbc6912d8628c6188f15754c5ec78fa771c07fff2c884bb82`. Equal means unchanged.
2. Otherwise read two places in that file: the `PatKind::Ref` arm of `cat_pattern` and the
   `adjustment::Adjust::Deref` arm of `cat_expr_adjusted_with`. The defect is present at a site
   if `cat_deref` is reached for a pinned dereference without a preceding
   `cat_projection(.., ProjectionKind::Field(FieldIdx::ZERO, FIRST_VARIANT))`.
3. Or compile two files with that compiler: `support/probes/c02_closure_explicit_pin_mut_pattern.rs`
   (site 1) and `support/probes/c08_async_fn_await.rs` (site 2) with
   `rustc --edition 2024 --cap-lints allow <file> --emit=metadata`. Exit status 101 with
   "explicit deref of non-derefable type" means present; exit status 0 means fixed.
4. The states of `rust-lang/rust` issues 149225, 153733 and 154782.

**Are the gates of F4 present?** In the source: `PinV2OnPacked` in
`compiler/rustc_hir_analysis/src/check/check.rs` (`check_packed`) and `check_pin_projection` in
`compiler/rustc_hir_typeck/src/pat.rs`, called from both `check_pat_struct` and
`check_pat_tuple_struct`. By execution: `b01_explicit_pattern_on_non_pin_v2_struct.rs` and
`b10_pin_v2_repr_packed.rs` must be rejected.

**Everything at once.** With a nightly toolchain that has the `miri` and `rust-src` components
and a built Miri sysroot:

```sh
python3 support/probe_pin_ergonomics_pin_v2_and_ice.py \
    --check support/results/observed_rustc_nightly_2026-05-31_14210df0e.json
```

On `nightly-2026-06-01` this prints `check passed: all 38 probes match ...`. On a different
compiler the driver notes the commit mismatch and lists every probe whose stable fields differ.
Differences to expect on a compiler that has both soundness fixes: `a2`, `a4`, `b01`, `b10` and
`b11` change from accepted to rejected, and every `delayed_at` path changes with the commit hash
and line. Any *other* change in the `a*` or `b*` probes — in particular a `b*` probe that was
rejected becoming accepted, or `DROP_PINNED_MOVED` becoming non-zero in `a1` — means a finding
here no longer holds for that compiler. On a compiler in which the capture-analysis defect is
fixed, `c02`, `c03`, `c06`-`c11` and `c15` are expected to be accepted. A passing run establishes
only what these probes check. `--out FILE` writes a fresh record; `--skip-miri` omits the Miri
runs (the four runnable probes then differ from the stored record in their Miri fields);
`--rustc`, `--miri` and `--miri-sysroot` select the tools.

**The Lean model.** With Lean `v4.34.1`:

```sh
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
    support/PinErgonomicsSoundnessTriangle.lean
```

must exit 0 and print the line
`audit ok: 408 module constants, 31 stated theorems, no axioms, no recursion helpers` followed
by nine `does not depend on any axioms` lines. A different Lean version may need small proof
adjustments; the constant count is specific to this version, the theorem count is not.

**Anneal.** In `trusted/lean/Trusted/MirAst.lean` of the revision of interest, check whether
`MirTy` has gained a struct constructor and `TerminatorKind` a `drop` constructor, and which
`rust-lang/rust` commit is named as the capture compiler. If the fragment has grown to cover
either, F10's "outside the fragment" statement no longer applies and F1, F3, F5 and F6 become
the relevant inputs; if the capture compiler is a descendant of
`927b226fcaccff5452ce68c7dcf20baad5f68571`, the exposure noted in F10 is gone.

**What cannot be revalidated cheaply.** Behaviour of `3ef0c22c` itself requires installing that
nightly and running the driver; until then the statements about it remain source-based plus the
preserved record.
