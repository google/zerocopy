# Rust unsafe fields at nightly-2026-05-31

## Summary

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the compiler behind Anneal-era nightly-2026-05-31, `#![feature(unsafe_fields)]` is an incomplete unstable feature for marking named fields whose library safety invariant is stronger than the invariant supplied by their Rust type.

The compiler makes two operations unsafe: constructing a variant that contains an unsafe field, and projecting an unsafe field. The projection rule covers reads, writes, moves/copies, references, raw borrows, and patterns that bind the field. Safe fields of the same ADT remain ordinary. A pattern may skip an unsafe field with `..`, and `offset_of!` may name the field without projecting its value.

The marker does not verify the documented invariant or make every relevant transition unsafe. In particular, automatic destruction remains safe. RFC 3458 therefore requires abstractions to keep an unsafe field soundly droppable even when its library invariant is relaxed, using `ManuallyDrop` when necessary. The compiler separately prevents two implicit structural shortcuts: `Copy` becomes unsafe to implement for an ADT containing unsafe fields, and unsafe auto traits are not automatically implemented for such a type.

The accepted RFC and the pinned compiler differ on unions. RFC 3458 says unsafe union fields remain forbidden while that design question is unresolved. The pinned compiler's checked-in UI fixture declares an unsafe union field without an expected declaration error. This report preserves that discrepancy rather than treating the RFC as an exact description of the implementation.

No fresh rustc execution was performed. Evidence is pinned source, the accepted RFC, implementation history, and checked-in UI fixtures and expected diagnostics.

## Applicability

The compiler subject is `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, corresponding to Anneal-era nightly-2026-05-31.

The design subject is RFC 3458 at `rust-lang/rfcs@f5749baed7b7ecfe03d95dc9197d0c1344712f43`. The RFC was accepted before the compiler revision examined here.

The feature remains gated as `unsafe_fields` and marked incomplete at the compiler pin. The tracking issue, rust-lang/rust#132922, remained open when observed and still listed Rust Reference documentation and stabilization as unfinished. These findings therefore describe exact pinned behavior, not a stable cross-version Rust guarantee.

“Safety invariant” follows RFC 3458: a condition whose violation can lead to undefined behavior. An unsafe field denotes a library safety invariant; it does not permit violating the Rust language validity requirements of the field's type.

## Findings

### The marker is an authorization boundary for library invariants

RFC 3458 proposes unsafe fields for state whose API-level safety invariant differs from the ordinary invariant of its type. The compiler preserves the marker beyond parsing: `lower_field_def` stores field safety in HIR, and later type metadata exposes whether a variant or ADT has unsafe fields.

This makes field safety semantic compiler metadata rather than a documentation-only annotation.

Basis: **documentation** + **source**.

### Only named fields carry the syntax at this pin

The parser accepts optional `unsafe` before a record-field name and gates it under `unsafe_fields`. It explicitly excludes tuple fields because `struct X(unsafe fn())` would be syntactically ambiguous.

Basis: **source**.

### The RFC and compiler disagree about union declarations

RFC 3458's reference-level text says unsafe fields on unions remain forbidden while their interaction with safe unions is unresolved.

The pinned compiler UI fixture nevertheless declares `union WithUnsafeFieldUnion { unsafe unsafe_field: u32, safe_field: u32 }`, and its paired expected stderr contains no declaration error for that union. The record-field parser also carries field safety for named record fields.

The narrow pinned fact is therefore that this declaration is accepted by the implementation represented by the checked-in fixture. No eventual stable union rule is inferred.

Basis: RFC **documentation** + compiler **source** + preserved test artifact.

### Constructing a variant containing an unsafe field requires unsafe

In `check_unsafety.rs`, an `ExprKind::Adt` requires unsafe when the selected variant reports any unsafe field. The checked-in test confirms that a struct literal for such a type produces E0133 outside an unsafe block.

The obligation belongs to construction of the ADT variant, not merely to a textual assignment to the marked field.

Basis: **source** + preserved test artifact.

### Projecting an unsafe field requires unsafe

For `ExprKind::Field`, the unsafety checker consults the selected field's safety metadata and requires unsafe for an unsafe field.

The UI fixture exercises this rule for assignment, value read/copy, shared reference, raw const borrow, and destructuring patterns. Each has an expected E0133 outside unsafe. Corresponding operations inside an unsafe block are accepted by the fixture.

A raw borrow does not bypass the rule: `&raw const self.unsafe_field` is expected to fail outside unsafe.

Basis: **source** + preserved test artifact.

### Skipping the field and querying layout are different from projecting it

The fixture permits a destructuring pattern that binds only the safe field and uses `..` to ignore the unsafe field. It also permits `offset_of!(WithUnsafeField, unsafe_field)`.

These cases identify structure without obtaining the invariant-bearing field value or place. The safety obligation follows the semantic field use, not every mention of the field name.

Basis: preserved test artifact + **derived** interpretation of the source rule.

### Visibility is independent of field safety

A cross-crate fixture exports a public unsafe field and a public safe field. Downstream code can name both according to ordinary visibility rules, but construction and projection of the unsafe field require unsafe while operations on the safe field remain safe.

Thus `pub unsafe field: T` is publicly visible state with an unsafe use obligation. The unsafe marker neither makes the field private nor bypasses privacy.

Basis: preserved cross-crate test artifact.

### Unsafe fields cannot relax Rust language validity

RFC 3458 distinguishes library safety invariants from language invariants. It explicitly rejects using an unsafe field to make an otherwise invalid `T` acceptable. It separately permits relaxing a library invariant, such as UTF-8 validity, only while the underlying language validity requirements remain satisfied.

An unsafe-field proof obligation therefore is not permission to suspend arbitrary Rust validity rules.

Basis: accepted-RFC **documentation**.

### Automatic destruction is outside the projection barrier

The accepted RFC calls out a critical limitation: automatic destruction does not become unsafe merely because a type contains an unsafe field. If a relaxed field invariant can make its destructor invoke undefined behavior, the enclosing abstraction must restore a safe-to-drop state or prevent automatic destruction. The RFC demonstrates the latter with `ManuallyDrop`.

This means unsafe fields localize explicit accesses without turning the type into a compiler-checked invariant state machine.

Basis: accepted-RFC **documentation** + **derived** implication.

### `Copy` is conditionally unsafe to implement

A `Copy` implementation has no method body in which a field projection can carry a local unsafe block, yet implementing it permits safe duplication of the whole value.

The pinned coherence checker handles this explicitly: when the trait is the `Copy` lang item and the self type has unsafe fields, it treats the implementation as unsafe. The UI fixture records that an ADT with unsafe fields needs `unsafe impl Copy`, while a safe ADT uses ordinary `impl Copy`.

Implementation PR #134008 documents the same rationale.

Basis: compiler **source** + implementation-history **documentation** + preserved test artifact.

### Unsafe auto traits are not inferred structurally through unsafe fields

Both the classic trait solver and the next solver suppress automatic candidates for an unsafe auto trait when the self type has unsafe fields. The pinned `auto-traits.rs` fixture checks this for both solver configurations.

Implementation PR #133934 explains why: an unsafe field can carry an invariant that is not reducible to the conjunction of the field types' invariants, so structural inference is insufficient.

This finding is specific to unsafe auto traits; it does not imply that every safe auto trait or derive is similarly suppressed.

Basis: compiler **source** + implementation-history **documentation** + preserved test artifact.

### The feature narrows proof sites but does not establish the invariant

Construction and projection checks, plus the `Copy` and unsafe-auto-trait rules, expose important places where an unsafe-field invariant must be established or respected. They do not prove that the documented invariant is true.

Safe operations on the enclosing value can still matter, especially destruction. The separate safety-boundary-completeness report therefore remains complementary: a sound abstraction proof must still track invariant producers, relevant safe and unsafe transitions, and unsafe consumers.

Basis: **derived** from the pinned rules and RFC rationale.

## Boundaries

- No fresh rustc, Cargo, Clippy, rustfmt, Miri, or runtime execution was performed.
- `unsafe_fields` is incomplete and unstable at the examined revision; adjacent-version continuity is not assumed.
- The tracking issue still listed Rust Reference documentation and stabilization as unfinished when observed. The accepted RFC is not presented as a stable Reference rule.
- The RFC says unsafe union fields should remain forbidden, while the pinned checked-in compiler fixture accepts an unsafe union-field declaration without an expected declaration error.
- Tuple/positional unsafe fields are unsupported by the pinned parser.
- The compiler gates construction and projection but does not verify the programmer's library invariant.
- Unsafe fields cannot relax Rust language validity requirements.
- Automatic `Drop` is not made unsafe merely because a type contains an unsafe field.
- `Copy` and unsafe auto traits have specific rules described here. Other derives and trait-system corners were not exhaustively inventoried.
- No layout, ABI, offset, or runtime-representation change is claimed from the unsafe marker.
- Charon and Aeneas preservation of unsafe-field metadata was not examined here.
- No Anneal invariant or annotation architecture is selected.

## Evidence

**Accepted language-design documentation**

- `rust-lang/rfcs@f5749baed7b7ecfe03d95dc9197d0c1344712f43`, `text/3458-unsafe-fields.md`, blob `4d9bc5b975d54327ae41df16bbab8bdf729893c7`.
- `rust-lang/rust#132922`, observed 2026-09-26: tracking issue for `unsafe_fields`.
- rust-lang/rust PRs #132915, #133934, and #134008: implementation and rationale history.

**Compiler source — `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`**

- `compiler/rustc_feature/src/unstable.rs`, blob `388482209cf9eb17a562735bae03b644db686368`: incomplete feature gate.
- `compiler/rustc_parse/src/parser/item.rs`, blob `3f6429c6a60f0372cb44262a12218bd6a821c390`: field parsing and tuple exclusion.
- `compiler/rustc_ast_lowering/src/item.rs`, blob `70f55d67c7a16e582eabdfd160db93d6b03f8c4d`: field-safety lowering.
- `compiler/rustc_middle/src/ty/mod.rs`, blob `6df1ed82d260a5c95dbe9671f2c7ddf8585c36ab`: variant unsafe-field query.
- `compiler/rustc_middle/src/ty/util.rs`, blob `99da2da391151fe1f67cbb0d48fdde32f0c982e9`: ADT unsafe-field query.
- `compiler/rustc_mir_build/src/check_unsafety.rs`, blob `f99d8934aa7fa8944e2906c2719e1eb4356c3c09`: construction and projection obligations.
- `compiler/rustc_hir_analysis/src/coherence/unsafety.rs`, blob `8114106a2a4117a1e8e1d706afff753ff834f263`: conditional `Copy` unsafety.
- `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs`, blob `3b599db8ff1c20005aa95ed9928e78aeecfd7f53`: classic-solver auto-trait rule.
- `compiler/rustc_next_trait_solver/src/solve/trait_goals.rs`, blob `e09864295020f89899863236d38853505ed1f0ef`: next-solver auto-trait rule.

**Preserved UI fixtures — same compiler revision**

- `tests/ui/unsafe-fields/unsafe-fields.rs`, blob `cb86479bb20d36dd6db2ea4bdde6ab46f839d578`.
- `tests/ui/unsafe-fields/unsafe-fields.stderr`, blob `d0e2dc16a13d546baada6f6252181e1fced0fecf`.
- `tests/ui/unsafe-fields/unsafe-fields-crate.rs`, blob `cfb9ad6b544fde44efb7e6a555dd9f35eef2d937`.
- `tests/ui/unsafe-fields/copy-trait.rs`, blob `fb09ed02e3ffee1231400e5ab191e284972d5407`.
- `tests/ui/unsafe-fields/auto-traits.rs`, blob `e15d0000079ef16c85506900219c99f66f9ad815`.

These are checked-in upstream artifacts. This report performed no fresh **execution**.

## Revalidation

For another Rust pin, first determine whether `unsafe_fields` remains gated, incomplete, or has stabilized. If stabilized, read the then-current Rust Reference rather than carrying RFC wording forward.

Then diff four narrow implementation areas: record-field parsing/HIR metadata; `check_unsafety.rs` around ADT construction and field projection; the `Copy` coherence rule; and both unsafe-auto-trait solver paths. Reconcile those results with the current union and drop rules.

On a capable execution surface, use one fixture with an unsafe field and safe control field. Exercise construction, read, write, move/copy, shared/mutable/raw borrow, destructuring with and without `..`, `offset_of!`, whole-value move/drop, `Copy`, and one unsafe auto trait. Add tuple and union declarations as controls. Preserve stderr and exact revisions.

That probe establishes observable safety gating for the fixture. It does not prove arbitrary user-documented invariants sound or establish downstream preservation by Charon/Aeneas.
