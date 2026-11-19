# Metaprogramming Hygiene, Staging, Reflection, and Compile-Time Execution

## Summary

Compile-time metaprogramming systems span four coupled architectural axes—**representation level** (untyped token streams vs. scoped syntax trees vs. compiler-resolved semantic graphs), **binding hygiene** (span-based call/mixed-site vs. sets of scopes vs. scoped names with quotation-time pre-resolution), **phase discipline** (strictly staged vs. phase-collapsed), and **reflection boundary** (none vs. access-controlled layout/member metadata). No mainstream language simultaneously maximizes syntactic extensibility, modular definition-time type safety, layout reflection, and build hermeticity.

Four primary-source invariants anchor the design space:

1. **Pre-resolution token-stream macros cannot soundly compose with `unsafe` layout proofs.** Executing procedural macros before name resolution, attribute completion, and type layout (`Rust` `proc_macro`) produces five concrete soundness and maintenance failures documented in `google/zerocopy`: outside-in attribute ordering allowing downstream attributes to mutate struct fields after an earlier `#[derive(...)]` emitted an `unsafe impl`; re-expanding nondeterministic field-type macros into divergent trait-bound and field-definition sites; lexical parser drift on raw identifiers (`#[r#repr(r#align(8))]`); missing stable def-site item hygiene (`Span::mixed_site()` hides only locals, labels, and `$crate`, exposing generated marker types to generic-parameter shadowing and forcing Unicode workarounds such as `ẕ` that collide with UTS #39 Unicode 18 crate-level lints); and identically spelled tokens carrying distinct hygiene marks, forcing `Identity<Type = T>` bounds to invoke `rustc` as a name-resolution equality oracle.
2. **Hygienic binding has two distinct, production-proven models.** Racket's *Binding as Sets of Scopes* (Flatt 2016) replaces KFFD renaming histories with per-max-scope binding tables, symmetric-difference `flip-scope` macro marking, and maximal-subset resolution with explicit ambiguity detection on incomparable scope sets; Turnstile (Chang, Knauth, and Greenman 2017) interleaves bidirectional typing with expansion via `local-expand` and syntax properties. Lean 4 (Ullrich and de Moura 2020/2022) instead embeds scope lists directly in hierarchical `Name`s (`MacroScopesView`) paired with quotation-time global pre-resolution (`Syntax.Preresolved`), pairing pure syntactic macros (`MacroM`) with typed dependent elaborator reflection (`TermElabM`) at the cost of order-sensitive postponement (`synthesizeSyntheticMVars`).
3. **Typed multi-stage programming separates well-typedness from scope-extrusion enforcement.** MetaML (Taha and Sheard 2000) and environment classifiers (Taha and Nielsen 2003; Kameyama, Kiselyov, and Shan 2008/2011) guarantee both well-typedness and scope-extrusion freedom statically at generator compile time, but pure classifiers conflict with unrestricted OCaml effects (`ref`, exceptions, `delimcc`). BER MetaOCaml (N101–N153; Kiselyov 2014/2024) **removed static environment classifiers**, preserving static generator-compile-time well-typedness while enforcing comprehensive scope-extrusion freedom eagerly at generator runtime via `stackmark` region tokens and a free-variable priority heap (`typing/trx.ml`)—which also powers native let-insertion (`genlet`, `with_locus`). Scala 3 (`scala.quoted`) enforces a static Phase Consistency Principle with level-0 `Type[T]` healing and explicit `ToExpr[T]` cross-stage persistence, while Two-Level Type Theory (Kovács 2022) unifies dependent typing with guaranteed-erased modular staging.
4. **Phase-collapsed CTFE (`Zig comptime`) and post-resolution static reflection (`C++26 P2996R13`) eliminate token-stream drift at contrasting costs.** Zig (`src/Sema.zig`) collapses type computation and runtime functions via lazy instantiation (`.generic_poison_type` resolved only inside `analyzeCall`), gaining ergonomic layout reflection (`@typeInfo` calling `ty.resolveLayout`) and hermetic `@embedFile` dependency tracking at the cost of Post-Monomorphization Errors (PMEs), bounded-fuel halting (`default_branch_quota = 1000`), and weak IDE completion in uninstantiated generics. C++26 P2996R13 (`^^`, `[: :]`, `std::meta::info`, `offset_of`, `define_aggregate`) enforces strict `consteval`-only stage containment over resolved compiler entities while exposing Reynolds's parametricity vs. intensional-analysis tension whenever `access_context::unchecked()` bypasses private access control.

## Applicability

This report synthesizes findings across thirteen primary subjects pinned in `REPORT.json`:

| Subject Area | Examined Primary Sources | Role |
| --- | --- | --- |
| Token-stream macros & `unsafe` derives | `google/zerocopy` (`ec133ce4d7993775413d852f91c9e3eb2a2a0897`); `rust-lang/rust` (`b0b600668bb9b4a897e2299b0a44289d42276545`) | Production soundness postmortems and `proc_macro::Span` hygiene contract |
| Sets of Scopes & typed macros | Flatt (POPL '16, DOI `10.1145/2837614.2837620`); `racket/racket` (`8ed38e11307b13f25ca67224c66438b83340ae68`); Chang, Knauth, & Greenman (POPL '17, DOI `10.1145/3009837.3009886`) | Multi-phase scope-set expander and `local-expand` bidirectional typing |
| Scoped names & elaborator reflection | Ullrich & de Moura (IJCAR '20 / LMCS 2022, DOI `10.1007/978-3-030-51054-1_10`); `leanprover/lean4` (`8009d0a64d2860606c6a5ac5ff6702622b24921e`) | `MacroScopesView`, `Syntax.Preresolved`, `MacroM`/`TermElabM` split, postponement |
| Typed multi-stage programming | Taha & Sheard (TCS 2000, DOI `10.1016/S0304-3975(00)00053-0`); Kiselyov (FLOPS '14 & '24); `metaocaml/ber-metaocaml` (`8891433d4bce906e69cb397fe27da04c4e6b3f37`); `scala/scala3` (`90f3daf0a4795308d9c0e1b8f2265aeaecae8aa2`) | Explicit staging, static classifiers vs. dynamic stackmarks, CSP, type healing |
| Phase-collapsed CTFE & C++26 reflection | `ziglang/zig` (`738d2be9d6b6ef3ff3559130c05159ef53336224`); WG21 P2996R13 (`2025-06-20`) | Lazy `comptime` generics, `@typeInfo`/`@embedFile`, `consteval`-only `std::meta::info` |

These findings apply to compiler, verification-tool, proof-assistant, and systems-library design where compile-time code generation interacts with memory layout, `unsafe` invariants, incremental builds, or IDE responsiveness.

**Adjacent corpus packages (cross-referenced, not duplicated here):**
- Rust incremental dependency graphs, proc-macro determinism sandboxing, and ThinLTO invalidation: `scoped-exportlist-invalidation-slicing-and-proc-macro-determinism-sandbox`.
- Lean 4 namespace resolution, source positions, and InfoTree interactive tooling: `lean-elaboration-hygiene-positions-and-infotree`.
- Compiler-backed language server snapshot/view architectures: `language-server-snapshots-views-and-compiler-backed-ide-architectures`.

Executable models in `support/verify_hygiene_and_staging.py` witness the core algorithms on Python 3.10+ (stdlib only) as observed on `2026-11-19`; they verify algorithmic properties rather than full upstream compiler implementations.

## Findings

### 1. Comparative Design Matrix Across Metaprogramming Paradigms

Basis: normative + documentation + source + derived

| System | Representation | Hygiene / Binding | Phase Discipline | Modular Checking | Scope-Extrusion Defense | Layout / Type Reflection | Hermeticity & I/O | IDE / Incremental Impact |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| **Rust `proc_macro`** (`rust-lang/rust` `b0b60066`) | Untyped `TokenStream` + `Span` | `call_site` or `mixed_site` (locals/labels/`$crate`); `def_site` unstable | Pre-resolution host dylib | Post-expansion per call site only | None for items/type params | None (must re-parse `#[repr]`) | Unrestricted host OS I/O unless sandboxed | Black-box expansion; coarse invalidation (`scoped-exportlist-invalidation-slicing-and-proc-macro-determinism-sandbox`) |
| **Racket** (`racket/racket` `8ed38e11`) | Scoped `syntax` + `multi-scope` | Sets of scopes + `flip-scope` + `use-site`; ambiguity errors | Multi-phase tower (`0, 1, ...`) | Untyped (Turnstile adds `local-expand` typing) | Preserved across nested macros; explicit `datum->syntax` | Syntax properties only | Phase-separated compilation; effects allowed at phase 1 | Exact binding provenance for check-syntax/rename |
| **Lean 4** (`leanprover/lean4` `8009d0a6`) | `Syntax` (`MacroM`) + `Expr` (`TermElabM`) | `MacroScopesView` in `Name` + `Syntax.Preresolved` | Pure `MacroM` + interleaved `TermElabM` | Kernel checks elaborated `Expr` per invocation | Sanitized binders (`✝`); kernel rejects ill-scoped `Expr` | Full semantic `Environment` & expected type | `MacroM` pure; `TermElabM` allows `IO` via `CoreM` | InfoTree provenance (`lean-elaboration-hygiene-positions-and-infotree`); postponement order sensitivity |
| **Idris 2** (Christiansen & Brady 2016) | Core TT terms via `Elab` | Elaborator-managed binder names | Direct elaborator reflection | Checked per invocation | Core elaborator enforces well-scopedness | Full semantic types & local context | Pure `Elab` primitives | Order-sensitive dependent elaboration |
| **BER MetaOCaml N153** (`metaocaml/ber-metaocaml` `8891433d`) | Typed `'a code` (`Parsetree` + free-var heap) | Runtime `gensym` + stage typing | Strict explicit staging (`.< >.`, `.~`, `run`) | **Yes**: static well-typedness of generated code | **Eager dynamic** (`stackmark` + `close_code`); classifiers removed in N101 | None (parametric over staged types) | `CSP_ok` (bytecode) vs. `CSP_error` (native/AOT) | Modular generator typing; explicit bracket ceremony |
| **Scala 3** (`scala/scala3` `90f3daf0`) | Typed `Expr[T]`/`Type[T]` + TASTy `quotes.reflect` | Static Phase Consistency Principle + `Type[T]` healing | Explicit `'{...}`/`${...}` + `inline` macros | **Yes** for high-level quotes; low-level `reflect` checked dynamically | Static PCP bars local term cross-level escape | Full post-typer reflection (`TypeRepr`, `Mirror`) | Compiler JVM execution; explicit `ToExpr[T]` CSP | Separate compilation via TASTy; macro bytecode boundary |
| **Zig `comptime`** (`ziglang/zig` `738d2be9`) | Unified ZIR/AIR + first-class `type` | Standard lexical scoping | **Phase-collapsed** lazy CTFE | **No**: `.generic_poison_type` checked only on call (`analyzeCall`) | `isComptimeMutablePtr` bars `comptime var` escape | Post-layout `@typeInfo` (`ty.resolveLayout(pt)`) | Hermetic: package-confined `@embedFile` + dep tracking | PMEs and missing completion inside uninstantiated generics |
| **C++26 P2996R13** (`2025-06-20`) | Opaque `std::meta::info` + splicer `[: :]` | Compiler-resolved canonical entities | Strict `consteval`-only type containment | Non-dependent `consteval` modular; templates per instantiation | `consteval`-only types + `[expr.const]` injection scope rules | Post-resolution `offset_of`, `size_of`, `alignment_of`, `bit_size_of` | Pure core constant evaluation (no host I/O) | Eliminates token drift; `define_aggregate` adds completion edges |

The matrix exposes a structural frontier: syntactic token macros maximize surface-syntax freedom at the cost of compositional soundness; typed multi-stage languages preserve modular generator typing at the cost of explicit stage annotations; phase-collapsed CTFE maximizes generic layout ergonomics at the cost of PMEs and IDE analyzability; and post-resolution static reflection eliminates token-stream drift while forcing explicit encapsulation policy (`access_context`).

---

### 2. Syntactic Token-Stream Macros and Real-World Soundness Failures

Basis: normative + source + execution

Rust procedural macros execute during AST expansion **before** name resolution, trait solving, and layout computation, receiving only raw lexical tokens and opaque `Span` values. When derives synthesize `unsafe impl` blocks asserting padding freedom or bit validity—as in `google/zerocopy` (`ec133ce4d7993775413d852f91c9e3eb2a2a0897`)—five recurring failure modes arise directly from operating on pre-resolution syntax.

#### 2.1 Outside-In Attribute Ordering Invalidating Earlier `unsafe impl`s

Rust evaluates item attributes **outside-in** (lexically top-to-bottom). A `#[derive(...)]` macro receives the struct's token stream *at its position in the attribute stack* and appends generated `impl` items without preventing subsequent attributes from mutating the struct definition (`google/zerocopy` issue 388):

```rust
#[repr(C)]
#[derive(IntoBytes)]         // 1. Sees `{ bar: u8 }` -> 0 padding -> emits `unsafe impl IntoBytes`
#[insert_field(baz = "u32")] // 2. Runs AFTER derive; rewrites struct to `{ bar: u8, baz: u32 }` (3B padding!)
struct Foo {
    bar: u8,
}
```

In the verified proof-of-concept recorded on `google/zerocopy` issue 388 (comment `1737817682`), placing `#[derive(Debug)]` above `#[insert_field(baz = "u32")]` prints `Foo { bar: 10 }` even when constructed with `Foo { bar: 10, baz: 100 }`, confirming the derive never saw `baz`. Substituting `IntoBytes` for `Debug` emits an unsound `unsafe impl` exposing 3 uninitialized padding bytes to safe Rust. Rejecting unrecognized attributes inside a derive cannot fully close this hazard without language guarantees on attribute evaluation order, stripping, `#[cfg_attr(..., repr(...))]`, and forward-compatible built-in layout attributes.

#### 2.2 Missing Referential Type Identity and Nondeterministic Re-Expansion

Because token-stream derives lack canonical `DefId` handles for field types, validating field traits requires duplicating each field's syntactic type tokens into generated `where` clauses. If a field type is a macro invocation, the compiler expands it **multiple times**—once in the generated bounds and again in the struct definition.

In the safe-code segfault reproducer from `google/zerocopy` issue 2762:

```rust
static COUNTER: AtomicI32 = AtomicI32::new(0);

#[proc_macro]
pub fn make_type(_: TokenStream) -> TokenStream {
    match COUNTER.fetch_add(1, Ordering::SeqCst) {
        0..=2 => "i32",          // Checked in generated `where` bounds (`i32: TryFromBytes`)
        3 => "&'static i32",     // Actually compiled into `struct Thing { field: &'static i32 }`
        _ => panic!(),
    }.parse().unwrap()
}

#[derive(FromBytes)]
struct Thing { field: make_type!() }
```

`Thing::read_from_bytes(&1usize.to_ne_bytes())` succeeds in safe Rust, forging a dangling `&'static i32` at address `0x1` and segfaulting on dereference. Unexpanded syntax lacks **referential identity**: repeating tokens cannot guarantee they denote the same resolved type (and likewise duplicates side effects or nominal definitions inside inline `const { ... }` expressions).

#### 2.3 Lexical Frontend Duplication Drift on Raw Identifiers

Without a compiler `ReprOptions` query, `zerocopy-derive` must re-parse `#[repr(...)]` tokens (`zerocopy/zerocopy-derive/src/repr.rs`). Rust normalizes raw identifiers (`r#...`) inside attributes, so `#[r#repr(r#align(8))]` applies 8-byte alignment in `rustc`. Prior to `google/zerocopy` commit `cb6d16d0143c64e6e94058edbc2302d045e3e1a3` (present in examined `main` `ec133ce4d7993775413d852f91c9e3eb2a2a0897`), literal `is_ident("repr")` and `ident.to_string()` comparisons skipped `#[r#repr(r#align(8))]`, emitting padding-free `IntoBytes` impls for 8-byte-aligned 1-byte structs (7 trailing padding bytes). At `ec133ce4`, `util.rs:363–384` (`to_ident_str`, `path_is_ident`) strips `"r#"` for `RawRepr::from_attrs` / `RawRepr::from_meta` (`repr.rs:522–605`), but every future lexical normalization in `rustc` threatens renewed frontend drift.

#### 2.4 Missing Stable Def-Site Hygiene, Item Shadowing, and Unicode Lint Collisions

Inspecting `rust-lang/rust` at `b0b600668bb9b4a897e2299b0a44289d42276545` (`library/proc_macro/src/lib.rs:644–675`) shows the exact `proc_macro::Span` hygiene contract:
- `Span::call_site()` (stable 1.29.0): unhygienic call-site resolution.
- `Span::mixed_site()` (stable 1.45.0): def-site resolution **only** for local variables, labels, and `$crate`; **call-site resolution for everything else** (including items, generic type parameters, associated items, lifetimes, and fields), with call-site diagnostic location.
- `Span::def_site()` (`#[unstable(feature = "proc_macro_def_site", issue = "54724")]`): full def-site hygiene—unavailable on stable Rust.

Because `Span::mixed_site()` cannot hide generated marker types or shield them from caller type parameters, `zerocopy-derive` hits a three-way conflict:
1. At `ec133ce4`, `derive_projection_struct_union` (`zerocopy/zerocopy-derive/src/derive/project.rs:153–177`) generates private field-projection marker enums using non-ASCII `ẕ` (U+1E95) with `ident.span()`: `#vis enum ẕ<field> {}`.
2. When Unicode 18 (UTS #39) reclassified `ẕ` (U+1E95) from `IdentifierType::Recommended` to `IdentifierType::Uncommon_Use`, attributing `ẕ<field>` to the caller's span triggered `uncommon_codepoints` warnings and broke `#![deny(non_ascii_idents)]` crates (including Linux kernel targets); neither lint is suppressible at item scope because both are `crate_level_only`.
3. Conversely, using a fixed ASCII marker prefix without scanning `DeriveInput` creates a soundness hole: as noted in `zerocopy/zerocopy-derive/src/util.rs:182–193` (`Ctx::fresh_ident`: *"Unlike local variables, type parameters are not hidden by mixed-site hygiene"*), a caller generic parameter with the same ASCII name shadows the private marker enum inside `HasField` / `ProjectField`, exposing private fields to external safe `Ptr::project` callers. Even AST-scanning freshening (`util.rs:186–193`) is explicitly documented as *"best-effort; names introduced by nested macros are not considered."*

#### 2.5 Homonym Tokens with Distinct Hygiene Contexts (`Identity<Type = T>`)

In macro-generated Rust items, two `syn::Ident`s both printing as `T` can carry distinct opaque `SyntaxContext` hygiene marks (e.g., call-site `type T = u8` vs. def-site generic parameter `T`). Treating a `#[repr(C)]` struct with fields `(T_alias, T_param)` as homogeneous would overlook inter-field padding when `T_param = u16`.

In `google/zerocopy` `ec133ce4` (merged via commit `830bc15e5b29dcad061ce9751845e73713907a5f`), `homogeneous_field_bounds` (`zerocopy/zerocopy-derive/src/derive/into_bytes.rs:24–87`) preserves each field's original AST token and emits **non-deduplicated** bounds against a blanket-implemented `Identity` trait (`zerocopy/src/util/macro_util.rs:989–997`):

```rust
pub trait Identity { type Type: ?Sized; }
impl<T: ?Sized> Identity for T { type Type = T; }

// Emitted once per field element (intentionally NOT deduplicated):
// #element: ::zerocopy::util::macro_util::Identity<Type = #parameter>
```

Because `rustc` checks each bound after name resolution, `Identity<Type = T>` forces the compiler's type checker to serve as a hygiene-equivalence oracle that the macro API itself omits.

**Probe execution:** Part (b) of `support/verify_hygiene_and_staging.py` reproduces all three layout/validity counterexamples (`attr_order_hazard`: `token_emitted=True, actual_padding=3`; `reexpansion_hazard`: `token_emitted=True, actual_field_ty="&'static i32"`; `raw_ident_hazard`: `naive_emitted=True, actual_padding=7`) and verifies that post-resolution `ResolvedStructMetaInfo` reflection rejects all three while accepting padding-free `ValidPair` (`size=8, padding=0`).

---

### 3. Hygienic Binding as Sets of Scopes (Racket) and Turnstile

Basis: normative + documentation + source + execution

#### 3.1 Flatt's Sets-of-Scopes Expander (`racket/racket`)

Earlier Scheme macro expanders (KFFD, Clinger–Rees, `syntax-case`) tracked lexical hygiene via nested substitution ribcages, marks, and renaming histories that grew brittle across internal definition contexts, local modules, and multi-phase compilation (`for-syntax`). Matthew Flatt's *Binding as Sets of Scopes* (POPL '16, DOI `10.1145/2837614.2837620`), implemented in `racket/racket` at `8ed38e11307b13f25ca67224c66438b83340ae68`, replaces renaming with pure set algebra:

1. **Scoped syntax and phase-indexed `multi-scope`s:** Every syntax object pairs a datum with a set of `scope` tokens (`racket/src/expander/syntax/scope.rkt:89–93`, each holding an exact-rational `id`, hash `key`, `kind`, and mutable `binding-table`) plus module-level `multi-scope`s realized per phase on demand (`scope.rkt:170–185, 1104–1110`).
2. **GC-friendly binding storage (`add-binding-in-scopes!`):** Bindings for `(scopes, sym)` are attached to the `binding-table` of `max-sc = (find-max-scope scopes)`—the most recently allocated scope in the set (`scope.rkt:83–87, 992–1001`)—so disjoint lexical scopes do not pin one another in memory.
3. **Symmetric-difference macro marking (`flip-scope`) and use-site scopes:** `apply-transformer` (`racket/src/expander/expand/apply-transformer.rkt:98–134`) creates a fresh `intro-scope = (new-scope 'macro)` and `use-scopes = (maybe-create-use-site-scope ctx binding)`. It adds both to macro arguments on entry (`scope-arg`, lines 114–117) and applies `flip-scope` with `intro-scope` (`scope.rkt:633–640`, symmetric difference) to transformer results on exit (`scope-res`, lines 127–130). Caller subterms gain `intro-scope` on entry and lose it on exit; macro-introduced identifiers lack it on entry and gain it on exit.
4. **Maximal-subset resolution with explicit ambiguity detection:** `resolve` (`scope.rkt:1022–1098`) matches bindings `(b-scopes, binding)` for `sym` where `b-scopes ⊆ (scs ∪ reps)` and selects the **unique** candidate whose `b-scopes` is a superset of every other matching candidate. If two matching candidates have incomparable scope sets (neither `b1 ⊆ b2` nor `b2 ⊆ b1`) with no common matching superset, `resolve` returns `ambiguous-value` (`scope.rkt:1074–1085`) rather than picking arbitrarily. `free-identifier=?` (`racket/src/expander/syntax/binding.rkt:50–80`) compares canonical resolved bindings (`same-binding?`), while `bound-identifier=?` compares scope-set equality.
5. **Intentional anaphoric capture (`datum->syntax`):** Copying caller scope sets onto a synthesized symbol (`datum->syntax ctx-stx 'it`) cleanly supports controlled capture (e.g., anaphoric `aif`) without weakening default hygiene.

**Probe execution:** Part (a) of `support/verify_hygiene_and_staging.py` implements `SetsOfScopesEnv.resolve` and verifies five invariants: accidental capture prevention (`macro:tmp` vs. `caller:tmp`), reverse-capture prevention (`mod:helper_fn` vs. `caller:helper_fn`), intentional anaphoric capture (`aif:it`), incomparable-scope ambiguity (`AMBIGUOUS` disambiguated by superset `bind:ab`), and homonym hygiene distinctness (`type_alias:u8` vs. `generic_param:T`).

#### 3.2 Interleaving Bidirectional Typing with Expansion: Turnstile

Because standard Racket (and Typed Racket) expands macros completely before type checking, macro errors surface against desugared core forms and macros cannot inspect inferred subterm types. Chang, Knauth, and Greenman (*Type Systems as Macros*, POPL '17, DOI `10.1145/3009837.3009886`) introduce **Turnstile**, implementing bidirectional type systems ($\Gamma \vdash e \Rightarrow \tau$ and $\Gamma \vdash e \Leftarrow \tau$) directly inside Racket's expander:
- Typing rules are macros that drive subexpression elaboration via `local-expand` (`racket/src/expander/expand/local-expand.rkt`) inside internal definition contexts binding lexical variables to type metadata.
- Expanded subterms carry computed types on Racket `syntax-property` annotations, allowing parent macros to check premises and report errors at surface spans while elaborating to untyped core forms.

Turnstile achieves high linguistic reuse (System F, $\text{F}_\omega$, dependent DSLs) without duplicating parsers or hygiene, yet remains bound to `local-expand`'s recursive tree order—lacking global metavariable unification constraints and postponed typeclass resolution.

---

### 4. Hygienic Scoped Names and Typed Elaborator Reflection (Lean 4 and Idris)

Basis: normative + documentation + source + derived

Dependently typed theorem provers require overloading, dot-notation, coercions, and expected-type-driven elaboration—meaning name resolution and macro expansion cannot finish before type inference.

#### 4.1 Lean 4's `MacroScopesView` and Quotation-Time Pre-Resolution

Ullrich and de Moura (*Beyond Notations: Hygienic Macro Expansion for Theorem Proving Languages*, IJCAR '20, DOI `10.1007/978-3-030-51054-1_10`; extended in LMCS 2022, DOI `10.46298/lmcs-18(2:1)2022`), implemented in `leanprover/lean4` at `8009d0a64d2860606c6a5ac5ff6702622b24921e`, adapt scope stamping to an immutable, separately compiled design:

1. **Scopes encoded inside `Name` (`src/Init/Prelude.lean:5830–5910`):** Instead of mutable scope binding tables, Lean 4 encodes module-qualified scope lists directly inside hierarchical `Name`s (`<name>._@.(<module_name>.<scopes>)*.<mainModule>._hyg.<scopes>`), decoded by `extractMacroScopes` into `MacroScopesView { name, imported, ctx, scopes }` and re-encoded via `MacroScopesView.review`. `addMacroScope ctx n scp` (`Prelude.lean:5896–5909`) appends `scp` within the same `ctx` or archives prior scopes into `imported` across modules—serializing cleanly in `.olean` artifacts with zero mutable side tables. Pretty-printing sanitizes scoped binders with `✝` tombstones (`src/Lean/Hygiene.lean:49–115`, `pp.sanitizeNames`).
2. **Quotation-time global pre-resolution (`src/Init/Prelude.lean:5133–5193`):** To preserve overloading and prevent caller local variables from shadowing global constants inside macro templates, every `Syntax.ident` carries a `preresolved : List Syntax.Preresolved` field (`namespace (ns : Name) | decl (n : Name) (fields : List String)`), populated when the quotation `` `(...) `` is elaborated at macro definition time.

#### 4.2 Stratified `MacroM` vs. `TermElabM` and Postponement Order Sensitivity

Lean 4 separates metaprogramming into two layers:
- **Layer 1 — Pure `MacroM` (`src/Init/Prelude.lean:6020–6100`):** `Macro := Syntax → MacroM Syntax` has no `IO` and no mutable `Environment`, offering only hygienic quotation (`MonadQuotation`, `withFreshMacroScope`), recursion limits (`withIncRecDepth`), and read-only namespace/global queries (`Macro.Methods`). `macro` declarations desugar to `syntax` + `macro_rules` (`src/Lean/Elab/Macro.lean:18–47`).
- **Layer 2 — Typed `TermElabM` / `MetaM` (`elab`):** Elaborator macros inspect expected types, local contexts, and metavariables, producing core `Expr` terms checked by the small Lean kernel—parallel to Idris's `Elab` elaborator reflection over core TT terms (Christiansen and Brady, ICFP '16, DOI `10.1145/2951913.2951932`).

Because macro expansion, unification, coercions, typeclasses, and tactics mutually invoke one another, elaboration is **non-confluent**. Lean 4 orchestrates blocked tasks in `src/Lean/Elab/SyntheticMVars.lean:601–675` (`synthesizeSyntheticMVars`):
1. Loop `synthesizeSyntheticMVarsStep (postponeOnError := false) (runTactics := false)` in creation order (`filterRevM`) while progress continues (lines 612–644).
2. Under `postpone != .yes`, retry with `withoutPostponing` and `postponeOnError := true` (unblocking stuck projections such as `let x := ⟨1, 2⟩; Prod.fst x`, lines 646–663).
3. Fire `@[default_instance]` synthesis (`synthesizeUsingDefault`, line 664), then error-committing synthesis (line 666), then tactic blocks (`runTactics := true`, line 668), and finally report stuck metavariables and process universe constraints (lines 670–674).

Because these tiers fire sequentially, harmless syntactic reorderings can alter which metavariable unifies first. For Lean 4's InfoTree and LSP mechanics over this elaborator, see `lean-elaboration-hygiene-positions-and-infotree`.

---

### 5. Typed Multi-Stage Programming: MetaML, BER MetaOCaml, Scala 3, and 2LTT

Basis: normative + documentation + source + execution

#### 5.1 MetaML and Static Environment Classifiers

Taha and Sheard (*MetaML and Multi-Stage Programming with Explicit Annotations*, *Theoretical Computer Science* 248(1–2), pp. 211–242, 2000, DOI `10.1016/S0304-3975(00)00053-0`) established explicit typed staging via brackets (`<e> : <t>`), escapes (`~e`), and execution (`run e`). Typing the generator once guarantees generated code is well-typed for all inputs—provided **scope extrusion** is prevented (smuggling a future-stage binder `<x>` out of `<fun x -> ...>` via `run`, mutable refs, or exceptions).

Taha and Nielsen (*Environment Classifiers*, POPL '03, DOI `10.1145/640128.604134`) indexed code types by environment classifiers (`code γ τ`), requiring universally quantified closedness ($\forall \gamma.\ \text{code}\ \gamma\ \tau$) for `run`. Kameyama, Kiselyov, and Shan (*Closing the Stage*, PEPM '08, DOI `10.1145/1328408.1328430`; *Shifting the Stage*, JFP 2011, DOI `10.1017/S0956796811000256`) extended classifiers to handle mutable references and delimited control (`shift`/`reset`): an outer cell of invariant type `Ref(code γ0 τ)` statically rejects storing inner-binder code `code γ_inner τ` when $\gamma_{\text{inner}} \not\sqsubseteq \gamma_0$.

#### 5.2 BER MetaOCaml N153: Static Typing + Dynamic Stackmarks + Native Let-Insertion

Direct inspection of `metaocaml/ber-metaocaml` (`8891433d4bce906e69cb397fe27da04c4e6b3f37`, N153) and Kiselyov's FLOPS '14 (`10.1007/978-3-319-07151-0_6`) and FLOPS '24 (`10.1007/978-981-97-2300-3_12`) papers clarifies a crucial architectural shift:

1. **Static environment classifiers were deliberately dropped starting in BER N101** (`ber-metaocaml-153/NOTES.txt:365–372, 784`): pure classifiers could not soundly cover arbitrary OCaml effects without restricting the language and complicating generator types. `ber-metaocaml-153/codelib.mli:10–13` exposes unary `type !+'a code = 'a Trx.code`, `'a closed_code`, `'a pat_code`, and `'a val_code`.
2. **Static well-typedness + eager dynamic stackmarks** (`typing/trx.ml:18–29, 62–120, 996–1095`): OCaml's type checker verifies stage consistency at generator compile time (guaranteeing every generated AST is well-typed). Future-stage binders translate to HOAS-like combinators (`<fun x -> e>` $\to$ `build_simple_fun "x" (fun x -> <e>)`, `trx.ml:65`) performing runtime `gensym` inside a `with_stack_mark` region (`type stackmark = unit -> bool`, invalidated via `mark := false` on return or exception unwind; `trx.ml:996–1015`, swappable via `set_with_stack_mark` for `delimcc`). Each code value carries `Code of (string loc heap * vletbindings) * Parsetree.expression` (`trx.ml:1086–1091`), storing free variables in a priority max-heap (`trx.ml:1036–1061`). Every `build_*` combinator checks that all `stackmark`s remain active, catching ref-cell or exception scope extrusion **immediately** during code construction; `close_code_delay_check` (`trx.ml:1163–1182`) rejects any remaining free variables with binder source locations.
3. **Native let-insertion (`genlet`, `with_locus`, `val_code`):** Because `code_repr` already tracks free variables in a priority heap, BER MetaOCaml adds floating virtual bindings (`vletbindings`, `codelib.mli:65–105`; `trx.ml:158–290`). `genlet e` floats `let fresh = e` outward and materializes it immediately beneath the binder of `e`'s innermost free variable; `with_locus` injects a dummy free variable to prevent effectful expressions like `genlet .< ref 0 >.` from floating outside a generated lambda (`trx.ml:257–277`); `'a val_code` (`[@metaocaml.value]`) witnesses syntactic values safe to duplicate.
4. **Cross-Stage Persistence (CSP) split** (`codelib.mli:20–34, 107–118`; `lifts.mli`; `trx.ml:292–307, 1106–1188`): Base literals and `module type lift` types serialize into ASTs, and separately compiled global identifiers persist by qualified path. Local closures and heap values become `metaocaml.csp` virtual bindings governed by `csp_handling = CSP_ok | CSP_warn | CSP_error`—allowed in same-process bytecode `Runcode.run` (`CSP_ok`) but rejected by default for native/AOT `Runnative` (`CSP_error`), where host memory pointers cannot cross binary/ISA boundaries.

**Probe execution:** Part (c) of `support/verify_hygiene_and_staging.py` runs both mechanisms: the static classifier checker accepts `run .< fun x:Int -> x + 1 >.` (`TFun(TInt, TInt)`) and outer-to-inner splices while rejecting ref-cell extrusion (`cannot store code at inner classifier gamma_4 into ref at outer classifier gamma0`) and open-code `run` (`Cannot run open code bound to rigid classifier gamma_5`); the dynamic stackmark engine builds closed `(fun x -> (x * (x * (x * 1))))` for `spower(3, x)` while eagerly catching ref-cell (`'x_ref'`) and exception-unwind (`'x_exc'`) extrusion.

#### 5.3 Scala 3 (`scala.quoted`), Two-Level Type Theory, and CMTT

- **Scala 3 (`scala/scala3` `90f3daf0a4795308d9c0e1b8f2265aeaecae8aa2`; Stucki, Biboudis, and Odersky, GPCE '18, DOI `10.1145/3278122.3278139`):** Combines typed staging (`Expr[T]`, `Type[T]`), compile-time `inline` macros, and typed TASTy reflection (`Quotes.reflect.{TypeRepr, Symbol}`, `library/src/scala/quoted/Quotes.scala:49, 138, 3080, 4356, 4964`). `StagingLevel.scala:14–52` tracks integer staging depth (`quoteContext` `+1`, `spliceContext` `-1`, `levelOf(sym)`), and `CrossStageSafety.scala:20–163` enforces the **Phase Consistency Principle (PCP)**: local terms must satisfy `levelOf(sym) == level`, while level-0 local types used inside higher-level quotes are **healed** by summoning a given `t: Type[T]` tag and rewriting `T` to `t.Underlying` (`CrossStageSafety.scala:24–52, 75–77`). CSP requires an explicit `ToExpr[T]` typeclass (`ToExpr.scala:12–55`), excluding unserializable closures statically.
- **Two-Level Type Theory (2LTT; Kovács, ICFP '22, DOI `10.1145/3547641`):** Separates a dependently typed Meta universe from an Object runtime universe, achieving modular definition-time type checking of staged generators with guaranteed complete erasure of stage-0 types and closures.
- **Contextual Modal Type Theory (CMTT; Nanevski, Pfenning, and Pientka, ACM TOCL 2008, DOI `10.1145/1352582.1352591`):** Explicitly types open code by its free-variable context (`[Ψ ⊢ A]`), enabling formal verification of metaprograms over open syntax trees at the cost of explicit context-substitution ceremony.

---

### 6. Phase-Collapsed CTFE (`Zig comptime`) vs. Post-Resolution Static Reflection (`C++26 P2996R13`)

Basis: normative + documentation + source + derived

#### 6.1 Zig `comptime` (`ziglang/zig` `738d2be9d6b6ef3ff3559130c05159ef53336224`)

Zig removes syntactic macros altogether: `type` is a first-class `comptime`-only value, generics are ordinary functions returning `type`, and `src/Sema.zig` evaluates `comptime` code lazily during semantic analysis.

1. **Lazy generic instantiation and Post-Monomorphization Errors (PMEs):** Uninstantiated generic signatures carry `.generic_poison_type` placeholders (`src/Sema.zig:2172, 4737–4741, 7368, 7464`). Only at a concrete call site inside `analyzeCall` (`Sema.zig:7218–7490`) does `Sema` require a comptime-known generic callee (line 7279), declare an incremental `.src_hash` dependency on the generic signature (line 7361), evaluate each generic parameter type via `resolveInlineBody` (line 7401), populate `generic_inst_map` with comptime arguments or dummy typed `.alloc` placeholders for runtime arguments (lines 7420–7449), resolve the return type (lines 7457–7490), and analyze the specialized body. Consequently, errors in uninstantiated generics or untaken `comptime if` branches surface only when a downstream caller instantiates them, and IDEs lack complete type info inside generic definitions.
2. **Bounded-fuel termination:** Because `comptime` is Turing-complete, `Sema` bounds backward branches using `pub const default_branch_quota = 1000` (`Sema.zig:77, 193`), adjustable via `@setEvalBranchQuota`.
3. **Post-layout reflection (`@typeInfo`) and hermetic `@embedFile`:** `zirTypeInfo` (`Sema.zig:17143–17770`) registers an incremental `.namespace` dependency (`Sema.zig:17155`) and for structs calls **`try ty.resolveLayout(pt)`** (`Sema.zig:17702`) before emitting `std.builtin.Type.Struct` / `StructField` records carrying resolved names, canonical types, default pointers, and target ABI alignments—eliminating all pre-resolution token-macro layout hazards. Mutable `comptime var` pointers are barred from escaping to runtime (`checkPtrIsNotComptimeMutable` / `isComptimeMutablePtr`, `Sema.zig:23368, 36928–36989`), and ambient compile-time I/O is forbidden; external files enter strictly through `zirEmbedFile` (`Sema.zig:13903–13937`), which enforces package-path confinement (`ImportOutsideModulePath`) and registers `.embed_file` dependencies (line 13929).

#### 6.2 C++26 Static Reflection (`WG21 P2996R13`, Adopted Sofia June 2025)

WG21 **P2996R13** (*Reflection for C++26*, Childers, Dimov, Katz, Revzin, Sutton, Vali, and Vandevoorde, `2025-06-20`, adopted into the C++26 draft alongside expansion statements `template for`) provides compiler-resolved static reflection without untyped token rewriting:

1. **Opaque semantic handle (`std::meta::info`, §4.1–§4.3):** `^^` (`[expr.reflect]`) reflects resolved types, aliases, members, bases, enumerators, functions, namespaces, templates, or structural-type constants into `std::meta::info` (`decltype(^^::)`), and splicers `[: r :]` (`[basic.splice]`) re-inject reflections into expressions, types, or member accesses (disallowing constructors, destructors, and namespace definitions, §4.2.2). Comparing reflections tests canonical entity identity, eliminating re-expansion divergence.
2. **`consteval`-only stage containment (§4.3.3):** `std::meta::info` and every compound type containing it (`is_consteval_only`) are `consteval`-only: objects may exist only within constant evaluation, `constexpr` variables, or template parameter objects, and operands of `consteval`-only type trigger immediate-function escalation, barring runtime leakage.
3. **Compiler-computed layout reflection (`[meta.reflection.layout]`, §4.4.20):**
   ```cpp
   namespace std::meta {
     struct member_offset {
       ptrdiff_t bytes; ptrdiff_t bits;
       constexpr auto total_bits() const -> ptrdiff_t { return CHAR_BIT * bytes + bits; }
       auto operator<=>(member_offset const&) const = default;
     };
     consteval auto offset_of(info r) -> member_offset;
     consteval auto size_of(info r) -> size_t;
     consteval auto alignment_of(info r) -> size_t;
     consteval auto bit_size_of(info r) -> size_t;
   }
   ```
   Metafunctions verify padding, alignment, and bit-field geometry directly against the compiler's target layout without re-parsing attributes.
4. **Scoped type synthesis (`data_member_spec`, `define_aggregate`, §4.4.19):** `consteval` blocks may complete forward-declared aggregates via `define_aggregate(^^S, specs)`, bounded by `[expr.const]` rules prohibiting injected declarations from escaping function parameter scopes.
5. **Encapsulation vs. Intensional Type Analysis (`access_context`):** Member queries (`members_of`, `nonstatic_data_members_of`, `bases_of`) accept `std::meta::access_context`: `access_context::current()` enforces C++ access control, whereas `access_context::unchecked()` bypasses `private`/`protected` boundaries. This sharpens the classical tension between **Reynolds's Parametricity / Representation Independence** (Reynolds 1983) and **Harper & Morrisett's Intensional Type Analysis** (POPL '95, DOI `10.1145/199448.199475`): unchecked layout/member reflection lets generic code observe or mutate private representation invariants (e.g., writing zero bytes into a private `NonZero` field) unless types explicitly gate structural views behind opt-in traits or validity predicates.

---

### 7. Cross-Cutting Engineering Trade-offs: Hermeticity, Verification Scaling, Host-Target CTFE, and IDE Incrementality

Basis: documentation + source + derived

1. **Hermeticity and separate compilation:** Ambient host I/O inside metaprograms (`Rust` `proc_macro`, `Template Haskell` `runIO`, `Lean 4` `TermElabM` with `IO`) breaks reproducible caching and expands build-time supply-chain risk; whole-program open-world reflection queries destroy separate compilation. Zig's `zirEmbedFile` (`Sema.zig:13903–13937`) exemplifies the minimal hermetic contract: forbid ambient I/O and track every external input as an explicit content-addressed build dependency (see `scoped-exportlist-invalidation-slicing-and-proc-macro-determinism-sandbox` for Rust-specific proc-macro sandboxing).
2. **Verifying metaprograms once vs. per expansion:** Post-expansion verification of `#[derive(...)]`, templates, or tactics scales with expanded code size and provides no universal guarantee for untested caller types. Universal generator verification requires either typed staging (`BER MetaOCaml`, `Scala 3`, `2LTT`) for type safety, deep-embedded computational reflection for functional/layout soundness proven once, or LCF-style small proof certificates emitted per expansion to keep complex generators outside the trusted computing base.
3. **Host-target semantic divergence in CTFE:** Cross-compiling (e.g., x86-64 host targeting 32-bit big-endian RISC-V or Wasm) causes silent miscompilation unless CTFE runs on a **target-parameterized abstract machine** controlling pointer width, endianness, struct alignment (`ty.resolveLayout(pt)`), `char` signedness, IEEE-754 `NaN` payloads, and pointer provenance. Native host proc-macros in Rust drift whenever macro logic inspects host `usize`/layout instead of emitting target-side `const` checks.
4. **IDE responsiveness and incrementality:** Modular definition-time typing (`MetaOCaml`, `Scala 3`, `2LTT`), explicit hygiene/provenance (`Racket` scope sets, `Lean 4` `MacroScopesView` + `InfoTree`), and fine-grained dependency registration (`Zig` `declareDependency`) enable responsive completion and refactoring; lazy phase-collapsed generics and black-box token macros degrade both (see `language-server-snapshots-views-and-compiler-backed-ide-architectures`).

## Boundaries

- **not examined:**
  - Empirical compile-time wall-clock and memory benchmarks comparing Rust proc-macro dylib IPC, Zig `comptime`, BER MetaOCaml staging, and experimental C++26 P2996 compilers.
  - Source-level implementations of Template Haskell (`Language.Haskell.TH`), the C/C++ preprocessor (`cpp`), Idris 2's compiler internals beyond Christiansen and Brady (ICFP '16), and internal `rustc_expand` `SyntaxContext` structures beyond `library/proc_macro/src/lib.rs`.
  - Interaction between Scala 3's experimental capture checking (`import language.experimental.captureChecking` in `ToExpr.scala:3`) and effectful multi-stage scope extrusion.
- **unknown:**
  - Whether C++26 `std::meta::define_aggregate` combined with `access_context::unchecked()` will induce widespread encapsulation fragility in production C++ libraries after standard-conforming compilers ship.
  - Whether Kovács's Two-Level Type Theory (2LTT) can integrate ergonomic binding-time polymorphism and affine/linear borrow checking without duplicating standard libraries across stages.
  - Stabilization timeline for Rust `proc_macro_def_site` (`rust-lang/rust#54724`) or compiler-backed post-resolution Rust reflection APIs.
- **known not to apply:**
  - Static environment-classifier scope-extrusion guarantees (Taha and Nielsen 2003) **do not apply** to BER MetaOCaml N101–N153 (`metaocaml/ber-metaocaml` `8891433d`), which removed environment classifiers and detects extrusion dynamically at generator runtime via `stackmark` checks.
  - Rust's stable `Span::mixed_site()` hygiene **does not apply** to generated item definitions, generic type parameters, associated items, lifetimes, or struct fields.
  - Post-resolution semantic reflection (`std::meta::info`, Zig `@typeInfo`) **does not by itself enforce abstraction or type invariants** when unchecked private access (`access_context::unchecked()`) or raw layout byte mutation is permitted.
  - Passing `support/verify_hygiene_and_staging.py` certifies only its self-contained algorithmic models, not full upstream compilers.
- **unsupported:**
  - Stable Rust `proc_macro` explicitly does not support `Span::def_site()` (`#[unstable(feature = "proc_macro_def_site", issue = "54724")]`), compiler-resolved layout reflection during expansion, or post-attribute-expansion derive hooks.
  - C++26 P2996R13 explicitly prohibits runtime objects of `std::meta::info` (§4.3.3 `consteval`-only) and splicing constructors, destructors, or namespace definitions (§4.2.2).
  - BER MetaOCaml native compilation (`Runnative` / `close_code ~csp:CSP_error`, `typing/trx.ml:1161–1176`) explicitly rejects non-serializable local closures and heap values as CSP.
  - Zig `comptime` explicitly prohibits ambient filesystem/network I/O outside `@embedFile` and rejects paths outside the package root (`error.ImportOutsideModulePath`, `src/Sema.zig:13918–13921`).

## Evidence

All primary sources below were verified on `2026-11-19`.

### 1. Pinned Repository Sources

- **`google/zerocopy`** (`ec133ce4d7993775413d852f91c9e3eb2a2a0897`):
  - `zerocopy/zerocopy-derive/src/derive/into_bytes.rs:24–87` (`homogeneous_field_bounds`) & `zerocopy/src/util/macro_util.rs:989–997` (`Identity`, merged in `830bc15e5b29dcad061ce9751845e73713907a5f`).
  - `zerocopy/zerocopy-derive/src/repr.rs:522–605` & `zerocopy/zerocopy-derive/src/util.rs:363–384` (`to_ident_str`, `path_is_ident`, merged in `cb6d16d0143c64e6e94058edbc2302d045e3e1a3`).
  - `zerocopy/zerocopy-derive/src/derive/project.rs:143–195` (`derive_projection_struct_union`, `ẕ` marker enum) & `zerocopy/zerocopy-derive/src/util.rs:182–193` (`Ctx::fresh_ident`).
  - Upstream issue specimens: `google/zerocopy` issue 388 (comment `1737817682`) and issue 2762.
- **`rust-lang/rust`** (`b0b600668bb9b4a897e2299b0a44289d42276545`): `library/proc_macro/src/lib.rs:644–675` (`Span::{def_site, call_site, mixed_site}`).
- **`racket/racket`** (`8ed38e11307b13f25ca67224c66438b83340ae68`): `racket/src/expander/syntax/scope.rkt:83–185, 633–644, 992–1110`; `syntax/binding.rkt:50–135`; `expand/apply-transformer.rkt:98–159`.
- **`leanprover/lean4`** (`8009d0a64d2860606c6a5ac5ff6702622b24921e`): `src/Init/Prelude.lean:5133–5193, 5806–5934, 6020–6100`; `src/Lean/Hygiene.lean:16–115`; `src/Lean/Elab/Macro.lean:18–47`; `src/Lean/Elab/SyntheticMVars.lean:601–675`.
- **`metaocaml/ber-metaocaml`** (`8891433d4bce906e69cb397fe27da04c4e6b3f37`, N153): `ber-metaocaml-153/{codelib.mli,lifts.mli,runcode.mli,NOTES.txt:355–395,784}`; `typing/trx.ml:1–307, 996–1200`.
- **`scala/scala3`** (`90f3daf0a4795308d9c0e1b8f2265aeaecae8aa2`): `compiler/src/dotty/tools/dotc/staging/{StagingLevel.scala:14–52,CrossStageSafety.scala:20–163}`; `library/src/scala/quoted/{ToExpr.scala:1–55,Quotes.scala:49,138,3080,4356,4964}`.
- **`ziglang/zig`** (`738d2be9d6b6ef3ff3559130c05159ef53336224`): `src/Sema.zig:77, 193, 2172, 4737–4741, 7218–7490, 13903–13937, 17143–17770, 23368, 36928–36989`.

### 2. Peer-Reviewed Literature and Standards

- Matthew Flatt, *"Binding as Sets of Scopes"*, POPL '16, pp. 705–717, Jan. 2016, DOI `10.1145/2837614.2837620`.
- Stephen Chang, Alex Knauth, and Ben Greenman, *"Type Systems as Macros"*, POPL '17, pp. 694–705, Jan. 2017, DOI `10.1145/3009837.3009886`.
- Sebastian Ullrich and Leonardo de Moura, *"Beyond Notations: Hygienic Macro Expansion for Theorem Proving Languages"*, IJCAR '20 (LNCS 12167, pp. 167–182), DOI `10.1007/978-3-030-51054-1_10`; extended in *LMCS* 18(2:1), 2022, DOI `10.46298/lmcs-18(2:1)2022`.
- David R. Christiansen and Edwin Brady, *"Elaborator Reflection: Extending Idris in Idris"*, ICFP '16, Sept. 2016, DOI `10.1145/2951913.2951932`.
- Walid Taha and Tim Sheard, *"MetaML and Multi-Stage Programming with Explicit Annotations"*, *TCS* 248(1–2), pp. 211–242, Oct. 2000, DOI `10.1016/S0304-3975(00)00053-0`.
- Walid Taha and Michael Florentin Nielsen, *"Environment Classifiers"*, POPL '03, Jan. 2003, DOI `10.1145/640128.604134`.
- Yukiyoshi Kameyama, Oleg Kiselyov, and Chung-chieh Shan, *"Closing the Stage"*, PEPM '08, DOI `10.1145/1328408.1328430`; *"Shifting the Stage: Staging with Delimited Control"*, *JFP*, 2011, DOI `10.1017/S0956796811000256`.
- Oleg Kiselyov, *"The Design and Implementation of BER MetaOCaml"*, FLOPS '14 (LNCS 8475, pp. 86–102), DOI `10.1007/978-3-319-07151-0_6`; *"MetaOCaml: Ten Years Later"*, FLOPS '24 (LNCS 14659, pp. 219–236), DOI `10.1007/978-981-97-2300-3_12`.
- Nicolas Stucki, Aggelos Biboudis, and Martin Odersky, *"A Practical Unification of Multi-Stage Programming and Macros"*, GPCE '18, Nov. 2018, DOI `10.1145/3278122.3278139`.
- András Kovács, *"Staged Compilation with Two-Level Type Theory"*, *PACMPL* 6(ICFP), Art. 110, 2022, DOI `10.1145/3547641`.
- Aleksandar Nanevski, Frank Pfenning, and Brigitte Pientka, *"Contextual Modal Type Theory"*, *ACM TOCL* 9(3), Art. 23, 2008, DOI `10.1145/1352582.1352591`.
- John C. Reynolds, *"Types, Abstraction and Parametric Polymorphism"*, *Information Processing 83*, pp. 513–523, 1983.
- Robert Harper and Greg Morrisett, *"Compiling Polymorphism Using Intensional Type Analysis"*, POPL '95, Jan. 1995, DOI `10.1145/199448.199475`.
- ISO/IEC JTC1/SC22/WG21 P2996R13, Childers, Dimov, Katz, Revzin, Sutton, Vali, and Vandevoorde, *"Reflection for C++26"*, `2025-06-20`, `https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2025/p2996r13.html`.

### 3. Preserved Executable Probe Output

Command run on `2026-11-19` (Python 3 stdlib, exit code `0`):

```console
python3 -B reports/metaprogramming-hygiene-staging-and-compile-time-execution/support/verify_hygiene_and_staging.py
```

```text
[PASS] Part (a) Flatt Sets-of-Scopes:
  - capture_prevented: ('macro:tmp', 'caller:tmp')
  - reverse_capture_prevented: ('mod:helper_fn', 'caller:helper_fn')
  - anaphoric_capture_resolved: aif:it
  - incomparable_ambiguity: ('AMBIGUOUS', 'bind:ab')
  - homonym_distinct: ('type_alias:u8', 'generic_param:T')
[PASS] Part (b) Token-Stream Macros vs. Semantic Reflection:
  - attr_order_hazard: {'token_emitted': True, 'actual_padding': 3, 'reflection_ok': False}
  - reexpansion_hazard: {'token_emitted': True, 'actual_field_ty': "&'static i32", 'reflection_ok': False}
  - raw_ident_hazard: {'naive_emitted': True, 'actual_padding': 7, 'reflection_ok': False}
  - valid_pair: {'size': 8, 'padding': 0, 'reflection_ok': (True, True)}
[PASS] Part (c) Multi-Stage Scope-Extrusion Detection:
  - static_valid_run_type: TFun(arg=TInt(), ret=TInt())
  - static_ref_extrusion_caught: Ref scope extrusion rejected statically: cannot store code at inner classifier gamma_4 into ref at outer classifier gamma0
  - static_open_run_caught: Cannot run open code bound to rigid classifier gamma_5
  - dynamic_spower3: (fun x -> (x * (x * (x * 1))))
  - dynamic_ref_extrusion_caught: Scope extrusion detected at code construction: variable 'x_ref' escaped its binder region
  - dynamic_exc_extrusion_caught: Scope extrusion detected at code construction: variable 'x_exc' escaped its binder region
```

## Revalidation

1. **Re-run the preserved executable probe (`< 0.1 s`, stdlib only):**
   ```console
   python3 -B reports/metaprogramming-hygiene-staging-and-compile-time-execution/support/verify_hygiene_and_staging.py
   ```
   Confirms internal consistency of the Sets-of-Scopes, token-vs-reflection, static-classifier, and dynamic-stackmark models; does not test newer compiler builds.
2. **Rust `proc_macro` & `google/zerocopy` targeted diffs:**
   - Diff `library/proc_macro/src/lib.rs` in `rust-lang/rust` against `b0b600668bb9b4a897e2299b0a44289d42276545` for `proc_macro_def_site` stabilization or new reflection APIs.
   - Diff `zerocopy/zerocopy-derive/src/{repr.rs,util.rs,derive/into_bytes.rs,derive/project.rs}` in `google/zerocopy` against `ec133ce4d7993775413d852f91c9e3eb2a2a0897` to track `ẕ` marker replacement, `Identity<Type = T>`, and mitigations for issues 388 and 2762.
3. **Upstream expander, staging, and CTFE diffs:**
   - `racket/racket` (`8ed38e11`): `racket/src/expander/syntax/scope.rkt` (`resolve`, `flip-scope`) and `expand/apply-transformer.rkt`.
   - `leanprover/lean4` (`8009d0a6`): `src/Init/Prelude.lean` (`MacroScopesView`, `Syntax.Preresolved`, `MacroM`) and `src/Lean/Elab/SyntheticMVars.lean`.
   - `metaocaml/ber-metaocaml` (`8891433d`): `typing/trx.ml` (`with_stack_mark`, `close_code_delay_check`) and `ber-metaocaml-153/codelib.mli`.
   - `scala/scala3` (`90f3daf0`): `compiler/src/dotty/tools/dotc/staging/{StagingLevel,CrossStageSafety}.scala` (including any capture-checking integration).
   - `ziglang/zig` (`738d2be9`): `src/Sema.zig` (`analyzeCall`, `zirTypeInfo`, `zirEmbedFile`, `default_branch_quota`, `isComptimeMutablePtr`).
4. **C++26 standard check:** Compare published ISO/IEC 14882:2026 `[expr.reflect]`, `[basic.splice]`, `[meta.reflection.access.context]`, `[meta.reflection.layout]`, and `[meta.reflection.define.aggregate]` against WG21 P2996R13 (`2025-06-20`) for post-Sofia defect resolutions.
