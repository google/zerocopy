# rustc Macro Hygiene (`SyntaxContext`, `Transparency`), Procedural-Macro Spans, `$crate` Resolution, and Edition 2024 `:expr` / `:expr_2021` Fragment Grammar

## Summary

Rust's macro hygiene, `$crate` crate-root resolution, procedural-macro span modes, and Edition 2024 fragment-specifier backward compatibility are governed by four coupled compiler mechanisms across `rustc_span`, `rustc_ast`, `rustc_parse`, `rustc_expand`, `rustc_resolve`, `rustc_middle`, and `rustc_hir_typeck`:

1. **Mark-stack `SyntaxContext` with a three-tier `Transparency` lattice (`Transparent < SemiOpaque < Opaque`):** Every `Span` carries a `SyntaxContext` index whose node caches two pre-projected parent contexts—`opaque` (retaining only `Opaque` marks, exposed as `normalize_to_macros_2_0()`) and `opaque_and_semiopaque` (retaining `Opaque` and `SemiOpaque` marks, exposed as `normalize_to_macro_rules()`). Declarative `macro_rules!` expansions receive `Transparency::fallback(true) = Transparency::SemiOpaque`, while experimental Macros 2.0 (`macro`) receive `Transparency::fallback(false) = Transparency::Opaque`. During `macro_by_example` (MBE) transcription, `Marker::mark_span` applies `(expand_id, transparency)` to tokens emitted from the macro template while leaving captured metavariable arguments wrapped inside `Delimiter::Invisible(InvisibleOrigin::MetaVar(_))` with their caller `SyntaxContext` intact.
2. **Projection-selected name-resolution asymmetry under `SemiOpaque`:** `SemiOpaque` isolation applies strictly to resolution queries that normalize via `normalize_to_macro_rules()`—local variable bindings (`fresh_binding` and non-parameter, non-`TypeNS` ribs in `resolve_ident_in_lexical_scope`), loop and block labels (`resolve_label`, `with_resolved_label`), delegation `self`, and `$crate` (`resolve_crate_root`). Every module-level item, import, type-namespace binding (`IdentKey` / `BindingKey` backed by `Macros20NormalizedSyntaxContext`), generic type/const parameter (`rib.kind.contains_params()`), struct/variant field (`find_adt_field`), and inherent or trait method (`AssocItems::find_by_ident_and_namespace`, `TyCtxt::hygienic_eq`, `TyCtxt::adjust_ident_and_get_scope`) normalizes via `normalize_to_macros_2_0()`, which strips `SemiOpaque` marks prior to comparison and prior to `adjust(...)`. Consequently, `macro_rules!` and `Span::mixed_site()` isolate locals and labels while leaking macro-defined items (`struct`, functions) into caller scope and accessing caller private methods; by contrast, `Opaque` (`macro` 2.0 and `Span::def_site()`) retains its mark through `normalize_to_macros_2_0()`, isolating items (`E0425`) and forcing method visibility checks into the macro definition module (`E0624` on private caller methods).
3. **Resolving `$crate` bypasses `SemiOpaque` stripping via reverse mark scan:** `Resolver::resolve_crate_root` normalizes `$crate` with `normalize_to_macro_rules()` and scans `ctxt.marks()` from outermost to innermost—first consuming any trailing `Opaque` marks and then continuing across adjacent `SemiOpaque` marks—selecting `self.expn_def_scope(mark)`'s crate. This renders `$crate` immune to caller module shadowing across both same-crate and cross-crate boundaries while preserving standard visibility checks (`E0603` on private items).
4. **Procedural-macro spans and Rust Reference drift:** Contrary to `rust-lang/reference`'s unqualified prose ("Procedural macros are *unhygienic*"), `rustc`'s `proc_macro::server::Rustc` populates three distinct hygiene anchors in `ExpnGlobals`: `Span::call_site()` (`Transparent`), `Span::mixed_site()` (`SemiOpaque`, stable since Rust 1.45.0), and `Span::def_site()` (`Opaque`, unstable behind `#![feature(proc_macro_def_site)]`), plus `resolved_at`/`located_at` re-anchoring (stable since 1.45.0).
5. **Edition 2024 `:expr` vs. `:expr_2021` binds at macro definition time while preserving `FOLLOW(expr)`:** `NonterminalKind::from_symbol` inspects the edition of the macro-definition span (via `mbe::quoted`): `:expr` inside Edition 2024 lowers to `NtExprKind::Expr`, `:expr` inside Edition <= 2021 lowers to `Expr2021 { inferred: true }`, and `:expr_2021` always lowers to `Expr2021 { inferred: false }`. In `Parser::nonterminal_may_begin_with`, `Expr2021` excludes top-level `const` (`const { ... }`) and `kw::Underscore` (`_`), whereas Edition 2024 `Expr` admits both (`(can_begin_expr() || is_keyword(kw::Underscore)) && !is_keyword(kw::Let)`). Both variants share the exact same `is_in_follow` set (`=>`, `,`, `;`, closing delimiters), preserving fragment-boundary determinism across editions.
6. **Anneal boundary and kernel-checked mechanization:** In `joshlf/anneal`, `anneal-rustc-capture` runs inside `Callbacks::after_analysis`, strictly downstream of macro expansion and name resolution; procedural macros and build scripts sit outside the Lean verification kernel's TCB (requiring host build isolation under the threat model). All structural invariants above—local-variable alpha-invariance under `SemiOpaque`/`Opaque`, 3-tier `Transparency` separation witnesses, `$crate` reverse mark scanning across nested macros, and `Expr2021 ⊊ Expr2024` strict sublanguage inclusion preserving follow-set disjointness—are formalized and kernel-checked in `support/MacroHygieneSyntaxContextAndEditionFragSoundness.lean` (`Lean v4.34.1`, 1,556 lines, 81 surface theorems, 74 `noncomputable def`s, 0 `sorry`, 0 `Classical.choice`, 0 `._unsafe_rec`, only axiom `[propext]`).

## Applicability

Basis: source + execution + documentation

This report characterizes the exact relationship across five pinned primary subjects recorded in `REPORT.json`:

| Subject | Pin / Version | Role in this report |
| :--- | :--- | :--- |
| `rust-lang/rust` (HEAD) | `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` (`1.102.0`, 2026-11-23) | Primary compiler source authority for `SyntaxContext`, `Transparency`, MBE transcription, resolution, typeck method/field lookup, proc-macro server globals, and fragment parsing. |
| `rust-lang/rust` (executed toolchain) | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, 2026-05-31, LLVM `22.1.6`) | Live compiler binary executed on `x86_64-unknown-linux-gnu` for all 21 sub-experiments in `support/probe_macro_hygiene_and_edition2024_expr_frag.py` and `support/probe_results.json`. |
| `rust-lang/reference` | `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (2026-11-17) | Descriptive specification compared against `rustc` implementation (`src/macros-by-example.md`, `src/procedural-macros.md`, `src/macros.md`). |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` (2026-11-19) | Downstream Rust verifier establishing capture phase (`after_analysis`), build/proc-macro threat boundaries, and Lean TCB purity rules (`noncomputable def`, zero `._unsafe_rec`). |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, `x86_64-unknown-linux-gnu`) | Kernel proof checker executing strict verification (`-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) and MetaM constant-environment auditing on `support/MacroHygieneSyntaxContextAndEditionFragSoundness.lean`. |

**Cross-revision equivalence and deltas (`1.98.0-nightly` vs. `1.102.0` HEAD):** Direct file-by-file source comparison between `14210df0e27c` and `0259d5e9a81c` confirms identical semantics across every examined state machine, with only representational refactoring and line-offset shifts:
- `compiler/rustc_span/src/hygiene.rs`: In `1.98.0-nightly` (`1,556` lines), `SyntaxContext` is `pub struct SyntaxContext(u32)` (`hygiene.rs:54`), `Transparency` is at `hygiene.rs:167-186`, and `HygieneData::apply_mark` is at `hygiene.rs:519-554`. In `1.102.0` HEAD (`1,766` lines), `SyntaxContext` uses `rustc_index::newtype_index!` with `#[max = 0x1FFF_FFFF]` (`hygiene.rs:52-60`), `Transparency` is at `hygiene.rs:180-200`, and `HygieneData::apply_mark` is at `hygiene.rs:688-723`—preserving the exact 29-bit index invariant, negative `!Ord`/`!PartialOrd` bounds, cached projection fields, and splicing logic.
- `compiler/rustc_parse/src/parser/nonterminal.rs`: Identical `nonterminal_may_begin_with` logic for `Expr2021` and `Expr` (shifted by 1 line: `nonterminal.rs:21-63` in `1.98.0-nightly` vs. `nonterminal.rs:22-64` in `1.102.0` HEAD).
- `compiler/rustc_ast/src/token.rs`, `compiler/rustc_expand/src/mbe/{macro_rules.rs, transcribe.rs, quoted.rs}`, `compiler/rustc_expand/src/proc_macro_server.rs`, `compiler/rustc_resolve/src/{lib.rs, ident.rs, late.rs}`, `compiler/rustc_middle/src/ty/{mod.rs, assoc.rs}`, and `compiler/rustc_hir_typeck/src/{expr.rs, method/probe.rs}`: Identical algorithms and normalization sites, differing only in line numbers (`resolve_crate_root` at `lib.rs:2312-2383` in `1.98.0-nightly` vs. `2375-2446` in HEAD; `fresh_binding` at `late.rs:4336` in `1.98.0-nightly` vs. `4697` in HEAD).

Unless otherwise noted, line numbers throughout **Findings** cite `rust-lang/rust` HEAD (`0259d5e9a81c6af08e40f8c204f2c0c41dca1647`), while live compilation outputs reflect `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) running with `--edition=2021` or `--edition=2024` as recorded per test. Unless gated explicitly with `#![feature(decl_macro)]` or `#![feature(proc_macro_def_site)]`, `Opaque` behavior belongs to nightly/compiler-internal paths whereas `Transparent` and `SemiOpaque` apply on stable Rust across both Edition 2021 and Edition 2024.

## Findings

### 1. SyntaxContext Mark Stacks, Cached Projections, and the Transparency Lattice

Basis: source + execution

In `compiler/rustc_span/src/hygiene.rs`, every AST/HIR identifier's lexical provenance is encoded by `SyntaxContext`, a 29-bit interned handle (`#[max = 0x1FFF_FFFF]` in HEAD `hygiene.rs:52-60`; `pub struct SyntaxContext(u32)` in `1.98.0-nightly` `hygiene.rs:54`) representing a finite linked list—called a "mark stack"—of pairs `(ExpnId, Transparency)`. Crucially, `SyntaxContext` (and `LocalExpnId`) explicitly opts out of comparison traits via negative trait bounds (`impl !Ord for SyntaxContext {}`, `impl !PartialOrd for SyntaxContext {}`, `hygiene.rs:65-66, 135-136`) so incremental compilation queries cannot observe or depend on interning allocation order.

#### 1.1 Internal Representation (`SyntaxContextData`) and Root Invariant

Each interned `SyntaxContext` indexes a `SyntaxContextData` record (`hygiene.rs:72-86`):

```rust
struct SyntaxContextData {
    /// The last macro expansion in the chain.
    /// (Here we say the most deeply nested macro expansion is the "outermost" expansion.)
    outer_expn: ExpnId,
    /// Transparency of the last macro expansion
    outer_transparency: Transparency,
    parent: SyntaxContext,
    /// This context, but with all transparent and semi-opaque expansions filtered away.
    opaque: SyntaxContext,
    /// This context, but with all transparent expansions filtered away.
    opaque_and_semiopaque: SyntaxContext,
    /// Name of the crate to which `$crate` with this context would resolve.
    dollar_crate_name: Symbol,
}
```

Slot `0`, `SyntaxContext::root()` (`hygiene.rs:89-98`), holds `outer_expn: ExpnId::root()`, `outer_transparency: Transparency::Opaque`, `parent: SyntaxContext::root()`, `opaque: SyntaxContext::root()`, `opaque_and_semiopaque: SyntaxContext::root()`, and `dollar_crate_name: kw::DollarCrate`. Giving the sentinel root `outer_transparency: Transparency::Opaque` is a deliberate terminator optimization: normalization stops naturally at root without special-casing empty stacks during parent lookup, and `is_descendant_of` sees root as ancestor of every expansion.

Because `opaque` and `opaque_and_semiopaque` are materialized monotonically inside `alloc_ctxt` (`hygiene.rs:727-760`), the two projection operations used everywhere in `rustc_resolve` and `rustc_middle` reduce to `O(1)` table lookups (`hygiene.rs:599-606`):
- `normalize_to_macros_2_0(ctxt)` returns `self.syntax_context_data[ctxt].opaque` (retaining **only** `Opaque` marks).
- `normalize_to_macro_rules(ctxt)` returns `self.syntax_context_data[ctxt].opaque_and_semiopaque` (retaining **both** `SemiOpaque` and `Opaque` marks).

#### 1.2 Three-Tier `Transparency` Ordering and Macro Defaults

`Transparency` (`hygiene.rs:178-200`) derives `PartialOrd` over three ordered variants (`Transparent < SemiOpaque < Opaque`):

| Variant | Derived Order Rank | `normalize_to_macro_rules()` | `normalize_to_macros_2_0()` | Default Producers |
| :--- | :--- | :--- | :--- | :--- |
| `Transparent` | `0` (least opaque) | Stripped | Stripped | `Span::call_site()` (`rustc_span/src/lib.rs:1300-1302`), opt-in `#[rustc_macro_transparency = "transparent"]` |
| `SemiOpaque` | `1` (mixed-site) | **Retained** | Stripped | `macro_rules!` (`Transparency::fallback(true)`, `hygiene.rs:198`), `Span::mixed_site()` (`lib.rs:1306-1308`), built-in macros (`derive`, `format_args!`, etc.) |
| `Opaque` | `2` (def-site) | **Retained** | **Retained** | Macros 2.0 `macro` (`Transparency::fallback(false)`, `hygiene.rs:198`), unstable `Span::def_site()` (`lib.rs:1294-1296`) |

In `compiler/rustc_expand/src/mbe/macro_rules.rs` (`MacroRulesMacroExpander`, `macro_rules.rs:920-922`), a declarative macro's default expansion transparency is computed by `#[rustc_macro_transparency]` attribute lookup `.unwrap_or(Transparency::fallback(macro_rules))` (`macro_rules = true` for `macro_rules!`, `false` for `macro`).

#### 1.3 `apply_mark` and Cross-Layer Splicing (`HygieneData::apply_mark`)

When macro expansion stamps a span with `(expn_id, transparency)`, `HygieneData::apply_mark` (`hygiene.rs:688-723`) does not unconditionally push `(expn_id, transparency)` on top of `ctxt`. Instead:

1. If `transparency == Transparency::Opaque`, it pushes directly: `alloc_ctxt(ctxt, expn_id, transparency)`.
2. Otherwise (`SemiOpaque` or `Transparent`), it fetches `call_site_ctxt = self.expn_data(expn_id).call_site.ctxt()` and normalizes it according to the inner macro's transparency:
   - for `SemiOpaque`: `normalize_to_macros_2_0(call_site_ctxt)`
   - for `Transparent`: `normalize_to_macro_rules(call_site_ctxt)`
3. If that normalized `call_site_ctxt` is `root()`, it allocates `(ctxt, expn_id, transparency)` directly (`hygiene.rs:706-708`).
4. Otherwise—such as a `macro_rules!` (`SemiOpaque`) invocation occurring *inside* a Macros 2.0 (`Opaque`) macro definition—`apply_mark` **re-bases** all existing marks of `ctxt` on top of the outer `call_site_ctxt`, then pushes `(expn_id, transparency)` on top (`hygiene.rs:719-722`):
   ```text
   Outer call_site:  root ──(eOuter, Opaque)
   Body token ctxt:  []  (plus any prior marks in ctxt)
   Inner apply_mark: root ──(eOuter, Opaque) ── ...[ctxt.marks]... ──(eInner, SemiOpaque)
   ```
   As verified formally by theorem `legacy_inside_macros_2_0_preserves_both_layers` in our Lean development, this splicing guarantees that `normalize_to_macros_2_0` preserves `eOuter` (so the enclosing Macros 2.0 item isolation cannot be punctured by emitting a `macro_rules!` definition inside it), while `normalize_to_macro_rules` preserves both `(eOuter, Opaque)` and `(eInner, SemiOpaque)`.

#### 1.4 MBE Transcription Separation (`Marker::mark_span` vs. `InvisibleOrigin::MetaVar`)

During declarative macro transcription (`compiler/rustc_expand/src/mbe/transcribe.rs`), macro-template tokens and caller-supplied metavariables are handled differently:
- Every literal token tree, group delimiter, `$crate` token, and interpolated `NtIdent`/`NtLifetime` produced from the macro's RHS template passes through `Marker::mark_span` (`transcribe.rs:95-112`, invoked across token emission sites around lines `191, 288-295`), which caches and applies `ctxt.apply_mark(self.expand_id.to_expn_id(), self.transparency)`.
- Captured nonterminal AST/expression fragments (e.g., `$v:expr`) are wrapped inside `Delimiter::Invisible(InvisibleOrigin::MetaVar(mv_kind))` (`transcribe.rs:468-490`) whose inner parsed token trees **do not** receive `(expand_id, transparency)` from `Marker`. Thus, when `hygiene_probe!(x, ...)` substitutes caller identifier `x` (`ctxt = root`) into `let x = 1u32; ... LeakedItem($v)`, the macro's `x` carries `(expn, SemiOpaque)` whereas `$v`'s `x` retains `root`, cleanly printing `OUT=(1,2) ITEM=2` in Group B (`support/probe_results.json`, `edition_2021` & `edition_2024`).

---

### 2. Name Resolution Asymmetry Across Locals, Labels, Items, Parameters, Fields, Methods, and `$crate`

Basis: source + execution

A widespread conceptual pitfall is treating `macro_rules!` (`SemiOpaque`) as simply "local variables hygienic, everything else unhygienic." In `rustc`, that behavior emerges mechanically from **which normalization helper each resolver or type-checker call site invokes** on an identifier's `SyntaxContext`:

| Syntactic / Semantic Role | Compiler Entry Point (`rust-lang/rust` HEAD) | Context Normalization Applied | `Transparent` (`call_site`) | `SemiOpaque` (`macro_rules!`, `mixed_site`) | `Opaque` (`macro` 2.0, `def_site`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| Local `let` / pattern bindings | `LateResolutionVisitor::fresh_binding` (`rustc_resolve/src/late.rs:4697`) | `ident.normalize_to_macro_rules()` | Stripped (unhygienic capture/leak) | **Preserved** (isolated per expansion) | **Preserved** (isolated per expansion) |
| Value-NS local lookup (non-param ribs) | `resolve_ident_in_lexical_scope` (`rustc_resolve/src/ident.rs:328-338`) | `ident.span.normalize_to_macro_rules()` when `ns != TypeNS && !rib.kind.contains_params()` | Stripped | **Preserved** (macro locals isolate from caller) | **Preserved** (macro locals isolate from caller) |
| Loop & block labels (`'blk`) | `resolve_label` (`late.rs:2887`), `with_resolved_label` (`late.rs:5389`) | `label.normalize_to_macro_rules()` | Stripped | **Preserved** (`E0426` across macro boundary) | **Preserved** (`E0426` across macro boundary) |
| Delegation `self` keyword | `late.rs:4272` (`kw::SelfLower`) | `body.span.normalize_to_macro_rules()` | Stripped | **Preserved** | **Preserved** |
| `$crate` crate-root resolution | `Resolver::resolve_crate_root` (`rustc_resolve/src/lib.rs:2375-2424`) | `normalize_to_macro_rules()` + reverse `(Opaque*, SemiOpaque+)` scan | No `$crate` expansion def scope | **Resolves to defining crate** (immune to shadowing) | **Resolves to defining crate** |
| `TypeNS` & generic/const params | `resolve_ident_in_lexical_scope` (`ident.rs:324-326, 338`), `late.rs:1943, 3319, 3434` | `normalize_to_macros_2_0()` | Stripped | Stripped (sees caller types & type params) | **Preserved** |
| Module items, imports, `BindingKey` | `IdentKey::new` (`lib.rs:619-620`, `3133`), `build_reduced_graph.rs:76, 384, 1065, 1340` | `Macros20NormalizedSyntaxContext::new` (`normalize_to_macros_2_0()`) | Stripped | Stripped (**leaks** `struct`/`fn` to caller!) | **Preserved** (caller lookup fails `E0425`) |
| `self` (`SelfUpper` type alias) | `ident.rs:320-323` | Explicit `.with_ctxt(SyntaxContext::root())` (`FIXME`) | Stripped to root | Stripped to root | Stripped to root |
| Struct/enum ADT fields & `offset_of` | `FnCtxt::find_adt_field` (`rustc_hir_typeck/src/expr.rs:1877, 2292, 2838, 2864`) | `normalize_to_macros_2_0()` + `adjust_ident_and_get_scope` | Stripped | Stripped (can access caller private/tuple fields) | **Preserved** (field identity/privacy checked at def-site) |
| Inherent & trait method lookup | `AssocItems::find_by_ident_and_namespace` (`rustc_middle/src/ty/assoc.rs:331, 345`) | `tcx.hygienic_eq` (`hygiene.rs:1019-1025`) -> `normalize_to_macros_2_0()` + `adjust` | Stripped (`adjust = None`) | Stripped (`adjust = None`, caller `mod_id`!) | **Preserved** (`adjust = Some(expn)` -> def-site privacy!) |

#### 2.1 Method & Item Privacy Asymmetry: Why `SemiOpaque` Accesses Private Caller Methods While `Opaque` Raises `E0624`

Method candidate probing in `rustc_hir_typeck/src/method/probe.rs:882` computes the privacy-checking module `def_scope` via `TyCtxt::adjust_ident_and_get_scope` (`compiler/rustc_middle/src/ty/mod.rs:2344-2356`):

```rust
pub fn adjust_ident_and_get_scope(
    self,
    mut ident: Ident,
    scope: DefId,
    mod_id: LocalModId,
) -> (Ident, ModId) {
    let scope = ident
        .span
        .normalize_to_macros_2_0_and_adjust(self.expn_that_defined(scope))
        .and_then(|actual_expansion| actual_expansion.expn_data().parent_module)
        .unwrap_or(mod_id.to_mod_id());
    (ident, scope)
}
```

And `SyntaxContext::hygienic_eq` (`hygiene.rs:1019-1025`) likewise normalizes **both** `self` and `other` with `normalize_to_macros_2_0_and_adjust(expn_id)` before equality testing. The order of operations inside `normalize_to_macros_2_0_and_adjust` (`hygiene.rs:938-941`) is decisive:

1. **First**, it collapses `*self = data.normalize_to_macros_2_0(*self)`.
2. **Second**, it calls `adjust(expn_id)` (`hygiene.rs:680-686`), which pops marks until `!is_descendant_of(expn_id, outer_expn(*ctxt))` stops, returning `Option<ExpnId>`—namely `None` if no mark had to be stripped after step 1, or `Some(outermost_popped_expn)` otherwise.

Tracing both cases directly explains our empirical Group B, C, and D probe outputs:
- **Under `SemiOpaque` (`macro_rules!` or `Span::mixed_site()`):** Step 1 erases the `SemiOpaque` mark *before* `adjust` runs, reducing `ident.ctxt` to `SyntaxContext::root()`. Because `ExpnId::root()` satisfies `is_descendant_of(expn_id, ExpnId::root())`, the `while` loop in `adjust` runs zero iterations and returns `None`. `adjust_ident_and_get_scope` falls back via `.unwrap_or(mod_id.to_mod_id())` to the **caller's module `mod_id`**. Consequently, calling a caller-private inherent method `h.get_val()` from `macro_rules! call_method_on!(h)` succeeds (`METH=15`, Group B), and calling it from `hygiene_pm::call_method_mixed_site!(h)` succeeds (`MS_METH=15`, Group C).
- **Under `Opaque` (`macro` 2.0 or `Span::def_site()`):** Step 1 retains the `Opaque` mark `(expn_macro, Opaque)`. Unless the target type itself was defined inside that same expansion (or a descendant expansion), `!is_descendant_of(type_def_expn, expn_macro)` triggers `remove_mark`, so `adjust` returns `Some(expn_macro)`! `.and_then(|e| e.expn_data().parent_module)` then overrides `def_scope` to the **macro definition's parent module** (`hygiene_pm` crate or `mod defs`). When the method on the caller's struct (`Holder::get_val` or `caller_priv::CallerHolder::priv_val`) is private to the caller module, typeck rejects the call with **`error[E0624]: method ... is private`** (`negative_def_site_method_isolated` in Group C; `macros_2_0_opaque_method_privacy_at_def_site` in Group D). Conversely, marking the caller's method `pub` makes it visible from the macro's definition module, so `DS_PUB_METH=15` and `DECL2_PUB_METH=19` compile and succeed cleanly!

Notice a subtle trap caught during Group D probe construction: if a private method is placed directly in the **parent** module of `mod defs` (rather than a sibling `mod caller_priv`), Rust's child-sees-parent visibility rule permits `mod defs` to see private items in its ancestor module, so `E0624` only triggers when the caller's module is not an ancestor of (nor identical to) the macro's definition module.

#### 2.2 `$crate` Reverse Mark-Stack Scan (`Resolver::resolve_crate_root`)

When `rustc_resolve` encounters leading path segment `$crate` (`kw::DollarCrate`), `Resolver::resolve_crate_root` (`compiler/rustc_resolve/src/lib.rs:2375-2446`) runs a specialized algorithm distinct from both `normalize_to_macros_2_0()` and plain `IdentKey` lookup:

```rust
ctxt = ctxt.normalize_to_macro_rules();
let mut iter = ctxt.marks().into_iter().rev().peekable();
let mut result = None;
// Find the last opaque mark from the end if it exists.
while let Some(&(mark, transparency)) = iter.peek() {
    if transparency == Transparency::Opaque {
        result = Some(mark);
        iter.next();
    } else {
        break;
    }
}
// Then find the last semi-opaque mark from the end if it exists.
for (mark, transparency) in iter {
    if transparency == Transparency::SemiOpaque {
        result = Some(mark);
    } else {
        break;
    }
}
```

Understanding the order of `ctxt.marks()` is critical here (`hygiene.rs` parent-to-outer walk): `ctxt.marks()` yields marks in **innermost-to-outermost expansion-history order** (`parent -> child`), so `.rev()` reverses them to iterate from **most deeply nested (outermost AST expansion) down toward root**:
1. Suppose a `macro` 2.0 invocation sits inside a `macro_rules!` helper, OR vice versa (`apply_mark` splices `eOuter` (`Opaque`) *underneath* `eInner` (`SemiOpaque`), giving stack `[eOuter (Opaque), eInner (SemiOpaque)]` from root up).
2. `iter` (via `.rev()`) sees `[(eInner, SemiOpaque), (eOuter, Opaque)]` from outermost down toward root.
3. The initial `while` loop peeks `(eInner, SemiOpaque)` (`!= Opaque`), so it breaks immediately.
4. The subsequent `for` loop iterates over contiguous `SemiOpaque` marks, updating `result = Some(eInner)`, then stops at `(eOuter, Opaque)` (`!= SemiOpaque`).
5. Result is **`Some(eInner)`**—meaning `$crate` inside the nested `macro_rules!` macro resolves to the `macro_rules!` macro's defining crate (`eInner`), **not** the enclosing `macro` 2.0 crate `eOuter`! (Notice a source comment at `lib.rs:2379-2385` warns this heuristic is a "guess" that can fail if a `macro_rules!` *definition* itself is generated by a `macro` 2.0 macro.)
6. On the inverse nesting (`push (push root eSemi SemiOpaque) eOpq Opaque`), `.rev()` sees `[(eOpq, Opaque), (eSemi, SemiOpaque)]`, skips `eOpq` in the `while` loop, and advances `result` to `Some(eSemi)`.
7. Finally, `self.expn_def_scope(mark)` extracts the `CrateNum` of the crate that defined the macro, ignoring any caller module or extern-crate alias shadowing it (`mod dep_hygiene { ... }`, `fn helper() -> u32 { 999 }`). Yet visibility checking still runs against the caller's invocation module (`negative_dollar_crate_respects_visibility` fails with `error[E0603]: function 'priv_fn' is private`).

---

### 3. Procedural Macro Spans and Rust Reference Discrepancy

Basis: documentation + source + execution

In `compiler/rustc_expand/src/proc_macro_server.rs:467-499`, right before invoking a procedural macro, `Rustc::new` constructs three `Span` values in `ExpnGlobals`:

```rust
Rustc {
    def_site: ecx.with_def_site_ctxt(expn_data.def_site),
    call_site: ecx.with_call_site_ctxt(expn_data.call_site),
    mixed_site: ecx.with_mixed_site_ctxt(expn_data.call_site),
    ...
}
```

And in `compiler/rustc_span/src/lib.rs:1292-1315`, each helper applies one mark directly onto `SyntaxContext::root()` (`SyntaxContext::root().apply_mark(expn_id, transparency)`):
- `with_call_site_ctxt` -> `Transparency::Transparent` (`proc_macro::Span::call_site()`, stable since Rust `1.29.0`, `library/proc_macro/src/lib.rs:645-648`).
- `with_mixed_site_ctxt` -> `Transparency::SemiOpaque` (`proc_macro::Span::mixed_site()`, stable since Rust `1.45.0`, `library/proc_macro/src/lib.rs:654-657`).
- `with_def_site_ctxt` -> `Transparency::Opaque` (`proc_macro::Span::def_site()`, unstable behind `#![feature(proc_macro_def_site)]` tracking issue `#54724`, `library/proc_macro/src/lib.rs:636-639`).

Additionally, `proc_macro::Span` stabilizes two hygiene-combining constructors since Rust `1.45.0` (`library/proc_macro/src/lib.rs:737-747`):
- `span.resolved_at(other)`: retains source location (`lo`/`hi`) of `self` for diagnostics while replacing its `SyntaxContext` with `other`'s.
- `span.located_at(other)`: dual helper `other.resolved_at(*self)`—retaining `self`'s `SyntaxContext` for name resolution while pointing diagnostics at `other`'s source span.

**Primary-source discrepancy with `rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`):**
`src/procedural-macros.md:45-49` states flatly: *"Procedural macros are unhygienic. This means they behave as if the output token stream was simply written inline to the code it's next to."* While accurate for `Span::call_site()` (the default for raw string `.parse()` and `quote!` without custom spans), it omits stable `Span::mixed_site()` and `resolved_at`/`located_at` (available since Rust 1.45.0), which reproduce exact `macro_rules!` `SemiOpaque` behavior inside stable proc macros—as empirically confirmed in Group C (`CS=42 CS_DEF=77 MS=10 MS_RES_AT=19 MS_ITEM=55 MS_METH=15 DS_INTERNAL=88 CALLER_X=42`, while `read_x_mixed_site!()` and `define_z_mixed_site!()` fail with `E0425` and `def_site_method_probe!(h)` fails with `E0624` on private `Holder::get_val`).

**Compiler `FIXME` on `quote!` cross-crate span recovery (`proc_macro_server.rs:862-869`):** When `proc_macro` recovers saved `Span`s serialized inside macro crate metadata (`span_recover_proc_macro_span`), `rustc` explicitly notes: `// FIXME: SyntaxContext for spans from proc macro crates is lost during encoding, replace it with a def-site context until we are encoding it properly.` (`resolver.get_proc_macro_quoted_span(krate, id).with_ctxt(def_site.ctxt())`).

---

### 4. Edition 2024 `:expr` vs. `:expr_2021` Fragment Specifier Grammar

Basis: normative + source + execution

In Rust Edition 2024, `const { ... }` inline const blocks and `_` wildcard LHS assignment targets became valid expressions accepted by top-level `$e:expr` macro matchers. To prevent silently breaking existing crates written under earlier macro grammars (for example, macros having one arm `($e:expr) => ...` and another arm `(_) => ...` or `(const $k:ident) => ...`), `rustc` splits `MetaVarKind::Expr` / `NonterminalKind::Expr` (`compiler/rustc_ast/src/token.rs:1136-1192`):

```rust
pub enum NtExprKind {
    // Matches expressions using the post-edition 2024. Was written using
    // `expr` in edition 2024 or later.
    Expr,
    // Matches expressions using the pre-edition 2024 rules.
    // - `inferred`: was written using `expr` in edition 2021 or earlier.
    // - `!inferred`: was written using `expr_2021`.
    Expr2021 { inferred: bool },
}
```

#### 4.1 Definition-Site Edition Binding (`mbe::quoted`)

`compiler/rustc_expand/src/mbe/quoted.rs:165` parses each fragment specifier `$x:kind` in a macro's *matcher* using `NonterminalKind::from_symbol(fragment.name, edition)` where `edition` is evaluated lazily from the **macro definition span's edition** (`token.rs:1167-1192`):
- `sym::expr`: evaluates `if edition().at_least_rust_2024() { Expr } else { Expr2021 { inferred: true } }`.
- `sym::expr_2021`: always evaluates to `Expr2021 { inferred: false }` regardless of edition (and mirrors how `sym::pat` splits at `at_least_rust_2021()` between `PatWithOr` and `PatParam { inferred: true }` alongside explicit `sym::pat_param`).

Consequently, grammar admission depends **exclusively** on the edition of the crate/span that *defined* the `macro_rules!`, never on the caller's edition:
- Group A `cross_edition_def2021_call2024` (macro defined in Edition 2021 with `$e:expr`, invoked from Edition 2024): fails compilation (`rc=1`) on both `const { 1 + 2 }` and `_`.
- Group A `cross_edition_def2024_call2021` (macro defined in Edition 2024 with `$e:expr`, invoked from Edition 2021): compiles and prints `X21=3` (`rc=0`), accepting both `m2024!(const { 1 + 2 })` and `m2024!(_) = 99`.

#### 4.2 Token-Start Gate (`nonterminal_may_begin_with`) and Why `(const { ... })` Works Everywhere

`Parser::nonterminal_may_begin_with` (`compiler/rustc_parse/src/parser/nonterminal.rs:43-64`) decides first-token admission at macro-matching dispatch:

| Variant | Exact Rust Predicate (`nonterminal.rs:45-64`) | `const { ... }` | `(_)` / `(const { ... })` | Bare `_` | `let _ = 1` |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `Expr2021 { .. }` | `token.can_begin_expr() && !token.is_keyword(kw::Let) && !token.is_keyword(kw::Const)` | Rejected (`no rules expected keyword const`) | **Admitted** (`A_PAREN=3`; starts with `OpenParen`) | Rejected (`no rules expected reserved identifier _`) | Rejected |
| `Expr` (Edition 2024) | `(token.can_begin_expr() \|\| token.is_keyword(kw::Underscore)) && !token.is_keyword(kw::Let)` | **Admitted** (`A=3`) | **Admitted** | **Admitted** (`_ = 99;`) | Rejected (`no rules expected keyword let`) |

Two subtle token facts in `compiler/rustc_ast/src/token.rs:312-349` explain why this asymmetry is coded that way:
1. `ident_can_begin_expr` already returns `true` for **both** `kw::Const` and `kw::Let`, because `const` and `let` can begin expression constructs in other parser contexts; therefore `Expr2021` explicitly subtracts `&& !token.is_keyword(kw::Const)` and both editions subtract `&& !token.is_keyword(kw::Let)`.
2. `ident_can_begin_expr` checks `!ident_token.is_reserved_ident() || ...`, and `kw::Underscore` (`_`) is a reserved identifier omitted from the explicit allowlist array (`token.rs:322-348`). Thus `token.can_begin_expr()` is `false` for `_`, so `Expr` must explicitly OR `token.is_keyword(kw::Underscore)` right inside `nonterminal_may_begin_with` (see the compiler comment at `nonterminal.rs:58-60`: *"Because `can_begin_expr` is used elsewhere, we need to reduce the scope of where the `_` is considered an expression to just macro parsing code."*).

Meanwhile, `is_in_follow` (`compiler/rustc_expand/src/mbe/macro_rules.rs:1729-1759`) matches `NonterminalKind::Stmt | NonterminalKind::Expr(_)`, ignoring the `NtExprKind` payload completely. Both Edition 2021 `Expr2021` and Edition 2024 `Expr` therefore enforce the identical follow set `FOLLOW(expr) = { =>, ,, ;, CloseDelim }`. Because neither `kw::Const` nor `kw::Underscore` appears in `FOLLOW(expr)`, widening Edition 2024 `$e:expr` introduces zero follow-set ambiguity (`FIRST(Expr2024) ∩ FOLLOW(expr) = ∅`).

---

### 5. Anneal TCB Boundary & Kernel-Checked Lean v4.34.1 Mechanization

Basis: source + derived + execution

#### 5.1 Position of Macro Expansion Relative to Anneal's TCB (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`)

Inspection of `joshlf/anneal` shows a sharp architectural split between Rust-compile-time expansion and Lean kernel checking:
1. **Post-expansion MIR capture:** `anneal-rustc-capture` hooks into `rustc_driver::Callbacks::after_analysis` (`trusted/rustc-capture/src/driver.rs:27, 75-84`), capturing expanded and resolved MIR (`MirAst.lean`) after MBE transcription, proc-macro execution, `rustc_resolve`, and type checking have completed. Neither `macro_rules!`, procedural macros, nor Edition 2024 fragment parsing execute inside the captured MIR model.
2. **Host build-time TCB exclusion (`THREAT_MODEL.md:137-146, 176` & `trusted/audit/src/lib.rs:21-25, 1251`):** `THREAT_MODEL.md` explicitly warns that arbitrary Cargo `build.rs` scripts, procedural macros, compiler plugins, and Lean elaborator I/O run with host code-execution authority unless sandboxed at the OS level, because proc macros execute *during* `rustc` before `after_analysis` capture; `check_cargo_boundary` keeps the trusted workspace DAG localized under `trusted/`.
3. **Strict Lean 4 kernel purity (`Trusted/MirAst.lean:165`, `Trusted/MirSemantics.lean:178`, `trusted/audit/TrustedBoundary.lean:92-93, 1605-1663, 2164`):** `TrustedBoundary.lean` enforces that proof modules contain zero `sorryAx`, zero `Lean.ofReduceBool` / `Lean.ofReduceNat` / `Lean.trustCompiler` (`native_decide`), zero `unsafe` or quotient/axiom bypasses, and zero Lean elaborator macros inside verified obligations, while `MirSemantics.lean` mandates `noncomputable def` on definitions so Lean does not synthesize partial/unsafe codegen `._unsafe_rec` auxiliaries that fail `Kernel.Environment.replay`.

#### 5.2 Formalization Architecture (`support/MacroHygieneSyntaxContextAndEditionFragSoundness.lean`)

Following those exact purity constraints, `support/MacroHygieneSyntaxContextAndEditionFragSoundness.lean` (1,556 lines, 66,312 bytes) models `rustc`'s hygiene and fragment rules cleanly inside `namespace RustcMacroHygiene` using strictly structural `noncomputable def` and `match` (zero `partial def`, zero `let rec`, zero `deriving`, zero `sorry`, zero `omega`/`bv_decide`/`native_decide`, zero `Classical.choice`, zero `._unsafe_rec`). Kernel compilation under Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` succeeds with exit code `0`, zero warnings, `81` surface theorems, `74` `noncomputable def`s, `19` inductive/structure types (`1,005` total kernel constants in `map₂`), and transitive axiom footprint strictly `[propext]`.

The table below catalogs the key theorems and what each proves:

| Pillar | Key Mechanized Theorems (`RustcMacroHygiene`) | Mechanized Guarantee |
| :--- | :--- | :--- |
| Lattice & `SyntaxContext` | `transparency_le_refl`, `transparency_le_antisym`, `transparency_le_trans`, `transparency_fallback_macro_rules`, `transparency_fallback_decl_macro` | `(Transparency, le, join, meet)` forms a partial order / lattice with `fallback true = .semiOpaque` and `fallback false = .opaq`. |
| Projection Idempotence & Isolation | `normalizeToMacros20_idempotent`, `normalizeToMacroRules_idempotent`, `normalizeToMacros20_erases_semiOpaque`, `normalizeToMacroRules_preserves_semiOpaque`, `normalizeToMacros20_preserves_opaque`, `semiOpaque_marks_distinct_invocations`, `opaque_marks_distinct_invocations`, `normalizeToMacros20_depth_le`, `normalizeToMacroRules_depth_le` | Both normalizations are idempotent and depth-non-increasing; `normalizeToMacros20` erases `SemiOpaque` while preserving `Opaque`; distinct expansion IDs remain distinct under the appropriate normalizations. |
| Local Alpha-Invariance (Non-Capture) | `lookupLocal_bind_macro_noncapture`, `lookupLocal_bind_caller_noncapture`, `agreesOnRoot_bind_macro`, `evalLocalExpr_agreesOnRoot`, `caller_eval_invariant_under_macro_local`, `agreesOnCtxt_bind_caller`, `lookupLocal_bind_different_semiOpaque_invocations` | Evaluating any caller expression (`eCaller.allRootCtxt = true`) in a `RibEnv` extended with any macro-introduced `SemiOpaque` or `Opaque` binding produces the exact same `Option Val` as the original caller environment; dual theorem preserves macro-introduced bindings against caller bindings; distinct macro invocations never collide. |
| Three-Tier Separation & Method Privacy | `sep_transparent_captures_caller_semiOpaque_isolates`, `sep_semiOpaque_leaks_item_opaque_isolates`, `sep_semiOpaque_vs_opaque_method_privacy`, `hygienicEq_transparent_erasable`, `hygienicEq_semiOpaque_erasable`, `adjust_opaque_at_non_descendant_strips_mark`, `adjust_after_norm20_semiOpaque_returns_none` | Constructive witnesses proving (1) `Transparent` (`call_site`) captures caller locals while `SemiOpaque` (`mixed_site`/`macro_rules!`) isolates them, (2) `SemiOpaque` leaks items (`IdentKey` collision with `root`) while `Opaque` (`def_site`/`macro` 2.0) isolates them, and (3) `adjust_after_norm20_semiOpaque_returns_none` falls back to caller `mod_id` whereas `adjust_opaque_at_non_descendant_strips_mark` returns `some e` (`parent_module` privacy check). |
| `$crate` Resolution & Visibility | `resolveDollarCrateMark_semiOpaque`, `resolveDollarCrateMark_transparent_ignored`, `resolveDollarCrateMark_opaque_alone`, `resolveCrateRoot_bypasses_caller_shadow`, `resolveCrateRoot_transparent_wrapper_invariant`, `dollarCrate_resolves_crate_but_respects_visibility` | Exact model of `Resolver::resolve_crate_root`: ignores `Transparent` wrappers, resolves to defining crate bypassing caller module shadowing (`CrateId 1 ≠ 0`), while `checkVisibility` still rejects private `ModId` targets (`visOk = false`). |
| Edition 2024 `:expr` vs `:expr_2021` | `expr2021_tok_subset_expr2024`, `expr2021_subset_expr2024`, `expr2021_strict_sublanguage_witnesses`, `definition_site_edition_determines_expr_kind`, `expr_follow_set_invariant`, `expr2024_first_follow_disjoint`, `expr2024_start_not_in_follow`, `paren_constBlock_admitted_in_2021`, `pat_edition_leading_pipe_separation`, `pat_edition_2021_boundary` | Total inclusion `∀ e, acceptsExprFragment (.expr2021 b) e = true → acceptsExprFragment .expr2024 e = true`; strict separation on `const { ... }` and `_`; `(const { ... })` accepted in `expr2021`; identical `FOLLOW(expr)` with empty intersection `FIRST(expr2024) ∩ FOLLOW(expr) = ∅`. |
| Full Pipeline & Nested Macros | `mbe_transcription_preserves_caller_metavar_hygiene`, `proc_macro_mixed_or_def_site_noncapture`, `legacy_inside_macros_2_0_preserves_both_layers`, `dollarCrate_skips_outer_opaque_to_semiOpaque`, `scanDollarCrate_single_semi`, `scanDollarCrate_opaq_then_semi`, `rustc_macro_hygiene_and_edition2024_soundness_summary` | Connects `Marker.mark_span` transcription (`applyMark`) cleanly to non-capture of caller metavariable expressions, models nested `macro_rules!`-inside-`macro` splicing (`resolveDollarCrateMark c = some eInner`), and establishes equivalence between reverse list scan `scanDollarCrateMarksRev` and structural `resolveDollarCrateMark`. |

## Boundaries

To prevent unwarranted extrapolation, this report distinguishes explicitly among four negative-space categories:

1. **Known not to apply:**
   - *Caller-local capture inside `macro_rules!` across functions or unrelated expansions:* Although `rust-lang/reference` (`src/macros-by-example.md:600-603`) shows `check!()` reading `let x = 1` declared earlier in the *same* enclosing lexical function body where `macro_rules! check` itself was defined (sharing the same `DefId` rib chain), cross-function or cross-module `macro_rules!` invocations cannot access caller `let` bindings (`negative_macro_rules_cannot_capture_caller_local` fails with `E0425`) and cannot leak `let` bindings out to caller statements (`negative_macro_rules_local_does_not_leak` fails with `E0425`).
   - *"Procedural macros are unhygienic" (`rust-lang/reference`, `src/procedural-macros.md:47`):* Known not to apply universally whenever a procedural macro constructs output spans via `Span::mixed_site()` (stable since Rust `1.45.0`), `Span::resolved_at`/`located_at`, or `#![feature(proc_macro_def_site)]` `Span::def_site()`, as proved by Group C live executions (`E0425`, `E0624`).
   - *Edition-of-caller determination for `:expr`:* Edition 2024's widened `Expr` matcher does **not** apply to Edition <= 2021 macros merely because the caller crate uses Edition 2024 (`cross_edition_def2021_call2024` fails with errors on `const` and `_`), and explicit `:expr_2021` never widens in Edition 2024 (`edition_2024_expr_2021_const_block` and `edition_2024_expr_2021_underscore` both fail). Conversely, parenthesized `(const { 1 + 2 })` is known to compile in Edition 2021 (`A_PAREN=3`) because `Token::OpenParen` satisfies `can_begin_expr()`.
   - *Visibility bypass via `$crate`:* `$crate` resolves crate root only; it is known **not** to grant private item access (`negative_dollar_crate_respects_visibility` fails with `E0603`). Similarly, `macro_rules!` / `Span::mixed_site()` cannot access private *inherent* methods of types outside the caller's visibility when caller itself lacks visibility—it checks privacy at caller `mod_id`, whereas `Opaque` (`macro` 2.0 / `Span::def_site()`) checks privacy at macro definition `parent_module`.
   - *Equivalence across parent/sibling modules for `E0624`:* Putting a `CallerHolder` struct in a module that is an *ancestor* of the Macros 2.0 module `defs` allows `defs` to see private methods via standard Rust ancestor visibility; `E0624` specifically requires the caller's module not to grant access to the macro definition module.

2. **Unsupported:**
   - Stable Rust (`--edition=2021` or `--edition=2024` without nightly `#![feature(...)]`) does not support `Transparency::Opaque` macros (`#![feature(decl_macro)]`), `proc_macro::Span::def_site()` (`#![feature(proc_macro_def_site)]`), or `#[rustc_macro_transparency]` (`#![feature(rustc_attrs)]`).
   - Cross-crate preservation of arbitrary `SyntaxContext` inside `quote!`-like `Span::save_span` / `span_recover_proc_macro_span` is explicitly unsupported in upstream `rustc` HEAD (`proc_macro_server.rs:865-867` replaces recovered span context with `def_site.ctxt()`).

3. **Not examined:**
   - Attribute (`#[proc_macro_attribute]`) and derive (`#[proc_macro_derive]`) procedural macros, including helper-attribute registration and `#[cfg]`/`#[derive]` built-in expander interactions.
   - Cross-crate incremental serialization (`ExpnHash`, `.rmeta` encoding/decoding of `SyntaxContext` tables) and proc-macro token span sub-slicing (`Span::subspan`, `Span::join`) beyond `resolved_at`/`mixed_site`/`def_site`/`call_site`.
   - Complex nested-macro edge cases warned about in `rustc_resolve/src/lib.rs:2382-2384` (specifically `macro_rules!` *definitions* dynamically generated by `macro` 2.0 definitions or `macro` 2.0 definitions emitted inside `macro_rules!`, which the compiler comment flags as unstable and heuristic).
   - Live `rustc` executions under `--edition=2015` or `--edition=2018` (only upstream `Edition::at_least_rust_2021()` / `at_least_rust_2024()` source branches were inspected for pre-2021 editions; live executions covered Editions `2021` and `2024`).
   - Machine-checked bidirectional equivalence (simulation proof in Coq/Lean connecting the full Rust `rustc` codebase directly to the Lean AST model); `MacroHygieneSyntaxContextAndEditionFragSoundness.lean` formalizes a clean extracted semantic model tied line-for-line to inspected `rustc` source functions rather than verifying LLVM/MIR execution of `rustc` itself.

4. **Unknown:**
   - Whether future stabilization of `decl_macro` (Macros 2.0) or proc-macro span serialization (`#54724` / `proc_macro_server.rs:865`) will change the cross-crate `save_span` replacement or refine `resolve_crate_root`'s `macro_rules!`-inside-`macro` heuristic (`lib.rs:2382`).

## Evidence

### Upstream Primary-Source Audit (`rust-lang/rust`, `rust-lang/reference`, `joshlf/anneal`)

All commit SHAs below were resolved live against upstream repositories, and the exact source regions were read directly:

1. **`rust-lang/rust` HEAD (`0259d5e9a81c6af08e40f8c204f2c0c41dca1647`, `src/version`: `1.102.0`, 2026-11-23) & Executed Toolchain (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `1.98.0-nightly`, 2026-05-31):**
   - `compiler/rustc_span/src/hygiene.rs`: `SyntaxContext` (`#[max = 0x1FFF_FFFF]`, `!Ord`, `!PartialOrd`, lines `52-66` HEAD / `54` local); `SyntaxContextData` and `SyntaxContextData::root()` (lines `72-103` HEAD / `67` local); `Transparency` and `Transparency::fallback` (lines `178-200` HEAD / `167-186` local); `normalize_to_macros_2_0` and `normalize_to_macro_rules` (lines `599-606` HEAD); `adjust` (lines `680-686` HEAD); `apply_mark` and `alloc_ctxt` (lines `688-760` HEAD / `519` local); `normalize_to_macros_2_0_and_adjust` and `hygienic_eq` (lines `938-941, 1019-1025` HEAD).
   - `compiler/rustc_span/src/lib.rs`: `Span::{with_def_site_ctxt, with_call_site_ctxt, with_mixed_site_ctxt, with_ctxt_from_mark}` (lines `1292-1315` HEAD).
   - `compiler/rustc_expand/src/mbe/macro_rules.rs`: `MacroRulesMacroExpander` transparency (`Transparency::fallback(macro_rules)`, line `921` HEAD); `is_in_follow` for `NonterminalKind::Stmt | NonterminalKind::Expr(_)` (lines `1729-1759` HEAD).
   - `compiler/rustc_expand/src/mbe/transcribe.rs`: `Marker::mark_span` (`apply_mark` caching, lines `95-112` HEAD) and `Delimiter::Invisible(InvisibleOrigin::MetaVar(_))` metavar group preservation (lines `468-490` HEAD).
   - `compiler/rustc_expand/src/mbe/quoted.rs`: definition-site `edition` closure passed to `NonterminalKind::from_symbol(fragment.name, edition)` (lines `67, 78, 165` HEAD).
   - `compiler/rustc_ast/src/token.rs`: `ident_can_begin_expr` including `kw::Const`/`kw::Let` and excluding reserved `kw::Underscore` (lines `312-349` HEAD); `NtExprKind::{Expr, Expr2021}` and `NonterminalKind::from_symbol` (lines `1136-1192` HEAD).
   - `compiler/rustc_parse/src/parser/nonterminal.rs`: `Parser::nonterminal_may_begin_with` (`Expr2021` vs. Edition 2024 `Expr`, lines `22-64` HEAD / `21-63` local).
   - `compiler/rustc_expand/src/proc_macro_server.rs`: `Rustc::new` populating `def_site`, `call_site`, `mixed_site` and `ExpnGlobals` (lines `457-499` HEAD); `span_recover_proc_macro_span` cross-crate `def_site.ctxt()` replacement `FIXME` (lines `862-869` HEAD).
   - `library/proc_macro/src/lib.rs`: `Span::{def_site, call_site, mixed_site}` (lines `636-657` HEAD) and `Span::{resolved_at, located_at}` (lines `737-747` HEAD).
   - `compiler/rustc_resolve/src/lib.rs`: `IdentKey`, `BindingKey`, and `Macros20NormalizedSyntaxContext` (lines `611-660, 3127-3170` HEAD); `Resolver::resolve_crate_root` reverse mark scan (lines `2375-2446` HEAD / `2312-2383` local).
   - `compiler/rustc_resolve/src/ident.rs`: `resolve_ident_in_lexical_scope` choosing `normalize_to_macros_2_0()` for `TypeNS` / `rib.kind.contains_params()` vs. `normalize_to_macro_rules()` for locals, and `SelfUpper` root override (lines `309-340` HEAD).
   - `compiler/rustc_resolve/src/late.rs`: `fresh_binding` (`ident.normalize_to_macro_rules()`, line `4697` HEAD / `4336` local); `resolve_label` / `with_resolved_label` (`normalize_to_macro_rules()`, lines `2873-2890, 5378-5395` HEAD); delegation `SelfLower` (`line 4272` HEAD).
   - `compiler/rustc_resolve/src/build_reduced_graph.rs`: module item/binding registration via `IdentKey::new` (`lines 76, 384, 1065, 1340` HEAD).
   - `compiler/rustc_middle/src/ty/mod.rs` & `assoc.rs`: `TyCtxt::adjust_ident_and_get_scope` (`mod.rs:2344-2356` HEAD); `AssocItems::find_by_ident_and_namespace` calling `tcx.hygienic_eq` (`assoc.rs:331, 336-346` HEAD).
   - `compiler/rustc_hir_typeck/src/{expr.rs, method/probe.rs}`: `MethodProbe` privacy scope via `adjust_ident_and_get_scope` (`probe.rs:882` HEAD); ADT field lookup and `offset_of` field matching via `normalize_to_macros_2_0()` (`expr.rs:1877, 2281-2295, 2838, 2864` HEAD).

2. **`rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, 2026-11-17):**
   - `src/macros-by-example.md`: `expr_2021` specification (`lines 32, 111, 143`), `r[macro.decl.hygiene.intro]` mixed-site hygiene summary (`lines 587-611`), `r[macro.decl.hygiene.crate]` `$crate` and visibility rules (`lines 629-675`).
   - `src/procedural-macros.md`: `r[macro.proc.hygiene]` "Procedural macros are *unhygienic*" prose (`lines 44-50`, omitting stable `mixed_site`/`resolved_at`).

3. **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`, 2026-11-19):**
   - `trusted/rustc-capture/src/driver.rs`: `AnalysisCallbacks::after_analysis` post-expansion capture (`lines 27, 75-84`).
   - `THREAT_MODEL.md`: build-script / procedural-macro / Lean I/O TCB exclusion (`lines 137-146, 176`).
   - `trusted/audit/src/lib.rs`: `check_cargo_boundary` DAG containment (`lines 21-25, 1251`).
   - `trusted/lean/Trusted/{MirAst.lean, MirSemantics.lean}` & `trusted/audit/TrustedBoundary.lean`: mandatory `noncomputable def` preventing `._unsafe_rec` replay failures (`MirAst.lean:165`, `MirSemantics.lean:178`, `TrustedBoundary.lean:2164`), zero `sorryAx` / `Lean.ofReduceBool` / `Lean.ofReduceNat` / `Lean.trustCompiler` (`TrustedBoundary.lean:92-93, 1605-1663`).

### Empirical Compiler Probe Results (`support/probe_macro_hygiene_and_edition2024_expr_frag.py`, `support/probe_results.json`)

Executed locally on `2026-11-23` against `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`) via `python3 support/probe_macro_hygiene_and_edition2024_expr_frag.py --json support/probe_results.json`:

| Group | Probe Case | Edition / Type | Exit Code | Key Observed Output / Diagnostic |
| :--- | :--- | :--- | :--- | :--- |
| **A** | `edition_2021_expr` | `2021` bin | compile `1` | `error: no rules expected keyword const`; `error: no rules expected reserved identifier _` |
| **A** | `edition_2024_expr` | `2024` bin | run `0` | `A=3`; `-Zunpretty=expanded` confirms `let a = const { 1 + 2 }; _ = 99;` |
| **A** | `edition_2021_expr_parenthesized_subexpr` | `2021` bin | run `0` | `A_PAREN=3` (`OpenParen` satisfies `can_begin_expr`) |
| **A** | `edition_2024_expr_rejects_let` | `2024` bin | compile `1` | `error: no rules expected keyword let` |
| **A** | `edition_2024_expr_2021_const_block` | `2024` bin | compile `1` | `error: no rules expected keyword const` (while matching `$e:expr_2021`) |
| **A** | `edition_2024_expr_2021_underscore` | `2024` bin | compile `1` | `error: no rules expected reserved identifier _` (while matching `$e:expr_2021`) |
| **A** | `cross_edition_def2021_call2024` | `2021` rlib -> `2024` bin | compile `1` | Fails at call site on both `const` and `_` (definition edition wins) |
| **A** | `cross_edition_def2024_call2021` | `2024` rlib -> `2021` bin | run `0` | `X21=3` (definition edition 2024 wins inside Edition 2021 caller) |
| **B** | `edition_2021` & `edition_2024` | `2021`, `2024` bin | run `0` | Identical: `OUT=(1,2) ITEM=2 DC=77 HELPER_SHADOW=999 LEAKED=33 METH=15 TMETH=20 FIELD=10` |
| **B** | `cross_crate_dollar_crate_vs_shadow` | `2024` rlib + bin | run `0` | `EXT_DC=55 SHADOW_MOD=888` (`$crate` bypasses `mod dep_hygiene` shadow) |
| **B** | `negative_dollar_crate_respects_visibility` | `2024` rlib + bin | compile `1` | `error[E0603]: function priv_fn is private` |
| **B** | `negative_macro_rules_local_does_not_leak` | `2024` bin | compile `1` | `error[E0425]: cannot find value secret in this scope` (macro hygiene help note) |
| **B** | `negative_macro_rules_cannot_capture_caller_local` | `2024` bin | compile `1` | `error[E0425]: cannot find value caller_only in this scope` (macro hygiene help note) |
| **B** | `negative_macro_rules_label_isolation` | `2024` bin | compile `1` | `error[E0426]: use of undeclared label 'blk` |
| **C** | `proc_macro_build` | `2024` proc-macro | compile `0` | Compiles `libhygiene_pm.so` cleanly (`call_site`, `mixed_site`, `resolved_at`, `#![feature(proc_macro_def_site)]` `def_site`) |
| **C** | `positive_call_site_mixed_site_def_site_internal` | `2024` bin | run `0` | `CS=42 CS_DEF=77 MS=10 MS_RES_AT=19 MS_ITEM=55 MS_METH=15 DS_INTERNAL=88 CALLER_X=42` |
| **C** | `negative_mixed_site_cannot_capture_caller_x` | `2024` bin | compile `1` | `error[E0425]: cannot find value x in this scope` |
| **C** | `negative_mixed_site_local_does_not_leak` | `2024` bin | compile `1` | `error[E0425]: cannot find value z in this scope` |
| **C** | `negative_def_site_item_isolated` | `2024` bin | compile `1` | `error[E0425]: cannot find function, tuple struct or tuple variant DefSiteOnly in this scope` |
| **C** | `negative_def_site_method_isolated` | `2024` bin | compile `1` | `error[E0624]: method get_val is private` (`Holder::get_val` invisible from proc-macro def scope) |
| **C** | `positive_def_site_pub_method_accessible` | `2024` bin | run `0` | `DS_PUB_METH=15` (`PubHolder::get_val` is `pub`) |
| **D** | `macros_2_0_opaque_item_isolated` | `2024` `#![feature(decl_macro)]` | compile `1` | `error[E0425]: ... OpaqueStruct ... not found in this scope` |
| **D** | `macros_2_0_opaque_method_privacy_at_def_site` | `2024` `#![feature(decl_macro)]` | compile `1` | `error[E0624]: method priv_val is private` |
| **D** | `macros_2_0_opaque_def_site_and_pub_method` | `2024` `#![feature(decl_macro)]` | run `0` | `DECL2_VAL=15 DECL2_HELPER=321 DECL2_PUB_METH=19` |

### Kernel-Checked Lean v4.34.1 Verification (`support/MacroHygieneSyntaxContextAndEditionFragSoundness.lean`)

`support/MacroHygieneSyntaxContextAndEditionFragSoundness.lean` (`1,556` lines, `66,312` bytes) compiled cleanly under Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with kernel type-checking enabled and warnings promoted to errors (`-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`), exiting `0`. An independent MetaM environment audit over all `1,005` elaborated constants in `Environment.constants.map₂` (`966` under `RustcMacroHygiene.*` and `39` private match splitters/equations; `81` surface `theorem`s, `74` `noncomputable def`s, `19` inductive/structure types) established:
- `0` constants containing `_unsafe_rec`;
- `0` `partial` definitions;
- `0` `unsafe` declarations;
- `0` custom axioms (`axiomInfo`);
- Exact transitive axiom set across every theorem and definition: `[propext]` (zero `Classical.choice`, zero `sorryAx`, zero `Lean.ofReduceBool`, zero `Lean.ofReduceNat`, zero `Lean.trustCompiler`).

## Revalidation

To revalidate all technical claims, empirical compiler outputs, and formal proofs without repeating the upstream source crawl:

1. **Re-run all 21 live `rustc` experiments across a target toolchain:**
   ```bash
   python3 support/probe_macro_hygiene_and_edition2024_expr_frag.py --json /tmp/probe_out.json
   ```
   Verify all exit codes, run outputs, `-Zunpretty=expanded` blocks, and error diagnostics (`E0425`, `E0426`, `E0603`, `E0624`, Edition 2021 vs. 2024 fragment errors) against `support/probe_results.json`. Requires a nightly `rustc` only for `#![feature(proc_macro_def_site)]` and `#![feature(decl_macro)]` in Groups C and D (and `-Zunpretty=expanded` inspection); stable `macro_rules!`, `Span::call_site()`, `Span::mixed_site()`, `Span::resolved_at()`, and Edition 2021/2024 `:expr` / `:expr_2021` checks run on stable `rustc` without feature gates.

2. **Re-verify kernel soundness and purity of the Lean 4 formalization:**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/MacroHygieneSyntaxContextAndEditionFragSoundness.lean
   ```
   Confirm exit code `0` with zero warnings and zero `sorry`/`Classical.choice`/`omega`/`bv_decide`/`native_decide`/`partial`/`._unsafe_rec` occurrences (`env.constants` check).

3. **Targeted upstream source drift check (`rust-lang/rust`):**
   If evaluating a newer `rust-lang/rust` commit beyond `0259d5e9a81c6af08e40f8c204f2c0c41dca1647`, inspect diffs in the seven narrow decision functions:
   - `Transparency::fallback`, `HygieneData::{normalize_to_macros_2_0, normalize_to_macro_rules, apply_mark, adjust}` (`compiler/rustc_span/src/hygiene.rs`)
   - `Marker::mark_span` and `Delimiter::Invisible(InvisibleOrigin::MetaVar(_))` (`compiler/rustc_expand/src/mbe/transcribe.rs`)
   - `Rustc::{new, span_recover_proc_macro_span}` (`compiler/rustc_expand/src/proc_macro_server.rs`)
   - `Resolver::resolve_crate_root`, `IdentKey::new` (`compiler/rustc_resolve/src/lib.rs`)
   - `resolve_ident_in_lexical_scope` (`compiler/rustc_resolve/src/ident.rs`) and `fresh_binding` (`compiler/rustc_resolve/src/late.rs`)
   - `TyCtxt::adjust_ident_and_get_scope` (`compiler/rustc_middle/src/ty/mod.rs`) and `AssocItems::find_by_ident_and_namespace` (`compiler/rustc_middle/src/ty/assoc.rs`)
   - `NonterminalKind::from_symbol` (`compiler/rustc_ast/src/token.rs`), `Parser::nonterminal_may_begin_with` (`compiler/rustc_parse/src/parser/nonterminal.rs`), and `is_in_follow` (`compiler/rustc_expand/src/mbe/macro_rules.rs`)
