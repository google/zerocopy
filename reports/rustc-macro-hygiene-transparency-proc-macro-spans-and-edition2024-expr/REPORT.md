# `rustc` Macro Hygiene, Transparency Tiers, `proc_macro` Spans, `FnDef` Type Privacy, and Edition 2024 `expr` Fragment Semantics

## Summary

`rustc` implements macro hygiene through a three-tier `Transparency` lattice (`Transparent`, `SemiOpaque`, `Opaque`) attached to every expansion mark on a token's `SyntaxContext` stack (`compiler/rustc_span/src/hygiene.rs`), coupled with **dual normalization projections** in `rustc_resolve` and a **hygiene-oblivious semantic type-privacy pass** in `rustc_privacy`:

1. **Three-Tier Transparency & Dual Normalization (`source` + `execution` + `derived`):**
   - `SyntaxContextData` eagerly caches two projections on every mark push (`alloc_ctxt`): `opaque` (`normalize_to_macros_2_0`, retaining only `Opaque` marks) and `opaque_and_semiopaque` (`normalize_to_macro_rules`, retaining both `SemiOpaque` and `Opaque` marks while stripping `Transparent`).
   - `macro_rules!` and `proc_macro::Span::mixed_site()` produce `SemiOpaque` marks. In `rustc_resolve`, local variables (`ident.rs`), loop labels (`late.rs`), and `$crate` crate-root lookup (`lib.rs`) use `normalize_to_macro_rules()` (resolving at definition-site and avoiding local/label capture in both directions), whereas module-level items, type paths, lifetimes, and generic parameters use `normalize_to_macros_2_0()` (stripping `SemiOpaque` marks and resolving at call-site).
   - `proc_macro::Span::call_site()` produces `Transparent` marks, which both normalizers discard—causing emitted local identifiers to capture caller locals (`PM_CALL=77`).
   - Declarative `macro` 2.0 (`#![feature(decl_macro)]`) and `proc_macro::Span::def_site()` (`#![feature(proc_macro_def_site)]`) produce `Opaque` marks, which survive both normalizers—resolving locals, labels, and unqualified items at the macro definition module (`OPAQUE_ITEM_DEFSITE=10`) and isolating call-site items (`E0425`).
2. **Name-Resolution Hygiene vs. Semantic `FnDef` Type-Privacy Asymmetry (`source` + `execution` + `derived`):**
   - Under `Opaque` (`decl_macro`) hygiene, `IdentKey::new_adjusted` pops non-descendant opaque marks and switches name-resolution visibility checking to `expn_def_scope(def)` (`rustc_resolve/src/ident.rs`), bypassing `E0603` for private definition-site items.
   - Downstream after type inference, however, `rustc_privacy::TypePrivacyVisitor` walks every expression's semantic `Ty<'tcx>` **"regardless of names and their hygiene"** (`rustc_privacy/src/lib.rs`) against the **call-site** module (`self.mod_id`). Because every function item has a unique zero-sized nominal `ty::FnDef(def_id, ..)` type, calling a private `fn helper() -> u32` from a `pub macro` passes `rustc_resolve` yet fails in `rustc_privacy` with `error: type fn() -> u32 {helper} is private` (both intra-crate and cross-crate), as does constructing a private `struct Hidden(u32)` (`error: type Hidden is private`).
   - By contrast, reading a private `const SECRET: u32 = 777` via `decl_macro` succeeds both intra-crate (`777`) and cross-crate (`505`) because `u32` contains no private `DefId`. Coercing a private function into a private function-pointer constant (`const HELPER_PTR: fn() -> u32 = helper;`) erases the private `FnDef` into public `ty::FnPtr`, succeeding intra-crate (`10`) and isolating `FnDef` type privacy as the exact cause—while cross-crate it bypasses both `rustc_resolve` and `rustc_privacy` before failing at upstream `.rlib` metadata (`missing optimized MIR`). Additionally, `TypePrivacyVisitor::visit_qpath` explicitly exempts only `def_id.is_local()` statics: intra-crate private `static` succeeds (`888`), while cross-crate private `static` is rejected (`error: static up_mac::UPSTREAM_SECRET_STATIC is private`).
   - `macro_rules!` (`SemiOpaque`) `$crate::secret_helper()` and `$crate::UPSTREAM_SECRET_CONST` fail earlier during name resolution with `E0603`, because `$crate` uses `normalize_to_macro_rules()` while the member segment uses `normalize_to_macros_2_0()`.
3. **Edition 2021 vs. 2024 `expr`/`expr_2021` Fragment Drift (`normative` + `source` + `execution`):**
   - `NonterminalKind::from_symbol` (`rustc_ast/src/token.rs`) maps `expr` to `NtExprKind::Expr` when the **definition-site** span edition is `>= 2024` and to `NtExprKind::Expr2021 { inferred: true }` on Edition `<= 2021`, while `expr_2021` unconditionally produces `Expr2021 { inferred: false }`.
   - `Parser::nonterminal_may_begin_with` (`rustc_parse/src/parser/nonterminal.rs`) excludes `kw::Const` under `Expr2021` and adds `kw::Underscore` under `Expr` (while excluding `kw::Let` in both). Cross-edition tests confirm definition-site edition governs: an Edition 2021 macro invoked from Edition 2024 rejects `const { 1 + 2 }`, whereas an Edition 2024 macro invoked from Edition 2021 accepts it (`XED=3`).
4. **Exact Default `recursion_limit = 128` Accounting (`source` + `execution` + `derived`):**
   - Crate compilation defaults `recursion_limit` to `128` (`rustc_interface/src/limits.rs`, overriding `ExpansionConfig::default`'s `1024` test fallback), and `MacroExpander::expand_invoc` (`rustc_expand/src/expand.rs`) enforces `depth <= limit` where each collected macro invocation increments `depth + 1`.
   - For recursive `count!(+^n)` (`n` inductive steps plus `1` base-case expansion), exact admission is `outer_frames + n + 1 <= 128`: top-level `count!` (`outer_frames = 0`) passes at `n = 127` and overflows at `n = 128`, whereas `println!("{}", count!(+^n))` (`outer_frames = 2` via `println!` -> `format_args_nl!` in `library/std/src/macros.rs`) passes at `n = 125` and overflows at `n = 126`.
5. **Host-Impure `proc_macro` Reproducibility Cliff & Anneal TCB Boundary (`source` + `execution` + `derived`):**
   - `rustc_expand/src/proc_macro.rs` executes compiled `proc_macro` dylibs unsandboxed inside the host compiler process/thread with unrestricted access to host environment variables. Under identical source and flags (`-C codegen-units=1 -C debuginfo=0 --remap-path-prefix`), an env-reading `proc_macro` yields bit-exact `984`-byte `.o` files under identical `PROBE_BUILD_NONCE` (`a1a45796...`) but diverges to a different `.o` hash (`83fde0ee...`) when `PROBE_BUILD_NONCE` changes, while a pure `proc_macro` remains invariant (`1c643033...`).
   - Consistent with `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`THREAT_MODEL.md`, `docs/trust-model.md`, `trusted/rustc-capture/src/driver.rs`), procedural macro execution must be hermetically sandboxed and sealed upstream of any verification or certified-compilation TCB operating on post-expansion `Runtime(PostCleanup)` MIR.
6. **Kernel-Checked Lean 4.34.1 Mechanization (`source` + `execution` + `derived`):**
   - `support/MacroHygieneAndTransparencySoundness.lean` (944 lines) mechanizes mark-stack normalization, dual-pass resolution and `FnDef` type privacy, exact `recursion_limit` fuel bounds, Edition 2021/2024 `NtExprKind` matching, and pure vs. host-impure expansion determinism across 26 kernel-checked public theorems (18 headline theorems including all 4 core soundness theorems and 3 constructive counterexamples, plus 8 supporting algebraic lemmas and 2 private helpers) under `leanprover/lean4@v4.34.1` with `-DwarningAsError=true`, `0` `sorry`, `0` `Classical.choice`, `0` `Quot.sound`, `0` `Lean.ofReduceBool`, and `0` `partial def`.

## Applicability

This report characterizes four concrete, immutable upstream subjects recorded in `REPORT.json` and their explicit relationships:

1. **Upstream `rust-lang/rust` source (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`, dated `2026-11-22`)** and **executed `rustc 1.98.0-nightly` compiler (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `2026-05-31`, LLVM `22.1.6`, host `x86_64-unknown-linux-gnu`)**:
   - All empirical probe measurements (`support/probe_macro_hygiene.py`, recorded in `support/probe_macro_hygiene_results.json`) were executed live on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` on `x86_64-unknown-linux-gnu`.
   - Primary source audits were performed directly on `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` and cross-checked against `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` for the four load-bearing files (`hygiene.rs`, `token.rs`, `expand.rs`, `rustc_privacy/src/lib.rs`). All inspected mechanisms—`Transparency` enum variants, dual `SyntaxContext` normalizations, `NtExprKind::{Expr, Expr2021}`, `expand_invoc` `value_within_limit`, and `TypePrivacyVisitor` `FnDef`/`is_local_static` checks—are identical in structure across both revisions, with only minor line-number shifts recorded explicitly in **Evidence**.
   - **Nightly feature gates required:** `macro_rules!`, `proc_macro::Span::call_site()`, `proc_macro::Span::mixed_site()`, Edition 2021/2024 `expr`/`expr_2021`, and `#![recursion_limit = "..."]` are stable Rust features. By contrast, `decl_macro` (`pub macro ...`) requires `#![feature(decl_macro)]` and `proc_macro::Span::def_site()` requires `#![feature(proc_macro_def_site)]`, both restricted to nightly `rustc`.
   - **Object-file determinism flags:** Empirical `.o` bit-exactness measurements require `--crate-type=lib --emit=obj -C codegen-units=1 -C debuginfo=0 -C opt-level=2 --remap-path-prefix=<workdir>=/remap`. Omitting `-C codegen-units=1` with `-C opt-level=2` causes `rustc` to partition into multiple codegen units and overwrite `-o <path>` with an empty crate-root CGU, masking function body differences in single-file `-o` `.o` emission.
2. **Anneal verification architecture (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, dated `2026-11-19`):**
   - Inspected to establish how a `rustc_driver`-backed Lean verification system positions macro expansion and `proc_macro` execution relative to its TCB (`THREAT_MODEL.md`, `docs/trust-model.md`, `docs/architecture.md`, `trusted/rustc-capture/src/driver.rs`, `trusted/audit/TrustedBoundary.lean`).
   - At `c131b320e`, `trusted/rustc-capture/src/driver.rs` pins `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` and implements an analysis-callback gate stub (`Callbacks::after_analysis`) rather than full MIR extraction; its architectural contracts in `THREAT_MODEL.md` and `docs/architecture.md` establish the intended post-expansion capture boundary.
3. **Lean 4 kernel verification (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`, `x86_64-unknown-linux-gnu`):**
   - Used to kernel-check the standalone formalization `support/MacroHygieneAndTransparencySoundness.lean` with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` and `#print axioms`.
   - The Lean formalization models the abstract semantics of `rustc`'s hygiene, privacy, expansion fuel, Edition 2024 fragment matching, and determinism properties; it does **not** import `joshlf/anneal`'s `Trusted.MirSemantics` and does **not** formally verify `rustc`'s Rust source code.

## Findings

### 1. Transparency Lattice and `SyntaxContext` Mark-Stack Architecture

Basis: `source` + `derived`

In `compiler/rustc_span/src/hygiene.rs` (`lines 178-200` at `342d74463`; `lines 165-187` at `14210df0e`), `rustc` defines identifier hygiene resolution via a three-element ordered enum `Transparency`:

```rust
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Hash, Debug, Encodable, Decodable)]
#[derive(StableHash)]
pub enum Transparency {
    /// Identifier produced by a transparent expansion is always resolved at call-site.
    /// Call-site spans in procedural macros, hygiene opt-out in `macro` should use this.
    Transparent,
    /// Identifier produced by a semi-opaque expansion may be resolved
    /// either at call-site or at definition-site.
    /// If it's a local variable, label or `$crate` then it's resolved at def-site.
    /// Otherwise it's resolved at call-site.
    /// `macro_rules` macros behave like this, built-in macros currently behave like this too,
    /// but that's an implementation detail.
    SemiOpaque,
    /// Identifier produced by an opaque expansion is always resolved at definition-site.
    /// Def-site spans in procedural macros, identifiers from `macro` by default use this.
    Opaque,
}

impl Transparency {
    pub fn fallback(macro_rules: bool) -> Self {
        if macro_rules { Transparency::SemiOpaque } else { Transparency::Opaque }
    }
}
```

Every `Span` carries an interned `SyntaxContext` (`SyntaxContext::root() = 0` for unexpanded source tokens). Inside `HygieneData` (`hygiene.rs:598-783` at `342d74463`), each `SyntaxContext` indexes a `SyntaxContextData` record storing six fields:

| Field | Role | Computation in `HygieneData::alloc_ctxt` (`hygiene.rs:727-782`) |
| :--- | :--- | :--- |
| `outer_expn: ExpnId` | Expansion that introduced this mark | Set to `expn_id` |
| `outer_transparency: Transparency` | Hygiene tier of `outer_expn` | Set to `transparency` |
| `parent: SyntaxContext` | Next inner context in the mark stack | Set to `parent` |
| `opaque: SyntaxContext` | Cached `normalize_to_macros_2_0` projection | Retains mark iff `transparency == Opaque`; otherwise inherits `parent.opaque` |
| `opaque_and_semiopaque: SyntaxContext` | Cached `normalize_to_macro_rules` projection | Retains mark iff `transparency ∈ {SemiOpaque, Opaque}`; strips `Transparent` |
| `dollar_crate_name: Symbol` | Pretty-printed crate name for `$crate` | Initialized to `kw::DollarCrate`, updated lazily by `update_dollar_crate_names` |

This eager dual-projection design gives `O(1)` access to both normalizations (`hygiene.rs:599-606`):

```rust
fn normalize_to_macros_2_0(&self, ctxt: SyntaxContext) -> SyntaxContext {
    self.syntax_context_data[ctxt].opaque
}
fn normalize_to_macro_rules(&self, ctxt: SyntaxContext) -> SyntaxContext {
    self.syntax_context_data[ctxt].opaque_and_semiopaque
}
```

Algebraically, `normalize_to_macros_2_0` and `normalize_to_macro_rules` are idempotent projections on mark stacks satisfying the absorption law `normalize_to_macros_2_0(normalize_to_macro_rules(c)) = normalize_to_macros_2_0(c)` (mechanized in `MacroHygieneAndTransparencySoundness.lean`).

#### `apply_mark` and Mixed Legacy/Macros-2.0 Grafting

When pushing a new mark (`hygiene.rs:688-723`), `HygieneData::apply_mark` handles `Opaque` directly (`alloc_ctxt(ctxt, expn_id, Opaque)`). For `SemiOpaque` and `Transparent`, it first inspects `call_site_ctxt = self.expn_data(expn_id).call_site.ctxt()`, normalized via `normalize_to_macros_2_0` (if `SemiOpaque`) or `normalize_to_macro_rules` (if `Transparent`). If that normalized call-site context is non-root—which occurs when a `macro_rules!` or `Transparent` macro is invoked *inside* a `decl_macro` (`Opaque`) body—`apply_mark` replays `self.marks(ctxt)` onto `call_site_ctxt` before appending `(expn_id, transparency)` (`hygiene.rs:719-722`). This grafting preserves enclosing `decl_macro` hygiene when legacy macros are expanded inside `decl_macro` definitions.

#### Mapping `proc_macro::Span` Constructors to `Transparency`

Procedural macros receive three global spans via `proc_macro_server::Rustc::new` (`compiler/rustc_expand/src/proc_macro_server.rs:467-476`), delegating through `ExtCtxt::with_*_site_ctxt` (`compiler/rustc_expand/src/base.rs:1280-1295`) to `Span::with_*_site_ctxt` (`compiler/rustc_span/src/lib.rs:1294-1315`):

```rust
pub fn with_def_site_ctxt(self, expn_id: ExpnId) -> Span {
    self.with_ctxt_from_mark(expn_id, Transparency::Opaque)
}
pub fn with_call_site_ctxt(self, expn_id: ExpnId) -> Span {
    self.with_ctxt_from_mark(expn_id, Transparency::Transparent)
}
pub fn with_mixed_site_ctxt(self, expn_id: ExpnId) -> Span {
    self.with_ctxt_from_mark(expn_id, Transparency::SemiOpaque)
}
fn with_ctxt_from_mark(self, expn_id: ExpnId, transparency: Transparency) -> Span {
    self.with_ctxt(SyntaxContext::root().apply_mark(expn_id, transparency))
}
```

#### Unified Three-Tier Hygiene Behavior Table

| Mechanism | `Transparency` | Retained in `normalize_to_macro_rules`? | Retained in `normalize_to_macros_2_0`? | Local vars & Loop labels | `$crate` | Lifetimes & Generic params | Unqualified items (`fn`, `const`, `struct`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `proc_macro::Span::call_site()` | `Transparent` | No | No | Call-site (captures caller) | Call-site | Call-site | Call-site |
| `macro_rules!`, `Span::mixed_site()` | `SemiOpaque` | **Yes** | No | **Def-site** (capture-avoiding) | **Def-site** | Call-site | Call-site (shadowable by caller) |
| `decl_macro` (`macro`), `Span::def_site()` | `Opaque` | **Yes** | **Yes** | **Def-site** (capture-avoiding) | **Def-site** | **Def-site** | **Def-site** (name-res privacy adjusted to `def_mod`) |

---

### 2. Dual Normalization in `rustc_resolve`: Locals, Labels, Lifetimes, `$crate`, and Items

Basis: `source` + `execution`

`rustc_resolve` directly enforces the split between `normalize_to_macro_rules()` and `normalize_to_macros_2_0()` across four resolution sites:

1. **Lexical Value and Type Ribs (`compiler/rustc_resolve/src/ident.rs:309-390`):**
   In `resolve_ident_in_lexical_scope`:
   - `Self` (`kw::SelfUpper`) resets to `SyntaxContext::root()` (`lines 320-323`).
   - `TypeNS` normalizes both spans with `normalize_to_macros_2_0()` (`lines 324-326`).
   - `ValueNS` computes **two** spans: `general_span = ident.span.normalize_to_macro_rules()` (retaining `SemiOpaque` + `Opaque`) and `normalized_span = ident.span.normalize_to_macros_2_0()` (retaining only `Opaque`) (`line 328`).
   - While walking ribs inward-to-outward (`lines 334-340`), `rib_ident` selects `normalized_ident` (`macros_2_0`) when `rib.kind.contains_params()` (type/const generic parameters) and `ident` (`macro_rules`) for local-variable ribs (`let` bindings, function arguments).
   - Upon reaching `RibKind::Module(module)` (`lines 362-377`), resolution abandons ribs and calls `resolve_ident_in_scope_set(orig_ident, ScopeSet::All(ns), ...)`, which immediately constructs `IdentKey::new(orig_ident)` using `Macros20NormalizedSyntaxContext::new(ident.span.ctxt())` (`rustc_resolve/src/lib.rs:619-621, 3137-3139`)—stripping all `SemiOpaque` and `Transparent` marks!
2. **Loop Labels vs. Lifetimes (`compiler/rustc_resolve/src/late.rs`):**
   - Loop labels (`'lbl: loop { break 'lbl ... }`) normalize via `let ident = label.normalize_to_macro_rules();` (`late.rs:2887`), giving `macro_rules!` and `Span::mixed_site()` full bidirectional label hygiene.
   - Lifetimes (`'a`) normalize via `ident.normalize_to_macros_2_0()` (`late.rs:1943, 2028`), meaning `SemiOpaque` macros do *not* isolate lifetime parameters—only `Opaque` macros do.
3. **Lexical Parent Walk and Privacy-Scope Adjustment (`compiler/rustc_resolve/src/ident.rs:244-254, 1019-1023`):**
   - In `hygienic_lexical_parent`, when walking out of `module` with a `Macros20NormalizedSyntaxContext`, if `!module.expansion.outer_expn_is_descendant_of(**ctxt)`, `rustc_resolve` pops the outermost `Opaque` mark `expn_id` and jumps directly to `self.expn_def_scope(expn_id)`.
   - In module-member resolution (`ident.rs:1019-1023`), `IdentKey::new_adjusted(ident, module.expansion)` calls `SyntaxContext::normalize_to_macros_2_0_and_adjust` (`hygiene.rs:938-943`):
     ```rust
     let (ident_key, def) = IdentKey::new_adjusted(ident, module.expansion);
     let adjusted_parent_scope = match def {
         Some(def) => ParentScope { module: self.expn_def_scope(def), ..*parent_scope },
         None => *parent_scope,
     };
     ```
     If an `Opaque` mark was stripped by `adjust`, `def` is `Some(expn_id)`, switching the name-resolution visibility check `is_accessible_from(binding.vis(), adjusted_parent_scope.module)` to the **macro's definition module**. Because `SemiOpaque` marks were already stripped by `normalize_to_macros_2_0` before `adjust`, `SemiOpaque` invocations yield `def = None` and check name-resolution visibility against the **call-site** module.
4. **`$crate` Crate-Root Resolution (`compiler/rustc_resolve/src/lib.rs:2375-2410`):**
   - `resolve_crate_root` normalizes `$crate` with `ctxt = ctxt.normalize_to_macro_rules()`, preserving `SemiOpaque` marks so `$crate` inside `macro_rules!` resolves to the defining crate root. Notably, `lib.rs:2379-2410` contains an explicit reverse-scan heuristic (with an upstream `FIXME` at `lines 2382-2384`) that walks past trailing `Opaque` marks to find the last `SemiOpaque` mark so a `macro_rules!` invoked inside a `decl_macro` still resolves `$crate` to the `macro_rules!` crate rather than the enclosing `decl_macro` crate.

#### Empirical Verification: Three-Tier Hygiene Matrix (Part A)

Executed via `support/probe_macro_hygiene.py` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`support/probe_macro_hygiene_results.json`):

| Probe Case | Mechanism & Span | `compile_rc` | `run_rc` | Observed Output / Exact Diagnostic Head |
| :--- | :--- | ---: | ---: | :--- |
| `macro_rules_semi_opaque` | `macro_rules!` (`SemiOpaque`) | `0` | `0` | `LOCAL_HYG=(100,7) ITEM_CALLSITE=999 LABEL_HYG=42 LABEL_BIDIR=99` |
| `decl_macro_opaque_pub_defsite` | `decl_macro` (`Opaque`, `pub fn`) | `0` | `0` | `OPAQUE_LOCAL=(100,7) OPAQUE_ITEM_DEFSITE=10 OPAQUE_LABEL=55` |
| `proc_macro_crate_build` | `--crate-type=proc-macro` `libpm_hyg.so` | `0` | — | Clean build (`0` warnings/errors) |
| `proc_macro_call_site_captures_local` | `proc_macro` `Span::call_site()` (`Transparent`) | `0` | `0` | `PM_CALL=77` (captured caller `let x: u32 = 77`) |
| `proc_macro_mixed_site_isolates_local` | `proc_macro` `Span::mixed_site()` (`SemiOpaque`) | `1` | — | `error[E0425]: cannot find value x in this scope` (+ `help: an identifier with the same name exists, but is not accessible due to macro hygiene`) |
| `proc_macro_def_site_isolates_local` | `proc_macro` `Span::def_site()` (`Opaque`) | `1` | — | `error[E0425]: cannot find value x in this scope` (+ macro hygiene `help`) |
| `proc_macro_mixed_site_resolves_item_at_callsite` | `proc_macro` `Span::mixed_site()` (`let x` + `caller_item()`) | `0` | `0` | `PM_MIXED_ITEM=321 CALLER_X=77` (item at call-site; local `x` isolated) |
| `proc_macro_def_site_isolates_callsite_item` | `proc_macro` `Span::def_site()` (`caller_item()`) | `1` | — | `error[E0425]: cannot find function caller_item in this scope` |

Notice the `LABEL_BIDIR=99` check in `macro_rules_semi_opaque`: passing caller `break 'lbl 99u32` as `$e:expr` into a macro defining its own `'lbl: loop { let _ = $e; break 'lbl 42u32; }` breaks the **caller's** `'lbl` loop (returning `99`), while the macro's own `break 'lbl 42u32` breaks the **macro's** `'lbl` loop (`LABEL_HYG=42`), empirically confirming bidirectional label capture-avoidance under `SemiOpaque`.

---

### 3. Name-Resolution Hygiene vs. Semantic `FnDef` Type-Privacy Asymmetry

Basis: `source` + `execution` + `derived`

A sharp, non-obvious asymmetry governs private items referenced inside `decl_macro` (`Opaque`) expansions vs. `macro_rules!` (`SemiOpaque`) `$crate::...` expansions. The compiler enforces privacy in **two distinct passes** that treat `SyntaxContext` differently:

1. **Pass A — Name-Resolution Privacy (`rustc_resolve/src/ident.rs:1019-1023`):**
   - For `decl_macro` (`Opaque`), `IdentKey::new_adjusted` sets `adjusted_parent_scope.module = expn_def_scope(def)`. Therefore, private functions, private constants, private statics, and private structs in the macro's defining module ALL **pass name resolution** without emitting `E0603`—both intra-crate and cross-crate.
   - For `macro_rules!` (`SemiOpaque`), `$crate::secret_helper()` resolves `$crate` to the defining crate (`lib.rs:2385`), then resolves `secret_helper` with `IdentKey::new_adjusted`, which strips the `SemiOpaque` mark and checks `is_accessible_from` against the **call-site** module, immediately failing with `error[E0603]: function secret_helper is private` (and `error[E0603]: constant UPSTREAM_SECRET_CONST is private`).
2. **Pass B — Post-Typeck Semantic Type Privacy (`compiler/rustc_privacy/src/lib.rs:185-205, 1119-1310`):**
   After HIR type inference produces `TypeckResults`, `TypePrivacyVisitor` checks every inferred expression and pattern type. Its doc comment (`lib.rs:1119-1123` at `342d74463`; `1122-1126` at `14210df0e`) states the exact invariant:
   ```rust
   /// Type privacy visitor, checks types for privacy and reports violations.
   ///
   /// Both explicitly written types and inferred types of expressions and patterns are checked.
   /// Checks are performed on "semantic" types regardless of names and their hygiene.
   struct TypePrivacyVisitor<'tcx> {
       tcx: TyCtxt<'tcx>,
       mod_id: LocalModId,
       ...
   }
   impl<'tcx> TypePrivacyVisitor<'tcx> {
       fn item_is_accessible(&self, did: DefId) -> bool {
           self.tcx.visibility(did).is_accessible_from(self.mod_id, self.tcx)
       }
   ```
   When walking a type (`lib.rs:185-205`), `DefIdVisitor` visits every nominal `DefId`:
   ```rust
   match ty_kind {
       ty::Adt(ty::AdtDef(Interned(&ty::AdtDefData { did: def_id, .. }, _)), ..)
       | ty::View(ty::AdtDef(Interned(&ty::AdtDefData { did: def_id, .. }, _)), ..)
       | ty::Foreign(def_id)
       | ty::FnDef(def_id, ..)
       | ty::Closure(def_id, ..)
       | ty::CoroutineClosure(def_id, ..)
       | ty::Coroutine(def_id, ..) => {
           try_visit!(self.def_id_visitor.visit_def_id(def_id, "type", &ty));
   ```
   If `!self.item_is_accessible(def_id)` relative to the **call-site** module `self.mod_id`, `check_def_id` (`lib.rs:1165-1171`) emits `ItemIsPrivate` (`error: type <ty> is private`, with **no** `E0603` error code).
   - Calling `helper()` evaluates the callee path expression `helper` to its zero-sized nominal function-item type `ty::FnDef(helper_def_id, [])`, printed as `fn() -> u32 {helper}`. `TypePrivacyVisitor::visit_expr` checks `node_type(expr)` against the caller's `self.mod_id` and rejects it!
   - Constructing `Hidden(42).get()` evaluates `Hidden(42)` to `ty::Adt(Hidden)`, which `TypePrivacyVisitor` rejects with `error: type Hidden is private`.
   - Reading `const SECRET: u32 = 777` evaluates to primitive `ty::Uint(U32)`, which has no private `DefId`—so `TypePrivacyVisitor` accepts it both intra-crate and cross-crate!
   - **Decisive Discriminator (FnDef Coercion to `fn() -> u32`):** Defining `const HELPER_PTR: fn() -> u32 = helper;` inside `def_mod` performs the `FnDef -> FnPtr` coercion inside `def_mod`'s own body. At the call site, `(HELPER_PTR)()` evaluates `HELPER_PTR` to `ty::FnPtr` (`fn() -> u32`), which contains **no** `DefId` for `helper`. Intra-crate, `decl_macro` calling `(HELPER_PTR)()` compiles and runs (`OPAQUE_PRIV_FNPTR=10`)! Cross-crate, it passes **both** `rustc_resolve` and `rustc_privacy`, and then fails at MIR/const-eval codegen metadata (`error: missing optimized MIR for up_mac::secret_helper in the crate up_mac`), exposing a third boundary: upstream `.rlib` reachability/MIR export does not automatically export non-reachable private functions referenced only through private constants expanded via `decl_macro`.
3. **Pass B Static-Specific Cross-Crate Guard (`compiler/rustc_privacy/src/lib.rs:1263-1293`):**
   `TypePrivacyVisitor::visit_qpath` carries an explicit carve-out documented directly in upstream source:
   ```rust
   // Additionally, until better reachability analysis for macros 2.0 is available,
   // we prohibit access to private statics from other crates, this allows to give
   // more code internal visibility at link time. (Access to private functions
   // is already prohibited by type privacy for function types.)
   ...
   let is_local_static =
       if let DefKind::Static { .. } = kind { def_id.is_local() } else { false };
   if !self.item_is_accessible(def_id) && !is_local_static {
       ... emit ItemIsPrivate ...
   }
   ```
   This source rule predicts—and our live probe confirms—that a `decl_macro` reading a private `static`:
   - **succeeds intra-crate** (`def_id.is_local() == true` -> `OPAQUE_PRIV_STATIC=888`),
   - **fails cross-crate** (`def_id.is_local() == false` -> `error: static up_mac::UPSTREAM_SECRET_STATIC is private`, distinct from `E0603`!).

#### Complete Intra-Crate and Cross-Crate Privacy Matrix (Parts A2 & B)

| Probe Case | Scope | Macro Tier | Target Item & Semantic Type | `compile_rc` | Failing Pass | Observed Output / Diagnostic |
| :--- | :--- | :--- | :--- | ---: | :--- | :--- |
| `decl_macro_opaque_priv_const_ok` | Intra-crate | `decl_macro` (`Opaque`) | `const SECRET: u32` (`u32`) | `0` | None | `OPAQUE_PRIV_CONST=777` |
| `decl_macro_opaque_priv_static_ok` | Intra-crate | `decl_macro` (`Opaque`) | `static SECRET_STATIC: u32` (`u32`, local) | `0` | None | `OPAQUE_PRIV_STATIC=888` |
| `decl_macro_opaque_priv_fn_via_fnptr_const_ok` | Intra-crate | `decl_macro` (`Opaque`) | `const HELPER_PTR: fn() -> u32` (`FnPtr`) | `0` | None | `OPAQUE_PRIV_FNPTR=10` |
| `decl_macro_opaque_priv_fn_rejected` | Intra-crate | `decl_macro` (`Opaque`) | `fn helper() -> u32` (`FnDef`) | `1` | `rustc_privacy` (`visit_expr`) | `error: type fn() -> u32 {helper} is private` |
| `decl_macro_opaque_priv_struct_rejected` | Intra-crate | `decl_macro` (`Opaque`) | `struct Hidden(u32)` (`Adt`) | `1` | `rustc_privacy` (`visit_expr`) | `error: type Hidden is private` |
| `macro_rules_dollar_crate_pub` | Cross-crate | `macro_rules!` (`SemiOpaque`) | `$crate::pub_helper()` (`pub fn`) | `0` | None | `DC_PUB=200` |
| `macro_rules_dollar_crate_priv_fn_rejected` | Cross-crate | `macro_rules!` (`SemiOpaque`) | `$crate::secret_helper()` (`fn`) | `1` | `rustc_resolve` (`E0603`) | `error[E0603]: function secret_helper is private` |
| `macro_rules_dollar_crate_priv_const_rejected` | Cross-crate | `macro_rules!` (`SemiOpaque`) | `$crate::UPSTREAM_SECRET_CONST` (`const`) | `1` | `rustc_resolve` (`E0603`) | `error[E0603]: constant UPSTREAM_SECRET_CONST is private` |
| `decl_macro_upstream_pub_fn_ok` | Cross-crate | `decl_macro` (`Opaque`) | `pub_helper()` (`pub fn`) | `0` | None | `DECL_PUB=200` |
| `decl_macro_upstream_priv_const_ok` | Cross-crate | `decl_macro` (`Opaque`) | `UPSTREAM_SECRET_CONST` (`u32`) | `0` | None | `DECL_PRIV_CONST=505` |
| `decl_macro_upstream_priv_fn_rejected` | Cross-crate | `decl_macro` (`Opaque`) | `secret_helper()` (`FnDef`) | `1` | `rustc_privacy` (`visit_expr`) | `error: type fn() -> u32 {up_mac::secret_helper} is private` |
| `decl_macro_upstream_priv_static_rejected` | Cross-crate | `decl_macro` (`Opaque`) | `UPSTREAM_SECRET_STATIC` (`static`, non-local) | `1` | `rustc_privacy` (`visit_qpath`) | `error: static up_mac::UPSTREAM_SECRET_STATIC is private` |
| `decl_macro_upstream_priv_fnptr_mir_missing` | Cross-crate | `decl_macro` (`Opaque`) | `(UPSTREAM_HELPER_PTR)()` (`FnPtr` -> private fn) | `1` | MIR/metadata (`rustc_metadata`) | `error: missing optimized MIR for up_mac::secret_helper in the crate up_mac` |

---

### 4. Edition 2021 vs. Edition 2024 `expr` / `expr_2021` Fragment Specifier Drift

Basis: `normative` + `source` + `execution`

In Rust 2024, the macro fragment specifier `$e:expr` expanded its accepted leading tokens to match inline `const { ... }` blocks and `_` assignee expressions, while introducing the explicit backward-compatibility specifier `$e:expr_2021`.

#### Primary-Source Representation and First-Set Gate

1. **Fragment Specifier Resolution (`compiler/rustc_ast/src/token.rs:106-107, 1136-1204` at `342d74463`; `106-107, 1102-1170` at `14210df0e`):**
   `NtExprKind` distinguishes Edition 2024 `Expr` from pre-2024 `Expr2021 { inferred: bool }` (`inferred: true` when written `expr` in Edition `<= 2021`; `inferred: false` when written `expr_2021`). `NonterminalKind::from_symbol` evaluates `edition()` lazily from the **definition-site** span of the fragment specifier token:
   ```rust
   sym::expr => {
       if edition().at_least_rust_2024() {
           NonterminalKind::Expr(Expr)
       } else {
           NonterminalKind::Expr(Expr2021 { inferred: true })
       }
   }
   sym::expr_2021 => NonterminalKind::Expr(Expr2021 { inferred: false }),
   ```
   `MetaVarKind`'s `Display` impl (`token.rs:106-107`) renders `Expr2021 { inferred: true } | Expr` as `expr` and `Expr2021 { inferred: false }` as `expr_2021`, explaining why diagnostic notes say `while trying to match meta-variable $e:expr` in Edition 2021 and `$e:expr_2021` when explicitly written `expr_2021`.
2. **Exact First-Set Difference (`compiler/rustc_parse/src/parser/nonterminal.rs:43-64`):**
   In `Parser::nonterminal_may_begin_with`:
   ```rust
   // `expr_2021` and earlier
   NonterminalKind::Expr(Expr2021 { .. }) => {
       token.can_begin_expr()
       && !token.is_keyword(kw::Let)
       && !token.is_keyword(kw::Const)
   }
   // Current edition expressions
   NonterminalKind::Expr(Expr) => {
       (token.can_begin_expr() || token.is_keyword(kw::Underscore))
       && !token.is_keyword(kw::Let)
   }
   ```
   Two exact deltas separate `Expr` from `Expr2021`:
   - `kw::Const` (`const { ... }`) is permitted under `Expr` (because `can_begin_expr()` includes `const` blocks) and explicitly rejected under `Expr2021`.
   - `kw::Underscore` (`_`) is explicitly permitted under `Expr` (even though `token.can_begin_expr()` returns `false` for `_`) and rejected under `Expr2021`.
   - `kw::Let` remains excluded in **both** `Expr2021` and `Expr` for backward compatibility.

#### Empirical Verification: Edition 2021 / 2024 & Cross-Edition Matrix (Part C1–C3)

| Probe Case | Def Edition | Call Edition | Specifier | Input Tokens | `compile_rc` | Observed Output / Diagnostic |
| :--- | :--- | :--- | :--- | :--- | ---: | :--- |
| `ed2021_expr_const_block` | `2021` | `2021` | `$e:expr` | `const { 1 + 2 }` | `1` | `error: no rules expected keyword const` (`while trying to match meta-variable $e:expr`) |
| `ed2024_expr_const_block` | `2024` | `2024` | `$e:expr` | `const { 1 + 2 }` | `0` | `EXPR_CONST=3` |
| `ed2021_expr_underscore` | `2021` | `2021` | `$e:expr` | `_` (in `$e = 9`) | `1` | `error: no rules expected reserved identifier _` |
| `ed2024_expr_underscore` | `2024` | `2024` | `$e:expr` | `_` (in `$e = 9`) | `0` | `EXPR_UNDERSCORE_OK` |
| `ed2024_expr_2021_rejects_const_block` | `2024` | `2024` | `$e:expr_2021` | `const { 1 + 2 }` | `1` | `error: no rules expected keyword const` (`while trying to match meta-variable $e:expr_2021`) |
| `ed2024_expr_2021_rejects_underscore` | `2024` | `2024` | `$e:expr_2021` | `_` (in `$e = 9`) | `1` | `error: no rules expected reserved identifier _` |
| `ed2024_expr_2021_accepts_regular_expr` | `2024` | `2024` | `$e:expr_2021` | `1 + 2` | `0` | `EXPR_2021_ADD=3` |
| `cross_edition_def2021_call2024_const_block` | `2021` (`ed21_mac`) | `2024` | `$e:expr` | `const { 1 + 2 }` | `1` | `error: no rules expected keyword const` (def-site edition governs!) |
| `cross_edition_def2024_call2021_const_block` | `2024` (`ed24_mac`) | `2021` | `$e:expr` | `const { 1 + 2 }` | `0` | `XED=3` (def-site edition governs!) |

For a verified Rust frontend or macro-expansion specification, the cross-edition test confirms a critical invariant: **macro matcher semantics are edition-hygienic at the macro definition span, not the caller's `--edition` flag**. Storing only a crate-global edition without per-span edition metadata miscompiles cross-edition macro invocations.

---

### 5. Default `recursion_limit = 128` Accounting and Enclosing Macro Frame Consumption

Basis: `source` + `execution` + `derived`

#### Exact Compiler Mechanism

1. **Default Value (`compiler/rustc_interface/src/limits.rs:55-62`):**
   ```rust
   fn get_recursion_limit(attrs: &[Attribute], sess: &Session) -> Limit {
       let limit_from_crate = find_attr!(attrs, RecursionLimit { limit } => limit.0).unwrap_or(128);
       Limit::new(
           sess.opts.unstable_opts.min_recursion_limit
               .map_or(limit_from_crate, |min| min.max(limit_from_crate)),
       )
   }
   ```
   `compiler/rustc_interface/src/passes.rs:204-208` injects `tcx.recursion_limit()` into `ExpansionConfig.recursion_limit` during real crate expansion. (By contrast, `ExpansionConfig::default` in `compiler/rustc_expand/src/expand.rs:2591-2600` initializes `Limit::new(1024)`, which is only a fallback for standalone/test drivers and does **not** govern normal `rustc` compilation.)
2. **Depth Increment and Limit Check (`compiler/rustc_expand/src/expand.rs:698-718, 2134-2144`):**
   - Root unexpanded AST starts at `current_expansion.depth = 0`.
   - Every collected nested invocation constructs `ExpansionData { depth: self.cx.current_expansion.depth + 1, .. }` (`expand.rs:2139`).
   - Before expanding any invocation, `MacroExpander::expand_invoc` (`expand.rs:708`) tests:
     ```rust
     if !recursion_limit.value_within_limit(self.cx.current_expansion.depth) {
         let guar = match self.cx.reduced_recursion_limit {
             Some((_, guar)) => guar,
             None => self.error_recursion_limit_reached(),
         };
         self.cx.reduced_recursion_limit = Some((recursion_limit / 2, guar));
         return ExpandResult::Ready(invoc.fragment_kind.dummy(invoc.span(), guar));
     }
     ```
     where `Limit(L).value_within_limit(d)` holds iff `d <= L`. On the first overflow, `rustc` emits `RecursionLimitReached` suggesting `limit * 2` (`256`), halves `reduced_recursion_limit` to prevent cascading expansion blowups, substitutes a dummy error fragment, and aborts immediately after macro expansion via `passes.rs:242-245` (`if ecx.reduced_recursion_limit.is_some() { sess.dcx().abort_if_errors(); }`).
3. **Closed-Form Depth Formula Explaining `125` vs. `126` (Nested) and `127` vs. `128` (Top-Level):**
   Consider the unary-counting macro:
   ```rust
   macro_rules! count {
       () => { 0usize };
       (+ $($rest:tt)*) => { 1 + count!($($rest)*) };
   }
   ```
   Expanding `count!` on $n$ `+` tokens creates $n + 1$ nested `count!` frames (the $n$ inductive arms plus the base arm `count!()`). If invoked inside $k$ enclosing macro frames (`outer_frames = k`), the base case `count!()` is checked at:
   $$\text{depth}_{\text{base}} = k + n + 1.$$
   Expansion succeeds if and only if $k + n + 1 \le L$:
   - **Top-level invocation** (`let v = count!(+^n);`): $k = 0 \implies n + 1 \le 128 \iff n \le 127$. Thus `n = 127` passes (`depth = 128`) and `n = 128` overflows (`depth = 129`).
   - **Nested inside `println!("...", count!(+^n))`**: `library/std/src/macros.rs:147-149` defines `println!($($arg:tt)*)` as `$crate::io::_print($crate::format_args_nl!($($arg)*))`, consuming **$k = 2$** outer macro expansion frames (`println!` at depth `1`, `format_args_nl!` at depth `2`, so the outer `count!` starts at depth `3`). Therefore $2 + n + 1 \le 128 \iff n \le 125$: `n = 125` passes (`depth = 128`) and `n = 126` overflows (`depth = 129`)!

#### Empirical Verification: `recursion_limit` Boundary Sweep (Part C4)

| Probe Case | Enclosing Macro Context (`k`) | `+` Tokens (`n`) | Base Depth (`k + n + 1`) | Limit (`L`) | `compile_rc` | Observed Output / Diagnostic |
| :--- | :--- | ---: | ---: | ---: | ---: | :--- |
| `recursion_nested_println_depth_124` | Inside `println!` (`k = 2`) | `124` | `127` | `128` | `0` | `REC=124:124` |
| `recursion_nested_println_depth_125` | Inside `println!` (`k = 2`) | `125` | `128` | `128` | `0` | `REC=125:125` |
| `recursion_nested_println_depth_126` | Inside `println!` (`k = 2`) | `126` | `129` | `128` | `1` | `error: recursion limit reached while expanding count!` (suggests `256`) |
| `recursion_nested_println_depth_127` | Inside `println!` (`k = 2`) | `127` | `130` | `128` | `1` | `error: recursion limit reached while expanding count!` |
| `recursion_toplevel_depth_125` | Top-level `let v = ...` (`k = 0`) | `125` | `126` | `128` | `0` | `REC_TOP=125:125` |
| `recursion_toplevel_depth_126` | Top-level `let v = ...` (`k = 0`) | `126` | `127` | `128` | `0` | `REC_TOP=126:126` |
| `recursion_toplevel_depth_127` | Top-level `let v = ...` (`k = 0`) | `127` | `128` | `128` | `0` | `REC_TOP=127:127` |
| `recursion_toplevel_depth_128` | Top-level `let v = ...` (`k = 0`) | `128` | `129` | `128` | `1` | `error: recursion limit reached while expanding count!` |
| `recursion_toplevel_depth_129` | Top-level `let v = ...` (`k = 0`) | `129` | `130` | `128` | `1` | `error: recursion limit reached while expanding count!` |
| `recursion_nested_println_depth_126_limit_256` | Inside `println!` (`k = 2`) | `126` | `129` | `256` | `0` | `REC_RAISED=126:126` |

---

### 6. Unsandboxed Host `proc_macro` Execution, `.o` Determinism Cliff, and Anneal's Trusted Boundary

Basis: `source` + `execution` + `derived`

#### Host Execution Model in `rustc_expand`

In `compiler/rustc_expand/src/proc_macro.rs` (`lines 16-88` at `342d74463`), `BangProcMacro::expand`, `AttrProcMacro::expand`, and `DeriveProcMacro::expand` invoke compiled native `proc_macro` shared libraries via `self.client.run1(&strategy, server, input, proc_macro_backtrace)` (or `run2`), where `exec_strategy` selects either same-thread or cross-thread execution (`MaybeCrossThread`) inside the host `rustc` OS process. No OS sandbox, syscall filter, environment scrubber, or filesystem confinement is applied by `rustc`: any `proc_macro` can execute arbitrary `std::env::var`, `std::fs`, `std::time`, `std::net`, or FFI syscalls during AST expansion.

#### Empirical Verification: Environment-Driven `.o` Divergence vs. Pure Invariance (Part D)

Using `pm_env` (`libpm_env.so`) exposing `emit_env_nonce!()` (reading `PROBE_BUILD_NONCE` into `#[unsafe(no_mangle)] pub extern "C" fn nonce() -> u64`) and `emit_pure_const!()` (emitting constant `0xCAFE_BABEu64`), compiling identical consumer `.rs` source with `--crate-type=lib --crate-name=det_probe --edition=2024 -C codegen-units=1 -C debuginfo=0 -C opt-level=2 --remap-path-prefix=<workdir>=/remap --emit=obj`:

| Run | Macro | `PROBE_BUILD_NONCE` | `rc` | `.o` Size (bytes) | `.o` SHA-256 Digest | Equality Result |
| :--- | :--- | :--- | ---: | ---: | :--- | :--- |
| `impure_run1_nonce_111111` | `emit_env_nonce!` | `111111` | `0` | `984` | `a1a4579654aea87214f770341140a4d4a243fdfcfdd45e9216587d50bc4c5602` | Baseline (`mov $0x1b207,%eax; ret`) |
| `impure_run2_nonce_111111` | `emit_env_nonce!` | `111111` | `0` | `984` | `a1a4579654aea87214f770341140a4d4a243fdfcfdd45e9216587d50bc4c5602` | **Bit-exact match** (`same_env_bit_exact = true`) |
| `impure_run3_nonce_222222` | `emit_env_nonce!` | `222222` | `0` | `984` | `83fde0ee05988105d6e2ecbe3b478462ac537b3ff8e3050353151fbb1244e391` | **Diverges** (`mov $0x3640e,%eax; ret`; `diff_env_breaks_reproducibility = true`) |
| `pure_run1_nonce_111111` | `emit_pure_const!` | `111111` | `0` | `984` | `1c64303330ec09bd1178dee691c0f6c731b7babbcf368fe37e788f63b25ef9f9` | Baseline (`0xCAFE_BABEu64`) |
| `pure_run2_nonce_222222` | `emit_pure_const!` | `222222` | `0` | `984` | `1c64303330ec09bd1178dee691c0f6c731b7babbcf368fe37e788f63b25ef9f9` | **Bit-exact invariant** (`pure_proc_macro_env_invariant = true`) |

#### Alignment with Anneal's Trusted Boundary (`joshlf/anneal@c131b320e`)

Direct inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` establishes three concrete architectural boundaries governing macro expansion and `proc_macro` execution:

1. **Host Build-Time Tampering Is Outside User-Space Automated Defense (`THREAT_MODEL.md:136-159`):** Anneal explicitly classifies build-time execution of Cargo `build.rs` scripts, procedural macros, compiler plugins, and Lean elaborator I/O as host-tampering vectors that no unsandboxed user-space tool can block; preventing such tampering requires OS-level sandboxing (for example, isolated CI runners or `bwrap` confinement as used by `anneal-audit` for Pass 2 Lean preflight in `TrustedBoundary.lean:58-63`).
2. **Repository Containment Forbids Rust Crates Outside `trusted/` (`docs/trust-model.md:104-113, 197-202`):** Because Rust code (including `build.rs` and `proc_macro` crates) is effectful and unchecked by the Lean kernel, `anneal-audit` pins `trusted/root-manifest.sha256` and rejects any Cargo workspace member or `path` dependency residing outside `trusted/`.
3. **Post-Expansion, Post-Analysis Capture Boundary (`trusted/rustc-capture/src/driver.rs:75-84, 137-150`; `docs/architecture.md:539-605`):** `anneal-rustc-capture` hooks `rustc_driver::Callbacks::after_analysis` and requires the full `rustc` session to complete without late errors (`tcx.dcx().has_errors().is_none()`). Macro expansion (`rustc_expand`), hygiene resolution (`rustc_resolve`), type checking, `TypePrivacyVisitor` (`rustc_privacy`), and `Runtime(PostCleanup)` MIR lowering therefore all execute **upstream** of Anneal's Lean capture boundary. Consequently:
   - Any Rust code *generated* by a `macro_rules!`, `decl_macro`, or `proc_macro` is verified downstream identically to hand-written code (`THREAT_MODEL.md:139-142`), and Anneal's Lean semantics (`Trusted/MirSemantics.lean`) do **not** need to model `SyntaxContext` hygiene or macro expansion to guarantee soundness of the captured MIR.
   - However, for **bit-exact reproducible builds** and **incremental proof caching** across machines or CI runs, an unsealed host-impure `proc_macro` invalidates source-hash-keyed caches whenever host state changes (`ce3_impure_proc_macro_breaks_build_determinism`). A verified compiler or proof-cache pipeline MUST either (a) sandbox `proc_macro` execution hermetically (scrubbing environment, clock, filesystem, and network) or (b) key verification and codegen certificates on the **sealed post-expansion IR/MIR digest** rather than pre-expansion `.rs` source hashes alone.

---

### 7. Kernel-Checked Lean 4.34.1 Formalization (`support/MacroHygieneAndTransparencySoundness.lean`)

Basis: `source` + `execution` + `derived`

The self-contained Lean `v4.34.1` module `support/MacroHygieneAndTransparencySoundness.lean` (944 lines, SHA-256 `3222acd956351b4c174b429dd458eb4c195560a85abcba8bbf194a583a4d204a`) formalizes the core mechanisms audited above and verifies 26 public theorems (18 headline theorems plus 8 supporting algebraic lemmas) through the standalone Lean 4.34.1 kernel with zero warnings (`-DwarningAsError=true`) and zero forbidden axioms or tactics.

#### Modeled Abstractions

- **Mark stacks & dual normalizers (Section 1):** `Transparency.{transparent, semiOpaque, opaque}`, `Mark`, `SyntaxContext := List Mark`, `applyMark`, `normalizeToMacros20`, `normalizeToMacroRules`, and `FreshIn`.
- **Two-pass identifier resolution and semantic type privacy (Section 2):** `IdentKind.{localVar, label, dollarCrate, itemFn, itemConst}`, `Visibility.{pubVis, privTo}`, `SemTy.{pubScalar, pubFnPtr, privFnDef, privAdt}`, `ResolveEnv`, `resolveIdent` (Pass 1), `resolveDollarCrateMember` (Pass 1 `$crate::member` dual normalization), `checkTypePrivacy` (Pass 2 hygiene-oblivious semantic type check), and `checkIdentTwoPass`.
- **Expansion fuel and `recursion_limit` (Section 4):** `ExpandOutcome`, `expandCountAt`, and `expandCount` enforcing `depth <= limit` at every expansion step.
- **Pure vs. host-impure expansion & compilation (Section 5):** `HostEnv`, `MacroExpanderFn`, `IsPureExpander`, `expandFuel`, and `compilePipeline`.
- **Edition 2021/2024 `NtExprKind` fragment matching (Section 5b):** `Edition`, `NtExprKind.{expr2024, expr2021}`, `resolveNtExprKind` (parameterized by definition-site edition), `ExprLeadToken`, and `exprMayBeginWith`.

#### Verified Theorem Inventory and `#print axioms` Audit

| Theorem / Lemma | Formal Statement Summary | Verified Axioms (`#print axioms`) |
| :--- | :--- | :--- |
| `normalizeToMacros20_idem` | `normalizeToMacros20 (normalizeToMacros20 c) = normalizeToMacros20 c` | `[propext]` |
| `normalizeToMacroRules_idem` | `normalizeToMacroRules (normalizeToMacroRules c) = normalizeToMacroRules c` | `[propext]` |
| `normalizeToMacros20_of_macroRules` | `normalizeToMacros20 (normalizeToMacroRules c) = normalizeToMacros20 c` | `[propext]` |
| `applyMark_semiOpaque_or_opaque_distinct_macroRules` | Fresh mark `e` with `t ∈ {semiOpaque, opaque}` yields distinct `normalizeToMacroRules` context | `[]` (none) |
| `semiOpaque_opaque_avoid_local_and_label_capture` | **Theorem 1:** Under `t ∈ {semiOpaque, opaque}` and `k ∈ {localVar, label}`, prepending a macro binder leaves caller lookup invariant (alpha-equivalence) and macro refs never capture caller ribs (`E0425`) | `[propext]` |
| `semiOpaque_resolves_item_at_callsite_vs_opaque_at_defsite` | **Theorem 2:** For `k ∈ {itemFn, itemConst}`, `semiOpaque` resolves & privacy-checks at `callSiteMod`, whereas `opaque` resolves & privacy-checks at `expnDefMod e` | `[]` (none) |
| `opaque_priv_const_passes_while_priv_fn_rejected_by_type_privacy` | **Theorem 3:** When `defMod ≠ callMod`, under `opaque` both private `const` (`pubScalar`) and private `fn` (`privFnDef`) pass Pass 1, then Pass 2 accepts `const` and rejects `fn` with `privateTypePrivacy`, while `semiOpaque` `$crate::fn` fails in Pass 1 with `E0603` | `[]` (none) |
| `opaque_priv_fnptr_const_passes_two_pass` | Private `const` of `SemTy.pubFnPtr` passes both Pass 1 and Pass 2 under `opaque` hygiene | `[]` (none) |
| `expandCountAt_ok_iff` / `count_expansion_succeeds_iff` | `expandCount limit outerFrames n = .ok n ↔ outerFrames + 1 + n ≤ limit` | `[propext]` |
| `expandCountAt_overflow_exact` | Whenever `depth ≤ limit + 1` and `limit < depth + n`, overflows at exact depth `limit + 1` | `[propext]` |
| `count_nested_println_125_passes_126_overflows` | `expandCount 128 2 125 = .ok 125 ∧ expandCount 128 2 126 = .recursionLimitReached 129` | `[propext]` |
| `count_toplevel_127_passes_128_overflows` | `expandCount 128 0 127 = .ok 127 ∧ expandCount 128 0 128 = .recursionLimitReached 129` | `[propext]` |
| `pure_macro_expansion_deterministic` | **Theorem 4:** For any `IsPureExpander f` and deterministic `backend`, `expandFuel` and `compilePipeline` yield identical outputs across arbitrary `HostEnv`s | `[]` (none) |
| `edition2024_expr_strict_superset_of_expr2021` | `Expr2024` accepts every `Expr2021` leading token plus `kwConst` and `kwUnderscore`, whereas `expr_2021` rejects both even in Edition 2024 | `[propext]` |
| `ce1_transparent_call_site_captures_caller_local` | **Counterexample 1:** `Transparent` (`Span::call_site()`) resolves caller local `target = 77` while `SemiOpaque` and `Opaque` reject with `E0425` | `[]` (none) |
| `ce2_semi_opaque_item_hijacked_by_caller_shadow` | **Counterexample 2:** `SemiOpaque` resolves `helper` to caller shadow (`999`) while `Opaque` resolves to def-site (`10`, `10 ≠ 999`) | `[]` (none) |
| `ce3_impure_proc_macro_breaks_build_determinism` | **Counterexample 3:** `HostEnv.envNonce`-reading `proc_macro` is `¬ IsPureExpander` and produces divergent `compilePipeline` artifacts across `env1` (`111111`) vs. `env2` (`222222`) | `[propext]` |

Every theorem uses `0` `sorryAx`, `0` `Classical.choice`, `0` `Quot.sound`, `0` `Lean.ofReduceBool`, `0` `Lean.ofReduceNat`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, and `0` `._unsafe_rec`.

## Boundaries

### Negative-Space Classification

- **`not examined`:**
  - `#[macro_export(local_inner_macros)]` `$crate` prepending (`compiler/rustc_resolve/src/macros.rs:812-820`) combined with nested `decl_macro` expansions.
  - Wildcard glob-import hygiene (`SyntaxContext::glob_adjust` and `reverse_glob_adjust` in `compiler/rustc_span/src/hygiene.rs:971-1017`) and `derive_fallback_lint_id` compatibility paths (`rustc_resolve/src/ident.rs:259-270`).
  - Attribute and derive procedural macros (`#[proc_macro_attribute]`, `#[proc_macro_derive]`), helper attributes, and `-Z cache-proc-macros` / `-C incremental` caching (`EXPAND_DERIVE_MACRO_CACHED` in `compiler/rustc_expand/src/proc_macro.rs:113-119`).
  - Alternative execution strategies such as `-Z proc-macro-execution-strategy=cross-thread` or external WebAssembly proc-macro sandboxes (e.g., `watt`-style runners).
  - Pre-2021 `$p:pat` vs. `$p:pat_param` (`NtPatKind` in `compiler/rustc_ast/src/token.rs:1127-1134, 1177-1184`) and macro follow-set ambiguity rules (`rustc_expand/src/mbe/macro_parser.rs`).
  - Method-call and associated-item type privacy in `TypePrivacyVisitor::visit_expr` (`ExprKind::MethodCall`, `rustc_privacy/src/lib.rs:1238-1256`) and `visit_qpath` for private associated constants/types/functions (`DefKind::{AssocFn, AssocConst, AssocTy}`).
  - Non-`x86_64-unknown-linux-gnu` hosts or cross-compilation targets for `.o` reproducibility.
- **`unknown`:**
  - Whether or when upstream Rust will stabilize `#![feature(decl_macro)]` or `#![feature(proc_macro_def_site)]`, and whether future macros-2.0 reachability analysis will relax either the `TypePrivacyVisitor` `FnDef` rejection or the cross-crate private-static rejection noted in `compiler/rustc_privacy/src/lib.rs:1265-1268`.
  - Whether future `rustc_resolve` changes will replace the mixed `macro_rules!`/`decl_macro` `$crate` mark-scanning heuristic documented as a `FIXME` at `compiler/rustc_resolve/src/lib.rs:2382-2384`.
- **`known not to apply`:**
  - `Opaque` (`decl_macro`) hygiene **does not** grant access to private functions (`FnDef`), private ADTs (`struct`/`enum`), or cross-crate private `static` items: `rustc_privacy::TypePrivacyVisitor` intentionally ignores `SyntaxContext` hygiene (`lib.rs:1122`).
  - `SemiOpaque` (`macro_rules!` and `Span::mixed_site()`) **does not** protect unqualified items against caller shadowing (`ITEM_CALLSITE=999`, `ce2_semi_opaque_item_hijacked_by_caller_shadow`), nor does it isolate lifetime parameters (`late.rs:1943`).
  - Compiling a downstream crate with `--edition=2024` **does not** enable `const { ... }` or `_` matching for `$e:expr` inside macros defined in an Edition 2021 upstream crate (`cross_edition_def2021_call2024_const_block` fails with `rc = 1`).
  - `ExpansionConfig::default`'s `Limit::new(1024)` (`expand.rs:2596`) **does not** apply to standard `rustc` crate compilation, which overrides it with `128` (`limits.rs:56`, `passes.rs:204`).
  - Running `rustc --emit=obj -o out.o` with `-C opt-level=2` and default `codegen-units=16` **does not** reliably capture single-function object-byte divergence unless `-C codegen-units=1` is passed.
  - Anneal's Lean kernel checks and `TrustedBoundary.lean` **do not** defend against a malicious or non-deterministic `proc_macro` tampering with the host OS during `cargo build`; OS-level sandboxing is required (`THREAT_MODEL.md:144-159`).
- **`unsupported`:**
  - `decl_macro` (`pub macro`) and `proc_macro::Span::def_site()` are unsupported on stable `rustc` without nightly feature flags (`#![feature(decl_macro)]`, `#![feature(proc_macro_def_site)]`).
  - Hermetic in-compiler sandboxing of native `proc_macro` dylibs is unsupported in stock `rustc` (`compiler/rustc_expand/src/proc_macro.rs` loads and runs native host code directly).

### Attractive Stronger Conclusions Not Established

- **Not a proof of `rustc` implementation correctness:** `support/MacroHygieneAndTransparencySoundness.lean` proves properties of an abstract formal model of `SyntaxContext` stacks, dual normalization, two-pass resolution/privacy, fuel limits, and pure expansion; it does not prove that `rustc`'s Rust source code (`HygieneData::apply_mark` legacy grafting, glob adjustment, or `rustc_privacy` visitors) faithfully refines that model without bugs.
- **Not a complete `proc_macro` determinism proof across all `rustc` flags:** Confirming bit-exact `984`-byte `.o` files for `pm_env::emit_pure_const!` under `-C codegen-units=1 -C debuginfo=0 --remap-path-prefix` demonstrates isolation of the `PROBE_BUILD_NONCE` vector, not that arbitrary Rust crates are reproducible across differing LLVM versions, target triples, or unremapped debug paths.
- **Not a claim that `const HELPER_PTR: fn() -> u32 = helper` works cross-crate:** Intra-crate `FnPtr` coercion bypasses `TypePrivacyVisitor` (`OPAQUE_PRIV_FNPTR=10`), but cross-crate it fails at upstream `.rlib` MIR availability (`missing optimized MIR for up_mac::secret_helper in the crate up_mac`), showing that private-item encapsulation across crates also depends on upstream reachability/MIR-export metadata.

## Evidence

### 1. Upstream Primary-Source Audit Table

All 40-hex commit SHAs were resolved live via GitHub API on `2026-11-22`:

| Repository & Pinned 40-Hex Commit | Path | Line Range(s) & Key Symbols | Role |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_span/src/hygiene.rs` | `L178-200` (`Transparency`, `fallback`), `L598-641` (`normalize_to_macros_2_0`, `normalize_to_macro_rules`, `marks`), `L680-782` (`adjust`, `apply_mark`, `alloc_ctxt`), `L900-1043` (`SyntaxContext::adjust`, `normalize_to_macros_2_0_and_adjust`) | `source` |
| `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_span/src/hygiene.rs` | `L165-187` (`Transparency`, `fallback`), matching executed `rustc 1.98.0-nightly` | `source` |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_span/src/lib.rs` | `L1294-1315` (`with_def_site_ctxt`, `with_call_site_ctxt`, `with_mixed_site_ctxt`, `with_ctxt_from_mark`) | `source` |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_expand/src/base.rs` | `L1280-1295` (`ExtCtxt::with_{def,call,mixed}_site_ctxt`) | `source` |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_expand/src/proc_macro_server.rs` | `L457-499` (`Rustc::new`, `ExpnGlobals::{def_site, call_site, mixed_site}`) | `source` |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_expand/src/proc_macro.rs` | `L16-88` (`exec_strategy`, `BangProcMacro::expand`, `AttrProcMacro::expand`), `L94-157` (`DeriveProcMacro`) | `source` |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_resolve/src/ident.rs` | `L244-254` (`hygienic_lexical_parent`), `L309-390` (`resolve_ident_in_lexical_scope`), `L1019-1030` (`IdentKey::new_adjusted` privacy scope) | `source` |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_resolve/src/late.rs` | `L1943, L2028` (lifetime `normalize_to_macros_2_0`), `L2887` (label `normalize_to_macro_rules`) | `source` |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_resolve/src/lib.rs` | `L612-627` (`IdentKey::new`, `new_adjusted`), `L2375-2410` (`resolve_crate_root` `$crate` mark scan), `L3130-3143` (`Macros20NormalizedSyntaxContext`) | `source` |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_privacy/src/lib.rs` | `L185-205` (`ty::FnDef`/`ty::Adt` def-id walk), `L1119-1171` (`TypePrivacyVisitor`, `item_is_accessible`, `check_def_id`), `L1226-1310` (`visit_expr`, `visit_qpath`, `is_local_static`) | `source` |
| `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_privacy/src/lib.rs` | `L1126` (`TypePrivacyVisitor`), `L1261` (`visit_qpath`), matching executed `rustc 1.98.0-nightly` | `source` |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_ast/src/token.rs` | `L106-107` (`MetaVarKind` `Display`), `L1136-1225` (`NtExprKind`, `NonterminalKind::from_symbol`) | `source` |
| `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_ast/src/token.rs` | `L1103-1170` (`NtExprKind`, `NonterminalKind`), matching executed `rustc 1.98.0-nightly` | `source` |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_parse/src/parser/nonterminal.rs` | `L43-64` (`Parser::nonterminal_may_begin_with` for `Expr2021` vs. `Expr`) | `source` |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_interface/src/limits.rs` | `L55-62` (`get_recursion_limit` `.unwrap_or(128)`) | `source` |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_interface/src/passes.rs` | `L204-208` (`ExpansionConfig.recursion_limit`), `L242-245` (`reduced_recursion_limit` abort) | `source` |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_expand/src/expand.rs` | `L666-718` (`error_recursion_limit_reached`, `expand_invoc`, `value_within_limit`), `L2134-2144` (`depth + 1`), `L2591-2600` (`ExpansionConfig::default` `1024`) | `source` |
| `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_expand/src/expand.rs` | `L702` (`expand_invoc`), matching executed `rustc 1.98.0-nightly` | `source` |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `library/std/src/macros.rs` | `L143-150` (`macro_rules! println` -> `$crate::format_args_nl!`, 2 outer macro frames) | `source` |
| `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `THREAT_MODEL.md` | `L136-159` (`build.rs` and `proc_macro` host tampering boundary vs. generated-code verification) | `documentation` + `source` |
| `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `docs/trust-model.md` | `L78-118`, `L195-203` (Cargo workspace containment under `trusted/` due to effectful `build.rs`/`proc_macro`) | `documentation` + `source` |
| `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `docs/architecture.md` | `L533-605` (`Runtime(PostCleanup)` MIR extraction, Cargo flag fidelity, late PME/layout checks) | `documentation` + `source` |
| `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/rustc-capture/src/driver.rs` | `L25`, `L75-84`, `L137-150` (`Callbacks::after_analysis`, full session completion gate) | `source` |
| `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/audit/TrustedBoundary.lean` | `L16-65` (Lean `v4.34.1` `5045d0056413266e57c625dcd7c365b10e377c52` pin, `bwrap` sandbox for effectful compile-time extensions) | `source` |

### 2. Preserved Package Support Artifacts

All preserved artifacts live under `support/` in this package and are scrubbed of host-local paths:

| Artifact Path | Purpose | Lines | Size (bytes) | SHA-256 Digest |
| :--- | :--- | ---: | ---: | :--- |
| `support/probe_macro_hygiene.py` | Standalone Python 3.10+ stdlib probe compiling and executing all 44 empirical `rustc` cases across Parts A–D (plus 5 supporting `proc-macro`/`rlib` builds) | `794` | `27,394` | `159ed5d8147e57fa7bd8eddda272347bb81bce48678df0e8504423f39f94a74d` |
| `support/probe_macro_hygiene_results.json` | Recorded execution output from `rustc 1.98.0-nightly (14210df0e 2026-05-31)` on `2026-11-22` | `245` | `17,940` | `1460e3c84dcd512c5b990d95e90f51fce2e1319b695ea38fc2e6284500120d5` |
| `support/MacroHygieneAndTransparencySoundness.lean` | Kernel-checked Lean `v4.34.1` formalization (26 public theorems, `0` `sorry`, `0` `Classical.choice`, `0` `Lean.ofReduceBool`) | `944` | `42,485` | `3222acd956351b4c174b429dd458eb4c195560a85abcba8bbf194a583a4d204a` |

### 3. Execution Receipts (`2026-11-22`)

1. **`rustc` Probe Execution (`exit 0`):**
   - Environment: `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `LLVM version: 22.1.6`, `host: x86_64-unknown-linux-gnu`, `Python 3.13.15`.
   - Command: `python3 support/probe_macro_hygiene.py --out support/probe_macro_hygiene_results.json`.
   - Result: Exit `0`; all 12 Part A test cases (plus `libpm_hyg.so` build), 8 Part B cross-crate cases (plus `libup_mac.rlib` build), 19 Part C edition and recursion-limit cases (plus 2 cross-edition upstream `rlib`s), and 5 Part D `.o` builds (plus `libpm_env.so` build) matched expected verdicts (`same_env_bit_exact: true`, `diff_env_breaks_reproducibility: true`, `pure_proc_macro_env_invariant: true`).
2. **Lean `v4.34.1` Strict Kernel Check (`exit 0`):**
   - Toolchain: `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`.
   - Command:
     ```bash
     lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
       support/MacroHygieneAndTransparencySoundness.lean
     ```
   - Result: Exit `0`, `0` errors, `0` warnings.
3. **Lean `#print axioms` Audit (`exit 0`):**
   - Appended `#print axioms` for all 18 exported theorems in a temporary copy outside the package and checked with `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false`.
   - Result: Exit `0`; 7 theorems depend on `[]` (no axioms), 11 theorems depend exclusively on `[propext]`, and `0` theorems depend on `sorryAx`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`, or `Lean.ofReduceNat`.

## Revalidation

To cheaply determine whether these findings still hold on a newer `rustc` toolchain, a newer `joshlf/anneal` revision, or a newer Lean 4 release, execute these narrow discriminating checks rather than repeating the full audit:

1. **Re-run the Empirical `rustc` Matrix (~10–15 seconds):**
   ```bash
   python3 support/probe_macro_hygiene.py --out /tmp/reval_macro_hygiene.json
   ```
   Verify all four behavioral invariants on the target nightly `rustc`:
   - Part A: `macro_rules_semi_opaque` prints `LOCAL_HYG=(100,7) ITEM_CALLSITE=999 LABEL_HYG=42 LABEL_BIDIR=99`; `proc_macro_call_site_captures_local` prints `PM_CALL=77`; `proc_macro_mixed_site_isolates_local` and `proc_macro_def_site_isolates_local` fail with `E0425`; `proc_macro_mixed_site_resolves_item_at_callsite` prints `PM_MIXED_ITEM=321 CALLER_X=77`; `proc_macro_def_site_isolates_callsite_item` fails with `E0425`.
   - Parts A2 & B: `decl_macro_opaque_priv_const_ok` (`777`), `decl_macro_opaque_priv_static_ok` (`888`), `decl_macro_opaque_priv_fn_via_fnptr_const_ok` (`10`), and `decl_macro_upstream_priv_const_ok` (`505`) exit `0`; `decl_macro_opaque_priv_fn_rejected` and `decl_macro_upstream_priv_fn_rejected` fail with `type fn() -> u32 {...} is private` (without `E0603`); `decl_macro_upstream_priv_static_rejected` fails with `static up_mac::UPSTREAM_SECRET_STATIC is private`; `macro_rules_dollar_crate_priv_{fn,const}_rejected` fail with `E0603`. If `decl_macro_opaque_priv_fn_rejected` or `decl_macro_upstream_priv_static_rejected` starts passing, re-inspect `compiler/rustc_privacy/src/lib.rs` (`TypePrivacyVisitor`) for a macros-2.0 reachability change.
   - Part C: `ed2021_expr_{const_block,underscore}`, `ed2024_expr_2021_rejects_{const_block,underscore}`, and `cross_edition_def2021_call2024_const_block` exit `1`, while `ed2024_expr_{const_block,underscore}` and `cross_edition_def2024_call2021_const_block` exit `0`; nested-in-`println!` `count!` passes at `125` and overflows at `126`, while top-level `count!` passes at `127` and overflows at `128`. If `125`/`126` shifts while `127`/`128` holds, inspect `library/std/src/macros.rs` for a change in `println!`'s macro nesting depth.
   - Part D: `same_env_bit_exact`, `diff_env_breaks_reproducibility`, and `pure_proc_macro_env_invariant` all remain `true`. If `diff_env_breaks_reproducibility` becomes `false`, check whether `rustc` introduced an opt-in or default `proc_macro` environment scrubber.
2. **Diff the Seven Load-Bearing Upstream `rust-lang/rust` Files:**
   ```bash
   git diff 342d74463af7dd3018ef6aa04dd5500c2deb5bd1..HEAD -- \
     compiler/rustc_span/src/hygiene.rs \
     compiler/rustc_resolve/src/ident.rs \
     compiler/rustc_privacy/src/lib.rs \
     compiler/rustc_ast/src/token.rs \
     compiler/rustc_parse/src/parser/nonterminal.rs \
     compiler/rustc_expand/src/expand.rs \
     compiler/rustc_interface/src/limits.rs
   ```
   A zero-diff across `Transparency`, `SyntaxContextData::alloc_ctxt`, `IdentKey::new_adjusted`, `TypePrivacyVisitor`, `NtExprKind`, `nonterminal_may_begin_with`, `get_recursion_limit`, and `expand_invoc` preserves every source-derived finding without rerunning full source analysis.
3. **Re-verify the Lean 4 Formalization and Axiom Envelope (~5 seconds):**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/MacroHygieneAndTransparencySoundness.lean
   ```
   Follow with a temporary `#print axioms` check confirming zero `sorryAx`, `Classical.choice`, `Quot.sound`, or `Lean.ofReduceBool`.
4. **Re-check Anneal's Capture and Sandbox Boundary:**
   Diff `joshlf/anneal` from `c131b320eeeb26ef692e5afd5ec8db49ee518613` across `THREAT_MODEL.md`, `docs/trust-model.md`, and `trusted/rustc-capture/src/driver.rs` whenever `anneal-rustc-capture` transitions from its analysis-callback gate to full MIR extraction or adds OS-level sandboxing around Cargo/proc-macro invocations.
