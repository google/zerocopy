# rustc `#![forbid(unsafe_code)]`: the `--cap-lints` ceiling, the foreign-macro span filter, Edition 2024 unsafe markers, and `#[expect]`

## Summary

`unsafe_code` is an ordinary allow-by-default lint, and `forbid` is an ordinary
lint level. In `rustc 1.98.0-nightly (14210df0e 2026-05-31)` a crate that says
`#![forbid(unsafe_code)]`, or is compiled with `-F unsafe_code`, compiles
successfully while containing and executing `unsafe` code in each of these
situations (with no diagnostic at all in the first two), all observed by
execution and traced to source:

- **`--cap-lints allow` anywhere on the command line.** The effective level of
  every lint is `min(level, cap)`, computed after all attributes and flags have
  been combined. The cap is stored separately from the ordered `-A/-W/-D/-F`
  list, so flag order is irrelevant. It lowers an attribute `forbid` and a
  command-line `-F` alike, and it also removes the E0453 error for an inner
  `#[allow]`, because that error is raised only when the *capped* outer level
  is still `forbid`. Cargo passes `--cap-lints allow` (`warn` under `-vv`) for
  every dependency that is not a path dependency.
- **The `unsafe` token comes from a macro defined in another crate.** The lint
  emitter drops a lint whose span is "in an external macro" unless the lint
  opts in (`unsafe_code` does not). The test looks only at the most deeply
  nested expansion of the span. A foreign `macro_rules!` body, and a foreign
  procedural macro using `Span::call_site()`, `Span::mixed_site()` or
  `Span::def_site()`, attribute macros and derive macros included, all
  qualify. A procedural macro that re-uses a span from its *input* does not.
- **`--force-warn unsafe_code`.** A command-line force-warn is exempt from the
  cap and cannot be raised by a later `#![forbid]`; the crate compiles with a
  warning.
- **`--cap-lints deny`.** The outer level is revealed as `deny`, so an inner
  `#[allow(unsafe_code)]` is accepted.

The apparent paradox that a foreign macro emitting bare `unsafe { .. }` passes
while one emitting `#[allow(unsafe_code)] unsafe { .. }` fails with E0453 has a
single cause: E0453 is a hard error raised by the lint-level builder for every
attribute in the expanded syntax tree, whereas the `unsafe_code` diagnostic is
a lint routed through the emitter that applies the external-macro filter.

The Edition 2024 requirements do not close these gaps. `unsafe_op_in_unsafe_fn`
(warn in 2024) and `static_mut_refs` (deny in 2024, **a lint, not a hard
error**) are capped and allowable like any lint. The hard errors for a bare
`#[no_mangle]` and a bare `extern "C"` block are keyed on the edition of the
*span*, so a macro defined in an Edition 2021 crate still injects both into an
Edition 2024 `#![forbid(unsafe_code)]` crate with no diagnostic.

`#[expect(L)]` sets level `expect`, which sits between `allow` and `warn`;
under `--cap-lints allow` it becomes `allow`, and the warn-by-default
`unfulfilled_lint_expectations` lint is capped too. An expectation is not
fulfilled by a lint that the external-macro filter dropped.

What does survive every one of these configurations is the compiled body: MIR
emitted for a `#![forbid(unsafe_code)]` crate whose raw-pointer dereference was
written by a foreign macro, or silenced by the cap, contains the dereference.
`unsafe_code` is a property of spelling and provenance; whether a crate
performs unsafe operations has to be read from the post-expansion body.

A small Lean 4 model of the level algebra, the nesting rule, the provenance
predicate and a span-erasing lowering is included. It proves the ceiling
property, proves that `forbid` *is* sound in the model when nothing caps the
lint and every `unsafe` block is local, and exhibits each escape above as a
closed, kernel-checked counterexample. The model's theorems are about the
model; its correspondence to the compiler rests on the source reading and the
execution results recorded here.

## Applicability

**What was examined, and how.**

| Subject | Role in this report |
|---|---|
| `rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | The compiler that was **executed** (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, host `x86_64-unknown-linux-gnu`, LLVM 22.1.6) and whose **source** was read. Every source line number below refers to this commit unless stated otherwise. |
| `rust-lang/rust` at `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` | **Source only.** This is the compiler commit that Anneal's capture driver requires at the Anneal commit below. Twenty-three audited files were compared with the executed commit: twenty-two are byte-identical and one (`compiler/rustc_lint_defs/src/builtin.rs`) differs only in documentation-comment lines of an unrelated lint. Nothing was executed on this commit. |
| `rust-lang/cargo` at `fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef` | **Executed** (`cargo 1.98.0-nightly (fbb61be30 2026-05-26)`) and **source** read, for the rule that decides which units get `--cap-lints`. |
| `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` | **Source only**: `trusted/rustc-capture`, `THREAT_MODEL.md`, `trusted/lean/Trusted/MirAst.lean`. The capture driver was not built or run. |
| `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (v4.34.1) | The proof checker that was **executed** on the model. |
| `rust-lang/rfcs` at `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` | RFC 1193 (`--cap-lints`) and RFC 2383 (`expect`), read as design **documentation**. |
| `rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | Lint attribute rules, **documentation**. |
| `rust-lang/edition-guide` at `ab8544aeed7b792984366aa122ac19bd47ad9a2f` | Edition 2024 pages, **documentation**. |

No source consulted here is normative for lint levels: the Reference describes
them and defers the lint list to the compiler. Where documentation and
implementation disagree, both are reported.

**Scope of the execution results.** All runs used the single toolchain above
on `x86_64-unknown-linux-gnu`, crates compiled directly with `rustc`
(`--edition 2021` or `2024` as stated per case), plus two `cargo build -v`
runs. The foreign crates in the probe are built from source files in the same
temporary directory as the crates that use them; "foreign" therefore means
"another crate", not "third-party code". One case uses the unstable
`Span::def_site()` and three use `--emit=mir`; the rest use stable features
only, but were run only on this nightly.

**Extension beyond what was executed.** The findings are claimed for
`f8a08b688` by source identity of the determining code (derived, not
executed). They are not claimed for any other compiler version; see
Boundaries for what is known about a later commit. Target, optimisation level
and codegen backend do not enter any of the audited code paths, which all run
before code generation; that these do not matter is derived from source, not
tested.

**Scope of the Lean model.** One lint (`unsafe_code` or a lint with the same
metadata) at a time; one safe function body after expansion; lint groups
other than `warnings` absent. The model is authored for this report and is not
part of any upstream project.

## Findings

### 1. Levels are a six-element chain and the effective level is computed late

`rustc_lint_defs::Level` is declared as

```rust
#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Debug, Hash, Encodable, Decodable, StableHash)]
pub enum Level { Allow, Expect, Warn, ForceWarn, Deny, Forbid }
```

so the derived order is `Allow < Expect < Warn < ForceWarn < Deny < Forbid`
(`compiler/rustc_lint_defs/src/lib.rs` L151-185). `Level::from_str`, used for
`--cap-lints`, accepts only `allow`, `warn`, `deny`, `forbid` (L202-210);
`--cap-lints expect` is rejected with ``error: unknown lint level: `expect` ``
(execution).

A lint's level at a syntax node is stored as a raw `LevelSpec { level, src }`
where `src` is `Default`, `Node { .. }` (an attribute) or
`CommandLine(name, flag_level)`
(`compiler/rustc_middle/src/lint.rs` L19-37, L58-75). The raw spec is found by
walking attribute scopes outwards to the command line. It is turned into the
level used for diagnostics by `reveal_actual_level_spec` (L138-195), in this
order:

1. no raw spec: use `lint.default_level(edition)` with source `Default`;
2. if the level is exactly `Warn`, a configured `warnings` level may replace
   the whole spec (`-A warnings`, `-D warnings`, ...; a `ForceWarn` there is a
   delayed bug);
3. the cap:

   ```rust
   // Ensure that we never exceed the `--cap-lints` argument unless the source is a --force-warn
   if !matches!(level_spec.src, LintLevelSource::CommandLine(_, Level::ForceWarn)) {
       level_spec.level = min(level_spec.level, sess.opts.lint_cap.unwrap_or(Level::Forbid));
   };
   ```
4. a per-lint driver cap (`sess.driver_lint_caps`), applied with `min` to every
   source including force-warn.

Basis: source.

### 2. `--cap-lints` is a ceiling over attribute `forbid` and over `-F`, in any flag order

Because step 3 runs after the raw spec has been chosen, it does not matter
whether `Forbid` came from `#![forbid(unsafe_code)]` (source `Node`) or from
`-F unsafe_code` (source `CommandLine(_, Forbid)`): both are replaced by
`min(Forbid, cap)`. With `--cap-lints allow` the level is `Allow` and, for a
lint without future-breakage reporting such as `unsafe_code`, `emit_lint_base`
returns at its first `match` arm (L417-424).

Flag order cannot matter because the two kinds of flag are parsed into
different fields. `get_cmd_lint_options`
(`compiler/rustc_session/src/config.rs` L1892-1922) collects the
`-A/-W/--force-warn/-D/-F` occurrences, sorts them by argument position into
`lint_opts`, and separately reads

```rust
let lint_cap = matches.opt_str("cap-lints").map(|cap| { lint::Level::from_str(&cap)... });
```

`cap-lints` is declared as a repeatable option (L1812-1819). Which occurrence
`opt_str` returns is not visible in the audited source; execution shows it is
the first: `--cap-lints allow --cap-lints forbid` compiles the forbidden crate
silently and the reverse order rejects it.

| Observation (all on a crate whose only `unsafe` is `unsafe { 42u32 }`) | Result |
|---|---|
| `#![forbid(unsafe_code)]`, no flags | ``error: usage of an `unsafe` block``, exit 1 |
| `#![forbid(unsafe_code)]`, `--cap-lints allow` | no output, exit 0, program prints `UNSAFE_RAN=42` |
| `#![forbid(unsafe_code)]`, `--cap-lints warn` | ``warning: usage of an `unsafe` block``, exit 0, program runs |
| no attribute, `-F unsafe_code` | error, with the note ``requested on the command line with `-F unsafe-code` `` |
| no attribute, `--cap-lints allow -F unsafe_code` | no output, exit 0, program runs |
| no attribute, `-F unsafe_code --cap-lints allow` | no output, exit 0, program runs |
| attribute and `-F unsafe_code --cap-lints allow` | no output, exit 0, program runs |
| `#![forbid(unsafe_code)]`, `--cap-lints deny` | error (level is `deny`), exit 1 |

Two refinements, both from source and both confirmed by execution:

- **Force-warn is the one exemption.** `--force-warn unsafe_code --cap-lints
  allow` still prints ``warning: usage of an `unsafe` block``. RFC 1193 describes
  the cap as something that "cannot be overridden by other flags or
  attributes" and does not mention force-warn; the rustc book at the audited
  commit records the exception ("`--cap-lints allow` does **not** override
  lints marked as `force-warn`"). The RFC text and the implementation
  disagree on this point, and the book sides with the implementation.
- **Force-warn also beats a later `forbid` attribute.** `add_command_line`
  skips a flag when the current command-line spec is already `ForceWarn` or
  `Forbid` ("ForceWarn and Forbid cannot be overridden",
  `compiler/rustc_lint/src/levels.rs` L551-557), and `insert_spec` keeps
  `ForceWarn` when an attribute arrives on top of it (L656-664). So
  `--force-warn unsafe_code` on a `#![forbid(unsafe_code)]` crate yields a
  warning and exit 0, and `-F unsafe_code -A unsafe_code` stays an error.

Basis: source + execution; RFC 1193 and the rustc book as documentation.

### 3. `forbid` resists inner attributes only while it is still revealed as `forbid`

Attributes are processed by `LintLevelsBuilder::insert_spec`
(`compiler/rustc_lint/src/levels.rs` L567-668). It first asks for the
*revealed* level of the enclosing scope (`old_level`, which already includes
the cap), then:

```rust
if self.lint_added_lints && level == Level::Deny && old_level == Level::Forbid {
    // Having a deny inside a forbid is fine and is ignored, so we skip this check.
    return;
} else if self.lint_added_lints && level != Level::Forbid && old_level == Level::Forbid {
    ... // E0453 (`OverruledAttribute`) via `self.sess.dcx().emit_err(..)`, then `return`
}
...
match (old_level, level) {
    (Level::ForceWarn, Level::Expect) => /* keep ForceWarn, remember the expectation */,
    (Level::ForceWarn, _) => /* keep ForceWarn */,
    _ => /* insert the new level */,
};
```

The source comment states the consequence directly: "Note that this is not
necessarily true even with a `#[forbid(..)]` attribute present, as that is
overridden by `--cap-lints`. This means that this only errors if we're truly
lowering the lint level from forbid."

Consequences, each observed:

| Crate text | Flags | Result |
|---|---|---|
| `#![forbid(unsafe_code)]` + `#[allow(unsafe_code)] fn main() { unsafe {..} }` | none | E0453 **and** the `unsafe` block error (forbid is retained) |
| same | `--cap-lints allow` | no output, exit 0 |
| same | `--cap-lints deny` | exit 0; no E0453, no `unsafe_code` diagnostic (outer level is `deny`, inner `allow` accepted) |
| `#![forbid(unsafe_code)]` + `#[deny(unsafe_code)]` item | none | no E0453; the `unsafe` block is an error |
| `#![forbid(unsafe_code)]` + `#[expect(unsafe_code)]` item | none | `error[E0453]: expect(unsafe_code) incompatible with previous forbid` |
| `#![allow(unsafe_code)]` | `-F unsafe_code` | E0453 with note "`forbid` lint level was set on command line" |

Two further facts from the same function:

- **`lint_added_lints` gates the check.** The builder used by the
  post-expansion AST lint pass is created with `lint_added_lints =
  !pre_expansion` (`compiler/rustc_lint/src/early.rs` L312-328, called with
  `false` for `pre_expansion` from `early_lint_checks`,
  `compiler/rustc_interface/src/passes.rs` L469-476), so E0453 is raised there.
  The per-owner HIR query `shallow_lint_levels_on` builds with
  `lint_added_lints: false` (`levels.rs` L158-175), so there both guarded
  branches are skipped and the inner level is recorded. Derived, not executed:
  a lint that reads its level through that query would see the inner level,
  while the compilation has already been failed by the AST pass's E0453.
- **A `forbid` set through a lint group is not sticky.** When the old source
  names a lint group, the code emits the `forbidden_lint_groups`
  future-compatibility lint instead of E0453 and then *does* apply the inner
  level (L595-599, L626-645). Observed on `#![forbid(unused)]` +
  `#[allow(unused_variables)]`: a warning, exit 0, and no unused-variable
  diagnostic. `unsafe_code` is not reached by this path at the audited commit:
  `rustc -W help` lists it with default `allow` and in no lint group, and no
  `add_lint_group!` call in `compiler/rustc_lint/src/lib.rs` names it.

The Reference describes the nesting rule without the cap: "`#[forbid(C)]` is
the same as `deny(C)`, but also forbids changing the lint level afterwards"
and "except for `deny`, which is allowed inside a `forbid` context, but
ignored". The rustc book adds the cap ("levels may still be capped with
`--cap-lints` ... so `rustc --cap-lints warn` will make lints set to 'forbid'
just warn").

Basis: source + execution; Reference and rustc book as documentation.

### 4. The external-macro filter, and why all three proc-macro span modes pass it

`emit_lint_base` (`compiler/rustc_middle/src/lint.rs` L378-587), the innermost
function through which every lint diagnostic goes, contains after the level
conversion:

```rust
let disable_suggestions = if let Some(ref span) = span
    // If this code originates in a foreign macro, aka something that this crate
    // did not itself author, then it's likely that there's nothing this crate
    // can do about it. We probably want to skip the lint entirely.
    && span.primary_spans().iter().any(|s| s.in_external_macro(sess.source_map())) { true } else { false };

if disable_suggestions {
    let incompatible = future_incompatible.is_some_and(|f| f.reason.edition().is_none());
    let is_in_find_attr = sess.enable_internal_lints() && ...;
    if !incompatible && !lint.report_in_external_macro && !is_in_find_attr {
        return;
    }
}
```

The return happens for every level above `Allow`, `Forbid` and `ForceWarn`
included, and before an `Expect`-level diagnostic is emitted.
`report_in_external_macro` defaults to `false`
(`compiler/rustc_lint_defs/src/lib.rs` L511-525) and `UNSAFE_CODE` is declared
with only `@eval_always = true` (`compiler/rustc_lint/src/builtin.rs`
L192-230), with no future-incompatibility data.

The predicate (`compiler/rustc_span/src/hygiene.rs` L916-938):

```rust
pub fn in_external_macro(self, sm: &SourceMap) -> bool {
    let expn_data = self.outer_expn_data();
    match expn_data.kind {
        ExpnKind::Root
        | ExpnKind::Desugaring(DesugaringKind::ForLoop | DesugaringKind::WhileLoop
            | DesugaringKind::OpaqueTy | DesugaringKind::Async | DesugaringKind::Await) => false,
        ExpnKind::AstPass(_) | ExpnKind::Desugaring(_) => true, // well, it's "external"
        ExpnKind::Macro(MacroKind::Bang, _) => {
            // Dummy span for the `def_site` means it's an external macro.
            expn_data.def_site.is_dummy() || sm.is_imported(expn_data.def_site)
        }
        ExpnKind::Macro { .. } => true, // definitely a plugin
    }
}
```

`outer_expn` is documented as "The last macro expansion in the chain. (Here we
say the most deeply nested macro expansion is the "outermost" expansion.)"
(L68-70). `is_imported` is true when the definition site lies in a source file
that has no source text attached (`self.src.is_none()`;
`compiler/rustc_span/src/source_map.rs` L1085-1089,
`compiler/rustc_span/src/lib.rs` L2358-2361). That this is how files recorded
in another crate's metadata are represented is derived from the field's
meaning and confirmed end to end by the cases below. Three consequences:

1. **Only the innermost expansion counts.** A local macro whose body invokes a
   foreign macro yields external spans; a foreign macro that invokes a local
   macro by name yields local spans. Observed: the former compiles silently,
   the latter is rejected with the diagnostic pointing into the local macro.
2. **A function-like macro is external exactly when its definition site is a
   dummy span or lies in a source file imported from another crate; attribute
   and derive macros are always external.**
3. **`Span::call_site()`, `Span::mixed_site()` and `Span::def_site()` are all
   external for a foreign proc macro.** The proc-macro server builds them as
   `with_call_site_ctxt`, `with_mixed_site_ctxt` and `with_def_site_ctxt` of
   the current expansion (`compiler/rustc_expand/src/proc_macro_server.rs`
   L435-437); these are `with_ctxt_from_mark(expn_id, Transparent)`,
   `(.., SemiOpaque)` and `(.., Opaque)`
   (`compiler/rustc_span/src/lib.rs` L1269-1290), i.e.
   `SyntaxContext::root().apply_mark(expn_id, t)`. Every branch of
   `apply_mark` returns `alloc_ctxt(_, expn_id, _)` (`hygiene.rs` L519-554), a
   context whose `outer_expn` is the proc macro's expansion. The transparency
   argument does not change `outer_expn`. A `call_site`
   span has the *location* of the invocation but not the root *context*, and
   the predicate reads the context.

The filter is therefore not "any output of a foreign macro". A token keeps the
context it was created with. Tokens passed through a foreign macro
(`foreign_passthrough!(unsafe { .. })` with `($e:expr) => { $e }`) keep the
caller's root context and are linted; a proc macro that stamps its output with
the span of an input token produces root-context spans and is linted.

| Macro that supplies the `unsafe` block, used in a `#![forbid(unsafe_code)]` crate | Result |
|---|---|
| local `macro_rules!` | error, "in this macro invocation" |
| foreign `macro_rules!` | silent, program prints `FMAC=101` |
| foreign proc macro, `Span::call_site()` | silent, `PM_CALL=201` |
| foreign proc macro, `Span::mixed_site()` | silent, `PM_MIXED=202` |
| foreign proc macro, `Span::def_site()` (unstable API) | silent, `PM_DEF=203` |
| foreign attribute macro and foreign derive macro, each adding a function with an `unsafe` block | silent, `PM_ATTR_DERIVE=205 206` |
| foreign proc macro re-using an input token's span | error at the input token |
| foreign pass-through of caller-written `unsafe { .. }` | error at the caller's block |
| local macro wrapping the foreign macro | silent, `WRAP=101` |
| foreign macro invoking a local macro that contains `unsafe` | error in the local macro |

A second, independent exemption sits in the lint pass itself:
`UnsafeCode::report_unsafe` returns early when `span.allows_unsafe()`, i.e.
when the innermost expansion is a macro marked `#[allow_internal_unsafe]`
(`builtin.rs` L234-248, `rustc_span/src/lib.rs` L1066-1071). The pass also
reports the *definition* of such a macro (`BuiltinUnsafe::AllowInternalUnsafe`,
L312-322). This attribute is unstable; no case exercises it.

Basis: source + execution for the table; source only for
`allow_internal_unsafe`.

### 5. Why a foreign `#[allow(unsafe_code)]` is E0453 while a foreign bare `unsafe` passes

Both facts follow from which channel reports them.

- The level builder visits every lint-level attribute present in the
  **expanded** tree. `insert_spec` reports a lowered `forbid` with
  `self.sess.dcx().emit_err(OverruledAttribute { .. })` (`levels.rs` L618-625).
  That is a hard error. It does not go through `emit_lint_base`, so neither the
  external-macro filter nor (directly) the lint level of anything applies. The
  only way it is avoided is that `old_level` is not `Forbid` (section 3).
- The `unsafe` block is reported by the `UnsafeCode` early pass with
  `cx.emit_span_lint(UNSAFE_CODE, span, ..)`, which ends in `emit_lint_base`
  and is dropped by the filter.

Observed with a foreign macro expanding to
`{ #[allow(unsafe_code)] let v = unsafe { 102u32 }; v }`: exactly one error,
`error[E0453]: allow(unsafe_code) incompatible with previous forbid`, with the
note "this error originates in the macro
`up_unsafe_mac::foreign_allow_unsafe_expr`", and **no** "usage of an `unsafe`
block" diagnostic even though E0453 retains the `forbid` level. The same macro
without the attribute compiles silently.

A practical reading: inside a `forbid(unsafe_code)` crate, an upstream macro
author who politely annotates generated `unsafe` with `#[allow(unsafe_code)]`
breaks the build, and one who does not annotate is invisible.

Basis: source + execution.

### 6. What the lint inspects, and what the unsafety checker inspects

`UnsafeCode` is an `EarlyLintPass` registered in
`BuiltinCombinedEarlyLintPass` (`compiler/rustc_lint/src/lib.rs` L175) and run
on the expanded AST. At the audited commit it reports, by syntax alone
(`builtin.rs` L250-359): user-written `unsafe` blocks; `unsafe trait`;
`unsafe impl`; `#[no_mangle]`, `#[export_name]`, `#[link_section]` on functions
and statics and the first two on associated functions; `global_asm!`;
`unsafe extern` blocks; `#[allow_internal_unsafe]` macro definitions; and
`unsafe fn` declarations other than those inside `extern` blocks. It does not
look at operations.

Operations are checked on THIR by `rustc_mir_build::check_unsafety`. Its
`UnsafeOpKind` lists thirteen kinds (`CallToUnsafeFunction`,
`UseOfInlineAssembly`, `InitializingTypeWithUnsafeField`,
`UseOfMutableStatic`, `UseOfExternStatic`, `UseOfUnsafeField`,
`DerefOfRawPointer`, `AccessToUnionField`, `MutationOfLayoutConstrainedField`,
`BorrowOfLayoutConstrainedField`, `CallToFunctionWith`, `UnsafeBinderCast`,
`CallDropExplicitly`; `compiler/rustc_mir_build/src/check_unsafety.rs`
L644-668). `requires_unsafe` (L127-164) treats one of these inside an `unsafe`
block as fine, inside an `unsafe fn` body as the `unsafe_op_in_unsafe_fn` lint
(nothing when that lint is revealed as `allow`), and in a safe context as a
hard error E0133.

The two analyses are incomparable, and both directions were observed:

- `unsafe { 42u32 }` is rejected by `forbid(unsafe_code)`, the checker
  separately warns ``unnecessary `unsafe` block``, and the function's MIR
  contains no raw-pointer dereference. `#[expect(unsafe_code)]` on such a block
  counts as fulfilled.
- A raw-pointer dereference supplied by a foreign macro, or silenced by
  `--cap-lints allow`, draws no `unsafe_code` diagnostic and is present in MIR
  (section 10).
- A raw-pointer dereference outside any `unsafe` block is `error[E0133]` even
  under `--cap-lints allow`. The message then ends "requires unsafe function
  or block" rather than "requires unsafe block", because the wording depends
  on whether `unsafe_op_in_unsafe_fn` is revealed as `allow`, which the cap
  causes (`check_unsafety.rs` L949-957); the error itself is raised with
  `dcx.emit_err` and is not a lint.

Basis: source + execution.

### 7. Edition 2024 unsafe markers

| Rule | Edition 2021 | Edition 2024 | Mechanism at the audited commit |
|---|---|---|---|
| unsafe operation in `unsafe fn` body without a block | silent | `warning[E0133]: ... requires unsafe block` | lint `unsafe_op_in_unsafe_fn`: `Allow`, `@edition Edition2024 => Warn` (`compiler/rustc_lint_defs/src/builtin.rs` L2584-2592); the checker asks whether its revealed level `is_allow()` (`check_unsafety.rs` L175-178) |
| `&mut STATIC_MUT` | warning | error, with the note that `#[deny(static_mut_refs)]` is on by default | lint `static_mut_refs`: `Warn`, `@edition Edition2024 => Deny` (`compiler/rustc_lint/src/static_mut_refs.rs` L52-60) |
| `&raw mut STATIC_MUT` | accepted | accepted | not matched by the lint |
| bare `#[no_mangle]` | accepted | `error: unsafe attribute used without unsafe` | `check_attribute_safety`: hard error iff `path_span.edition() >= unsafe_since`, else lint `unsafe_attr_outside_unsafe` (allow) (`compiler/rustc_attr_parsing/src/safety.rs` L12-115, decision at L42-51) |
| bare `extern "C" { .. }` | accepted | `error: extern blocks must be unsafe` | hard error iff `item.span.at_least_rust_2024()`, else lint `missing_unsafe_on_extern` (allow) (`compiler/rustc_ast_passes/src/ast_validation.rs` L1289-1301) |
| `#[unsafe(no_mangle)]` under `#![forbid(unsafe_code)]` | n/a | error from `unsafe_code` (``declaration of a `no_mangle` function``) | `UnsafeCode::check_item` |
| `unsafe extern "C" { safe fn .. }` under `#![forbid(unsafe_code)]` | n/a | error from `unsafe_code` (``usage of an `unsafe extern` block``) | `UnsafeCode::check_item` |

All ten Edition cases behaved as in the table (execution). Three points change
how the table should be read.

1. **`static_mut_refs` in Edition 2024 is a deny-by-default lint, not a hard
   error.** The same file compiles and runs under `--cap-lints allow`, and
   under `#![allow(static_mut_refs)]`. The Edition Guide says so too ("The
   `static_mut_refs` lint level is now `deny` by default"), although its code
   comments say `ERROR`.
2. **`unsafe_op_in_unsafe_fn` is capped.** With `--cap-lints allow` the
   Edition 2024 warning disappears.
3. **The two hard errors are per-span, and the remaining check is the
   filtered lint.** Both hard errors test the edition recorded in the *span*
   of the attribute name or of the `extern` item. A macro defined in a crate
   compiled with `--edition 2021` carries 2021 spans into its expansion.
   Observed: a 2021 foreign `macro_rules!` that expands to

   ```rust
   #[no_mangle] pub extern "C" fn up_exported_symbol() -> u32 { 301 }
   extern "C" { fn abs(x: i32) -> i32; }
   pub fn foreign_abs(x: i32) -> i32 { unsafe { abs(x) } }
   ```

   invoked in a crate compiled with `--edition 2024` and
   `#![forbid(unsafe_code)]`: no output, exit 0, program prints `FFI=301 5`.
   The edition errors do not fire (2021 spans), the allow-by-default migration
   lints are silent, and the two `unsafe_code` reports (for the `#[no_mangle]`
   attribute and for the `unsafe` block) are dropped by the external-macro
   filter. A bare `extern` block is not something `unsafe_code` reports at all;
   only `unsafe extern` is.

Basis: source + execution; Edition Guide as documentation.

### 8. `#[expect]`

RFC 2383 introduces `expect` as an attribute that "functions identically to
`allow`, but will cause a lint to be emitted when the code it decorates ***does
not*** raise a lint warning"; the Reference states the fulfilment rule as "The
expectation will be fulfilled, if a `#[warn(C)]` attribute at the same location
would result in a lint emission." The implementation matches that sentence
closely, including in the corner cases:

- `Expect` is a level (section 1). `emit_lint_base` builds the diagnostic at
  `rustc_errors::Level::Expect` and emits it silently so that the expectation
  is recorded as fulfilled (`lint.rs` L425-434, L522-525). After the lint
  passes, `check_expectations` emits `unfulfilled_lint_expectations` for each
  expectation not recorded (`compiler/rustc_lint/src/expect.rs` L28-64). That
  lint is declared `Warn` (`rustc_lint_defs/src/builtin.rs` L678-680).
- Under `--cap-lints allow`, `min(Expect, Allow) = Allow`, so nothing is
  recorded, and the `unfulfilled_lint_expectations` lint itself is capped to
  `allow`. Observed: `#[expect(dead_code)]` on a used function warns "this lint
  expectation is unfulfilled" normally and is silent under the cap.
- The external-macro return in `emit_lint_base` precedes the silent emission,
  so a lint that the filter drops does not fulfil an expectation. Observed:
  `#[expect(unsafe_code)]` on a function whose only `unsafe` block comes from a
  foreign macro warns that the expectation is unfulfilled while the program
  runs the block. This agrees with the Reference sentence: `#[warn]` there
  would not have emitted either.
- `#[expect(L)]` under a revealed `forbid(L)` is E0453 (section 3).
- `insert_spec` ignores `#[expect(unfulfilled_lint_expectations)]`
  (`levels.rs` L647-654).

Basis: source + execution; RFC 2383 and Reference as documentation. The RFC
text names the lint `expectation_missing`; the implemented name is
`unfulfilled_lint_expectations`.

### 9. Cargo decides the cap by where a package came from

`add_cap_lints` (`src/cargo/core/compiler/mod.rs` L1151-1165 in
`rust-lang/cargo`):

```rust
if !unit.show_warnings(bcx.gctx) {
    cmd.arg("--cap-lints").arg("allow");
} else if !unit.is_local() {
    cmd.arg("--cap-lints").arg("warn");
}
```

with `is_local() = source_id().is_path() && !is_std` and `show_warnings() =
is_local() || gctx.extra_verbose()` (`src/cargo/core/compiler/unit.rs`
L161-171). So every registry or git dependency is compiled with `--cap-lints
allow` (or `warn` under `-vv`), and path dependencies and workspace members
are not capped.

Observed with one dependency crate containing
`#![forbid(unsafe_code)] pub fn peek(v: &u32) -> u32 { unsafe { *(v as *const u32) } }`
and an application that is itself `#![forbid(unsafe_code)]`:

| Dependency declared as | rustc line for the dependency | `cargo build -v` | Program |
|---|---|---|---|
| `{ path = "../forbid_dep" }` | no `--cap-lints` | fails with ``error: usage of an `unsafe` block`` | not built |
| `{ git = "file://.../forbid_dep" }` | ends with `--cap-lints allow` | succeeds | prints `DEP_PEEK=11` |

The same source therefore passes or fails its own `forbid` depending on how
the consumer names it, and the consumer's own `#![forbid(unsafe_code)]` is
silent about it either way, since the lint is per crate. RFC 1193 specifies
this division of labour ("have Cargo pass `--cap-lints allow` to all upstream
dependencies").

Basis: source + execution. A registry dependency was not executed (no network
registry in the observation environment); that it behaves like the git
dependency is derived from `is_path()` being false for both.

### 10. The compiled body keeps what the lint did not report

`--emit=mir` on the function below, in a `#![forbid(unsafe_code)]` crate
compiled without any lint flag, produced no diagnostic and this body
(abridged to the lines that matter; the full text is in
`support/probe_results.json`):

```rust
pub fn read_through_foreign_macro(x: &u32) -> u32 {
    let p = x as *const u32;
    up_unsafe_mac::foreign_read_raw!(p)      // foreign: ($p:expr) => { unsafe { *$p } }
}
```

```text
fn read_through_foreign_macro(_1: &u32) -> u32 {
    let _2: *const u32;
    ...
    bb0: { _2 = &raw const (*_1); ... assert(.. "misaligned pointer dereference: ..") .. }
    bb1: { ... assert(.. "null pointer dereference occurred") .. }
    bb2: { _0 = copy (*_2); return; }
}
```

The same shape (`_0 = copy (*_2)` with `_2: *const u32`) was produced for a
locally written `unsafe { *p }` compiled with `--cap-lints allow`, and no
raw-pointer local or dereference appeared for `unsafe { 42u32 }`. The emitted
MIR text carries no marker of the `unsafe` block and no lint level; the
dereference appears as a place projection through a raw-pointer local.

Basis: execution (three functions, debug build, the MIR text that
`--emit=mir` writes) + derived (that this holds for unsafe operations in
general follows from lints being diagnostics only; it was not tested per
operation kind).

### 11. The Lean model and what it establishes

`support/LintCapAndForbidUnsafeSoundness.lean` (no imports, 81 theorems) models
the pieces above. Definitions and the source they transcribe:

| Model definition | Compiler source it follows | Deliberate simplification |
|---|---|---|
| `LintLevel`, `rank`, `min` | `Level` and `std::cmp::min` | none |
| `revealActualLevelSpec` = `applyDriverCap ∘ applyCap ∘ applyWarningsGroup` | `reveal_actual_level_spec` | one lint; the `warnings` spec is a session field |
| `lintOpts`, `lintCapOf` | `get_cmd_lint_options` | flags classified as naming this lint, `warnings`, or another lint |
| `addCommandLineStep` | the loop tail of `add_command_line` | lint not feature-gated |
| `insertSpecLiteral` (if-chain) and `insertSpecTable` (decision table), proved equal | `insert_spec` | `lint_added_lints = true`; no lint-group downgrade; not the `unfulfilled_lint_expectations` lint |
| `ExpnData.external`, `inExternalMacro`, `allowsUnsafe` | `SyntaxContext::in_external_macro`, `Span::allows_unsafe` | a context is the list of its expansions, innermost first; unnamed desugarings collapsed into one constructor |
| `procMacroSpanCtxt` | `with_ctxt_from_mark` / `apply_mark` | only the outer expansion is modelled faithfully |
| `emitLintBase` | level conversion and external-macro return of `emit_lint_base` | no future-breakage reporting; internal `find_attr` exception omitted |
| `lintWalk`, `reportUnsafe` | `UnsafeCode::check_expr` + level builder, on blocks only | other syntactic triggers omitted |
| `unsafeckOk` | `requires_unsafe` in a safe function | one safe function; six sample operation kinds |
| `lower`, `hasUnsafeMir` | none (an abstraction of "the body keeps operations and has no spans or levels") | not derived from the MIR builder |

Statements proved (names as in the file):

- **Lattice.** `le_refl`, `le_trans`, `le_antisymm`, `le_total`, `allow_le`,
  `le_forbid`, `min_le_left`, `min_le_right`, `le_min`, `min_comm`,
  `min_assoc`: the chain order, with `min` as greatest lower bound.
- **Ceiling.** `reveal_le_lintCap`: if the raw spec and the `warnings` spec do
  not come from a command-line force-warn, the revealed level is `≤` the cap.
  `reveal_le_driverCap`: the driver cap bounds every source.
- **Flag order.** `cap_flag_position_irrelevant`: for arguments
  `pre ++ [--cap-lints c] ++ post` with no earlier cap in `pre`, the parsed
  `(lint_opts, lint_cap)` equals that of `[--cap-lints c] ++ pre ++ post`.
- **Theorem 1, `capLints_allow_silences_forbid_and_cli_F`.** With
  `--cap-lints allow` as the first cap anywhere among the arguments and no
  `--force-warn` flag, for every list of crate-level attributes, every
  command-line level flag and every body, the lint walk yields the empty
  diagnostic list (no `unsafe_code` diagnostic at any depth and no E0453), and
  the crate is accepted exactly when the unsafety check passes.
- **Stickiness.** `insertSpec_of_forbid`: with no cap below `forbid`, an
  attribute under a revealed `forbid` is either E0453 or leaves the revealed
  level at `forbid`.
- **Theorem 2, `forbid_catches_local_non_capped_unsafe`** and its crate form
  `forbid_attr_crate_sound`. If nothing caps the lint, no `--force-warn` is
  given, the level in scope is `forbid`, and every `unsafe` block's span is
  neither in an external macro nor inside an `allow_internal_unsafe` macro,
  then a body that passes the lint walk and the unsafety check lowers to a
  body with no unsafe operation. So in the model `forbid(unsafe_code)` *is* a
  sound "no unsafe operations in this function" check on exactly the fragment
  that excludes the escapes.
- **Provenance.** `inExternalMacro_cons` (only the innermost expansion is
  read), `procMacro_span_modes_agree` (the three transparencies give the same
  answer), `foreign_proc_macro_span_external`,
  `attr_or_derive_macro_external`, `local_bang_macro_not_external`,
  `emitLintBase_unsafeCode_external` (no emission at any level for an external
  span).
- **Theorem 3, `mir_unsafe_audit_catches_all_macro_and_capped_unsafe`**, with
  `hasUnsafeMir_lower_iff` and `lower_relabel`. For every crate, whatever its
  command line, attributes and span contexts, the audit of the lowered body is
  true exactly when the body contains an unsafe operation, and the lowered
  body is unchanged by any relabelling of contexts and attribute levels. This
  theorem is true by the construction of `lower`, which is given no access to
  spans or levels; its content is that such an audit *cannot* be influenced by
  the inputs that defeat the lint. It says nothing about rustc's MIR builder.
- **Counterexamples**, each a closed term evaluated by the kernel:

| Theorem | What it exhibits | Execution cases with the same outcome |
|---|---|---|
| `ce1_cap_lints_allow_overrides_forbid_and_cli_F` | attribute forbid and `-F` each reject a local block; with `--cap-lints allow` in either position the crate with both is accepted with zero diagnostics and its lowered body has an unsafe operation | Part A, all five; `cli_F_alone_rejects`; `attr_forbid_plus_cli_F_plus_cap_lints_allow`; `mir_shows_raw_deref_under_cap_lints_allow` |
| `ce2_foreign_call_site_proc_macro_bypasses_forbid` | a block whose span is a foreign proc macro's call-site, mixed-site or def-site span is accepted silently under uncapped forbid; with a root span it is rejected; same lowered body | `proc_macro_{call,mixed,def}_site_unsafe_in_forbid_crate`, `default_forbid_rejects` |
| `ce3_foreign_macro_bare_unsafe_passes_while_allow_attr_fails_e0453` | foreign bare block: accepted, no diagnostics; same block under `allow`: rejected with exactly `[E0453]`; same lowered body | `foreign_macro_rules_unsafe_in_forbid_crate`, `foreign_macro_rules_allow_unsafe_in_forbid_crate` |
| `ce4_cap_lints_deny_makes_forbid_overridable` | under `--cap-lints deny`, inner `allow` accepted | `cap_lints_deny_makes_forbid_overridable`, `cap_lints_deny_keeps_forbid_an_error` |
| `ce5_force_warn_is_neither_capped_nor_raised_by_forbid` | force-warn survives the cap and a later forbid attribute | `force_warn_survives_cap_lints_allow`, `force_warn_flag_downgrades_attribute_forbid` |
| `chain_only_outermost_expansion_counts` | local-wraps-foreign external, foreign-calls-local local | `local_macro_wrapping_foreign_macro_bypasses`, `foreign_macro_invoking_local_macro_is_caught` |
| `lint_and_audit_are_incomparable` | block without operation rejected yet nothing to audit; foreign block with operation accepted yet audited | `default_forbid_rejects`, the three `mir_*` cases |
| `expect_and_deny_below_forbid`, `expect_and_unfulfilled_expectations_under_cap_allow` | E0453 for `expect` under forbid; `expect` and the unfulfilled-expectation lint under the cap | `expect_inside_forbid_is_e0453`, `deny_inside_forbid_is_not_e0453`, Part D |

Checking results (`support/lean_verification.json`): the file elaborates and
passes kernel type checking with warnings as errors; a text scan finds no
unfinished-proof token, no arithmetic or bit-vector decision procedure, no
compiled-code evaluation, no classical-logic identifier, no termination
bypass, no axiom declaration and no import; of the 25 `#print axioms` lines
for theorems, 6 report no axioms and 19 report `propext` only; an environment
audit over all 760 constants of the compiled module finds no axiom, opaque or
unsafe constant, no compiler-generated unchecked copy of a recursive
definition, and `propext` as the only axiom reachable from any constant.
`propext` is already a dependency of five *definitions* (`insertSpecLiteral`,
`insertSpecTable`, `emitLintBase`, `applyCap`, `lintWalk`; the file prints
their axioms too, next to two definitions that have none, `levelEmission` and
`lower`). The likely origin is how Lean 4.34.1 compiles pattern matches with
catch-all arms; that was not investigated further, and whether any proof step
adds a further use of `propext` was not separated out.

Every definition is marked `noncomputable`. Without the modifier, Lean
generates an executable helper copy for each of the eleven recursive
definitions, and that copy is not a kernel-checked definition; the
environment audit failed on exactly those eleven names until the modifier was
added. Kernel reduction, on which every `decide` here relies, is unaffected.

Basis: execution of the Lean checker for "proved"; derived for the
correspondence between model and compiler, which rests on the table above and
on the agreement of the listed execution cases.

### 12. Implication for a verifier's trusted boundary (Anneal)

Facts at `joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613` (source):

- `trusted/rustc-capture` is, in its own words, a scaffold: "Run the compiler
  scaffold without claiming that a crate is verified" (`src/main.rs` L9), and
  its help text says "Verification is not implemented" and "Pass compiler
  options unchanged" (L25-27). `src/driver.rs` insists on
  `COMPILER_VERSION = "1.98.0-nightly (f8a08b688 2026-05-30)"` (L25, L45),
  implements `after_analysis` as `self.analysis_reached =
  tcx.dcx().has_errors().is_none(); Compilation::Continue` with the comment "No
  compiler data or verification obligation is extracted here" (L75-84), and
  ends with the note "compiler analysis callback reached; verification not
  performed" (L149).
- `THREAT_MODEL.md` L139-142: "non-malicious Rust code *generated* by a
  `build.rs` script or procedural macro is compiled by `rustc` and verified by
  Anneal under the same soundness, specification, and TCB rules as
  hand-written code in the crate."
- `trusted/lean/Trusted/MirAst.lean` represents places with a `deref`
  projection (L472-475), raw-pointer types and address-of rvalues, and records
  `Body.isUnsafe` from the function signature (L862-867). It has no field for
  spans, expansion data or lint levels.
- The strings `unsafe_code` and `cap-lints` do not occur anywhere in the tree
  (`git grep` on a checkout of that commit). Nothing there relies on the lint.

What follows (derived):

1. At this commit the driver's only output is "the requested compilation
   reached analysis without errors". By sections 2 to 5 that statement is
   compatible with a `#![forbid(unsafe_code)]` crate that performs unsafe
   operations. Because arguments are passed unchanged, whatever
   `--cap-lints` Cargo chose for the unit (section 9) is in force during
   capture. A clean compile of a `forbid(unsafe_code)` crate is therefore not
   usable as evidence of anything about unsafe operations, now or in a later
   driver that extracts data.
2. `#![forbid(unsafe_code)]` cannot be a trusted-boundary or supply-chain
   criterion: a consumer cannot observe from the dependency's source whether
   its `forbid` was in effect (cap), the dependency's author cannot see unsafe
   introduced by the macros it uses (filter), and neither appears in the
   crate's own text.
3. A sound criterion has to be evaluated on a representation that has no
   access to the two things the lint is defeated through, the lint
   configuration and span provenance, and that exists after expansion. MIR
   bodies have that shape (section 10), and Anneal's trusted MIR AST already
   has it by construction. The `after_analysis` hook used by the scaffold is
   called after macro expansion and after the `analysis` query, which runs the
   THIR unsafety check for every body
   (`compiler/rustc_driver_impl/src/lib.rs` L306-334,
   `compiler/rustc_interface/src/passes.rs` L1073-1197 with the
   `check_unsafety` call at L1159); an extraction step at or after that point
   sees the foreign-macro and capped operations.
4. The Lean results give the precise trade: on the fragment without caps,
   force-warn and foreign or `allow_internal_unsafe` spans, the lint and the
   body audit agree in the model (Theorem 2); outside it only the body audit
   is reliable (Theorem 3 and the counterexamples).

Basis: source for the listed facts; derived for the four consequences. No
Anneal code was executed, and at the audited commit no extraction exists to
test.

### Complete case list

Outcomes of all 58 executed cases; `rc` is the compiler's exit status.
Diagnostics are the `error`/`warning` headline lines; full text, argument
vectors and sources are in `support/probe_results.json`.

#### Part A: forbid against the cap (5)

| Case | Source, edition, extra arguments | Compile | Diagnostics | Program output |
|---|---|---|---|---|
| `default_forbid_rejects` | `a_forbid.rs`, 2021 | rc 1 | error: usage of an `unsafe` block; warning: unnecessary `unsafe` block | not run |
| `cap_lints_allow_bypasses_forbid` | `a_forbid.rs`, 2021, `--cap-lints allow` | rc 0 | (none) | `UNSAFE_RAN=42` |
| `cap_lints_warn_downgrades_forbid` | `a_forbid.rs`, 2021, `--cap-lints warn` | rc 0 | warning: usage of an `unsafe` block; warning: unnecessary `unsafe` block | `UNSAFE_RAN=42` |
| `cap_lints_allow_plus_cli_F_unsafe_code` | `a_plain.rs`, 2021, `--cap-lints allow -F unsafe_code` | rc 0 | (none) | `UNSAFE_RAN=42` |
| `cli_F_unsafe_code_plus_cap_lints_allow` | `a_plain.rs`, 2021, `-F unsafe_code --cap-lints allow` | rc 0 | (none) | `UNSAFE_RAN=42` |

#### Part B: foreign macros (6)

| Case | Source, edition | Compile | Diagnostics | Program output |
|---|---|---|---|---|
| `local_macro_rules_unsafe_caught_by_forbid` | `b0_local_mac.rs`, 2021 | rc 1 | error: usage of an `unsafe` block; warning: unnecessary `unsafe` block | not run |
| `foreign_macro_rules_unsafe_in_forbid_crate` | `b1_fmac.rs`, 2021 | rc 0 | (none) | `FMAC=101` |
| `foreign_macro_rules_allow_unsafe_in_forbid_crate` | `b2_fmac_allow.rs`, 2021 | rc 1 | error[E0453]: allow(unsafe_code) incompatible with previous forbid | not run |
| `proc_macro_call_site_unsafe_in_forbid_crate` | `b3_pm_call.rs`, 2021 | rc 0 | (none) | `PM_CALL=201` |
| `proc_macro_mixed_site_unsafe_in_forbid_crate` | `b4_pm_mixed.rs`, 2021 | rc 0 | (none) | `PM_MIXED=202` |
| `proc_macro_def_site_unsafe_in_forbid_crate` | `b5_pm_def.rs`, 2021 | rc 0 | (none) | `PM_DEF=203` |

#### Part C: Edition 2024 (10)

| Case | Source, edition | Compile | Diagnostics | Program output |
|---|---|---|---|---|
| `unsafe_op_in_unsafe_fn_ed2021` | `c1_uop.rs`, 2021 | rc 0 | (none) | `UOP=9` |
| `unsafe_op_in_unsafe_fn_ed2024` | `c1_uop.rs`, 2024 | rc 0 | warning[E0133]: dereference of raw pointer is unsafe and requires unsafe block | `UOP=9` |
| `static_mut_ref_ed2021` | `c2_smut.rs`, 2021 | rc 0 | warning: creating a mutable reference to mutable static | `SMUT=2` |
| `static_mut_ref_ed2024` | `c2_smut.rs`, 2024 | rc 1 | error: creating a mutable reference to mutable static | not run |
| `raw_mut_static_ed2024` | `c2_raw.rs`, 2024 | rc 0 | (none) | `RAW=2` |
| `bare_no_mangle_ed2021` | `c3_nm.rs`, 2021 | rc 0 | (none) | `NM=7` |
| `bare_no_mangle_ed2024_rejected` | `c3_nm.rs`, 2024 | rc 1 | error: unsafe attribute used without unsafe | not run |
| `forbid_unsafe_code_rejects_unsafe_no_mangle` | `c4_forbid_nm.rs`, 2024 | rc 1 | error: declaration of a `no_mangle` function | not run |
| `bare_extern_c_ed2024_rejected` | `c5_ext.rs`, 2024 | rc 1 | error: extern blocks must be unsafe | not run |
| `forbid_unsafe_code_rejects_unsafe_extern_c` | `c6_forbid_ext.rs`, 2024 | rc 1 | error: usage of an `unsafe extern` block | not run |

#### Part D: `expect` and overriding forbid (4)

| Case | Source, edition, extra arguments | Compile | Diagnostics | Program output |
|---|---|---|---|---|
| `allow_under_forbid_rejected_e0453` | `d1_e0453.rs`, 2021 | rc 1 | error[E0453]: allow(unsafe_code) incompatible with previous forbid; error: usage of an `unsafe` block; warning: unnecessary `unsafe` block | not run |
| `expect_fulfilled_clean` | `d2_exp_ok.rs`, 2021 | rc 0 | (none) | `EXP_OK` |
| `expect_unfulfilled_warns` | `d3_exp_unful.rs`, 2021 | rc 0 | warning: this lint expectation is unfulfilled | `EXP_UNFUL=5` |
| `expect_unfulfilled_silenced_by_cap_lints_allow` | `d4_exp_cap.rs`, 2021, `--cap-lints allow` | rc 0 | (none) | `EXP_CAP=5` |

#### Part E: further discriminators (31)

| Case | Source, edition, extra arguments | Compile | Diagnostics | Program output |
|---|---|---|---|---|
| `cli_F_alone_rejects` | `a_plain.rs`, 2021, `-F unsafe_code` | rc 1 | error: usage of an `unsafe` block; warning: unnecessary `unsafe` block | not run |
| `attr_forbid_plus_cli_F_plus_cap_lints_allow` | `a_forbid.rs`, 2021, `-F unsafe_code --cap-lints allow` | rc 0 | (none) | `UNSAFE_RAN=42` |
| `cap_lints_allow_suppresses_e0453` | `d1_e0453.rs`, 2021, `--cap-lints allow` | rc 0 | (none) | (empty) |
| `force_warn_survives_cap_lints_allow` | `a_plain.rs`, 2021, `--force-warn unsafe_code --cap-lints allow` | rc 0 | warning: usage of an `unsafe` block | `UNSAFE_RAN=42` |
| `cap_lints_repeated_allow_then_forbid` | `a_forbid.rs`, 2021, `--cap-lints allow --cap-lints forbid` | rc 0 | (none) | `UNSAFE_RAN=42` |
| `cap_lints_repeated_forbid_then_allow` | `a_forbid.rs`, 2021, `--cap-lints forbid --cap-lints allow` | rc 1 | error: usage of an `unsafe` block; warning: unnecessary `unsafe` block | not run |
| `cap_lints_deny_keeps_forbid_an_error` | `a_forbid.rs`, 2021, `--cap-lints deny` | rc 1 | error: usage of an `unsafe` block; warning: unnecessary `unsafe` block | not run |
| `cli_F_then_cli_A_stays_forbid` | `a_plain.rs`, 2021, `-F unsafe_code -A unsafe_code` | rc 1 | error: usage of an `unsafe` block; warning: unnecessary `unsafe` block | not run |
| `cap_lints_deny_makes_forbid_overridable` | `d1_e0453.rs`, 2021, `--cap-lints deny` | rc 0 | warning: unnecessary `unsafe` block | (empty) |
| `cap_lints_rejects_expect_as_a_level` | `a_forbid.rs`, 2021, `--cap-lints expect` | rc 1 | error: unknown lint level: `expect` | not run |
| `force_warn_flag_downgrades_attribute_forbid` | `a_forbid.rs`, 2021, `--force-warn unsafe_code` | rc 0 | warning: usage of an `unsafe` block; warning: unnecessary `unsafe` block | `UNSAFE_RAN=42` |
| `cli_F_then_crate_allow_attribute_is_e0453` | `e_crate_allow.rs`, 2021, `-F unsafe_code` | rc 1 | error[E0453]: allow(unsafe_code) incompatible with previous forbid; error: usage of an `unsafe` block; warning: unnecessary `unsafe` block | not run |
| `forbid_of_lint_group_is_overridable_with_future_compat_warning` | `e_group_forbid.rs`, 2021 | rc 0 | warning: allow(unused_variables) incompatible with previous forbid | `GROUP_FCW` |
| `deny_inside_forbid_is_not_e0453` | `e_deny_in_forbid.rs`, 2021 | rc 1 | error: usage of an `unsafe` block; warning: unnecessary `unsafe` block | not run |
| `expect_inside_forbid_is_e0453` | `e_expect_in_forbid.rs`, 2021 | rc 1 | error[E0453]: expect(unsafe_code) incompatible with previous forbid; error: usage of an `unsafe` block; warning: unnecessary `unsafe` block | not run |
| `foreign_passthrough_of_local_unsafe_tokens_is_caught` | `e_passthrough.rs`, 2021 | rc 1 | error: usage of an `unsafe` block; warning: unnecessary `unsafe` block | not run |
| `local_macro_wrapping_foreign_macro_bypasses` | `e_local_wraps_foreign.rs`, 2021 | rc 0 | (none) | `WRAP=101` |
| `foreign_macro_invoking_local_macro_is_caught` | `e_foreign_calls_local.rs`, 2021 | rc 1 | error: usage of an `unsafe` block; warning: unnecessary `unsafe` block | not run |
| `proc_macro_reusing_input_span_is_caught` | `e_pm_input_span.rs`, 2021 | rc 1 | error: usage of an `unsafe` block; warning: unnecessary `unsafe` block | not run |
| `ed2021_foreign_macro_ffi_items_in_ed2024_forbid_crate` | `e_ed2021_ffi_in_2024.rs`, 2024 | rc 0 | (none) | `FFI=301 5` |
| `static_mut_ref_ed2024_under_cap_lints_allow` | `c2_smut.rs`, 2024, `--cap-lints allow` | rc 0 | (none) | `SMUT=2` |
| `static_mut_ref_ed2024_under_allow_attribute` | `e_smut_allow_attr.rs`, 2024 | rc 0 | (none) | `SMUT_ALLOW=2` |
| `unsafe_op_in_unsafe_fn_ed2024_under_cap_lints_allow` | `c1_uop.rs`, 2024, `--cap-lints allow` | rc 0 | (none) | `UOP=9` |
| `expect_unsafe_code_fulfilled_by_block_without_unsafe_operation` | `e_expect_noop_block.rs`, 2021 | rc 0 | warning: unnecessary `unsafe` block | `EXP_NOOP` |
| `expect_unsafe_code_unfulfilled_when_only_site_is_foreign_macro` | `e_expect_foreign.rs`, 2021 | rc 0 | warning: this lint expectation is unfulfilled | `EXP_FOREIGN=101` |
| `attribute_and_derive_proc_macros_bypass_forbid` | `e_pm_attr_derive.rs`, 2021 | rc 0 | (none) | `PM_ATTR_DERIVE=205 206` |
| `unsafe_operation_outside_unsafe_block_is_e0133_under_cap_lints_allow` | `e_e0133.rs`, 2021, `--cap-lints allow` | rc 1 | error[E0133]: dereference of raw pointer is unsafe and requires unsafe function or block | not run |
| `mir_shows_raw_deref_from_foreign_macro_in_forbid_crate` | `e_mir_foreign_raw.rs`, 2021 | rc 0 | (none); MIR dereference `_0 = copy (*_2);` | `MIR_FOREIGN=21` |
| `mir_shows_raw_deref_under_cap_lints_allow` | `e_mir_local_raw.rs`, 2021, `--cap-lints allow` | rc 0 | (none); MIR dereference `_0 = copy (*_2);` | `MIR_LOCAL=22` |
| `mir_has_no_raw_deref_for_unsafe_block_without_unsafe_operation` | `e_mir_no_op.rs`, 2021, `--cap-lints allow` | rc 0 | (none); no raw-pointer local, no dereference | `MIR_NOOP=42` |
| `unsafe_code_is_allow_by_default_and_in_no_lint_group` | `rustc -W help` | rc 0 | lint table line `unsafe-code  allow  ...`; member of no listed group | n/a |

Cases that use a foreign crate pass `--extern up_unsafe_mac=...rlib` or
`--extern up_unsafe_pm=...so`. The two Cargo cases are in section 9.

Basis: execution.

## Boundaries

**Known not to apply.**

- The external-macro filter does not exempt tokens that keep a root-context
  span: caller tokens passed through a foreign macro and proc-macro output
  stamped with an input token's span are linted (section 4).
- The cap does not lower a command-line `--force-warn`, and does not affect
  E0133 in a safe context or the two Edition 2024 hard errors when the span's
  edition is 2024.
- `#![forbid(unsafe_code)]` is not vacuous for hand-written code compiled
  without a cap or force-warn: a local `unsafe` block, `#[unsafe(no_mangle)]`
  and `unsafe extern` block are reported (execution), as are `unsafe impl`,
  `unsafe trait`, `unsafe fn` and the other link attributes (source), and an
  inner `allow` or `expect` attribute is E0453 (execution; `warn` by source).

**Not examined.**

- Any compiler other than the two commits listed. A textual comparison of the
  fifteen determining regions with `rust-lang/rust`
  `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (committed 2026-11-11, about five
  months after the executed commit)
  found six identical (`Level`, `get_cmd_lint_options`, `apply_mark`,
  `requires_unsafe`, `allows_unsafe`, `with_ctxt_from_mark`) and nine changed.
  Among the changed ones, the cap statement in `reveal_actual_level_spec` is
  untouched (only a delayed-bug call differs), `in_external_macro` gained an
  early return for the root context, and the `UnsafeCode` AST pass no longer
  handles `no_mangle`, `export_name` and `link_section` in that function
  (where they are reported instead was not traced). The changed regions were
  not re-audited and nothing was executed on that commit.
- Stable-channel compilers. One case needs a nightly feature; the others were
  not run on a stable release.
- Macros from the standard library and the built-in derives. They are external
  by the same predicate (derived), but no case checks which of them expand to
  `unsafe` or use `#[allow_internal_unsafe]`.
- `#[allow_internal_unsafe]` (source only), declarative macros 2.0, attribute
  macros that rewrite a function body, `include!`, and `--extern` crates
  loaded through `-Z` options.
- Syntactic triggers of `unsafe_code` other than blocks, `#[unsafe(no_mangle)]`
  and `unsafe extern` (for example `unsafe impl`, `global_asm!`,
  `#[export_name]`) in combination with the filter. The source treats them
  uniformly through `report_unsafe`; only blocks, `#[no_mangle]` and a bare
  `extern` block were executed inside a foreign macro.
- Driver lint caps (`driver_lint_caps`), used by tools that embed the compiler;
  modelled from source, not executed.
- Clippy and rustdoc, which register their own lints and passes.
- A registry (crates.io) dependency under Cargo; a git dependency was used
  instead (section 9). `cargo build -vv`, which the source says switches the
  cap to `warn`, was not run.
- Operation kinds other than raw-pointer dereference in the MIR observation.
- Building or running Anneal's capture driver.

**Unknown.**

- Whether any lint group registered by an external tool contains
  `unsafe_code`; only the groups printed by `rustc -W help` were checked.
- Whether the first-occurrence rule for a repeated `--cap-lints` is intended.
  It is what was observed; no documentation was found for it.

**Unsupported by the toolchain.**

- `--cap-lints expect` and `--cap-lints force-warn` are rejected (`unknown
  lint level`).
- `--force-warn warnings` is rejected by `add_command_line`
  (`UnsupportedGroup`); not executed.

**Conclusions the evidence does not support.**

- That MIR-level inspection makes a crate "safe". It establishes only whether
  the inspected bodies contain unsafe operations; it says nothing about the
  bodies of dependencies, about soundness of the safe APIs involved, or about
  code the capture did not cover.
- That the Lean theorems are theorems about rustc. They are about a
  hand-written model. Theorem 2's positive result in particular depends on the
  model's reduced syntax (one safe function, blocks as the only trigger, six
  operation kinds) and must not be read as "`forbid(unsafe_code)` is sound for
  local code in rustc".
- That the external-macro filter is a defect. The source comment gives its
  rationale (the crate "did not itself author" the code); this report records
  the behaviour and its consequences only.
- That dependencies compiled by Cargo "ignore" their own `forbid`: path
  dependencies and workspace members are not capped.

## Evidence

All observations were made on 2026-11-22.

**Commit identities.** Each 40-hex revision in this report was resolved with
`gh api repos/<owner>/<repo>/commits/<ref> --jq .sha` on the observation date:
`rust-lang/rust` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (also printed by
`rustc -vV` of the executed toolchain) and
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`; `rust-lang/cargo` `fbb61be30` to
`fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef` (also printed by `cargo -vV`);
`joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613`;
`leanprover/lean4` tag `v4.34.1` to
`5045d0056413266e57c625dcd7c365b10e377c52` (also printed by `lean --version`);
`rust-lang/rfcs` `main` to `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`;
`rust-lang/reference` `master` to `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`;
`rust-lang/edition-guide` `master` to
`ab8544aeed7b792984366aa122ac19bd47ad9a2f`; and, for the comparison in
Boundaries only, `rust-lang/rust`
`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`. Source files were read from
`https://raw.githubusercontent.com/<owner>/<repo>/<sha>/<path>`; the Anneal
files from a local checkout of the commit.

**Source locations** (`rust-lang/rust` at `14210df0e...` unless prefixed).

| Topic | Path and lines |
|---|---|
| `Level`, `from_str`, `Lint` defaults, `default_level` | `compiler/rustc_lint_defs/src/lib.rs` L151-185, L202-210, L258-307, L511-525, L532-537 |
| `LintLevelSource`, `LevelSpec`, `reveal_actual_level_spec`, `emit_lint_base` | `compiler/rustc_middle/src/lint.rs` L19-37, L58-75, L138-195, L378-587 (level conversion L416-438, external-macro return L440-475, expect emission L522-525) |
| level builder: HIR query, AST builder, `add_command_line`, `insert_spec`, `add` | `compiler/rustc_lint/src/levels.rs` L158-210, L399-440, L497-565, L567-668, L670-939 |
| post-expansion AST lint pass wiring; driver callbacks and the `analysis` query | `compiler/rustc_lint/src/early.rs` L312-344; `compiler/rustc_interface/src/passes.rs` L400-476 (pre-expansion call at L97-104), L1073-1197; `compiler/rustc_driver_impl/src/lib.rs` L306-334 |
| `UNSAFE_CODE`, `UnsafeCode` pass, registration, diagnostics text | `compiler/rustc_lint/src/builtin.rs` L192-359; `compiler/rustc_lint/src/lib.rs` L168-176 and L276-411; `compiler/rustc_lint/src/lints.rs` L153-167 |
| `in_external_macro`, `outer_expn`, `apply_mark`, `ExpnKind`, `DesugaringKind` | `compiler/rustc_span/src/hygiene.rs` L916-938, L68-70, L519-554, L1116-1125, L1198-1228 |
| span helpers | `compiler/rustc_span/src/lib.rs` L777-784, L1066-1071, L1269-1290, L2358-2361; `compiler/rustc_span/src/source_map.rs` L1085-1089 |
| proc-macro spans | `compiler/rustc_expand/src/proc_macro_server.rs` L435-437; `compiler/rustc_expand/src/base.rs` L1330-1344 |
| command line | `compiler/rustc_session/src/config.rs` L1807-1819, L1892-1922 |
| expectations | `compiler/rustc_lint/src/expect.rs` L28-64; `compiler/rustc_lint_defs/src/builtin.rs` L678-680 |
| Edition lints and errors | `compiler/rustc_lint_defs/src/builtin.rs` L2584-2592, L5039-5045, L5079-5085; `compiler/rustc_lint/src/static_mut_refs.rs` L52-60; `compiler/rustc_attr_parsing/src/safety.rs` L12-115; `compiler/rustc_ast_passes/src/ast_validation.rs` L1289-1301 |
| unsafety checker | `compiler/rustc_mir_build/src/check_unsafety.rs` L127-164, L175-178, L226-246, L624-668, L842-957 |
| E0453 text; rustc book | `compiler/rustc_error_codes/src/error_codes/E0453.md`; `src/doc/rustc/src/lints/levels.md` L138-139, L293-333 |
| Cargo (`rust-lang/cargo` at `fbb61be30...`) | `src/cargo/core/compiler/mod.rs` L1151-1165; `src/cargo/core/compiler/unit.rs` L161-171; `src/cargo/core/source_id.rs` L343-346 |
| Anneal (`joshlf/anneal` at `c131b320...`) | `trusted/rustc-capture/src/main.rs` L9, L25-27; `trusted/rustc-capture/src/driver.rs` L25, L45, L75-84, L149; `THREAT_MODEL.md` L139-142; `trusted/lean/Trusted/MirAst.lean` L472-475, L862-867 |
| RFCs (`rust-lang/rfcs` at `f43d5789...`) | `text/1193-cap-lints.md` L44-55; `text/2383-lint-reasons.md` L159-238 |
| Reference (`rust-lang/reference` at `c9cc3282...`) | `src/attributes/diagnostics.md` L27-40, L61-66, L143-151 |
| Edition Guide (`rust-lang/edition-guide` at `ab8544ae...`) | `src/rust-2024/unsafe-op-in-unsafe-fn.md`, `static-mut-references.md`, `unsafe-attributes.md`, `unsafe-extern.md` |

**Comparison of the two compiler commits.** For each of twenty-three files
(`compiler/rustc_lint/src/{levels,builtin,early,expect,static_mut_refs,lints,lib}.rs`,
`compiler/rustc_middle/src/lint.rs`,
`compiler/rustc_lint_defs/src/{lib,builtin}.rs`,
`compiler/rustc_span/src/{hygiene,lib,source_map}.rs`,
`compiler/rustc_session/src/config.rs`,
`compiler/rustc_expand/src/{proc_macro_server,base}.rs`,
`compiler/rustc_mir_build/src/check_unsafety.rs`,
`compiler/rustc_ast_passes/src/ast_validation.rs`,
`compiler/rustc_attr_parsing/src/safety.rs`,
`compiler/rustc_interface/src/passes.rs`,
`compiler/rustc_driver_impl/src/lib.rs`,
`compiler/rustc_error_codes/src/error_codes/E0453.md`,
`src/doc/rustc/src/lints/levels.md`) the raw file at `f8a08b688...` was
compared byte for byte with the raw file at `14210df0e...`. Twenty-two are
identical; `rustc_lint_defs/src/builtin.rs` differs only at L5449-5458, in the
documentation-comment lines of the `varargs_without_pattern` lint.

**Execution environment.** `rustc 1.98.0-nightly (14210df0e 2026-05-31)`,
commit-date 2026-05-31, host `x86_64-unknown-linux-gnu`, LLVM 22.1.6;
`cargo 1.98.0-nightly (fbb61be30 2026-05-26)` with vendored libgit2 1.9.2;
`Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413..., Release)`;
Python 3 standard library; `git` for the Cargo cases. Linux, x86-64.

**Preserved material** (all under `support/`).

| File | Content |
|---|---|
| `probe_forbid_unsafe_and_cap_lints.py` | The probe. Contains every Rust source verbatim (two foreign crates, 36 case sources, and the three files of the Cargo dependency and application), the 55 compile cases with their expectations, one `rustc -W help` check, and the two Cargo cases. Compiles and runs everything in a temporary directory; exits non-zero if any executed case contradicts its expectation. |
| `probe_results.json` | Output of the probe on the toolchain above (`observed_utc` 2026-11-22): for every case the argument vector, exit status, full diagnostics, program output, MIR text where requested, expectation and verdict. 58 cases, 58 pass, 0 skipped. Temporary and toolchain paths are replaced by `$TMP`, `$SYSROOT`, `$HOME`. |
| `LintCapAndForbidUnsafeSoundness.lean` | The model and proofs (section 11). |
| `EnvAudit.lean` | Loads the compiled module and inspects every constant and its reachable axioms. |
| `verify_lean.py` | Runs the text scan, the proof check (`lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) and the environment audit. |
| `lean_verification.json` | Output of `verify_lean.py` on Lean 4.34.1: all three steps pass. |

The expectations in the probe are hypotheses written before execution. Four
of them failed on first execution and were then changed to match what the
compiler does: (i) `unsafe { 5u32 }` under `#[expect(unsafe_code)]` is not
diagnostic-free, it draws `unused_unsafe` (the "clean" case now uses a block
with a real dereference, and the original is kept as its own case);
(ii) at this commit the `unsafe_code` diagnostic for `#[unsafe(no_mangle)]`
reads ``declaration of a `no_mangle` function``, not the wording first
expected; (iii) E0133 under `--cap-lints allow` ends "requires unsafe
function or block"; (iv) one check was itself too broad: it searched a
warning-only output for the substring `error`, which occurs in rustc's "For
more information about this error" line, and was replaced by a test for
`error` headline lines. In all four the exit status and program output were
as predicted; only diagnostic text, or the check on it, was wrong.

**What is synthesis rather than observation.** The explanation of *why* each
outcome occurs (sections 2 to 8) connects source text to executed outcomes;
the connection was checked by predicting further cases from the source before
running them (the Part E cases), not by instrumenting the compiler. The
consequences in section 12 are reasoning from the listed facts.

## Revalidation

**Cheapest check of the behavioural findings (about ten seconds).** With the
toolchain of interest on `PATH`:

```bash
cd /tmp && python3 <package>/support/probe_forbid_unsafe_and_cap_lints.py --out /tmp/probe_results.json
```

Exit status 0 with `"fail": 0` means all executed cases still behave as
recorded; the per-case lines name any that changed. A failing case is a
finding about that toolchain, not an error in the probe: compare its `stderr`
with the stored `support/probe_results.json`. Set `RUSTC` and `CARGO` to
select binaries. On a stable toolchain the def-site case is reported as
skipped. The cases most likely to move are those that pin diagnostic wording
and the lint-group case. The check for
`forbid_unsafe_code_rejects_unsafe_no_mangle` deliberately does not pin the
headline, because the code that produces it is among the regions that changed
in the later commit described under Boundaries.

**Single-command spot checks**, for when the probe cannot be run:

```bash
printf '#![forbid(unsafe_code)]\nfn main() { let x = unsafe { 42u32 }; println!("{x}"); }\n' > /tmp/f.rs
rustc --edition 2021 /tmp/f.rs -o /tmp/f                     # expect: error
rustc --edition 2021 /tmp/f.rs -o /tmp/f --cap-lints allow   # expect: silent, /tmp/f prints 42
```

**Source regions that determine the behaviour.** If a compiler commit differs
from `14210df0e...` in any of these, re-read that region before relying on the
corresponding section:

| Region | Section it determines |
|---|---|
| the `min(level, lint_cap)` statement and its force-warn guard in `reveal_actual_level_spec` | 2 |
| `get_cmd_lint_options` (separate `lint_cap`, `opt_str`) | 2 |
| the two `old_level == Level::Forbid` branches of `insert_spec`, and `lint_added_lints` at the builder's construction sites | 3, 5 |
| the `in_external_macro` return in `emit_lint_base`; `report_in_external_macro` on `UNSAFE_CODE` | 4, 5, 8 |
| `SyntaxContext::in_external_macro` and `apply_mark` | 4 |
| `UnsafeCode` pass (`report_unsafe`, `check_expr`, `check_item`) | 4, 6, 7 |
| `@edition Edition2024 => ..` on `UNSAFE_OP_IN_UNSAFE_FN` and `STATIC_MUT_REFS`; the edition tests in `check_attribute_safety` and in the `ForeignMod` arm of AST validation | 7 |
| `add_cap_lints`, `Unit::is_local`, `Unit::show_warnings` in Cargo | 9 |

A quick textual test for a new `rust-lang/rust` commit is to fetch the files
listed under Evidence and `diff` them against `14210df0e...`; identical files
carry the findings over by source identity, as was done for `f8a08b688...`.

**The Lean results.** With Lean 4.34.1 as `lean` on `PATH` (or `LEAN` set):

```bash
python3 <package>/support/verify_lean.py --out /tmp/lean_verification.json
```

Exit status 0 means the proof file still elaborates under the strict flags,
its text is free of the listed tokens, the `#print axioms` lines mention only
`propext`, and the environment audit prints `ENV_AUDIT_OK`. A different Lean
version may compile pattern matches differently (changing which theorems
mention `propext`) or reject a proof script; that affects the artefact, not
the compiler findings. If a definition in the model is edited to follow a
changed compiler, the counterexample theorems are the fastest regression
check: they are closed terms and fail to elaborate as soon as the model stops
exhibiting the corresponding execution outcome.

**The Anneal facts.** Re-read `trusted/rustc-capture/src/driver.rs` at the
commit of interest. Section 12's first consequence stops applying in its
present form once `after_analysis` extracts data; the question to ask of a
later driver is whether what it extracts depends on diagnostics or lint
levels, and whether it is taken after macro expansion.

**What a passing probe does not show.** It shows these 58 outcomes on one
toolchain and host. It does not show that no other bypass exists, that
unexecuted trigger kinds behave like blocks under the filter, or that a
registry dependency behaves like the git dependency.
