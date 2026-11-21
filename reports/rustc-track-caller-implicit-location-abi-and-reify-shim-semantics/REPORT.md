# `#[track_caller]` in rustc: implicit `&Location` argument ABI, scope walk across MIR inlining, and reify shims

## Summary

`#[track_caller]` is implemented in `rustc` as **one extra trailing argument in the function's
ABI**: a `&'static core::panic::Location<'static>`. It is present exactly when
`InstanceKind::requires_caller_location` is true, it is not part of the function's type or MIR
signature, and a function pointer type never has it. Everything else follows from keeping
callers and callees in agreement about that argument.

What to retain:

1. **One function decides every reported location:** `Body::caller_location_span`. Starting from
   a statement's `(span, scope)` it walks `SourceScopeData::inlined_parent_scope`; an *untracked*
   MIR-inlined callee stops the walk with the span reached so far, a *tracked* inlined callee
   replaces the span by its call-site span, and when the walk runs out the enclosing function's
   own implicit argument is used if it has one. The text of this function and of the inliner's
   scope rewriting is identical at the three audited `rustc` revisions.
2. **MIR inlining does not change any reported location.** On the executed toolchain thirteen
   `Location::caller()` observations are identical natively and under Miri, with and without MIR
   inlining. After inlining, two functions that report different lines have *textually identical
   basic blocks* and differ only in their scope trees.
3. **Coercion to a function pointer goes through a shim** whose body is one direct call to the
   tracked function with `fn_span = def_span`, so the callee observes its own definition header
   (`FP1 = FP2 = definition line`, column of the first token of the header).
4. **Trait objects: it depends on where the attribute is.** With the attribute on the *trait's*
   method declaration the vtable holds the implementation itself and a `dyn` call reports the
   real call site. With the attribute on the *impl only*, the vtable holds a reify shim and the
   call reports the impl method's definition. The Rust Reference's remark that trait objects
   lose caller information describes only the second case.
5. **`ReifyReason::{FnPtr, Vtable}` exists only under KCFI.** In ordinary builds the shim is
   `ReifyShim(def_id, None)` and both uses share one symbol suffix (`reify`); with
   `-Zsanitizer=kcfi` the suffixes become `reify_fnptr` and `reify_vtable`.
6. **`E0737` admits only the `"Rust"` ABI.** `extern "rust-call" fn` with the attribute is
   rejected with `E0737`; `"rust-call"` meets the attribute only through (unstable) tracked
   closures and the `Fn*` shims.
7. **On x86-64 the implicit argument is an ordinary trailing integer-class argument:** `%rdi`,
   `%rsi`, `%rdx` for 0, 1, 2 explicit integer arguments, the first stack slot after six. A
   tracked caller forwards its own incoming pointer; an untracked caller materialises a 24-byte
   constant.
8. **The interpreter changed mechanism between revisions.** At the executed revision
   (2026-05-31) const-eval/Miri compute the location by a *stack walk* and never look at what the
   caller passed; at the 2026-10-20 and 2026-11-11 revisions frames store the passed location
   (`track_caller_arg`) and a caller/callee disagreement is reported as undefined behaviour. On
   the executed toolchain Miri runs a tracked definition called through a declaration without
   the attribute to completion, and under `explicit_tail_calls` Miri and native code report
   different lines.
9. A kernel-checked Lean 4 development (`support/TrackCallerAbiAndReifySoundness.lean`) proves,
   for a model transcribed from the audited source: exactness of one inlining step on
   `SourceScopeData` tables, invariance of every observation under arbitrary sequences of
   inlinings, agreement of stack walk and implicit argument under the calling discipline, arity
   and slot typing of the reify shim, the vtable case split, and two sharpness counterexamples.
   It is a statement about the model; the link to `rustc` is transcription plus the probe.

## Applicability

**Subjects and how they relate.** `REPORT.json` lists three revisions of `rust-lang/rust`, the
Rust Reference, RFC 2091, `joshlf/anneal`, and Lean 4. The report is about `rustc`; the other
subjects are documentation it is compared against (Reference, RFC), a consumer whose trusted
boundary is characterised with respect to it (Anneal), and the checker of the mechanised model
(Lean).

The three `rustc` revisions are referred to by commit date:

| Label | Commit | Role |
| --- | --- | --- |
| **R-May** | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (2026-05-31, `1.98.0-nightly`) | source audited **and executed** (`nightly-2026-06-01` toolchain incl. its Miri) |
| **R-Oct** | `8144389c895da997dbdecaa635e41d6a50be6ffd` (2026-10-20) | source audited only; the `rustc` commit named by Anneal's trusted MIR syntax and by the interpreter it vendors |
| **R-Nov** | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (2026-11-11, `1.102.0-nightly`) | source audited only; one earlier recorded run exists (see Evidence) |

**Shared across R-May, R-Oct and R-Nov** (compared textually: whole function bodies for the
first four items, the relevant lines for the rest):
`Body::caller_location_span`; `Integrator::visit_source_scope_data`; `FunctionCx::get_caller_location`;
`should_inherit_track_caller`; the `E0737` condition; the `.chain(caller_location)` construction
of `FnAbi::args`; the logic of `Instance::resolve_for_fn_ptr` and
`Instance::expect_resolve_for_vtable` (identifier renames only); `build_call_shim` using
`tcx.def_span(def_id)`.

**Different between revisions:**

| Aspect | R-May | R-Oct and R-Nov |
| --- | --- | --- |
| Shim representation | `InstanceKind::ReifyShim(DefId, Option<ReifyReason>)`, `VTableShim`, `ClosureOnceShim { call_once, track_caller }` | `InstanceKind::Shim(ShimKind::Reify(DefId, Option<ReifyReason>))`, `ShimKind::VTable`, `ShimKind::ClosureOnce { call_once, closure, track_caller }` |
| `requires_caller_location` | `Item`, `Virtual`, `ClosureOnceShim` | additionally `Shim(ShimKind::VTable(def_id))` |
| Interpreter (`rustc_const_eval`, used by Miri) | stack walk `find_closest_untracked_caller_location`; the passed location is ignored | per-frame `track_caller_arg: Option<Span>`; `caller_location()` reads it; mismatch is a UB error |
| `E0737` diagnostic struct | `rustc_ast_passes/src/errors.rs` | `rustc_ast_passes/src/diagnostics.rs` (R-Nov) |

**Executed configuration.** Host and target `x86_64-unknown-linux-gnu`, edition 2021, LLVM
22.1.6, GNU objdump 2.47. Native builds at `-C opt-level=0 -Zinline-mir=no` and
`-C opt-level=3 -Zinline-mir=yes`; Miri with its default (no MIR optimisations) and with
`-Zmir-opt-level=3 -Zinline-mir=yes`. Assembly evidence comes from a library crate compiled with
`-C opt-level=3 -C codegen-units=1 -C symbol-mangling-version=v0`. Closures with the attribute
and `become` need nightly features (`closure_track_caller`, `explicit_tail_calls`).

**Reach of each kind of claim.** Source claims hold for the revision(s) named. Execution claims
hold for R-May on the target above. Register assignments are observations of the unstable Rust
ABI on one target and are not a guarantee. Statements about R-Oct and R-Nov behaviour at run time
are derived from source and marked so. The Lean theorems hold for the model defined in the Lean
file; their bearing on `rustc` is argued in Findings §10.

**Anneal.** The findings about `joshlf/anneal` concern commit
`c131b320eeeb26ef692e5afd5ec8db49ee518613` only, and only the question whether caller locations
can enter a verified result there.

## Findings

Quoted `rustc` code is verbatim apart from condensed layout and elisions written `...` or
`{ .. }`; quoted MIR and assembly are abridged to the lines discussed. Line numbers are in
Evidence.

### 1. Where the attribute is accepted and what it sets

Basis: source (R-May, R-Nov) + execution (R-May) + documentation.

* **Flag.** A parsed `#[track_caller]` sets `CodegenFnAttrFlags::TRACK_CALLER` (bit `1 << 8`) in
  the `codegen_fn_attrs` query. The same query adds the flag to an item for which
  `should_inherit_track_caller` holds:

  ```rust
  fn should_inherit_track_caller(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
      tcx.trait_item_of(def_id).is_some_and(|id| {
          tcx.codegen_fn_attrs(id).flags.intersects(CodegenFnAttrFlags::TRACK_CALLER)
      })
  }
  ```

  So a method in a trait impl is tracked if it carries the attribute itself *or* the trait's
  declaration of that method does. The Reference states the same rule
  (`attributes.codegen.track_caller.traits`).
* **ABI restriction (`E0737`).** The error is emitted during AST validation, not in codegen:

  ```rust
  // #[track_caller] can only be used with the rust ABI.
  if let Some(attr) = attr::find_by_name(attrs, sym::track_caller)
      && extern_abi != ExternAbi::Rust
  { self.dcx().emit_err(errors::RequiresRustAbi { .. }); }
  ```

  The check runs only when the function header has an `extern` qualifier, and for items of an
  `extern` block (`self.extern_mod_abi != Some(ExternAbi::Rust)`). The comparison is against
  `ExternAbi::Rust` alone. Executed: `extern "C" fn`, `extern "rust-call" fn` (with
  `unboxed_closures`), and a function in an `extern "C"` block are each rejected with `E0737`;
  `extern "Rust" fn` and a function in an `extern "Rust"` block are accepted. `codegen_attrs.rs`
  only re-asserts this with `delayed_bug("`#[track_caller]` requires the Rust ABI")` and skips
  the assertion for closures.
* **Other rejections (executed on R-May).** `#[track_caller] fn main` ("`main` function is not
  allowed to be `#[track_caller]`"); with `#[unsafe(naked)]` (`E0736`); on a closure without the
  feature gate (`E0658`); on a struct; and a tracked function may not perform `become` ("a
  function marked with `#[track_caller]` cannot perform a tail-call"). Accepted: bodiless trait
  methods, provided trait methods, impl methods.
* **`requires_caller_location`.** This predicate, not the raw flag, is what the ABI, codegen,
  the inliner's pretty-printer and the interpreter consult. R-May:

  ```rust
  pub fn requires_caller_location(&self, tcx: TyCtxt<'_>) -> bool {
      match *self {
          InstanceKind::Item(def_id) | InstanceKind::Virtual(def_id, _) => {
              tcx.body_codegen_attrs(def_id).flags.contains(CodegenFnAttrFlags::TRACK_CALLER)
          }
          InstanceKind::ClosureOnceShim { call_once: _, track_caller } => track_caller,
          _ => false,
      }
  }
  ```

  For `Virtual(def_id, _)` the `def_id` is the *trait's* method, so a virtual call site passes a
  location exactly when the trait declaration is tracked. A reify shim is never tracked. At
  R-Oct and R-Nov the first arm also covers `InstanceKind::Shim(ShimKind::VTable(def_id))` (the
  shim for by-value unsized `self`); that case was not exercised.

### 2. The implicit argument in `FnAbi`, in codegen, and on x86-64

Basis: source (all three revisions) + execution (R-May).

* **`FnAbi`.** `FnAbiDesc::for_instance` sets
  `caller_location: instance.def.requires_caller_location(tcx).then(|| tcx.caller_location_ty())`
  and `FnAbiDesc::for_fn_ptr` sets `caller_location: None`. `fn_abi_new_uncached` builds

  ```rust
  args: inputs.iter().copied()
      .chain(extra_args.iter().copied())
      .chain(caller_location)
      .enumerate().map(|(i, ty)| arg_of(ty, Some(i))).collect::<Result<_, _>>()?,
  ```

  For `"rust-call"` signatures `extra_args` are the untupled arguments, so the location comes
  last there too. `caller_location_ty` is `&'static Location<'static>`.
* **Call sites.** `codegen_call_terminator` first replaces the span of the terminator's
  `source_info` by the call's `fn_span`, then, if the callee instance requires a location,
  asserts `fn_abi.args.len() == mir_args + 1` ("`#[track_caller]` fn's must have 1 more argument
  in their ABI than in their MIR") and passes `self.get_caller_location(bx, source_info)` as the
  last argument.
* **Callee prologue.** `arg_local_refs` makes the mirror-image assertion, requires the last ABI
  argument to be `PassMode::Direct`, and stores it in `FunctionCx::caller_location`.
* **`get_caller_location`** is
  `self.mir.caller_location_span(source_info, self.caller_location, tcx, |span| const_loc(span))`.
  The same function serves the `caller_location` intrinsic (`sym::caller_location` in
  `mir/intrinsic.rs`) and the location passed to panic lang items from `Assert` terminators.
* **x86-64 observations** (disassembly of `support/probe_src/abi_probe.rs`; `0x10` is the offset
  of `Location::line`):

  | Function | Callee reads location from | Shim / call site writes |
  | --- | --- | --- |
  | `abi_tracked0()` | `mov 0x10(%rdi),%eax` | `lea <Location>(%rip),%rdi` then `jmp` |
  | `abi_tracked1(a)` | `add 0x10(%rsi),%eax` | `lea <Location>(%rip),%rsi` then `jmp` |
  | `abi_tracked2(a, b)` | `add 0x10(%rdx),%eax` | `lea <Location>(%rip),%rdx` then `jmp` |
  | `abi_tracked6(a..f)` | `mov 0x8(%rsp),%r9` … `add 0x10(%r9),%eax` | (not called in the probe) |
  | `<A as DeclTracked>::m(&self, a)` | `add 0x10(%rdx),%esi` | virtual call site loads a constant and moves it to `%rdx` |
  | `abi_untracked1(a)` | none: `lea 0x24(%rdi),%eax` (line 36 folded) | none |

  A tracked caller forwards: `forward_tracked1(a)` is the single instruction
  `jmp *abi_tracked1@GOTPCREL(%rip)`, leaving its incoming `%rsi` in place. A call through a
  function pointer passes nothing: `call_through_pointer(fp, a)` is
  `mov %rdi,%rax; mov %rsi,%rdi; jmp *%rax`.
* **`Location` constant.** Each location is a 24-byte read-only constant: a pointer to the
  NUL-terminated file name, the name length (`u64`), `line: u32`, `col: u32`, matching
  `struct Location { filename: NonNull<str>, line: u32, col: u32, .. }`. Line and column come from
  `span_as_caller_location`: the start of the span, after replacing a macro-expanded span by its
  outermost expansion cause; the column is the display column plus one. For a method call the
  call's `fn_span` starts at the method name, so `a.m()` reports the column of `m`.

### 3. The scope walk

Basis: source (identical text at R-May lines 687–715, R-Oct 691–719, R-Nov 690–718 of
`compiler/rustc_middle/src/mir/mod.rs`).

```rust
pub fn caller_location_span<T>(&self, mut source_info: SourceInfo, caller_location: Option<T>,
                               tcx: TyCtxt<'tcx>, from_span: impl FnOnce(Span) -> T) -> T {
    loop {
        let scope_data = &self.source_scopes[source_info.scope];
        if let Some((callee, callsite_span)) = scope_data.inlined {
            // Stop inside the most nested non-`#[track_caller]` function,
            // before ever reaching its caller (which is irrelevant).
            if !callee.def.requires_caller_location(tcx) {
                return from_span(source_info.span);
            }
            source_info.span = callsite_span;
        }
        // Skip past all of the parents with `inlined: None`.
        match scope_data.inlined_parent_scope {
            Some(parent) => source_info.scope = parent,
            None => break,
        }
    }
    // No inlined `SourceScope`s, or all of them were `#[track_caller]`.
    caller_location.unwrap_or_else(|| from_span(source_info.span))
}
```

The walk reads two fields of `SourceScopeData`: `inlined: Option<(ty::Instance, Span)>` ("Whether
this scope is the root of a scope tree of another body, inlined into this body by the MIR
inliner. `ty::Instance` is the callee, and the `Span` is the call site.") and
`inlined_parent_scope: Option<SourceScope>` ("Nearest (transitive) parent scope (if any) which is
inlined."). `SourceScopeLocalData` holds only `lint_root` and plays no part. In optimised MIR the
intrinsic call survives as a `Call` terminator (`_1 = caller_location() -> [return: bb1, unwind
unreachable]`); there is no MIR-level lowering of it.

### 4. What the MIR inliner does to scopes

Basis: source (identical text at R-May lines 1257–1277, R-Oct and R-Nov 1233–1253 of
`compiler/rustc_mir_transform/src/inline.rs`) + execution (R-May).

`inline.rs` contains no caller-location logic at all (no occurrence of `caller_location` or
`track_caller`). It preserves locations purely by how it rewrites scopes when it appends the
callee's `source_scopes` to the caller's. `map_scope` adds the caller's old scope count; the call
site is `SourceInfo { span: fn_span, ..terminator.source_info }`; and the default
`super_source_scope_data` called first renumbers `parent_scope` and `inlined_parent_scope`
through `visit_source_scope`:

```rust
fn visit_source_scope_data(&mut self, scope_data: &mut SourceScopeData<'tcx>) {
    self.super_source_scope_data(scope_data);
    if scope_data.parent_scope.is_none() {
        // Attach the outermost callee scope as a child of the callsite
        // scope, via the `parent_scope` and `inlined_parent_scope` chains.
        scope_data.parent_scope = Some(self.callsite.source_info.scope);
        assert_eq!(scope_data.inlined_parent_scope, None);
        scope_data.inlined_parent_scope = if self.callsite_scope.inlined.is_some() {
            Some(self.callsite.source_info.scope)
        } else {
            self.callsite_scope.inlined_parent_scope
        };
        // Mark the outermost callee scope as an inlined one.
        assert_eq!(scope_data.inlined, None);
        scope_data.inlined = Some((self.callsite.callee, self.callsite.source_info.span));
    } else if scope_data.inlined_parent_scope.is_none() {
        // Make it easy to find the scope with `inlined` set above.
        scope_data.inlined_parent_scope = Some(self.map_scope(OUTERMOST_SOURCE_SCOPE));
    }
}
```

Statements keep their spans and get renumbered scopes. The consequence, proved in §10, is that a
callee statement's walk after the splice equals its walk in the stand-alone callee run with the
implicit argument the call site would pass.

Executed evidence from the probe's `wrapper_site` (pretty MIR with `-Zmir-include-spans=on`; the
pretty-printer prints `#[track_caller]` for inlined callees that require a location):

```text
fn wrapper_site() -> (u32, u32) {
    scope 1 (inlined untracked_wrapper) { // at track_caller_probe.rs:54:5: 54:24
        scope 2 (inlined #[track_caller] top_tracked) { // at track_caller_probe.rs:49:5: 49:18
            scope 3 (inlined #[track_caller] mid_tracked) { // at track_caller_probe.rs:38:5: 38:18
                scope 4 (inlined #[track_caller] leaf_tracked) { // at track_caller_probe.rs:32:5: 32:19
                    scope 5 (inlined #[track_caller] Location::<'_>::caller) { // at track_caller_probe.rs:26:9: 26:27
    ...
    bb0: { _1 = caller_location() -> [return: bb1, unwind unreachable]; // scope 5 at .../core/src/panic/location.rs:181:9
```

The walk from scope 5 passes four tracked scopes (span becomes 26:9, 32:5, 38:5, 49:5) and stops
at the untracked scope 1, returning 49:5, which is what the program prints. `direct_site`, whose
outermost inlined scope is the tracked `top_tracked` at 43:5, has the same basic blocks once the
pretty-printer's scope and span comments are stripped, and prints 43:5. A Python transcription of the walk applied to the dumped scope tables
predicts the executed output for `direct_site`, `wrapper_site` and `tracked_outer_site`.

### 5. The regime matrix (executed on R-May)

Basis: execution. All four configurations (native without and with MIR inlining, Miri without and
with MIR inlining) print the same `line:column` pairs; line numbers refer to
`support/probe_src/track_caller_probe.rs` and are checked against `@NAME` markers.

| Observation | Situation | Reported | Is the … |
| --- | --- | --- | --- |
| `UNTRACKED_SELF` | `Location::caller()` in an untracked function | 19:9 | call to `Location::caller` itself |
| `DIRECT` | untracked function calls a three-level tracked chain | 43:5 | outermost tracked call site |
| `WRAPPER` | same chain called inside an untracked wrapper | 49:5 | call inside the wrapper, not the wrapper's call site (54) |
| `TRACKED_OUTER_WRAPPER` | a tracked function calls the untracked wrapper | 49:5 | same; neither line 61 nor the outer call site 66 |
| `FP1`, `FP2` | two calls through `fn() -> Pos` | 72:1 | definition header of the tracked function |
| `FNPTR_DIRECT` | direct call to the same function | 81:18 | call site |
| `DYN_DECL_TRACKED` | `&dyn Trait`, attribute on the trait declaration | 121:22 | virtual call site |
| `DYN_PROVIDED` | `&dyn Trait`, tracked provided method | 122:26 | virtual call site |
| `DYN_IMPL_ONLY` | `&dyn Trait`, attribute on the impl only | 108:5 | impl method's definition header |
| `STATIC_IMPL_ONLY` | same method, static dispatch | 125:30 | call site |
| `GENERIC_STATIC` | generic `t.m()` with `T = B` | 115:7 | call site inside the generic function |
| `GENERIC_DYN` | same generic function with `T = dyn Trait` | 108:5 | impl method's definition header |

The interpreted MIR was confirmed to be inlined in the fourth configuration (Miri's
`runtime-optimized` dump of `direct_site` contains `(inlined #[track_caller] top_tracked)`).

### 6. Reify shims and function pointers

Basis: source (all three revisions) + execution (R-May).

* **Creation.** Casting a function item to a function pointer (`PointerCoercion::ReifyFnPointer`)
  resolves the target with `Instance::resolve_for_fn_ptr` in the collector, in codegen and in the
  interpreter:

  ```rust
  let reason = tcx.sess.is_sanitizer_kcfi_enabled().then_some(ReifyReason::FnPtr);
  ...
  InstanceKind::Item(def) if resolved.def.requires_caller_location(tcx) => {
      resolved.def = InstanceKind::ReifyShim(def, reason);
  }
  InstanceKind::Virtual(def_id, _) => { resolved.def = InstanceKind::ReifyShim(def_id, reason); }
  ```

  Without KCFI `reason` is `None`. An untracked function is returned as itself (executed:
  `reify_untracked1` returns the address of `abi_untracked1`; no shim symbol exists for it).
* **Body.** `make_shim` handles `ReifyShim(def_id, _)` with
  `build_call_shim(tcx, instance, None, CallKind::Direct(def_id))`. `build_call_shim` takes
  `let span = tcx.def_span(def_id);`, uses `SourceInfo::outermost(span)` for every statement and
  `fn_span: span` for the call, and `new_body` gives the body a single scope with
  `inlined: None, inlined_parent_scope: None`. The shim instance is untracked, so its call
  terminator passes `Location(def_span)`. Dumped MIR:

  ```text
  fn leaf_tracked_noinline() -> (u32, u32) {
      bb0: { _0 = leaf_tracked_noinline() -> [return: bb1, unwind continue]; // scope 0 at track_caller_probe.rs:72:1: 72:34
      bb1: { return; }
  ```

  `def_span` covers the header only (`fn leaf_tracked_noinline() -> Pos`), starts at the first
  token of the item (`fn`, or `pub` for a public item) and excludes attributes on earlier lines.
* **Machine code.** Each shim is `lea <Location constant>(%rip),%REG; jmp *<tracked fn>` with
  `REG` the register of §2 and the constant's `(line, column)` equal to the definition header:
  `(11,1)`, `(17,1)`, `(23,1)` for the three free functions of the ABI probe.
* **`ReifyReason`.** Symbol names show the reason: without KCFI all four shims of the ABI probe
  end in `reify`; emitting assembly with `-Zsanitizer=kcfi` gives three `reify_fnptr` and one
  `reify_vtable` (mapping in `rustc_symbol_mangling/src/v0.rs`). The KCFI build was only compiled
  to assembly, with `-C panic=abort -Cunsafe-allow-abi-mismatch=sanitizer`, and not run.
* **Tail calls (unstable).** `become f()` to a tracked `f` is compiled as a call to the reify
  shim: codegen re-resolves the callee with `resolve_for_fn_ptr`, the collector records the use
  as indirect, and the lint `tail_call_track_caller` fires ("tail calling a function marked with
  `#[track_caller]` has no special effect"). Executed: native code reports the definition of `f`
  (line 8 of `tail_call_probe.rs`).

### 7. Vtable slots

Basis: source (all three revisions) + execution (R-May).

`vtable_entries` resolves each method with `Instance::expect_resolve_for_vtable`:

```rust
let needs_track_caller_shim = resolved.def.requires_caller_location(tcx)
    // 2) The caller location parameter comes from having `#[track_caller]`
    // on the implementation, and *not* on the trait method.
    && !tcx.should_inherit_track_caller(def)
    // If the method implementation comes from the trait definition itself ...
    && !matches!(tcx.opt_associated_item(def),
                 Some(ty::AssocItem { container: ty::AssocContainer::Trait, .. }));
if needs_track_caller_shim {
    if tcx.is_closure_like(def) {
        resolved = Instance { def: InstanceKind::ReifyShim(def_id, reason), args };
    } else {
        resolved.def = InstanceKind::ReifyShim(def, reason);
    }
}
```

with `reason = is_sanitizer_kcfi_enabled().then_some(ReifyReason::Vtable)`. Together with
`requires_caller_location` on `Virtual` (§1) this gives three cases:

| `#[track_caller]` on | Vtable slot | Virtual call site passes | Implementation observes |
| --- | --- | --- | --- |
| trait declaration (impl may or may not repeat it; includes provided bodies) | the implementation itself | its own location | the virtual call site |
| impl method only | reify shim in front of the implementation | nothing | the impl method's definition header |
| neither | the implementation itself | nothing | (not tracked) |

Executed: the vtable constant for `A as DeclTracked` holds the symbol of `<A as DeclTracked>::m`;
the one for `B as DeclUntracked` holds `<B as DeclUntracked>::m::{shim:reify}`. The virtual call
site for `DeclTracked` loads a `Location` constant for its own line (115) and jumps through slot
`0x18`; the one for `DeclUntracked` is `mov 0x18(%rsi),%rax; mov %rdx,%rsi; jmp *%rax`.

**Closures (unstable `closure_track_caller`).** For a closure-like implementation the shim is
built for the `Fn*` *trait method* (`def_id`), not for the closure. Its `def_span` is therefore
in `core`: a tracked closure called through `&dyn Fn()` reports `ops/function.rs:79` and through
`Box<dyn FnOnce()>` reports `ops/function.rs:250`, the declarations of `Fn::call` and
`FnOnce::call_once` at R-May. Called directly or through a generic `F: Fn()`/`F: FnOnce()` it
reports the call site (lines 26, 16 and 21 of `closure_probe.rs`). `fn_once_adapter_instance`
copies the closure's flag into `ClosureOnceShim { track_caller }`.

### 8. Two mechanisms in the interpreter, and where they disagree with codegen

Basis: source (R-May, R-Oct, R-Nov) + execution (R-May) + derived.

* **R-May.** The intrinsic is implemented as
  `let span = self.find_closest_untracked_caller_location();`. That function iterates
  `self.stack().iter().rev()`; for each frame it takes the current `source_info` (with `fn_span`
  if the frame is at a `Call` terminator) and calls
  `frame.body.caller_location_span(source_info, if tracked { Some(Err(())) } else { None }, tcx, Ok)`,
  returning the first `Ok(span)`. `init_stack_frame` only *counts* the argument ("If
  `with_caller_location` is set we pretend there is an extra argument (that we will not pass; our
  `caller_location` intrinsic implementation walks the stack instead)").
* **R-Oct, R-Nov.** `Frame` has `track_caller_arg: Option<Span>` ("This is `Some` if and only if
  `instance.def.requires_caller_location` returns `true`"), set in `init_stack_frame` from
  `with_caller_location.then(|| self.caller_location())`; the intrinsic calls
  `frame.body.caller_location_span(source_info, frame.track_caller_arg, tcx, identity)`; and

  ```rust
  match (instance.def.requires_caller_location(*self.tcx), with_caller_location) {
      (false, true) => throw_ub_format!("calling a non-`#[track_caller]` function from a `#[track_caller]` declaration"),
      (true, false) => throw_ub_format!("calling a `#[track_caller]` function from a non-`#[track_caller]` declaration"),
      _ => {}
  }
  ```
* **Agreement.** Derived, and proved for the model in §10: when every tracked frame was called
  with the location its caller computes at the call statement, the stack walk and the implicit
  argument give the same answer, because the caller's frame is still at that call statement.
  This is why native code and Miri agree on the whole matrix of §5 at R-May.
* **Disagreement 1: declaration mismatch.** The Reference
  (`attributes.codegen.track_caller.extern`) makes it undefined behaviour to call a tracked
  definition through an `extern "Rust"` declaration without the attribute. Executed at R-May
  under Miri only (`extern_decl_mismatch_interpreter_only.rs`): the program **runs to completion
  with exit status 0 and prints the call-site line (24)**. The interpreter decides "tracked" from
  the callee instance and walks to the caller, so it never notices that nothing was passed;
  native code would read an unwritten argument slot (§2). Derived from source, not executed: at
  R-Oct and R-Nov the same program takes the `(true, false)` arm above. With the attribute on
  the declaration too, native and Miri both report the call site (line 20).
* **Disagreement 2: tail calls.** Executed at R-May (`tail_call_probe.rs`): native code prints the
  callee's definition line (8, via the shim), Miri prints line 23, the call site of the
  *tail-calling function* in `main`, because `init_fn_tail_call` pops the calling frame before
  pushing the callee. An ordinary call in the same program prints line 19 in both.

### 9. Documentation compared with the implementation

Basis: documentation + source + execution.

* The Reference describes the behaviour as walking "up the stack from `f`'s frame to find the
  nearest frame of an *unattributed* function" and says the result "is a hint and implementations
  are not required to preserve it" (`attributes.codegen.track_caller.hint`). The invariance under
  inlining established here is a property of this implementation, not a language guarantee.
* The Reference (`attributes.codegen.track_caller.decay`): "coercing a function with
  `#[track_caller]` to a function pointer creates a shim which appears to observers to have been
  called at the attributed function's definition site, losing actual caller information across
  virtual calls. A common example of this coercion is the creation of a trait object whose
  methods are attributed." Source and execution agree for function pointers and for
  *impl-only* attributes; for an attribute on the trait declaration no shim is created and the
  virtual call site is reported (§7). The two sources are left side by side.
* RFC 2091 specifies a different implementation (redirection through a generated closure and a
  placeholder intrinsic), says of dynamic calls "Currently this will report where the function
  is declared", and lists trait methods as unresolved ("Currently the RFC simply prohibit
  applying `#[track_caller]` to trait methods"). It is historical context for the surface
  behaviour, not a description of the mechanism above.
* The `ReifyReason` documentation says the reason "will only be populated if we are compiling in
  a mode that needs these shims to be separable, currently only when KCFI is enabled"; execution
  agrees (§6).

### 10. The mechanised model

Basis: derived (Lean 4 kernel-checked); the correspondence with `rustc` is by transcription and
by the executed cross-checks named below.

`support/TrackCallerAbiAndReifySoundness.lean` imports nothing beyond the Lean prelude. Spans are
natural numbers; an inlined callee is the pair `(requires_caller_location, call-site span)`.

*Definitions transcribed from the source.*

* `resolveChain : List (Bool × Span) → Option Span → Span → Span` — the walk of §3 on the list of
  enclosing inlined callees, innermost first.
* `ScopeTree σ := σ → ScopeData σ` with fields `parentScope`, `inlined`, `inlinedParentScope`, and
  `findOutermostTrackedCallSite tree implicit fuel scope span` — the same loop on the
  pointer-linked table (`fuel` bounds iterations).
* `remapScopesOnInline caller callsiteScope callsiteSpan calleeTracked callee calleeRoot :
  ScopeTree (Sum σ τ)` — the rewriting of §4. Caller scopes are `Sum.inl`, appended callee scopes
  `Sum.inr`; the tagged sum stands for `new_scopes.start + index`. The two `assert_eq!`s become
  the hypothesis `CalleeRootWellFormed`.
* `Node`/`Nodes` — a call tree whose call nodes are either real calls (`call`: new frame,
  implicit argument iff tracked) or inlined (`inl`: chain extended by `(tracked, span)`), with
  `observations` listing every value of the intrinsic.
* `stackWalkLocation` — the R-May interpreter's stack walk; `Frame.codegenLocation` — the
  implicit-argument computation; `Disciplined` — the calling discipline.
* `lowerFnAbiTrackCaller mirArity requiresCallerLocation : List ArgClass` —
  `replicate mirArity value ++ (if requiresCallerLocation then [location] else [])`;
  `fnPtrAbi n := lowerFnAbiTrackCaller n false`.
* Argument slots `Regs := Nat → Word` with `Word ::= val | loc span | stale`; `writeArgs` (a call
  passing exactly the explicit arguments), `writeLocationSlot n span`, and
  `reifyToFnPtrShim n defSpan := writeLocationSlot n defSpan`.
* `MethodAttrs`, `needsTrackCallerShim`, `vtableSlot`, `vtableMethodDispatch` — the rule of §7.

*Theorems.*

| Theorem | Content | Axioms |
| --- | --- | --- |
| `resolveChain_append` | `resolveChain (inner ++ (t, cs) :: outer) imp s = resolveChain inner (if t then some (resolveChain outer imp cs) else none) s` | none |
| `find_of_hasChain` | the pointer walk equals `resolveChain` of the scope's chain for all sufficiently large fuel | `propext` |
| `hasChain_remap_callee` | after `remapScopesOnInline`, a callee scope's chain is `inner ++ (calleeTracked, callsiteSpan) :: outer` | `propext` |
| `remapScopesOnInline_exact` | **one inlining step is exact:** a callee statement's walk after the splice equals its walk in the stand-alone callee with implicit argument `if calleeTracked then (walk of the call site in the caller) else none` | `propext` |
| `remapScopesOnInline_caller_unchanged` | statements already in the caller resolve as before | `propext` |
| `location_caller_invariant_under_inlining` | **(1)** `InlineSeq a b → observations chain imp a = observations chain imp b`, where `InlineSeq` is any finite sequence of steps each replacing some call node, tracked or untracked, at any depth, by its inlined body | `propext` |
| `stackWalk_eq_codegen` | on a `Disciplined` stack the stack walk equals the top frame's implicit-argument computation | none |
| `mismatched_declaration_diverges` | off the discipline they differ: the walk gives the call site, the slot read gives the stale value | none |
| `lowerFnAbiTrackCaller_length`, `reifyToFnPtrShim_abi_safe` | **(2)** ABI arity is `N + 1` exactly for tracked instances; for every prior slot state the shim's output is well-typed for the tracked ABI, forwards slots `< N` unchanged and holds `loc defSpan` in slot `N` | `propext` |
| `vtable_abi_agreement`, `vtable_decl_tracked_reports_call_site`, `vtable_impl_only_reports_impl_definition`, `vtable_untracked_reads_nothing`, `vtableMethodDispatch_ignores_stale` | **(3)** for all eight attribute placements the virtual caller's ABI equals the slot's ABI; declaration tracked ⇒ direct slot and the call site is read; impl-only ⇒ shim and the impl definition is read | none |
| `ce1_omitting_reify_shim_corrupts_implicit_location_register_abi` | **sharpness:** without the shim slot `N` is whatever it held before the call; that state can be ill-typed for the callee's ABI, or well-typed and equal to *any* location; with the shim it is the definition span for every prior state | `propext` |
| `ce2_collapsing_untracked_inline_scope_leaks_outer_caller_location` | **sharpness:** on the probe's `tracked_outer_site` chain the walk gives 49:5; with the untracked scope's entry removed it gives 66:5, the outer tracked function's call site | none |
| `probe_scope_tables_reproduce_executed_locations`, `probe_remap_reproduces_executed_location` | the transcribed walk and rewriting, run on the scope tables dumped by the probe, give 43:5, 49:5, 49:5 | none |

`ce2` has a general form (`collapsing_untracked_scope_leaks_enclosing_location`) and a companion
(`walking_through_untracked_scope_reports_wrapper_call_site`: not stopping at the wrapper yields
54:5, the wrapper's own call site).

*Audit.* Checked with Lean `v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`) with
`-DwarningAsError=true -Ddebug.skipKernelTC=false`. The 25 theorems printed by `#print axioms`
depend on `propext` (10) or on nothing (15); none depends on `Classical.choice`, `sorryAx`,
`Quot.sound` or `Lean.ofReduceBool`. `support/EnvironmentAudit.lean` walks all constants of the
compiled module (133 theorems, 248 definitions, 17 inductive types): no axiom, no opaque,
unsafe or partial constant, no use of `Acc.rec` or `WellFounded.*`, and `propext` as the only
reachable axiom. The audit was shown to fail on a module containing an admitted proof, an added
axiom, a partial definition, well-founded recursion, a classical proof and a compiled-evaluation
proof.

*A Lean observation made on the way.* On Lean `v4.34.1` a computable structurally recursive
`def` still gets an unsafe compiled helper constant (suffix `_unsafe_rec`) that is marked
partial; the same definition marked `noncomputable` does not, and `rfl`/`decide` proofs about it
are unaffected. The recursive definitions of the model are therefore `noncomputable`.

*What the model does not capture.* Spans, files and columns beyond identity; `ty::Instance`
beyond the boolean; statements other than the intrinsic and calls; unwinding; the real argument
classification of the Rust ABI (`Regs` is an indexed slot array, not registers and stack); and
the derivation of `MethodAttrs` from items. The vtable theorems transcribe `rustc`'s condition
and check its consequences; they do not derive it.

### 11. Anneal at `c131b320eeeb26ef692e5afd5ec8db49ee518613`

Basis: source.

* The trusted MIR syntax (`trusted/lean/Trusted/MirAst.lean`) models post-cleanup runtime MIR
  (`Runtime(PostCleanup)`). In `rustc` that is the form bodies have before
  `run_optimization_passes`, which is where both inlining passes run (checked at R-May and
  R-Nov; the capture tool's own `rustc` pin was not audited), so such bodies carry no inlined
  scopes. Its `Body` has
  `argumentCount`, `locals`, `basicBlocks`, `isUnsafe`, `identity` and **no source scopes**; its
  `TerminatorKind.call callee args dst target unwind` has **no `fn_span`**; indirect calls and
  `TailCall` are `.unsupported`.
* The trusted semantics (`trusted/lean/Trusted/MirSemantics.lean`) steps every call to a fault
  in `evalTerminator`:
  `| .unwindResume | .assert _ _ _ _ _ | .call _ _ _ _ _ | .unsupported => .fault .unsupported`.
  The same arm covers `Assert` terminators, the other MIR construct whose compiled form consumes
  a caller location. The call case is documented as "Interprocedural calls fail closed: … any reachable `TerminatorKind.call` steps
  to `.fault .unsupported` and therefore refutes `WellFormed` fail-closed."
* Derived: at this commit no value of `Location::caller()` can reach a result verified against
  the trusted semantics, because reaching the intrinsic requires a call. `#[track_caller]`
  therefore cannot currently make a verified statement wrong; it can only make a body
  unverifiable. Lifting the call restriction would require adding spans and the two scope fields
  of §3 to the trusted syntax, or treating the intrinsic's result as an unconstrained value.
* The vendored interpreter (`vendor/lean-miri`, recorded in `UPSTREAM_PIN.json` as
  `proofs-rs/lean-miri` at `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` with `rustc_commit`
  `8144389c…`, i.e. R-Oct) follows the R-Oct design: `Frame.trackCallerArg : Option SpanRef`
  (`Miri/Interpreter/Stack.lean`), `callerLocationSpan`, a fuel-bounded transcription of §3
  (`Miri/Interpreter/VirtualCalls.lean`), the check
  `if requiresLocation != withCallerLocation then throw (.undefinedBehavior "caller/callee
  #[track_caller] mismatch")` (`Miri/Interpreter/Call.lean`), and an input decoder reading
  per-scope `inlined.callsite_span`, `inlined.requires_caller_location` and
  `inlined_parent_scope` (`Miri/Input/CompilerScopes.lean`), the same projection of
  `SourceScopeData` as `ScopeData` in §10. The only mention outside `vendor/` is
  `trackCallerArg := none` when the correspondence layer builds a dummy frame
  (`trusted/correspondence/Trusted/Correspondence.lean`).

## Boundaries

**Not examined.**

* Targets other than `x86_64-unknown-linux-gnu`; the Cranelift backend, which has its own
  `get_caller_location` calling the same `caller_location_span`; the GCC backend, which shares
  `rustc_codegen_ssa`; LTO; cross-crate inlining beyond the standard-library
  functions inlined in the probe; `-Zlocation-detail` (source: it can blank file, line and
  column).
* `Location::caller()` evaluated at compile time; promoted constants inside tracked functions
  (an R-Nov comment notes that `requires_caller_location` is true for such a promoted while no
  argument exists); coroutines and `async fn`; unwinding paths; panic messages produced through
  `Assert` terminators (source only).
* `InstanceKind::Shim(ShimKind::VTable)` being tracked at R-Oct/R-Nov; KCFI at run time (only
  assembly was emitted); `ClosureOnceShim` at the machine level; where the implicit argument sits
  for a `"rust-call"` signature in machine code (source only: after the untupled arguments).
* Whether any released stable toolchain matches either interpreter design; the revisions between
  the three audited ones.

**Unknown.**

* Run-time behaviour at R-Oct and R-Nov. No toolchain for them was available; in particular it is
  not confirmed by execution that Miri there reports the declaration mismatch, nor what it prints
  for the tail-call program. The earlier recorded R-Nov run (Evidence) shows only `FP1 = FP2` and
  native/Miri agreement for a program whose source is not preserved.
* Whether the R-May interpreter's acceptance of the mismatched declaration was regarded upstream
  as a defect; no issue or pull request was consulted.

**Known not to apply.**

* "`E0737` allows `"rust-call"`": refuted by source and execution (§1).
* "A function-pointer shim is `ReifyReason::FnPtr`": only under KCFI; otherwise the reason is
  `None` (§6).
* "`inline.rs` remaps caller locations" / "the walk goes through `SourceScopeLocalData`": the
  inliner has no caller-location code and the walk reads `inlined` and `inlined_parent_scope`
  (§3, §4). There is no `Intrinsic::CallerLocation` MIR construct; the intrinsic is an ordinary
  call to `core::intrinsics::caller_location`.
* "Trait objects always lose the caller location": false for attributes on the trait declaration
  (§7).
* "Miri and native code always agree": false for `become` at R-May (§8).

**Unsupported (by the subject).** The attribute on `main`, on naked functions, on weak lang
items, on non-`"Rust"` ABIs, on closures without `closure_track_caller`; `become` inside a
tracked function. In Anneal's trusted semantics at the audited commit: any call.

**Stronger conclusions the evidence does not establish.**

* That Rust guarantees inlining-invariant locations: the Reference calls the value a hint.
* That `rustc` is proved correct: the Lean theorems are about a hand-transcribed model, tied to
  the compiler by reading the source and by three executed scope tables.
* That the register assignment is stable: it is an observation of an unstable ABI at one
  optimisation level on one target.
* That absence of UB reports from Miri at R-May implies ABI agreement for tracked functions.

## Evidence

All commit identifiers were resolved against the GitHub API
(`GET /repos/<owner>/<repo>/commits/<ref>` or `.../git/commits/<sha>`) on 2026-11-21; source text
was read from the corresponding raw files and tarballs on the same day.

**`rust-lang/rust`** (line numbers: R-May / R-Nov; R-Oct given where compared).

| Path | Item | R-May | R-Nov |
| --- | --- | --- | --- |
| `compiler/rustc_ast_passes/src/ast_validation.rs` | `E0737` checks (extern block; fn header) | 1499–1506; 1704–1712 | 1759–1766; 1968–1976 |
| `compiler/rustc_ast_passes/src/{errors,diagnostics}.rs` | `RequiresRustAbi` (`code = E0737`) | `errors.rs` 1144 | `diagnostics.rs` 1212 |
| `compiler/rustc_error_codes/src/error_codes/E0737.md` | error text | whole file | whole file |
| `compiler/rustc_codegen_ssa/src/codegen_attrs.rs` | attribute arm; inherit; `should_inherit_track_caller` | 146–169; 356–358; 613–617 | 162–173; 438–440; 674–678 |
| `compiler/rustc_middle/src/middle/codegen_fn_attrs.rs` | `TRACK_CALLER = 1 << 8` | 185 | 202 |
| `compiler/rustc_middle/src/ty/instance.rs` | `ReifyReason`; shim variant; `requires_caller_location`; `resolve_for_fn_ptr`; `expect_resolve_for_vtable`; `fn_once_adapter_instance` | 45–58; 102; 311–319; 584–627; 629–705; 755–779 | 45–58; 125; 306–320; 655–702; 704–783; 833–861 |
| `compiler/rustc_ty_utils/src/abi.rs` | `for_fn_ptr`; `for_instance`; `.chain(caller_location)` | 241–259; 261–286; 593 | 241–257; 259–279; 593 |
| `compiler/rustc_mir_transform/src/shim.rs` | reify arm of `make_shim`; `new_body`; `build_call_shim`; `def_span` | 96–98; 407–439; 811–1041; 883 | 60–62; 374–406; 779–1007; 851 |
| `compiler/rustc_mir_transform/src/inline.rs` | call-site `source_info`; scope append; `map_scope`; `visit_source_scope_data` | 603; 1001; 1217–1221; 1257–1277 | 588; 977; 1193–1197; 1233–1253 |
| `compiler/rustc_middle/src/mir/visit.rs` | `super_source_scope_data` | 324–380 | 324–382 |
| `compiler/rustc_mir_transform/src/lib.rs` | cleanup passes end at `Runtime(PostCleanup)`; `ForceInline` and `Inline` in `run_optimization_passes` | 653–666; 675–770 (707, 709) | 682–689; from 698 (721, 723) |
| `compiler/rustc_mir_transform/src/lower_intrinsics.rs` | no occurrence of `caller_location` | whole file | whole file |
| `compiler/rustc_middle/src/mir/mod.rs` | `caller_location_span`; `SourceScopeData` | 687–715; 1478–1495 | 690–718; 1504–1521 |
| `compiler/rustc_middle/src/mir/pretty.rs` | `#[track_caller]` in scope headers | 508 | 522 |
| `compiler/rustc_middle/src/mir/consts.rs` | `span_as_caller_location` | 515–525 | 533–543 |
| `compiler/rustc_middle/src/ty/context.rs` | `caller_location_ty` | 1542–1550 | 1627–1635 |
| `compiler/rustc_codegen_ssa/src/mir/block.rs` | call `source_info`; tail-call arm; `needs_location`; `get_caller_location`; `Assert` | 907; 1052–1074; 1346–1374; 1871–1880; 740 | 973; from 1118; from 1435; 2171–2180; 798 |
| `compiler/rustc_codegen_ssa/src/mir/mod.rs` | callee prologue | 563–588 | 637–662 |
| `compiler/rustc_codegen_ssa/src/mir/intrinsic.rs` | intrinsic arm | 148–151 | 160–163 |
| `compiler/rustc_codegen_ssa/src/mir/rvalue.rs` | `ReifyFnPointer` cast | 416–430 | from 510 |
| `compiler/rustc_codegen_cranelift/src/common.rs` | Cranelift's `get_caller_location` | 420–421 | not compared |
| `compiler/rustc_const_eval/src/interpret/eval_context.rs` | stack walk / `caller_location` | 387–427 | 383–415 |
| `compiler/rustc_const_eval/src/interpret/call.rs` | argument counting; mismatch check; store | 435–439, 553–555 | 485–497, 575, 731–733 |
| `compiler/rustc_const_eval/src/interpret/stack.rs` | `track_caller_arg` | absent | 103 |
| `compiler/rustc_const_eval/src/interpret/cast.rs` | fn-pointer reification in the interpreter | 84–93 | 141–142 |
| `compiler/rustc_hir_typeck/src/closure.rs` | closure signatures built with `ExternAbi::RustCall` | 724, 861, 936, 1099 | not compared |
| `compiler/rustc_const_eval/src/interpret/intrinsics.rs` | intrinsic arm | 290–296 | 294–300 |
| `compiler/rustc_const_eval/src/util/caller_location.rs` | `alloc_caller_location` | 12–54 | 12–54 |
| `compiler/rustc_monomorphize/src/collector.rs` | fn-pointer use; tail-call note | 961; 835 | 981; 842 |
| `compiler/rustc_trait_selection/src/traits/vtable.rs` | vtable entry resolution | 288 | 283 |
| `compiler/rustc_symbol_mangling/src/v0.rs` | shim suffixes | 54–56 | 54–59 |
| `compiler/rustc_mir_build/src/check_tail_calls.rs` | `caller_needs_location` | 196–199 | 202–205 |
| `compiler/rustc_lint_defs/src/builtin.rs` | `TAIL_CALL_TRACK_CALLER` | 5390 | 5472 |
| `library/core/src/panic/location.rs` | `struct Location`; `Location::caller` | 39–47; 175–182 | 39–47; 184–186 |
| `library/core/src/ops/function.rs` | `Fn::call`; `FnOnce::call_once` | 79; 250 | 79; 250 |

R-Oct was compared for `caller_location_span` (691–719), `visit_source_scope_data` (1233–1253),
`requires_caller_location` (306–320), `resolve_for_fn_ptr` (655–702), `expect_resolve_for_vtable`
(704–783), `get_caller_location`, `should_inherit_track_caller`, the reify arm of `make_shim`
(`shim.rs` 60), `new_body` (367), `build_call_shim` (from 764), the interpreter's
`caller_location` (383), the store at `call.rs` 561 and the mismatch errors at `call.rs` 468/473.
The `rust-src` copies of `location.rs` and `ops/function.rs` shipped with the executed toolchain
are byte-identical to R-May.

**Documentation.** `rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`,
`src/attributes/codegen.md` lines 943–1053 (rules `attributes.codegen.track_caller.*`).
`rust-lang/rfcs` at `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `text/2091-inline-semantic.md`
lines 524–529, 613–625, 1161–1163.

**Anneal.** `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`:
`trusted/lean/Trusted/MirAst.lean` (`TerminatorKind` lines 785–795, `Body` lines 862–867, note on
cited revisions lines 40–48), `trusted/lean/Trusted/MirSemantics.lean` lines 1568–1569 and
1691–1694, `trusted/correspondence/Trusted/Correspondence.lean` line 1340,
`vendor/lean-miri/UPSTREAM_PIN.json`, `vendor/lean-miri/Miri/Interpreter/{Stack.lean (88),
VirtualCalls.lean (168–199), Call.lean (356–358, 385), Instance.lean (9–18)}`,
`vendor/lean-miri/Miri/Input/CompilerScopes.lean` (15–27). A case-insensitive search of that
tree for `track_caller`, `caller_location`, `CallerLocation`, `ReifyShim`, `ReifyReason` and
`trackCaller` finds one file outside `vendor/` (the correspondence layer) and 35 under
`vendor/lean-miri`. The same note in `MirAst.lean` names two further commits, both resolved but
not otherwise examined here: `rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`
(2026-05-30, the `rustc` pin of Anneal's MIR capture tool, one day before R-May) and the
vendored interpreter's upstream commit quoted in Findings §11.

**Execution (R-May, 2026-11-21).** `support/probe_track_caller_abi_and_shims.py` (Python standard
library only) compiles and runs everything in `support/probe_src/` inside a temporary directory
and writes `support/probe_track_caller_abi_and_shims.json`: toolchain versions, every command
line, per-configuration output, marker tables, the pretty MIR and scope tables of the three
inlined bodies, the shim MIR, assembly and disassembly of every function of the ABI probe, the
decoded `Location` constants, vtable entries, shim symbol suffixes with and without KCFI, the
compile matrix, and 223 self-checks (all passed: 87 ABI, 64 regime, 23 MIR, 23 closure, 11
compile matrix, 10 tail call, 4 declaration, 1 KCFI). Local path prefixes in the output are
replaced by `$SYSROOT`, `$MIRI_SYSROOT` and `$WORK`. Toolchain as recorded:
`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `miri 0.1.0 (14210df0e2 2026-05-31)`, LLVM 22.1.6.

**Mechanisation (2026-11-21).** `support/TrackCallerAbiAndReifySoundness.lean` (sha256
`e366e6eba03d63b3a31e776df6478a270a6debeb8f10ffd76d89d63039625c62`),
`support/EnvironmentAudit.lean` (sha256
`1ed6d1999fd49c956d9e5023e20856ea66abb02ce7172d7753ff5b4cd765d8b5`), and the transcript
`support/lean_check_output.txt`. The Lean runs were wrapped in a local memory and time limiter,
which does not affect the result.

**Earlier recorded run (R-Nov; not reproduced).** `support/prior_run_nightly_2026_11_11.json` is
an excerpt of a separately recorded run on `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`:
`DIRECT=22 WRAPPER_DEF_SITE=18 FP1=6 FP2=6` natively and under Miri, the shim MIR
`_0 = leaf_tracked_noinline() -> [return: bb1, unwind continue]`, and a shim symbol ending in
`5reify`. The program's source was not kept, so the line numbers cannot be interpreted; the
record is cited only for `FP1 = FP2`, native/Miri agreement and the shim's shape at R-Nov.

**Support files.**

| File | Content |
| --- | --- |
| `support/probe_track_caller_abi_and_shims.py` | probe harness |
| `support/probe_track_caller_abi_and_shims.json` | its output on R-May |
| `support/probe_src/track_caller_probe.rs` | regime matrix program |
| `support/probe_src/abi_probe.rs` | library crate for assembly evidence |
| `support/probe_src/closure_probe.rs`, `tail_call_probe.rs` | unstable-feature programs |
| `support/probe_src/extern_decl_match.rs`, `extern_decl_mismatch_interpreter_only.rs` | declaration agreement and (interpreter-only) mismatch |
| `support/probe_src/compile_matrix/*.rs` | eleven accept/reject inputs |
| `support/TrackCallerAbiAndReifySoundness.lean` | the model and proofs |
| `support/EnvironmentAudit.lean` | whole-module audit |
| `support/lean_check_output.txt` | Lean transcript |
| `support/prior_run_nightly_2026_11_11.json` | earlier R-Nov record |

## Revalidation

Cheapest first; each check establishes only what it names.

1. **Did the walk or the scope rewriting change?** Diff two functions against the text quoted in
   Findings §3 and §4: `Body::caller_location_span` in `compiler/rustc_middle/src/mir/mod.rs` and
   `Integrator::visit_source_scope_data` in `compiler/rustc_mir_transform/src/inline.rs`. If both
   are unchanged, findings 1–2 of the Summary and the model's `resolveChain` /
   `remapScopesOnInline` still transcribe the compiler.
2. **Did the predicate or the shim rules change?** Diff `InstanceKind::requires_caller_location`,
   `Instance::resolve_for_fn_ptr` and `Instance::expect_resolve_for_vtable` in
   `compiler/rustc_middle/src/ty/instance.rs`, and search `compiler/rustc_ty_utils/src/abi.rs` for
   `.chain(caller_location)`. A new arm in `requires_caller_location` (as happened between R-May
   and R-Oct) changes which instances carry the argument.
3. **Which interpreter mechanism does a toolchain have?** Search
   `compiler/rustc_const_eval/src/interpret/` for `find_closest_untracked_caller_location` (stack
   walk) versus `track_caller_arg` (stored argument).
4. **Rerun the probe** with a nightly toolchain that has the `miri` component and `rust-src`
   (the Miri sysroot is taken from `--miri-sysroot`, `MIRI_SYSROOT`, or
   `cargo miri setup --print-sysroot`):

   ```text
   cd support
   python3 probe_track_caller_abi_and_shims.py --out probe_rerun.json
   ```

   Exit status 0 means all self-checks passed. The harness derives expected lines from markers,
   so it survives edits to the sources. Two results are *classified* rather than asserted because
   they are expected to differ on newer toolchains: `extern_declarations.mismatch.miri.outcome`
   (`not_detected_reports_call_site_of_mismatched_declaration` on R-May; expected
   `undefined_behaviour_reported` where the interpreter stores `track_caller_arg`) and
   `tail_calls.miri_tail_call_outcome`. Failures of `abi/...` checks on another target or LLVM
   version indicate a different register assignment or code shape, not necessarily a semantic
   change; compare `abi.disassembly` by eye. `--skip-miri` runs the native part only. Never run
   `extern_decl_mismatch_interpreter_only.rs` natively.
5. **Recheck the model** with Lean `v4.34.1`:

   ```text
   cd support
   lean -DwarningAsError=true -Ddebug.skipKernelTC=false TrackCallerAbiAndReifySoundness.lean
   lean -o TrackCallerAbiAndReifySoundness.olean TrackCallerAbiAndReifySoundness.lean
   LEAN_PATH=. lean EnvironmentAudit.lean
   rm TrackCallerAbiAndReifySoundness.olean
   ```

   Expected: exit status 0 three times; 25 `#print axioms` lines mentioning at most `propext`;
   the audit's final line begins `audit passed`. Compare with `lean_check_output.txt`. If the
   probe's scope tables change (step 4), update the literal tables in section 8 of the Lean file
   from `mir.inlined_bodies` in the probe output; the general theorems do not depend on them.
6. **Anneal.** To see whether the trusted semantics still rejects calls, look for the arm
   `.call _ _ _ _ _` in `evalTerminator`'s fault case in
   `trusted/lean/Trusted/MirSemantics.lean` and for a `fn_span` or source-scope field in
   `trusted/lean/Trusted/MirAst.lean`. If calls become supported while those fields are still
   absent, the question of what `caller_location()` evaluates to has to be reopened.

What cannot be revalidated cheaply: run-time claims about R-Oct and R-Nov need those toolchains;
other targets need the ABI part of the probe to be adapted to their argument registers.
