# `rustc` Lint-Level Precedence Lattice, `forbid` Stickiness, `--cap-lints` vs. `--force-warn`, `#[expect]` Fulfillment, and `--check-cfg` / `#[cfg_attr(false, ...)]` Expansion Rules

## Summary

`rustc` governs lint severity, command-line overrides, RFC 2383 lint expectations, and conditional compilation diagnostics through four coupled but cleanly factored mechanisms whose interactions contradict naive "monotonic lattice" intuitions in several verification-relevant ways:

1. **Six-level precedence chain inside `LevelSpec(level, lint_id, src)`:** `rustc_lint_defs::Level` is totally ordered as `Allow < Expect < Warn < ForceWarn < Deny < Forbid` (`compiler/rustc_lint_defs/src/lib.rs`). Every effective entry in `LintLevelsBuilder` and `reveal_actual_level_spec` is not just a `Level`, but a validated tuple `LevelSpec { level, lint_id, src }` enforcing the invariant `(Allow | Warn | Deny | Forbid, None) | (Expect, Some(_)) | (ForceWarn, _)`.
2. **Direct vs. group `forbid` asymmetry (`E0453` vs. FCW `#81670`) and the mixed-source overwrite loophole:** Under `LintLevelsBuilder::insert_spec` (`compiler/rustc_lint/src/levels.rs`), lowering an active `Forbid` triggers hard error `E0453` *only* when `lint_added_lints` is true and the existing `old_src` is not a lint group (`is_lint_group(name) == false`); inner `Deny` is silently ignored without lowering. If `old_src` *is* a lint group (e.g., `#![forbid(unused)]` or `#![forbid(warnings)]` on a `Warn`-by-default lint), inner lowering emits the future-compatibility warning `forbidden_lint_groups` (which itself carries `ignore_deny_warnings`, preventing self-escalation under `forbid(warnings)`) and **replaces** the stored `LevelSpec` with the lower level. Moreover, because `insert_spec` overwrites `old_src` when a `#[forbid(group)]` attribute follows `#![forbid(member)]`, writing `#![forbid(dead_code)]`, `#[forbid(unused)]`, `#[allow(dead_code)]` compiles cleanly (`rc = 0`) with only `forbidden_lint_groups` (`a12b`).
3. **`--cap-lints` bounds revealed levels *except* CLI `--force-warn`, while `-A warnings` latches `can_emit_warnings` at session construction:** `reveal_actual_level_spec` (`compiler/rustc_middle/src/lint.rs`) first substitutes an active `warnings` directive when `baseSpec.level == Warn` (skipping `Deny`/`Forbid` for `ignore_deny_warnings` lints), then applies `min(level, opts.lint_cap)` **unless** `matches!(src, CommandLine(_, Level::ForceWarn))`, and finally applies `driver_lint_caps`. Consequently, `--cap-lints=allow` silences both `#[forbid(...)]` and `-F ...`, removes `E0453` (because `insert_spec` inspects the *revealed* `old_level`), yet `--force-warn` bypasses `--cap-lints=allow`, `#[allow(...)]`, and later `#![forbid(...)]`. First-wins/last-wins asymmetry splits across CLI options: `--cap-lints` is first-wins (`matches.opt_str("cap-lints")`), CLI `-F`/`--force-warn` ignore subsequent CLI flags (`matches!(current.level(), ForceWarn | Forbid)`), while `-D`/`-W`/`-A` overwrite each other left-to-right except that `build_session` computes `can_emit_warnings = !(warnings_allow || cap_lints_allow)` **once** from CLI flags (`compiler/rustc_session/src/session.rs`), permanently dropping plain `Warning` emissions even against crate-level `#![warn(warnings)]`.
4. **RFC 2383 `#[expect]` conservation and `ForceWarning` ID pass-through:** `Level::ForceWarn` uniquely accepts `Some(LintExpectationId)` (`compiler/rustc_middle/src/lint.rs`), allowing `insert_spec` to preserve `#[expect(L)]` inside an active `--force-warn L` while emitting the `ForceWarning` diagnostic *and* marking the expectation fulfilled (`Expect | ForceWarning` in `compiler/rustc_errors/src/lib.rs`). Inner `#[allow(L)]` under `--force-warn L` discards `lint_id` (`LevelSpec::new(Level::ForceWarn, None, old_src)`), causing both the forced warning and `unfulfilled_lint_expectations` to fire (`a45`). `#[expect(unfulfilled_lint_expectations)]` returns early in `insert_spec` without altering the level and always emits unfulfilled with a dedicated note (`a46`). External-macro suppression returns before diagnostic construction (`emit_lint_base:470-474`), preventing foreign-macro violations from fulfilling local expectations.
5. **`--check-cfg` validation and `#[cfg_attr(false, ...)]` pre-validation erasure vs. `InvocationCollector` parent-ID routing:** `StripUnconfigured::expand_cfg_attr` (`compiler/rustc_expand/src/config.rs`) validates the outer `cfg_attr` predicate via `parse_cfg_attr` (`UNEXPECTED_CFGS` fires even when false: `b03`) and parses inner attributes strictly as syntactic `AttrItem`s (`b07`), then immediately replaces false `cfg_attr` forms with a `cfg_attr_trace` / `SyntheticAttr::CfgAttrTrace` marker before semantic attribute checking, `in_cfg`, or lint-level construction runs (`b04`, `b06b`, `b08`). Meanwhile, macro expansion (`InvocationCollector::flat_map_node` in `compiler/rustc_expand/src/expand.rs`) expands `#[cfg(...)]` and `#[cfg_attr(...)]` on an item *before* `assign_id!` updates `current_expansion.lint_node_id` to the item's new `NodeId`, so an item's own `#[expect(unexpected_cfgs)]` misses its own `#[cfg(unknown_flag)]` (emitting both warnings even when enabled with `--cfg=unknown_flag`: `b12b`), whereas crate-root `#![expect]` (`b12a`), enclosing `mod` `#[expect]` (`b12d`), and body `cfg!()` (`b12c`) catch and fulfill it.

All behavioral rules are corroborated across three independent evidence layers preserved in this package: (1) primary-source inspection across four `rust-lang/rust` revisions (`14210df0e`, `f8a08b688`, `3ef0c22cd`, and `main` at `277240238`) plus `joshlf/anneal` (`c131b320e`), (2) 70 live `rustc 1.98.0-nightly (14210df0e 2026-05-31)` compiler executions in `support/probe_results.json`, and (3) a self-contained 2,514-line Lean `v4.34.1` kernel-checked mechanization (`support/LintLevelLatticeCapLintsAndCheckCfgSoundness.lean`) containing 261 theorems and 564 `noncomputable def` declarations with `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, and `0` `._unsafe_rec` constants (`support/lean_axiom_audit_output.txt`).

---

## Applicability

This report characterizes the front-end lint-level, diagnostic-emission, expectation-checking, and conditional-compilation pipelines of `rustc` and their interface with Anneal's compiler-capture harness. Eight durable upstream subjects were examined (exact full 40-hex commit hashes are recorded in `REPORT.json` and `support/resolved_revisions.json`):

- **Primary executed compiler (`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly (14210df0e 2026-05-31)` on `x86_64-unknown-linux-gnu`):** All 70 live compilation and runtime probes in `support/probe_lint_lattice_and_check_cfg.py` and `support/probe_results.json` were executed on this toolchain on 2026-11-23.
- **Anneal-pinned compiler (`rust-lang/rust` @ `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`):** Direct diff comparison across the 18 audited files (`rustc_lint_defs`, `rustc_lint`, `rustc_middle`, `rustc_session`, `rustc_attr_parsing`, `rustc_expand`, `rustc_errors`, `rustc_interface`, `rustc_builtin_macros`) shows 17 of 18 files are byte-identical to `14210df0e`; only `compiler/rustc_lint_defs/src/builtin.rs` differs outside the lints modeled here (`WARNINGS`, `UNFULFILLED_LINT_EXPECTATIONS`, `FORBIDDEN_LINT_GROUPS`, `UNEXPECTED_CFGS`, `UNSAFE_CODE`, `DEAD_CODE`, `UNUSED`). Findings on `14210df0e` therefore transfer directly at source level to Anneal's pinned compiler libraries.
- **Newer upstream `rust-lang/rust` revisions (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` / `1.102.0-nightly` and `main` @ `277240238554297f93fa9ee3c7643dfa03ccbbb4` on 2026-11-23):** Audited at source level to determine continuity and refactors:
  - **Shared across all four `rust-lang/rust` revisions:** All six `Level` variants (`Allow`, `Expect`, `Warn`, `ForceWarn`, `Deny`, `Forbid`), `LevelSpec::new` invariant, `reveal_actual_level_spec` precedence logic (`warnings` substitution, `!matches!(src, CommandLine(_, ForceWarn))` cap bypass, `driver_lint_caps`), `LintLevelsBuilder::add_command_line` and `insert_spec` (`E0453` vs. `FORBIDDEN_LINT_GROUPS`, `Deny`-under-`Forbid` silent ignore, direct-then-group `forbid` source overwrite, `ForceWarn`+`Expect` ID retention, `unfulfilled_lint_expectations` early return), `build_session` `can_emit_warnings` latch, `emit_lint_base`, `DiagCtxtInner::emit_diagnostic`, `check_expectations` (`steal_fulfilled_expectation_ids` conservation), and `StripUnconfigured::expand_cfg_attr` / `in_cfg` ordering.
  - **Revision-specific refactors observed between `1.98.0-nightly` (`14210df0e`) and `3ef0c22cd` / `main` (`277240238`):**
    1. `StableLintExpectationId` retains `attr_index: u16` in `1.98.0-nightly`, whereas `main` removes `attr_index` and looks up `AttrId` via `find_attr!(tcx, id.hir_id, LintCheck(lints) => lints)` in `compiler/rustc_lint/src/expect.rs`.
    2. `lints_that_dont_need_to_run` in `compiler/rustc_lint/src/levels.rs` (`1.98.0-nightly`) is renamed `skippable_lints` in `1.102.0-nightly` and `main`.
    3. `LintLevelsBuilder::add` in `1.98.0-nightly` is split into `add_ast` (pre-expansion AST pass via `AttributeParser::parse_limited_all`) and `add_hir` (`hir::Attribute` HIR pass) in `main`, with comments explicitly preserving permissive pre-expansion skipping for attributes later stripped by `#[cfg(false)]`.
    4. `expand_cfg_attr` in `1.98.0-nightly` calls `attr_into_trace(trace_attr, sym::cfg_attr_trace)` with `EarlyParsedAttribute::CfgAttrTrace`, whereas `main` converts via `.convert_normal_to_synthetic(SyntheticAttr::CfgAttrTrace(cfg_predicate))` after evaluating `cfg_predicate`.
    5. `compiler/rustc_middle/src/lint.rs` changes `sess.dcx().span_delayed_bug(...)` (`1.98.0-nightly`) to `sess.dcx().delayed_bug(...)` (`main`), and `LintLevelsBuilder` replaces `registered_tools` (`1.98.0-nightly`) with `registered_lint_tools` (`main`).
- **Anneal capture driver (`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Explains how Anneal's `AnalysisCallbacks::after_analysis` (`trusted/rustc-capture/src/driver.rs:75-84`) interacts with `check_expectations` and `--cap-lints` / `-Dwarnings` / `-A warnings` (`Passes` query order in `compiler/rustc_interface/src/passes.rs:1215-1257` and `trusted/rustc-capture/tests/compiler_session.rs:139-192`).
- **Specifications & Lean Toolchain (`rust-lang/rfcs` @ `f43d5789b8`, `rust-lang/reference` @ `c9cc32825b`, `leanprover/lean4` `v4.34.1` @ `5045d00564`):** Normative RFCs 1193 (`--cap-lints`) and 2383 (`#[expect]` and `reason = "..."`), Reference diagnostics documentation, and the Lean 4 kernel checker verifying `support/LintLevelLatticeCapLintsAndCheckCfgSoundness.lean`.

Claims in **Findings** explicitly note whether evidence comes from source inspection (`source`), RFC/Reference (`normative` / `documentation`), live `rustc 1.98.0-nightly` runs (`execution`), or Lean theorem proving (`derived`). No live probe binary was executed on `1.102.0-nightly` or `main` in this investigation; behavior on those revisions is established via source diffing rather than re-execution.

---

## Findings

### 1. The Six-Level Lint Precedence Lattice and `LevelSpec` Invariants

`Basis: source + execution + derived (Lean Part 2–3)`

`rustc_lint_defs::Level` defines six totally ordered variants with derived `PartialOrd, Ord` (`compiler/rustc_lint_defs/src/lib.rs:151-185` in `14210df0e`; lines `159-192` in `main`):

```text
Allow < Expect < Warn < ForceWarn < Deny < Forbid
```

- **Partial string parser (`Level::from_str`):** Only `"allow"`, `"warn"`, `"deny"`, and `"forbid"` parse from bare level names (`compiler/rustc_lint_defs/src/lib.rs:202-209`). `"expect"` returns `None` because constructing `Level::Expect` requires a `LintExpectationId` token, which also prevents `--cap-lints=expect` or `--cap-lints=force-warn` from ever passing `get_cmd_lint_options` (`compiler/rustc_session/src/config.rs:1916-1919`).
- **Paired invariant in `LevelSpec<Id>` (`compiler/rustc_middle/src/lint.rs:58-90`):** Both `level` and `lint_id` are private fields constructed exclusively through `LevelSpec::new(level, lint_id, src)` with a runtime panic guard:

| `LevelSpec::level` | Allowed `lint_id` | Origin Sources (`LintLevelSource`) | Error status (`Level::is_error`) |
| :--- | :--- | :--- | :--- |
| `Allow` | `None` only | `Default`, `Node` (`#[allow]`), `CommandLine` (`-A`) | `false` |
| `Expect` | `Some(id)` only | `Node` (`#[expect]`) only | `false` |
| `Warn` | `None` only | `Default`, `Node` (`#[warn]`), `CommandLine` (`-W`) | `false` |
| `ForceWarn` | `None` or `Some(id)` | `CommandLine(_, ForceWarn)` only (`--force-warn`) | `false` |
| `Deny` | `None` only | `Default`, `Node` (`#[deny]`), `CommandLine` (`-D`) | `true` |
| `Forbid` | `None` only | `Node` (`#[forbid]`), `CommandLine` (`-F`) (note: `Default` is modeled identically if present, though built-in lints use `Allow`/`Warn`/`Deny`) | `true` |

Note the structural asymmetry between `Expect` and `ForceWarn`: `ForceWarn` is the *only* non-`Expect` level permitted to hold `Some(LintExpectationId)`. This is what lets an expectation survive beneath a CLI `--force-warn`.

#### Command-Line Accumulation Order (`get_cmd_lint_options` and `add_command_line`)

In `compiler/rustc_session/src/config.rs:1892-1922` (`Rmain`: lines `1980-2009`), `get_cmd_lint_options` collects `-A`, `-W`, `--force-warn`, `-D`, and `-F` along with their CLI argument byte positions (`matches.opt_strs_pos(level.as_str())`), normalizes `'-'` to `'_'`, and sorts the vector stably by argument index (`lint_opts_with_position.sort_by_key(|x| x.0)`). Separately, `--cap-lints` is queried with `matches.opt_str("cap-lints")` — `getopts::Matches::opt_str` returns the **first** occurrence of the flag (`a20` vs. `a21`), not the last:

- `--cap-lints=allow --cap-lints=forbid` (`a20`): `opt_str` selects `allow`, silencing `#![forbid(unsafe_code)]` (`rc = 0`).
- `--cap-lints=forbid --cap-lints=allow` (`a21`): `opt_str` selects `forbid`, rejecting `#[allow(unsafe_code)] unsafe {}` (`rc = 1`).
- Mechanized in Lean theorem `cap_flag_first_wins` and `cap_flag_irrelevant_to_lintOpts`.

When `LintLevelsBuilder::add_command_line` replays `sess.opts.lint_opts` (`compiler/rustc_lint/src/levels.rs:497-565` in `14210df0e`; lines `483-552` in `main`):

1. **Special check on `--force-warn warnings`:** Before resolving lint IDs, if `lint_name_only == "warnings"` and `matches!(level, Level::ForceWarn)`, `rustc` emits error `E0602` (`UnsupportedGroup`; verified in `a32`: ``error[E0602]: `warnings` lint group is not supported with `--force-warn` ``).
2. **CLI stickiness rule (`levels.rs:552-557`):** For each `id` expanded from `store.find_lints(lint_name)`:
   ```rust
   if let Some(level_spec) = self.provider.current_specs().get(&id)
       && matches!(level_spec.level(), Level::ForceWarn | Level::Forbid)
   {
       continue;
   }
   ```
   Therefore, on the command line:
   - `-F L -A L` (`a23`): keeps `Forbid`.
   - `-A L -F L` (`a24`): raises `Allow` to `Forbid`.
   - `-D L -A L` (`a25`) / `-A L -D L` (`a26`): neither is sticky, so the later flag wins cleanly.
   - `--force-warn L -F L` (`a30`) keeps **`ForceWarn`** (`rc = 0`, warning emitted), whereas `-F L --force-warn L` (`a31`) keeps **`Forbid`** (`rc = 1`, error emitted)! Because both variants sit under `matches!(level_spec.level(), Level::ForceWarn | Level::Forbid)`, whichever appears **first** on the CLI locks out the other for that lint (`witness_a30_a31_cli_symmetry`).

---

### 2. `Forbid` Stickiness, `E0453`, `forbidden_lint_groups` (`#81670`), and the Mixed-Source Overwrite Loophole

`Basis: source + execution + derived (Lean Part 5)`

Attribute-level and query-level lint insertion passes through `LintLevelsBuilder::insert_spec` (`compiler/rustc_lint/src/levels.rs:570-668` in `14210df0e`; lines `560-658` in `main`). Tracing `insert_spec` line by line explains every non-obvious `forbid` interaction:

1. **Lookup uses the *revealed* spec (`levels.rs:575`):**
   `let old_level_spec = self.provider.get_lint_level_spec(id.lint, self.sess);`
   Inside late/early lint passes (`LateContext` / `EarlyContext`), `get_lint_level_spec` calls `reveal_actual_level_spec`, so `old_level` and `old_src` reflect CLI `warnings` expansion, `--cap-lints`, and `driver_lint_caps` *before* checking whether `old_level == Level::Forbid`. Notice the guard `self.lint_added_lints`:
   - `EarlyContext` runs with `lint_added_lints = !pre_expansion` (`compiler/rustc_lint/src/early.rs:325`).
   - `shallow_lint_levels_on` runs with `lint_added_lints = false` (`levels.rs:172`), preventing duplicate `E0453` emissions when building HIR lint maps and letting queries store raw specs without prematurely raising `E0453` during AST/HIR query setup.
   - Post-expansion `EarlyContext` and `LateContext` run with `lint_added_lints = true`.

2. **`Deny` under `Forbid` is silently ignored (`levels.rs:585-587`):**
   ```rust
   if self.lint_added_lints && level == Level::Deny && old_level == Level::Forbid {
       return;
   }
   ```
   Under `#![forbid(unsafe_code)]`, `#[deny(unsafe_code)]` neither emits `E0453` nor downgrades `old_src` (`a04`). Crucially, the unsafe block diagnostic still reports `#![forbid(unsafe_code)]` as its lint level note, and a subsequent inner `#[allow(unsafe_code)]` (`a05`) still emits `E0453` pointing back to `#![forbid(unsafe_code)]`. Same-scope reverse order (`#[allow(unsafe_code)] #[forbid(unsafe_code)]` on the same item, `a06`) is also valid (`E0453` does not trigger; `Forbid` applies).

3. **Direct vs. group `old_src` split (`levels.rs:588-645`):**
   When `self.lint_added_lints && level != Level::Forbid && old_level == Level::Forbid`:
   ```rust
   let fcw_warning = match old_src {
       LintLevelSource::Default => false,
       LintLevelSource::Node { name, .. } => self.store.is_lint_group(name),
       LintLevelSource::CommandLine(symbol, _) => self.store.is_lint_group(symbol),
   };
   ```
   - **Direct `old_src` (`fcw_warning == false`):** `emit_err(OverruledAttribute ...)` emits `error[E0453]: allow(...) incompatible with previous forbid` and **returns early at line 643**, leaving the map unchanged (`insertSpec_direct_forbid_unoverridable`, `a01`, `a02`, `a03`). This holds inductively across arbitrary inner attribute lists unless capped or overwritten by a lint-group `forbid` (`applyAttrList_direct_forbid_invariant`).
   - **Lint-group `old_src` (`fcw_warning == true`):** `emit_span_lint(FORBIDDEN_LINT_GROUPS, ...)` emits future-compatibility warning `#81670`, does **not** return early (`if !fcw_warning { return; }`), and falls through to lines `656-667`, **actually overwriting the lint's active level** to `Allow` / `Expect` / `Warn` (`insertSpec_group_forbid_emits_fcw_and_lowers`, `witness_a07_group_forbid_fcw_lowers`)! Live verification confirms `rc = 0` for `#![forbid(unused)]` + `#[allow(dead_code)]` (`a07`), `#![forbid(unused)]` + `#[allow(unused)]` (`a08`), `#![forbid(unused)]` + `#[expect(dead_code)]` (`a09`), and `-F unused` + `#[allow(dead_code)]` (`a10`). Moreover, after `#![forbid(unused)] #[allow(dead_code)]`, an inner `#[warn(dead_code)]` works normally (`a11d`), proving `dead_code` truly left `Forbid`.

4. **`#![forbid(warnings)]` default-level asymmetry:**
   `warnings` is a lint group (`is_lint_group(sym::warnings) == true`), *not* an ordinary expanded list of lints in `LintStore::find_lints`: instead, `reveal_actual_level_spec` checks `probe_for_lint_level_spec(WARNINGS)` **only if** `level_spec.level == Level::Warn` (`compiler/rustc_middle/src/lint.rs:156-182`). Two sharp consequences follow (`forbid_warnings_promotes_dead_code_but_not_unsafe_code`):
   - A `Warn`-by-default lint such as `dead_code` starts with `baseSpec.level == Warn`, pulls `old_src = Node("warnings")` (`Level::Forbid`), so `#[allow(dead_code)]` triggers `forbidden_lint_groups` FCW (`a11`, `rc = 0`); notice `FORBIDDEN_LINT_GROUPS` itself is declared with `ignore_deny_warnings` (`compiler/rustc_lint_defs/src/builtin.rs:187-199`), preventing `#![forbid(warnings)]` from escalating the FCW into an error. Similarly `#![forbid(warnings)]` + `#[allow(warnings)]` emits FCW and compiles (`a12`, `rc = 0`).
   - An `Allow`-by-default lint such as `unsafe_code` starts with `baseSpec.level == Allow != Warn`, so `#![forbid(warnings)]` + `#[allow(unsafe_code)] unsafe {}` does *not* match `WARNINGS` and compiles cleanly for `unsafe_code` (`a11b` fails only on `unused_unsafe`, which *is* `Warn`-by-default and therefore promoted to `Forbid` by `#![forbid(warnings)]`!). However, writing `#[warn(unsafe_code)] #[allow(unsafe_code)]` under `#![forbid(warnings)]` (`a11c`) first sets `unsafe_code` to `Warn`, causing the subsequent lookup before `#[allow(unsafe_code)]` to see `Level::Warn`, absorb `WARNINGS`'s `Forbid` source, and emit `forbidden_lint_groups` FCW on `allow(unsafe_code)`!

5. **Mixed-source overwrite loophole (`direct_forbid_group_forbid_allow_loophole_witness`, `a12b`):**
   Look carefully at `insert_spec` lines `656-667`:
   ```rust
   match (old_level, level) {
       (Level::ForceWarn, Level::Expect) => ...,
       (Level::ForceWarn, _) => ...,
       _ => self.provider.insert(id, LevelSpec::new(level, lint_id, src)),
   }
   ```
   Notice that when `level == Level::Forbid`, the condition `level != Level::Forbid` at line `588` is `false`. So if `dead_code` already had **direct** `#![forbid(dead_code)]`, and an inner scope adds `#[forbid(unused)]`, `insert_spec` runs line `666` and **overwrites `old_src`** from `Node("dead_code")` to `Node("unused")`! Consequently, a further inner `#[allow(dead_code)]` now observes `fcw_warning = is_lint_group("unused") == true`, emits only the `forbidden_lint_groups` FCW instead of `E0453`, and **lowers `dead_code` to `Allow`** (`a12b` compiles `fn unused() {}` with `rc = 0`!). This subtle edge case is both empirically confirmed in `probe_results.json` (`a12b`) and kernel-proven by `rfl` in `direct_forbid_group_forbid_allow_loophole_witness`.

---

### 3. `--cap-lints` Upper-Bounding, `--force-warn` Non-Capping Bypass, and the Session `can_emit_warnings` Latch

`Basis: source + execution + derived (Lean Part 4)`

`reveal_actual_level_spec` (`compiler/rustc_middle/src/lint.rs:141-195`) computes a lint's effective `LevelSpec` through four ordered transforms:

```text
raw spec (or lint default)
  └─▶ if level == Warn: consult WARNINGS (ignore Deny/Forbid if lint.ignore_deny_warnings)
  └─▶ if !matches!(src, CommandLine(_, ForceWarn)):
          level = min(level, opts.lint_cap.unwrap_or(Forbid))
  └─▶ if let Some(d_cap) = sess.driver_lint_caps.get(&lint):
          level = min(level, d_cap)
```

From this code structure, three theorems hold unconditionally (formalized in Lean Part 4 and reproduced in probes `a13`–`a34`):

1. **`--cap-lints` is an upper bound for non-`ForceWarn` sources (`reveal_le_lintCap_unless_forceWarn`):**
   Whenever neither the lint nor `warnings` holds `CommandLine(_, ForceWarn)` and `driver_lint_caps` is absent, `(reveal_actual_level_spec ...).level <= cap`. Because `insert_spec` reads `old_level_spec` *after* `reveal_actual_level_spec`:
   - `--cap-lints=warn` lowers `#![forbid(unsafe_code)]` and `#[deny(...)]` to `Warn`, removing `E0453` (`a14`, `a18`).
   - `--cap-lints=deny` keeps `Forbid` errors at `Deny` (`a16`: `unsafe {}` still errors `rc = 1`) yet lowers `old_level` to `Deny != Forbid`, **eliminating `E0453`** (`a17`: `#![forbid(unsafe_code)] #[allow(unsafe_code)] unsafe {}` emits zero `E0453` and compiles `rc = 0` with only `unused_unsafe` warning!).
   - `--cap-lints=allow` silences both `#![forbid]` and `-F` (`a15`, `a19`, `reveal_capLints_allow_silences_forbid`), dropping all diagnostics even for `Allow`- vs. `Forbid`-level violations unless `future_incompatible.report_in_deps` triggers the special future-breakage allow tracking (`emit_lint_base:418-423`).

2. **CLI `--force-warn` bypasses `--cap-lints` (`reveal_forceWarn_bypasses_capLints_allow`):**
   Line 185 guards `--cap-lints` with `if !matches!(level_spec.src, LintLevelSource::CommandLine(_, Level::ForceWarn))`. Meanwhile `insert_spec` lines 656-664 lock `(Level::ForceWarn, _) => ForceWarn`, and `add_command_line` lines 553-557 lock out later `-F`/`-D`/`-A`/`-W` CLI flags. Thus `--cap-lints=allow --force-warn dead_code` (`a28`), `--force-warn dead_code` over `#![allow(dead_code)]` (`a27`), and `--force-warn dead_code` over `#[forbid(dead_code)]` (`a29`) all force `ForceWarn` emissions (`rc = 0` with warning). Note the final step at line 190: `driver_lint_caps` applies **unconditionally** after line 185, without exempting `ForceWarn` (`reveal_driverCap_always_bounds`).

3. **`-A warnings` permanently latches `can_emit_warnings = false` in `DiagCtxt` (`compiler/rustc_session/src/session.rs:1020-1032`):**
   During `build_session`:
   ```rust
   let warnings_allow = sopts
       .lint_opts
       .iter()
       .rfind(|&(key, _)| *key == "warnings")
       .is_some_and(|&(_, level)| level == lint::Allow);
   let cap_lints_allow = sopts.lint_cap.is_some_and(|cap| cap == lint::Allow);
   let can_emit_warnings = !(warnings_allow || cap_lints_allow);
   ```
   Look at `rfind`: if `-W warnings` appears after `-A warnings` on the CLI (`a34`), `rfind` finds `Warn != Allow`, so `can_emit_warnings == true` and warnings appear (`rc = 0`, warning emitted). Conversely, if CLI passes only `-A warnings`, `can_emit_warnings` is locked to `false` inside `DiagCtxt`:
   - Crate-level `#![warn(warnings)]` cannot re-enable plain `Warning` emissions (`a33`: `rc = 0`, 0 warnings), because `emit_lint_base:486` (`let skip = err_level == Warning && !sess.dcx().can_emit_warnings();`) and `DiagCtxtInner::emit_diagnostic:1256` discard `Warning`s silently (`cli_allow_warnings_suppresses_crate_warn_but_not_deny_or_expect`).
   - Crucially, **`-A warnings` does NOT disable `Deny` / `Forbid` errors** (`a33b`: `#[deny(dead_code)]` under `-A warnings` still fails compilation with `rc = 1`), **nor does it disable `ForceWarning`** (which is not `Level::Warning`), **nor does it suppress `#[expect]` fulfillment** (because `Expect` maps to `rustc_errors::Level::Expect`, not `Warning`, though it *does* silence `unfulfilled_lint_expectations` itself when that lint remains at `Warn` — see `a39`!).

---

### 4. RFC 2383 `#[expect]` Fulfillment Conservation and Cross-Mechanism Interactions

`Basis: normative + source + execution + derived (Lean Part 6)`

RFC 2383 expectations operate across three distinct compilation phases:

1. **Expectation collection (`LintLevelsBuilder` in `levels.rs` + `lint_expectations` query in `expect.rs:15-26`):**
   - Each `#[expect(L)]` generates a unique `(attr_id, lint_index)` / `StableLintExpectationId` (carrying `hir_id`, `lint_index`, and in `1.98.0-nightly` `attr_index`), records a `LintExpectation` in `ShallowLintLevelMap::expectations`, and calls `insert_spec` with `LevelSpec::new(Level::Expect, Some(lint_id), src)`.
   - **Self-expectation exception (`levels.rs:650-654`):** If `level == Level::Expect && id == LintId::of(UNFULFILLED_LINT_EXPECTATIONS)`, `insert_spec` returns early without setting the level, while the expectation list entry is still pushed with `is_unfulfilled_lint_expectations = true` (`levels.rs:767-779` in `main`). Therefore, `#[expect(unfulfilled_lint_expectations)]` can never fulfill itself (`expect_self_unfulfilled_ignored`, `a46`) and always warns with an extra note: ``note: the `unfulfilled_lint_expectations` lint can't be expected and will always produce this message``.
   - **Under CLI `-A L` (`a37`, `a38`) vs. under `--force-warn L` (`a42`, `a44`, `a45`):**
     - `#[expect(dead_code)]` overrides crate/CLI `-A dead_code` (`a37` fulfilled silent; `a38` unfulfilled warns!), because `Allow` is not sticky.
     - Under `--force-warn L`, `insert_spec` hits `(Level::ForceWarn, Level::Expect)` (`levels.rs:658-660`), storing `LevelSpec::new(ForceWarn, lint_id, old_src)`. When `L` fires (`a42`), `emit_lint_base` maps `ForceWarn` to `rustc_errors::Level::ForceWarning` with `lint_id` attached; `emit_diagnostic` does **not** take the `ForceWarning if diagnostic.lint_id.is_none()` branch (`rustc_errors/src/lib.rs:1254`) and instead enters `Expect | ForceWarning => { self.fulfilled_expectations.insert(diagnostic.lint_id.unwrap()); ... }` (`lib.rs:1276-1278`). Thus **`a42` both emits the `--force-warn` warning AND fulfills `#[expect]`** (`expect_under_forceWarn_fulfills_and_warns`).
     - If an inner attribute writes `#[allow(L)]` *below* `#[expect(L)]` under `--force-warn L` (`a45`), `insert_spec` hits `(Level::ForceWarn, _) => LevelSpec::new(Level::ForceWarn, None, old_src)` (`levels.rs:662-664`), stripping `lint_id`! Therefore `L` still emits its forced warning (with `lint_id = None`), nothing enters `fulfilled_expectations`, and `check_expectations` *also* emits `unfulfilled_lint_expectations` (`expect_inner_allow_drops_id_under_forceWarn`, `a45`: 2 warnings!).

2. **Lint pass firing (`emit_lint_base` -> `DiagCtxtInner::emit_diagnostic`):**
   - `emit_lint_base` (`compiler/rustc_middle/src/lint.rs:417-509`) sets `err_level = Expect` for `Level::Expect`.
   - **External-macro filter precedes fulfillment (`emit_lint_base:440-475`):** If any primary span originates in an external macro (`s.in_external_macro(sess.source_map())`) and neither `future_incompatible` (non-edition) nor `lint.report_in_external_macro` nor internal `find_attr` override holds, `emit_lint_base` returns early at line `473` **before** calling `decorate` or `dcx.emit_diagnostic`. Hence suppressed external-macro violations never fulfill an enclosing `#[expect(...)]` (`external_macro_never_fulfills_expect`; note that `UNEXPECTED_CFGS` specifically sets `report_in_external_macro` in `builtin.rs:2993`).
   - Otherwise, `Expect` does **not** return early in `emit_lint_base`, creates the diagnostic (even though `err_level == Expect` suppresses printing at `lib.rs:1278-1283`), and inserts `diagnostic.lint_id` into `self.fulfilled_expectations` (`expect_fulfillment_exact_conservation`).
   - **Scope precedence ordering (`a47`, `a48`, `a49`):** On the same item, later attributes overwrite earlier attributes (`#[warn(L)] #[allow(L)]` allows `a47`; `#[allow(L)] #[warn(L)]` warns `a48`), and nested item attributes override outer/crate `#![deny(L)]` (`a49`).

3. **Post-lint expectation check (`check_expectations` in `compiler/rustc_lint/src/expect.rs:28-64`, invoked at `passes.rs:1251`):**
   - Runs **once per compilation** after `rustc_lint::check_crate(tcx)` completes, via `tcx.ensure_ok().check_expectations(None)`.
   - Steals `dcx().steal_fulfilled_expectation_ids()`, canonicalizes `Unstable(attr_id, lint_index)` and `Stable(hir_id, attr_index, lint_index)` (in `main`, via `find_attr!(tcx, id.hir_id, LintCheck(...))`) into `(attr_id, lint_index)` pairs, and emits `UNFULFILLED_LINT_EXPECTATIONS` on the expectation's `hir_id` for every collected expectation absent from the fulfilled set.
   - **Silencing by `-A warnings` and `--cap-lints=allow`:**
     - Under `-A warnings`, `UNFULFILLED_LINT_EXPECTATIONS` is emitted at `Warning`, which `can_emit_warnings == false` drops (`a39`: `rc = 0`, 0 warnings), whereas `-A dead_code` leaves `unfulfilled_lint_expectations` active (`a38`).
     - Under `--cap-lints=allow`, *both* the expected lint (`a40`) and `unfulfilled_lint_expectations` (`a41`) reveal as `Allow`, silencing everything (`capLints_allow_silences_expect_and_unfulfilled`).

---

### 5. `--check-cfg` Validation, `#[cfg_attr(false, ...)]` Pre-Validation Erasure, and Macro `lint_node_id` Routing

`Basis: source + execution + derived (Lean Part 7)`

Conditional configuration checks (`UNEXPECTED_CFGS`) and `cfg`/`cfg_attr` expansion obey an exact multi-stage pipeline in `rustc_expand` and `rustc_attr_parsing`:

1. **`parse_name_value` checks `sess.check_config` eagerly during `cfg` predicate parsing (`compiler/rustc_attr_parsing/src/attributes/cfg.rs:194-236`):**
   - For every `(name, Option<value>)` atom inside `cfg(...)` or `cfg_attr(pred, ...)`, `parse_name_value` inspects `cx.sess.check_config.expecteds.get(&name)` immediately upon parsing `pred`, *before* evaluating whether `pred` is true or false (`validateCfgPred`, `checkCfg_soundness`):
     - If `expecteds.get(&name)` is `Some(ExpectedValues::Some(vals))` and `value` is not in `vals`, it emits `UNEXPECTED_CFGS` (`unexpected_cfg_value`, `b02`).
     - If `expecteds.get(&name)` is `None` and `check_config.exhaustive_names == true`, it emits `UNEXPECTED_CFGS` (`unexpected_cfg_name`, `b02`).
     - If `--check-cfg` was never passed, `CheckCfg::default()` has `exhaustive_names = false` and empty `expecteds` (`no_check_cfg_never_emits`). Note also `UNEXPECTED_CFGS` only checks predicates when any `--check-cfg` flag is passed (`b01`–`b03`).

2. **`#[cfg_attr(false, ...)]` syntactic gate vs. `CfgAttrTrace` erasure (`compiler/rustc_expand/src/config.rs:248-306`):**
   Inside `StripUnconfigured::expand_cfg_attr`:
   - **Step A (`parse_cfg_attr` at lines `270-277`):** Parses `pred` via `parse_cfg_entry` — **validating `pred` against `--check-cfg`** even when `pred` evaluates to `false` (`b03`: `#[cfg_attr(unknown_pred, ...)]` warns on `unknown_pred`) — and parses the comma-separated inner elements as raw **`ast::AttrItem` token forms** via `parser.parse_attr_item(ForceCollect::Yes)` (`cfg.rs:437`). Syntactically invalid non-`AttrItem` tokens inside `cfg_attr(false, 123_not_an_attr)` therefore still fail parsing (`b07`, `rc = 1`).
   - **Step B (`!eval_config_entry.as_bool()` at lines `289-291`):** Immediately returns `vec![trace_attr]`, leaving only `cfg_attr_trace` (`SyntheticAttr::CfgAttrTrace` in `main`) on the AST node and **erasing all inner attributes before**:
     - `AttributeParser` / built-in attribute validation runs (`b04`: `#[cfg_attr(false, inline(bogus_never_valid))]` compiles with `rc = 0`, whereas `b05`: `#[cfg_attr(true, ...)]` fails `E0539`);
     - recursive `expand_cfg_attr` or `in_cfg` inspects inner `cfg(...)` predicates (`b04`: `#[cfg_attr(false, cfg(unknown_nested_cfg))]` emits zero `unexpected_cfgs` warnings);
     - `LintLevelsBuilder::insert_spec` processes inner `#[allow(unsafe_code)]` (`b04` under `#![forbid(unsafe_code)]` emits zero `E0453`, `cfgAttr_false_erases_inner_attrs_before_validation`, `cfgAttr_false_zero_errors_when_pred_valid`).
   - **Same-item `cfg_attr` + `cfg` ordering (`config.rs:170-176`, `expand.rs:2347-2376`, `b06a` vs. `b06b`, `b09` vs. `b10`):**
     `StripUnconfigured::configure` calls `process_cfg_attrs` **before** `in_cfg`, and `in_cfg` short-circuits (`attrs.iter().all(...)`) on the first `false` `#[cfg(...)]`:
     - On `#[cfg_attr(true, allow(unsafe_code))] #[cfg_attr(true, cfg(unknown_nested_cfg))]` under `#![forbid(unsafe_code)]` (`b06b`), both `cfg_attr`s expand, `in_cfg` drops the item while evaluating `cfg(unknown_nested_cfg)` (still warning on `unknown_nested_cfg`), and **`E0453` never fires** (`rc = 0`, `cfgAttr_true_allow_plus_false_cfg_strips_before_e0453`). Compare `b06a` where the second `#[cfg_attr]` is absent (`rc = 1`, `E0453` fires).
     - On `#[cfg(false)] #[cfg_attr(unknown_after_false, allow(dead_code))]` (`b09`), `InvocationCollector::take_first_attr` walks attributes left-to-right and removes `#[cfg(false)]` first (`expand.rs:2205-2218`); since `eval_config_entry` returns `False`, `flat_map_node` returns `Default::default()` immediately without ever expanding `#[cfg_attr(unknown_after_false, ...)]` (`b09` emits zero warnings!). Swapping them (`b10`: `#[cfg(unknown_first_cfg)] #[cfg(false)]`) checks `unknown_first_cfg` first and emits `unexpected_cfgs`.

3. **Why `#[expect(unexpected_cfgs)]` on an item misses its own `#[cfg(...)]` (`expand.rs:1231-1244, 2134-2376`):**
   Macro expansion assigns `NodeId`s via `assign_id!`:
   ```rust
   let old_id = $self.cx.current_expansion.lint_node_id;
   ...
   $self.cx.current_expansion.lint_node_id = new_id;
   let ret = ($closure)();
   $self.cx.current_expansion.lint_node_id = old_id;
   ```
   When `InvocationCollector` visits an item `fn f()`, it expands the item's `#[cfg(...)]` and `#[cfg_attr(...)]` attributes via `self.cfg()` (which captures `self.cx.current_expansion.lint_node_id`, i.e., **the parent scope's `NodeId`** — crate root or enclosing `mod`!) **before** `assign_id!` creates and activates `f`'s own `new_id` for walking `f`'s body:
   - `#[expect(unexpected_cfgs)] #[cfg(unknown_flag)] fn f() {}` with `--cfg=unknown_flag` (`b12b`, `item_expect_misses_own_cfg_while_parent_expect_catches`): `unknown_flag`'s `unexpected_cfgs` diagnostic is buffered under `parent`'s `lint_node_id`, so `f`'s `#[expect(unexpected_cfgs)]` **does not see it** — **both** `unexpected_cfgs` and `unfulfilled_lint_expectations` emit!
   - By contrast, crate-level `#![expect(unexpected_cfgs)]` (`b12a`), enclosing `mod`'s `#[expect(unexpected_cfgs)]` (`b12d`), and `#[expect(unexpected_cfgs)] fn f() { let _ = cfg!(unknown_flag); }` (`b12c`, expanded inside `f`'s body *after* `assign_id!`) all buffer at a `lint_node_id` covered by the `#[expect]`, fulfilling it cleanly with zero warnings!

---

### 6. Anneal Trusted Compiler Capture Boundaries

`Basis: source + derived`

Inspecting `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/rustc-capture/src/driver.rs:75-145` and `tests/compiler_session.rs:139-192`) establishes how these lint rules govern Anneal's TCB gate:

1. **`after_analysis` runs *after* `check_expectations` and gates strictly on `tcx.dcx().has_errors()`:**
   `compiler/rustc_interface/src/passes.rs:1232-1251` runs both `rustc_lint::check_crate(tcx)` and `tcx.ensure_ok().check_expectations(None)` inside `tcx.analysis(())` *before* invoking `Callbacks::after_analysis`, where Anneal checks `self.analysis_reached = tcx.dcx().has_errors().is_none()` (`driver.rs:82`).
2. **Warnings vs. errors in Anneal capture (`compiler_session.rs:140-192`):**
   - Plain warnings (including `unfulfilled_lint_expectations`, `forbidden_lint_groups`, and `unexpected_cfgs` at default `Warn`, or CLI `--force-warn L` — even under `#[deny(warnings)]` for `ignore_deny_warnings` lints like `forbidden_lint_groups`) do **not** increment `dcx.has_errors()`, so `after_analysis` sets `analysis_reached = true`.
   - Passing `-Dwarnings` (or `#![deny(dead_code)]`, `#![forbid(...)]`, `E0453`, or `#[forbid(unexpected_cfgs)]`) promotes non-exempt warnings to `Level::Error`, causing `tcx.dcx().has_errors().is_some()` and aborting `rustc-capture` with exit code `1` and zero callback evidence (`warnings_allow_callback_evidence_until_promoted_to_errors`).
   - **Cargo `--cap-lints=allow` on third-party crates:** Because `--cap-lints=allow` silences even `#![forbid(unsafe_code)]`, `E0453`, and `unfulfilled_lint_expectations` (`a15`, `a19`, `a40`, `a41`), lint attributes alone in Cargo dependency builds provide no compiler-enforced error guarantee unless compiled without `--cap-lints=allow` or checked with `after_analysis` AST/HIR/MIR semantic extraction directly (as Anneal does) or overridden via `--force-warn` (which still only emits `ForceWarning`, not an error).

---

### 7. Kernel-Checked Lean 4 Formalization Architecture

`Basis: derived (support/LintLevelLatticeCapLintsAndCheckCfgSoundness.lean)`

`support/LintLevelLatticeCapLintsAndCheckCfgSoundness.lean` (2,514 lines, namespace `RustcLintAndCfgModel`) provides a self-contained Lean `v4.34.1` model built strictly on core `Init` with `-DwarningAsError=true -DElab.async=false -Ddebug.skipKernelTC=false`:

- **Purity guarantees:** Every executable/relational definition uses `noncomputable def` (564 definitions total), with zero `partial def`, zero `deriving` clauses on inductive/structure types, zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`, and **`0` `._unsafe_rec` constants** verified across all constants in `RustcLintAndCfgModel` via MetaM inspection (`support/lean_axiom_audit_output.txt`). Only `propext` (or zero axioms) appears across all 261 theorems.
- **Core components and proved invariants:**
  1. **Six-Level Lattice & CLI Flags (Parts 2–4):** `LintLevel` (`rank`, `le`, `min`, `fromCapStr?`), `LintName`, `LintMeta`, `LevelSpec.WF`, `parseCapLints`, `addCommandLine`, `revealActualLevelSpec`, proving total lattice laws (`le_antisymm`, `min_assoc`), `cap_flag_first_wins`, `cli_forceWarn_sticky_against_forbid` / `cli_forbid_sticky_against_forceWarn`, `reveal_le_lintCap_unless_forceWarn`, `reveal_forceWarn_bypasses_capLints_allow`, `reveal_capLints_allow_silences_forbid`, `reveal_driverCap_always_bounds`, and `forbid_warnings_promotes_dead_code_but_not_unsafe_code`.
  2. **`insert_spec` Monotonicity & Overwrite Quirks (Part 5):** `insertSpec` proving `insertSpec_preserves_WF`, `insertSpec_direct_forbid_unoverridable`, `insertSpec_group_forbid_emits_fcw_and_lowers`, `insertSpec_cap_below_forbid_no_e0453`, `insertSpec_under_forceWarn`, `applyAttrList_direct_forbid_invariant`, and the kernel-computed quirk theorem `direct_forbid_group_forbid_allow_loophole_witness`.
  3. **`emit_lint_base` & `#[expect]` Conservation (Part 6):** `emitLintBase` + `checkExpectations`, proving `emitLintBase_preserves_fulfilled_mem`, `emitLintBase_only_adds_spec_lintId`, `expect_fulfillment_exact_conservation`, `expect_under_forceWarn_fulfills_and_warns`, `expect_inner_allow_drops_id_under_forceWarn`, `expect_self_unfulfilled_ignored`, `capLints_allow_silences_expect_and_unfulfilled`, `external_macro_never_fulfills_expect`, and `cli_allow_warnings_suppresses_crate_warn_but_not_deny_or_expect`.
  4. **`--check-cfg`, `cfg_attr(false, ...)`, and Macro Routing (Part 7):** Mutual structural models of `CfgPred.eval`, `validateCfgPred`, `predAtomWellTyped`, `expandAttrList`, `evalInCfg`, `compileItemAttrs`, and `emitBufferedUnexpectedCfg`, proving `ExpectedValues.join_assoc`, `ExpectedValues.join_comm_obs`, `applyCheckCfgSpec_comm_obs`, `checkCfg_soundness`, `no_check_cfg_never_emits`, `cfgAttr_false_erases_inner_attrs_before_validation`, `cfgAttr_false_zero_errors_when_pred_valid`, `cfgAttr_true_exposes_malformed_and_e0453`, `cfgAttr_true_allow_plus_false_cfg_strips_before_e0453`, and `item_expect_misses_own_cfg_while_parent_expect_catches`.
  5. **Kernel Matrix Witnesses (Part 8):** Concrete `rfl` witnesses `witness_a01_forbid_allow_e0453` through `witness_b04_b05_cfg_attr_matrix` tying concrete probe outcomes directly to the mechanized semantics.

---

## Boundaries

- **Known not to apply:**
  - *Cross-crate / workspace-wide immutability of `#![forbid(...)]` under Cargo:* Passing `--cap-lints=allow` completely caps `forbid` and suppresses `E0453` (`a15`, `a19`), `--force-warn` overrides `#[allow(...)]` and `#[forbid(...)]` (`a27`, `a29`), and `driver_lint_caps` overrides `--force-warn` (`reveal_driverCap_always_bounds`).
  - *`#[forbid(warnings)]` on `Allow`-by-default lints such as `unsafe_code`:* Because `reveal_actual_level_spec` inspects `WARNINGS` only when `baseSpec.level == Warn` (`rustc_middle/src/lint.rs:156`), `#![forbid(warnings)]` alone neither forbids `unsafe {}` nor triggers `forbidden_lint_groups` on `#[allow(unsafe_code)]` (`a11b`) unless a `#[warn(unsafe_code)]` scope intervenes (`a11c`).
  - *Item-level `#[expect(unexpected_cfgs)]` covering the item's own `#[cfg(...)]`:* Because `InvocationCollector` checks an item's `#[cfg]` before `assign_id!` updates `lint_node_id`, an item `#[expect(unexpected_cfgs)]` misses its own `#[cfg(...)]` (`b12b`).
  - *Assuming `#[cfg_attr(false, ...)]` validates zero tokens:* Inner arguments inside `#[cfg_attr(false, ...)]` still undergo lexer tokenization and `Parser::parse_attr_item` syntax parsing (`b07`); only semantic attribute parsing and expansion are erased.
- **Unsupported:**
  - *`--force-warn warnings`:* Explicitly rejected with `E0602` in `add_command_line` (`levels.rs:501-505`, `a32`), with a `span_delayed_bug` / `delayed_bug` defense in `reveal_actual_level_spec` (`lint.rs:170-175`).
  - *`--cap-lints=expect` or `--cap-lints=force-warn`:* Rejected by `Level::from_str` (`"expect" | _ => None`) because neither level is a valid `--cap-lints` argument.
  - *Self-expecting `#[expect(unfulfilled_lint_expectations)]`:* Explicitly ignored for expectation fulfillment (`levels.rs:650-654`, `a46`).
- **Not examined:**
  - *Live binary execution on `1.102.0-nightly` (`3ef0c22cd`) or `main` (`277240238`):* Those revisions were audited via upstream source inspection and diffing against `14210df0e`; live `rustc` subprocess runs in `support/probe_results.json` were executed on `1.98.0-nightly (14210df0e 2026-05-31)` only.
  - *Cargo's own `Cargo.toml` `[lints]` translation layer (`lints.rust` emission of `--cap-lints`, `-F`, `--force-warn` flags):* Out of scope beyond how `rustc` parses the resulting CLI flags.
  - *Tool lint namespaces (`#[allow(clippy::...)]` / `#[allow(rustdoc::...)]`) and custom driver-registered passes beyond `driver_lint_caps` / `tool_filter`:* `registered_tools` / `registered_lint_tools` lookup mechanics in `check_lint_name` were not empirically probed.
  - *Proc-macro `LazyAttrTokenStream` token configuration (`StripUnconfigured::configure_tokens`, `config.rs:191-234`):* Documented by source inspection; no custom proc-macro crate probe was executed in the standalone `rustc` matrix.
- **Unknown:**
  - *Timeline for promoting `forbidden_lint_groups` (`#81670`) from FCW to a hard error:* The lint carries `FutureReleaseError #81670` and `report_in_deps: true` across `1.98.0-nightly`, `1.102.0-nightly`, and `main` (2026-11-23), with no committed removal milestone present in the audited files.

---

## Evidence

### Preserved Package Artifacts

| Artifact | Purpose & Scope | Verification Status |
| :--- | :--- | :--- |
| [`support/probe_lint_lattice_and_check_cfg.py`](support/probe_lint_lattice_and_check_cfg.py) | Standalone Python probe harness compiling 70 test crates in isolated temporary directories | Executed cleanly (`exit 0`) against `rustc 1.98.0-nightly (14210df0e 2026-05-31)` |
| [`support/probe_results.json`](support/probe_results.json) | Complete schema `"rustc-lint-lattice-check-cfg-probe/1"` capturing all 70 source snippets, SHA-256 digests, CLI flags, exit codes, and verbatim `rustc` stderr/stdout | Generated directly by the probe run (`70` cases: `a01`–`a49`, `b01`–`b12d`) |
| [`support/LintLevelLatticeCapLintsAndCheckCfgSoundness.lean`](support/LintLevelLatticeCapLintsAndCheckCfgSoundness.lean) | 2,514-line self-contained Lean `v4.34.1` formalization (namespace `RustcLintAndCfgModel`, core `Init` only, 261 theorems, 564 `noncomputable def`s) | Kernel-checked cleanly (`exit 0`) with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` |
| [`support/lean_axiom_audit_output.txt`](support/lean_axiom_audit_output.txt) | Per-theorem `collectAxioms` listing plus exhaustive environment scan across all `RustcLintAndCfgModel.*` constants | `THEOREMS_AUDITED=261`, `DEFS_AUDITED=564`, `UNSAFE_REC_COUNT=0`, `FORBIDDEN_AXIOM_HITS=0` |
| [`support/resolved_revisions.json`](support/resolved_revisions.json) | Live-resolved 40-hex commit hashes, commit dates, and branch/tag metadata for all audited upstream repositories | Resolved via GitHub REST API on 2026-11-23 |

### Primary-Source Line Index (`rust-lang/rust` and `joshlf/anneal`)

| Symbol / Construct | `1.98.0-nightly` (`14210df0e`) & Anneal-Pinned (`f8a08b688`) | `1.102.0-nightly` (`3ef0c22cd`) | `main` (`277240238`) |
| :--- | :--- | :--- | :--- |
| `LintExpectationId`, `StableLintExpectationId` | `compiler/rustc_lint_defs/src/lib.rs:102-146` (`attr_index: u16`) | `rustc_lint_defs/src/lib.rs:109-151` | `rustc_lint_defs/src/lib.rs:112-154` (`attr_index` removed) |
| `Level` enum (`Allow..Forbid`), `from_str` | `compiler/rustc_lint_defs/src/lib.rs:154-210` | `rustc_lint_defs/src/lib.rs:158-213` | `rustc_lint_defs/src/lib.rs:161-216` |
| `FORBIDDEN_LINT_GROUPS`, `UNFULFILLED_LINT_EXPECTATIONS`, `UNEXPECTED_CFGS` | `compiler/rustc_lint_defs/src/builtin.rs:187-199, 678-681, 2990-2994` | `rustc_lint_defs/src/builtin.rs` (`ignore_deny_warnings`, `report_in_external_macro` preserved) | `rustc_lint_defs/src/builtin.rs` (`ignore_deny_warnings`, `report_in_external_macro` preserved) |
| `LintLevelSource`, `LevelSpec::new`, `reveal_actual_level_spec` | `compiler/rustc_middle/src/lint.rs:21-90, 141-195` | `rustc_middle/src/lint.rs:21-90, 141-195` | `rustc_middle/src/lint.rs:20-90, 140-191` (`delayed_bug`) |
| `emit_lint_base` (external-macro filter, `skip`) | `compiler/rustc_middle/src/lint.rs:386-509` | `rustc_middle/src/lint.rs:383-506` | `rustc_middle/src/lint.rs:382-505` |
| `shallow_lint_levels_on`, `add_command_line`, `insert_spec`, `add` | `compiler/rustc_lint/src/levels.rs:158-200, 497-565, 570-668, 670+` | `rustc_lint/src/levels.rs:160-202, 483-552, 560-658` | `rustc_lint/src/levels.rs:160-202, 483-552, 560-658, 660-780` (`add_ast`/`add_hir`) |
| `lint_expectations`, `check_expectations` | `compiler/rustc_lint/src/expect.rs:15-64` | `rustc_lint/src/expect.rs:16-69` | `rustc_lint/src/expect.rs:16-69` (`find_attr!`) |
| `EarlyContext::new` (`!pre_expansion`) | `compiler/rustc_lint/src/early.rs:322-335` | `rustc_lint/src/early.rs` | `rustc_lint/src/early.rs` |
| `passes::analysis` (`check_crate` before `check_expectations`) | `compiler/rustc_interface/src/passes.rs:1231-1256` | `rustc_interface/src/passes.rs` | `rustc_interface/src/passes.rs` |
| `get_cmd_lint_options` (`opt_str("cap-lints")`) | `compiler/rustc_session/src/config.rs:1892-1922` | `rustc_session/src/config.rs:2248-2278` | `rustc_session/src/config.rs:1980-2010` |
| `build_session` (`can_emit_warnings` latch) | `compiler/rustc_session/src/session.rs:1020-1032` | `rustc_session/src/session.rs:1364-1375` | `rustc_session/src/session.rs:1374-1385` |
| `DiagCtxtInner::emit_diagnostic` (`ForceWarning` / `Expect` / `Warning`) | `compiler/rustc_errors/src/lib.rs:1197-1300` | `rustc_errors/src/lib.rs:1145-1248` | `rustc_errors/src/lib.rs:1146-1249` |
| `parse_name_value`, `parse_cfg_attr`, `parse_cfg_attr_internal` | `compiler/rustc_attr_parsing/src/attributes/cfg.rs:194-236, 315-445` | `rustc_attr_parsing/src/attributes/cfg.rs:185-227, 303-433` | `rustc_attr_parsing/src/attributes/cfg.rs:185-227, 303-433` |
| `StripUnconfigured::configure`, `expand_cfg_attr`, `in_cfg` | `compiler/rustc_expand/src/config.rs:170-379` | `rustc_expand/src/config.rs:152-328` | `rustc_expand/src/config.rs:152-328` (`SyntheticAttr::CfgAttrTrace`) |
| `assign_id!`, `InvocationCollector::cfg`, `expand_cfg_true`, `flat_map_node` | `compiler/rustc_expand/src/expand.rs:1231-1244, 2134-2376` | `rustc_expand/src/expand.rs` | `rustc_expand/src/expand.rs` |
| Anneal `AnalysisCallbacks::after_analysis` & `-Dwarnings` test | `joshlf/anneal` (`c131b320e`): `trusted/rustc-capture/src/driver.rs:75-145`, `tests/compiler_session.rs:140-192` | — | — |

### Live Empirical Matrix (`rustc 1.98.0-nightly 14210df0e`, All 70 Cases)

| ID | Case Key | Key CLI Args | `rc` (Run) | Observed Compiler Behavior |
| :--- | :--- | :--- | :--- | :--- |
| `a01` | `a01_forbid_overruled_by_allow_e0453` | `[]` | `1` (`-`) | `error[E0453]: allow(unsafe_code) incompatible with previous forbid` + unsafe error |
| `a02` | `a02_forbid_overruled_by_expect_e0453` | `[]` | `1` (`-`) | `error[E0453]: expect(unsafe_code) incompatible with previous forbid` |
| `a03` | `a03_forbid_overruled_by_warn_e0453` | `[]` | `1` (`-`) | `error[E0453]: warn(unsafe_code) incompatible with previous forbid` |
| `a04` | `a04_forbid_with_inner_deny_ignored` | `[]` | `1` (`-`) | `#[deny]` under `#![forbid]` emits no `E0453`; `#[forbid]` stays active in error note |
| `a05` | `a05_forbid_deny_then_allow_still_e0453` | `[]` | `1` (`-`) | `#[deny]` ignored, subsequent `#[allow]` still triggers `E0453` |
| `a06` | `a06_allow_then_forbid_same_item_valid` | `[]` | `1` (`-`) | `#[allow]` before `#[forbid]` raises cleanly without `E0453`; `unsafe` errors |
| `a07` | `a07_forbid_group_vs_member_allow_fcw` | `[]` | `0` (`-`) | `#![forbid(unused)]` + `#[allow(dead_code)]` -> `forbidden_lint_groups` FCW; lowers to `Allow` |
| `a08` | `a08_forbid_group_vs_same_group_allow_fcw` | `[]` | `0` (`-`) | `#![forbid(unused)]` + `#[allow(unused)]` -> `forbidden_lint_groups` FCW; lowers |
| `a09` | `a09_forbid_group_vs_member_expect_fcw` | `[]` | `0` (`-`) | `#![forbid(unused)]` + `#[expect(dead_code)]` -> FCW; expects & suppresses `dead_code` |
| `a10` | `a10_cli_forbid_group_vs_member_allow_fcw` | `["-F", "unused"]` | `0` (`-`) | CLI `-F unused` + `#[allow(dead_code)]` -> FCW; lowers |
| `a11` | `a11_forbid_warnings_vs_member_allow_dead_code` | `[]` | `0` (`-`) | `#![forbid(warnings)]` + `#[allow(dead_code)]` -> `forbidden_lint_groups` FCW (`ignore_deny_warnings`); lowers |
| `a11b` | `a11b_forbid_warnings_vs_allow_default_lint_unsafe` | `[]` | `1` (`-`) | `#![forbid(warnings)]` + `#[allow(unsafe_code)]` emits **no** FCW (`Allow`-default); fails only on `unused_unsafe` |
| `a11c` | `a11c_forbid_warnings_vs_warn_then_allow_unsafe` | `[]` | `1` (`-`) | `#[warn(unsafe_code)]` exposes `WARNINGS` `Forbid`, so `#[allow(unsafe_code)]` triggers FCW |
| `a11d` | `a11d_forbid_unused_allow_then_warn_dead_code` | `[]` | `0` (`-`) | After `#![forbid(unused)] #[allow(dead_code)]` FCW, inner `#[warn(dead_code)]` warns normally |
| `a12` | `a12_forbid_warnings_vs_allow_warnings_fcw` | `[]` | `0` (`-`) | `#![forbid(warnings)]` + `#[allow(warnings)]` -> FCW (`#81670`); compiles |
| `a12b` | `a12b_direct_forbid_then_group_forbid_then_allow_downgrades` | `[]` | `0` (`-`) | `#![forbid(dead_code)]` + `#[forbid(unused)]` overwrites `old_src`; `#[allow(dead_code)]` triggers FCW and compiles! |
| `a13` | `a13_cap_lints_uncapped_default_rejected` | `[]` | `1` (`-`) | Uncapped `#[forbid(unsafe_code)]` rejects `unsafe {}` |
| `a14` | `a14_cap_lints_warn_downgrades_forbid_and_deny` | `["--cap-lints=warn"]` | `0` (`0`) | Downgrades `forbid`/`deny` `unsafe_code` to warning; binary exits `0` |
| `a15` | `a15_cap_lints_allow_silences_forbid_and_deny` | `["--cap-lints=allow"]` | `0` (`0`) | Silences `forbid`/`deny` completely (0 warnings); binary exits `0` |
| `a16` | `a16_cap_lints_deny_caps_forbid_to_deny` | `["--cap-lints=deny"]` | `1` (`-`) | `Forbid` capped to `Deny` still rejects `unsafe {}` |
| `a17` | `a17_cap_lints_deny_removes_e0453` | `["--cap-lints=deny"]` | `0` (`0`) | `#![forbid(unsafe_code)] #[allow(unsafe_code)]` succeeds because revealed `old_level == Deny != Forbid` |
| `a18` | `a18_cap_lints_warn_removes_e0453` | `["--cap-lints=warn"]` | `0` (`0`) | Same under `--cap-lints=warn`: `E0453` eliminated |
| `a19` | `a19_cap_lints_allow_removes_e0453` | `["--cap-lints=allow"]` | `0` (`0`) | Same under `--cap-lints=allow`: zero errors, zero warnings |
| `a20` | `a20_cap_lints_repeated_allow_then_forbid` | `["--cap-lints=allow", "--cap-lints=forbid"]` | `0` (`-`) | First `--cap-lints` (`allow`) wins (`opt_str`) |
| `a21` | `a21_cap_lints_repeated_forbid_then_allow` | `["--cap-lints=forbid", "--cap-lints=allow"]` | `1` (`-`) | First `--cap-lints` (`forbid`) wins (`opt_str`) |
| `a22` | `a22_cli_forbid_dead_code` | `["-F", "dead_code"]` | `1` (`-`) | CLI `-F dead_code` promotes `dead_code` to error |
| `a23` | `a23_cli_forbid_then_allow_sticky` | `["-F", "dead_code", "-A", "dead_code"]` | `1` (`-`) | CLI `-F` sticky over later CLI `-A` |
| `a24` | `a24_cli_allow_then_forbid_raises` | `["-A", "dead_code", "-F", "dead_code"]` | `1` (`-`) | CLI `-A` before `-F` allows `-F` to overwrite |
| `a25` | `a25_cli_deny_then_allow_overrides` | `["-D", "dead_code", "-A", "dead_code"]` | `0` (`-`) | CLI `-D` not sticky: later `-A` overrides |
| `a26` | `a26_cli_allow_then_deny_overrides` | `["-A", "dead_code", "-D", "dead_code"]` | `1` (`-`) | CLI `-A` before `-D` allows `-D` to overwrite |
| `a27` | `a27_force_warn_overrides_allow` | `["--force-warn", "dead_code"]` | `0` (`-`) | `--force-warn` overrides `#![allow(dead_code)]` |
| `a28` | `a28_force_warn_bypasses_cap_lints_allow` | `["--cap-lints=allow", "--force-warn", "dead_code"]` | `0` (`-`) | `--force-warn` bypasses `--cap-lints=allow` |
| `a29` | `a29_force_warn_beats_forbid_attr` | `["--force-warn", "dead_code"]` | `0` (`-`) | `--force-warn` over `#![forbid(dead_code)]` keeps `ForceWarn` (`rc = 0`!) |
| `a30` | `a30_cli_force_warn_then_forbid_keeps_force_warn` | `["--force-warn", "dead_code", "-F", "dead_code"]` | `0` (`-`) | `--force-warn` first on CLI blocks later `-F` (`rc = 0`, warning) |
| `a31` | `a31_cli_forbid_then_force_warn_keeps_forbid` | `["-F", "dead_code", "--force-warn", "dead_code"]` | `1` (`-`) | `-F` first on CLI blocks later `--force-warn` (`rc = 1`, error) |
| `a32` | `a32_cli_force_warn_warnings_rejected` | `["--force-warn", "warnings"]` | `1` (`-`) | ``error[E0602]: `warnings` lint group is not supported with `--force-warn` `` |
| `a33` | `a33_cli_allow_warnings_vs_crate_warn_warnings` | `["-A", "warnings"]` | `0` (`-`) | `-A warnings` permanently sets `can_emit_warnings = false`, silencing crate `#![warn(warnings)]` |
| `a33b` | `a33b_cli_allow_warnings_vs_crate_deny_dead_code` | `["-A", "warnings"]` | `1` (`-`) | `-A warnings` does **not** silence crate `#![deny(dead_code)]` |
| `a34` | `a34_cli_allow_warnings_then_warn_warnings_cli` | `["-A", "warnings", "-W", "warnings"]` | `0` (`-`) | CLI `rfind("warnings")` sees `-W warnings` last, re-enabling `can_emit_warnings` (`1` warning) |
| `a35` | `a35_expect_fulfilled_silent` | `[]` | `0` (`-`) | Fulfilled `#[expect(dead_code, reason = "...")]` produces zero warnings |
| `a36` | `a36_expect_unfulfilled_warn_with_reason` | `[]` | `0` (`-`) | Unfulfilled `#[expect]` emits `unfulfilled_lint_expectations` with `reason` |
| `a37` | `a37_expect_fulfilled_with_cli_allow` | `["-A", "dead_code"]` | `0` (`-`) | `#[expect(dead_code)]` overrides `-A dead_code` and fulfills cleanly |
| `a38` | `a38_expect_unfulfilled_with_cli_allow_still_warns` | `["-A", "dead_code"]` | `0` (`-`) | Under `-A dead_code`, unfulfilled `#[expect(dead_code)]` warns |
| `a39` | `a39_expect_unfulfilled_suppressed_by_cli_allow_warnings` | `["-A", "warnings"]` | `0` (`-`) | `-A warnings` suppresses `unfulfilled_lint_expectations` output |
| `a40` | `a40_expect_fulfilled_suppressed_by_cap_lints_allow` | `["--cap-lints=allow"]` | `0` (`-`) | `--cap-lints=allow` silences both expected lint and checker |
| `a41` | `a41_expect_unfulfilled_suppressed_by_cap_lints_allow` | `["--cap-lints=allow"]` | `0` (`-`) | `--cap-lints=allow` silences unfulfilled expectation (`0` warnings) |
| `a42` | `a42_expect_fulfilled_with_force_warn` | `["--force-warn", "dead_code"]` | `0` (`-`) | Emits `dead_code` forced warning AND fulfills `#[expect(dead_code)]` (`0` unfulfilled warning!) |
| `a43` | `a43_expect_unfulfilled_with_force_warn` | `["--force-warn", "dead_code"]` | `0` (`-`) | Unviolated `#[expect(dead_code)]` under `--force-warn` emits `unfulfilled_lint_expectations` |
| `a44` | `a44_expect_overridden_by_inner_allow_unfulfilled` | `[]` | `0` (`-`) | `#[expect(dead_code)]` overridden by inner `#[allow(dead_code)]` emits `unfulfilled_lint_expectations` |
| `a45` | `a45_expect_overridden_by_inner_allow_under_force_warn` | `["--force-warn", "dead_code"]` | `0` (`-`) | Inner `#[allow(dead_code)]` strips `lint_id` from `ForceWarn`, emitting **both** `dead_code` AND `unfulfilled_lint_expectations` |
| `a46` | `a46_expect_unfulfilled_lint_expectations_ignored` | `[]` | `0` (`-`) | `#[expect(unfulfilled_lint_expectations)]` ignored; always emits unfulfilled + note |
| `a47` | `a47_later_allow_overrides_earlier_warn` | `[]` | `0` (`-`) | `#[warn(L)] #[allow(L)]` on same item allows (`0` warnings) |
| `a48` | `a48_later_warn_overrides_earlier_allow` | `[]` | `0` (`-`) | `#[allow(L)] #[warn(L)]` on same item warns (`1` warning) |
| `a49` | `a49_nested_scope_overrides_crate_deny` | `[]` | `0` (`-`) | Inner `#[allow(dead_code)]` overrides `#![deny(dead_code)]` |
| `b01` | `b01_check_cfg_expected_fast_silent` | `["--check-cfg=cfg(feature, values(\"fast\"))"]` | `0` (`0`) | Matching `--check-cfg` compiles silently; binary exits `0` |
| `b02` | `b02_check_cfg_typo_and_unknown_name_warn` | `["--check-cfg=cfg(feature, values(\"fast\"))"]` | `0` (`-`) | Emits `unexpected_cfgs` (`unexpected_cfg_value` + `unexpected_cfg_name`) |
| `b03` | `b03_check_cfg_checks_false_cfg_attr_predicate` | `["--check-cfg=cfg(feature, values(\"fast\"))"]` | `0` (`-`) | Outer predicate `unknown_pred` in `#[cfg_attr(unknown_pred, ...)]` still checked (`unexpected_cfgs`) |
| `b04` | `b04_cfg_attr_false_strips_malformed_and_unknown_inner_attrs` | `["--check-cfg=cfg(feature, values(\"fast\"))"]` | `0` (`0`) | `#![forbid(unsafe_code)]` + `#[cfg_attr(false, inline(bogus), cfg(unknown), allow(unsafe_code))]` compiles cleanly (`0` errors, `0` warnings) |
| `b05` | `b05_cfg_attr_true_rejects_malformed_inner_attr` | `[]` | `1` (`-`) | `#[cfg_attr(true, inline(bogus_never_valid))]` triggers `error[E0539]: malformed inline attribute input` |
| `b06a` | `b06a_cfg_attr_true_triggers_e0453_and_unexpected_cfgs` | `["--check-cfg=cfg(feature, values(\"fast\"))"]` | `1` (`-`) | Active `#[cfg_attr(true, allow(unsafe_code))]` triggers `E0453`; `unknown_nested_cfg` warns |
| `b06b` | `b06b_cfg_attr_true_allow_plus_false_cfg_strips_item_before_e0453` | `["--check-cfg=cfg(feature, values(\"fast\"))"]` | `0` (`-`) | Same-item `#[cfg_attr(true, allow(unsafe_code))] #[cfg_attr(true, cfg(unknown_nested_cfg))]` warns on `unknown_nested_cfg` then strips item before `E0453` (`rc = 0`) |
| `b07` | `b07_cfg_attr_false_still_requires_attr_item_syntax` | `[]` | `1` (`-`) | `#[cfg_attr(false, 123_not_an_attr)]` rejected at parse (`expected identifier, found 123_not_an_attr`) |
| `b08` | `b08_cfg_false_strips_unvalidated_inner_attrs_and_e0453` | `["--check-cfg=cfg(feature, values(\"fast\"))"]` | `0` (`-`) | `#[cfg(false)] #[allow(unsafe_code)] #[inline(bogus)]` strips item silently (`0` errors/warnings) |
| `b09` | `b09_cfg_false_short_circuits_second_cfg_attr_only_in_order` | `["--check-cfg=cfg()"]` | `0` (`-`) | `#[cfg(false)]` before `#[cfg_attr(unknown_after_false, ...)]` short-circuits (`0` warnings) |
| `b10` | `b10_cfg_unknown_first_then_cfg_false_warns` | `["--check-cfg=cfg()"]` | `0` (`-`) | `#[cfg(unknown_first_cfg)] #[cfg(false)]` emits `unexpected_cfgs` on `unknown_first_cfg` before false `cfg` strips item |
| `b11` | `b11_check_cfg_cap_lints_allow_vs_force_warn_unexpected_cfgs` | `["--check-cfg=cfg()", "--cap-lints=allow", "--force-warn", "unexpected_cfgs"]` | `0` (`-`) | `--force-warn unexpected_cfgs` overrides `--cap-lints=allow` on `unexpected_cfgs` |
| `b12a` | `b12a_crate_expect_covers_item_unexpected_cfgs` | `["--check-cfg=cfg()"]` | `0` (`-`) | `#![expect(unexpected_cfgs)]` catches item `#[cfg(unknown_flag)]` (`0` warnings) |
| `b12b` | `b12b_item_expect_misses_own_cfg_even_when_active` | `["--check-cfg=cfg()", "--cfg=unknown_flag"]` | `0` (`-`) | Item `#[expect(unexpected_cfgs)]` on `#[cfg(unknown_flag)] fn f()` misses it (`unexpected_cfgs` + `dead_code` + `unfulfilled_lint_expectations` emitted!) |
| `b12c` | `b12c_item_expect_covers_cfg_macro_inside_body` | `["--check-cfg=cfg()"]` | `0` (`-`) | Item `#[expect(unexpected_cfgs)]` catches `cfg!(unknown_flag)` inside function body (`0` warnings) |
| `b12d` | `b12d_mod_expect_covers_inner_item_cfg` | `["--check-cfg=cfg()"]` | `0` (`-`) | Enclosing `mod` `#[expect(unexpected_cfgs)]` catches inner item's `#[cfg(unknown_flag)]` (`0` warnings) |

Selected verbatim `rustc` outputs establishing the non-obvious compiler quirks (`a12b`, `a45`, `b12b`):

- **`a12b` (`#![forbid(dead_code)]` overwritten by `#[forbid(unused)]`, then lowered by `#[allow(dead_code)]`, `rc = 0`):**
  ```text
  warning: allow(dead_code) incompatible with previous forbid
   --> probe.rs:3:9
    |
  2 | #[forbid(unused)]
    |          ------ `forbid` level set here
  3 | #[allow(dead_code)]
    |         ^^^^^^^^^ overruled by previous forbid
    |
    = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
    = note: for more information, see issue #81670 <https://github.com/rust-lang/rust/issues/81670>
    = note: `#[warn(forbidden_lint_groups)]` (part of `#[warn(future_incompatible)]`) on by default

  warning: 1 warning emitted
  ```

- **`a45` (`#[expect(dead_code)]` + inner `#[allow(dead_code)]` under `--force-warn dead_code`, `rc = 0`):**
  ```text
  warning: function `unused` is never used
   --> probe.rs:3:4
    |
  3 | fn unused() {}
    |    ^^^^^^
    |
    = note: requested on the command line with `--force-warn dead-code`

  warning: this lint expectation is unfulfilled
   --> probe.rs:1:10
    |
  1 | #[expect(dead_code)]
    |          ^^^^^^^^^
    |
    = note: `#[warn(unfulfilled_lint_expectations)]` on by default

  warning: 2 warnings emitted
  ```

- **`b12b` (item `#[expect(unexpected_cfgs)]` + `--cfg=unknown_flag` misses item `#[cfg(unknown_flag)]`, `rc = 0`):**
  ```text
  warning: unexpected `cfg` condition name: `unknown_flag`
   --> probe.rs:2:7
    |
  2 | #[cfg(unknown_flag)]
    |       ^^^^^^^^^^^^
  ...
  warning: function `f` is never used
   --> probe.rs:3:4
  ...
  warning: this lint expectation is unfulfilled
   --> probe.rs:1:10
    |
  1 | #[expect(unexpected_cfgs)]
    |          ^^^^^^^^^^^^^^^
  ...
  warning: 3 warnings emitted
  ```

### Lean `v4.34.1` Kernel Verification Receipt

`support/LintLevelLatticeCapLintsAndCheckCfgSoundness.lean` (`2,514` lines) compiled with `exit 0` under:

```text
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/LintLevelLatticeCapLintsAndCheckCfgSoundness.lean
```

And the Lean MetaM constant & axiom scan preserved in `support/lean_axiom_audit_output.txt` recorded verbatim:

```text
THEOREMS_AUDITED=261
DEFS_AUDITED=564
UNSAFE_REC_COUNT=0
FORBIDDEN_AXIOM_HITS=0
```

with every theorem relying exclusively on `[]` (no axioms) or `[propext]`.

---

## Revalidation

To verify whether any `rustc` toolchain change alters these findings, run the following checks:

1. **Re-execute the 70-case empirical matrix against any target `rustc`:**
   ```bash
   python3 support/probe_lint_lattice_and_check_cfg.py --output /tmp/reval_probe.json
   ```
   Confirm `exit 0` and diff the `"compile_returncode"` and `"compile_stderr"` fields against `support/probe_results.json`. Pay special attention to `a07`–`a12b` (whether FCW `#81670` has become a hard error or direct `forbid` overwrites are guarded) and `b12b` (whether `InvocationCollector::flat_map_node` changes `lint_node_id` binding for item `#[expect]`).

2. **Re-verify the Lean `v4.34.1` formalization and MetaM purity check:**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/LintLevelLatticeCapLintsAndCheckCfgSoundness.lean
   ```
   Expect `exit 0` with zero errors and zero warnings; re-run `collectAxioms` + `env.constants` `_unsafe_rec` inspection to confirm `UNSAFE_REC_COUNT=0` and `FORBIDDEN_AXIOM_HITS=0`.

3. **Targeted upstream source drift check (`rust-lang/rust` and `joshlf/anneal`):**
   Diff these exact implementation files against the SHA anchors in `support/resolved_revisions.json`:
   - `compiler/rustc_lint_defs/src/lib.rs` (`Level`, `Level::from_str`, `LintExpectationId`)
   - `compiler/rustc_middle/src/lint.rs` (`LevelSpec::new`, `reveal_actual_level_spec`, `emit_lint_base`)
   - `compiler/rustc_lint/src/{levels.rs, expect.rs}` (`add_command_line`, `insert_spec`, `check_expectations`)
   - `compiler/rustc_session/src/session.rs` (`build_session` `can_emit_warnings`) and `compiler/rustc_errors/src/lib.rs` (`DiagCtxtInner::emit_diagnostic`)
   - `compiler/rustc_attr_parsing/src/attributes/cfg.rs`, `compiler/rustc_expand/src/config.rs`, and `compiler/rustc_expand/src/expand.rs` (`parse_name_value`, `expand_cfg_attr`, `configure`, `assign_id!`, `flat_map_node`)
   - `joshlf/anneal`: `trusted/rustc-capture/src/driver.rs` (`AnalysisCallbacks::after_analysis`).

4. **Corpus structural validation:**
   ```bash
   python3 tools/reference.py catalog
   python3 tools/reference.py check
   ```
   Confirm `reference check passed`.
