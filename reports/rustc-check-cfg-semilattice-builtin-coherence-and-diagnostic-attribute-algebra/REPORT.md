# rustc check-cfg accumulation, builtin-cfg coherence, atomic cfgs, and `#[diagnostic::*]` merge algebra

## Summary

Four mechanisms of the `rustc` front end were examined by source audit at four
pinned revisions, by a subprocess probe against a real `rustc 1.98.0-nightly`
(662 compiler and program runs), and by a kernel-checked Lean 4 model (105
theorems, no placeholder proofs, `propext` the only axiom used). What to retain:

1. **`--check-cfg` accumulation is a per-name join.** The state for each cfg
   name is *absent*, `ExpectedValues::Some(set)` or `ExpectedValues::Any`.
   Each `--check-cfg` argument joins into it: sets are unioned, and `Any`
   (from `values(any())`) is an absorbing top in either order. The
   `unexpected_cfgs` verdict for every `#[cfg]` predicate is therefore
   independent of the order (and multiplicity) of `--check-cfg` arguments.
   This is proved for all argument lists and observed for all 120 orders of a
   five-argument set; the model also predicted the compiler's verdicts on 80
   random argument lists.
2. **`CheckCfg::fill_well_known` is not a join for bare well-known names.** A
   user `--check-cfg 'cfg(unix, values("x"))'` *removes* the implicit bare form:
   `#[cfg(unix)]` is then reported as an unexpected value. For valued
   well-known names (`panic`, `target_os`, ...) the builtin values are unioned
   with the user's.
3. **Tool cfgs are well-known; `test` deliberately is not.** `clippy`, `doc`,
   `doctest`, `miri`, `rustfmt` are expected although `rustc` never sets them;
   `rust_analyzer` was added by a commit of 2026-08-10 and is *not* well-known
   in the 1.98.0 nightlies; `test` is treated as a user-space cfg so that a build
   system can decline to expect it.
4. **The builtin-cfg gate is a lint, not a hard error.** `--cfg ub_checks`,
   `--cfg debug_assertions`, `--cfg unix`, `--cfg panic="abort"` and similar
   are rejected by the deny-by-default lint `explicit_builtin_cfgs_in_flags`.
   With `-A`, `-W`, `--cap-lints allow|warn` or an in-source `#![allow]`, the
   same command line is accepted and the crate observes `cfg!(ub_checks) ==
   true` while `core::intrinsics::ub_checks()` is `false`. Flag-to-cfg
   coherence holds exactly when no gated builtin pair is spoofed; the gate
   guarantees that only while the lint stays at an error level. The gate also
   does not match some shapes (`--cfg target_has_atomic` without a value).
5. **Atomic cfgs come from the target specification, not from target
   features.** `x86_64-unknown-linux-gnu` never gets
   `target_has_atomic="128"`, including with `-C target-cpu=x86-64-v3` or
   `-C target-feature=+cmpxchg16b`; `x86_64-apple-darwin` and
   `x86_64-pc-windows-msvc` have it by specification. `i686` targets have
   64-bit compare-and-swap without `target_has_atomic_primitive_alignment="64"`.
   Since a commit of 2026-11-09 the width range may additionally depend on
   the `-C target-cpu` *name* through a per-CPU table (populated for BPF).
6. **Only `cfg_select!` is stable.** `cfg(target(..))`, `cfg(version(..))` and
   `#[cfg_accessible(..)]` are feature-gated hard errors (`E0658`) at every
   examined revision, including the main branch head of 2026-11-22.
7. **`#[diagnostic::*]` attributes never hard-error by default, but they are
   ordinary warn-level lints.** Unknown, feature-gated, malformed and misplaced
   uses compile with warnings; `-D warnings` turns each into an error.
8. **Stacked `#[diagnostic::on_unimplemented]` attributes form a
   non-commutative monoid:** first-wins on `message` and `label`,
   concatenation on `note`. Evaluation uses the same operation, so evaluating
   a stack equals evaluating its merge. Identical notes are printed twice.
9. **`#[diagnostic::do_not_recommend]` hoists the reported predicate to the
   head of the outermost marked impl.** The current solver's bottom-up loop and
   the next-generation solver's top-down walk provably select the same goal on
   a linear chain, and both do so on the probe's two-impl chain.
10. **`#[diagnostic::on_move]` placeholders changed spelling.** `{This}` was
    accepted until a commit of 2026-10-13 renamed it to `{this}`; `{Self}`
    always prints the bare type name without generic arguments.

The diagnostic attribute namespace is specified by RFC 3368, not RFC 3399
(which concerns `cfg` attributes in `where` clauses).

## Applicability

### Subjects and how they relate

| Label | Revision of `rust-lang/rust` | Date (UTC) | Role |
| --- | --- | --- | --- |
| R98a | `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` | 2026-05-30 | Compiler that `joshlf/anneal` at `c131b320` pins (`1.98.0-nightly (f8a08b688 2026-05-30)`); source compared with R98 |
| R98 | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | 2026-05-31 | `rustc 1.98.0-nightly`, LLVM 22.1.6, host `x86_64-unknown-linux-gnu`; **every execution result in this report**; source audited |
| R102 | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | 2026-11-11 | `rustc 1.102.0-nightly`; source audited; not executed here |
| Rmain | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | 2026-11-22 | Head of `main` on the observation date; source audited for drift |

R98a is an ancestor of R98 (69 commits), R98 of R102 (18,861 commits) and
R102 of Rmain (2,474 commits). Of 41 files compared between R98a and R98, 36
are byte-identical, including every file that implements cfg construction,
`--check-cfg` parsing, cfg evaluation, the diagnostic attribute parsers, the
examined target specifications and the next-generation solver's
`do_not_recommend` walk. The five that differ do so only in version
placeholders, documentation comments, one new macro's documentation, and one
hunk of `fulfillment_errors.rs` that suppresses `#[rustc_on_unimplemented]`
notes when a `#[derive]` suggestion is shown; the function
`apply_do_not_recommend` in that file is unchanged.
Execution results for R98 are therefore extended to R98a by derivation, with
that hunk as the single stated exception; R98a itself was not executed.

`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` is examined as
a consumer: which compiler it pins, which `--cfg` arguments it passes or
records, and how its trusted MIR boundary treats the flag-dependent runtime
checks. No Anneal code was executed.

Lean `v4.34.1` (`leanprover/lean4` at `5045d005...`) checks the model in
`support/CheckCfgSemilatticeAndDiagnosticMerge.lean`. The model is independent
of Anneal's Lean sources and imports nothing beyond Lean's core library.

RFC text (`rust-lang/rfcs` at `f43d5789...`) and the Reference
(`rust-lang/reference` at `c9cc3282...`) supply the normative and descriptive
statements quoted in section 5.

### Which evidence covers which revision

| Topic | R98 | R102 | Rmain |
| --- | --- | --- | --- |
| check-cfg accumulation and lint decision | source + execution | source (same logic) | source (same logic) |
| well-known list | source + execution | source: adds `rust_analyzer`, `target_has_threads` | as R102 |
| builtin-cfg gate | source + execution | source: same arms plus `target_has_threads`, `target_has_reliable_f16b`; `emscripten_wasm_eh` removed | as R102 |
| atomic cfgs | source + execution (322 targets) | source: per-CPU width table | as R102 |
| `cfg_select!` and gated predicates | source + execution | source: same feature status | source: same feature status |
| directive merge | source + execution | source: merge extended to all six fields | as R102 |
| `do_not_recommend` | source + execution (both solvers) | source: same loop | as R102 |
| `on_move` placeholders | source + execution (`{This}`) | source (`{this}`) | source (`{this}`) |

A record of an earlier run against R102 is preserved in
`support/prior_observation_rustc_1_102_0_nightly_3ef0c22cd.json`. It was not
reproduced for this report and its command lines were not recorded; it is
cited only where its quoted compiler output is unambiguous, and always
labelled as a prior observation.

### Configuration and scope

- Host and default target `x86_64-unknown-linux-gnu`; other targets are
  examined only through `rustc --print cfg --target <t>`, which needs no
  installed standard library for that target.
- Parts of the probe use nightly-only flags (`-Z ub-checks`, `-Z sanitizer`,
  `-Z next-solver`, `-Z unstable-options`) and feature gates. Stable-channel
  behaviour is approximated by `RUSTC_BOOTSTRAP=-1`, which makes a nightly
  compiler refuse unstable features; no stable release binary was run.
- All compilations are single-crate invocations of `rustc` (no Cargo).
  Statements about Cargo appear only where the compiler's own source comments
  make them and are marked as such.
- The Lean model abstracts hash sets to lists observed through membership,
  hash maps to lookup functions, symbols to an arbitrary type with decidable
  equality, and format strings to an abstract type. It models the decision
  logic quoted in this report, not `rustc` as a whole.

## Findings

Unless a line says otherwise, source citations are to R98
(`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) and execution results are from
`support/probe_results.json`.

### 1. `--check-cfg`: a per-name join, order-independent

#### 1.1 Data model

`compiler/rustc_session/src/config/cfg.rs`, lines 44-59:

```rust
pub struct CheckCfg {
    pub exhaustive_names: bool,
    pub exhaustive_values: bool,
    pub expecteds: FxHashMap<Symbol, ExpectedValues<Symbol>>,
    pub well_known_names: FxHashSet<Symbol>,
}
pub enum ExpectedValues<T> {
    Some(FxHashSet<Option<T>>),
    Any,
}
```

Inside `Some`, the element `None` stands for the bare form `#[cfg(name)]` and
`Some(v)` for `#[cfg(name = "v")]`. `Some(∅)` (from `cfg(name, values())`) and
an absent key are different states: the first makes the *name* expected with
no acceptable value, the second leaves the name unexpected.

#### 1.2 Accumulation

`compiler/rustc_interface/src/interface.rs`, `parse_check_cfg` (lines 116-311).
Both exhaustiveness flags start as `!specs.is_empty()`. A bare `cfg(name)` is
given an implicit `none()` (lines 269-272). `cfg(any())` sets
`exhaustive_names = false` and must appear alone in its argument (lines
279-284). Every other argument updates each listed name (lines 286-306):

```rust
check_cfg.expecteds.entry(name.name)
    .and_modify(|v| match v {
        ExpectedValues::Some(v) if !values_any_specified => v.extend(values.clone()),
        ExpectedValues::Some(_) => *v = ExpectedValues::Any,
        ExpectedValues::Any => {}
    })
    .or_insert_with(|| {
        if values_any_specified { ExpectedValues::Any }
        else { ExpectedValues::Some(values.clone()) }
    });
```

Read as algebra: with `join(Some a, Some b) = Some(a ∪ b)` and
`join(_, Any) = join(Any, _) = Any`, an existing entry `e` becomes
`join(e, new)` and a missing entry becomes `new`. The Lean model states this
as `mergeEntry_some` and `mergeEntry_none`, both proved by case analysis on the
three `and_modify` arms and the two `or_insert_with` branches. The join is
associative on the nose, commutative and idempotent up to set extensionality,
has identity `Some(∅)` and absorbing element `Any` (theorems
`ExpectedValues.join_assoc`, `join_comm`, `join_idem`, `join_bot_left`,
`join_bot_right`, `join_any_left`, `join_any_right`). `Any` is never
observationally equal to a `Some` set (`any_ne_some`), which matters because
the diagnostic code pattern-matches on the constructor.

Basis: source + derived (Lean).

#### 1.3 The lint decision

`compiler/rustc_attr_parsing/src/attributes/cfg.rs`, `parse_name_value`
(lines 215-233):

```rust
match cx.sess.check_config.expecteds.get(&name) {
    Some(ExpectedValues::Some(values)) if !values.contains(&value.map(|(v, _)| v)) =>
        /* lint UNEXPECTED_CFGS: unexpected value */,
    None if cx.sess.check_config.exhaustive_names =>
        /* lint UNEXPECTED_CFGS: unexpected name */,
    _ => { /* not unexpected */ }
}
```

`UNEXPECTED_CFGS` is warn-by-default
(`compiler/rustc_lint_defs/src/builtin.rs`, lines 2990-2994). With no
`--check-cfg` argument at all, `exhaustive_names` is `false` and the map is
empty, so the lint cannot fire.

Observed verdicts for the predicates `mode="alpha"`, `mode="beta"`, `mode`,
`lvl="x"`, `lvl="y"`, `lvl`, `other` (`ok` / `N` = unexpected name / `V` =
unexpected value):

| `--check-cfg` arguments | verdicts |
| --- | --- |
| *(none)* | ok ok ok ok ok ok ok |
| `cfg()` | N N N N N N N |
| `cfg(any())` | ok ok ok ok ok ok ok |
| `cfg(mode)` | V V ok N N N N |
| `cfg(mode, values("alpha"))` | ok V V N N N N |
| `cfg(mode, values(none(), "alpha"))` | ok V ok N N N N |
| `cfg(mode, values())` | V V V N N N N |
| `cfg(mode, values("alpha"))` + `cfg(mode, values("beta", none()))` | ok ok ok N N N N |
| `cfg(mode, values("alpha"))` + `cfg(mode, values(any()))` | ok ok ok N N N N |
| `cfg(mode, values(any()))` + `cfg(mode, values("alpha"))` | ok ok ok N N N N |
| `cfg(mode, lvl, values("x"))` | V V V ok V V N |
| `cfg(any())` + `cfg(mode, values("alpha"))` | ok V V ok ok ok ok |

All lints are warnings (exit status 0); `-D unexpected_cfgs` makes them errors
(exit status 1).

Basis: source + execution.

#### 1.4 Order independence

The Lean theorem `lint_parse` gives the denotation of the fold: for any
argument list, the verdict for `(name, value)` is

- *ok* or *unexpected value*, according to whether some argument that mentions
  `name` grants `value` (lists it, or says `values(any())`), if any argument
  mentions `name`;
- otherwise *unexpected name* if the list is non-empty and contains no
  `cfg(any())`, else *ok*.

Each ingredient is an existential over the list, hence invariant under
permutation. `checkCfg_fold_perm_invariant` states: if `l₁` is a permutation of
`l₂` then `lint (parseCheckCfg l₁) name value = lint (parseCheckCfg l₂) name
value` for all names and values. `checkCfg_duplicate_spec` adds that repeating
an argument changes nothing, and `checkConfig_perm_invariant` extends order
independence through the well-known fill of section 1.5 for an arbitrary
well-known table.

Execution: the five arguments `cfg(mode, values("alpha"))`,
`cfg(mode, values("beta"))`, `cfg(lvl, values(any()))`,
`cfg(lvl, values("x"))`, `cfg(mode)` were passed in all 120 orders; all runs
produced the single verdict vector `ok ok ok ok ok ok N`. A reference
implementation of the model inside the probe predicted the compiler's verdicts
for every named case, every permutation and 80 pseudo-random argument lists
(seed recorded) with zero mismatches. The reference implementation is a
transcription of the Lean definitions into Python, so this is a differential
test of the model against the compiler, not an independent derivation.

Basis: derived (Lean) + execution.

#### 1.5 Well-known fill: union for valued names, shadowing for bare names

After parsing, `check_cfg.fill_well_known(&sess.target)` runs
(`interface.rs`, lines 460-462). It returns immediately when both
exhaustiveness flags are `false`, i.e. when no `--check-cfg` argument was
given (`cfg.rs`, lines 340-342). Its insertion macro (lines 357-362) is

```rust
macro_rules! ins {
    ($name:expr, $values:expr) => {{
        self.well_known_names.insert($name);
        self.expecteds.entry($name).or_insert_with($values)
    }};
}
```

used in two shapes:

- `ins!(sym::unix, no_values);` where `no_values` is `Some({None})`. Because
  of `or_insert_with`, an entry created by the user is left untouched: the
  bare form is **not** added to it.
- `ins!(sym::panic, empty_values).extend(...)`. The entry (the user's, if
  present) is extended with the builtin values, and `extend` is a no-op on
  `Any`: a union.

Observed:

| arguments | predicate | verdict | compiler note |
| --- | --- | --- | --- |
| `cfg()` | `unix` | ok | |
| `cfg(unix, values("x"))` | `unix` | unexpected value | ``expected values for `unix` are: `x` `` |
| `cfg(debug_assertions, values("x"))` | `debug_assertions` | unexpected value | ``expected values for `debug_assertions` are: `x` `` |
| `cfg()` | `panic = "zzz"` | unexpected value | ``expected values for `panic` are: `abort`, `immediate-abort`, and `unwind` `` |
| `cfg(panic, values("zzz"))` | `panic = "zzz"`, `panic = "abort"` | ok, ok | |
| `cfg(target_os, values("myos"))` | `target_os = "myos"`, `target_os = "linux"` | ok, ok | |
| `cfg(panic, values(any()))` | `panic = "zzz"` | ok | |

The Lean theorem `ce_wellKnown_fill_shadows_bare_form` exhibits the asymmetry:
with the user argument `cfg(unix, values("x"))` the model's verdict for bare
`unix` is *unexpected value*, although the join of the user entry with the
well-known entry `Some({None})` accepts the bare form.
`wellKnown_fill_unions_valued_names` is the positive counterpart. Because the
fill runs once after all arguments have been folded, it does not disturb order
independence.

Basis: source + execution + derived (Lean).

#### 1.6 Which names are well-known

`fill_well_known` (lines 383-499) inserts every name that
`default_configuration` can set, unconditionally, with two documented
deviations (comments at lines 371-374 and 387-390):

> One exception is the `test` cfg which is consider to be a "user-space" cfg,
> despite being also set by in `default_configuration` above. It allows the
> build system to "deny" using the config by not marking it as expected
> (e.g. `lib.test = false` for Cargo).

> These four are never set by rustc, but we set them anyway; they should not
> trigger the lint because `cargo clippy`, `cargo doc`, `cargo test`,
> `cargo miri run` and `cargo fmt` (respectively) can set them.

followed by `ins!` lines for `clippy`, `doc`, `doctest`, `miri`, `rustfmt`
(five names despite "four"). R102 adds `ins!(sym::rust_analyzer, no_values);`
(line 396; introduced by commit `0166f5056a311d91cd38a8e3199a7ae8b84a05c4`,
2026-08-10) and the upstream documentation `src/doc/rustc/src/check-cfg.md`
lists `rust_analyzer` from its `2026-08-11T` edition.

Observed on R98 under `--check-cfg 'cfg()'`: `miri`, `clippy`, `doc`,
`doctest`, `rustfmt`, `unix`, `windows`, `debug_assertions`, `proc_macro` and
bare `target_has_atomic` are expected; `test`, `rust_analyzer` and `feature`
are unexpected names; bare `panic` is an unexpected value. The prior
observation on R102 contains a case named
`tool_cfgs_miri_clippy_ra_doc_under_empty_check_cfg` with exit status 0 and
empty standard error; its input is not preserved, so it is consistent with,
but does not independently establish, the R102 source reading.

`rust_analyzer` illustrates that being a registered *tool* is not being a
well-known *cfg*: at R98 `rust_analyzer` is already one of the predefined
tool names (`compiler/rustc_resolve/src/macros.rs`, lines 150-154: `clippy`,
`rustfmt`, `diagnostic`, `miri`, `rust_analyzer`) but not a well-known cfg.

Basis: source (R98, R102) + execution (R98) + documentation.

### 2. Builtin cfgs on the command line

#### 2.1 How the crate configuration is built

`compiler/rustc_session/src/config.rs`, lines 1568-1576:

```rust
pub fn build_configuration(sess: &Session, mut user_cfg: Cfg) -> Cfg {
    // First disallow some configuration given on the command line
    cfg::disallow_cfgs(sess, &user_cfg);
    // Then combine the configuration requested by the session (command line) with
    // some default and generated configuration items.
    user_cfg.extend(cfg::default_configuration(sess));
    user_cfg
}
```

`Cfg` is `FxIndexSet<(Symbol, Option<Symbol>)>` and a predicate is true iff
`sess.config.contains(&(name, value))` (`attributes/cfg.rs`, lines 272-278).
The configuration is thus the *union* of the `--cfg` pairs and
`default_configuration(sess)`, which reads compiler flags and the target
specification (`cfg.rs`, lines 167-335). Order and repetition of `--cfg`
arguments do not affect any predicate.

The same flags drive code generation independently of the cfg set. For the
three runtime-check families the single source of truth is
`compiler/rustc_middle/src/mir/syntax.rs`, lines 1591-1599:

```rust
impl RuntimeChecks {
    pub fn value(self, sess: &rustc_session::Session) -> bool {
        match self {
            Self::UbChecks => sess.ub_checks(),
            Self::ContractChecks => sess.contract_checks(),
            Self::OverflowChecks => sess.overflow_checks(),
        }
    }
}
```

with `sess.ub_checks()` defined as `-Z ub-checks` defaulting to
`-C debug-assertions`, and `sess.overflow_checks()` as `-C overflow-checks`
defaulting to `-C debug-assertions`
(`compiler/rustc_session/src/session.rs`, lines 724-734). A cfg predicate and
the corresponding runtime behaviour agree only if nothing but
`default_configuration` contributes the builtin pair.

#### 2.2 The gate

`disallow_cfgs` (`cfg.rs`, lines 96-164) buffers the lint
`EXPLICIT_BUILTIN_CFGS_IN_FLAGS` for each offending `--cfg` pair. Its comment
states the purpose and the single exemption:

> We want to restrict setting builtin cfgs that will produce incoherent
> behavior between the cfg and the rustc cli flag that sets it. [...]
> By-default all builtin cfgs are disallowed, only those are allowed:
>  - test: as it makes sense to the have the `test` cfg active without the
>    builtin test harness. See Cargo `harness = false` config.

The lint is declared `Deny` (`builtin.rs`, lines 3024-3027). The match arms
are shape-specific, for example `(sym::overflow_checks, None)`,
`(sym::panic, Some(sym::abort | sym::unwind | sym::immediate_abort))`,
`(sym::target_has_atomic, Some(_))`, `(sym::unix, None)`.

Observed at the default lint level (each as the only `--cfg` argument of an
otherwise empty library crate):

| Result | `--cfg` arguments (with the compiler's "controlled by" note) |
| --- | --- |
| error, exit 1 | `ub_checks` (`-Z ub-checks`); `overflow_checks` (`-C overflow-checks`); `contract_checks` (`-Z contract-checks`); `debug_assertions` (`-C debug-assertions`); `sanitize="address"` (`-Z sanitizer`); `panic="abort"`, `panic="unwind"`, `panic="immediate-abort"` (`-C panic`); `proc_macro` (`--crate-type proc-macro`); `target_feature="avx2"` (`-C target-feature`); `fmt_debug="full"` (`-Z fmt-debug`); `unix`, `windows`, `target_os="linux"`, `target_arch="x86_64"`, `target_family="unix"`, `target_pointer_width="64"`, `target_has_atomic="128"`, `target_has_atomic_load_store="8"`, `target_has_atomic_primitive_alignment="8"`, `target_thread_local`, `relocation_model="pic"` (`--target`) |
| accepted, exit 0, no diagnostic | `test`; `miri`, `clippy`, `doc`, `doctest`, `rustfmt`, `rust_analyzer`; `feature="x"`; `anneal_driver_test`; and the unmatched shapes `panic`, `panic="zzz"`, `target_os`, `target_arch`, `target_has_atomic`, `target_has_atomic_load_store`, `overflow_checks="x"` |

The error reads ``unexpected `--cfg ub_checks` flag`` with the notes
``config `ub_checks` is only supposed to be controlled by `-Z ub-checks` ``,
`manually setting a built-in cfg can and does create incoherent behaviors`,
and `` `#[deny(explicit_builtin_cfgs_in_flags)]` on by default ``.

The gate is conservative in one direction and incomplete in the other:

- `--cfg unix` is rejected on a `unix` target although it adds nothing
  (theorem `gate_strictly_conservative`).
- Shapes that no arm matches pass. Most are harmless because `rustc` never
  sets them (`panic` without a value). One is not: bare `target_has_atomic`
  is set by `default_configuration` (only on nightly builds and only when the
  target has compare-and-swap, lines 284-289) but the arm is
  `(sym::target_has_atomic, Some(_))`. `rustc --print cfg --target
  thumbv6m-none-eabi` prints `target_has_atomic_load_store` and no bare
  `target_has_atomic`; adding `--cfg target_has_atomic` prints both, with
  exit status 0 (theorem `ce_gate_gap_bare_target_has_atomic`).
- `--print cfg` does not run the lint at all: `rustc --print cfg -Z
  ub-checks=no` prints no `ub_checks` line, and adding `--cfg ub_checks`
  prints `ub_checks` with exit status 0 and no diagnostic.

Basis: source + execution.

#### 2.3 The gate depends on the lint level

A test program prints `cfg!(ub_checks)`, `core::intrinsics::ub_checks()`,
`cfg!(overflow_checks)`, whether `255u8 + 1` panicked, and
`cfg!(debug_assertions)`. "Spoof" means `-Z ub-checks=no -C overflow-checks=off
-C debug-assertions=off --cfg ub_checks --cfg overflow_checks --cfg
debug_assertions`.

| Configuration | exit | gate diagnostics | `cfg!(ub_checks)` | intrinsic `ub_checks()` | `cfg!(overflow_checks)` | add panicked | `cfg!(debug_assertions)` |
| --- | --- | --- | --- | --- | --- | --- | --- |
| default flags | 0 | none | true | true | true | true | true |
| all three flags off | 0 | none | false | false | false | false | false |
| all three flags on | 0 | none | true | true | true | true | true |
| spoof | 1 | 3 errors | - | - | - | - | - |
| spoof + `-A explicit_builtin_cfgs_in_flags` | 0 | none | true | **false** | true | **false** | true |
| spoof + `-W explicit_builtin_cfgs_in_flags` | 0 | 3 warnings | true | **false** | true | **false** | true |
| spoof + `--cap-lints allow` | 0 | none | true | **false** | true | **false** | true |
| spoof + `--cap-lints warn` | 0 | 3 warnings | true | **false** | true | **false** | true |
| spoof + `#![allow(explicit_builtin_cfgs_in_flags)]` in the crate | 0 | none | true | **false** | true | **false** | true |

Without spoofing, the cfg view and the code-generation view agree in all three
baselines. With spoofing accepted, they diverge: the crate is compiled as if
checks were on (every `cfg!`-guarded branch is active, and so is every
`debug_assert!`, which expands to `if $crate::cfg!(debug_assertions) { .. }`,
`library/core/src/macros/mod.rs` lines 287-293) while the intrinsic and the
arithmetic overflow check are off. Any
driver that lowers or caps lint levels for a crate, on the command line or
through a crate attribute it does not control, removes the gate for that
crate.

Basis: execution; the mechanism (a buffered lint attached to the crate root)
is source.

#### 2.4 Formal statement

In the Lean model, `flagSets f b` is membership of the builtin pair `b` in
`default_configuration` for flags `f`; `cfgActive f user a` is membership of
`a` in the union of `user` and that default; `gated b` is "some arm of
`disallow_cfgs` matches `b`"; and `disallowBuiltinCfgs user` is the list of
gated entries of `user`.

- `Coherent f user` := for every gated `b`, `cfgActive f user b ↔ flagSets f b`.
- `Spoofed f a` := `a` is a gated builtin pair that the flags do not imply.
- **`coherentSession_iff_no_spoofed_builtin_cfg`**:
  `Coherent f user ↔ ∀ a ∈ user, ¬ Spoofed f a`.
- `disallow_empty_implies_coherent`: if `disallowBuiltinCfgs user = []` then
  `Coherent f user` for every `f`; in particular
  `cfgActive f user ubChecks ↔ f.ubChecks` (`ubChecks_coherent_of_gate`).
- `accepted_at_deny_implies_coherent`: a session accepted with the lint at an
  error level is coherent.
- **`ce1_spoofed_cli_ub_checks_diverges_from_codegen`**: with the lint at
  `allow` or `warn`, the session with all flags off and `--cfg ub_checks` is
  accepted, `cfg(ub_checks)` is active, the code-generation value is `false`,
  the session is not coherent, and the same session is rejected at `deny`.
- `test_cfg_is_exempt`: `--cfg test` passes the gate without the harness flag.

These theorems are about the model. Their link to the compiler is the quoted
source plus the tables in 2.2 and 2.3; the coherence notion covers only the
pairs the model enumerates (the four check cfgs, three `panic` values, three
`sanitize` values, `proc_macro`, `unix`, `windows`, `test`, bare
`target_has_atomic`).

Basis: derived (Lean) from source + execution.

#### 2.5 Two cfg values from one flag; two flags for one cfg value

`default_configuration`, lines 216-223 and 235-245:

```rust
// Since the ImmediateAbort strategy is new, it also sets cfg(panic="abort"), so that code
// which is trying to detect whether unwinding is enabled by checking for cfg(panic="abort")
// does not need to be updated.
ins_sym!(sym::panic, sess.panic_strategy().desc_symbol());
if sess.panic_strategy() == PanicStrategy::ImmediateAbort {
    ins_sym!(sym::panic, PanicStrategy::Abort.desc_symbol());
}
...
for mut s in sess.sanitizers() {
    // KASAN is still ASAN under the hood, so it uses the same attribute.
    if s == SanitizerSet::KERNELADDRESS { s = SanitizerSet::ADDRESS; }
    // KHWASAN is still HWASAN under the hood, so it uses the same attribute.
    if s == SanitizerSet::KERNELHWADDRESS { s = SanitizerSet::HWADDRESS; }
    ins_str!(sym::sanitize, &s.to_string());
}
```

Observed with `--print cfg`:

| Flags | relevant lines | exit |
| --- | --- | --- |
| `-C panic=unwind` | `panic="unwind"` | 0 |
| `-C panic=abort` | `panic="abort"` | 0 |
| `-C panic=immediate-abort` | *(none)*; ``error: `-Cpanic=immediate-abort` requires `-Zunstable-options` and a nightly compiler`` | 1 |
| `-Z unstable-options -C panic=immediate-abort` | `panic="abort"`, `panic="immediate-abort"` | 0 |
| `-Z sanitizer=address` | `sanitize="address"` | 0 |
| `-Z sanitizer=address,leak` | `sanitize="address"`, `sanitize="leak"` | 0 |
| `-Z sanitizer=kernel-address --target x86_64-unknown-none` | `sanitize="address"` | 0 |
| `-Z sanitizer=kernel-address` (host target) | `sanitize="address"` is printed, then `error: kernel-address sanitizer is not supported for this target` | 1 |
| `-Z sanitizer=hwaddress --target aarch64-unknown-linux-gnu` | `sanitize="hwaddress"` | 0 |
| `-Z sanitizer=kernel-hwaddress --target aarch64-unknown-none` | `sanitize="hwaddress"` | 0 |

Consequences: `cfg(panic = "abort")` does not identify the panic strategy
(`panic_abort_cfg_not_injective`), and `cfg(sanitize = "address")` does not
distinguish the user-space from the kernel sanitizer (`kernel_sanitizers_fold`).
`cfg(sanitize)` is feature-gated (`cfg_sanitize`,
`compiler/rustc_feature/src/builtin_attrs.rs`, line 29).

Basis: source + execution.

#### 2.6 Relevance to Anneal's compiler boundary

At `joshlf/anneal` `c131b320`:

- `trusted/rustc-capture/src/driver.rs` line 25 pins
  `COMPILER_VERSION = "1.98.0-nightly (f8a08b688 2026-05-30)"` (R98a). Its
  `config` callback (lines 33-73) adjusts only the error format, the version
  check and the default sysroot; all command-line arguments go unchanged to
  `rustc_driver::run_compiler` (line 137). The driver therefore inherits the
  gate of 2.2 with the lint-level dependence of 2.3; it adds no filtering of
  `--cfg` of its own. Its test
  `trusted/rustc-capture/tests/compiler_session.rs` (lines 92-110) passes
  `--cfg anneal_driver_test`, a user-space cfg that no arm of the gate
  matches (observed accepted on R98).
- `vendor/lean-miri/Miri/Input/ProducerEvidence.lean` records producer
  settings. `pinnedMiriDefaultArgs` (lines 85-88) begins with `--cfg=miri`,
  a tool cfg that is well-known and ungated. `requestedCfgs` (lines 90-99)
  keeps "every explicit cfg argument in its original compiler syntax" and
  "does not infer built-in target cfgs from a target triple";
  `compareReferenceInputs` (lines 104-118) requires
  `requestedCfgs actual == requestedCfgs reference`, both `requested_cfg_miri`
  flags, and equal `effective_panic_strategy` strings.
- `trusted/lean/Trusted/MirAst.lean` (lines 548-556) documents that
  `Operand::RuntimeChecks` "is intentionally unmodeled in `MirAst.Operand` and
  must fail closed (be rejected by capture)", and
  `trusted/correspondence/Trusted/Correspondence.lean` (lines 1399-1400)
  resolves `runtimeChecks` to an error.

What the findings imply for a consumer of such evidence (derived):

1. Comparing explicit `--cfg` arguments as ordered arrays is stricter than the
   compiler's semantics, which is a set union (2.1); equal arrays imply equal
   contributions, so the comparison is sound, and it may reject sessions that
   differ only in argument order or repetition.
2. Explicit cfg equality does not by itself give equality of the effective
   cfg set: the builtin part is a function of flags and target (2.1), and it
   is a *faithful* function of them only when no gated builtin pair appears
   among the explicit arguments or the gate is known to have run at an error
   level (2.3, 2.4). An explicit-argument list containing, say,
   `debug_assertions` shows that the gate did not run at an error level; from
   then on the cfg view cannot be inferred from the flags.
3. Rejecting `RuntimeChecks` operands removes the code-generation side of the
   three check families from the modelled MIR, but the cfg side is resolved
   during expansion and leaves no operand behind: MIR captured from a spoofed
   session contains the `cfg`-selected branches with no marker.
4. An equal `effective_panic_strategy` string is finer than the cfg view:
   `cfg(panic = "abort")` is true for both `abort` and `immediate-abort`
   (2.5).

Basis: source (Anneal, R98a/R98) + derived.

### 3. `target_has_atomic*`

#### 3.1 The loop

`default_configuration`, lines 269-305 (R98):

```rust
let layout = sess.target.parse_data_layout().unwrap_or_else(|err| { sess.dcx().emit_fatal(err); });
let mut has_atomic = false;
for (i, align) in [(8, layout.i8_align), (16, layout.i16_align), (32, layout.i32_align),
                   (64, layout.i64_align), (128, layout.i128_align)] {
    if i >= sess.target.min_atomic_width() && i <= sess.target.max_atomic_width() {
        if !has_atomic {
            has_atomic = true;
            if sess.is_nightly_build() {
                if sess.target.atomic_cas { ins_none!(sym::target_has_atomic); }
                ins_none!(sym::target_has_atomic_load_store);
            }
        }
        let mut insert_atomic = |sym, align: Align| {
            if sess.target.atomic_cas { ins_sym!(sym::target_has_atomic, sym); }
            if align.bits() == i { ins_sym!(sym::target_has_atomic_primitive_alignment, sym); }
            ins_sym!(sym::target_has_atomic_load_store, sym);
        };
        insert_atomic(sym::integer(i), align);
        if sess.target.pointer_width as u64 == i {
            insert_atomic(sym::ptr, layout.pointer_align().abi);
        }
    }
}
```

Inputs: `min_atomic_width()` (default 8), `max_atomic_width()` (default
pointer width; `compiler/rustc_target/src/spec/mod.rs`, lines 2965-2973),
`atomic_cas`, the pointer width, and integer ABI alignments from the data
layout (defaults in `compiler/rustc_abi/src/lib.rs`, lines 302-306: `i64` and
`i128` default to 32-bit alignment unless the layout string overrides them).
Neither `-C target-feature` nor the enabled feature set is read.

Three independent facts are encoded per width `w`:

| cfg | meaning | condition |
| --- | --- | --- |
| `target_has_atomic_load_store = "w"` | atomic load and store exist | `w` in the target's range |
| `target_has_atomic = "w"` | compare-and-swap also exists | additionally `atomic_cas` |
| `target_has_atomic_primitive_alignment = "w"` | `AtomicUw` and `uw` have equal alignment | additionally data-layout alignment of the `w`-bit integer is `w` bits |

The feature gate that stabilised the third cfg in 1.97.0 is still named
`cfg_target_has_atomic_equal_alignment`
(`compiler/rustc_feature/src/accepted.rs`, line 112).

#### 3.2 Observed matrix (`rustc --print cfg`, R98, nightly)

Widths are listed in ascending order; `p` is `"ptr"`.

| Target and options | `target_has_atomic` | `..._load_store` | `..._primitive_alignment` | bare `target_has_atomic` | `target_feature="cmpxchg16b"` |
| --- | --- | --- | --- | --- | --- |
| `x86_64-unknown-linux-gnu` | 8 16 32 64 p | 8 16 32 64 p | 8 16 32 64 p | yes | no |
| same, `-C target-cpu=x86-64-v3` | 8 16 32 64 p | 8 16 32 64 p | 8 16 32 64 p | yes | **yes** |
| same, `-C target-feature=+cmpxchg16b` | 8 16 32 64 p | 8 16 32 64 p | 8 16 32 64 p | yes | **yes** |
| `x86_64-apple-darwin` | 8 16 32 64 128 p | 8 16 32 64 128 p | 8 16 32 64 128 p | yes | yes |
| `x86_64-pc-windows-msvc` | 8 16 32 64 128 p | 8 16 32 64 128 p | 8 16 32 64 128 p | yes | yes |
| `aarch64-unknown-linux-gnu` | 8 16 32 64 128 p | 8 16 32 64 128 p | 8 16 32 64 128 p | yes | no |
| `i686-unknown-linux-gnu` | 8 16 32 64 p | 8 16 32 64 p | 8 16 32 p | yes | no |
| `m68k-unknown-linux-gnu` | 8 16 32 p | 8 16 32 p | 8 16 | yes | no |
| `s390x-unknown-linux-gnu` | 8 16 32 64 128 p | 8 16 32 64 128 p | 8 16 32 64 p | yes | no |
| `thumbv6m-none-eabi` | *(none)* | 8 16 32 p | 8 16 32 p | no | no |
| `riscv32imc-unknown-none-elf` | *(none)* | 8 16 32 p | 8 16 32 p | no | no |
| `bpfel-unknown-none` (also with `-C target-cpu=v4`) | *(none)* | 64 p | 64 p | no | no |

The specification values behind the rows (R98,
`compiler/rustc_target/src/spec/targets/`): `x86_64_unknown_linux_gnu.rs`
lines 7-9 `base.cpu = "x86-64"`, `base.max_atomic_width = Some(64)`;
`x86_64_apple_darwin.rs` line 20 `max_atomic_width: Some(128), // penryn+
supports cmpxchg16b`; `x86_64_pc_windows_msvc.rs` lines 6-8
`base.features = "+cmpxchg16b,+sse3,+lahfsahf"`,
`base.max_atomic_width = Some(128)`; `i686_unknown_linux_gnu.rs` lines 20-21
`base.cpu = "pentium4"`, `base.max_atomic_width = Some(64)`, with a data
layout that does not override `i64`; `thumbv6m_none_eabi.rs` lines 25-28
`features: "+strict-align,+atomics-32"`, `atomic_cas: false`;
`riscv32imc_unknown_none_elf.rs` lines 23-25 `max_atomic_width: Some(32)`,
`atomic_cas: false`, `features: "+m,+c,+forced-atomics"`.

Readings:

- **`i686`**: `target_has_atomic="64"` without
  `target_has_atomic_primitive_alignment="64"`, because `u64` is 4-byte
  aligned while `AtomicU64` is 8-byte aligned. Code that reinterprets
  `&mut u64` as `&AtomicU64` must test the alignment cfg, not the
  compare-and-swap cfg (Lean:
  `ce2_i686_atomic64_has_cas_without_primitive_align`).
- **`m68k`**: the same gap at *pointer width* (32-bit integers and pointers
  are 2-byte aligned); **`s390x`**: the same gap at 128 bits.
- **`thumbv6m`, `riscv32imc`**: load/store without compare-and-swap; bare
  `target_has_atomic` is absent while bare `target_has_atomic_load_store` is
  present.
- **`x86_64-unknown-linux-gnu`**: enabling `cmpxchg16b` through the CPU or the
  feature flag changes `target_feature` but not the atomic cfgs (Lean:
  `ce3_x86_64_linux_cx16_still_lacks_atomic128_due_to_static_target_max`).

Basis: source + execution.

#### 3.3 Census over all builtin targets (R98)

`rustc --print cfg --target <t>` succeeded for all 322 targets printed by
`rustc --print target-list`.

| Property | Count | Targets |
| --- | --- | --- |
| `target_has_atomic="128"` | 68 | 53 `aarch64*`/`arm64*` targets; `s390x-unknown-linux-gnu`, `-musl`, `s390x-unknown-none-softfloat`; `x86_64-apple-darwin`, `-ios`, `-ios-macabi`, `-tvos`, `-watchos-sim`; `x86_64h-apple-darwin`; `x86_64-pc-windows-gnu`, `-gnullvm`, `-msvc`; `x86_64-uwp-windows-gnu`, `-msvc`; `x86_64-unknown-fuchsia` |
| compare-and-swap at 64 without primitive alignment at 64 | 18 | `armv7s-apple-ios`, `i386-apple-ios`, the four `i586-*` targets, and twelve `i686-*` targets |
| ... at 32 and at `ptr` | 2 | `m68k-unknown-linux-gnu`, `m68k-unknown-none-elf` |
| ... at 128 | 3 | the three `s390x` targets |
| load/store but no compare-and-swap | 12 | `avr-none`, `bpfeb-unknown-none`, `bpfel-unknown-none`, `riscv32e`/`em`/`emc`/`i`/`im`/`imc-unknown-none-elf`, `riscv64im-unknown-none-elf`, `thumbv6m-none-eabi`, `xtensa-esp32s2-none-elf` |
| no atomic cfg at all | 6 | `armv4t-none-eabi`, `armv5te-none-eabi`, `thumbv4t-none-eabi`, `thumbv5te-none-eabi`, `mipsel-sony-psx`, `msp430-none-elf` |

For every target the compare-and-swap set and the primitive-alignment set are
subsets of the load/store set, as the loop implies. No `x86_64-*-linux-*`
target is in the first row.

Basis: execution; full lists are in `support/probe_results.json`.

#### 3.4 Since a commit of 2026-11-09: widths may depend on the CPU name

R102 replaces the two accessor calls
(`compiler/rustc_session/src/config/cfg.rs`, lines 272-275 and 283):

```rust
let (min_atomic_width, max_atomic_width) = {
    let cpu = sess.opts.cg.target_cpu.as_deref().unwrap_or(sess.target.cpu.as_ref());
    sess.target.atomic_widths(cpu)
};
```

with, in `compiler/rustc_target/src/spec/mod.rs` (lines 2885-2890):

```rust
pub fn atomic_widths(&self, cpu: &str) -> (u64, u64) {
    self.per_cpu_atomic_widths.get(cpu).copied().unwrap_or((
        self.min_atomic_width.unwrap_or(8),
        self.max_atomic_width.unwrap_or_else(|| self.pointer_width.into()),
    ))
}
```

(commit `78fda199166913f9c3e34c0fb1ec27f511f82f42`, "BPF: Define max/min
atomic width per CPU version"). The table is keyed by the CPU *name* string.
`compiler/rustc_target/src/spec/base/bpf.rs` at R102 sets
`min_atomic_width: Some(8)`, `max_atomic_width: Some(64)` and maps the names
`v1`, `v2`, `v3`, `generic` to `(8, 0)`, an empty range; at R98 the BPF base
has the static `min = max = 64` seen in the last matrix row.

For `x86_64-unknown-linux-gnu` the R102 target file still sets
`base.max_atomic_width = Some(64)` and no table (its only differences from
R98 are unrelated: one removed and one added boolean option), so every `-C
target-cpu` falls through to the static range. The prior observation on R102
records `target_feature="cmpxchg16b"` together with widths 8-64 only for
`-C target-cpu=x86-64-v3`, in agreement.

"Static" therefore needs qualifying: at R98 the range is a function of the
target specification alone; at R102 it is a function of the specification and
the CPU name; at neither revision is it a function of the enabled target
features. The Lean model carries the table (`atomicWidths`, `lookupCpu`) and
proves both directions: `ce3_...` quantifies over every CPU choice and both
settings of the feature bit for a target with an empty table, and
`per_cpu_table_changes_atomic_cfgs` shows that a BPF-like table changes the
result with the CPU name. `atomicCfgs_ignores_target_features` holds by
construction of the model (the definition never reads the feature bit); it
records the source fact rather than adding evidence for it.

Basis: source (R98, R102) + derived; R102 execution only via the prior
observation.

#### 3.5 Nightly-only entries

The bare `target_has_atomic` and `target_has_atomic_load_store` entries are
inserted only `if sess.is_nightly_build()`. With `RUSTC_BOOTSTRAP=-1` the
host's `--print cfg` loses, relative to the nightly output: bare
`target_has_atomic`, every `target_has_atomic_load_store` line, `ub_checks`,
`overflow_checks`, `relocation_model="pic"`, `fmt_debug="full"`,
`target_thread_local`, `target_object_format="elf"`,
`target_has_reliable_f16`, `target_has_reliable_f16_math`,
`target_has_reliable_f128`, `emscripten_wasm_eh` and `target_feature="x87"`;
nothing is gained. Some of these are not inserted at all on a non-nightly
build and some are inserted but hidden by `--print cfg` because their cfg is
feature-gated; the probe does not separate the two causes.

Of the cfg *names*, only `target_has_atomic_load_store` is in the gated-cfg
table (`compiler/rustc_feature/src/builtin_attrs.rs`, lines 18-58, feature
`cfg_target_has_atomic`); the name `target_has_atomic` is not, so the bare
predicate `#[cfg(target_has_atomic)]` is accepted without a feature gate,
is false on non-nightly builds, and can be made true by the ungated
`--cfg target_has_atomic` of section 2.2.

Basis: source + execution.

#### 3.6 Model validation

For `i686-unknown-linux-gnu`, `x86_64-unknown-linux-gnu`,
`thumbv6m-none-eabi` and `m68k-unknown-linux-gnu`, the Lean theorems
`*_model_matches_print_cfg` state that the model's output equals, as a set,
the complete list of atomic cfg lines transcribed from the matrix above. They
are proved by kernel evaluation (`decide`), so a transcription error in either
direction would make the file fail to check.

Basis: derived (Lean) against execution.

### 4. `cfg_select!`, `cfg(target(..))`, `cfg(version(..))`, `#[cfg_accessible(..)]`

Feature status, identical at R98, R102 and Rmain (line numbers for R98):

| Construct | Status | Source |
| --- | --- | --- |
| `core::cfg_select!` | stable since 1.95.0 | `compiler/rustc_feature/src/accepted.rs` line 106 `(accepted, cfg_select, "1.95.0", ...)`; `library/core/src/macros/mod.rs` lines 231-235 `#[stable(feature = "cfg_select", since = "1.95.0")] pub macro cfg_select` |
| `cfg(target(os = "..", arch = ".."))` | unstable, feature `cfg_target_compact` | `compiler/rustc_feature/src/unstable.rs` line 444 |
| `cfg(version(".."))` | unstable, feature `cfg_version` | `unstable.rs` line 454; gated-cfg table `builtin_attrs.rs` line 30 |
| `#[cfg_accessible(path)]` | unstable library feature `cfg_accessible`, "`cfg_accessible` is not fully implemented" | `library/core/src/macros/mod.rs` lines 1865-1874 |

Only the first of the four is stable; the other three were unstable at every
examined revision.

Semantics (`compiler/rustc_attr_parsing/src/attributes/cfg.rs`):

- `target(k = "v", ...)` is rewritten to the conjunction of `target_k = "v"`
  predicates (lines 158-192, `Symbol::intern(&format!("target_{name}"))`),
  each of which goes through the ordinary name/value path, including the
  `unexpected_cfgs` check.
- `version("x.y")` is true iff `RustcVersion::current_overridable() >= x.y`
  (strictly greater under `-Z assume-incomplete-release`); an unparsable
  literal yields a warning and evaluates to `false` (lines 126-156, 279-297).
- A plain `name` / `name = "v"` predicate is true iff the pair is in the
  crate configuration (lines 272-278).

Observed (R98, with the three feature gates): `cfg_select!` picked the
64-bit arm; with two `true` arms the first won and the compiler warned
`unreachable configuration predicate`; `cfg!(target(os = "linux", arch =
"x86_64"))` was `true` and the `aarch64` variant `false`;
`cfg!(version("1.90"))` was `true`, `cfg!(version("1.250"))` `false`, and
`cfg!(version("not.a.version"))` `false` with the warning `unknown version
literal format, assuming it refers to a future version`; an item under
`#[cfg_accessible(core::mem::size_of)]` was kept and a `compile_error!` under
`#[cfg_accessible(core::mem::no_such_item_zzz)]` was removed.

Without the gates the same file fails with `E0658` three times for
`` `cfg(version)` is experimental and subject to change ``, twice for
``compact `cfg(target(..))` is experimental and subject to change`` and twice
for the `cfg_accessible` library feature. `cfg_select!` alone needs no gate,
also under `RUSTC_BOOTSTRAP=-1`, and a `cfg_select!` arm naming an unknown cfg
is reported by `unexpected_cfgs` under `--check-cfg 'cfg()'`.

The gating policy is the opposite of the diagnostic namespace (section 5.1):
an ungated cfg predicate is a hard error; an ungated diagnostic attribute is
a warning.

Basis: source (R98, R102, Rmain) + execution (R98).

### 5. `#[diagnostic::*]`

#### 5.1 Forward compatibility is "warn by default", nothing stronger

Normative: RFC 3368 ("The `#[diagnostic]` attribute namespace",
`text/3368-diagnostic-attribute-namespace.md`) says that applying such an
attribute "should never cause a compilation error as long as they are
syntactically valid", that the compiler "must not [...] Emit an hard error on
malformed attribute" and "should [...] implement a warn-by-default lint for
unrecognised attributes or options". The Reference rule
`attributes.diagnostic.namespace.unknown-invalid-syntax` restates it:
"Unknown attributes in this namespace are accepted, though they may emit
warnings for unused attributes."

Source: `diagnostic` is a predefined tool namespace
(`compiler/rustc_resolve/src/macros.rs`, lines 150-154). Four lints, all
declared `Warn` (`compiler/rustc_lint_defs/src/builtin.rs`, lines 4447, 4472,
4497, 4522) and grouped as `unknown_or_malformed_diagnostic_attributes`
(`compiler/rustc_lint/src/lib.rs`, lines 354-360), cover the namespace:
`unknown_diagnostic_attributes`, `malformed_diagnostic_attributes`,
`misplaced_diagnostic_attributes`, `malformed_diagnostic_format_literals`.
At R98 the unknown-attribute lint is emitted by the resolver from a table of
known attributes with optional feature gates (`macros.rs`, lines 716-731:
`on_unimplemented` and `do_not_recommend` ungated; `on_move`, `on_const`,
`on_unknown`, `on_unmatch_args` gated), and a gated attribute's parser simply
returns when its feature is off. At R102 the same policy lives in the
attribute parser as the macro `gate_diagnostic_attr`
(`compiler/rustc_attr_parsing/src/attributes/diagnostic/mod.rs`, lines 80-97),
which emits `UNKNOWN_DIAGNOSTIC_ATTRIBUTES` and returns; the table there
(lines 44-55) lists eight attributes, adding `on_type_error` and `opaque` and
renaming `on_unmatch_args` to `on_unmatched_args`. The accepted features are
`diagnostic_namespace` (1.78.0) and `do_not_recommend` (1.85.0)
(`accepted.rs`, lines 186 and 188).

Observed (R98) for one crate containing an unknown attribute
(`#[diagnostic::future_attr(..)]`), an ungated `#[diagnostic::on_move(..)]`,
an unknown option, `#[diagnostic::do_not_recommend(with_args)]` and a
`do_not_recommend` on a function:

| Invocation | exit | diagnostics |
| --- | --- | --- |
| default | 0 | 5 warnings: 2 × `unknown diagnostic attribute` (the `on_move` one with help ``add `#![feature(diagnostic_on_move)]` to the crate attributes to enable``), ``malformed `diagnostic::on_unimplemented` attribute``, `` `#[diagnostic::do_not_recommend]` does not expect any arguments``, `` `#[diagnostic::do_not_recommend]` can only be placed on trait implementations``; no error code |
| `RUSTC_BOOTSTRAP=-1` | 0 | the same 5 warnings, without the feature help |
| `-D warnings` | 1 | the same 5 diagnostics as errors |
| `-A unknown_or_malformed_diagnostic_attributes` | 0 | none |

So an attribute introduced by a newer compiler never produces `E0658` on an
older one, but a crate built with `-D warnings` (or with the lint group
denied) does fail to compile on a compiler that does not know the attribute.
The guarantee is a default lint level, not an unconditional property.

Basis: normative + documentation + source + execution.

#### 5.2 Stacked attributes: a first-wins × append monoid

R98, `compiler/rustc_attr_parsing/src/attributes/diagnostic/mod.rs`,
lines 114-152:

```rust
fn merge_directives(cx: &mut AcceptContext<'_, '_>,
                    first: &mut Option<(Span, Directive)>, later: (Span, Directive)) {
    if let Some((_, first)) = first {
        if first.is_rustc_attr || later.1.is_rustc_attr { cx.emit_err(DupesNotAllowed); }
        merge(cx, &mut first.message, later.1.message, sym::message);
        merge(cx, &mut first.label, later.1.label, sym::label);
        first.notes.extend(later.1.notes);
    } else {
        *first = Some(later);
    }
}
fn merge<T>(cx: &mut AcceptContext<'_, '_>, first: &mut Option<(Span, T)>,
            later: Option<(Span, T)>, option_name: Symbol) {
    match (first, later) {
        (Some(_) | None, None) => {}
        (Some((first_span, _)), Some((later_span, _))) => { /* lint MALFORMED_DIAGNOSTIC_ATTRIBUTES:
            "`message` is ignored due to previous definition of `message`" */ }
        (first @ None, Some(later)) => { first.get_or_insert(later); }
    }
}
```

The helper is first-wins, i.e. `Option::or` written out with a lint on the
losing side; the code does not literally call `Option::or`. R102 (lines
192-231) and Rmain (identical to R102) extend the same shape to every field:
`first.is_rustc_attr |= is_rustc_attr; first.filters.extend(filters);`,
first-wins on `message`, `label` and `parent_label`, and
`first.notes.extend(notes)`; stacking `#[rustc_on_unimplemented]` is then
merged instead of rejected.

Within one attribute the parser applies the same rule: a second `message` or
`label` triggers the "ignored" lint, every `note` is pushed (R98 lines
299-318).

The Reference states both halves:
`attributes.diagnostic.on_unimplemented.note-repetition` ("The `note` option
can appear several times, which results in several note messages being
emitted.") and `attributes.diagnostic.on_unimplemented.repetition` ("If any of
the other options appears several times the first occurrence of the relevant
option specifies the actually used value. Subsequent occurrences generates a
warning."). **RFC 3368 disagrees on `note`**: "Multiple attributes are
evaluated in order. The first matching instance for each of the
`message`/`label`/`note` options is emitted." The implementation and the
Reference accumulate notes; the RFC text describes first-wins for all three.

Observed (R98), structured JSON diagnostics of the resulting `E0277`:

| Attributes in source order | message | primary label | custom notes, in order |
| --- | --- | --- | --- |
| A = (`FIRST_MSG`, `FIRST_LBL`, `NOTE_ONE`), B = (`SECOND_MSG`, `SECOND_LBL`, `NOTE_TWO`) | ``FIRST_MSG for `u8` `` | `FIRST_LBL` | `NOTE_ONE`, `NOTE_TWO` |
| B, A | `SECOND_MSG` | `SECOND_LBL` | `NOTE_TWO`, `NOTE_ONE` |
| A, B, C = (note `NOTE_THREE`) | ``FIRST_MSG for `u8` `` | `FIRST_LBL` | `NOTE_ONE`, `NOTE_TWO`, `NOTE_THREE` |
| C, A, B | ``FIRST_MSG for `u8` `` | `FIRST_LBL` | `NOTE_THREE`, `NOTE_ONE`, `NOTE_TWO` |
| (note `SAME_NOTE`), (note `SAME_NOTE`) | default | default | `SAME_NOTE`, `SAME_NOTE` |
| (note `N0`), (label `LATER_LBL`), (message `LATER_MSG`) | `LATER_MSG` | `LATER_LBL` | `N0` |
| one attribute: `note = "N1", note = "N2", message = "M_A", message = "M_B"` | `M_A` | default | `N1`, `N2` |
| (`bogus = "x"`), A | ``FIRST_MSG for `u8` `` | `FIRST_LBL` | `NOTE_ONE` |

Whenever a later `message` or `label` lost, the compiler also emitted the
"is ignored due to previous definition" warning. The fifth row shows that the
operation is not idempotent; the first two that it is not commutative; the
last that an attribute with only malformed options contributes the identity.

Lean (`Directive` with all six R102 fields; the R98 behaviour is the
projection to three of them):

- **`directiveMerge_assoc`**: `(a.merge b).merge c = a.merge (b.merge c)`.
- `directiveMerge_empty_left`, `directiveMerge_empty_right`: the default
  directive is a two-sided identity.
- **`ce_directiveMerge_noncomm`**: two directives whose merges differ in the
  winning message and in the note order.
- `ce_directiveMerge_not_idempotent`: a directive `a` with `a.merge a ≠ a`.
- `foldl_mergeInto`: the parser's `Option` accumulator started at `None`
  computes the monoid fold over a non-empty stack.
- `mergeAll_spec`: a stack denotes the first present `message`, the first
  present `label`, and all notes in source order.

Basis: source (R98, R102, Rmain) + documentation + normative (with the
recorded disagreement) + execution (R98) + derived (Lean).

#### 5.3 Evaluation uses the same operation

R98, `compiler/rustc_hir/src/attrs/diagnostic.rs`, lines 53-107 (at R102 the
type moved to `compiler/rustc_attr_ir/src/diagnostic.rs`, lines 52-106):

```rust
pub fn eval(&self, filter_options: Option<&FilterOptions>, args: &FormatArgs) -> CustomDiagnostic {
    let mut ret = CustomDiagnostic::default();
    if let Some(filter_options) = filter_options {
        for (filter, directive) in &self.filters {
            if filter.matches_predicate(filter_options) { ret.update(directive, args); }
        }
    } ...
    ret.update(self, args);
    ret
}
fn update(&mut self, di: &Directive, args: &FormatArgs) {
    if self.message.is_none() { self.message = di.message.as_ref().map(|m| m.1.format(args)); }
    if self.label.is_none() { self.label = di.label.as_ref().map(|l| l.1.format(args)); }
    if self.parent_label.is_none() { self.parent_label = di.parent_label.as_ref().map(|p| p.format(args)); }
    self.notes.extend(di.notes.iter().map(|n| n.format(args)))
}
```

Matching `on(..)` filters (only `#[rustc_on_unimplemented]` has them) are
applied in order before the root directive, each by the same first-wins /
append rule. The Lean theorem `eval_sequence_eq_render_mergeAll` states that
folding `update` over a list of directives from the empty diagnostic equals
formatting their merge, for any formatting function; the step lemma is
`update_render_eq_render_merge`. Parsing-time merging and evaluation-time
updating are thus one monoid and its homomorphic image.

Basis: source + derived (Lean).

#### 5.4 `on_unimplemented` on a trait alias is ignored

R98, `attributes/diagnostic/on_unimplemented.rs`, lines 19-26: the parser
emits `MISPLACED_DIAGNOSTIC_ATTRIBUTES` and returns unless the attribute's
target is `Target::Trait`; a trait alias is a different target, so no
directive is stored. Observed (R98, with `#![feature(trait_alias)]`): one
warning `` `#[diagnostic::on_unimplemented]` can only be applied to trait
definitions`` and an `E0277` whose message is the default ``the trait bound
`u8: MyAlias` is not satisfied`` with none of the custom text. The prior
observation on R102 quotes a differently worded warning (``the
`diagnostic::on_unimplemented` attribute cannot be used on trait aliases``)
and the same default error line. A check that searches the whole diagnostic
stream for the custom string will find it, because the warning echoes the
attribute's source line; only the `E0277` record itself is conclusive.

Basis: source + execution (R98); prior observation (R102).

#### 5.5 `do_not_recommend` hoists the reported predicate

Current solver, `compiler/rustc_trait_selection/src/error_reporting/traits/fulfillment_errors.rs`,
lines 829-861 (R98; R102 and Rmain differ in one span-context comparison only):

```rust
let mut base_cause = obligation.cause.code().clone();
let mut applied_do_not_recommend = false;
loop {
    if let ObligationCauseCode::ImplDerived(ref c) = base_cause {
        if self.tcx.do_not_recommend_impl(c.impl_or_alias_def_id) {
            let code = (*c.derived.parent_code).clone();
            ...
            obligation.cause.map_code(|_| code);
            obligation.predicate = c.derived.parent_trait_pred.upcast(self.tcx);
            applied_do_not_recommend = true;
        }
    }
    if let Some(parent_cause) = base_cause.parent() { base_cause = parent_cause.clone(); } else { break; }
}
```

The loop walks the derived-cause chain from the failing leaf towards the
root. At each `ImplDerived` link whose impl carries the attribute it
overwrites the reported obligation with that impl's *parent* predicate and
parent cause. Later overwrites win, so the result is the parent of the marked
link closest to the root. It is called for unimplemented-trait and projection
errors (`error_reporting/traits/mod.rs`, lines 297-305).

Next-generation solver, `compiler/rustc_trait_selection/src/solve/fulfill/derive_errors.rs`,
lines 450-459: while descending from the root goal through goals that have a
single candidate,

```rust
// Don't walk into impls that have `do_not_recommend`.
if let inspect::ProbeKind::TraitCandidate { source: CandidateSource::Impl(impl_def_id), result: _ } = candidate.kind()
    && tcx.do_not_recommend_impl(impl_def_id)
{
    return ControlFlow::Break(self.obligation.clone());
}
```

i.e. it stops at the first marked impl met from the root and reports the goal
that impl was a candidate for.

Observed (R98) for `impl<T: A> B for T` (inner) and `impl<T: B> C for T`
(outer), calling a function that requires `u8: C`; results are identical with
and without `-Z next-solver`:

| attribute on inner | on outer | primary label | "required for" notes |
| --- | --- | --- | --- |
| no | no | ``the trait `A` is not implemented for `u8` `` | `` `u8` to implement `B` ``, `` `u8` to implement `C` `` |
| yes | no | ``the trait `B` is not implemented for `u8` `` | `` `u8` to implement `C` `` |
| no | yes | ``the trait `C` is not implemented for `u8` `` | none |
| yes | yes | ``the trait `C` is not implemented for `u8` `` | none |

The top line of the error is ``the trait bound `u8: C` is not satisfied`` in
all four cases: the attribute changes which predicate is explained and how
much of the chain is shown, not which obligation failed.

Lean, over an abstract linear chain of causes:

- `report_eq`: the loop's result is the parent of the marked link closest to
  the root, or the original obligation if none is marked.
- `report_chain_dnrFree`: the reported cause chain contains no marked impl.
- `report_idempotent`: running the loop on its own output changes nothing.
- **`report_pred_eq_topDown`**: the predicate selected by the bottom-up
  overwrite loop equals the one selected by the top-down first-hit walk.
- `probe_chain_reports`: on the two-impl chain the four placements yield
  `A`, `B`, `C`, `C` with remaining chains of length 2, 1, 0, 0, matching
  the table.

The attribute also filters impl candidates out of "other types implement"
style suggestions (`fulfillment_errors.rs`, lines 2063-2064 and 2457).

Basis: source + execution (R98, both solvers) + derived (Lean).

#### 5.6 `on_move`: placeholders and their renaming

`#[diagnostic::on_move]` is unstable (feature `diagnostic_on_move`,
`unstable.rs` line 514) and applies to structs, enums and unions. The borrow
checker evaluates it for a use-after-move error (`E0382`),
`compiler/rustc_borrowck/src/diagnostics/conflict_errors.rs`, lines 143-165
(R98; the same code at R102 lines 146-168):

```rust
let this = self.infcx.tcx.item_name(item_def.did()).to_string();
let mut generic_args: Vec<_> = self.infcx.tcx.generics_of(item_def.did()).own_params.iter()
    .filter_map(|param| Some((param.name, args[param.index as usize].to_string())))
    .collect();
generic_args.push((kw::SelfUpper, this.clone()));
let args = FormatArgs { this, generic_args, .. };
let CustomDiagnostic { message, label, notes, parent_label: _ } = directive.eval(None, &args);
```

`{Self}` is bound to the item's bare name, not to the instantiated type; a
generic parameter placeholder is bound to the actual argument.

Observed (R98, feature enabled) for `struct LinearToken<G>` moved twice at
type `LinearToken<u32>` with message
``MOVE_MSG Self=`{Self}` This=`{This}` this=`{this}` G=`{G}` Bad=`{BadArg}` ``:

- `E0382` message: ``MOVE_MSG Self=`LinearToken` This=`LinearToken`
  this=`{this}` G=`u32` Bad=`{BadArg}` ``;
- two warnings `` unknown parameter `this` `` and `` unknown parameter
  `BadArg` `` (lint `malformed_diagnostic_format_literals`), unknown
  placeholders being printed verbatim;
- the custom label is attached as a secondary label next to `value moved
  here`; both notes appear in order.

Without the feature: one `unknown diagnostic attribute` warning with the
feature help, the default message ``use of moved value: `tok` ``, and no
`E0658`.

Placeholder spelling by revision
(`attributes/diagnostic/mod.rs`, the arm that maps the item placeholder to
`FormatArg::This`):

| Revision | date | accepted spelling |
| --- | --- | --- |
| R98 | 2026-05-31 | `{This}` (`sym::This`, line 442) |
| `ada41e1ce81819f01577c0ee40ccbd6fc41384e8` (on `main`) | 2026-09-11 | `{This}` |
| commit `8def69b4a70c099548c747bf83f5869ba3d4fb4b`, "convert non-generic diagnostic attribute placeholders to snake_case" | 2026-10-13 | changes `{This}` to `{this}` and `{ItemContext}` to `{item_context}` |
| R102 | 2026-11-11 | `{this}` (`sym::this`, line 547) |
| Rmain | 2026-11-22 | `{this}` |

The prior observation on R102 agrees: there `{This}` produced `` unknown
parameter `This` `` and was printed verbatim while `{Self}` printed
`LinearToken`. The direction of the change is uppercase first, lowercase
later. A source tree taken from a branch that forked from `main` in September
shows the uppercase spelling and, compared against a November compiler, looks
like a contradiction between help text and behaviour; it is only an older
tree (see Evidence for one such commit).

Basis: source (four revisions) + execution (R98); prior observation (R102).

### 6. What the Lean file establishes

`support/CheckCfgSemilatticeAndDiagnosticMerge.lean` (1,735 lines, 105
theorems) is checked by Lean v4.34.1 with warnings as errors. Its footer
prints the axioms of every one of the 105 theorems: 54 depend on `propext`
only and 51 on no axiom; none depends on choice, on an unproved placeholder,
or on compiler-evaluated reduction. The file contains no general-recursion escape
and no arithmetic decision procedure; concrete facts are proved by kernel
evaluation (`decide`) and general ones by structural induction and case
analysis.

| Part | Headline theorems | What a reader may rely on |
| --- | --- | --- |
| A | `join_assoc`, `join_comm`, `join_idem`, `join_any_left/right`, `join_bot_left/right`, `le_antisymm`; `mergeEntry_none/some`; `lint_parse`; `checkCfg_fold_perm_invariant`; `checkCfg_duplicate_spec`; `checkConfig_perm_invariant`; `ce_wellKnown_fill_shadows_bare_form` | The code shape quoted in 1.2, 1.3 and 1.5 is order-independent and is a join except for the bare well-known case |
| B | `coherentSession_iff_no_spoofed_builtin_cfg`; `disallow_empty_implies_coherent`; `accepted_at_deny_implies_coherent`; `ce1_spoofed_cli_ub_checks_diverges_from_codegen`; `gate_strictly_conservative`; `ce_gate_gap_bare_target_has_atomic`; `immediate_abort_sets_both_panic_cfgs`; `kernel_sanitizers_fold` | The gate is sound for the pairs it matches when it runs at an error level, and neither complete nor unconditional |
| C | four `*_model_matches_print_cfg`; `ce2_i686_atomic64_has_cas_without_primitive_align`; `ce3_x86_64_linux_cx16_still_lacks_atomic128_due_to_static_target_max`; `per_cpu_table_changes_atomic_cfgs`; `bare_entries_are_nightly_only` | The loop of 3.1, fed with specification values, reproduces the observed cfg lists; the three named properties follow |
| D | `directiveMerge_assoc`; `directiveMerge_empty_left/right`; `ce_directiveMerge_noncomm`; `foldl_mergeInto`; `mergeAll_spec`; `eval_sequence_eq_render_mergeAll`; `report_eq`; `report_chain_dnrFree`; `report_idempotent`; `report_pred_eq_topDown` | Stacking is a non-commutative monoid shared by parsing and evaluation; `do_not_recommend` pruning is idempotent, complete, and solver-independent on linear chains |

The model's correspondence to `rustc` is by inspection of the quoted source
and by the execution results; the Lean kernel checks the theorems, not that
correspondence.

## Boundaries

**Not examined**

- Cargo. Nothing here was run through Cargo; how Cargo passes `--check-cfg`,
  `--cfg` or `--cap-lints` to `rustc` is not established by this report beyond
  what the quoted compiler comments say.
- Stable or beta release binaries. Non-nightly behaviour was approximated
  with `RUSTC_BOOTSTRAP=-1` on a nightly compiler.
- Execution on R98a, R102 and Rmain. R98a is covered by source identity with
  one stated exception; R102 by source and a prior, unreproduced observation;
  Rmain by source for the functions named in the Applicability table.
- Custom target specification files, `-Z has-thread-local`, and `cfg` values
  contributed after `build_configuration` (target features, `crt-static`).
- `#[diagnostic::on_const]`, `on_unknown`, `on_unmatch_args` /
  `on_unmatched_args`, `on_type_error`, `opaque`; `#[rustc_on_unimplemented]`
  filters; cross-crate use of any diagnostic attribute.
- `do_not_recommend` on branching proof trees, with several candidates, for
  projection goals, or for host-effect predicates. The model and the probe
  cover a linear chain of two blanket impls.
- Which targets other than BPF populate the per-CPU atomic width table at
  R102 or Rmain.
- Anneal beyond the four files cited in 2.6; in particular whether any
  caller of `compareReferenceInputs` exists and what the producer exports as
  `rustc_args`.

**Unknown**

- For each cfg hidden by `--print cfg` under `RUSTC_BOOTSTRAP=-1`, whether it
  is absent from the session or merely not printed (3.5).
- Whether the merge of the R98a-to-R98 hunk in `fulfillment_errors.rs`
  changes any diagnostic for user-defined traits; by reading, it applies only
  when a `#[derive]` suggestion is available, which was not tested.

**Known not to apply**

- "The builtin-cfg gate makes cfg and flags coherent" does not hold as an
  unconditional statement: it fails under `-A`, `-W`, `--cap-lints
  allow|warn`, and an in-source `#![allow]` (2.3), and for unmatched shapes
  (2.2).
- "`fill_well_known` is the join with the well-known table" does not hold
  for bare names (1.5).
- "`-C target-cpu=x86-64-v3` enables 128-bit atomics on
  `x86_64-unknown-linux-gnu`" does not hold at R98 (execution) nor, by
  source, at R102.
- "`cfg(target(..))`, `cfg(version(..))` and `#[cfg_accessible]` are stable"
  does not hold at any examined revision.
- "`{This}` replaced `{Self}`/`{this}`" has the direction backwards: `{This}`
  is the older spelling (5.6).
- RFC 3399 is not the diagnostic namespace RFC; it is
  `text/3399-cfg-attribute-in-where.md`.
- The order-independence theorem does not extend to
  `#[diagnostic::on_unimplemented]` stacking, which is order-dependent by
  design.

**Unsupported**

- `-C panic=immediate-abort` without `-Z unstable-options` on a nightly
  compiler is rejected by the compiler itself.
- `-Z sanitizer=kernel-address` on `x86_64-unknown-linux-gnu` is rejected
  ("not supported for this target"), although `--print cfg` prints the cfg
  line before the error.

**Stronger conclusions the evidence does not support**

- That an accepted compilation implies coherent builtin cfgs.
- That the Lean theorems hold of `rustc`; they hold of the model, and the
  model was compared with `rustc` on the cases listed.
- That the R102 behaviour was observed; except where a prior observation is
  cited, R102 statements are source readings.

## Evidence

### Revisions

All revisions were resolved on 2026-11-22 through the GitHub REST API
(`GET /repos/{owner}/{repo}/commits/{ref}`, `.../compare/{base}...{head}`,
`.../commits?sha=&path=&since=`); the responses are summarised in
`support/resolved_revisions.json`.

| Repository | Revision | Commit date (UTC) | Note |
| --- | --- | --- | --- |
| `rust-lang/rust` | `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` | 2026-05-30T17:09:19Z | R98a |
| `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | 2026-05-31T20:13:59Z | R98; `rustc -vV` reports this hash |
| `rust-lang/rust` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | 2026-11-11T17:59:24Z | R102 |
| `rust-lang/rust` | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | 2026-11-22T00:04:39Z | Rmain |
| `rust-lang/rust` | `ada41e1ce81819f01577c0ee40ccbd6fc41384e8` | 2026-09-11T10:47:32Z | on `main`; used only for the placeholder spelling |
| `rust-lang/rust` | `8def69b4a70c099548c747bf83f5869ba3d4fb4b` | 2026-10-13T16:13:08Z | placeholder renaming |
| `rust-lang/rust` | `0166f5056a311d91cd38a8e3199a7ae8b84a05c4` | 2026-08-10T21:55:50Z | "Add rust_analyzer to check-cfg names" |
| `rust-lang/rust` | `78fda199166913f9c3e34c0fb1ec27f511f82f42` | 2026-11-09T16:29:34Z | "BPF: Define max/min atomic width per CPU version" |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | 2026-11-19T21:39:21Z | |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` | 2026-09-24T17:27:27Z | tag `v4.34.1` |
| `rust-lang/rfcs` | `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` | 2026-11-14T17:21:49Z | |
| `rust-lang/reference` | `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | 2026-11-17T20:49:56Z | |

Ancestry from the compare endpoint: R98a → R98 `ahead` by 69; R98 → R102
`ahead` by 18,861; R102 → Rmain `ahead` by 2,474.

A caution for anyone resolving hashes this way: the commits endpoint of a
repository also resolves commits that exist only in its forks. Commit
`49d734536222bf28bb6d07d885b3a81d145981da` (2026-09-11, a one-file change to
`compiler/rustc_transmute/src/layout/tree.rs`) resolves under `rust-lang/rust`
but the compare endpoint reports it as `diverged` from R102: 3 commits ahead
of, and 7,061 behind, with merge base `ada41e1ce...`. It is not an ancestor of
any compiler discussed here, and its tree has the September state of the
diagnostic attribute code. The preserved prior observation names this commit
as the source tree it inspected, which explains the apparent placeholder
contradiction described in 5.6.

### Source files read

At R98 the compiler sources were read from the toolchain's own `rustc-src`
component and 38 of them were compared byte-for-byte with
`raw.githubusercontent.com/rust-lang/rust/14210df0e.../<path>` (no
difference). R98a, R102, Rmain and `ada41e1ce` were read from the same raw
endpoint. Files, all under `compiler/` unless noted:

- `rustc_session/src/config/cfg.rs` (`ExpectedValues`, `disallow_cfgs`,
  `default_configuration`, `fill_well_known`), `rustc_session/src/config.rs`
  (`build_configuration`), `rustc_session/src/session.rs` (`ub_checks`,
  `overflow_checks`, `contract_checks`);
- `rustc_interface/src/interface.rs` (`parse_check_cfg`);
- `rustc_attr_parsing/src/check_cfg.rs` (rendering of the two diagnostics),
  `rustc_attr_parsing/src/attributes/cfg.rs` (predicate parsing, lint
  decision, evaluation);
- `rustc_attr_parsing/src/attributes/diagnostic/{mod,on_unimplemented,on_move,do_not_recommend}.rs`;
- `rustc_hir/src/attrs/diagnostic.rs` (R98) and
  `rustc_attr_ir/src/diagnostic.rs` (R102, Rmain) (`Directive`,
  `CustomDiagnostic`);
- `rustc_trait_selection/src/error_reporting/traits/{on_unimplemented,fulfillment_errors,mod}.rs`,
  `rustc_trait_selection/src/solve/fulfill/derive_errors.rs`;
- `rustc_borrowck/src/diagnostics/conflict_errors.rs`;
- `rustc_middle/src/mir/syntax.rs` (`RuntimeChecks::value`),
  `rustc_middle/src/traits/mod.rs` (`ObligationCauseCode::parent`),
  `rustc_middle/src/ty/context.rs` (`do_not_recommend_impl`);
- `rustc_target/src/spec/mod.rs`, `rustc_target/src/spec/base/bpf.rs`, and
  the target files named in 3.2; `rustc_abi/src/lib.rs` (default alignments);
- `rustc_lint_defs/src/builtin.rs`, `rustc_lint/src/lib.rs`,
  `rustc_feature/src/{accepted,unstable,builtin_attrs}.rs`,
  `rustc_resolve/src/macros.rs`;
- `library/core/src/macros/mod.rs`; `src/doc/rustc/src/check-cfg.md`;
  `tests/ui/cfg/disallowed-cli-cfgs.rs`.

Anneal files were read with `git show c131b320...:<path>` from a clone:
`trusted/rustc-capture/src/driver.rs`,
`trusted/rustc-capture/tests/compiler_session.rs`,
`vendor/lean-miri/Miri/Input/ProducerEvidence.lean`,
`trusted/lean/Trusted/MirAst.lean`,
`trusted/correspondence/Trusted/Correspondence.lean`.

RFC and Reference text: `text/3368-diagnostic-attribute-namespace.md`,
`text/2397-do-not-recommend.md`, `text/3013-conditional-compilation-checking.md`,
`text/3399-cfg-attribute-in-where.md` at the `rust-lang/rfcs` revision above;
`src/attributes/diagnostics.md` at the `rust-lang/reference` revision above.

### Execution

Environment: `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, LLVM 22.1.6,
host `x86_64-unknown-linux-gnu`, Python 3 standard library, 2026-11-22.

```text
python3 support/probe_check_cfg_and_diagnostic_attrs.py
662 subprocess calls; 50/50 invariant checks hold        (exit status 0, about 33 s)
```

The probe writes every source file into a temporary directory, runs `rustc`
with `--error-format=json` and classifies diagnostics by error code, lint
name, primary-span line and child notes, never by searching rendered text. It
runs the binaries it builds for sections 2.3 and 4. Paths of the temporary
directory, the sysroot and the home directory are replaced by placeholders
before serialisation, and the script refuses to write a result that still
contains one of them.

```text
LEAN_SYSROOT=<lean-4.34.1 toolchain> lean -M2048 -DElab.async=false \
  -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/CheckCfgSemilatticeAndDiagnosticMerge.lean       (exit status 0, about 6 s)
```

Its standard output is preserved as `support/lean_axiom_audit_output.txt`.

### Preserved material

| File | Content |
| --- | --- |
| `support/probe_check_cfg_and_diagnostic_attrs.py` | the probe; `--rustc`, `--out`, `--skip-census` |
| `support/probe_results.json` | its output on R98: all cases, the 50 named checks, and seven version discriminators |
| `support/CheckCfgSemilatticeAndDiagnosticMerge.lean` | the model and proofs |
| `support/lean_axiom_audit_output.txt` | the 105 `#print axioms` lines, one per theorem |
| `support/resolved_revisions.json` | revisions, dates, titles and ancestry as returned by the API |
| `support/prior_observation_rustc_1_102_0_nightly_3ef0c22cd.json` | the earlier R102 record with its limitations stated in the file |

SHA-256 digests of these files are listed in `support/SHA256SUMS`.

## Revalidation

Cheapest first; each check says what it does and does not establish.

1. **Another toolchain, all four areas.** Run
   `python3 support/probe_check_cfg_and_diagnostic_attrs.py --rustc <path>
   --out probe_rerun.json` with a nightly `rustc`. Exit status 0 means the 50
   invariant checks hold on that compiler. Then compare the
   `version_discriminators` object: on a compiler at or after R102 the
   source reading (not an execution) predicts
   `rust_analyzer_is_well_known: true`,
   `on_move_uppercase_This_is_substituted: false`,
   `on_move_lowercase_this_is_substituted: true`,
   `host_prints_target_has_threads: true`,
   `host_nightly_prints_emscripten_wasm_eh: false`, and BPF load/store widths
   that differ between the default CPU and `-C target-cpu=v4`. A failing
   check names the finding to re-read. Passing establishes only the listed
   cases on that binary.
2. **Order independence after a refactor of `parse_check_cfg`.** Diff the
   `.and_modify(..).or_insert_with(..)` block against 1.2. If the three arms
   and two branches are unchanged, the Lean theorems still describe it; if
   not, update `mergeEntry` and re-run the Lean check. The probe's
   permutation and random differential cases catch a behavioural change
   without reading source.
3. **Well-known shadowing.** `rustc --check-cfg 'cfg(unix, values("x"))'` on
   a file containing `#[cfg(unix)] fn f() {}`: an `unexpected_cfgs` warning
   about value `(none)` means 1.5 still holds; silence means the fill became
   a union.
4. **Gate strength.** `rustc --cfg ub_checks -A explicit_builtin_cfgs_in_flags
   <any crate>`: exit status 0 means the gate is still a lint. If this starts
   to fail, the conditional statements in 2.3 and 2.4 can be strengthened. For
   new builtin cfgs, compare the arms of `disallow_cfgs` with the insertions
   of `default_configuration`; upstream keeps a list in
   `tests/ui/cfg/disallowed-cli-cfgs.rs`.
5. **Atomic cfgs for one target.** `rustc --print cfg --target <t> [-C
   target-cpu=<cpu>] | grep target_has_atomic`. For the per-CPU table, search
   the target specification directory for `per_cpu_atomic_widths`.
6. **Feature status.** Search `compiler/rustc_feature/src/accepted.rs` for
   `cfg_target_compact`, `cfg_version`, and
   `library/core/src/macros/mod.rs` for `feature = "cfg_accessible"`;
   presence in `accepted.rs` or a `#[stable]` attribute would retire the
   corresponding row of section 4.
7. **Directive merge.** Diff `merge_directives`, `merge` and
   `CustomDiagnostic::update` against 5.2 and 5.3. A change from "first
   wins" or from `extend` invalidates the monoid description; the probe's
   stacked cases detect it.
8. **Lean file.** Re-run the command under Evidence; exit status 0 with the
   same 105 lines (54 `[propext]`, 51 "does not depend on any axioms")
   re-establishes every theorem. A newer Lean may deprecate lemma names used
   in the proofs; that would be a maintenance failure, not a change in any
   finding.
9. **Hash provenance.** For any revision cited from another source, call the
   compare endpoint against a known nightly commit before trusting it as "the
   repository head"; `status: diverged` identifies a fork-only commit.

No cheap check exists for the Anneal reading in 2.6 other than re-reading the
five cited files at the revision of interest.
