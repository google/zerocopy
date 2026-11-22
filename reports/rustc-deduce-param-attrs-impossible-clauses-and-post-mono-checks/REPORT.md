# rustc `deduce_param_attrs`, `ImpossibleClauses`, and the post-monomorphization `abi_check` / `move_check`: source audit, differential execution on two nightlies, and a kernel-checked model

## Summary

Three rustc mechanisms sit between the MIR a verifier can read and the machine
code that runs. This report pins down what each one does, where, under which
flags, and what its soundness argument is.

**1. Deduced parameter attributes.** The query `deduced_param_attrs` walks a
function's *optimized* MIR once and records, per table index (index 0 is the
return place, indices 1.. are the arguments), a four-flag `UsageSummary`
(`DROP`, `SHARED_BORROW`, `MUTATE`, `CAPTURE`). When the ABI of a rustic-ABI
function instance is computed, every index whose pass mode is
`PassMode::Indirect` receives

- `readonly` iff `!MUTATE && !(DROP && needs_drop(T)) && !(SHARED_BORROW && !is_freeze(T))`,
- `captures(none)` iff `!CAPTURE && !(DROP && needs_drop(T))`,

where `T` is the **monomorphic** parameter type. The same generic function
therefore gets different attributes per instantiation.

The rules that carry the soundness burden:

- The return place is seeded with `MUTATE`, so it is never `readonly`; codegen
  unconditionally marks the `sret` pointer `writable`, and LLVM's verifier
  rejects `writable` together with `readonly`. (This is an IR well-formedness
  rule, not run-time undefined behaviour.)
- `&x` sets `SHARED_BORROW | CAPTURE`: `readonly` survives exactly when the
  type is `Freeze`, `captures(none)` never does.
- `&raw const x` sets `MUTATE | CAPTURE`.
- A whole-local `Drop` sets only `DROP`, resolved by `needs_drop` after
  monomorphization; a `Drop` of a projection sets `MUTATE | CAPTURE`.
- A call argument `Operand::Move(x)` sets `MUTATE | CAPTURE` on `x`, because
  codegen passes the caller's own slot pointer to the callee without copying.
  `Operand::Copy(x)` sets nothing, because codegen copies into a fresh slot.
- A `TailCall` sets `MUTATE | CAPTURE` on **every** index, because the backend
  rewrites the caller's argument slots.

**2. Three independent gates.** The attributes exist only if (a) the defining
crate's provider ran with optimization and without `-C incremental`, (b) the
defining crate's metadata encoder wrote the table under the same condition, and
(c) the *using* crate is itself optimized and non-incremental
(`TyCtxt::fn_abi_of_instance`). Turning `-C incremental` on in **either** crate
removes them: across crates `readonly … captures(none)` becomes
`captures(address)`. Executed on rustc 1.98.0-nightly: 175 checks (attributes on
declarations and definitions, and one forwarding outcome per configuration)
over 9 flag configurations, 0 disagreements with this model; and LLVM removed
an argument copy (`alloca` + `memcpy`) in exactly the one configuration where
all three gates were open and LLVM's pipeline ran.

**3. `ImpossibleClauses`.** The first pass of MIR analysis cleanup replaces the
whole body by a single `unreachable` block when the item's `where` clauses
cannot hold. It runs at every optimization level. It is sound only because no
well-typed use of such an item exists. **Version difference:** at the audited
revision the pass also recognises structurally impossible `Sized` clauses that
mention generic parameters (`dyn Trait<T>: Sized`); the executed 1.98.0-nightly
(where the pass is still called `ImpossiblePredicates`) does not, and leaves
that body intact. This was predicted from source and confirmed by execution.

**4. Post-monomorphization checks.** `check_mono_item` runs `abi_check` and
`move_check` on every monomorphized instance. `abi_check` rejects passing a
vector in a vector register unless the function containing the definition, and
(for non-rustic ABIs only) the function containing the call, enables the
required target feature. For a 256-bit vector on x86 the required feature is
**`avx`** (not `avx2`). The Rust ABI passes vectors wider than 128 bits through
memory on x86-64 and so never trips the check. `abi_check` also rejects unsized
by-value parameters on non-rustic ABIs. `move_check` is the `large_assignments`
lint; its exemption for by-move call arguments is syntactic on optimized MIR,
so the same source lints at `opt-level=0` and not at `opt-level=2`.

**5. Kernel-checked model.** A 1539-line Lean 4.34.1 file (82 theorems, 80 of
them depending on no axiom at all, including all 22 headline results; the other
two use only `propext`) proves, for models written in that file: the flag set
is a join-semilattice equal to bitwise OR on the `u8` encoding; trimming
trailing default entries is unobservable and is one half of a bijection;
deduced `readonly` implies no execution changes the caller's slot;
argument forwarding in the caller is sound under the deduced attributes; the
empty table is a sound coarsening; body erasure is a refinement on well-typed
instantiations; accepted vector calls transfer the value faithfully; and six
concrete counterexamples show each rule is necessary. It is a proof about
transcriptions, not about the compiler binary.

## Applicability

### Subjects and how they relate

| Short name used below | Identity | Role |
| --- | --- | --- |
| audited revision | `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (nightly 1.102.0, 2026-11-11) | All source statements are read at this commit unless marked otherwise. |
| executed revision | `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (nightly 1.98.0, 2026-05-31) | The toolchain that was actually run. Its source was diffed against the audited revision for every file a finding relies on. |
| head | `rust-lang/rust@01afe534803b93889b85f6028117251cfbd431da` (default branch on 2026-11-22) | Diffed only, to say which audited files have changed since. |
| LLVM 23.1.5 | `rust-lang/llvm-project@0a5579eb649d3634a9c30ac873300cc2944fa070` | The `src/llvm-project` submodule of the audited revision; source of the LangRef, verifier and `MemCpyOpt` statements. |
| LLVM 22.1.6 | `rust-lang/llvm-project@08c84e69a84d95936296dfcab0e38b34100725d5` | The submodule of the executed revision; only its version file and the two entry conditions of `processImmutArgument` were read. |
| Reference | `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | Normative text on bounds, aliasing and interior mutability. |
| Anneal semantics | `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/lean/Trusted/MirSemantics.lean` | A trusted Lean MIR semantics, examined only to place these mechanisms relative to it. |
| Lean | `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (tag `v4.34.1`) | The checker for the model. |

The report is about the audited revision. The executed revision is an older
compiler used as an executable witness; where the two differ the difference is
stated and traced to source. The LLVM, Reference and Anneal subjects are
interpretive context for rustc's behaviour, not objects of study in themselves.

### Configuration covered

- Host and target `x86_64-unknown-linux-gnu`; nightly toolchain (unstable `-Z`
  flags and the feature gates `trivial_bounds`, `repr_simd`,
  `unsized_fn_params`, `custom_mir`, `core_intrinsics`, `explicit_tail_calls`).
- Attribute matrix: `--edition=2021 -C codegen-units=1 -C symbol-mangling-version=v0`,
  `-C opt-level=2` (or `0` for one upstream build), with and without
  `-C incremental=<dir>`, with and without `-C no-prepopulate-passes`, default
  `panic=unwind`.
- Parameters are 64-byte, 8-aligned aggregates and `[u8; 80]` returns, which the
  Rust ABI passes by hidden pointer on this target; vectors are `#[repr(simd)]`
  structs of 128 and 256 bits.

### What was observed on which revision

- **Source:** every cited rustc path was read at the audited revision.
- **Execution in this investigation:** only the executed revision.
- **Recorded execution at the audited revision:** a preserved record of an
  earlier, smaller probe (16 comparable observations: `declare`-line
  attributes of 5 functions in 2 configurations, plus 6 single-crate cases; 15
  agree with the local run and 1 differs, as §8 explains). It was not re-run
  here and does not contain its Rust sources; see **Evidence** for why it is
  nevertheless treated as corroboration.

### Shared and version-specific behaviour

Shared by the audited and executed revisions (source identical or differing
only in names; which of these were also exercised by execution is stated per
finding):

- `UsageSummary`, `DeducedParamAttrs`, `read_only`, `captures_none`
  (`compiler/rustc_middle/src/middle/deduced_param_attrs.rs` is byte-identical).
- The visitor rules, the trailing-default trim, the optimization/incremental
  gate in the provider, the encoder gate, the consumer gate, and
  `apply_deduced_attributes`.
- Body erasure for *global* impossible clauses and for bodies tainted by errors.
- The definition-site and call-site vector checks, the unsized-parameter check,
  and the move-size logic.

Specific to the audited revision (absent from the executed one):

- The structural `Sized` test in the erasure pass, the pass name
  `ImpossibleClauses`, and its policy `PassPolicy::optional(true)` (the older
  `ImpossiblePredicates` declares `is_required() == true`).
- The early exit of deduction for compile-time-only (`Constness::Const { always: true }`)
  functions, and `()` being treated as not worth deducing for.
- `PassMode::Indirect { attrs, address_space, mode: IndirectMode }` in place of
  the older `on_stack` flag; `NoFree` among the default attributes of an
  indirect argument (the executed revision's IR has no `nofree`).
- Diagnostic wording of the vector check, and the `MutatingUseContext::Retag`
  arm (present only in the executed revision).

Head versus audited revision: `deduce_param_attrs.rs`,
`middle/deduced_param_attrs.rs`, `impossible_clauses.rs`,
`mono_checks/{mod.rs,move_check.rs}`, `rustc_ty_utils/src/abi.rs`,
`rustc_codegen_ssa/src/mir/mod.rs` and the body of
`TyCtxt::fn_abi_of_instance` are unchanged. `mono_checks/abi_check.rs` differs
only in its handling of the `llvm-intrinsic` ABI. `rustc_codegen_llvm/src/abi.rs`,
`rustc_target/src/callconv/mod.rs` and `rustc_codegen_ssa/src/mir/block.rs`
have changed elsewhere; the specific lines this report quotes from them are
still present at head, but those files were not re-read in full.

### Extending beyond what was examined

Nothing here is claimed for other targets, other backends, stable or beta
channels, or revisions outside the three listed. The visitor and the two
predicates are target-independent source, so the *rules* extend to any target
at the audited revision; which parameters are `PassMode::Indirect`, and
therefore whether any attribute is emitted, is target- and ABI-specific and was
observed only on x86-64 Linux.

## Findings

### 1. The data: `UsageSummary` and `DeducedParamAttrs`

Basis: source (audited revision, `compiler/rustc_middle/src/middle/deduced_param_attrs.rs`, the whole 80-line file).

```rust
pub struct UsageSummary(u8);
bitflags::bitflags! {
    impl UsageSummary: u8 {
        /// This parameter is dropped when it `needs_drop`.
        const DROP = 1 << 0;
        /// There is a shared borrow to this parameter.
        /// It allows for mutation unless parameter is `Freeze`.
        const SHARED_BORROW = 1 << 1;
        /// This parameter is mutated (excluding through a drop or a shared borrow).
        const MUTATE = 1 << 2;
        /// This parameter is captured (excluding through a drop).
        const CAPTURE = 1 << 3;
    }
}
pub struct DeducedParamAttrs { pub usage: UsageSummary }
```

The three methods (lines 39–79), with their bodies reduced to the decisive
expressions:

```rust
pub fn is_default(self) -> bool {
    self.usage.contains(UsageSummary::MUTATE | UsageSummary::CAPTURE)
}
pub fn read_only(&self, tcx, typing_env, ty) -> bool {
    if self.usage.contains(UsageSummary::MUTATE) { return false; }
    if self.usage.contains(UsageSummary::DROP) && ty.needs_drop(tcx, typing_env) { return false; }
    if self.usage.contains(UsageSummary::SHARED_BORROW) && !ty.is_freeze(tcx, typing_env) { return false; }
    true
}
pub fn captures_none(&self, tcx, typing_env, ty) -> bool {
    if self.usage.contains(UsageSummary::CAPTURE) { return false; }
    if self.usage.contains(UsageSummary::DROP) && ty.needs_drop(tcx, typing_env) { return false; }
    true
}
```

Three consequences worth retaining:

- `is_default` is true for four of the sixteen flag sets (any combination of
  `DROP` and `SHARED_BORROW` on top of `MUTATE | CAPTURE`), and for each of
  them both predicates are false at every type. "Default" means "contributes
  no attribute", not "equal to one particular value".
- The summary is type-independent; `ty` enters only when the predicates are
  evaluated, with the typing environment of the instance being compiled. That
  is what makes `DROP` and `SHARED_BORROW` *deferred* judgements.
- Flags are only ever combined with `|=`, so the summary of a body is the join
  of per-use contributions and is insensitive to control flow and to order.

### 2. The visitor: which MIR use sets which flag

Basis: source (audited revision, `compiler/rustc_mir_transform/src/deduce_param_attrs.rs`, `visit_place` lines 48–100 and `visit_terminator` lines 102–149) + execution (executed revision) for the rows that name a probe function.

The visitor is indexed by `Local`; only locals with index `< arg_count + 1`
(the return place and the arguments) are tracked. Cases are tried in this
order:

| MIR use of a tracked local | Flags added | Rationale given in source, or derived | Probe function exercising it |
| --- | --- | --- | --- |
| `PlaceContext::NonUse(..)` | none | "Not actually using the local." | — |
| any context, when the place's first projection is `Deref` | none | "Neither mutated nor captured." The access goes through the value stored in the slot. | — |
| `MutatingUse(Drop)` with **empty** projection | `DROP` | "This is a `Drop`. It could disappear at monomorphization, so mark it specially." | `generic_drop_only` |
| `MutatingUse(Call \| Yield \| Drop \| Borrow \| RawBorrow)` (so: call destination, yield resume place, `Drop` of a projection, `&mut`, `&raw mut`) | `MUTATE \| CAPTURE` | For `Drop` of a projection: "Projection changes the place's type, so `needs_drop(local.ty)` is not `needs_drop(place.ty)`." | `ret_captured` (call destination) |
| `MutatingUse(Store \| SetDiscriminant \| AsmOutput \| Projection)` | `MUTATE` | A plain write; the address goes nowhere. | `mutate_local_copy_big_freeze`, `ret_not_captured` |
| `NonMutatingUse(RawBorrow)` (`&raw const`) | `MUTATE \| CAPTURE` | "Whether mutating though a `&raw const` is allowed is still undecided, so we disable any sketchy `readonly` optimizations for now." | `raw_const_borrow_big_freeze` |
| `NonMutatingUse(SharedBorrow)` (`&`) | `SHARED_BORROW \| CAPTURE` | "Not mutating if the parameter is `Freeze`." | `shared_borrow_big_freeze`, `shared_borrow_big_cell` |
| `NonMutatingUse(Inspect \| Copy \| Move \| FakeBorrow \| PlaceMention \| Projection)` | none | "Not mutating, so it's fine." | `read_big_freeze` |
| terminator `Call`, for each argument that is `Operand::Move(place)` with `place` not starting with `Deref` and based on a tracked local | `MUTATE \| CAPTURE` | See below. | `forward_by_move_indirect`, `custom_call_move_arg` |
| terminator `TailCall` | `MUTATE \| CAPTURE` on **every** tracked local | "Like a call, but more conservative because the backend may introduce writes to an argument if the argument is passed as `PassMode::Indirect { mode: IndirectMode::Pointer, ... }`." | `tail_reads_then_becomes` |

Before visiting, `DeduceParamAttrs::new` (lines 31–39) sets
`usage[RETURN_PLACE] |= MUTATE`, with the comment "Code generation indicates
that a return place is writable. To avoid setting both `readonly` and
`writable` attributes, when return place is never written to, mark it as
mutated."

**Why a moved call argument must count as mutated and captured.** The source
comment (lines 103–123) uses `fn f(x: BigStruct) { g(x) }` /
`fn g(mut y: BigStruct) { y.foo = 1 }` and concludes that with
`_0 = g(move _1)` "it would be incorrect to mark `x` (i.e. `_1`) as `readonly`,
because `g`'s write to its copy of the indirect parameter would actually be a
write directly to the pointer that `f` passes. Note that function arguments are
the only situation in which this problem can arise: every other use of `move`
in MIR doesn't actually write to the value it moves from."

The codegen side of that statement is in
`compiler/rustc_codegen_ssa/src/mir/block.rs`. For an ordinary call
`by_move` is `matches!(arg.node, mir::Operand::Move(_))` (line 1411), and
`codegen_argument` then decides (lines 2030–2040):

```rust
// Copy to an alloca when the argument is neither by-val nor by-move.
if op_place_val.align < required_align
    || (mode == IndirectMode::Pointer && !by_move)
{
    let scratch = PlaceValue::alloca(bx, arg.layout.size, required_align);
    …
    op.store_with_annotation(bx, scratch.with_type(arg.layout));
    …
    scratch
} else {
    op_place_val
}
```

So a `Copy` operand is copied into a fresh `alloca` and the callee receives a
pointer to that; a `Move` operand hands the callee the caller's own place.
This is why `Operand::Copy` contributes no flag while `Operand::Move`
contributes two. It was confirmed with hand-written MIR, where the only
difference between two functions is the operand kind:

```rust
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn custom_call_copy_arg(a: Big) { mir! { { Call(RET = custom_call_copy_arg(a), ReturnTo(bb1), UnwindUnreachable()) } bb1 = { Return() } } }
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn custom_call_move_arg(a: Big) { mir! { { Call(RET = custom_call_move_arg(Move(a)), ReturnTo(bb1), UnwindUnreachable()) } bb1 = { Return() } } }
```

Observed on the executed revision (`-C opt-level=2 -C no-prepopulate-passes`):
`custom_call_copy_arg(ptr … readonly … captures(none) … %_1)` and
`custom_call_move_arg(ptr … captures(address) … %_1)` with no `readonly`.

**Why a tail call must mark everything.** In the same file (lines 1260–1306
and 1363–1409) guaranteed tail calls first copy each
`PassMode::Indirect { mode: IndirectMode::Pointer, .. }` argument to a
temporary, then copy the temporaries *into the caller's own argument slots*,
and pass those slots: "Therefore we store the argument for the callee in the
corresponding caller's slot." The write to the caller's slot is introduced by
the backend and appears in no MIR statement. Observed on the executed
revision: in

```rust
pub fn tail_reads_then_becomes(a: BigFreeze, b: BigFreeze, n: u64) -> u64 {
    if n == 0 { return a.0[0] ^ b.0[0]; }
    let s = a.0[1].wrapping_add(b.0[1]);
    become tail_helper(BigFreeze([s; 8]), BigFreeze([n; 8]), n - 1)
}
```

both `a` and `b` are only read by the function's own statements and the
`become` passes fresh values, yet both parameters come out
`captures(address)` without `readonly`, while `tail_helper` (same uses, no
`become`) gets `readonly … captures(none)` on both.

### 3. When the table is empty, and how it is trimmed

Basis: source (audited revision, `deduce_param_attrs.rs` lines 177–242).

`deduced_param_attrs(tcx, def_id: LocalDefId) -> &[DeducedParamAttrs]`
returns the empty slice, in this order, when:

1. `tcx.sess.opts.optimize == OptLevel::No || tcx.sess.opts.incremental.is_some()`
   ("This computation is unfortunately rather expensive, so don't do it unless
   we're optimizing. Also skip it in incremental mode.");
2. there is no `Freeze` lang item;
3. the item is a `FnDef` and no input or output type "could potentially
   benefit from deduction" (false for `bool`, `char`, floats, integers, raw
   pointers, references, slices and `()`; true for everything else);
4. `!tcx.is_mir_available(def_id)`;
5. the function is compile-time-only (`hir::Constness::Const { always: true }`);
6. the body has a `spread_arg` ("Arguments spread at ABI level are currently
   unsupported.").

Otherwise it visits `tcx.optimized_mir(def_id)` and then trims:

```rust
// Trailing parameters past the size of the `deduced_param_attrs` array are assumed to have the
// default set of attributes, so we don't have to store them explicitly. Pop them off to save a
// few bytes in metadata.
while let Some((last, rest)) = deduced_param_attrs.split_last()
    && last.is_default()
{
    deduced_param_attrs = rest;
}
```

The consumer (§4) treats a missing index as "add nothing". Because an
`is_default` entry also adds nothing at every type (§1), trimming cannot change
any emitted attribute; the Lean development proves exactly this statement
(`rmeta_trim_lookup_eq`, §10). Index 0 always carries `MUTATE`; it is default
exactly when the return place is also captured, for instance when `_0` is the
destination of a call. Two tables, derived by applying §2 to MIR preserved from
the probe (the tables themselves were not dumped):

- `mixed_read_then_forward`, whose MIR is `_3 = copy (_1.0)[0]`,
  `_4 = sink_big_freeze(move _2)`, `_0 = Add(copy _3, copy _4)`:
  `[{MUTATE}, {}, {MUTATE, CAPTURE}]`, stored as `[{MUTATE}, {}]`.
- `forward_by_move_indirect`, whose MIR is `_0 = sink_big_freeze(move _1)`:
  `[{MUTATE, CAPTURE}, {MUTATE, CAPTURE}]`, stored as the empty table. A plain
  forwarding wrapper therefore leaves nothing in metadata at all.

The module's opening comment states the invariant the whole scheme rests on:
"Note that this *crucially* relies on codegen *not* doing any more MIR-level
transformations after `optimized_mir`! We check for things that are *not*
guaranteed to be preserved by MIR transforms, such as which local variables
happen to be mutated." The matching comment sits in
`compiler/rustc_codegen_ssa/src/mir/mod.rs` (lines 212–214), next to the
`fn_abi_of_instance` call in `codegen_mir`.

### 4. From table to LLVM attributes

Basis: source (audited revision) + execution (executed revision).

The path from a summary to an attribute on an LLVM parameter has three stations,
none of which is in `rustc_codegen_ssa`:

**(a) `compiler/rustc_ty_utils/src/abi.rs`.** `fn_abi_of_instance_raw` (lines
298–316) starts from the attribute-free `fn_abi_of_instance_no_deduced_attrs`
result and, only for `InstanceKind::Item(fn_def_id)`, calls
`fn_abi_adjust_for_deduced_attrs` (lines 643–665):

```rust
let deduced = if abi.is_rustic_abi() { tcx.deduced_param_attrs(fn_def_id) } else { &[] };
if deduced.is_empty() {
    fn_abi
} else {
    let mut fn_abi = fn_abi.clone();
    apply_deduced_attributes(cx, deduced, 0, &mut fn_abi.ret);
    for (arg_idx, arg) in fn_abi.args.iter_mut().enumerate() {
        apply_deduced_attributes(cx, deduced, arg_idx + 1, arg);
    }
    …
}
```

and `apply_deduced_attributes` (lines 671–693):

```rust
// Deduction is performed under the assumption of the indirection pass mode.
let PassMode::Indirect { ref mut attrs, .. } = arg.mode else { return; };
// The default values at the tail of the list are not encoded.
let Some(deduced) = deduced.get(idx) else { return; };
if deduced.read_only(cx.tcx(), cx.typing_env, arg.layout.ty) {
    attrs.regular.insert(ArgAttribute::ReadOnly);
}
if deduced.captures_none(cx.tcx(), cx.typing_env, arg.layout.ty) {
    attrs.regular.insert(ArgAttribute::CapturesNone);
}
```

Hence: non-rustic ABIs never get deduced attributes; shims and other
non-`Item` instances never get them; directly passed, pair-passed, cast and
`IndirectUnsized` parameters never get them; and the type consulted is the
instance's `arg.layout.ty`.

**(b) `compiler/rustc_target/src/callconv/mod.rs`.** An indirect argument
starts with `NoAlias`, `CapturesAddress`, `NonNull`, `NoUndef`, `NoFree`
(`indirect_pass_mode`, lines 425–446; its comment: "For non-immediate arguments
the callee gets its own copy of the value on the stack, so there are no
aliases. The function can capture the address of the argument, but not the
provenance."). The capture attributes are nested bit patterns
(`CapturesNone = 0b111`, `CapturesAddress = 0b110`, `CapturesReadOnly = 0b100`,
lines 133–146), so inserting `CapturesNone` upgrades `CapturesAddress`.

**(c) `compiler/rustc_codegen_llvm/src/abi.rs`.** `get_attrs` (lines 60–115)
emits the optimization attributes only "when optimizing"
(`cx.sess().opts.optimize != config::OptLevel::No`), mapping
`ArgAttribute::ReadOnly` to LLVM `readonly` (table at lines 42–52) and the first
matching capture attribute, tried in the order `CapturesNone`,
`CapturesAddress`, `CapturesReadOnly` (lines 54–58). For an indirect **return**
the same file adds `sret(…)` and, when optimizing, `writable` and
`dead_on_unwind` unconditionally (around line 542); an indirect pointer
**argument** gets `dead_on_return` (around line 589).

**The return place.** LLVM's rule is stated twice in the vendored LLVM 23.1.5:
`llvm/docs/LangRef.md`, under `writable`: "The `writable` attribute cannot be
combined with `readnone`, `readonly` or a `memory` attribute that does not
contain `argmem: write`."; and `llvm/lib/IR/Verifier.cpp` (line 2147):
`Check(!(Attrs.hasAttribute(Attribute::Writable) && Attrs.hasAttribute(Attribute::ReadOnly)), "Attributes writable and readonly are incompatible!", V);`.
A body that never writes `_0` (a diverging function, or a body erased to
`unreachable` by §8) would, without the `MUTATE` seed, produce a `readonly
writable` `sret` pointer, i.e. IR the verifier rejects. The seed costs nothing
else: `captures(none)` is still deduced for the return place. Observed on the
executed revision, upstream definition and downstream declaration alike:

```text
ret_never_returns : (ptr dead_on_unwind noalias noundef writable sret([80 x i8]) align 1 captures(none) dereferenceable(80) %_0)
ret_not_captured  : (ptr dead_on_unwind noalias noundef writable sret([80 x i8]) align 1 captures(none) dereferenceable(80) %_0, i8 noundef %v)
ret_captured      : (ptr dead_on_unwind noalias noundef writable sret([80 x i8]) align 1 captures(address) dereferenceable(80) %_0, i8 noundef %v)
```

where `ret_never_returns` is `loop {}`, `ret_not_captured` is `[v; 80]`, and
`ret_captured` is `black_box([v; 80])` (the return place is a call
destination). None carries `readonly`.

### 5. Three gates on session options

Basis: source (audited revision; the three code sites are textually the same in the executed revision) + execution (executed revision).

| Gate | Code site (audited revision) | Condition for the attributes to survive | Whose session |
| --- | --- | --- | --- |
| provider | `compiler/rustc_mir_transform/src/deduce_param_attrs.rs` lines 183–185 | `optimize != OptLevel::No && incremental.is_none()` | defining crate |
| encoder | `compiler/rustc_metadata/src/rmeta/encoder.rs` lines 2008–2023 | `output_types.should_codegen() && optimize != OptLevel::No && incremental.is_none()`; then one entry per `DefKind::Fn \| DefKind::AssocFn` in `mir_keys` | defining crate |
| consumer | `compiler/rustc_middle/src/ty/mod.rs` lines 2374–2385, `TyCtxt::fn_abi_of_instance` | `optimize != OptLevel::No && incremental.is_none()`, else it calls `fn_abi_of_instance_no_deduced_attrs` | using crate |

The decoder (`compiler/rustc_metadata/src/rmeta/decoder/cstore_impl.rs` lines
294–307) returns the default (empty) slice for a missing table entry and carries
the comment "FIXME: `deduced_param_attrs` has some sketchy encoding settings,
where we don't encode unless we're optimizing, doing codegen, and not
incremental (see `encoder.rs`). I don't think this is right!". The consumer's
comment reads "Only deduce attrs in full, optimized builds. Otherwise, avoid
the query system overhead of ever invoking the `fn_abi_of_instance_raw` query."

The consumer gate is the easy one to miss: reading only the provider and the
decoder suggests that an incremental *downstream* crate would still see an
optimized upstream crate's table. It does not. Executed on the executed
revision with an upstream crate `deduce_up` and a downstream crate
`deduce_down` that calls it, both at `-C opt-level=2`, for
`pub fn read_big_freeze(x: BigFreeze) -> u64 { x.0[0].wrapping_add(x.0[7]) }`
(`BigFreeze` is `struct BigFreeze(pub [u64; 8])`):

| upstream `-C incremental` | downstream `-C incremental` | `declare` of `read_big_freeze` in the downstream crate's IR |
| --- | --- | --- |
| no | no | `ptr dead_on_return noalias noundef readonly align 8 captures(none) dereferenceable(64)` |
| yes | no | `ptr dead_on_return noalias noundef align 8 captures(address) dereferenceable(64)` |
| no | yes | `ptr dead_on_return noalias noundef align 8 captures(address) dereferenceable(64)` |
| yes | yes | `ptr dead_on_return noalias noundef align 8 captures(address) dereferenceable(64)` |

In the third row the upstream crate's *own* definition still carries
`readonly … captures(none)` (it is both producer and consumer of its facts),
which isolates the consumer gate. With the upstream crate at `-C opt-level=0`
and the downstream crate optimized and non-incremental, every declaration again
shows `captures(address)` and no `readonly`.

A side effect seen in the preserved MIR: the optimized MIR of the same crate
differs between the incremental and non-incremental builds, because the MIR
inliner is off in incremental mode
(`compiler/rustc_mir_transform/src/inline.rs` lines 45–62: "Only inline for
`-Copt-level >= 2`, and don't inline in incremental mode to increase
incremental effectiveness."). The summaries that *would* have been computed
are therefore not even the same summaries.

### 6. Observed attribute matrix

Basis: execution (executed revision); every row agrees with the rules of §2 applied to the function's optimized MIR, which is preserved under `support/specimens/mir/`.

All functions are `#[inline(never)] pub fn` in `deduce_up`; `BigCell` is
`struct BigCell(pub [Cell<u64>; 8])`. The column shows, per pointer parameter,
whether `readonly` is present and the `captures(…)` value, as emitted by rustc
when all gates are open. "rustc-emitted" means: read from `declare` lines in
the downstream crate, and from `define` lines only under
`-C no-prepopulate-passes`; the two always agreed.

| Function (body) | Uses of the parameter in optimized MIR | rustc-emitted |
| --- | --- | --- |
| `read_big_freeze(x: BigFreeze)` — `x.0[0].wrapping_add(x.0[7])` | two `copy (_1.0)[…]` | `readonly`, `captures(none)` |
| `shared_borrow_big_freeze(x: BigFreeze)` — `black_box(&x); x.0[0]` | `&_1`, one copy | `readonly`, `captures(address)` |
| `shared_borrow_big_cell(x: BigCell)` — `black_box(&x); x.0[0].get()` | `&_1`, `&(_1.0)[0]` | no `readonly`, `captures(address)` |
| `raw_const_borrow_big_freeze(x: BigFreeze)` — `black_box(&raw const x); x.0[0]` | `&raw const _1`, one copy | no `readonly`, `captures(address)` |
| `mutate_local_copy_big_freeze(mut x: BigFreeze)` — `let i = (x.0[0] & 7) as usize; x.0[i] = 0xdead; x.0[0] ^ x.0[7]` | copies and `(_1.0)[_2] = const 57005_u64` | no `readonly`, `captures(none)` |
| `forward_by_move_indirect(x: BigFreeze)` — `sink_big_freeze(x)` | `sink_big_freeze(move _1)` | no `readonly`, `captures(address)` |
| `mixed_read_then_forward(a, b)` — `a.0[0].wrapping_add(sink_big_freeze(b))` | `a`: copy; `b`: `move _2` in a call | `a`: `readonly`, `captures(none)`; `b`: neither |
| `mixed_forward_then_read(a, b)` — `sink_big_freeze(a).wrapping_add(b.0[0])` | mirror image | `a`: neither; `b`: `readonly`, `captures(none)` |
| `generic_drop_only::<u64>(_x: [u64; 8], flag)` — `flag.wrapping_mul(3)` | `drop(_1)` | `readonly`, `captures(none)` |
| `generic_drop_only::<String>(_x: [String; 8], flag)` — same generic body | `drop(_1)` | no `readonly`, `captures(address)` |

Notes on reading compiler output, each of which changed a conclusion during
this work:

- **`define` lines under the normal LLVM pipeline are not rustc's deduction.**
  LLVM runs its own attribute inference on definitions. Under plain
  `-C opt-level=2`, `forward_by_move_indirect` is *defined* with
  `readonly … captures(none)` (LLVM sees that `sink_big_freeze` only reads),
  while the cross-crate *declaration*, which only rustc can annotate, has
  neither. Use declarations, or `-C no-prepopulate-passes`, to see what rustc
  emitted. The generic instantiations exist only as definitions in the
  downstream crate, so the `DROP` refinement is visible only under
  `-C no-prepopulate-passes`.
- **The two `mixed_*` rows exercise trimming end to end.** In
  `mixed_read_then_forward` the last table entry is default and is popped
  before the table is written to metadata; the downstream declaration still
  shows the correct attributes for both parameters.
- **`mutate_local_copy_big_freeze` needs a store no MIR pass can delete.** The
  data-dependent index keeps the store alive in optimized MIR. Derived, not
  observed: because the visitor reads *optimized* MIR, a store that a MIR
  optimization removes is invisible to it, and the parameter would then be
  deduced `readonly`, correctly, since the compiled function no longer
  performs the store.

### 7. What the attributes buy, and what a wrong one would cost

Basis: source (LLVM 23.1.5) + execution (executed revision, LLVM 22.1.6) + derived.

`llvm/docs/LangRef.md` at the vendored LLVM 23.1.5 defines `readonly` on a
pointer argument as "This attribute indicates that the function does not write
through this pointer argument, even though it may write to the memory that the
pointer points to. If a function writes to a readonly pointer argument, the
behavior is undefined.", and lists `captures(none)` as "Pointer not captured."
and `captures(address)` as "Address may be captured, but not provenance."

A concrete consumer is `MemCpyOptPass::processImmutArgument`
(`llvm/lib/Transforms/Scalar/MemCpyOptimizer.cpp`, from line 2102). It is
invoked for call arguments with `CB->onlyReadsMemory(i)`, requires
`CB.doesNotCapture(ArgNo)` and either `noalias` on the parameter or an
alias-analysis proof, requires the argument to be an `alloca` wholly initialised
by one `memcpy`, and then replaces the argument by the `memcpy` *source*:
"This is called on memcpy dest pointer arguments attributed as immutable during
call. Try to use memcpy source directly if all of the following conditions are
satisfied." The first two conditions are also present in LLVM 22.1.6.

This was observed end to end. The downstream crate contains

```rust
#[inline(never)]
pub fn forwarding_witness(src: &BigCopy) -> u64 { read_big_copy(*src) }
```

with `BigCopy` a `Copy` twin of `BigFreeze` and `read_big_copy` an upstream
`#[inline(never)]` reader. rustc lowers the argument as `alloca`,
`memcpy(tmp, src, 64)`, `call read_big_copy(tmp)`; the downstream crate knows
nothing about `read_big_copy` except its declaration.

| Configuration | `alloca` in `forwarding_witness` | `memcpy` calls | pointer passed to `read_big_copy` |
| --- | --- | --- | --- |
| both crates optimized, non-incremental, normal LLVM pipeline | no | 0 | `%src` itself: `tail call … @read_big_copy(ptr noalias noundef nonnull readonly align 8 captures(none) dereferenceable(64) %src)` |
| either or both crates `-C incremental` | yes | 1 | the temporary: `call … @read_big_copy(ptr noalias noundef nonnull align 8 captures(address) dereferenceable(64) %_2)` |
| any configuration with `-C no-prepopulate-passes` on the downstream crate (LLVM's optimization passes do not run), including the one with the upstream crate at `-C opt-level=0` | yes | 1 | the temporary |

The cleanest control is the configuration in which only the *upstream* crate is
incremental: the downstream command line is then identical to the first row,
and the only difference is whether the upstream metadata carries a table.

So the deduced attributes are precisely what lets the using crate's LLVM hand
a callee the caller's live object instead of a private copy, and the three
gates of §5 turn that off. The optimization is pattern-sensitive: a variant
that also reads `src.0[3]` after the call was never forwarded in any
configuration (two `memcpy` calls remain; an earlier LLVM pass had split the
copy, so no single `memcpy` initialises the `alloca`).

Derived: this is the mechanism by which a wrong `readonly` or `captures(none)`
becomes a miscompilation rather than a missed optimization. If a callee wrote
through, or retained, a parameter that rustc had marked `readonly
captures(none)`, the forwarded call would let that write land in the caller's
object, which the unoptimized program never exposes. The Lean development
models exactly this pair of lowerings (`callerReference` and `callerForwarded`,
§10) and its first counterexample is the `Operand::Move` case of §2.

The Rust-level facts the two type-dependent rules lean on are normative
(Reference, `src/behavior-considered-undefined.md`, rule `undefined.immutable`):
"the bytes pointed to by a shared reference, including transitively through
other references (both shared and mutable) and `Box`es, are immutable", with
`undefined.alias` exempting "data inside an `UnsafeCell<U>`"; and
`src/interior-mutability.md`, rule `interior-mut.unsafe-cell`:
"`std::cell::UnsafeCell<T>` type is the only allowed way to disable this
requirement." `is_freeze` is rustc's query for "contains no `UnsafeCell`
outside indirection"; that correspondence is the usual reading and was not
separately audited here.

### 8. `ImpossibleClauses`: erasing bodies whose `where` clauses cannot hold

Basis: source (audited and executed revisions) + normative (Reference) + execution (executed revision) + recorded execution (audited revision).

**What it is for.** The module comment of
`compiler/rustc_mir_transform/src/impossible_clauses.rs`: "It's possible to
`#!feature(trivial_bounds)]` to write a function with impossible to satisfy
clauses, e.g.: `fn foo() where String: Copy {}`. We don't usually need to worry
about this kind of case, since we would get a compilation error if the user
tried to call it. However, since we optimize even without any calls to the
function, we need to make sure that it even makes sense to try to evaluate the
body. If there are unsatisfiable where clauses, then all bets are off, and we
just give up."

**The decision at the audited revision** (`has_impossible_clauses`, lines 68–97):

```rust
let clauses = tcx.clauses_of(def_id).instantiate_identity(tcx);
// Some `Sized` clauses that mention local generics are still impossible
// for every instantiation, e.g. `dyn Trait<T>: Sized`.
if let Some(sized_trait) = tcx.lang_items().sized_trait() {
    if clauses.clauses.iter().copied().map(Unnormalized::skip_norm_wip)
        .any(|clause| has_structurally_impossible_sized_clause(tcx, sized_trait, clause))
    { return true; }
}
let clauses = clauses.clauses.into_iter().map(Unnormalized::skip_norm_wip).filter(|c| {
    !c.has_type_flags(
        // Only consider global clauses to simplify.
        TypeFlags::HAS_FREE_LOCAL_NAMES
            // Clauses that refer to alias constants as they cause cycles.
            | TypeFlags::HAS_CONST_ALIAS,
    )
});
let clauses: Vec<_> = traits::elaborate(tcx, clauses).collect();
clauses.references_error() || traits::impossible_clauses(tcx, clauses)
```

Two tests, with different domains:

1. *Structural `Sized`* (lines 38–64), applied to **all** clauses including
   those mentioning generic parameters: a positive `Sized` clause whose self
   type is `str`, a slice, a `dyn` type, a foreign type, a tuple whose last
   element is such, or an ADT whose sizedness constraint is such.
2. *Trait solving*, applied only to clauses with neither
   `HAS_FREE_LOCAL_NAMES` nor `HAS_CONST_ALIAS`. The module comment gives both
   reasons for the filter: such clauses could never be proven unsatisfiable
   ("`<T as Foo>`"), and normalizing them "can confuse the normalization code
   (leading to cycle errors)". `traits::impossible_clauses`
   (`compiler/rustc_trait_selection/src/traits/mod.rs`, lines 856–883)
   "Normalizes the clauses and checks whether they hold in an empty
   environment", under `TypingEnv::fully_monomorphized()`, and reports
   impossibility "only … for true errors, and not ambiguities or overflows".

**The transformation** (`run_pass`, lines 99–115) fires when
`body.tainted_by_errors.is_some() || has_impossible_clauses(..)`: it truncates
`basic_blocks` to one block, clears its statements, sets its terminator to
`TerminatorKind::Unreachable`, clears `var_debug_info`, and truncates
`local_decls` to `arg_count + 1`. Its policy is `PassPolicy::optional(true)`
with the comment "This can only replace code proven unreachable with immediate
UB, so it cannot remove UB."

**Where it runs.** It is the first pass of `run_analysis_cleanup_passes`
(`compiler/rustc_mir_transform/src/lib.rs`, lines 642–652), reached through
`run_analysis_to_runtime_passes` from `mir_drops_elaborated_and_const_checked`
and, for promoted constants, from `promoted_mir`. It is therefore not gated on
the optimization level. `inner_optimized_mir` (lines 802–833) later skips the
optimization pipeline for such bodies: "If
`mir_drops_elaborated_and_const_checked` found that the current body has
unsatisfiable predicates, it will shrink the MIR to a single `unreachable`
terminator. More generally, if MIR is a lone `unreachable`, there is nothing to
optimize."

**Why it is sound.** Normative, Reference `src/trait-bounds.md`: rule
`bound.trivial`, "Bounds that don't use the item's parameters or higher-ranked
lifetimes are checked when the item is defined. It is an error for such a
bound to be false."; rule `bound.special`, "`Copy`, `Clone`, and `Sized` bounds
are also checked for certain generic types when using the item, even if the
use does not provide a concrete type. … It is an error to have `Sized` as a
bound on a trait object or slice." The unstable `trivial_bounds` feature (not
described by the Reference) relaxes the first rule from an error to a lint at
the definition; it does not make the item usable. Derived: an item flagged by
either test has no well-typed use at any instantiation, so replacing its body
by immediate UB cannot change the behaviour of a well-typed program. The
soundness argument is *vacuous by construction*, and its one premise is that
the flagged clauses really fail for every instantiation. That premise is why
the solver test must skip parameter-dependent clauses (a clause like `T: Copy`
fails for some `T` and holds for others) and why the structural test may look
at them (substitution cannot change `dyn Trait<…>` into a sized type).

**Execution.** Each case compiles one file with
`--edition=2021 --crate-type=lib -C opt-level=1 --emit=mir` and inspects the
function's MIR. "Erased" means the body is exactly `bb0: { unreachable; }`.
In this table and the one in §9, compiler messages are quoted with their inner
backquotes removed.

| Source | Executed revision (1.98.0) | Recorded, audited revision (1.102.0) |
| --- | --- | --- |
| `#![feature(trivial_bounds)] pub fn impossible_string_copy(x: u32) -> u32 where String: Copy { x.wrapping_mul(3).wrapping_add(1) }` | erased; warning `trait bound String: Copy does not depend on any type or lifetime parameters` | erased; same warning |
| the same at `-C opt-level=0` | erased | not recorded |
| the same body with no `where` clause | not erased | not recorded |
| `pub trait MyTrait<T> {} pub fn impossible_dyn_sized<T>(x: u32) -> u32 where dyn MyTrait<T>: Sized { … }` | **not erased**; no diagnostic | **erased**; no diagnostic |
| `pub fn possible_for_some_t<T>(x: u32) -> u32 where T: Copy { … }` | not erased | not recorded |
| `#![feature(trivial_bounds)] pub fn impossible_str_sized<T>(x: u32) -> u32 where str: Sized { … }` | erased | not recorded |
| a caller `impossible_string_copy(1)` | rejected: `error[E0277]: the trait bound String: Copy is not satisfied` | not recorded |
| a caller `impossible_dyn_sized::<u8>(1)` | rejected: `error[E0277]: the size for values of type (dyn MyTrait<u8> + 'static) cannot be known at compilation time` | not recorded |

The fourth row is the version difference. At the executed revision the pass is
`ImpossiblePredicates`
(`compiler/rustc_mir_transform/src/impossible_predicates.rs`); its
`has_impossible_predicates` (lines 39–55) consists only of the filter on
`HAS_FREE_LOCAL_NAMES | HAS_CT_PROJECTION` followed by elaboration and
`traits::impossible_predicates`. `dyn MyTrait<T>: Sized` mentions `T`, is
filtered out, and nothing remains to be impossible. The sixth row is the
control: `str: Sized` is structurally the same kind of clause but mentions no
parameter, so the older solver-only test catches it too. The last two rows
confirm, on the executed revision, the premise that such items cannot be used.

A cross-link with §4: an erased body never writes `_0`. If such a function
returns indirectly, only the `MUTATE` seed keeps its `sret` pointer from being
deduced `readonly`.

### 9. Post-monomorphization checks: `abi_check` and `move_check`

Basis: source (audited revision; executed revision diffed) + execution (executed revision) + recorded execution (audited revision).

**Entry point.** `compiler/rustc_monomorphize/src/mono_checks/mod.rs` is 19
lines: "This implements a single query, `check_mono_fn`, that gets fired for
each monomorphization of all functions. This lets us implement
monomorphization-time checks in a way that is friendly to incremental
compilation."

```rust
fn check_mono_item<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) {
    let body = tcx.instance_mir(instance.def);
    abi_check::check_feature_dependent_abi(tcx, instance, body);
    move_check::check_moves(tcx, instance, body);
}
```

It is requested from the collector
(`compiler/rustc_monomorphize/src/collector.rs`, `collect_items_of_instance`,
line 1340: `tcx.ensure_ok().check_mono_item(instance);`, under the comment
"This item is getting monomorphized, do mono-time checks."). A generic function
that is never instantiated is never checked.

**`abi_check`, vectors** (`abi_check.rs`, 323 lines). `passes_vectors_by_value`
(lines 25–48) classifies a `(PassMode, BackendRepr)` pair:
`Ignore | Indirect { .. } | IndirectUnsized { .. }` is `UsesVectorRegisters::No`;
a `Cast` whose registers include a vector register, or `Direct`/`Pair` with a
`SimdVector` layout, is `FixedVector`; `Direct`/`Pair` with a scalable-vector
layout is `ScalableVector`. `do_check_simd_vector_abi` (lines 54–138) then, for
every argument and the return value that is `FixedVector`, looks up the first
entry of `features_for_correct_fixed_length_vector_abi()` whose bit width is at
least the value's size, and errors unless

```rust
let have_feature = |feat: Symbol| {
    let target_feats = tcx.sess.internal_target_features.contains(&feat);
    let fn_feats = codegen_attrs.target_features.iter().any(|x| x.name == feat);
    target_feats || fn_feats
};
```

holds for it, where `codegen_attrs` belongs to the function passed in. For x86
the table is
`&[(128, "sse"), (256, "avx"), (512, "avx512f")]`
(`compiler/rustc_target/src/target_features.rs`, lines 1172–1173). A 256-bit
vector therefore requires `avx`. A function that enables only `avx2` passes
(observed below: the `avx2` callee's own definition is accepted), which is
consistent with implied features being included in the function's feature
list; that expansion was not traced in source. The `vectorcall` ABI
additionally requires `sse2` regardless of types.

The check is applied at two sites with different ABI coverage:

- *Definition site* (`check_instance_abi`, lines 171–208): every instance
  except the `llvm-intrinsic` ABI, with the features of the instance's own
  definition. "Unlike the call-site check, we do also check "Rust" ABI
  functions here."
- *Call site* (`check_call_site_abi`, lines 210–287): for each `Call` and
  `TailCall` terminator in blocks reachable after monomorphization, with the
  features of the **caller**. It returns early for rustic ABIs: "We directly
  handle the soundness of Rust ABIs -- so let's skip the majority of call sites
  to avoid a perf regression.", followed at the audited revision by a `FIXME`
  that calls this skip "unsound" in connection with scalable vectors
  ("we need the call-site check here as well then").

**Why the Rust ABI is exempt for fixed vectors.**
`compiler/rustc_target/src/callconv/mod.rs`, `adjust_for_rust_abi` (from line
756): "we want callers and callees to always agree on the ABI of how they pass
SIMD arguments. If we were to *not* make these arguments indirect then they'd
be immediates in LLVM, which means that they'd used whatever the appropriate
ABI is for the callee and the caller. That means, for example, if the caller
doesn't have AVX enabled but the callee does, then passing an AVX argument
across this boundary would cause corrupt data to show up. This problem is fixed
by passing most SIMD arguments through memory", implemented as
`if spec.simd_types_indirect && !can_pass_simd_directly(arg) { arg.make_indirect(); }`.
`can_pass_simd_directly` (from line 776) allows direct passing on x86-64
(non-softfloat) only for `arg.layout.size.bits() <= 128`, because SSE2 is always
available there. So on this target a 256-bit vector is `PassMode::Indirect`
under the Rust ABI and `PassMode::Direct` under `extern "C"`.

**`abi_check`, unsized parameters** (`do_check_unsized_params`, lines 144–164):
returns immediately if `fn_abi.conv.is_rustic_abi()` ("Unsized parameters are
allowed with the (unstable) "Rust" (and similar) ABIs."); otherwise every
argument whose layout is not sized is an error, because "Unsized types do not
have a stable layout, so should not be used with stable ABIs."

**`move_check`** (`move_check.rs`, 209 lines) implements the
`large_assignments` lint. It does nothing when `tcx.move_size_limit().0 == 0`.
That was the observed state without `-Z move-size-limit=N`; the diagnostic
names `#![move_size_limit = "..."]` as the other way to set a limit, and how
the limit query computes its value was not read. Otherwise, over blocks
reachable after monomorphization:

- `visit_operand` flags **any** operand, `Copy` or `Move`, whose monomorphized
  type's layout size exceeds the limit;
- for `Call`/`TailCall` terminators it does not visit the operands generically;
  `check_fn_args_move_size` skips callees that are not `FnDef`, skips
  `Box::new`, `Rc::new` and `Arc::new`, and skips arguments that are
  `Operand::Move` ("Moving args into functions is typically implemented with
  pointer passing at the llvm-ir level and not by memcpy's. So always allow
  moving args into functions."), flagging the rest;
- the lint is dropped silently when the location has no lint root, "when the
  issue is in a function from a foreign crate that we monomorphized in the
  current crate".

The `Operand::Move` exemption is the same codegen fact as in §2, used in the
opposite direction: there it makes a parameter *mutated*, here it makes a large
move *free*.

**Execution.** Each case compiles one file with
`--edition=2021 --crate-type=lib --emit=obj` plus the flags shown.
`Simd256` is `#[repr(simd)] #[derive(Clone, Copy)] pub struct Simd256([u64; 4]);`.

| Case | Executed revision (1.98.0) | Recorded, audited revision (1.102.0) |
| --- | --- | --- |
| Rust-ABI `callee_takes_ymm_rust(v: Simd256) -> Simd256` called from a caller with no features | compiles; IR signature `(ptr … sret([32 x i8]) … %_0, ptr … %v)` | compiles |
| `#[target_feature(enable = "avx2")] pub unsafe extern "C" fn callee_takes_ymm_c(v: Simd256) -> Simd256 { v }` called from a caller with no features | error at the call: `this function call uses SIMD vector type Simd256 which (with the chosen ABI) requires the avx target feature, which is not enabled in the caller` | error at the call: `this function call requires the avx target feature, which is not enabled in the caller`, note `the function has type Simd256 in its signature, which is passed in SIMD vector registers under the "C" ABI` |
| the same callee, caller marked `#[target_feature(enable = "avx")]` | compiles; callee's IR signature is `<4 x i64> (<4 x i64> %v)` | not recorded |
| `pub extern "C" fn definition_takes_ymm_c(v: Simd256) -> Simd256 { v }` with no features | error at the definition: `this function definition uses SIMD vector type Simd256 which (with the chosen ABI) requires the avx target feature, which is not enabled` | not recorded |
| `extern "C"` function taking a 128-bit `#[repr(simd)]` vector, no features | compiles; IR signature `<2 x i64> (<2 x i64> %v)` | not recorded |
| `#![feature(unsized_fn_params)] pub extern "C" fn c_abi_unsized_slice(_s: [u8]) {}` | error: `this function definition uses unsized type [u8] which is not supported with the chosen ABI`, help `only rustic ABIs support unsized parameters` | compilation fails (exit status 1; the preserved diagnostic text is cut off before the error) |
| the same with the Rust ABI | compiles | not recorded |
| `pub fn big_move(src: &[u8; 256]) -> [u8; 256] { let x = *src; x }` with `-Z move-size-limit=64 -D large-assignments` | error: `moving 256 bytes`, label `value moved from here` on `*src` | same error |
| the same without `-Z move-size-limit` | compiles | not recorded |
| `pub fn pass_by_move(b: Big) -> u8 { sink(b) }` (`Big` is 256 bytes), limit 64, `-C opt-level=0` | error: `moving 256 bytes` at the argument `b` | not recorded |
| the same at `-C opt-level=2` | compiles | not recorded |

The last two rows show that the `large_assignments` verdict depends on MIR
optimization. The MIR emitted alongside explains it: at `opt-level=0` the call
is `_0 = sink(copy _1)` (a `Copy` operand, linted, even though the type is not
`Copy` and the source text is a move), and at `opt-level=2` it is
`_0 = sink(move _1)` (exempt). The diagnostic says "moving" in both situations
of the first kind.

The foreign-declaration form `extern "C" { fn f(v: Simd256) -> u64; }` could
not be used for these cases on the executed revision: it is rejected before
monomorphization with `use of SIMD type Simd256 in FFI is highly experimental
and may result in invalid code` and a suggestion to add
`#![feature(simd_ffi)]`. That is a different check. The probe records it as an
observation-only case, with no expectation attached, because the corresponding
source at the audited revision was not read.

### 10. The Lean development

Basis: execution (Lean 4.34.1 kernel check) of `support/DeduceParamAttrsImpossibleClausesAndMonoChecksSoundness.lean`; the correspondence between its definitions and rustc is by inspection (transcription), not mechanized.

**Shape.** One file, 1539 lines, `import Lean` only (used by the audit command),
namespace `DeduceParamAttrs`: 15 inductive or structure types, 78 definitions,
82 theorems, 26 closed `example`s. Checked with

```sh
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  DeduceParamAttrsImpossibleClausesAndMonoChecksSoundness.lean
```

exit status 0.

**What is transcribed from rustc (decision procedures).**

| Lean | rustc counterpart |
| --- | --- |
| `Usage` (four `Bool` fields), `Usage.join`, `Usage.bits`, `Usage.isDefault` | `UsageSummary`, `\|=`, the `u8` encoding, `is_default` |
| `TyFacts` (`needsDrop`, `isFreeze`), `readOnly`, `capturesNone` | `ty.needs_drop`, `ty.is_freeze`, `read_only`, `captures_none` |
| `Use` (10 constructors), `classify` | the rows of the table in §2 |
| `Stmt` (`use p u`, `tailCall p v`), `initUsage`, `summary`, `analyze` | the visitor over a body, the `MUTATE` seed for index 0 |
| `trim`, `lookup`, `lookupAttrs`, `padTo` | the trailing-default loop, `deduced.get(idx)`, absent entries |
| `effectiveAttrs` | the gates of §5 |
| `Ty`, `Clause`, `hasImpossibleClauses`, `hasImpossiblePredicatesLegacy`, `erasePass` | the two tests of §8 at the audited revision, the single test at the executed revision, the pass |
| `passMode`, `usesVectorRegisters`, `requiredFeature`, `checkCallSite`, `checkDefinition` | §9 for x86-64 |

**What is authored here (semantics).** A memory `Nat → Nat` with a set of
"retained" addresses. Each `Use` constructor that can write or leak carries an
adversarial payload: the value written, whether the write happens, whether the
address is retained. `Use.writes` and `Use.escapes` say when a payload takes
effect: drop glue only if `needsDrop`; a write through a shared borrow only if
not `isFreeze`; everything else unconditionally. `applyUse`, `run1` (one
parameter) and `run` (a body, with an address map `ρ` and per-index type facts
`Γ`) execute them. Quantifying over all bodies quantifies over all payloads.
For §8, a body is a function from an instantiation and an argument to
`ret v` or `ub`, and `b'` refines `b` iff `b = ub ∨ b' = b`. For §9, a 256-bit
value is a pair of halves and a register file has `xmm0`, `ymm0hi`, `xmm1`;
with `avx` the high half travels in `ymm0hi`, without it in `xmm1`.

**Headline results** (all 22 depend on no axiom; names as in the file):

| Theorem | Statement, informally |
| --- | --- |
| `deducedReadOnly_no_caller_slot_mutation` | If `ρ` is injective and `readOnly (analyze body q) (Γ q)` holds, then `run ρ Γ body σ` leaves memory at `ρ q` unchanged, for every body and state. |
| `returnPlace_never_readonly` | `readOnly (analyze body 0) t = false` for every body and type. |
| `rmeta_trim_lookup_eq` | `lookupAttrs (trim tbl) i t = lookupAttrs tbl i t` for every table, index and type. |
| `trim_idem`, `trim_padTo`, `padTo_trim_of_canonical` | `trim` is idempotent; `trim (padTo n ys) = trim ys`; and `padTo xs.length (trim xs) = xs` when every default-class entry of `xs` is literally `MUTATE \| CAPTURE`. Together: a bijection between such tables of arity `n` and trimmed tables of length at most `n`. |
| `forwarding_sound_of_deduced_attrs` | With `readOnly` and `capturesNone` deduced for the callee, a caller that passes its own object (`callerForwarded`) observes the same value afterwards as one that passes a fresh copy (`callerReference`), even if the environment later writes through every retained address. |
| `generic_drop_readonly_iff_not_needsDrop` | For the summary `{DROP}`: `readOnly` holds iff `needsDrop = false`, and likewise `capturesNone`. |
| `generic_drop_semantic_exactness` | The body "drop the parameter" preserves the slot for every drop-free type and every payload; for every type with drop glue some payload changes it. |
| `incremental_empty_attrs_sound_coarsening` | The empty table yields no attribute at every index; that is below what any table yields, is sound for every callee, and is what `effectiveAttrs` returns whenever a gate is closed. |
| `hasImpossibleClauses_sound` | A flagged clause list is unsatisfiable at every instantiation. |
| `impossibleClauses_erase_to_unreachable_refines` | `erasePass cs body` refines `body` on every instantiation satisfying `cs`. |
| `erasure_not_refinement_without_clause_precondition` | There are `cs`, `body` and an instantiation violating `cs` at which the erased body is `ub` and the original returns: the clause precondition cannot be dropped. |
| `current_strictly_extends_legacy` | `dyn Trait<T>: Sized` is flagged by the audited-revision test, not by the executed-revision test, and fails at every instantiation. |
| `abiCheck_accepts_implies_vector_transfer_faithful` | If the call-site and definition-site checks accept a 256-bit `extern "C"` argument, the callee receives the value sent. |
| `abiCheck_reject_is_tight` | If the call-site check rejects and the callee uses the wide register, some value arrives corrupted. |
| `ce1_omitting_indirect_call_move_mutate_causes_caller_aliasing_miscompile` | With the `Operand::Move` rule deleted, a callee that forwards its parameter to a writer is deduced `readonly captures(none)`, and `callerForwarded ≠ callerReference`. |
| `ce2_shared_borrow_non_freeze_unsafecell_violates_readonly` | With the `Freeze` test deleted, `&x` on a non-`Freeze` type is deduced `readonly` although the slot is written; the same body at a `Freeze` type preserves the slot. |
| `ce3_return_place_without_mutate_emits_contradictory_writable_readonly` | Without the seed, the empty body gives an `sret` pointer with both `writable` and `readonly`; with the seed the verifier rule is always satisfied. |
| `ce4_extern_c_vector_passMode_direct_without_caller_feature_faults` | `extern "C"`, caller without `avx`, callee with it: the call-site check rejects, the transferred value is wrong, and the same feature sets under the Rust ABI are harmless. |
| `ce5_erasing_on_instantiation_dependent_clause_breaks_valid_instantiation` | A detector that samples one instantiation erases `fn f<T: Copy>` and breaks the well-typed instantiation `T = u32`. |
| `ce6_tail_call_rewrites_slot_of_parameter_that_is_only_read` | A parameter only read by the function's statements is rewritten by a tail call; `analyze` refuses `readonly`. |

Supporting results include the semilattice laws (`join_comm`, `join_assoc`,
`join_idem`, `le_refl`, `le_trans`, `le_antisymm`, `join_least`), the
correspondence with the `u8` encoding (`bits_join : (a.join b).bits = a.bits ||| b.bits`,
`ofBits_bits`, `bits_lt_sixteen`), `readOnly_join` and `capturesNone_join`
(each predicate turns a join into a conjunction, which is what makes a
flow-insensitive summary sufficient), monotonicity in the type facts, and the
frame lemmas.

**Replay of the probe.** Sixteen `example`s evaluate the transcribed rules on
the use lists read off the probe functions' optimized MIR and yield the pairs
in the table of §6 and the return-place and tail-call observations of §2 and
§4. They tie the transcription to executed behaviour on those inputs only.

**Axioms and the audit.** A command at the end of the file enumerates every
constant the module itself declares, collects the axioms each depends on, and
fails elaboration on any of: a dependency on `Classical.choice`, `sorryAx`,
`Lean.ofReduceBool` or `Lean.trustCompiler`; an unsafe, partial, opaque or
axiom declaration; a constant with an `_unsafe_rec` name component; a missing
headline theorem; a headline theorem with a non-empty axiom set. Its output:

```text
AUDIT module-local constants in namespace: 604 (theorems: 182, of which axiom-free: 158; definitions: 356)
AUDIT axioms reachable from any module-local constant, auto-generated ones included: [propext]
AUDIT forbidden axiom names checked: 4 (unknown to the environment: 0); offenders: 0
AUDIT headline theorems required axiom-free: 22; missing: 0; depending on some axiom: 0
AUDIT unsafe recursion companions: module-local (map₂) = 0; imported under this namespace (map₁) = 0 of 0 imported constants under this namespace
AUDIT unsafe/partial/opaque/axiom declarations: 0
```

The counts include compiler-generated constants. Of the 82 written theorems,
two (`Usage.bits_join`, `Usage.ofBits_bits`) depend on `propext`, through
`Nat` bitwise operations in the standard library; so does the definition
`Usage.ofBits`. The other 22 `propext` dependents are generated
constructor-injectivity lemmas that no proof here uses. The source file does
not spell the forbidden identifiers anywhere (its audit assembles them from
string fragments), so a text search of it for them finds nothing; the check
that matters is the one on the environment.

Two negative controls were run: removing `noncomputable` from one recursive
definition, and replacing one proof by an admitted goal. Both mutated files
were rejected, by the companion check and the axiom check respectively.

**Two facts about Lean 4.34.1 that this file had to accommodate.** Both were
found by the audit failing, and both generalize to any development that wants
the same guarantees.

- *Every compiled recursive definition gets an unsafe companion.* A plain
  structurally recursive `def f : List Nat → Nat` produces a constant
  `f._unsafe_rec`; twelve such companions appeared in the first version of
  this file. Marking the definition `noncomputable`, or writing it without
  self-reference through a library fold such as `List.foldr`, produces none,
  and kernel evaluation by `rfl` and `decide` still works. The companion is a
  code-generation artefact and not part of any proof, but a "no `_unsafe_rec`
  constants" requirement can only be met by avoiding compiled recursion. So the
  cause is not specific to `deriving` handlers; those were not tested on
  recursive types here (the file derives `DecidableEq` only on non-recursive
  structures, which produced no companion).
- *The constants of the file being elaborated are in `env.constants.map₂`.*
  `map₁` holds imported constants. An inspection of `map₁` alone reports zero
  for any property of the current file, vacuously. The audit reports both and
  enforces on `map₂`.

A third, smaller one: a `match` with a catch-all arm over an inductive type
elaborates through an auxiliary (`…._sparseCasesOn_…`) that depends on
`propext`; writing out every constructor avoids it.

**What the model does not cover.** Control flow (the summary is
flow-insensitive, and so is the model); places finer than "the parameter";
layouts; provenance; concurrency; unwinding; the trait solver beyond a
two-trait toy environment; clause elaboration, error taint and the
`HAS_CONST_ALIAS` filter; any ABI or architecture other than a schematic
x86-64; scalable vectors; LLVM itself. The register file in the vector model
is illustrative: the theorems use only that the two conventions disagree about
where the high half lives, and no claim is made that LLVM assigns registers
this way.

### 11. Position relative to Anneal's trusted MIR semantics

Basis: source (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/lean/Trusted/MirSemantics.lean`) + derived.

That file defines a small-step semantics for a MIR fragment. Three
of its stated properties determine how the mechanisms above relate to it:

- Its documentation states, under "Interprocedural calls fail closed",
  that "any reachable `TerminatorKind.call` steps to `.fault .unsupported`",
  and under "Value-only entry memory" that verification statements "quantify
  over value arguments `args : List Val` paired with empty caller memory …
  while pointer and reference entry parameters remain outside the supported
  domain". Arguments are values; there is no caller-provided slot for a
  by-value parameter.
- "`Operand.move` deliberately and conservatively deinitializes non-ZST local
  storage upon evaluation".
- Executing `TerminatorKind.unreachable` is classified as
  `FaultKind.undefined`.

Derived consequences:

1. **Deduced attributes are entirely below this semantics.** They concern
   whether a callee writes or leaks the *address* of an indirect by-value
   parameter. The semantics has neither that address nor calls, so no statement
   proved against it constrains, or is constrained by, `readonly` or
   `captures(none)`. Their soundness rests on rustc's visitor being right about
   optimized MIR and on codegen not transforming MIR afterwards (§3); it is
   part of the trusted base of any conclusion about the compiled program.
2. **The move rule is compatible in spirit.** Treating a moved-from local as
   deinitialized is the source-level counterpart of the codegen fact that a
   moved call argument's slot now belongs to the callee. A semantics that let
   the caller keep reading a moved-from by-value argument would be assuming
   something the `Operand::Move` rule exists to deny.
3. **Erasure changes what "the MIR of the function" is.** For an item with
   impossible clauses, every MIR obtained at or after
   `mir_drops_elaborated_and_const_checked` is a lone `unreachable`, which
   this semantics classifies as UB on every execution, while MIR obtained
   earlier is the body the programmer wrote. A statement such as "this
   function has no UB" is therefore true of one and false of the other. Both
   readings are harmless for whole programs, since the function cannot be
   called, but a tool that reports per-function results has to choose. Which
   MIR stage Anneal's extraction consumes was not determined here.

## Boundaries

**Not examined**

- Any target other than `x86_64-unknown-linux-gnu`; any backend other than
  LLVM; stable and beta toolchains.
- Closures, coroutines, async functions, trait-object method instances and
  compiler-generated shims. The source says only `InstanceKind::Item` instances
  receive deduced attributes; how closure and coroutine bodies fare in the
  provider (for example with respect to `spread_arg`) was not traced.
- The `rust-call`, `rust-cold` and tail-call (`RustTail`) ABIs.
  `adjust_for_rust_abi` gives tail-ABI arguments `pass_by_stack_offset`; the
  interaction with `apply_deduced_attributes`, which matches any
  `PassMode::Indirect` mode, was not examined.
- `Yield` resume places, `SetDiscriminant`, `AsmOutput`, drops of projections
  and places whose first projection is `Deref`: read in source, not executed.
- The bail-outs of §3 other than optimization level and `-C incremental`.
- Scalable vectors, the `vectorcall` rule, homogeneous-aggregate unit sizes,
  and every architecture's feature table except x86's first three entries.
- `#![move_size_limit]` as an attribute, `Box::new`/`Rc::new`/`Arc::new`
  exemptions, the missing-lint-root path, and deduplication by span.
- Erasure triggered by `tainted_by_errors`, by `references_error`, through
  tuple tails, ADT sizedness constraints or foreign types; promoted constants;
  the LLVM IR produced for an erased body.
- Whether LLVM 23.1.5 performs the forwarding of §7 (observed only with LLVM
  22.1.6), and every other LLVM consumer of `readonly`/`captures(none)`.
- The files changed at head (`rustc_codegen_llvm/src/abi.rs`,
  `rustc_target/src/callconv/mod.rs`, `rustc_codegen_ssa/src/mir/block.rs`)
  beyond confirming that the quoted lines still exist.

**Unknown**

- Whether the full probe produces zero mismatches on the audited revision. The
  expectations were derived from that revision's source, but only the recorded
  subset (16 comparable observations) was executed there, by a probe whose
  sources are not preserved.
- Which MIR stage Anneal's extraction reads (§11).
- Whether `is_freeze` coincides exactly with the Reference's notion of
  "contains an `UnsafeCell`" in every corner (for example through generic
  parameters at the call site); assumed, not audited.
- Whether the issue referenced by the `FIXME` in `check_call_site_abi` has
  consequences beyond scalable vectors.

**Known not to apply**

- Deduced attributes do not apply to non-rustic ABIs, to non-`Item` instances,
  or to parameters that are not `PassMode::Indirect` (§4).
- The call-site vector check does not apply to rustic ABIs (§9); the
  definition-site check does.
- On the executed revision the structural `Sized` erasure does not apply
  (§8).
- `-C incremental` does not merely weaken the deduction: with any gate closed
  no deduced attribute is emitted at all (§5).

**Unsupported**

- rustc states that "Arguments spread at ABI level are currently unsupported"
  for deduction, and that unsized parameters are unsupported on non-rustic
  ABIs.

**Attractive conclusions the evidence does not establish**

- *"The Lean proof shows rustc's deduction is sound."* It shows the
  transcribed rules are sound and sharp against a memory model written for the
  purpose. Fidelity of the transcription, and of the model to LLVM and to
  Rust's operational semantics, is argued in prose and spot-checked by
  execution, not proved.
- *"`readonly` and `writable` together are undefined behaviour."* LLVM's
  verifier rejects the combination; the module is malformed, which is a
  different failure.
- *"A 256-bit vector needs `avx2`."* The table says `avx`.
- *"The lowering to LLVM attributes happens in `rustc_codegen_ssa`."* It
  happens in `rustc_ty_utils/src/abi.rs` and `rustc_codegen_llvm/src/abi.rs`;
  `rustc_codegen_ssa/src/mir/mod.rs` only requests the resulting ABI and
  carries the "no MIR transforms after this" comment.
- *"Only the defining crate's flags matter across crates."* The using crate's
  flags gate consumption independently.
- *"Moves into call arguments are never linted by `large_assignments`."* Only
  operands that are `Operand::Move` in optimized MIR are exempt.
- *"A `define` line with `readonly` shows rustc deduced it."* Under the normal
  pipeline LLVM infers attributes on definitions itself.
- *"Erased bodies are an optimization."* Erasure happens at every optimization
  level and is a semantic precondition for later passes ("it even makes sense
  to try to evaluate the body"), not a size or speed measure.

## Evidence

All evidence was acquired on 2026-11-22. Every commit identifier in this report
was resolved on that date through the GitHub REST API
(`GET /repos/<owner>/<repo>/commits/<ref>`); `head` is what the default branch
of `rust-lang/rust` resolved to, the Reference revision is what its default
branch resolved to, and the Lean revision is what the tag `v4.34.1` resolved
to. The two LLVM revisions are the `src/llvm-project` submodule entries of the
audited and executed rustc revisions (`GET …/contents/src/llvm-project?ref=…`),
each then confirmed as a commit; their `cmake/Modules/LLVMVersion.cmake` give
23.1.5 and 22.1.6, matching the version strings the two compilers print. Files
were read from `raw.githubusercontent.com` at those commits.

### Source, `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`

| Path | Lines | Used for |
| --- | --- | --- |
| `compiler/rustc_middle/src/middle/deduced_param_attrs.rs` | 1–80 | §1 |
| `compiler/rustc_mir_transform/src/deduce_param_attrs.rs` | 1–10, 24–45, 48–100, 102–149, 153–168, 177–242 | §2, §3 |
| `compiler/rustc_ty_utils/src/abi.rs` | 298–316, 643–693 | §4 |
| `compiler/rustc_middle/src/ty/mod.rs` | 2359–2385 | §5 consumer gate |
| `compiler/rustc_middle/src/queries.rs` | 1803–1835, 2754–2757 | query documentation for the two ABI queries and `deduced_param_attrs` |
| `compiler/rustc_metadata/src/rmeta/encoder.rs` | 2008–2023 | §5 encoder gate |
| `compiler/rustc_metadata/src/rmeta/decoder/cstore_impl.rs` | 294–307 | §5 decoder default |
| `compiler/rustc_target/src/callconv/mod.rs` | 41–92, 133–146, 425–446, 756–931 | §4, §9 |
| `compiler/rustc_codegen_llvm/src/abi.rs` | 42–115, 527–592 | §4 |
| `compiler/rustc_codegen_ssa/src/mir/mod.rs` | 212–216 | §3 |
| `compiler/rustc_codegen_ssa/src/mir/block.rs` | 1260–1306, 1363–1412, 2030–2040 | §2 |
| `compiler/rustc_mir_transform/src/impossible_clauses.rs` | 1–121 | §8 |
| `compiler/rustc_mir_transform/src/lib.rs` | 608–652, 802–833 | §8 |
| `compiler/rustc_mir_transform/src/inline.rs` | 45–62 | §5 |
| `compiler/rustc_trait_selection/src/traits/mod.rs` | 856–883 | §8 |
| `compiler/rustc_monomorphize/src/mono_checks/mod.rs` | 1–19 | §9 |
| `compiler/rustc_monomorphize/src/mono_checks/abi_check.rs` | 1–323 | §9 |
| `compiler/rustc_monomorphize/src/mono_checks/move_check.rs` | 1–209 | §9 |
| `compiler/rustc_monomorphize/src/collector.rs` | 1329–1340 | §9 |
| `compiler/rustc_monomorphize/src/diagnostics.rs` | 28–37, 104–207 | diagnostic wording |
| `compiler/rustc_target/src/target_features.rs` | 1172–1173, 1260–1284 | §9 |
| `tests/codegen-llvm/deduced-param-attrs.rs` | 1–173 | upstream test with the same shape as §6 (uses `-Copt-level=3 -Cno-prepopulate-passes`); independent confirmation of the intended behaviour for `Copy` vs `Move` call arguments, shared borrows, raw borrows, drops and return places |

Six of these files are preserved unmodified under
`support/upstream/rust-lang-rust-3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1/`.

### Source, `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`

`compiler/rustc_mir_transform/src/impossible_predicates.rs` (lines 39–77) and
`compiler/rustc_mir_transform/src/deduce_param_attrs.rs` (preserved under
`support/upstream/`), plus the corresponding regions of
`rustc_ty_utils/src/abi.rs` (647–697), `rustc_middle/src/ty/mod.rs` (2241–2252),
`rustc_metadata/src/rmeta/encoder.rs` (1879–1892),
`rustc_monomorphize/src/mono_checks/{abi_check.rs,move_check.rs}`,
`rustc_monomorphize/src/errors.rs`, `rustc_target/src/callconv/mod.rs`
(401–415), `rustc_target/src/target_features.rs` (998–999) and
`rustc_mir_transform/src/{lib.rs,inline.rs}`, each compared with the audited
revision.

### Source, other subjects

- `rust-lang/llvm-project@0a5579eb649d3634a9c30ac873300cc2944fa070`:
  `llvm/docs/LangRef.md` (entries `captures(...)` from line 1538, `readonly`
  from line 1797, `writable` from line 1815); `llvm/lib/IR/Verifier.cpp`
  (lines 2143–2149); `llvm/lib/Transforms/Scalar/MemCpyOptimizer.cpp`
  (`processImmutArgument` and its doc comment, lines 2088–2189, and its call
  site near line 2223).
- `rust-lang/llvm-project@08c84e69a84d95936296dfcab0e38b34100725d5`:
  `llvm/lib/Transforms/Scalar/MemCpyOptimizer.cpp`, the first two conditions of
  `processImmutArgument` (from line 2032).
- `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`:
  `src/trait-bounds.md` (rules `bound.trivial`, `bound.special`);
  `src/behavior-considered-undefined.md` (rules `undefined.alias`,
  `undefined.immutable`); `src/interior-mutability.md` (rule
  `interior-mut.unsafe-cell`).
- `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:
  `trusted/lean/Trusted/MirSemantics.lean` (documentation comments near lines
  60–91 and 1686–1693, `evalOperandToSlot` near lines 916–976).

### Execution in this investigation

- Compiler: `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, commit hash
  `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, host `x86_64-unknown-linux-gnu`,
  LLVM 22.1.6.
- Probe: `support/probe_deduce_param_attrs_impossible_clauses_and_mono_checks.py`.
  It writes the embedded Rust sources into a temporary directory, runs
  `rustc`, and parses `define`/`declare` lines, MIR and diagnostics. Nothing in
  its result is hard-coded: the expectation tables are compared with the
  observations and every mismatch is reported.
- Result: `support/results/local_rustc-1.98.0-nightly-14210df0e.json`.
  9 matrix configurations with 175 expectation checks (0 mismatches); 2
  auxiliary crates with 3 checks (0 mismatches); 20 single-crate cases, of
  which 19 carry an expectation (1 mismatch: the `dyn MyTrait<T>: Sized` case,
  explained by the executed revision's source) and 1 is observation-only;
  3 IR-signature cases. A second run produced a
  byte-identical file. With `--strict` the probe exits 1 on this toolchain
  because of that one mismatch.
- Specimens: the Rust sources (`support/specimens/rust/`) and the optimized MIR
  of the upstream and auxiliary crates (`support/specimens/mir/`).
- Lean: `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit
  5045d0056413266e57c625dcd7c365b10e377c52, Release)`; transcript in
  `support/lean_check_transcript.txt`, including the two negative controls.

### The recorded execution at the audited revision

`support/results/recorded_rustc-1.102.0-nightly-3ef0c22cd.json` was produced
before, and independently of, this investigation, by a smaller probe whose
Rust sources were not kept; only raw IR signature lines and diagnostics are in
it. It is used as corroboration, with these limits:

- It cannot be re-run here, and the sources in this package are
  reconstructions. They match every detail the record exposes: function names,
  parameter sizes visible in the IR, the MIR signatures of the two erased
  functions, and the line and column of each recorded diagnostic. Details the
  record does not expose may differ. Agreement is therefore agreement on
  comparable inputs, not a byte-level replay.
- For the `extern "C"` vector case there is a visible discrepancy: the
  reconstruction, run on the executed revision, prints two
  `improper_ctypes_definitions` warnings before the error, and the record shows
  none. Whether the recorded source declared the callee differently or the lint
  differs between the two revisions is unknown. The error itself, its span and
  the required feature (`avx`) agree.
- Only `declare` lines are compared for the attribute matrix (10 comparable
  entries, all equal to the local run; 2 entries for the generic function have
  no `declare` line). Its `define` lines were produced under the normal LLVM
  pipeline and are not evidence of rustc's deduction (§6).
- Its configuration named `opt2_incremental` shows no deduced attribute on any
  declaration, which by §5 is consistent with either crate, or both, having
  been built incrementally; the record does not say which.

Four version-specific details make it credible as an execution of a compiler at
the audited revision rather than at the executed one: its IR carries `nofree`
on indirect parameters, which only the audited revision's
`indirect_pass_mode` sets; its vector diagnostic has the audited revision's
wording, which differs from what the executed revision printed here; its
`dyn MyTrait<T>: Sized` body is erased, which only the audited revision's
source produces; and its LLVM version string matches the vendored LLVM of the
audited revision.

### Expectations that execution refuted during this investigation

These are recorded because each was a plausible reading of part of the source
that turned out to be incomplete:

1. *Cross-crate attributes depend only on the defining crate.* Refuted by the
   downstream-incremental configuration; the consumer gate in
   `TyCtxt::fn_abi_of_instance` was found afterwards.
2. *Moving a large value into a call is never linted.* Refuted at
   `opt-level=0`, where the optimized MIR has a `Copy` operand.
3. *A read-only, non-capturing callee always lets LLVM forward the caller's
   object.* Refuted for the variant that reads the source again after the call.
4. *`extern "C" { fn f(v: Simd256) -> u64; }` reaches the
   post-monomorphization check.* On the executed revision it is rejected
   earlier by the `simd_ffi` gate.

## Revalidation

In increasing order of cost. Each check establishes only what it checks.

1. **Have the rules changed?** Diff
   `compiler/rustc_mir_transform/src/deduce_param_attrs.rs` and
   `compiler/rustc_middle/src/middle/deduced_param_attrs.rs` against the
   copies under `support/upstream/`. Any change to the `match` in
   `visit_place`, to `visit_terminator`, to the seed in `new`, or to
   `read_only`/`captures_none` invalidates §1–§2 and the Lean transcription.
2. **Have the gates changed?** Search for `incremental.is_none()` and
   `incremental.is_some()` in `deduce_param_attrs.rs`,
   `rustc_metadata/src/rmeta/encoder.rs` and the body of
   `TyCtxt::fn_abi_of_instance` in `rustc_middle/src/ty/mod.rs`. One test in
   each of those three places is the state described in §5.
3. **Has erasure changed?** Diff
   `compiler/rustc_mir_transform/src/impossible_clauses.rs` (or, on older
   trees, `impossible_predicates.rs`) against the preserved copies; check that
   it is still the first entry of `run_analysis_cleanup_passes`.
4. **Have the mono checks changed?** Diff `mono_checks/abi_check.rs` and
   `mono_checks/move_check.rs` against the preserved copies, and the x86 entry
   `X86_FEATURES_FOR_CORRECT_FIXED_LENGTH_VECTOR_ABI` in
   `rustc_target/src/target_features.rs`.
5. **Run the probe** on the toolchain of interest (a nightly on x86-64 Linux):

   ```sh
   python3 support/probe_deduce_param_attrs_impossible_clauses_and_mono_checks.py \
     --rustc "$(rustup which --toolchain nightly rustc)" \
     --baseline support/results/recorded_rustc-1.102.0-nightly-3ef0c22cd.json \
     --out /tmp/probe_results.json --strict
   ```

   It takes a few seconds. Read `summary.total_prediction_mismatches`,
   `summary.build_failures` and `baseline_comparison.different_count` in the
   output. Expected on a toolchain at the audited revision: zero mismatches
   (not yet observed with this probe). Known on 1.98.0-nightly: exactly one,
   in case `impossible_02_generic_dyn_trait_sized_erased_to_unreachable`. A
   build failure of the auxiliary crates means the unstable `custom_mir` or
   `explicit_tail_calls` surface moved, not that a finding changed. The single
   most discriminating observation is `matrix.<config>.forwarding_witness`:
   `observed_forwarded` should be true only for `opt2_non_incr`.
6. **Re-check the Lean file** with Lean 4.34.1:

   ```sh
   bash support/lean_check.sh "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
   bash support/lean_audit_negative_controls.sh "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
   ```

   Exit status 0 from the first and two "rejected as expected" lines from the
   second reproduce §10. On another Lean version the proofs may need
   adjustment; the audit's use of `env.constants.map₂` and `collectAxioms` is
   the part most likely to need attention.
7. **If a rule did change**, the Lean file must be re-transcribed by hand:
   update `classify`, `readOnly`, `capturesNone` or `hasImpossibleClauses` to
   match, re-run the check, and replace the sixteen replay `example`s with
   the new probe observations. There is no cheaper way to keep the model in
   step with the compiler.
