# rustc function-entry instrumentation attributes (XRay, mcount) and coverage levels (block, branch, condition): attribute overwrite, macro branch erasure, negation polarity and condition diamonds

## Summary

Two independent `rustc` instrumentation mechanisms are characterised, each from
upstream source at pinned commits, from execution of a real nightly toolchain,
and from a kernel-checked Lean model.

**Function-entry instrumentation (`-Z instrument-xray`, `-Z instrument-mcount`,
`#[instrument_fn = "on" | "off"]`).**

- In `rust-lang/rust` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` and at
  `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`, the XRay branch of
  `instrument_function_attr` keeps two independent booleans. `#[instrument_fn =
  "off"]` sets `never` without clearing `always`, `#[instrument_fn = "on"]` sets
  `always` without clearing `never`, and `"function-instrument"="xray-never"` is
  pushed before `"function-instrument"="xray-always"`. `rustc` hands the pushes
  to one LLVM `AttrBuilder`, which keeps one value per string key and lets the
  last add win. Consequence (source + derived): under `-Z instrument-xray=always`
  a function marked `#[instrument_fn = "off"]` carries
  `"function-instrument"="xray-always"`. That is the only one of the nine
  (command line, attribute) combinations that departs from "the attribute
  overrides the command line"; `on` under `-Z instrument-xray=never` is correct
  only because of the push order.
- Execution: the toolchain that was run (`rustc 1.98.0-nightly`, commit
  `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) predates `#[instrument_fn]` and
  rejects it. On that toolchain the push sequence
  `[xray-never, xray-always]` was given to the toolchain's own compiled
  `LLVMRustAddFunctionAttributes` and to its `llvm-as`/`llc`: the surviving
  attribute is `xray-always`, and the function gets an entry sled, an exit sled
  and four `R_X86_64_PC64` relocations in `xray_instr_map`. **No compiler that
  accepts `#[instrument_fn]` was run**, so the end-to-end behaviour at the two
  later commits is a source-derived conclusion, not an observation.
- The mcount/fentry branch of the same function tests the attribute directly
  (`Some(Off) => false`) and has no such overwrite.
- Derived hazard: an XRay handler that calls a helper it expected to be excluded
  re-enters itself without bound if the sleds are patched and the handler has no
  re-entrancy guard. This was modelled, not run.

**Coverage (`-C instrument-coverage -Z coverage-options=block|branch|condition`)**,
observed end to end on commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and
source-identical in the deciding logic at the two later commits.

- Branch regions are emitted only for conditions whose expression span has the
  same syntax context as the function body, and only if that context is the
  root (non-expansion) context. A condition written in a `macro_rules!` body
  gets no branch region; a function whose whole body comes from a macro gets
  none at all, while its code regions are still reported and executed. A
  condition whose tokens are written at the macro call site keeps its branch
  region.
- `condition` does not produce MC/DC records. It adds, for the right operand of
  a lazy boolean (`&&`, `||`) evaluated as a value, a four-block diamond over
  the already computed boolean and one more two-way branch region. `mcdc` is not
  an accepted level.
- For `if !^k e` the single branch region spans the outermost `!`, and its true
  count is the number of runs in which the whole expression is true, for
  `k = 1, 2, 3`.
- A `#[coverage(off)] #[inline(always)]` callee has no function record, no
  counter and no region, also after inlining at `-C opt-level=2`.

**Lean.** A prelude-only Lean 4.34.1 module proves the "last push wins" law of
the builder, the exact disagreement set of the two-boolean encoding for either
push order, agreement of a three-valued repair, non-termination of the modelled
handler, the erasure rule and its loss accounting, polarity of `!` chains for
every `k`, and flow conservation of the diamond. It is a hand-written model of
the quoted source, not an extraction from `rustc`.

**Verification boundary.** In `joshlf/anneal` at
`c131b320eeeb26ef692e5afd5ec8db49ee518613`, a MIR `Coverage` statement is in the
unsupported bucket of the MIR statement type, and executing an unsupported
statement faults. XRay and mcount instrumentation is selected below MIR, through
LLVM function attributes, and is not visible in MIR at all.

## Applicability

**Subjects and how they relate.**

| Subject | Identity | Role here |
| :--- | :--- | :--- |
| `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (committed 2026-05-31, `src/version` 1.98.0) | The commit of the nightly toolchain that was executed (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, LLVM 22.1.6). Its source was also read. It has no `#[instrument_fn]`. |
| `rust-lang/rust` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (committed 2026-11-11, `src/version` 1.102.0) | Source read only. Has `#[instrument_fn]`. |
| `rust-lang/rust` | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (head of the default branch `main` on 2026-11-22, `src/version` 1.102.0) | Source read only. Has `#[instrument_fn]`; the code under study is unchanged from the previous row. |
| LLVM | release tag `llvmorg-22.1.6` of `llvm/llvm-project` (source read); the LLVM 22.1.6 tools shipped in the executed toolchain (executed) | Attribute builder, XRay machine pass, sled and table emission. |
| LLVM | release tag `llvmorg-23.1.5` of `llvm/llvm-project` (source read only) | Representative of the 23.1 line that the two later `rust-lang/rust` commits name in `.gitmodules` (`branch = rustc/23.1-2026-07-22`). |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Source read only: how its MIR statement type classifies `Coverage` statements. |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (tag `v4.34.1`) | The checker that elaborated and kernel-checked the Lean module. |

The report is about `rustc` as interpreted through LLVM: `rustc` chooses string
attributes, LLVM decides what they mean. The Lean module and the `joshlf/anneal`
commit are not consumers of each other; the Lean module imports nothing.

**Which statements hold for which commit.**

- `#[instrument_fn]` findings apply to the two later `rust-lang/rust` commits
  only. The attribute was added by `rust-lang/rust` pull request 157681, merged
  through rollup 157999 on 2026-06-17, after the executed commit. The executed
  toolchain answers `#![feature(instrument_fn)]` with
  ``error: cannot find attribute `instrument_fn` in this scope``.
- `-Z instrument-mcount=fentry` exists at the two later commits only; at the
  executed commit `instrument_mcount` is a plain boolean option.
- The command-line behaviour of `-Z instrument-xray` (`always`, `never`, bare),
  the LLVM attribute builder law, and all coverage findings were observed on the
  executed commit. They are extended to the two later commits by source
  comparison: the option parser arms, `AddAttributes`, the `Root` test in
  `extract_branch_mappings`, the bucketing loop in `expansion.rs`,
  `visit_with_not_info`, `visit_coverage_branch_condition` and
  `visit_coverage_standalone_condition` are the same code up to renames
  (`CoverageInfoHi` became `CoverageEarlyInfo`, `ExprKind::Use` became
  `ExprKind::ValueExpr`, `then_block`/`else_block` became
  `true_block`/`false_block`, `then_else_break_inner` became
  `lower_if_condition`). That extension is derived; the later commits were not
  executed.

**Configuration of the executed observations.** Host and target
`x86_64-unknown-linux-gnu`, ELF objects, `--edition 2021`. Instrumentation
attribute runs: `-C opt-level=2 -C codegen-units=1`, library crate, object and
LLVM IR emitted, not linked. Coverage runs: `-C codegen-units=1
-C symbol-mangling-version=v0`, at `-C opt-level=0` and `-C opt-level=2`,
linked, run once, profile merged with `llvm-profdata`, read with `llvm-cov
export`. Sled byte patterns and relocation types are specific to x86-64 ELF.

## Findings

### 1. LLVM keeps one value per string attribute key; the last add wins

Basis: source (LLVM, both tags) + execution (LLVM 22.1.6).

`llvm/lib/IR/Attributes.cpp`, tag `llvmorg-22.1.6`, lines 2120-2136 (the same
text at tag `llvmorg-23.1.5`, lines 2176-2192):

```cpp
template <typename K>
static void addAttributeImpl(SmallVectorImpl<Attribute> &Attrs, K Kind,
                             Attribute Attr) {
  auto It = lower_bound(Attrs, Kind, AttributeComparator());
  if (It != Attrs.end() && It->hasAttribute(Kind))
    std::swap(*It, Attr);
  else
    Attrs.insert(It, Attr);
}

AttrBuilder &AttrBuilder::addAttribute(Attribute Attr) {
  if (Attr.isStringAttribute())
    addAttributeImpl(Attrs, Attr.getKindAsString(), Attr);
```

An attribute whose key is already present replaces the stored one. The textual
IR parser reaches the same function through `AttrBuilder::addAttribute(StringRef,
StringRef)` (`llvm/lib/AsmParser/LLParser.cpp` line 2001 at `llvmorg-22.1.6`).

`rustc` applies function attributes through one builder
(`compiler/rustc_llvm/llvm-wrapper/RustWrapper.cpp`, lines 387-396 at the two
later commits, lines 493-502 at the executed commit, identical text):

```cpp
template <typename T>
static inline void AddAttributes(T *t, unsigned Index, LLVMAttributeRef *Attrs,
                                 size_t AttrsLen) {
  AttributeList PAL = t->getAttributes();
  auto B = AttrBuilder(t->getContext());
  for (LLVMAttributeRef Attr : ArrayRef<LLVMAttributeRef>(Attrs, AttrsLen))
    B.addAttribute(unwrap(Attr));
  AttributeList PALNew = PAL.addAttributesAtIndex(t->getContext(), Index, B);
  t->setAttributes(PALNew);
}
```

`LLVMRustAddFunctionAttributes` calls it, and `llfn_attrs_from_instance`
collects all attributes of a function into one `to_add` vector, in source order,
and passes it in one call (`compiler/rustc_codegen_llvm/src/attributes.rs`,
lines 542 and 721 at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`).

Execution on the 1.98.0-nightly toolchain, two routes, same result in all 27
cells of the replay described in finding 4:

- the toolchain's compiled `LLVMRustAddFunctionAttributes` (not exported; its
  address is taken from the ELF symbol table of `librustc_driver`) called with
  `[xray-never, xray-always]` leaves `xray-always`; with
  `[xray-always, xray-never]` it leaves `xray-never`;
- `llvm-as` followed by `llvm-dis` on an attribute group written as
  `"function-instrument"="xray-never" "function-instrument"="xray-always"`
  prints one `"function-instrument"="xray-always"`.

### 2. How LLVM interprets the surviving attribute

Basis: source (LLVM) + execution.

`llvm/lib/CodeGen/XRayInstrumentation.cpp`, `XRayInstrumentation::run`
(`llvmorg-22.1.6` lines 205-254; the same decision code at `llvmorg-23.1.5`
from line 203):
`"function-instrument"="xray-always"` instruments the function without
consulting the threshold; `"xray-never"` returns early; with neither, the
function is instrumented only if `"xray-instruction-threshold"` is present and
the machine-instruction count reaches it or the function has a loop (unless
`"xray-ignore-loops"`). `rustc` always pushes the threshold (default 200).

Observed on x86-64 (`rustc -Z instrument-xray=always`, and the same bytes from
`llc`): an entry sled `eb 09` + `66 0f 1f 84 00 00 02 00 00` (disassembled as
`jmp 0xb` then `nopw 0x200(%rax,%rax)`), and after each return an exit sled
`c3` + `2e 66 0f 1f 84 00 00 02 00 00` (`retq` then `nopw %cs:0x200(%rax,%rax)`).
Each instrumented function gets its own `xray_instr_map` section
(`SHF_LINK_ORDER`, linked to the function's text section) holding one entry
per sled, and each entry starts with two PC-relative words (sled address,
function address; `AsmPrinter::emitXRayTable`, `llvm/lib/CodeGen/AsmPrinter/AsmPrinter.cpp`
lines 4818-4906 at `llvmorg-22.1.6`), which appear as two `R_X86_64_PC64`
relocations against `.text.<function>`. A function with one return therefore
shows four such relocations, a function with two returns six.

### 3. The XRay selection code once `#[instrument_fn]` exists

Basis: source.

`compiler/rustc_codegen_llvm/src/attributes.rs`, function
`instrument_function_attr(cx, sess, instrument_fn: Option<InstrumentFnAttr>)`:
lines 264-356 at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (XRay block
311-354) and lines 268-360 at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (XRay
block 315-358). The two versions differ only in the Rust type of an LLVM
attribute handle. Lines 316-335 at the first of these commits:

```rust
        let mut never = options.never;
        let mut always = options.always;

        // always and never may be overridden by the #[instrument_fn = ...] attribute.
        match instrument_fn {
            Some(InstrumentFnAttr::On) => {
                always = true;
            }
            Some(InstrumentFnAttr::Off) => {
                never = true;
            }
            None => {}
        }

        if never {
            attrs.push(llvm::CreateAttrStringValue(cx.llcx, "function-instrument", "xray-never"));
        }
        if always {
            attrs.push(llvm::CreateAttrStringValue(cx.llcx, "function-instrument", "xray-always"));
        }
```

`options` is the parsed `-Z instrument-xray` value, a struct `InstrumentXRay {
always: bool, never: bool, ignore_loops, instruction_threshold, skip_entry,
skip_exit }`. `InstrumentFnAttr` is `On | Off`, parsed from the name-value
attribute `#[instrument_fn = "on"]` / `#[instrument_fn = "off"]`
(`compiler/rustc_attr_parsing/src/attributes/codegen_attrs.rs`, lines 658-693),
allowed on free functions, inherent methods, trait methods with a body and
trait-impl methods, behind `#![feature(instrument_fn)]`
(`compiler/rustc_feature/src/unstable.rs` line 609, issue 157081 of
`rust-lang/rust`), and stored in `CodegenFnAttrs::instrument_fn`.

The source comment states the intent ("may be overridden by the
`#[instrument_fn = ...]` attribute"), and so does the comment where the
attribute is registered (`compiler/rustc_feature/src/builtin_attrs.rs`, lines
230-234 at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`: "to insert or inhibit
instrumentation function calls inside a function"; at the later commit that
list no longer carries per-entry comments). Neither arm clears the opposite
boolean.

Combining this with findings 1 and 2 (derived; rows are the command line,
columns the attribute; the entry is the surviving `"function-instrument"` value,
`-` meaning none, so that the threshold heuristic decides):

| command line | no attribute | `#[instrument_fn = "on"]` | `#[instrument_fn = "off"]` |
| :--- | :--- | :--- | :--- |
| `-Z instrument-xray` | - | `xray-always` | `xray-never` |
| `-Z instrument-xray=always` | `xray-always` | `xray-always` | **`xray-always`** (pushes `[xray-never, xray-always]`; intended `xray-never`) |
| `-Z instrument-xray=never` | `xray-never` | `xray-always` (pushes `[xray-never, xray-always]`) | `xray-never` |

The bold cell is the only disagreement with "attribute overrides command line".
The `on`-under-`never` cell is right only because `xray-always` happens to be
pushed second. With the opposite order (which is the order the pre-attribute
code used, see finding 5) the disagreement moves to that cell instead. No order
of two independent pushes is correct in both.

### 4. LLVM-level replay of the nine cells (executed), and its limits

Basis: derived push sequences + execution of LLVM 22.1.6 from the executed
toolchain.

`support/probe_xray_attr_overwrite_and_coverage_modes.py` contains a Python
transliteration of the code quoted in finding 3 (and of two variants), computes
the push sequence of each cell, and for each cell (a) calls the toolchain's
compiled `LLVMRustAddFunctionAttributes` with that sequence and (b) writes the
pushes, in order, into the attribute group of a three-instruction function,
assembles it with `llvm-as`, reads it back with `llvm-dis`, compiles it with
`llc -O2 -filetype=obj -function-sections`, and reads sleds and relocations with
`llvm-objdump -d -r` and `llvm-readobj -r`. Results
(`support/probe_results_rustc_1_98_0_nightly_14210df0e.json`, key
`part_a3_llvm_level_replay`):

| variant | cells whose surviving attribute differs from "attribute overrides command line" |
| :--- | :--- |
| two booleans, `xray-never` pushed first (finding 3) | `cli=always,attr=off` only |
| two booleans, `xray-always` pushed first | `cli=never,attr=on` only |
| one three-valued mode (finding 8) | none |

In the `cli=always,attr=off` cell of the first variant the tools report: pushes
`["xray-never", "xray-always"]`, surviving attribute `xray-always` by both
routes, 1 entry sled, 1 exit sled, first instructions `jmp 0xb
<replay_target+0xb>` / `nopw 0x200(%rax,%rax)`, 4 `R_X86_64_PC64` relocations in
`xray_instr_map`. In every cell with surviving `xray-never` (and in the
no-attribute threshold cell, where the tiny function is below the threshold)
the tools report 0 sleds and 0 relocations.

Limits. The push sequences are computed from the quoted source by a script, not
by the compiler that contains that source. The replay establishes what LLVM
22.1.6 does with a given sequence and that the compiled wrapper of the executed
toolchain preserves "last add wins"; it does not establish that a compiler built
from the later commits emits that sequence. The three cells that the executed
compiler can express (no attribute, the three command lines) were compared:
the real `rustc` output and the replay agree on the surviving attribute and on
sled presence in all three
(`cross_check_against_real_rustc_without_attribute`).

### 5. The command line alone cannot produce the double push

Basis: source (three commits) + execution (executed commit).

`parse_instrument_xray` (`compiler/rustc_session/src/options.rs`, from line 1541
at the executed commit, 1738 and 1775 at the later ones) has, at all three
commits:

```rust
                "always" if !seen_always && !seen_never => {
                    options.always = true;
                    options.never = false;
                    seen_always = true;
                }
                "never" if !seen_never && !seen_always => {
                    options.never = true;
                    options.always = false;
                    seen_never = true;
                }
```

Each word clears the other flag, also across repeated `-Z instrument-xray=`
arguments, and both words in one argument are rejected. At the executed commit
the selection code is `if options.always { push xray-always }` followed by
`if options.never { push xray-never }` (lines 236-241), with no attribute
parameter. Observed with the executed `rustc` on three functions without
attributes (`fn_default`: straight-line; `caller_inlines_callee`: calls an
`#[inline(always)]` function; `fn_with_loop`: contains a loop):

| command line | exit status | `"function-instrument"` in emitted IR | sleds (entry/exit) and `xray_instr_map` relocations |
| :--- | :--- | :--- | :--- |
| `-Zinstrument-xray` | 0 | none (only `"xray-instruction-threshold"="200"`) | `fn_with_loop`: 1/2 and 6; other two: 0/0 and 0 |
| `-Zinstrument-xray=always` | 0 | `xray-always` on all three | 1/1 and 4; `fn_with_loop` 1/2 and 6 |
| `-Zinstrument-xray=never` | 0 | `xray-never` on all three | 0/0 and 0 |
| `-Zinstrument-xray=always -Zinstrument-xray=never` | 0 | `xray-never` on all three | 0/0 and 0 |
| `-Zinstrument-xray=always,never` | 1 | ``incorrect value `always,never` ... `always` or `never` (mutually exclusive)`` | - |
| `-Zinstrument-mcount` | 0 | `"instrument-function-entry-inlined"="mcount"` on all three | no sleds; one call relocation to `mcount` per function |
| `-Zinstrument-mcount=fentry` | 1 | ``incorrect value `fentry` ...`` (not an accepted value at this commit) | - |

The bare `-Zinstrument-xray` row shows the threshold mode: the loop function is
instrumented, the two short straight-line functions are not.

### 6. mcount and fentry honour `#[instrument_fn = "off"]`

Basis: source (two later commits) + execution at LLVM level.

Lines 270-279 at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (274-283 at
`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`):

```rust
    if sess.opts.unstable_opts.instrument_mcount != InstrumentMcount::Disabled {
        // Similar to `clang -pg` behavior. Handled by the
        // `post-inline-ee-instrument` LLVM pass.

        let instrument_entry = match instrument_fn {
            Some(InstrumentFnAttr::On) | None => true,
            Some(InstrumentFnAttr::Off) => false,
        };

        if instrument_entry {
```

Inside `if instrument_entry`, `InstrumentMcount::Mcount` pushes
`"instrument-function-entry-inlined"=<mcount symbol>` and
`InstrumentMcount::Fentry` pushes `"fentry-call"="true"`; each is pushed at most
once, so the builder law of finding 1 has nothing to overwrite. `llc` 22.1.6 on
a function carrying the attribute emits one `R_X86_64_PLT32 mcount-0x4`
(respectively `__fentry__-0x4`) call relocation; without the attribute, none
(`mcount_cells` in the results file).

A measurement pitfall worth retaining: in an unlinked object the call to
`mcount` is `callq` to the next instruction plus a relocation. A disassembly
without relocations (`llvm-objdump -d` without `-r`) shows no symbol name, so a
text search for `mcount` reports a false negative for every function.

### 7. The upstream codegen test exercises one of the three XRay command lines

Basis: source.

`tests/codegen-llvm/instrument_fn.rs` (56 lines, identical at the two later
commits) has three revisions. Its XRay revision is line 6:

```text
//@ [XRAY] compile-flags: -Zinstrument-xray --target=x86_64-unknown-linux-gnu
```

and it expects, for the `#[instrument_fn = "off"]` function, lines 48-49:

```text
// XRAY-NOT: attributes [[OFF_ATTR]] {{.*}} "function-instrument"="xray-always"
// XRAY:     attributes [[OFF_ATTR]] {{.*}} "function-instrument"="xray-never"
```

That is the first row of the table in finding 3. There is no revision with
`-Zinstrument-xray=always` or `=never`. A GitHub code search for `instrument_fn`
in `rust-lang/rust` on 2026-11-22 returned, among tests, only this file,
`tests/ui/attributes/instrument_fn.rs` and
`tests/ui/feature-gates/feature-gate-instrument-fn.rs` (with their `.stderr`
files); the two UI tests check attribute placement and the feature gate. The
expectation quoted above is also what "intended" means in finding 3: the test
author expects `off` to yield `xray-never` and not `xray-always`.

### 8. Repairs that restore the override

Basis: derived + Lean + execution at LLVM level.

Either of these makes all nine cells agree with "attribute overrides command
line", independently of push order:

- let the attribute set both booleans (`On` gives `never = false, always =
  true`; `Off` gives `never = true, always = false`), or
- replace the two booleans by one three-valued mode `Threshold | Always |
  Never`, taken from the command line and replaced wholesale by the attribute,
  and push at most one `"function-instrument"`.

The three-valued variant was replayed through LLVM (no disagreeing cell, table
in finding 4). Both are proved correct for all inputs in the Lean module
(`fixed_agrees`, `threeState_agrees`), together with the properties that the
override is idempotent, ignores the command line when an attribute is present,
and makes XRay honour an explicit attribute exactly as mcount does
(`threeState_parity_with_mcount`). These are candidate repairs evaluated here,
not upstream changes.

### 9. Inlining across attributes, and the handler re-entrancy hazard

Basis: source + execution (no-attribute case) + derived.

Neither inliner separates functions by instrumentation attribute. The MIR
inliner's compatibility check (`check_codegen_attributes`,
`compiler/rustc_mir_transform/src/inline.rs` from line 803 at
`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) looks at `inline`, `optimize`,
sanitizers, instruction set and target features, not at `instrument_fn`; LLVM's
attribute compatibility table (`llvm/include/llvm/IR/Attributes.td`, both tags)
has no rule mentioning `function-instrument`, `instrument-function-entry` or
`fentry`. Observed for the no-attribute case: the `#[inline(always)]` callee has
no body of its own in the emitted IR (three `define`s for four source
functions), and under `-Zinstrument-xray=always` its code sits between the
caller's entry and exit sleds. Derived for the attribute case: an
`#[inline(always)] #[instrument_fn = "off"]` function inlined into an
instrumented caller executes inside that caller's instrumentation; the
attribute protects a function's own entry and exit, not its code wherever it is
inlined.

Hazard (derived, modelled, not run). XRay's design is that a runtime patches
the sleds to call a handler at function entry and exit (the comment above the
code of finding 3 reads "Function prologue and epilogue are instrumented with
NOP sleds, a runtime library later replaces them with detours into tracing
code"; the unstable book page for `-Z instrument-xray` says the flag "only
enables generation of NOP sleds" and that a runtime must be linked
separately). Code reachable from the
handler must not itself be patched, otherwise entering it calls the handler
again. `#[instrument_fn = "off"]` is the tool for that (the upstream mcount
documentation, `src/doc/unstable-book/src/compiler-flags/instrument-mcount.md`,
uses it on its example counting function for exactly this reason). In the bold
cell of finding 3 the tool does not work: a helper marked `off` and compiled
with `-Z instrument-xray=always` has patchable sleds. If the runtime patches
them, and the handler calls the helper on every activation, and the handler has
no re-entrancy guard of its own, the first instrumented call never returns and
the nesting depth grows without bound (`handler_reentrancy_diverges`,
`handlerDepth_unbounded` in the Lean module, which state these three
assumptions in the definition they are about).

### 10. Coverage levels and option parsing

Basis: source + documentation + execution.

`-Z coverage-options` accepts `block` (default), `branch`, `condition` and
`discard-all-spans-in-codegen` (`parse_coverage_options`,
`compiler/rustc_session/src/options.rs`). `CoverageLevel` is ordered `Block <
Branch < Condition`; `instrument_coverage_branch()` is `level >= Branch` and
`instrument_coverage_condition()` is `level >= Condition`
(`compiler/rustc_session/src/session.rs`). The doc comment on `Condition`
(`compiler/rustc_session/src/config.rs`, from line 219 at the later commits):
"Same as branch coverage, but also adds branch instrumentation for certain
boolean expressions that are not directly used for branching ... mainly
intended to be a stepping-stone towards full MC/DC instrumentation". The
unstable book (`src/doc/unstable-book/src/compiler-flags/coverage-options.md` at
`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`) lists the same three levels.

Observed: `-Z coverage-options=mcdc` is rejected (``incorrect value `mcdc` ...
`block` | `branch` | `condition` was expected``); `llvm-cov export` reports
`mcdc` totals `0/0` and no MC/DC record in any function at all three levels.
`llvm-cov` counts each two-way branch region as two branches: the probe program
totals are 0, 20 and 26 branches for 0, 10 and 13 branch regions.

### 11. Branch regions are kept only in the body's root syntax context

Basis: source (three commits) + execution.

Branch spans are recorded while MIR is built (`BranchSpan { span, true_marker,
false_marker }`, the span being that of the condition expression). The coverage
pass first buckets them by the syntax context of that span
(`compiler/rustc_mir_transform/src/coverage/expansion.rs`, lines 174-182):

```rust
    if let Some(early_info) = mir_body.coverage_early_info.as_deref() {
        for branch_span in &early_info.branch_spans {
            if let Some(node) = nodes.get_mut(&branch_span.span.ctxt()) {
                node.branch_spans.push(BranchSpan::clone(branch_span));
            }
        }
    }
```

and then emits only one bucket
(`compiler/rustc_mir_transform/src/coverage/mappings.rs`,
`extract_branch_mappings`, lines 71-98; lines 81-88):

```rust
    // For now, ignore any branch span that was introduced by
    // expansion. This makes things like assert macros less noisy.
    let Some(node) = expn_tree.get(hir_info.body_span.ctxt()) else { return };
    if node.expn_kind != ExpnKind::Root {
        return;
    }

    mappings.extend(node.branch_spans.iter().filter_map(
```

`hir_info.body_span` is the span of the function's body expression (for
closures it is first walked back to the context of the closure declaration).
So the rule is two tests, not one: (a) if the body's context is not the root
context, the function gets no branch mapping at all; (b) otherwise only branch
spans whose own context equals the body's context are mapped. Spans in other
buckets are never read. Ordinary code regions do not go through this function,
which is why they survive.

Observed at `branch` and `condition` level, identically at both optimisation
levels (each function is called with `x = 1, 9, 10`, so `x > 5` is true twice):

| function in the probe program | where the `if` and its condition are written | code regions (executed) | branch regions |
| :--- | :--- | :--- | :--- |
| `normal_if` | ordinary function | 5 (5) | 1: true 2, false 1 |
| `macro_def_site_condition` | `if v > 5` inside a `macro_rules!` body, macro used in an ordinary function | 4 (4) | **0** |
| `macro_call_site_condition` | macro body is `if $cond { .. }`, `x > 5` written at the call site | 4 (4) | 1, located at the call-site tokens: true 2, false 1 |
| `macro_generated_fn` | whole `fn`, body included, written in a `macro_rules!` body | 5 (5) | **0** |
| `macro_fn_call_site_body` | `fn` item produced by a macro, body block passed in from the call site | 4 (4) | 1: true 2, false 1 |

The two bold rows are functions with every code region executed and no branch
information. The third and fifth rows show that "came from a macro" is not the
criterion; the syntax context of the condition's span and of the body's span is.

### 12. `condition` level: a diamond on the right operand of a value-context lazy boolean

Basis: source (three commits) + execution.

`visit_coverage_standalone_condition`
(`compiler/rustc_mir_build/src/builder/coverageinfo.rs`, lines 253-306 at the
later commits, 180-233 at the executed commit) has exactly one caller, the
lowering of `ExprKind::LogicalOp` into a destination
(`compiler/rustc_mir_build/src/builder/expr/into.rs`, line 198 at the later
commits):

```rust
                let mut rhs_block =
                    this.expr_into_dest(destination, continue_block, rhs).into_block();
                // Instrument the lowered RHS's value for condition coverage.
                // (Does nothing if condition coverage is not enabled.)
                this.visit_coverage_standalone_condition(rhs, destination, &mut rhs_block);
```

The left operand is lowered as a branch condition and so already gets a branch
span at `branch` level. For the right operand the function returns early unless
the level is `condition`, strips `ValueExpr`/`Scope` wrappers, returns if the
operand is itself a `LogicalOp` (it will be handled when that operator is
lowered), and otherwise builds

```text
         block
        /     \
true_block   false_block
 (marker)     (marker)
        \     /
       join_block
```

by terminating `block` with `if_(Operand::Copy(place), true_block, false_block)`
on the value already stored in the destination, registering one two-way branch,
and making both arms `goto` a new `join_block`. Three new blocks, one new
`switchInt`, two marker statements, no assignment.

Observed for the probe function

```rust
    let cond_pair: bool = (x > 10) && (y < 50);
    let single: bool = x > 10;
    let or_pair: bool = (x > 100) || (y < 5);
    let nested: bool = (x > 1) && ((y > 1) || (x > 2));
```

called with `(20,10) (20,60) (5,10) (200,3) (20,0) (0,0)`:

| expression | lowest level with a branch region | true / false (observed = recomputed from the inputs) |
| :--- | :--- | :--- |
| `(x > 10)` left of `&&` | branch | 4 / 2 |
| `(y < 50)` right of `&&` | condition | 3 / 1 |
| `(x > 100)` left of `\|\|` | branch | 1 / 5 |
| `(y < 5)` right of `\|\|` | condition | 2 / 3 |
| `(x > 1)` left of outer `&&` | branch | 5 / 1 |
| `(y > 1)` left of inner `\|\|` | branch | 4 / 1 |
| `(x > 2)` right of inner `\|\|` | condition | 1 / 0 |
| `x > 10` alone (`single`) | never | no branch region at any level |

Branch regions in this function: 0 at `block`, 4 at `branch`, 7 at `condition`.
The right operand of the outer `&&` in `nested` is itself a lazy operator and
gets no diamond of its own. Flow is conserved in every pair: the right
operand's true plus false count equals the count of the left operand's outcome
that reaches it (3+1 = 4, 2+3 = 5, 1+0 = 1, and for the inner left operand
4+1 = 5).

Built MIR of the same function (`-Z dump-mir`, file `*.built.after.mir`):

| level | basic blocks | `switchInt` | `switchInt(copy _)` | `Coverage::BlockMarker` |
| :--- | :--- | :--- | :--- | :--- |
| block | 21 | 4 | 0 | 0 |
| branch | 21 | 4 | 0 | 8 |
| condition | 30 | 7 | 3 | 14 |

`condition` changes the control-flow graph that every later MIR consumer sees:
+9 blocks and +3 `switchInt` for three diamonds. `branch` only adds marker
statements.

### 13. `!` chains: one branch region on the outermost `!`, with source polarity

Basis: source (three commits) + execution.

A `!` in a branch condition is lowered by lowering its operand as a condition
and exchanging the roles of the two outcome blocks
(`compiler/rustc_mir_build/src/builder/matches/mod.rs`, lines 141-162 at the
later commits). Before doing so it calls `visit_unary_not`, which records, for
every expression reached through `!`, `Scope` and `ValueExpr` nodes below this
`!`, a `NotInfo { enclosing_not, is_flipped }`
(`coverageinfo.rs` lines 97-134):

```rust
    fn visit_with_not_info(&mut self, thir: &Thir<'_>, expr_id: ExprId, not_info: NotInfo) {
        match self.nots.entry(expr_id) {
            // This expression has already been marked by an enclosing `!`.
            Entry::Occupied(_) => return,
            Entry::Vacant(entry) => entry.insert(not_info),
        };

        match thir[expr_id].kind {
            ExprKind::Unary { op: UnOp::Not, arg } => {
                // Invert the `is_flipped` flag for the contents of this `!`.
                let not_info = NotInfo { is_flipped: !not_info.is_flipped, ..not_info };
                self.visit_with_not_info(thir, arg, not_info);
            }
```

The visit starts with `is_flipped: false` for the `!` itself. Because an
occupied entry stops the visit, the outermost `!` wins: when the inner `!`
operators are lowered later their visits return at once. When the innermost
non-`!` condition is finally lowered, `visit_coverage_branch_condition` (lines
310-331) replaces the expression by `enclosing_not` for the span and exchanges
the two blocks if `is_flipped`, before placing the true and false markers. The
innermost condition under `k` operators has `is_flipped` equal to "`k` is odd",
which is exactly when the truth of `!^k e` is the opposite of the truth of `e`.

Observed (`x, y, z` = `(1,10,0) (2,20,0) (3,60,0) (4,70,0) (200,80,5)`; the
counts are asymmetric on purpose so that an exchanged pair would be visible):

| condition | region | true / false observed | recomputed from the inputs | exchanged pair |
| :--- | :--- | :--- | :--- | :--- |
| `if !(x > 100)` | the whole `!(x > 100)` | 4 / 1 | 4 / 1 | 1 / 4 |
| `if !!(y < 50)` | the whole `!!(y < 50)` | 2 / 3 | 2 / 3 | 3 / 2 |
| `if !!!(z == 0)` | the whole `!!!(z == 0)` | 1 / 4 | 1 / 4 | 4 / 1 |

One branch region per `if`, none for the inner operators.

### 14. `#[coverage(off)]` on an `#[inline(always)]` function

Basis: source + execution.

`is_eligible_for_coverage` returns false when `coverage_attr_on` is false
(`compiler/rustc_mir_transform/src/coverage/query.rs`), and
`CoverageInfoBuilder::new_if_enabled` returns `None` for ineligible functions,
so such a function gets neither counters nor mappings of its own. Observed at
all three levels and both optimisation levels: nine function records for ten
source functions; no record, no `__profc_` counter global (nine in total) and
no region of any function on the lines of `excluded_inline_callee`; the emitted
IR neither defines nor calls it (it is inlined into `caller_of_excluded`, whose
three code regions are all executed). `#[coverage(off)]` needed
`#![feature(coverage_attribute)]` on the executed toolchain.

### 15. What the Lean module proves

Basis: derived (machine-checked).

`support/XrayAttrOverrideAndCoverageBranchSoundness.lean` (no imports) defines
and proves, in namespace `XrayCov`:

- Builder. `addAttr` (replace on equal key, else insert), `getAttr`, `addAll`
  (pushes left to right), `lastPush`. Theorem `getAttr_addAll`: after any push
  sequence the value stored for a key is that of the last push with that key,
  and keys never pushed keep their previous value.
- Parser. `applyWord` models the two parser arms; `parse_wellFormed`: no word
  sequence makes both flags true.
- Selection. `pushesNeverFirst` is the code of finding 3, `pushesAlwaysFirst`
  the opposite order; `spec` is "attribute overrides command line".
  `off_overwritten_under_always`; `neverFirst_agrees_iff` (for well-formed
  options the result equals `spec` if and only if it is not the case that
  `always` is set and the attribute is `off`); `alwaysFirst_agrees_iff` (the
  mirror image); `no_push_order_implements_override`; `table_neverFirst` and
  `table_alwaysFirst` (the nine cells, equal to the replay tables).
- Repairs and parity. `threeState_agrees`, `threeState_at_most_one_push`,
  `fixed_agrees`, `fixedPair_exclusive`, `resolve_idempotent`,
  `resolve_override`, `neverFirst_parity_with_mcount_iff`,
  `threeState_parity_with_mcount`.
- Handler. `callHelper` is a fuel-indexed call of a helper from the handler;
  `callHelper_patched_never_returns`, `handlerDepth_unbounded`,
  `handler_reentrancy_diverges`, `handler_returns_with_three_state`.
- Erasure. `extractBranchMappings` is the two tests of finding 11.
  `mem_extractBranchMappings` (a span survives if and only if the body context
  is root, the span was recorded, and its context is the body's),
  `kept_span_is_root`, `expansion_body_erases_everything`,
  `erasure_accounting` (kept plus foreign-context spans equals recorded), and
  the four probe cases.
- Negation. `visitWithNotInfo` models insert-if-vacant and the inverted flag;
  `lowerNots` visits every `!` from the outside in. `leaf_notInfo`: the entry
  of the innermost condition names the outermost `!` and is flipped exactly for
  odd `k`. `true_marker_hit`: the true marker is executed exactly when `!^k e`
  is true, for every `k`. `trueCount_eq`, `falseCount_eq`,
  `uncompensated_counts_are_swapped` (without the exchange, odd `k` reports the
  false count as the true count), `parity_add_two`, and the three probe rows.
- Diamond and levels. `diamond_conserves` (true count plus false count equals
  entry count), `diamond_join`, `and_rhs_flow`, `or_rhs_flow`;
  `condition_adds_diamonds` (the `condition` level adds exactly one branch span
  per right operand that is not itself lazy); `probe_branch_spans` (0, 4 and 7
  for the probe function) and `probe_diamonds` (3).

Every recursive definition is `noncomputable`. The check
(`support/lean_check_transcript.txt`) ends with exit status 0 under
`-DwarningAsError=true`; the 63 printed axiom reports name only `propext` and
`Quot.sound`; the whole-module audit
(`support/AuditXrayAttrOverrideAndCoverageBranchSoundness.lean`, run from a
second file so that the module's constants are the entries of
`env.constants.map₁` belonging to that module) examined 580 constants (207
theorems, 311 definitions) and found 0 names containing `_unsafe_rec`, 0 unsafe
or partial constants, 0 declared axioms or opaque constants, and no dependency
on an axiom other than `propext` and `Quot.sound`. The audit was also run
against a deliberately bad module (a computable recursive function and a use of
the choice axiom) and failed as intended.

### 16. Relation to a MIR-level verifier (`joshlf/anneal`)

Basis: source.

At `c131b320eeeb26ef692e5afd5ec8db49ee518613`,
`trusted/lean/Trusted/MirAst.lean` lines 654-662 define

```lean
inductive StatementKind where
  | assign (dst : Place) (rvalue : Rvalue)
  | storageLive (localId : LocalId)
  | storageDead (localId : LocalId)
  | nop
  | unsupported
```

with the documented correspondence "`.unsupported` represents all other
`StatementKind` variants (`FakeRead`, `SetDiscriminant`, `PlaceMention`,
`AscribeUserType`, `Coverage`, `Intrinsic`, `ConstEvalCounter`, and
`BackwardIncompatibleDropHint`)", and `evalStatement` in
`trusted/lean/Trusted/MirSemantics.lean` (lines 1370-1427) ends with
`| .unsupported => .fault .unsupported`. Consequences, stated as far as the
source supports them:

- MIR produced with `-C instrument-coverage` at `branch` or `condition` level
  contains `Coverage` statements (finding 12: 8 and 14 markers in one small
  function). Under the documented correspondence each is an unsupported
  statement, and executing one faults closed. That is a statement about the
  statement type and its step function only; how a captured body is translated
  into that type was not examined.
- `condition` additionally changes the block structure (finding 12). A result
  about the uninstrumented body is not a result about the `condition` body,
  even though the diamond has no data effect.
- XRay and mcount selection happens in `rustc_codegen_llvm` on LLVM function
  attributes. It has no MIR representation, so a MIR-level proof neither sees
  nor constrains sleds, `mcount` calls, or the overwrite of finding 3.

## Boundaries

**Not examined.**

- End-to-end behaviour of `#[instrument_fn]` on any compiler that accepts it.
  The probe contains that matrix (seven command lines against `fn_default`,
  `fn_explicit_on`, `fn_explicit_off` and a caller that inlines an excluded
  callee) and runs it when the given `rustc` accepts the feature; in the
  preserved results it is recorded as not executed. The analysis code of that
  branch was exercised once with the attribute lines removed from its source
  (same function names); the attribute-bearing source itself has only ever been
  compiled as far as the feature-gate rejection.
- Any XRay runtime. Nothing was linked against one; no sled was patched; the
  re-entrancy hazard is a model. Whether a given runtime's own handlers carry a
  re-entrancy guard was not examined.
- Targets other than x86-64 ELF (sled encodings, relocation types, mcount
  symbol names), `xray-skip-entry`, `xray-skip-exit`, `ignore-loops`, custom
  thresholds, and the `fentry-record` variants.
- The exact LLVM revision bundled by the two later `rust-lang/rust` commits.
  The upstream `llvmorg-23.1.5` tag was read as a representative of the 23.1
  line named in their `.gitmodules`.
- Coverage of closures, async functions, `let`-`else`, `if let`, match guards,
  nested macro expansions, procedural macros, and compiler desugarings. By the
  rule of finding 11 a branch span in any non-root context is dropped, but only
  `macro_rules!` expansion was run.
- Cross-crate inlining and LTO for the `#[coverage(off)]` case.
- How `joshlf/anneal` captures MIR and whether it can be run on instrumented
  bodies at all.

**Unknown.**

- Whether upstream knows of the overwrite. A GitHub issue search for
  `instrument_fn` in `rust-lang/rust` on 2026-11-22 returned four results (pull
  requests 153742, 157681, 157999 and issue 157081), none of whose titles
  describes it; a report worded differently would not have been found.
- Whether compilers built from the two later commits behave as their source
  reads. No contrary evidence was found, and none was sought by execution.

**Known not to apply.**

- The overwrite cannot be triggered from the command line alone (finding 5).
- It does not affect mcount or fentry (finding 6), nor bare `-Z instrument-xray`
  (the case the upstream test covers), nor `#[instrument_fn = "on"]`.
- Macro erasure does not remove code regions, and does not apply to conditions
  whose tokens are written at the call site or to macro-produced functions whose
  body block is written at the call site (finding 11).
- `condition` is not MC/DC: no bitmap, no MC/DC record, no decision grouping.

**Unsupported by the subject.**

- `-Z coverage-options=mcdc` (rejected at the executed commit; absent from the
  parser at the later ones).
- `#![feature(instrument_fn)]` and `-Z instrument-mcount=fentry` at the executed
  commit.

**Stronger conclusions the evidence does not establish.**

- "A nightly from November 2026 emits XRay sleds into `#[instrument_fn =
  "off"]` functions": supported by source and by LLVM-level replay on LLVM
  22.1.6, not by running such a nightly.
- "Programs using XRay handlers recurse forever": only under the three stated
  assumptions.
- "The Lean theorems are about `rustc`": they are about definitions written by
  hand to mirror the quoted source. The nine-cell tables and the probe rows tie
  the model to observed outputs at a finite number of points; nothing ties it to
  the compiler mechanically, and it shares no definitions with `joshlf/anneal`.
- "Branch coverage percentages are comparable across code bases": a code base
  that expresses its conditions inside macros reports fewer branches for the
  same logic.

## Evidence

All evidence was acquired on 2026-11-22.

**Source, `rust-lang/rust`.** Paths are relative to the repository root. `A` is
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `B` is
`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `C` is
`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`. The files read at `A` are
byte-identical to the `rustc-src` component of the executed toolchain.

| Path | Symbol | Lines at A / B / C |
| :--- | :--- | :--- |
| `compiler/rustc_codegen_llvm/src/attributes.rs` | `instrument_function_attr` | 210-261 / 264-356 / 268-360 |
| same | XRay pushes | 236-241 / 330-335 / 334-339 |
| same | `let mut never`, `let mut always`, `match instrument_fn` | absent / 316-328 / 320-332 |
| same | mcount `instrument_entry` | absent / 274-277 / 278-281 |
| same | `to_add.extend(instrument_function_attr(..))`, `apply_to_llfn(llfn, Function, &to_add)` | 445, 613 / 542, 721 / 546, 725 |
| `compiler/rustc_llvm/llvm-wrapper/RustWrapper.cpp` | `AddAttributes`, `LLVMRustAddFunctionAttributes` | 493-502, 510 / 387-396, 404 / 387-396, 404 |
| `compiler/rustc_session/src/options.rs` | `parse_instrument_xray` (`always`/`never` arms) | 1562-1571 / 1759-1768 / 1796-1805 |
| `compiler/rustc_session/src/config.rs` | `CoverageLevel` | 168 / 219 / 219 |
| `compiler/rustc_attr_parsing/src/attributes/codegen_attrs.rs` | `InstrumentFnParser` | absent / 658-693 / 658-693 |
| `compiler/rustc_feature/src/unstable.rs` | `instrument_fn` feature | absent / 608-609 / 608-609 |
| `tests/codegen-llvm/instrument_fn.rs` | whole file | absent / 1-56 / 1-56 |
| `compiler/rustc_mir_transform/src/coverage/mappings.rs` | `extract_branch_mappings` | 71-98 at all three |
| `compiler/rustc_mir_transform/src/coverage/expansion.rs` | branch-span bucketing | 174-182 at all three |
| `compiler/rustc_mir_transform/src/coverage/hir_info.rs` | `body_span` | 46 / 54 / 54 |
| `compiler/rustc_mir_build/src/builder/coverageinfo.rs` | `NotInfo`, `visit_unary_not`, `visit_with_not_info` | 30-38, 91-128 / 36-44, 97-134 / same as B |
| same | `visit_coverage_standalone_condition` | 180-233 / 253-306 / 253-306 |
| same | `visit_coverage_branch_condition` | 237-258 / 310-331 / 310-331 |
| `compiler/rustc_mir_build/src/builder/expr/into.rs` | call of `visit_coverage_standalone_condition` | 200 / 198 / 198 |
| `compiler/rustc_mir_build/src/builder/matches/mod.rs` | `!` arm, `visit_unary_not`, `visit_coverage_branch_condition` | 156-182, 161, 224 / 141-162, 151, 207 / same as B |
| `compiler/rustc_mir_transform/src/coverage/query.rs` | `is_eligible_for_coverage`, `coverage_attr_on` | 23, 50 / 26, 65 / 26, 65 |
| `compiler/rustc_mir_transform/src/inline.rs` | `check_codegen_attributes` | not read / 803 / not read |

**Source, LLVM** (`llvm/llvm-project`, release tags; no commit hashes recorded):
`llvm/lib/IR/Attributes.cpp` (`addAttributeImpl`, `AttrBuilder::addAttribute`),
`llvm/lib/CodeGen/XRayInstrumentation.cpp` (`XRayInstrumentation::run`),
`llvm/lib/CodeGen/AsmPrinter/AsmPrinter.cpp` (`emitXRayTable`),
`llvm/lib/AsmParser/LLParser.cpp` (string attribute parsing),
`llvm/include/llvm/IR/Attributes.td`, at `llvmorg-22.1.6` and `llvmorg-23.1.5`,
with the line numbers given in the findings.

**Source, `joshlf/anneal`** at `c131b320eeeb26ef692e5afd5ec8db49ee518613`:
`trusted/lean/Trusted/MirAst.lean` lines 630-662,
`trusted/lean/Trusted/MirSemantics.lean` lines 332-334 and 1370-1427.

**Execution environment.** `rustc -vV`: `rustc 1.98.0-nightly (14210df0e
2026-05-31)`, `commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `host:
x86_64-unknown-linux-gnu`, `LLVM version: 22.1.6`; `llvm-objdump`,
`llvm-readobj`, `llvm-cov`, `llvm-profdata`, `llvm-as`, `llvm-dis`, `llc` from
the same toolchain's `llvm-tools` component (`LLVM version
22.1.6-rust-1.98.0-nightly`); a system C compiler for the short harness that calls
`LLVMRustAddFunctionAttributes`. Lean: `Lean (version 4.34.1,
x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52,
Release)`.

**Preserved material** (`support/`):

| File | Content |
| :--- | :--- |
| `probe_xray_attr_overwrite_and_coverage_modes.py` | The probe. Embeds every input (Rust sources, LLVM IR template, C harness), runs the tools, and writes one JSON document. Values named `oracle_*` are recomputed from the inputs in Python; push sequences are transliterated from the quoted source; everything else is tool output. |
| `probe_results_rustc_1_98_0_nightly_14210df0e.json` | The output of the probe on the executed toolchain. Absolute paths are replaced by placeholders before writing. Keys: `instrument_fn_attribute`, `part_a1_real_rustc_command_line_matrix_no_attribute` (finding 5), `part_a2_real_rustc_instrument_fn_matrix` (`executed: false`), `part_a3_llvm_level_replay` (findings 1, 4, 6), `part_b_coverage_levels` (findings 10-14). |
| `XrayAttrOverrideAndCoverageBranchSoundness.lean` | The Lean module of finding 15. |
| `AuditXrayAttrOverrideAndCoverageBranchSoundness.lean` | The whole-module audit. |
| `check_lean.sh` | Runs both Lean files. |
| `lean_check_transcript.txt` | Output of `check_lean.sh` with the Lean build named above. |

The command lines used are in the probe (`compile_instrument_matrix`,
`llvm_replay`, `coverage_run`, `built_mir_shape`) and are not repeated here.

## Revalidation

Cheapest checks first.

1. **Is the overwrite still in the source?** In
   `compiler/rustc_codegen_llvm/src/attributes.rs`, function
   `instrument_function_attr`, look at the two `match instrument_fn` arms of the
   XRay block. If `Some(InstrumentFnAttr::Off)` still only sets `never = true`
   and `if never` is still pushed before `if always`, finding 3 holds. If either
   arm now clears the opposite flag, or a single mode replaced the two booleans,
   it is repaired. Also check whether `tests/codegen-llvm/instrument_fn.rs`
   gained a revision with `-Zinstrument-xray=always`.
2. **End-to-end confirmation, which this report lacks.** Run
   `python3 support/probe_xray_attr_overwrite_and_coverage_modes.py --rustc
   <nightly rustc> --out out.json` with a nightly from 2026-06-17 or later that
   has the `llvm-tools` component (the wrapper call additionally needs a C
   compiler and a `librustc_driver` whose symbol table still lists
   `LLVMRustAddFunctionAttributes`).
   `instrument_fn_attribute.accepted_by_this_rustc` must be `true`; then under
   `part_a2_real_rustc_instrument_fn_matrix.configs.xray_always.functions.fn_explicit_off`
   the overwrite shows as `"function-instrument"="xray-always"` in
   `llvm_ir_instrument_attributes`, `entry_sleds` 1 and
   `xray_instr_map_pc64_relocations` 4, and a repaired compiler shows
   `"xray-never"`, 0 and 0. The attribute-bearing source of that branch has
   never been compiled successfully (see Boundaries); read its output critically
   the first time.
3. **Builder law on another LLVM.** The `part_a3_llvm_level_replay` section
   needs only `llvm-as`, `llvm-dis`, `llc` and, optionally, a C compiler; the
   list `disagreeing_cells` must be `["cli=always,attr=off"]`,
   `["cli=never,attr=on"]` and `[]` for the three variants, and
   `direct_wrapper_call_agrees_with_llvm_as` must be true in every cell. If the
   wrapper symbol cannot be located the section records why and continues with
   the tool route only.
4. **Coverage.** In `part_b_coverage_levels.runs.*`, the fields
   `all_sites_presence_as_source_predicts` and `all_present_sites_match_oracle`
   must be true for all six runs, `macro_def_site_condition` and
   `macro_generated_fn` must have empty `branch_regions`, and every
   `flow_conservation[*].conserved` must be true. A change of the `Root` test in
   `extract_branch_mappings` would show up as branch regions in those two
   functions. `built_mir.condition.standalone_conditions.basic_blocks` minus the
   `branch` value must be three times the number of `condition`-only sites (9
   for 3).
5. **Lean.** `LEAN=<lean 4.34.1 binary> sh support/check_lean.sh` must print
   `step 1 exit status: 0`, axiom reports naming at most `propext` and
   `Quot.sound`, `AUDIT PASSED` and `step 2 exit status: 0`. With another Lean
   version, expect to adjust proofs; the statements are what matters.

A passing probe on a toolchain without `#[instrument_fn]` re-establishes
findings 1, 2, 4-6 (LLVM part) and 10-14 for that toolchain and nothing about
finding 3 beyond what the source check in step 1 gives. The handler hazard has
no cheap executable check: it needs a target with an XRay runtime, a handler
installed through that runtime, and a helper compiled as in the bold cell of
finding 3.
