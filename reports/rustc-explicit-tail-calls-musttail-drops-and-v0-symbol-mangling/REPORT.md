# Explicit tail calls in rustc (`become`, `TerminatorKind::TailCall`, LLVM `musttail`): frame reuse, pre-jump drop order, inlining, and `v0` backreference symbol mangling

## Summary

- `become f(args)` is lowered to the MIR terminator `TailCall { func, args, fn_span }`,
  which has no destination, no successor block and no unwind edge. Both the MIR
  interpreter (used by Miri) and the LLVM backend implement it as "discard the current
  frame, then enter the callee with the discarded frame's return continuation". The
  backend emits `musttail call` immediately followed by `ret`.
- On `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, x86-64 Linux, a 250,000-step mutual
  recursion written with `become` ran at `-C opt-level=0` inside a 64 KiB thread stack
  with **0 bytes** between the shallowest and deepest activation, and under Miri with a
  frame-count spread of **0**. The same program with an ordinary `return f(..)` used
  48 bytes per step at `opt-level=0` and aborted with a stack overflow in a 1 MiB stack.
- The caller's variables are destroyed **before** the jump, in reverse declaration
  order across all enclosing scopes, by-value parameters last; operands moved into the
  call are not destroyed by the caller. With an ordinary call the callee runs first.
  Measured logs (identical natively at `opt-level` 0 and 3 and under Miri): `2193`
  versus `9321`, and `54321976` versus `97654321`.
- That order is produced while MIR is built (`break_for_tail_call`), not by drop
  elaboration. `StorageDead` is emitted before the tail call only for non-parameter
  locals whose type has a destructor; parameters never receive `StorageDead`, and a
  local without a destructor receives none on this path either.
- An argument that borrows a caller local or a by-value parameter is rejected with
  `E0597`. The rejection comes from the borrow checker treating `TailCall` like
  `Return` (every local is invalidated at the terminator).
- Caller/callee ABI equality and signature equality are enforced by a THIR visitor in
  `rustc_mir_build` (`check_tail_calls.rs`), not by the HIR type checker, which only
  requires the callee's return type to match without coercion. At two later commits the
  signature requirement is waived when the callee uses the then-new `extern "tail"` ABI.
- The MIR inliner refuses to inline a callee whose body contains a `TailCall`, and it
  never treats a `TailCall` terminator as a call site. LLVM's own inliner still inlined
  an `#[inline(always)]` helper ending in `become`; the resulting module contained no
  `musttail` and the caller made an ordinary call to the helper's callee.
- `v0` (`_R…`) is the default symbol mangling in the compiler source at all three
  audited commits, and `legacy` needs `-Z unstable-options`. `v0` caches every
  non-basic type and every path by the byte offset where it was first printed and
  emits `B<base-62>_` on reuse. For `touch_gen::<D_n>` with `D_0 = u64`,
  `D_(n+1) = Pair<D_n, D_n>`, the `v0` symbol grew 63 → 141 bytes over depths 1–10
  (+8 per level, then +9) while the type it denotes grew from 2 to 1,024 leaves and its
  demangled text from 59 to 27,653 bytes; the `legacy` symbol stayed 49 bytes and
  demangles to a name with no type arguments.
- A self-contained Lean 4 development (kernel-checked, axioms limited to `propext` and
  `Quot.sound`) proves, for an abstract frame-stack machine and an abstract
  backreference encoder: frame replacement with exact pre-jump drop order; a constant
  stack bound for programs whose only transfers are tail calls; that copying a callee
  body ending in a tail call into its caller loses the caller's continuation; undefined
  behaviour for a pointer into the replaced frame; a lossless decode of the
  backreference encoding with a size bound linear in the number of distinct compound
  subtrees; and that every digest of bounded range collides. The models are not rustc.
- Anneal at the audited commit does not model `TailCall`: its trusted MIR syntax folds
  it into `.unsupported` and its correspondence hook fails closed with
  `"TailCall unsupported"`.

## Applicability

**Subjects and how they relate.** Five subjects are listed in `REPORT.json`.

1. `rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` is both the source
   that was read and the toolchain that was executed: `rustc 1.98.0-nightly
   (14210df0e 2026-05-31)`, host `x86_64-unknown-linux-gnu`, bundled LLVM 22.1.6, and
   the Miri driver from the same toolchain. Every execution result in this report was
   obtained with this toolchain and no other.
2. `rust-lang/rust` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` and
3. `rust-lang/rust` at `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` (the default-branch
   head on 2026-11-21) were **read only**. They are used to say which of the cited
   source regions are byte-identical to subject 1 and which changed. No compiler built
   from them was run.
4. `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` was read to establish
   how Anneal treats the `TailCall` terminator.
5. Lean 4 `v4.34.1` (`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`)
   is the kernel that checked the mechanization preserved with this report.

**Configuration of the executed observations.** Edition 2024; crate attribute
`#![feature(explicit_tail_calls)]` (the gate is declared `incomplete` at all three
rustc commits, so `#![allow(incomplete_features)]` is also used); `-C opt-level=0` and
`-C opt-level=3`; default panic strategy (unwind); default codegen backend (LLVM);
one target, `x86_64-unknown-linux-gnu`. The inliner and mangling observations
additionally use the nightly-only flags `-Z dump-mir`, `-Z merge-functions=disabled`
and `-Z unstable-options`.

**Shared and differing behaviour across the three rustc commits (source comparison).**
The file `support/upstream_anchors.json` records, for 36 cited regions, the line at each
commit and a digest of the region. 25 regions are byte-identical at all three commits;
the other 11 differ between `14210df0…` and the later two, and in all 36 the two later
commits agree with each other. Summarised:

| Region | `14210df0…` | `3ef0c22c…` | `c7d5ba59…` | Same text? |
| --- | --- | --- | --- | --- |
| `TailCall` variant and doc comment (`rustc_middle/src/mir/syntax.rs`) | 823 | 812 | 812 | identical |
| `check_expr_become` (`rustc_hir_typeck/src/expr.rs`) | 905 | 947 | 942 | identical |
| ABI equality check (`rustc_mir_build/src/check_tail_calls.rs`) | 134 | 132 | 132 | identical |
| Signature equality check (same file) | 150 | 148 | 148 | **changed**: later commits add `&& !matches!(callee_sig.abi(), ExternAbi::RustTail)` |
| `supports_guaranteed_tail_call` (`rustc_abi/src/extern_abi.rs`) | 316 | 321 | 335 | **changed**: see below |
| MIR building of `become` (`builder/expr/stmt.rs`) | 107 | 107 | 107 | identical |
| `break_for_tail_call` (`builder/scope.rs`) | 1095 | 1090 | 1090 | changed only by removal of one struct field (`async_fut: None`) |
| Borrow check exit invalidation (`rustc_borrowck/src/lib.rs`) | 1010 | 1015 | 1015 | identical |
| Inliner refusal (`rustc_mir_transform/src/inline.rs`) | 445 | 428 | 429 | identical |
| `is_inline_valid_on_body` (`check_inline.rs`) | 73 | 72 | 72 | identical |
| `LLVMSetTailCallKind(.., MustTail)` (`rustc_codegen_llvm/src/builder.rs`) | 1455 | 1518 | 1517 | call marked the same way; later commits pass an extra `return_slot` argument and add an arm for unsized returns |
| `init_fn_tail_call` (`rustc_const_eval/src/interpret/call.rs`) | 816 | 1027 | 1027 | changed only in one parameter type (`Option<&FnAbi>`) |
| Default mangling version (`rustc_session/src/config.rs`) | 1473 | 1608 | 1608 | identical |
| `legacy` needs `-Z unstable-options` (same file) | 2500 | 2879 | 2916 | identical |
| `v0` backreference and type cache (`rustc_symbol_mangling/src/v0.rs`) | 231, 482 | 307, 558 | 307, 558 | identical |
| `legacy` hash inputs (`legacy.rs`, `get_symbol_hash`) | 115 | 125 | 125 | changed: the instance-kind discriminant hashed last is replaced by an explicit five-way tag |

Two differences matter for anyone relying on the checks rather than on the mechanics:

- At `14210df0…` there is no `extern "tail"` ABI. At `3ef0c22c…` and `c7d5ba59…`
  `ExternAbi::RustTail` exists (feature gate `rust_tail_cc`, declared `unstable`), is
  accepted by `supports_guaranteed_tail_call`, and exempts the call from the signature
  equality check; an additional check rejects unsized argument types.
- At `14210df0…` `ExternAbi::RustCall` is in the accepted list of
  `supports_guaranteed_tail_call`; at both later commits it returns `false`, with the
  comment that argument untupling needs additional support.

Everything stated below as *execution* applies to subject 1 only. Extending the
execution results to the two later commits is an inference from identical source
regions and is marked **derived** wherever it is made; where a region changed, no
extension is claimed.

**Scope of the mechanization.** The Lean file imports nothing: not rustc's semantics,
not Anneal, not the Lean Miri model vendored in Anneal. Its machine has frames,
straight-line observable statements, ordinary calls, tail calls, one optional pointer
argument, and returns. It has no values, no branching and no unwinding. Its mangling
model uses binary type trees and backreferences that index a table of previously
emitted compound subtrees; rustc's `v0` uses byte offsets written in base 62. The
theorems are statements about these models. They are connected to rustc in exactly two
ways: the step rule for `tailcall` has the same shape as the interpreter routine quoted
in Findings 3, and the model reproduces the five destructor logs measured on real
rustc (Findings 8). Neither is a refinement proof.

## Findings

### 1. Where a `become` is checked

Basis: source (`14210df0…`) + execution, unless stated otherwise.

**HIR type checking** (`compiler/rustc_hir_typeck/src/expr.rs:905-929`,
`check_expr_become`) does one thing: it type-checks the operand with the function's
return type as a hint and then calls `demand_suptype(expr.span, ret_ty, call_expr_ty)`.
The comment in the source reads "don't coerce here, as tail calls can't support
most/all coercions". Outside a function body it reports the same error as a misplaced
`return`. It does not compare signatures or ABIs.

**THIR check** (`compiler/rustc_mir_build/src/check_tail_calls.rs`, 469 lines; the query
`check_tail_calls` is forced from `builder/mod.rs:75` before MIR is built). A visitor
calls `check_tail_call` (lines 55-192) for every `ExprKind::Become`. In source order it
reports:

| Lines | Condition | Diagnostic headline |
| --- | --- | --- |
| 56-59 | body is a closure | ``` `become` is not allowed in closures ``` |
| 77-86 | operand is a built-in unary/binary/assign/index operator | ``` `become` does not support operators ``` |
| 88-91 | operand is not a call | ``` `become` requires a function call ``` |
| 97-121 | callee is a closure or other `Fn*` object called through the trait; callee is an intrinsic | "tail calling closures directly is not allowed"; a separate error for intrinsics |
| 134-136 | `caller_sig.abi() != callee_sig.abi()` | "mismatched function ABIs" |
| 138-140 | `!callee_sig.abi().supports_guaranteed_tail_call()` | "ABI does not support guaranteed tail calls" |
| 150-161 | `caller_sig.inputs_and_output != callee_sig.inputs_and_output` | "mismatched signatures" |
| 163-183 | the caller carries the caller-location attribute (the one that makes `Location::caller()` report the caller's position, which adds a hidden argument) | an error stating such a function cannot perform a tail call |
| 185-191 | caller or callee is C-variadic | two separate errors |

The signature comparison is on the full list of argument types plus return type after
region erasure ("tail calls don't care about lifetimes", line 130). The accepted ABIs at
`14210df0…` (`compiler/rustc_abi/src/extern_abi.rs:316-358`) are `C`, `System`, `Rust`,
`RustCall`, `RustCold`, `RustInvalid`, `Unadjusted`, `EfiApi`, `Aapcs`, `Cdecl`,
`Stdcall`, `Fastcall`, `Thiscall`, `Vectorcall`, `SysV64`, `Win64`, `RustPreserveNone`,
`Swift`; rejected are the CMSE, interrupt, GPU/PTX kernel and `Custom` ABIs.

Observed (execution, `support/rust/reject_*.rs`; full diagnostics in
`support/probe_results.json` under `rejections`):

```text
reject_signature.rs      error: mismatched signatures
                           = note: caller signature: `fn(u64) -> u64`
                           = note: callee signature: `fn(u32) -> u64`
reject_abi.rs            error: mismatched function ABIs
                           = note: caller ABI is `"Rust"`, while callee ABI is `"C"`
reject_closure.rs        error: `become` is not allowed in closures
reject_feature_gate.rs   error[E0658]: `become` expression is experimental
```

**Borrow checking** (`compiler/rustc_borrowck/src/lib.rs`). At the terminator, `func`
and every argument are consumed (lines 923-928). After the terminator's primary effect,
`TailCall` is grouped with `UnwindResume`, `Return` and `CoroutineDrop` (lines
1008-1027): for every borrow still in scope, `check_for_invalidation_at_exit` is run,
with the source comment "Returning from the function implicitly kills storage for all
locals and statics". This is what rejects borrowed arguments:

```text
reject_borrow_local.rs   error[E0597]: `local` does not live long enough
                           become callee_ref(&local)
                                             ^^^^^^- `local` dropped here while still borrowed
reject_borrow_param.rs   error[E0597]: `v` does not live long enough
```

The identical borrow compiles and runs when the transfer is an ordinary call
(`accept_borrow_plain_call.rs`). For the local-borrow program the built MIR has no
`StorageDead` and no `drop` between the borrow and the tail call (the borrowed local is
a `u64`); the block ends, verbatim, `_7 = &_2; _6 = &(*_7); tailcall callee_ref(move _6);`.
So the error cannot come from a `StorageDead` and must come from the exit invalidation.
Basis for that last sentence: derived from the MIR shape (execution) and the borrow
checker source.

### 2. MIR shape and where the drops come from

Basis: source + execution.

The terminator (`compiler/rustc_middle/src/mir/syntax.rs:823-851`) is documented as
"a chimera of `Call` and `Return`": "pop of the current stack frame" followed by "a call
to the `func`, with the return address of the **current** caller". Compared with `Call`
it lacks `destination` ("always the return place"), `target` and `unwind` ("always taken
from the current stack frame"). Accordingly `successors()` yields nothing and `unwind()`
returns `None` for it (`compiler/rustc_middle/src/mir/terminator.rs:532-539`, `619-637`).

MIR building (`compiler/rustc_mir_build/src/builder/expr/stmt.rs:107-143`) evaluates the
callee and each argument into operands, records the operands as moved
(`record_operands_moved`), calls `break_for_tail_call`, and terminates the block with
`TailCall`.

`break_for_tail_call` (`compiler/rustc_mir_build/src/builder/scope.rs:1095-1203`) is
introduced by the comment "Unlike other kinds of early exits, tail calls do not go
through the drop tree. Instead, all scheduled drops are immediately added to the CFG."
Its loop is

```rust
for scope in self.scopes.scopes[1..].iter().rev().skip(1) {
    for drop_data in scope.drops.iter().rev() {
        let local = drop_data.local;
        if !self.local_decls[local].ty.needs_drop(self.tcx, typing_env) {
            continue;
        }
        match drop_data.kind {
            DropKind::Value => { /* emit `Drop { place: local, target: next, .. }` */ }
            DropKind::ForLint => { /* emit a backward-incompatible-drop hint */ }
            DropKind::Storage => {
                // Only temps and vars need their storage dead.
                assert!(local.index() > self.arg_count);
                /* emit `StorageDead(local)` */
            }
        }
    }
}
```

Three consequences can be read off it and were each confirmed on real MIR:

1. Scopes are visited innermost-first (`.rev()`), skipping the innermost scope, which
   "contains only the destructors for the tail call arguments", and stopping before
   `scopes[0]`. Within a scope, drops are visited in reverse. By-value parameters come
   last in the emitted MIR, as they would if their drops were scheduled in the
   outermost visited scope; that placement was observed in the MIR below, not read from
   the code that schedules them.
2. The `needs_drop` test precedes the `match`, so a local whose type has no destructor
   gets neither a `Drop` nor a `StorageDead` here.
3. The `assert!` shows that `StorageDead` is never emitted for a parameter.

Built MIR for `tail_caller2` in `support/rust/drop_order.rs` (parameters `p1`, `p2`;
locals `_a`, then `_b` and `_c` in a nested block), reduced to the events on the normal
path and rewritten with source names through the MIR `debug` lines:

```text
drop(_c)  StorageDead(_c)  drop(_b)  StorageDead(_b)  drop(_a)  StorageDead(_a)
drop(p2)  drop(p1)  tailcall callee2(move _11, move _12, move _13)
```

Drop elaboration does not reorder anything. `compiler/rustc_mir_transform/src/
elaborate_drops.rs` contains no mention of `TailCall` at any of the three commits, and
the MIR of `tail_caller` after `ElaborateDrops` has the same `drop(_3)` →
`StorageDead(_3)` → `drop(_1)` → `tailcall callee(move _6, move _7)` sequence as the
built MIR (both dumps are preserved in `support/probe_results.json`).

Each pre-jump `Drop` has an unwind edge. In the built MIR its cleanup block first drops
the argument temporaries of the pending tail call and then continues with the caller's
remaining variables; this is the stated purpose of the `arg_drops` list in the source
("the tail call arguments must be dropped if any of these drops panic"). These unwind
paths were read in the MIR but not exercised at run time.

### 3. Execution: frame replacement and constant stack

Basis: source + execution.

**Interpreter.** This is the engine in `rustc_const_eval`; that Miri executes
`TailCall` through it was not re-read in Miri's own sources, but the Miri measurements
below behave exactly as this routine prescribes.
`compiler/rustc_const_eval/src/interpret/call.rs:814-867`, `init_fn_tail_call`, is
commented "the 'canonical' implementation of tails calls, a pop of the current stack
frame, followed by a normal call which pushes a new stack frame, with the return
address from the popped stack frame". It copies the arguments, calls
`pop_stack_frame_raw`, takes `ret` and `unwind` from the popped frame's return
continuation, calls `init_fn_call` with the popped frame's return place and that
continuation, and only then cleans up the popped frame's locals. The caller of this
routine (`interpret/step.rs:578-596`) asserts that the frame index is unchanged, with
the message "evaluating this tail call pushed a new stack frame".

**LLVM backend.** `compiler/rustc_codegen_ssa/src/mir/block.rs:1638-1651` lowers the
terminator through the ordinary call path with `CallKind::Tail`, destination
`RETURN_PLACE`, no target and `UnwindAction::Unreachable`; lines 234-237 dispatch to the
backend's `tail_call`. `compiler/rustc_codegen_llvm/src/builder.rs:1443-1461`:

```rust
// line breaks adjusted
let call = self.call(llty, caller_attrs, Some(fn_abi), llfn, args, funclet, callee_instance);
llvm::LLVMSetTailCallKind(call, llvm::TailCallKind::MustTail);
match &fn_abi.ret.mode {
    PassMode::Ignore | PassMode::Indirect { .. } => self.ret_void(),
    PassMode::Direct(_) | PassMode::Pair { .. } | PassMode::Cast { .. } => self.ret(call),
}
```

Arguments passed indirectly (`PassMode::Indirect { on_stack: false }`) are first copied
to temporaries and then into the *caller's own* incoming argument slots, which are then
passed on (`block.rs:1184-1223`, `1281-1316`). The source comment gives the reason and
ties it to the signature rule: "Because guaranteed tail calls demand that the caller's
signature matches the callee's, the corresponding slot has the correct type."

**Measured** (`support/rust/tail_recursion.rs`; two mutually recursive functions; each
activation records the address of a stack local natively, or the backtrace length under
Miri; the recursion runs on a thread with an explicit stack size):

| Build | Steps | Thread stack | Result | Depth witness spread |
| --- | --- | --- | --- | --- |
| `become`, `opt-level=0` | 250,000 | 64 KiB | completed | 0 bytes |
| `become`, `opt-level=0` | 250,000 | 1 MiB | completed | 0 bytes |
| `become`, `opt-level=3` | 250,000 | 1 MiB | completed | 0 bytes |
| ordinary call, `opt-level=0` | 2,000 | 1 MiB | completed | 96,000 bytes (48 per step) |
| ordinary call, `opt-level=0` | 250,000 | 1 MiB | aborted (`SIGABRT`, "has overflowed its stack") | — |
| ordinary call, `opt-level=3` | 250,000 | 1 MiB | completed | 0 bytes |
| `become`, Miri | 250,000 | — | completed | 0 frames |
| ordinary call, Miri | 2,000 | — | completed | 2,000 frames |

The `opt-level=0` LLVM IR of the `become` build contains exactly two `musttail call`
instructions, each immediately followed by `ret`, for example

```text
%0 = musttail call i64 @_RNvCs…_14tail_recursion8odd_step(i64 %_6.0, i64 %_8.0)
```

and the x86-64 assembly transfers between the two functions with `jmp`, not `call`.

The `opt-level=3` row for the ordinary call shows that LLVM *may* turn an ordinary call
in tail position into a jump; the `opt-level=0` rows show that it is not obliged to.
That difference, not speed, is what `become` provides.

### 4. Destructor order

Basis: execution, cross-checked against the MIR in Findings 2.

`support/rust/drop_order.rs` gives every guard value a digit that its destructor appends
to a log; a callee body appends `9`.

| Scenario | Caller owns | Callee receives | `become` log | ordinary-call log |
| --- | --- | --- | --- | --- |
| 1 | parameter guard `1`, local guard `2` | fresh guard `3` | `2193` | `9321` |
| 2 | parameters `1`, `2`; locals `3`, then `4`, `5` in an inner block | fresh guards `6`, `7` | `54321976` | `97654321` |
| 3 | parameter guard `1` (forwarded as the argument), local guard `2` | the caller's own guard `1` | `291` | — |

All five logs are the same in three executions: native `opt-level=0`, native
`opt-level=3`, and Miri. Reading scenario 2: with `become` the caller's locals go in
reverse declaration order across both scopes (`5 4 3`), then its parameters in reverse
(`2 1`), then the callee body (`9`), then the callee's own parameters in reverse
(`7 6`). With an ordinary call the callee body and the callee's parameters come first.
Scenario 3 shows that an operand moved into the call is not destroyed by the caller:
guard `1` is destroyed once, by the callee, after its body.

### 5. Inlining

Basis: source + execution; the remark about intent is a reading of source comments.

The MIR inliner has three relevant sites at `14210df0…`
(`compiler/rustc_mir_transform/src/`):

- `inline.rs:555-556`: call sites are found by matching `TerminatorKind::Call` only,
  under the comment "FIXME(explicit_tail_calls): figure out if we can inline tail
  calls". A `TailCall` terminator is therefore never itself inlined.
- `check_inline.rs:73-86`, `is_inline_valid_on_body`: returns
  `Err("can't inline functions with tail calls")` if any block of the candidate callee
  ends in `TailCall`. It is called per call site at `inline.rs:640` and also backs the
  definition-site check for `#[rustc_force_inline]`.
- `inline.rs:445-448`: the same refusal inside the reachability walk, commented
  "FIXME(explicit_tail_calls): figure out how exactly functions containing tail calls
  can be inlined (and if they even should)". The block-remapping code at
  `inline.rs:1321-1324` is `unreachable!()` for `TailCall` on that basis.

The source describes the refusal as an open question, not as a protection of the stack
guarantee.

Observed (`support/rust/inline_refusal.rs`, two `#[inline(always)]` helpers identical
except that one ends in `become leaf(x)` and the other in `leaf(x)`), optimized MIR at
`opt-level=3`:

```text
fn caller_of_become:  _2 = helper_become(move _1) -> [return: bb1, unwind continue];
fn caller_of_plain:   scope 1 (inlined helper_plain) { … }   _2 = leaf(move _1) -> …
```

and `#[rustc_force_inline]` on a function ending in `become` is a hard error whose note
reads "incompatible due to: can't inline functions with tail calls".

The refusal is specific to MIR. In the LLVM IR of the same crate (function merging
disabled so both callers stay visible), at both `opt-level=0` and `opt-level=3`:
`helper_become` is not defined in the module, the string `musttail` does not occur
anywhere in the module, and `caller_of_become` calls `leaf` directly — `call` at
`opt-level=0`, `tail call` at `opt-level=3`. LLVM inlined the helper and turned the
guaranteed tail call into an ordinary call that returns into the caller. That is the
semantically correct shape (Findings 8, Theorem 2a) and costs at most the caller's own
frame. Without `-Z merge-functions=disabled`, `opt-level=3` emits `caller_of_become` as
an `alias` of `caller_of_plain` (recorded under `opt_level_3_default_function_merging`).

### 6. Symbol mangling: default, gating, mechanism

Basis: source; history from two upstream merge commits; execution for the gate.

`compiler/rustc_session/src/config.rs:1473-1475` at `14210df0…`:

```rust
pub fn get_symbol_mangling_version(&self) -> SymbolManglingVersion {
    self.cg.symbol_mangling_version.unwrap_or(SymbolManglingVersion::V0)
}
```

There is no release-channel test, so any compiler built from this source defaults to
`v0`. Lines 2500-2521 classify the values of `-C symbol-mangling-version`: `None` and
`V0` are "Stable values"; `Legacy` and `Hashed` are "Unstable values" and abort with
``"`-C symbol-mangling-version=legacy` requires `-Z unstable-options`"`` unless that flag
is given. The option's help text (`options.rs:2165-2167`) reads "which mangling version
to use for symbol names ('legacy', 'v0' (default), or 'hashed')". Both regions are
byte-identical at the two later commits.

History: at `683dd08db5808c41baceef49368fc82a6c4767bb` (merge of rust-lang/rust pull
request 89917, "sess: default to v0 symbol mangling on nightly", merged 2025-11-20) the
default was `V0` if `is_nightly_build()` and `Legacy` otherwise, and the explicit value
`legacy` already required `-Z unstable-options`. At
`1857d2ee9f35709c721f085a1d19816396df2779` (merge of pull request 151994, "switch to v0
mangling by default on stable", merged 2026-04-28) the function has the unconditional
form quoted above.

Observed: with no flag, every probe symbol begins `_R` and equals the symbol produced
with `-C symbol-mangling-version=v0`; `-C symbol-mangling-version=legacy` alone fails
with the quoted error; with `-Z unstable-options` it produces `_ZN…` symbols.

Dispatch (`compiler/rustc_symbol_mangling/src/lib.rs:263-316`): the version is taken
from the instantiating crate when there is one; `Legacy` falls back to `v0` for a
symbol longer than 65,000 bytes on targets using PDB debug info; `Hashed` wraps the
`v0` name.

**`v0` mechanism** (`compiler/rustc_symbol_mangling/src/v0.rs`). The mangler state
(lines 169-181) holds the output string and three maps whose "values are start
positions in `out`, in bytes": `paths`, `types`, `consts`. `print_type` (from line 445)
first emits basic types as fixed strings that are "never cached (single-character)" —
`b c e a s l x n i h t m y o j f d z u p`, with `C3f16` and `C4f128` for the two newer
float types. For any other type it looks the type up (`if let Some(&i) =
self.types.get(&ty) { return self.print_backref(i); }`, lines 482-484), otherwise
prints it and records `self.types.insert(ty, start)` — but "only cache types that do
not refer to an enclosing binder" (lines 603-608). `print_def_path` (lines 291-309)
does the same for `(DefId, generic args)` pairs. `print_backref` (lines 231-235) pushes
`B` and then `push_integer_62(i - start_offset)`, where the integer format is: `0` is
just `_`; `x > 0` is `x - 1` in base 62 followed by `_`.

**`legacy` mechanism** (`legacy.rs`). The symbol is the item path followed by
`17h{hash:016x}E` (`finish`, lines 207-212). For an ordinary function the generic
arguments are *not* printed into the path (`mangle` passes `&[]`, lines 62-81); they
enter only through `get_symbol_hash` (lines 115-171), which hashes the definition-path
hash, the item type, the function signature, the generic arguments, the instantiating
crate and an instance-kind discriminator into a 64-bit value ("64 bits should be enough
to avoid collisions").

### 7. Symbol mangling: measured scaling

Basis: execution; the per-level explanation is derived.

Crate `mangling_scale`, `pub fn touch_gen<T>() -> usize`, `struct Pair<A, B>`,
`D0 = u64`, `D(n+1) = Pair<Dn, Dn>`; one compilation per depth and mode; symbol read
with `llvm-nm`, demangled with `llvm-nm -C` (LLVM's demangler, a separate implementation
from rustc's mangler).

| Depth | `u64` leaves in the type | `legacy` bytes | `v0` bytes | `v0` backreferences | `v0` demangled bytes |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 2 | 49 | 63 | 2 | 59 |
| 2 | 4 | 49 | 71 | 4 | 113 |
| 3 | 8 | 49 | 79 | 6 | 221 |
| 4 | 16 | 49 | 87 | 8 | 437 |
| 5 | 32 | 49 | 96 | 10 | 869 |
| 6 | 64 | 49 | 105 | 12 | 1,733 |
| 7 | 128 | 49 | 114 | 14 | 3,461 |
| 8 | 256 | 49 | 123 | 16 | 6,917 |
| 9 | 512 | 49 | 132 | 18 | 13,829 |
| 10 | 1,024 | 49 | 141 | 20 | 27,653 |

Depth 1 and depth 10 `v0` symbols:

```text
_RINvCs6tOw9BmjSZ7_14mangling_scale9touch_genINtB2_4PairyyEEB2_
_RINvCs6tOw9BmjSZ7_14mangling_scale9touch_genINtB2_4PairIBH_IBH_IBH_IBH_IBH_IBH_IBH_IBH_IBH_yyEB1n_EB1j_EB1f_EB1b_EB17_EB13_EBZ_EBV_EBR_EEB2_
```

- The `v0` increments are 8, 8, 8, 9, 9, 9, 9, 9, 9 bytes (mean 8.667). Derived
  explanation: each level adds `I`, a backreference to the path of `Pair` (`BH_`), `E`,
  and a backreference to the first type argument. That last backreference is 3 bytes
  while its offset fits one base-62 digit (`BR_`, `BV_`, `BZ_`) and 4 bytes afterwards
  (`B13_` …), giving 1+3+1+3 = 8 and then 1+3+1+4 = 9. Growth is therefore linear with
  a logarithmic term in the offset width, not constant per level.
- At every depth the demangled `v0` name is string-equal to the fully expanded type
  generated independently by the probe (`mangling_scale::touch_gen::<mangling_scale::
  Pair<…>>`); the number of `u64` occurrences is exactly `2^depth`. The symbol is a
  lossless, compressed spelling of an exponentially large type.
- The `legacy` symbol is `_ZN14mangling_scale9touch_gen17h<16 hex digits>E` at every
  depth (49 bytes), the ten digests are pairwise different, and the demangled name is
  `mangling_scale::touch_gen::h<16 hex digits>` — the type argument cannot be read back.
- For small types `v0` is *longer* than `legacy` (63 versus 49 bytes at depth 1). The
  advantage of `v0` here is recoverability, not size.

### 8. Mechanized model (`support/TailCallDropOrderAndV0Mangling.lean`)

Basis: derived (machine-checked proofs about models defined in the file). 74 theorems;
`#print axioms` on 25 of them reports `propext` and `Quot.sound` for 16, `propext` alone
for 6, and no axioms for 3. The file contains no `sorry`, no `omega`, `bv_decide` or
`native_decide`, no `partial` or `unsafe` definition, and no use of `Classical`.

**Machine.** `Stmt` is `eff e` (an observable event: `emit n` or `drop r`),
`call f byRef`, `tailcall f byRef`, `useRef`, or `ret`. A `Frame` is
`(id, code, ref)`: a unique activation id, the statements still to run, and an optional
pointer argument holding the id of the activation it points into. A `State` is
`(stack, next, trace)`. `step` returns `Option State`, `none` meaning undefined
behaviour: `call` pushes a frame for the callee above the caller's frame (which keeps
its remaining statements); `tailcall` replaces the caller's frame with the callee's and
discards whatever followed in the caller; `useRef` yields `none` unless the pointee id
is on the stack. `run P n` iterates `step`.

**Lowering.** `Scopes` holds `params` and `blocks` (enclosing block scopes,
outermost first, each in declaration order). `lowerBecome sc moved f byRef` is defined
by a scope walk shaped like `break_for_tail_call`: scopes innermost-first, each scope
reversed, operands in `moved` skipped, then `tailcall`. The specification `lifoDrops sc
moved` is defined differently: reverse the single declaration-order list
`params ++ flat blocks` and filter. `scopeWalk_eq_lifo` proves the two agree.

| Theorem | Statement (paraphrased; exact text in the file) |
| --- | --- |
| `become_frame_reuse_and_lifo_drops` (Theorem 1) | From any state whose active frame holds `lowerBecome sc moved f byRef ++ junk`, running `(lifoDrops sc moved).length + 1` steps yields the state whose stack is the callee's frame (with its whole body) on top of the *unchanged* remaining frames and whose trace is the old trace followed by exactly `lifoDrops sc moved` as drop events. `junk` is irrelevant. |
| `run_depth_le` (Theorem 1′) | If no function body and no frame on the stack contains `call`, then for every `n` and every state reached by `run P n`, the stack is no deeper than at the start. |
| `tail_loop_depth_const`, `call_loop_depth_linear` | The one-statement self loop keeps depth `rest.length + 1` for every `n` with `tailcall`, and has depth `rest.length + 1 + n` after `n` steps with `call`. |
| `inline_configurations` (Theorem 2a) | Caller `pre ++ [call f] ++ post`, with `f = fpre ++ [tailcall g]`. On entry to `g`: the original and the "demoted" inlining (`pre ++ fpre ++ [call g] ++ post`) have the same frame contents and trace; the verbatim splice (`pre ++ fpre ++ [tailcall g] ++ post`) has the same trace but one frame fewer — `post` is gone. |
| `naive_inline_of_tailcall_unsound` (Theorem 2b) | For all `pre`, `fpre` and every event `x` with `post = [eff x]` and `g` empty: the original halts with trace `pre ++ fpre ++ [x]`; the verbatim splice halts with `pre ++ fpre` and cannot halt with the original trace. |
| `ce1_dangling_stack_borrow_across_tailcall_frame_reuse_ub` | In every state with fresh, pairwise distinct activation ids (an invariant of `step`: `step_fresh`, `run_fresh`), `tailcall f true` into a body starting with `useRef` gives `none` after two steps, while `call f true` gives a defined state. |
| `ce2_post_tailcall_caller_drop_violates_tail_position_and_order` | Scenario 1 under three lowerings: `become` lowering — log `2193`, depths `1,1,1,1,1,1,0`; drops after an ordinary call — log `9321`, depth reaches 2; drops placed after a `tailcall` in the same frame — log `93`, i.e. guards `2` and `1` are never destroyed. |
| `scenario_logs` | The model yields `54321976`, `97654321` and `291` for scenarios 2 and 3. |
| `decode_encode`, `encodeV0Dag_injective` (Theorem 3a, 3b) | `decodeV0Dag (encodeV0Dag t) = some t` for every type tree; hence the encoder is injective. |
| `encodeV0Dag_length_le` (Theorem 3c) | If the list `m` contains every compound subtree of `t`, the encoding has at most `2 * m.length + 1` tokens. Taking `m` duplicate-free makes this linear in the number of *distinct* compound subtrees. `tower_bound_is_tight` shows equality on the shared-children tower. |
| `ce3_naive_tree_mangling_exponential_vs_v0_dag_linear` | For `tower n` (`tower 0` a leaf, `tower (n+1) = node (tower n) (tower n)`): naive serialization has `2^(n+1) − 1` tokens, the backreference encoding `2n + 1`; at `n = 10`, 1,024 leaves, 2,047 versus 21 tokens. |
| `digest_mangling_not_injective`, `digest_mangling_has_no_decoder`, `digest64_mangling_collides` (Theorem 4) | For every function `h` on type trees with values below any bound `n`, two different trees have the same `(path, h t)`; no decoder exists; in particular any function reduced modulo `2^64` collides. |

How the model touches the measurements: `ce2…` and `scenario_logs` compute, inside the
kernel, the same five numbers that real rustc printed in Findings 4. The three `become`
logs come out of `lowerBecome`, the lowering whose behaviour Theorem 1 states in
general; the two ordinary-call logs come from hand-written statement lists that put the
caller's drops after the call; the callee bodies are hand-written in both cases (log
`9`, then drop the callee's parameters in reverse). That is a consistency check between
the model's caller-side drop order and rustc's, on those programs. Theorem 2a's "demoted" shape is the
shape observed in LLVM's output in Findings 5. The tower is the `Pair<T, T>` family of
Findings 7; the model's `2n + 1` tokens and rustc's 8-to-9 bytes per level are both
linear but are different units and are not derived from one another.

### 9. Anneal at `c131b320…`

Basis: source.

- `trusted/lean/Trusted/MirAst.lean:782-784`: the constructor `.unsupported` of
  Anneal's trusted `TerminatorKind` "represents all other `TerminatorKind` variants
  (`UnwindTerminate`, `Drop`, indirect `Call`, `TailCall`, `Yield`, `CoroutineDrop`,
  `FalseEdge`, `FalseUnwind`, and `InlineAsm`)".
- `trusted/correspondence/Trusted/Correspondence.lean:2185`: the terminator hook is
  `tailCall := fun _ _ st => (st, .error (.unsupported "TailCall unsupported"))`; the
  surrounding documentation (lines 2107-2110) lists it among hooks that "fail closed".
- The vendored Lean Miri model does implement the terminator:
  `vendor/lean-miri/Miri/Interpreter/Call.lean:646-663` (`initFnTailCall`) pops the
  frame, rejects a tail call at the root of the stack, re-enters `initFnCall` with the
  popped frame's return place and continuation, and then cleans up;
  `evalTailCallTerminator` (lines 681-688) requires the frame index to be unchanged
  ("evaluating this tail call pushed a new stack frame"), and
  `Miri/Interpreter/ControlFlow.lean:181-189` repeats that check as "tail call changed
  frame index". This mirrors the rustc routine in Findings 3 step for step.

So a Rust body containing `become` is outside what Anneal's trusted semantics accepts
at this commit, by explicit rejection rather than by silent mis-modelling.

### 10. Statements that sound right and are not

Each line is a correction established above.

- "The signature and ABI rules are enforced by the HIR type checker." No: by
  `rustc_mir_build/src/check_tail_calls.rs` (Findings 1).
- "`StorageDead` is emitted for all caller locals and parameters before the tail call."
  No: only for non-parameter locals whose type needs dropping (Findings 2).
- "Drop elaboration orders the drops before the tail call." No: MIR building does;
  `elaborate_drops.rs` never mentions `TailCall` (Findings 2).
- "The MIR inliner refuses tail calls in order to protect the stack bound." The source
  calls it an unresolved question, and LLVM inlines such callees anyway (Findings 5).
- "`v0` grows by a constant number of bytes per level." It grew by 8 and then by 9;
  the backreference width depends on the offset (Findings 7).
- "`v0` symbols are shorter than `legacy` ones." Not for small types (Findings 7).

## Boundaries

**Not examined.**

- Any target other than `x86_64-unknown-linux-gnu`, any codegen backend other than
  LLVM, `-C panic=abort`, optimization levels other than 0 and 3, LTO, and incremental
  compilation.
- Execution on any compiler other than `1.98.0-nightly (14210df0e)`. For
  `3ef0c22c…` and `c7d5ba59…` only source was compared; in particular the
  `extern "tail"` ABI and its exemption from the signature rule were read, not run.
- Run-time behaviour of unwinding: a panic in a pre-jump destructor, or a panic in the
  callee propagating past the replaced frame. The MIR cleanup blocks were read only.
- Tail calls through function pointers, trait methods, generic callees, or with
  arguments passed indirectly; the indirect-argument copying code was read only.
- `become` during compile-time evaluation, and debug information or backtraces across
  tail calls.
- `v0` mangling of const generics, lifetimes and binders (types referring to an
  enclosing binder are deliberately not cached), and the `hashed` mode.
- The hash function behind `legacy` digests. It lives in an external crate
  (`rustc-stable-hash` 0.1.2 according to the toolchain's `Cargo.lock`) that was not
  read; this report calls the value a 64-bit digest and nothing more specific.
- Which stable release first shipped the unconditional `v0` default. Only the merge
  commit and its date were established.
- LLVM's own specification of `musttail`. The guarantee is reported here as observed
  behaviour plus rustc's use of the marker, not as a quotation of LLVM's reference.
- Whether Anneal's vendored Lean Miri model agrees with rustc's interpreter beyond the
  structural correspondence read in Findings 9.

**Unknown.**

- Whether a later rustc will let the MIR inliner handle tail calls; the source marks it
  as undecided at all three commits.
- Whether any two real Rust instantiations have ever produced equal `legacy` digests.
  None was observed among the ten probe symbols; Theorem 4 shows only that collisions
  must exist for any fixed-width digest over an unbounded set of types.

**Known not to apply.**

- The constant-stack property does not extend to ordinary calls in tail position: at
  `opt-level=0` they grow the stack and overflowed.
- The signature-equality rule does not apply to `extern "tail"` callees at the two
  later commits, and `extern "rust-call"` is not tail-callable at `c7d5ba59…`.
- The Lean theorems do not apply to rustc or to rustc's mangler. They apply to the
  machine and encoder defined in the file. In particular the token counts of Theorem 3c
  are not byte counts of `v0` symbols.
- The frame-depth measurement by stack addresses is meaningful only natively; under
  Miri the probe uses the backtrace length instead.

**Unsupported (rejected by the tool).**

- By rustc at `14210df0…`: `become` in closures, on operators and non-call
  expressions, to closures called directly, to intrinsics, with mismatched ABI or
  signature, with CMSE, interrupt, GPU/PTX kernel or `Custom` ABIs, with C-variadic
  caller or callee, from a function carrying the caller-location attribute, with an
  argument borrowing a caller local or by-value parameter, without the feature gate.
- By rustc: `-C symbol-mangling-version=legacy` or `=hashed` without
  `-Z unstable-options`.
- By Anneal at `c131b320…`: any body containing `TailCall`.

**Stronger conclusions that the evidence does not establish.**

- That `become` is sound under unwinding, or on other targets and ABIs.
- That the explicit tail call feature is stable or complete: its gate is `incomplete`.
- That the Lean model's `lowerBecome` *is* `break_for_tail_call`. It was written to
  have the same shape and reproduces five measured logs; no proof relates the two.
- That LLVM always demotes an inlined `musttail` as observed; two optimization levels
  and one small crate were examined.

## Evidence

All observations were made on 2026-11-21.

**Commit identities.** Each 40-hex id below was resolved through the GitHub REST API on
the observation date (`repos/<owner>/<repo>/commits/<ref>`, or `pulls/<n>` for the two
merge commits): `rust-lang/rust` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (also
printed by the executed `rustc -vV` as `commit-hash`), `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`,
`c7d5ba59d8e11ee2e2204b173458eec4cb41c973` (returned for `HEAD`, committer date
2026-11-20T16:58:50Z), `683dd08db5808c41baceef49368fc82a6c4767bb` (merge commit of pull
request 89917), `1857d2ee9f35709c721f085a1d19816396df2779` (merge commit of pull request
151994); `joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613`; `leanprover/lean4`
`5045d0056413266e57c625dcd7c365b10e377c52` (returned for tag `v4.34.1`, and printed by
`lean --version`).

**rustc source.** Line numbers in Findings refer to `14210df0…`. They were read from
the toolchain's `rustc-src` component; for the 22 files cited, that copy was compared
byte-for-byte against `raw.githubusercontent.com/rust-lang/rust/14210df0…/<path>` and
all 22 were identical. Paths under `compiler/`:

```text
rustc_middle/src/mir/syntax.rs:823-851            TailCall variant and documentation
rustc_middle/src/mir/terminator.rs:532-539,619-637  no successors, no unwind edge
rustc_hir_typeck/src/expr.rs:905-929              check_expr_become
rustc_mir_build/src/check_tail_calls.rs:55-192    check_tail_call (ABI 134-140, signature 150-161)
rustc_mir_build/src/builder/mod.rs:75             check_tail_calls forced before MIR building
rustc_abi/src/extern_abi.rs:316-358               supports_guaranteed_tail_call
rustc_feature/src/unstable.rs:534                 (incomplete, explicit_tail_calls, "1.72.0", Some(112788))
rustc_mir_build/src/builder/expr/stmt.rs:107-143  lowering of `become`
rustc_mir_build/src/builder/scope.rs:1095-1203    break_for_tail_call (assert at 1192)
rustc_borrowck/src/lib.rs:923-928,1008-1027       operand consumption; exit invalidation
rustc_mir_transform/src/inline.rs:445-448,555-556,640,1321-1324
rustc_mir_transform/src/check_inline.rs:73-86     is_inline_valid_on_body
rustc_codegen_ssa/src/mir/block.rs:39-45,234-237,1184-1223,1281-1316,1638-1651
rustc_codegen_llvm/src/builder.rs:1443-1461       tail_call, MustTail at 1455
rustc_const_eval/src/interpret/call.rs:814-867    init_fn_tail_call
rustc_const_eval/src/interpret/step.rs:578-596    frame-index assertion
rustc_session/src/config.rs:1473-1475,2500-2521   default version; unstable values
rustc_session/src/options.rs:2165-2167            option help text
rustc_symbol_mangling/src/lib.rs:263-316          version selection and dispatch
rustc_symbol_mangling/src/v0.rs:169-181,231-235,291-309,445-609,974-979
rustc_symbol_mangling/src/legacy.rs:62-81,115-171,207-212
rustc_mir_transform/src/elaborate_drops.rs        (whole file: no occurrence of `TailCall`)
```

Lines at the other two commits and per-region digests are in
`support/upstream_anchors.json`, produced by `support/locate_upstream_anchors.py`. The
table was generated twice, once from files fetched beforehand and once by the script's
own network mode, with byte-identical output.

**Anneal source** at `c131b320…`: `trusted/lean/Trusted/MirAst.lean:758,782-784`;
`trusted/correspondence/Trusted/Correspondence.lean:2107-2110,2185`;
`vendor/lean-miri/Miri/MIR/Syntax.lean:552`;
`vendor/lean-miri/Miri/Interpreter/Call.lean:646-663,681-688`;
`vendor/lean-miri/Miri/Interpreter/ControlFlow.lean:124,181-189`.

**Execution.** Toolchain as reported by the tools themselves:

```text
rustc 1.98.0-nightly (14210df0e 2026-05-31)
commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65
host: x86_64-unknown-linux-gnu
LLVM version: 22.1.6
llvm-nm: LLVM version 22.1.6-rust-1.98.0-nightly
```

The Miri driver is the `miri` binary of that toolchain; its standard library was built
with `cargo miri setup` from the toolchain's own `rust-src` component and vendored
dependencies, offline. Operating system Linux, machine `x86_64`.

The whole empirical part is one command, run from the package directory:

```text
python3 support/probe_tail_calls_and_v0_mangling.py \
    --rustc <nightly>/bin/rustc \
    --miri <nightly>/bin/miri --miri-sysroot <miri sysroot> \
    --out support/probe_results.json
```

It took about one minute, most of it the 250,000-step Miri run, and ended with
`checks: 28/28 passed`. The script copies `support/rust/*.rs` into a temporary
directory, invokes the tools with relative file names, and records for every command
its argument list, exit status and output. It contains no table of expected
measurements; its 28 checks compare observed values with each other or with facts
derived from the probe sources (for example the reverse of the declaration order in
`drop_order.rs`). Recorded per section:

- `tail_recursion`: four builds, six native runs, the `musttail` lines of the IR, the
  assembly transfer instructions, two Miri runs.
- `drop_order`: logs from three executors; built and post-`ElaborateDrops` MIR of
  `tail_caller` verbatim; normal-path event lists for `tail_caller2`.
- `rejections`: full diagnostics of seven rejected programs, the accepted control, and
  the tail-call block of the rejected local-borrow program's built MIR.
- `inline_refusal`: optimized MIR of both callers; LLVM call lines at two levels.
- `mangling`: thirty compilations (ten depths, three modes), symbols, lengths,
  demangled lengths, the equality test against the expanded type, the gate error.

**Mechanization.** `support/TailCallDropOrderAndV0Mangling.lean` (1,386 lines,
74 theorems), checked with

```text
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
    TailCallDropOrderAndV0Mangling.lean
```

using Lean `4.34.1` (commit `5045d005…`). Exit status 0 with warnings treated as
errors. The transcript, including all 25 `#print axioms` lines, is
`support/lean_check_output.txt`.

**Package contents.**

```text
support/probe_tail_calls_and_v0_mangling.py   empirical probe driver
support/probe_results.json                    its output from the run described above
support/rust/tail_recursion.rs                `become` versus ordinary call, depth witness
support/rust/drop_order.rs                    three destructor-order scenarios
support/rust/inline_refusal.rs                two helpers, two callers
support/rust/reject_*.rs (7 files)            programs that must be rejected
support/rust/accept_borrow_plain_call.rs      control for the borrow rejection
support/locate_upstream_anchors.py            line and digest locator for cited regions
support/upstream_anchors.json                 its output for the three rustc commits
support/TailCallDropOrderAndV0Mangling.lean   the mechanization
support/lean_check_output.txt                 kernel-check transcript
```

## Revalidation

Cheapest first. Each item says what it does and does not establish.

1. **A different rustc (a few minutes).** Run the probe command from Evidence against
   the other toolchain and compare `checks` and the tables in Findings 3, 4 and 7.
   A failing `reject_*` check after the `extern "tail"` ABI exists is expected only if
   a probe source is changed to use it; the preserved sources do not. A change in the
   `v0` byte counts with unchanged leaf counts and unchanged demangled equality means
   the encoding details moved but losslessness held. The probe needs nightly-only
   flags and cannot run on a stable compiler as written.
2. **Did the cited source move? (about a minute, no checkout.)**
   `python3 support/locate_upstream_anchors.py <old sha> <new sha>` prints, per region,
   the line at each commit and whether the text is identical. A `null` line means the
   anchor text disappeared and that finding must be re-read by hand. Regions already
   known to differ between the audited commits are listed in Applicability.
3. **Drop order only.** Compile and run `support/rust/drop_order.rs`; expect the five
   lines `2193`, `9321`, `54321976`, `97654321`, `291`. To see *where* the order comes
   from, add `-Z dump-mir=tail_caller2` and read the `built` dump: the drops must
   precede `tailcall` and no `StorageDead` may name a parameter.
4. **Constant stack only.** Build `support/rust/tail_recursion.rs` at `opt-level=0` and
   run `./tail_recursion 250000 65536`; `WITNESS_SPAN=0` is the property. Rebuilding
   with `--cfg plain_call` must make the same invocation abort; if it does not, the
   control has stopped discriminating and the first result means nothing.
5. **Default mangling only.** Compile any generic function without a mangling flag and
   look at the symbol prefix (`_R` for `v0`, `_ZN` for `legacy`); then check that
   `-C symbol-mangling-version=legacy` without `-Z unstable-options` is still an error.
   For the source of truth read `get_symbol_mangling_version` in
   `compiler/rustc_session/src/config.rs`.
6. **Mechanization.** Re-run the `lean` command from Evidence with Lean `4.34.1` and
   compare the `#print axioms` lines with `support/lean_check_output.txt`. A newer Lean
   may rename library lemmas (`ite_eq_left`, `List.mem_append`, `Nat.two_pow_pos` and
   similar are the only library facts used); such breakage is about the library, not
   about the statements. Passing establishes the theorems about the model, never a
   property of rustc.
7. **Anneal.** `grep -n "TailCall unsupported" trusted/correspondence/Trusted/
   Correspondence.lean` at the commit of interest. If the string is gone, Anneal's
   treatment of tail calls has changed and Findings 9 must be redone from the new
   hook's definition.

What has no cheap check: behaviour under unwinding, on other targets, with indirect
arguments, and with the `extern "tail"` ABI. Those need new probe programs and, for the
ABI, a compiler built from a commit that has it.
