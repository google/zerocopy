# Proposed next E33 codegen and Windows gates

*Authored by an AI agent acting on joshlf's behalf.*

This is a plan, not execution authority or completed code generation. Current
results are trusted compiler FnAbi captures and comparisons. They do not report
physical registers, stack locations, shadow space or emitted machine semantics.

## Host: four matched, compile-only outputs

After parent review, compile exactly the unchanged subjects/vector source for
its same four host profiles, once per profile, with the pinned May1 compiler,
explicit sysroot and the same edition/crate/target/optimization/panic/CPU/options.
Replace observer `--emit=metadata` with rustc `--emit=llvm-ir,asm,obj`, in fresh
owned directories. Proposed argv templates and identities are in the adjacent
JSON. No linking, fixture execution, foreign call or vector execution is needed.
Use one compiler at a time with monitored RSS, bounded wall time/output and
before/after identity checks; preserve the exact five vector warnings and stop
on any additional diagnostic. No warning suppression or representation edit.

Bind all three artifacts to their actual source/profile and full FnAbi packet,
plus compiler/backend identities, command/environment, output hashes and actual
target metadata. Inspect the LLVM module target/datalayout and selected function
signatures and attributes; inspect the emitted assembly and actual object ranges,
relocations and instruction bytes rather than assuming the text and object agree.
Existing Apple tools may read host Mach-O; identify their actual bytes/versions
when used. A text parser/object decoder is another trusted component unless proved.
No formal rustc/LLVM-to-machine or ABI-conformance theorem follows from matching
these observations.

| Fixed subject | Concrete observation to extract |
|---|---|
| C/system narrow u8/i16/bool | Actual extension in LLVM interface and entry/return code, compared with query extensions. |
| Pair versus Rust tuple | Query Cast versus Pair; actual LLVM operand count/types and object-level accesses, without claiming different physical registers solely from different IR shape. |
| Big | Ret.mode Indirect should connect through the inspected lowering to the actual hidden result parameter and selected result-pointer register/access. Verify actual bytes, not a hardcoded AArch64 x8 assumption. |
| HFA | Four-byte floating uniform/consecutive cast versus actual LLVM and physical passing; inspect selected body only. |
| Pointer/reference/UnsafeCell | Map query attributes to emitted positions. At opt0 many attributes are suppressed; at opt2 dereferenceable may replace explicit nonnull. Interpret using actual get_attrs source; absence is not a Rust permission result. |
| Slice/unit | Pair splitting and omitted Ignore operands; keep source argument count separate from LLVM/machine count. |
| track_caller | Actual extra location operand on direct function; do not confuse it with the unused function-pointer alias or prove a coercion/shim theorem. |
| Twelve-scalar driver | Incoming stack accesses and outgoing non-tail external call argument placements; derive offsets relative to actual prologue/call/return state. FnAbi Direct does not mean all12 values fit registers. |
| Variadic driver | Actual foreign-call signature plus promoted i32/f64/raw-pointer operands; distinguish fixed declaration inputs from call extras. No opaque foreign callee executes. |
| V4 | Experimental compiler-specific C/system Direct versus Rust Indirect at size/alignment16. Preserve FFI-unsafety warnings; do not claim a portable/safe C vector contract or execute it. |

The original source exports20 ordinary non-generic functions. Its two generic
query instances and four alias/extra-query entries need not produce emitted
bodies: those generic instances are unused and the aliases are types. Do not
claim every queried entry has a corresponding emitted function. An actual
function-pointer coercion/shim or explicit generic-caller codegen control would
require a separate source/claim grant, preserving the original fixtures.

## Windows: explicit missing setup and consumer-domain extension

Read-only inventory still finds only aarch64-apple-darwin target libraries in the
May1 toolchain. Its installed channel manifest advertises the matching target
archive:

```text
https://static.rust-lang.org/dist/2026-05-01/rust-std-nightly-x86_64-pc-windows-msvc.tar.xz
sha256 0e217c42f8f89e98b255461f96d75b6aef812a9d192d9eb1826a4ff336e050e2
```

No archive was fetched or installed here. Parent-owned setup must verify exact
archive/extracted core/std identities and the May1 compiler compatibility; do
not substitute the separate Rust1.89 E08 targets. Backend target support remains
unqueried. This compile-only library stage needs no Windows SDK, linker or
runtime, but actual compiler behavior must confirm whether further resources
are needed. Do not reinterpret setup/operational errors as target unsupportedness.

The current consumer rejects non-Darwin/Apple-M1 profiles by design. Windows
cannot be admitted merely by changing a candidate's target string. Prepare a
separate consumer-owned catalog/authority/profile with the exact original
subject/selector hashes and explicit x86_64-pc-windows-msvc/x86-64 options. A
reviewed, distinct version may admit only that named additional profile, with
matching target-library identities, preserving the current host consumer and
all accepted packet meanings. No such new consumer or Windows query is executed
or authorized by this plan. The optional Windows profile in the historical
preparation is a lead, not an already accepted request.

Propose one ordinary-subject Windows opt2 FnAbi capture followed by its fresh
whole-packet check and matched IR/asm/COFF output. Keep vectors outside the first
Windows gate; the experimental SIMD/FFI diagnostic boundary does not disappear
on changing targets. Bind target, CPU and actual convention/hidden-result modes;
a generic canonical `C` label does not erase platform identity.

Use the actual twelve-argument driver to inspect the incoming register/stack
locations and outgoing non-tail call. For the Microsoft x64 convention inspect
the actual caller reservation/accesses for the32-byte home/shadow area, stack
argument offsets, alignment, return address and result pointer. Do not equate
all reserved frame bytes with shadow space, infer it from FnAbi alone, or assume
one fixed total frame size. Pair/Big cases can discriminate Microsoft aggregate
indirection from Darwin's smaller casts. Reading actual COFF/disassembly may
need a compatible existing tool; confirm availability/identity rather than
installing anything under this plan.

The earlier four-target clang C report is comparison evidence from a different
compiler/language, not this actual Rust result. No native Windows or foreign
execution, arbitrary cross-target theorem, unwinder/resource theorem or universal
Rust ABI stability claim is proposed.
