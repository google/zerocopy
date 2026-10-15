# Matched Rust, assembly and zerocopy pilot on AArch64 and emulated x86-64

## Summary

The same valid-input Rust1.89 fixture passed four finite runs: native Linux
AArch64 container processes at optimization0 and3, and Linux x86-64 SysV
processes under QEMU user-mode emulation at optimization0 and3. Each unchanged
positive image returned0, produced empty stderr and printed its exact success
line reporting4,617 harness checks. The total reported count is18,468; it is
not a count of distinct ISA transitions or independent proofs.

The fixture covers actual whole-function and inline assembly for multiply,
carry, byte-swap, load/store, disjoint copy, pointer return, inline labels,
C-ABI helper calls and16-byte SIMD. It also compiles and calls actual pinned
zerocopy operations. Independent integer/byte vectors were fixed before
compilation. Exact final image/function bytes, call relocations, caller ABI,
selected frame metadata, loader identities and run receipts are preserved.

The compiler findings matter beyond the passing values: an optimized private
zerocopy decoder takes a promoted scalar through Rust fastcc rather than its
source-level reference, and the optimized zerocopy16-byte copy uses overlapping
scalar operands whose widths sum to17 per direction while their interval
union is16. Equal final results do not make these access traces equivalent to
the handcrafted16-byte SIMD copy. No universal Rust/ISA/compiler/resource
refinement or complete access-model theorem is established.

## Applicability

The source is [pilot.rs](pilot.rs), SHA256
`1b9466576e315530e54eea9622d102e59ae219177473440c2ebade46fd9e4616`,
with [AArch64](aarch64.s) and [x86-64](x86_64.s) whole-function bodies.
The actual dependency is zerocopy0.8.63 from google/zerocopy commit
`8d8ed8dcc98c991d32cee3c3a84e129f29cba136`; selected regular-file hashes and
its inspected clean-source receipt are preserved. No license symlink was
followed or source modified. Direct rustc builds use no Cargo invocation,
optional feature, derive or proc-macro build.

All eight accepted crate/harness compilations use one Rust1.89 binary at
commit `29483883eed69d5fb4db01964cdf2af4d86e9cb2`, LLVM20.1.7, and matching
AArch64/x86-64 GNU std components: opt-level0 or3, codegen-units1,
panic=abort, overflow-checks=yes, no LTO or target-cpu=native. The native
GNU linker and x86 GNU cross-linker identities are retained. Default cfg
query output mentioning panic=unwind is not the actual panic=abort profile.
The original harness temporary-borrow E0716 was corrected only by binding a
U64 to a named local before inspecting its write_to error; original source,
diagnostic and successful pre-existing rlib remain preserved.

The native runs are AArch64 processes in the existing Linux VM/container,
not macOS ABI experiments. The x86-64 runs use installed Debian QEMU7.2.22,
package1:7.2+dfsg-7+deb12u18+b3, binary SHA256
`ca7b4d72cb2a1a36dd63e31ae989ec909d4c4a711981bc318ae64ed191e96167`,
explicit `-cpu qemu64-v1 -L /usr/x86_64-linux-gnu`. These are emulated
observations, not physical x86 hardware results. Source/model inspection and
installed catalog identify the selected SSE2 baseline; no guest feature
probe or QEMU rebuild was performed. Native feature metadata reports asimd.
Compiler CPU defaults are not physical CPU identity.

The C boundary passes only scalar integers and pointers, not aggregate or
vector-valued ABI arguments/returns. Memory calls use live initialized
u64/16-byte arrays with sufficient8/16-byte alignment, exact in-allocation
spans and distinct output allocations. Copy inputs/outputs do not overlap;
selected read-only inputs may alias on diagonal cases. Returned pointers use
offsets0..16 within the same live16-byte array; one-past is compared and never
dereferenced. No invalid span, bad ABI, misannotated asm, altered executable
or deliberately undefined Rust case was executed. [CONTRACTS.md](CONTRACTS.md)
fixes the complete source-level domain and each selected effect/clobber claim.

Runtime evidence was acquired/revalidated on2026-10-15 UTC
(2026-10-14 America/New_York); REPORT.json uses the UTC calendar date.
Historical preparation/status documents remain immutable snapshots, not the
current execution status. [runtime-results.json](runtime-results.json) is the
current aggregate result.

## Findings

### The shared finite corpus actually ran in four configurations

Basis: source + execution. The same generated [vectors.rs](vectors.rs) and
[expected.json](expected.json) feed every build; Python unbounded arithmetic
and explicit byte lists generated them before compilation. The Rust baselines
and actual zerocopy operations provide additional comparisons, though their
compiled behavior still depends on the same compiler. Some comparisons may be
folded or inlined by optimization; a check count does not prove that every
source operation remains a distinct emitted call.

| Case | Fixed corpus | Value/resource observations in the harness |
|---|---|---|
| u64 multiply to128 |289 pairs | Independent product low/high limbs; Rust u128; output sentinels |
|128-bit add and carry |144 pairs | Carry propagation/overflow; Rust overflowing_add; output sentinels; diagonal shared reads |
| inline carry-in/out |578 triples | carry-in0/1; sum modulo2^64 and outgoing carry; Rust u128 |
| byte-swap and real wire conversion |17 words | BSWAP/REV versus explicit byte oracle; actual U64<BigEndian> new/set/get/read/write; native-endian read on these little-endian targets |
| whole/inline load and store |17 words | Exact live aligned8-byte locations; source equality and destination guards; Rust baseline |
| scalar/SIMD/zerocopy/Rust copy16 |12 patterns | Four final byte arrays, disjoint guarded spans, unchanged source; actual zerocopy array read/write and ref_from_bytes pointer identity |
| whole-function pointer return |204 calls | Same-allocation pointer equality at offsets0..16, including one-past without dereference |
| inline label |17 words | Declared label blocks with no output operands;0 maps to17, other values to41 |
| C-ABI helper bounce |289 pairs | Rotate/xor/wrapping-multiply+1 oracle; assembly and Rust bounces each call the real helper exactly once, counted separately |
|16-byte SIMD wrapping add |144 pairs | Sixteen independent modulo256 lanes; diagonal shared input; output/source guards |
| safe zerocopy size rejection |Lengths7/9 | Read/write Err and unchanged destination; short spans never reach assembly |

[Source-loop counts](source-call-counts.json) distinguish these categories:
per profile there are1,145 whole-function assembly entry invocations and629
inline-wrapper invocations. The4,617 harness checks also include Rust baseline,
input-domain, alignment, guard, view and safe-error checks; they are not4,617
foreign calls. These invocation totals are derived from the fixed source loops,
not observed hardware call-trace counters. Optimized Rust wrappers may inline
or fold, and the helper's callbacks are separate selected callee behavior.

The success streams are exact bytes, including the final newline:

```text
E46_OK arch=aarch64 checks=4617 native_or_emulated=external_receipt
E46_OK arch=x86_64 checks=4617 native_or_emulated=external_receipt
```

Each line occurred once for each corresponding optimization profile. Complete
raw streams, statuses and actual argv are retained per image:

| Actual image | Execution | Final ELF SHA256 | Status / result |
|---|---|---|---|
| aarch64-O0 | native-AArch64-container | `adb86a7669598af8b9fa65d84bdea9b652fbc95171bff686fa3af85a24d10f20` | 0 / empty stderr / 4,617 |
| aarch64-O3 | native-AArch64-container | `b8047348558fdbc9fb7335e561dbb93f2983a9158f6604b26cfe8ae3d82f87f8` | 0 / empty stderr / 4,617 |
| x86_64-O0 | QEMU-user-x86_64-emulated | `ab6265e1c5333c11e971973b39b4cbc0a1ada16763c8c70515b8d881ce40ed4c` | 0 / empty stderr / 4,617 |
| x86_64-O3 | QEMU-user-x86_64-emulated | `64a1efa22c13b1b01e540193225fc50f7dd3911cd387a592165f7fe566c7a144` | 0 / empty stderr / 4,617 |

[The sequence receipt](runtime-captures-v2/SEQUENCE.json) and
[outer driver receipt](runtime-driver-v2/receipt.json) record successful
completion. The reported per-call elapsed times include Docker/supervision;
this investigation makes no benchmark or performance-ranking claim.

### Actual byte, caller and metadata linkage constrain the comparison

Basis: source + execution + derived inspection. The
[function binding inventory](compile-static/function-bindings.json) extracts
actual symbol ranges/body bytes and hashes from each object and final ELF,
with raw-byte cross-checks against GNU objdump. Of40 whole-function
object/image pairs,36 have exact equal bytes without body relocations. Four
helper bounces differ only at a checked call relocation: AArch64 CALL26 at
function offset8/addend0, or x86 R_X86_64_PLT32 at field offset5/addend-4.
Decoded final targets match the actual Rust pilot_helper symbol. Whole-function
object body hashes are equal between O0/O3 within each architecture. Other
Rust-generated body relocations are hashed, not universally verified.

Actual LLVM declarations use default C calling convention for all ten foreign
entries. Selected call sites use AArch64 X0/X1/X2 or SysV RDI/RSI/RDX as their
scalar/pointer signatures require. The bounded reader resolves AArch64 BL and
x86 RIP/GOT calls through actual relative relocation slots. One optimized
pointer call hoists a LEA into R13: nextPC0xc9d5 plus displacement-0xf7a
is pilot_ptr0xba5b, then CALL R13 at0xcb93 uses RDI/source and RSI/index.
The exact opcode/target route and preservation interval were inspected;
there is no universal register/CFG/loader proof.

The helper bounce restores its selected ABI frame: AArch64 saves X29/X30 in
an aligned16-byte frame; SysV subtracts8 from entry RSP8 modulo16 before its
call and restores it before RET. Actual object/final FDE/CIE rules match those
selected frames. Rust1.89 does not list .cfi_* in its guaranteed directive
subset, so LLVM/GNU handling remains an inspected assembler-specific premise.
No unwind experiment occurs in this panic=abort fixture. The optimized Rust
helper also has a real atomic counter and, on AArch64, an
__aarch64_ldadd8_relax call; those compiler/runtime accesses and frames are
additional to the handwritten bounce's own instructions.

Both final targets' PT_INTERP, NEEDED and version-needs sections were inspected.
The actual x86 prefix contains lib64/ld-linux-x86-64.so.2 resolving to its
matching cross loader; all required version-name sets are subsets of actual
selected loader/libc/libgcc definitions. All seven path identities (six unique
files), including the native loader, matched before/after every run.
Actual successful loading is observed here, while loader/libc implementation
correctness remains trusted. No ldd or loader invocation was used in the
static-inspection phase.

### Real zerocopy code separates interval footprints from access multiplicity

Basis: source + execution + derived inspection. At O3, private zc_decode's
source-level reference is promoted to i64 through internal fastcc on both
targets; the emitted REV/BSWAP consumes that scalar. It must not be assigned
the C raw-pointer contract of an unrelated assembly entry by its function name.
The named rust_load baseline disappears at O3. At O0 inline wrappers also
include compiler stack/red-zone spills; nomem/nostack promises concern the
inline template, not every surrounding wrapper instruction.

On both targets, the real O3 zerocopy copy16 adapter uses memory operand
widths4@0,4@3,8@7 and1@15 on each source/destination, in differing order.
Thus byte3 is read/written twice, widths sum to17 per direction, and the byte
interval union is16. The handwritten scalar copy uses two8-byte elements;
the SIMD copy uses one16-byte load/store. All returned the expected arrays on
the disjoint valid corpus. These value observations do not establish equal
access events, absence of extra reads, or a generic scalar/SIMD footprint model.
[Selected disassembly/IR and330 static checks](compile-static/STATIC-HANDOFF.md)
preserve the actual widths, fastcc promotion, callers and frame evidence.

### Negative controls remain data, and the failed reader is preserved

Basis: execution on data. The initial runtime capture helper stopped before
its first target call: its new reader took18 header bytes while the retained
ELF identity inventory takes20, including e_machine. All full library hashes,
sizes, resolved paths and link metadata agreed; no image or source changed.
The original helper, STOP trace, raw metadata output and
[diagnosis](runtime-stop-v1-diagnosis.json) remain intact. The
[exact v2 diff](runtime-v2.diff) changes only18 to20 and versioned evidence
paths. A [pure-data regression](runtime-header-v2-regression.json) checks all
seven paths: old18 rejects, exact20 accepts, changed e_machine rejects, and
changed earlier byte rejects (28 passes). No malformed header is loaded.

After each actual positive run, six copies of captured stdout/stderr/status
are altered as DATA ONLY: wrong printed count, wrong architecture, omitted
newline, trailing stdout, added stderr and nonzero status. All24 copies are
rejected by the exact receipt matcher. Original raw streams/statuses remain
unchanged. These test receipt admission, not injected bad machine returns,
guard corruption, ABI violations or a formal checker theorem. The one-line
stdout does not contain per-case return/guard records; none are invented.
The earlier actual function-byte identity controls also reject two one-bit
changed candidates as bytes, without creating or executing changed images.
Prepared arithmetic/span/alignment/overlap/hidden-read controls retain their
separate data-only scope.

## Boundaries

The bounded four-configuration experiment is performed. E46 denotes the
shared-pilot item in the [execution agenda](https://github.com/google/zerocopy/issues/3876);
this report supplies evidence for its assessment without making a checkbox
decision. It does not establish E29 reference-ISA correspondence; E30 complete
access production/permission spans; E34 universal inline operand/options/
continuation contracts; E35 the actual MiniRust/machine ABI-resource relation;
E36 behavioral/contextual replacement; or E37 verified final-byte, relocation,
dispatch and host-composition linkage.

Unestablished: universal correctness of these leaves; Rust/MiniRust adequacy
for raw foreign resources/provenance; compiler preservation; full caller/frame
or linker/loader correctness; generic relocation; complete memory-access
event production; absence of hidden/restored effects; reference-ISA simulation;
complete SIMD semantics; universal no-panic/no-UB or side-channel properties.
The independent mathematical vectors and emitted-byte inspection do not
supply these missing arrows. Python readers/checkers, compiler/assembler,
linker, runtime, kernel/Docker and QEMU implementations remain trusted.

Final guards/source equality are finite final-state observations. They do not
observe all reads, distinguish transient writes restored before return, or
validate permission semantics for arbitrary pointers. The selected actual
QEMU calls are emulated, and the upstream model source is not a proof that
Debian's binary/patches implement every feature correctly. No QEMU guest
feature probe, physical x86 run or QEMU rebuild was performed.

Not examined here: other compiler releases/profiles, LTO or optional zerocopy
features, Cargo/derive builds, overlapping copy, arbitrary alias patterns,
invalid caller contracts, AVX/SVE/wider SIMD or vector/aggregate C ABI passing,
unwinding, concurrency or a generic assembly atomic mapping. The helper's
single-threaded atomic counter is a call-count oracle, not a weak-memory
experiment. Runtime case/source coverage is not ISA-wide semantic coverage.

## Evidence

An [independent review](independent-review.md) rederived the finite oracles and
source counts, checked selected object/final bytes, caller routes and frame
metadata, and separately replayed the original AArch64 O0 and emulated x86-64
O3 images once each. Both passed; their9,234 reported checks are separate
from the original18,468 and add no new input-domain coverage. The review also
checks the exact public projection. [The structured verdict](independent-review.json)
records its bindings and scope.

Normative selected interfaces: Rust1.89's actual gitlinked
[Reference at9571d4d…](https://github.com/rust-lang/reference/blob/9571d4d38cc580bd9fe926f97fccd98f215564a9/src/inline-assembly.md),
selected [AAPCS64](https://github.com/ARM-software/abi-aa/blob/ec3e2fb69065768aa1caf298813a7808b50bc264/aapcs64/aapcs64.rst)
register/stack clauses, and selected
[SysV psABI](https://gitlab.com/x86-psABIs/x86-64-ABI/-/blob/e1ce098331da5dbd66e1ffc74162380bcc213236/x86-64-ABI/low-level-sys-info.tex)
integer/pointer/register/stack/SSE2 clauses. Exact paths, line ranges and input
hashes are in [primary-contract-index.json](primary-contract-index.json).
Later external ABI snapshots are selected contracts, not historical proofs
that Rust1.89 conforms. Whole global assembly, inline labels/operands,
nomem/readonly/nostack/flags and stateful directive restoration were inspected
separately from compiled behavior. Section push/pop was corrected before the
first compile; no instruction/control-flow/CFI line changed then.

Source and model: [zerocopy source pin](https://github.com/google/zerocopy/tree/8d8ed8dcc98c991d32cee3c3a84e129f29cba136),
selected source inventory/current Git-blob receipt, and
[QEMU v7.2.22 cpu.c](https://github.com/qemu/qemu/blob/30a68773a4de9960647aa82718e5b8dafea05e7a/target/i386/cpu.c#L609).
The latter defines PPRO_FEATURES including SSE/SSE2, includes that set in
qemu64, and defaults an absent version list to version1. Exact CPU source/tag
receipt copies are in compile-static/primary/. Signature verification and a
Debian binary-from-source proof were not performed.

| Preserved evidence | Role |
|---|---|
| pilot.rs, both .s files, vectors.rs, expected.json, CONTRACTS.md | Exact subject, accepted spans/ABI and fixed oracle |
| compile-static/captures/ and captures-v3/ | All8 accepted compiler commands/statuses/streams and original E0716 |
| compile-static/artifacts/, function-bindings.json, static-checks.json | Exact object/final/IR/disassembly, body bytes, selected relocations/callers/CFI/loader checks |
| runtime-captures-v1/, runtime-driver-v1/, runtime-stop-v1-diagnosis.json | Preserved pre-target reader failure, not a failed native test |
| capture_runtime_v2.py, runtime-v2.diff, RUNTIME-CAPTURE-PREPARATION-v2.json | Exact reviewed descendant, immutable hashes and pre-execution scope |
| runtime-captures-v2/, runtime-driver-v2/, runtime-results.json | Four actual raw streams/status/argv, image bindings, fresh identity/resource snapshots,24 data-only controls |
| runtime-header-v2-regression.json |28 data-only header controls, no target execution |
| evidence-inputs/provenance.json and owned copies | Exact selected compiler/linker/QEMU/platform/cfg/primary-source/zerocopy receipts |
| RESULTS-FREEZE.json | Final candidate/report/support identity inventory |

The runtime capture checked28 staged source files,69 selected std libraries,
12 prior tools,20 build artifacts, seven loader/runtime paths and the newly
pinned env/Python reader/wrapper paths before/after every call. Host Python
and Docker CLI identities also matched. Exact container ID/base/start state,
no mounts,1CPU/1GiB memory,2GiB configured memory+swap and PID256 limits were
checked freshly per call. Cgroup readings are raw snapshots, not subject-only
peak RSS or a performance bound. The complete successful helper invocation
finished exit0 with empty stderr; no unexpected subject panic/assertion,
timeout, hash/resource mismatch or target retry occurred.

The public support is a display projection: three host path prefixes are
replaced as documented in [PUBLIC-PROJECTION.md](PUBLIC-PROJECTION.md). The
original execution hashes and raw-to-display file hashes remain explicit.
Projected argv and two historical helper copies are not literal executed
bytes; no projected helper was run. Program/assembly/ELF subject bytes are
unchanged. Historical freeze manifests record the original capture, while
package-manifest.json binds the public files. Host ELF
copies are exact code/data but mode0644 and were never executed; only original
container images were called. Tool binaries/caches/whole upstream trees are not
packaged. All107 indexed companion acquisition/staging/preflight inputs are
also preserved as owned evidence with exact copy provenance.

## Revalidation

First verify package-manifest.json and public-projection.json, then the
original identities recorded in RESULTS-FREEZE.json, stream/status hashes,
exact four image hashes and function/body ranges. Historical manifest entries
for projected support retain their raw identities; use the projection table
to relate them to the public display files. Re-read the small reader sources before
using them; their passing checks do not establish formal correctness. The
retained-header regression is a cheap discriminating data check for the
18/20-byte seam. Inspect any changed decoder ABI, copy operand widths, helper
call relocation, caller frame or loader version requirement directly; do not
replace these with symbol-name or report-count matching.

To repeat execution, use a fresh owned capture namespace after reviewing the
new invocation. The preserved helpers deliberately reject overwriting prior
receipts. Keep the same source/compiler/std/linker configuration, live aligned
span/overlap policies and fixed oracle; inspect regenerated objects/final
images/callers/CFI/sysroot before valid calls. Use explicit qemu64-v1 and the
matching loader prefix, retain native-versus-emulated labels, and stop on any
unexpected status/output/identity/reader failure. Existing failed and successful
receipts must remain unchanged. A changed tool/configuration or broader domain
requires a new bounded investigation or proof, not extrapolation from these
four finite passes.

*Authored by an AI agent acting on joshlf's behalf.*
