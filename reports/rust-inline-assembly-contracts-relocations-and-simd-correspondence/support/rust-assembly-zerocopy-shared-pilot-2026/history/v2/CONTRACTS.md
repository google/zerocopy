# E46 proposed valid-source and ABI contracts

This is a preparation artifact, not a proof or execution result. The parent must
accept the exact source and proposed environment before compilation. The narrow
fixture is a single-threaded executable, not a new general-purpose safe library.
All statements about an instruction or foreign function below are proposed
external-contract premises to review, not consequences of source spelling.

The intended compiler is exactly Rust 1.89.0, commit
`29483883eed69d5fb4db01964cdf2af4d86e9cb2`, using its LLVM backend and matching
standard libraries for the two GNU/Linux targets. Both targets are little
endian with 64-bit pointers. Baseline Advanced SIMD/NEON and SSE2, respectively,
must be established before the SIMD entrypoints run. There is no AVX, SSSE3,
privileged instruction, floating-point arithmetic, inline call, stack switch,
concurrency, unwinding subject, or intentionally invalid input.

## Common memory and lifetime obligations

Every address passed to assembly is derived directly from an existing stack
array or field through `.as_ptr()`, `.as_mut_ptr()` and bounded `.add()`. No
integer is converted to a pointer. The arrays remain in scope until the call
returns; all bytes are initialized before the first call. No assembly pointer
is stored or retained. The harness has no writer concurrent with an input read
and performs no Rust access to an output while its call is active. A mutable
pointer is derived from the current exclusive output borrow; the temporary
borrow ends before the harness checks that output.

The guarded u64 output is `[before, low, high, after]` or
`[before, value, after]`; all elements are initialized u64 values. Its passed
pointer is to element1 and is aligned8. The 16-byte region is a field at offset16
in a `#[repr(C, align(16))]` 48-byte structure. It has16 initialized guard bytes
on either side. The harness checks size/alignment/offset and actual pointer
alignment before SIMD calls. Guards help detect changed writes; they do not
detect all reads or establish a complete dynamic access trace.

Copy destinations are always distinct objects, disjoint from every input.
Scalar128 addition and SIMD addition permit two shared input arguments to alias
each other; diagonal corpus entries deliberately use the same input pointer.
They never alias the destination. No overlapping memcpy/memmove case is called.
Short spans, misalignment, overlap, invalid carry and an out-of-region pointer
offset occur only as nonexecuted admission records. The separate zerocopy size
error paths are well-typed safe calls which must return Err; no short slice is
ever passed to assembly.

## Whole-function contracts and footprints

The names below refer to the unique definitions in `aarch64.s` / `x86_64.s`.
They are externally called through the exactly matching `unsafe extern "C"`
declarations. No aggregate or vector value crosses a C ABI boundary; multiword
outputs are written to explicit raw-pointer spans. Return types are u64,
pointer or unit. Instruction fetches and ABI return/stack accesses are additional
to the data footprints listed here.

| Function | Inputs / result | Data reads | Data writes |
|---|---|---|---|
| pilot_mul | a,b; out[low,high] = a*b | none | out[0..16] |
| pilot_add128 | little-limb a,b; out=sum modulo2^128; u64 carry0/1 | a[0..16], b[0..16] | out[0..16] |
| pilot_bswap | reversed eight byte positions | none | none |
| pilot_load | initialized aligned u64 pointed to by p | p[0..8] | none |
| pilot_store | store all eight bytes of value | none | p[0..8] |
| pilot_copy16 | exact16-byte copy, disjoint | src[0..16] | dst[0..16] |
| pilot_ptr | p+offset, offset0..16 | none | none |
| pilot_call_helper | helper(a,b)+1 modulo2^64 | helper counter | helper counter |
| pilot_simd_copy16 | same bytes as scalar copy | src[0..16] | dst[0..16] |
| pilot_simd_add16 | sixteen independent additions modulo256 | a[0..16], b[0..16] | dst[0..16] |

These are proposed instruction-level footprint specifications. Static code and
object inspection can check the selected load/store instructions and widths.
Finite guard checks cannot prove the specification or an ISA-wide SIMD model.
The helper also executes ordinary compiler-generated Rust code and has its own
ABI stack accesses; no full helper access trace is claimed.

Linux AAPCS64 integer/pointer arguments use x0,x1,x2 and result x0. Leaf code
modifies only x0..x6 or v0/v1 as listed in the source, plus arithmetic flags.
It does not write x18 or x19..x29. RET consumes incoming LR. The helper wrapper
saves/restores x29/x30 in a16-byte aligned frame, keeps SP aligned16 at BL,
passes x0/x1 unchanged to the Rust C helper and restores SP before RET. Its CFI
describes CFA=SP+16 after STP, then X29+16, saved FP=-16 and LR=-8, then restores
the entry state. The selected helper does not unwind. These CFI directives are
planned for actual metadata inspection, not an E40 unwind replay.

Linux x86_64 SysV arguments use RDI,RSI,RDX and result RAX. All leaves write
only RAX,RCX,RDX,R8 or XMM0/XMM1, plus arithmetic flags; RBX,RBP,R12..R15 and DF
are unchanged. MUL first saves the output pointer from RDX to RCX before writing
the implicit RAX/RDX product. At C ABI entry RSP is8 modulo16 with a live return
address. The helper wrapper subtracts8 before CALL, giving RSP0 modulo16 at the
call site, and adds8 before RET. Its CFA offset changes8→16→8 and the return
address remains at CFA-8. The helper and system runtime are outside the listed
leaf register/footprint claims. No red-zone scratch or stack data beyond this
frame is intentionally touched by the hand-written code.

The cached primary AAPCS64 source is abi-aa commit
`ec3e2fb69065768aa1caf298813a7808b50bc264`, SHA256
`7f4e6a9c02bd88184f92d5309e062539babccc1fa90c4e4676d26b58df965dbd`.
The inspected General-purpose registers / SIMD and floating-point registers /
Stack constraints sections support these selected A64 rules.

The selected primary [SysV psABI source](https://gitlab.com/x86-psABIs/x86-64-ABI/-/blob/e1ce098331da5dbd66e1ffc74162380bcc213236/x86-64-ABI/low-level-sys-info.tex)
is revision `e1ce098331da5dbd66e1ffc74162380bcc213236`, SHA256
`2d42f2ab76b99a3b8456e6bc07e18314e85991119f72db90ca1175328e27b705`.
We read the baseline feature table, Registers and the Stack Frame sections,
and Parameter Passing / Classification / Passing / Returning of Values. They
support baseline SSE2, INTEGER classification of integer/pointer arguments,
RDI/RSI/RDX argument order and RAX first INTEGER result, the listed callee saves,
DF clear on entry/return, and RSP+8 aligned16 at entry after CALL. No stack vector
arguments require stronger alignment here. MXCSR control bits and x87 control
word are preserved; the selected XMM integer instructions do not change them
or use MMX/x87 state. These last instruction effects remain external ISA
premises. The psABI snapshot is later than Rust1.89: it supplies the inspected
selected external contract, not historical Rust compiler conformance evidence.

## Inline assembly contracts

`inline_carry`: only register operands and arithmetic flags change. AArch64
CMP cin,#1 establishes incoming C for cin0/1; ADCS consumes it and CSET exports
outgoing C. x86 BT cin,0 establishes CF; ADC consumes it and SETC exports CF.
`inout` result and the other inputs are simultaneous constraints; `lateout`
carry is written after the last input read. `nomem,nostack` match this template;
`preserves_flags` and `pure` are absent.

`inline_load`: one exact initialized aligned8 read, `readonly,nostack,
preserves_flags`. `inline_store`: one exact exclusive aligned8 write,
`nostack,preserves_flags`, with no `nomem`, `readonly` or `pure`. LDR/STR and
MOV do not alter the relevant flags. Both use declared pointer/value registers
only and return to the surrounding Rust normally.

`inline_label`: no output operands, avoiding the separately unstable
asm-goto-with-outputs feature. The only branch is a direct CBZ / JZ to the
declared label block. A Rust assignment selects17 when value=0; normal
fallthrough leaves41. The block has no unsafe Rust operations. There is no
`noreturn` promise and no flags-preservation or memory-effect option. This
exercise checks Rust control-flow integration, not arbitrary jumps into Rust.

The [Rust1.89 Reference](https://github.com/rust-lang/reference/blob/9571d4d38cc580bd9fe926f97fccd98f215564a9/src/inline-assembly.md)
is revision `9571d4d38cc580bd9fe926f97fccd98f215564a9`, SHA256
`b0c3343b46e4fa198bf3ae16deb2e29dcde9dcad12c77b37a414b952ea8adb64`.
The parent-acquired immutable source gitlink receipt identifies this reference
at Rust commit `29483883eed69d5fb4db01964cdf2af4d86e9cb2`. Its selected
clauses, line locations, consumed propositions and source consumers are indexed
in [primary-contract-index.json](primary-contract-index.json).

The actual1.89 text supports direct label branches, return after the label
block, the block's new safety context, and a compile-time prohibition on
label+output operands. It specifies lateout reuse after input reads, the selected
memory/stack/flag options, register restoration, memory permissions as for FFI,
and no unwinding out of ordinary asm. It specifies default x86 Intel syntax and
global_asm scope/options restrictions. The proposed source conforms to those
selected interface rules on review; instruction semantics, the external C ABI
mapping, actual compiler implementation and source/resource adequacy remain
separate premises. Successful compilation and finite runs will not prove them.
The older preparation's later Reference2daf is now background only, not used
to supply1.89 rules.

One discrepancy was found during this review: original global-asm sources left
the section selector changed. `asm.directives.stateful` requires restoring
stateful directive effects. The parent authorized the exact preparation-only
correction: `.pushsection .text` / `.popsection`, then a separately balanced
push/pop for the GNU-stack marker. No instruction/control-flow/CFI line changed.
The original freeze and all its exact bound bytes are retained in `history/v1/`.
The `.cfi_*` directives are absent from1.89's guaranteed directive subset;
acceptance/meaning are therefore explicit LLVM20/GNU-ELF assembler premises,
to be checked in actual object/final CFI before any runtime grant. No object or
CFI output exists yet, and no missing directive is silently assumed supported.

## Actual zerocopy operations

The local repository's parent-attested clean commit is
`8d8ed8dcc98c991d32cee3c3a84e129f29cba136`, tree
`3813fe25cc2c548c419b216dcc5981932abf0f45`, crate version0.8.63. The selected
source manifest binds every regular `zerocopy/src/**` entry plus Cargo.toml,
build.rs, cargo.sh and AGENTS.md to current SHA256 and immutable Git blob ID.
No claim is based merely on a crate name.

The shared harness actually calls:

- `U64::<BigEndian>::new`, `.set`, `.get` and `.read_from_bytes`;
- `u64::read_from_bytes` to relate the big-endian byte sequence to the host's
  little-endian word and the byte-swap oracle;
- `IntoBytes::write_to` on U64 and `[u8;16]`;
- `<[u8;16]>::read_from_bytes` and `::ref_from_bytes`.

The byteorder wrapper implementation is at src/byteorder.rs:560–622 and its
U64 instantiation at773–787. `FromBytes::read_from_bytes` is at lib.rs:5441,
`IntoBytes::write_to` at6171, `as_bytes` at5995. We inspected these definitions
and relevant documentation/trait usage; this is not a recursive proof of all
zerocopy internals. Built-in trait implementations are used, with no manual
unsafe impl and no derive dependency.

The exact crate Cargo.toml states direct rustc builds are supported with no
version cfgs on sufficiently recent toolchains. All listed negative version
gates have threshold≤1.89, so none is selected at1.89. No Cargo feature, test,
doc, dev-mode, nightly or unstable cfg is supplied. `CARGO_PKG_VERSION=0.8.63`
must be set for literal documentation env expansions. No build.rs execution,
Cargo command, dependency resolution or proc-macro build is proposed. The
ordinary cargo.sh wrapper would first bootstrap a +stable tool, which would
introduce a different toolchain; it is not invoked here. A build rejection is
a stop-and-diagnose outcome, not permission to alter compiler/configuration.

## Proof and experiment boundary

No source/LLVM/ELF execution currently exists for this fixture. Later byte
identity checks bind observed artifacts; they are not decoder-correctness or
reference-ISA theorems. Expected math, Rust baselines, native/emulated observed
results, static instruction/width inspection and proposed footprint records
remain distinct. No finite pass establishes Rust/MiniRust adequacy, compiler
refinement, provenance preservation in every external-call implementation,
arbitrary SIMD accesses, generic resource linkage, relocation correctness,
unwinding or E29/E30/E34–E37. Those stronger claims remain UNPROVED.
