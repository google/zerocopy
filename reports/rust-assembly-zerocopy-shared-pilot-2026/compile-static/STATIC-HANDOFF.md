# E46 compile and static checkpoint

All eight required compilations now have accepted exit0 outputs from the same
Rust1.89 compiler: zerocopy and the corrected harness for AArch64 and x86_64,
at optimization0 and3. All accepted compiler streams are empty. No pilot image,
QEMU guest, feature probe or mutated artifact has executed. Runtime remains a
separate proposed stage requiring the parent's grant.

This is the current checkpoint. `PLAN.md`, `commands-proposed.json`,
`PREPARATION-FREEZE.json`, `oracle-preparation.json`, `controls-proposed.json`
and `compile-static/CURRENT-STATUS.md` preserve earlier preparation/checkpoint
snapshots; their statements about absent tools, uncompiled source, pending
restaging or future byte controls describe those snapshots. This file and the
new static evidence below supply the current facts without changing frozen
historical evidence. The existing authorship disclosure is in PLAN.md.

## Exact source, compiler and artifacts

The unchanged zerocopy selection is crate0.8.63 at inspected clean repository
commit `8d8ed8dcc98c991d32cee3c3a84e129f29cba136`. The parent source receipt,
selected24 regular files and direct-rustc/no-feature configuration are bound in
`zerocopy-selected-source.json` and CONTRACTS. No Cargo, proc-macro or derive
build ran. Both crate and harness use the exact same Rust1.89 commit
`29483883eed69d5fb4db01964cdf2af4d86e9cb2`, LLVM20.1.7, selected target std,
optimization0 or3, codegen-units1, panic=abort and overflow-checks=yes. The
read-only default cfg query's panic=unwind describes that query's default, not
these actual compile flags. Compiler binary SHA256 is
`93c98482c1bdedf3789c2bd0a86ff82a7075a58528abbca2990066f4e8faedb7`.

Current `pilot.rs` SHA256 is
`1b9466576e315530e54eea9622d102e59ae219177473440c2ebade46fd9e4616`.
The original temporary-U64 expression failed with E0716. The parent approved
only binding that U64 to a named local before its error value is inspected.
No ABI, assembly, dependency, corpus, oracle or compiler argument changed.
The successful AArch64 O0 rlib was retained; its accepted compilation was not
repeated. Original source, failed compiler streams and successive preparation
freezes remain in history/ and compile-static/captures/. The v3 continuation
is captured separately in compile-static/captures-v3/.

| Actual image | Final ELF SHA256 | Harness object SHA256 |
|---|---|---|
| aarch64 O0 | `adb86a7669598af8b9fa65d84bdea9b652fbc95171bff686fa3af85a24d10f20` | `0f1c90ffb65103b3b912efa9542d80b5d6017eb65c7f990d75df9ea8e5f58bb8` |
| aarch64 O3 | `b8047348558fdbc9fb7335e561dbb93f2983a9158f6604b26cfe8ae3d82f87f8` | `ba178e05a648ba2d16d43ab7a56038a42fe23df0b10ac4296dfa4541f810d49a` |
| x86_64 O0 | `ab6265e1c5333c11e971973b39b4cbc0a1ada16763c8c70515b8d881ce40ed4c` | `6ec7cae837203a116b2cf54c603e81581ab35adac61025252bfd5b07e03aa576` |
| x86_64 O3 | `64a1efa22c13b1b01e540193225fc50f7dd3911cd387a592165f7fe566c7a144` | `412216a187aa5a2e6fee73b561dc7c71042a012d1555a1829b546d23bbd6ea71` |

`image-and-function-identities.json` binds all116 selected function records,
including the two intentionally absent optimized rust_load entries.
`function-bindings.json` records exact symbol ranges, file offsets, body bytes
and hashes. Its owned ELF reader was cross-checked against GNU objdump raw
instruction bytes. The16 copied image/object/assembly/LLVM-IR evidence files
match container inventory hashes. Host image copies are mode0644 data and
were never executed; proposed execution would use original container images.
Rlibs remain in the container, bound by compiler after-inventories.

The capture helper verified all121 v3 frozen historical inputs before each
continuation command. All28 staged inputs,69 selected target-library files
and12 captured tool files matched before and after every accepted compile.
Exact argv, clean environment, cwd, status and full streams are retained.
Static input identities bind107 parent acquisition/staging/preflight files;
source/model/tool acquisition is distinguished from authored inspection output.

## Code, calls and frame evidence

All ten whole-function bodies per image were inspected, along with the four
inline wrappers, three real zerocopy adapters, Rust helper and selected named
Rust baselines. The whole functions cover multiply,128-bit carry, byte-swap,
load/store, disjoint copy16, bounded pointer return, a C helper call, SIMD
copy16 and SIMD byte add. Their source-level valid-span and clobber contracts
are in CONTRACTS; selected disassemblies and LLVM IR retain actual compiler
behavior rather than assuming function names fix a private Rust ABI.

Of40 whole-function object/image pairs,36 have exact equal bytes and no body
relocations. The four helper bounces differ only at their checked call
relocation: AArch64 R_AARCH64_CALL26 at function offset8/addend0, or x86_64
R_X86_64_PLT32 at field offset5/addend-4. Decoded final call targets equal the
actual Rust `pilot_helper` symbol. All ten whole-function object body hashes
are equal between O0 and O3 within each architecture. Rust-generated bodies
are individually hashed; their other relocations are not universally proved.

The actual LLVM declarations use the default C calling convention for the ten
external assembly entries. Selected caller windows and the bounded reader
find all ten intended calls per image. AArch64 callers place scalar/pointer
arguments in X0/X1/X2 as the selected signature requires; SysV callers use
RDI/RSI/RDX. x86 RIP/GOT calls are tied through the actual R_X86_64_RELATIVE
slot/addend to the intended function; applying the load base remains a loader
premise. One optimized pointer call uses a hoisted LEA into R13 followed by
CALL R13: nextPC0xc9d5 plus displacement-0xf7a equals pilot_ptr0xba5b,
then CALL R13 occurs at0xcb93 with RDI/source and RSI/index. The reader checks
this exact observed opcode/target route. Preservation of R13 and the selected
instruction interval was reviewed; this is not universal register/CFG analysis.

The helper bounce saves/restores AArch64 X29/X30 in a16-byte frame. Its
object and final FDEs give SP+16 with X29@CFA-16 and X30@CFA-8, switch CFA to
X29+16 after establishing FP, and restore SP-based rules at the epilogue.
SysV entry RSP is8 modulo16; subtract8 aligns the helper call, then add8
restores return state. Its actual CIE is RSP+8/RIP@CFA-8 and the helper FDE
switches CFA offset16 then8. The final FDE's referenced CIE was checked,
including its distinction from the startup CIE with undefined RIP.
CFI remains an assembler-specific subject: Rust1.89's guaranteed directive
subset does not establish these directives' meaning. Here actual object/final
CFI and Rust helper/bounce frames were inspected; no unwinder execution or
unwinder correctness theorem is claimed. panic=abort is the actual profile.

The optimized AArch64 Rust helper calls __aarch64_ldadd8_relax for its counter;
x86_64 uses lock inc. Compiler runtime dispatch, atomic counter accesses,
callee frames and library effects are additional to the handwritten bounce's
own instructions. The helper's planned exact call count is a runtime oracle,
not a proved final-state or footprint theorem.

## Compiler findings relevant to memory contracts

The O3 private `zc_decode` reference argument is promoted to an i64 value on
both targets (internal fastcc in LLVM IR). Its scalar REV/BSWAP body consumes
that value, not a raw pointer C argument. Actual call sites were inspected.
The named Rust load baseline disappears at O3 on both targets; no independently
emitted rust_load body is asserted there. At O0 inline wrappers include
compiler stack/red-zone spills around the template: nomem/nostack options
constrain the inline template, not surrounding Rust wrapper instructions.

The real O3 zerocopy copy16 adapter has scalar memory operand widths4@0,
4@3,8@7 and1@15 on each source and destination, in architecture-dependent
order. Per source or destination, operand widths sum to17, the interval union is16, and byte3
is read and written twice. The handcrafted SIMD version uses one16-byte load
and one16-byte store (plus return/control state). A bounded result comparison
can test equal final values on disjoint valid spans. It cannot establish equal
access events or justify replacing operand widths/event multiplicity with the
union interval. No general scalar or SIMD access semantics has been proved.

The owned static checks report330 passes across four images. They check
selected encodings/relocations, C declarations, helper CFI, loader identity
and version-name compatibility. They are unverified text/binary readers,
not machine-checked semantics or exhaustive call-graph analysis.
`byte-identity-controls.json` compares actual load-body slices with their bound
bytes and rejects a one-bit changed candidate for each architecture. Those
candidates exist only as JSON byte data, never as linked/loaded/executed code.
Prepared short-span/alignment/overlap/carry/hidden-read controls are admission
or oracle data, not invalid executed Rust. A negative derived from an observed
return/guard record remains pending because there is no runtime record yet.

## Platform and proposed execution boundary

Actual native feature preflight reports AArch64 `asimd`; the compiler's baseline
cfg includes neon. This supports the selected whole-function NEON templates
for native Linux AArch64 VM/container calls. The x86 templates use baseline
SSE2. For the proposed QEMU runs, installed model catalog output names
qemu64-v1. That catalog command exits1 with empty stderr after printing the
catalog; it is not a guest failure. The newly proposed runtime argv selects
explicit `-cpu qemu64-v1`, replacing only the old machine-dependent qemu64
alias in the historical proposal.

The exact [official QEMU source](https://github.com/qemu/qemu/blob/30a68773a4de9960647aa82718e5b8dafea05e7a/target/i386/cpu.c#L609)
at v7.2.22 defines PPRO_FEATURES including SSE/SSE2, includes that set in the
qemu64 model, and registers default version1 when no versions list is given.
An exact source copy, tag-object receipt and selected line ranges are in
primary/ and static-input-identities.json. No signature was independently
verified. The installed Debian QEMU7.2.22 binary has SHA256
`ca7b4d72cb2a1a36dd63e31ae989ec909d4c4a711981bc318ae64ed191e96167`.
Its Debian patches/build correspondence, actual feature exposure and emulator
correctness remain implementation trust, not consequences proved from the
upstream source. No guest feature probe has executed.

Both final targets' PT_INTERP and NEEDED/version-needs sections were read.
AArch64 selects /lib/ld-linux-aarch64.so.1 (resolved loader SHA256
`add9309ee6f1252a4d018de9db5ed39100f8128037f45e387e07e279824d05a4`).
For x86 PT_INTERP /lib64/ld-linux-x86-64.so.2, the actual QEMU-prefix candidate
/usr/x86_64-linux-gnu/lib64/ld-linux-x86-64.so.2 exists and resolves to the
matching x86 loader SHA256
`0eae8509658fdb9310562b8814c198bff579f0314b1dcd4500d1556bf4cc7d0e`.
The proposed argv uses `-L /usr/x86_64-linux-gnu`. Six actual loader/libc/libgcc
files have ELF64-LE/machine and identity evidence. Every image's required
version-name set is a subset of the inspected matching library definitions;
this is more specific than comparing a maximum glibc version. Actual runtime
resolution and loader/library implementation correctness remain untested.
No ldd, target loader or target binary was invoked for inspection.

`runtime-proposal.json` fixes four positive runs, once each serially,30-second
supervision, exact four image hashes and clean environment. All pointers are
live, initialized and sufficiently aligned; source/destination policies are
fixed before compilation. Pointer results0..16 are compared within the same
allocation, including one-past without dereference. The immutable independent
integer/byte oracle plus Rust/zerocopy baselines expects4617 checks per run.
No invalid caller, bad annotation, overlap mutation or changed image is to be
executed. stdout/stderr/status and identity checks must be captured; mismatch,
unexpected panic/assertion, timeout or changed identity stops dependent work.
The proposal is not an executed receipt or runtime authorization.

## Preserved diagnostics and remaining claims

The original E0716 failure, pre-effect Docker sandbox denial, missing-manifest
lookup and owned excerpt-reader path concatenation error are retained or
explicitly described in operational evidence. The static caller reader first
stopped on the legitimate LEA-R13/CALL-R13 route; its original source and
integration diagnosis are preserved before the narrow observed-route extension.
The new handoff writer stopped on a null absent-symbol entry, was diagnosed,
and was corrected only to preserve that absence in the summary. These are
operational limitations, not compiler ISA disagreements. No compiler ICE,
subject panic/assertion, image/source identity change or pilot/guest execution
occurred. Integration diagnoses are labeled as transcriptions where original
subprocess capture was not made.

Even successful proposed runs would establish only this finite source/corpus,
compiler configuration, actual native/emulated execution and result/guard
observations. They would not prove Rust/MiniRust adequacy, reference-ISA
agreement, compiler preservation, complete memory-access production, general
ABI/resource linkage, generic SIMD semantics or the stronger E29/E30/E34-E37
milestones. No execution/proof checkbox is closed here. Container build output
is78,400,062 bytes, with20,303,074 bytes of owned artifact copies; retained logs
and source copies also remain below the authorized256MiB additional-output cap.
