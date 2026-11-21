# x86-64 FS/GS segment-override SFI escape, 0x67/0x66 prefix decoding, %fs:0x28 stack-canary lifting, and Cartesian Pass-2 silicon fuzzing in Lean 4

## Summary

Auditing x86-64 legacy/REX prefix decoding (`0x64` `FS:`, `0x65` `GS:`, `0x67`
`addr32`, `0x66` `op16`, and Group 2 null overrides `0x26`/`0x2E`/`0x36`/`0x3E`)
against live Intel Xeon Ice Lake-SP silicon, `intelxed/xed@0bcb6237`, and
`awslabs/s2n-bignum@d4518712` uncovers a correlated soundness blind spot across
binary Software Fault Isolation (`PicMultiFnSfi`), `.o` stack-frame lifting
(`ByteX86`), and Pass-2 reference simulation (`VendorX86Ref` $\subseteq$
`ByteX86`)—and closes all four surfaces end-to-end in Lean `v4.34.1`:

1. **Non-flat `FS:`/`GS:` (`0x64`/`0x65`) breaks flat-segment SFI containment on
   every stock Linux process (`support/reproduce_prefix_sfi_escape_and_rewriter_v2.py`,
   `support/RealX64PrefixSem.lean`, `support/PicMultiFnSfiV2.lean`).** Although
   64-bit mode forces `CS`/`DS`/`ES`/`SS` segment bases (`0x2E`/`0x3E`/`0x26`/`0x36`)
   to zero, `FS` (`0x64`) and `GS` (`0x65`) add full 64-bit `IA32_FS_BASE` /
   `IA32_GS_BASE` (`%fs` is non-zero in every glibc Linux thread for TLS).
   Because unpatched `scanPrefixes` accepted `0x64` as an ignored legacy prefix,
   the 5-byte store `64 4f 89 04 2e` (`mov %r8, %fs:(%r14,%r13,1)`) passed
   unpatched `checkSfiPicMultiFn` (`rfl`) yet overwrote host virtual memory at
   `fs_base + arenaBase + guest_sp` (`0x00007f760d591740`) outside the
   `[arenaBase - 64 KiB, arenaBase + 4 GiB + 64 KiB)` `PROT_NONE` guard envelope
   with `sig = 0` (`fs_escape_overwrites_outside_arena_on_realX64`,
   `gs_escape_overwrites_outside_arena_on_realX64`). Adding `fsBase, gsBase :
   BitVec 64` and `seg : Option SegReg` to `RealX64PrefixSem` (`70,486` B,
   `6.06 s` compile, `438 ms` private kernel replay) and enforcing `addr.seg ==
   none && !addr.addr32` plus zero `0x66` stack/branch prefixes in
   `PicMultiFnSfiV2` (`90,002` B, `11.59 s` compile, `999 ms` replay) rejects all
   five escape families by `rfl` and proves `checkSfiPicMultiFnV2_sound`
   universally over **all** `(fsBase, gsBase : BitVec 64)`!
2. **`0x67` (`addr32`) effective-address truncation and `0x66` (`op16`) stack
   `REX.W` precedence + disassembler `rel16` desynchronization
   (`support/prefix_sfi_escape_and_rewriter_v2_results.json`,
   `support/RealX64PrefixSem.lean`).** On live Ice Lake-SP silicon:
   (a) `0x67` truncates effective addresses to `ZeroExtend64(rawEA[31:0])`
   *before* adding 64-bit `fsBase`/`gsBase` (`67 48 8b 07` reads `[edi]`,
   `67 f0 48 0f b1 0f` `addr32 lock cmpxchg` mutates `[edi]`, `67 48 8b 05 00 00
   00 00` truncates `(nextRip + disp32)[31:0]`, while `64 48 8d 07` `LEA`
   ignores `FS:`); (b) on `d64` `PUSH`/`POP`/`LEAVE` (`50`/`58`/`C9`), `REX.W =
   1` immediately preceding the opcode *overrides* `0x66` back to 64-bit (`66 48
   50` pushes `8` bytes, whereas `48 66 50` and `66 41 50` push `2` bytes,
   shifting `%rsp` by `-2` and breaking 16-byte ABI alignment; `66 C9` `leavew`
   sets `RSP := RBP + 2` and merges 16-bit `BP`); and (c) on near branches
   (`66 E8`, `66 E9`, `66 0F 84`), Intel silicon forces 64-bit `f64` `rel32`
   fetch lengths (`6`, `6`, `7` bytes), whereas both `llvm-mc 21.1.8` and GNU
   `objdump 2.47` decode them as AMD64 16-bit `rel16` (`4`, `4`, `5` bytes)
   followed by `addb %al, (%rax)`—creating a **2-byte instruction-boundary
   desynchronization** in any disassembler-backed validator!
3. **Upgrading the stock-GCC SFI rewriter (`support/sfi_gcc_rewriter_v2.py`) and
   lifting real `-fstack-protector-strong` / `-Z stack-protector=all` `.o` code
   (`support/StackCanaryLiftV2.lean`).** `sfi_gcc_rewriter_v2.py` supports
   `--canary-mode={arena_guarded,strip,reject}` (rewriting `%fs:40`/`%fs:0x28`
   canary reads to a loader-initialized `PROT_READ` arena page at `0xFE28(%r14)`
   where guest tampering traps with `SIGSEGV = 11, SEGV_ACCERR = 2`, and
   `call __stack_chk_fail` to deterministic portal abort `0xbadca028dead0001`),
   normalizes GCC's spontaneous `0x67` `(%edi)` memory operands into
   `movl %edi, %r11d; (%r14,%r11,1)`, and fail-closed rejects rogue `%fs:`/`%gs:`/
   `addr32`/`pushw` instructions. On the 5-function decompression workload compiled
   *with* `-fstack-protector-strong`, the `2,048`-byte `.text.sfi` image passes
   `checkSfiPicMultiFnV2 2048 stockGccCanaryImg2048 = true := rfl` and runs at
   **`3,241.50 MiB/s`** vs. **`3,477.80 MiB/s`** native (**`+7.29%` overhead**).
   For Mode-1 `.o` functional lifting, `StackCanaryLiftV2.lean` (`63,573` B,
   `4.97 s` compile, `1,579 ms` replay) refutes flat-`[0x28]` mismodeling
   (`unpatched_fs28_flat_mismodel_counterexample`) and proves universal
   `PrivateStackCanarySep` functional correctness, caller/TCB memory preservation,
   and deadness of `__stack_chk_fail` directly on exact `gcc 15.2.0 -O2
   -fstack-protector-strong` (`83` B, `gcc_hash2_canary_verified`) and `rustc
   1.102.0-nightly -C opt-level=2 -Z stack-protector=all` (`88` B,
   `rust_unexposed_canary_verified`) `.o` byte streams, paired with a two-sided
   corrupted-canary trap theorem (`gcc_hash2_canary_corrupted_traps_to_stack_chk_fail`).
4. **Diagnosing the correlated Pass-2 blind spot via a `352`-vector Cartesian
   silicon + `intelxed` sweep and proving repaired Pass-2 correspondence
   (`support/probe_cartesian_prefix_silicon_and_xed.py`,
   `support/VendorX86RefV2/*.lean`, `support/ByteX86Pass2CorrespondenceV2.lean`).**
   Why did `VendorX86Ref.Step ⊆ ByteX86.Step` pass with `0` `sorry` while missing
   `FS:`/`GS:`, `0x67`, and `0x66`? Because both models shared the same
   `scanPrefixes` `hasSegOr67` projection (`blind_pass2_vacuous_simulation` and
   `pass2_shared_scanPrefixes_blind_spot_counterexample`). Across a `352`-vector
   Cartesian grid (`24` prefix orderings $\times$ `14` GP/Imm/Mem/LEA/Stack/Branch/
   LOCK/VEX/EVEX templates + `16` 15B/16B/`%fs:0x28`/`LEAVE` boundary vectors),
   unpatched Pass-2 diverged from silicon on **`84 / 318` (`26.42%`)** valid
   vectors while `llvm-mc` and `objdump` silently false-accepted **`34 / 34`
   (`100.0%`)** `#UD`/`#GP(0)` fault vectors. Repaired `VendorX86RefV2` achieves
   **`352 / 352` (`100.0%`)** exact match with both Ice Lake-SP silicon and
   `intelxed@0bcb6237`—certified inside the Lean `v4.34.1` kernel by
   `SiliconCartesian352Cert.cartesianAll352_silicon_verified` (`0`
   `native_decide`)—and `ByteX86Pass2CorrespondenceV2.lean` (`64,492` B, `5.18 s`
   compile, `1,112 ms` replay across `2,284` constants) proves universal
   `vendorX86RefV2_step_sub_byteX86V2_step` and
   `vendorX86RefV2_stepsN_sub_byteX86V2_stepsN` over all `(fsBase, gsBase :
   BitVec 64)`.

## Applicability

These findings govern x86-64 machine-code decoders, binary SFI verifiers, ELF
`.o` functional lifters, and Pass-2 ISA reference models across the twelve
pinned subjects in [`REPORT.json`](REPORT.json):

- **Theorem prover & kernel audit boundary:** `leanprover/lean4` `v4.34.1`
  (`5045d0056413266e57c625dcd7c365b10e377c52`) compiled strictly with
  `prelude` + `Init.*` only (`-DElab.async=false -Ddebug.skipKernelTC=false -j1
  -M4096`, `< 150 KB` and `< 15.0 s` per `.lean` file, `0` `sorry`, `0` custom
  `axiom`/`opaque`, `0` `unsafe`/`partial`/`*._unsafe_rec`/`native_decide`/
  `bv_decide`) and replayed from scratch via `(trustLevel := 0) (plugins := #[])
  (loadExts := false) (level := .private)` `base.toKernelEnv.replay`, matching
  `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`).
- **ISA reference specifications & silicon target:** 64-bit Ring-3 (`CS.L = 1,
  CS.D = 0`) execution on Intel Xeon Ice Lake-SP (`GenuineIntel` Family 6 Model
  106 Stepping 6, `CR4.FSGSBASE = 1`, `Linux 7.1.6-1rodete1-amd64`) cross-checked
  against `intelxed/xed` (`0bcb6237345c5066726dcc08b3d87928df3b5b26`),
  `awslabs/s2n-bignum` (`d4518712d040485efe621caba1c723a07fbc549e`),
  `lfi-project/lfi-verifier` (`8c3c47983572039b138f8fa15c12231f2655bbef`),
  Intel SDM (`325462-087US`, 2025), and System V AMD64 psABI (`1.0`).
- **Compilers, disassemblers, and repaired corpus baselines:** Debian `gcc
  15.2.0-14` (`-O2 -fstack-protector-strong`), `rustc 1.102.0-nightly`
  (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, LLVM `23.1.5`, `-C opt-level=2
  -Z stack-protector=all`), `llvm-mc 21.1.8`, and GNU `binutils 2.47` (`as`,
  `objdump`, `readelf`). This package repairs and supersedes the flat-segment /
  unmodeled-`0x67` / unmodeled-`0x66` decoder assumptions in corpus packages
  `binary-sfi-call-ret-reentrant-callbacks-unwind-rop-and-stock-gcc-rewriter`,
  `byte-decoded-x86-64-sharded-lifting-dead-flag-collapse-and-binary-sfi-containment`,
  and `s2n-bignum-xed-pass2-x86-64-transpiler-and-lean-miri-simd-triangulation`.
- **Vendor-specific boundary (`Intel 64` vs. `AMD64` on `66 E8`/`66 E9`/`66 0F 8x`):**
  Exact `f64` (`rel32`) fetch lengths on `0x66`-prefixed near branches apply to
  Intel 64 processors (`intelxed` default chip model and Ice Lake-SP silicon);
  AMD64 processors honor `0x66` (`rel16` + `EIP[15:0]` truncation) on near
  branches. `checkSfiPicMultiFnV2` rejects `0x66` on all near branches (`has66 =
  false`), remaining sound across **both** Intel 64 and AMD64 silicon!

## Findings

### Finding 1: Non-flat `FS:`/`GS:` (`0x64`/`0x65`) breaks flat-segment binary SFI on Linux, while Group 2 null overrides (`0x26`/`0x2E`/`0x36`/`0x3E`) preserve prior `FS:`/`GS:` and reset `REX`

`Basis:` `normative` (Intel SDM Vol. 2A §2.1.1 & Vol. 3A §3.4.4 segment bases in IA-32e 64-bit mode; System V AMD64 psABI §3.7.2 `%fs:0x28` TLS stack guard), `source` (`intelxed/xed@0bcb6237` `src/dec/xed-ild.c:192-251`), `execution` ([`support/reproduce_prefix_sfi_escape_and_rewriter_v2.py`](support/reproduce_prefix_sfi_escape_and_rewriter_v2.py) $\to$ [`support/prefix_sfi_escape_and_rewriter_v2_results.json`](support/prefix_sfi_escape_and_rewriter_v2_results.json)), and `derived` ([`support/RealX64PrefixSem.lean`](support/RealX64PrefixSem.lean), [`support/PicMultiFnSfiV2.lean`](support/PicMultiFnSfiV2.lean)).

In 64-bit mode (`CS.L = 1`), hardware treats segment overrides asymmetrically
even within Legacy Prefix Group 2:

1. **Live Ring-3 SFI sandbox escape via `64 4f 89 04 2e` (`mov %r8, %fs:(%r14,%r13,1)`):**
   Every Linux `x86_64` process linked with `glibc` initializes `IA32_FS_BASE`
   (`ARCH_SET_FS`) to its Thread Control Block (`orig_fs_base =
   0x00007f660d57f740` in our live probe), and on Linux kernels with
   `CR4.FSGSBASE = 1` (`fsgsbase_ring3_enabled = true` on `Linux 7.1.6` + Ice
   Lake-SP), unprivileged Ring-3 code can also set arbitrary 64-bit `FS`/`GS`
   bases via `wrfsbase`/`wrgsbase`. In unpatched `PicMultiFnSfi.lean` and
   `ByteX86Base.lean`, `scanPrefixes` accepted `0x64` (`FS:`) and `0x65` (`GS:`)
   as no-op prefixes while `evalLinearAddr` omitted `fsBase`/`gsBase`.
   Consequently:
   - The 32-byte untrusted bundle starting with `64 4f 89 04 2e e9 b6 ff ff ff`
     (`mov %r8, %fs:(%r14,%r13,1); jmp __sfi_portal_exit`) satisfies the
     unpatched SFI checker (`unpatched_decoder_blinds_sfi_to_fs_prefix` in
     [`support/RealX64PrefixSem.lean`](support/RealX64PrefixSem.lean)).
   - Executing that bundle inside a live `4 GiB + 2 * 64 KiB PROT_NONE` arena
     (`arenaBase = 0x0000001000010000`, `guest_sp = 0x12000`) leaves the intended
     arena slot `[arenaBase + 0x12000]` untouched (`0xaaaaaaaaaaaaaaaa`) and
     instead writes `0xdeadbeefcafe0001` cleanly (`fs_sig = 0`!) into a host page
     at `orig_fs_base + arenaBase + 0x12000 = 0x00007f760d591740`, strictly
     outside `[0x1000000000, 0x1100020000)` (`fs_outside_arena_envelope = true`)!
     Identically, `65 4f 89 04 2e` (`GS:`) overwrites `gs_base + arenaBase +
     0x12000 = 0x0000003000012000` with `0xdeadbeefcafe0002` (`gs_sig = 0`).
   - Theorems `fs_escape_overwrites_outside_arena_on_realX64` and
     `gs_escape_overwrites_outside_arena_on_realX64` mechanize both escapes in
     Lean `v4.34.1`.
2. **Exact Group 2 interaction with null `CS`/`DS`/`ES`/`SS` prefixes and `LEA`:**
   What happens when `0x2E` (`CS:` / branch-not-taken hint), `0x3E` (`DS:` /
   branch-taken hint), `0x26` (`ES:`), or `0x36` (`SS:`) appears *after* `0x64`
   (`FS:`), e.g. `64 2e 48 8b 07`? Naive "last Group-2 byte wins" logic would
   reset `segOverride` back to `none` (flat `0`). Live Ice Lake-SP silicon
   (`prefix_group2_and_lea` in
   [`support/prefix_sfi_escape_and_rewriter_v2_results.json`](support/prefix_sfi_escape_and_rewriter_v2_results.json))
   and `intelxed/xed@0bcb6237` (`src/dec/xed-ild.c:218-246`, which ignores
   `0x26`/`0x2E`/`0x36`/`0x3E` in 64-bit mode when updating `SEG_OVD`) confirm:
   - `64 2e 48 8b 07`, `64 3e 48 8b 07`, `64 26 48 8b 07`, and `64 36 48 8b 07`
     **all read `fs:[rdi]`** (`0xf5f500000000f5f5`)—null segment prefixes do
     **not** clear an earlier `0x64`/`0x65` override, though they **do** clear an
     immediately preceding `REX` (`0x40..0x4F`) byte and count toward the 15-byte
     `#GP(0)` cap!
   - Between `0x64` and `0x65`, **last active segment wins** (`64 65 48 8b 07`
     reads `gs:[rdi]`; `65 64 48 8b 07` reads `fs:[rdi]`).
   - `LEA` (`64 48 8d 07`) computes the offset `evalEffectiveAddr` before segment
     addition, completely ignoring `FS:`/`GS:` (`null_cs_2e_preserves_fs_while_lea_ignores_fs`).

### Finding 2: `0x67` (`addr32`) truncates effective addresses before segment addition, while `0x66` (`op16`) obeys `REX.W` override even on `d64` `PUSH`/`POP`/`LEAVE` and triggers an Intel-vs-disassembler `rel16` desynchronization

`Basis:` `normative` (Intel SDM Vol. 1 §3.6.1, Vol. 2A §2.1.1 & Table B-40 `f64`/`d64`), `execution` ([`support/prefix_sfi_escape_and_rewriter_v2_results.json`](support/prefix_sfi_escape_and_rewriter_v2_results.json), [`support/cartesian_prefix_silicon_and_xed_results.json`](support/cartesian_prefix_silicon_and_xed_results.json)), and `derived` ([`support/RealX64PrefixSem.lean`](support/RealX64PrefixSem.lean)).

Probing `0x67` and `0x66` across scalar, atomic, stack, and control-flow
instructions on Ice Lake-SP silicon establishes three exact invariants required
for sound decoding:

| Byte Sequence | Disassembly / Intent | Live Ice Lake-SP Silicon Outcome | Unpatched Decoder / Disassembler Hazard |
| :--- | :--- | :--- | :--- |
| `67 48 8b 07` | `mov (%edi), %rax` (`rdi = 0x140001000`) | Loads `[0x040001000]` (`0xaaaabbbbccccdddd`) | Unpatched `ByteX86`/`VendorX86Ref` read `[0x140001000]` |
| `67 f0 48 0f b1 0f` | `addr32 lock cmpxchg %rcx, (%edi)` | Atomically mutates `[0x040001000]`; `[0x140001000]` untouched | Unpatched model mutated 64-bit `[rdi]` |
| `64 67 48 8b 07` | `mov %fs:(%edi), %rax` | Loads `fs_base + ZeroExtend64(edi)` (`0x7777666655554444`) | Truncation occurs *before* 64-bit `fsBase` addition |
| `67 48 8b 05 00 00 00 00` | `mov 0(%eip), %rax` at `0x240000800` | Loads `ZeroExtend64((rip + 8)[31:0]) = [0x40000808]` | `0x67` truncates RIP-relative `(nextRip + disp32)` to 32 bits |
| `66 50` / `48 66 50` / `66 41 50` | `pushw %ax` / `rex.W` nullified / `pushw %r8w` | `len = 2, 3, 3`; **`rsp_delta = -2`**, writes 2 bytes | Breaks `rsp % 16` alignment & shifts caller stack offsets by `6` B |
| `66 48 50` / `66 49 50` | `data16 rex.W pushq %rax` / `%r8` | `len = 3, 3`; **`rsp_delta = -8`**, writes 8 bytes | **`REX.W = 1` overrides `0x66` even on `d64` `PUSH`/`POP`/`LEAVE`!** |
| `66 c9` vs. `66 48 c9` | `leavew` vs. `data16 rex.W leaveq` | `66 c9`: `rsp := rbp + 2`, `bp := Mem16[rbp]`; `66 48 c9`: 64-bit `leaveq` | `StackAddrSize` stays 64-bit (`RSP := RBP`) while pop width is 16-bit |
| `66 e8 01 00 00 00` / `66 e9 ...` / `66 0f 84 ...` | `0x66` + `CALL` / `JMP` / `Jcc` near `rel32` | Guard-page fetch lengths **`6`, `6`, `7` bytes** (`f64` on Intel) | **`llvm-mc 21.1.8` & `objdump 2.47` decode as `4`, `4`, `5` B (`rel16`) + `addb %al, (%rax)`!** |

The third hazard (`66 E8` / `66 E9` / `66 0F 84`) is particularly insidious for
binary SFI: if an attacker places `66 e9 <2-byte-offset> <smuggled-2-byte-gadget>`
inside a 32-byte bundle, any validator relying on LLVM MC or GNU `libopcodes`
sees a 4-byte `jmpw` followed by a benign 2-byte instruction, whereas Intel 64
silicon consumes all 6 bytes as a single `jmp rel32` (or vice versa on AMD64)!
`PicMultiFnSfiV2` eliminates both the stack misalignment and the cross-vendor
length desynchronization by rejecting `push*`/`pop*`/`leave*` and requiring
`!has66` on every `jmpRel`, `jccRel`, and `jmpReg` (`checkSfiPicMultiFnV2_rejects_op16_push`,
`checkSfiPicMultiFnV2_rejects_op16_jmp`).

### Finding 3: Prefix-hardened PIC SFI (`PicMultiFnSfiV2` + `sfi_gcc_rewriter_v2.py`) and sound `%fs:0x28` stack-canary lifting (`StackCanaryLiftV2`) for stock GCC and Rustc `.o` code

`Basis:` `normative` (System V AMD64 psABI §3.7.2 `tcbhead_t.stack_guard` at `%fs:0x28`), `source` ([`support/sfi_gcc_rewriter_v2.py`](support/sfi_gcc_rewriter_v2.py)), `execution` ([`support/prefix_sfi_escape_and_rewriter_v2_results.json`](support/prefix_sfi_escape_and_rewriter_v2_results.json)), and `derived` ([`support/PicMultiFnSfiV2.lean`](support/PicMultiFnSfiV2.lean), [`support/StackCanaryLiftV2.lean`](support/StackCanaryLiftV2.lean)).

Supporting real production C and Rust compiler flags (`-fstack-protector-strong`,
`-Z stack-protector=all`) requires handling `%fs:0x28` differently in Mode-2
untrusted SFI sandboxing versus Mode-1 trusted-ABI `.o` functional lifting:

1. **Mode 2 (`PicMultiFnSfiV2` + `sfi_gcc_rewriter_v2.py`): Zero `%fs` access inside untrusted SFI bundles with `PROT_READ` arena-guarded stack canaries.**
   Untrusted SFI code must **never** read host TLS (`%fs:0x28` leaks the host
   process's ASLR/stack-guard secret and co-locates `tcbhead_t.pointer_guard` at
   `%fs:0x30`). [`support/sfi_gcc_rewriter_v2.py`](support/sfi_gcc_rewriter_v2.py)
   (`502` lines, `19,629` B) provides `--canary-mode={arena_guarded,strip,reject}`:
   - Under `arena_guarded` (default), `%fs:40` / `%fs:0x28` prologue loads and
     epilogue comparisons (`movq %fs:40, %rax`, `subq %fs:40, %rdx`, `xorq
     %fs:40, %rax`) rewrite to `movl $0xFE28, %r11d; <op> (%r14,%r11,1), %reg`,
     where `[arenaBase + 0xF000, arenaBase + 0x10000)` is a dedicated `4 KiB`
     `PROT_READ`-only arena page populated by the host loader with a fresh
     per-sandbox CSPRNG canary, and `call __stack_chk_fail` rewrites to
     `movabsq $0xbadca028dead0001, %rax; jmp __sfi_portal_exit`.
   - `sfi_gcc_rewriter_v2.py` also normalizes GCC's spontaneous `0x67` 32-bit
     base-register addressing (`(%edi)` emitted when indexing `uint32_t` offsets)
     into `movl %edi, %r11d; (%r14,%r11,1)`, normalizes `%rsp` inside multi-part
     SIB expressions (`(%rsp,%rax,8)` $\to$ `(%r13,%rax,8)`), and fail-closed
     rejects any non-canary `%fs:` (`%fs:48`), `%gs:`, `addr32`, multi-register
     32-bit SIB `(%edi,%eax,8)`, or 16-bit stack mnemonic (`pushw`).
   - Live execution on the 5-function `64 KiB` RLE+LZ4 decompression workload
     compiled with `gcc 15.2.0 -O2 -fstack-protector-strong` confirms:
     (i) clean execution matches native output at **`3,241.50 MiB/s`** vs.
     **`3,477.80 MiB/s`** native (**`+7.29%` overhead**, `1,792` active bytes in
     a `2,048`-byte `.text.sfi`, `0` untrusted relocations); (ii) guest attempts
     to forge `0xFE28(%r14)` trap immediately (`SIGSEGV = 11`, `SEGV_ACCERR = 2`);
     (iii) guest stack-frame buffer overflow returns deterministic sentinel
     `0xbadca028dead0001` via Portal `0` with host canary intact; and (iv)
     `StockGccCanaryWorkloadCertV2` proves `checkSfiPicMultiFnV2 2048
     stockGccCanaryImg2048 = true := rfl` and instantiates
     `checkSfiPicMultiFnV2_sound` over **all** `(fsBase, gsBase : BitVec 64)`!
2. **Mode 1 (`StackCanaryLiftV2.lean`): Sound `PrivateStackCanarySep` lifting of raw `-fstack-protector-strong` and `-Z stack-protector=all` `.o` functions.**
   When lifting trusted-ABI `.o` functions without SFI rewriting, flat-segment
   decoders silently mismodel `64 48 8b 04 25 28 00 00 00` (`mov %fs:0x28, %rax`)
   as reading flat address `0x28` (`unpatched_fs28_flat_mismodel_counterexample`).
   In [`support/StackCanaryLiftV2.lean`](support/StackCanaryLiftV2.lean),
   `PrivateStackCanarySep rsp0 fsBase frameBytes` asserts `64 ≤ rsp0.toNat` and
   byte-range disjointness between `[rsp0 - frameBytes, rsp0)` and the 8-byte
   TCB slot `[fsBase + 0x28, fsBase + 0x30)`. Because all private frame stores
   preserve `readMem64 sf.mem (fsBase + 0x28#64) = readMem64 s0.mem (fsBase +
   0x28#64)`, the epilogue `sub`/`cmp`/`xor` against `%fs:0x28` identically
   sets `ZF = true`, `jne __stack_chk_fail` (`75 05`) is proved dead across all
   inputs and all demonic `UndefFlags`, and the trailing `e8 00 00 00 00`
   (`call __stack_chk_fail`) is never reached:
   - `gcc_hash2_canary_verified`: verifies the exact `83`-byte `gcc 15.2.0 -O2
     -fstack-protector-strong` `.o` function (`sub %fs:0x28, %rdx; jne +5; add
     $0x28, %rsp; ret; call __stack_chk_fail`).
   - `rust_unexposed_canary_verified`: verifies the exact `88`-byte `rustc
     1.102.0-nightly -C opt-level=2 -Z stack-protector=all` `.o` function
     (`mov %fs:0x28, %rcx; cmp 0x10(%rsp), %rcx; jne +5; add $0x18, %rsp; ret`).
   - `xor_fs28_canary_verified` & `gcc_hash2_canary_corrupted_traps_to_stack_chk_fail`:
     verify the `xor %fs:0x28, %rdx` idiom and prove two-sided sensitivity
     (corrupting the saved canary slot forces control to `rip_entry + 78`, the
     exact offset of `call __stack_chk_fail`).

### Finding 4: Diagnosing the correlated Pass-2 `scanPrefixes` blind spot via a `352`-vector Cartesian silicon + `intelxed` sweep and proving repaired Pass-2 correspondence (`VendorX86RefV2 ⊆ ByteX86V2`)

`Basis:` `source` (`awslabs/s2n-bignum@d4518712` `x86/proofs/decode.ml`, `intelxed/xed@0bcb6237`), `execution` ([`support/probe_cartesian_prefix_silicon_and_xed.py`](support/probe_cartesian_prefix_silicon_and_xed.py) $\to$ [`support/cartesian_prefix_silicon_and_xed_results.json`](support/cartesian_prefix_silicon_and_xed_results.json)), and `derived` ([`support/VendorX86RefV2/Decode.lean`](support/VendorX86RefV2/Decode.lean), [`support/ByteX86Pass2CorrespondenceV2.lean`](support/ByteX86Pass2CorrespondenceV2.lean), [`support/verify_all_v2_lean_and_replay.py`](support/verify_all_v2_lean_and_replay.py)).

1. **Root cause of the correlated Pass-2 blind spot (`blind_pass2_vacuous_simulation`):**
   In the prior Pass-2 package, `VendorX86Ref.Decode.scanPrefixes` collapsed all
   seven Group-2/Group-4 bytes `{0x2E, 0x36, 0x3E, 0x26, 0x64, 0x65, 0x67}` into
   a single unused flag `hasSegOr67 : Bool`, omitted `fsBase`/`gsBase` from
   `MachineState`, and ignored `has66` on `d32` `01/89/8B/8D/B8/0F B1` and `d64`
   `50/58`. Because `ByteX86Pass2Correspondence` shared `VendorX86Ref.decodeRef`
   and the flat-segment `MachineState` projection, `VendorX86Ref.Step ⊆
   ByteX86.Step` held with `0` `sorry` while both models diverged identically
   from hardware (`pass2_shared_scanPrefixes_blind_spot_counterexample`).
2. **`352`-vector Cartesian `(Prefix-Ordering × Opcode-Class)` differential sweep:**
   [`support/probe_cartesian_prefix_silicon_and_xed.py`](support/probe_cartesian_prefix_silicon_and_xed.py)
   cross-checks **`24` prefix sequences** (`none`, `66`, `67`, `64`, `65`, `2e`,
   `3e`, `26`, `36`, `f0`, `f2`, `f3`, `48`, `41`, `66 48`, `48 66`, `67 48`,
   `48 67`, `64 2e`, `64 3e`, `64 65`, `65 64`, `64 67 48`, `41 40`) $\times$
   **`14` opcode templates** (`ADD r/m,r`, `MOV r,imm`, `XCHG rAX,r`, `MOV load`,
   `MOV store`, `LEA`, `PUSH`, `POP`, `JMP rel32`, `Jcc rel32`, `ADD [mem],r`,
   `CMPXCHG [mem],r`, VEX `VMOVDQA`, EVEX `VPROLVD` = `336` pairs) plus **`16`
   boundary vectors** (`RET`, `66 RET`, `66 EB`, `66 74`, `LEAVE` $\times 4$,
   SIB `%fs:0x28` load/sub/xor, `67` RIP-rel load, and `15`B/`16`B `#GP(0)` caps):

| Oracle / Model Evaluated on All `352` Vectors | `OK_EXEC` (`318`) | `FAULT_UD` (`32`) | `FAULT_GP0` (`2`) | Divergences vs. Live Ice Lake-SP Silicon |
| :--- | ---: | ---: | ---: | :--- |
| **Live Intel Xeon Ice Lake-SP silicon** (`SA_SIGINFO` guard-page + `wrfsbase`/`wrgsbase`) | `318` | `32` | `2` | Ground truth (`0`) |
| **Pinned `intelxed/xed@0bcb6237`** (`xed -64 -v 4`) | `318` | `32` | `2` | **`0 / 352` (`100.0%` exact verdict & length match)** |
| **`llvm-mc 21.1.8` & GNU `objdump 2.47`** | False-accept `34` faults | Miss `32 / 32` | Miss `2 / 2` | **`34 / 34` (`100.0%`) fault vectors silently accepted** + `66 E9`/`66 0F 84` `rel16` desync |
| **Unpatched `VendorX86Ref` / `ByteX86`** (`hasSegOr67` ignored) | `234` match, **`84` wrong** | `32` | `2` | **`84 / 318` (`26.42%`) valid vectors diverge** (`31` `FS:`, `12` `GS:`, `21` `0x67`, `20` `0x66`) |
| **Repaired `VendorX86RefV2` (`SiliconCartesian352Cert`)** | **`318` exact** | **`32` exact** | **`2` exact** | **`0 / 352` (`100.0%` kernel-certified match across all GPRs, `RFLAGS`, `YMM0`, & 7 memory regions)** |

   Notably, silicon + `intelxed` confirm that `48 67 c5 f9 6f 07` (`REX.W`
   followed by `0x67` before VEX2 `VMOVDQA`) and `48 67 62 f2 7d 28 15 07`
   (before EVEX `VPROLVD`) **succeed** (`OK_EXEC`, reading `[edi]`) because the
   trailing `0x67` nullifies `REX` (`pfx.rex = none`), whereas reversing the two
   bytes to `67 48 c5 ...` or `67 48 62 ...` leaves `REX` immediately adjacent
   to `0xC5`/`0x62` and traps with **`#UD`** (`FAULT_UD`)!
3. **Universal Repaired Pass-2 Simulation (`ByteX86Pass2CorrespondenceV2.lean`):**
   Across all `77` instruction forms (including VEX/EVEX memory `FS:`/`GS:` and
   `0x67` `addr32`, `.s16`/`.s32`/`.s64` GP/atomic RMW, `d64` `PUSH`/`POP`/`LEAVE`,
   and TCB `%fs:0x28` `tcb_fs_0x28_canary_load_and_xor`),
   `vendorX86RefV2_step_sub_byteX86V2_step` and
   `vendorX86RefV2_stepsN_sub_byteX86V2_stepsN` prove `VendorX86RefV2.Step ⊆
   ByteX86V2.Step` universally over all `(fsBase, gsBase : BitVec 64)` (`5.18 s`
   compile, `1,112 ms` fresh private kernel replay, axioms `["Quot.sound",
   "propext"]`).

## Boundaries

- **Known not to apply:**
  - **Flat-segment (`fsBase = gsBase = 0`) machine models for Ring-3 Linux SFI or `.o` lifting:** Refuted on live silicon and in Lean (`fs_escape_overwrites_outside_arena_on_realX64`, `unpatched_fs28_flat_mismodel_counterexample`).
  - **Assuming shared-decoder Pass-2 simulation (`Ref.Step ⊆ Impl.Step`) validates prefix decoding without a silicon/XED Cartesian oracle:** Refuted by `blind_pass2_vacuous_simulation` (`84 / 318` valid Cartesian vectors diverged identically in both unpatched models).
  - **Assuming `REX.W` is ignored on `d64` stack instructions when `0x66` is also present, or assuming `2E`/`3E` clears `64`/`65`:** Refuted on Ice Lake-SP (`66 48 50` pushes `8` bytes; `64 2e 48 8b 07` still reads `fs:[rdi]`).
- **Unsupported (rejected fail-closed):**
  - **Direct `%fs:` / `%gs:` / `0x67` / `0x66`-stack / `0x66`-branch instructions inside untrusted SFI bundles:** Rejected statically by `checkSfiPicMultiFnV2` (`false`) and `sfi_gcc_rewriter_v2.py` (except `--canary-mode=arena_guarded`, which rewrites `%fs:0x28` into an unprefixed `0xFE28(%r14)` read).
  - **Unprivileged Ring-3 `wrfsbase`/`wrgsbase` (`0F AE /2`, `0F AE /3`) inside SFI bundles:** Unmapped in `PicMultiFnSfiV2` (`false`), and even if host code mutates `fsBase`/`gsBase` before entering SFI, `checkSfiPicMultiFnV2_sound` holds universally for arbitrary `fsBase, gsBase : BitVec 64` because untrusted bundles execute zero `FS:`/`GS:` instructions.
- **Not examined:**
  - **AMD64 hardware execution of `66 E8` / `66 E9` / `66 0F 8x` (`rel16` truncation):** Live silicon measurements ran on Intel Xeon Ice Lake-SP (`GenuineIntel`, where near branches are `f64`); AMD64 behavior is documented from normative manuals and disassembler behavior, and rejected fail-closed in `PicMultiFnSfiV2`.
  - **512-bit `ZMM`, EVEX opmask registers `k1..k7`, and x87/MMX state:** `VendorX86RefV2` models `16 × 256`-bit `YMM` registers and unmasked `VL128`/`VL256` EVEX instructions (`aaa = 0, z = 0`).

## Evidence

All claims are backed by `16` self-contained support files in `support/` (every
`.lean` file `< 150 KB`, compiling in `0.57 s`–`11.59 s` `< 15.0 s` with `0`
`sorry`, `0` `*._unsafe_rec`, and `Init.*`-only external imports):

| File | Bytes | Lines | SHA-256 | Role & Verified Deliverables |
| :--- | ---: | ---: | :--- | :--- |
| [`support/RealX64PrefixSem.lean`](support/RealX64PrefixSem.lean) | `70,486` | `1,582` | `5dae12ecae6d7c8255a2189d2aea3e104e77beef012dc4429fd3cca07a988bde` | Standalone `prelude` + `Init.*` x86-64 prefix machine (`6.06 s` compile, `438 ms` replay, `1,214` constants): `fsBase`/`gsBase`, `addr32`, `op16`, `decodeX64V2_prefix_invariant`, and 6 prefix-bug refutation theorems. |
| [`support/PicMultiFnSfiV2.lean`](support/PicMultiFnSfiV2.lean) | `90,002` | `1,608` | `26a43e686276ce8e8810acffd42287f2b72692810c95bdbeb77025f548883b1b` | Prefix-hardened PIC multi-function SFI verifier & soundness (`11.59 s` compile, `999 ms` replay, `1,457` constants): 5 `rfl` rejection certs + universal `checkSfiPicMultiFnV2_sound` over all `(fsBase, gsBase)`. |
| [`support/StackCanaryLiftV2.lean`](support/StackCanaryLiftV2.lean) | `63,573` | `888` | `6da56fe19fac6502c96c8f44dbd50feaac2a28525111308234d09b1bcc434392` | `PrivateStackCanarySep` `.o` lifter (`4.97 s` compile, `1,579 ms` replay, `1,250` constants): `gcc_hash2_canary_verified` (`83` B), `rust_unexposed_canary_verified` (`88` B), `xor_fs28_canary_verified`, and corrupted-canary trap theorem. |
| [`support/VendorX86RefV2/Types.lean`](support/VendorX86RefV2/Types.lean) | `16,318` | `403` | `c6cf1c44ed3bdf314930b455480c8d2031794af53a16c25e0a027a88cb1c7736` | Repaired Pass-2 types (`4.68 s` compile): `SegReg`, `OpSize (.s16/.s32/.s64)`, `MemAddr` (`seg`, `addr32`), `MachineState` (`fsBase`, `gsBase`), and `77`-form `Instr` AST. |
| [`support/VendorX86RefV2/Decode.lean`](support/VendorX86RefV2/Decode.lean) | `38,608` | `756` | `6bdd02a6df69f392472ccadda6c525f9c665bf2388176a825f1cdaaf6b67f2bc` | Prefix-accurate 16-byte window decoder (`2.02 s` compile): Group-2 `FS`/`GS` vs. null `26/2E/36/3E`, `0x67`, `opSizeOf`/`opSizeD64`, VEX/EVEX prefix `#UD`, `finishLen_le_15`. |
| [`support/VendorX86RefV2/SemanticsScalar.lean`](support/VendorX86RefV2/SemanticsScalar.lean) | `25,861` | `623` | `e28a6cefd2784ecbbeda5c2e613b2dae9c0f69588ebeeccf2961bbc642429038` | Repaired `.s16`/`.s32`/`.s64` scalar, `evalEffectiveAddr` vs. `evalLinearAddr`, `PUSH`/`POP`/`LEAVE`, and `CMPXCHG`/`LOCK` semantics (`1.52 s` compile). |
| [`support/VendorX86RefV2/SemanticsSimd.lean`](support/VendorX86RefV2/SemanticsSimd.lean) | `25,849` | `424` | `6bc4ca1782de5800d45774bb35c59ee06cb70839b8d698716796f468f5d055b8` | Repaired VEX/EVEX 128/256-bit SIMD + AES-NI + `VPCLMULQDQ` honoring `FS`/`GS` and `0x67` `evalLinearAddr` (`1.73 s` compile). |
| [`support/VendorX86RefV2/Machine.lean`](support/VendorX86RefV2/Machine.lean) | `3,241` | `76` | `5f93cb02fac0c419989adfa1b2df2d6498852282493ba55761de2ca8ccfcdc30` | Top-level relational `Step` / `StepsN` / `stepWithOracle` (`0.57 s` compile). |
| [`support/ByteX86Pass2CorrespondenceV2.lean`](support/ByteX86Pass2CorrespondenceV2.lean) | `64,492` | `1,347` | `f0ab5873c7f97df461020f9d6e62956b1084135394aaf935410c7338f29f8cc9` | Universal `vendorX86RefV2_step_sub_byteX86V2_step`, `blind_pass2_vacuous_simulation`, `pass2_shared_scanPrefixes_blind_spot_counterexample`, and `tcb_fs_0x28_canary_load_and_xor` (`5.18 s` compile, `1,112 ms` replay). |
| [`support/sfi_gcc_rewriter_v2.py`](support/sfi_gcc_rewriter_v2.py) | `19,629` | `502` | `85b6078255e2beedf16d33ec1fdc4b1c095c5f4fc15d13cba3b9cf7b6609a4d5` | Upgraded AT&T assembly SFI rewriter supporting `--canary-mode={arena_guarded,strip,reject}`, `0x67` `(%edi)` normalization, and fail-closed rogue-prefix rejection. |
| [`support/reproduce_prefix_sfi_escape_and_rewriter_v2.py`](support/reproduce_prefix_sfi_escape_and_rewriter_v2.py) | `40,336` | `984` | `b4aad16645eef2a5c00d1ef063b5cd2805b789414ece16bd5b33537c1cad55a4` | Live silicon reproducer for `%fs:`/`%gs:` SFI escape, `0x67` truncation, `0x66` stack/branch probes, `llvm-mc`/`objdump` desync, GCC/Rustc `.o` canary specimens, and `2,048` B SFI V2 benchmark. |
| [`support/prefix_sfi_escape_and_rewriter_v2_results.json`](support/prefix_sfi_escape_and_rewriter_v2_results.json) | `11,038` | `232` | `a3023735e849c90856dfb790c2ec9df2822c637df23d1005317a0cf96321a9e8` | Captured silicon escape/prefix measurements, `83` B GCC & `88` B Rustc canary `.text` hex, and `2,048` B rewritten `.text.sfi` (`+7.29%` overhead, `SHA-256: 505b6e81...`). |
| [`support/probe_cartesian_prefix_silicon_and_xed.py`](support/probe_cartesian_prefix_silicon_and_xed.py) | `26,164` | `650` | `511d755ff426dd481b8f5e80906d9410858f79c6f9239de1eb8749c73dc7d725` | `352`-vector (`24 × 14 + 16`) Cartesian silicon `SA_SIGINFO` guard-page + `wrfsbase`/`wrgsbase` harness cross-checked against `intelxed`, `llvm-mc`, `objdump`, and unpatched Pass-2. |
| [`support/cartesian_prefix_silicon_and_xed_results.json`](support/cartesian_prefix_silicon_and_xed_results.json) | `403,772` | `11,652` | `86cf66d8ab10da42603abbaceb20de08d3f00c5f4202f3226b1d3a68d563a57a` | Full `352`-vector ground-truth dataset (`352 / 352` silicon == `intelxed`, `34 / 34` disassembler false-accepts, `84 / 318` unpatched Pass-2 divergences). |
| [`support/verify_all_v2_lean_and_replay.py`](support/verify_all_v2_lean_and_replay.py) | `33,859` | `719` | `0c794b1ab6a37b5b9f9cf7468fa00753b4a4d2f80e5f76aefc0ad50461681bb7` | Compiles all 9 staged `.lean` files + `2,048` B SFI V2 cert + `352`-vector silicon kernel cert in `tempfile.TemporaryDirectory()`, enforcing `< 150 KB`, `< 15 s`, `0` `*._unsafe_rec`, and fresh private `base.toKernelEnv.replay` across `30` theorems. |
| [`support/lean_v2_verification_and_replay_results.json`](support/lean_v2_verification_and_replay_results.json) | `12,821` | `477` | `4dce10270044b4a2370260292ea3286cd473ab5ced022640491fce8ef64b717d` | Captured compile metrics, constant-purity audit, fresh-kernel replay times (`438 ms`–`8,259 ms`), and transitive axiom receipts across all `30` theorems. |

## Revalidation

All three harnesses run cleanly in isolated `tempfile.TemporaryDirectory()`
sandboxes:

1. **Reproduce the live `%fs:`/`%gs:` SFI escape, `0x67`/`0x66` silicon probes,
   GCC/Rustc canary `.o` extraction, and `sfi_gcc_rewriter_v2.py` `128 MiB`
   benchmark (~5 s):**
   ```bash
   python3 -B support/reproduce_prefix_sfi_escape_and_rewriter_v2.py
   ```
   Expected terminal line: `ALL_PREFIX_SFI_ESCAPE_AND_REWRITER_V2_PROBES_PASSED` (`exit 0`).

2. **Re-run the `352`-vector Cartesian `(Prefix × Opcode)` live silicon +
   disassembler sweep (~4 s; pass `--xed-bin` / `--xed-lib` when a local
   `intelxed` build is present):**
   ```bash
   python3 -B support/probe_cartesian_prefix_silicon_and_xed.py
   ```
   Expected terminal line: `CARTESIAN_SILICON_AND_XED_352_PASSED` (`exit 0`, `318` `OK_EXEC`, `32` `FAULT_UD`, `2` `FAULT_GP0`).

3. **Compile all 9 staged V2 Lean modules, certify the `2,048` B `-fstack-protector-strong`
   SFI image and all `352` silicon vectors in Lean `v4.34.1`, and run fresh
   `(trustLevel := 0, level := .private)` kernel replay across `30` theorems (~95 s):**
   ```bash
   python3 -B support/verify_all_v2_lean_and_replay.py
   ```
   Expected terminal line: `ALL_V2_LEAN_MODULES_352_SILICON_CERT_2048B_SFI_CERT_AND_REPLAY_PASSED` (`exit 0`).

### Minimal Conditions Invalidating Findings

- Running the live silicon `wrfsbase`/`wrgsbase` probes on a kernel or CPU with
  `CR4.FSGSBASE = 0` will trap on `wrfsbase` (though the `ARCH_GET_FS` glibc TLS
  `%fs` SFI escape still reproduces without `FSGSBASE`).
- Running `probe_cartesian_prefix_silicon_and_xed.py` on an AMD64 processor will
  show `fetch_len = 4` / `5` (`rel16`) instead of Intel `f64` `fetch_len = 6` / `7`
  on `66 E9` and `66 0F 84`, confirming the cross-vendor hazard that
  `PicMultiFnSfiV2` blocks by rejecting `0x66` on near branches.
