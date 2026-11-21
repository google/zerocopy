# Byte-decoded x86-64 sharded lifting, dead-flag collapse, private stack separation, and loop-invariant-free binary SFI containment in Lean 4

## Summary

Moving machine-code verification in Lean `v4.34.1` from synthetic pre-decoded
instruction trees (`pc + 1` indexing, no `RFLAGS`, word-typed registers/slots)
to real variable-length (`1..15` byte) `gcc 15.2.0` x86-64 `.o` byte streams
exposes three concrete scaling cliffs—and admits three kernel-checked
architectural collapses plus a loop-invariant-free second verification mode:

1. **Disassemblers are unsound byte-validity oracles on x86-64 silicon, whereas
   split length/body decoding matches hardware and admits a universal
   prefix-invariance bridge.** Cross-checking `48` adversarial byte sequences on
   an Intel Xeon Ice Lake-SP CPU via a two-page `mmap` (`PROT_READ | PROT_EXEC`
   followed by `PROT_NONE` + `SA_SIGINFO` trap inspection) shows **`48 / 48`
   (`100.0%`)** exact length and fault agreement with our pure Lean `v4.34.1`
   decoder `ByteX86.decodeX64` (`support/ByteX86Base.lean`), whereas **both
   `llvm-mc 21.1.8` and `objdump 2.47` silently accept `11 / 11` (`100.0%`)** of
   architectural decode-fault specimens (`2` overlong `> 15`-byte `#GP(0)`
   encodings, `4` illegal `LOCK` `#UD` encodings, and `5` legacy-prefixed VEX
   `{0x66, 0xF2, 0xF3, REX, 0xF0} + 0xC5` `#UD` encodings) with exit code `0`
   and zero warnings. Factoring `decodeX64` into prefix/length scanning
   (`scanPrefixes` + `ildBodyLen`) followed by exact-slice parsing
   (`parseExactBody (body.take bLen)`) yields a single 34-line universal
   determinism theorem (`decodeX64_prefix_invariant`) that lifts local chunk
   decodes to global 16-byte fetch windows (`fetchWindow16`) without unfolding
   opcode dispatch.
2. **Backward `DeadFlagCollapse` eliminates both the $O(4^K)$ demonic-flag
   case-split cliff and the open-term `parity8` WHNF wall.** On live silicon,
   `imul rax, rsi` (`48 0f af c6`) on `0 * 7 = 0` leaves `ZF = 0, PF = 1`,
   confirming that Intel SDM undefined status flags must be modeled demonically
   (`nd : Nat → UndefFlags`). Across `5` `gcc 15.2.0` `-O2` and `-O3 -mavx2`
   object workloads (`210` instructions, `818` `.text` bytes), **`507 / 516`
   (`98.26%`)** of status-flag bit writes, **`105 / 105` (`100.0%`)** of
   demonic undefined flag writes, and **`86 / 86` (`100.0%`)** of 8-bit `PF`
   XOR-parity writes are dead before any flag consumer. Without pruning, Lean
   `v4.34.1` (`0` `set_option`, default `200,000` heartbeats) fails at **`K = 3`
   `imul` instructions** under explicit demonic case-splitting (`20.50 s`) and
   at **`L = 4` instructions (`21` bytes)** under open-term symbolic `runX64`
   reduction (`18.36 s`). Factoring byte decoding and backward liveness into a
   closed certificate (`compileByteLeaf ... = some ... := rfl`) plus
   parameterized flag-mask simulation (`checkByteLeaf_sound`) verifies a
   `64`-instruction (`302`-byte) variable-length leaf over all `nd` in
   **`1.92 s`** (`875 ms` standalone `(level := .private)` kernel replay).
3. **Unexposed Private Stack-Frame Separation (`PrivateStackSep`) collapses
   $O(S \times P)$ flat byte-memory aliasing to $O(S + P)$ even under dynamic
   `and rsp, -32` stack realignment, and `ByteShardedTreeLift` scales linearly
   to `N = 5,120` variable-length instructions (`24,160` bytes).** When a
   function never leaks an `rsp`-derived address, `realigned_frame_envelope_separation`
   confines `[rsp, rsp + 8 * maxSlots)` inside `[rsp_entry - (39 + frameSz), rsp_entry)`
   and proves saved `%rbp` disjoint from `[rsp + 8 * slot]` spills so `leave; ret`
   restores caller `rsp`/`rbp`. At `S = 64` spills and `P = 32` caller pointers
   (`2,048` pairs), `PrivateStackSep` compiles **`8.95x` faster** (`1.88 s` vs
   `16.82 s`) with **`4.18x` smaller `.olean` artifacts** than pairwise
   `ByteMem` disjointness rewrites. Combining `ByteCodeTree`, C++ GMP `Nat.ble`
   offset guards, `DeadFlagCollapse`, and `PrivateStackSep` verifies `N = 5,120`
   variable-length instructions (`24,160` bytes) in **`207.46 s` sequential CPU**
   (**`30.82 s` parallel shard critical path**, `0.208 s` top composition,
   `64,886 ms` private kernel replay, axioms `[Quot.sound, propext]`).
4. **Decidable Binary SFI Containment (`checkSfiObject`) eliminates
   `#[anneal::trusted]` waivers on arbitrarily cyclic C `.o` archives with zero
   manual loop invariants.** Over the **exact same `decodeX64` and `runX64` ISA
   semantics**, `checkSfiObject_preserves_rust_host_safety` (`support/ByteX86Sfi.lean`)
   proves that any object passing `checkSfiObject totalBytes img = true`
   (32-byte bundle targets, adjacent `mov idx32, src32` + `[r14 + idx*1 + disp]`
   sandboxing, and read-only `%r14`, `%rsp`, `%rbp`, `%rbx`, `%r12`–`%r15`)
   never faults, never clobbers Rust callee-saved registers, never escapes
   `[0, totalBytes)`, and never writes outside `[r14, r14 + 2^32 + 64 KiB)` for
   all step counts `steps : Nat` and demonic streams `nd`. Sharded via
   `checkSfiSubtree_node`, `SfiTop_10240` verifies **`N = 10,240` cyclic x86-64
   instructions (`40,960` bytes, `1,280` bundles with backward loops and masked
   indirect jumps)** with zero manual loop invariants in **`554.46 s` sequential
   CPU** (**`63.90 s` parallel critical path**, `0.306 s` top composition,
   `136,684 ms` private kernel replay).

> **Prefix-Decoding Errata (`FS:`/`GS:`, `0x67`, `0x66`):** `ByteX86.decodeX64` (`support/ByteX86Base.lean`) scanned `0x64` (`FS:`), `0x65` (`GS:`), and `0x67` (`addr32`) as no-op legacy prefixes under a flat `fsBase = gsBase = 0` address calculation, and omitted `0x66` (`op16`) `±2`-byte `%rsp` adjustments on `PUSH`/`POP`/`LEAVE`. Consequently, `%fs:0x28` stack-canary reads (`-fstack-protector-strong` / `-Z stack-protector=all`) would mis-decode as flat `[0x28]`, `0x67` memory instructions would ignore 32-bit effective-address truncation, and `64`/`65` stores would bypass `ByteX86Sfi.checkSfiObject` on Linux threads with non-zero `%fs`/`%gs`. Corpus package `x86-64-fs-gs-segment-sfi-escape-addr32-opsize-decoding-and-pass2-prefix-fuzzing` (`RealX64PrefixSem.lean`, `StackCanaryLiftV2.lean`, `PicMultiFnSfiV2.lean`, `ByteX86Pass2CorrespondenceV2.lean`) repairs all four prefix families and mechanizes `PrivateStackCanarySep` lifting over arbitrary `(fsBase, gsBase : BitVec 64)`.

## Applicability

The findings in this report govern the design and scaling of machine-code
verification pipelines in Lean 4 that consume compiled x86-64 ELF relocatable
objects (`.o`) or static archives (`.a`) linked into verified Rust programs,
specifically connecting the thirteen subjects recorded in `REPORT.json`:

- **Theorem prover and kernel replay target:** Lean `v4.34.1` (`leanprover/lean4`
  commit `5045d0056413266e57c625dcd7c365b10e377c52`) invoked with
  `-DElab.async=false -Ddebug.skipKernelTC=false -j1 -M2048` and zero
  `set_option` overrides (`maxHeartbeats = 200,000`, `maxRecDepth = 512`),
  audited out-of-process via `importModules ... (trustLevel := 0) (plugins := #[])
  (loadExts := false) (level := .private)` followed by `base.toKernelEnv.replay`
  matching the replay contract of Anneal (`joshlf/anneal` commit
  `c131b320eeeb26ef692e5afd5ec8db49ee518613`).
- **Compiler, binary tools, and hardware target:** 64-bit Ring-3 System V AMD64
  psABI (`1.0`) code emitted by `gcc` (`Debian 15.2.0-14`, `x86_64-linux-gnu`)
  at `-O2` and `-O3 -mavx2 -fcf-protection=full`, inspected with GNU `objdump` /
  `readelf` (`2.47`) and `llvm-mc` (`21.1.8`), and executed on an Intel Xeon
  Ice Lake-SP processor (`GenuineIntel` Family 6 Model 106 Stepping 6, feature
  flags `sse2 avx avx2 avx512f bmi1 bmi2 abm fsgsbase ibrs_enhanced`) under
  Linux `7.1.6` (`x86_64`) against the normative rules of the Intel 64 and
  IA-32 Architectures Software Developer's Manual (`325462-087US`, 2025).
- **Relationship to prior formal ISA, lifting, fuzzing, and SFI systems:**
  `xoreaxeaxeax/sandsifter` (`8375e6123d093629e3e4437d7903839fd0742c2a`) defines
  the page-boundary trap technique adapted into `support/sandsifter_page_oracle.py`;
  `intelxed/xed` (`0bcb6237345c5066726dcc08b3d87928df3b5b26`), `acl2/acl2`
  `x86isa` (`f040a8db474f68e11b5fa980c99b7c1f7be28e54`), and `awslabs/s2n-bignum`
  (`280a220986a0bc6249248187717a771153d073db`) provide architectural points of
  comparison for x86-64 length decoding, demonic `RFLAGS`, and symbolic
  evaluation; and `lfi-project/lfi-verifier`
  (`8c3c47983572039b138f8fa15c12231f2655bbef`) informs the base-register +
  32-bit zero-extension SFI discipline mechanized in `support/ByteX86Sfi.lean`
  (adapted here from AArch64 fixed-width instructions to variable-length 32-byte
  x86-64 bundles).

Exact compile wall times, CPU seconds, RSS, and kernel replay milliseconds are
specific to the observed Intel Xeon `2.60 GHz` Linux host and Lean `v4.34.1`.
The asymptotic complexity separations ($O(4^K)$ vs. $O(L)$, $O(S \times P)$ vs.
$O(S + P)$, unary `Nat.decLe` vs. C++ GMP `Nat.ble`, and loop-invariant-free SFI
induction) and the proved theorems in `support/ByteX86Base.lean` and
`support/ByteX86Sfi.lean` hold across all hosts running Lean `v4.34.1`.

## Findings

### 1. Silicon page-boundary decode oracle vs. `ByteX86.decodeX64`, `llvm-mc 21.1.8`, and `objdump 2.47`

`Basis: normative + execution + source`

To measure ground-truth hardware instruction length and decode-vs-execute fault
priority without relying on disassemblers, `support/sandsifter_page_oracle.py`
compiles and runs a C/assembly harness that allocates two adjacent `4,096`-byte
pages via `mmap`: page 0 mapped `PROT_READ | PROT_EXEC` and page 1 mapped
`PROT_NONE`. For each candidate byte sequence $B$ (`|B| ≤ 16`), the harness
places `B ++ [0xCC]` (`int3` trap) at `PAGE_END - L` for $L \in \{1, \dots, 17\}$,
executes from `PAGE_END - L` with controlled GPRs and cleared `RFLAGS`
(`{CF, PF, AF, ZF, SF, OF} = 0`), and intercepts `SIGSEGV`, `SIGILL`, and
`SIGTRAP` via `SA_SIGINFO` (`ucontext_t` inspecting `REG_RIP`, `REG_TRAPNO`,
`REG_ERR`, post-state GPRs, memory, and `REG_EFL`):

- For any valid non-branch instruction of true silicon decode length $\ell \le 15$:
  placements $L < \ell$ fault during instruction fetch at `PAGE_END` with `#PF`
  (`trapno = 14`, `err & 0x10 != 0`, `cr2 = PAGE_END`), whereas placement
  $L = \ell$ fetches all $\ell$ bytes inside page 0, executes the instruction,
  and either faults fetching the trailing `0xCC` at `PAGE_END` with advanced
  `REG_RIP == PAGE_END` ($L = \ell$) or hits `SIGTRAP` (`trapno = 3`) at
  $L = 17$ with `REG_RIP == start + \ell + 1`.
- For architectural decode faults (`#UD`, `trapno = 6`), placements $L < \ell$
  raise `#PF` (`trapno = 14`) while placement $L = \ell$ transitions sharply to
  `SIGILL` (`trapno = 6`, `REG_RIP == start`), measuring the exact byte count
  $\ell$ consumed by the hardware instruction-length decoder before `#UD` fires.
- For overlong sequences exceeding Intel SDM Vol. 2A §2.1.1's 15-byte ceiling
  (e.g., `15` `0x66` prefixes + `0x90`, or `15` `0x66` prefixes followed by the
  harness's `0xCC`), placements $L \le 15$ raise `#PF` (`trapno = 14`) at
  `PAGE_END`, and placement **`L = 16` transitions to `#GP(0)`** (`SIGSEGV`,
  `trapno = 13`, `err = 0`, `REG_RIP == start`), confirming that Ice Lake-SP
  fetches byte 16 before raising length-exceeded `#GP(0)` prior to opcode
  execution (even when byte 16 is `0xCC` `int3`).

Across all **`48` specimens** in `support/sandsifter_page_oracle_results.json`
(`36` `OK_EXEC`, `9` `FAULT_UD`, `2` overlong `FAULT_GP0`, and `1` Ring-3
privileged `cli` `FAULT_GP0`), `ByteX86.decodeX64` in Lean `v4.34.1` achieves
**`48 / 48` (`100.0%`) exact verdict and length agreement** with silicon. By
contrast, **both `llvm-mc 21.1.8` and `objdump 2.47` silently accept `11 / 11`
(`100.0%`) of architectural decode-fault specimens** (`rc = 0`, zero stderr
diagnostics):

| Specimen category | Representative hex bytes | Silicon trap & decode len | `ByteX86.decodeX64` (Lean `v4.34.1`) | `llvm-mc 21.1.8 --disassemble` | `objdump 2.47 -D -b binary` |
| --- | --- | --- | --- | --- | --- |
| Max legal length (`15`B) | `66`×14 + `90` | `OK_EXEC`, `15`B | `.ok .nop 15` | `nop` (`rc=0`) | `data16`×14 (`rc=0`) |
| Overlong `> 15`B (`#GP(0)`) | `66`×15 + `90` (`16`B) | `FAULT_GP0` (`trapno=13`), at `16`B | `.fault .gpLenExceeded` | **Silent false-accept:** `nop` (`rc=0`) | **Silent false-accept:** `data16`... (`rc=0`) |
| Overlong prefix stream + `int3` | `66`×15 (`+ cc` at byte 16) | `FAULT_GP0` (`trapno=13`), at `16`B | `.fault .gpLenExceeded` | **Silent false-accept:** `data16` (`rc=0`) | **Silent false-accept:** `data16`... (`rc=0`) |
| Hintable NOP (`0F 1E /r`, no `F3`) | `0f 1e fa` (`3`B) | `OK_EXEC`, `3`B (no-op) | `.ok .nop 3` | **Misparsed:** emits `cli` + warning | `nop edx` (`rc=0`) |
| Ring-3 privileged `cli` | `fa` (`1`B) | `FAULT_GP0` (`trapno=13`), `1`B | `.fault .gpRing3Priv` | `cli` (`rc=0`, Ring-0 valid) | `cli` (`rc=0`, Ring-0 valid) |
| Illegal `LOCK` on non-RMW / reg (`4` cases) | `f0 90`, `f0 48 01 f0`, `f0 48 8b 07`, `f0 48 89 07` | `FAULT_UD` (`trapno=6`), `2..4`B | `.fault .udIllegalLock` (`4/4`) | **Silent false-accept (`4/4`):** `lock; addq %rsi, %rax` etc. | **Silent false-accept (`4/4`):** `lock mov rax, [rdi]` etc. |
| Segment / addr32 before VEX (`2` cases) | `2e c5 f8 77`, `67 c5 f8 77` | `OK_EXEC`, `4`B (`vzeroupper`) | `.ok .vzeroupper 4` (`2/2`) | `vzeroupper` / `addr32 vzeroupper` (`rc=0`) | `cs vzeroupper` / `addr32 vzeroupper` (`rc=0`) |
| Forbidden `{66,F2,F3,REX,F0}` before VEX (`5` cases) | `66 c5 f8 77`, `f2 c5 f8 77`, `f3 c5 f8 77`, `48 c5 f8 77`, `f0 c5 f8 77` | `FAULT_UD` (`trapno=6`), `4`B (`5/5`) | `.fault .udIllegalVexPrefix` (`5/5`) | **Silent false-accept (`5/5`):** `vzeroupper` / `rep vzeroupper` | **Silent false-accept (`5/5`):** `data16` / `rex.W vzeroupper` |
| REX last-wins & legacy nullification (`6` cases) | `41 40 90` vs `40 41 90`; `41 66 90` vs `66 41 90`; `48 67 01 f0` vs `67 48 01 f0` | `OK_EXEC`: `nop` vs `xchg32`; `nop` vs `xchg16`; `add32` vs `add64` | Exact `6/6` match (`stepPrefix` resets `rex := none` on legacy byte) | Matches semantics (`6/6`) | Splits dead REX as standalone pseudo-insn |
| `IMUL` undefined flags (`0 * 7 = 0`) | `48 0f af c6` (`rax=0, rsi=7`) | `OK_EXEC`, `4`B, `rax = 0`, **`efl6 = 0x004` (`ZF=0, PF=1`)** | `.ok (.imulRR64 .rax .rsi) 4` (`evalImul64` leaves `{ZF,SF,PF,AF}` demonic) | `imulq %rsi, %rax` | `imul rax, rsi` |
| `BSF` vs. `TZCNT` on zero (`rcx = 0`) | `48 0f bc d1` vs `f3 48 0f bc d1` | `BSF`: `rdx` unchanged, `ZF=1,CF=0`; `TZCNT`: `rdx=64`, `CF=1,ZF=0` | Exact `4`B `.bsf64` vs `5`B `.tzcnt64` match | `bsfq` vs `tzcntq` | `bsf` vs `tzcnt` |

Three immediate TCB rules follow from these hardware observations:

1. **Never gate byte-level proof or SFI admission on `llvm-mc` or `objdump` exit
   status.** An attacker or mis-relocated jump landing one byte early on a `0x66`,
   `0x48`, or `0xF0` byte immediately preceding `0xC5`/`0xC4` (VEX) or `0x8B`
   (`MOV`) sees clean disassembly in both tools while triggering `#UD` on
   hardware—or, conversely, `llvm-mc` splits `f0 90` into two pseudo-lines
   (`lock` + `nop`), hiding instruction-boundary desynchronization.
2. **Prefix state is order-sensitive, not commutative.** Intel SDM Vol. 2A §2.2.1
   requires a `REX` prefix (`0x40..0x4F`) to *immediately* precede the opcode or
   `0x0F` escape byte. On silicon, `41 66 90` leaves `rax = 0x1111111122222222`
   and `r8 = 0x7777777788888888` untouched (`nop`), whereas `66 41 90` swaps
   their low 16 bits (`rax = 0x1111111122228888`, `r8 = 0x7777777788882222`);
   similarly `48 67 01 f0` nullifies `REX.W` and zero-extends the 32-bit sum
   (`rax = 0x5`), whereas `67 48 01 f0` computes the full 64-bit sum
   (`rax = 0x300000005`). Modeling prefixes as an unordered set of booleans is
   unsound; `stepPrefix` (`ByteX86Base.lean:356–363`) resets `rex := none`
   whenever any legacy prefix (`0xF0, 0xF2, 0xF3, 0x66, 0x67, 0x2E, 0x3E, ...`)
   is scanned after a `REX` byte, and `parseExactBody` rejects VEX (`0xC4`/`0xC5`)
   whenever `ps.has66 || ps.rep != .none || ps.rex.isSome || ps.hasLock`. *(Errata: `stepPrefix` in `ByteX86Base.lean` did not propagate `0x64`/`0x65` `FS:`/`GS:` segment overrides, `0x67` `addr32` effective-address truncation, or `0x66` `d64` `PUSH`/`POP`/`LEAVE` operand-size overrides (`REX.W` precedence: `66 48 50` = 8B push vs. `48 66 50` = 2B push) into `X64Instr`; see corpus package `x86-64-fs-gs-segment-sfi-escape-addr32-opsize-decoding-and-pass2-prefix-fuzzing` for the repaired silicon-certified prefix semantics.)*
3. **Deterministic `ZF = (result == 0)` models for `IMUL` are unsound on real
   Intel hardware.** On `rax = 0, rsi = 7`, `imul rax, rsi` writes `0` to `rax`
   while leaving `ZF = 0` (`efl6 = 0x004`) on Ice Lake-SP. Theorem
   `imul_je_diverges_under_demonic_flags` (`ByteX86Base.lean:1570–1579`)
   formalizes that `imul rax, rsi; je +2` diverges in `rip` (`9` vs. `7`) across
   legal hardware executions from identical architectural pre-states.

### 2. Universal variable-length decode prefix-invariance (`decodeX64_prefix_invariant`) and the ELF PIC `.rela.rodata` shifted-addend law

`Basis: source + execution + derived`

In variable-length x86-64 operational semantics (`stepX64`, `ByteX86Base.lean:1413`),
the machine fetches a 16-byte lookahead window `fetchWindow16 img.code s.rip`
from the global `ByteCodeTree` at every step and advances `rip` by the decoded
byte length `len` (`1 ≤ len ≤ 15`). Naively proving that a locally decoded
`len`-byte slice `pfx` decodes identically when embedded inside a larger code
tree requires case-splitting over every opcode, ModR/M mode, SIB `base=5`
escape, and immediate width—an $O(|\text{ISA}|)$ proof tax that breaks
modularity whenever new opcodes are added.

`ByteX86Base.lean` eliminates this tax by factoring `decodeX64` (`L1100–1113`)
into two stages:

1. **Prefix + length determination (`scanPrefixes` + `ildBodyLen`, `L365–587`):**
   scans up to 16 prefix bytes, determines exact body length `bLen ≥ 1` solely
   from the opcode, `0x0F` escape, VEX header, and ModR/M + SIB topology
   (`modrmLenAt`), checks `(body.take bLen).length < bLen` (`truncated`) and
   `15 < pfxLen + bLen` (`gpLenExceeded`), and
2. **Exact-slice body parsing (`parseExactBody ps (body.take bLen)`, `L845–1098`):**
   consumes *only* `body.take bLen`, never inspecting trailing bytes beyond
   `pfxLen + bLen`.

Because `List.take_append_of_le_length` collapses `(body ++ sfx).take bLen` to
`body.take bLen` whenever `bLen ≤ body.length`, prefix-invariance holds
universally in **34 lines** (`ByteX86Base.lean:1168–1201`) **without unfolding
`parseExactBody` at all**:

```lean
theorem decodeX64_prefix_invariant {pfx : List UInt8} {ins : X64Instr} {len : Nat}
    (hok : decodeX64 pfx = .ok ins len) (sfx : List UInt8) :
    decodeX64 (pfx ++ sfx) = .ok ins len
```

Combined with `fetchBytes_prefix` (`L1256–1276`) and `checkLeafBytesAt_getByte?`
(`L2037–2072`), any leaf or SFI bundle verified on its finite byte list lifts
immediately to `stepX64` over an arbitrarily large `ByteCodeTree`.

Applying this byte-accurate model to `gcc 15.2.0 -O2 -fcf-protection=full`
position-independent switch tables (`switch_pic8_o2` in `Suite 1`, `48`
instructions, `179` `.text` bytes) surfaces a critical ELF relocation invariant
for `.o` lifters that ingest unlinked relocatable objects (`readelf -r -W`):

- GCC emits `lea rcx, [rip + 0x0]` (`48 8d 0d 00 00 00 00` at `.text + 0x0d`,
  with `.rela.text` `R_X86_64_PC32` targeting `.rodata - 0x04`), zero-extends the
  index (`mov edi, edi`), loads a signed 32-bit relative offset
  `movsxd rax, DWORD PTR [rcx + rdi*4]` (`48 63 04 b9`), adds the table base
  `add rax, rcx` (`48 01 c8`), and dispatches via CET `notrack jmp rax`
  (`3e ff e0`, decoded at `L1052–1059`).
- In `.rela.rodata`, entry $k \in \{0..7\}$ at section offset $4k$ has relocation
  type `R_X86_64_PC32` (`S + A_k - P`) against symbol `S = .text`. Because the
  relocated storage unit is at $P_k = \text{.rodata} + 4k$, GCC biases the raw
  relocation addend by $+4k$:
  $$A_k = \text{target}_k + 4k \implies (S + A_k) - P_k = (\text{.text} + \text{target}_k) - \text{.rodata}.$$
  In `switch_pic8_o2.o`, the raw `.rela.rodata` addends are
  `[64, 92, 120, 140, 152, 180, 56, 76]`, whereas the true instruction-boundary
  `.text` targets are `[64, 88, 112, 128, 136, 160, 32, 48]`.
- Theorem `gcc_pic_switch8_unadjusted_addend_corrupts` (`GccRealObjectProofs` in
  `support/bench_byte_x86_lifting_and_sfi.py`) proves on the actual GCC bytes
  that an `.o` loader that forgets $-P_k$'s intra-`.rodata` offset $4k$ sends
  `op = 1` to `.text + 92`—4 bytes inside the 8-byte immediate of
  `48 b8 15 7c 4a 7f b9 79 37 9e` (`movabs rax, 0x9e3779b97f4a7c15` at byte
  `88`)—executing immediate constant bytes as unintended instructions, whereas
  exact `S + A_k - P_k` resolution proves all 8 switch arms plus the symbolic
  `ja` default arm (`gcc_pic_switch8_case1_symbolic_verified`,
  `gcc_pic_switch8_default_symbolic_verified`) over arbitrary `baseMem`, `x`,
  `y`, and demonic `nd`.

### 3. Empirical `RFLAGS` death rate in `gcc 15.2.0`, the $O(4^K)$ and `parity8` WHNF cliffs, and certified `DeadFlagCollapse`

`Basis: execution + source + derived`

Backward CFG dataflow analysis across `5` `gcc 15.2.0` workloads in
`support/gcc_object_and_flag_liveness_probe.py` (`support/gcc_object_and_flag_liveness_results.json`)
quantifies how often status-flag writes (`{CF, PF, AF, ZF, SF, OF}`) actually
survive to a conditional jump, `cmovcc`, `setcc`, or `adc`/`sbb`:

| `gcc 15.2.0` `.o` workload | Flags | `.text` bytes | Insns (B/insn) | Flag-bit writes | Dead flag-bit writes | Demonic undef writes (`imul`/`shl`/`xor` `AF`) | Dead demonic undef writes | `PF` (`parity8`) writes | Dead `PF` writes |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `straight_alu_mix_o2` | `-O2 -fcf-protection=full` | `84` | `23` (`3.65`) | `84` | `84` (`100.0%`) | `19` | `19` (`100.0%`) | `14` | `14` (`100.0%`) |
| `aligned_frame_spills_o2` | `-O2 -mno-red-zone -fcf-protection=full` | `329` | `78` (`4.22`) | `204` | `203` (`99.51%`) | `43` | `43` (`100.0%`) | `34` | `34` (`100.0%`) |
| `switch_dispatch_8_o2` | `-O2 -fcf-protection=full` | `179` | `48` (`3.73`) | `120` | `118` (`98.33%`) | `25` | `25` (`100.0%`) | `20` | `20` (`100.0%`) |
| `avx2_vec_accum_o3` | `-O3 -mavx2 -fcf-protection=full` | `114` | `29` (`3.93`) | `30` | `27` (`90.00%`) | `4` | `4` (`100.0%`) | `5` | `5` (`100.0%`) |
| `cyclic_crc_state_o2` | `-O2 -fcf-protection=full` | `112` | `30` (`3.73`) | `78` | `75` (`96.15%`) | `14` | `14` (`100.0%`) | `13` | `13` (`100.0%`) |
| **Aggregate (`5` `.o` files)** | — | **`818`** | **`210` (`3.90`)** | **`516`** | **`507` (`98.26%`)** | **`105`** | **`105` (`100.0%`)** | **`86`** | **`86` (`100.0%`)** |

In optimized compiler output, only loop/switch `cmp` and `test` instructions immediately
preceding `jcc` keep `1`–`2` deterministic flags (`ZF`, `CF`) live (`9 / 516` =
`1.74%` of all flag writes); **`100.0%` (`105 / 105`)** of demonic undefined flag
writes and **`100.0%` (`86 / 86`)** of 8-bit `PF` XOR-tree writes are dead.

`Suite 2` in `support/bench_byte_x86_lifting_and_sfi.py` (`support/byte_x86_scaling_and_sfi_results.json`)
measures what happens in Lean `v4.34.1` (`0` `set_option`, `200,000` heartbeats)
without vs. with certified backward `DeadFlagCollapse`:

| Formulation in Lean `v4.34.1` (`-DElab.async=false -Ddebug.skipKernelTC=false -j1`) | Scale | Exit `rc` | Compile wall (`s`) | Peak RSS (`MB`) | `.olean` (`KB`) | Private replay (`ms`) | Outcome / bottleneck |
| --- | --- | ---: | ---: | ---: | ---: | ---: | --- |
| Explicit demonic `(cf, of)` case split (`DemonicSplit_1`) | `K = 1` `imul` (`4` goals) | `0` | `0.373` | `280.1` | `46.6` | `34` | Passes (`[Quot.sound, propext]`) |
| Explicit demonic `(cf, of)` case split (`DemonicSplit_2`) | `K = 2` `imul` (`16` goals) | `0` | `5.204` | `284.2` | `55.9` | `43` | `13.9x` slower for $+1$ `imul` |
| Explicit demonic `(cf, of)` case split (`DemonicSplit_3`) | `K = 3` `imul` (`64` goals) | **`1`** | `20.498` | `268.2` | — | — | **Fails:** deterministic `whnf` timeout (`200,000` heartbeats) |
| Explicit demonic `(cf, of)` case split (`DemonicSplit_4`) | `K = 4` `imul` (`256` goals) | **`1`** | `20.240` | `266.6` | — | — | **Fails:** deterministic `whnf` timeout (`200,000` heartbeats) |
| Uncollapsed open-term `runX64` (`UncollapsedWhnf_1`) | `L = 1` insn (`10`B) | `0` | `0.353` | `276.6` | `39.8` | — | Passes |
| Uncollapsed open-term `runX64` (`UncollapsedWhnf_2`) | `L = 2` insns (`13`B) | `0` | `1.576` | `280.6` | `44.9` | — | `4.5x` slower at `2` insns |
| Uncollapsed open-term `runX64` (`UncollapsedWhnf_4`) | `L = 4` insns (`21`B) | **`1`** | `18.356` | `266.7` | — | — | **Fails:** deterministic `whnf` timeout (`200,000` heartbeats) |
| Uncollapsed open-term `runX64` (`UncollapsedWhnf_8` / `16`) | `L = 8..16` (`36..74`B) | **`1`** | `18.49–19.51` | `268.6` | — | — | **Fails:** deterministic `whnf` timeout (`200,000` heartbeats) |
| **Certified `DeadFlagCollapse` (`CollapsedLeaf64`)** | **`L = 64` insns (`302`B, `8` `imul` + `16` shifts + `24` ALU)** | **`0`** | **`1.918`** | **`355.5`** | **`567.7`** | **`875`** | **Passes** (`∀ nd`, `[Quot.sound, propext]`) |

Why does `CollapsedLeaf64` verify `64` instructions (`302` bytes, including `8`
demonic `imul`s and `16` demonic shifts = $2^{8 \times 4 + 16 \times 5} = 2^{112}$
nondeterministic flag outcomes) in **`1.92 s`** while `UncollapsedWhnf_4` dies
at `4` instructions in `18.36 s`? Two mechanisms cooperate in
`ByteX86Base.lean:1731–2648`:

1. **Parameterized `FlagsAgreeOn liveMask` simulation (`L79–89`, `L1736–1743`):**
   `AbstractsLeaf maxSlots live s l` relates concrete `X64State` `s` to pure
   `LiftedX64State` `l` only on the boolean mask `live : FlagMask` of flags live
   at that program point. When `liveOut == FlagMask.dead` (`98.26%` of writes),
   `collapseOneInstr` (`L1894–1947`) emits `.aluDead`, `.shiftDead`, or
   `.imulDead`, whose soundness proof discharges flag agreement in $O(1)$ via
   `flagsAgreeOn_dead _ _` **without ever constructing or reducing `parity8`,
   signed overflow, or `nd 0`**. When a `cmp` or `test` feeds a branch
   (`liveOut != FlagMask.dead`), `aluNoLiveUndef op liveOut` verifies that no
   undefined bit (such as `AF` on `xor`/`test`) is live in `liveOut`, and emits
   `.aluFlags` with deterministic flags (`evalAluFlags64_agree_det`, `L1862`).
2. **Closed-certificate separation (`compileByteLeaf ... = some ... := rfl`):**
   `compileByteLeaf` (`L1977–1981`) runs `decodeByteBlock` + backward
   `collapseDecodedList` on **concrete closed byte lists `List UInt8`** with zero
   free variables, allowing Lean's kernel/elaborator evaluator to reduce all byte
   decoding and liveness propagation at native C++ speed, while open state
   variables (`s0`, `l0`, `nd`) interact only with the linear `CollapsedOp` list.

### 4. Unexposed Private Stack-Frame Separation (`PrivateStackSep`) under dynamic `and rsp, -32` stack realignment

`Basis: source + execution + derived`

Real `gcc 15.2.0 -O2` functions with 32-byte aligned locals or AVX2 spills emit
dynamic stack realignment prologues:

```text
f3 0f 1e fa    endbr64
55             push   rbp                 ; rsp1 := rsp0 - 8; mem[rsp1..rsp1+7] := rbp0
48 89 e5       mov    rbp, rsp            ; rbp  := rsp1
48 83 e4 e0    and    rsp, -32            ; rsp2 := rsp1 &&& 0xFFFFFFFFFFFFFFE0
48 83 ec 40    sub    rsp, 0x40           ; rsp  := rsp2 - 64
...            [rsp + 8*slot] spills ...
c9             leave                      ; rsp := rbp + 8 = rsp0; rbp := mem[rbp]
c3             ret
```

On flat byte-addressed `ByteMem := BitVec 64 → BitVec 8`, proving that $S$ stack
stores preserve $P$ caller-owned 8-byte pointers $p_0, \dots, p_{P-1}$ naively
requires $S \times P$ pairwise `readMem64_writeMem64_disjoint` rewrites—and
dynamic `and rsp, -32` masks low address bits nonlinearly, obscuring the constant
offset from `rsp0` (`rspEntry`).

`ByteX86Base.lean` solves both problems constructively using only `Init.*`
(`0` `omega`, `0` SMT):

1. **Exact bitmask-to-remainder identity (`and_mask32_eq_sub_rem`, `L208–247`):**
   Proves bitwise via `BitVec.eq_of_getLsbD_eq` and `Nat.div_add_mod` that for
   every `x : BitVec 64`:
   $$(x \mathbin{\&\&\&} \text{0xFFFFFFFFFFFFFFE0}_{64}) = x - (x \mathbin{\&\&\&} 31_{64}), \qquad (x \mathbin{\&\&\&} 31_{64}).\text{toNat} = x.\text{toNat} \bmod 32 < 32.$$
2. **Realigned stack-envelope separation (`realigned_frame_envelope_separation`, `L1664–1707`) and saved-`rbp` preservation (`saved_rbp_outside_realigned_spills`, `L1709–1729`):**
   For `rsp := ((rspEntry - 8) &&& -32) - frameSz` with `maxSlots * 8 ≤ frameSz`,
   every byte $a = \text{rsp} + 8 \cdot \text{slot} + k$ ($0 \le \text{slot} < \text{maxSlots}$,
   $0 \le k < 8$) satisfies `1 ≤ (rspEntry - a).toNat ≤ 39 + frameSz`
   (`InStackEnvelope rspEntry 103 a` for `frameSz = 64`), AND every byte
   `rsp1 + j` ($0 \le j < 8$) of the saved caller `%rbp` satisfies
   `OutsideSpillRange rsp maxSlots (rsp1 + j)`.
3. **Syntactic non-leakage enforcement in `collapseOneInstr` (`L1894–1947`):**
   Every straight-line instruction touching `.rsp` as a general-purpose source or
   destination is rejected, and only `[rsp + 8 * slot]` with `slot < maxSlots` is
   admitted as a stack store/load, mapping `ByteMem` stack slots to an $O(1)$
   functional slot map `slots : Nat → BitVec 64` inside `LiftedX64State` while
   emitting a single bulk frame-preservation guarantee
   `∀ a, OutsideSpillRange (s.regs .rsp) maxSlots a → sf.mem a = s.mem a`.

In `Suite 1` (`GccRealObjectProofs`), theorem `gcc_aligned_frame_mix_full_verified`
combines these pieces on the literal `62`-instruction (`251`-byte) `gcc 15.2.0 -O2`
`aligned_frame_spills_o2` binary (`5`-insn realignment prologue + `55` literal
GCC spill/`imul`/shift/`xor`/`add` instructions + `leave; ret`), proving in
**`8.46 s`** (`7,860 ms` private kernel replay) exact functional return value in
`%rax`, exact restoration of `%rsp` and `%rbp`, and byte-for-byte preservation of
all caller memory outside the `103`-byte stack envelope across all demonic
hardware streams `nd`.

`Suite 3` (`support/byte_x86_scaling_and_sfi_results.json`) isolates the scaling
of caller-pointer preservation across $(S, P)$:

| Spills $S$ | Caller ptrs $P$ | Pairs $S \times P$ | Naive flat `ByteMem` wall (`s`) | Naive `.olean` (`KB`) | `PrivateStackSep` wall (`s`) | `PrivateStackSep` `.olean` (`KB`) | Compile speedup (`Naive / Priv`) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `16` | `4` | `64` | `0.391` | `109.8` | `0.704` | `194.6` | `0.56x` (fixed byte-decode overhead) |
| `16` | `16` | `256` | `1.410` | `335.6` | `0.792` | `208.5` | **`1.78x`** |
| `32` | `16` | `512` | `2.912` | `637.9` | `1.242` | `325.2` | **`2.34x`** |
| `32` | `32` | `1,024` | `7.703` | `1,229.3` | `1.294` | `343.7` | **`5.95x`** |
| `64` | `16` | `1,024` | `6.334` | `1,242.3` | `1.720` | `559.3` | **`3.68x`** |
| `64` | `32` | `2,048` | **`16.817`** | **`2,413.8`** | **`1.879`** | **`577.8`** | **`8.95x` (`4.18x` smaller `.olean`)** |

Crucially, `PrivateStackSep` includes full x86-64 byte decoding (`compileByteLeaf`
on the `4..5`-byte `[rsp + disp]` instructions) plus `checkByteLeaf_sound`, yet
adding `16` more caller pointers at `S = 64` (`P = 16 → 32`) adds only **`0.159 s`**
(`1.720 s → 1.879 s`), whereas naive flat `ByteMem` adds **`10.483 s`**
(`6.334 s → 16.817 s`).

### 5. `ByteShardedTreeLift` linear scaling to `N = 5,120` variable-length instructions (`24,160` bytes) and four Lean `v4.34.1` scaling invariants

`Basis: execution + source + derived`

Scaling sharded lifting from synthetic `pc + 1` ASTs to multi-kilobyte
variable-length byte streams under Lean `v4.34.1`'s default limits (`0`
`set_option`, `maxRecDepth = 512`, `maxHeartbeats = 200,000`) exposed **four
distinct elaborator and kernel recursion traps**, each requiring an explicit
data/theorem representation invariant:

1. **Trap 1 — Unary `List.length` and `List` syntax recursion at `> ~150..512`
   elements:** Standard `List.length` unfolds unary `List.rec` once per byte,
   exhausting `maxRecDepth = 512` around `150`–`250` bytes inside `isDefEq`, and
   a single monolithic `[b_0, ..., b_1023]` syntax literal exhausts `maxRecDepth`
   during elaboration (`SfiMono_256` at `1,024` bytes fails in `0.68 s` with
   `maximum recursion depth has been reached`). **Fix:** define an 8-element
   stride tail-recursive `lenTR` (`ByteX86Base.lean:425–435`, proved equal to
   `List.length` once via `lenTR_eq_length`) and shard code into top-level `def`
   leaves of `≤ 512` bytes inside `ByteCodeTree`.
2. **Trap 2 — Unary Peano `decide (a ≤ b)` / `decide (a = b)` recursion at byte
   offsets `> 512`:** Even with `ByteCodeTree`, `decide (base + lenTR bs ≤ lsz)`
   invokes `Nat.decLe`, which recurses in unary Peano steps $O(\min(a, b))$ times
   and hits `maxRecDepth = 512` as soon as byte offset `base` or subtree split
   `lsz` reaches `512` bytes (`N ≥ 128` instructions). **Fix:** replace `decide`
   on byte offsets, jump targets, and bundle sizes with **`Nat.ble`**
   (`natLeB`, `natLtB`, `natEqB` in `ByteX86Base.lean:1984–2001`, bridged via
   `Nat.le_of_ble_eq_true` and `Eq.mpr (@Nat.ble_eq x x)`). Because `Nat.ble`,
   `Nat.add`, `Nat.sub`, and `Nat.mod` are **C++ GMP kernel primitives** in Lean
   4 (`reduce_nat`), closed comparisons at offset `40,960` reduce in **`O(1)`
   time and `0` recursion frames**.
3. **Trap 3 — Unassigned metavariable subtraction `?base - lsz =?= 0` in tree
   path proofs:** In `checkLeafBytesAt_goRight`, writing `(base - lsz)` directly
   as the recursive index causes bidirectional elaboration to unify `?base - 604 =?= 0`
   when `leafBase` or `subBase` is not yet assigned, peeling `604` unary
   `Nat.pred` frames (`> 512`). **Fix:** parameterize `checkLeafBytesAt_goRight`
   (`ByteX86Base.lean:2029–2035`) by explicit `{lsz base subBase : Nat}` with
   `(hsub_eq : base - lsz = subBase)` discharged by `rfl` on closed integer
   literals.
4. **Trap 4 — Bidirectional metavariable addition `?n1 + ?n2 =?= N` in sequential
   composition:** When `SegmentVerified_seq` has conclusion
   `SegmentVerified r0 r2 (n1 + n2) ...` with `{n1 n2}` implicit, checking a
   nested composition against expected type `SegmentVerified 0 1510 320 shardFn`
   unifies `?n1 + ?n2 =?= 320` *before* elaborating the subproofs, peeling
   `320 + 256 = 576 > 512` unary `Nat.succ` frames. **Fix:** parameterize
   `SegmentVerified_seq` by `{n1 n2 n3 : Nat}` with trailing
   `(hn : n1 + n2 = n3)` (`rfl` evaluated *after* `h1` and `h2` fix `n1` and `n2`
   to closed literals).

With all four invariants in place (`0` `set_option`), `Suite 4` scales
`ByteShardedTreeLift` (`64`-instruction variable-length leaves averaging `4.72`
B/insn across `movabs` `10`B, `[rsp+disp]` spills `4..5`B, `imul` `4`B, shifts
`4`B, `lea` `4..5`B, and `alu` `3..4`B, grouped `5` leaves = `320` instructions
per shard module) cleanly from `N = 64` to **`N = 5,120` instructions (`24,160`
bytes)**:

| Instructions $N$ | Raw code bytes | Leaves (`64` insn) | Shards | Seq compile sum (`s`) | Critical-path wall (`s`) | Top-module wall (`s`) | Max RSS (`MB`) | `.olean` sum (`MB`) | Private replay (`ms`) | Replayed consts | Kernel axioms |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| `64` | `302` | `1` | `1` | `2.685` | `2.685` | `0.156` | `350.6` | `0.63` | `792` | `13` | `[Quot.sound, propext]` |
| `256` | `1,208` | `4` | `1` | `9.090` | `9.090` | `0.137` | `355.9` | `1.70` | `3,243` | `31` | `[Quot.sound, propext]` |
| `512` | `2,416` | `8` | `2` | `17.647` | `11.278` | `0.149` | `356.9` | `3.16` | `6,661` | `57` | `[Quot.sound, propext]` |
| `1,024` | `4,832` | `16` | `4` | `35.187` | `13.323` | `0.266` | `395.1` | `5.87` | `15,687` | `109` | `[Quot.sound, propext]` |
| `2,560` | `12,080` | `40` | `8` | `92.688` | `19.732` | `0.205` | `575.3` | `13.55` | `33,404` | `261` | `[Quot.sound, propext]` |
| **`5,120`** | **`24,160`** | **`80`** | **`16`** | **`207.462`** | **`30.818`** | **`0.208`** | **`884.8`** | **`26.59`** | **`64,886`** | **`517`** | **`[Quot.sound, propext]`** |

Across the $80\times$ span from `N = 64` to `N = 5,120`, sequential compile time
scales as **$O(N^{0.99})$** (`42.0 ms/insn` at `N = 64` vs. **`40.5 ms/insn`** at
`N = 5,120`), standalone `(level := .private)` `base.toKernelEnv.replay` scales as
**$O(N^{1.00})$** (`12.4 ms/insn` at `N = 64` vs. **`12.7 ms/insn`** at
`N = 5,120`), top-level stitching stays flat at **`0.14–0.27 s`**, and the entire
byte-decoded lifting proof uses **zero `Classical.choice`**, zero `sorryAx`, and
zero `Lean.ofReduceBool`.

Comparing directly against our earlier synthetic `pc + 1` pre-decoded `ShardedTreeLift`
baseline (`17.49 s` compile and `1,842 ms` private replay at `N = 5,000` on a
16-constructor toy AST with no bytes, no `RFLAGS`, and no `ByteMem`), adding full
`1..15` byte variable-length x86-64 decoding, demonic 6-flag `RFLAGS` + `DeadFlagCollapse`,
and byte-addressed `ByteMem` + `PrivateStackSep` increases per-instruction cost by
a constant factor of **`11.6x` in sequential compile** (**`1.76x` on the parallel
shard critical path**: `30.82 s` vs. `17.49 s`) and **`34.4x` in private kernel
replay** (`12.7 ms/insn` vs. `0.37 ms/insn`) while preserving **strict $O(N^{1.00})$
linearity**!

### 6. Two-mode `.o` verification: decidable loop-invariant-free binary SFI containment (`checkSfiObject`) up to `N = 10,240` cyclic instructions (`40,960` bytes)

`Basis: source + execution + derived`

While `ByteShardedTreeLift` makes functional equivalence verification practical
for `10^2`–`10^4`-instruction C/assembly primitives, large C dependencies
(`sqlite3.o`, `libz.a`, codec/compression archives of $5 \times 10^4$–$2 \times 10^5$
instructions with deeply nested pointer loops) remain bottlenecked by **human
specification and loop-invariant authoring**, forcing users to mark FFI boundaries
with unsound `#[anneal::trusted]` waivers.

`support/ByteX86Sfi.lean` (`1,179` lines, `233` kernel constants, `529 ms`
private replay) mechanizes a **decidable, loop-invariant-free Binary SFI
Containment Mode** over the **exact same `ByteX86.decodeX64` byte decoder and
`ByteX86.runX64` operational semantics** as `ByteShardedTreeLift`. Instead of
proving functional postconditions on C data structures, `checkSfiObject` verifies
statically that an arbitrarily cyclic x86-64 `.o` image obeys three machine-code
sandboxing rules within 32-byte aligned bundles:

1. **Bundle-aligned control-flow integrity (`sfiJmpTargetOk`, `peekMaskedJmp2nd`,
   `L132–196`):** Every 32-byte bundle `[bBase, bBase + 32)` decodes cleanly
   without crossing the bundle boundary (`off + len ≤ 32`) and without falling
   off the final bundle (`!(isLast && off + len = 32)` except on `ret` or
   unconditional `jmpRel`). Direct jumps (`jmpRel`, `jccRel`) must target a
   32-byte bundle boundary `< totalBytes`; indirect jumps are admitted *only* as
   an adjacent 2-instruction macro-pair `and eax, mask32; jmp rax` inside the
   same 32-byte bundle with `(mask32 &&& 31) == 0` and `mask32 < totalBytes`
   (`masked32_target_valid`, `L786–803`), preventing mid-macro jumps into the
   `jmp rax` or memory instruction.
2. **32-bit zero-extended `%r14`-arena memory containment (`peekMem2nd`,
   `isSandboxedMem2nd`, `L116–130`, `L50–83`):** Arbitrary `load*`/`store*`/`push`/`pop`/`leave`
   instructions are rejected. Memory reads and writes are admitted *only* as an
   adjacent intra-bundle 2-instruction macro-pair: `mov idx32, src32` (which
   architecturally zero-extends `idx` to `[0, 2^32)`) immediately followed by
   `mov [r14 + idx*1 + disp], src` or `mov dst, [r14 + idx*1 + disp]` with
   `dst` a scratch register and `0 ≤ disp.toNat ≤ 65,528`. Theorem
   `sfi_store_preserves_outside_arena` (`L57–83`) proves every byte written lies
   strictly inside `[r14, r14 + 2^32 + 65,536)`, preserving `OutsideSandboxArena`
   host memory byte-for-byte.
3. **Host register & stack isolation (`isHostProtectedReg`, `L29–48`) and a
   constructive negative control (`guest_stack_callee_save_unsound_under_sfi`,
   `L92–103`):** `isHostProtectedReg` marks `%r14` (arena base), `%rsp`, `%rbp`,
   `%rbx`, `%r12`, `%r13`, and `%r15` (all System V AMD64 callee-saved registers
   plus stack/arena pointers) strictly read-only across `isPureSfiOp` and
   `isSandboxedMem2nd` (sandboxed C code maintains its own guest stack pointer in
   a scratch register or dedicated arena slot, invoked via a tiny host entry/exit
   trampoline). Theorem `guest_stack_callee_save_unsound_under_sfi` (`L92–103`)
   proves constructively on `runX64` why naive SFI designs that allow guest code
   to save/restore `%rbx` on its own sandboxed stack are unsound for host safety:
   a 5-instruction guest sequence overwriting that arena slot before reloading
   `%rbx` halts cleanly (`fault = false`) with `sf.regs .rbx = 0xBADC0FFEE ≠ s0.regs .rbx`,
   corrupting Rust's callee-saved register invariant after `ret`.

To handle multi-instruction macro-pairs (`mov idx32` + `mem`, `and eax, mask` +
`jmp rax`) under single-step `runX64` induction without multi-step stuttering
complexity, `SfiPhase` (`L434–464`) defines a 3-state operational invariant:
`atMacro` (at a verified macro boundary inside the current 32-byte bundle),
`pendingMem` (immediately after `mov idx32, src32` has established
`(s.regs idx).toNat < 2^32`, poised at the validated `[r14 + idx*1 + disp]`
instruction in the same bundle), and `pendingJmp` (immediately after
`and eax, mask32` has established `(s.regs .rax).toNat < totalBytes` and
`% 32 = 0`, poised at `jmp rax`). Single-step induction (`step_preserves_sfiInv`,
`L806–1136`) yields the top-level **loop-invariant-free Rust host safety theorem**
(`ByteX86Sfi.lean:1154–1177`):

```lean
theorem checkSfiObject_preserves_rust_host_safety
    {totalBytes : Nat} {img : X64ObjImage}
    (hok : checkSfiObject totalBytes img = true)
    (s0 : X64State)
    (hrip0 : s0.rip < totalBytes) (hmod0 : s0.rip % 32 = 0)
    (hnf0 : s0.fault = false) :
    ∀ (steps : Nat) (nd : Nat → UndefFlags),
      let sf := runX64 img steps nd s0
      sf.fault = false ∧
      sf.regs .r14 = s0.regs .r14 ∧
      sf.regs .rsp = s0.regs .rsp ∧
      (∀ r, isHostProtectedReg r = true → sf.regs r = s0.regs r) ∧
      (∀ a, OutsideSandboxArena (s0.regs .r14) a → sf.mem a = s0.mem a) ∧
      (sf.halted = false → sf.rip < totalBytes)
```

Because `checkSfiSubtree` is homomorphic over `ByteCodeTree.node`
(`checkSfiSubtree_node`, `L226–233`), `checkSfiObject` shards across `512`-byte
(`16`-bundle = `128`-instruction) leaves with **zero inter-bundle CFG edge
tracking or cutpoint invariants**. `Suite 5` (`support/byte_x86_scaling_and_sfi_results.json`)
benchmarks monolithic vs. sharded SFI verification on cyclic 32-byte bundles
containing `endbr64`, sandboxed loads/stores, `imul`, shifts, backward cyclic
loops (`jb -52` jumping to the previous bundle), and masked indirect jumps
(`and eax, 0xE0; jmp rax`):

| Mode & module | Cyclic insns $N$ | Bundles (`32`B) | Raw code bytes | Shards | Seq compile sum (`s`) | Critical-path wall (`s`) | Top wall (`s`) | Max RSS (`MB`) | `.olean` sum (`MB`) | Private replay (`ms`) | Outcome |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| `SfiMono_64` (1 `.leaf`) | `64` | `8` | `256` | `1` | `2.680` | `2.680` | `2.680` | `378.1` | `0.35` | `951` | Passes |
| `SfiMono_128` (1 `.leaf`) | `128` | `16` | `512` | `1` | `3.890` | `3.890` | `3.890` | `460.3` | `0.67` | `1,616` | Passes |
| `SfiMono_256` (1 `.leaf`) | `256` | `32` | `1,024` | `1` | `0.682` | — | — | `291.4` | — | — | **Fails (`rc=1`):** `maxRecDepth` on `1,024`B `List` literal |
| `SfiMono_512` (1 `.leaf`) | `512` | `64` | `2,048` | `1` | `1.407` | — | — | `317.1` | — | — | **Fails (`rc=1`):** `maxRecDepth` on `2,048`B `List` literal |
| `SfiSharded` (`SfiTop_256`) | `256` | `32` | `1,024` | `1` | `8.317` | `8.317` | `0.176` | `467.8` | `1.25` | `3,242` | Passes (`∀ steps nd`) |
| `SfiSharded` (`SfiTop_1024`) | `1,024` | `128` | `4,096` | `1` | `40.653` | `40.653` | `0.229` | `514.7` | `2.36` | `12,661` | Passes (`∀ steps nd`) |
| `SfiSharded` (`SfiTop_2560`) | `2,560` | `320` | `10,240` | `3` | `94.970` | `38.733` | `0.170` | `509.7` | `5.92` | `29,440` | Passes (`∀ steps nd`) |
| `SfiSharded` (`SfiTop_5120`) | `5,120` | `640` | `20,480` | `5` | `204.873` | `60.847` | `0.178` | `516.9` | `9.60` | `76,917` | Passes (`∀ steps nd`) |
| **`SfiSharded` (`SfiTop_10240`)** | **`10,240`** | **`1,280`** | **`40,960`** | **`10`** | **`554.460`** | **`63.900`** | **`0.306`** | **`515.5`** | **`18.64`** | **`136,684`** | **Passes (`∀ steps nd`, `0` loop invariants)** |

Together, `ByteShardedTreeLift` and `checkSfiObject` yield a **Two-Mode `.o`
Verification Architecture** over a single shared x86-64 decoder and machine TCB
(`ByteX86Base.lean`):

| Property | Mode 1: Functional `.o` Lifting (`ByteShardedTreeLift`) | Mode 2: Binary SFI Containment (`checkSfiObject`) |
| --- | --- | --- |
| **Target C / ASM workload** | Small, high-assurance primitives (`10^1`–`5 × 10^3` insns: crypto, checksums, SIMD kernels, allocators) | Large cyclic C archives (`10^4`–`2 × 10^5` insns: `sqlite3.o`, `libz.a`, parsers, codecs) |
| **Compiler requirement** | Stock `gcc -O2` / `clang -O2` `.o` + ELF relocation resolution (`S + A - P`) | SFI/LFI-instrumented toolchain (`lfi-clang` / `%r14` arena + 32B bundle alignment) |
| **Loop invariants required** | Explicit per-loop cutpoint invariant (`CutBox`) | **Zero (`0` manual loop or data invariants)** |
| **Proved guarantee on `runX64`** | Exact functional postcondition on registers, stack restoration, and memory + host non-aliasing | Unconditional host memory isolation outside `[r14, r14 + 4 GiB + 64 KiB)`, callee-saved/stack preservation, and no faults across `∀ steps nd` |
| **Measured Lean `v4.34.1` cost** | `40.5 ms/insn` compile, `12.7 ms/insn` private kernel replay (`30.8 s` critical path at `N = 5,120`) | `54.1 ms/insn` compile, `13.3 ms/insn` private kernel replay (`63.9 s` critical path at `N = 10,240`), peak RSS `515.5 MB` |
| **`#[anneal::trusted]` waiver** | **Eliminated** (Rust caller receives full functional spec) | **Eliminated** (Rust caller validates untrusted outputs returned in arena buffer; host memory/control safety is kernel-proved) |

## Boundaries

- **Known not to apply:**
  - Disassembler exit-code or syntax acceptance (`llvm-mc`, `objdump`) **does not
    apply** as a soundness check for x86-64 machine-code decoding (`11 / 11`
    architectural `#GP(0)` and `#UD` specimens silently accepted).
  - Deterministic `RFLAGS` semantics for `IMUL`, `SHL`/`SHR`, or `BSF` **do not
    apply** on Intel x86-64 hardware (`imul 0, 7` produces `ZF = 0, PF = 1` on
    Ice Lake-SP), and naive `R_X86_64_PC32` `.rodata` jump-table loading that
    equates raw addend `A_k` with `.text` target offset **does not apply** when
    $k > 0$ (`target_k = A_k - 4k`).
  - Guest-arena saving/restoring of System V callee-saved registers (`%rbx`,
    `%rbp`, `%r12`–`%r15`) **does not preserve** host register integrity without
    a trusted host-side trampoline (`guest_stack_callee_save_unsound_under_sfi`).
- **Unsupported:**
  - `ByteX86.decodeX64` (`support/ByteX86Base.lean`) intentionally fails closed
    (`.fault .unsupported`) outside its modeled 36-constructor Ring-3 integer/VEX
    subset: EVEX (`0x62` AVX-512), x87/MMX, floating-point SSE/AVX data-path
    semantics (`ymm`/`xmm` vector register values beyond prefix/length/fault
    validation and `vzeroupper`), string instructions (`rep movsb`/`stosb`),
    `syscall`, segment-base (`%fs`/`%gs`) TLS loads, and sub-64-bit memory stores
    other than the modeled 32/64-bit forms are unsupported in the prototype and
    require incremental `candidate:<feature>` opcode additions. *(Errata: in `ByteX86Base.lean`, `0x64` (`FS:`), `0x65` (`GS:`), and `0x67` (`addr32`) were accepted as ignored prefixes by `stepPrefix` rather than rejected with `.fault .unsupported`, so `%fs:0x28` canary loads and `%fs:` SFI stores decoded as flat 64-bit accesses instead of failing closed; `x86-64-fs-gs-segment-sfi-escape-addr32-opsize-decoding-and-pass2-prefix-fuzzing` models `fsBase`/`gsBase`, `0x67`, and `0x66` explicitly and rejects them in `checkSfiPicMultiFnV2`.)*
  - `PrivateStackSep` (`collapseOneInstr`) rejects functions that pass `&local`
    to an external callee or store an `rsp`-derived pointer into memory/GPRs
    (exposed stack frames); exposed frames require explicit Kripke region or
    separation-logic frame ownership rather than syntactic non-leakage.
  - Stock uninstrumented `gcc -O2` binaries do not satisfy `checkSfiObject`
    directly because standard codegen uses `[rsp + disp]`, arbitrary pointer
    dereferences, and unbundled jumps; Mode 2 requires compiling the C archive
    with an SFI/LFI-instrumented compiler backend (such as `lfi-clang` targeting
    `%r14` + bundle alignment) plus a verified ~15-instruction host-to-sandbox
    entry/exit trampoline.
- **Unknown:**
  - Exact microarchitectural `IMUL`/`MUL`/`BSF` undefined-flag circuits vary across
    AMD Zen 3/4/5 and older Intel families; because `ByteX86Base.lean` universally
    quantifies over all `nd : Nat → UndefFlags`, its proofs remain sound across
    all x86-64 CPUs conforming to the Intel/AMD manuals, whereas whether any CPU
    violates SDM *defined* flags (such as errata on exotic instructions) was not
    resolved beyond the 48-specimen Ice Lake-SP probe.
  - Whether Lean 4's kernel reducer (`whnf` / `reduce_nat`) could add a native
    byte-array literal (`ByteArray`) primitive to avoid `ByteCodeTree` sharding
    altogether without enlarging Lean's C++ TCB remains an open upstream Lean
    design question.
- **Not examined:**
  - Concurrency, weak memory (`TSO` store-buffer litmus tests for `LOCK`
    instructions), OS signal delivery inside sandboxed execution, self-modifying
    code / JIT `W^X` transitions, and Spectre-PHT/BTB speculative-execution
    leakage across the `%r14` SFI boundary (which requires LFENCE or index
    masking under speculative threat models) were not examined.
  - Do not extrapolate `checkSfiObject_preserves_rust_host_safety` to claim
    absence of *logical bugs* or *termination* inside the sandboxed C library:
    Mode 2 proves **partial-correctness containment** (no out-of-arena writes, no
    host register clobbers, no faults, no control-flow escape for all `steps : Nat`),
    not functional correctness of the C library's output bytes or liveness.

## Evidence

### Primary upstream sources and normative specifications

- **Intel 64 and IA-32 Architectures Software Developer's Manual** (`325462-087US`,
  2025): Vol. 2A §2.1.1 (15-byte instruction-length limit `#GP(0)`), §2.2.1 (REX
  prefix placement immediately preceding opcode/escape), §2.3.5 (VEX prefix
  `#UD` when preceded by `0x66`, `0xF2`, `0xF3`, `REX`, or `0xF0`), §2.1.2
  (`LOCK` `#UD` on non-memory or non-lockable opcodes), Vol. 2A `BSF`/`IMUL` and
  Vol. 2B `SAL`/`SAR`/`SHL`/`SHR`/`TZCNT`/`XOR` (`RFLAGS` Affected tables).
- **System V Application Binary Interface — AMD64 Architecture Processor
  Supplement** (`1.0`): §3.2.1–3.2.2 (callee-saved registers `%rbx`, `%rbp`,
  `%rsp`, `%r12`–`%r15`; 16-byte entry alignment `(rsp + 8) % 16 == 0`) and
  §4.4.1 Table 4.9 (`R_X86_64_PC32` relocation calculation `S + A - P`).
- **Anneal** (`joshlf/anneal`, commit `c131b320eeeb26ef692e5afd5ec8db49ee518613`):
  `trusted/audit/src/main.rs` and `trusted/audit/Lean/TrustedBoundary.lean`
  (`trustLevel := 0, plugins := #[], loadExts := false, level := .private`,
  `base.toKernelEnv.replay`, `-DElab.async=false`, `-Ddebug.skipKernelTC=false`).
- **Lean 4** (`leanprover/lean4`, commit `5045d0056413266e57c625dcd7c365b10e377c52`,
  `v4.34.1`): kernel `Nat.ble` / `reduce_nat` GMP primitives, `Lean.Replay`, and
  `Init.Data.BitVec.Basic`.
- **Comparative upstream implementations:** `xoreaxeaxeax/sandsifter`
  (`8375e6123d093629e3e4437d7903839fd0742c2a`, `injector.c` NX page-boundary
  length trap), `lfi-project/lfi-verifier`
  (`8c3c47983572039b138f8fa15c12231f2655bbef`), `intelxed/xed`
  (`0bcb6237345c5066726dcc08b3d87928df3b5b26`), `awslabs/s2n-bignum`
  (`280a220986a0bc6249248187717a771153d073db`), and `acl2/acl2`
  (`f040a8db474f68e11b5fa980c99b7c1f7be28e54`, `books/projects/x86isa/`).

### Preserved package support material (`observed_at: 2026-11-21`)

All mechanized Lean `v4.34.1` modules, silicon/compiler probes, benchmark
generators, and raw JSON measurements are preserved under `support/`:

| Package path | Bytes | SHA-256 digest | Role |
| --- | ---: | --- | --- |
| `support/ByteX86Base.lean` | `118,520` | `24744585dbcf08b319c8cc0ee45c54c190f6009480359fab3a87d5e5a535146a` | `Init.*`-only (`0` `sorry`, `0` `partial`, `0` `opaque`, `0` `set_option`) variable-length (`1..15`B) x86-64 byte decoder (`decodeX64`, `decodeX64_prefix_invariant`), `ByteCodeTree` + demonic `RFLAGS` machine (`runX64`), dynamic `and rsp, -32` `PrivateStackSep` (`realigned_frame_envelope_separation`), and certified `DeadFlagCollapse` (`compileByteLeaf`, `checkByteLeaf_sound`). |
| `support/ByteX86Sfi.lean` | `59,770` | `d398dfeb999bbad8587b085ccbd1044b0f7cd275d80732072fec3804a632fdf2` | `Init.*`-only decidable 32-byte bundle & `ByteCodeTree` SFI verifier (`checkSfiObject`, `checkSfiSubtree_node`), negative control `guest_stack_callee_save_unsound_under_sfi`, 3-phase invariant `SfiPhase`, and `checkSfiObject_preserves_rust_host_safety`. |
| `support/sandsifter_page_oracle.py` | `23,261` | `10183adb3aee77d39c270887651d7d2babb9698b3a2194bf86ec31d57c901142` | Live Linux x86-64 `mmap` `PROT_EXEC` + `PROT_NONE` page-boundary silicon trap oracle cross-checking hardware against `ByteX86.decodeX64`, `llvm-mc 21.1.8`, and `objdump 2.47`. |
| `support/sandsifter_page_oracle_results.json` | `58,347` | `987426029bd938906bced9c102974064720853187dc7a673b0a8110e7a6a3342` | Recorded silicon trap numbers, boundary lengths, post-state registers/flags, Lean decode outcomes, and disassembler outputs across all `48` specimens. |
| `support/gcc_object_and_flag_liveness_probe.py` | `16,850` | `c8787ab128dc0433d2a78260baf24084c12afb3e40c9e47c4393a7972077a38d` | Compiles `5` `gcc 15.2.0` `-O2` / `-O3 -mavx2` C workloads to `.o`, extracts `.text` and `.rela.*`, and computes exact backward CFG liveness for `{CF, PF, AF, ZF, SF, OF}`. |
| `support/gcc_object_and_flag_liveness_results.json` | `36,290` | `f0f28dad5c2a932d8d3fdf96fd3332988463e88419479461733b8b4352f6933b` | Per-workload and aggregate `.text` hex bytes, relocations, instruction lengths, and dead-flag / demonic-undef / `PF` death percentages. |
| `support/bench_byte_x86_lifting_and_sfi.py` | `87,169` | `0143cad1a36f7dacb3a806888a0f300a4303f7309e603ef8949f5b07376f254d` | End-to-end Lean `v4.34.1` benchmark and standalone `(level := .private)` `toKernelEnv.replay` harness (`--canary` and full `5`-suite sweep, running in `tempfile.TemporaryDirectory()`). |
| `support/byte_x86_scaling_and_sfi_results.json` | `17,917` | `1baa28d0f26fb4cfefe5322e1e0647c96d8c681e99390fd12f01af950aec4b9e` | Complete compile wall/CPU, RSS, `.olean` bytes, and standalone `(level := .private)` kernel replay measurements across Foundation + Suites 1–5 (`31` replayed modules). |

## Revalidation

To revalidate the core claims on a new Linux x86-64 CPU, a newer `gcc` / `llvm-mc` /
`binutils` release, or a newer Lean 4 toolchain without repeating full scaling
sweeps, run the following three narrow probes from a clean temporary copy of
`support/`:

1. **Silicon vs. Lean `decodeX64` vs. disassembler oracle (~`12 s`):**
   ```console
   python3 -B support/sandsifter_page_oracle.py
   ```
   Verifies `48 / 48` agreement between live CPU page-boundary traps and
   `ByteX86.decodeX64`, checks whether newer `llvm-mc` or `objdump` still
   false-accept the `11` `#GP(0)`/`#UD` encodings, and re-tests whether `IMUL` on
   `0 * 7` leaves `ZF != 1` on the target microarchitecture.
2. **Compiler `.o` encoding & backward `RFLAGS` liveness check (~`2 s`):**
   ```console
   python3 -B support/gcc_object_and_flag_liveness_probe.py
   ```
   Recompiles the `5` C workloads with the active `gcc`, verifies `.rela.rodata`
   `R_X86_64_PC32` addends and instruction-length distributions, and checks
   whether dead-flag (`~98%`) and demonic-undefined-flag (`100%`) death rates
   shift under new optimizer passes.
3. **End-to-end Lean 4 kernel + `(level := .private)` replay canary (~`90 s`):**
   ```console
   python3 -B support/bench_byte_x86_lifting_and_sfi.py --canary
   ```
   Compiles `ByteX86Base.lean` and `ByteX86Sfi.lean` from scratch with
   `-DElab.async=false -Ddebug.skipKernelTC=false -j1 -M2048` (`0` `set_option`),
   checks real `gcc` `.o` lifting (`GccRealObjectProofs`), the demonic/WHNF cliff
   vs. `CollapsedLeaf64`, `NaiveAlias` vs. `PrivateStackSep`, `ByteShardedTreeLift`
   (`N = 64, 512`), and `checkSfiObject` (`N = 256, 1024`), and runs standalone
   `(level := .private)` `toKernelEnv.replay` across all `12` canary modules
   verifying `CANARY_ALL_PASSED` with zero `sorryAx` or `_inhabitedExprDummy`.
   Omit `--canary` (~`25–35 min` sequential single-core) only when re-measuring
   full `N = 5,120` lifting and `N = 10,240` SFI curves.
