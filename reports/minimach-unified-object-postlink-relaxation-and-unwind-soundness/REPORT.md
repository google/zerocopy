# Unified `MiniMach` Object Encoding, AST-Free ELF64 Post-Link Relaxation Validation, `%r11` Stack-Probe CFA, and `.eh_frame_hdr` Binary-Search Soundness

## Summary

A verified drop-in replacement for `rustc` cannot stop its machine-code proof at pre-link `.o` instruction emission. On `x86_64-unknown-linux-gnu`, the linker (`rust-lld` at `rust-lang/llvm-project@08c84e69a84d95936296dfcab0e38b34100725d5` / `llvm/llvm-project@392dfff97d29b59d77e5cac6d4b6ef2585fe7117`, or `GNU ld 2.47`) mutates instruction opcodes, ModRM bytes, prefix lengths, and internal instruction boundaries *in place* during ELF64 PIE/static-PIE linking, appends `0xCC` (`int3`) or multi-byte `NOP` inter-function alignment padding, and relocates `.eh_frame` / `.eh_frame_hdr` unwind tables across segments (`--rosegment`). Any post-link binary validator that merely masks 4-byte relocation displacement holes (`naiveDispOnlyValidator`) falsely rejects real `rustc` PIE binaries on every relaxed TLS access, every relaxed `REX_GOTPCRELX` load, and every `0xCC`-padded function tail—while any validator that peeks at the compiler's internal `MiniMach` AST (`validateLinkedOp`) collapses into a tautological `x == x` check and cannot audit an untrusted linker.

This report presents **`VrustcFormal.F1_4`** (`support/MiniMachUnifiedObjectPostLink.lean`, `3,919` lines, `210,113` bytes, SHA-256 `c3547f2d62315598a5b07d626e3c7d141fd6b2b7ebc73c8e5c0e6b109f8ef782`), a 5-stage **Statement-First** Lean 4 formalization grounded in:
1. An exhaustive `30`-`.rlib` (`350,943`-relocation) `rustc 1.102.0-nightly` (`rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) `x86_64-unknown-linux-gnu` sysroot relocation census (`support/e3_1_postlink_reloc_summary.json`),
2. Differential post-link probes across `rustc 1.98.0-nightly` (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `rust-lld 22.1.6`, and `GNU ld 2.47` (`../rustc-elf64-postlink-relocation-tls-relaxation-and-ehframe-ground-truth/REPORT.md`), and
3. Coupled backend unwind/stack-probe measurements (`../coupled-backend-seam-verification-subregisters-vzeroupper-probestack-and-cfi/REPORT.md`, Table E1).

### Headline Verified Results

1. **Cryptographically Frozen Statement-First Contract (`[real measurement]` + `[kernel-checked proof]`):**
   - Prior to proof construction, an independent blind adversarial statement review (`7` blocking findings `B1`–`B7`, all fixed before freeze) caught and eliminated unary `-4` syntax rejected by Anneal's `TrustedBoundary.lean` (`B1`), tautological AST-peeking post-link validation (`B2`), missing negative signed 32-bit PC-relative displacements `[-2^31, 0)` (`B3`), conflated regular GOT vs. `GOTTPOFF` slots (`B4`), monolithic TLS blob decoding (`B5`), linear scan mislabeled as `.eh_frame_hdr` binary search and clamped `%r11` probes (`B6`), and `TLSLD` `48 8b 80` `mov` vs. `48 8d 80` `lea` opcode coverage (`B7`).
   - Stripping `section Stage4ProofHelpers` (`138` strictly `private` declarations: `2 private def`, `136 private theorem`) and replacing the `4` target theorem proof bodies with `  sorry` reconstructs the frozen Stage 3 contract (`67,357` bytes, `1,398` lines, SHA-256 `34005ada17594000626966089727c2f58c0cda9273ed9aa9c34092e34620708e`) **byte-for-byte**. `Basis: execution + source`

2. **Mechanically AST-Free Byte-Level Post-Link Validator Soundness, Completeness, & `GOTPCREL` Tamper Rejection (`[kernel-checked proof]`):**
   - `validateLinkedBytes` scans `(objBytes, relocs, linkedBytes)` in lockstep with structural fuel. Kernel dependency-closure inspection across both `env.constants.map₁` and `env.checked.get` (`524` visited constants) confirms **`0` references** to `MiniMachOp`, `encodeOneOp`, `encodeOpsLoop`, `encodeFn`, `linkOneOpBytes`, `linkOpsLoop`, `linkFn`, `Gpr`, `WriteMode`, `MachState`, `X86Insn`, `decodeInsn`, or `execByteStream`.
   - **Theorem 1 (`codecs_and_multifn_relaxation_preserve_byte_span`):** Proves `decodeLe16 (le16Bytes w16) = some w16`, `decodeLe32 (le32Bytes w32) = some w32`, and exact multi-op code-span invariance `(linkFn env vaddr relax padBytes ops).length = (encodeFn fnSym ops).code.length + padBytes` for both `relax = true` and `relax = false`—proving zero intra-function PC drift across `TLSGD` (`8B+8B -> 9B+7B` = `16B`), `TLSLD` (`7B+5B+7B -> 12B+7B` = `19B`), `GOTTPOFF` (`7B -> 7B`), and `REX_GOTPCRELX` (`7B -> 7B`).
   - **Theorem 2 (`postlink_validator_sound_complete_and_tamper_rejecting`):** Proves (a) completeness on `linkFn` under `OpsValidForRelaxMode`, (b) **AST-free operational soundness** for *arbitrary* raw candidate byte streams `linkedBytes` accepted against `encodeFn fnSym ops` under `LinkEnvConsistent` and full signed `[-2^31, 2^31)` `OpsPcRelReachable` (including backward displacements and `vaddr >= 2^32`), stepping single-instruction `execByteStream` across shifted `+9` (`TLSGD`) and `+12` (`TLSLD`) instruction boundaries and all `3` x86-64 `WriteMode`s (`full64`, `zeroExt32`, `lo16PreserveUpper48`), and (c) universal rejection (`= false`) of `48 8b 05 -> 48 8d 05` tampering on legacy non-relaxable `R_X86_64_GOTPCREL`.
   - **Theorem 4 (`naive_disp_only_rejects_all_relaxations_and_int3_padding`):** Proves universally (`forall env vaddr fnSym s padBytes`, `1 <= padBytes`) that `validateLinkedBytes = true` while `naiveDispOnlyValidator = false` across all `4` relaxation families (`TLSGD`, `TLSLD` `mov`, `GOTTPOFF`, `REX_GOTPCRELX`) and trailing `0xCC` padding. `Basis: execution (Lean kernel) + derived`

3. **Two-Phase `%r11` Fixed-Stride Probe Loop CFA & Relocated `.eh_frame_hdr` Binary Search (`[kernel-checked proof]`):**
   - **Theorem 3 (`r11_two_phase_probe_and_eh_frame_bsearch_sound`):** Proves that for every frame `(rsp0, savedCfaOff, numPages, tailBytes)` satisfying `8 <= savedCfaOff`, `savedCfaOff - 8 <= 4096`, `tailBytes < 4096`, and `(savedCfaOff - 8) + numPages * 4096 + tailBytes <= rsp0`, the zero-clamping `4096`-byte `%r11` probe loop preserves `evalCfa = rsp0 + 8` (`r11 + (savedCfaOff + numPages * 4096)`) and `maxUnprobedGap <= 4096` at every iteration `k`, exits at `rsp = r11 = lastProbedRsp` for `k >= numPages`, and preserves both invariants across Phase 4 `finishR11ProbeTail` (`rsp + (savedCfaOff + numPages * 4096 + tailBytes)`). Simultaneously proves `bsearchEhFrame pc tbl = lookupEhFrame pc tbl` for every `EhTableSorted lo tbl`, hit completeness, converse soundness, `0xCC`-gap rejection, and post-link `relocateEhTable baseAddr tbl` invariance. `Basis: execution (Lean kernel) + derived`

4. **Three-Kernel + Unmodified Anneal `TrustedBoundary.lean` Pass 1 `"audit"` Verification (`[real measurement]`):**
   - **Lean `v4.34.1`** (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`): `rc = 0` (`24.115 s`, `0` errors, `0` warnings, `0` `sorry`, `895` module constants, `0` `Classical.choice`/`sorryAx`/`ofReduceBool`/`_unsafe_rec`).
   - **Unmodified Anneal `TrustedBoundary.lean`** (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`): `"preflight"` positive `rc = 0` (`ok = true`; negative frozen `sorry` rejected fail-closed `rc = 1`); **full Pass 1 `"audit"`** (`requireMirWp = true`) **`rc = 0`, `ok = true`, `replay = true`, `replayedDeclarations = 2,476`** (standalone `F1_4` Pass 1 `"audit"`: `rc = 0`, `replay = true`, `replayedDeclarations = 895`, `axioms = ["propext", "Quot.sound"]`).
   - **Independent `Lean v4.35.0` (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) + `lean4export 3.1.0` (`5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe`) + Rust `nanoda_bin 0.4.19` (`ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`):** **`Checked 1164 declarations with no typechecker errors` in `0.776 s` and `48.80 MB` peak RSS** (`rc = 0`; two-sided negative sensitivity probes with `permitted_axioms = ["propext"]` and `[]` both rejected fail-closed with `rc = 1`). `Basis: execution`

---

## Applicability

### Subject Relationships and Configuration Scope

- `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly`) and `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`) supply the `30`-`.rlib` `x86_64-unknown-linux-gnu` sysroot relocation vocabularies (`350,943` and `320,016` ELF64 relocations across the identical `10`-type set) and live post-link PIE disassemblies.
- `rust-lang/llvm-project@08c84e69a84d95936296dfcab0e38b34100725d5` (`rust-lld`, LLD 22.1.6) and `llvm/llvm-project@392dfff97d29b59d77e5cac6d4b6ef2585fe7117` (`lld/ELF/Arch/X86_64.cpp`, LLVM 23.1.5) define the post-link relocation/relaxation templates (`R_X86_64_REX_GOTPCRELX`, `TLSGD -> LE`, `TLSLD -> LE`, `GOTTPOFF -> LE`, strict non-relaxation of legacy `R_X86_64_GOTPCREL`, and `0xCC` inter-function padding) formalized in `VrustcFormal.F1_4`.
- `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/audit/TrustedBoundary.lean` and `trusted/lean/foundation-lock.json`) defines the closed `SourceRole.theory` syntax allowlist, `51`-module `Init.*` foundation lock, and `trustLevel := 0` `Kernel.Environment.replay` gate satisfied by `support/MiniMachUnifiedObjectPostLink.lean`.
- `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`), `leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`), `leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` (`3.1.0`), and `ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` (`nanoda_bin 0.4.19`) are the three independent kernel typecheckers and proof exporter executed against the frozen statement and proof.

### Generalization Envelope

- All `4` core theorems (`T1`–`T4`) hold universally across every `MiniMach` function (`List MiniMachOp`), `LinkEnv`, `vaddr`, `padBytes`, `ProbeState` frame parameters, and `EhTableSorted` table within the modeled `x86-64` ELF64 Static-PIE/PIE subset.
- Linker policy claims (`0x8B` preservation on `R_X86_64_GOTPCREL` and `0xCC` inter-function padding) are specific to `rust-lld` (`lld/ELF/Arch/X86_64.cpp`); `GNU ld 2.47` relaxes `R_X86_64_GOTPCREL` data loads `48 8b -> 48 8d` and emits multi-byte `NOP` padding (see **Boundaries**).

---

## Findings

### 1. `30`-`.rlib` (`350,943`-Relocation) `rustc` Sysroot Relocation Census

`Basis: execution + source (support/e3_1_postlink_reloc_summary.json, rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1)`

Scanning every object member across all `30` `x86_64-unknown-linux-gnu` sysroot `.rlib` archives (`350,943` ELF64 relocations total) establishes that `rustc` emits **exact 10 distinct ELF64 relocation types** (`Elf64RelocKind`):

| ELF64 Relocation Kind | Count (`1.102.0-nightly`) | Share | Post-Link Behavior in `rust-lld` PIE | Modeled in `F1-4` |
|---|---:|---:|---|---|
| `R_X86_64_PC32` | `151,103` | `43.06%` | Patches signed 32-bit `S + A - P` hole (`lea disp(%rip)` / `.eh_frame`) | `leaRipSym` (`tmplLeaRip`, `7 B`) |
| `R_X86_64_32` | `113,289` | `32.28%` | Debuginfo / non-`.text` 32-bit section offsets | `Elf64RelocKind.r_32` (rejected in `.text`) |
| `R_X86_64_PLT32` | `66,530` | `18.96%` | Patches `call rel32` (`E8 disp32`) / `jmp rel32` or pairs with `TLSGD`/`TLSLD` | `callSym` (`5 B`) + `TLSGD`/`TLSLD` multi-reloc |
| `R_X86_64_GOTPCREL` | `17,227` | `4.91%` | **Never opcode-relaxed in `rust-lld`** (`48 8b 05` GOT load kept; *relaxed by `GNU ld`*) | `loadGotStrict` + Theorem 2(3) tamper rejection |
| `R_X86_64_64` | `2,315` | `0.66%` | Data/vtable `.data.rel.ro` 64-bit pointers | `Elf64RelocKind.r_64` (rejected in `.text`) |
| `R_X86_64_GOTTPOFF` | `198` | `0.056%` | **Opcode-relaxed (`IE -> LE`)**: `48 8b 05 disp -> 48 c7 c0 tpoff32` | `tlsGotTpOff` (`7 B -> 7 B`, relaxed & unrelaxed) |
| `R_X86_64_TLSGD` | `178` | `0.051%` | **Boundary-shifted (`GD -> LE`)**: `8 B + 8 B -> 9 B + 7 B` (`16 B`) | `tlsGdAddr` (`tmplTlsGdObj`, `+9` fetch shift) |
| `R_X86_64_REX_GOTPCRELX` | `84` | `0.024%` | **Opcode-relaxed**: `48 8b 05 got -> 48 8d 05 sym` *(all `84` from C `libprofiler_builtins`)* | `loadGotRelaxable` (`7 B -> 7 B`, `mov` or `lea`) |
| `R_X86_64_TLSLD` | `15` | `0.004%` | **Boundary-shifted (`LD -> LE`)**: `7 B + 5 B + 7 B -> 12 B + 7 B` (`19 B`) | `tlsLdAddr` (`0x8D`) & `tlsLdLoad` (`0x8B`) |
| `R_X86_64_DTPOFF32` | `4` (`+11` paired) | `0.001%` | Paired with `TLSLD` (`48 8d 80` `lea` or live `48 8b 80` `mov` -> `tpoff32`) | Matched in 3-reloc `matchRelocAtOff` |

*(Note: `Elf64RelocKind` also includes `r_tpoff32` for direct Local-Exec `R_X86_64_TPOFF32` completeness.)*

### 2. In-Place Opcode & Instruction-Boundary Shifts (`rust-lld` vs. `GNU ld 2.47`)

`Basis: execution + source (llvm/llvm-project@392dfff97d29b59d77e5cac6d4b6ef2585fe7117, lld/ELF/Arch/X86_64.cpp)`

1. **`TLSGD -> Local-Exec` (`16 B` preserved, internal boundary shifts `+8 -> +9`):**
   - Pre-link `.o` (`tmplTlsGdObj`): `[66 48 8d 3d 00 00 00 00]` (`8 B`, `R_X86_64_TLSGD` at `+4`) followed by `[66 66 48 e8 00 00 00 00]` (`8 B`, `R_X86_64_PLT32 __tls_get_addr - 4` at `+12`).
   - Post-link PIE: `[64 48 8b 04 25 00 00 00 00]` (`9 B`: `mov %fs:0x0, %rax`) followed by `[48 8d 80 <tpoff32>]` (`7 B`: `lea disp32(%rax), %rax`). Total function span stays `16 B`, but instruction #2 now starts at `+9` instead of `+8`.
2. **`TLSLD + DTPOFF32 -> Local-Exec` (`19 B` preserved, internal boundaries `7 + 5 + 7 -> 12 + 7`):**
   - Pre-link `.o` (`tmplTlsLdObj opByte`): `[48 8d 3d 00 00 00 00]` (`7 B`, `R_X86_64_TLSLD` at `+3`) + `[e8 00 00 00 00]` (`5 B`, `R_X86_64_PLT32` at `+8`) + `[48 <0x8D|0x8B> 80 00 00 00 00]` (`7 B`, `R_X86_64_DTPOFF32` at `+15`). Notice real `rustc` folds field loads into the `DTPOFF32` user instruction (`48 8b 80` `mov`, not only `48 8d 80` `lea`).
   - Post-link PIE: `[66 66 66 64 48 8b 04 25 00 00 00 00]` (`12 B`: triple-`0x66`-prefixed `mov %fs:0x0, %rax`) + `[48 <0x8D|0x8B> 80 <tpoff32>]` (`7 B`). Three pre-link instructions collapse into two post-link instructions with the split at `+12`.
3. **Critical Linker Provenance & Policy Difference (`rust-lld` vs. `GNU ld 2.47`):**
   - Stock pure-Rust `rustc` crates emit `0` `R_X86_64_REX_GOTPCRELX` (`relax_elf_relocations = false`, `RtLibUseGOT = 1`) and `17,227` legacy `R_X86_64_GOTPCREL`. `rust-lld` (`X86_64::adjustGotPcExpr`) **never relaxes** legacy `R_X86_64_GOTPCREL` and pads inter-function alignment gaps with `0xCC` (`int3`), whereas `GNU ld 2.47` relaxes `R_X86_64_GOTPCREL` `48 8b -> 48 8d` and pads with multi-byte `NOP`s. *(Note: in the initial `E3-1` probe JSON, host `$PATH` reported `GNU ld 2.47`, but `rustc 1.102.0-nightly` actually invoked its bundled `rust-lld`, as confirmed by `--rosegment` `.eh_frame_hdr < .text`, `0xCC` padding, and unrelaxed `48 8b 05` `GOTPCREL` in `unwinding_caller`.)* `VrustcFormal.F1_4` formalizes `rust-lld`'s strict PIE validation policy.

### 3. Pre-Freeze Adversarial Review (`7` Blocking Bugs Caught Before Freeze) and `VrustcFormal.F1_4` Theorem Inventory

`Basis: source + execution (support/MiniMachUnifiedObjectPostLink.lean, L1–L3919; [kernel-checked proof])`

Before freezing `F1_4_MiniMach_UnifiedObject_PostLink_Stmt.frozen.lean` (`SHA-256: 34005ada17594000626966089727c2f58c0cda9273ed9aa9c34092e34620708e`), an independent blind review audited the 702-line initial statement draft and caught **7 blocking defects (`B1`–`B7`)**, every one of which was repaired and re-verified (`0` new blockers) prior to cryptographic freeze:

| ID | Pre-Freeze Defect | Resolution in Frozen `VrustcFormal.F1_4` (`1,398` LOC) |
|---|---|---|
| `B1` | Unary `-4` (`«term-_»`) in `encodeOneOp` rejected by `TrustedBoundary.lean` `"preflight"` | Replaced all negative `Int` literals with `Int.negSucc 3` (`0` disallowed syntax kinds) |
| `B2` | `validateLinkedOp` peeked at `MiniMachOp` AST (`x == x` tautology) with `0` soundness proof | Replaced with AST-free `validateLinkedBytes` (`0/524` AST/encoder/linker/decoder refs) + Theorem 2 soundness |
| `B3` | Forward-only `vaddr + 7 <= target` excluded backward PC-rel (`lea -0xd9(%rip)`) & dead-coded negative `sext32To64` | Defined full signed `[-2^31, 2^31)` `PcRel32Reachable`, proved `pcRel32_add_exact` (`vaddr >= 2^32` & `-2^31` included), added `W3` |
| `B4` | Conflated `gotSlotAddr` made unrelaxed `GOTTPOFF` false; unrelaxed `TLSLD` used `tpoff` instead of `dtpoff` | Split `gotSlotAddr` vs. `gotTpOffSlotAddr` in `LinkEnv`/`LinkEnvConsistent`; gated PIE TLS via `OpsValidForRelaxMode` |
| `B5` | Dead `WriteMode`, non-x86 encodings, monolithic TLS blob decode, no multi-op `encodeFn`/`linkFn` or `0xCC` | Real x86-64 encodings (`48 C7`, `B8+r`, `66 B8+r`, `REX 89`), single-instruction `decodeInsn` across `+9`/`+12`, `mkInt3Pad` |
| `B6` | Linear `lookupEhFrame` mislabeled as binary search; clamped 1-phase `%r11` probe omitted `push` & `tailBytes` | Genuine `O(log n)` `bsearchEhFrame` + `relocateEhTable` + 4-phase fixed-stride `4096 B` `%r11` loop (`Crucible 3` Table E1) |
| `B7` | Omitted `TLSLD` `48 8b 80` (`mov`) and `R_X86_64_{32,TPOFF32}` | Added `.tlsLdLoad` (`48 8b 80`) alongside `.tlsLdAddr` (`48 8d 80`), `.r_32`, `.r_tpoff32`, and exact `E3-1` byte witnesses `W1`–`W3` |

| Declaration (`VrustcFormal.F1_4.*`) | Kind | Statement Summary | Axioms | Reachable Decls |
|---|---|---|---|---:|
| `codecs_and_multifn_relaxation_preserve_byte_span` | Core Theorem 1 | `le16`/`le32` roundtrips + `linkFn` byte-span invariance (`relax = true` & `false`) across arbitrary `List MiniMachOp` + `padBytes` | `[propext]` | `672` |
| `postlink_validator_sound_complete_and_tamper_rejecting` | Core Theorem 2 | (1) `validateLinkedBytes` completeness on `linkFn`; (2) AST-free `execByteStream = some (execMiniMachFn ...)` soundness across signed `[-2^31, 2^31)` PC-rel, `+9`/`+12` TLS shifts, & 3 `WriteMode`s; (3) `R_X86_64_GOTPCREL` `mov -> lea` tamper rejection | `[propext, Quot.sound]` | `976` |
| `r11_two_phase_probe_and_eh_frame_bsearch_sound` | Core Theorem 3 | Two-phase `%r11` fixed-stride `4096 B` loop + tail `evalCfa = rsp0 + 8` & `maxUnprobedGap <= 4096`; `bsearchEhFrame = lookupEhFrame`, hit/converse/gap soundness, & `relocateEhTable` invariance | `[propext]` | `533` |
| `naive_disp_only_rejects_all_relaxations_and_int3_padding` | Core Theorem 4 | Universal (`forall env vaddr fnSym s padBytes`) proof that `validateLinkedBytes = true` while `naiveDispOnlyValidator = false` on `TLSGD`, `TLSLD` (`mov`), `GOTTPOFF`, `REX_GOTPCRELX`, and `0xCC` padding | `[propext, Quot.sound]` | `982` |
| `witness_e31_tlsgd_shifted_boundary_and_naive_rejection` | Witness `W1` | Live `E3-1` `TLSGD -> LE` (`64 48 8b 04 25 ... 48 8d 80 a8 ff ff ff` at `0x14701`) executes across `+9` shift to `0x7ffff7fbffa8` | `[propext]` | `689` |
| `witness_e31_tlsld_mov_and_gottpoff_exact_bytes` | Witness `W2` | Live `E3-1` `TLSLD` `mov` (`66 66 66 64 ... 48 8b 80 a8 ff ff ff`) loads `0xCAFEBABE12345678` across `+12` shift + `GOTTPOFF` `48 c7 c0 a8 ff ff ff` | `[propext]` | `689` |
| `witness_e31_neg_pcrel_tamper_rejection_and_writemode` | Witness `W3` | Backward `lea -0xd9(%rip)` (`27 ff ff ff` at `0x14932 -> 0x14860`), `GOTPCREL` tamper rejection, & `zeroExt32` + `lo16PreserveUpper48` (`0x000000001234ABCD`) + `3`x`0xCC` | `[propext]` | `683` |
| `witness_crucible3_exact_r11_probe_and_bsearch` | Witness `W4` | Exact `Crucible 3` Table E1 (`savedCfaOff = 16, numPages = 9, tailBytes = 32`: `r11 + 36880 -> rsp + 36912 = 0x100008`, `maxUnprobedGap = 4096`) + relocated `bsearchEhFrame` hit/gap | **`[]` (`0` axioms)** | `252` |

### 4. Multi-Kernel & Unmodified Anneal `TrustedBoundary.lean` Verification Receipts

`Basis: execution (support/stage5_verification_summary.json)`

| Verification Gate | Toolchain / Revision | Command / Mode | Exit | Wall (s) | Peak RSS (MB) | Verified Result |
|---|---|---|---:|---:|---:|---|
| 1. Primary Kernel | `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` | **`0`** | `24.115` | `2,117.93` | `0` errors, `0` warnings, `895` module consts (`643` pub + `252` priv), `bad = 0` |
| 2a. `TrustedBoundary` Preflight (pos) | `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `TrustedBoundary.lean` `"preflight"` (`SourceRole.theory`) | **`0`** | `5.319` | `854.10` | `ok = true`, `51/51` `foundation-lock.json` modules matched |
| 2b. `TrustedBoundary` Preflight (neg) | `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `TrustedBoundary.lean` `"preflight"` on frozen `sorry` contract | **`1`** | `4.112` | `848.20` | Fail-closed: `policy:unsupported syntax kind Lean.Parser.Tactic.tacticSorry` |
| 2c. `TrustedBoundary` Pass 1 `"audit"` | `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | Full repo (`requireMirWp = true`) & standalone (`requireMirWp = false`) fresh `Kernel.Environment.replay` | **`0`** | `17.188` / `16.067` | `2,609.92` / `2,601.26` | `ok = true`, **`replay = true`**, `replayedDeclarations = 2,476` (`895` standalone), `axioms = ["propext", "Quot.sound"]` |
| 3. Cross-Version Kernel | `leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`) | `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` | **`0`** | `22.118` | `2,097.40` | `6,779,200 B` `.olean`, `0` errors, `0` warnings |
| 4. Proof Exporter | `leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` (`3.1.0`) | Export all `8` public theorems of `VrustcFormal.F1_4` | **`0`** | `0.812` | `459.08` | `8,944,361 B` NDJSON (`179,821` lines, `1,164` declarations) |
| 5a. External Rust Kernel (pos) | `ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` (`0.4.19`) | `permitted_axioms: ["propext", "Quot.sound"]`, `unpermitted_axiom_hard_error: true` | **`0`** | **`0.776`** | **`48.80`** | **`Checked 1164 declarations with no typechecker errors`** |
| 5b. External Rust Kernel (neg) | `ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` (`0.4.19`) | Sensitivity probes: `permitted_axioms: ["propext"]` and `[]` | **`1`** / **`1`** | `0.038` / `0.009` | `6.20` / `3.87` | Fail-closed: rejects unpermitted `"Quot.sound"` and `"propext"` |

---

## Boundaries

### Honest Scope & Non-Claims (`VrustcFormal.F1_4`)

**What `VrustcFormal.F1_4` proves (`[kernel-checked proof]`):** Over a standalone, locked-`Init.*`-only Lean 4 formalization grounded in the `E3-1` `30`-`.rlib` (`350,943`-relocation) `rustc` sysroot census, the `GNU ld 2.47` vs. `rust-lld 22.1.6` post-link ELF64 probe, and `Crucible 3` Table E1—using **only `[propext]` and `[Quot.sound]`** (`0` axioms on `W4`, `[propext]`-only on `T1`, `T3`, and `W1`–`W3`; `0` `Classical.choice`, `0` `sorry`, `0` `omega`/`bv_decide`/`native_decide`, `0` `unsafe`/`partial`/`_unsafe_rec`; independently kernel-checked by Lean `v4.34.1` + unmodified Anneal `TrustedBoundary.lean` Pass 1 replay, Lean `v4.35.0`, and the Rust external typechecker `nanoda_bin 0.4.19` over `1,164` exported declarations)—`F1-4` mechanizes:
1. **Little-endian codec roundtrips & multi-op post-link byte-span invariance** (`codecs_and_multifn_relaxation_preserve_byte_span`): exact `16`-bit and `32`-bit little-endian roundtrips (`decodeLe16`/`le16Bytes`, `decodeLe32`/`le32Bytes`) and exact function code-span preservation `(linkFn env vaddr relax padBytes ops).length = (encodeFn fnSym ops).code.length + padBytes` across arbitrary `List MiniMachOp` functions under both `relax = true` and `false` (zero intra-function PC drift across `TLSGD` `8B+8B -> 9B+7B`, `TLSLD` `7B+5B+7B -> 12B+7B`, `GOTTPOFF`, and `REX_GOTPCRELX`).
2. **Non-tautological AST-free byte-level post-link validator completeness, soundness, and `GOTPCREL` tamper rejection** (`postlink_validator_sound_complete_and_tamper_rejecting`): `validateLinkedBytes` (mechanically verified across all `524` reachable constants in `env.constants.map₁` and `env.checked.get` to contain **`0` references** to `MiniMachOp`, `encode*`, `link*`, `decode*`, or `exec*`) accepts `linkFn` under `OpsValidForRelaxMode`, rejects `48 8b 05 -> 48 8d 05` tampering on legacy `R_X86_64_GOTPCREL`, and guarantees for **any** candidate byte stream `linkedBytes` accepted against `encodeFn fnSym ops` (under `LinkEnvConsistent` and full signed `[-2^31, 2^31)` `OpsPcRelReachable`, including backward displacements and `vaddr >= 2^32`) that single-instruction decoding/execution `execByteStream` across shifted `+9`/`+12` TLS boundaries and all `3` `WriteMode`s (`full64`, `zeroExt32`, `lo16PreserveUpper48`) returns `some (execMiniMachFn env ops st)`.
3. **Two-phase `%r11` fixed-stride stack-probe CFA & relocated `.eh_frame_hdr` binary search** (`r11_two_phase_probe_and_eh_frame_bsearch_sound`): across all valid `(rsp0, savedCfaOff, numPages, tailBytes)` (`savedCfaOff - 8 <= 4096`, `tailBytes < 4096`), zero-clamping `4096`-byte `runFixedStrideR11Loop` and `finishR11ProbeTail` preserve `evalCfa = rsp0 + 8` and `maxUnprobedGap <= 4096` and exit at `rsp = r11 = lastProbedRsp` for `k >= numPages`; across all strictly sorted `EhTableSorted lo tbl`, `bsearchEhFrame` equals linear `lookupEhFrame` with hit completeness, converse soundness, gap rejection, and `relocateEhTable` invariance.
4. **Universal sharpness & live empirical witnesses** (`naive_disp_only_rejects_all_relaxations_and_int3_padding` + `W1`–`W4`): proves universally that `naiveDispOnlyValidator` falsely rejects while `validateLinkedBytes` accepts `TLSGD -> LE`, `TLSLD (mov) -> LE`, `GOTTPOFF -> LE`, `REX_GOTPCRELX (mov -> lea)`, and trailing `0xCC` padding (`padBytes >= 1`), and checks verbatim `E3-1` post-link byte sequences (`W1`–`W3`) and `Crucible 3` Table E1 (`W4`).

### Eight Blind-Audited Over-Reading Boundaries

`Basis: source + derived + execution (line-by-line audit of support/MiniMachUnifiedObjectPostLink.lean against live rust-lld 22.1.6 and GNU ld 2.47 probes)`

1. **`rust-lld` PIE policy vs. `GNU ld 2.47` `GOTPCREL`/`NOP` divergence, `-Wl,--no-relax`, and ASLR GOT precondition:** `validateLinkedBytes` enforces `rust-lld`'s (`X86_64::adjustGotPcExpr`) strict non-relaxation of legacy `R_X86_64_GOTPCREL` (`0x8B` required) and `rust-lld`'s `0xCC` (`int3`) inter-function padding; it **rejects** `GNU ld 2.47` PIE outputs that relax `R_X86_64_GOTPCREL` `48 8b -> 48 8d` or emit multi-byte `NOP` inter-function padding *(note: `E3-1`'s binaries were linked via `rustc`'s bundled `rust-lld` despite host `$PATH` reporting `GNU ld 2.47`)*. `linkFn` / `OpsValidForRelaxMode` couple GOT and TLS relaxation under one boolean `relax`, whereas real `-Wl,--no-relax` suppresses GOT relaxation without suppressing PIE `TLSGD`/`TLSLD`/`GOTTPOFF -> LE`. Theorem 2(2) assumes `LinkEnvConsistent` (post-relocation GOT contents), so it does not discharge the freestanding `#![no_std] -nostdlib -static-pie` ASLR `SIGSEGV` hazard when `rust-lld` leaves `R_X86_64_GOTPCREL` unrelaxed without a `_DYNAMIC` self-relocator.
2. **Straight-line `12`-op x `8`-GPR `MiniMach` subset (`%rax`-only relocations, abstract `callSym`/`ret`):** Covers `8` GPRs (`rax, rcx, rdx, rdi, rsi, rsp, rbp, r11`) and `12` straight-line ops; omits intra-function branches/CFG, `push`/`pop`, ALU/general memory ops, `lo8`/`hi8` (`AL`/`AH`), `XMM`/`YMM` SIMD (`vzeroupper`), non-`%rax` GOT/RIP/TLS destinations (`48 8d 3d` `%rdi`, `48 8b 1d` `%rbx`), `GOTTPOFF` `add` forms (`48 03 05 -> 48 8d 80`, `4c 03 25 -> 49 81 c4`), indirect `call *got` (`ff 15 -> 67 e8`), and direct `R_X86_64_TPOFF32`. `callSym` and `ret` are modeled as state no-ops (`st -> st`), `OpsPcRelReachable` does not bound `callSym` within `[-2^31, 2^31)`, and `execByteStream` does not halt at `ret` before `0xCC`/EOF.
3. **Trusted `encodeFn` pre-link `.o` inputs vs. untrusted external `.o` files:** Theorem 2(2) quantifies over `obj := encodeFn fnSym ops` objects (which fix `r.addend = -4` / `0`, `r2.sym = 0`, and `REX.X = 0`); validating arbitrary untrusted external `.o` files additionally requires checking `r.addend`, `__tls_get_addr` symbol identity, `REX.X`, and unreachable post-`ret` `0xCC` placement.
4. **Disconnected `ProbeState` / pre-decoded `EhFrameEntry` tables & `--rosegment` `sdata4` polarity:** `ProbeState` and `EhFrameEntry` (`Nat` `[startPc, endPc)` intervals shifted by `+ baseAddr`, indexed via `List` `listGet?`) are standalone models not mechanically connected to `MiniMachOp` byte decoding, binary `.eh_frame_hdr` `[0x01, 0x1b, 0x03, 0x3b]` signed `sdata4` (`init_loc_rel = entry_pc - hdrVA`) two-stage FDE range lookup, or post-epilogue `.cfi_remember_state`/`.cfi_restore_state`.
5. **Static-PIE Local-Exec TLS scope only:** Dynamic `cdylib` (`-shared`) `DTPMOD64`/`DTPOFF32`/`__tls_get_addr` caller-saved clobber semantics, `TLSDESC`, AArch64 `ADRP`/`ADD` veneers, Windows PE/COFF, and Mach-O compact unwind are out of scope.
6. **Theorem 4 sharpness scope:** Covers `4` of `5` relaxable `MiniMachOp` constructors (`tlsGdAddr`, `tlsLdLoad`, `tlsGotTpOff`, `loadGotRelaxable`) plus `[.ret]` with `padBytes >= 1` `0xCC` bytes (omitting a separate conjunct for `.tlsLdAddr`, whose completeness and soundness are proved in Theorem 2).
7. **Standalone `Init.*` namespace:** Not yet mechanically bridged via AST/state translation to `joshlf/anneal` `Trusted.*`, `VrustcFormal.F1_3`, or `Crucible 3`'s `Reg256` SIMD lane model.
8. **`noncomputable` specifications & `-M2048` module-splitting note:** All `59` public `def`s are `noncomputable` specifications (requiring an executable mirror + equivalence proof for native validator execution), and monolithic `3,919`-line elaboration/replay (`2.12`–`2.61 GB` RSS) should be split into two `< 2,048 MiB` submodules if staged under `anneal-audit`'s `-M2048` single-process CLI flag.

---

## Evidence

### Preserved Package Artifacts

- `support/MiniMachUnifiedObjectPostLink.lean` — Complete zero-`sorry` Lean 4 formalization (`3,919` lines, `210,113` bytes, SHA-256 `c3547f2d62315598a5b07d626e3c7d141fd6b2b7ebc73c8e5c0e6b109f8ef782`).
- `support/MiniMachUnifiedObjectPostLink.frozen.sha256` — Cryptographic SHA-256 digests of the Stage 3 frozen statement (`34005ada...0708e`) and Stage 4 proof (`c3547f2d...ef782`).
- `support/e3_1_postlink_reloc_summary.json` — `30`-`.rlib` (`350,943`-relocation) `rustc` sysroot relocation census and post-link disassembly measurements.
- `support/stage5_verification_summary.json` — Machine-readable receipts across Lean `v4.34.1`, unmodified Anneal `TrustedBoundary.lean` Pass 1 `"audit"` (`replay = true`), Lean `v4.35.0`, `lean4export 3.1.0`, `nanoda_bin 0.4.19` (`1,164` declarations), and AST-free `validateLinkedBytes` dependency-closure verification.

---

## Revalidation

All verification gates run self-contained in a fresh temporary directory (`BUILD_DIR="$(mktemp -d)"`):

1. **Digest & Byte-Exact Frozen Contract Reconstruction (~0.1 s):**
   ```bash
   sha256sum support/MiniMachUnifiedObjectPostLink.lean
   # Expected: c3547f2d62315598a5b07d626e3c7d141fd6b2b7ebc73c8e5c0e6b109f8ef782
   ```
   Confirm that stripping `L1149–L3532` (`section Stage4ProofHelpers`) and replacing the `4` Part VII theorem proof bodies with `  sorry` yields `67,357` bytes with SHA-256 `34005ada17594000626966089727c2f58c0cda9273ed9aa9c34092e34620708e`.

2. **Synchronous Lean `v4.34.1` Build & Axiom Check (~25 s):**
   ```bash
   LEAN434="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
   "$LEAN434" -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     -R support -o "$BUILD_DIR/MiniMachUnifiedObjectPostLink.olean" \
     support/MiniMachUnifiedObjectPostLink.lean
   ```
   Confirm `rc = 0`, `0` errors/warnings, and `#print axioms` returning `[propext]` / `[propext, Quot.sound]` / `[]` across all `8` public theorems (`0` `Classical.choice`/`sorryAx`).

3. **Unmodified Anneal `TrustedBoundary.lean` Preflight & Pass 1 Replay (~23 s):**
   Against `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, run `trusted/audit/TrustedBoundary.lean` `"preflight"` (`rc = 0`, `ok = true`; frozen `sorry` negative control `rc = 1`) and Pass 1 `"audit"` (`rc = 0`, `ok = true`, `replay = true`, `replayedDeclarations = 2,476` full / `895` standalone).

4. **Independent Cross-Version & Rust External Kernel Check (~24 s):**
   Compile unmodified `support/MiniMachUnifiedObjectPostLink.lean` with `leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`), export all `8` public theorems via `leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` (`3.1.0`), and verify with `ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` (`nanoda_bin 0.4.19`, `permitted_axioms = ["propext", "Quot.sound"]`): confirm `Checked 1164 declarations with no typechecker errors` (`rc = 0`) and confirm `permitted_axioms = ["propext"]` and `[]` both fail closed (`rc = 1`).
