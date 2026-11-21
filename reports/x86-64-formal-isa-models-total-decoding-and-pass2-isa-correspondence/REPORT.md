# x86-64 Formal ISA Models, Total Kernel-Sound Machine-Code Decoding, and Two-Model Pass-2 ISA Correspondence in Lean 4

## Summary

Formalizing an x86-64 machine-code verification boundary in Lean 4 under a
zero-custom-axiom, zero-`partial`, zero-`opaque` trust discipline requires
solving three coupled architectural problems: selecting and cross-checking a
reference ISA model $I_{\text{ref}}$, decoding variable-length x86-64 machine
bytes totally inside the kernel without ambiguity, and generalizing two-model
Pass-2 correspondence (`M_anneal` vs. `vendor/lean-miri`) to multi-ISA
nondeterministic hardware semantics ($I_{\text{ref}} \subseteq I_{\text{anneal}}$):

1. **Ground-Truth x86-64 Formal ISA Landscape (`Basis: source`):**
   No single upstream repository combines broad scalar + atomic + system + SIMD
   x86-64 semantics with a total Lean 4 kernel representation and an active
   machine-code decoder:
   - **`AeneasVerif/kraken@019a72cb`** (MIT; `nightly-2026-09-21`, experimental
     `module` imports) models **73** x86-64 instruction constructors (`47`
     scalar `Operation`, `26` `AvxOperation`) in `Kraken/X64/` (`21` files,
     `6,924` LOC), with `0` `axiom`s and `0` `opaque`s (`1` `partial def`
     `Executable.eval` in `Semantics.lean:1101`, `4` `sorry`s in `Elab.lean`/examples,
     `5` `bv_decide` in `Examples.lean`), but has **zero machine-code byte
     decoder** (assembly text syntax/elaborator only), **zero `LOCK`/atomic
     instructions**, **zero system registers**, and **zero CET (`endbr64`)**.
   - **`acl2/acl2@f040a8db`** (`books/projects/x86isa`, BSD-3-Clause, `91,363`
     LOC across `106` `.lisp` files, `211` `def-inst` definitions) is the most
     complete executable x86-64/i686 specification covering scalar, `LOCK`
     atomics (`xchg`, `cmpxchg`, `cmpxchg8b/16b`, `xadd`), `RFLAGS` with
     explicit undefined-flag non-determinism (`undef-flg`), full Ring 0–3
     paging/MSRs/descriptors/`SYSCALL`, and `endbranch.lisp` (`ENDBR32`/`ENDBR64`
     modeled as NOPs without CET tracker state), with a Sail snapshot in
     `rems-project/sail-x86-from-acl2@0c6c023d` (`63` `model/*.sail` files,
     last updated 2024-11-29).
   - **`awslabs/s2n-bignum@280a2209`** (`Apache-2.0 OR ISC OR MIT-0`, HOL Light)
     provides **163** x86-64 instruction constructors (`instruction.ml`, `692`
     LOC), a verified prefix-linear total byte decoder (`decode.ml`, `4,052`
     LOC, proving `list_linear_decode` and `x86_decode_unique` in `x86.ml:2854`),
     explicit `UNDEFINED_VALUES[...]` relational flag nondeterminism (`44` sites
     in `x86.ml`), `ENDBR64` (as NOP), and `ZMM0..31` + `EVEX` masking, but
     rejects `LOCK` (`0xF0 -> NONE`), `FS`/`GS`, and `0x67` address-size
     override and omits `CMPXCHG`, `XADD`, fences, and system registers. Its
     Lean 4 port **`cslib-community/bignum@1b3952cb`** (Apache-2.0) currently
     contains **zero x86-64 modules** (`Bignum/Arm/` only on `main` and `orig`),
     and **`leanprover/LNSym@49f8a1d9`** (Apache-2.0) is likewise **strictly
     AArch64-only** (zero x86 files, branches, or issues) and carries `22`
     `bv_decide` proofs in `Arm/` (`16` in `Arm/Insts/Common.lean`) whose
     generated `._native.bv_decide.ax_*` axioms fail strict zero-axiom audits.
   - **`kframework/X86-64-semantics@592380ae`** (UIUC/NCSA, unmaintained since
     2020-03-04) covers `3,155` user-mode Haswell instruction variants (`cmpxchg`,
     `xadd`, `xchg`, `SSE`–`AVX2`) via assembly-text rules rather than a byte
     decoder, omits `LOCK`, fences, `SYSCALL`, `CPUID`, `ENDBR64`, and `AVX-512`,
     and exhibits documented disassembly-ambiguity and synthesis bugs (PR `#4`,
     PR `#7`, issue `#14`).
   - **`NationalSecurityAgency/ghidra@3fb3eec6`** SLEIGH (`39,255` LOC across
     `27` `.slaspec`/`.sinc` files, `1,477` distinct constructor mnemonics,
     Apache-2.0) encodes `125` `lockable.sinc` forms and `cet.sinc`, but relies
     on **`1,716` distinct opaque `define pcodeop` userops** (including `LOCK`
     and `ShadowStack*`, explicitly noting CET shadow-stack semantics are
     unimplemented) and lacks APX/`REX2`. **`intelxed/xed@0bcb6237`**
     (Apache-2.0, `1,995` distinct `ICLASS`es, `9,149` `ICLASS` blocks, `62`
     `LOCKABLE` tags, covering CET, AVX-512, AMX, AVX10, and APX/`REX2`) is
     the authoritative open-licensed decode/legality specification, with zero
     arithmetic semantics. **`rems-project/sail-tiny-x86@229bd844`**
     (BSD-2-Clause, `19` AST constructors including `LOCK`/`CMPXCHG`/`XCHG`/fences)
     targets Rocq only; **`HOL-Theorem-Prover/HOL@aee6a90d`** `x64` (`26` scalar
     + `24` SSE constructors, `BadFlagAccess` on `NONE` flags) and
     **`digama0/mm0@0d414c0b`** (`examples/x86.mm0`, `1,727` LOC, CC0-1.0,
     proving decoder determinism in `x86_determ.mm1`) are small scalar cores.

2. **Total Kernel-Sound x86-64 Decoding (`Basis: normative + source + execution`):**
   - Empirical probing of real `gcc 15.2.0 -O2 -fcf-protection=full -mavx2` `.o`
     code (`support/x86_64_encoding_multiplicity_probe.py`) confirms that
     compilers routinely emit non-canonical and multi-form encodings—including
     11-byte repeated-prefix alignment NOPs (`66 66 2e 0f 1f 84 00 00 00 00 00`),
     mandatory SIB `[rsp-0x8]`, `disp8`/`disp32`, `F3 0F 1E FA` (`endbr64`),
     `F0` `lock cmpxchg`/`lock add`, `F3 48 0F BC` (`tzcnt`, aliased to `bsf`
     pre-BMI1), and mixed VEX2 (`C5`) / VEX3 (`C4`). Cross-checking `34`
     controlled cases across `llvm-mc 21.1.8` and GNU `objdump 2.47` exposes
     three real-world disassembler hazards: (a) **both** `llvm-mc` and `objdump`
     silently accept architecturally `#UD` `LOCK` forms (`f0 48 01 f0` register
     dst; `f0 48 8b 07` non-lockable `mov`); (b) **neither** enforces the
     15-byte `#GP(0)` instruction-length limit (`llvm-mc` accepts 16 bytes as
     `nop`; `objdump` splits at 14 bytes); and (c) `llvm-mc 21.1.8` rejects
     `0f 1e fa` (Intel hintable NOP, decoded as `nop edx` by `objdump`) and
     resynchronizes on byte `0xfa` to emit **`cli`**.
   - Mechanization in Lean `v4.34.1` (`support/X86DecodingAndPass2CorrespondenceProbe.lean`,
     `1,210` lines, `Init.*`-only, `0` `partial`, `0` `sorry`, `0` custom axioms)
     establishes that a **canonical-only** witness encoder (`encode ins = bytes`)
     is strictly incomplete on compiler `.o` bytes
     (`canonical_encoder_misses_alternate_encodings`), whereas a
     **hint-parameterized witness encoder** (`encodeWithHint ins hint = some bs`)
     achieves soundness **only** when paired with a kernel-checked functionality /
     unambiguity theorem (`encodeWithHint_sound_wrt_decodeDirect`,
     `encodeWithHint_unambiguous`). Omitting even one side condition—such as
     `REX.B = 0` on `0x90`—allows the exact byte sequence `[0x41, 0x90]` to
     witness both `nop` and `xchg r8d, eax`
     (`buggy_witness_checker_ambiguous_on_41_90`). Consequently, Architecture
     (b) does not eliminate decoder legality logic from proof obligations; a
     **direct total fuel-bounded structural decoder** (`decodeDirect`) using
     flat opcode dispatch (or paired with untrusted decode hints proved sound
     against `decodeDirect`) is strictly safer and cleaner for `Trusted.*`.

3. **Two-Model Pass-2 ISA Correspondence (`Basis: source + execution + derived`):**
   Generalizing `joshlf/anneal@c131b320`'s Pass-2 `CorrespondenceAtChoicesClaim`
   (`docs/mir-correspondence-design.md:2057-2180`) from MIR to multi-ISA
   (`x86_64`, `aarch64`, `riscv64`) requires three architectural adjustments,
   all kernel-checked in `support/X86DecodingAndPass2CorrespondenceProbe.lean`:
   - **Per-opcode staged support gate (`pass2_isa_correspondence_and_post_transfer`):**
     An `Init.*`-only Pass-1 $I_{\text{anneal}}$ covering 50–150 opcodes fails
     closed to `.fault .unsupported` outside `SupportedOp`; proving per-opcode
     one-way refinement only on `SupportedOp` lifts universally to
     `WellFormed_anneal → WellFormed_ref`, `Behavior_ref ⊆ Behavior_anneal`,
     `Diverges_ref → Diverges_anneal`, and sound `SatisfiesPost` transfer while
     allowing Pass-2 CI proofs to be sliced into per-extension modules that
     avoid monolithic `-M2048` OOMs (`LeanRV64D.Defs` at `2.47 GiB` RSS,
     `sail-arm` at `182k` LOC).
   - **One-way refinement $I_{\text{ref}} \subseteq I_{\text{anneal}}$ over
     architectural nondeterminism (`symmetric_vta_iff_false`,
     `narrow_anneal_proves_false_hardware_property`):** Because hardware
     specifications allow nondeterministic outcomes (x86 undefined flags on
     `bsf`/`bsr`/`shl`/`mul`, RVV `vta`/`vma` agnostic bits, `LR`/`SC` spurious
     failures, quiet-NaN payload propagation) while some extracted references
     hardcode concrete choices (e.g., `opencompl/sail-riscv-lean@51c635c4`
     hardcoding RVV `AGNOSTIC` to undisturbed), symmetric `↔` equivalence fails
     against narrow references, whereas copying a narrow reference into
     $I_{\text{anneal}}$ proves false properties violated by silicon.
     $I_{\text{anneal}}$ must therefore carry the **normative wide** demonic
     choice set so that both $I_{\text{ref}} \subseteq I_{\text{anneal}}$ and
     $I_{\text{hw}} \subseteq I_{\text{anneal}}$.
   - **Poison-fault vs. demonic-bit-choice (`poison_breaks_reverse_fault_equiv`):**
     Modeling undefined x86 flags as poison (`Option Bool = none`, faulting on
     read) preserves `WellFormed_anneal → WellFormed_ref` and `SatisfiesPost`
     transfer, but breaks bidirectional `FaultEquivalenceClaim`
     (`AnnealFault ↔ RefFault`) against bit-choice references such as
     `s2n-bignum` or ACL2 `x86isa`.

---

## Applicability

This report governs formal ISA reference selection, total Lean 4 machine-code
decoding, and Pass-2 CI ISA correspondence across `x86_64`, `aarch64`, and
`riscv64` under strict zero-custom-axiom, zero-`partial`, zero-`opaque` Lean 4
trust boundaries.

Relationship among examined subjects (`REPORT.json`):
- **Candidate x86-64 formal ISA specifications and decoders:**
  `AeneasVerif/kraken@019a72cb`, `acl2/acl2@f040a8db` (`books/projects/x86isa`),
  `kframework/X86-64-semantics@592380ae`, `awslabs/s2n-bignum@280a2209`,
  `cslib-community/bignum@1b3952cb`, `rems-project/sail-x86-from-acl2@0c6c023d`,
  `rems-project/sail-tiny-x86@229bd844`, `coruus/L3@d6558e67`,
  `HOL-Theorem-Prover/HOL@aee6a90d` (`examples/l3-machine-code/x64/`),
  `BinaryAnalysisPlatform/bap@034bbd09`,
  `NationalSecurityAgency/ghidra@3fb3eec6` (`Ghidra/Processors/x86/data/languages/`),
  `intelxed/xed@0bcb6237`, and `digama0/mm0@0d414c0b` (`examples/x86.mm0`,
  `examples/x86_determ.mm1`) are directly audited and compared.
- **Cross-ISA AArch64 and RISC-V reference models:**
  `leanprover/LNSym@49f8a1d9`, `rems-project/sail-arm@5416ef6b`,
  `UQ-PAC/aslp@92e4fd94`, `riscv/sail-riscv@71dc9c25`,
  `opencompl/sail-riscv-lean@51c635c4`, and `Verified-zkEVM/riscv-zkvm@b878729f`
  are audited for comparison in the unified multi-ISA decision matrix and for
  nondeterminism/CFI/replay compatibility.
- **Pass-2 correspondence baseline and execution toolchains:**
  `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` defines the Pass-1 /
  Pass-2 correspondence architecture generalized here; `leanprover/lean4`
  `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) kernel-checks
  `support/X86DecodingAndPass2CorrespondenceProbe.lean` with
  `-DElab.async=false -Ddebug.skipKernelTC=false`; `gcc 15.2.0` (`Debian 15.2.0-14`),
  `llvm-mc 21.1.8`, and GNU `objdump 2.47` on `x86_64` Linux supply the
  empirical machine-code encoding and disassembly measurements in
  `support/x86_64_encoding_multiplicity_probe.py`.

This report builds on—and intentionally does not duplicate—companion corpus
packages covering adjacent layers:
- `anneal-lean-miri-pass2-audit-and-sail-riscv-reference-audit-requirements`
  (Pass-2 `UPSTREAM_PIN.json` mechanics, `bwrap` sandboxing, and `LeanRV64D.Defs`
  `-M2048` OOM measurements);
- `x86-64-and-aarch64-simd-isa-formalizations-sail-asl-acl2-hol-k-comparison`
  (media codec SIMD instruction-by-instruction coverage and cross-ISA lane
  hazards);
- `asl-l3-lnsym-and-isa-verification-frameworks-lean-adaptation` (`ASLv0`/`ASLv1`,
  `L3` export internals, `LNSym` `mayModifiedRegs` bugs, and `Islaris` trace
  adequacy);
- `unreachable-stub-isolation-opaque-axioms-and-scoped-isa-correspondence-proofs`
  (kernel `opaqueDecl` mechanics and parameterized stub bundles);
- `verified-builtin-inline-asm-template-parser-and-direct-encoder` (Rust `asm!`
  template substitution and `InlineAsmOptions` checking);
- `kraken-aarch64-x86-64-instruction-validation-and-rust-assembly-pilots` and
  `kraken-wp-foundation-parser-theorem-closure-and-certificate-checking`
  (`Kraken` `Program.wp` and `loadAvx` `.W64` under-checking).

Where primary-source inspection at newer commits corrects earlier corpus
observations—specifically `AeneasVerif/kraken` licensing (`MIT`),
`cslib-community/bignum`'s absence of x86 modules, `LNSym/Arm`'s `bv_decide`
axiom footprint, and `ACL2 x86isa`'s 2026 `endbranch.lisp` addition—those
differences are noted explicitly below.

---

## Findings

### 1. Ground-Truth Audit of x86-64 Formal ISA Specifications and Cross-ISA Decision Matrix

`Basis: source + documentation`

Direct repository inspection at pinned 2026-11-20 revisions establishes the exact
instruction coverage, decoder design, trust-boundary construct census, license,
and maintenance posture of every serious x86-64 formal ISA model:

#### 1.1 Per-Repository x86-64 Ground-Truth Findings

1. **`AeneasVerif/kraken@019a72cb0f494d26cdceefb2fd40aad19f704ed9` (MIT; `lean-toolchain: nightly-2026-09-21`):**
   - **Coverage (`Kraken/X64/Syntax.lean`, `370` LOC; `Kraken/X64/`, `21` files / `6,924` LOC):**
     Declares **47** scalar `Operation` constructors (`mov`, `movsx`, `movzx`,
     `push`, `pop`, `setcc`, `cmovcc`, `movs`, `stos`, `lea`, `add`, `adc`,
     `adcx`, `adox`, `inc`, `dec`, `neg`, `sub`, `sbb`, `cmp`, `mul`, `mulx`,
     `imul1`, `imul`, `test`, `and`, `not`, `or`, `xor`, `shl`, `shr`, `sar`,
     `shld`, `shrd`, `rol`, `ror`, `rcl`, `rcr`, `bswap`, `cld`, `std`, `jcc`,
     `jmp`, `call`, `ret`, `nop`, `nopalign`) and **26** `AvxOperation`
     constructors (SSE/AVX moves, `addps`/`subps`, `paddd`, `pshufb`, `pshufd`,
     `palignr`, `pblendw`, `vzeroupper`, `sha256rnds2`/`sha256msg1`/`sha256msg2`,
     and 6 unmasked AVX-512 integer ops `vmovdqu32`, `vmovdqa32`, `vpaddd`,
     `vprord`, `vpsrld`, `vpternlogd` — total **73** x86-64 constructors).
     Omits **all `LOCK`/atomic instructions** (`xchg`, `cmpxchg`, `xadd`,
     `mfence`/`lfence`/`sfence`), bit-scan/BMI (`bsf`/`bsr`/`tzcnt`/`lzcnt`),
     all system registers/instructions (`syscall`, `cpuid`, `rdtsc`, `cr*`), and
     all CET (`endbr64`).
   - **Decoder & Trust Census:** Contains **zero machine-code byte decoder**;
     `Kraken/X64/Parser/` parses AT&T/Intel assembly text via `TermElabM`
     elaboration into ASTs (with an unverified `Layout`). Across `Kraken/X64/`,
     static scanning finds `0` `axiom`, `0` `opaque`, `0` `@[extern]`, `0`
     `native_decide`, `3` `partial def` (`Semantics.lean:1101` `Executable.eval`,
     `SemanticsTests.lean`, `Parser/Delab.lean`), `4` `sorry` (`Parser/Elab.lean`,
     `Examples/Examples.lean` ×2, `Examples/IncrementDMA.lean`), `5` `bv_decide`
     (all in `Examples/Examples.lean`), and `2` `unsafe` (in `Parser/Elab.lean`).
     Uses Lean's experimental `module` / `public import` / `meta import` system
     targeting `nightly-2026-09-21`, requiring syntax adaptation for Lean `v4.34.1`.
     Note also that `LICENSE` is **MIT** (`Copyright (c) 2026 AeneasVerif`),
     not Apache-2.0.

2. **`acl2/acl2@f040a8db474f68e11b5fa980c99b7c1f7be28e54` (`books/projects/x86isa`, BSD-3-Clause; active, pushed 2026-11-20):**
   - **Coverage (`91,363` LOC across `38` `machine/*.lisp` + `68` `machine/instructions/**/*.lisp` files; `211` `def-inst` forms):**
     Uniquely spans **64-bit long mode and 32-bit compatibility/IA-32 mode**,
     full scalar ALU/control/string/bit ops, `x87`/MMX/`EMMS`, SSE–SSE4.1 +
     partial AVX + `EVEX`/`ZMM0..31` dispatch, **full `LOCK` prefix legality and
     atomics** (`exchange.lisp`: `x86-xchg`, `x86-cmpxchg`, `x86-cmpxchg8b/16b`;
     `arith-and-logic.lisp` / `bit.lisp` lockable operations; `dispatch-macros.lisp`
     lock enforcement), **`RFLAGS` with explicit undefined-flag nondeterminism**
     (`rflags-spec.lisp`, `866` LOC; `undef-flg` via `other-non-det.lisp`), full
     Ring 0–3 system architecture (`paging.lisp`, `segmentation.lisp`,
     `interrupt-servicing.lisp`, `msrs.lisp`, `cpuid.lisp`, `syscall.lisp`), and
     2026-added `instructions/endbranch.lisp` (`x86-endbr32/endbr64`, decoding
     `F3 0F 1E FA`/`FB` with 15-byte `#GP(0)` length checking but explicitly
     documenting at lines 61–65 that CET tracker semantics are not yet modeled:
     `For now we model ENDBR32 and ENDBR64 as no-ops`).
   - **Decoder Architecture:** Direct byte-level fetch-and-decode in
     `get-prefixes.lisp` (`cnt : (integer 0 15)`, tracking `LOCK` independently
     of `REP`/`REPNE` and nullifying any `REX` byte followed by a legacy prefix,
     lines 207–239 and 387–510), `prefix-modrm-sib-decoding.lisp` (`2,524` LOC),
     and multi-map opcode dispatch (`one-byte`, `two-byte`, `three-byte`, `vex`,
     `evex`).
   - **Sail Bridge (`rems-project/sail-x86-from-acl2@0c6c023d`, BSD-2-Clause translator / BSD-3-Clause model; last commit 2024-11-29):**
     Exports `63` `model/*.sail` files from an older ACL2 `x86isa` snapshot
     (pre-dating 2026 `endbranch.lisp`). Translating it to Lean 4 via
     `sail -lean` inherits Sail's monadic overhead, `noncomputable` sections, and
     significant Sail-to-Lean refactoring cost.

3. **`awslabs/s2n-bignum@280a220986a0bc6249248187717a771153d073db` (`Apache-2.0 OR ISC OR MIT-0`, HOL Light; active, pushed 2026-11-19) and `cslib-community/bignum@1b3952cba6438a6a03da02ff207deb6c93e7d4eb` (Apache-2.0, Lean 4):**
   - **Coverage (`x86/proofs/instruction.ml`, `692` LOC; `x86/proofs/x86.ml`, `6,632` LOC):**
     Declares **163** `instruction` constructors covering scalar ALU/control/bit
     (`ADD`, `ADC`, `ADCX`, `ADOX`, `MUL2`, `MULX4`, `BSF`, `BSR`, `TZCNT`,
     `LZCNT`, `POPCNT`, `BT`/`BTC`/`BTR`/`BTS`, `SHLD`/`SHRD`, `XCHG`, `ENDBR64`
     modeled as identity `x86_ENDBR64 s = \s'. s = s'` at `x86.ml:1011-1012`),
     AES-NI / `PCLMULQDQ`, SSE2/SSSE3/AVX2 integer SIMD (`PSHUFB`/`VPSHUFB`,
     `VPMADDUBSW`, `VPMADDWD`, `VPACKUSWB`, `VZEROUPPER`), and `ZMM0..31` +
     `EVEX` opmasking (`evex_mask`, `x86.ml:2612`). Omits **`LOCK` atomics**
     (`CMPXCHG`, `XADD`, and `0xF0` prefix), memory fences, floating-point SIMD /
     `MXCSR`, and system registers (`SYSCALL`, `CPUID`, `CR*`, `MSR`).
   - **Decoder Architecture (`x86/proofs/decode.ml`, `4,052` LOC; `x86.ml:2833-2871`):**
     Implements a **total structural recursive decoder** `decode : byte list -> (instruction # byte list) option`
     (`decode.ml:1505-1508`), allowing arbitrary repeated `0x66` alignment
     prefixes (`pfxs_set_opo`, lines 41–46) and segment overrides for multi-byte
     NOPs (`NOP_N`, lines 480–489), while failing closed (`NONE`) on `0xF0`
     (`LOCK`), `0x64`/`0x65` (`FS`/`GS`), and `0x67` (address-size override,
     lines 90–93). Crucially, `decode.ml` proves **`list_linear_decode`**
     (line 3400: decoding consumes a prefix independently of trailing bytes),
     from which `x86.ml:2854-2871` proves **`x86_decode_unique`**:
     `x86_decode s pc x ==> x86_decode s pc y ==> x = y`.
   - **Undefined Flags:** Uses relational nondeterminism `UNDEFINED_VALUES[...]`
     at `44` sites in `x86.ml` (e.g., `x86_BSF` at lines 890–896 sets `destx`
     undefined on `0` and `UNDEFINED_VALUES[CF;OF;SF;PF;AF]`; `x86_SHL` at lines
     1678–1691 leaves `OF` undefined for count `> 1` and `CF` undefined when
     `dimindex(:N) <= c`; `x86_MUL2` at lines 1226–1236 leaves `ZF;SF;PF;AF`
     undefined).
   - **Lean 4 Port Status (`cslib-community/bignum@1b3952cb`):** Direct tree
     inspection of `main` and all other branches (`orig`, `gflima`, `fix-build`)
     confirms **`cslib-community/bignum` currently contains 0 x86-64 files**
     (`41` `.lean` files exclusively covering `Bignum/Arm/` on `v4.36.0-rc1`).

4. **`kframework/X86-64-semantics@592380aea04820ea11cfa5475b343f0257f2474e` (UIUC/NCSA; unmaintained since 2020-03-04):**
   - **Coverage (`3,063` instruction `.k` files across `registerInstructions` `1,147`, `memoryInstructions` `1,474`, `immediateInstructions` `320`, `systemInstructions` `122` — note `systemInstructions` holds control-flow/branch/call/ret ops like `callq_*` and `jcc_*`, NOT Ring-0 system ops):**
     Covers `3,155` Haswell 64-bit user-mode variants synthesized from Intel SDM
     and Strata, including `cmpxchg*` (`21` files), `xadd*` (`12` files),
     `xchg*` (`44` files), `bsf`/`bsr` (`12` files, explicitly setting
     `undefMInt`), and rich `SSE`–`AVX2`/`FMA`/`BMI`/`AES-NI` media SIMD.
     Omits **all `LOCK` prefix rules (`0` files)**, `mfence`/`lfence`/`sfence`
     (`0`), `syscall`/`cpuid`/`rdtsc` (`0`), `endbr64` (`0`), `i686`, and
     `AVX-512`. Operates on assembly text (`x86-syntax.k`), with no machine-code
     byte decoder.
   - **Known Soundness/Maintenance Issues:** Repository has been stagnant for
     over 6 years (broken on modern K compilers, issues `#10`, `#11`, `#13`);
     open PR `#4` documents ambiguous assembly mnemonics (`VCVTPD2DQ` 128- vs
     256-bit memory operands); closed PR `#7` patched semantic defects across 30
     FP/blend/cmov instruction rules (`vcvtps2ph`, `vextractf128`, `blendvp*`,
     `cmovnsw`, `cvts*2si`); issue `#14` notes implicit register-overwrite order
     reliance on `MULX` when both destination operands alias; and stratified
     vector rules expand into huge unrolled `#ifMInt` trees (`512` nested
     branches in `vpshufb_ymm_ymm_ymm.k:12`). Suitable only as a differential
     test cross-check for Haswell user-mode ALU/SIMD, not as a Pass-2 Lean 4
     $I_{\text{ref}}$.

5. **`rems-project/sail-tiny-x86@229bd8448937042baa51b0a2d14bc437929b0dce` (BSD-2-Clause; active, pushed 2026-10-06):**
   - Minimal Sail model (`17` files) declaring **19** AST constructors in
     `decode.sail` (`MOV`, `XOR`, `SFENCE`, `LFENCE`, `MFENCE`, `CMP`,
     `CMPXCHG`, `XCHG`, `PUSH`, `POP`, `ADD`, `SUB`, `IMUL`, `CALL`, `LEAVE`,
     `RET`, `JMP`, `JNS`, `JNE`) with explicit `bool` `lock` flags on `XOR`,
     `ADD`, `SUB`, and `CMPXCHG` and Sail concurrency interface hooks
     (`interface.sail`). Its `Makefile` currently targets Rocq (`snapshot/Tiny_x86.v`)
     and C only (no Lean 4 target yet), and its instruction set is too small for
     a general $I_{\text{ref}}$, though its clean byte decoder (`decode.sail`) is
     a useful Sail-concurrency reference.

6. **`coruus/L3@d6558e67` & `HOL-Theorem-Prover/HOL@aee6a90d` (`examples/l3-machine-code/x64/`, BSD-3-Clause):**
   - `L3` `x64.spec` (`1,357` LOC, unmaintained since 2015-05-13) and its HOL4
     export `x64Script.sml` (`11,473` LOC, actively kept compiling in HOL4)
     define **26** scalar `instruction` constructors (including `Zcmpxchg`,
     `Zxadd`, `Zxchg`, `Zbinop`, `Zbit_test`, `Zdiv`/`Zidiv`, `Zmul`/`Zimul*`,
     `Zmov`/`Zmovsx`/`Zmovzx`) plus **24** `SSE` FP/shift constructors with
     `MXCSR` and `option bool` flags raising `BadFlagAccess` on reading `NONE`
     undefined flags (`x64Script.sml:86-163`). Omits packed integer SIMD,
     AVX/AVX2/AVX-512, `LOCK` prefix legality, fences, system registers, and CET.

7. **`NationalSecurityAgency/ghidra@3fb3eec6a05442c901e9ead8620ca21eae830b18` (SLEIGH, Apache-2.0; active, pushed 2026-11-20):**
   - `Ghidra/Processors/x86/data/languages/` totals `39,255` LOC across `27`
     `.slaspec`/`.sinc` files defining **`1,477` distinct constructor mnemonics**,
     including `ia.sinc` (`552` KB), `avx512.sinc` (`783` KB), `lockable.sinc`
     (`125` locked constructors), `cmpccxadd.sinc`, `rao.sinc`, `sgx.sinc`, and
     `cet.sinc` (no `REX2`/APX yet).
   - **Critical Verification Blocker:** Across those 27 files, SLEIGH declares
     **`1,716` distinct uninterpreted `define pcodeop` userops** (including
     `LOCK`, `ShadowStackPush8B`, `PackedFloatingADD`, `GlobalDescriptorTableRegister`,
     etc.), and `cet.sinc:292-293` explicitly warns:
     `Shadow Stack semantics is not currently implemented correctly in these instructions nor in the instructions affected by CET`.
     Thus SLEIGH is an excellent reverse-engineering disassembler/p-code lifter
     but **unsuitable as a complete, zero-axiom formal $I_{\text{ref}}$**
     because every `pcodeop` acts as an uninterpreted black box.

8. **`BinaryAnalysisPlatform/bap@034bbd09646a589d5eb1f10b740177d628da80fd` (MIT; last pushed 2026-05-07):**
   - Splits x86-64 lifting across legacy OCaml BIL lifters (`plugins/x86/x86_disasm.ml`,
     `x86_cmpxchg.ml`, `x86_btx.ml`) and Primus Lisp semantics
     (`plugins/x86/semantics/x86-64.lisp`, `x86-common.lisp`,
     `x86-64-sse-intrinsics.lisp`), delegating binary decoding to LLVM MC
     (`x86_llvm_env.ml`). Includes `CMPXCHG` and CET function-start patterns
     (`patterns/cet.xml`: `0xf30f1efa`), but inherits LLVM MC's unverified C++
     decoder and lacks a kernel-checked theorem-prover semantics.

9. **`intelxed/xed@0bcb6237345c5066726dcc08b3d87928df3b5b26` (Apache-2.0; pushed 2026-08-24):**
   - `datafiles/` spans `110` ISA-extension subdirectories (`apx-f`, `cet`,
     `avx512*`, `avx10-1`, `avx10-2`, `amx-*`, `rao-int`, `cmpccxadd`, `fred`,
     `tdx`, `sgx`, `uintr`), defining **`1,995` distinct `ICLASS`es**, **`9,149`
     `ICLASS` encoding blocks**, and **`62` `LOCKABLE` tags**. Supplies the
     gold-standard vendor encoding/decoding/prefix-precedence/legality tables
     (including APX `REX2`), with **zero arithmetic/operational semantics**.

10. **`digama0/mm0@0d414c0bfdaaeb7fea571895127abc1fa5a3d956` (CC0-1.0; pushed 2026-09-30):**
    - `examples/x86.mm0` (`1,727` LOC) formalizes ~30 user-mode scalar x86-64
      instructions (`cmpxchg`, `xadd`, `xchg`, ALU, control, `syscall`, `ud2`,
      explicit 15-byte `len l <= 15` limit at line 729) via a relational
      predicate `decode (ast l : nat) : wff` (`x86.mm0:726-729`), paired with
      a **731-line machine-checked determinism proof** `examples/x86_determ.mm1`
      (`readMemX_decode_determ` / `decode_step` at lines 727–730) and a Lean 3
      port (`mm0-lean/x86/`). Zero SIMD, zero system registers, zero CET.

11. **`leanprover/LNSym@49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c` (Apache-2.0; `lean-toolchain: v4.35.0`):**
    - Strictly **AArch64-only**: `0` x86/x64 files, `0` x86 branches, `0` x86
      issues/PRs, and `0` x86 plans in `README.md`. Direct construct census of
      `Arm/` (`71` files, `14,334` LOC) reveals `0` `axiom`, `0` `opaque`, `1`
      `sorry` macro (`Arm/Util.lean:9`), `35` `partial def` (all in random
      co-simulation generators `*.rand` and `Expr` tactic helpers, outside
      semantics), and **`22` `bv_decide` calls** (`16` inside `Arm/Insts/Common.lean`,
      `1` in `Arm/State.lean`, `3` in `Arm/BVDecideEnums.lean`, `1` in
      `Arm/Memory/MemoryProofs.lean`, `1` in `Advanced_simd_copy.lean`) which
      emit kernel `._native.bv_decide.ax_*` axioms.

#### 1.2 Unified Cross-ISA Reference Model Decision Matrix (`x86_64`, `aarch64`, `riscv64`)

| Candidate Model (Pinned SHA) | ISA | Scalar / Flags / CSRs | SIMD / Vector | Atomics & Fences | CET / BTI / PAC / Zicfi | Lean 4 Replay Compatibility (`axiom`/`partial`/`opaque`/`sorry`/`bv_decide`) | License | Maintenance Risk |
| :--- | :---: | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`ACL2 x86isa`** (`f040a8db`) + **`sail-x86-from-acl2`** (`0c6c023d`) | `x86_64` + `i686` | Full GP, `RFLAGS` (`undef-flg`), Ring 0–3, paging, MSRs, `SYSCALL` (`211` `def-inst`) | `x87`, MMX, SSE–SSE4.1, partial AVX, `ZMM`/EVEX infra (no `PSHUFB`/VNNI) | Full `LOCK` legality, `XCHG`, `CMPXCHG8B/16B`, `XADD` | `ENDBR32`/`64` as NOP only (no CET tracker) | Requires ACL2→Lean or Sail→Lean port (`sail-x86-from-acl2` needs Sail refactor; `noncomputable` + monad overhead) | **BSD-3-Clause** (translator BSD-2) | Low (ACL2 active 2026); Medium (`sail-x86` stale since 2024-11) |
| **`s2n-bignum` x86** (`280a2209`) | `x86_64` | `163` ctors; GP, `UNDEFINED_VALUES` flags; no system regs | SSE2/SSSE3/AVX2/AVX-512 crypto+integer (`ZMM`+`EVEX` masks); no FP/`MXCSR` | `XCHG` only; `LOCK` (`0xF0`) rejected (`NONE`), no `CMPXCHG`/`XADD`/fences | `ENDBR64` as NOP (`x86.ml:1011`) | Clean HOL Light→Lean 4 port path (total decoder + `x86_decode_unique`); `cslib-bignum` has 0 x86 files yet | **Apache-2.0 OR ISC OR MIT-0** | Very Low (AWS active 2026) |
| **`AeneasVerif/kraken` X64** (`019a72cb`) | `x86_64` | `47` scalar ctors, 6 flags; no system regs, **no byte decoder** | `26` `AvxOperation` (SSE/AVX2/SHA256/6 unmasked AVX-512) | **None** | **None** | Native Lean 4 (`0` `axiom`/`opaque`; `1` `partial` `eval`; `4` `sorry` + `5` `bv_decide` in elab/examples); uses `nightly-2026-09-21` `module` syntax | **MIT** | Low (active 2026), fast-moving nightly target |
| **`K X86-64`** (`592380ae`) | `x86_64` | `3,155` Haswell user variants, `undefMInt`; no system regs, no byte decoder | Broadest `SSE`–`AVX2`/`FMA`/`BMI`; **0** `AVX-512` | `cmpxchg`/`xadd`/`xchg` (un-locked); **0** `LOCK`, **0** fences | **None** | Poor: legacy K syntax, 512-branch unrolled `#ifMInt` rules, known PR `#4`/`#7` defects; test oracle only | **UIUC / NCSA** | **High** (unmaintained >6 yrs, 2020-03) |
| **`Ghidra SLEIGH`** (`3fb3eec6`) | `x86_64` + `i686` | `1,477` mnemonics, `39k` LOC | Full `SSE`–`AVX-512` (no APX/`REX2`) | `125` `lockable.sinc` ctors (via opaque `LOCK` pcodeop) | `cet.sinc` (shadow stack explicitly unimplemented) | **Blocked** as formal $I_{\text{ref}}$: `1,716` opaque `define pcodeop` black boxes | **Apache-2.0** | Very Low (NSA active 2026) |
| **`Intel XED`** (`0bcb6237`) | `x86_64` + `i686` | Decode/encode/legality only (`1,995` `ICLASS`es, `9,149` blocks); **0** semantics | All through `AVX-512`, `AMX`, `AVX10`, `APX` (`REX2`) | Exact `62` `LOCKABLE` tags & `#UD` rules | Full CET decode (`cet-isa.xed.txt`) | High for **decoder/legality table certification** (`decodeDirect` oracle); N/A for ALU execution | **Apache-2.0** | Very Low (Intel active 2026) |
| **`MM0 x86.mm0`** (`0d414c0b`) / **`sail-tiny-x86`** (`229bd844`) | `x86_64` | ~30 (`MM0`) / `19` (`sail-tiny`) user scalar + `syscall` (`MM0`) | **None** | `cmpxchg`/`xadd`/`xchg` (`MM0`); `LOCK`+fences (`sail-tiny`) | **None** | High clarity (`x86_determ.mm1` determinism pattern); far too small for full $I_{\text{ref}}$ | **CC0-1.0** / **BSD-2-Clause** | Medium (research prototypes) |
| **`sail-arm`** (`5416ef6b`) + **`ASLp`** (`92e4fd94`) | `aarch64` (+ `armv7`) | Full A64 + EL0–EL3 + `FPCR`/`FPSR` | Full NEON, DotProd, I8MM, SVE/SVE2, SME | Full LSE/LSE2/LL-SC/barriers | Full **BTI + PAC + GCS + MTE** | `sail-arm` monolithic `182k` LOC + `ArmExtras.lean` `sorry` fallback; **viable via `ASLp` per-opcode `rASL` slicing** | **BSD-3-Clause-Clear** (`sail-arm`); **BSD-3-Clause** (`aslp` tool; raw Arm XML proprietary) | Low (`sail-arm` active 2026); Medium (`aslp`) |
| **`LNSym`** (`49f8a1d9`) / **`Kraken` AArch64** (`019a72cb`) | `aarch64` | `LNSym`: user GP+`NZCV`; `Kraken`: `93` scalar `Operation` ctors (no byte decoder) | `LNSym`: 128-bit NEON+Crypto (no `FPSR.QC`, no SVE); `Kraken`: scalar only | **None** | **None** (`LNSym` `Hints.lean` rejects `BTI`/`PACIASP`) | `LNSym`: native Lean (`v4.35.0`), but `22` `bv_decide` in `Arm/` inject `_native` axioms (`35` `partial` in tests/tactics); `Kraken`: nightly `module` | **Apache-2.0** / **MIT** | Low (AWS / AeneasVerif active 2026) |
| **`sail-riscv`** (`71dc9c25`) / **`sail-riscv-lean`** (`51c635c4`) / **`riscv-zkvm`** (`b878729f`) | `riscv64` | Full U/S/M/H modes, CSRs, Sv39/48/57 | Full F/D/Zfh + RVV 1.0 (note `sail-riscv-lean` hardcodes `vta`/`vma` undisturbed) | Full `Zaamo` + `Zalrsc` (pure-extern `match_reservation` seam in Sail) | Full **`Zicfilp` + `Zicfiss`** in `sail-riscv@71dc9c25` | `0` `partial`/`unsafe`/`opaque`/`sorry` in generated Lean, **75 `axiom`s** in `RiscvExtras.lean` requiring scoped patch; full `Defs` OOMs at `-M2048` (passes `-M4096`); scoped `riscv-zkvm` ~80 mods / 47k LOC | **BSD-2-Clause** (`sail-riscv`) | Very Low (RISC-V official spec, active 2026) |

**Derived Architecture Selection (`Basis: derived`):**
- **RISC-V (`riscv64`):** Scoped `riscv/sail-riscv` extraction (`riscv-zkvm`
  pattern) with patched `RiscvExtras.lean` (`0` axioms) and explicit stateful
  reservation lifting is already viable for Pass-2 CI.
- **AArch64 (`aarch64`):** `rems-project/sail-arm` (`BSD-3-Clause-Clear`) sliced
  per opcode/extension (or `ASLp` `rASL` over open-licensed Arm ASL) provides
  complete EL0–EL3 + SIMD + LSE + BTI/PAC coverage without monolithic blowup,
  while `LNSym`/`Kraken` inform the fast Pass-1 $I_{\text{anneal}}$ design
  (stripped of `bv_decide` axioms and `partial` test helpers).
- **x86-64 (`x86_64`):** No single upstream Lean 4 $I_{\text{ref}}$ exists.
  The lowest-risk, permissively licensed Pass-2 architecture composes:
  (1) **`intelxed/xed`** (`Apache-2.0`) as the authoritative decode/legality
  table generator/oracle, (2) a clean Lean 4 port of **`s2n-bignum`** (`Apache-2.0/MIT-0`)
  encoding/scalar/SIMD rules + **`ACL2 x86isa`** (`BSD-3-Clause`) `LOCK`/atomic,
  `RFLAGS`, and system semantics (either via direct Lisp→Lean extraction of
  the pure `def-inst` specs or a sliced Sail export), cross-checked
  differentially against `kframework/X86-64-semantics` and native x86-64 silicon.

---

### 2. Low-TCB Total Machine-Code Decoding in Lean 4: Direct Structural Decoder vs. Witness-Checked Encoder

`Basis: normative + source + execution + derived`

Fixed-width 32-bit ISAs (AArch64 and base non-compressed RISC-V) decode by pure
bitfield slicing of a single `BitVec 32` (`LNSym` `Arm/Decode.lean`, `riscv-coq`
`Decode.v`), trivially terminating without recursion. By contrast, x86-64
instructions span **1 to 15 bytes** with four legacy prefix groups, optional
`REX` (`0x40..0x4F`) or APX `REX2` (`0xD5`), 2- or 3-byte `VEX` (`0xC5`/`0xC4`),
4-byte `EVEX` (`0x62`), 1–3 opcode bytes, `ModR/M`, optional `SIB`, 0/1/2/4-byte
displacement, and 0/1/2/4/8-byte immediate.

#### 2.1 Empirical Evidence of Real-Compiler Encoding Multiplicity and Disassembler Hazards

Running `support/x86_64_encoding_multiplicity_probe.py` against `gcc 15.2.0`
(`-O2 -fcf-protection=full -mavx2`), `llvm-mc 21.1.8`, and GNU `objdump 2.47`
(`support/x86_64_encoding_multiplicity_results.json`) establishes two empirical
facts:

1. **Real `-O2` object files emit non-canonical and multi-form encodings immediately:**
   - **11-byte repeated-prefix alignment NOP:** `gcc -O2` emitted
     `66 66 2e 0f 1f 84 00 00 00 00 00` (`data16 cs nop WORD PTR [rax+rax*1+0x0]`,
     with **two `0x66` prefixes**, a `0x2e` CS override, SIB, and 4-byte zero
     displacement) alongside 3-byte (`0f 1f 00`), 7-byte (`0f 1f 80 00 00 00 00`),
     and 8-byte (`0f 1f 84 00 00 00 00 00`) NOPs.
   - **Mandatory prefix semantic aliasing & CET:** `gcc -O2` emitted
     `f3 0f 1e fa` (`endbr64`) at all 5 function entries, `f0 48 83 01 01`
     (`lock add [rcx], 1`) and `f0 48 0f b1 17` (`lock cmpxchg [rdi], rdx`),
     `f3 48 0f bc d1` (`tzcnt rdx, rcx`, which executes as `bsf` on pre-BMI1
     CPUs because `0xF3` is ignored there!), mandatory SIB `48 89 74 24 f8`
     (`[rsp-0x8]`), `disp32` `48 03 87 00 01 00 00` (`[rdi+0x100]`), and mixed
     VEX2 (`c5 fd ef c1` `vpxor`) vs. VEX3 (`c4 e2 7d 00 c2` `vpshufb`).

2. **34-case differential matrix (`llvm-mc 21.1.8` vs. GNU `objdump 2.47`):**

| Hazard / Multiplicity Class | Concrete Byte Specimen(s) | `llvm-mc 21.1.8` Output | GNU `objdump 2.47` Output | Normative Intel SDM Semantics |
| :--- | :--- | :--- | :--- | :--- |
| **Direction-bit alternate opcodes** | `48 01 f0` vs. `48 03 c6` | Both `addq %rsi, %rax` | Both `add rax, rsi` | Identical 64-bit `add rax, rsi` (`0x01` MR vs. `0x03` RM) |
| **3-way immediate multiplicity** | `48 05 01000000` (6 B) vs. `48 81 c0 01000000` (7 B) vs. `48 83 c0 01` (4 B) | All 3 `addq $1, %rax` | All 3 `add rax, 0x1` | Identical `add rax, 1` (`0x05` RAX-short, `0x81 /0` imm32, `0x83 /0` sext imm8) |
| **4-way ModR/M + SIB multiplicity** | `48 8b 07` (3 B) vs. `48 8b 47 00` (4 B) vs. `48 8b 87 00000000` (7 B) vs. `48 8b 04 27` (4 B) | `movq (%rdi), %rax` / `(%rdi,%riz)` | `mov rax, [rdi]` / `[rdi+0x0]` / `[rdi+riz*1]` | All 4 compute identical `mov rax, [rdi]` |
| **`REX.B` + `0x90` soundness trap** | `90`, `66 90`, `40 90`, `48 90` vs. **`41 90`**, **`49 90`** | `nop` vs. **`xchgl %r8d, %eax`**, **`xchgq %r8, %rax`** | `nop` vs. **`xchg r8d, eax`**, **`xchg r8, rax`** | `0x90` is `NOP` **iff `REX.B = 0`**; `41 90` mutates & zero-extends `r8`/`rax`! |
| **REX nullification by later legacy prefix** | `48 67 01 00` vs. `67 48 01 00` | `addl %eax, (%eax)` vs. `addq %rax, (%eax)` | `rex.W; add [eax], eax` vs. `add [eax], rax` | Any legacy prefix *after* `REX` nullifies `REX` (`48 67 01 00` is 32-bit!) |
| **`66`/`F2`/`F3` mandatory-prefix precedence** | `66 f3 0f 58 c1` & `f3 66 0f 58 c1`; `f2 f3 0f 58 c1` vs. `f3 f2 0f 58 c1` | `addss`; `addss` vs. `addsd` | `data16 addss`; `repnz addss` vs. `repz addsd` | `F2`/`F3` override `66` regardless of order; last-wins within `{F2, F3}` |
| **Disassembler resync bug on `0F 1E FA`** | `0f 1e fa` (no `F3`) vs. `f3 0f 1e fa` | **Warning + `cli` (`0xFA`)** vs. `endbr64` | `nop edx` vs. `endbr64` | `0F 1E /r` without `F3` is a 3-byte hintable NOP (`llvm-mc` mis-resyncs!) |
| **Silent acceptance of `#UD` `LOCK`** | `f0 48 01 f0` (reg dst); `f0 48 8b 07` (`mov`) | `lock \| addq %rsi, %rax`; `lock \| movq (%rdi), %rax` | `lock add rax, rsi`; `lock mov rax, [rdi]` | **Both raise architectural `#UD`** (neither disassembler flags `#UD`!) |
| **15-byte `#GP(0)` limit** | 14×`66` + `90` (15 B) vs. **15×`66` + `90` (16 B)** | **Both `nop`** (no error at 16 B!) | Splits at 14×`data16` + `66 90` | 15 B is legal `nop`; **16 B raises architectural `#GP(0)`** |
| **VEX2 vs. VEX3 multiplicity** | `c5 f5 ef c0` (4 B) vs. `c4 e1 75 ef c0` (5 B) | Both `vpxor %ymm0, %ymm1, %ymm0` | Both `vpxor ymm0, ymm1, ymm0` | Identical 256-bit `vpxor` |

#### 2.2 Architectural Comparison: (a) Direct Total Structural Decoder vs. (b) Witness-Checked Encoder

Comparing the two kernel-sound decoding designs in Lean 4 (`Init.*`-only, zero
`partial def`) and mechanizing both side by side in
`support/X86DecodingAndPass2CorrespondenceProbe.lean` resolves a frequent design
misconception:

| Criterion | (a) Direct Total Structural Decoder (`decodeDirect : List UInt8 → DecodeOutcome`) | (b1) Naive Canonical Encoder (`encodeCanonical ins = some bs`) | (b2) Hint-Parameterized Witness Encoder (`encodeWithHint ins hint = some bs`) |
| :--- | :--- | :--- | :--- |
| **Total termination (`0` `partial def`)** | Structural recursion on explicit fuel `16` (naturally enforces the 15-byte `#GP(0)` bound with zero `partial def`). | Structurally non-recursive. | Structurally non-recursive (bounds `pad66Count ≤ 14`). |
| **Handles compiler `.o` multiplicity** | **Yes** — maps all legal forms (`0x01`/`0x03`, `0x05`/`0x81`/`0x83`, SIB/disp, 11-byte GCC NOPs, VEX2/VEX3) to canonical `X64Instr`. | **No** (`canonical_encoder_misses_alternate_encodings` proves rejection of `48 03 c6` and GCC's 11-byte NOP). | **Yes** (`encodeWithHint_covers_multiplicity`), provided every emitted variant has an explicit `EncHint` constructor. |
| **Determinism / Unambiguity** | **Automatic by functionality of `decodeDirect`** (plus prefix-linearity as in `s2n-bignum` `list_linear_decode` / `x86_decode_unique`). | Trivially injective if encoding forms are disjoint. | **NOT automatic — major TCB hazard!** An omitted legality check (`REX.B = 0` on `0x90`, `LOCK` reg-dst, REX-before-legacy nullification) lets one byte slice witness two different instructions (`buggy_witness_checker_ambiguous_on_41_90` proves `[0x41, 0x90]` matches both `nop` and `xchg r8d, eax`). Requires proving `encodeWithHint_unambiguous` (just as `MM0` requires `731`-line `x86_determ.mm1`). |
| **`#UD` / `#GP(0)` Fault Semantics** | Directly models `#UD` (illegal `LOCK`, invalid `EVEX`/`VEX`) and `#GP(0)` (`> 15` bytes) as first-class `DecodeFault` outcomes. | Cannot express why a byte stream traps without specifying the full complement of valid encodings. | Same complement gap: an encoder alone cannot distinguish "unsupported instruction" from "architectural `#UD`/`#GP`" unless paired with a decoder. |
| **Lean 4 Kernel Reduction Ergonomics** | Fast `rfl` on concrete byte lists; **critical engineering rule:** dispatch opcodes via flat `match opc` or structured lookup tables rather than chained `if-else-if` inside `simp` (chained `if` over `UInt8` triggers $2^k$ equational-theorem blowup). | Trivial `rfl` on byte equality. | Fast `rfl` for positive checks (`encodeWithHint ins hint = some bs`), but the soundness proof `encodeWithHint_sound_wrt_decodeDirect` must still reason about `decodeDirect` anyway. |

**Derived Verdict (`Basis: derived + execution`):**
Architecture (b2) (witness-checked encoding) **does not avoid** specifying
x86-64 prefix precedence, REX nullification, `LOCK` legality, and the 15-byte
limit inside the TCB: without a proved functionality/disjointness theorem
linking `encodeWithHint` to a deterministic decoder (or pairwise bit-disjointness
as in `digama0/mm0/examples/x86_determ.mm1`), an untrusted prover can exploit
encoding overlaps to prove false theorems about real machine bytes. The optimal
Lean 4 design is therefore **Architecture (a) — a direct, fuel-bounded (`fuel = 16`),
total `Init.*`-only structural decoder `decodeDirect` in `Trusted.*`**,
cross-certified in Pass-2 CI against `intelxed/xed` tables (and $I_{\text{ref}}$'s
decoder), optionally paired with untrusted decode-step hints in `theory/` proof
tactics that discharge `decodeDirect (bytes ++ rest) = .ok ins n` in one `rfl`
step per concrete instruction (mirroring `s2n-bignum`'s `X86_DECODE_CONS`).

---

### 3. Generalizing Two-Model Pass-2 Correspondence (`M_anneal` vs. `lean-miri`) to Multi-ISA ($I_{\text{anneal}}$ vs. $I_{\text{ref}}$)

`Basis: source + execution + derived`

#### 3.1 Baseline Mechanism in `joshlf/anneal@c131b320`

In `joshlf/anneal@c131b320` (`trusted/correspondence/Trusted/Correspondence.lean`,
`3,048` lines; `docs/mir-correspondence-design.md:559-624, 1421-1490, 2057-2180`),
Pass-1 verification runs on a compact `Init.*`-only model (`Trusted.MirSemantics`,
shipped to users without `vendor/`), while Pass-2 CI replays the pinned
160-module `vendor/lean-miri` slice (`44,730` LOC) and checks locked `*Claim`
theorems. Three design elements transfer directly to multi-ISA correspondence:

1. **Three-pole step outcomes:** `.step next`, `.done out`, `.fault .undefined`
   (modeled UB / architectural fault), and `.fault .unsupported` (staged support
   gate). `WellFormed p q` requires entry success, non-empty `ValidChoice` at
   every reachable state, and zero reachable faults.
2. **Staged support gate:** `Trusted.Correspondence` fences `M_ref` via
   `refIsSupportedLocalTy` / `refEnumAdmitted` so unsupported constructs map to
   `.blocked` matching `M_anneal`'s `.fault .unsupported`, keeping the initial
   verified surface small without altering upstream `vendor/` semantics.
3. **Choice-coupled one-way refinement (`CorrespondenceAtChoicesClaim`, `mir-correspondence-design.md:2118-2136`):**
   Already anticipates nondeterminism by making `WellFormed → RefWellFormed`,
   `RefValidPrefixAtChoices → ValidPrefixAtChoices`,
   `RefBehaviorAtChoices → BehaviorAtChoices`, and
   `RefDivergesAtChoices → DivergesAtChoices` **one-way** from reference to
   Anneal, while retaining bidirectional `FaultEquivalenceAtChoicesClaim`.

#### 3.2 Staged-Gate Per-Opcode Correspondence and Slicing for Multi-ISA Scaling

Generalizing to `x86_64`, `aarch64`, and `riscv64` hits an immediate Pass-2 CI
scaling wall: monolithic extracted ISA models blow past Lean's single-module
allocator budget (`opencompl/sail-riscv-lean`'s `LeanRV64D.Defs` fails with
`(kernel) excessive memory consumption detected` under Anneal's `-M2048` vendor
limit and requires `-M4096` / `2.47 GiB` peak RSS; `rems-project/sail-arm`
emits a monolithic `182,786`-line `SailArm.lean`).

`support/X86DecodingAndPass2CorrespondenceProbe.lean` mechanizes the modular
solution (`per_opcode_ref_refined_by_anneal` →
`pass2_isa_correspondence_and_post_transfer`):

1. **Compact `Init.*`-only $I_{\text{anneal}}$ (`50–150` initial opcodes):**
   Defines a closed `SupportedOp : IsaOp → Bool` predicate covering the baseline
   compiler/kernel subset (recall from `formal-isa-models-x86-64-i386-and-aarch64-coverage`
   that all of Rust `libcore` emits only `199` x86-64 and `129` AArch64 distinct
   mnemonics). Any decoded or undecoded instruction outside `SupportedOp`
   transitions deterministically to `.fault .unsupported` (fail-closed).
2. **Per-opcode / per-extension sliced Pass-2 modules:**
   Because the top-level refinement theorem
   `pass2_isa_correspondence_and_post_transfer` depends on $I_{\text{ref}}$
   **exclusively** through the single-step per-opcode obligation
   $$\forall \text{op},\; \text{SupportedOp}(\text{op}) = \text{true} \implies \forall s\, c,\; \exists c',\; \text{evalAnnealOp}(\text{op}, c', s) = \text{evalRefOp}(\text{op}, c, s),$$
   Pass-2 CI can partition both the scoped $I_{\text{ref}}$ extraction and
   `correspondence/Anneal/<ISA>/` into independent extension slices (`BaseALU`,
   `ShiftsBitScan`, `ControlFlow`, `Atomics`, `SSE2`/`NEON`, `AVX2`/`SVE`,
   `PrivTraps`). Each slice compiles and replays under bounded memory (`-M2048`
   to `-M4096`), and a thin dispatcher composes them without importing
   out-of-scope extensions (e.g., SoftFloat `F`/`D`, `AMX`, `SME`) into the
   kernel cone. Out-of-scope opcodes require **zero** semantic correspondence
   proofs because `WellFormedOf evalAnnealStep` guarantees no reachable state
   ever executes an `.unsupported` opcode.

#### 3.3 Handling ISA-Level Nondeterminism Under One-Way Refinement ($I_{\text{ref}} \subseteq I_{\text{anneal}}$)

Four concrete hardware nondeterminism mechanisms expose subtle traps if Pass-2
ISA correspondence naively copies symmetric `↔` equivalence or trusts an
over-determined $I_{\text{ref}}$:

| Nondeterminism Mechanism | Normative Hardware Rule | Behavior in Existing Upstream $I_{\text{ref}}$ Models | Required $I_{\text{anneal}}$ Model & Refinement Direction |
| :--- | :--- | :--- | :--- |
| **x86-64 undefined flags & zero-input dest (`BSF`/`BSR`, `SHL`/`SHR`/`SAR`, `MUL`/`IMUL`)** | Intel SDM Vol. 2: `BSF`/`BSR` leave `CF,OF,SF,PF,AF` undefined (and dest undefined if `src = 0`); `SHL` leaves `OF` undefined for `count > 1` and `AF` undefined for `count > 0`; `MUL` leaves `ZF,SF,PF,AF` undefined. | `s2n-bignum` (`UNDEFINED_VALUES[...]`), ACL2 (`undef-flg`), and K (`undefMInt`) model nondeterministic bits; HOL4 `x64` (`BadFlagAccess`) and Jasmin (`ErrAddrUndef`) fault on read. | **Demonic bit choice** (`c.undefBit : Bool`) preserves both `RefBehavior ⊆ AnnealBehavior` AND bidirectional `FaultEquivalence`; **poison-fault** (`Option Bool = none`) still soundly transfers `SatisfiesPost` (`WellFormed_anneal → WellFormed_ref`), but **breaks reverse fault equivalence** (`poison_breaks_reverse_fault_equiv`). |
| **RVV 1.0 `vta`/`vma` agnostic elements** | RISC-V Vector Spec §3.4.3: when `vta = 1` or `vma = 1`, each tail/inactive element may independently remain **undisturbed** or be overwritten with **all 1s**. | `opencompl/sail-riscv-lean@51c635c4` (`VextUtilsInsts.lean:498-523`) **hardcodes undisturbed** (`vd_val[i]`). | $I_{\text{anneal}}$ MUST model the wide choice `{undisturbed, all-1s}` (`c.vtaAllOnes : Bool`). Against narrow `sail-riscv-lean`, one-way `I_ref ⊆ I_anneal` holds (`per_opcode_ref_refined_by_anneal`), while symmetric `↔` is **provably false** (`symmetric_vta_iff_false`). Copying narrow `sail-riscv-lean` into $I_{\text{anneal}}$ is **unsound against silicon** (`narrow_anneal_proves_false_hardware_property`). |
| **RISC-V `LR`/`SC` & AArch64 `LDAXR`/`STLXR` spurious failure** | Both architectures permit `SC`/`STXR` to fail spuriously even after a matching `LR`/`LDXR` without intervening writes. | `riscv/sail-riscv` declares `match_reservation`/`valid_reservation` as `pure` externs (open seam); `RiscvExtrasExecutable` hardcodes `false` (always fail). | Lift `reserved : Option PhysAddr` into state and include `c.scSpurious : Bool` so `SC` succeeds only when `reserved = some addr ∧ !c.scSpurious`, subsuming both always-fail and stateful-match references. |
| **IEEE-754 quiet-NaN payload & sign propagation** | x86-64 SSE/AVX propagates the first NaN operand's payload; AArch64 (`FPCR.DN = 1`) and RISC-V emit a canonical quiet NaN (`0x7FF8_0000_0000_0000` / `0x7FC0_0000`); cross-ISA / fused-op NaN payloads vary. | Concrete FP models pick one ISA's specific quiet-NaN bit pattern. | Per-ISA exact quiet-NaN rule for bit-exact Pass-2 `↔`, OR demonic choice over all quiet NaNs (`c.nanPayload : BitVec 51`) when proving ISA-independent NaN-agnostic specs, cleanly subsuming canonical-NaN references (`per_opcode_ref_refined_by_anneal`). |

**Critical Pass-2 Audit Rule for Narrow References (`Basis: derived + execution`):**
Whenever an upstream $I_{\text{ref}}$ under-approximates normative architectural
nondeterminism (as `sail-riscv-lean` does for RVV `vta`/`vma` and `vl_use_ceil`,
or `s2n-bignum` and ACL2 `endbranch.lisp` do by treating `ENDBR64` as a NOP
ignoring CET-IBT `TRACKER`), Pass-2 refinement `I_ref ⊆ I_anneal` **checks
agreement on the deterministic core**, while the wider demonic branches of
$I_{\text{anneal}}$ (such as `vtaAllOnes = true` or CET-IBT `TRACKER = WAIT_FOR_ENDBRANCH`
trapping `#CP`) must be explicitly listed in the human-audited TCB boundary
(`Human review surface`) and validated by targeted hardware/litmus probes
rather than silently narrowed to match $I_{\text{ref}}$.

---

## Boundaries

- **Not examined:**
  - Full compilation or Lean kernel replay of `rems-project/sail-x86-from-acl2`
    or `AeneasVerif/kraken@019a72cb` (which targets `nightly-2026-09-21` rather
    than Lean `v4.34.1`);
  - Hardware execution of illegal `LOCK` (`#UD`) or 16-byte (`#GP(0)`) byte
    sequences under a signal-trapping `SIGILL`/`SIGSEGV` harness on physical
    Intel/AMD silicon (legality rules are cited from Intel SDM Vol. 2A/2B and
    `intelxed/xed`, while `llvm-mc` and GNU `objdump` were executed directly);
  - Weak-memory multi-threaded x86-TSO / Armv8 / RVWMO store-buffer semantics
    beyond single-core sequential step transitions and atomic `LOCK`/`LR`/`SC`
    interfaces (covered separately in `weak-memory-concurrency-models-hardware-mappings-and-optimizations`);
  - Full `EVEX` / `APX` `REX2` (`0xD5`) byte decoding inside the Lean probe
    (only legacy prefixes, `REX`, `ModR/M`, `imm8`/`imm32`, `LOCK`, `0x0F`
    escape, and the 15-byte limit are mechanized in `X86DecodingAndPass2CorrespondenceProbe.lean`).
- **Unknown:**
  - Exact Lean `v4.34.1` peak RSS and cold replay wall-clock time for a
    150-instruction x86-64 Pass-2 $I_{\text{ref}}$ slice derived from
    `s2n-bignum` + `ACL2 x86isa` (no full 150-instruction x86-64 Lean $I_{\text{ref}}$
    has been built yet);
  - Whether upstream `cslib-community/bignum` or `leanprover/LNSym` plans an
    x86-64 port (none is present in public branches, PRs, or issues as of
    2026-11-20);
  - Whether `rems-project/sail-tiny-x86` will add a `sail -lean` backend target
    alongside Rocq.
- **Known not to apply:**
  - Off-the-shelf binary disassemblers (`llvm-mc 21.1.8`, GNU `objdump 2.47`)
    as architectural `#UD`/`#GP(0)` legality oracles: empirical execution proves
    both accept illegal `LOCK` forms, neither enforces the 15-byte `#GP(0)`
    bound, and `llvm-mc 21.1.8` mis-resynchronizes `0f 1e fa` as `cli`;
  - Unparameterized canonical-only encoders (`encode ins = raw_bytes`) for
    verifying arbitrary compiler-emitted `.o` machine code (refuted both by
    `gcc 15.2.0 -O2` emitting `66 66 2e 0f 1f 84 00 00 00 00 00` and by
    `canonical_encoder_misses_alternate_encodings`);
  - Unproved witness-checked encoders without a functionality/disjointness
    theorem (refuted by `buggy_witness_checker_ambiguous_on_41_90`);
  - Symmetric `↔` Pass-2 correspondence against narrow concrete references when
    $I_{\text{anneal}}$ models normative hardware nondeterminism (refuted by
    `symmetric_vta_iff_false`), and bidirectional `FaultEquivalenceClaim` when
    $I_{\text{anneal}}$ uses poison-fault semantics for undefined flags while
    $I_{\text{ref}}$ uses bit-choice nondeterminism (refuted by
    `poison_breaks_reverse_fault_equiv`);
  - Direct adoption of Ghidra SLEIGH as a zero-axiom formal $I_{\text{ref}}$
    (`1,716` opaque `define pcodeop` black boxes) or unpatched `LNSym/Arm` as a
    zero-axiom vendor slice (`22` `bv_decide` calls generating `_native` axioms).
- **Unsupported:**
  - `AeneasVerif/kraken@019a72cb` has no x86-64 machine-code byte decoder, no
    `LOCK`/atomic instructions, and no CET/system-register modeling;
  - `awslabs/s2n-bignum@280a2209` `x86/proofs/decode.ml` explicitly rejects
    `0xF0` (`LOCK`), `0x64`/`0x65` (`FS`/`GS`), and `0x67` address-size overrides;
  - `joshlf/anneal@c131b320` Pass-2 audit (`trusted/audit/src/lib.rs`) currently
    hardcodes a single `vendor/lean-miri` root and does not yet support
    pluggable multi-ISA vendor roots.
- **Stronger conclusions not established:**
  - Proving `encodeWithHint_sound_wrt_decodeDirect` on the 9-instruction probe
    subset establishes the structural proof pattern and ambiguity hazard, not
    full coverage of Intel XED's `9,149` encoding forms;
  - Proving `I_ref ⊆ I_anneal` against a narrow $I_{\text{ref}}$ does not
    mechanically prove `I_hw ⊆ I_anneal` for architectural nondeterminism that
    $I_{\text{ref}}$ omits.

---

## Evidence

All primary-source inspections, tool executions, and Lean `v4.34.1` kernel
proofs were acquired on `2026-11-20`.

### Primary Upstream Sources

1. **`AeneasVerif/kraken`** (`019a72cb0f494d26cdceefb2fd40aad19f704ed9`):
   `LICENSE` (MIT), `lean-toolchain` (`nightly-2026-09-21`),
   `Kraken/X64/Syntax.lean:189-288` (`47` `Operation` + `26` `AvxOperation`),
   `Kraken/X64/Semantics.lean:1101` (`partial def Executable.eval`),
   `Kraken/AArch64/Syntax.lean` (`93` `Operation` constructors), and full tree
   construct census (`51` files under `Kraken/`, `21` files / `6,924` LOC under
   `Kraken/X64/`).
2. **`acl2/acl2`** (`f040a8db474f68e11b5fa980c99b7c1f7be28e54`):
   `books/projects/x86isa/doc.lisp:1-20` (BSD-3-Clause),
   `machine/get-prefixes.lisp:67-68, 207-239, 387-510` (15-byte bound, `LOCK`
   tracking, `REX` nullification before legacy prefixes),
   `machine/instructions/exchange.lisp:51-377` (`x86-xchg`, `x86-cmpxchg`,
   `x86-cmpxchg8b/16b`), `machine/instructions/endbranch.lisp:47-89`
   (`x86-endbr32/endbr64` modeled as NOP with 15-byte `#GP(0)` check),
   `machine/rflags-spec.lisp` (`866` LOC), and full census (`106` `.lisp` files,
   `91,363` LOC, `211` `def-inst`).
3. **`awslabs/s2n-bignum`** (`280a220986a0bc6249248187717a771153d073db`) and
   **`cslib-community/bignum`** (`1b3952cba6438a6a03da02ff207deb6c93e7d4eb`):
   `s2n-bignum`: `LICENSE` (`Apache-2.0 OR ISC OR MIT-0`),
   `x86/proofs/instruction.ml` (`692` LOC, `163` `instruction` constructors),
   `x86/proofs/decode.ml:12-110, 473-489, 827, 1505-1508, 3400` (`read_prefixes`,
   `0xF0`/`0x64`/`0x65`/`0x67` → `NONE`, `ENDBR64`, `NOP_N`, `decode`,
   `list_linear_decode`), `x86/proofs/x86.ml:865-910, 1002-1012, 1226-1236, 1678-1691, 2833-2871`
   (`UNDEFINED_VALUES`, `x86_BSF`, `x86_SHL`, `x86_MUL2`, `x86_ENDBR64`,
   `x86_decode`, `x86_decode_unique`). `cslib-community/bignum`: tree census
   across `main` and `orig` (`41` `.lean` files, `Bignum/Arm/` only, `0` x86 files).
4. **`kframework/X86-64-semantics`** (`592380aea04820ea11cfa5475b343f0257f2474e`):
   `semantics/{register,memory,immediate,system}Instructions/` (`3,063` `.k`
   files; `0` `lock`/`mfence`/`lfence`/`sfence`/`syscall`/`cpuid`/`endbr`),
   `semantics/registerInstructions/bsfq_r64_r64.k`,
   `semantics/memoryInstructions/cmpxchgq_m64_r64.k`,
   `semantics/x86-syntax.k:1313-1377`, and GitHub issues/PRs `#4`, `#7`, `#10`,
   `#11`, `#13`, `#14`.
5. **`rems-project/sail-x86-from-acl2`** (`0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf`,
   `63` `model/*.sail` files) and **`rems-project/sail-tiny-x86`**
   (`229bd8448937042baa51b0a2d14bc437929b0dce`, `LICENSE` BSD-2-Clause,
   `Makefile`, `decode.sail`, `19` AST constructors).
6. **`coruus/L3`** (`d6558e679a25ffaaf16a47a3189f8f8111e45e0c`,
   `isa-models/x86-64/x64.spec`, `1,357` LOC) and **`HOL-Theorem-Prover/HOL`**
   (`aee6a90d9856a842f4cbd2bfc44efb7067a141e4`,
   `examples/l3-machine-code/x64/model/x64Script.sml:86-163`, `11,473` LOC).
7. **`NationalSecurityAgency/ghidra`** (`3fb3eec6a05442c901e9ead8620ca21eae830b18`):
   `Ghidra/Processors/x86/data/languages/{x86-64.slaspec,ia.sinc,lockable.sinc,cet.sinc,avx512.sinc}`
   (`27` files, `39,255` LOC, `1,477` mnemonics, `1,716` `define pcodeop`s,
   `125` `lockable.sinc` constructors, `cet.sinc:292-293` shadow-stack caveat).
8. **`BinaryAnalysisPlatform/bap`** (`034bbd09646a589d5eb1f10b740177d628da80fd`):
   `plugins/x86/{x86_disasm.ml,x86_cmpxchg.ml,semantics/x86-64.lisp,patterns/cet.xml}`
   and `lib/x86_cpu/x86_llvm_env.ml`.
9. **`intelxed/xed`** (`0bcb6237345c5066726dcc08b3d87928df3b5b26`):
   `datafiles/` (`110` subdirs including `apx-f`, `cet`, `avx10-1`, `avx10-2`,
   `amx-*`; `1,995` distinct `ICLASS`es, `9,149` blocks, `62` `LOCKABLE` tags).
10. **`digama0/mm0`** (`0d414c0bfdaaeb7fea571895127abc1fa5a3d956`):
    `examples/x86.mm0:391-750` (`decode`, `len l <= 15`) and
    `examples/x86_determ.mm1:1-40, 702-731` (`decode_step`).
11. **`leanprover/LNSym`** (`49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c`,
    `Arm/Util.lean:9`, `Arm/Insts/Common.lean:27, 135-935`, `Arm/Insts/BR/Hints.lean`),
    **`rems-project/sail-arm`** (`5416ef6b43e9527c38dc71fb752259c1d01a47e1`,
    `arm-v9.4-a/lean/ArmExtras.lean`),
    **`riscv/sail-riscv`** (`71dc9c251a82eb3ecf6f271b02b0161ea8345dfd`,
    `model/extensions/cfi/{zicfilp,zicfiss}_{insts,regs}.sail`),
    **`Verified-zkEVM/riscv-zkvm`** (`b878729f3e58629819283635240d021b5f6c21ac`,
    `sail-import/PROVENANCE.toml`), and
    **`joshlf/anneal`** (`c131b320eeeb26ef692e5afd5ec8db49ee518613`,
    `trusted/correspondence/Trusted/Correspondence.lean:2530-2650`,
    `docs/mir-correspondence-design.md:514-625, 1421-1490, 1954-2180`).

### Preserved Runnable Probes and Verified Receipts (`support/`)

| Artifact | Size / Scope | SHA-256 | Verified Result |
| :--- | :--- | :--- | :--- |
| `support/x86_64_encoding_multiplicity_probe.py` | `295` LOC Python 3 stdlib (`gcc` + `objdump` + `llvm-mc`) | `beb5609aa004515d56a7ed7a10e51403261795ad1f1ef93b43dbcfa0e893973e` | Exits `0`; reproduces real `gcc 15.2.0 -O2` `.o` encodings and 34-case `llvm-mc 21.1.8` vs. `objdump 2.47` matrix |
| `support/x86_64_encoding_multiplicity_results.json` | Recorded JSON output of probe execution | `fd8fa41f8d7653baf04d4e05db10dc46385a532dd4744021ae5c47e8fcc57690` | Captures `66 66 2e 0f 1f 84 00 00 00 00 00`, `0f 1e fa` → `cli` bug, silent `#UD`/`#GP` acceptance |
| `support/X86DecodingAndPass2CorrespondenceProbe.lean` | `1,210` LOC standalone Lean `v4.34.1` (`Init.*`-only) | `f213c36b5b2ae4fe300a828ffc51553e7914051e53fe53fe04eb937804c4a4af` | Exits `0` with `-DElab.async=false -Ddebug.skipKernelTC=false`, `0` warnings, `0` `sorry`, `0` `partial`, `0` `opaque` |
| `support/lean_probe_v4_34_1.log` | Kernel `#print axioms` output across all 9 theorems | `f2ad843c219f98c065166e2b23a62a55bf019820e2bf6947304d0367b2f3b6a6` | All 9 theorems depend strictly on subsets of `{propext, Classical.choice, Quot.sound}` (`0` `sorryAx`, `0` `_native` axioms) |

---

## Revalidation

Run both standalone probes from the report package directory:

1. **Revalidate real-compiler x86-64 encoding multiplicity and disassembler `#UD`/`#GP` hazards** (requires `python3`, `gcc`, `objdump`, and `llvm-mc` on `x86_64` Linux; all temporary build files are cleaned up automatically):
   ```bash
   python3 -B support/x86_64_encoding_multiplicity_probe.py
   ```
   Check that `gcc -O2` emits multi-byte alignment NOPs (`0f 1f ...`), `endbr64`
   (`f3 0f 1e fa`), `lock cmpxchg`, and VEX2/VEX3 encodings, and inspect whether
   newer `llvm-mc` or `objdump` releases still accept `f0 48 01 f0` (`#UD`),
   16-byte `nop` (`#GP(0)`), or mis-resynchronize `0f 1e fa`.

2. **Revalidate all 9 Lean `v4.34.1` decoding and Pass-2 correspondence theorems** (zero external dependencies beyond Lean `v4.34.1` `Init.*`):
   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     support/X86DecodingAndPass2CorrespondenceProbe.lean
   ```
   Confirm exit code `0`, zero warnings, and that every `#print axioms` line
   lists only subsets of `[propext, Classical.choice, Quot.sound]`.

3. **Cheap upstream drift checks (without repeating full repository crawls):**
   - `AeneasVerif/kraken`: check whether `Kraken/X64/` adds a machine-code byte
     decoder, `LOCK`/atomic constructors in `Syntax.lean`, or moves off
     `nightly-2026-09-21`.
   - `cslib-community/bignum` and `leanprover/LNSym`: check top-level directory
     listings for any new `X86/` or `X64/` module tree, and check `LNSym/Arm/`
     for removal of `bv_decide` calls in `Arm/Insts/Common.lean`.
   - `acl2/acl2` (`books/projects/x86isa/machine/instructions/endbranch.lisp`):
     diff for CET `TRACKER` state beyond the current NOP stub.
   - `rems-project/sail-tiny-x86`: check `Makefile` for a new `lean` target.
