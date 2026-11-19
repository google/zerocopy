# Trusting Trust, Bootstrappable Builds, and Verified Binary Lifting as a Legacy FFI Substrate

## Summary

End-to-end software verification faces two irreducible epistemic boundaries at opposite ends of a binary's lifecycle: (1) **the bootstrap root of trust** beneath the compiler and proof checker that produced the executable, and (2) **the adoption of source-less legacy binaries** linked across an FFI boundary. Every formal theorem proved about source code or checked by a proof assistant rests on executing compiled binaries — compiler, assembler, linker, proof kernel, OS — and every call into a precompiled foreign library executes machine code whose ABI, stack discipline, and memory safety are unverified unless lifted, translated, or isolated.

Five concrete findings anchor engineering practice across these two domains:

1. **Bootstrap trust cannot be eliminated, only shrunk to auditable seeds and diversified via threshold checks.** Thompson's self-reproducing compiler trojan (CACM 1984) is a fixed point where clean source produces backdoored binaries forever. Wheeler's Diverse Double-Compiling (DDC; ACSAC 2005 / PhD 2009) detects trojans by comparing $c(s_A, c(s_A, c_T))$ against $c(s_A, c_A)$, converting single-compiler trust into a threshold assumption ("at least one of two genuinely independent compilers is clean") — provided compilation is bit-for-bit deterministic and $s_A$'s semantics are implementation-independent. Direct inspection of `thepowersgang/mrustc@4e020d6b` (`TestRustcBootstrap.sh`) confirms an operational stage-3 DDC gate for Rust: building `rustc 1.91.1` from `mrustc`-compiled `rustc 1.90.0` vs. the official `rustc 1.90.0` binary and verifying bit-identity via `diff -qs` over normalized tarballs.
2. **Full-source distribution bootstrapping collapses opaque binary seeds to ~181–357 bytes, while shifting residual trust to the build driver, kernel, and historical C sources.** Executable verification (`Probe 2A`) directly confirmed that assembling `oriansj/stage0-posix-x86@14721630:hex0_x86.hex0` (155 lines) yields the exact 181-byte `POSIX/x86/hex0-seed` binary (`SHA-256 f74dcf9c...`), and assembling `oriansj/stage0-posix-amd64@15535f88:hex0_AMD64.hex0` (152 lines) yields the exact 229-byte `POSIX/AMD64/hex0-seed` binary (`SHA-256 66c95985...`: 120 bytes of ELF64+PHDR headers + 109 bytes of x86-64 machine code invoking only Linux `open`, `read`, `write`, `exit`). GNU Guix's April 2023 full-source bootstrap roots >22,000 packages in a 357-byte seed via `stage0-posix` -> `M2-Planet` -> `GNU Mes 0.24.2` -> `TinyCC` -> `GCC`, while explicitly retaining a ~25 MiB static `bootstrap-guile-2.0.9` build driver and Linux kernel in its residual TCB.
3. **Proof assistants carry hidden bootstrap seeds of their own; only in-logic bootstrapping (`CakeML`) or tiny independent proof checkers (`MM0`, `Lean4Lean`) break the cycle.** Direct inspection of `leanprover/lean4@01716786` (`doc/dev/bootstrap.md`) confirms Lean 4 breaks its self-hosting cycle using pre-generated C files checked into `stage0/src/`, explicitly describing Stage 0 as equivalent to a downloaded bootstrap binary. By contrast, `CakeML/cakeml@2874b664` evaluates its verified compiler inside HOL4 (`backendProofScript.sml`, `compile_correct_eval`) to emit machine bytes together with a refinement theorem `machine_sem mc ffi ms ⊆ extend_with_resource_limit (semantics_prog ...)`, shifting trust from any external compiler binary to the HOL4 kernel, ISA model, loader, and the FFI oracle (`semantics/ffi/ffiScript.sml`).
4. **Recovering CFGs and types from stripped binaries is undecidable in general, separating heuristic lifters (`rev.ng`, `Ddisasm`) from translation-validated lifters (`FoxDec`).** Disassembly of interleaved code/data is halting-problem equivalent (Horspool & Marovac 1980), and heuristic type recovery (`WYSINWYX`, `TIE`, `Retypd`, `rev.ng` `AnalyzeDataLayout`) cannot prove byte validity or pointer ownership. `FoxDec` (`ssrg-vt/FoxDec@d9206efe`, PLDI 2022, CCS 2024) avoids trusting its lifter by constructing an over-approximative **Hoare Graph** (scaling near-linearly up to Xen's ~450K instructions) and exporting per-instruction Hoare triples to Isabelle/HOL, discharging a **minimal FFI ABI contract** (return-address integrity, bounded control flow, System V AMD64 calling-convention adherence) and producing symbolized, patchable NASM — restricted to sequential C-compiled x86-64 ELF binaries.
5. **Adopting arbitrary source-less binaries safely requires a four-rung graded ladder anchored on authoritative ISA semantics and `tainted<T>` validation.** Hand-written lifters disagree semantically (`MeanDiff` ASE 2017; Dasgupta PLDI 2019/2020), motivating vendor-derived authoritative ISA models (`Sail` POPL 2019 -> `Isla` -> `Islaris` PLDI 2022 Coq/Iris verification of ARMv8-A/RISC-V machine code). Binaries that cannot be lifted and proved step down a sound hierarchy: verified lifting (`FoxDec`/`Islaris`) -> weak-memory-preserving translation (`Lasagne` PLDI 2022 / `Risotto` ASPLOS 2023) -> SFI/Wasm sandboxing behind enforced `tainted<T>` validators (`RLBox` `copy_and_verify`, `VeriWasm` NDSS 2021) -> process/hardware isolation.

## Applicability

This report covers two coupled engineering subsystems pinned to exact upstream revisions observed on `2026-11-19`:

- **Compiler & Proof-Checker Bootstrapping (`oriansj/bootstrap-seeds@cedec6b8`, `oriansj/stage0-posix@64359804`, `oriansj/stage0-posix-{x86,amd64}`, `oriansj/M2-Planet@ebfecc2f`, `fosslinux/live-bootstrap@a49273cb`, `thepowersgang/mrustc@4e020d6b`, `CakeML/cakeml@2874b664`, `leanprover/lean4@01716786`, `digama0/lean4lean@67f63b0c`, `digama0/mm0@0d414c0b`, `Ekdohibs/camlboot@2692b14a`, `golang/go@c19c4c56` [v1.21.0]):** Applies to POSIX/Linux `x86` (i386), `x86-64` (`AMD64`), `AArch64`, and `riscv64` user-space bootstrap pipelines, compiler self-hosting chains, and proof-checker TCB minimization. Sub-ISA physical hardware, silicon fabrication, and boot-firmware roots of trust are bounded explicitly as the base case below the software seed.
- **Binary Lifting, Disassembly, ISA Semantics, and Sandboxed Legacy FFI (`ssrg-vt/FoxDec@d9206efe`, `revng/revng@5afe5310`, `rems-project/islaris@c978e10f`, `rems-project/sail@97aa617d`, `GrammaTech/ddisasm@f8b63ee2`, `PLSysSec/rlbox_sandboxing_api@b0157dc8`):** Applies to stripped and position-independent ELF binaries on `x86-64` (System V AMD64 ABI), `AArch64`, and `RISC-V`. FoxDec findings apply strictly to sequential C-compiled x86-64 ELF binaries (explicitly excluding C++ exceptions/RTTI and concurrent code). Islaris findings apply to `AArch64` and `RISC-V` code fragments verifiable against Sail/Isla symbolic traces.
- **Executable Micro-Probes:** Python 3.13.15 + GNU `objdump` probes executed on Linux x86-64 directly validate the bit-exact fixed point between upstream `.hex0` sources and upstream `hex0-seed` ELF binaries, verify exact x86-64 instruction/syscall footprints of `POSIX/AMD64/hex0-seed`, and model Wheeler's DDC detection and failure regimes.

Do not generalize `mrustc` bit-identity results to `rustc` versions outside its explicitly tested release list (`1.19.0`, `1.29.0`, `1.39.0`, `1.54.0`, `1.74.0`, `1.90.0` -> `1.91.1`) or generalize `FoxDec`'s Isabelle/HOL soundness guarantees to heuristic decompilers or non-C binaries without independent proof checking.

## Findings

### 1. The Self-Reproducing Compiler Trojan and Real-World Build-Chain Attacks

Basis: normative (Thompson CACM 1984, `10.1145/358198.358210`) + documentation (Karger & Schell 1974; Cox 2023; Goregaokar 2016; CVE-2024-3094)

Ken Thompson's 1984 Turing Award lecture (*Reflections on Trusting Trust*, CACM 27(8), `10.1145/358198.358210`, building on Karger and Schell's 1974 Multics security evaluation) demonstrated an irreducible limitation of source-only auditing through a three-step construction:

1. **Quine (self-reproduction):** A program that prints its own exact source text.
2. **Compiler memory (bootstrap persistence):** Teaching a self-hosted compiler a rule (e.g., interpreting `'\v'` as ASCII `11`) and then removing the hard-coded constant from the compiler's source; the fact survives solely inside the compiled compiler binary across all future self-compilations.
3. **Self-perpetuating trojan fixed point:** Inserting two pattern-matching triggers into the compiler binary — one recognizing the target program (`login`) to inject a backdoor, and one recognizing the compiler's own source (`compile()`) to re-inject *both* triggers — and then deleting the trojan from the source repository. No subsequent inspection of the source code can reveal the backdoor.

Russ Cox (2023) retrieved and executed Thompson's historical PDP-11 C compiler binary to confirm the mechanism empirically, and Manish Goregaokar (2016, *Reflections on Rusting Trust*) demonstrated the analogous self-reproducing attack for `rustc`. Real-world supply-chain incidents instantiate distinct points along the build-trust chain, revealing which countermeasures catch which attack class:

| Incident (Year) | Injection Point in Build Graph | Caught by Source Audit? | Caught by Reproducible Builds (Same Toolchain)? | Caught by Diverse Double-Compiling (DDC)? | Caught by Full-Source Bootstrap (From VCS)? |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Thompson Trojan** (1984) | Self-hosted compiler binary (`cc` / `rustc` stage0) | No (absent from source) | No (poisoned binary reproduces its own backdoor) | **Yes** (if diverse compiler $c_T$ is clean) | **Yes** (eliminates opaque stage0 binary) |
| **Win32/Induc** (2009) | Mutated Delphi runtime source file (`SysConst.pas`) compiled into `.dcu` | Yes (if runtime diffed) | Yes (diff vs clean build) | Yes (if clean sources used) | Yes |
| **XcodeGhost** (2015) | Counterfeit repackaged Xcode toolchain + modified static library | No (developer source clean) | **Yes** (independent rebuild with genuine Xcode diverges) | **Yes** | **Yes** |
| **SUNSPOT / SolarWinds** (2020) | Build-host daemon swapping a source file in flight during MSBuild compilation | No (VCS clean) | **Yes** (independent clean build diverges) | **Yes** | **Yes** |
| **xz / liblzma** (`CVE-2024-3094`, 2024) | Malicious `m4`/test payload injected into **release tarballs** (`5.6.0`/`5.6.1`) absent from Git tags | No (if auditing Git only); Yes (if auditing tarball vs Git) | No (if rebuilding from the poisoned release tarball) | No (if both compilers consume the poisoned tarball) | **Yes** — *only* if policy forbids pre-generated release tarballs and builds strictly from VCS source |

**Verification clash:** Every formal proof of a compiler (such as CompCert or a Lean/Coq verification proof) proves a theorem about the compiler's *source representation*, checked by an executable proof-checker binary. If either the compiler binary used to build the target or the proof-checker binary used to check the theorem carries a Thompson trojan, or if a build script/proc-macro executes unvetted native code during compilation, the formal guarantee collapses at the execution layer.

### 2. Diverse Double-Compiling (DDC): Formal Assumptions, Failure Modes, and Rust's `mrustc` Gate

Basis: normative (Wheeler ACSAC 2005 / PhD 2009) + source (`thepowersgang/mrustc@4e020d6b`, `README.md` & `TestRustcBootstrap.sh`) + execution (Probe 2B)

David A. Wheeler (ACSAC 2005; PhD dissertation, George Mason University, 2009) formalized **Diverse Double-Compiling (DDC)** to verify that an untrusted compiler executable $c_A$ corresponds faithfully to its claimed source $s_A$.

#### Formal DDC Protocol and Preconditions

Let $c(s, x)$ denote compiling source $s$ using compiler executable $x$, and let $c_T$ be a second, independent ("trusted") compiler capable of compiling $s_A$:

1. **Stage 1:** Compile $s_A$ with the diverse compiler $c_T$: $\text{stage}_1 := c(s_A, c_T)$.
2. **Stage 2:** Compile $s_A$ with $\text{stage}_1$: $\text{stage}_2 := c(s_A, \text{stage}_1)$.
3. **Reference self-compile:** Compile $s_A$ with the suspect binary $c_A$: $\text{ref} := c(s_A, c_A)$.
4. **Comparison:** Check bit-for-bit equality $\text{stage}_2 \stackrel{?}{=} \text{ref}$ (or $\text{stage}_2 \stackrel{?}{=} c_A$ if $c_A$ is already a fixed point $c(s_A, c_A) = c_A$).

Wheeler proved (and empirically demonstrated up to GCC) that $\text{stage}_2 = \text{ref}$ establishes correspondence between $c_A$ and $s_A$ **modulo four strict preconditions**:
- **(P1) Determinism / Reproducibility:** Compiling identical source $s_A$ with functionally equivalent compilers must produce bit-identical outputs (no timestamps, path leaks, ASLR-dependent hash ordering, or parallel race nondeterminism).
- **(P2) Genuine Independence:** $c_T$ (and its execution environment: OS, libc, assembler, linker, CPU) must not share the same Thompson trojan as $c_A$. DDC converts "trust $c_A$" into the monotone threshold formula $\text{Honest}(c_A) \lor \text{Honest}(c_T)$, never into zero trust.
- **(P3) Implementation-Independent Semantics of $s_A$:** $s_A$ must not rely on undefined or implementation-defined behavior where $c_T$ and $c_A$ legitimately diverge in semantics (a language-design constraint on self-hosting compilers).
- **(P4) Existence of a Second Implementation:** A genuinely independent compiler $c_T$ for the language of $s_A$ must exist and remain maintained as the language evolves.

Executable **Probe 2B** (`probe_p2_bootstrap.py`) verified all four regimes mechanically: (1) clean $c_A$ + clean $c_T$ yields `match=True`; (2) Thompson-trojaned $c_A$ + clean $c_T$ yields `match=False` (`stage2` recovers the clean compiler binary while `c_A_out` retains `trojan=THOMPSON_84`); (3) a correlated trojan present in *both* $c_A$ and $c_T$ (violating P2) yields a silent false negative (`match=True`); and (4) non-deterministic build timestamps (violating P1) yield a false positive (`match=False`) even when both compilers are clean.

#### Primary-Source Audit of `mrustc`'s Rust DDC Verification (`thepowersgang/mrustc@4e020d6b`)

Rust's official `rustc` build downloads a prebuilt prior-release `stage0` binary. `mrustc` — an independent C++14 implementation of Rust that assumes its input is valid Rust (omitting borrow checking) and lowers Rust to C compiled by `gcc` — provides the second compiler needed for DDC. Direct inspection of `thepowersgang/mrustc@4e020d6b` (`README.md` lines 16–30 and `TestRustcBootstrap.sh` lines 1–104) establishes exactly what "binary-equal" verifies:

- **Supported bootstrap targets (`README.md`, L18–L20):** Tested to bootstrap `rustc 1.90.0` yielding a **binary-equal `rustc 1.91.1`** (and also supports `1.19.0`, `1.29.0`, `1.39.0`, `1.54.0`, `1.74.0`; `1.19.0` is noted as not fully repeatable, whereas later versions are).
- **Exact stage-3 comparison script (`TestRustcBootstrap.sh`, L44–L104):**
  1. Builds `stage0` `rustc` (`1.90.0`) and `cargo` via `mrustc` + `minicargo`.
  2. Runs `./x.py build --stage 3` on `rustc-1.91.1-src.tar.gz` (`full-bootstrap = true`, `vendor = true`, `extended = true`, `download-ci-llvm = false`) using the `mrustc`-built `1.90.0` tools.
  3. Copies `build/<target>/stage3` and `stage3-tools-bin/*`, strips `lib/rustlib/{src,rustc-src}`, and archives deterministically with `tar --mtime="@0" --sort=name -czf mrustc.tar.gz`.
  4. Runs an identical `./x.py build --stage 3` using the **official downloaded** `stage0` `rustc 1.90.0`, archiving `official.tar.gz` identically.
  5. Compares bit-for-bit via **`diff -qs mrustc.tar.gz official.tar.gz`**.
- **Residual shared TCB (P2 boundary):** Because both runs execute inside the same host environment and compile LLVM and `mrustc` using the same host `gcc`/C++ toolchain, libc, linker, Linux kernel, and `rustc-1.91.1-src.tar.gz` tarball, `TestRustcBootstrap.sh` specifically eliminates trust in the **downloaded `stage0` Rust compiler binary** (`1.90.0`), while leaving the C/C++ host toolchain and source tarball in the shared TCB until paired with a full-source C bootstrap.

### 3. Minimal Binary Seeds and Full-Source Distribution Bootstrapping (`stage0`, `GNU Mes`, `Guix`, `live-bootstrap`)

Basis: source (`oriansj/bootstrap-seeds@cedec6b8`, `oriansj/stage0-posix-{x86,amd64}`, `fosslinux/live-bootstrap@a49273cb`) + documentation (GNU Guix April 2023 blog) + execution (Probe 2A)

The Bootstrappable Builds movement eliminates large opaque compiler blobs by starting from a human-auditable binary seed (`hex0`) that reads commented ASCII hexadecimal text (stripping `;` and `#` comments to end-of-line and whitespace) and emits raw binary bytes.

#### Pinned Upstream Binary Seeds and Live Fixed-Point Verification (Probe 2A)

Direct download, SHA-256 measurement, and execution against `oriansj/bootstrap-seeds@cedec6b8066d1db229b6c77d42d120a23c6980ed` and `oriansj/stage0-posix-{x86,amd64}` establish exact seed sizes and cryptographic identity:

| Upstream Artifact (`oriansj/bootstrap-seeds@cedec6b8`) | Size (Bytes) | Exact SHA-256 Digest | Verified Source Fixed Point (`Probe 2A`) |
| :--- | ---: | :--- | :--- |
| `POSIX/x86/hex0-seed` | **181** | `f74dcf9cef2aee9eb7723eca755849d474fccd89662947021d1aa08429d23c13` | Bit-for-bit equal to assembling `oriansj/stage0-posix-x86@14721630:hex0_x86.hex0` (155 lines); ELF32 (`e_machine=0x3`, `e_entry=0x804804c`, overlapping `e_phoff=0x2c`) |
| `POSIX/AMD64/hex0-seed` | **229** | `66c95985e668f20f2465c2b876f83fef066fd7c8c2dd3adb51a969f2d7120c8b` | Bit-for-bit equal to assembling `oriansj/stage0-posix-amd64@15535f88:hex0_AMD64.hex0` (152 lines); ELF64 (`e_machine=0x3e`, `e_entry=0x600078`, `e_phoff=0x40`) |
| `POSIX/riscv64/hex0-seed` | **392** | `1b50ceef632b83b79aef0cf91d60bc0cb242a3b2bfba22cb5115d80112b50ac9` | Seed binary inspected & hashed (source assembly not executed in Probe 2A) |
| `POSIX/AArch64/hex0-seed` | **526** | `8ca9745e20af3f0d6037684cbc3ec3789c205d86ccecf43f77d0aeabf16050b4` | Seed binary inspected & hashed (source assembly not executed in Probe 2A) |
| `POSIX/AMD64/kaem-optional-seed` | **618** | `153b8915b73bd07132b59538d10fe53d26578eb160a67db72af07aaa61c51b3b` | Optional minimal script runner (replaceable by any shell per `bootstrap-seeds/README.md`) |
| `POSIX/x86/kaem-optional-seed` | **632** | `545f89537f070d7e62b05243be34cbcfdb1e92dbf9d82e2cd15792d880436ac2` | Optional minimal x86 script runner |

Disassembling `POSIX/AMD64/hex0-seed` from `0x78` (`objdump -D -b binary -m i386:x86-64 --start-address=0x78`) confirms that the entire executable consists of **120 bytes of ELF64 + Program Header** (`0x00..0x77`) plus **109 bytes of x86-64 machine code** (`0x78..0xe4`) invoking only four Linux syscalls: `open` (`rax=2`) for input and output paths, `read` (`rax=0`) 1 byte at a time, `write` (`rax=1`) upon completing each nibble pair, and `exit(0)` (`rax=0x3c`) on EOF, while skipping `#` (`0x23`) and `;` (`0x3b`) comments to `\n` (`0x0a`). Every byte is auditable by hand in minutes.

#### The Full-Source Bootstrap Ladder and Its Residual TCB

Starting from `hex0-seed`, `stage0-posix` climbs a self-bootstrapping tower of increasingly expressive languages:
```text
hex0-seed (181B x86 / 229B AMD64; 357B in Guix 2023)
  -> hex0 -> hex1 (1-char labels) -> catm -> hex2 (arbitrary labels & ELF relocations)
  -> M0 (macro assembler) -> cc_x86 (minimal C subset) -> M1 -> M2 -> blood-elf / get_machine
  -> M2-Planet (bootstrappable C compiler, oriansj/M2-Planet)
  -> GNU Mes 0.24.2 (Scheme interpreter + MesCC C compiler written in Scheme)
  -> TinyCC (tcc-boot 0.9.27 -> bootstrappable-tcc 0.9.26+31 patches)
  -> gzip-mesboot (1.2.4) + gnu-make-mesboot0 (3.80) + patch-mesboot (2.5.9)
  -> binutils-mesboot (2.20.1a) + glibc-mesboot (2.2.5) + gcc-core-mesboot (2.95.3)
  -> gcc-mesboot (4.9.4) -> modern GCC / glibc / binutils -> >22,000 Guix packages
```

Primary-source inspection of GNU Guix's April 2023 announcement (*The Full-Source Bootstrap: Building from source all the way down*) and `fosslinux/live-bootstrap@a49273cb` reveals the exact trade-offs:
- **Residual binary TCB in Guix:** Guix's graph explicitly retains a statically linked **`bootstrap-guile-2.0.9` binary (~25 MiB)** used as the package-graph build driver (to evaluate Guile build recipes) plus the **host Linux kernel**. `fosslinux/live-bootstrap` attacks the build-driver dependency directly by bootstrapping directly inside a minimal `stage0-posix` / `kaem` environment (even supporting a bare-metal builder kernel path).
- **Conservation of audit burden:** Shrinking the binary seed from ~250 MiB to 181 bytes does not eliminate trust — it shifts the audit obligation from unauditable binary blobs to **tens of megabytes of historical C/Scheme source code** (Mes, TinyCC, GCC 2.95.3, glibc 2.2.5) and requires every intermediate source archive to be free of pre-generated artifacts (`configure`, Bison parsers, lexers) that could harbor `CVE-2024-3094`-style tarball backdoors.
- **Cross-distribution reproducibility check:** In 2019, independent builds across Guix, Nix, and Debian produced a bit-identical GNU Mes binary — functioning as a cross-environment check on the intermediate chain.

### 4. Per-Language Self-Hosting Chains, Proof-Assistant Seeds, and In-Logic Bootstrapping

Basis: source (`CakeML/cakeml@2874b664`, `leanprover/lean4@01716786`, `digama0/lean4lean@67f63b0c`, `digama0/mm0@0d414c0b`, `Ekdohibs/camlboot@2692b14a`, `thepowersgang/mrustc@4e020d6b`, `golang/go@c19c4c56`) + normative (POPL 2014, PLDI 2019, POPL 2020, CICM 2020, ITP 2022)

A polyglot system linking $N$ languages inherits the **union** of their bootstrap TCBs. Self-hosting compilers and proof assistants exhibit sharply different bootstrap postures:

| Language / Prover | Standard Bootstrap Seed | From-Source / Diverse Path | Bit-for-Bit Reproducibility / DDC Status | Residual Software TCB |
| :--- | :--- | :--- | :--- | :--- |
| **C / GCC** | Host C/C++ compiler | `hex0` (181B/229B) -> `M2-Planet` -> `Mes` -> `TinyCC` -> `GCC 2.95.3` -> `4.9.4` -> modern GCC | Reproducible across Guix/Nix/Debian at Mes; Wheeler demonstrated DDC on GCC | Seed bytes, kernel, historical C/Scheme sources (+ Guile driver in Guix) |
| **Rust (`rustc`)** | Downloaded official `N-1` `rustc` + `cargo` binary | `thepowersgang/mrustc` (C++14 -> C -> `gcc`) builds `rustc 1.90.0` (or `1.19`..`1.74`) | `TestRustcBootstrap.sh` checks stage-3 `rustc 1.91.1` bit-identical (`diff -qs`) against official `stage0` | Host C/C++ compiler (`gcc`), linker, libc, LLVM source, `rustc` source tarball |
| **Go (`go1.21.0+`)** | Prior Go toolchain binary (Go 1.4 C-based historical root) | `golang/go@c19c4c56` (`go1.21.0`): first perfectly reproducible Go toolchain (`go.dev/blog/rebuild`) | Anyone can rebuild and verify official/distro binaries (e.g., Ubuntu Go 1.21.0) bit-for-bit | Prior Go bootstrap binary (or chain from C-compiled Go 1.4) + host OS |
| **OCaml** | Bundled `boot/ocamlc` bytecode binary in OCaml repo | `Ekdohibs/camlboot@2692b14a` (Courant, Lepiller, Scherer, ‹Programming› 2022): Guile-hosted `miniml` compiler + OCaml interpreter + handwritten lexer | Produces bytecode bit-for-bit compatible with OCaml's bundled bootstrap compiler (~4h wall / 16h CPU on 8 cores) | Host C compiler (`gcc`) + GNU Guile + OCaml runtime C source |
| **Lean 4** | Pre-generated C files checked into repo (`stage0/src/`) | `leanprover/lean4@01716786` (`doc/dev/bootstrap.md`): `stage0` C -> `stage1` -> `stage2` (fixed point checked at `stage3`) | `stage3 == stage2` sanity check; `stage0/src/` explicitly documented as equivalent to a downloaded bootstrap binary | Checked-in `stage0/src/*.c`, C++ runtime/kernel (`src/`), host C++ compiler; mitigated by independent checkers (`Lean4Lean`) |
| **CakeML** | **In-logic HOL4 evaluation** (zero external ML compiler binary in loop) | `CakeML/cakeml@2874b664` evaluates verified compiler AST on itself inside HOL4 to emit x64/ARM/RISC-V machine code | Produces machine bytes + machine-checked theorem in one kernel run (`x64Bootstrap`) | HOL4 proof kernel + Poly/ML runtime running HOL4, ISA model, OS loader, unverified C FFI stubs |
| **Metamath Zero (`MM0`)** | `mm0-c` (<3,000 LoC C reference verifier) | `digama0/mm0@0d414c0b`: separate untrusted elaborator (`mm0-rs`) emitting `.mmb` checked by `mm0-c`; `examples/verifier.mm0` targets verified x86-64 verifier | Checking `.mmb` runs at near-I/O speed; independent verifier re-implementations trivial | `mm0-c` + host C compiler (until self-verified x86-64 verifier closes loop) |
| **Coq / Rocq (`MetaCoq`)** | OCaml compiler + Coq kernel | `MetaCoq/metacoq@51b14e4b` (*Coq Coq Correct!*, POPL 2020, `10.1145/3371076`): verifies type checking & erasure of Coq in Coq | Certified extraction via OCaml (or CertiCoq) still crosses extraction/compiler trust boundary | Coq kernel + OCaml bootstrap chain (`Camlboot` can reduce OCaml seed) |

#### CakeML's In-Logic Bootstrap Theorem and FFI Oracle Boundary

Direct inspection of `CakeML/cakeml@2874b664` clarifies both the power and exact residual TCB of in-logic bootstrapping (Kumar, Myreen, Norrish, Owens, POPL 2014, `10.1145/2535838.2535841`; Tan et al., JFP 2019; Myreen, CPP 2021):

- **End-to-end refinement theorem (`compiler/backend/proofs/backendProofScript.sml`, lines 5048–5061):**
  ```sml
  Theorem compile_correct_eval:
    compile asm_conf c prog = SOME (bytes,bitmaps,c') ⇒
     let (s0,env) = THE (prim_sem_env (ffi: 'ffi ffi_state)) in
     ¬semantics_prog (add_eval_state ev s0) env prog Fail ∧ backend_config_ok asm_conf c ∧
     lab_to_targetProof$mc_conf_ok (mc:('a,'b,'c) machine_config) ∧ mc_init_ok asm_conf c mc ∧ ... ∧
     installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names
       (heap_regs c.stack_conf.reg_names) mc c'.lab_conf.shmem_extra ms ⇒
       machine_sem mc ffi ms ⊆
         extend_with_resource_limit
           (semantics_prog (add_eval_state ev s0) env prog)
  ```
  Evaluating `compile` on CakeML's own compiler AST inside HOL4 emits concrete machine `bytes` *together* with a HOL4 theorem proving those exact bytes implement the compiler (modulo hardware out-of-memory `extend_with_resource_limit`). Lööw et al. (`Silver`, PLDI 2019, `10.1145/3314221.3314631`) extended this chain onto a formally verified processor, and Abrahamsson et al. (`Candle`, ITP 2022) built a verified HOL Light theorem prover running on CakeML (following Milawa on Jitawa by Davis & Myreen).
- **Exact FFI oracle assumption (`semantics/ffi/ffiScript.sml`, lines 20–95):** CakeML models all external I/O and C foreign calls via an abstract `oracle : ffiname -> 'ffi -> word8 list -> word8 list -> 'ffi oracle_result` (`call_FFI_def`), where `ffiname = ExtCall mlstring | SharedMem shmem_op` (`MappedRead | MappedWrite`) and returning a mutated byte array of mismatched length transitions to `FFI_final (Final_event ... FFI_failed)`. The C FFI stubs implementing those `ExtCall`s sit *outside* the HOL4 proof — if the external OS or C library violates the assumed `oracle` contract, the machine-code theorem inherits the exact adversarial-FFI boundary problem of untrusted OS/C callees.

#### Who Checks the Checker: De Bruijn Criterion and Independent Kernels

By Gödel's second incompleteness theorem, no proof checker can certify its own soundness unconditionally. Checking proof terms with **multiple independent small kernels** written in different languages and compiled via distinct bootstrap chains is the proof-checking analogue of Wheeler's DDC:
- **`Lean4Lean` (`digama0/lean4lean@67f63b0c`, Carneiro):** Re-implements the Lean 4 kernel (`Environment.lean`, `TypeChecker.lean`, `Inductive/`, `Quot.lean`) inside Lean itself alongside a formalized metatheory (`Theory/VExpr.lean`, `VEnv.lean`, `Typing/`), providing an independent checker separated from Lean 4's C++ kernel.
- **`Metamath Zero` (`digama0/mm0@0d414c0b`, Carneiro, CICM 2020, `10.1007/978-3-030-53518-6_5`):** Separates human-readable `.mm0` specs from untrusted `.mmb` proof streams verified by `mm0-c` (<3,000 lines of C), targeting full self-verification (`examples/verifier.mm0`) down to x86-64 machine code.
- **Zero-knowledge proof checking (`zkPi`, Laufer, Ozdemir, Boneh, 2024):** Demonstrates generating succinct ZK proofs that a Lean theorem passed type-checking, enabling remote parties to verify *that* a check occurred without trusting a remote server's execution environment.

### 5. Reproducible Builds as the Hinge Between Trusting Trust and Attestation

Basis: documentation (Lamb & Zacchiroli IEEE Software 2022; Russ Cox `go.dev/blog/rebuild`, Go 1.21.0) + derived

Reproducible builds — where independent builders reconstruct bit-identical artifacts from identical explicitly declared inputs — play a dual structural role:
1. **Equality oracle for DDC:** Without deterministic outputs, Wheeler's check $\text{stage}_2 = \text{ref}$ suffers false positives (Probe 2B Case 4), making compiler-trojan detection indistinguishable from timestamp noise.
2. **Measurement bridge for remote attestation:** Hardware TEEs measure loaded binary bytes (`MRENCLAVE`, `MR_TD`, `MEASUREMENT`, `RIM`). Only when compilation, linking, and image assembly are pure functions of content-addressed inputs can an offline measurement calculator derive the expected hardware measurement from source and formal proofs.

Russ Cox's primary analysis for Go 1.21.0 (`go.dev/blog/rebuild`, `golang/go@c19c4c56`) cleanly partitions build inputs into **relevant inputs** (source revision, dependency versions, target OS/arch, compiler version/flags) and **unintentional inputs** that destroy reproducibility: filesystem mtimes embedded in `tar`/`zip` archives (fixed via `--mtime="@0"` or source-derived epochs), build directory paths embedded in DWARF/debug info (`-trimpath`), host `uid`/`gid`/usernames in archive headers, parallel build ordering, and non-deterministic map iteration. Eliminating unintentional inputs is necessary but not sufficient for trust: reproducibility proves that *two parties got the same bytes from the same inputs*, not that the inputs were clean (`CVE-2024-3094`) or that the compiler wasn't identically trojaned on both hosts.

### 6. Undecidability of Disassembly, Symbolization, and Type/Layout Recovery

Basis: normative (Horspool & Marovac 1980; Pang et al. S&P 2021 `10.48550/arXiv.2007.14266`; Balakrishnan & Reps TOPLAS 2010 `10.1145/1838212.1838215`; Noonan et al. PLDI 2016 `10.1145/2908080.2908083`) + source (`revng/revng@5afe5310`, `GrammaTech/ddisasm@f8b63ee2`)

When adopting a source-less legacy binary across an FFI boundary, four fundamental recovery problems arise before any verification or recompilation can begin:

1. **Code-vs.-data separation and CFG recovery:** Horspool and Marovac (1980) proved that distinguishing executable instructions from inline data in general binaries reduces to the halting problem. Variable-length x86-64 encodings, jump tables embedded in `.text`/`.rodata`, tail calls, indirect branches (`jmp *%rax`), non-returning functions (`exit`, `abort`), and hand-written assembly defeat purely syntactic sweeps. Pang et al. (*SoK: All You Ever Wanted to Know About x86/x64 Binary Disassembly*, IEEE S&P 2021, `10.48550/arXiv.2007.14266`) systematized 9 disassemblers across compilers and optimization levels, demonstrating that function-start identification and indirect-jump target resolution remain error-prone whenever debug/unwinding/relocation metadata is stripped.
2. **Symbolization (reassembleable disassembly):** Patching or re-laying out a binary requires replacing raw numeric addresses with symbolic labels so relocated code and data references remain valid. A single mis-symbolized integer constant (mistaking `0x401200` the literal integer for a pointer, or failing to symbolize a computed jump-table address) causes silent runtime miscompilation. Approaches span:
   - Heuristic/static reassembly (`Uroboros`, Wang, Wang, Wu, USENIX Security 2015);
   - Weighted Datalog inference (`Ddisasm`, Flores-Montoya & Schulte, USENIX Security 2020, `GrammaTech/ddisasm@f8b63ee2`);
   - Relocation-driven exact lifting (`Egalito`, Williams-King et al., ASPLOS 2020, `10.1145/3373376.3378470`), showing that position-independent executables (PIEs) retaining relocation metadata turn heuristic guessing into near-exact parsing;
   - Dynamic trace-based lifting (`BinRec`, Altinay et al., EuroSys 2020), trading completeness for execution fidelity.
3. **Unified multi-architecture lifting and Data Layout Analysis (`rev.ng`):** Di Federico, Payer, and Agosta (`rev.ng`, ACM CC 2017, `10.1145/3033019.3033028`; `revng/revng@5afe5310`) avoid hand-writing per-ISA semantics by reusing QEMU's Tiny Code Generator (TCG) front ends to lift arbitrary architectures (x86-64, AArch64, ARM, MIPS, RISC-V, s390x) into LLVM IR, recovering CFGs and function boundaries via combined dataflow analysis, followed by interprocedural **Data Layout Analysis** (`include/revng/DataLayoutAnalysis/DLA.h`: `revng::pypeline::analyses::AnalyzeDataLayout`) to reconstruct C `struct`/`union`/array field offsets and `Clift` (MLIR dialect) for C decompilation.
4. **Irreducible limits of type and ABI recovery:** Balakrishnan and Reps (`WYSINWYX`, ACM TOPLAS 2010, `10.1145/1838212.1838215`) established via Value-Set Analysis (VSA) that source-level invariants often fail at the binary level due to compiler optimizations, dead-store elimination, and stack-slot reuse. Constraint-based type inference (`TIE`, Lee, Avgerinos, Brumley, NDSS 2011; `Retypd`, Noonan, Loginov, Cok, PLDI 2016, `10.1145/2908080.2908083`, inferring polymorphic and recursive machine-code types) can propose *a* consistent typing, never uniquely reconstruct the original source types. Critically for memory-safe FFI (and zero-copy byte-level casts):
   - Recovered layouts cannot determine **padding-byte initialization** or **value-validity invariants** (e.g., valid enum discriminants, non-null invariants, UTF-8 invariants);
   - **Ownership and lifetime** ("who frees this pointer?", "is this borrow exclusive or aliased?") are erased entirely from machine bytes;
   - Whole-program LTO / interprocedural register allocation can invent custom internal calling conventions outside the System V AMD64 ABI document.

### 7. Formally Verified Binary Lifting and Authoritative ISA Semantics (`FoxDec`, `Sail`, `Isla`, `Islaris`)

Basis: source (`ssrg-vt/FoxDec@d9206efe`, `rems-project/islaris@c978e10f`, `rems-project/sail@97aa617d`) + normative (PLDI 2013, POPL 2019, PLDI 2019, PLDI 2020, PLDI 2022, CCS 2024)

Because heuristic lifters cannot be trusted to justify FFI soundness, formal binary lifting separates **untrusted analysis/lifting** from **machine-checked verification** against a formal ISA semantics.

#### Comparison of Binary Lifting & Machine-Code Verification Stacks

| System / Stack | Target ISAs | Formal ISA Model Provenance | What Is Proved (Checked) | What Remains Heuristic / Assumed | Documented Scale & Limits |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`FoxDec`** (`ssrg-vt/FoxDec@d9206efe`; PLDI 2022, CCS 2024) | x86-64 (System V ELF) | Formal x86-64 semantics in Isabelle/HOL (evolving with `Chum` / `libLISA`) | Over-approximative **Hoare Graph**; return-address integrity, bounded CFG, calling-convention adherence; symbolized NASM semantic equivalence (CCS 2024) | Unresolvable indirect jumps/memory aliases surface as explicit **verification conditions / assumptions**; entry points in `.entry` | Verified GNU CoreUtils, OpenSSL, FDLIBM, seL4 x86-64, **Xen (~450K instructions)**; C-compiled sequential x86-64 only (no C++, no concurrency) |
| **`Islaris`** (`rems-project/islaris@c978e10f`; PLDI 2022) | AArch64, RISC-V | **Authoritative Sail** models (`Armv8-A` vendor ASL->Sail, `RISC-V` Sail) via `Isla` symbolic traces | Full functional & memory-safety specs in Coq/Iris separation logic directly over machine instructions | Manual `objdump` slicing + `//@constraint:` SMT alignment annotations; adequacy bridges Isla traces to Iris | Verified concrete kernel/hypervisor code (e.g., **pKVM EL2 exception handler**); function/routine scale |
| **`seL4` Binary Translation Validation** (Sewell, Myreen, Klein, PLDI 2013) | ARMv7 / RISC-V / x86-64 | HOL4 / Isabelle machine models (`L3`/Cambridge ISA models) | Equivalence between verified C semantics and GCC-compiled kernel binary (removes C compiler from TCB) | Decompilation-to-logic & SMT equivalence checker TCB; requires compiler-emitted symbols/structure | Full **seL4 microkernel** (~10K LoC C) |
| **`Dasgupta et al.`** (PLDI 2019 & PLDI 2020) | x86-64 (user-level) | Complete K-framework formal semantics of user-level x86-64 (~3,155 instruction variants) | Per-instruction translation validation of binary lifters (e.g., McSema/LLVM IR) against formal x86-64 semantics | Validates single-instruction / basic-block lifting fidelity, not whole-binary CFG/type recovery | Found dozens of silent semantic bugs in production x86-64 lifters |
| **`rev.ng`** (`revng/revng@5afe5310`; CC 2017) | Multi-arch (x86-64, AArch64, ARM, MIPS, RISC-V, s390x) | QEMU TCG translator -> LLVM IR | None formally proved (empirical testing & differential validation) | CFG recovery, function boundaries, `AnalyzeDataLayout` struct/type recovery | Scales to large stripped production binaries; **heuristic only** |

#### Deep Dive: `FoxDec` (`ssrg-vt/FoxDec@d9206efe`) as a Verified Legacy-FFI Gate

Direct inspection of `ssrg-vt/FoxDec@d9206efe` (`README.md`, lines 1–175) clarifies how FoxDec solves both scalability and trust:
- **Translation-validation architecture:** FoxDec's Haskell lifter is *untrusted*. For each binary $B_0$, it constructs an abstract state machine — a **Hoare Graph** — whose states hold symbolic invariants and an abstract memory model and whose edges represent instruction executions and control transfers (including dynamically computed indirect branches). A **join operator** merges abstract states at merge points/loops (forming a join semi-lattice), avoiding path explosion and achieving an **almost linear** relationship between constructed states and binary instruction count — enabling verification of industrial binaries up to the **Xen hypervisor (~450,000 instructions)**, GNU CoreUtils, OpenSSL, FDLIBM, OpenSC, and seL4 x86-64.
- **Minimal FFI ABI contract proved in Isabelle/HOL (`PLDI 2022`, `10.1145/3519939.3523702`):** Each transition in the Hoare Graph is exported as a Hoare triple and proved in **Isabelle/HOL**. The resulting theorem establishes that the binary preserves (i) **return-address integrity** (the callee does not overwrite the caller's saved RIP), (ii) **bounded control flow** (every branch stays within the verified CFG), and (iii) **System V AMD64 calling-convention adherence** (callee-saved registers and stack pointer balance are preserved). Any unprovable indirect target or memory-disjointness requirement is emitted explicitly in the Annotated Call Graph (`$NAME.callgraph.dot`) as a residual verification condition rather than silently assumed.
- **Symbolized, patchable NASM IR (`CCS 2024`, `10.1145/3658644.3690244`):** FoxDec 3.0 lifts position-independent x86-64 binaries to recompilable, symbolized **NASM** assembly (`nasm/$NAME.asm`, recompiled with `nasm -felf64` + `gcc`), demonstrated on `wget` to disable plaintext HTTP, swap OpenSSL for post-quantum `oqsprovider`, remediate `CVE-2019-5953` in `do_conversion()`, and retrofit Intel CET / full RELRO hardening.
- **Hard boundaries (`README.md`, L110–L116):** Explicitly restricted to sequential x86-64 System V ELF binaries compiled from C (no C++, no concurrency).

#### Authoritative ISA Semantics (`Sail` -> `Isla` -> `Islaris`) and Lifter Disagreement

Kim et al. (`MeanDiff`, ASE 2017) and Dasgupta et al. (PLDI 2019 `10.1145/3314221.3314601`, PLDI 2020 `10.1145/3385412.3385964`) demonstrated that independent lifters (BAP, angr/VEX, Ghidra SLEIGH/P-Code, Remill, McSema, QEMU TCG) routinely disagree on flag updates, undefined bits, memory-operand ordering, and edge-case encodings — and lifting into LLVM IR can *inject LLVM Undefined Behavior* absent from hardware machine semantics.

The architectural remedy is grounding lifting and verification in **authoritative, vendor-derived ISA specifications**:
- **`Sail` (`rems-project/sail@97aa617d`, Armstrong et al., POPL 2019, `10.1145/3290384`):** Compiles formal ISA definitions (including Arm's authoritative machine-readable ASL converted to Sail for Armv8-A, plus official golden-model Sail for RISC-V and CHERI-MIPS) to C/OCaml emulators, SMT, Coq, Isabelle/HOL, and Lean. For x86-64, no vendor-authored formal ISA specification exists; community models (such as ACL2's `x86isa` translated to Sail, Dasgupta's K-x86-64, or FoxDec's `Chum`/`libLISA`) fill the gap without vendor normative authority.
- **`Islaris` (`rems-project/islaris@c978e10f`, Sammler et al., PLDI 2022, `10.1145/3519939.3523434`):** Connects `Isla` (CAV 2021, symbolic execution over Sail ISA snapshots) to **Iris separation logic in Coq**. Inspection of `rems-project/islaris@c978e10f` (`README.md`, lines 36–108) illustrates the exact human-in-the-loop workflow on a real **pKVM EL2 exception handler** (`pkvm_handler.dump`): raw `objdump` disassembly (`stp x0, x1, [sp, #-16]!`, `mrs x0, esr_el2`, `br x5`) is annotated with SMT bitvector constraints (e.g., `//@constraint: = (bvand SP_EL2 0xfff0000000000007) 0x0000000000000000` encoding 8-byte alignment and canonical address range), processed by `isla-footprint` to emit one Coq instruction-trace file per address, and then verified in Coq/Iris against functional and isolation specifications.

### 8. A Graded Legacy-Binary FFI Adoption Ladder: Verified Lifting, Weak-Memory Translation, and Tainted Sandboxing

Basis: source (`PLSysSec/rlbox_sandboxing_api@b0157dc8`, `code/include/rlbox.hpp`) + normative (USENIX Security 2020, NDSS 2021, PLDI 2022, ASPLOS 2023) + derived

Because no single technique handles arbitrary stripped, concurrent, multi-architecture legacy binaries, a sound FFI architecture organizes legacy-binary ingestion into a **four-rung graded ladder**, where every rung enforces explicit trust/verification invariants:

1. **Rung 1 — Lift and Prove (`FoxDec`, `Islaris`, `seL4` Translation Validation):**
   - *When applicable:* Sequential C-compiled x86-64 binaries (FoxDec) or small high-assurance AArch64/RISC-V routines (Islaris).
   - *FFI guarantee:* Machine-checked ABI safety (stack/return-address integrity, bounded CFG, register preservation) or full functional separation-logic contract directly against an ISA semantics, with residual assumptions discharged by the caller or guarded dynamically.
2. **Rung 2 — Cross-ISA Translation with Memory-Model Soundness (`Lasagne`, `Risotto`, Hardware TSO):**
   - *When applicable:* Concurrent x86-64 binaries executed on weaker memory-model hosts (AArch64 / RISC-V). Naive translation breaks lock-free x86-TSO code unless excessive fences are inserted everywhere.
   - *Mechanisms:* **Lasagne** (Rocha et al., PLDI 2022, `10.1145/3519939.3523719`) performs static binary translation to weak-memory architectures guided by formal memory-model analysis to minimize fences; **Risotto** (Gouicem et al., ASPLOS 2023, `10.1145/3567557.3571665`) performs dynamic binary translation with formal weak-memory reasoning; Apple Silicon provides a hardware TSO execution mode for Rosetta 2. Crucially, if a translated thread shares memory with a native weak-memory thread, *both* sides must obey the stronger memory-order contract at the FFI boundary.
3. **Rung 3 — In-Process SFI/Wasm Sandboxing with Enforced Tainted Types (`RLBox`, `VeriWasm`):**
   - *When applicable:* Complex, concurrent, or C++ legacy libraries (e.g., font shapers, media codecs, image parsers) that cannot be formally lifted.
   - *Mechanisms:* **RLBox** (Narayan et al., USENIX Security 2020; shipped in Firefox starting with the Graphite font-shaping library) compiles legacy libraries into a sandbox (e.g., WebAssembly via `wasm2c`/Lucet or OS processes) and enforces C++ type-system taint tracking at the host-sandbox FFI boundary. Direct inspection of `PLSysSec/rlbox_sandboxing_api@b0157dc8` (`code/include/rlbox.hpp`, lines 65–90, 474–520) confirms the exact static-assertion invariants:
     - Every value returning from the sandbox is wrapped in `tainted<T, T_Sbx>`.
     - Elimination requires **`copy_and_verify(verifier)`** (L487), which snapshots the value out of sandbox memory *once* (eliminating double-fetch TOCTOU) before passing the local copy to the caller's validator lambda.
     - Raw escape hatches are statically gated: `unverified_safe_because` rejects pointers via `static_assert` (L69–L70); `unverified_safe_pointer_because` explicitly rejects pointers-to-pointers with `"There is no way to use unverified_safe_pointer_because for 'pointers to pointers' safely. Use copy_and_verify instead."` (L86–L87); and `copy_and_verify` forbids direct use on `void*` or function pointers (L506–L520).
   - **Post-compilation SFI verification (`VeriWasm`, Johnson et al., NDSS 2021, `10.14722/ndss.2021.24078`):** Applies abstract interpretation directly to the *native x86-64 binary* emitted by a WebAssembly AOT compiler (Lucet) to verify SFI memory-isolation invariants *after* compilation, removing the Wasm compiler from the isolation TCB.
4. **Rung 4 — Process / Hardware Isolation (`seccomp`, MicroVM, Attested TEE):**
   - *When applicable:* Untrusted binaries requiring isolation even against speculative-execution / microarchitectural leakage or executing across a network boundary.
   - *Unifying invariant:* Across Rungs 3 and 4 — just as across adversarial OS/TEE boundaries — every inbound byte sequence crosses as `Untrusted<T>` / `tainted<T>` and can only enter typed host invariants through a single-fetch, total validator.

## Boundaries

- **not examined:** Full end-to-end execution of `mrustc`'s `TestRustcBootstrap.sh`, GNU Guix's full-source bootstrap, `fosslinux/live-bootstrap`, CakeML's HOL4 self-bootstrap build, `FoxDec`'s Isabelle/HOL proof scripts, or `Islaris`'s Coq/Isla build was not run locally on this host (multi-hour native builds requiring multi-gigabyte toolchains). Claims about their runtime outputs rely on direct inspection of the pinned source scripts/proofs plus published peer-reviewed measurements, complemented by local execution of Probes 2A and 2B.
- **not examined:** Sub-ISA silicon, mask-level/dopant-level hardware trojans (e.g., Becker et al., CHES 2013; A2, Yang et al., IEEE S&P 2016), boot firmware parsers (`LogoFAIL`), and FPGA/EDA synthesis toolchains (`Lutsig`, Lööw, CPP 2021; open roots of trust such as OpenTitan and Caliptra) were not examined in depth; they constitute the physical hardware base case lying strictly below the 181-byte `hex0-seed`.
- **unknown:** Whether `oriansj/bootstrap-seeds` `POSIX/riscv64/hex0-seed` (392 bytes) and `POSIX/AArch64/hex0-seed` (526 bytes) match their respective `stage0-posix` `.hex0` sources bit-for-bit was not executed in Probe 2A (only `x86` and `AMD64` were assembled and bit-compared).
- **unknown:** Exact current status of `digama0/mm0`'s end-to-end x86-64 self-verification proof (`examples/verifier.mm0`) and whether `digama0/lean4lean` currently covers 100% of Lean 4's latest kernel primitives without axioms was not audited line-by-line beyond their pinned `README.md` inventories.
- **known not to apply:** Diverse Double-Compiling (Wheeler 2005/2009) is *known not to apply* as a detector of bugs or backdoors present in the *source code* itself, poisoned release tarballs consumed by both compilers (`CVE-2024-3094`), or correlated trojans present in both compilers/shared host toolchains (demonstrated in Probe 2B Case 3); it proves $c_A = \text{compile}(s_A)$, not semantic correctness of $s_A$.
- **known not to apply:** Heuristic decompilation and type recovery (`rev.ng`, `Ddisasm`, `TIE`, `Retypd`) are *known not to apply* as sound proofs of ABI conformance, padding-byte initialization, or pointer ownership for memory-safe FFI bindings without an independent verifier or runtime sandbox.
- **unsupported:** `ssrg-vt/FoxDec@d9206efe` explicitly documents (`README.md` L110–L116) that C++ binaries, non-x86-64 architectures, and concurrent binaries are **unsupported**. Authoritative vendor-authored formal ISA specifications are **unsupported** (non-existent) for x86-64, unlike Armv8-A (Arm ASL->Sail) and RISC-V (official Sail golden model).

## Evidence

All primary-source inspections, SHA-256 measurements, and micro-probe executions were acquired on `2026-11-19`.

### Pinned GitHub Source Inspections (`Basis: source`)

- **`oriansj/bootstrap-seeds`** at `cedec6b8066d1db229b6c77d42d120a23c6980ed`:
  - `README.md` (exact `hex0` equivalence formula `sed 's/[;#].*$//g' $input_file | xxd -r -p > $output_file` and `kaem-optional-seed` replaceability).
  - `POSIX/x86/hex0-seed` (181 bytes, SHA-256 `f74dcf9cef2aee9eb7723eca755849d474fccd89662947021d1aa08429d23c13`).
  - `POSIX/AMD64/hex0-seed` (229 bytes, SHA-256 `66c95985e668f20f2465c2b876f83fef066fd7c8c2dd3adb51a969f2d7120c8b`).
  - `POSIX/riscv64/hex0-seed` (392 bytes, SHA-256 `1b50ceef632b83b79aef0cf91d60bc0cb242a3b2bfba22cb5115d80112b50ac9`).
  - `POSIX/AArch64/hex0-seed` (526 bytes, SHA-256 `8ca9745e20af3f0d6037684cbc3ec3789c205d86ccecf43f77d0aeabf16050b4`).
  - `POSIX/AMD64/kaem-optional-seed` (618 bytes, SHA-256 `153b8915b73bd07132b59538d10fe53d26578eb160a67db72af07aaa61c51b3b`).
  - `POSIX/x86/kaem-optional-seed` (632 bytes, SHA-256 `545f89537f070d7e62b05243be34cbcfdb1e92dbf9d82e2cd15792d880436ac2`).
- **`oriansj/stage0-posix-x86`** at `14721630c8d3e4a7de943e27488d0d582788837f`: `hex0_x86.hex0` (155 lines).
- **`oriansj/stage0-posix-amd64`** at `15535f88e25825f01a0de275b6d45f77e618bd6b`: `hex0_AMD64.hex0` (152 lines).
- **`oriansj/stage0-posix`** at `643598041bf7639883874fe2cdc9d9693c9b03d5` & **`fosslinux/live-bootstrap`** at `a49273cbb5c381b851198bc1e53c294702f4f7c9`: `README.md` / `README.rst` stage progression.
- **`thepowersgang/mrustc`** at `4e020d6b307c738434209435e9b75b7d81b00077`:
  - `README.md` L16–L30 (supported `rustc` versions `1.19.0`, `1.29.0`, `1.39.0`, `1.54.0`, `1.74.0`, and `1.90.0` yielding binary-equal `1.91.1`).
  - `TestRustcBootstrap.sh` L1–L104 (stage-3 `x.py build --stage 3`, `tar --mtime="@0" --sort=name`, `diff -qs mrustc.tar.gz official.tar.gz`).
- **`CakeML/cakeml`** at `2874b664e10939a3ee462215b2e068c89c1f70eb`:
  - `semantics/ffi/ffiScript.sml` L1–L95 (`oracle_function`, `ffiname`, `call_FFI_def`, `behaviour`, `trace_oracle_def`).
  - `compiler/backend/proofs/backendProofScript.sml` L5048–L5061 (`Theorem compile_correct_eval`).
- **`leanprover/lean4`** at `0171678607a54e5a72c6a4ab6409286ba5002b05`: `doc/dev/bootstrap.md` L1–L80 (`stage0/src/` pre-built C seed, `stage1`/`stage2`/`stage3` fixed point).
- **`digama0/lean4lean`** at `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` & **`digama0/mm0`** at `0d414c0bfdaaeb7fea571895127abc1fa5a3d956` & **`Ekdohibs/camlboot`** at `2692b14a4e685387194556e511fe23057d25c6c3`: `README.md` architectures, `mm0-c` <3,000 LoC C verifier, `camlboot` 4h wall / 16h CPU bit-identical bytecode bootstrap.
- **`ssrg-vt/FoxDec`** at `d9206efe59a94138924d45c3d69d7c7afa1eb4ac`: `README.md` L1–L175 (Hoare Graph, join semi-lattice, Isabelle/HOL translation validation, Xen ~450K instructions, `wget` patching, `nasm/$NAME.asm`, Limitations L110–L116).
- **`revng/revng`** at `5afe53108d6487a3aecc92eec133d89f03461e52`: `include/revng/DataLayoutAnalysis/DLA.h` L1–L25 (`revng::pypeline::analyses::AnalyzeDataLayout`), `README.md`.
- **`rems-project/islaris`** at `c978e10f50db5c40f0fdf113f5f76a779782c6f9`: `README.md` L1–L120 (`isla` commit `b8e614bd...`, `isla-snapshots` commit `b58da917...`, `pkvm_handler.dump` `//@constraint:` alignment annotations and `isla-footprint` workflow).
- **`PLSysSec/rlbox_sandboxing_api`** at `b0157dc84f86ffbe4549e32ed5cbdfad79c17f43`: `code/include/rlbox.hpp` L65–L90 (`unverified_safe_because` / `unverified_safe_pointer_because` `static_assert`s), L474–L520 (`copy_and_verify` and pointer/function-pointer restrictions).

### Verified Papers and Primary Articles (`Basis: normative | documentation`)

- Thompson (CACM 27(8), Aug 1984, `10.1145/358198.358210`) — *Reflections on Trusting Trust*.
- Wheeler (ACSAC 2005; PhD Dissertation, George Mason University, 2009) — *Countering Trusting Trust through Diverse Double-Compiling*.
- Nieuwenhuizen (GNU Guix Blog, April 2023) — *The Full-Source Bootstrap: Building from source all the way down*.
- Cox (Go Blog, 2023; `golang/go@c19c4c56` `go1.21.0`) — *Perfectly Reproducible, Verified Go Toolchains*.
- Kumar, Owens, Norrish, Myreen (POPL 2014, `10.1145/2535838.2535841`) — *CakeML*; Lööw et al. (PLDI 2019, `10.1145/3314221.3314631`) — *Verified Compilation on a Verified Processor* (`Silver`); Abrahamsson et al. (ITP 2022) — *Candle*.
- Sozeau et al. (POPL 2020, `10.1145/3371076`) — *Coq Coq Correct!* (`MetaCoq`); Carneiro (CICM 2020, `10.1007/978-3-030-53518-6_5`) — *Metamath Zero*.
- Verbeek, Bockenek, Fu, Ravindran (PLDI 2022, `10.1145/3519939.3523702`) — *Formally Verified Lifting of C-Compiled x86-64 Binaries*; Verbeek, Naus, Ravindran (CCS 2024, `10.1145/3658644.3690244`) — *Verifiably Correct Lifting of Position-Independent x86-64 Binaries to Symbolized Assembly*.
- Di Federico, Payer, Agosta (CC 2017, `10.1145/3033019.3033028`) — *rev.ng*; Pang et al. (IEEE S&P 2021, `10.48550/arXiv.2007.14266`) — *SoK: x86/x64 Binary Disassembly*; Flores-Montoya & Schulte (USENIX Security 2020) — *Datalog Disassembly*; Williams-King et al. (ASPLOS 2020, `10.1145/3373376.3378470`) — *Egalito*.
- Balakrishnan & Reps (TOPLAS 2010, `10.1145/1838212.1838215`) — *WYSINWYX*; Lee, Avgerinos, Brumley (NDSS 2011) — *TIE*; Noonan, Loginov, Cok (PLDI 2016, `10.1145/2908080.2908083`) — *Retypd*.
- Dasgupta et al. (PLDI 2019, `10.1145/3314221.3314601`; PLDI 2020, `10.1145/3385412.3385964`); Armstrong et al. (POPL 2019, `10.1145/3290384`) — *Sail*; Sammler et al. (PLDI 2022, `10.1145/3519939.3523434`) — *Islaris*; Sewell, Myreen, Klein (PLDI 2013, `10.1145/2491956.2491960`) — *seL4 Translation Validation*.
- Rocha et al. (PLDI 2022, `10.1145/3519939.3523719`) — *Lasagne*; Gouicem et al. (ASPLOS 2023, `10.1145/3567557.3571665`) — *Risotto*; Narayan et al. (USENIX Security 2020) — *RLBox*; Johnson et al. (NDSS 2021, `10.14722/ndss.2021.24078`) — *VeriWasm*.

### Executable Micro-Probes (`Basis: execution`)

Environment: Python 3.13.15 + GNU `objdump` on Linux x86-64. Standalone script (`/tmp/bootstrap_probe.py`) assembling upstream `hex0_x86.hex0` and `hex0_AMD64.hex0` and comparing against upstream `POSIX/{x86,AMD64}/hex0-seed`, plus executable Wheeler DDC model:

```python
import hashlib, re, struct
from pathlib import Path

def hex0_assemble(src_text: str) -> bytes:
    cleaned = [re.sub(r"[^0-9a-fA-F]", "", re.split(r"[;#]", line, maxsplit=1)[0])
               for line in src_text.splitlines()]
    return bytes.fromhex("".join(cleaned))

# Check bit-for-bit identity against upstream bootstrap-seeds@cedec6b8:
# hex0_assemble(hex0_x86.hex0)   == POSIX/x86/hex0-seed   (181 bytes)
# hex0_assemble(hex0_AMD64.hex0) == POSIX/AMD64/hex0-seed (229 bytes)
# Disassembly: objdump -D -b binary -m i386:x86-64 --start-address=0x78 hex0-seed-AMD64
```

Observed output (`exit 0`):
```text
Arch: x86   | lines=155 | assembled_bytes=181 | upstream_seed_bytes=181 | BIT-FOR-BIT EQUAL: True
  sha256: f74dcf9cef2aee9eb7723eca755849d474fccd89662947021d1aa08429d23c13
  ELF32: magic=b'\x7fELF', e_machine=0x3, e_entry=0x804804c, e_phoff=0x2c
Arch: AMD64 | lines=152 | assembled_bytes=229 | upstream_seed_bytes=229 | BIT-FOR-BIT EQUAL: True
  sha256: 66c95985e668f20f2465c2b876f83fef066fd7c8c2dd3adb51a969f2d7120c8b
  ELF64: magic=b'\x7fELF', e_machine=0x3e, e_entry=0x600078, e_phoff=0x40
objdump @ 0x78..0xe4 (109 bytes): open (rax=2), open out (rax=2, O_CREAT|O_WRONLY|O_TRUNC 0x241, 0700),
  read (rax=0), exit (rax=0x3c), comment checks (0x0a/0x23/0x3b), hex nibble decode, write (rax=1).
DDC Case 1 (clean c_A, clean c_T):               match=True
DDC Case 2 (trojaned c_A, clean c_T):            match=False (detected THOMPSON_84; stage2 clean)
DDC Case 3 (correlated trojan in BOTH c_A, c_T): match=True  (FALSE NEGATIVE: independence violated)
DDC Case 4 (clean c_A, nondet timestamp):        match=False (FALSE POSITIVE: determinism violated)
```

## Revalidation

Use these narrow, cheap checks to determine whether the findings still hold for newer revisions:

1. **`hex0` seed fixed-point check:** Re-fetch `oriansj/bootstrap-seeds` `POSIX/{x86,AMD64,riscv64,AArch64}/hex0-seed` and the corresponding `stage0-posix-*` `.hex0` sources, re-run `/tmp/bootstrap_probe.py` (~10 ms), and verify SHA-256 bit-identity and syscall footprints via `objdump`.
2. **Rust DDC coverage (`mrustc`):** Diff `thepowersgang/mrustc` `TestRustcBootstrap.sh` and `README.md` against commit `4e020d6b307c738434209435e9b75b7d81b00077` to check the latest `rustc` version supported and whether `diff -qs` still validates bit-equal stage-3 toolchains.
3. **Lean 4 / independent kernel status:** Diff `leanprover/lean4` `doc/dev/bootstrap.md` (whether `stage0/src/` still holds checked-in C), `digama0/lean4lean` (completeness against current Lean 4 kernel rules), and `digama0/mm0` (`examples/verifier.mm0` completion status).
4. **FoxDec & Islaris lifting scope:** Diff `ssrg-vt/FoxDec` `README.md` (`Limitations` section) against commit `d9206efe59a94138924d45c3d69d7c7afa1eb4ac` to check whether C++, AArch64, or concurrency support has been added, and check `rems-project/islaris` and `rems-project/sail` for updated ISA snapshot coverage or automated constraint generation.
5. **RLBox tainted-type invariants:** Diff `PLSysSec/rlbox_sandboxing_api` `code/include/rlbox.hpp` (`copy_and_verify` and `unverified_safe_*` `static_assert`s) against commit `b0157dc84f86ffbe4549e32ed5cbdfad79c17f43` to confirm no unvalidated pointer escape paths were introduced.
