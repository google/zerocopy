# Compiler bootstrapping, Diverse Double-Compiling, and the trusted-computing-base chain of a verified rustc

## Summary

A Rust compiler whose correctness evidence is checked by Lean 4 rests on three separate binary lineages: the `rustc` binary, the Lean binary that checks proofs, and the Rust-built driver that decides which Lean binary and which files to admit. Thompson's attack (a compiler binary that reinserts a payload whenever it compiles its own clean source) applies to each lineage independently; countering it for one says nothing about the others.

- **rustc seed.** `rust-lang/rust` 1.99.1 names exactly one seed toolchain in `src/stage0`: `rustc 1.98.0` dated 2026-08-20, behind 441 SHA-256-pinned download entries. Official builds descend from a chain of prebuilt binaries.
- **Source-only chain length.** `mrustc` at the examined revision documents bootstrapping `rustc 1.90.0` and from it a binary-equal 1.91.1. Reaching 1.99.1 takes one `mrustc`-built compiler plus nine rustc-by-rustc builds (1.91 to 1.99); this count is derived, not executed. GNU Guix encodes the same splice for its default 1.98.1: 9 packages from the 1.90.0 entry point, against 25 from 1.74.0 and 45 from 1.54.0. A chain starting at `mrustc -> rustc 1.54` is no longer the shortest. nixpkgs builds 1.99.1 from the prebuilt 1.99.1 binary.
- **DDC works on a real compiler, and its assumptions are checkable.** A Diverse Double-Compiling (DDC) run on TinyCC 0.9.28rc with GCC 15.2.0 and Clang 22.1.4 as unrelated host compilers produced a bit-identical second-generation compiler from both lineages (SHA-256 `7a787d82…ff460`) in three runs, and flagged a deliberately modified compiler. Wheeler's Proof #1 and Proof #2 were restated in Lean 4.34.1 and kernel-checked with no axioms; a countermodel shows the comparison passing while unsound when the "trusted" compiler shares the payload.
- **Lean binary identity gap.** In the Lean 4.34.1 Linux distribution `bin/lean` is a 9,024-byte launcher; the kernel entry points are exported by the 233,708,536-byte `lib/lean/libleanshared.so`. The Anneal audit at the examined revision hashes only the launcher against its lock; the library is pinned only indirectly, by a release-archive digest on the Nix build path.
- **Checker diversity is thinner than it looks.** Lean4Lean calls itself "not really an independent implementation" of the C++ kernel. `nanoda_lib` is independent but is a Rust program with a 29-entry lockfile that includes a proc-macro stack. At their heads `lean4export` targets Lean v4.36.0-rc1 and Lean4Lean v4.33.0-rc2; the lock requires v4.34.1, for which `lean4export` has no tag. The Anneal tree examined references none of the three.
- **Alternative Rust compilers.** `gccrs` states it is "not usable yet for compiling real Rust programs"; `rustc_codegen_gcc` is loaded by the existing `rustc` front end. Only `mrustc` can serve today as the diverse compiler in a DDC of `rustc`.

Consequence (derived): make soundness independent of the `rustc` binary by checking per-build evidence with a small proof checker, get checker assurance from agreement between independently built checkers, and keep DDC of `rustc` through `mrustc` as a release-level audit.

## Applicability

`REPORT.json` lists upstream repositories at fixed revisions, three papers and three executed toolchain artifacts.

- *Read at a pinned revision (source and documentation):* `rust-lang/rust` 1.99.1, `mrustc`, GNU Guix `gnu/packages/rust.scm`, nixpkgs, Lean 4 v4.34.1, Lean4Lean, `nanoda_lib`, `lean4export`, `joshlf/anneal`, CakeML, CompCert 3.18, CertiRocq (repository formerly `CertiCoq/certicoq`), MetaRocq (formerly `MetaCoq/metacoq`), `gccrs`, `rustc_codegen_gcc`, SLSA, in-toto. Heads were resolved on 2026-11-20.
- *Executed:* TinyCC at the pinned commit, built by GCC 15.2.0 and by the Clang 22.1.4 shipped inside the Lean 4.34.1 distribution; the Lean 4.34.1 `x86_64-unknown-linux-gnu` distribution (inspected with `ldd`, `readelf`, `nm`, `sha256sum`; used to check one Lean file); Python parsers over `src/stage0` and Guix's `rust.scm`.
- *Papers:* Thompson 1984; Wheeler 2009 (text from the author's HTML edition, abstract from arXiv:1004.5534); Carneiro, arXiv:2403.14064v3 (abstract only).

Host: one shared x86_64 Linux machine, 8 logical CPUs, 31 GiB RAM; timings are wall-clock and noisy.

**Not executed.** No `rustc`, `mrustc`, `gccrs`, `nanoda_lib`, Lean4Lean, `lean4export`, CakeML, CompCert or Rocq build was run; the host had no `rustc 1.99.1`. Every statement about Rust bootstrap chains is source or derived. The TinyCC run is a DDC of TinyCC, not of `rustc`. The Lean file models the DDC argument, not a compiler.

**Scope limits.** Chain lengths hold for the stated revisions. The Lean launcher/library layout was observed only on the x86_64 Linux distribution; the lock lists three others. The Guix revision is a Codeberg commit, recorded in full in `REPORT.json` and abbreviated here as `0a08fa79a9e9`.

**Related reports in this corpus**, built on and not repeated here:

- `trusting-trust-bootstrappable-builds-and-verified-binary-lifting`: seed sizes, full-source bootstraps, a step-by-step reading of `mrustc`'s `TestRustcBootstrap.sh`, CakeML's installed-code theorem.
- `verified-rust-compiler-architecture-self-hosting-and-certifying-bootstrap`: architecture comparison; a finite DDC witness.
- `de-bruijn-kernels-self-verifying-checkers-and-proof-producing-toolchains`: statement/proof split, kernel escape surfaces.
- `cross-prover-interoperability-verified-checkers-and-tcb-accounting`: export formats, claim-relative TCB accounting.
- `rust-sysroot-rlib-artifact-provenance-reproducible-capture-and-toctou-hardening`: sysroot artifact capture.

New here: the 1.99.1 seed census, packager chain lengths, an executed DDC with a negative control, kernel-checked DDC proofs, the Lean launcher/library finding, checker version skew, the design ranking.

## Findings

### 1. What the attack is and what DDC establishes

Basis: documentation (Wheeler 2009, sections 4.3, 5.6, 5.7) + execution (kernel-checked restatement; a model of the argument, not of a compiler)

Wheeler's setting: `sA` is the source of the compiler under test, `cA` its distributed executable, `sP` the source of the parent compiler that putatively built `cA`, and `cT` a second, diverse compiler. DDC computes

```text
stage1 = compile(sP, cT, e1effects, e1, e2)
stage2 = compile(sA, stage1, e2effects, e2, eArun)
```

and compares `stage2` with `cA`. Proof #1 (`source_corresponds_to_executable`) concludes `(stage2 = cA) -> exactly_correspond(cA, sA, lsA, eArun)` from the two definitions and three assumptions:

- `cT_compiles_sP`: `all EnvEffects accurately_translates(cT, lsP, sP, EnvEffects, e1, e2)`;
- `sP_compiles_sA`: an accurately compiled `sP` accurately translates `sA`;
- `define_exactly_correspond`: the output of an accurate translation exactly corresponds to its source.

Proof #2 (`always_equal`, goal `cA = stage2`) shows the check is not vacuous in the benign case. It needs nine assumptions, among them `cP_corresponds_to_sP`, `sP_portable_and_deterministic` and `define_determinism`.

"Trusted" is narrow in the dissertation: "something is 'trusted' if we have justified confidence that it does not have triggers and payloads that would affect the results of DDC."

Both proofs were restated in Lean 4 with opaque sorts and uninterpreted functions (`support/DdcWheelerProofs.lean`, 216 lines). Lean 4.34.1 accepts the file; `#print axioms` reports "does not depend on any axioms" for all five theorems. Two additions:

- `proof1_assumptions_satisfiable`: a one-point model satisfies the Proof #1 assumptions.
- `ddc_passes_but_unsound_when_cT_shares_payload`: in a two-point "taint" model where `compile` returns the taint of the compiler that ran, a tainted `cT` gives `stage2 = cA` while `cA` does not correspond to its source. `sP_compiles_sA` and `define_exactly_correspond` hold there; only `cT_compiles_sP` fails. With an untainted `cT` the model yields `stage2 ≠ cA`.

Derived: DDC concerns one executable and one source text. It does not show the source is correct, and gives nothing if `cT` and `cA` share an ancestor carrying the payload. Every official `rustc` shares the ancestry of section 2, so two official builds are not diverse.

### 2. The rustc seed at release 1.99.1

Basis: source (`rust-lang/rust` at the 1.99.1 tag) + execution (`support/rustc_stage0_census.py`)

`src/version` reads `1.99.1`. `src/stage0` (lines 16–19) records `compiler_date=2026-08-20`, `compiler_version=1.98.0`, a channel-manifest hash and the seed's commit (`88d9e12ae178…`, resolved in `rust-lang/rust`); lines 10–11 say it is generated by `./x.py run src/tools/bump-stage0`. The generator states the policy (`src/tools/bump-stage0/src/main.rs:119–121`): "Currently Rust always bootstraps from the previous stable release, and in our train model this means that the master branch bootstraps from beta, beta bootstraps from current stable, and stable bootstraps from the previous stable release."

Measured over the manifest (SHA-256 `759b73ec…1d4e`):

| Quantity | Value |
| --- | --- |
| download entries (`dist/...=sha256`) | 441 |
| by component | `rust-std` 232, `rustc` 68, `cargo` 66, `clippy` 66, `rust` installers 9 |
| by extension | `tar.gz` 216, `tar.xz` 216, `msi` 7, `pkg` 2 |
| distinct `rustc` host targets / `rust-std` targets | 34 / 116 |
| distinct (date, version) pairs | 1: (2026-08-20, 1.98.0) |

Enforcement: `src/bootstrap/bootstrap.py` `get` (lines 52–90) refuses a URL absent from the manifest (line 57), looks up `sha256 = checksums[url]` (line 66) and calls `verify` (lines 181–194); the tarballs fetched are `rust-std`, `rustc` and `cargo` (lines 661–677). The digest gives integrity of a binary, not correspondence to source.

Staging rules that constrain any replacement seed (`src/doc/rustc-dev-guide/src/building/bootstrapping/what-bootstrapping-does.md`):

- "the only way to build a modern version of `rustc` is with a slightly less modern version" (lines 9–10);
- the downloaded compiler "is then used only to compile [`src/bootstrap`] and [`compiler/rustc`] with precompiled stage0 std" (lines 67–68);
- sources built by the seed get `--cfg bootstrap`, and `RUSTC_BOOTSTRAP=1` lets a non-nightly seed accept `#![feature(...)]` (lines 146–153);
- the `std` linked into a compiler and the `std` it compiles with are built one step apart because "they aren't necessarily ABI-compatible" (lines 226–237).

Another seed is supported: `bootstrap.example.toml:295–303` documents `build.cargo` and `build.rustc` ("use this rustc binary instead as the stage0 snapshot compiler"). `mrustc`'s script sets both.

### 3. Source-only Rust chains: mrustc, Guix, nixpkgs

Basis: source + documentation + execution (`support/guix_rust_chain.py`) + derived (count to 1.99.1)

**mrustc.** `README.md:18–20`: "Currently tested to fully bootstrap (with a binary-equal 1.91.1) version 1.90.0"; it also "supports and might still bootstrap" five older versions. It needs a "C++14-compatible compiler" and a "C11 compatible C compiler" for its output (lines 38–39), since code generation emits C (line 12). `TestRustcBootstrap.sh:25–28` maps 1.90.0 to next version 1.91.1; lines 72 and 100 run `./x.py build --stage 3` once with the `mrustc`-built seed and once with the downloaded one; line 113 compares with `diff -qs`. That script is a DDC with `cT` = `mrustc` plus the host C/C++ compilers. Qualifications:

- The 1.90.0 source `mrustc` compiles is patched: `rustc-1.90.0-src.patch` (43 lines, 5 files) puts `#[cfg(not(rust_compiler="mrustc"))]` on three size-assertion items and rewrites two auto-deref expressions (`self.split_last()` to `(**self).split_last()`, `self.iter()` to `(***self).iter()`). `cT` compiles a variant of `sP`; the 1.91.1 compared at the end is unpatched.
- The CI matrix (`.github/workflows/c-cpp.yml:32`) is `["1.29", "1.39", "1.19", "1.54", "1.74"]`; the 1.90.0 bootstrap and the 1.91.1 comparison are not exercised there.
- Audit surface (Git tree): 296 C/C++ files, 7,141,223 bytes, of which `src/` is 228 files and 6,192,185 bytes.

**Count to 1.99.1 (derived).** Under the previous-stable rule the path is `mrustc` → 1.90.0 → 1.91.1 → 1.92 → … → 1.98 → 1.99.1: one compiler built by `mrustc` and nine built by the previous `rustc`. Only the first two links are documented as tested upstream.

**Guix** (revision `0a08fa79a9e9`, `rust.scm` SHA-256 `e2adeaf1…75e1`). "The rust-bootstrap packages are special in that they are built with mrustc, which shortens the bootstrap path" (lines 199–200). The file defines three such entry points and 44 `rust-1.NN` packages; all but `rust-1.55` call `rust-bootstrapped-package` (lines 116–137) on their predecessor; the default `rust` inherits `rust-1.98` (lines 2420–2421), version 1.98.1. Three packages take an `mrustc`-built compiler as native input: `rust-1.55` always, `rust-1.75` and `rust-1.91` when the platform supports the bootstrap package (lines 1936–1943 for the last). Parsed chains to the default package:

| Entry point (built by `mrustc`) | Compilers in chain | Built by a previous `rustc` | Path |
| --- | --- | --- | --- |
| `rust-bootstrap-1.90` | 9 | 8 | 1.90.0, 1.91.1, 1.92.0, …, 1.97.1, 1.98.1 |
| `rust-bootstrap-1.74` | 25 | 24 | 1.74.0, 1.75.0, …, 1.98.1 |
| `rust-bootstrap-1.54` | 45 | 44 | 1.54.0, 1.55.0, …, 1.98.1 |

Guix pins `mrustc` at `a822472b9ee7` for 1.90 and `06b87d1af49d` for 1.54 (both resolve upstream), not at the head examined above, and does not package 1.99.

**nixpkgs.** `pkgs/development/compilers/rust/1_99.nix` sets `rustcVersion = "1.99.1"` (line 53), LLVM 23 (line 59) and `bootstrapVersion = "1.99.1"` with the note "the version MUST be the same version that we are building. Upstream ensures that each released compiler can compile itself" (lines 66–69). `bootstrap.nix:12–15` fetches `rust-${version}-${platform}.tar.gz` from `static.rust-lang.org` against one of 17 per-platform digests (`1_99.nix:72–90`). The compiler under test is its own parent, fetched as a binary.

### 4. DDC executed on TinyCC

Basis: execution (real DDC of TinyCC; not `rustc`), `support/ddc_tinycc.sh`, `support/ddc_tinycc_result.json`

`sA = sP` = TinyCC at the pinned commit (0.9.28rc; tarball SHA-256 `c1927898…7c1c`). Every generation is unpacked and built at the same path with `./configure --cc=<compiler> && make tcc libtcc1.a`; a TinyCC used as compiler is always reached through the same symlink, so the lineages differ only in the compiler binary.

| Name | Built by | Role | Bytes | SHA-256 (prefix) |
| --- | --- | --- | --- | --- |
| A1 | GCC 15.2.0 | parent in the putative lineage | 377,552 | `aeb53c93` |
| A2 | A1 | `cA`, compiler under test | 445,052 | `7a787d82` |
| A3 | A2 | self-regeneration | 445,052 | `7a787d82` |
| B1 | Clang 22.1.4 | `stage1` | 439,272 | `1513f798` |
| B2 | B1 | `stage2` | 445,052 | `7a787d82` |
| N2 | A1, from modified source | negative control | 445,068 | `8e0058e2` |

Results, identical in three runs in different work directories (47 s, 56 s and 40 s wall for all six builds):

- `stage2 = cA`: B2 and A2 are byte-identical, as are their `libtcc1.a` (`7fac7e6c`).
- A1 and B1 differ, so the two host compilers did produce different parents.
- A3 = A2: the compiler regenerates itself.
- N2, built from a source whose banner was changed to `tcc version (payload) 0.9.28rc`, differs from B2: a compiler that does not correspond to the audited source is flagged.

For transfer to other compilers:

- `configure` records build-host facts in `config.h`: the kernel release (`CONFIG_OS_RELEASE`, `configure:718`) and the building compiler (`CC_NAME`, `GCC_MAJOR`; `configure:642–644`). The release is read only by BSD-only code (`tccelf.c:2948, 2982–2983`) and its string occurs in none of A1, A2, B1, B2; on a BSD target it would put host state into the compiler, which `sP_portable_and_deterministic` rules out. The compiler macros are read by the `Makefile` and the test suite, and A2 and B2 have identical `config.h`.
- Equality across hosts or compiler versions was not tested.
- Common-mode components remain: glibc headers and startup objects, `make`, shell, kernel.

### 5. The proof-checker lineage: Lean 4.34.1

Basis: documentation + source (`leanprover/lean4`, `joshlf/anneal`) + execution (`support/lean_toolchain_identity_probe.py` and its result file)

**Bootstrap.** `doc/dev/bootstrap.md:3–9`: the self-hosting cycle "is broken by using pre-built C files checked into the repository (which ultimately go back to a point where the Lean compiler was not written in Lean)". The first build step "is equivalent to downloading a bootstrapping binary as done in other compilers" (lines 36–38); the third rebuild "should always be identical to" the second "and only exists as a sanity check" (lines 54–56). The seed is generated C, refreshed by an automated workflow (lines 73–77) and compiled by a C++ toolchain. Measured from the Git tree: `stage0/stdlib/` holds 2,519 generated `.c` files totalling 612,862,472 bytes; `stage0/src/` holds 242 files, 1,726,952 bytes.

**Where the kernel lives (measured).**

| File | Bytes | SHA-256 | Kernel entry points exported |
| --- | --- | --- | --- |
| `bin/lean` | 9,024 | `e8baaa71…5550` | none |
| `lib/lean/libleanshared.so` | 233,708,536 | `6b30cc96…4f13` | `lean_kernel_check`, `lean_kernel_is_def_eq`, `lean_add_decl` |
| `libleanshared_1.so`, `libleanshared_2.so`, `libInit_shared.so` | 6,264 each | in the result file | none |

`bin/lean` has `NEEDED` entries for those four libraries, `RUNPATH` `$ORIGIN/../lib:$ORIGIN/../lib/lean`, and takes `libc` and four more system libraries from the host.

**What the Anneal lock pins.** `trusted/lean/foundation-lock.json:16–21` maps four `lean --version` strings to SHA-256 values; the x86_64 Linux value equals the measured `bin/lean` digest. `Checker::tool_admission` (`trusted/audit/src/lib.rs:2402`) computes `sha256_file(&self.lean, "toolchain")` (line 2468), requires it among the lock's values and equal to the entry for the reported version (lines 2469–2500), then hashes each foundation module's `.lean` source and `.olean`/`.ir` parts (from line 2511). The four digests recur as `LOCKED_LEAN_SHA256` (lines 1513–1518), documented as digests "of the official Lean 4.34.1 `bin/lean` binaries". The probe finds no prefix library's digest in the lock, and `git grep -i libleanshared -- trusted` returns nothing.

Derived: the audit's admission check authenticates a 9 KB launcher and the foundation data files, not the 234 MB library containing the kernel. It strips `LD_*` variables (crate documentation, line 38), which blocks preloading, but `RUNPATH` resolves the library relative to the launcher, so a prefix holding the genuine launcher and a different `libleanshared.so` satisfies the digest check as written. Closing it is cheap: hashing the library took a median 1.27 s (min 0.94, max 1.48; five runs) against 4.7 ms for the launcher.

**Pins outside the audit.** `flake.nix:103–106` fetches the Lean release archive under a per-platform SHA-256 (lines 27, 32, 37, 42), which fixes every file, the library included, on the Nix build path; `trusted/root-manifest.sha256` hashes `flake.nix`. The archive metadata for `cargo anneal setup` (`trusted/cargo-anneal/Cargo.toml:19–44`) is marked `FIXME`: `example.com` URLs and one digest, the SHA-256 of `abc`, for all four platforms. The audit's default search also accepts an elan install (`lib.rs:1547`), covered by neither. The gap is thus in the run-time check and on non-Nix installs.

**Replay is not diversity.** The audit replays declarations through `base.toKernelEnv.replay` (crate documentation, lines 56–59), the mechanism of the shipped `leanchecker` (`src/LeanChecker.lean:33`), which upstream describes in line 68 as `not an external verifier, simply a tool to detect "environment hacking"`. It re-runs the same kernel code in the same binary.

**Absent at the examined revision.** A case-insensitive `git grep` outside `vendor/` finds no file mentioning `lean4lean`, `nanoda`, `lean4export`, `in-toto`, `slsa` or `mrustc`.

### 6. Independent Lean checkers

Basis: source + documentation (pinned heads) + execution (Git tree sizes, tag list); published abstract for throughput

| Checker | Language | Self-description | Lean version at head | Size and notes |
| --- | --- | --- | --- | --- |
| Lean4Lean | Lean 4 | "derived directly from the C++ kernel implementation, and as such likely shares some implementation bugs with it (it's not really an independent implementation)" (`README.md:3–7`) | `v4.33.0-rc2` | checker proper 18 files, 168,491 B; `Verify/` 37 files, 1,271,976 B; no `reduceBool` (`divergences.md:5`); three kernel bugs credited (`bugs-found.md:3–5`) |
| `nanoda_lib` 0.4.32 | Rust | "an external type checker for the Lean 4 programming language" (`README.md:3`) | reads `lean4export` output | 16 non-test `src/*.rs` files, 366,393 B; 8 direct dependencies (`Cargo.toml:24–32`); 29 `[[package]]` entries in `Cargo.lock` (itself and dev-dependencies included) with `serde_derive`, `syn`, `quote`, `proc-macro2`; Nat and String extensions "disabled by default" (`README.md:39`) |
| `lean4export` | Lean 4 | "A simple declaration exporter for Lean 4" (`README.md:1`) | `v4.36.0-rc1` | 50 tags returned by the tags API include `v4.34.0` and `v4.35.0`, not `v4.34.1` |

Published throughput: the Lean4Lean abstract reports it "running between 20% and 50% slower" than the C++ kernel. No checker throughput was measured here.

Derived:

- *Version skew.* The exporter must be built with the Lean that produced the modules. A project locked to v4.34.1 cannot use either head as is; whether the `v4.34.0` exporter tag works with 4.34.1 modules is unknown.
- *Lineage.* Lean4Lean is compiled by Lean's own compiler into the same runtime, so it shares the binary lineage of section 5: algorithmic cross-checking, not binary independence.
- *`nanoda_lib` moves the question to `rustc`.* Its binary comes from the chain of sections 2–3 and its build runs procedural macros. Whether `mrustc` can compile it is unknown.
- *The exporter is shared.* External checkers establish that exported declarations type-check; that the exported statement is the intended one needs a comparison outside Lean.

### 7. Other verified-compiler bootstraps as reference points

Basis: source + documentation (pinned heads)

**CakeML compiles the compiler inside the logic.** `compiler/bootstrap/README.md:1–2`: "Theories that perform proof-grounded bootstrapping of the CakeML compiler in HOL." Translation yields a deep embedding where "each deep embedding comes with a certificate theorem" (`compiler/bootstrap/translation/README.md:1–5`); compilation produces "the verified machine code implementing the compiler itself" (`compiler/bootstrap/compilation/README.md:1–3`). For x64, `compiler/bootstrap/compilation/x64/x64BootstrapScript.sml:29–37` defines `compiler_compiled` with `output_filename = "cake.S"`, and `proofs/x64BootstrapProofScript.sml:65–66` derives `cake_compiled_thm` by `MATCH_MP compile_correct_eval`. No compiler binary sits between source and machine code. What remains is HOL4 on Poly/ML (`README.md:7–10`) and "the system's C compiler to build `basis_ffi.c`" (`how-to.md:48–51`).

**CompCert extracts.** `Makefile:292–302` runs `extraction/extraction.v` through Rocq and fails if any `AXIOM TO BE REALIZED` remains; lines 307–308 build `ccomp` from the extracted OCaml. The file holds 26 `Extract Constant` and 7 `Extract Inlined Constant` directives (counted) substituting hand-written OCaml, for example `Allocation.regalloc => "Regalloc.regalloc"` (line 77). The path from proof to `ccomp` passes through unverified extraction, these realizations and `ocamlopt`.

**CertiRocq and MetaRocq.** CertiRocq "targets WebAssembly and Clight"; "Large parts of the CertiRocq compiler have been verified whereas others are in the process of being verified" (`README.md:14–16`); `bootstrap/` holds "the bootstrapped CertiRocq plugin for Rocq and a CertiRocq-compiled variant of MetaRocq's safe type checker" (lines 47–48). MetaRocq's safe checker is "fuel-free and verified" and "relies on a postulate of strong normalization" (`README.md:128–134`). This is the closest existing case of a proof checker compiled by a largely verified pipeline, for Rocq.

### 8. Provenance frameworks

Basis: draft specification text (SLSA main branch; in-toto)

SLSA's draft build levels (`spec/build-track-basics.md:8–12`) run from L1 "Provenance showing how the package was built" to L4 "Complete dependency provenance enforced by the build platform". The compromised-build-tool threat (`spec/threats.md:1108–1120`) is "partially mitigated by treating build tooling, including OS images, as any other artifact to be verified prior to use". The FAQ defines "verified reproducible" as "using two or more independent build platforms" and warns that "Reproducers must truly be independent, lest they all be susceptible to the same attack" (`spec/faq.md:36–54`). An in-toto Statement binds a predicate to subjects, each of which "MUST have `digest` set" (`spec/v1/statement.md:9–37`).

Derived: provenance records which binaries produced which binaries; applied recursively it reproduces the seed chain of section 2 and ends in a binary. It is the right carrier for a DDC result and for the per-file identity of section 5, and replaces neither.

### 9. Three ways to break the dependence, ranked

Basis: derived from sections 1–8

| | Checker-first | Verified checker | Dual-compiler DDC of `rustc` |
| --- | --- | --- | --- |
| Idea | `rustc` untrusted; each build's evidence checked by a small, independently built checker | checker proved correct and compiled by a verified pipeline | compare `rustc` built from two unrelated seeds |
| Removes trust in | `rustc`, LLVM, linker, for the checked property | checker algorithm and its compiler | the downloaded `rustc` seed |
| Still trusted | checker binary, exporter, statement, host OS | the prover kernel that verified the checker, runtime shims | `mrustc`, host C/C++ compilers, sources of every release in the chain |
| Available today | parts: `nanoda_lib`, Lean4Lean, `lean4export`, with the skew of section 6 | no Lean kernel with an in-logic bootstrap was found | only with `mrustc`: `gccrs` "is in a very early stage and not usable yet for compiling real Rust programs" (`README.md:10`); `rustc_codegen_gcc` "can be loaded by the existing rustc frontend" and "requires a patched libgccjit" (`Readme.md:6, 17`) |
| Cost | per build: one export and N checks | large one-off proof effort | per release: ten compiler builds to reach 1.99.1 |
| Fails when | all checker lineages share a payload, or the exporter misstates the theorem | the verified pipeline's own seed is subverted | `cT` shares the payload, or compilation is not deterministic |

Ranking (derived). *Checker-first* is the only design that removes `rustc` from the soundness argument and is partly buildable now, so it is the primary gate. Checker assurance should come from agreement of verdicts across lineages: the C++ kernel, Lean4Lean, `nanoda_lib` built by official `rustc`, and, if it can be built, `nanoda_lib` built by `mrustc` plus a C compiler. Verdict agreement needs no bit-identical binaries. *Dual-compiler DDC* protects a different asset, the shipped compiler binary, and belongs at release cadence; `rustc_codegen_gcc` gives back-end diversity only. *Verified checker* is the long-term replacement for N-version agreement.

Prerequisites exposed here: have the audit hash every executable file of the Lean distribution, not only the launcher; pin exporter and checker to the locked Lean version; record DDC and checker verdicts as attestations over digests.

### 10. Performance, comprehensibility and validation dimensions

Basis: execution where a number is given; otherwise not measured

| Dimension | Result |
| --- | --- |
| L1 authoring and proof velocity; L4 generated-code performance | not measured |
| L2 toolchain build time | TinyCC: six builds in 47 s, 56 s and 40 s. `mrustc`, the `rustc` chain, Lean from its seed: not measured |
| L3 compile latency | Lean 4.34.1 on `DdcWheelerProofs.lean`: 1.10 s wall, one run, including a resource-limiting wrapper |
| L5 checking throughput, cold start | `lean --version`: median 0.118 s (min 0.101, max 0.291; 5 runs). External checkers: not measured |
| L6 footprint | `bin/lean` 9,024 B; `libleanshared.so` 233,708,536 B; installed Lean toolchain about 3.0 GB |
| C1 auditability | Proof #1 has three assumptions, Proof #2 nine; the `rustc` seed is two manifest lines; Lean's seed is 613 MB of generated C; CompCert's extraction has 33 hand-written realizations |
| C2 orthogonality | binary provenance (DDC, attestations) and algorithmic soundness (checker proofs) are independent axes |
| V1 adequacy, mutation, non-vacuity | satisfiable-assumptions theorem; taint countermodel; TinyCC negative control N2 |
| V2 differential checking | two host compilers agree at the second generation (TinyCC); checker differential fuzzing not examined |
| V3 weak memory, crash, hardware leakage | not examined |
| V4 held-out replay | not measured: no Rust bootstrap or external checker run was executed |

## Boundaries

**Not examined**

- Any execution of `mrustc`, of a `rustc` bootstrap, or of the 1.90.0 → 1.91.1 comparison; the binary-equality claim is upstream documentation.
- The previous-stable chain from 1.91.1 to 1.99.1, including whether a point release of the previous minor (Guix uses 1.98.1) is accepted where `src/stage0` names 1.98.0.
- The contents of Lean's generated seed files, and the Lean distributions for the other three platforms in the lock.
- Running the Anneal audit binary or substituting a modified `libleanshared.so`: the identity gap is derived from source and file inspection, not demonstrated.
- LLVM 23, the linker and vendored crates as seeds of `rustc`; full-source C bootstraps beneath the host C compilers.
- The text of Thompson's paper: the publisher page could not be retrieved; only the bibliographic record was confirmed.

**Unknown**

- Whether `mrustc` can compile `nanoda_lib` 0.4.32 with its procedural-macro dependencies.
- Whether Lean4Lean has a revision matching Lean v4.34.1, and whether `lean4export` `v4.34.0` reads 4.34.1 modules.
- Whether `rustc` 1.99.1 builds are bit-for-bit deterministic across hosts, which DDC requires.

**Known not to apply**

- The TinyCC result is not evidence about `rustc`; it shows the procedure and its pitfalls on a much smaller compiler.

**Unsupported**

- `gccrs` as a compiler for `rustc` sources, by its own README.
- Lean4Lean checking proofs that rely on `reduceBool`.
- A Guix package for Rust 1.99 at the examined revision.

**Stronger conclusions the evidence does not support**

- That an external checker makes the Lean binary untrusted: the exporter still runs inside it.

## Evidence

GitHub revisions were resolved with the commits API on 2026-11-20 and files read from `raw.githubusercontent.com` at those revisions. Paths and line ranges are cited inline in Findings.

| Subject | Revision |
| --- | --- |
| `rust-lang/rust` (tag 1.99.1) | `58cf8f9c35b355199727627d07ae34a4e2846d67` |
| `thepowersgang/mrustc` | `4e020d6b307c738434209435e9b75b7d81b00077` |
| GNU Guix, `codeberg.org/guix/guix` | `0a08fa79a9e9…`, in full in `REPORT.json` |
| `NixOS/nixpkgs` | `dd621dfccea326fef05c6ce516cf99c3cfc94561` |
| `leanprover/lean4` (v4.34.1) | `5045d0056413266e57c625dcd7c365b10e377c52` |
| `digama0/lean4lean` | `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` |
| `ammkrn/nanoda_lib` | `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` |
| `leanprover/lean4export` | `df81913eee5519d5a88ae5b0fd701b5298cc29ab` |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` |
| `CakeML/cakeml` | `2874b664e10939a3ee462215b2e068c89c1f70eb` |
| `AbsInt/CompCert` (3.18) | `2685140bf72c959446981fb99b5e44a8975021bc` |
| CertiRocq | `ab66e0164e7ecb63e5af95c90c8e479068bf95c2` |
| MetaRocq | `51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56` |
| `Rust-GCC/gccrs` | `f802cdb6101ee21743df0bbca3478eafadda9407` |
| `rust-lang/rustc_codegen_gcc` | `3d46c6c1460843f1803fae04caaf6f5e6771798f` |
| `slsa-framework/slsa` | `8c3161670b7a6cf7bd6d858b2332ae7eb0838b0c` |
| `in-toto/attestation` | `50bf01716982189898823e90586075f37cd9bb7d` |
| `TinyCC/tinycc` (built) | `56b75101ef323cca9e45c925ba17042ce87134de` |

Papers: Thompson, "Reflections on Trusting Trust", CACM 27(8):761–763, 1984, DOI 10.1145/358198.358210; Wheeler, arXiv:1004.5534; Carneiro, arXiv:2403.14064v3.

Support material in `support/`:

- `DdcWheelerProofs.lean`, `DdcWheelerProofs.out.txt`: the Lean restatement and Lean's output (`lean support/DdcWheelerProofs.lean`).
- `ddc_tinycc.sh`, `ddc_tinycc_result.json`: the DDC procedure and the recorded third run (`ddc_tinycc.sh <workdir> gcc <clang> "-isystem <lean prefix>/include/clang"`).
- `rustc_stage0_census.py`, `guix_rust_chain.py`, `lean_toolchain_identity_probe.py`, `git_tree_census.py`, each with a `*_result.json`; the Guix result holds the full `mrustc` revisions Guix pins.
- `lean4export_tags_result.json`.

Counts without a script used `grep -c`, `git grep -l -i` and `du -sh`.

## Revalidation

- **Seed of another Rust release.** `python3 support/rustc_stage0_census.py --rev <commit>`. More than one (date, version) pair, or a version that is not the previous minor, means the previous-stable rule changed; re-read `detect_compiler` in `src/tools/bump-stage0/src/main.rs`.
- **Chain length.** Check `mrustc`'s `README.md` "Progress" list and the version table in `TestRustcBootstrap.sh`. For Guix, run `python3 support/guix_rust_chain.py rust.scm` on the new `gnu/packages/rust.scm`. For nixpkgs, read `bootstrapVersion` in the newest `1_NN.nix`.
- **DDC procedure.** Re-run `support/ddc_tinycc.sh` with any two unrelated C compilers; all five `checks` must be `true`. Absolute digests were observed on one host; the equalities are what should carry over.
- **DDC argument.** `lean support/DdcWheelerProofs.lean` must exit 0 and print five "does not depend on any axioms" lines.
- **Lean identity.** `python3 support/lean_toolchain_identity_probe.py --prefix "$(lean --print-prefix)" --lock trusted/lean/foundation-lock.json`. The gap is closed when `lock.library_digests_listed` is `true` for every library in `libraries_defining_kernel_entry_points`, or when `tool_admission` hashes `lib/lean/*.so`.
- **Checker skew.** Compare `lean-toolchain` in `lean4export` and `lean4lean` with the lock.
- **Alternative compilers.** Re-read the opening of the `gccrs` README.
- **No cheap check exists** for the 1.90.0 → 1.91.1 binary equality or the nine further builds: that needs `TestRustcBootstrap.sh 1.90.0` and successive `x.py` builds.
