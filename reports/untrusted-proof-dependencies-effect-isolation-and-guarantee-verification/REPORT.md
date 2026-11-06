# Untrusted Proof Dependencies, Elaboration Side-Effect Isolation, and Guarantee-Preserving Verification in Lean 4 and Peer Systems

## Summary

Verification architectures that separate a small Trusted Computing Base (TCB)
from a large, untrusted proof-engineering and theory layer—such as Anneal's
split between `trusted/` (`Trusted.lean`, `anneal-rustc-capture`,
`anneal-audit`) and untrusted `theory/` + `Proof.lean`
(`joshlf/anneal@287e7ad5182f74f25fcaf9098840f5f39aa601d6`,
`docs/trust-model.md`)—require a three-part guarantee whenever a trusted target
takes an untrusted dependency $D$:

1. **Property 1 (Build- and Elaboration-Time Side-Effect Isolation):**
   Compiling, importing, or auditing $D$ must not execute arbitrary host I/O
   (reading secrets via `include_str`, overwriting upstream `.olean` files,
   spawning persistent background processes, or opening network/IPC sockets).
2. **Property 2 (Specification and Statement Non-Contamination):** $D$ must not
   alter the meaning of the target theorem statement (`Trusted.CrateTheorem
   Mir.crate`) by redefining or shadowing specification constants, overriding
   notations or macros, injecting high-priority or LIFO typeclass instances into
   the statement, or mutating compiler overrides (`@[implemented_by]`,
   `@[extern]`, `@[csimp]`).
3. **Property 3 (Proof-Soundness and Axiom Discipline):** $D$ must not prove the
   target theorem vacuously via axioms (`axiom`, `sorryAx`,
   `Lean.trustCompiler`, `_native.*`), `unsafe` or `partial` definitions,
   in-process kernel bypasses (`debug.skipKernelTC`, `addDeclWithoutChecking`,
   `lakeAdd`), or malformed `.olean` memory images (`src/runtime/compact.cpp`).

Combining primary-source audits across 18 pinned repositories with 15 standalone
runnable Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) and Linux
`7.1.6-1rodete1-amd64` probes in [`support/`](support/) establishes seven central
results:

1. **No Single Existing Lean 4 Tool Enforces All Three Properties simultaneously,
   and `SafeVerify` (`b291b588a53999a7e837dda61c7dbfe8c550c814`) Has Five
   Empirical Soundness/Verification Bypasses:**
   - `lean4checker` (`91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`) and built-in
     `leanchecker` (`v4.34.1`) enforce only per-module `Environment.replay`
     (Level III of the Lean FRO verification hierarchy), trusting `.olean`
     pointer-graph deserialization, providing no statement comparison or build
     sandboxing, and remaining vulnerable in `v4.34.1` to three `.olean`-level
     kernel replay bypasses: negative GMP `mpz` `Nat` literals crafted via
     `lean4#15717`'s safe `ST.Ref.mk` coercion (`support/ProbeNegativeNatLit.lean`),
     `ModuleData.constNames` vs. `ConstructorVal.name` mismatches (`lean4#15100`),
     and forged `.quotInfo` entries (`lean4#15101`, where
     `environment::add_quot()` in `src/kernel/quot.cpp:47-49` is a silent no-op
     once `Init.Prelude` is loaded; `support/ProbeReplayExploits.lean`).
   - `GasStationManager/SafeVerify` (`b291b588a53999a7e837dda61c7dbfe8c550c814`)
     compares `Target.olean` against `Submission.olean` without sandboxing
     compilation, and our runnable probe [`support/SafeVerifyBugsProbe.lean`](support/SafeVerifyBugsProbe.lean)
     demonstrates five concrete flaws: (a) `partial def` completely bypasses
     `--disallow-partial` because `isCompilerUnsafeRecName` (`Main.lean:28-30,
     157, 202`) whitelists every `._unsafe_rec` constant while Lean emits the
     user declaration as `.opaqueInfo` (`isPartial = false`); (b)
     `checkImportSuperset` (`Main.lean:232-254`) permits extra helper module
     imports while `replayFileWithEnv` (`Main.lean:195-205`) only replays
     `Submission.olean`'s `map₂`, allowing an imported `EvilHelper.olean` using
     `set_option debug.skipKernelTC true` to prove `False` with `passed = true`;
     (c) `equivDefn` (`Main.lean:58`) disables definition-value comparison
     whenever a target definition mentions `sorryAx`; (d) `supplementedDecls`
     (`Main.lean:418-434`) is computed and then discarded at line 433; and (e)
     `SafeVerify`'s `(toString n).startsWith "-"` check (`Main.lean:258-286`)
     for negative GMP `mpz` `Nat` literals returns `false` in Lean `v4.34.1`
     because `Nat.reprFast` (`src/lean/Init/Data/Repr.lean:238-241`) takes the
     `n < USize.size` (`lean_nat_big_lt(-2^32, 2^64) == true`) fast path and
     strips the sign via `mpz_get_ui` (`"4294967296"`).
   - `leanprover/comparator` (`865edc14486c3388e9225daa971da8e157488c3e`,
     upstreamed into Lean `v4.35.0` as `lake comparator [--paranoid]` in PRs
     `#14885`, `#15005`, `#15145`, and `#15156`) is the closest upstream
     counterpart to Anneal: it sandboxes `lake build` and `leanexport`, exports
     kernel declarations to NDJSON (`lean4export`
     `df81913eee5519d5a88ae5b0fd701b5298cc29ab`), and rechecks them out-of-sandbox
     in `leanchecker-paranoid` (`MI_SECURE=3`), `nanoda_bin`
     (`8de7e0c4ed3052745a7f8725164efd9e76d84c56`), `lean4lean`
     (`67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`), and formally verified
     `con-leche` / `con-ron` (`lean-kernel-arena`
     `a6a56d26c0c94df807368d218725e9414ab4209e`).
2. **How Anneal's `TrustedBoundary.lean` Defeats the 2026 `.olean` and Replay
   Exploits—and One Newly Discovered Enclosing-Namespace Shadowing Seam:**
   - Anneal's Phase 2 auditor (`trusted/audit/TrustedBoundary.lean` in
     `joshlf/anneal@287e7ad5182f74f25fcaf9098840f5f39aa601d6`) defeats negative
     GMP `mpz` `Nat` literals via `rebuildNat` (`Nat.ofDigits 10 (Nat.toDigits
     10 n)` at line 625, which maps `-2^32` to `['*','*',...]` $\rightarrow$ `0`
     and breaks the forged proof during `base.toKernelEnv.replay`), defeats
     `lean4#15100` (`constNames == constants.map ConstantInfo.name` at line 681
     plus single-pass whole-DAG replay at line 773), defeats `lean4#15101`
     (rejecting `.quotInfo` outside `Init` at line 661 plus whole-DAG replay),
     and defeats `partial def` via `isStructuralRecCompilerHelper` (lines
     666–685, verifying `env.checked.get.find? baseName` is `.defnInfo` with
     `!isUnsafe && !isPartial`).
   - However, [`support/retroactive_mutation/RunRetroactiveMutationProbe.lean`](support/retroactive_mutation/RunRetroactiveMutationProbe.lean)
     uncovers a subtle seam when `Proof.lean` opens `namespace Proof`: because
     `validateLocalConstant` (`TrustedBoundary.lean:647`) only checks
     `(privateToUserName ci.name).getRoot == \`Trusted` while `isValidSourceIdent`
     (`line 355`) forbids `_root_`, an untrusted `Theory.lean` can declare
     `namespace Proof.Trusted def CrateTheorem (_ : Crate) : Prop := True end
     Proof.Trusted`. Because `(\`Proof.Trusted.CrateTheorem).getRoot` is
     `` `Proof `` (not `` `Trusted ``), this declaration **passes both Phase 1
     and Phase 2**, and inside `namespace Proof` in `Proof.lean`,
     `Trusted.CrateTheorem Mir.crate` resolves to `Proof.Trusted.CrateTheorem`
     (`True`). Closing this seam requires: (a) checking
     `(privateToUserName ci.name).components.contains \`Trusted` in non-`Trusted`
     modules, (b) emitting `theorem Proof.verify_crate : Trusted.CrateTheorem
     Mir.crate` at the root namespace in `Proof.lean`, and (c) checking
     `kci.type == mkApp (mkConst ``Trusted.CrateTheorem) (mkConst ``Mir.crate)`
     in `Kernel.Environment`.
3. **Why Lean 4's `module` System (`public`, `meta`, `meta import`, `import all`,
   `IRPhases`) Is a Build-Performance Boundary, Not a Security or Trust
   Boundary:**
   - Even when `Consumer` uses `module` and writes plain `import Dep` (without
     `meta import Dep`), `Dep` still exports and executes `public` `syntax`,
     `macro`, `macro_rules`, `notation`, `elab`, `tactic`, `@[simp]`,
     `@[instance]`, and `meta initialize` blocks in `Consumer` because `aux_def`
     (`src/Lean/Elab/AuxDef.lean:39`) marks macro/elaborator declarations `meta`,
     `declMapExt` (`src/Lean/Compiler/IR/CompilerM.lean:87-111`) exports the full
     IR of all `meta` declarations into `Dep.olean`, and `getIRPhases`
     (`src/Lean/Compiler/MetaAttr.lean:73-90`) checks `isMarkedMeta` before
     `mod.irPhases` ([`support/module_system/`](support/module_system/)).
   - Critically for kernel auditors, under `module`, `AddDecl.addDeclCore`
     (`src/Lean/AddDecl.lean:112-128`) weakens **every `theorem` and every
     non-`@[expose]` `def` into a `ConstantInfo.axiomInfo` in `Dep.olean` and
     `Dep.olean.server`**, storing the actual `.thmInfo` proof terms and
     `.defnInfo` bodies **only in `Dep.olean.private`**! Meanwhile,
     `Lean.collectAxioms` (`#print axioms`,
     `src/Lean/Util/CollectAxioms.lean:77-86, 113-155`) trusts an unverified
     `PersistentEnvExtension` (`exportedAxiomsExt`) in `Dep.olean` without
     walking imported constant bodies.
   - Any file can bypass `module` encapsulation via `import all` or by omitting
     `module`, and Lake's `allowImportAll` enforcement is commented out in
     `v4.34.1` (`src/lake/Lake/Build/Module.lean:418-442`) while
     `Module.fetchOLeans` (`line 496`) unconditionally passes `.olean.private`,
     `.olean.server`, and `.ir` (`-- TODO: this is too dangerous!`).
4. **Why `lakefile.toml` Alone Does Not Prevent Code Execution or Kernel
   Bypasses During `lake build`, `lake setup-file`, or `lake serve`:**
   - Auditing `src/lake/Lake/Load/Toml.lean` (`v4.34.1`) shows that while
     `loadTomlConfig` parses pure TOML during workspace loading (omitting
     `extern_lib`, `script`, `post_update`, and custom `target` declarations),
     twelve `lakefile.toml` fields still trigger native code execution (`dlopen`),
     unverified `.olean` injection, or kernel bypasses during `lake build`,
     `lake setup-file` (invoked automatically by the LSP server), or `lake serve`:
     `precompileModules = true`, `plugins`, `dynlibs`,
     `leanOptions = { "debug.skipKernelTC" = true }`, `moreServerOptions`,
     `moreLeanArgs = ["--trust=100"]`, `weakLeanArgs`, `moreGlobalServerArgs`,
     `moreLeancArgs`/`moreLinkObjs`, `defaultFacets = ["shared"]`,
     `extraDepTargets`, `[[require]]` (transitively loading a dependency's
     `lakefile.lean`), and `preferReleaseBuild`/Reservoir barrels (plus Lake's
     `.trace` cache not hashing output `.olean` files on disk, `lean4#16123`).
5. **Cross-Prover Design Duality (`GHC Safe Haskell`, `Agda --safe`, `Rocq
   coqchk`, `Metamath Zero mm0-c`, `watt`, `cackle`, `endo`):**
   - GHC Safe Haskell (`ghc/ghc@37ad47105079d55e0da68f3c660f9bbd2e18047a`,
     `compiler/GHC/Driver/Main.hs:1058-1275`) is the exact type-system
     structural dual of Anneal's three-tier model: `-XSafe` (`Sf_Safe`)
     corresponds to `.theory`, `-XTrustworthy` (`Sf_Trustworthy`) corresponds to
     `.trusted .vetted`, and `-XTrustworthy` gated by `-fpackage-trust` (`-trust
     <pkg>`) corresponds to `.trusted (.candidate f)`.
   - Agda's `--safe` (`agda/agda@ec45c73baa385bd90ad8db80f0a9d21cdafe8dc5`)
     safely permits reflection (`TC` monad) during typechecking because `evalTCM`
     (`src/full/Agda/TypeChecking/Unquote.hs:630-703`) interprets a deep
     embedding over 42 closed primitives rather than native `IO` (`tcExec`
     requires `--allow-exec`, which `--safe` bans). However, our audit uncovered
     a backend-compilation boundary bypass in Agda `--safe`: `tcPragmaForeign`
     and `tcPragmaCompile` (`Unquote.hs:1150-1159`) mutate `stForeignCode` and
     `defCompiledRep` without checking `optSafe`, persist into `.agdai`
     interface files (`Imports.hs:1660, 1707`, `DeadCode.hs:58, 65-67`), and are
     spliced verbatim into generated Haskell/JS code by `MAlonzo` and `JS`
     backends whenever a `--safe` module is compiled (`agda --compile --safe`)
     or imported by a compiled module.
6. **Quantified Phase 1 vs. Phase 2 Conservativity (`40 / 42` Benign Features
   Pass Phase 2) and Runnable Pure-Macro Prototype (`support/PureMacroAudit.lean`):**
   - Testing 42 representative Lean 4 proof-engineering constructs in
     [`support/PreflightVsPhase2Probe.lean`](support/PreflightVsPhase2Probe.lean)
     shows that `TrustedBoundary.lean`'s Phase 1 surface-syntax allowlist rejects
     40 of 42 constructs (including 3 accidental child-node omissions in
     `Parser.Command.optDeriving`, `Parser.Termination.suffix`, and
     `Parser.Tactic.optConfig`), whereas **all 40 rejected pure constructs pass
     Phase 2** (`loadExts := false`, `validateLocalConstant` +
     `isStructuralRecCompilerHelper`, `base.toKernelEnv.replay`).
   - [`support/PureMacroAudit.lean`](support/PureMacroAudit.lean) demonstrates
     that a verifier can safely admit custom `notation`, `infixl`, `syntax`, and
     `macro_rules` in `Theory.lean` *without OS sandboxing* by combining (1)
     **Macro-Definition Purity** over `@[macro]` constant cones (excluding
     `unsafe`, `@[extern]`, local `@[implemented_by]`, `dbgTrace*`, `dbgSleep`,
     `dbgStackTrace`, `unsafeIO`, `ST.Prim.*`, `IO.Prim.*`), (2) **Post-Expansion
     Syntax Auditing** in pure `MacroM` before `CommandElabM`/`TermElabM` runs,
     and (3) **Namespace-Component + Kernel Statement-Identity Verification**
     (passing all 8 positive and negative test cases).
7. **Hardened Unprivileged Linux Process Sandboxing (`+3.11 ms` / `+1.19%`
   Overhead, `CLONE_THREAD`-Preserving):**
   - Lifting Phase 1 completely requires an OS sandbox because `include_str`
     (`src/Lean/Elab/BuiltinTerm.lean:431-446`) reads arbitrary host files during
     elaboration and embeds their contents as a pure `.safe` `String` constant
     that passes Phase 2 ([`support/Phase2FeatureAudit.lean`](support/Phase2FeatureAudit.lean)).
   - [`support/hardened_sandbox_probe.py`](support/hardened_sandbox_probe.py) and
     [`support/linux_sandbox_probe.py`](support/linux_sandbox_probe.py)
     demonstrate an unprivileged Linux `7.1.6-1rodete1-amd64` sandbox combining
     **Landlock ABI v9** (`LANDLOCK_ACCESS_FS_RESOLVE_UNIX`,
     `LANDLOCK_SCOPE_ABSTRACT_UNIX_SOCKET`, `LANDLOCK_SCOPE_SIGNAL`) with a
     **`seccomp-bpf` filter** that returns `ENOSYS` on `SYS_clone3` (causing
     glibc `pthread_create` to fall back to `SYS_clone`), permits `SYS_clone`
     when `CLONE_THREAD` (`0x00010000`) is set so Lean's multi-threaded
     `Task.spawn` / `IO.asTask` pool runs unmodified, and returns `EPERM` on
     process forks (`!CLONE_THREAD`), `SYS_fork`, `SYS_vfork`, `SYS_setsid`,
     `SYS_socket`, `SYS_connect`, `SYS_ptrace`, `SYS_process_vm_readv/writev`,
     and post-exec `SYS_execve`/`SYS_execveat` (as well as composing with
     `bubblewrap 0.12.0` via `bwrap --unshare-all --die-with-parent --tmpfs /run
     --seccomp <fd>`). Across $N = 20$ runs, the sandbox blocks all 11 host I/O,
     `include_str`, `AF_UNIX` (`/run/docker.sock`), UDP, `ld-linux-x86-64.so.2`,
     `setsid` sleeper-daemon, and `ptrace` vectors while adding **`+3.11 ms`
     (`+1.19%`, `264.8 ms` vs. `261.7 ms`)** and producing byte-for-byte
     identical `.olean` files.

---

## Applicability

The findings, source citations, and runnable verification probes in this report
apply to the pinned repositories and revisions recorded in `REPORT.json`:

| Subject | Pinned Revision / Version | Role and Scope in This Report |
| :--- | :--- | :--- |
| `joshlf/anneal` | `287e7ad5182f74f25fcaf9098840f5f39aa601d6` | Defines the reference trust model (`docs/trust-model.md`), three-tier module classification (`.foundation`, `.trusted`, `.theory`), and two-phase boundary auditor (`trusted/audit/TrustedBoundary.lean`, `trusted/audit/src/lib.rs`, `trusted/lean/Trusted.lean`). (See also companion package `anneal-trusted-boundary-audit-olean-stubbing-and-conservativity`.) |
| `leanprover/lean4` | `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) | Pinned Lean 4 toolchain governing the C++ kernel (`src/kernel/`), `.olean` compactor (`src/runtime/compact.cpp`, `src/library/module.cpp`), elaboration monads (`src/Init/Prelude.lean`, `src/Lean/CoreM.lean`), `module` system (`src/Lean/AddDecl.lean`, `src/Lean/Environment.lean`), `Replay.lean`, `LeanChecker.lean`, and Lake (`src/lake/`). Upstream PRs `#13940`, `#14885`, `#14947`, `#15005`, `#15145`, and `#15156` (merged onto `master` for `v4.35.0+`) are cited by exact commit SHA where `lake comparator` evolved. |
| `GasStationManager/SafeVerify` | `b291b588a53999a7e837dda61c7dbfe8c550c814` | `.olean`-based submission verifier audited and tested in `support/SafeVerifyBugsProbe.lean`. |
| `leanprover/comparator` | `865edc14486c3388e9225daa971da8e157488c3e` | Challenge-solution sandbox and multi-kernel verification orchestrator (`Landrun.lean`, `Export.lean`, `Compare.lean`, `Kernel.lean`). |
| `leanprover/lean4checker` | `91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709` | Standalone environment replay verifier compared against built-in `leanchecker` in Lean `v4.34.1`. |
| `leanprover/lean4export` | `df81913eee5519d5a88ae5b0fd701b5298cc29ab` (format `3.1.0`) | NDJSON kernel declaration exporter (`Export.lean`, `Main.lean`). |
| `ammkrn/nanoda_lib` | `v0.4.31` (`8de7e0c4ed3052745a7f8725164efd9e76d84c56`) | Independent Rust implementation of the Lean 4 kernel (`src/env.rs`, `src/tc.rs`). |
| `digama0/lean4lean` | `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` | Pure Lean 4 kernel reimplementation (`Lean4Lean/Verify/Environment/Basic.lean`, `Lean4Lean/Primitive.lean`). |
| `leanprover/lean-kernel-arena` | `a6a56d26c0c94df807368d218725e9414ab4209e` | Benchmark and conformance harness across 24 independent Lean 4 kernel implementations (including formally verified `con-leche` and `con-ron`). |
| `BSVKey/bsvkey-axiom-proofs` | `180479de363d3f7a81652df4f41f6f999d66fc64` | Production `#guard_msgs in #print axioms` discipline combined with `lean4checker --fresh` in CI. |
| `agda/agda` | `ec45c73baa385bd90ad8db80f0a9d21cdafe8dc5` | Agda `--safe` flag, coinfective import checker (`Interaction/Imports.hs`), reflection interpreter (`TypeChecking/Unquote.hs`), and `MAlonzo`/`JS` compiler backends. |
| `ghc/ghc` | `37ad47105079d55e0da68f3c660f9bbd2e18047a` | GHC Safe Haskell (`-XSafe`, `-XTrustworthy`, `-XUnsafe`, `-fpackage-trust` in `compiler/GHC/Driver/Main.hs`). |
| `rocq-prover/rocq` & `MetaRocq/metarocq` | `4402a03e266932251cbd32d1fc5fd1125e64ce8d` & `51b14e4bb5f45808f00f60208ff8dbf31f3ad6f56` | Rocq standalone `.vo` verifier `coqchk` (`checker/validate.ml`, `checker/check.ml`) and verified `SafeTemplateChecker`. |
| `digama0/mm0` | `0d414c0bfdaaeb7fea571895127abc1fa5a3d956` | Metamath Zero C verifier `mm0-c` (`mm0-c/verifier.c`, `mm0-c/main.c`) enforcing lockstep `.mm0`/`.mmb` separation. |
| `dtolnay/watt`, `davidlattimore/cackle`, `endojs/endo` | `8f16788f649efcfb6c1995d5c7357e2504d426fb`, `f9f09eeb1f016aaf50adb8e7503efeef3d28595d`, `679d9afaa4acd089f578055118b6711a22537f05` | Language-level build/macro/dependency isolation systems in Rust and Hardened JavaScript (SES / LavaMoat). |

---

## Findings

### Finding 1: The Three-Property Untrusted-Dependency Guarantee and Comparative Audit of Lean 4 Verification Tools

Basis: `source` + `execution`

#### 1.1 Anneal's Three-Property Guarantee for Untrusted Dependencies

In `joshlf/anneal@287e7ad5182f74f25fcaf9098840f5f39aa601d6` (`docs/trust-model.md`,
`trusted/audit/TrustedBoundary.lean`, `trusted/audit/src/lib.rs`), Anneal scales
verification of Rust programs by keeping `theory/` (program logics, tactic
automation, and general lemmas) and per-crate `Proof.lean` files **outside**
`trusted/`. For this separation to hold when `Proof.lean` imports `theory/`, the
verification pipeline must enforce three distinct guarantees:

1. **Property 1 (Side-Effect Isolation):** Untrusted `.lean` files must not
   perform arbitrary host side effects during compilation or auditing. In
   baseline `anneal-audit`, this is enforced before invoking `lean` by Phase 1
   (`TrustedBoundary.lean` `"preflight"` mode, invoked from
   `trusted/audit/src/lib.rs:297-315`), which parses every `.lean` source file
   via `Parser.parseHeader` and `Parser.parseCommand` without running the
   elaborator and validates every `SyntaxNodeKind` against a closed allowlist.
   Additionally, `trusted/audit/src/lib.rs:146-185` copies only `.lean` source
   files into a fresh temporary staging directory (rejecting pre-existing
   `.olean`, `.ir`, `.c`, or `.so` files in the source tree at lines 28–31) and
   compiles them directly via `lean` (bypassing `lake` and `lakefile.lean`).
2. **Property 2 (Specification and Statement Non-Contamination):** Untrusted
   `.lean` files must not change the meaning of `Trusted.CrateTheorem
   Mir.crate`. In `anneal-audit`, this is enforced by:
   - **Statement-Origin Separation:** `Trusted.lean` and generated `Mir.lean` are
     compiled *before* `Theory.lean`, and `Proof.lean` states `theorem
     verify_crate : Trusted.CrateTheorem Mir.crate` using only those pre-compiled
     constants.
   - **Tiered Import DAG and Namespace Hygiene (`TrustedBoundary.lean:511-565,
     647`):** `.foundation` modules may import only `.foundation`; `.trusted`
     modules may import only `.foundation` and `.trusted`; only `.theory` (and
     `Proof.lean`) may import `.theory`.
   - **Extension Suppression (`loadExts := false` at `TrustedBoundary.lean:506`):**
     Phase 2 loads `.olean` files with `loadExts := false` and `trustLevel := 0`,
     ignoring all serialized persistent environment extensions (`@[simp]`,
     `@[csimp]`, `@[implemented_by]`, `@[extern]`, `@[init]`, custom attributes,
     and `exportedAxiomsExt`).
3. **Property 3 (Proof-Soundness and Axiom Discipline):** Untrusted `.lean`
   files must not discharge `Trusted.CrateTheorem Mir.crate` vacuously. In Phase
   2 (`TrustedBoundary.lean:586-773`), `anneal-audit`:
   - Rejects any non-foundation `.axiomInfo`, `.opaqueInfo`, `.quotInfo`, or
     `unsafe` constant (`lines 655-665`), allowing `ci.isPartial` if and only if
     `isStructuralRecCompilerHelper` (`lines 666-685`) confirms it is a
     compiler-generated `<base>._unsafe_rec` companion whose `<base>` in
     `env.checked` is a `.defnInfo` with `!isUnsafe && !isPartial`.
   - Deep-rebuilds every `Expr`, `Level`, and `Literal.natVal` (`rebuildNat` at
     line 625: `Nat.ofDigits 10 (Nat.toDigits 10 n)`) and checks that the
     transitive constant closure of every audited declaration contains no
     `sorryAx` and only the three standard classical axioms
     `{propext, Quot.sound, Classical.choice}` (`lines 586-620`).
   - Replays the union of all non-foundation constants in a single pass over the
     foundation-only kernel environment via `base.toKernelEnv.replay locals`
     (`line 773`).

#### 1.2 Architectural Comparison of Existing Lean 4 Verifiers and External Kernels

The table below compares Anneal's `anneal-audit` against every major tool in the
Lean 4 verification ecosystem at their pinned revisions in `REPORT.json`:

| Tool & Pinned Revision | Primary Input Format | Property 1: Elaboration & Import Side-Effect Isolation | Property 2: Specification & Statement Non-Contamination | Property 3: Proof-Soundness, Axiom Discipline & Kernel Replay |
| :--- | :--- | :--- | :--- | :--- |
| **Anneal `anneal-audit`** (`joshlf/anneal@287e7ad5`) | Staged `.lean` sources $\rightarrow$ locally compiled `.olean` DAG | Phase 1 AST allowlist before `lean`; bypasses `lake`; Phase 2 `loadExts := false` | Statement-Origin Separation + tiered DAG + `loadExts := false` (requires 3-part fix for `Proof.Trusted` namespace shadowing; see Finding 4.2) | Single-pass whole-DAG `base.toKernelEnv.replay locals` + `rebuildNat` + `isStructuralRecCompilerHelper` + `{propext, Quot.sound, Classical.choice}` closure |
| **`lean4checker`** (`91a7f0e8`) & built-in **`leanchecker`** (`v4.34.1`, `src/Lean/LeanChecker.lean`) | `.olean` files on `LEAN_PATH` | **None** during compilation; `leanchecker` itself uses `loadExts := false` | **None** (checks internal consistency of `.olean`s, not whether a theorem matches a specification) | Per-module `env.replay'` (`Replay.lean`). **Vulnerable in `v4.34.1`** to negative GMP `mpz` `Nat` literals (`SafeVerify#20`), `constNames != ci.name` (`#15100`), forged `.quotInfo` (`#15101`), and crafted `.olean` `mmap` pointers (`compact.cpp`) |
| **`SafeVerify`** (`GasStationManager/SafeVerify@b291b588`) | Pre-compiled `Target.olean` + `Submission.olean` | **None** during compilation; **calls `unsafe enableInitializersExecution`** (`Main.lean:395`) and `importModules (loadExts := true)` (`line 369`) on `Submission.olean`! | Compares `Target.olean` vs `Submission.olean` via `equivThm`/`equivDefn` (`SafeVerify/Util.lean:16-39`) and `checkImportSuperset` | Replays **only `Submission.olean`'s `map₂`** (`Main.lean:195-205`). **Vulnerable** to 5 concrete bypasses demonstrated in Finding 2.1 (`support/SafeVerifyBugsProbe.lean`) |
| **`comparator`** (`865edc14`) & **`lake comparator [--paranoid]`** (`v4.35.0+`, PRs `#14885`, `#15005`, `#15145`, `#15156`) | `Challenge.lean` + untrusted solution repo $\rightarrow$ `lean4export` NDJSON (`3.1.0`) | Sandboxes `lake build` + `leanexport` inside `landrun` (`comparator`) or `bwrap --unshare-all --die-with-parent --tmpfs /run` (`lake comparator` PR `#15005`) | Compares exported solution types/values against `Challenge.lean` in a fresh kernel environment + `checkPrimitiveConstants` (`Compare.lean:49-185`) + `checkImportedConstantsNotModified` (`Axioms.lean`) | Out-of-sandbox verification of NDJSON export by `leanchecker-paranoid` (`MI_SECURE=3`), `nanoda_bin`, `lean4lean`, and formally verified `con-leche` / `con-ron`. Immune to `.olean` memory corruption and `#15100`/`#15101` |
| **`lean4export`** (`df81913e`, format `3.1.0`) + **`nanoda_lib`** (`8de7e0c4`, `v0.4.31`) | Line-oriented NDJSON text stream (`lean4export`) | Decouples external kernel completely from `.olean` `mmap` and Lean runtime; `lean4export` itself must run inside the build sandbox | Verifies exported declarations from an empty environment; requires orchestrator to compare target theorem signature | Independent multi-threaded Rust kernel (`nanoda_bin`). Note open upstream issues if `nat_extension = true` (`#68`: trusts `Nat.*` by name without checking `Init.Prelude` equations), `#79`, and `#81` |
| **`lean4lean`** (`digama0/lean4lean@67f63b0c`) | `.olean` (`lean4lean --fresh`) or NDJSON export | None by itself | Validates primitive shapes (`Lean4Lean/Primitive.lean:10-81`: verifies exact structure/constructor shapes of `Bool`, `Nat`, `String`, `Char` before enabling kernel fast paths!) | Pure Lean 4 kernel reimplementation (`Lean4Lean/Verify/Environment/Basic.lean`) |
| **`con-leche`** & **`con-ron`** (`lean-kernel-arena@a6a56d26`) | NDJSON export (`3.0.0` / `3.1.0`) | Runs on pure NDJSON stream outside build sandbox | Verifies primitive declarations (`Nat`, `Bool`, `String`) structurally before fast-path reduction | **Formally verified** Lean 4 kernel (`con-leche` in Lean 4 with machine-checked soundness proofs; `con-ron` transpiled to Rust), passing all 16 soundness/conformance tests in `lean-kernel-arena` |

#### 1.3 Survey of the 24 Kernel Implementations in `leanprover/lean-kernel-arena`

Auditing `leanprover/lean-kernel-arena@a6a56d26c0c94df807368d218725e9414ab4209e`
(`kernels.yaml` and `README.md`) shows 24 registered Lean 4 kernel
implementations across Rust, C++, Lean 4, Go, OCaml, ATS2, and Python tested
against 16 conformance/attack benchmarks (including negative GMP `Nat` literals,
forged `.quotInfo`, `let`-fvar projection bugs, nested inductives, and `Init`
/ `Std` / `Mathlib` exports). Only 6 implementations pass all 16 conformance
tests:
1. `lean4` (`leanchecker --from-export`, C++ reference kernel),
2. `nanoda` (`ammkrn/nanoda_lib`, Rust),
3. `lean4lean` (`digama0/lean4lean`, Lean 4),
4. `con-leche` (formally verified Lean 4 kernel, bundled in `lake comparator --paranoid`),
5. `con-ron` (Rust transpilation of `con-leche`, bundled in `lake comparator --paranoid`), and
6. `scarlet` (Rust).

---

### Finding 2: Empirical Audit of `SafeVerify` Bypasses and 2026 Lean 4 Kernel, `Replay.lean`, and `BaseIO` Exploits in Lean `v4.34.1`

Basis: `source` + `execution`

#### 2.1 Five Empirical Bypasses in `SafeVerify` (`b291b588a53999a7e837dda61c7dbfe8c550c814`)

Running [`support/SafeVerifyBugsProbe.lean`](support/SafeVerifyBugsProbe.lean)
and [`support/ProbeNegativeNatLit.lean`](support/ProbeNegativeNatLit.lean)
against `SafeVerify`'s exact checking functions (`Main.lean` and
`SafeVerify/Util.lean` at `b291b588a53999a7e837dda61c7dbfe8c550c814`) under Lean
`v4.34.1` demonstrates five vulnerabilities, each contrasted against Anneal's
`TrustedBoundary.lean`:

1. **Bypass 1 — `partial def` Completely Bypasses `--disallow-partial` (`Main.lean:28-30, 157, 202`):**
   - In Lean `v4.34.1`, elaborating `partial def diverge (n : Nat) : Nat := diverge (n + 1)` emits **two** constants into `ModuleData.constants`:
     - `diverge`: `ConstantInfo.opaqueInfo` (`isPartial == false`, `isUnsafe == false`), and
     - `diverge._unsafe_rec`: `ConstantInfo.defnInfo` with `safety := .partial` (`isPartial == true`).
   - `SafeVerify` (`Main.lean:28-30, 157, 202`) checks:
     ```lean
     def isCompilerUnsafeRecName : Name → Bool
       | .str _ s => s == "_unsafe_rec"
       | _ => false
     ...
     if disallowPartial && ci.isPartial && !isCompilerUnsafeRecName name then
       throw <| IO.userError s!"File contains partial definition '{name}'..."
     ```
     Because Lean 4 *only* sets `ci.isPartial = true` on the `._unsafe_rec`
     companion (and emits the user constant `diverge` as `.opaqueInfo` with
     `isPartial = false`), `ci.isPartial && !isCompilerUnsafeRecName name` is
     **identically `false`** for every `partial def` in Lean 4! In
     `support/SafeVerifyBugsProbe.lean`, `SafeVerify` with `disallowPartial :=
     true` accepts `SubBug1` (`passed = true`).
   - **How Anneal Blocks It (`TrustedBoundary.lean:657-685`):** Anneal rejects
     `.opaqueInfo diverge` at line 659 and checks `diverge._unsafe_rec` via
     `isStructuralRecCompilerHelper` (`lines 666-685`), which resolves `baseName
     := Compiler.isUnsafeRecName? ci.name` (`diverge`), looks up `env.checked.get.find?
     baseName`, and requires a `.defnInfo` with `!isUnsafe && !isPartial`.
2. **Bypass 2 — Un-Replayed `map₁` Helper Module Import Bypass (`Main.lean:195-205, 232-254`):**
   - `SafeVerify`'s `checkImportSuperset` (`Main.lean:232-254`) requires only
     that `submissionImports ⊇ targetImports`, permitting `Submission.lean` to
     import an auxiliary `EvilHelper.olean`.
   - `replayFileWithEnv` (`Main.lean:195-205`) then calls `importModules
     mod.imports {} 0`—which loads `EvilHelper.olean` directly into
     `env.constants.map₁` **without replaying it**—and only replays
     `Submission.olean`'s own `map₂` constants!
   - In `support/SafeVerifyBugsProbe.lean`, `EvilHelper.lean` uses `set_option
     debug.skipKernelTC true` to export `theorem evil_false : False :=
     True.intro` (a `.thmInfo` with zero axioms), and `SubBug2.lean` imports
     `EvilHelper` and proves `theorem target_false : False := evil_false`.
     `SafeVerify` accepts `SubBug2.olean` with **`passed = true, logs = #[]`**,
     whereas Anneal's full-DAG `TrustedBoundary.lean` replays `EvilHelper` +
     `SubBug2` from `base.toKernelEnv` and fails with `(kernel) declaration type
     mismatch`.
3. **Bypass 3 — `equivDefn` Disables Definition Value Comparison When Target Mentions `sorryAx` (`Main.lean:58`, `SafeVerify/Util.lean:22-31`):**
   - `Main.lean:58` calls `equivDefn target.constInfo submission.constInfo
     (\`sorryAx ∉ target.axioms)`. Whenever a target definition contains a
     `sorry` hole alongside specification structure (`def specProp : Prop := (1
     = 2) ∧ (sorry : Prop)`), `checkVal` becomes `false`, allowing the
     submission to replace the entire definition with `def specProp : Prop :=
     True` and pass `SafeVerify` (`passed = true`).
4. **Bug 4 — `supplementedDecls` Computed and Discarded (`Main.lean:418-434`):**
   - Lines 418–425 accumulate `supplementedDecls` for target constants imported
     by the submission from helper modules, but line 433 passes the original
     `submissionDecls` instead of `supplementedDecls`.
5. **Bypass 5 — `SafeVerify` Executes `Submission.olean` Initializers and Its `(toString n).startsWith "-"` Check Fails on Negative GMP `mpz` `Nat` Literals in Lean `v4.34.1`:**
   - `Main.lean:395` calls `unsafe enableInitializersExecution` before loading
     `Submission.olean` with `loadExts := true` (`line 369`), executing any
     `@[init]` / `initialize` block inside the untrusted submission during
     verification!
   - Furthermore, as detailed in Section 2.2 below, `SafeVerify`'s check for
     negative GMP `mpz` `Nat` literals (`(toString (Expr.lit (.natVal
     n))).startsWith "-"` at `Main.lean:258-286`) returns **`false`** in Lean
     `v4.34.1`!

#### 2.2 `leanprover/lean4#15717` (`ST.Ref.mk` 0-`unsafe` Coercion) Combined with `SafeVerify#20` Negative GMP `mpz` `Nat` Literals in Lean `v4.34.1`

Running [`support/ProbeSafeCoerce.lean`](support/ProbeSafeCoerce.lean) and
[`support/ProbeNegativeNatLit.lean`](support/ProbeNegativeNatLit.lean) against
Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) establishes the
exact interaction between `lean4#15717` and `SafeVerify#20`:

1. **0-`unsafe` Type Coercion in Lean `v4.34.1` (`src/lean/Init/System/ST.lean:87-91`):**
   Because `ST.Ref.mk` is exported publicly in `v4.34.1` and `ST.Prim.Ref σ α`
   erases `α` at runtime (`ST.RefPointed : NonemptyType.{0}`), 100% safe Lean
   code (with **zero** `unsafe`, `partial`, `implemented_by`, `extern`, or
   `import all` tokens) can define both `safeCoerce : α → BaseIO β` and pure
   `pureCoerceNoDo : β → α → β` (via `runST`):
   ```lean
   def safeCoerce (defaultB : β) (a : α) : BaseIO β := do
     let r : IO.Ref α ← IO.mkRef a
     let r2 : IO.Ref β := { ref := r.ref, h := ⟨defaultB⟩ }
     r2.get
   ```
   (By contrast, `IO.Promise` in `Init/System/Promise.lean:33-36` and
   `EnvExtension` in `Lean/Environment.lean:199-203` mark their constructors and
   fields `private`, requiring `module` + `import all` to construct.)
   In the Lean kernel (`Kernel.whnf`), `pureCoerceNoDo` is **irreducible
   (stuck)** on `(ST.Prim.mkRef Void (-2) Void.mk).1` because `ST.Prim.mkRef`
   (`ST.lean:45`) is `opaque`. Thus `pureCoerceNoDo` cannot prove `False` by
   kernel reduction (`rfl`) alone.
2. **Proving `boom : False` in `v4.34.1` via `safeCoerce (-4294967296 : Int)` + `run_elab` (`ProbeNegativeNatLit.lean`):**
   - When invoked during elaboration (`run_elab`), `safeCoerce 0 (-4294967296 :
     Int)` executes `@[extern "lean_st_mk_ref"]` in the VM and returns a heap
     `lean_mpz_object` (`tag = 250`) whose GMP value is $-2^{32}$, typed as
     `Nat`!
   - Adding `def badNat : Nat := .lit (.natVal badNatVal)` to the environment
     exploits asymmetric comparison in `lean_nat_big_le`
     (`src/runtime/object.cpp:424-430`):
     - `badNat ≤ 9223372036854775807` ($2^{63}-1$, a boxed scalar) hits `else if
       (lean_is_scalar(b)) return false;`, so `Nat.ble badNat (2^63 - 1) = false`
       by `rfl` in the C++ kernel!
     - `9223372036854775808 ≤ badNat` ($2^{63}$, a positive `lean_mpz_object`)
       hits `mpz_value(2^63) <= mpz_value(-2^32)`, so `Nat.ble (2^63) badNat =
       false` by `rfl` in the C++ kernel!
     - Combining both with `omega` proves `theorem boom : False` with **zero
       `unsafe` or `partial` keywords**, and **`leanchecker ExploitNegNat` exits
       with code `0`** (`Replay.lean` accepts `boom : False`)!
3. **Why `SafeVerify`'s `(toString n).startsWith "-"` Check Returns `false` in `v4.34.1`, Whereas Anneal's `rebuildNat` Catches It:**
   - In Lean `v4.34.1`, `toString (n : Nat)` calls `Nat.reprFast`
     (`src/lean/Init/Data/Repr.lean:238-241`):
     ```lean
     def Nat.reprFast (n : Nat) : String :=
       if h : n < USize.size then
         (USize.ofNatLT n h).repr
       else
         Nat.toDigits 10 n |>.asString
     ```
     Because `USize.size` ($2^{64}$) is also a `lean_mpz_object`, `n <
     USize.size` calls `lean_nat_big_lt(-2^32, 2^64)`, which evaluates
     `mpz_value(-2^32) < mpz_value(2^64)` $\rightarrow$ **`true`**!
     `Nat.reprFast` therefore enters `(USize.ofNatLT n h).repr`, which calls
     `mpz_get_ui` (stripping the GMP sign bit) and returns `"4294967296"`! Thus
     `(toString bigViaSafe).startsWith "-"` is **`false`**!
   - By contrast, Anneal's `TrustedBoundary.lean:625` (`rebuildNat`) bypasses
     `Nat.reprFast` and computes `Nat.ofDigits 10 (Nat.toDigits 10 n)` directly.
     In `Nat.toDigits 10`, `n % 10 = -6`, which `digitChar` maps to `'*'`,
     yielding `['*','*','*','*','*','*','*','*','*','*']`, which `Nat.ofDigits
     10` converts to **`0 : Nat`**. Replaying the sanitized constants in
     `base.toKernelEnv.replay` immediately rejects `not_le` with `(kernel)
     application type mismatch`.

#### 2.3 `leanprover/lean4#15100`, `leanprover/lean4#15101`, `CVE-2026-72711`, `CVE-2026-72844`, and `leanprover/lean4#14875` in Lean `v4.34.1`

Running [`support/ProbeReplayExploits.lean`](support/ProbeReplayExploits.lean)
and [`support/ProbeCVEsAnd14875.lean`](support/ProbeCVEsAnd14875.lean) on Lean
`v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) establishes:

1. **`lean4#15100` (`ModuleData.constNames` vs. `ConstantInfo.name` Mismatch — Unfixed in `v4.34.1` `leanchecker`, Blocked by `TrustedBoundary.lean`):**
   - `finalizeImport` (`src/library/module.cpp:696-706`) indexes imported
     constants in `map₁` by `mod.constNames[i]`, whereas `LeanChecker.lean:45-48`
     builds `newConstants` by keying on `ci.name` (`for ci in m.constants do
     newConstants := newConstants.insert ci.name ci`).
   - In `ProbeReplayExploits.lean`, `Helper15100.olean` contains `constNames =
     #[\`Fake, \`evil_false, \`Fake.mk]` while `constants[1]` (`type := False`)
     and `constants[2]` (`type := Fake`) both have `ci.name = \`Fake.mk`. During
     `leanchecker Helper15100`, `constants[2]` overwrites `constants[1]` in
     `newConstants`, so `Helper15100` passes (`exitCode = 0`); when `Main15100`
     imports `Helper15100`, `map₁` binds `evil_false : False`, proving `theorem
     boom : False := evil_false` (`leanchecker` `exitCode = 0`).
   - Anneal's `TrustedBoundary.lean` blocks this at **two independent layers**:
     Layer 1 (`line 681`) enforces `unless data.constNames ==
     data.constants.map ConstantInfo.name` (and line 692 rejects duplicate
     `ci.name`), while Layer 2 (`line 773`, whole-DAG `base.toKernelEnv.replay
     locals`) never uses `importModules`'s `map₁` for non-foundation modules.
2. **`lean4#15101` / `comparator#71` (Forged `.quotInfo` + `environment::add_quot` Silent No-Op — Unfixed in `v4.34.1` `leanchecker`, Blocked by `TrustedBoundary.lean`):**
   - In `src/lean/Lean/Replay.lean:133-134`, `.quotInfo _` calls `addQuot`, and
     in `src/kernel/quot.cpp:47-49`, `environment::add_quot()` begins with `if
     (is_quot_initialized()) return *this;`—a silent no-op once `Init.Prelude`
     is imported!
   - Placing `.quotInfo { name := \`evil_quot_false, type := False, kind := .ctor
     }` in `Helper15101.olean` and proving `theorem boom : False :=
     evil_quot_false` in `Main15101.lean` passes `leanchecker` on both modules
     (`exitCode = 0`).
   - Anneal's `TrustedBoundary.lean` blocks this at **two independent layers**:
     Layer 1 (`line 661`) rejects `.quotInfo` outside `Init`, and Layer 2 (`line
     773`, whole-DAG `base.toKernelEnv.replay`) rejects `boom` with `(kernel)
     unknown constant 'evil_quot_false'`.
3. **`CVE-2026-72711` (`lean4#14484`) and `CVE-2026-72844` (`lean4#14576`) Are Fixed in `v4.34.1`, While `lean4#14875` Still Reproduces in `v4.34.1` (`lean`) and Is Caught by `leanchecker` and `TrustedBoundary.lean`:**
   - `CVE-2026-72711` (`add_opaque` missing `check_no_metavar_no_fvar` on value,
     fixed by `734621996795` at `src/kernel/environment.cpp:251`) and
     `CVE-2026-72844` (`elim_nested_inductive_fn` before `check_header`, fixed by
     `a39eab69e1ee` at `src/kernel/inductive.cpp:1138-1156`) are both rejected by
     the `v4.34.1` C++ kernel (`ProbeCVEsAnd14875.lean`).
   - `lean4#14875` (`public class inductive` in a `module` with `import all`
     leaking an unexported `_private.ModA.0.ClassHidden` constant into a public
     recursor because `src/lean/Lean/Environment.lean:724` has `if true /-
     !isPrivateName n-/ then`) **still reproduces in `v4.34.1`**, allowing
     `Mod14875C.lean` to redefine `_private.Mod14875A.0.ClassHidden := True` and
     prove `boom14875 : False` during `lean` compilation (`exitCode = 0`). Both
     `leanchecker` (`importAll := true`, `exitCode = 1`) and Anneal's
     `TrustedBoundary.lean` (rejecting non-exported `.olean.private` imports at
     line 528 and duplicate/mismatched provenance at lines 692–695) reject it.

---

### Finding 3: Lean `v4.34.1` Elaboration Monad Hierarchy, `module` System Non-Guarantees, and `.olean` Deserialization Attack Surface

Basis: `source` + `execution`

#### 3.1 Exact Monad Hierarchy and the Three `MacroM` Escape Hatches (`support/effects/`)

In `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, the
metaprogramming monads divide into two stacks ([`support/effects/M.lean`](support/effects/M.lean),
[`support/effects/N_compile.lean`](support/effects/N_compile.lean)):

- **Pure State/Exception Monad (`MacroM`):** `src/Init/Prelude.lean:5934` defines
  `abbrev MacroM := ReaderT Macro.Context (EStateM Macro.Exception Macro.State)`.
  `MacroM` has **no `MonadLiftT IO MacroM` instance**; when `liftMacroM`
  (`src/Lean/Elab/Util.lean:179-219`) runs a `Macro`, it supplies only five
  read-only queries over the `Environment` (`expandMacro?`, `hasDecl`,
  `getCurrNamespace`, `resolveNamespace`, `resolveGlobalName`).
- **Effectful `EIO Exception` / `IO` Monads (`CoreM`, `AttrM`, `MetaM`,
  `TermElabM`, `TacticM`, `CommandElabM`, `ImportM`):** `CoreM`
  (`src/Lean/CoreM.lean:256`), `AttrM` (`src/Lean/Attributes.lean:20`), `MetaM`
  (`src/Lean/Meta/Basic.lean:596`), `TermElabM`
  (`src/Lean/Elab/Term/TermElabM.lean:381`), `TacticM`
  (`src/Lean/Elab/Tactic/Basic.lean:50`), and `CommandElabM`
  (`src/Lean/Elab/Command.lean:70`) all sit atop `EIO Exception` with `MonadLift
  IO`, while `ImportM` (`src/Lean/Environment.lean:1554`) sits atop `IO`.

Despite `MacroM` lacking `MonadLiftT IO`, an unrestricted `macro` or
`macro_rules` declaration can still trigger host side effects through three
routes demonstrated in `support/effects/M.lean`:
1. **Direct `IO` inside `MacroM` via `@[implemented_by]` / `@[extern]` / `unsafe
   def` + `unsafeIO` (`src/Init/System/IO.lean:208`), `#15717` `safeCoerce`, or
   safe `@[extern]` debug hooks (`dbgTrace`, `dbgSleep`, `dbgStackTrace` in
   `src/Init/Util.lean:18-42`).**
2. **Two-stage Trojan `Syntax` expansion:** A pure `Macro` (`Syntax → MacroM
   Syntax`) can expand a benign token into effectful built-in syntax (`by_elab
   ...`, `run_cmd ...`, `run_meta ...`, `#eval ...`, or `include_str ...`),
   which executes arbitrary `IO` when the downstream elaborator processes the
   expanded `Syntax`.
3. **Import-time closure evaluation (`KeyedDeclsAttribute.ofOLeanEntry`,
   `src/Lean/KeyedDeclsAttribute.lean:123-127`):** When `import M` runs with
   `loadExts := true`, `ofOLeanEntry` calls `evalConstCheck` on every `@[macro]`,
   `@[command_elab]`, `@[term_elab]`, and `@[tactic]` constant in `M`.

As verified in [`support/effects/AuditHarness.lean`](support/effects/AuditHarness.lean):
- Calling `importModules (loadExts := false)` (`src/Lean/Environment.lean:2403`)
  skips `finalizePersistentExtensions` completely: zero `[init]`/`initialize`
  blocks, zero `PersistentEnvExtension` (`mkInitial` / `addImportedFn`) hooks,
  and zero `evalConstCheck` calls run.
- Calling `importModules (loadExts := true)` without prior
  `enableInitializersExecution` unconditionally throws ``
  `enableInitializersExecution` must be run before calling `importModules
  (loadExts := true)` `` (`src/Lean/Compiler/InitAttr.lean:199-203`).

#### 3.2 Why Lean 4's `module` System Cannot Isolate Untrusted Proof Dependencies (`support/module_system/`)

In `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, a file with the
`module` header emits up to five artifacts (`<Mod>.olean`, `<Mod>.olean.server`,
`<Mod>.olean.private`, `<Mod>.ir.sig`, `<Mod>.ir`). Running
[`support/module_system/InspectParts.lean`](support/module_system/InspectParts.lean)
and `ConsumerPlainImport.lean` establishes three reasons why `module` is not a
security or verification boundary:

1. **Plain `import Dep` (Without `meta import Dep`) Still Exports and Executes
   Macros, Elaborators, Tactics, Attributes, and `meta initialize` Blocks:**
   - When `syntax`, `macro`, `macro_rules`, `notation`, or `elab` is defined in
     `Dep`, `aux_def` (`src/Lean/Elab/AuxDef.lean:39`) automatically marks the
     generated declaration `meta`.
   - `declMapExt` (`src/Lean/Compiler/IR/CompilerM.lean:87-111`) exports the
     **complete IR (`Decl.fdecl`) of every `meta` declaration directly into
     `Dep.olean` (`ExportLevel.exported`)**, and `regularInitAttr`
     (`src/Lean/Compiler/InitAttr.lean:67`) exports `meta initialize` entries
     into `Dep.olean`.
   - `getIRPhases` (`src/Lean/Compiler/MetaAttr.lean:73-90`) checks `if
     isMarkedMeta env declName then .comptime else mod.irPhases`—evaluating
     `isMarkedMeta` *before* `mod.irPhases`! Thus, even when `Consumer` writes
     plain `import Dep` (`mod.irPhases == .runtime`), `Dep`'s `meta initialize`
     blocks run at `import Dep` time and `Dep`'s `public` macros, elaborators,
     tactics, `@[simp]` lemmas, and `@[instance]`s run during `Consumer`'s
     elaboration (`ConsumerPlainImport.lean`).
2. **Axiom Weakening in `Dep.olean` vs. `Dep.olean.private` (`src/Lean/AddDecl.lean:112-128`) and `Lean.collectAxioms` Trusting `exportedAxiomsExt`:**
   - Under `module` (`env.header.isModule == true`), `AddDecl.addDeclCore`
     (`src/Lean/AddDecl.lean:116-124`) weakens **every `theorem` and every
     non-`@[expose]` `def` or `opaque` into a `ConstantInfo.axiomInfo`** in the
     public environment (`Dep.olean` and `Dep.olean.server`), storing the actual
     `.thmInfo` proof terms and `.defnInfo` bodies **only in
     `Dep.olean.private`** (`InspectParts.lean`)!
   - Meanwhile, `Lean.collectAxioms` (`src/Lean/Util/CollectAxioms.lean:77-86,
     113-155`) does not inspect `ConstantInfo` for imported modules when
     `loadExts := true`; it trusts a precomputed `PersistentEnvExtension`
     (`exportedAxiomsExt`) stored in `Dep.olean`!
   - Consequently, any kernel auditor that inspects `Dep.olean` alone sees every
     theorem and unexposed definition in a `module` as an unverified
     `.axiomInfo`, and any auditor that calls `Lean.collectAxioms` with
     `loadExts := true` can be spoofed by a forged `exportedAxiomsExt` entry.
3. **Unrestricted `import all` and `set_option compiler.checkMeta false`:**
   - Any downstream file can write `import all Dep` or omit `module` to load
     `Dep.olean.private` (`src/Lean/Environment.lean:2029-2034`), Lake's
     `allowImportAll` check is commented out (`src/lake/Lake/Build/Module.lean:418-442`),
     and any module can disable `LCNF.checkMeta` via `set_option
     compiler.checkMeta false` (`src/Lean/Compiler/LCNF/Visibility.lean:63`).

#### 3.3 `.olean` Deserialization Attack Surface (`src/runtime/compact.cpp` and `support/olean_deser/`)

Auditing `src/library/module.cpp:452-619` and `src/runtime/compact.cpp:506-685`
and running [`support/olean_deser/TestOleanDeser.lean`](support/olean_deser/TestOleanDeser.lean)
proves that `loadExts := false` and `trustLevel := 0` **cannot** protect an
auditor against untrusted pre-compiled `.olean` binaries:
- `lean_compacted_region_read` (`src/library/module.cpp:467-494`) checks only
  the 88-byte `olean_header` (`marker`, `version`, `flags`, `githash`).
- **Fast path (`m_begin == m_base_addr`, `src/runtime/compact.cpp:643-657`):**
  When `mmap` maps the file at `header.base_addr`, `compacted_region::read()`
  skips object-graph traversal completely and returns `*static_cast<object_offset
  *>(m_next)` (bytes `88..96`) directly as a `ModuleData` pointer with zero
  bounds, tag, or type checks (`FastPathBogusRoot.olean` and
  `FastPathClosureRoot.olean` immediately crash `importModules (trustLevel := 0)
  (loadExts := false)` with `SIGSEGV`, `exitCode = 139`).
- **Slow path (`m_begin != m_base_addr`, `src/runtime/compact.cpp:565-685`):**
  Accepts `LeanClosure` (`line 670`), performs unchecked `m_closure_offsets`
  pointer writes (`begin + off` with no `off < size` check at `lines 627-641`) in
  `v3` `.olean`s, and trusts `o->m_size` in `fix_array` (`lines 565-572`).
- Therefore, `.olean`-based replay (`loadExts := false` + `toKernelEnv.replay`)
  is sound **if and only if** every `.olean` file was produced locally by a
  trusted `lean` binary from staged `.lean` sources (as `anneal-audit` enforces).

---

### Finding 4: Retroactive Environment Mutation Across Module Imports and Statement-Origin Separation

Basis: `source` + `execution`

#### 4.1 Five-Vector Defense-in-Depth Matrix (`support/retroactive_mutation/`)

Using [`support/retroactive_mutation/RunRetroactiveMutationProbe.lean`](support/retroactive_mutation/RunRetroactiveMutationProbe.lean)
with a buggy crate `Mir.crate` (`entryReturnVal := 0, expectedVal := 1`) for
which the true `Trusted.CrateTheorem Mir.crate` reduces to `false = true`
(unprovable), we tested five classes of retroactive environment mutation from an
imported `Theory.lean` module containing zero axioms or `sorry`:

| Mutation Vector in Imported `Theory.lean` | Allowed by Raw Lean `v4.34.1`? | Blocked by Phase 1 (`"preflight"`)? | Blocked by Phase 2 (`loadExts := false`, `validateLocalConstant`, `replay`)? | Blocked by Statement-Origin Separation + Kernel `ConstantInfo.type` Check? |
| :--- | :--- | :--- | :--- | :--- |
| **1a. Retroactive `attribute [simp]` / `attribute [-simp]` on `Trusted.*` or `Init.*`** | **Yes** (`simpExtension` is a `SimpleScopedEnvExtension`) | **No** (`attribute`, `eraseAttr`, and `simp` are in `allowedCommandKinds` / `allowedAttributeNames` at `TrustedBoundary.lean:205, 229, 346`) | Ignored (`loadExts := false`); does not alter kernel constants | Cannot corrupt soundness (`simp` still builds kernel-checked proof terms; at worst causes tactic failure) |
| **1b. Retroactive `attribute [reducible]` / `[irreducible]` on `Trusted.*`** | Rejected by default (`Lean/ReducibilityAttrs.lean:140-141`); **allowed if `set_option allowUnsafeReducibility true`** via `reducibilityExtraExt` (`lines 71-77, 95`) | **Yes** (`set_option` is excluded from `allowedCommandKinds` at `TrustedBoundary.lean:200`) | Ignored by kernel (`Kernel.isDefEq` uses `DefinitionVal.hints` fixed at declaration time in `Trusted.lean`, ignoring `reducibilityExtraExt`) | Does not alter `ConstantInfo.type` of `Trusted.CrateTheorem Mir.crate` (`TheoryV1.lean` in `RunRetroactiveMutationProbe.lean`) |
| **2a. Retroactive `attribute [implemented_by ...]` or `attribute [extern ...]` on `Trusted.*`** | **No — rejected by Lean `v4.34.1`** (`Lean/Attributes.lean:291-292`: `throwAttrDeclInImportedModule`) | **Yes** (`implemented_by` and `extern` excluded from `allowedAttributeNames` at `lines 345-346`) | Ignored (`loadExts := false`, and kernel `isDefEq` ignores compiler overrides when `Lean.trustCompiler` is excluded) | Rejected at compile time by Lean |
| **2b. `@[csimp]` theorem replacing `Trusted.*` with `Theory.*`** | **Yes, only if `@Trusted.f = @Theory.g` is proved in `Theory.lean`** (`Lean/Compiler/CSimpAttr.lean:33-56`) | **Yes** (`csimp` excluded at `lines 345-346`) | Ignored (`loadExts := false`, and `@[csimp]` only affects compiled code, never the kernel) | Requires a kernel proof of `@f = @g` (`TheoryV2.lean`) |
| **3. High-priority `instance (priority := 1000000)` or default-priority LIFO `instance` overriding `OfNat`, `Add`, `BEq`, `Coe`** | **Yes** (`instanceExtension` uses priority then LIFO order across imports) | **Partial:** `inspectNodeKind` (`lines 433-435`) blocks explicit `(priority := ...)`, **but default-priority `instance` is allowed (`lines 214, 346`) and shadows `Init` instances via LIFO!** | **No** if `Proof.lean`'s statement uses typeclass syntax (`==`, `+`, literals), because `Proof.verify_crate` elaborates with `Theory`'s instance in `ConstantInfo.type` and replays cleanly (`ProofV3.lean`)! | **Yes:** Statement-Origin Separation compiles `Trusted.lean` and `Mir.lean` *before* `Theory.lean`, keeping `Trusted.CrateTheorem Mir.crate` in `Proof.lean` free of typeclass obligations (`V3c`), and checks `ConstantInfo.type` |
| **4. Global `notation` / `macro` / `elab` overriding `Trusted.CrateTheorem`** | **Yes** (`notation (priority := 1000000) "Trusted.CrateTheorem" c:arg => c = c` rewrites `Trusted.CrateTheorem Mir.crate` to `Mir.crate = Mir.crate` in `ProofV4.lean`) | **Yes** (`notation`, `macro`, `syntax`, `elab` excluded at `lines 199-206`) | **No!** If Phase 1 is relaxed, `Proof.verify_crate` has kernel type `Mir.crate = Mir.crate` (`rfl`), which **passes `loadExts := false`, `validateLocalConstant`, and `base.toKernelEnv.replay`!** | **Yes!** Checking `kci.type == mkApp (mkConst ``Trusted.CrateTheorem) (mkConst ``Mir.crate)` in `Kernel.Environment` immediately rejects `Mir.crate = Mir.crate` |
| **5a. Root namespace spoofing (`def Trusted.CrateTheorem` in `Theory.lean`)** | Rejected by Lean if `Trusted` is imported; allowed if `Trusted` is not imported (`V5a-2`) | **No** | **Yes:** `validateLocalConstant` (`line 647`) rejects `(privateToUserName ci.name).getRoot == \`Trusted` in non-`Trusted` modules | **Yes** |
| **5b. Enclosing-namespace prefix shadowing (`namespace Proof.Trusted def CrateTheorem` in `Theory.lean` when `Proof.lean` opens `namespace Proof`)** | **Yes!** Inside `namespace Proof`, Lean resolves `Trusted.CrateTheorem` to `Proof.Trusted.CrateTheorem` before `_root_.Trusted.CrateTheorem`! | **NO! Admitted by Phase 1!** (`isValidSourceIdent` at `line 355` even forbids `_root_`!) | **NO! Admitted by Phase 2!** Because `(\`Proof.Trusted.CrateTheorem).getRoot` is `` `Proof `` (not `` `Trusted ``), `validateLocalConstant` (`line 647`) **does not fire**, and `ProofV5Ns.lean` passes `base.toKernelEnv.replay`! | **Yes!** Checking `kci.type == mkApp (mkConst ``Trusted.CrateTheorem) (mkConst ``Mir.crate)` in `Kernel.Environment` catches `Proof.Trusted.CrateTheorem Mir.crate` |

#### 4.2 Closing the `Proof.Trusted.CrateTheorem` Enclosing-Namespace Shadowing Seam

Vector 5b (`TheoryV5Ns.lean` + `ProofV5Ns.lean` in
[`support/retroactive_mutation/`](support/retroactive_mutation/)) demonstrates why
relying solely on `(privateToUserName ci.name).getRoot == \`Trusted`
(`TrustedBoundary.lean:647`) is insufficient if generated `Proof.lean` files open
`namespace Proof`:
1. In `validateLocalConstant`, forbid `` `Trusted `` as **any component** of a
   non-`Trusted` constant name:
   ```lean
   if tier != .trusted && (privateToUserName ci.name).components.contains `Trusted then
   ```
2. In generated `Proof.lean` files, emit `theorem Proof.verify_crate :
   Trusted.CrateTheorem Mir.crate` at the **root (anonymous) namespace** (never
   inside `namespace Proof ... end Proof`), and never include typeclass-mediated
   syntax (literals, operators, or coercions) in `Proof.lean`'s theorem
   statement while `theory/` is in scope.
3. In Phase 2, after `base.toKernelEnv.replay`, inspect the replayed
   `ConstantInfo` of `Proof.verify_crate` in `Kernel.Environment` and verify
   structural equality (`==`) of `kci.type` against `mkApp (mkConst
   ``Trusted.CrateTheorem) (mkConst ``Mir.crate)` with `kci.levelParams.isEmpty`
   (as implemented in [`support/PureMacroAudit.lean`](support/PureMacroAudit.lean)).

---

### Finding 5: Lean Community Threat Model, Lake Configuration Attack Surface, and Upstream Sandbox Evolution

Basis: `source` + `execution`

#### 5.1 Official Lean FRO Verification Hierarchy and Elaborator Threat Model

Rather than attempting to restrict `IO` inside `CoreM`/`MetaM`/`TermElabM`
(`leanprover/lean4#13449`, `leanprover/lean4#13310`), the Lean Reference Manual
(*Validating a Lean Proof*), Leonardo de Moura's *Kernel bug hunt* specification,
and Sebastian Ullrich's September 2026 IFIP WG 2.2 presentation (*Lean and trust
in the age of AI*) explicitly exclude the elaborator, metaprogramming API, and
`.olean` memory-image loader from the adversarial TCB (*"Note that the `unsafe`
marker on API functions is unrelated to whether this API can be used in a
dishonest way"*), defining four verification levels:
- **Level I (`lake build`):** In-process C++ kernel; bypassed by
  `debug.skipKernelTC` (`src/Lean/Environment.lean:76-79, 2559, 2604`),
  `addDeclWithoutChecking` (`lines 307, 692`), `lakeAdd` (`line 742`), or custom
  syntax/notations.
- **Level II (`#print axioms` / `Lean.collectAxioms`):** Inspects transitive
  axioms (`propext`, `Classical.choice`, `Quot.sound`, `sorryAx`, `_native.*`);
  trusts the in-memory `Environment`, `exportedAxiomsExt` in imported `.olean`s,
  and theorem statement fidelity.
- **Level III (`leanchecker --fresh`):** Replays `.olean` constants in a
  separate process (`Environment.replay`), catching in-process state hacks, but
  trusts `.olean` binary integrity (`compact.cpp`), does not sandbox builds, and
  does not verify statement fidelity against a frozen specification.
- **Level IV (`lake comparator [--paranoid]`):** Sandboxed build (`bubblewrap`)
  + NDJSON text export (`leanexport`) + out-of-sandbox verification by
  `leanchecker-paranoid` (`MI_SECURE=3`, added in `lean4#14884`
  `ec5816f82fabf7d0982f388a19694a926c9ec5ac` because `lean_object.m_rc` sits at
  byte offset `0` where `mimalloc` stores its intrusive free-list pointer) and
  independent external kernels (`nanoda`, `lean4lean`, `con-leche`, `con-ron`) +
  structural comparison against a trusted `Challenge.lean`.

#### 5.2 Complete Matrix of Dangerous `lakefile.toml` Fields (`src/lake/Lake/Load/Toml.lean` in `v4.34.1`)

In `src/lake/Lake/Load/Package.lean:108-133`, Lake checks `lakefile.lean` before
`lakefile.toml` on the root package and every transitive `[[require]]`
dependency; `loadLeanConfig` (`src/lake/Lake/Load/Lean/Elab.lean:61-131`) calls
`unsafe enableInitializersExecution` and runs arbitrary `IO` during `lake env`,
`lake setup-file`, `lake update`, or `lake build`. Even when a package uses a
pure `lakefile.toml` (`src/lake/Lake/Load/Toml.lean:404-509`), the following
fields decoded by `Toml.lean` trigger native code compilation/execution (`dlopen`)
or disable the kernel typechecker during `lake build`, `lake setup-file`
(invoked automatically by `lean --server` in the IDE), or `lake serve`:

| `lakefile.toml` Field | Decoded in `Lake/Load/Toml.lean` (`v4.34.1`) | Consumed in Lake / Lean (`v4.34.1`) | Security Impact During `lake build`, `lake setup-file`, or `lake serve` |
| :--- | :--- | :--- | :--- |
| **`precompileModules`** (`Bool`) | `L254`, `L342` | `Lake/Build/Module.lean:571-576, 1332-1353, 1424-1430` | Compiles imported modules to native `.so`/`.dylib` (`plugin := true`) and `dlopen`s them via `Lean.loadPlugin` (`src/Lean/Environment.lean:2446`) during both `lake build` and `lake setup-file`! |
| **`plugins`** & **`dynlibs`** (`TargetArray Dynlib`) | `L225-226` | `Lake/Build/Module.lean:579-580, 1433-1434, 1476-1477` | Builds and `dlopen`s native shared libraries via `setup.json` during `lake build` and `lake setup-file`. |
| **`leanOptions`** & **`moreServerOptions`** | `L213`, `L217` | `Lake/Build/Module.lean:606, 658, 1451, 1493`; `Lake/CLI/Serve.lean:96-99` | Injects `ModuleSetup.options` into `setup.json`; setting `leanOptions = { "debug.skipKernelTC" = true }` disables the C++ kernel (`addDeclWithoutChecking` at `Environment.lean:2559`) for every theorem in the package! |
| **`moreLeanArgs`** & **`weakLeanArgs`** | `L214-215` | `Lake/Build/Module.lean:984, 989, 1530-1538` | Appends raw CLI flags to `lean`, allowing `-Ddebug.skipKernelTC=true`, `--trust=100`, `--plugin=/path/evil.so`, or `-o /arbitrary/path`. |
| **`moreGlobalServerArgs`** | `L255` | `Lake/CLI/Serve.lean:95, 101` | Appends raw CLI flags (`--plugin`, `--load-dynlib`, `--trust`) to `lean --server`. |
| **`moreLeancArgs`**, **`moreLinkArgs`**, **`moreLinkObjs`**, **`moreLinkLibs`** | `L216, 218-222` | `Lake/Build/Module.lean:1223-1253`; `Lake/Build/Library.lean:91, 134, 152-153` | Passes arbitrary compiler/linker flags (`-fplugin=...`, `-Wl,-init,...`) and object files to `leanc`/`cc` whenever native compilation runs. |
| **`defaultTargets`**, **`defaultFacets`**, **`extraDepTargets`**, **`needs`**, **`testDriver`**, **`lintDriver`** | `L253, 264-267, 339-343, 369-370, 429` | `Lake/Build/Package.lean:98-107`; `Lake/Build/Module.lean:556, 1417`; `Lake/CLI/Actions.lean:55-127` | `extraDepTargets` runs before `lake build` or `lake setup-file` computes `ModuleSetup` for any file; `defaultFacets = ["shared"]` forces native compilation on `lake build`. |
| **`[[require]]`** | `L290-322, 428` | `Lake/Load/Package.lean:125-133` | Transitive dependency may supply a `lakefile.lean`, executing arbitrary `IO` during `loadWorkspace`. |
| **`preferReleaseBuild`**, **`releaseRepo`**, **`buildArchive`**, Reservoir Barrels, & `.trace` Cache (`lean4#16123`) | `L260-263, 277-278` | `Lake/Build/Package.lean:60-70, 102-103, 141-279` | Unpacks prebuilt `.olean` and `.so` archives from GitHub Releases or Reservoir Barrels without kernel replay, and Lake `.trace` files (`lean4#16123`) do not hash output `.olean` files on disk. |

#### 5.3 Evolution of Build Sandboxing in Upstream Lean (`PR #13940` $\rightarrow$ `PR #14885` $\rightarrow$ `PR #14947` $\rightarrow$ `PR #15005`)

Upstream Lean iterated through three sandboxing designs in 2026 after concrete
bypasses were discovered in each earlier design:
1. **Per-module Landlock (`PR #13940`, `742bf162268d8817ecf046657718d03900b7eff3`, closed):**
   Added `lean --sandbox-exec` (Landlock LSM) and `lake build --sandbox`; closed
   after `@marcelolynch` showed that an untrusted `lakefile.lean` can define an
   unsandboxed `@[default_target] target poison` in the Lake driver process that
   overwrites `.olean` files after module compilation completes.
2. **`landrun` wrapper (`PR #14885` `fe1939c0b3bf` & `PR #14947` `b5466a1aa841`):**
   Integrated `leanexport` and `comparator` as `lake challenge` under `landrun`.
   PR `#14947` fixed two flaws: (a) running `lake env` outside the sandbox
   executed the untrusted `lakefile.lean` on the host before sandboxing started;
   and (b) Landlock `LANDLOCK_ACCESS_FS_EXECUTE` restrictions on `--ro` files
   were bypassed by invoking `/lib64/ld-linux-x86-64.so.2 <binary>` directly.
3. **`bubblewrap` (`bwrap`) replacement and `/run/docker.sock` fix (`PR #15005` `0243d9f4bc04983c037caa738a29ab5e78b5459f`):**
   Replaced `landrun` with `bwrap --unshare-all --die-with-parent` because
   Landlock rules are additive-only (unable to hide `~/.ssh` under `--ro /`),
   Landlock network rules only filter TCP (leaving UDP and `AF_UNIX` sockets
   open), and detached `setsid()` sleeper processes (`comparator#77`) or
   `ptrace(PTRACE_ATTACH)` on the parent verifier (`comparator#43`) require PID
   namespace isolation or syscall filtering. During review of PR `#15005`,
   `@kim-em` discovered that `--ro-bind / /` with only `--tmpfs /run/user` left
   `/run/docker.sock` accessible (`connect()` on a `SOCK_STREAM` Unix socket
   ignores VFS read-only mount flags), fixed by mounting `--tmpfs /run`.

---

### Finding 6: Cross-Prover and Safe-Language Prior Art (`Agda --safe`, GHC Safe Haskell, Rocq `coqchk`, Metamath Zero `mm0-c`, `watt`, `cackle`, `endo`)

Basis: `source`

#### 6.1 Cross-System Architectural Mapping Against Anneal

| System & Pinned Revision | Equivalent of `.foundation` / `.trusted` / `.theory` | How Metaprogramming / Elaboration Side Effects Are Contained | How Statement / Specification Contamination Is Prevented |
| :--- | :--- | :--- | :--- |
| **GHC Safe Haskell** (`ghc/ghc@37ad471050`, `compiler/GHC/Driver/Main.hs:1058-1275`) | **Exact 3-tier structural dual:** `-XSafe` (`Sf_Safe`) $\leftrightarrow$ `.theory`; `-XTrustworthy` (`Sf_Trustworthy`) $\leftrightarrow$ `.trusted .vetted`; `-XTrustworthy` + `-fpackage-trust` (`-trust <pkg>`) $\leftrightarrow$ `.trusted (.candidate f)` | Bans Template Haskell (`-XTemplateHaskell`), quasi-quotes, `RULES`, `GeneralizedNewtypeDeriving`, and `FfiImports` in `-XSafe` (`GHC/Driver/DynFlags.hs:865-915`); restricts overlapping instances via `instance_overlap_ok` (`GHC/Tc/Solver/Dict.hs:912-944`) | `checkSafeImports` (`Main.hs:1058-1275`) verifies the transitive `(ModuleName, Fingerprint, Bool)` `dep_trusted_pkgs` closure in `.hi` interface files (`GHC/Iface/Load.hs:371-445`) |
| **Agda `--safe`** (`agda/agda@ec45c73baa`, `Syntax/Concrete/Definitions/Errors.hs:314-352`, `Interaction/Imports.hs:1080-1122`) | **Coinfective binary flag** (`optSafe`) plus a hardcoded 40-file `builtinModulesWithSafePostulates` allowlist (`TypeChecking/Monad/Base.hs:984-985`); **cannot** express user-defined `.trusted` modules with domain axioms imported by `--safe` modules | Allows reflection (`TC` monad) because `evalTCM` (`TypeChecking/Unquote.hs:630-703`) interprets a deep embedding over 42 closed primitives rather than native `IO` (`tcExec` requires `--allow-exec`, which `--safe` bans). **However, see Section 6.2 for our newly discovered `tcPragmaForeign`/`tcPragmaCompile` backend-compilation bypass** | Bans `postulate`, `{-# REWRITE #-}`, `primEraseEquality`, `--type-in-type`, `--sized-types`, `--guardedness`, and `--injective-type-constructors` (`Options.hs:1661-1725`) |
| **Rocq `coqchk` & `MetaRocq`** (`rocq@4402a03e26`, `metarocq@51b14e4bb5`) | `.vo` kernel checker (`checker/check.ml`) and verified `SafeTemplateChecker` (`safechecker-plugin/theories/SafeTemplateChecker.v`) | `coqchk` excludes `vernac`, `interp`, `synterp`, `ltac`, and `dynlink` at link time (`checker/dune:1-38`), drops `.cmxs` plugin objects via `v_any` segment typing (`checker/check.ml:192-215`), skips `"vmlibrary"`, and runs a **two-pass memory-graph validator** (`checker/validate.ml:1-245`) before `Obj.obj` | `coqchk -norec <Mod>` checks `.vo` files and prints the exact `Context { Axioms / Inductives / Constants }` closure (`checker/check_stat.ml:20-85`) |
| **Metamath Zero (`mm0-c`)** (`digama0/mm0@0d414c0bfd`, `mm0-c/verifier.c`, `mm0-c/main.c`) | Specification file `spec.mm0` (`.trusted` + target statement) vs. untrusted proof/metaprogram file `proof.mm1` $\rightarrow$ `proof.mmb` (`.theory` + `Proof`) | `mm0-c` is a 2,100-line C verifier that never executes `.mm1` Scheme metaprograms; it reads only `spec.mm0` (on `stdin`) and `proof.mmb` (checked for alignment and bounds in `main.c:48-140`) | **Lockstep specification stream (`verifier.c:660-740`):** `parse_until(CMD_END)` checks every non-local sort, term, axiom, and theorem in `proof.mmb` byte-for-byte against `spec.mm0`, while skipping `.mm1`-local helper defs/theorems (`!IS_CMD_STMT_LOCAL` at `types.h:98-115`) |
| **Rust `watt`, `cackle`, Cargo `[lints]`, & JS `endo`** (`watt@8f16788f`, `cackle@f9f09eeb`, `endo@679d9afaa4`) | Host vs. Wasm guest (`watt`), per-crate `cackle.toml` `[pkg.<name>]` capabilities (`fs`, `net`, `process`, `unsafe`), and SES `Compartment` endowments (`endo`) | `watt` runs proc-macros in a zero-import Wasm32 linear-memory interpreter (`runtime/src/Deterministic.rs`); `cackle` intercepts linker symbol references via `--wrap` (`src/symbol_graph.rs`); `endo` freezes primordials (`lockdown()`) and restricts `importHook` per package (`packages/ses/`) | `watt` restricts output to pure `TokenStream` byte buffers; `cackle` rejects undeclared `unsafe` or FFI imports per crate in the dependency graph |

#### 6.2 Newly Discovered Agda `--safe` Backend-Compilation Bypass (`tcPragmaForeign` and `tcPragmaCompile`)

Auditing `agda/agda@ec45c73baa385bd90ad8db80f0a9d21cdafe8dc5` uncovered an
asymmetry between Agda's surface pragma checker and its reflection interpreter:
- In `src/full/Agda/Syntax/Concrete/Definitions.hs:539-545` and
  `src/full/Agda/Syntax/Concrete/Definitions/Errors.hs:314-352`, surface
  `{-# COMPILED ... #-}` pragmas are rejected under `--safe` (`CompilePragma{} ->
  singleton PragmaCompiled`; note also that line 323 maps surface
  `ForeignPragma{} -> empty`).
- However, in `src/full/Agda/TypeChecking/Unquote.hs:1150-1159`, the reflection
  primitives `tcPragmaForeign` and `tcPragmaCompile` mutate `stForeignCode` and
  `defCompiledRep` directly in `TC` **without checking `optSafe` (`--safe`)**:
  ```haskell
  tcPragmaForeign :: String -> String -> TC ()
  tcPragmaForeign backend code = addForeignCode ( BackendName $ Text.pack backend ) code

  tcPragmaCompile :: Name -> String -> String -> TC ()
  tcPragmaCompile x backend code = modifySignature $ updateDefinition x $ addCompilerPragma b pragma
  ```
- **Exact Boundary:**
  - *Pure typechecking (`agda --safe` without `--compile` / `--js`):*
    **Uncompromised.** Conversion checking, reduction, termination/positivity,
    and `evalTCM` never consult `stForeignCode` or `defCompiledRep`.
  - *Backend compilation (`agda --compile --safe` or importing a `--safe` module
    into a compiled module):* **Compromised both directly and transitively.**
    `--safe` does not block backend compilation (`Compiler/Backend.hs:159-207`),
    `DeadCode.hs:58, 65-67` retains `defCompiledRep` definitions as reachable
    roots, `Imports.hs:1660, 1707` and `Serialise/Instances/Internal.hs:241-243`
    serialize `iForeignCode` and `defCompiledRep` into `.agdai` files, and
    `Compiler/MAlonzo/Compiler.hs:443, 466-473, 556, 565-580` (`GHC`) and
    `Compiler/JS/Compiler.hs:407-425` (`JS`) splice the injected foreign code
    and replacement function bodies verbatim into generated Haskell/JS output.

---

### Finding 7: Runnable Building Blocks for Side-Effect-Free, Guarantee-Preserving Untrusted Dependencies in Lean 4

Basis: `source` + `execution`

#### 7.1 Quantified Conservativity of `TrustedBoundary.lean` Phase 1 vs. Phase 2 (`support/PreflightVsPhase2Probe.lean` and `support/Phase2FeatureAudit.lean`)

Running [`support/PreflightVsPhase2Probe.lean`](support/PreflightVsPhase2Probe.lean)
and [`support/Phase2FeatureAudit.lean`](support/Phase2FeatureAudit.lean) across
42 representative Lean 4 proof-engineering constructs establishes:
- **40 of 42 constructs** are rejected by `TrustedBoundary.lean`'s Phase 1
  (`"preflight"`) surface-syntax allowlist (`allowedCommandKinds`,
  `allowedTermKinds`, `allowedTacticKinds` at lines 199–343), whereas **all 40
  rejected pure constructs (`100%`) pass Phase 2** (`loadExts := false`,
  `validateLocalConstant` + `isStructuralRecCompilerHelper`,
  `base.toKernelEnv.replay`) while both soundness-violating controls (`axiom`
  and `sorry`) are rejected by Phase 2 (`EvilTheory.lean`).
- Furthermore, inspecting the ASTs in `PreflightVsPhase2Probe.lean` revealed
  **three accidental child-node omissions in `TrustedBoundary.lean` where the
  parent syntax kind is allowlisted in Phase 1, but any non-empty use is
  rejected because a mandatory child wrapper node is missing from
  `allowedTheorySyntaxKinds`:**
  1. `deriving DecidableEq` on `inductive`/`structure`: `Parser.Command.optDeriving`
     is allowlisted (`line 222`), but its child `Parser.Command.deriving` is not.
  2. `termination_by` / `decreasing_by`: `Parser.Termination.suffix`,
     `terminationBy`, and `decreasingBy` are allowlisted (`lines 223-225`), but
     a `termination_by` clause on a function with parameters produces child node
     `Lean.Parser.Term.ExplicitBinders`, and `decreasing_by` produces child node
     `Lean.Parser.Tactic.tacticSeqIndentGt`, neither of which is allowlisted.
  3. `simp (config := ...)` / `omega (config := ...)`: `Parser.Tactic.optConfig`
     is allowlisted (`line 336`), but its children `Parser.Tactic.config` and
     `Parser.Tactic.posConfigItem` are not.
- **Why Phase 1 Cannot Be Dropped Without Either Pure-Macro Auditing or an OS
  Sandbox:** `PreflightVsPhase2Probe.lean` (`F39_include_str`) demonstrates that
  `def leaked : String := include_str "/etc/hostname"` (`Lean.includeStr` in
  `src/Lean/Elab/BuiltinTerm.lean:431-446`) reads arbitrary host files during
  elaboration and compiles to a pure `.safe` `.defnInfo` whose value is a
  `Expr.lit (.strVal ...)` that passes Phase 2 with zero axioms.

#### 7.2 Building Block A: Pure `MacroM` Expansion + Post-Expansion Syntax Audit + Kernel Statement-Identity Verification (`support/PureMacroAudit.lean`)

[`support/PureMacroAudit.lean`](support/PureMacroAudit.lean) (798 lines, exit
code `0`, `"allAssertionsPassed": true`) demonstrates how a verifier can safely
admit custom `notation`, `infixl`, `syntax`, and `macro_rules` in `Theory.lean`
**without OS sandboxing** by combining three checks around frontend command
elaboration:

1. **Check 1 — Macro-Definition Purity (`checkMacroDefinitionPurity`):**
   - Identifies user `@[macro]` declarations added in `Theory.lean` via
     `(env.getModuleIdxFor? e.declName).isNone && !trustedConsts.contains
     e.declName` (noting that `KeyedDeclsAttribute.ofOLeanEntry` at
     `src/lean/Lean/KeyedDeclsAttribute.lean:126, 167` sets `isBuiltin := false`
     on imported `.olean` macros such as `Init.Notation`).
   - Because `notation`, `macro`, and `macro_rules` elaborate to a lambda
     (`fun stx => ...` in `Lean/Elab/MacroRules.lean:51-53`), `evalConstCheck`
     at `@[macro]` registration time only allocates the closure without running
     its body. Running Check 1 immediately after each command in `Theory.lean`
     verifies the transitive `Expr.getUsedConstants` cone of every `@[macro]`
     declaration before any subsequent command can invoke it:
     - `ci.safety == .safe`, `!Lean.isExtern env c`, and
       `Compiler.getImplementedBy? env c == none` on all non-foundation
       constants, and
     - exclusion of `dbgTrace`, `dbgTraceVal`, `dbgTraceIfShared`, `dbgSleep`,
       `dbgStackTrace`, `unsafeIO`, `unsafeBaseIO`, `unsafeEIO`, `ST.Prim.*`,
       and `IO.Prim.*`.
2. **Check 2 — Post-Expansion Syntax Audit in Pure `MacroM` (`expandAndInspectSyntax`):**
   - Before elaborating any command in `Theory.lean` or `Proof.lean`, runs
     `inspectSyntax` on the surface `Syntax`, then recursively expands user
     macros via `Macro.expandMacro?` in a pure `Macro.Context` and re-runs
     `inspectSyntax` after every expansion step—catching Trojan macros that
     expand into `by_elab`, `include_str`, `run_cmd`, or `#eval` before
     `CommandElabM`/`TermElabM` runs.
3. **Check 3 — Namespace-Component + Kernel Statement-Identity Verification (`checkKernelAndStatementIdentity`):**
   - Enforces `!(privateToUserName ci.name).components.contains \`Trusted` on
     all non-`Trusted` constants (closing `Proof.Trusted.CrateTheorem` shadowing)
     and verifies in `Kernel.Environment` after `baseEnv.toKernelEnv.replay`
     that `kci.type == mkApp (mkConst ``Trusted.CrateTheorem) (mkConst
     targetCrateConst)` (closing `notation "Trusted.CrateTheorem"` spoofing).

All 8 test cases in `support/PureMacroAudit.lean` pass (`T1` benign custom
`notation`/`infixl`/`macro_rules` accepted; `T2a` `by_elab` and `T2b`
`include_str` Trojan macros rejected at Check 2; `T3a` `dbgTrace` and
`T3b`/`T3c` `@[implemented_by]`/`unsafeIO` macros rejected at Check 1/2; `T4a`
`notation "Trusted.CrateTheorem"` spoofing and `T4b` `Proof.Trusted.CrateTheorem`
shadowing rejected at Check 3).

#### 7.3 Building Block B: Hardened Unprivileged Linux Sandbox (`support/hardened_sandbox_probe.py` and `support/linux_sandbox_probe.py`)

To lift Phase 1 completely (unlocking `omega`, `simp`, `decide`, `deriving
DecidableEq`, `macro_rules`, `elab`, `tactic`, `local instance`, and `section`
in `Theory.lean` and `Proof.lean`), [`support/hardened_sandbox_probe.py`](support/hardened_sandbox_probe.py)
and [`support/linux_sandbox_probe.py`](support/linux_sandbox_probe.py) implement
and benchmark an unprivileged Linux `7.1.6-1rodete1-amd64` sandbox around `lean`
compilation:

1. **Landlock ABI v9 (`SYS_landlock_create_ruleset` / `restrict_self`):**
   - Enables all 17 filesystem access bits (`handled_access_fs = (1 << 17) - 1`,
     including `LANDLOCK_ACCESS_FS_IOCTL_DEV` and
     `LANDLOCK_ACCESS_FS_RESOLVE_UNIX`), both TCP network bits
     (`handled_access_net = 0x3`), and both IPC scoping bits (`scoped = 0x3`:
     `LANDLOCK_SCOPE_ABSTRACT_UNIX_SOCKET` and `LANDLOCK_SCOPE_SIGNAL`).
   - Grants read-only access only to the Lean toolchain, system libraries
     (`/usr`, `/lib`, `/lib64`, `/bin`, `/dev/urandom`), and staged input
     `.lean`/`.olean` files, and write access only to the single output `.olean`
     directory.
2. **`seccomp-bpf` Filter with `CLONE_THREAD` Discrimination and Post-Exec `SYS_execve` Lock:**
   - Returns `ENOSYS` (`38`) on `SYS_clone3` (`435`), causing glibc
     `pthread_create` to fall back transparently to `SYS_clone` (`56`).
   - Inspects `(args[0] & CLONE_THREAD)` (`0x00010000`) on `SYS_clone`: permits
     thread creation (`CLONE_THREAD` set) so Lean's internal multi-threaded task
     pool (`Task.spawn` / `IO.asTask`) works unmodified, and returns `EPERM`
     (`1`) when `CLONE_THREAD` is unset (blocking process forks).
   - Blocks `SYS_fork`, `SYS_vfork`, `SYS_setsid`, `SYS_socket`,
     `SYS_socketpair`, `SYS_connect`, `SYS_bind`, `SYS_listen`, `SYS_sendto`,
     `SYS_sendmsg`, `SYS_ptrace`, `SYS_process_vm_readv`, and
     `SYS_process_vm_writev` with `EPERM`, and locks `SYS_execve`/`SYS_execveat`
     to `EPERM` at `lean` startup via a minimal constructor stub
     (`liblock_execve.so`).
3. **Empirical Verification and Overhead (`N = 20` Runs on Linux `7.1.6-1rodete1-amd64`):**
   - Parallel `Task.spawn` / `IO.asTask` inside Lean `v4.34.1` succeeds (`exit
     0`, `TASK_POOL_OK total=4000978`).
   - All 11 attack vectors—`IO.FS.writeFile`, `IO.FS.readFile "/etc/passwd"`,
     `include_str "../../../../../../etc/hostname"`, `IO.Process.output`,
     upstream `Trusted.olean` overwrite, TCP `socket(AF_INET, SOCK_STREAM)`,
     UDP `Std.Internal.UV.UDP.Socket` (`SOCK_DGRAM`), `AF_UNIX`
     (`/run/docker.sock` / abstract sockets), direct dynamic-linker invocation
     (`/lib64/ld-linux-x86-64.so.2`), `setsid()` background sleeper process
     spawning (`comparator#77`), and `ptrace(PTRACE_ATTACH)` /
     `process_vm_readv` (`comparator#43`)—are deterministically blocked with
     `EPERM`/`EACCES`.
   - Across $N = 20$ compilations of `GoodTheory.lean` (`omega`, `decide`,
     `deriving DecidableEq`, `macro_rules`, `elab`, `termination_by`), the
     sandbox adds **`+3.11 ms` (`+1.19%`, `264.80 ms` vs. `261.69 ms`
     unsandboxed)** and produces byte-for-byte identical `.olean` files
     (`SHA-256: b30dd5db9ce7177045e31072c6c5d999e46c8e0f104579b0b443e211b91e0fb4`).
   - `bubblewrap 0.12.0` (`bwrap --unshare-all --die-with-parent --ro-bind / /
     --tmpfs /run --tmpfs /tmp --proc /proc --dev /dev`) also runs unprivileged
     on `7.1.6-1rodete1-amd64` (`exit 0`) and composes with `--seccomp <fd>` for
     environments where unprivileged user namespaces are enabled.

---

## Boundaries

1. **Pre-Compiled Third-Party `.olean` Files Remain Untrusted Inputs:**
   As demonstrated in Finding 3.3 (`support/olean_deser/TestOleanDeser.lean`),
   Lean `v4.34.1`'s `lean_compacted_region_read` (`src/runtime/compact.cpp:643-685`)
   does not validate pointer graphs, object tags, or array bounds before
   returning `ModuleData` to `importModules`. Any `.olean`-based auditor
   (`TrustedBoundary.lean`, `leanchecker`, `SafeVerify`) must compile `.olean`
   files locally from staged `.lean` sources using a pinned `lean` binary;
   ingesting pre-compiled proofs from untrusted third parties without local
   re-elaboration requires a bounds-checked declaration wire format such as
   `lean4export` NDJSON (`df81913eee5519d5a88ae5b0fd701b5298cc29ab`) paired with
   an out-of-sandbox kernel (`nanoda_bin`, `lean4lean`, `con-leche`, `con-ron`).
2. **Pure `MacroM` Auditing (`support/PureMacroAudit.lean`) Covers `syntax` / `notation` / `macro` / `macro_rules`, Not Arbitrary `TermElabM` / `TacticM` Metaprograms:**
   Because `CoreM`, `MetaM`, `TermElabM`, `TacticM`, and `CommandElabM` wrap
   `EIO Exception` (`MonadLift IO`), user-defined `elab` and `elab_rules`
   extensions cannot be confined purely at the monad type level in Lean `v4.34.1`;
   permitting arbitrary `elab`/`tactic` metaprograms in `theory/` requires an OS
   process sandbox (`support/hardened_sandbox_probe.py` or `bwrap`).
3. **Linux Kernel Version Requirements for Unprivileged Sandboxing:**
   Landlock filesystem rules require Linux $\ge 5.13$ (ABI v1), TCP port
   filtering requires Linux $\ge 6.7$ (ABI v4), IPC abstract Unix socket and
   signal scoping requires Linux $\ge 6.12$ (ABI v6), and `RESOLVE_UNIX` requires
   Landlock ABI v9 (verified on Linux `7.1.6-1rodete1-amd64`). On older Linux
   kernels ($3.5 \le \text{kernel} < 6.12$), the `seccomp-bpf` filter in
   `support/hardened_sandbox_probe.py` still enforces `SYS_socket`,
   `SYS_connect`, `SYS_clone` (`CLONE_THREAD`), `SYS_execve`, and `SYS_ptrace`
   denial at the syscall layer, while filesystem path isolation on kernels
   without Landlock requires either `bwrap` (`CLONE_NEWUSER` + `CLONE_NEWNS`) or
   Phase 1 (`"preflight"` + `PureMacroAudit.lean`).

---

## Evidence

| Artifact / Source | Path / Revision | What It Establishes |
| :--- | :--- | :--- |
| Anneal Trust Model & Auditor | `joshlf/anneal@287e7ad5182f74f25fcaf9098840f5f39aa601d6` (`docs/trust-model.md`, `trusted/audit/TrustedBoundary.lean`, `trusted/audit/src/lib.rs`) | Baseline 3-tier classification, Phase 1 AST allowlist, Phase 2 `loadExts := false` + `rebuildNat` + `isStructuralRecCompilerHelper` + whole-DAG `base.toKernelEnv.replay`, and line 647 `getRoot == \`Trusted` check. |
| Lean `v4.34.1` Kernel, Runtime & Lake | `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`src/runtime/compact.cpp`, `src/runtime/object.cpp`, `src/kernel/quot.cpp`, `src/Lean/AddDecl.lean`, `src/Lean/Environment.lean`, `src/Lean/Replay.lean`, `src/lake/Lake/Load/Toml.lean`) | `MacroM` vs `CoreM` monad stack; `module` `.olean` axiom weakening; `compact.cpp` fast/slow paths; `lean_nat_big_le` and `Nat.reprFast` behavior on negative GMP `mpz`; `Replay.lean` `#15100`/`#15101`; Lake `Toml.lean` fields. |
| Phase 1 vs. Phase 2 42-Feature Probe | [`support/PreflightVsPhase2Probe.lean`](support/PreflightVsPhase2Probe.lean), [`support/Phase2FeatureAudit.lean`](support/Phase2FeatureAudit.lean) | Proves 40 of 42 benign constructs rejected by Phase 1 pass Phase 2, identifies 3 child-node omissions in Phase 1, and proves `include_str` exfiltrates host files if Phase 1 is dropped without a sandbox. |
| Pure `MacroM` + Post-Expansion Verifier | [`support/PureMacroAudit.lean`](support/PureMacroAudit.lean) | Runnable 3-check Lean `v4.34.1` prototype admitting pure `notation`/`infixl`/`syntax`/`macro_rules` without OS sandboxing across 8 positive/negative test cases. |
| Unprivileged Linux Sandbox Probes | [`support/hardened_sandbox_probe.py`](support/hardened_sandbox_probe.py), [`support/linux_sandbox_probe.py`](support/linux_sandbox_probe.py) | Landlock ABI v9 + `seccomp-bpf` (`CLONE_THREAD` filter + post-exec `SYS_execve` lock) and `bwrap` probes blocking all 11 host I/O, IPC, process, and `ptrace` vectors with `+3.11 ms` (`+1.19%`) overhead while preserving `Task.spawn`. |
| `SafeVerify` Bypasses Probe | [`support/SafeVerifyBugsProbe.lean`](support/SafeVerifyBugsProbe.lean) | Reproduces `SafeVerify@b291b588a53999a7e837dda61c7dbfe8c550c814` bypasses (`partial def` `._unsafe_rec`, un-replayed `map₁` helper module, `equivDefn` `sorryAx`, `supplementedDecls`) vs. `TrustedBoundary.lean`. |
| `v4.34.1` Exploits & Replay Probes | [`support/ProbeSafeCoerce.lean`](support/ProbeSafeCoerce.lean), [`support/ProbeNegativeNatLit.lean`](support/ProbeNegativeNatLit.lean), [`support/ProbeReplayExploits.lean`](support/ProbeReplayExploits.lean), [`support/ProbeCVEsAnd14875.lean`](support/ProbeCVEsAnd14875.lean) | Empirical verification of `#15717` (`ST.Ref.mk`), `SafeVerify#20` negative `mpz` `Nat` literal (`leanchecker` bypass & `Nat.reprFast` masking vs. `rebuildNat`), `#15100`, `#15101`, `CVE-2026-72711`, `CVE-2026-72844`, and `#14875`. |
| Elaboration Effects, `module`, `.olean`, & Retroactive Mutation Probes | [`support/effects/`](support/effects/), [`support/module_system/`](support/module_system/), [`support/olean_deser/`](support/olean_deser/), [`support/retroactive_mutation/`](support/retroactive_mutation/) | Runnable Lean `v4.34.1` probes for `loadExts`, `module` `.olean` vs. `.olean.private` axiom weakening, `compact.cpp` `SIGSEGV` crashes, and the 5 retroactive mutation vectors (including `Proof.Trusted.CrateTheorem`). |
| Cross-Prover Sources | `agda@ec45c73baa`, `ghc@37ad471050`, `rocq@4402a03e26`, `metarocq@51b14e4bb5`, `mm0@0d414c0bfd`, `watt@8f16788f`, `cackle@f9f09eeb`, `endo@679d9afaa4` | Primary-source verification of GHC Safe Haskell 3-tier duality, Agda `tcPragmaForeign`/`tcPragmaCompile` `--safe` backend-compilation bypass, Rocq `coqchk` `validate.ml`, and `mm0-c` lockstep specification stream. |

---

## Revalidation

All standalone probes in [`support/`](support/) can be re-executed directly with
the pinned Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) toolchain
and Python 3 on Linux x86_64:

```bash
cd reports/untrusted-proof-dependencies-effect-isolation-and-guarantee-verification/support

# 1. Phase 1 vs. Phase 2 42-feature matrix and Phase 2 audit
lean --run PreflightVsPhase2Probe.lean
lean Trusted.lean -o Trusted.olean
lean GoodTheory.lean -o GoodTheory.olean
lean EvilTheory.lean -o EvilTheory.olean
lean --run Phase2FeatureAudit.lean

# 2. Pure MacroM expansion + post-expansion syntax audit + kernel statement identity (8 test cases)
lean --run PureMacroAudit.lean

# 3. Unprivileged Linux Landlock v9 + seccomp-bpf (CLONE_THREAD) + bwrap sandbox probes
python3 linux_sandbox_probe.py
python3 hardened_sandbox_probe.py

# 4. SafeVerify bypass reproductions and Lean v4.34.1 exploit/replay probes
lean --run SafeVerifyBugsProbe.lean
lean --run ProbeSafeCoerce.lean
lean --run ProbeNegativeNatLit.lean
lean --run ProbeReplayExploits.lean
lean --run ProbeCVEsAnd14875.lean

# 5. Elaboration effects, module system part inspection, .olean deserialization, and retroactive mutation
(cd effects && lean M.lean -o M.olean && lean N_compile.lean && lean --run AuditHarness.lean)
(cd module_system && lean Dep.lean -o Dep.olean && lean --run InspectParts.lean && lean ConsumerPlainImport.lean)
(cd olean_deser && lean --run TestOleanDeser.lean)
(cd retroactive_mutation && lean --run RunRetroactiveMutationProbe.lean)
```
