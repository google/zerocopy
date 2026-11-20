# Sail RISC-V in Lean 4: Extraction Provenance, the 75 Extern Axioms and Their Cones, Lean 4.34.1 Portability, and Privileged/Config Coverage at sail-riscv `ec5200bd`

## Summary

- **Where the Lean comes from.** Upstream `riscv/sail-riscv` generates its Lean model in-tree. It has two CMake targets, `generated_lean_rv64d` (noncomputable, with axioms) and `generated_lean_executable_rv64d` (computable stubs), plus a `lean_emulator/`.
  - Both published third-party extractions are older ConcurrencyInterface-V1 snapshots: `opencompl/sail-riscv-lean@51c635c4` (nightly, no provenance recorded) and `Verified-zkEVM/riscv-zkvm@6810fc14` (pinned, scoped).
  - sail-riscv HEAD emits V2 (ArchSem free-monad) Lean.
- **The 75 axioms are hand-written.** They live in sail-riscv `handwritten_support/RiscvExtras.lean`, which reaches the build through `--lean-import-file`. The count is 75 at sail-riscv `0.13.1`, at `b7d13572`, and at HEAD `ec5200bd`.
  - Breakdown: 67 SoftFloat, 4 LR/SC reservation, 2 terminal, 1 random, 1 experimental-extension switch.
  - **The Sail Lean backend never emits `axiom` or `opaque` for externs.** It omits the definition and calls the extern's Lean name.
- **Reservation state is outside the model by design.** `match_reservation : paddr → Bool` is a state-independent function, so no theorem over the extraction can relate an LR to a later SC.
- **Axiom cones (syntactic, over-approximate probe).**
  - A whole-step root (`try_step`) reaches 74 of 75 axioms over the full model, and 6 over riscv-zkvm's scoped model.
  - Every load, store and page-table write reaches `load_reservation` or `match_reservation`, plus `plat_term_write`.
  - Pure ALU/M, SFENCE.VMA, FENCE.I, WFI and ECALL `execute_*` functions reach none.
  - riscv-zkvm does not eliminate axioms. It scopes the modules and allowlists 4 platform axioms for its per-instruction theorems. Its module list also omits Zifencei.
- **Removing them.** Replacing `axiom` with `opaque` in the import file keeps the externs uninterpreted with zero axioms and no `noncomputable` (Lean 4.34.1 probe). Upstream's executable stubs instead `panic`, which the kernel reduces to `default` — e.g. SC always fails.
- **Lean 4.34.1.** Sail `sail2` since `31342bdb` (2026-11-09) generates `lean4:v4.34.1` projects against lean-sail `v10`.
  - It needs two workaround options; its commit message reports 4.35.0 unusable for constructor-heavy models.
  - No Sail release does this yet: 0.20.3 targets v4.29.0, and pre-2026-10-14 output calls `assert`, which clashes with Lean ≥ 4.34.
  - Upstream's own Lean CI has been red since 2026-11-18 (model build) and 2026-11-03 (emulator).
- **Config is compile-time.** `config …` values become constant `def`s, not axioms or parameters. The default rv64d config enables C/F/D/V, CFI, and both Svade and Svadu, so an RV64IM S-mode reference needs a custom JSON and regeneration.

## Applicability

Observed 2026-11-20 (UTC). Subjects and their roles:

| Subject | Role |
|---|---|
| `riscv/sail-riscv@ec5200bdfe0c10afa6dbb1f7b0980db2d236236e` (`master` HEAD, 2026-11-19) | Primary Sail source: Lean targets, handwritten support, privileged model, config schema. |
| `riscv/sail-riscv@b7d13572fcd4a87d0999eb6303652cd05a47881e` (2026-08-19) | Inferred generator input of the opencompl snapshot (derived; see Findings §1). |
| `riscv/sail-riscv` tag `0.13.1` = `27224ccb2290f022e46213c05b3e72e8a9ea635e` | Pinned input of riscv-zkvm. |
| `rems-project/sail@97aa617dcd4d01575f773cb58ea1e8686858c8c2` (`sail2` HEAD, 2026-11-17; `git describe` `0.20.3-binary-90-g97aa617dc`) | Lean backend source. Tags `0.20.3` = `3df54034910b31a1e00d948ee965b2e9603d68e0` and `0.20.3-binary` = `60695b1ea377048f0adc39c62671cd099b2ed9f6` were inspected for the release defaults. `8eb1fb6b5bf9f18c0f89f71e94ff0c5894acd7c1` is the inferred opencompl generator. |
| `rems-project/lean-sail` `v10` = `e4745c82fe329f162700020dcd31da6b342473b9` (= `main` HEAD) | Runtime library; toolchain history checked across tags v5 (`079463134b9c…`) through v10. |
| `opencompl/sail-riscv-lean@51c635c460125ac87955d061fcd902ce03b8011f` (= `main` HEAD; last push 2026-08-20) | Full-model V1 extraction. |
| `Verified-zkEVM/riscv-zkvm@6810fc14d9c40373101321cefaec59df8d82e3e7` (= `main` HEAD) | Scoped, pinned V1 extraction and axiom gate. |
| Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) | Toolchain for all probes. |

Scope:
- The extraction-provenance, axiom and backend findings apply to the exact revisions above.
- The privileged-model coordinates (§8) are for `ec5200bd` only. For the opencompl generated-Lean coordinates of trap entry, CSR and Sv39 behaviour, see package `riscv64-sv39-opensbi-trap-wx-and-sail-lean-semantics`. For the RV64D integration and the ADD/decoder proofs, see package `sail-isa-models-lean-backend-and-rv64d-decoding-framing`.
- For the specification-vs-Sail analysis of address-translation caching (non-leaf entries that `SFENCE.VMA` with `rs1 ≠ x0` does not invalidate, Sail's leaf-only TLB and `FENCE.I` no-op as under-approximations, cross-ISA shootdown rules), see package `mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement`. It pins the same sail-riscv revision `ec5200bd`; §8 here records only the Sail-side details that package does not cover.
- No RISC-V Lean model was built or regenerated here, and the Sail compiler was not run. Lean-level claims about the extractions come from source inspection and the syntactic cone probe, not from `#print axioms` on a built environment.

## Findings

### 1. Where the Lean comes from

**1.1 Upstream targets.** Basis: source (`riscv/sail-riscv@ec5200bd`).

- Commands (`model/CMakeLists.txt:423-497`):
  - `generated_lean_rv64d` runs `sail <common flags> --config <cfg> --lean --memo-z3 --lean-output-dir … --lean-force-output --lean-non-beq-type instruction|instr_info|HartState|ExecutionResult|Step --lean-noncomputable --lean-noncomputable-function encdec_{forwards,backwards,compressed_forwards,compressed_backwards}[_matches] --lean-import-file ../handwritten_support/RiscvExtras.lean -o Lean_RV64D`.
  - `generated_lean_executable_rv64d` instead passes `--lean-import-file ../handwritten_support/RiscvExtrasExecutable.lean -o Lean_RV64D_executable` and drops `--lean-noncomputable`.
- Inputs:
  - config: `${CMAKE_BINARY_DIR}/config/rv64d_v256_e64.json` (`model/CMakeLists.txt:237-242`);
  - module set: `SAIL_MODULES`, default `--all-modules` (`model/CMakeLists.txt:9`);
  - Sail version: `--require-version` from `cmake/sail_required_version.txt` = `0.20.3`.
- The executable model dates from `bdff014367ece67fa10d210d402c3504d2387d90` (2025-06-05).
- The emulator `lean_emulator/` dates from `ba5c7598626832a529e5b59f16921b8decb2d7c7` (2026-07-16).
  - It requires `GaloisInc/ELFSage@7e68e68e836025df741de04a5bb83439fe88d956` plus the executable model.
  - It pins `lean-toolchain` `v4.29.0`, and lean-sail `c816ea7ad03cce98d51acee252540fd4215fede8` (`v6`) in `lake-manifest.json.in`.
  - Its Lean sources contain no `partial`, `unsafe`, `implemented_by`, `@[extern` or `axiom`.

**1.2 Upstream HEAD is ConcurrencyInterface V2.** Basis: source.
- `model/core/phys_mem_interface.sail:16` contains `$define CONCURRENCY_INTERFACE_V2`. It was introduced by `4f8ce828fcacd6f392cb4f9be9046d46ce4bec07` (2026-10-01, "Port to v2 of the Sail concurrency interface (#1871)").
- So HEAD's generated Lean uses lean-sail `Sail.ArchSem`. `handwritten_support/RiscvExtras.lean:13` reads `open Sail.ArchSem`.
- Both published extractions predate this and use `open ConcurrencyInterfaceV1`, the stateful `EStateM` interface.

**1.3 opencompl/sail-riscv-lean@51c635c4 is an unpinned nightly.** Basis: source + derived.
- Its `.github/workflows/update-sail-build.yml` (cron `0 6 * * *`) clones Sail and sail-riscv at HEAD, runs `cmake --build build/ --target generated_lean_rv64d`, then `lake build`, and publishes `build/model/Lean_RV64D`.
- The commit message ("Update main to output generated at ") records no input revisions. There has been no publish since 2026-08-20T06:16:02Z.
- Inferred inputs (derived):
  - **sail-riscv `b7d13572…`**, the last `master` commit before the 06:00Z cron. Corroboration: generated `LeanRV64D/SysControl.lean:611-612` has `shouldWakeForInterrupt` reading `read_mip IncludePlatformInterrupts`, which `b7d13572` introduced; its parent's `model/sys/sys_control.sail:149-151` has `(mip.bits & mie.bits) != zeros()`.
  - **Sail `8eb1fb6b…`** (`0.20.2-64-g8eb1fb6b5`). Its `src/sail_lean_backend/sail_plugin_lean.ml:97,100` emits `lean4:v4.29.0` and lean-sail `v5`, matching the snapshot's `lean-toolchain` and `lakefile.toml` (`rev = "v5"`, resolved to `079463134b9c…`).
- Counts (grep over `LeanRV64D/` + `LeanRV64D.lean`):
  - 161 files, 174,111 lines;
  - 75 `axiom`, 166 `noncomputable` tokens, 11 `termination_by`, 1 `macro_rules`;
  - 0 `partial def`, `unsafe`, `implemented_by`, `@[extern`, `opaque`, `sorry`, `native_decide` or `bv_decide`.
- There is one unmeasured `while`, in the top-level driver `loop` (`Step.lean:497`). A Lean `while` adds an `opaque` implementation constant (`_private.Init.While.0.repeatM.impl`) to the cone (probe `support/WhileLoopCone.lean`). `try_step` does not use it.

**1.4 riscv-zkvm@6810fc14 is pinned and scoped.** Basis: source.
- `sail-import/PROVENANCE.toml` records:
  - sail-riscv `0.13.1` (`27224ccb…`);
  - Sail `0.20.3` at rev `60695b1e…` (the `0.20.3-binary` tag, one CI-fix commit after tag `0.20.3`);
  - lean-sail `079463134b9c…`, Lean `v4.33.1`;
  - `sail_modules = ["main","I_insts","M_insts","Zicsr_insts","K_core","Zkr","Zicboz","Zicbom_insts"]`;
  - config `sail-import/rv64d_v256_e64.json` (sha256 `a3b545eb…`), a `model_sha256`, `expected_lean_files = 121`.
- `scripts/regen-model.sh --check|--write` checks `sail --version` against the pinned version and rev prefix, and the sail-riscv tag against the rev.
- Extraction: 121 files, 60,278 lines. Counts: 75 `axiom` (same handwritten file), 125 `noncomputable`, 0 `partial`/`unsafe`/`implemented_by`/`@[extern`/`sorry`.
- **The module list omits `Zifencei`** (no `execute_FENCEI`) and all A/F/D/C modules.
- `regen-model.sh` passes `--variable "TERMINATION_FILE = true"`. That variable has been dead in sail-riscv since `1993f2d414fe6326dc0855a901d620b82f582c71` (2025-12-08, "Scatter termination.sail"): `git grep` finds no use at `0.13.1` or at HEAD. Termination measures are now inline (e.g. `model/sys/vmem.sail`, `model/core/extensions.sail`, `model/postlude/step.sail`).

### 2. The 75 extern axioms: identity, origin, entry points

**2.1 Exact list (HEAD `handwritten_support/RiscvExtras.lean:31-112`).** Basis: source.

| Category | # | Declarations |
|---|---|---|
| LR/SC reservations | 4 | `axiom load_reservation : BitVec Arch.addr_size → Nat → SailM Unit`, `axiom match_reservation : BitVec Arch.addr_size → Bool`, `axiom cancel_reservation : Unit → SailM Unit`, `axiom valid_reservation : Unit → Bool` |
| Terminal / HTIF | 2 | `axiom plat_term_write {α} : α → SailM Unit`; `axiom plat_term_read : Unit → SailM String` (declared at `model/sys/platform.sail:241` but never called) |
| Random | 1 | `axiom get_16_random_bits : Unit → SailM (BitVec 16)` |
| Configuration | 1 | `axiom sys_enable_experimental_extensions : Unit → Bool` |
| SoftFloat | 67 | `riscv_f{16,32,64}{Add,Sub,Mul,Div,MulAdd,Sqrt}`, int↔float conversions (`riscv_f16ToI32` … `riscv_ui64ToF64`), float↔float conversions incl. `riscv_f32ToBF16`, comparisons `riscv_f*{Lt,Lt_quiet,Le,Le_quiet,Eq}`, `riscv_f*roundToInt`, each of shape `BitVec 3 → BitVec n … → (BitVec 5 × …)` |

- The count was verified as exactly 75 in the HEAD file, the riscv-zkvm copy (sail-riscv `0.13.1`) and the opencompl copy.
- The V1 copies type the reservation address as `Arch.pa`; the V2 port changed it to `BitVec Arch.addr_size`.
- The same file also supplies `instance : SizeOf extension` and `macro_rules | \`(tactic| decreasing_trivial) => \`(tactic| decide)` (lines 114-118), used for termination of `currentlyEnabled`.

**2.2 Sail-side origin.** Basis: source.
- Reservations: `model/sys/sys_reservation.sail:21-24`. These have no `lean:` key, and the file says reservation state "is maintained external to the model … this simplifies the concurrency analysis".
- `plat_term_write` (`model/sys/platform.sail:240`) and `get_16_random_bits` (`model/core/sys_regs.sail:1293`) have no `lean:` key.
- `val sys_enable_experimental_extensions = pure "sys_enable_experimental_extensions"` (`model/prelude/prelude.sail:245`) is a string extern for all backends.
- SoftFloat: `model/core/softfloat_interface.sail` (e.g. line 38 `val riscv_f16Add = pure {cpp: "softfloat_f16add", lem: "softfloat_f16_add"} : …`).

**2.3 How the backend handles externs (rems-project/sail@97aa617d).** Basis: source.
- At call sites, `src/sail_lean_backend/pretty_print_lean.ml:1079-1080`:
  ```ocaml
  let extern_id = if Env.is_extern f env "lean" then Some (Env.get_extern f env "lean") else None in
  let d_id = Option.fold ~some:string ~none:(doc_id_ctor ~ren_ctor:true ctx f) extern_id in
  ```
- Definitions of externs are skipped (`pretty_print_lean.ml:1507-1523`: `should_print_function_def`, and in `doc_defs_rec`, `if Env.is_extern (id_of_fundef fdef) env "lean" then docdefs else docdefs ^^ group (doc_fundef ctx fdef) …`). Body-less `val` specs fall through to a catch-all and print nothing.
- `Env.is_extern id env backend = Option.is_some (Ast_util.extern_assoc backend …)` (`src/lib/type_env.ml:1748`) holds for a backend key or a generic binding.
- **No code in `src/sail_lean_backend/` emits `axiom`**; the only occurrence is the reserved-word list `keywords.ml:22`. A body-less non-extern `val` such as `load_reservation` is simply referenced by its Sail name, and the program elaborates only if an import file defines that name.
- Import files are copied into the package with `sed 's/THE_MODULE_NAME/<Pkg>/g'` (`sail_plugin_lean.ml:348`).

**2.4 Entry points.** Basis: source. Generated call sites in opencompl; HEAD Sail sources correspond.

| Axiom | Generated call site | Enclosing function / guard | HEAD Sail source |
|---|---|---|---|
| `load_reservation` | `LeanRV64D/VmemUtils.lean:315` | `vmem_read_addr`, under `if res` | `model/sys/vmem_utils.sail:244` |
| `match_reservation` | `VmemUtils.lean:398` | `vmem_write_addr`: `res && not (match_reservation …)` | `vmem_utils.sail:272` |
| `cancel_reservation` | `InstsEnd.lean:67359`; `SysControl.lean:806` | `execute_STORECON`; `reset_sys` | — |
| `valid_reservation` | `Step.lean:256` | `run_hart_waiting`, WRS exit | — |
| `plat_term_write` | `Platform.lean:707` | HTIF `tohost` write handler on the physical-write path | — |
| `get_16_random_bits` | `ZkrControl.lean:265` | Zkr `seed` CSR read | — |
| `sys_enable_experimental_extensions` | `PlatformConfig.lean:1191,1261` | `hartSupports` clauses for `Ext_Zibi`, `Ext_Zvabd`, hence every `currentlyEnabled` / `hartSupports` caller | — |

- **At HEAD only,** MRET and SRET also contain `if plat_reservation_invalidate_on_xret then cancel_reservation();` (`model/extensions/I/base_insts.sail:650,724`). This came from `80314f5490c15213b97ee325823971745c2dfc3f` (2026-10-28), and the knob defaults to `false`. Before that commit, xRET never touched reservations; that includes the opencompl and riscv-zkvm snapshots.
- **Consequence (derived).** `match_reservation` is a fixed function of the physical address, and `load_reservation` / `cancel_reservation` are unknown monadic actions.
  - No theorem over these extractions can relate a prior LR to SC success.
  - None can show that LR leaves architectural state unchanged, because `load_reservation` is an arbitrary `SailM Unit`.
  - LR/SC pairing semantics needs a normative source other than Sail.

### 3. Axiom cones of step and per-instruction roots

Basis: derived (probe `support/axiom_cone.py`). This is a syntactic reachability over generated source that mimics `CollectAxioms`. It over-approximates, and it does not follow elaboration-introduced constants. Outputs: `support/axiom_cone_opencompl.txt`, `support/axiom_cone_riscv_zkvm.txt`.

| Root | opencompl full model | riscv-zkvm scoped model |
|---|---|---|
| `try_step` | 74 (67 SoftFloat + `cancel_reservation`, `get_16_random_bits`, `load_reservation`, `match_reservation`, `plat_term_write`, `sys_enable_experimental_extensions`, `valid_reservation`) | 6 (`get_16_random_bits`, `load_reservation`, `match_reservation`, `plat_term_write`, `sys_enable_experimental_extensions`, `valid_reservation`) |
| `execute` | 73 | 5 |
| `ext_decode` | 1 (`sys_enable…`) | 1 |
| `execute_LOAD`, `vmem_read` | 3 (`load_reservation`, `plat_term_write`, `sys_enable…`) | 3 |
| `execute_STORE`, `vmem_write` | 3 (`match_reservation`, `plat_term_write`, `sys_enable…`) | 3 |
| `execute_STORECON` | 4 (adds `cancel_reservation`) | absent |
| `translateAddr` | 2 (`plat_term_write` via `update_and_write_pte` → `write_pte` → physical write; `sys_enable…`) | 2 |
| `execute_CSRReg`, `read_CSR` | 2 (`get_16_random_bits`, `sys_enable…`) | 2 |
| `execute_SRET`, `execute_MRET`, `trap_handler`, `dispatchInterrupt`, `write_CSR` | 1 (`sys_enable…`) | 1 |
| `execute_RTYPE`, `execute_ITYPE`, `execute_MUL`, `execute_DIV`, `execute_SFENCE_VMA`, `execute_FENCEI`, `execute_WFI`, `execute_ECALL` | 0 | 0 (`execute_FENCEI` absent) |

- The only declared axiom unreachable from `try_step` is `plat_term_read`.
- At HEAD, `execute_SRET` / `execute_MRET` would also syntactically reach `cancel_reservation`, even when the config guard is `false`.
- riscv-zkvm's kernel-level gate is consistent with this for its own theorem set. `scripts/AxiomSweep.lean` scans every declaration under `RiscvZkvm.Rv64.*` / `RiscvZkvm.Interpreter.*` and allows only `propext, Classical.choice, Quot.sound, load_reservation, match_reservation, plat_term_write, sys_enable_experimental_extensions` (also `docs/validation.md:150-172`).
- The 4-axiom figure therefore comes from **per-instruction theorem selection plus module scoping**; it does not mean the axioms were eliminated.

### 4. Eliminating or reinterpreting the externs

Basis: source + execution.

- **Upstream executable stubs** (`handwritten_support/RiscvExtrasExecutable.lean`, 118 lines) replace all 75 with `def`s:
  - `panic "TODO: …"` for terminal, `load_reservation`, `match_reservation`, `get_16_random_bits` and every SoftFloat function;
  - `dbg_trace "TODO: cancel_reservation"; return ()`;
  - `fun _ => false` for `valid_reservation` and `sys_enable_experimental_extensions`.
  
  This is axiom-free and computable. However, `panic` elaborates to the type's `default` in the kernel, which fixes an unfaithful semantics: `match_reservation = default = false`, so SC always fails, and float results are default values.
- **`opaque` instead of `axiom`** (probe `support/ExternEncodings.lean`, Lean 4.34.1, all `#guard_msgs` pass):
  - `'sc_ax_total' depends on axioms: [match_reservation_ax]`;
  - `'sc_op_total' does not depend on any axioms`;
  - `'sc_par_total' does not depend on any axioms`.
  
  An `opaque` extern stays uninterpreted (a fixed unknown function, the same meaning as the axiom) and needs only `Inhabited`. The `axiom` form additionally forces `noncomputable` (`error(lean.dependsOnNoncomputable): … not supported by code generator`), which is why the default target passes `--lean-noncomputable`.
- **Explicit parameter.** A structure or typeclass argument gives universally quantified ("for every platform") statements with no axioms.
  - No Sail option produces this, and section `variable`s cannot cross the backend's per-file modules.
  - It would need a backend change: add a binder to `doc_fundef`'s binder list (`pretty_print_lean.ml:1295-1313`) for functions transitively using the externs.
  - Not implemented in any examined revision.
  - Derived: package `mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement` recommends a hand-reviewed target specification that exposes these hooks as `structure` fields. With the current backend that means either the change above or hand-restating the model rather than consuming `sail --lean` output; `opaque` is the zero-axiom option that needs no backend change.
- Relevant backend options (`sail_plugin_lean.ml:102-171`): `--lean-import-file`, `--lean-noncomputable`, `--lean-noncomputable-function`, `--lean-partial-function` (the only way the backend prints `partial`, `pretty_print_lean.ml:1309`), `--lean-extern-type`, `--lean-lib-path/-repo/-rev`, `--lean-matchbv`, `--lean-real-numbers` (pulls Mathlib `v4.29.0`).

### 5. Model-level and stdlib `lean:` bindings are trusted too

Basis: source.

- sail-riscv binds a few operations directly to Lean functions (`model/prelude/prelude.sail:37-47`):
  - `sub_vec` → `_lean_sub` (lean-sail);
  - `sub_vec_int` → `BitVec.subInt`;
  - `quot_round_zero` / `quot_positive_round_zero` → `Int.tdiv`;
  - `rem_round_zero` / `rem_positive_round_zero` → `Int.tmod`.

  DIV/REM fidelity therefore rests on `Int.tdiv` / `Int.tmod`.
- Sail stdlib bindings were corrected recently:
  - `_shr32` was bound to `Int.shiftl` (left shift) until `8efa11c5725477889fc06ffec7d4d6eaefede8a3` (2026-11-06, now `Int.shiftr`);
  - `sub_nat` was bound to `_lean_subi` until `b5fdf4a37f40d1702b900abb87488a46928c11ec` (2026-11-06, now `Nat.sub`).
- Both published RISC-V extractions predate these fixes. The opencompl output contains no `_shr32` lowering: its `Int.shiftl` uses are only `Arith.lean:244,251` (`_shl_int_general` / `_shr_int_general`, both correct).

### 6. Lean v4.34.1 portability and upstream CI state

**6.1 Target versions.** Basis: source + documentation.
- `src/sail_lean_backend/sail_plugin_lean.ml:97-100` at `97aa617d`: `let lean_version = "lean4:v4.34.1"`, `let lib_default_rev = "v10"`. These came from `31342bdbb5a3996d4c1f5231d06e7140df5d3288` (2026-11-09).
- That commit's message: "This requires a couple of workaround options for Lean issues … Using 4.34.1 because 4.35.0 doesn't allow types with a large number of constructors, even for noncomputable models."
- Every generated file now starts with (`sail_plugin_lean.ml:267-286`):
  - `set_option backward.do.legacy true` (Lean issues 13858, 15685);
  - `set_option cleanup.letToHave false` (15661);
  - plus `maxHeartbeats 1_000_000_000`, `maxRecDepth 1_000_000`, `linter.unusedVariables false`, `match.ignoreUnusedAlts true`.
- At tag `0.20.3` the same file still says `lean4:v4.29.0` and lean-sail `v6`. **No released Sail targets v4.34.1.**
- lean-sail toolchain history:
  - nightlies until `79b4d08505af29d88b3918f32d29840fae1fa191` (2026-04-09, → `v4.29.0`);
  - unchanged through v9 (`aa1671114862bbb41b5b1253711f787ab4dcd0de`);
  - v10 changes only `lean-toolchain` → `v4.34.1`.
- `lake build` of v10 on 4.34.1 succeeds: 14 jobs, about 14 s user CPU (`support/lean-sail-v10-build.log`).

**6.2 What broke across versions.** Basis: source + documentation.
- lean-sail v7 (`01bb54c7…`, tag commit dated 2026-10-14) consists of three compatibility commits on top of v6:
  - `30af7f40a5715e2a7b92d577c20393d3c512e7b2` "Make finite choice comparison obviously Nat (for recent Lean)";
  - `2c33d84e7c467706fd6c373314367eb26133306d` "Use unambiguous `open`";
  - `01bb54c7…` "Provide sail_assert to avoid clash with assert with recent Lean versions".
- Sail `7e0e53d183cad75b8f36bfbbecc0ef75614a8418` (2026-10-14, "Lean: change assert function name — For compatibility with Lean 4.34.0 and above"). The backend now prints `sail_assert` (`pretty_print_lean.ml:1203`).
- Older output calls `assert c m`, which collides with Lean ≥ 4.34's `do`-element `assert`. Affected: both published extractions and anything from Sail ≤ 0.20.3.
- One downstream workaround was observed but not inspected. The unmerged `riscv-zkvm` branch `chore/lean-v4.36` (`d81a91030371d1b66ad1a5ff5d348077d3690d6a`, `lean-toolchain` `v4.36.0-rc2`) keeps its generated tree and moves to a lean-sail fork. Its `PROVENANCE.toml` describes the fork as "lean-sail v5 … plus two commits … upstream's unambiguous `open` (2c33d84), and a macro scoped to `Sail` that keeps the generated `assert c m` a call to the model's `assert` on Lean >= 4.34".

**6.3 Upstream CI.** Basis: documentation (public GitHub Actions run metadata; job logs need authentication and were not read). See `support/sail-riscv-compile-lean-ci-runs.tsv`.
- Workflow `.github/workflows/compile-lean.yml` has two jobs:
  - `build`: generate `generated_lean_rv64d` with all modules, then build it with `lean-action`.
  - `lean-emulator`: generate `generated_lean_executable_rv64d` with `-DSAIL_MODULES="H;Zca;Zicbom_insts;Zicboz;Zicsr_insts;Zicfiss_regs;Zimop;Zaamo;Zicntr;Zkr;Sscofpmf;Zihpm;Ssqosid;postlude"`, then `ctest -R lean_emulator`.
  - Both install Sail as `sail-version: "latest"`, i.e. `git clone https://github.com/rems-project/sail.git && make install` (`.github/actions/sail-setup/action.yml:184-190`). That is `sail2` HEAD at job time, not the pinned 0.20.3.
- Run history:
  - Last all-green run: `41700456482` (`9ae1a39d122556fccd2d469665841bb54496aae4`, 2026-11-03).
  - `lean-emulator` has failed since `41719923186` (`02cc53657cf89aac322cc19924b3cb34bb8b787e`, 2026-11-03).
  - `build` last passed in `44095070251` (`6e2f7a935b82df6cc5c8eedafa947b8b3cd8d51c`, 2026-11-17T13:40Z). Sail HEAD then was inferred to be `c44944f11b71e5c9bd4b30cdbf79ea32f6dcf456`, already emitting v4.34.1 / v10.
  - `build` first failed in `44261709218` (`f07820481abee82415bf7f62dc2e97856d62542f`, 2026-11-18), and is still failing at HEAD `ec5200bd` (run `44645042260`, annotation "lake build failed").
- Derived: the full RV64D model generated by a v4.34.1-targeting Sail did compile on 2026-11-17.

### 7. Determinism, executability, licensing, build cost

- **Determinism.** Basis: source.
  - HEAD model text has 7 explicit `undefined`s, all in `model/extensions/V/vext_utils_insts.sail:413-535`.
  - Other choice sources:
    - generated `undefined_*` / register initialisation (`FinChoice` effects under V2);
    - the externs `get_16_random_bits`, `valid_reservation`, `match_reservation`;
    - `try_step(step_no, exit_wait : bool)` (`model/postlude/step.sail:268`), whose `exit_wait` argument decides when a WFI/WRS wait ends (`run_hart_waiting`, `step.sail:23-112`).
  - How lean-sail resolves `FinChoice` / `ChoiceSource` (always index 0 / a trivial source) is documented in package `sail-isa-models-lean-backend-and-rv64d-decoding-framing`.
- **Executability.** Basis: source.
  - The default target is noncomputable (axioms).
  - The executable target plus `lean_emulator` is runnable; its CI is currently red (§6.3).
  - lean-sail has one `partial def`, `elabMatchBv`, a term elaborator (meta code). `match_bv` without an else-branch inserts `by try bv_decide -enums` (`Sail/BitVec.lean:202-231`), but only under `--lean-matchbv`, which is off by default (`opt_disable_matchbv = true`, `sail_plugin_lean.ml:95`).
- **Licensing.** Basis: source.

  | Repo | License |
  |---|---|
  | sail-riscv | `LICENCE`: BSD-2-Clause, plus bundled dependencies |
  | Sail | `LICENSE`: BSD-2-Clause, except ASL-derived aarch64 files and items in `THIRD_PARTY_FILES.md` |
  | riscv-zkvm | BSD-2-Clause, plus MIT for `RiscvZkvm/Rv64/` |
  | **lean-sail** | **no license file** (`git ls-files`) |
  | **opencompl/sail-riscv-lean** | **no license file**; only `RiscvExtras.lean` carries an SPDX BSD-2-Clause header |

  lean-sail was split out of the BSD-2 Sail repository by `42a559fd3c0e70378a1d3e2a985eff645fcaf30c` (2026-01-22) without a stated license.
- **Size and cost.** Basis: source + documentation.
  - sail-riscv HEAD model source: 185 `.sail` files, 38,219 lines.
  - Full RV64D extraction: 161 files / 174k lines. Scoped riscv-zkvm extraction: 121 files / 60k lines; its `regen-model.sh --plan` asks for "about 8 GiB RAM" to regenerate.
  - The upstream CI step "Use Lean to build the model" took 287 s (run `44095070251`) and 406 s (run `41700456482`). `lean-action` may restore a cached `.lake`, so these are not cold timings.

### 8. Privileged-model coverage at sail-riscv `ec5200bd`

Basis: source. Paths are under `model/`. HEAD models the H extension throughout: `VirtualUser`/`VirtualSupervisor` arms in SRET, SFENCE.VMA and WFI, and `TranslationStage = S_Stage | VS_Stage | G_Stage` in the walk and TLB.

- **WARL legalization.**
  - `core/sys_regs.sail`: `legalize_misa:133`, `legalize_mstatus:254`, `legalize_menvcfg:526`, `legalize_senvcfg:545`, `legalize_tvec:673`, `legalize_cause:715`, `legalize_xepc:780`, `legalize_scounteren:826`, `legalize_mcounteren:852`, `legalize_sstatus:1047`, `legalize_satp:1224` (an unsupported MODE returns `prev_value`; ASID truncated to `asidlen`).
  - `core/interrupt_regs.sail`: `legalize_mip:72`, `legalize_mie:105`, `legalize_mideleg:122`, `legalize_medeleg:177`, `legalize_sip:529`, `legalize_sie:574`.
- **Delegation and traps** (`sys/sys_control.sail`).
  - `exception_delegatee:65-81`: S if `currentlyEnabled(Ext_S) & medeleg[idx]`, VS via `hedeleg` when virtual, never below the current privilege.
  - `trap_handler_inner:270`, `trap_handler:453`, `exception_handler:492`, `handle_interrupt:504`.
- **xRET** (`extensions/I/base_insts.sail`).
  - `MRET:616`, `SRET:666`. SRET is illegal in U, and in S when `mstatus.TSR`.
  - `MPRV` is cleared when the new privilege ≠ M, gated by `xret_clears_mstatus_mprv = priv_isa_version >= Privileged_ISA_1_12` (`core/isa_version.sail:57`).
  - Reservation cancel is guarded by `plat_reservation_invalidate_on_xret` (lines 650, 724; default `false`).
- **Sv39 walk and TLB** (`sys/vmem.sail`, `sys/vmem_tlb.sail`, `sys/vmem_pte.sail`).
  - `pt_walk` is declared at `vmem.sail:122` and defined at `vmem.sail:137-261`; `translate:474-498` does `lookup_TLB`, then hit (`translate_TLB_hit:370-413`) or miss (`translate_TLB_miss:416-456`).
  - TLB: `private register tlb : vector(num_tlb_entries, option(TLB_Entry))` with `num_tlb_entries = 2^6` (`vmem_tlb.sail:76-81`). It is direct-mapped by `vpn[5:0] XOR stage_bits` (`tlb_hash:97-108`) and holds **leaf entries only** (`pte`, `pteAddr`, `levelMask`, `asid`, `vmid`, `global`). A superpage entry is duplicated into each accessed 4 KiB index (`add_to_TLB:185-222`).
  - A TLB hit **re-checks** permissions against the cached PTE using the current privilege/MXR/SUM. So SUM/MXR changes take effect immediately, while PTE memory edits stay invisible until a flush.
  - Flushes happen only in `reset_TLB` (via `reset_vmem:765-771`), SFENCE.VMA (`base_insts.sail:778-797`; illegal in U and in S with `mstatus.TVM`) and HFENCE (`extensions/H/hext_insts.sail:119,147`).
  - **A `satp` write does not flush** (`vmem.sail:295-301`). `flush_TLB_Entry:135-163` spares `global` entries whenever an ASID is given (`rs2 ≠ x0`).
  - This TLB is model-specific; `vmem_tlb.sail:9-13` says "a TLB is not part of the RISC-V Architecture specification". Why this leaf-only TLB under-approximates the specification's address-translation caching, which `SFENCE.VMA` operand forms a kernel needs, and how seL4 chooses them is covered in package `mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement`.
- **Svade/Svadu.**
  - `hw_updates_pte` (`vmem_pte.sail:304-310`) is `(Svadu ∧ menvcfg.ADUE)` or `(¬Svadu ∧ ¬Svade)`. Otherwise `update_and_write_pte` (`vmem.sail:95-118`) returns `PTW_PTE_Needs_Update`, i.e. a page fault.
  - On a TLB **hit**, the A/D update writes the TLB's cached PTE (with new A/D bits) to `ent.pteAddr` with a plain store (`vmem.sail:399-405`, `write_pte:56-61`). Whether this matches the specification's atomicity rule is analysed in package `riscv-smode-kernel-sound-nondeterminism-and-spec-permitted-behaviors`.
- **fence.i:** `extensions/Zifencei/zifencei_insts.sail:23-32`, which is `sail_barrier(Barrier_RISCV_i); RETIRE_SUCCESS` with the comment "fence.i is a nop for the memory model". The consequence for instruction-fetch coherence proofs is in package `mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement`.
- **Interrupts** (`sys/sys_control.sail`).
  - `findPendingInterrupt:90-111` uses priority MEI > MSI > MTI > SEI > SSI > STI > SGEI > VSEI > VSSI > VSTI > LCOFI.
  - `getPendingSet:117-151`:
    - returns `None` at once if `mie == 0`, since `51b682d8304f93564b1f527e3d1e24c27e70a3cf` (2026-11-19);
    - computes `pending = read_mip(IncludePlatformInterrupts) & mie`, split by `mideleg` / `hideleg`;
    - M-level interrupts are enabled iff `priv ≠ M ∨ mstatus.MIE`; S-level iff `(priv = S ∧ mstatus.SIE) ∨ priv = U`.
  - `dispatchInterrupt:179-188` is consulted once per step at the start of `run_hart_active` (`postlude/step.sail:115-132`), after pending debug triggers and before fetch.
  - Timer sources:
    - `tick_clock` (`sys/interrupt_implementation.sail:31`), called every `plat_insns_per_tick` instructions (`step.sail:422`);
    - `mtimecmp` / `mtime` (`sys/platform.sail:75,79`);
    - Sstc `stimecmp` (`core/interrupt_regs.sail:11`, `extensions/Sstc/sstc.sail`).
- **WFI** (`base_insts.sail:751-767`).
  - M and S enter `WAIT_WFI`. U is illegal unless `plat_wfi_available_to_usermode`.
  - **`mstatus.TW` is checked only at wait time-out**, in `run_hart_waiting` (`step.sail:23-112`) when the caller passes `exit_wait = true`. There U is illegal if `TW ∨ Ext_S`, and S is illegal if `TW`.
  - Wake condition: `shouldWakeForInterrupt:173-175`, which is `(read_mip(IncludePlatformInterrupts) & mie) ≠ 0` and ignores MIE/SIE and `mideleg`.
- **Counters:** `counter_enabled` (`core/sys_regs.sail:1320`) is `feature_enabled_for_priv(priv, mcounteren[i], scounteren[i], hcounteren[i])`. Writable masks are `sys_scounteren_writable_bits` (`:823`) and `sys_mcounteren_writable_bits` (`:849`).
- **PMP:** `pmpCheck` (`pmp/pmp_control.sail:135`). Entries are checked in order; a partial match faults; M passes unless the entry is locked; `sys_pmp_count == 0` disables the check.
- **TVM** guards `satp` (`is_satp_accessible`, `sys/vmem.sail:282-290`) and SFENCE.VMA. **TSR** guards SRET. **TW** guards WFI as above.
- **Misaligned accesses** are classified before translation in `vmem_read_addr` (`sys/vmem_utils.sail:186-250`) and `vmem_write_addr` (`:308`).
  - `plat_misaligned_exception(access, res)` selects `AccessFault`, `AlignmentException`, or proceed.
  - A page-crossing non-LR/SC access is split. Order and granularity come from `sys_misaligned_order_decreasing`, `sys_misaligned_allowed_within_exp` and `sys_misaligned_byte_by_byte` (`sys/split_access_utils.sail:38,42,70`).

### 9. Configuration: knobs, defaults, and how config reaches the Lean

- **Mechanism.** Basis: source.
  - Model code reads `config a.b.c : T`, e.g. `let plat_reservation_invalidate_on_xret : bool = config platform.reservation.invalidate_on_xret` (`core/platform_config.sail:67`).
  - The Lean targets pass `--config <json>`, and the backend resolves each such value to a **constant `def`**. Examples from the generated opencompl tree: `def plat_reservation_set_size_exp : Nat := 3` (`PlatformConfig.lean:249`) and `def plat_insns_per_tick : nat1 := 2` (`:11032`).
  - Config is therefore neither an axiom nor a parameter, and changing it requires regeneration.
- **Knobs relevant to an S-mode kernel.** Basis: source.
  - HEAD template: `config/config.json.in`.
  - Concrete generated instance at `0.13.1`: riscv-zkvm `sail-import/rv64d_v256_e64.json`.

  | Knob | Default |
  |---|---|
  | `base.medeleg.delegatable_bits` | `0x…00fc_b7FF` at HEAD; `0x…000c_b3FF` at 0.13.1 |
  | `base.mideleg.delegatable_bits` | `0x2222` |
  | `base.scounteren_writable_bits` / `mcounteren_writable_bits` | `0xFFFF_FFFF` |
  | `base.mtvec` / `stvec` | direct + vectored supported, `base_alignment` 2 |
  | `base.reserved_behavior.xtvec_mode` | `Xtvec_Ignore` |
  | `base.xtval_nonzero.*` | `true` |
  | `base.privileged_isa_version` | `Privileged_ISA_1_13` |
  | `memory.pmp` | `count 16`, `usable_count 16`, `grain 0`, TOR/NA4/NAPOT supported |
  | `memory.misaligned.exceptions` | `load_store`, `vector`, `amo`: `None` (proceed); `lrsc`: `AccessFault` |
  | `memory.misaligned` (other) | `order_decreasing false`, `default_allowed_within_exp 0`, `byte_by_byte false` |
  | `platform.reservation` | `reservation_set_size_exp 3`, `require_exact_reservation_addr false`, `invalidate_on_same_hart_store false`, `invalidate_on_xret false` (HEAD only) |
  | `platform.instructions_per_tick` | 2 |
  | `platform.wfi_is_nop` | `false` |
  | `platform.wfi_available_to_user_mode` | `false` |
  | `platform.clint` | `base 0x0200_0000`, `size 0xC000` |
  | `memory.physaddr_bits` (rv64) | 56 |

- **Extensions on in the default rv64d instance:** S, U, M, A, F, D, V (Full), Zca, Zicsr, Zifencei, Zicntr, Zihpm, Sv39, Sv48, Sv57 (Sv32 off), Svbare, **Svade and Svadu both**, Sstc, Svinval, Svnapot, Svpbmt, Zicfilp, Zicfiss, Sscofpmf, Zkr.
- Derived: the default extraction is not an RV64IM-without-C hart. Zicfilp adds privilege/CSR reads to decode, as documented in package `sail-isa-models-lean-backend-and-rv64d-decoding-framing`.

### 10. Derived conclusions for a small kernel-reducible trusted RV64 S-mode model

Basis: derived from §§1–9. These are not established facts about any upstream subject.

1. **Pinning.** A reference that compiles on Lean 4.34.x currently needs an *unreleased* Sail (≥ `31342bdb`), pinned by SHA together with a sail-riscv SHA and lean-sail by SHA, not by the moving `v10` tag. Upstream's own build of HEAD is red, so a known-green pair must be re-established locally; 2026-11-17 is the last observed green date. Lean 4.35.0 is reported unusable for the full model, so the reference toolchain should stay ≤ 4.34.x unless that is re-tested.
2. **Scope and config.** Use a scoped module set (`main`, `I_insts`, `M_insts`, `Zicsr_insts`, **`Zifencei`**, plus a Zalrsc module only if LR/SC is in scope) and a custom, hash-pinned config JSON (C/F/D/V/CFI off; Svade *or* Svadu fixed). Every fidelity claim is relative to that JSON.
3. **Axioms.** Replacing `axiom` with `opaque` in the import file preserves uninterpretation at zero axioms. The upstream `panic` stubs must not be used as a proof reference. A parameterised encoding gives stronger universally-quantified statements but needs backend work.
4. **LR/SC fidelity cannot come from Sail.** The reservation state machine is external, so LR/SC semantics in the trusted model needs a normative basis of its own.
5. **Correspondence granularity.** State correspondence per instruction and per sub-function (`execute_<OP>`, `translateAddr`, `trap_handler`, `dispatchInterrupt`), then audit the composition into `try_step` separately. Per-op cones are axiom-free or tiny, while any statement mentioning `execute` or `try_step` syntactically drags in every clause. Avoid `loop`, which brings in an opaque `while` implementation.
6. **Do not over-fit Sail model artefacts.** These include the 64-entry direct-mapped leaf-only TLB and its hit-path A/D write-back, the WFI `exit_wait` oracle, `invalidate_on_xret = false`, and `tick_clock` every 2 instructions. A trusted model would represent them as nondeterminism or parameters, with correspondence stated as "Sail behaviours ⊆ trusted-model behaviours". Packages `mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement` (address-translation and instruction-cache barriers) and `riscv-smode-kernel-sound-nondeterminism-and-spec-permitted-behaviors` (specification-permitted behaviours) develop this direction.

## Boundaries

- **Not examined:**
  - No Sail binary was run and no RISC-V Lean model (default, executable or scoped) was regenerated or built, on any toolchain. The true kernel axiom closure of a scoped HEAD extraction on 4.34.1 and its cold build time and RAM are unmeasured.
  - The riscv-zkvm fork `dhsorens/lean-sail@f2eb54a2f137072afe561c1bacb759a38eaa8743` and lean-sail PR 25 were not inspected.
  - `GaloisInc/ELFSage` was not inspected.
  - Exposure of pre-2026-11-06 extractions to the `sub_nat` → `_lean_subi` binding was not examined.
- **Unknown:**
  - Why upstream Lean CI fails (logs not readable without authentication). The `build` failure window coincides with three Sail `sail2` commits of 2026-11-17 — `47530a5e93ca34c1c326b34fd02773c26259884a`, `322a415d7e0c4af13c2976fc52075d799ef6680e`, `3626605bbd6b0b783dbc0bfca99b56e9d633ab91` — and sail-riscv `f0782048`; which one breaks the build is unknown.
  - The opencompl generator inputs (§1.3) are inferred, not recorded.
  - "Sail HEAD at a CI run" is inferred from commit timestamps.
- **Known not to apply:**
  - The axiom-cone table is syntactic; it is not `#print axioms`. It can over-count (shadowed local names) and does not follow elaboration-introduced constants.
  - The ADUE / TLB-hit behaviour described here is the model's, not the specification's.
  - The privileged coordinates are for `ec5200bd` only; the H extension and the `invalidate_on_xret` knob are absent from both published V1 extractions.
- **Unsupported:**
  - The Sail Lean backend has no option to emit externs as parameters or typeclass fields.
  - Lean 4.35.0 is reported (commit message only) to reject the model's large inductive types.
- **Stronger conclusions not established:**
  - That any published extraction is a faithful translation of its Sail source.
  - That the riscv-zkvm scoped extraction is axiom-free.
  - That `opaque` externs would be accepted by any particular consumer's admission policy.
  - That HEAD's full model currently builds on 4.34.1.

## Evidence

All observations 2026-11-20 (UTC) unless stated. Repositories were cloned fresh from GitHub.

- **riscv/sail-riscv@ec5200bdfe0c10afa6dbb1f7b0980db2d236236e:**
  - Lean build: `model/CMakeLists.txt:1-50,237-242,423-497`; `cmake/sail_required_version.txt`; `handwritten_support/RiscvExtras.lean:1-118`; `handwritten_support/RiscvExtrasExecutable.lean`; `lean_emulator/{CMakeLists.txt,README.md,lean-toolchain,lakefile.toml.in,lake-manifest.json.in,LeanRiscv.lean,Main.lean}`.
  - CI: `.github/workflows/compile-lean.yml:1-103`; `.github/actions/sail-setup/action.yml:141-190`.
  - Model sources:
    - `model/core/phys_mem_interface.sail:16`; `model/sys/sys_reservation.sail:9-24`; `model/sys/platform.sail:75,79,240-241`;
    - `model/core/sys_regs.sail:133-1340`; `model/core/interrupt_regs.sail:11-579`; `model/core/isa_version.sail:57`; `model/core/platform_config.sail:12-190`; `model/prelude/prelude.sail:37-47,245`; `model/core/softfloat_interface.sail:38`;
    - `model/sys/sys_control.sail:60-190,453-510,544-576`; `model/sys/vmem.sail:50-136,282-301,365-500,765-771`; `model/sys/vmem_tlb.sail:1-243`; `model/sys/vmem_pte.sail:91,140,304-312`; `model/sys/vmem_utils.sail:150-280,308`; `model/sys/split_access_utils.sail:15-70`; `model/sys/interrupt_implementation.sail:31`;
    - `model/extensions/I/base_insts.sail:544,616-728,751-797`; `model/extensions/Zifencei/zifencei_insts.sail:9-40`; `model/postlude/step.sail:23-135,268,422`; `model/pmp/pmp_control.sail:130-170`; `model/extensions/V/vext_utils_insts.sail:413-535`; `model/riscv.sail_project`.
  - Config: `config/config.json.in`; `config/CMakeLists.txt`; `LICENCE`.
  - History: `git log -S'CONCURRENCY_INTERFACE_V2'` → `4f8ce828…`; `-S'invalidate_on_xret'` → `80314f54…`; `-S'TERMINATION_FILE'` → removal at `1993f2d4…`; `--diff-filter=A` for the emulator and executable files. `git show b7d13572` and its parent for `shouldWakeForInterrupt`.
- **rems-project/sail@97aa617dcd4d01575f773cb58ea1e8686858c8c2:**
  - `src/sail_lean_backend/sail_plugin_lean.ml:73-171,250-420`; `src/sail_lean_backend/pretty_print_lean.ml:1-60,1079-1090,1203,1295-1330,1507-1530`; `src/sail_lean_backend/keywords.ml:22`; `src/lib/type_env.ml:1748-1760`; `lib/arith.sail` (`_shr32`, `sub_nat`); `LICENSE`.
  - Tags and history: `git show 0.20.3:src/sail_lean_backend/sail_plugin_lean.ml` (lines 97, 100); `git describe` for `7e0e53d1…` (`0.20.3-binary-49-g7e0e53d18`), `97aa617d…` and `8eb1fb6b…` (`0.20.2-64-g8eb1fb6b5`).
  - Commit messages of `31342bdb…`, `7e0e53d1…`, `8efa11c5…`, `b5fdf4a3…`; first-parent log of `sail2` since 2026-11-05.
- **rems-project/lean-sail@e4745c82fe329f162700020dcd31da6b342473b9:**
  - Sources: all of `Sail/*.lean` (1,723 lines with `SailTest/`); `Sail/BitVec.lean:195-240`; `lakefile.toml`; `lake-manifest.json`; `git ls-files` (no license).
  - Tag→commit→toolchain table for v5–v10; `git log -p -- lean-toolchain`; `git log v6..v7`.
- **opencompl/sail-riscv-lean@51c635c460125ac87955d061fcd902ce03b8011f:**
  - `.github/workflows/update-sail-build.yml`; `README.md`; `lean-toolchain`; `lakefile.toml`; `lake-manifest.json`.
  - `LeanRV64D/RiscvExtras.lean`, `VmemUtils.lean:315,398`, `InstsEnd.lean:67340-67362`, `SysControl.lean:611-612,790-810`, `Step.lean:240-262,497`, `Platform.lean:707`, `ZkrControl.lean:265`, `PlatformConfig.lean:227-253,1164-1261,10994-11034`, `Arith.lean:244,251`.
  - Construct counts by `grep -o` over `LeanRV64D/`.
- **Verified-zkEVM/riscv-zkvm@6810fc14d9c40373101321cefaec59df8d82e3e7:** `sail-import/PROVENANCE.toml`, `sail-import/rv64d_v256_e64.json`, `scripts/regen-model.sh:1-120`, `scripts/check-axioms.sh`, `scripts/AxiomSweep.lean:1-80`, `docs/validation.md:150-172`, `RiscvZkvm/Sail/RiscvExtras.lean`, `LICENSE`.
  - Unmerged branch `chore/lean-v4.36` at `d81a91030371d1b66ad1a5ff5d348077d3690d6a`: only `lean-toolchain` and `sail-import/PROVENANCE.toml` were read.
- **GitHub REST API (unauthenticated, 2026-11-20T03:33–03:43Z):**
  - repository `license` fields;
  - `compile-lean.yml` run list (`support/sail-riscv-compile-lean-ci-runs.tsv`) and per-job conclusions, step timings and check-run annotations for runs `41700456482`, `41719923186`, `44095070251`, `44261709218`, `44645042260`.
- **Probes** (`support/README.md` gives exact commands and expected outputs):
  - `support/axiom_cone.py` with outputs `support/axiom_cone_opencompl.txt` and `support/axiom_cone_riscv_zkvm.txt` (python3; the run directories are the repository roots at the SHAs above);
  - `support/ExternEncodings.lean` (Lean 4.34.1, exit 0);
  - `support/WhileLoopCone.lean` → `support/WhileLoopCone.out` (Lean 4.34.1);
  - `support/lean-sail-v10-build.log` (`lake build`, Lean 4.34.1).
  - Lean binary: `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`.

## Revalidation

- **Axiom identity and count:** `grep -c '^axiom' handwritten_support/RiscvExtras.lean` at the target sail-riscv revision (expect 75 at `ec5200bd`). Also diff the file against `RiscvExtrasExecutable.lean`.
- **Backend extern handling:** in `rems-project/sail`, `grep -n -i axiom src/sail_lean_backend/*.ml` should hit only `keywords.ml`. Re-read `pretty_print_lean.ml` around `should_print_function_def` / `doc_defs_rec` and the `extern_id` call-site code.
- **Lean target version:** `grep -n 'lean_version\|lib_default_rev' src/sail_lean_backend/sail_plugin_lean.ml` at the Sail revision to be pinned, and at the newest release tag. `git describe` on a pinned Sail SHA tells release from development builds.
- **Cones:** rerun `support/axiom_cone.py` on a new extraction tree with the same roots. For authoritative results, build the extraction and run `#print axioms` on statements mentioning `try_step` and per-op `execute_*`.
- **Extern encodings / while-loop cone:** run `lean support/ExternEncodings.lean` (expect exit 0, no output) and `lean support/WhileLoopCone.lean` (expect `support/WhileLoopCone.out`) with the target Lean version.
- **lean-sail on a new toolchain:** check out the tag, edit `lean-toolchain`, run `lake build` (expect 14 jobs).
- **Upstream CI state:** query `…/actions/workflows/compile-lean.yml/runs?branch=master` and per-run `/jobs`.
- **Privileged behaviours:** diff `model/sys/{sys_control,vmem,vmem_tlb,vmem_pte,vmem_utils}.sail`, `model/extensions/I/base_insts.sail` (MRET/SRET/WFI/SFENCE_VMA), `model/postlude/step.sail` and `model/core/platform_config.sail` against `ec5200bd`.
- **Config-to-def lowering:** generate with a modified JSON and grep `PlatformConfig.lean` for the changed `def`.
