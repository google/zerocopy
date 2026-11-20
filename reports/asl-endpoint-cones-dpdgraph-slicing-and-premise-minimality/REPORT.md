# Transitive specification cones for Sail RISC-V and Arm models, statement pinning in Lean and Rocq, and feature-interaction inconsistency

## Summary

- **An authoritative ISA model is megabytes, and a per-instruction cone is tens of kilobytes plus a fixed state-type floor.** At the pinned revisions the Sail RISC-V model is 183 files, 26,614 non-blank non-comment lines and 1.57 MB; the Sail Armv9.4-A model is 432,383 such lines and 19.3 MB. In a published Lean translation of the RISC-V model (49.2 MB of declarations) the name-reference cone of one instruction's semantics is 48 KB to 2.0 MB (median 84 KB, 77 definitions, 38 registers); all 354 instruction definitions together reach 2.8 MB; the full fetch-decode-execute step reaches 26.4 MB because the decoder is in the cone. Even the smallest instruction carries about 140 type declarations, because the execution-result type embeds the syntax-tree type of every instruction and the state monad's register family names every register's type.
- **Pruning granularity decides the answer.** Sail's own module closure for the base integer instruction module is 87 files and 44% of model bytes, because that module requires the privileged `sys` layer. Definition-level cones are far smaller (53 generated definitions for a register-register instruction and 379 for a load, out of about 4,800), but only when overloads are resolved by the compiler: a purely lexical closure over the same source reports 78% of the model for a load instruction.
- **Slicers exist and differ in what they follow.** Sail has `:slice`/`:thin_slice` over a typed call graph (functions, registers, types, let-bindings, mappings, overloads, constructors); the pinned ASL-lineage interpreter has `:filter_reachable_from`; coq-dpdgraph walks kernel terms for constants, inductives and constructors, optionally skipping opaque proof bodies. dpdgraph ignores sorts and universe instances and adds no edge for a primitive projection's record type; Lean's `leanprover/comparator` ships a regression test (`proj_trick`) for exactly that omission.
- **Pretty-printed statements are not statements.** On Lean 4.34.1, `theorem two_plus_two : 2 + 2 = 5` is accepted axiom-free under a scoped instance and prints identically to an honest statement; a module that starts with `prelude` and redefines `Nat.gcd` yields an axiom-free `theorem boom : False` that the kernel accepts. A statement comparator must compare the transitive constant cone, including the kernel-special prelude constants, and must not trust serialized object files.
- **Individually consistent features that conflict when combined are routine, in provers and in ISAs.** Rocq's own critical-bug list (101 entries) has six "conflicts with axioms in library" and four guard-condition or subtyping entries that are inconsistent only together with propositional extensionality; Agda documents six feature combinations excluded from `--safe`; Isabelle accepted an overloading-plus-typedef proof of `False` until Isabelle2016. On the ISA side, the Arm v8-M specification yielded twelve bugs to cross-cutting properties after passing its test suite, and the RISC-V model carries a 1,372-line hand-written cross-extension validator.

## Applicability

Subjects (all in `REPORT.json`) and how they relate:

1. **Models measured:** `riscv/sail-riscv` `model/` and `rems-project/sail-arm` (three architecture versions) at the pinned revisions. Sizes are counted from source text; cones are computed three ways described in Finding 3. All Sail executions used the Sail 0.20.3 binary release (the exact version `sail-riscv` requires in `cmake/sail_required_version.txt`), not the pinned Sail development head; the head was read for source facts only.
2. **Generated prover artifacts:** the Coq, Isabelle, HOL4 and Lem snapshots stored in `sail-arm`, and `opencompl/sail-riscv-lean`, a published Lean 4 translation of the RISC-V model. That translation was generated upstream from a `sail-riscv` revision that is not necessarily the one pinned here, so its sizes characterise the same model family, not the identical revision. Regenerating Lean from the pinned revision with the 0.20.3 binary was attempted and failed (Finding 6).
3. **Slicing and dependency tools:** Sail's interactive slicing commands, the `:filter_reachable_from` command of the interpreter in `alastairreid/asl-interpreter`, and coq-dpdgraph. Only Sail was executed (on a toy specification); the other two were read. At its pinned revision the interpreter repository no longer contains Arm specifications: `CHANGES.md` for 2.0.0 says "ASLi now supports a new language Intel (R) ISA Specification Language using the .isa file suffix. ASL support is deprecated and will be removed soon", and the only specifications in the tree are a 172-line demo ISA and a 529-line standard library. No Arm ASL cone could therefore be measured from that subject.
4. **Statement pinning in Lean:** probes executed on the Lean v4.34.1 toolchain with only `Lean` and `Std` imported (208,072 constants); the comparator repository was read, and one of its test inputs was executed directly under Lean rather than through the comparator. The comparator's README says it was merged into Lean core as `lake comparator` in v4.35.0, one release after the toolchain used here.
5. **Interaction defects:** documentation at pinned revisions of the Rocq and Agda repositories, peer-reviewed papers, and two vulnerability write-ups. None of the historical defects was reproduced.

Measurements ran on a shared 8-vCPU x86-64 virtual machine under load; wall times are indicative only.

## Findings

### 1. How large the endpoint specifications are

Basis: source (counts over the pinned trees) + documentation (published sizes).

| Model | Files | Lines | Non-blank non-comment | Bytes | Top-level items |
| --- | ---: | ---: | ---: | ---: | --- |
| sail-riscv `model/` (all modules) | 183 | 38,169 | 26,614 | 1,565,741 | 1,697 functions, 425 mappings, 216 registers, 423 types, 252 lets; `execute` has 409 clauses over 361 instruction constructors |
| sail-arm `arm-v8.5-a/model` | 12 | 124,375 | 113,324 | 5,583,282 | not itemised |
| sail-arm `arm-v9.3-a/src` | 21 | 384,419 | 359,843 | 15,838,457 | not itemised |
| sail-arm `arm-v9.4-a/src` | 26 | 464,211 | 432,383 | 19,278,614 | about 12,100 functions and 1,392 registers in the 21 build sources |

The RISC-V item counts are those of Sail's documentation bundle (`sail --doc`), so they are the compiler's view. A RISC-V model instance is additionally parameterised by a JSON configuration: the default RV64 configuration instantiated from `config/config.json.in` is 49,267 bytes with 427 leaf settings, and the build generates 16 such files (XLEN 32/64 x ELEN 32/64 x four vector lengths). A pinned statement about "the RISC-V model" is incomplete without the configuration digest.

Published reference points:

| Source | Subject | Size reported |
| --- | --- | --- |
| Reid, FMCAD 2016 | Arm A- and M-class documentation | "over 6,000 pages of documentation, 1,570 instruction encodings, over 50,000 lines of pseudocode, over 4,500 system register fields grouped into 772 system register, and 112 system operations", plus 8,190 added support lines |
| Reid, FMCAD 2016, size table | v8-A ASL | AArch32 24,315; AArch64 10,657; shared 5,489; support 3,200 lines; 586 system registers with 3,951 fields |
| Reid, FMCAD 2016, size table | v8-M ASL | 9,898 lines plus 4,990 support; 186 registers with 622 fields |
| Reid, OOPSLA 2017 | v8-M specification | "over 15,000 lines of code consisting of over 300 instructions and over 250 functions" |
| Armstrong et al., POPL 2019 | Sail ARMv8.3-A (public) | 23,000 lines of specification |
| Armstrong et al., POPL 2019 | Sail ARMv8.3-A (Arm-internal source) | "approximately 30 000 lines of specification with 1279 functions and 501 registers, implementing a total of 390 instructions" (vector instructions excluded) |
| Armstrong et al., POPL 2019 | Sail RISC-V / MIPS / CHERI-MIPS | 5,000 / 2,000 / 4,000 lines |

Derived: between the 2019 paper and the pinned revisions the RISC-V model grew 5.3-fold in comparable lines (5,000 to 26,614) and the Sail Arm model about 19-fold (23,000 to 432,383), mostly by adding system registers, vector extensions and later architecture versions. Any audit plan sized on the 2019 figures is off by an order of magnitude.

Serialized prover forms (bytes of generated files stored upstream):

| Model | Coq | Isabelle | Other |
| --- | ---: | ---: | --- |
| sail-arm v8.5-a snapshots | 14.7 MB (30 files) | 6.6 MB (63 files) | HOL4 6.5 MB; Lem 5.7 MB |
| sail-arm v9.3-a snapshots | 36.3 MB (59 files) | 54.2 MB (75 files) | |
| sail-arm v9.4-a snapshots | 43.4 MB (7 files; `armv9.v` alone 42.4 MB) | 90.4 MB (81 files) | compressed C 18.7 MB |
| RISC-V, published Lean translation | | | Lean 49.8 MB in 161 files; `InstsEnd.lean` alone 45.7 MB |

The RISC-V Lean text is 32 times the Sail source, dominated by the expanded encode/decode and assembly mappings.

### 2. Module-level closure: what the model's own dependency declarations pin

Basis: execution (`sail --project riscv.sail_project <module> --list-files`, Sail 0.20.3).

`model/riscv.sail_project` declares modules with `requires`, `before` and `after` clauses; Sail resolves a module selection to a file list.

| Module selected | Files | Lines | Bytes | Share of model bytes |
| --- | ---: | ---: | ---: | ---: |
| `prelude` | 2 | 294 | 12,656 | 1% |
| `core` | 42 | 6,805 | 290,196 | 18% |
| `sys` (CSRs, traps, physical and virtual memory) | 84 | 15,718 | 659,497 | 42% |
| `I_insts` (base integer instructions) | 87 | 16,564 | 691,242 | 44% |
| `M_insts` (multiply/divide) | 89 | 16,735 | 698,979 | 44% |
| `Zicsr_insts` (CSR instructions) | 86 | 15,845 | 664,608 | 42% |
| `FD_instructions` (floating point) | 93 | 20,177 | 818,432 | 52% |
| `V_instructions` (vector) | 105 | 27,968 | 1,134,277 | 72% |
| `main` | 114 | 23,508 | 975,783 | 62% |
| all modules | 183 | 38,169 | 1,565,741 | 100% |

The base integer instruction module declares `requires exceptions, sys, I_types, Zicfilp_regs, Sdtrig`, and `sys` in turn requires vector core state, state-enable, pointer-masking and debug-trigger modules. At module granularity, therefore, pinning user-mode integer semantics pins 44% of the model, 42 points of which are the privileged layer. Module boundaries follow file organisation, not semantic reachability.

### 3. Definition-level cones in the RISC-V model, three instruments

Basis: execution; each instrument is labelled with what it is.

- **Lower bound (compiler-resolved direct references).** The documentation bundle records, per definition, links to the functions and registers it references (`hyperlinks_from_def` walks the typed AST). Calls made through overloaded names such as `X(rs1)` or `+` were absent from the links of the clauses inspected, so the closure misses everything reached only through an overload; types and constants are not link targets.
- **Compiler-resolved (generated Lean).** In the published Lean translation Sail has resolved every overload and split `execute` into one definition per instruction constructor. A name-reference closure over the generated top-level declarations (own script; string literals and comments removed; a local binder that shadows a global name would add a spurious edge, so values are upper bounds for that snapshot) gives the figures below.
- **Upper bound (lexical over source).** Own script over the Sail sources: an identifier token that names another top-level item is an edge; an overloaded name pulls in every alternative; a scattered function other than `execute` is one node with all its clauses.

| Root | Lower bound: functions / registers / source bytes | Generated Lean: definitions / types / registers / bytes | Lexical upper bound: items / source bytes (share) |
| --- | --- | --- | --- |
| `execute` clause `RTYPE` (register-register ALU) | 5 / 0 / 838 | 53 / 143 / 33 / 56,320 | 209 / 51,191 (3.3%) |
| `execute` clause `LOAD` | 247 / 83 / 176,174 | 379 / 169 / 67 / 236,438 | 2,257 / 1,224,689 (78.2%) |
| `execute` clause `SRET` | 50 / 26 / 44,337 | 98 / 147 / 23 / 98,136 | 784 / 406,765 (26.0%) |
| `execute` clause `CSRReg` | 244 / 126 / 179,573 | 500 / 164 / 96 / 1,993,631 | 2,257 / 1,224,689 (78.2%) |
| `translateAddr` | 192 / 45 / 146,978 | 317 / 165 / 40 / 215,452 | 1,034 / 544,664 (34.8%) |
| `handle_exception` | 92 / 50 / 64,192 | 142 / 149 / 30 / 110,953 | 2,285 / 1,246,268 (79.6%) |
| `execute` (all instruction clauses) | 707 / 203 / 731,023 | 1,438 / 195 / 169 / 2,778,150 | n/a |
| `try_step` (fetch, decode, execute, trap) | 795 / 207 / 793,571 | 1,963 / 201 / 173 / 26,393,996 | 2,365 / 1,310,371 (83.7%) |

Distribution over all 354 `execute_*` definitions in the generated Lean: cone bytes minimum 48,249, lower quartile 54,752, median 83,902, upper quartile 92,358, maximum 1,993,631 (the CSR instructions, whose cone contains the 928 KB `read_CSR` and 850 KB `write_CSR` definitions); functions and abbreviations minimum 23, median 77, maximum 500; registers actually read or written minimum 2, median 38, maximum 102; 23 instruction definitions reach `translateAddr`. As a share of the 49.2 MB of generated declarations every per-instruction cone is below 4.1%, and the union of all of them is 5.65%.

What the three columns teach:

1. **A fixed floor from two universe types.** The smallest instruction (`C_EBREAK`: 2 functions, 21 abbreviations) still carries 142 type declarations and 48 KB. Every instruction returns `ExecutionResult`, whose constructor `ExecuteAs (_ : instruction)` embeds the 19.6 KB syntax-tree type of all instructions and thereby every operand enumeration; monadic instructions additionally mention `SailM`, defined as `PreSailM RegisterType trivialChoiceSource exception`, where `RegisterType : Register → Type` enumerates the value type of all 180 registers. In a shallow embedding these two types are in every cone; no slicer can remove them without changing the result and state representations.
2. **Decode dominates bytes.** Instruction semantics for the whole ISA is 2.8 MB of Lean, while one machine step is 26.4 MB: the difference is the bit-pattern decoder, a single generated definition `encdec_backwards` of 22.8 MB (its companion `encdec_backwards_matches` is another 21.6 MB; together they are 90% of the generated text). A statement about "the effect of instruction I, given as an AST value" pins tens of kilobytes; a statement about "the effect of executing the 32-bit word W" pins the decoder too.
3. **Overload resolution is what makes cones small.** The lexical closure and the compiler-resolved closure differ by a factor of six in definition count for `LOAD` (2,257 items against 379) and by a factor of sixteen for `handle_exception`. Scattered predicate functions (`currentlyEnabled`, `read_CSR`, `write_CSR`, `is_CSR_accessible`) weld the lexical cone together because each is one node referencing every extension.
4. **Privileged state leaks into user-mode cones through memory.** `LOAD` reaches 67 registers and `translateAddr`; `RTYPE` reaches only the 31 integer registers and two others.
5. **Name-reference cones miss dependencies that flow through data.** 54 of the 354 instruction definitions (compressed and alias forms) do not compute anything themselves; they return `ExecuteAs(other instruction)` and the step function re-dispatches (`ExecuteAs(other_inst) => (Some(other_inst), execute(other_inst))` in `model/postlude/step.sail`). Their cones, which are the smallest in the distribution, exclude the semantics they delegate to. A pinned cone for such an instruction must be rooted at the step function or include the delegate explicitly.

### 4. Arm cones (lexical upper bound only)

Basis: execution (own lexical script over the 21 build sources of `arm-v9.4-a`, 19.26 MB, 14,732 items; not Sail's slicer). The ASL-derived sources declare 41 overloads (the RISC-V model declares 59) and use scattered functions for the decode tables (`__DecodeA64` and similar), which the instruction-level roots below do not reach; how far the lexical closure over-approximates was not calibrated.

| Root | Items (functions / registers) | Source bytes | Share |
| --- | --- | ---: | ---: |
| `execute_aarch64_instrs_integer_arithmetic_add_sub_immediate` | 74 (17 / 37) | 11,131 | 0.06% |
| same via its decode function | 75 (18 / 37) | 11,903 | 0.06% |
| `AArch64_TakeException` | 693 (232 / 252) | 211,554 | 1.1% |
| `AArch64_TranslateAddress` | 1,141 (497 / 302) | 464,325 | 2.4% |
| `AArch64_AutoGen_SysRegRead` | 3,300 (1,937 / 660) | 3,346,936 | 17.4% |
| `__TopLevel` (fetch-decode-execute) | 14,588 (12,050 / 1,355) | 19,128,343 | 99.3% |

Derived: an Arm integer instruction's own semantics is a few hundred lines; address translation is about 15,700 lines (POPL 2019 already noted that "the translation table walk function alone consists of over 500 lines of Sail code, not counting various helper functions"); the generated system-register accessor alone is 3.3 MB. A theorem about user-mode arithmetic can be pinned by an individual team; a theorem that mentions a system-register read or a full step cannot be audited line by line and must rely on a shared, vetted model identified by digest.

### 5. What the available slicers follow and omit

Basis: source; Sail additionally by execution on a toy specification.

| Tool | Roots | Edges followed | Granularity and known omissions |
| --- | --- | --- | --- |
| Sail `:slice_roots` + `:slice`, `:slice_cuts`, `:thin_slice` (`src/bin/callgraph_commands.ml`, `src/lib/callgraph.mli`) | identifiers resolved as let-binding, function or type | typed call graph with node kinds `Register`, `Function`, `Mapping`, `Letbind`, `Type`, `Overload`, `Constructor`, `FunctionMeasure`, `LoopMeasures`, `Outcome`; `G.prune roots cuts` then `filter_ast_extra` | function granularity: a scattered function is one node unless `:rewrite split execute` is applied first (then `:rewrite recheck_defs`); standard-library items dropped unless `:slice_keep_std` |
| Interpreter `:filter_reachable_from <group>` (`bin/iii.ml`, `libISA/isa_utils.ml` `reachable_decls`) | identifiers listed in a JSON configuration group, plus foreign exports, plus built-in function prototypes by default | free variables, called functions and type constructors of each declaration (`fvs#vars`, `fvs#funs`, `fvs#tycons`); enumeration constants map to their type | name-based depth-first search over declarations; operator declarations have no name and are never roots |
| coq-dpdgraph `Print DependGraph`, `Print FileDependGraph` (`searchdepend.mlg`) | constants or whole modules | kernel `Constr.t` nodes `Const`, `Ind`, `Construct`, and the inductive of a `Case`; type always, body unless opaque and `DependGraph AccessOpaque` is unset | `add_sort` returns the map unchanged (no sort or universe dependencies); universe instances dropped (`UVars.out_punivs`); `Proj` falls to the generic fold, so a primitive projection adds no edge to its record; for an inductive only its own constructors' types are scanned; node labels are `shortest_qualid_of_global`, which depend on what is imported |
| `leanprover/comparator` `Compare.loop` | constants in the target theorem's type, plus 26 kernel-special constants | type and value of every reached constant (`runForUsedConsts`), constructors and mutual block of inductives, recursor rules | compares full `ConstantInfo` equality between two exported environments; targets contribute their type only |

Executed check (Sail 0.20.3, 20-line toy with two instruction clauses, three helpers and three registers): after `:rewrite split execute`, `:rewrite recheck_defs`, `:slice_roots execute_ADD`, `:slice`, the dumped AST kept register `R1`, `helper_a`, `add_bits_int` and `execute_ADD` and dropped `R2`, `PRIV`, `helper_b`, `unused_c`, the instruction union and the dispatcher (58 lines, 1,837 bytes). Without the `recheck_defs` step the slice aborts with "no type annotation".

The same script could not be run on the full RISC-V model with this binary: `--is` initialises Sail's interpreter, which evaluates top-level bindings and register initialisers and fails with `run_frame got Fail: Runtime type error at unknown location` without `--config` and `run_frame got Fail: No such primop: sys_enable_experimental_extensions` with it, after 2.5-5.5 minutes of type checking. `initial_repl_state` always calls the interpreter's `initial_state`, so models that rely on externally implemented primitives need a plugin or a non-interactive slicing entry point to be sliced by Sail itself.

### 6. Cost of obtaining and elaborating a cone

Basis: execution (Sail 0.20.3 on the pinned RISC-V model) + documentation (build log stored in the published Lean translation).

| Step | Time | Peak memory |
| --- | ---: | ---: |
| type-check all modules, empty SMT cache | 511 s | 1.0 GB |
| type-check all modules, warm 200 KB SMT cache | 82-146 s | 1.0 GB |
| documentation bundle (6.86 MB JSON), warm cache | 82 s | not recorded |
| Lean generation from the pinned model (`--lean`, default RV64 configuration) | 19 min 16 s, then a type error | 1.6 GiB resident when last sampled |
| closure scripts over the bundle or over 49.8 MB of Lean | 1-6 s | not recorded |
| Lean 4.29 build of the published translation: sum of 132 per-module times | 300 s | not recorded |
| slowest Lean modules in that log | `InstsEnd` 86 s, `PlatformConfig` 33 s, `ZicsrInsts` 31 s, `Defs` 20 s | |

The Lean generation run ended with

```text
Type error:
extensions/Sdtrig/sdtrig_regs.sail:30.40-62:
30 |register written_trigger_index : option((trigger_index, tdata)) = None()
   | Unsupported register type (range(0, (16 - 1)), tdata)
```

so with the release binary that the model itself requires, the pinned revision's debug-trigger state is outside what the Lean back end translates; the published translation predates or avoids that register.

Neither the model type-check nor the Lean elaboration is interactive. A cone-pruned Lean file for one instruction (about 80 KB) was not built; whether it elaborates in seconds is plausible but unmeasured.

### 7. Statement cones in Lean: three definitions of "what must be pinned"

Basis: execution (Lean v4.34.1; own 90-line metaprogram mirroring the comparator's traversal; 5 s wall including import of `Lean` and `Std`).

For a theorem T, three closures over the environment were computed: (a) constants reachable from T's type, following definition bodies but only the types of theorems met on the way; (b) the comparator's walk, which also follows the proof terms of theorems met on the way; (c) statement plus T's own proof, the set `#print axioms` traverses.

| Theorem | Constants written in the statement | (a) meaning cone | (b) comparator-style cone | (c) statement + proof |
| --- | ---: | ---: | ---: | ---: |
| `Nat.add_comm` | 5 | 26 | 26 | 47 |
| `List.append_assoc` | 5 | 26 | 26 | 42 |
| `Array.size_push` | 10 | 51 | 51 | 68 |
| `Nat.gcd_comm` | 3 | 136 | 238 | 480 |
| `BitVec.add_comm` | 6 | 146 | 252 | 271 |
| `Int.emod_emod_of_dvd` | 7 | 150 | 212 | 707 |
| `String.append_assoc` | 5 | 232 | 378 | 633 |
| `Std.HashMap.getElem?_insert` | 18 | 677 | 2,374 | 3,332 |
| `Std.HashMap.size_insert_le` | 15 | 612 | 2,352 | 3,306 |

Observations. A statement that names three constants (`Nat.gcd_comm`: equality, `Nat`, `Nat.gcd`) pins 136 because `Nat.gcd` is defined by well-founded recursion. Walking proof terms of auxiliary theorems (the comparator's choice, which makes plain structural equality of exported constants sufficient) leaves the three smallest cones unchanged and multiplies the others by 1.4 to 3.8; for the hash-map statements 1,053 of the 2,374 constants are theorems whose proofs are compared although only their statements affect meaning. Measured in distinct expression objects, cone (b) for `Std.HashMap.getElem?_insert` is 309,816 objects against 35,733 for cone (a). Meaning cones (a) are 18%-75% of the full proof cone (c) here, so "pin the statement, not the proof" saves less than an order of magnitude in library-heavy statements.

The comparator's contract (README): given a trusted `Challenge` module and an untrusted `Solution`, success guarantees that the listed theorems "Prove the same statement as provided in `Challenge`", "Use no more axioms than listed in `permitted_axioms`", and are "accepted by the Lean kernel". Its stated internals are the pinning recipe: build both modules in a sandbox, export them with `lean4export`, "Verify that all declarations used in the statement of all relevant theorems in `Challenge` are the same as in the `Solution` environment. This always includes the declarations from `Init` with special meaning to the kernel", check axioms over the solution's bodies, then replay the solution environment into the kernel.

### 8. How unpinned preludes, notation and serialized files defeat naive comparison

Basis: execution for the first two rows (Lean v4.34.1); source for the comparator test inputs and their expected verdicts (`tests/projects/*/test.json`).

| Hazard | Concrete instance | What a text-level or name-level comparator misses | Evidence |
| --- | --- | --- | --- |
| Instance or notation alias | `scoped instance (priority := high) spoofAdd : Add Nat := ⟨fun _ _ => 5⟩` then `theorem two_plus_two : 2 + 2 = 5 := rfl`; `local notation "ℕ" => Bool` | `#check` prints `Spoof.two_plus_two : 2 + 2 = 5` and `∀ (n : ℕ), n = true ∨ n = false`; `#print axioms` reports no axioms. The constant lists differ: `instAddNat` in the honest statement, `Spoof.spoofAdd` in the spoofed one; `Bool` instead of `Nat` | executed |
| Unpinned prelude with kernel-accelerated constants | module starting with `prelude`, importing only `Init.Prelude` and `Init.Core`, defining `def Nat.gcd (_ _ : Nat) : Nat := 0`, proving `Nat.gcd a b = 0` by unfolding and `Nat.gcd 1 1 = 1` by `rfl`, hence `theorem boom : False` | Lean 4.34.1 exits 0 and prints "'boom' does not depend on any axioms". The kernel evaluates `Nat.gcd` on literals natively by name; the comparator source says "The challenge needs to have all the built-in constants of the kernel, as the kernel makes no guarantees when fed other definitions here" | executed (test `primitive_issue`, expected comparator exit 1) |
| Kernel-special type with a forged shape | custom prelude declaring `Char` with a field of type `False` and `Char.ofNat` returning another type; string-literal reduction then produces an ill-typed value | same class as above for `Char.ofNat`, `String.ofList` | test `char_ofnat_issue`, expected exit 1 |
| Raw projection naming a structure by string | statement uses `Expr.proj` with structure name `S` and index 0; the solution redefines `S` with an extra field `h : False` | a walk over constants in the statement never visits `S`, since a projection node is not a constant reference | test `proj_trick`, expected exit 1 |
| Quotient primitives re-declared | `prelude` module declaring `theorem Quot.lift : True` | the kernel's quotient initialisation and the declared constant disagree | test `quot_mismatch`, expected exit 1 |
| Serialized object files | a natural-number literal whose in-memory value was forged with `unsafeCast` and stored in an `.olean`; `decide` then proves contradictory bounds | README: "We generally adopt a policy of not loading olean files as they just get mmaped into our address space and then dereferenced and are as such a potential point of attack" | test `olean_issue`, expected exit 1 |
| Opaque values and axioms | `opaque v : False := f` with `axiom f : False` | an axiom audit that does not follow opaque bodies | test `opaque_value`, expected exit 1 |
| Definition holes | challenge `def X : Prop := sorry` with `theorem t : RH ↔ X`; solver sets `X := RH` | README: "all definition hole solutions **must** always be checked with an additional (potentially human) verifier" | documentation |

Derived rule: the pinned object must be a digest over the exported constants of the statement cone (types and bodies, universe parameters, inductive and recursor data), plus the fixed list of kernel-special constants, plus the checker and toolchain identity. Pretty-printed text, constant names, and object files produced by the untrusted party are not admissible inputs.

Rocq shows the same three classes in its own record (`dev/doc/critical-bugs.md` at the pinned revision): "deserialization of .vo data not properly checked" (versions 8.10-8.18.1, "can lead to segfaults or arbitrary code execution on crafted .vo files"); "rocqchk trusts the serialized VM bytecode segment" (8.20-9.3, a spliced `.vo` let `rocqchk -bytecode-compiler yes` accept a proof of False "with no axioms reported"); and a dependency-audit omission, "roqchk --output-context did not report axioms used through inductives sealed in a module" (8.12-9.4), where the axiom was reachable only through a let-binding inside a constructor type.

### 9. Rules that are consistent alone and inconsistent together: proof assistants

Basis: documentation at pinned revisions; papers as cited.

| System | Feature A | Feature B | Outcome and resolution | Source |
| --- | --- | --- | --- | --- |
| Rocq | structural guard condition (commutative cuts through equality proofs) | propositional extensionality axiom | "guard condition was unknown to be inconsistent with propositional extensionality in library Sets ... not a bug per se but an incompatibility discovered late"; guard constrained in 2014; a variant remained until 9.0.1; a further guard-checker entry "breaks propositional extensionality", fixed in 9.2.1, 9.3.1 and 9.4 | `critical-bugs.md` |
| Rocq | module subtyping of nested inductives | `propext` | "not a full proof of False, but dangerous when using propext"; fixed 9.3.1 | `critical-bugs.md` |
| Rocq | impredicative `Set` | axiom of description and decidable equality on reals in the standard library | inconsistent in 7.3.1 and 7.4; "fixed by deciding to drop impredicativity of Set" | `critical-bugs.md` |
| Rocq | elimination of large singletons to `Set` | axiom of choice with excluded middle | "not a bug but a change of intended model"; singleton elimination constrained in 2007 | `critical-bugs.md` |
| Rocq | primitive float or integer operations | their axiomatised specifications | three entries where the axiom and the implementation disagreed (`PrimFloat.leb`, `SFclassify`, `PrimInt.asr`): "proof of false when using the incorrect axiom" | `critical-bugs.md` |
| Agda | `--cubical=compatible` | `--with-K` | "the univalence axiom is provable using cubical constructions, which falsifies the K axiom" | `safe-agda.lagda.rst` |
| Agda | `--injective-type-constructors` | excluded middle | "leads to an inconsistency via Chung-Kil Hur's construction" | same |
| Agda | `--large-indices` | `--without-K` or `--forced-argument-recursion` | "both of these combinations are known to be inconsistent" | same |
| Agda | `--without-K` | `--flat-split`; `primEraseEquality` | listed as incompatible with `--safe`; "using `primEraseEquality`, one can derive the K axiom" | same |
| Isabelle/HOL | overloaded constant definitions | type definitions depending on an undefined overloaded constant | `consts c : α`, `typedef τ = {True, c_bool}`, `defs c_bool = ¬(∀x y : τ. x = y)` proved `False`; "works in versions of Isabelle prior to Isabelle2016"; fixed by an acyclic dependency relation through constants and types | Kuncar and Popescu |

The Rocq list contains 101 entries in total: 5 unfixed, and among the fixed ones 21 on the guard condition, 25 on conversion machines, 14 on universes, 10 each on typing constructions and the module system, 6 on conflicts with library axioms, 2 on forgotten axioms or flags, and 3 on deserialization. Eight titles name an axiom or `propext` explicitly. Agda's `--safe` is "coinfective": a safe module may import only safe modules, which is the mechanical form of "check the combination, not the parts".

Common shape. Each feature has a model: sets for K and uniqueness of identity proofs, simplicial sets or cubical sets for univalence, a classical proof-irrelevant model for excluded middle, an impredicative model for `Set`. The combination has none. Per-feature soundness arguments and per-feature tests cannot expose this; only a single model interpreting all enabled rules, or an explicit incompatibility table enforced by the tool, can.

### 10. The same pattern in instruction-set specifications

Basis: source (pinned RISC-V model) + documentation (papers and advisories).

| Case | Individually valid parts | Failure when combined | How it is handled or was found |
| --- | --- | --- | --- |
| RISC-V `misa` writes (`model/core/sys_regs.sail`, `legalize_misa`) | each extension bit is independently writable | D without F, V without F and D, S without U, H without S and U; clearing C while the next PC is 2-byte aligned | the legaliser computes each field from the others and suppresses the whole write in the misalignment case (source lines quoted below the table) |
| RISC-V configuration (`model/postlude/validate_config.sail`) | each extension's own parameters | 193 diagnostic messages for cross-extension requirements, such as "Zve*f is enabled but F is disabled", "Sv57 is enabled but Sv48 is disabled", "mutable F requires mutable D and V when they are supported" | a 1,372-line hand-written validator, asserted by the model's initialisation (`assert(config_is_valid(), ...)`); it is itself unverified specification text |
| Arm v8-A against the Architecture Validation Suite (FMCAD 2016) | 100% pass for integer, floating-point, SIMD and exception tests | residual failures in "interprocessing (switching between 32-bit and 64-bit modes) and prioritization of multiple exceptions within the same instruction"; memory 99%, interprocessing 98% | testing against over 11,000 programs and 2.5 billion instructions; correcting errors had changed "approximately 12% of the lines of code" |
| Arm v8-M (OOPSLA 2017) | a specification already "extensively tested" | "twelve bugs in the formal part of the specification and 9 issues in the natural language part", including debug logic "ignoring a debug disable control signal" and system-register status fields not masked by their control field; two were security bugs | cross-cutting "if X then Y" properties checked by an SMT translation, not per-instruction tests; the paper attributes the difficulty to "the combination of four different privilege/security modes, priority, derived exceptions, debug, lockup and security" |
| x86-64 `SYSRET` (CVE-2012-0217) | AMD's pseudocode for `SYSRET`; Intel's pseudocode; the canonical-address rule | "If an operating system is written according to AMD's spec, but run on Intel hardware, the difference in implementation can be exploited": with a non-canonical return address AMD processors "throw the #GP in guest mode" whereas in the Intel pseudocode the check "happens before the privilege level is changed" | found in the field; the write-up lists Xen, NetBSD, FreeBSD and some versions of Windows as affected |
| x86 `MOV SS`/`POP SS` with debug exceptions (CVE-2018-8897) | interrupt shadow after a stack-segment load; data breakpoints; `SYSCALL`/`INT 3` transfer | "a debug exception is delivered after the transfer to CPL < 3 is complete"; "Such deferred #DB exceptions by MOV SS and POP SS may result in unexpected behavior" in operating systems and hypervisors | CERT/CC attributes it to "developer interpretation of existing documentation" |

The `legalize_misa` lines referred to in the first row:

```text
let D = if hartSupports(Ext_D) & F == 0b1 then { if config extensions.D.mutable_misa then v[D] else m[D] } else 0b0;
// Suppress updates to MISA if by disabling C next PC would become misaligned or an extension vetoes
if   (C == 0b0 & m[C] == 0b1 & (nextPC[1] == 0b1 | ext_veto_disable_C()))
then m
```

Derived: for ISAs the analogue of "one model for all rules" is one executable specification with every configured extension enabled, exercised by cross-cutting properties. Per-extension models that are pinned and audited separately leave the interaction rules (legalisers, validators, exception prioritisation) outside every individual cone; in the RISC-V model those rules are 1,372 lines in the validator alone.

### 11. Cost, comprehensibility and validation matrix

Basis: derived from Findings 1-10 unless a cell cites documentation.

| Axis | ISA endpoint specification | Lean or Rocq statement cone |
| --- | --- | --- |
| Authoring effort | Arm: vendor-authored ASL, 8,190 support lines added to make it executable and about 12% of lines changed during clean-up (documentation). RISC-V: hand-written, 26,614 lines at the pin against 5,000 in 2019 | challenge/solution pair plus a JSON configuration; the cone is computed, not written |
| Tool build | Sail binary release used; not built | Lean toolchain used as shipped |
| Elaboration latency | 82-511 s to type-check RISC-V; 300 s of Lean module time for the generated model; nothing below the 50 ms interactive threshold | 5 s to compute nine cones over 208,072 constants |
| Generated-code execution | not measured (emulator speed is outside this report) | n/a |
| Check speed | n/a | comparator replays the whole solution environment; not timed here |
| Memory and size | 1.0 GB to type-check 1.57 MB of Sail; 6.9 MB documentation bundle; 43-90 MB prover snapshots for Arm; 49.8 MB Lean for RISC-V | 26 to 2,374 constants per statement; up to 309,816 expression objects |

Human comprehensibility. A reviewer can read an 80 KB instruction cone; nobody reads 26 MB of decoder or a 3.3 MB system-register accessor. The mental model that works is two-level: a per-team audit of the theorem statement and its small cone of project definitions, and a shared digest for the vendor-derived ISA model, whose trust comes from its test evidence (validation suites, operating-system boots) rather than from reading. The dangerous mistakes are local-looking: a statement whose printed form is right while an instance, notation or prelude changed its meaning (Finding 8); a module closure that silently includes the privileged layer (Finding 2); a configuration file that is part of the specification but not of the digest (Finding 1). Diagnostics are weak throughout: the comparator reports a mismatching constant name, not why it differs; Sail's slicer failed on the full model with an interpreter error unrelated to slicing.

Conceptual economy. One invariant, "the checked statement is the intended statement", is enforced today by several partial mechanisms: axiom listing, environment replay, statement comparison, sandboxed builds, refusal to load object files. They collapse to one rule: admission takes an out-of-band digest of the exported statement cone and of the kernel-special constants, and everything else is derived from it. For ISAs the equivalent single rule is "one model, all extensions, one configuration digest", with pruning as a derived view rather than a separate artifact. The complexity that this moves, and does not remove, is the export format and the canonical serialization used for the digest.

Validation practice observed. Specification adequacy: the Arm specifications were validated against vendor test suites and then by cross-cutting SMT properties; the Sail models by booting Linux, FreeBSD and seL4 (documentation). Statement adequacy: the comparator's 20 regression projects are an adversarial test suite for the pinning mechanism itself, of which the `primitive_issue` input was reproduced here. Checker and loader robustness: Rocq's three deserialization entries and its two unfixed virtual-machine memory-safety entries show that the reducer and the file loader are attack surface, not only the typing rules.

## Boundaries

- **Not examined: Sail's own slicer on the full RISC-V or Arm models.** The interactive entry point failed during interpreter initialisation (Finding 5). All RISC-V cone sizes come from the three substitute instruments of Finding 3, none of which is the Sail call graph; the generated-Lean figures are for a published snapshot whose source revision may differ from the pinned model.
- **Unsupported: Lean output for the pinned RISC-V revision with Sail 0.20.3.** The back end rejected a register of type `option((trigger_index, tdata))` after 19 minutes (Finding 6), so no generated-Lean cone exists for the exact pinned revision.
- **Not examined: type-checking or slicing `sail-arm` with Sail.** Arm cones are lexical upper bounds; no compiler-resolved figure exists here. The v9.4-a README says it was last tested with Sail 0.17.1.
- **Known not to apply: Arm ASL cones from the pinned interpreter repository.** That revision contains no Arm architecture specification, and ASL support is marked deprecated. System-register and decode-tree sizes for ASL are quoted from the FMCAD 2016 paper only.
- **Not examined: coq-dpdgraph execution.** No Rocq toolchain was available. The statements about sorts, universe instances, opaque bodies and primitive projections are read from `searchdepend.mlg`; whether the missing projection edge ever changes a computed cone in practice (the record type is usually referenced elsewhere in the term) is unknown.
- **Not examined: the comparator binary, `lean4export`, `lake comparator`.** The toolchain used predates the merged command; expected verdicts are taken from the repository's test metadata. Only `primitive_issue/Solution.lean` was run, directly under Lean.
- **Not examined: serialized byte sizes of Lean statement cones.** Cones are reported in constants and distinct expression objects, not export bytes.
- **Not examined: reproduction of any historical inconsistency or ISA defect.** Finding 9 and 10 rows are documentation. Lean 4 has no entry in Finding 9; no equivalent public critical-bug list for Lean was located, which is an absence of evidence only.
- **Unknown: how much of a per-instruction cone is semantically necessary.** Name-reference closures include definitions reachable only on paths excluded by configuration (for example hypervisor branches when the extension is disabled); partial evaluation against a fixed configuration was not attempted.
- **Not examined: concurrency and physical-level validation.** Relaxed-memory behaviour, power-loss, side-channel leakage and post-silicon conformance are outside the sequential specifications measured; the POPL 2019 paper's litmus-test validation of the RISC-V model is not reassessed. No human-subject evidence on specification reading was found or produced.
- **Stronger conclusions the evidence does not support.** (1) "Pruning makes an ISA model auditable": it makes instruction semantics auditable; decode, address translation and system registers stay megabytes. (2) "Statement pinning removes the specification from the trusted base": it names the specification; it does not validate it. (3) "A feature-interaction table suffices": the documented tables were assembled after inconsistencies were found.

## Evidence

Sources (paths relative to the revisions in `REPORT.json`):

- riscv/sail-riscv `ec5200bdfe0c10afa6dbb1f7b0980db2d236236e`: `model/riscv.sail_project`; `model/core/sys_regs.sail` (`legalize_misa`, lines 133-157); `model/postlude/validate_config.sail`; `model/CMakeLists.txt`; `config/CMakeLists.txt`, `config/config.json.in`; `cmake/sail_required_version.txt` (`0.20.3`).
- rems-project/sail-arm `5416ef6b43e9527c38dc71fb752259c1d01a47e1`: `arm-v8.5-a/model`, `arm-v9.3-a/src`, `arm-v9.4-a/src`, `arm-v9.4-a/Makefile` (`SAIL_SRCS`), `arm-v9.4-a/README.md`, `*/snapshots/`.
- rems-project/sail `97aa617dcd4d01575f773cb58ea1e8686858c8c2`: `src/bin/callgraph_commands.ml`, `src/lib/callgraph.mli`, `src/bin/repl.enabled.ml` (`initial_repl_state`, `:ast`, `:rewrite`), `src/bin/sail.ml` (`-is`), `src/sail_doc_backend/docinfo.ml` (`hyperlinks_from_def`), `src/lib/interpreter.ml`. Executable: release tag `0.20.3-binary`, commit `60695b1ea377048f0adc39c62671cd099b2ed9f6`, which reports `Sail 0.20.3` and bundles Z3 4.13.0.
- alastairreid/asl-interpreter `16260979137c38339743a04b7fd5d9f0fa8a6ee5`: `README.md`, `CHANGES.md`, `bin/iii.ml` (`:filter_reachable_from`), `libISA/isa_utils.ml` (`reachable_decls`), `demo/demo.isa`, `stdlib.isa`.
- coq-community/coq-dpdgraph `0fe97174151f119f96a0d434f2d1c864ccbc461f`: `searchdepend.mlg` (`collect_long_names`, `collect_dependance`), `graphdepend.mlg`, `README.md`.
- opencompl/sail-riscv-lean `51c635c460125ac87955d061fcd902ce03b8011f`: `LeanRV64D/*.lean`, `build_log.txt`, `lean-toolchain` (`v4.29.0`).
- leanprover/comparator `865edc14486c3388e9225daa971da8e157488c3e`: `README.md`, `Main.lean` (`primitiveTargets`, `runBuiltinKernel`), `Comparator/Compare.lean`, `Comparator/Util.lean` (`runForUsedConsts`), `Comparator/Axioms.lean`, `tests/projects/*/{Challenge,Solution}.lean` and `test.json`.
- leanprover/lean4 `5045d0056413266e57c625dcd7c365b10e377c52` (v4.34.1 release toolchain, `lean --version` confirms the commit).
- rocq-prover/rocq `25f5b18a320e4796f181f938d3b74bebe7db4dc4`: `dev/doc/critical-bugs.md`. agda/agda `11f7300c8303608196e620714100a056e8c1ed0f`: `doc/user-manual/language/safe-agda.lagda.rst`.
- Papers read in author or publisher copies: FMCAD 2016 (size tables, validation-suite pass rates), POPL 2019 (model size table, address-translation remark), OOPSLA 2017 (bug counts and classes), Journal of Automated Reasoning 2019 (Example 2). Advisories: CERT/CC VU#631579; Xen Project write-up of CVE-2012-0217.

Lean statement-cone traversal (core of the metaprogram; `stats` counted kinds and `Expr.numObjs`):

```lean
def nextConsts (env : Environment) (n : Name) (thmValues : Bool) : Array Name := Id.run do
  let some info := env.find? n | return #[]
  let mut out := info.type.getUsedConstants
  let followValue := match info with
    | .thmInfo _ => thmValues
    | _ => true
  if followValue then
    if let some v := info.value? (allowOpaque := true) then
      out := out ++ v.getUsedConstants
  match info with
  | .inductInfo i => out := out ++ i.ctors.toArray ++ i.all.toArray
  | .ctorInfo c => out := out.push c.induct
  | .recInfo r =>
    for rule in r.rules do
      out := (out.push rule.ctor) ++ rule.rhs.getUsedConstants
  | _ => pure ()
  return out
```

Cone (a) is the closure of `info.type.getUsedConstants` under `nextConsts env · false`; cone (b) under `nextConsts env · true`; cone (c) is the closure of the theorem itself under `nextConsts env · true`. Sample output line: `Nat.gcd_comm: direct statement constants=3 ... statement cone, theorem types only: consts=136 (def=75 thm=11 ind=20 ctor=23 rec=7 ...) exprObjs=4052 ... comparator-style walk: consts=238 ... statement + proof cone: consts=480`.

Lean spoofing probe (complete; outputs quoted in Finding 8):

```lean
import Lean
theorem honest : 2 + 2 = 4 := rfl
namespace Spoof
scoped instance (priority := high) spoofAdd : Add Nat := ⟨fun _ _ => 5⟩
theorem two_plus_two : 2 + 2 = 5 := rfl
end Spoof
local notation "ℕ" => Bool
theorem all_nat_small : ∀ n : ℕ, n = true ∨ n = false := by intro n; cases n <;> simp
#check @Spoof.two_plus_two
#check @all_nat_small
#print axioms Spoof.two_plus_two
open Lean in
run_cmd do
  let env ← getEnv
  for n in [``honest, ``Spoof.two_plus_two, ``all_nat_small] do
    let some ci := env.find? n | throwError "missing {n}"
    logInfo m!"{n} statement constants: {ci.type.getUsedConstants}"
```

```text
Spoof.two_plus_two : 2 + 2 = 5
all_nat_small : ∀ (n : ℕ), n = true ∨ n = false
'Spoof.two_plus_two' does not depend on any axioms
honest statement constants: [Eq, Nat, HAdd.hAdd, instHAdd, instAddNat, OfNat.ofNat, instOfNatNat]
Spoof.two_plus_two statement constants: [Eq, Nat, HAdd.hAdd, instHAdd, Spoof.spoofAdd, OfNat.ofNat, instOfNatNat]
all_nat_small statement constants: [Bool, Or, Eq, Bool.true, Bool.false]
```

Prelude probe: the file `tests/projects/primitive_issue/Solution.lean` from the comparator repository with the line `#print axioms boom` appended, run as `lean PrimitiveIssue.lean`; output `'boom' does not depend on any axioms`, exit status 0.

Sail slicing toy and script:

```text
default Order dec
$include <prelude.sail>
register R1 : bits(32)
register R2 : bits(32)
register PRIV : bits(2)
val helper_a : bits(32) -> bits(32)
function helper_a(x) = x + 1
val helper_b : bits(32) -> bits(32)
function helper_b(x) = { if PRIV == 0b11 then x + 2 else x }
val unused_c : bits(32) -> bits(32)
function unused_c(x) = x + 3
scattered union ast
val execute : ast -> unit
scattered function execute
union clause ast = ADD : bits(32)
function clause execute(ADD(x)) = { R1 = helper_a(x) }
union clause ast = SYS : bits(32)
function clause execute(SYS(x)) = { R2 = helper_b(x) }
end execute
end ast
```

```text
:rewrite split execute
:rewrite recheck_defs
:slice_roots execute_ADD
:slice
:ast /tmp/tiny_slice.sail
:quit
```

run as `sail --is tiny.cmd tiny.sail`. On the RISC-V model the corresponding command was `sail --strict-var --strict-bitvector --strict-exponentials --require-version 0.20.3 [--config rv64d_v256_e64.json] --project riscv.sail_project --all-modules --is script`, with the errors quoted in Finding 5.

Other commands:

```text
sail --project riscv.sail_project I_insts --list-files
sail --strict-var --strict-bitvector --strict-exponentials --require-version 0.20.3 --memo-z3-path cache --project riscv.sail_project --all-modules --just-check
sail ... --doc --doc-format identity --doc-compact --doc-embed plain --doc-embed-with-location -o out --doc-bundle riscv_doc.json --all-modules riscv.sail_project
sail ... --config rv64d_v256_e64.json --lean --lean-output-dir out --lean-force-output --lean-noncomputable --lean-import-file ../handwritten_support/RiscvExtras.lean -o Lean_RV64D --all-modules riscv.sail_project
```

The last command also carried the `--lean-non-beq-type` and `--lean-noncomputable-function` options listed in `model/CMakeLists.txt`; `rv64d_v256_e64.json` is `config/config.json.in` with its placeholders substituted as `config/CMakeLists.txt` does for XLEN 64, ELEN 64, VLEN 256.

Closure scripts (own, each under 110 lines of Python, not preserved in this package): (1) over the documentation bundle, nodes are functions, mappings and registers, edges are the bundle's `links`, and `execute` clauses are separated by matching each link's file offset to the clause's source span; (2) over generated Lean, nodes are top-level `def`/`abbrev`/`inductive`/`structure`/`instance`/`opaque` declarations, constructors and fields map to their type, constructors of `inductive Register` are register nodes referenced only from `def` bodies; (3) over Sail source, top-level items are split at keywords in column 0 and the `execute` clauses are named `execute_<Constructor>`. Two defects found and fixed while building these scripts are worth knowing when reproducing: in (2), tokens inside string literals (`"loop dummy assert"` matched the global definition `loop`) created false edges that inflated every memory-touching cone to 26 MB; in (3), the clause header's own function name linked every instruction clause to the dispatcher.

Sample outputs:

```text
modules=[I_insts] files=87 lines=16564 bytes=691242
bundle: functions=1697 mappings=425 registers=216 lets=252 vals=2308 types=423
cone(execute_RTYPE): bytes=56320 (0.11% of declarations) defs=53 types=143 registers=33
cone(execute_LOAD): bytes=236438 (0.48% of declarations) defs=379 types=169 registers=67
cone(try_step): bytes=26393996 (53.65% of declarations) defs=1963 types=201 registers=173
per-instruction cones over 354 execute_* definitions: bytes: min=48249 p25=54752 median=83902 p75=92358 max=1993631
cone(AArch64_TranslateAddress): nodes=1141 bytes=464325 (2.4% of source) lines=15697
```

All evidence was acquired on the observation date in `REPORT.json`. Counts are source facts; "share", "floor" and growth factors are this report's arithmetic.

## Revalidation

- **Model size and module closure (Findings 1, 2):** `sail --project model/riscv.sail_project --all-modules --list-files | xargs cat | wc -lc`, then the same with `I_insts` and `sys`. If the base-instruction module no longer requires `sys`, Finding 2 changes.
- **Per-instruction cones (Finding 3):** regenerate Lean with the model's `generated_lean_*` build target (or take the current published translation) and rerun a name-reference closure from `execute_RTYPE`, `execute_LOAD` and `try_step`; compare definition counts with 53, 379 and 1,963. A change in the type count of the small cones (142-143) signals a change in how the result and machine-state types are represented.
- **Slicer availability (Finding 5):** run the six-line script on the toy; then on the full model. If the full-model run gets past interpreter initialisation, replace the substitute instruments with Sail's own `:slice` output and re-measure.
- **Interpreter repository content (Applicability):** `find . -name '*.asl' -o -name '*.isa' | xargs wc -l` at the revision of interest; reappearance of Arm specifications would make an ASL cone measurable with `:filter_reachable_from`.
- **dpdgraph semantics (Finding 5):** read `collect_long_names` in `searchdepend.mlg` for a `Proj` case and for `add_sort`; with a Rocq toolchain, compare `Print DependGraph` on a lemma using a primitive projection with `Unset DependGraph AccessOpaque` and without.
- **Statement cones and spoofing (Findings 7, 8):** rerun the two Lean files. The discriminating outputs are the constant lists (`Spoof.spoofAdd` against `instAddNat`) and whether `PrimitiveIssue.lean` still exits 0 with "does not depend on any axioms"; if a later toolchain rejects it, the kernel has started checking its special constants and the corresponding comparator test becomes redundant. With Lean 4.35 or later, run `lake comparator` on the repository's `primitive_issue` and `proj_trick` projects and confirm exit status 1.
- **Interaction catalogues (Findings 9, 10):** `grep -c '^#### ' dev/doc/critical-bugs.md` and the section headings in the Rocq tree; the bullet list of `safe-agda.lagda.rst`; `wc -l model/postlude/validate_config.sail` and `grep -c print_endline` on it; `grep -n 'Suppress updates to MISA' model/core/sys_regs.sail`.
- **Not cheaply revalidated:** Arm cones with a real slicer (requires type-checking a 19 MB model) and export-byte sizes of Lean statement cones (requires building `lean4export`).
