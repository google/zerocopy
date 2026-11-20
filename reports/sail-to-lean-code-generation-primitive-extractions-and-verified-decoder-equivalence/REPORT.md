# Sail-to-Lean Code Generation, Primitive Extractions, and Verified Decoder Equivalence

## Summary

Extracting authoritative Sail instruction-set specifications (`riscv/sail-riscv`) into Lean 4 (`rems-project/sail`, `rems-project/lean-sail`, `opencompl/sail-riscv-lean`) yields a mechanized ISA semantics, yet creates four foundational obligations across monadic state translation, external primitive bindings, hardware nondeterminism refinement, and binary instruction decoding:

1. **Dual Monadic Lowering (`ConcurrencyInterfaceV1` vs. `ArchSem`)**: Sail's Lean backend (`sail_plugin_lean.ml`, `pretty_print_lean.ml`) lowers Sail functions into five body shapes (`<expr>`, `Id.run do`, `ExceptM.run do`, `do`, `SailME.run do`) selected by `(is_monadic, early_return, has_loop)`. By default (`interface_v = 1`), `PreSailM` is `EStateM (Sail.Error ue) (SequentialState RegisterType c)` where registers live in a partial `Std.ExtDHashMap Register RegisterType` (`readReg` throws `.Unreachable` when a key is absent, requiring register-presence hypotheses in downstream proofs). When preprocessor symbol `CONCURRENCY_INTERFACE_V2` is defined (`interface_v = 2`), `PreSailM` switches to a Kiselyov-Ishii freer monad `FreeM ((Except (Sail.Error ue) InstructionEffect) ⊕ FinChoice)` reifying 15 architectural effects (`regRead`..`printMessage`) and finite nondeterminism `FinChoice`.
2. **Primitive Extraction Hazards Under Zero-Trust Kernel Checkers**: External Sail `extern` primitives in `riscv/sail-riscv` expose a sharp soundness/auditability tradeoff:
   - **Uninterpreted `axiom`s** (`LeanRV64D/RiscvExtras.lean` declares **75 `axiom`s**: 8 platform/reservation hooks plus 67 SoftFloat operations) populate `ConstInfo.axiomInfo`, causing zero-trust replay checkers (`lean4lean`, `nanoda_lib`, or `#print axioms` gates enforcing `{propext, Classical.choice, Quot.sound}`) to reject every theorem transitively referencing `LeanRV64D.Functions.execute`.
   - **Transparent `panic` and `FakeReal` stubs** (`RiscvExtrasExecutable.lean` and default `FakeReal.lean`) are *transparent definitions* in Lean's kernel: `panic` unfolds to `Inhabited.default`, proving false identities like `riscv_f64Add rm x y = (0#5, 0#64)` and `match_reservation pa = false` **by `rfl`**, while `FakeReal.lean` defines `round_down x := x.toUInt64.toNat` and `round_up x := round_down (x + 0.5)`, where `round_down (-1.5) = 0 ≠ -2` and `round_up 1.2 = 1 ≠ 2`.
   - **`opaque` declarations** (`ConstInfo.opaqueInfo`) satisfy codomain inhabitation constructively with zero custom axioms and block unsound `rfl` unfolding for genuinely pure primitives, **but fail on pure-typed stateful externs**: because `sail-riscv` types `match_reservation : Arch.pa → Bool` and `valid_reservation : Unit → Bool` outside `SailM`, both `axiom` and `opaque` freeze them into state-invariant constants (`valid_reservation () = valid_reservation ()` by `rfl` across `cancel_reservation ()`), requiring monadic lifting into `SequentialState` or `InstructionEffect`.
   - **Bitvector pattern elaboration (`--lean-matchbv`)** invokes `elabMatchBv`, which closes omitted fallback arms via `by try bv_decide -enums`, silently introducing `Lean.ofReduceBool` compiler-trusted reflection unless explicit wildcard arms are emitted.
3. **Deterministic Sail to Nondeterministic Hardware Refinement**: Sequential `LeanRV64D` (`V1`) resolves `choose` deterministically via `trivialChoiceSource`, maintains a software `tlb` register, walks page tables deterministically in flat `mem`, and lowers `.cacheOp`/`.tlbOp`/`.barrier` to `pure ()`. Bridging to hardware requires effect-trace simulation over `ArchSem`'s `FreeM` trees for system/MMU execution, paired with two-step monadic-to-pure `BitVec` purification (`opencompl/riscv-lean` `SailToRV64` + `SailPureToInstructions`, discharging loop `sail_assert` invariants via `IntRange.forIn'_loop_eq_pure`) for pure user-level ALU/bitmanip opcodes.
4. **Right-Spined `encdec` Blowup and Bit-Exact Decoder Equivalence**: Without `--lean-matchbv`, Sail compiles `scattered mapping encdec` into a ~778-deep right-nested monadic cascade in `LeanRV64D/InstsEnd.lean` (`72,377` lines, `43.75 MiB`, where `encdec_backwards` spans `27,529` lines / `22.77 MB` with **`97.9%` leading indentation spaces** up to column `1,557`, requiring `--tstack=400000` and `-fbracket-depth=500`). Proving bit-exact equivalence (`∀ s w, myDecode s w = encdec_backwards w s`) must handle: (a) **non-invertibility of `encdec_forwards`** from wildcard `ILLEGAL(s) <-> s`, (b) **CSR/state-dependent decoding** (`currentlyEnabled Ext_*` in `SailM`), (c) **first-match HINT shadowing** (`ZICBOP` over `ITYPE` `ORI rd=x0`), and (d) major-opcode (`w[6:0]`) step-skipping lemmas to prevent WHNF `maxRecDepth` exhaustion.

## Applicability

The findings in this report characterize the extraction and verification pipeline across the five pinned upstream repositories in `REPORT.json`:

- **Compiler Backend (`rems-project/sail` at `97aa617dcd4d01575f773cb58ea1e8686858c8c2`)**: Applies to `src/sail_lean_backend/sail_plugin_lean.ml` and `src/sail_lean_backend/pretty_print_lean.ml` under `sail --lean` (targeting `lean4:v4.34.1` and `lean-sail` `v10` at `sail_plugin_lean.ml:97-101`), controlled by `--lean-matchbv`, `--lean-real-numbers`, `--lean-executable`, `--lean-noncomputable`, `--lean-single-file`, and preprocessor symbol `CONCURRENCY_INTERFACE_V2` (`sail_plugin_lean.ml:73-125, 431`).
- **Lean Runtime Library (`rems-project/lean-sail` at `e4745c82fe329f162700020dcd31da6b342473b9`)**: Applies to sequential `Sail.ConcurrencyInterfaceV1` (`Sail/ConcurrencyInterfaceV1.lean`) and freer-monad `Sail.ArchSem` / `Sail.ArchSemSequential` (`Sail/ArchSem.lean`, `Sail/ArchSemSequential.lean`), plus `Sail/Common.lean`, `Sail/Sail.lean`, `Sail/IntRange.lean`, and `Sail/BitVec.lean` (`elabMatchBv`) on Lean `v4.29.0-rc2`+.
- **Upstream RISC-V Model and Extracted Lean Artifact (`riscv/sail-riscv` at `76f1ce3c184797178864b9869963e8b44465889e` and `opencompl/sail-riscv-lean` at `51c635c460125ac87955d061fcd902ce03b8011f`)**: Applies to RV64D (`LeanRV64D`) and RV32D (`LeanRV32D`) generated without `--lean-matchbv` or `CONCURRENCY_INTERFACE_V2`, paired with `handwritten_support/RiscvExtras.lean` vs. `handwritten_support/RiscvExtrasExecutable.lean` on Lean `v4.29.0`.
- **Purified Instruction Equivalence Layer (`opencompl/riscv-lean` at `0e3365ac7b670d79d70e9b4a8b7fba782607c44f`)**: Applies to `RISCV/Skeleton.lean`, `RISCV/SailPure.lean`, `RISCV/SailToRV64.lean`, and `RISCV/SailPureToInstructions.lean` on Lean `v4.28.0` (sharing the `ConcurrencyInterfaceV1` `EStateM` + `ExtDHashMap` representation).

For general Lean 4 kernel definitional-equality issues, `Lean.ofReduceBool` trust enlargement, and external replay checkers (`lean4lean`, `nanoda_lib`), see corpus package `lean4-kernel-soundness-criticisms-defeq-pathologies-and-lean4lean-checkers`. For differential bisimulation testing against executable reference models, see `reference-model-bisimulation-executable-semantics-and-differential-oracles`; for non-coherent `Zicbom` cache maintenance invisible to flat Sail memory, see `non-coherent-dma-cache-maintenance-zicbom-granules-and-adjacent-field-tearing-hazards`.

## Findings

### 1. Sail-to-Lean Extraction Pipeline and Dual Monad Lowering (`ConcurrencyInterfaceV1` vs. `ArchSem`)

`Basis: source + documentation`

Under `sail --lean` (`sail_plugin_lean.ml:169-245`), Libsail runs 50+ AST rewrites before Lean emission: `realize_mappings` splits bidirectional `mapping` definitions into `*_forwards`, `*_forwards_matches`, `*_backwards`, and `*_backwards_matches`; when `--lean-matchbv` is disabled (`opt_disable_matchbv = true` at `lines 94-95, 195-203`), `remove_bitvector_pats` and `guarded_pats` desugar bitvector patterns into nested `if` guards over `Sail.BitVec.extractLsb`; `("split", [String_arg "execute"])` (`line 205`) shards `execute` into `execute_<MNEMONIC>`; and `early_return`, `rewrite_loops_with_escape_effect`, and `remove_e_assign` (`lines 218-238`) convert imperative control flow into functional state-passing tuples.

At code emission (`pretty_print_lean.ml:1290-1307`), each Sail function is classified by `(is_monadic, early_return, has_loop)`:

| `(is_monadic, early_return, has_loop)` | Generated Return & Prefix | Underlying Combinator (`lean-sail`) |
| --- | --- | --- |
| `(false, false, false)` | `: T := <expr>` | Pure Lean expression |
| `(false, false, true)` | `: T := Id.run do ...` | `Id` with `ForIn'` over `Sail.IntRange` (`Sail/IntRange.lean`) |
| `(false, true, _)` | `: T := ExceptM.run do ...` | `ExceptM α := ExceptT α Id`, merging `.ok e \| .error e => e` (`Sail/Sail.lean:26-31`) |
| `(true, false, _)` | `: SailM T := do ...` | `PreSailM` (`ConcurrencyInterfaceV1` or `ArchSem`) |
| `(true, true, _)` | `: SailM T := SailME.run do ...` | `PreSailME` (`ExceptT (Sail.Error ue ⊕ T) PreSailM` in `V1`; nested `Except` in `V2`) |

`file_prelude` and `create_lake_project` (`sail_plugin_lean.ml:270-281, 398-402`) emit `set_option maxHeartbeats 1_000_000_000`, `set_option maxRecDepth 1_000_000`, `set_option backward.do.legacy true`, `set_option cleanup.letToHave false`, `moreLeanArgs = ["--tstack=400000"]` (400 MB thread stack), and `moreLeancArgs = ["-fbracket-depth=500"]`.

**V1 (`ConcurrencyInterfaceV1`) vs. V2 (`ArchSem`)**: Selected at `sail_plugin_lean.ml:431` via `Preprocess.have_symbol "CONCURRENCY_INTERFACE_V2" symbols`:

1. **`Sail.ConcurrencyInterfaceV1` (`Sail/ConcurrencyInterfaceV1.lean:101-131, 173-176, 222-225, 324-333`)**:
   - Instantiates `PreSailM RegisterType c ue := EStateM (Sail.Error ue) (SequentialState RegisterType c)` where `SequentialState` holds `regs : Std.ExtDHashMap Register RegisterType`, `choiceState : c.α`, `mem : Std.ExtHashMap Nat (BitVec 8)`, `tags : Unit`, `cycleCount : Nat`, and `sailOutput : Array String`.
   - `Sail.Error ue` (`Sail/Common.lean:294-301`) has six constructors: `Exit`, `Unreachable`, `InfiniteNondeterminisim`, `OutOfMemoryRange (n : Nat)`, `Assertion (s : String)`, and `User (e : ue)`. `sailTryCatch` (`lines 122-131, 324-333`) catches *only* `.User u`, propagating internal errors and `PreSailME` early-return `.inr retVal` untouched.
   - **Partial Hash-Map Obligation**: Because `regs` is a finite `ExtDHashMap` rather than `(r : Register) → RegisterType r`, `readReg r` (`lines 173-176`) throws `.Unreachable` when `r` is absent (`readByte addr` at `lines 222-225` throws `.OutOfMemoryRange addr`). Even pure-PC instructions such as `AUIPC` require explicit register-presence hypotheses (`h_pc : s.regs.get? Register.PC = some valt` in `RISCV/SailToRV64.lean:27-37`).
2. **`Sail.ArchSem` (`Sail/ArchSem.lean:131-213, 246-271`)**:
   - Defines Kiselyov-Ishii freer trees `FreeM Eff α` (`pure` | `impure call cont`), setting `PreSailM userError := FreeM ((Except (Sail.Error userError) InstructionEffect) ⊕ FinChoice)` over **15 architectural effects** (`regRead`, `regWrite`, `memRead`, `memWrite`, `memWriteAnnounce`, `barrier`, `cacheOp`, `tlbOp`, `clockCycle`, `getCycleCount`, `translationStart`, `translationEnd`, `archException`, `returnException`, `printMessage`).
   - Bounded nondeterminism (`undefined_bit`, `undefined_bool`, `undefined_range`, `undefined_bitvector`) emits `FinChoice` (`choose_fin n : Fin n`), whereas unbounded `undefined_{int,nat,string}` (`lines 263-271`) throws `.InfiniteNondeterminisim` into `Empty.elim`. `interpretSailEffects` (`Sail/ArchSemSequential.lean:52-90`) folds `FreeM` into `EStateM`.

### 2. Primitive Extraction Taxonomy Under Zero-Trust Kernel Checkers: `axiom`, `panic`/`FakeReal`, `opaque`, and `match_bv`

`Basis: source + execution + derived`

Replaying proofs through zero-trust kernel checkers (`lean4lean`, Carneiro 2024, `arXiv:2403.14064`; `nanoda_lib`) or enforcing `#print axioms thm ⊆ {propext, Classical.choice, Quot.sound}` exposes five distinct behaviors across external Sail primitives:

| Binding Mechanism | Upstream Specimen | Kernel `ConstInfo` & Axioms | Kernel `whnf` / `isDefEq` | Soundness & Audit Verdict |
| --- | --- | --- | --- | --- |
| Uninterpreted `axiom` | `LeanRV64D/RiscvExtras.lean:31-112` (**75 `axiom`s**: 8 platform/LR-SC + 67 SoftFloat) | `axiomInfo`; up to 75 custom axioms | Irreducible | Sound if pure/effectfully typed; **rejected** by zero-custom-axiom audit gates |
| Transparent `panic` `def` | `RiscvExtrasExecutable.lean:31-112` (`λ _ => panic "TODO..."`) | `defnInfo`; **0** custom axioms | **Unfolds** to `Inhabited.default` (`(0#5, 0#64)`, `false`) | **Unsound**: proves `riscv_f64Add rm x y = (0#5, 0#64)` **by `rfl`** |
| Approximate `FakeReal` `def` | `LeanRV64D/FakeReal.lean:6-65` (default without `--lean-real-numbers`) | `defnInfo`; **0** custom axioms | **Unfolds** to `Float` + `UInt64` cast | **Unsound**: `round_down (-1.5) = 0 ≠ -2`, `round_up 1.2 = 1 ≠ 2`, `random_real () = 34` |
| `opaque` definition | `opaque f : A → B := default` | `opaqueInfo`; **0** custom axioms | Blocked in `whnf` / `isDefEq` | **Sound for truly pure functions**, **unsound for pure-typed stateful externs** |
| Constructive / Monadic `def` | Pure IEEE-754 `BitVec` spec + `SequentialState` reservation field | `defnInfo`; **0** custom axioms | Constructive reduction & lemmas | **Gold standard**: axiom-free, executable, state-accurate |

Three non-obvious traps govern primitive replacement:

1. **Why `opaque` Fails on Pure-Typed Stateful Externs (`match_reservation` and `valid_reservation`)**: Inspect `LeanRV64D/RiscvExtras.lean:35-38`:
   ```lean
   axiom load_reservation : Arch.pa → Nat → SailM Unit
   axiom match_reservation : Arch.pa → Bool
   axiom cancel_reservation : Unit → SailM Unit
   axiom valid_reservation : Unit → Bool
   ```
   Because `sail-riscv` typed `match_reservation` and `valid_reservation` as pure C externs outside `SailM` (invoked without `←` at `Step.lean:256`), both `axiom` and `opaque` bind them as **state-independent mathematical functions**. In `do load_reservation pa 8; let b1 := match_reservation pa; cancel_reservation (); let b2 := match_reservation pa`, Lean's kernel proves `b1 = b2` **by `rfl`**, violating RISC-V `Zalrsc` / `Zawrs` semantics! Axiom-free faithfulness requires adding `reservation : Option (Arch.pa × Nat)` to `SequentialState` (or `InstructionEffect`) and lifting both queries into `SailM Bool`.
2. **Transitive Axiom Taint on Monolithic `execute`**: Even if a theorem only executes `ADDI`, referencing `LeanRV64D.Functions.execute` pulls the entire 75-axiom `RiscvExtras` closure into `#print axioms`, because Lean collects `Expr.const` dependencies syntactically across all match arms of `execute`.
3. **Hidden `Lean.ofReduceBool` via `--lean-matchbv` (`Sail/BitVec.lean:202-238`)**: When `match_bv` lacks an explicit `| _ => rhsElse` wildcard (`lines 228-231`), `elabMatchBv` synthesizes `` `(fun _ => by try bv_decide -enums) ``, injecting `Lean.ofReduceBool` (Böving et al., OOPSLA 2025, DOI `10.1145/3763167`) into the kernel proof term unless patched to use kernel-checked tactics (`omega` / `decide`).

### 3. Bridging Deterministic Sail Semantics to Pure `BitVec` Specs and Nondeterministic Hardware Models

`Basis: source + normative + derived`

- **Two-Step Purification for User-Level ALU/Bitmanip Instructions (`opencompl/riscv-lean`)**: Extracted Sail definitions mix `EStateM` register access, unbounded `Int` conversions, and `IntRange.forIn'` loops containing `sail_assert` (e.g., `execute_CPOP`). `opencompl/riscv-lean` (`0e3365ac7b670d79d70e9b4a8b7fba782607c44f`) splits purification into:
  1. *Monad-to-Pure-Sail (`RISCV/SailToRV64.lean:14-497`)*: Proves `execute_<OP> = skeleton_* SailRV64.<op>`. For loop instructions (`CPOP`, `CLZ`, `CTZ`), `IntRange.forIn'_loop_eq_pure` (`lines 274-290`) proves by stride induction that under an invariant `P i b` discharging `sail_assert` (`f i h b = pure (.yield (g i h b))`), the monadic `SailM` loop equals `pure` of the `Id` loop.
  2. *`Int`-Sail-to-`BitVec` (`RISCV/SailPureToInstructions.lean`)*: Proves `SailRV64.<op> = RV64.<op>`, enabling bit-precise `bv_decide` reasoning.
- **Refining Nondeterministic Hardware MMU/TLB and External Transitions**: `LeanRV64D` (`V1`) initializes a deterministic software `tlb` (`LeanRV64D.lean:486`), walks page tables deterministically in `mem` (`VmemPtw.lean`), resolves all `choose` calls to `0`/`false` via `trivialChoiceSource` (`ConcurrencyInterfaceV1.lean:14-26`), and erases `.cacheOp`/`.tlbOp`/`.barrier` to `pure ()`. Real hardware (Armstrong et al., POPL 2019; Simner et al., ESOP 2022) permits: (1) speculative/out-of-order page-table walks (`AK_ttw`) and asynchronous TLB caching/eviction prior to `SFENCE.VMA`, (2) nondeterministic WARL, PMA/PMP fault-priority, and `PTE.A`/`D` trap-vs-update choices, (3) concurrent MMIO/DMA memory mutations, and (4) asynchronous `mip` interrupts. Unconditional forward simulation against `SailV1 + trivialChoiceSource` is unsound when live PTEs change without `SFENCE.VMA` or code depends on `undefined_*` choices. Sound refinement either interprets `ArchSem` `FreeM` effect traces (`InstructionEffect ⊕ FinChoice`, universally quantifying over `FinChoice` as in Islaris, Sammler et al., PLDI 2022) or imposes rely-guarded kernel invariants (`TLBSynced(hw) ∧ DisjointMMIO(pa)`) quantified over arbitrary `ChoiceSource` schedules.

### 4. Right-Spined `encdec` Codegen Blowup, Priority Shadowing, and Bit-Exact Decoder Equivalence

`Basis: source + execution + derived`

Measuring `LeanRV64D/InstsEnd.lean` in `opencompl/sail-riscv-lean` (`51c635c460125ac87955d061fcd902ce03b8011f`) exposes an extreme asymmetry between forward encoding and backward decoding of `scattered mapping encdec` (`model/postlude/insts_end.sail:13, 21`):

| Function (`LeanRV64D/InstsEnd.lean`) | Lines | Byte Size | Leading Spaces (`%`) | Max Indent |
| --- | --- | --- | --- | --- |
| `encdec_backwards : BitVec 32 → SailM instruction` | `L277–L27805` (`27,529`) | `22,766,269 B` (`22.77 MB`) | `22,279,874 B` (**`97.9%`**) | `1,557` cols (`385` `)`s on `L27805`) |
| `encdec_forwards_matches : instruction → SailM Bool` | `L27807–L29898` (`2,092`) | `102,429 B` (`0.10 MB`) | `19,312 B` (`18.9%`) | `26` cols |
| `encdec_backwards_matches : BitVec 32 → SailM Bool` | `L29900–L56256` (`26,357`) | `21,639,145 B` (`21.64 MB`) | `21,179,011 B` (**`97.8%`**) | `1,557` cols |
| `encdec_compressed_backwards : BitVec 16 → SailM instruction` | `L59373–L62819` (`3,447`) | `395,221 B` (`0.40 MB`) | `331,140 B` (`83.8%`) | `233` cols |
| **Total `LeanRV64D/InstsEnd.lean`** | `72,377` | **`45,876,653 B` (`43.75 MiB`)** | `43,893,491 B` (**`95.7%`**) | `1,557` cols |

Without `--lean-matchbv`, `guarded_pats` lowers ~778 `encdec` clauses into a right-nested `match (← do if <bits> then (if ← currentlyEnabled Ext then pure (some ...) else pure none) else pure none) with | .some r => pure r | none => (do ...)` spine, necessitating `--tstack=400000` for `lean` and `-fbracket-depth=500` for Clang (`leanc`). Four rules govern bit-exact equivalence (`myDecode` $\equiv$ `encdec_backwards`):

1. **Asymmetric Round-Tripping (`ILLEGAL` Non-Injectivity)**: Catch-all `ILLEGAL(s) <-> s` (`insts_end.sail:13`) maps `ILLEGAL w` forward to `w` unconditionally. Thus `encdec_forwards (ILLEGAL 0x0015200F#32) = 0x0015200F#32` (`cbo.clean (a0)`), which `encdec_backwards` decodes to `ZICBOM (CBO_CLEAN, regidx 10) ≠ ILLEGAL 0x0015200F#32`. Decode-then-encode (`encdec_forwards ∘ encdec_backwards = id`) holds on valid encodings, whereas encode-then-decode holds **only** under a well-formedness predicate `WF_insn s insn` (extension enabled in `s`, unshadowed by HINTs, and `ILLEGAL w` restricted to unmatched `w`).
2. **State-Dependent Decoding (`SailM`)**: Clauses query CSRs via `← currentlyEnabled Ext_*` (and `← readReg cur_privilege` for `Zicfiss` at `InstsEnd.lean:62101`). A pure decoder `BitVec 32 → instruction` is equivalent only when parameterized by an extracted CSR configuration `cfg` satisfying `MatchesExtConfig s cfg` (plus 16-bit vs. 32-bit parcel dispatch in `Fetch.lean`).
3. **Ordered First-Match HINT Shadowing (`ZICBOP` vs. `ORI rd=x0`)**: At `InstsEnd.lean:281-297`, `ZICBOP` (`w[14:0] == 0b110_00000_0010011#15`, `w[24:20] ∈ {0, 1, 3}`) precedes `ITYPE` (`ORI`). Across all $2^{17} = 131,072$ `ORI rd=x0` words, `Ext_Zicbop = true` decodes `12,288` words to `ZICBOP` and `118,784` to `ITYPE (..., x0, ORI)`; `Ext_Zicbop = false` returns `pure none` at `L296`, falling through on **all `131,072` words to `ITYPE` (`ORI`)** rather than `ILLEGAL` (and similarly `Zihintntl` at `L303-312` over `ADD x0, x0, rs2`). Table decoders must preserve HINT priority and disabled-extension fallthrough.
4. **Scalable Proof Decomposition Without 778-Deep WHNF Unfolding**: Monolithic `simp [encdec_backwards]` or `bv_decide` on symbolic `w : BitVec 32` blows out `maxRecDepth`. Instead, prove `(encdec_backwards w).run s = .ok insn s' → s' = s` (`readReg`-only purity under `WellFormedRegs s`), shield tail continuations behind auxiliary defs, and apply a 1-step skip lemma `(m = fun s => .ok none s) → (match ← m with | .some r => pure r | none => k) = k` partitioned by concrete 7-bit major opcode `w[6:0]` (`128` cases, ~110 immediately collapsing to `ILLEGAL w`) and `funct3 = w[14:12]`.

## Boundaries

- **Unconditional Bijectivity or State-Free `encdec` Signatures (`known not to apply`)**: Treating `encdec_forwards` and `encdec_backwards` as unconditional mutual inverses or typing `encdec_backwards` without CSR state is **known not to apply**, falsified by `ILLEGAL 0x0015200F#32` and `Ext_Zicbop`/`Ext_Zicbom` gating.
- **Unbounded Nondeterminism in `ArchSem` (`unsupported`)**: `undefined_int`, `undefined_nat`, and `undefined_string` are **unsupported** for branching in `Sail.ArchSem` (`Sail/ArchSem.lean:263-271`), immediately emitting `.InfiniteNondeterminisim`.
- **Tagged Capability Memory in `ArchSemSequential` (`unsupported`)**: `interpretInstructionEffect` (`Sail/ArchSemSequential.lean:60, 66`) rejects `req.numTag != 0` with `.Assertion "Tagged memory not supported"`.
- **Full `sail-riscv` Elaboration Scaling Under `--lean-matchbv` (`unknown`)**: `opencompl/sail-riscv-lean` disables `--lean-matchbv`; whether `elabMatchBv` (`dite_gather` + `bv_decide -enums`) elaborates all ~778 `encdec` clauses within Lean memory/heartbeat budgets is **unknown** from upstream builds.
- **SoftFloat C Equivalence and RVV 1.0 Vector Extraction (`not examined`)**: Bit-exact proofs equating the 67 `RiscvExtras` float signatures to Berkeley SoftFloat C / Lean `SymFP`, and RVV vector instruction extraction scaling, were **not examined**.
- **Attractive Stronger Conclusion Not Established**: Mechanical `s/axiom/opaque/` in `RiscvExtras.lean` removes `#print axioms` entries but does **not** yield a sound `Zalrsc` model: `opaque match_reservation : Arch.pa → Bool` and `opaque valid_reservation : Unit → Bool` remain state-invariant constants across `load_reservation` and `cancel_reservation`.

## Evidence

All upstream commits, source metrics, and executable probes were verified on `2026-11-20`:

1. **Sail Lean Backend (`rems-project/sail` at `97aa617dcd4d01575f773cb58ea1e8686858c8c2`)**: `src/sail_lean_backend/sail_plugin_lean.ml` (`lines 73-245, 262-288, 338-341, 395-431`: CLI options, 50+ rewrites, `ConcurrencyInterfaceV1` vs. `ArchSem`, prelude limits, `--tstack=400000`, `-fbracket-depth=500`, `FakeReal.lean`) and `src/sail_lean_backend/pretty_print_lean.ml` (`lines 1290-1330`: 5-way `do`-combinator dispatch).
2. **Lean-Sail Runtime (`rems-project/lean-sail` at `e4745c82fe329f162700020dcd31da6b342473b9`)**: `Sail/Common.lean` (`lines 294-310`), `Sail/Sail.lean` (`lines 26-32`), `Sail/BitVec.lean` (`lines 195-239`: `elabMatchBv` `bv_decide -enums` at `line 231`), `Sail/ConcurrencyInterfaceV1.lean` (`lines 14-26, 101-281, 320-350`), `Sail/ArchSem.lean` (`lines 120-285`), and `Sail/ArchSemSequential.lean` (`lines 52-95`).
3. **RISC-V Sail and Lean Artifacts**: `riscv/sail-riscv` (`76f1ce3c184797178864b9869963e8b44465889e`: `model/postlude/insts_end.sail:13-38`, `handwritten_support/RiscvExtras.lean:31-112`, `handwritten_support/RiscvExtrasExecutable.lean:31-112`); `opencompl/sail-riscv-lean` (`51c635c460125ac87955d061fcd902ce03b8011f`: `LeanRV64D/RiscvExtras.lean`, `LeanRV64D/FakeReal.lean:6-65`, `Step.lean:256`, `Fetch.lean`, `LeanRV64D/InstsEnd.lean:277-62819`); and `opencompl/riscv-lean` (`0e3365ac7b670d79d70e9b4a8b7fba782607c44f`: `RISCV/SailToRV64.lean:27-37, 274-290`, `RISCV/Skeleton.lean`, `RISCV/SailPureToInstructions.lean`).
4. **Literature**: Armstrong et al., POPL 2019, DOI `10.1145/3290384`; Carneiro, 2024, `arXiv:2403.14064`; Böving et al., OOPSLA 2025, DOI `10.1145/3763167`; Sammler et al., PLDI 2022, DOI `10.1145/3519939.3523434`; Simner et al., ESOP 2022, DOI `10.1007/978-3-030-99336-8_6`; Bhat et al., ITP 2024, DOI `10.4230/LIPIcs.ITP.2024.9`.
5. **Executable Metrics & Subspace Verification (`Basis: execution`)**: Python 3.11 checks confirmed `75` `axiom`s in `RiscvExtras.lean`, `97.9%` indentation whitespace in `encdec_backwards` (`22,279,874 / 22,766,269 B`), `262,144 / 262,144` CBO decode-to-encode round-trips, `ILLEGAL 0x0015200F` alias counterexample, and `(12288, 131072)` `ZICBOP`/`ORI rd=x0` HINT splits.

## Revalidation

1. **Self-Contained Decoder Subspace & `FakeReal` Probe (< 1 second, Python 3.10+ stdlib only)**:
   ```bash
   python3 - <<'PY'
   import math
   round_down = lambda x: 0 if x < 0.0 else int(x)
   round_up = lambda x: round_down(x + 0.5)
   assert round_down(-1.5) == 0 != math.floor(-1.5) and round_up(1.2) == 1 != math.ceil(1.2)
   def dec_cbo(w, zicbom=True, zicboz=True):
       if (w & 0x7F) == 0x0F and ((w >> 12) & 7) == 2 and ((w >> 7) & 0x1F) == 0:
           f12, rs1 = (w >> 20) & 0xFFF, (w >> 15) & 0x1F
           if f12 in (0, 1, 2) and zicbom: return ("ZICBOM", f12, rs1)
           if f12 == 4 and zicboz: return ("ZICBOZ", rs1)
       return ("ILLEGAL", w)
   enc_cbo = lambda a: ((a[1] << 20) | (a[2] << 15) | 0x200F) if a[0] == "ZICBOM" else (
       ((4 << 20) | (a[1] << 15) | 0x200F) if a[0] == "ZICBOZ" else a[1])
   for rd in (0, 1):
       for hi in range(1 << 17):
           w = (hi << 15) | 0x200F | (rd << 7)
           assert enc_cbo(dec_cbo(w)) == w
   assert dec_cbo(enc_cbo(("ILLEGAL", 0x0015200F))) == ("ZICBOM", 1, 10)
   dec_ori0 = lambda w, zbop: ("ZICBOP" if (((w >> 20) & 0x1F) in (0, 1, 3) and zbop) else "ITYPE_ORI")
   on_z = sum(dec_ori0((hi << 15) | 0x6013, True) == "ZICBOP" for hi in range(1 << 17))
   off_z = sum(dec_ori0((hi << 15) | 0x6013, False) == "ITYPE_ORI" for hi in range(1 << 17))
   assert (on_z, off_z) == (12288, 131072)
   print("Verified: FakeReal mismatch, 262144 CBO roundtrips, ZICBOP=(12288, 131072)")
   PY
   ```
2. **Upstream Source Drift Checks**:
   - Diff `src/sail_lean_backend/sail_plugin_lean.ml` (`opt_disable_matchbv`, `CONCURRENCY_INTERFACE_V2`) and `Sail/BitVec.lean` (`elabMatchBv`) to see if `sail-riscv-lean` enables `ArchSem` or `--lean-matchbv`, or removes `bv_decide` from `elabMatchBv`.
   - Diff `handwritten_support/RiscvExtras.lean` (`riscv/sail-riscv`) and `LeanRV64D/RiscvExtras.lean` (`opencompl/sail-riscv-lean`) to see if `match_reservation` / `valid_reservation` become monadic in `SailM` or SoftFloat `axiom`s become constructive `BitVec` defs.
