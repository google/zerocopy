# Millipede: LLM-Era Verified Systems Language and Compiler Embedded in Lean 4

## Summary

Millipede (`graydon/millipede`, pinned at `4f13d3980a5570177a774e63cfbc95e652dd3cde`) is an experimental low-level imperative programming language, proof environment, and end-to-end verified compiler embedded in Lean 4 (`v4.35.0`, Core and `Std` only, zero external Lake dependencies) targeting static x86-64 and AArch64 Linux ELF64 executables with no LLVM, assembler, linker, or C runtime in the compilation path. Its core thesis is that when LLMs simultaneously serve as threat models (automated bug-finding), primary program and proof authors, and compiler implementers, the cost-benefit ratio shifts away from human-ergonomic expressivity toward maximally restrictive static disciplines (no heap, no recursion, bounded loops, linear types, non-storable borrows, proof obligations on partial operations, declared units, capability tokens, and typestate handles) coupled with machine-checked compilation.

Direct source inspection establishes five durable architectural patterns and concrete limits:

1. **Dual-representation deep embedding keeps the elaborator out of the TCB**: `mp def` elaborates Lean `do`-notation into an intrinsically typed de Bruijn ANF term (`Exp Γ t`) and simplifies its structural denotation (`Exp.denote`) into an ordinary Lean function `f` (for `Std.WP`/`vcgen` proofs), proving `f.exp_denote` and `f.wf` in Lean's kernel. However, kernel checking of `f.exp_denote` scales roughly cubically in the number of jumping statements.
2. **Validation-over-verification scales verified compiler construction**: the compiler verifies simple checkers rather than complex search heuristics across four stages — untrusted `mp def` elaboration checked by `f.exp_denote`/`f.wf`; untrusted register allocation and live-set computation checked per instruction (`RegAlloc.check`, `Live.flex`); untrusted step-budget potential solver checked per instruction (`budgetOk`); and Core optimization passes (`inline`, `fold`, `dce`, `strength`) kept only if static cost/stack bounds do not increase.
3. **Unconditional byte-level soundness with tight TCB accounting**: `Millipede.compile_sound` (x64 Linux, standard Lean axioms only) and `Millipede.compile_sound_arm64` (arm64 Linux, standard axioms plus `bv_decide` restricted strictly to `Target/A64/{Word,Decode}.lean`) state `NeverStuck`, `TraceEq`, `StackWithin`, and per-reactor-step `StepsWithin` against an adversarial `Oracle`. `#audit` structurally re-validates `bv_decide` per-use axioms via `Meta.nativeEqTrue` and checks that arguments reference only library constants; `scripts/audit.sh` enforces that every unproved `*.Statement` definition is explicitly listed in `doc/open-claims.md`; every emitted binary ships with a `<file>.ledger.txt` assumption ledger.
4. **Human reviewability forced two mid-stream reversals even for an LLM-authored language**: custom loop syntax was replaced with Lean's familiar `do`-notation (Decision 28), and syntax-template modules were replaced with checked Lean terms under `variable` binders and `mp interface`/`mp implementation` structures (Decision 29).
5. **Substantial expressivity, codegen, and proof-kernel limits remain**: programs are sequential reactors limited to three Linux syscalls (`read`, `write`, `exit`); documented codegen runs 3.5x–21x more instructions than `gcc -O2`; only three example programs carry end-to-end trace specifications (`hello`, `revchunks`, `kvsrv`); kernel evaluation of `compile` acceptance completes only for `exit42` and `hello`; and information-flow typing, C FFI bindings, and general protocol refinement remain unbuilt.

## Applicability

- **Direct subject**: `graydon/millipede` at commit `4f13d3980a5570177a774e63cfbc95e652dd3cde` (authored `2026-11-21`, parent `73f84a0469b150bf6f058b1ef88e9997c71e7d76`), built against `leanprover/lean4:v4.35.0` with no external packages (`lake-manifest.json` lists `"packages": []`).
- **Scope of verification in this report**: Structural architecture, type/borrow/effect rules, theorem statements, compiler pipeline, audit enforcement, `@[implemented_by]` locations, and LOC/declaration/axiom censuses were verified directly from repository source (`source`). Runtime performance figures, `qemu`/hardware co-simulation outcomes, proof-burden ratios, safety censuses, and development cost estimates are reported from repository documentation (`documentation`) without independent build/execution on this host (see **Boundaries**).
- **Generalization boundary**: Findings characterize the concrete design, trade-offs, and failure modes of an LLM-authored Lean-4-embedded verified systems language and compiler at prototype scale (~81k lines of library Lean, ~24k lines of test Lean). They do not establish that the same restrictions scale to general-purpose concurrent/heap-allocating software or that the documented `$50` / 5-day construction cost reproduces across different models, specifications, or verification targets.

## Findings

### 1. Problem Statement and Inverted PL Design Axes

Basis: documentation (`README.md`, `doc/design/goals.md`, `doc/design/decisions.md`) + source.

Millipede frames language design around three simultaneous shifts attributed to LLMs (`README.md` L11–L28, L84–L92; `doc/design/goals.md` L7–L24):
- **LLMs as threat model**: automated analysis increases the urgency of ruling out whole defect classes by construction or proof before deployment.
- **LLMs as target authors**: dropping human-ergonomic convenience features in exchange for strict, verbose, or "fiddly" static disciplines becomes viable when agents write both code and routine proofs.
- **LLMs as compiler implementers**: the repository (~81,070 library lines, ~24,097 test lines, 3,006 library theorems) was written by LLM agents under one human's supervision (~6 hours human time, ~5 days wall-clock, ~$50 compute estimate; `README.md` L94–L107; `doc/design/goals.md` L22–L24).

Consequently, Millipede inverts typical human-facing systems PL priorities:

| Axis | Conventional systems PL choice | Millipede choice (`doc/design/goals.md`, `language.md`, `memory.md`) | Consequence |
|---|---|---|---|
| Memory & allocation | Dynamic heap, GC/RC, or general lifetimes | No heap; static root + fixed-size arrays/arenas (`Slots`, `Pool`, `Bump`); references cannot be stored in structs/arrays or returned | Zero lifetime annotations; static stack & footprint bounds; no linked/recursive types |
| Control flow & termination | Recursion, unbounded loops, exceptions/panics | Strictly acyclic call graph (call only earlier `mp def`s); single bounded loop `for i in lo...hi` (upper bound is a size expression or `min e N`); no exceptions; linear `Result` | Every function terminates; per-reactor-step static instruction and stack bounds |
| Arithmetic & partial ops | Default wrapping/UB or implicit runtime panics | Explicit three-way operator split: `+ - *` (total wrapping), `+? -? *?` (checked `Result`), `+! -! *!` (zero-overhead machine op with proof obligation); same for `a[i]` / `a[i]?` / `a[i]!` and unit `.to` / `.to?` / `.to!` | Overflow/bounds policy visible at every call site; zero hidden panics or UB |
| Execution model | Threads, globals, ambient OS authority | Sequential reactor (`init` once + infinite `step(&mut root)`); zero global variables; explicit capability tokens (`mp capability`) + `NoCalls` trace theorems | Data-race freedom and static authority bounds by construction/theorem |
| Generics & modularity | Dedicated object-language module/trait system | Ordinary Lean `variable` binders + `mp interface` / `mp implementation` structures; monomorphized before compilation | Compiler sees only closed first-order terms; generic proofs checked once |

**Counter-finding on human reviewability** (`doc/design/decisions.md` Decisions 28–29): despite stating that "humans aren't the target audience for writing Millipede programs" (`README.md` L64), human readability drove two major mid-project redesigns:
- **Decision 28 (`do`-notation surface)**: custom loop syntax (`for i < N, acc := init while c do body`) proved unreadable to human reviewers and was replaced by Lean's own `do` parser (`for i in lo...hi do`, `let mut`, `break`, `continue`, `return`, place assignments), while keeping Lean's `do` elaborator unused and Core/compiler byte-identical. Unbounded `while`/`repeat`/`try`/`←` are explicitly rejected at their source span.
- **Decision 29 (checked generic terms over syntax templates)**: template modules (`mp module` / `mp instance` re-elaborated per instantiation) were deleted and replaced with checked Lean terms under `variable` binders and `mp interface` structures so generic code is proved once rather than per instance.

### 2. Dual-Representation Deep Embedding in Lean 4

Basis: source (`Millipede/Core/Exp.lean`, `Millipede/Core/Denote.lean`, `Millipede/Core/Wf.lean`, `Millipede/Meta/Elab.lean`, `Millipede/Meta/Sem.lean`) + documentation (`doc/design/embedding.md`, `doc/open-claims.md`).

Each `mp def` produces two Lean artifacts tied together by a kernel-checked theorem:
1. **Core term `f.exp : Exp Γ t`** (`Millipede/Core/Exp.lean` L35–L180): an intrinsically typed de Bruijn A-normal form (ANF) inductive type (`Mem t Γ`, `Env Γ`, `Atom Γ t`, `Prim ps r`, `Exp Γ t`) with structural recursion for:
   - Value semantics `Exp.denote (ω : Oracle) : Exp Γ t → Env Γ → World → t.carrier × World` (`Millipede/Core/Denote.lean` L51–L97), where `&mut` borrows and reference calls are pure lens get/set updates (no pointers or aliasing in value semantics) and partial operations return defaults.
   - Instrumented cost semantics `Exp.exec` and syntactic bounds `Exp.cost`, `Exp.stackBytes`, `Exp.footprint` (`Millipede/Core/Cost.lean`, `Stack.lean`).
   - Decidable linearity and borrow checker `Exp.check` / `Exp.wf : Bool` (`Millipede/Core/Wf.lean` L47–L160), tracking per-binder state `BS` (`mode`, `lin`, `moved`, `wr`, `loans : List Loan`, `view`) with field-granular path overlap (`Sel.overlap`) and treating dynamic array indices conservatively as overlapping (`Sel.dyn`), supplemented by explicit disjoint pair borrows `&mut (a[i], a[j])` with an `i ≠ j` obligation.
   - Effect/authority symbol collector `Exp.syms` and `Exp.externs` (`Millipede/Core/Effects.lean`, `Top/Ledger.lean`).
2. **Simplified Lean function `f`** (`Millipede/Meta/Elab.lean` L41–L72): produced by running `simp` with a fixed lemma set (`Millipede/Meta/Sem.lean`) on `f.exp.denote` with loop bounds and callees abstracted (`normalFormOfExp`), living in `Id` (pure) or `StateM World` (effectful, taking `ω : Oracle`), returning `&mut` parameters as extra tuple outputs.

**Why both exist**: Lean's extensional logic cannot distinguish cost, memory layout, or linearity of two extensionally equal Lean functions, whereas Lean's `Std.WP` + `vcgen` tactic cannot see through `Exp.denote` on a deeply embedded AST (`doc/design/embedding.md` L10–L21, L71–L76). Because the kernel checks `f.exp_denote` (proving `f.exp` denotes `f`) and `f.wf` (by `decide`), the ~4,355-line `mp def` elaborator (`Millipede/Meta/Elab.lean`) is outside the TCB.

**Elaboration and kernel bottlenecks observed in source/docs**:
- To avoid building `List.range n` at runtime during `#eval` / differential testing when `n` approaches `2^64`, `Millipede/Meta/Sem.lean` L225–L236 defines `Upto.forIn` equal to `ForIn.forIn (List.range r.bound)` in the logic (`forIn_upto : ... := rfl`) with `@[implemented_by Upto.forInImpl]` for compiled evaluation.
- `doc/open-claims.md` L42–L44 documents that kernel checking of `f.exp_denote` grows roughly as the **cube** of the number of jumping statements (`if`/`match` copying continuations), causing a function with ~12 jumping statements to consume minutes and gigabytes of RAM (unbounded by the 100,000-node AST continuation cap in `doc/reference/messages.md` L117).

### 3. Type System, Obligations, Verification Stack, and Domain Extensions

Basis: source (`Millipede/Analysis/Domain.lean`, `Millipede/Meta/Burden.lean`, `Millipede/Core/Program.lean`, `Tests/KVRefine.lean`) + documentation (`doc/design/{obligations,arenas,modules,units,world,security,protocols}.md`, `doc/status.md`, `doc/open-claims.md`).

- **Multi-tier obligation discharge** (`doc/design/obligations.md` L70–L166): when `mp def` runs, obligations (`f.SafeGoal`) pass through three tiers in order:
  1. **Verified abstract interpreter** (`Millipede/Analysis/Domain.lean`, `Sound.lean`): closed intervals `Itv := [lo, hi]`, path comparison facts `Cmp Γ` (`<, ≤, =, ≠`), and affine loop-growth upper bounds `UB Γ` (`x ≤ c0 + d * y`), proved sound once (`Exp.an_sound`, `Exp.safe_of_safeBy`). Partial certification (`Exp.anR`, `Exp.safe_of_relax`) strips discharged obligations and forwards the remainder. Currently requires `Exp.LoopsOk` proved per definition by `rfl` (not decidable inside `compile`), and does not read reference-parameter fields, `Slots` cells, or callee `ensures` (`doc/open-claims.md` L124–L131).
  2. **Automatic tactics**: `mp_safe` (branch/loop splitting + `simp`/`omega`/`grind`) followed by `mp_auto` (bounded by `mp.autoSafe.maxHeartbeats := 200000` and `mp.autoSafe.kernelHeartbeats := 10000`).
  3. **Manual proof (`mp prove f.safe := ...` / `mp prove f.spec := ...`)**: contracts (`requires`/`ensures`) generate `@[spec]` Hoare triples (`f.spec`) for `Std.WP`/`vcgen` and plain facts (`f.post`) for obligations, enabling modular verification without unfolding callees. Event contracts expose `history`, `events`, and `exited` (`doc/design/obligations.md` L167–L211).
- **Arenas and linearity**: `Slots T n` is the single primitive for runtime occupancy (occupancies are proof-only ghost metadata; `put!`/`take!`/`[i]!` carry obligations). `Pool T n W` (bitmap-backed, sealed linear keys `Pool.Key T n W`) and `Bump T n` are implemented in Millipede over `Slots` and implement the `Alloc` interface (`doc/design/arenas.md`, `modules.md`). Keys are branded by arena type/parameters rather than per-value arena identity (`doc/design/deviations.md` Deviation 6).
- **Units (`mp dimension`, `mp unit`)**: `Q u` wraps `UInt64` with integer scale tags in one dimension; erased before Core. Mixed-unit arithmetic is rejected with actionable conversion diagnostics (`.to`, `.to?`, `.to!`, `.toFloor`, `.toCeil`); specs reason in base units via `u.inBase` (`doc/design/units.md`).
- **Capabilities and typestate**: `mp capability C for "sym"` binds extern symbol sets to zero-size sealed linear tokens (`Cap c`). `mp def` and `mp program` prove `f.noCalls` / `p.noCalls` from `Exp.syms`, carried to machine traces by `Program.NoCalls.machine` (`doc/design/world.md` L31–L69). Typestate handles are sealed linear structs parameterized by a Lean state value (`Log (s : LogSt)`); transitions consume and return owned handles, enforced by the borrow/linearity checker without a separate runtime tag (`doc/design/protocols.md` L14–L40).
- **Derived binary formats (`mp format`)**: an untyped inductive `Fmt` with values `Val` has once-for-all theorems (`Fmt.parse_write`, length bound, canonicality/injectivity, `Fmt.valid_iff`; `Millipede/Format/Theorems.lean`). `mp format f for T := (...)` generates Millipede `parseAt`/`writeAt`/`validAt` functions plus `T.toVal` and proves their contracts against `f`; the text-to-`Fmt`/`toVal` step is trusted generator code (`doc/design/security.md` L32–L97; `doc/design/deviations.md` Deviation 16). Used end-to-end in `Tests/KVRefine.lean` (`kvsrv_behaviour`, `kvsrv_answers`) to prove a compiled 4-slot key-value server refines an abstract map against every oracle.

### 4. End-to-End Verified Compiler Architecture and Top-Level Theorem

Basis: source (`Millipede/Top/{Statement,Compile,Sound,SoundA64,Ledger}.lean`, `Millipede/Target/{Target,X64/Isa,A64/Decode}.lean`, `Millipede/Extern/Oracle.lean`) + documentation (`doc/design/{compiler,targets,trust,resources}.md`).

The compiler (`Millipede.compile : Program → Target → Except String ByteArray`) executes one deterministic pipeline with zero external build tools (`Millipede/Top/Compile.lean` L17–L23, L59–L145):

```text
Program ──checks (wf + lawful certs)──▶ Core Opt (inline, fold, dce, strength; 2 rounds)
  ──Flat.lower (byte memory + <=4-word never-borrowed values in frame slots)──▶ Flat.Prog
  ──Lin.linearize──▶ Lin.Prog ──idOps + validated RegAlloc (preserved + caller-saved + parallel moves)──▶ Lin.Prog
  ──Sel.select (shared proof skeleton)──▶ Asm.Prog ──budgetOk (potential check)──▶ Asm.Prog
  ──Asm.assemble──▶ Obj ──Link.link (PIC, W^X)──▶ Image ──Elf.write──▶ ByteArray
```

Exact top-level theorem (`Millipede/Top/Statement.lean` L42–L51):
```lean
def CompileSound.Statement (compile : Program → Target → Except String ByteArray)
    (t : Target) : Prop :=
  ∀ (p : Program) (b : ByteArray), compile p t = .ok b → p.Safe →
    ∃ s₀, t.fmt.load b.data.toList = some s₀ ∧
      ∀ ω : Oracle,
        let m := Machine.run t s₀ ω
        m.NeverStuck ∧
        TraceEq m.trace (p.events ω) ∧
        m.StackWithin (p.stackBytes t.φ) ∧
        m.StepsWithin (p.events ω) (fun k => p.stepCost k ω t.κ)
```

Key verified properties from source:
- **Unconditional instantiation**: `Millipede.compile_sound : CompileSound.Statement compile x64Linux` (`Millipede/Top/Sound.lean` L252–L253), `Millipede.compile_sound_arm64 : CompileSound.Statement compile arm64Linux` (`Millipede/Top/SoundA64.lean` L109–L110), and `Millipede.compileWith_sound` (all option settings, L114–L118) all have zero extra hypotheses and factor through a single backend-generic composition theorem `compileWith_sound_of_backend` (`Sound.lean` L151–L166) parameterized by `Backend.Laws`.
- **Tight stack corollary**: `compile_stack_tight` / `compile_stack_tight_arm64` (`Millipede/Top/StackTight.lean`) bound stack depth by the smaller post-regalloc `PT_GNU_STACK` size actually requested in the ELF header (`≤ p.stackBytes t.φ`).
- **Deterministic forward simulations**: every intermediate semantics (`Flat`, `Lin`, `Target.sem`) shares one deterministic `Sem` interface with monotonic event traces and work counters, avoiding backward simulations (`doc/design/compiler.md` L108–L119).
- **Translation validation everywhere complex heuristics live**:
  - *Register allocation*: untrusted allocator proposes slot→location renaming (6 preserved + 6 caller-saved on x64; 6–10 preserved + 14 caller-saved on arm64) and live sets; `RegAlloc.check` validates lock-step equivalence and validates live sets by running on the program against itself (`Live.flex`), falling back cleanly on refusal (`Millipede/Top/Compile.lean` L133–L144; `Sound.lean` L178–L212).
  - *Instruction budgets*: untrusted fixed-point solver computes per-PC potential; `budgetOk` checks per-instruction payment against target cost model `κ` (`doc/design/compiler.md` L189–L195).
  - *Core optimizations*: each pass proves semantic/safety preservation (`Opt.Pass.apply_sim`), while cost/stack non-increase is checked dynamically per pass; fallback strips passes if downstream compilation refuses (`Sound.lean` L86–L115).
- **Adversarial oracle & minimal ISA subsets**: `Oracle := List Event → Call → Reply` (`Millipede/Extern/Oracle.lean` L48–L49) quantifies over all possible kernel replies (including arbitrary short writes/errors); ISA decoders (`X64.decode`, `A64.decodeWord`) accept only canonical encodings of emitted instructions (`A64/Decode.lean` L74–L75), so `NeverStuck` guarantees execution never leaves the modelled subset, and `W^X` ELF segments prevent self-modifying code (`doc/design/trust.md` L132–L149).

### 5. Auditing, Anti-Vacuity, Diagnostics, and LLM Feedback-Loop Tooling

Basis: source (`Millipede/Meta/Audit.lean`, `Millipede/Top/Ledger.lean`, `Millipede/Meta/Emit.lean`, `scripts/audit.sh`, `scripts/leanq.py`, `CLAUDE.md`) + documentation (`doc/reference/messages.md`, `doc/status.md`).

Because LLM-authored proof bases risk subtle vacuity, hidden axioms, or stale docs, Millipede builds mechanical guardrails directly into the toolchain:

1. **Deep `#audit` axiom verification** (`Millipede/Meta/Audit.lean` L79–L260):
   - Walks every theorem and axiom across `Millipede*` (including internal/private names).
   - Rejects `sorryAx`, any user axiom, `Lean.ofReduceBool`/`Lean.trustCompiler` outside `bvDecideMods := [Millipede.Target.A64.Word, Millipede.Target.A64.Decode]`, and any forged `_native` axiom.
   - For per-use `bv_decide` axioms (`P._native.bv_decide.ax_*`), `checkBvDecideAxiom` verifies that `P` is a theorem in the same module, the type is `Std.Tactic.BVDecide.Reflect.verifyBVExpr P._expr_def_* P._cert_def_* = true`, neither argument references any non-library Millipede constant (blocking `@[implemented_by]`/`@[extern]` smuggling), and re-executes `Meta.nativeEqTrue` on the unfolded expression.
   - Confirmed by direct source scan: `0` `sorry`, `0` `axiom`, `0` `native_decide` across all 295 `.lean` files; only 3 `@[implemented_by]` annotations exist, all in `Millipede/Meta/` (`Meta/Sem.lean:227`, `Meta/Report.lean:130`, `Meta/Emit.lean:106`).
2. **Honest open-claims gate (`scripts/audit.sh` L70–L86)**: greps every `def *.Statement` in `Millipede/` and `Tests/` and fails unless either a `theorem` proves that exact statement or it appears verbatim in `doc/open-claims.md`. Only one open statement exists at `4f13d398`: `CompileAccepts.Statement` (kernel evaluation of `compile` accepting `revchunks` times out after 20 minutes in `Sel.potential`).
3. **Safety-gated emission & per-binary assumption ledgers** (`Millipede/Meta/Emit.lean` L80–L94; `Millipede/Top/Ledger.lean`): `#mp_compile` and `mp_entry%` refuse any program lacking `p.safe` or whose `p.safe` fails `Audit.rejectedAxioms`. Every compiled binary writes `<file>.ledger.txt` naming the theorem, bounds, extern symbols, trusted models, and backing test scripts (cross-checked for file existence by `Tests/Ledger.lean`).
4. **Mutation-tested ("teeth") model validation** (`doc/status.md` L165–L188; `scripts/audit.sh` L47–L67): virtually every test script (differential suites, x64/arm64 co-simulation, arm64 encoder, bound-check, layout-check, ELF/PE/Mach-O/ElfRel checks, and `scripts/audit.sh`'s `doMutant` check) includes a `--selftest` mode that seeds deliberate bugs and requires failure.
5. **Low-latency agent proof-loop CLI (`scripts/leanq.py`) & actionable diagnostics (`doc/reference/messages.md`)**:
   - `scripts/leanq` wraps `leanclient` over Lean's LSP server to provide shell-invocable `goal`, `diag`, `try` (in-memory multi-tactic comparison without touching disk), `hover`, and `selftest`, cutting LLM proof-iteration latency vs full `lake build`.
   - Error and open-proof messages (`doc/reference/messages.md`) print exact remaining goals, name missing obligations/invariants, distinguish recoverable open-proof info messages from hard errors, and provide concrete repair hints (e.g., suggesting `KeyStack`/`Holds`, raising `mp.autoSafe.maxHeartbeats`, or splitting functions).

### 6. Empirical Codebase Census, Documented Measurements, and Concrete Limitations

Basis: source (LOC/declaration census on `4f13d3980a5570177a774e63cfbc95e652dd3cde`) + documentation (`doc/measurements.md`, `doc/design/limits.md`, `doc/open-claims.md`, `doc/status.md`).

**Direct source census (`4f13d3980a5570177a774e63cfbc95e652dd3cde`, `source`)**:
- `Millipede/`: 195 files, 81,070 lines, 2,717 definitions/types, 3,006 theorems/lemmas. Largest subsystems: `Compile/` (24,630 lines, 1,083 theorems), `Target/` (15,096 lines, 681 theorems), `Meta/` (11,916 lines, 81 theorems), `Object/` (7,795 lines, 316 theorems), `Core/` (6,202 lines, 215 theorems), `RegAlloc/` (5,221 lines, 183 theorems).
- `Tests/`: 92 files, 24,097 lines, 1,122 definitions, 168 theorems.

**Documented empirical measurements (`doc/measurements.md`, `doc/design/limits.md`, `documentation`)**:
- **Performance vs `gcc -O2 -nostdlib -static -s`** (after S6 step 3 optimizations: data-region base addressing, x64 immediates, identity-op removal, parallel moves):
  - `upper` (64 KiB input): code 1,869 B (x64) / 1,128 B (arm64) vs 244 B (`gcc`); executed instructions 4.5x (x64) / 3.5x (arm64) vs `gcc`.
  - `revchunks` (4 KiB): code 1,549 B / 904 B vs 156 B; executed 8.0x / 6.7x vs `gcc`.
  - `kvsrv` (244 B): code 29,607 B / 16,548 B vs 1,032 B; executed 21x / 18x vs `gcc`.
  - Static ELF file size: >=8 KiB (x64, 4 KiB pages) and >=128 KiB (arm64, 64 KiB page-padded segments for loader-model uniformity).
- **Resource-bound tightness**: static per-step instruction bounds are 1.7x–8.6x measured worst-step counts on small registered programs and 11x–17x on `upper` and `kvsrv` (due to worst-case loop counts, heavier branch arms, and allocation-off worst-case construct weights). Source `p.stackBytes` is 2x–1,340x measured stack, while the post-regalloc `PT_GNU_STACK` bound (`compile_stack_tight`) is 1.0x–1.5x.
- **Compile throughput**: ~5.0–6.6 s for 170 differential test programs across both targets (compiled Lean code on an 8-core host); register allocator ~0.35–0.65 s; checker <0.1 s.
- **Proof burden & safety automation**: measured `(contracts + proofs) / program` line ratios (`Millipede/Meta/Burden.lean`) range from 0.30x (`Reqs`) and 0.50x–0.53x (`Reactor`, `pooltally`) to 1.51x (`Bump`) and 1.89x (`ByteBuf`). Safety census (`scripts/census.lean`, 2026-11-19): 858 definitions — 324 total (no obligations), 160 proved automatically (45 via interval analyzer), 8 hand-proved, and 366 open (all in differential/negative tests; 0 open in `Millipede/`).

**Concrete architectural and verification limitations (`doc/design/limits.md`, `doc/open-claims.md`, `doc/status.md`)**:
- **Narrow program class**: sequential reactors, no heap/recursion/threads/floats/SIMD, only 3 Linux syscalls (`read`, `write`, `exit`), no C FFI bindings or macOS/Windows targets wired up yet (PE32+ and Mach-O writers/loaders exist as standalone modules only).
- **Limited functional specs**: compiler soundness guarantees refinement of the *source trace*, not that the source is right; only 3 programs (`hello`, `revchunks`, `kvsrv`) have end-to-end functional trace theorems carried to compiled bytes.
- **Trusted models & execution gaps**: x64 models were co-simulated only against `qemu-x86_64` (not x64 hardware; e.g., `r11` clobbering by `syscall` is not simulated by qemu, forcing `r11` to stay reserved); Linux short writes and `EINTR` are covered by the adversarial `Oracle` in proofs but never injected in live OS tests; Lean's own compiler/runtime is trusted to execute `compile` except for `exit42` and `hello` (`Accept.lean`).
- **Unbuilt security/protocol features**: information-flow labels / noninterference / constant-time mode, general reactor refinement & global session types, per-value arena brands, analyser-driven constant propagation/check elimination, and CI automation are designed but not built.
- **Author's explicit epistemic caveat (`README.md` L30–L48)**: Graydon Hoare explicitly notes he cannot independently audit most of the 3,000+ LLM-generated theorems and proofs, highlighting human QA and specification comprehension as an unresolved bottleneck even when kernel-checked proofs pass.

## Boundaries

- **Build and test execution (`not examined`)**: `lake build`, `scripts/check.sh`, `scripts/audit.sh`, `scripts/measure.sh`, and `scripts/census.lean` were **not executed** on this host due to host Lean build-slot contention and `/tmp` disk-budget constraints. All runtime execution measurements, co-simulation outcomes, and `check.sh` pass claims are therefore attributed strictly as `documentation` from the repository's own docs (`doc/status.md`, `doc/measurements.md`, `doc/design/limits.md`), not independently reproduced `execution` evidence.
- **Deep proof-term inspection (`not examined`)**: While top-level statements (`Top/Statement.lean`, `Top/Sound.lean`, `Top/SoundA64.lean`), core AST/semantics/checker (`Core/Exp.lean`, `Core/Denote.lean`, `Core/Wf.lean`, `Core/Program.lean`), audit logic (`Meta/Audit.lean`), and representative modules (`Analysis/Domain.lean`, `Extern/Oracle.lean`, `Target/Target.lean`, `Target/X64/Isa.lean`, `Target/A64/Decode.lean`, `Meta/Emit.lean`, `Meta/Sem.lean`, `Meta/Burden.lean`, `Tests/KVRefine.lean`) were inspected directly, the ~55,000 lines of intermediate simulation proofs inside `Millipede/Compile/`, `Millipede/Target/`, and `Millipede/RegAlloc/` were not audited line by line for subtle modelling mismatches (e.g., flag semantics or ELF edge cases).
- **External reception and post-publication commits (`not examined`)**: This report pins commit `4f13d3980a5570177a774e63cfbc95e652dd3cde` (`2026-11-21`). Any subsequent commits, third-party red-team findings, or independent formal audits of `graydon/millipede` are outside the observed snapshot.
- **Adjacent LLM-first PLs (`not examined` at revision pin)**: Other experimental LLM-targeted languages (e.g., MoonBit, Vibe, BAML, Nanolang) and classic verified compilers/DSLs (CompCert, CakeML, Bedrock2, Cogent, Aeneas, Jasmin) are referenced in `doc/design/prior-art.md` as design context, not independently verified subjects in this report.
- **What is `known not to apply`**: Millipede's theorems do *not* claim resistance to side-channel attacks (constant-time mode is unbuilt), do *not* cover programs linked by an external system linker (`elfrel` linking is tested only), do *not* prevent logic bugs or ignored short writes in source specifications, and do *not* cover dynamic memory, concurrency, or recursion.

## Evidence

All primary evidence was acquired on `2026-11-23` from a read-only clone of `https://github.com/graydon/millipede` at commit `4f13d3980a5570177a774e63cfbc95e652dd3cde` (`leanprover/lean4:v4.35.0`, `lake-manifest.json` with `"packages": []`).

- **Thesis, author caveats, and project rules (`documentation`)**:
  - `README.md` L1–L107 (thesis, ignorance caveat, `$50` / ~6h human supervision estimate).
  - `CLAUDE.md` L1–L149 (agent working rules, hard anti-vacuity/axiom rules, Lean proof-style guidelines, prose-audit rules).
  - `doc/design/goals.md` L1–L131; `doc/design/decisions.md` L1–L290 (Decisions 1–30, including Decision 28 `do`-notation reversal, Decision 29 checked-term generics reversal, Decision 30 liveness-aware register allocation); `doc/design/deviations.md` L1–L26 (Deviations 1–16); `doc/design/prior-art.md` L1–L41.
- **Language, embedding, and verification design (`documentation` + `source`)**:
  - `doc/design/language.md` L1–L250; `doc/design/memory.md` L1–L150; `doc/design/embedding.md` L1–L109; `doc/design/obligations.md` L1–L232; `doc/design/arenas.md` L1–L87; `doc/design/modules.md` L1–L146; `doc/design/units.md` L1–L80; `doc/design/world.md` L1–L116; `doc/design/security.md` L1–L100; `doc/design/protocols.md` L1–L85; `doc/design/resources.md` L1–L121.
  - `doc/reference/surface.md` L1–L73; `doc/reference/messages.md` L1–L150.
  - `Millipede/Core/Exp.lean` L1–L180 (`Mem`, `Env`, `Atom`, `Prim`, `Exp`); `Millipede/Core/Denote.lean` L1–L120 (`loopDenote`, `Exp.denote`); `Millipede/Core/Wf.lean` L1–L160 (`Sel.overlap`, `Loan`, `BS`, `BS.access`); `Millipede/Core/Program.lean` L1–L111 (`Program`, `Program.run`, `Program.Safe`, `Program.stackBytes`, `Program.footprint`).
  - `Millipede/Meta/Elab.lean` L1–L140; `Millipede/Meta/Sem.lean` L200–L260 (`@[implemented_by Upto.forInImpl]` at L227); `Millipede/Meta/Burden.lean` L1–L120; `Millipede/Analysis/Domain.lean` L1–L120 (`Itv`, `COp`, `Cmp`, `UB`).
- **Compiler pipeline, soundness theorems, and targets (`source` + `documentation`)**:
  - `doc/design/compiler.md` L1–L250; `doc/design/targets.md` L1–L160; `doc/design/trust.md` L1–L219; `doc/design/limits.md` L1–L162; `doc/roadmap.md` L1–L117.
  - `Millipede/Top/Statement.lean` L1–L108 (`CompileSound.Statement` L42–L51); `Millipede/Top/Compile.lean` L1–L160 (`x64Linux`, `arm64Linux`, `Backend`, `Compile.Options`, `prepA`); `Millipede/Top/Sound.lean` L1–L255 (`Backend.Laws`, `compileWith_sound_of_backend`, `compile_sound`); `Millipede/Top/SoundA64.lean` L1–L120 (`a64Backend_laws`, `compile_sound_arm64`, `compileWith_sound`).
  - `Millipede/Extern/Oracle.lean` L1–L138 (`Call`, `Reply`, `Event`, `Oracle`, `World`); `Millipede/Target/Target.lean` L1–L129 (`Target`, `Machine.run`, `NeverStuck`, `StackWithin`, `StepsWithin`); `Millipede/Target/X64/Isa.lean` L1–L45; `Millipede/Target/A64/Decode.lean` L1–L80 (`decodeWord`).
  - `Tests/KVRefine.lean` L1–L120 (`toStore`, `Refines`, end-to-end refinement of `kvsrv`).
- **Auditing, tooling, and empirical status (`source` + `documentation`)**:
  - `Millipede/Meta/Audit.lean` L1–L298 (`bvDecideMods`, `bvDecideArg`, `bvDecideShape`, `checkBvDecideAxiomM`, `rejectedAxioms`, `#audit`, `#audit_ledger`).
  - `Millipede/Meta/Emit.lean` L80–L136 (`mkEntry` safety/axiom gate, `@[implemented_by evalEmitUnsafe]` at L106); `Millipede/Top/Ledger.lean` L1–L160.
  - `scripts/audit.sh` L1–L87; `scripts/leanq.py` L1–L163.
  - `doc/status.md` L1–L219; `doc/open-claims.md` L1–L164; `doc/measurements.md` L1–L141.
  - Source scan via Python regex over `/tmp/millipede_src` at `4f13d398`: 195 library files (81,070 lines, 2,717 defs/types, 3,006 theorems), 92 test files (24,097 lines, 168 theorems), `0` `sorry`, `0` `axiom`, `0` `native_decide`, `bv_decide` confined to `Millipede/Target/A64/{Decode,Word}.lean` (plus audit/ledger/test references), and 3 `@[implemented_by]` annotations confined to `Millipede/Meta/{Sem,Report,Emit}.lean`.

## Revalidation

To verify whether these findings still hold on a newer revision of `graydon/millipede`, or to upgrade the `not examined` execution boundary to `execution` evidence:

1. **Fast source/hygiene revalidation probe (~2 s, no Lean build required)**:
   ```bash
   git clone --depth 1 https://github.com/graydon/millipede.git /tmp/millipede_reval
   git -C /tmp/millipede_reval rev-parse HEAD
   cat /tmp/millipede_reval/lean-toolchain /tmp/millipede_reval/lake-manifest.json
   grep -rnE '^\s*(private |protected )?(axiom|unsafe )|\b(sorry|native_decide|bv_decide)\b|@\[.*(implemented_by|extern)' /tmp/millipede_reval/Millipede/
   git -C /tmp/millipede_reval diff 4f13d3980a5570177a774e63cfbc95e652dd3cde..HEAD -- \
     Millipede/Top/Statement.lean Millipede/Top/Sound.lean Millipede/Top/SoundA64.lean \
     Millipede/Meta/Audit.lean doc/open-claims.md doc/status.md doc/measurements.md
   ```
2. **Full kernel-checked execution revalidation (requires Lean `v4.35.0` from `lean-toolchain` and sufficient RAM/disk)**:
   ```bash
   cd /tmp/millipede_reval
   ./scripts/audit.sh       # Builds Millipede, runs #audit, checks headline axioms and doc/open-claims.md
   ./scripts/proof-burden.sh
   lake env lean --run scripts/census.lean
   ./scripts/check.sh       # Full build + tests + differential/co-sim + audit (requires qemu-x86_64/arm64 host tools)
   ```
3. **Target-specific diffs to watch**: inspect `doc/design/decisions.md`, `doc/design/deviations.md`, and `doc/open-claims.md` for newly closed claims (e.g., `CompileAccepts.Statement`, C FFI bindings, information-flow labels, or general protocol refinement) and `Millipede/Meta/Audit.lean` (`bvDecideMods`, `stdAxioms`) for any TCB expansion.
