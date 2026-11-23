# Millipede Compiler, Simulation Pipeline, and Audit Architecture in Lean 4

## Summary

At commit `4f13d3980a5570177a774e63cfbc95e652dd3cde`, `graydon/millipede` implements an 81,070-line, 195-module verified compiler and proof environment in Lean 4 (`v4.35.0`, Core and `Std` only) that lowers a deeply embedded imperative language (`Exp Γ t`) to static position-independent x86-64 and AArch64 Linux ELF64 executables with unconditional byte-level soundness (`Millipede.compile_sound` and `Millipede.compile_sound_arm64`). Direct code-level inspection of the compiler pipeline, simulation proofs, audit commands, and elaboration machinery establishes six architectural mechanisms and concrete scaling limits:

1. **Stratified module closures with one subtle metaprogramming seam**: `Millipede.Top.Statement` depends on 22 modules (zero `Lean` or `Meta` imports); `Millipede.Top.Sound` (120 modules) and `Millipede.Top.SoundA64` (125 modules) exclude `import Lean` everywhere, but transitively import `Millipede.Meta.Sem` (via `Compile.LowerLawful` and `Analysis.Loop`), placing `@[implemented_by Upto.forInImpl]` (`Meta/Sem.lean:227`) inside the import closure of `compile_sound`. This leaves Lean's kernel reducer unaffected while affecting compiled evaluation.
2. **Spatial-hole memory refinement instead of separation logic**: `Flat.lower` lowers pure functional lens borrows (`Exp.borrowMut`, `Exp.callRef`, and disjoint element pairs `Place.pair2`) to in-place machine pointers without a separation-logic heap algebra. A per-binder runtime descriptor `SI` (`Compile/LowerInv.lean`) carves a byte-range `Hole` out of the lender's `VarRel` representation while a mutable borrow is live, using `Exp.wf` path-disjointness (`HoleOK`, `HoleAv`) and lexical write masks (`Exp.Restr`) to restore the lender's full representation on borrow exit with zero copying.
3. **Single-shape forward simulation plus amortized step-potential accounting**: Every operational layer (`Program.sem`, `Flat`, `Lin`, and `Target`) instantiates one deterministic state-machine record `Sem` (`Compile/Sem.lean`) in which `exit`-halted states stutter to themselves, reducing safety, trace equality (`TraceEq`), and per-reactor-step instruction budgets (`StepsWithin`) to `FwdSim` composition (`FwdSim.comp`, `FwdSim.schedule`) plus an integer potential certificate `N : Nat → Nat → Option Int` checked locally by `Sel.budgetOk` and pinned to `0` at the reactor loop header (`rcRun_boundary`).
4. **Dual-use register-allocation checker for liveness self-simulation**: Rather than verifying a separate backward-dataflow liveness pass, `RegAlloc.Live.of` runs the Rideau–Leroy-style local validator `RegAlloc.check P P (idMaps lv)` on an allocated program against itself using identity maps restricted to live locations (`{(x, x) | x ∈ live}`). Soundness of `RegAlloc.check` immediately yields a reflexive-transitive dead-location self-simulation (`Live.flex : Flex P`), justifying caller-saved register clobbers (`clobOk`), selective call saves (`keepCall`), and zero-stack-word caller-saved registers (`Sel.frameW`).
5. **Two root-caused Lean 4.35 kernel-checking blowups**: First, kernel evaluation (`decide +kernel`) of `compile` on `revchunks` fails to finish within 20 minutes (`CompileAccepts.Statement`) because `Sel.potential` (`Target/Budget.lean:119–184`) mutates `Array (Array (Option Int))` via `Array.modify`/`Array.set!`, which executes in $O(1)$ in compiled C (`#guard`) but reduces in Lean's kernel as $O(N)$ linked-list `List` traversals while recomputing selected block lengths on every sweep. Second, `mp def` normal-form equivalence (`f.exp_denote`) scales roughly cubically in the number of sequential jumping statements (`return`/`break`/`continue`) because `joinStmt` (`Meta/Elab.lean:926–1005`) nests monadic `let`/`ite` tuple-handback wrappers whose `simp` congruence proofs traverse $O(K)$-deep `Env` cons-lists and right-nested tuple lenses.
6. **Defense-in-depth axiom auditing with bounded in-process blindspots**: `#audit` (`Meta/Audit.lean`) inspects all public and `_private` constants, confines `bv_decide` to `Target/A64/{Word,Decode}.lean`, blocks `Millipede.*` `@[implemented_by]`/`@[extern]` smuggling into `bv_decide` via `bvDecideArg`, and re-runs `Meta.nativeEqTrue` (backed by 9 `addDecl` forgery tests in `Tests/Audit.lean`). Because `#audit` runs in-process on loaded `.olean` files, it trusts `.olean` integrity, does not inspect global `@[csimp]` overrides on `Init`/`Std` definitions, and relies on regex matching in `scripts/audit.sh` to enforce the `*.Statement` open-claims ledger.

## Applicability

- **Direct subject**: `graydon/millipede` at immutable Git commit `4f13d3980a5570177a774e63cfbc95e652dd3cde` (`2026-11-21`, 2 commits in public history above `73f84a0469b150bf6f058b1ef88e9997c71e7d76`), pinned to `leanprover/lean4:v4.35.0` with zero external Lake dependencies (`lake-manifest.json` has `"packages": []`).
- **Relationship to companion corpus coverage**: Whereas `reports/millipede-llm-era-verified-systems-language-in-lean/` surveys Millipede's language thesis, surface restrictions, feature set, and documented runtime measurements, this report dissects the internal compiler data structures, module dependency graph, simulation and memory-refinement invariants, certificate checkers, audit implementation, and Lean 4.35 proof-scaling mechanics directly from `.lean` and `scripts/*` source.
- **Evidentiary scope**: All type signatures, invariants, module dependency closures, proof-length distributions, tactic counts, recursion audits, and audit/script mechanisms are established by direct static inspection (`source`) or logical deduction from inspected definitions (`derived`). Build, test, and co-simulation scripts were not executed on the observation host (`not examined`); timing and binary-size measurements cited for context carry `documentation` basis from `doc/measurements.md` and `doc/open-claims.md`.

## Findings

### 1. Subsystem Stratification, Import Closures, and Recursion Discipline

Basis: source (complete import graph and declaration scan across all 195 `.lean` files in `Millipede/`).

The 81,070-line `Millipede/` library partitions into twelve top-level subdirectories with a nearly acyclic architectural layering:

| Subsystem | Files | Lines | Top-level `theorem`/`lemma` decls | Direct `Millipede.*` subsystem dependencies | Role in pipeline |
|---|---:|---:|---:|---|---|
| `Extern/` | 1 | 138 | 4 | *(none)* | `Call`, `Reply`, `Event`, `Oracle`, `World` (`Oracle.lean`) |
| `Core/` | 17 | 6,202 | 238 | `Extern` | De Bruijn ANF `Exp`, `Ty`, `Shape`, `Data`, `Place`, `Exp.denote`, `Exp.wf` (`WfSound`), `Exp.cost`, `Exp.stackBytes` |
| `Opt/` | 5 | 1,219 | 50 | `Analysis`, `Core` | Verified AST rewrites (`inline`, `fold`, `dce`, `strength`) + `Program.Within` cost/stack gate |
| `Analysis/` | 5 | 2,269 | 115 | `Core`, `Meta` (`Meta.Sem` only) | Verified interval (`Itv`), comparison (`Cmp`), and affine loop-bound (`UB`) abstract interpreter |
| `Compile/` | 42 | 24,630 | 1,196 | `Core`, `Extern`, `Meta` (`Meta.Sem`), `Object`, `Target`, `Top` (`Top.Statement`) | `Sem`/`FwdSim`, `Flat` memory lowering (`Lower*.lean`), `Lin` linearization, generic `Asm`/`Assemble` |
| `RegAlloc/` | 11 | 5,221 | 191 | `Compile`, `Target`, `Top` (`Top.Sound` in `RegAlloc.Compile` helper) | Untrusted greedy/liveness allocator, `RegAlloc.check`, `Live.flex`, `Lock`, and arm64 register selection (`A64Reg*`) |
| `Target/` | 38 | 15,096 | 757 | `Compile`, `Core`, `Extern`, `Object`, `RegAlloc`, `Top` (`Top.Compile` in `X64.Pipeline`) | Shared selection/budget proofs (16 files, 6,416L), x86-64 ISA/selector (13 files, 5,882L), AArch64 ISA/codec/slot selector (9 files, 2,798L) |
| `Object/` | 23 | 7,795 | 350 | `Compile`, `Target`, `Top` (`Top.Compile` in `ElfRel.Objects`) | Generic `Obj`/`Link`/`Image`, verified static `Elf` writer/loader, plus standalone `ElfRel`, `Pe`, `MachO` |
| `Format/` | 5 | 2,377 | 142 | `Lib` | Untyped wire-format `Fmt`/`Val` parser/serializer combinators and canonicality/round-trip proofs |
| `Lib/` | 9 | 2,086 | 105 | `Core`, `Meta` | Verified Millipede libraries (`Alloc`, `Pool`, `Bump`, `Slice`, `ByteBuf`, `Units`, `Cap`) |
| `Top/` | 14 | 2,121 | 71 | `Compile`, `Core`, `Lib`, `Meta`, `Object`, `Opt`, `RegAlloc`, `Target` | `CompileSound.Statement`, `compile`/`Backend`, `compile_sound`, `compile_sound_arm64`, `StackTight`, `NoCalls`, `Accept`, `Ledger` |
| `Meta/` | 25 | 11,916 | 113 | `Analysis`, `Core`, `Format`, `Lib`, `Top` (+ `Lean`) | `mp def` `do`-elaborator (`Elab.lean`, 4,355L), `mp_auto`, `FormatGen`, `#audit`, `#mp_report`, `Burden` |

*(Note: counting lines matching `^\s*(private |protected )?(theorem|lemma)` yields 3,006 declarations; including declarations preceded on the same line by `@[simp]`, `@[spec]`, or `omit [...]` yields 3,332 top-level `theorem`/`lemma` declarations across `Millipede/`.)*

Programmatic transitive-import analysis reveals three structural properties of the trusted and proved closures:
- **Minimal statement cone**: `Millipede.Top.Statement` transitively imports **22** `Millipede.*` modules (`Extern.Oracle`, 13 `Core.*` modules, `Compile.{Sem,Flat}`, `Object.{Image,Format}`, and `Target.{Machine,Isa,Target}`) and **zero** external modules beyond `Init`. Auditing the meaning of `CompileSound.Statement` for a concrete `Target` requires inspecting those 22 modules plus the target's `Target.{X64,A64}` ISA/ABI definitions and `Object.Elf.{Load,Format}` (~35 modules total).
- **`Lean` isolation vs. `Millipede.Meta.Sem` crossover**: Exactly 24 files in `Millipede/` import `Lean`, all inside `Millipede/Meta/`. However, `Millipede.Top.Sound` (120 modules) and `Millipede.Top.SoundA64` (125 modules) both transitively import `Millipede.Meta.Sem` (`Compile.LowerLawful` imports `Meta.Sem` for `Flat.CtorLaw.vec` and built-in constructors `Ctor.{pairMk,vec,fill,slotsEmpty}` at `Meta/Sem.lean:579–664`, while `Analysis.Loop` imports `Meta.Sem` for `loopDenote_invJ`). `Meta/Sem.lean` omits `import Lean`, but declares `@[implemented_by Upto.forInImpl] def Upto.forIn` (`Meta/Sem.lean:227`), placing one runtime replacement attribute inside the module closure of `compile_sound`. Because Lean's kernel ignores `@[implemented_by]` and unfolds `Upto.forIn` to `ForIn.forIn (List.range r.bound)`, kernel proof checking is unaffected; compiled `#eval` execution uses `Upto.forInImpl` to avoid allocating `2^64`-element `List.range` structures.
- **Strict structural recursion everywhere outside `Meta/`**: Across all 195 library files, there are **0 `noncomputable` declarations**, **0 `partial` declarations outside `Millipede/Meta/`** (all 95 `partial def`s reside in `Millipede/Meta/`), and only **2 `termination_by` clauses** in the entire repository (`Upto.loopImpl` at `Meta/Sem.lean:219` and an 8-byte helper at `Target/SelMem.lean:360`). Every semantic evaluator, borrow checker, certificate validator, assembler, linker, and loader uses structural recursion (or explicit `Nat` fuel) over plain inductive types so Lean's kernel reduces closed applications without blocking on well-founded fixpoint equations (`WellFounded.fix`).

### 2. End-to-End Compiler Pipeline and Spatial-Hole Pointer Refinement

Basis: source (`Millipede/Core/{Exp,Denote,Wf,WfSound}.lean`, `Millipede/Opt/Pass.lean`, `Millipede/Compile/{Flat,Lower,LowerInv,LowerSound,HandBack,LowerCallRef,Lin,Linearize,LinearizeProof}.lean`, `Millipede/RegAlloc/{Check,Live,Lock,Alloc,IdOps}.lean`, `Millipede/Target/{SelDriver,SelCases,PMove,X64/Select,A64/Select}.lean`, `Millipede/Object/{Obj,Link,LinkProof,Elf/Laws}.lean`).

#### 2.1 Representation Lowering Sequence
`Millipede.compileWith` (`Top/Compile.lean:291–312`) transforms a closed first-order `Program` through seven concrete representations:

1. **Core (`Exp Γ t`, `Core/Exp.lean`)**: Intrinsically typed de Bruijn A-normal form (21 constructors) where `Env Γ` is an inductive heterogeneous list (`Core/Exp.lean`), `&mut` borrows (`borrowMut p body k`) and reference calls (`callRef`) pass values functionally and splice returned tuples back via `Place.set` / `RArgs.writeBack`, and `Compile.checks p` (`Top/Compile.lean:169–170`) decides `p.init.certified && p.step.certified && p.wf`.
2. **Core Optimization (`Opt/Pass.lean`, `Opt/Rules.lean`)**: Runs two rounds of `[inline, fold, dce, strength]`. Each `Opt.Pass` proves only value/world preservation (`Pass.denote`) and safety preservation (`Pass.safe`). Resource non-increase is enforced dynamically by `Pass.apply` (`Opt/Pass.lean:59–67`):
   ```lean
   def Program.Within (q : Program) (κ : CostModel) (φ : FrameModel) (p : Program) : Bool :=
     decide (q.init.cost κ .copy ≤ p.init.cost κ .copy) &&
       decide (q.step.cost κ q.stepHb ≤ p.step.cost κ p.stepHb) &&
       decide (q.stackBytes φ ≤ p.stackBytes φ)
   ```
   If downstream lowering, selection, or budget checking rejects an optimized candidate, `Compile.firstOk` (`Top/Compile.lean:276–303`) retries progressively shorter pass prefixes down to the unoptimized source `p`.
3. **Flat (`Compile/Flat.lean`, `Compile/Lower.lean`)**: Untyped 64-bit frame slots (`Frame := Nat → UInt64`), byte-addressed static memory (`Heap := UInt64 → UInt8`, reactor root at address `0`), structured control (`Stmt.seq`, `ite`, `while`, `call`), and explicit cost ticks (`Stmt.tick`). Never-borrowed scalar/struct values of $\le 4$ words with no arrays or `Slots` (`Ty.slotTy`) stay in frame slots (`Loc.slot`, Decision 20); all other values and lent places reside in byte memory (`Data.reprBytes`). Constructors $\ge 64$ bytes filling literals or copying single large arguments lower to word-copy loops (`LowerFill.lean`).
4. **Lin (`Compile/Lin.lean`, `Compile/Linearize.lean`)**: Flattens `Flat.Stmt` into numbered functions `P.funs : List Lin.Fn` with PC-indexed straight-line instructions, labels (`jmp`, `jz`), and non-recursive calls (`g < i` enforced by `instrWf` at `RegAlloc/Check.lean:158`).
5. **Validated Register Allocation (`RegAlloc/`)**: Rewrites `RegAlloc.idOps` (`bor x, x, 0` / `mul x, x, 1` → `mov x, x`) and runs untrusted `Alloc.allocate` to map frame slots into `[0 .. k)` callee-saved registers (`rbx rbp r12..r15` on x64; `x19..x28` on arm64), `[k .. k+c)` caller-saved registers (`r8 r9 r10 rdi rsi rdx` on x64; `x4..x7 x10..x14 x8 x3..x0` on arm64), and `[k+c .. F)` stack frame words (`Sel.frameW k c F := min F k + (F - (k + c))`). Checked by `RegAlloc.check` + `frameOk`, with automatic fallback (`Compile.prepA`) from `(k, c)` to `(k, 0)` to unallocated `P` if `check` or `select` refuses.
6. **Symbolic Assembly (`Compile/Asm.lean`, `Target/SelDriver.lean`)**: Maps each `Lin.Fn` `i` to `Asm.Fn arch` (`mp_f<i>`) with one basic block per `Lin` PC, constant buffers `mp_d<i>_<pc>` in `.rodata`, and static `.bss` symbol `mp_mem` of size `p.memBytes`. Parallel moves (`Target/PMove.lean`) sequentialize argument/return/syscall register permutations using a single scratch register (`r11` on x64, `x9` on arm64) in $\le 2n + 1$ steps.
7. **Object, Link, and Static ELF64 (`Compile/Assemble.lean`, `Object/Link.lean`, `Object/Elf/Write.lean`)**: Encodes `.text` resolving intra-function PC-relative jumps and emitting `.text` relocations for inter-function/data symbols; places page-aligned `.text` (`PF_R|PF_X`), `.rodata` (`PF_R`), and `.bss` (`PF_R|PF_W`) segments without `W+X` overlap; records the post-regalloc stack bound in `PT_GNU_STACK`; and serializes static ELF64 bytes (`4 KiB` page alignment on x64; `64 KiB` page-padded segments on arm64 so files load uniformly on 4/16/64 KiB kernels).

#### 2.2 Spatial `Hole` Invariant for Zero-Copy Mutable Reference Lowering
The largest proof subsystem in the repository (`Millipede/Compile/Lower*.lean`, 27 files, ~21,600 lines) justifies compiling pure value-passing `Exp.borrowMut` and `Exp.callRef` into raw machine pointers without separation logic. Its invariant (`Compile/LowerInv.lean`) tracks four structures per de Bruijn binder:
- **Static slot `Loc`** (`own o`, `slot o k n`, `ref o` [8-byte pointer], or `ref2 o` [two 8-byte pointers for `&mut (a[i], a[j])`]) and **runtime storage info `SI`** (`LowerInv.lean:50–57`):
  ```lean
  structure Hole where
    a : Nat; len : Nat; path : List Sel
  structure SI where
    A : Nat
    hole : Option Hole := none
    ext : Option Nat := none
    snd : Option (Nat × Nat) := none
  ```
- **Punctured byte representation `VarRel`** (`LowerInv.lean:499–502`): Memory `h : Heap` matches `Data.reprBytes v B` at every byte `i < s.sz t` **outside** `s.inHole (s.at i)`:
  ```lean
  def VarRel (h : Heap) (t : Ty) (v : t.carrier) (s : SI) : Prop :=
    ∃ B : List UInt8, Data.reprBytes v B ∧
      (∀ i, i < s.sz t → ¬ s.inHole (s.at i) → h (UInt64.ofNat (s.at i)) = B.getD i 0) ∧
      ∀ e, s.ext = some e → s.snd = none → ViewOK t v e
  ```
- **Layout disjointness `Lay` and path non-interference `HoleOK` / `HoleAv`** (`LowerInv.lean:393–493, 558–559`): While binder `i` lends contiguous sub-place `p` (`[H.a, H.a + H.len)`) as `&mut`, the lender's writable flag in `W : List Bool` becomes `false` (`noW W`), `Compat` permits the new `&mut` binder's storage to overlap binder `i` *only* inside `sᵢ.inHole`, `HoleOK` ensures any non-overlapping path (`Sel.overlap H.path q.path = false`) maps outside `[H.a, H.a + H.len)` via certified `Lens.Lawful`, and `HoleAv` (`Exp.Avoids`, derived from `Exp.wf` in `Core/WfSound.lean`) guarantees the borrow body never touches an overlapping path on the lender.
- **Zero-copy handback (`HandBack.lean`, `BackOk.lean`)**: Because the borrow body mutates `[H.a, H.a + H.len)` in place and returns the borrow binder at its tail (`BackOk`), the heap at `[H.a, H.a + H.len)` already represents the updated sub-value `v'`, which `Lens.Lawful` (`splice bs (lensOff l) vb`) stitches straight back into the lender's `B` to re-establish unpunctured `VarRel` (`hole := none`) with zero runtime memory traffic.

### 3. Soundness Theorem Factoring, Forward Simulation, Liveness Self-Simulation, and Step Budgets

Basis: source (`Millipede/Top/{Statement,Sound,SoundA64,StackTight,NoCalls}.lean`, `Millipede/Compile/Sem.lean`, `Millipede/RegAlloc/{Check,Live,Lock,Sound}.lean`, `Millipede/Target/{Budget,SelSim,SelCases}.lean`, `Millipede/Compile/AssembleLaws.lean`, `Millipede/Object/{LinkProof,Elf/Laws}.lean`).

#### 3.1 Non-Terminating `Sem` and Single-Direction `FwdSim`
To avoid splitting terminating, diverging, and stuck runs across five compiler passes, `Compile/Sem.lean:38–42` gives every operational layer one deterministic small-step interface:
```lean
structure Sem where
  State : Type
  step : Oracle → State → Option State
  events : State → List Event
  clock : State → Nat
```
Calling `exit` sets `world.halted = true`, after which `step` transitions `s ↦ some s` with `events` and `clock` unchanged; `step ω s = none` occurs exclusively on UB/faults (undecodable bytes, page permission/W^X fault, misaligned/out-of-bounds access, or unmodeled syscall). Consequently:
- Every safe execution is infinite (`NeverStuck ω s := ∀ n, (S.run ω s n).isSome`).
- Because `step` is deterministic (`State → Option State`), forward simulation (`FwdSim S T ω`, `Compile/Sem.lean:187–197`) implies both `T.NeverStuck` (`FwdSim.neverStuck`) and trace limit equality `TraceEq` (`FwdSim.traceEq`, bi-directional prefix cofinality on `Nat → List Event`) **without** CompCert-style backward simulations or receptiveness/determinate-target side proofs.
- Stuttering source steps (`n = 0` target steps, such as entering `Stmt.seq`/`Stmt.while` in `Flat → Lin` or executing zero-instruction `Lin.Instr.tick` / coalesced `mov r, r` in `Lin → Machine`) are bounded by well-founded indices composed lexicographically via `Prod.Lex (Relation.TransGen s₂₃.lt) s₁₂.lt` (`FwdSim.comp`, `Compile/Sem.lean:243–274`), using subtraction-free clock inequalities `T.clock t' + factor * S.clock s ≤ T.clock t + factor * S.clock s'`.
- Capability isolation (`Program.NoCalls.machine`, `Top/NoCalls.lean:18–26`) transfers source symbol absence `p.NoCalls S` (`Exp.syms`) to all machine traces in 8 lines directly from the `TraceEq` clause of `CompileSound.Statement`.

#### 3.2 Two-for-One Register-Allocation and Liveness Validation (`Live.flex`)
`RegAlloc.check P P' maps` (`RegAlloc/Check.lean:178–180`) checks per-PC `LocMap := List (Nat × Nat)` lists `(srcSlot, dstLoc)` in one pass over `(P, P')`, producing `Lock P P' k c` (`RegAlloc/Lock.lean:103–115`). To support caller-saved registers and omit dead caller saves without verifying a dataflow fixpoint solver, `RegAlloc/Live.lean:41–68, 176–193` feeds the allocated program `P` into **the same `RegAlloc.check` against itself**:
```lean
def idMaps (lv : LiveSets) : List (List LocMap) := lv.map (·.map (·.map fun x => (x, x)))
def of (P : Prog) : Option LiveSets :=
  let c := compute P
  if check P P (idMaps c) then some c else none
```
When `check P P (idMaps c) = true`, `step_sim` (`RegAlloc/Sound.lean`) yields a reflexive-transitive self-simulation `Live.flex P : Flex P` relating any two `Lin.State`s that agree on `liveAt lv fn pc` and on suspended callers' `keepCall` sets. Shared instruction selection (`Target/SelCases.lean:83–93`) then proves `StepOkAt (Live.flex P)`, allowing any instruction `ins` passing `clobOk` (`∀ x ∈ liveAt lv i (pc+1), !kill ins x || defs P ins x`) to clobber dead caller-saved registers (`R_kill`) and allowing `call` to save only `keepCall` (`R_call`).

#### 3.3 Amortized Potential Certificates for Per-Reactor-Step Instruction Bounds
At the reactor source level (`Program.sem p ω κ`, `Top/Statement.lean:70–75`), state `k : Nat` counts completed reactor steps (`0` before `init`, `k + 1` after step `k`) and `clock k` is `costPrefix p ω κ k = ∑_{j < k} p.stepCost j ω κ`. Down to `Lin`, `Flat.lowerSim`, `Lin.linearize_sim`, and `L.sim` compose with `factor = 1`, yielding `Lin` step times `μ k` via `FwdSim.schedule` (`Compile/Sem.lean:347–379`, constructed via `@Nat.rec` and `Classical.choose`) at which `Lin.clockAt (μ (k+1)) - Lin.clockAt (μ k) ≤ p.stepCost k ω κ`.

Bridging `Lin` ticks (where only `.tick t` advances `Lin.clock` by `t.cost κ`, while `.mov`/`.bin`/`.call`/`.ret` advance `Lin.clock` by `0` yet execute $\ge 1$ machine instructions) to machine instructions uses an **amortized potential** (`Target/Budget.lean:58–104`, `Target/SelSim.lean:339–509`):
- A certificate `N : Nat → Nat → Option Int` assigns an integer credit/debt `N i pc` to each reachable `(fn, pc)`.
- `Sel.instrOk` verifies locally at every instruction that `C.ins + N(succ) ≤ N(here) + tickWeight`, splits call/return costs across frames via `stackPot` (`(resLen P g : Int) + N caller (pc+1)` constrained $\ge 0$ so an early `exit` inside a callee never discards negative debt!), checks `C.entry P + N main 0 ≤ 0`, and **forces `N i pc = 0` at every `jz (.imm u)` with `u ≠ 0`** (`Budget.lean:66`).
- Because the reactor's outer infinite loop compiles to `jz (.imm 1) l` at `stack = []` (`memBoundary`, `SelSim.lean:525–540`), `rcRun_boundary` (`SelSim.lean:497–508`) proves total state potential `q = pot P' N u = 0` at every reactor boundary `μ (k + 1)` (while `q ≤ 0` initially), telescoping `(M.clockAt (marks (k+1)) - M.clockAt (marks k)) ≤ Lc (μ (k+1)) - Lc (μ k) ≤ p.stepCost k ω κ` (`select_lower_cost`, `SelSim.lean:569–664`).

#### 3.4 Algebraic Laws at the Byte Layer (`Assemble`, `Link`, `Elf`) and `Backend.Laws`
Below `Asm`, Millipede abandons step-by-step state-machine simulation in favor of compositional functional laws:
- **Assembler (`Compile/AssembleLaws.lean`)**: `Assembler.Laws` states 5 per-instruction properties (`isa`, `size`, `sec`, `resolve_size`, `spec`), lifting to `assemble_text` (relocated `.text` bytes decode at every function/block offset to the resolved `Asm` instructions). Variable-length x86-64 uses `AssembleProof.lean`; fixed 4-byte AArch64 shares `AssembleWord.lean`.
- **Linker & ELF64 (`Object/LinkProof.lean`, `Object/Elf/Laws.lean`)**: `Link.link_assemble` proves `Asm.Prog.Loaded`, zeroed `.bss` bounds, and `W^X` disjoint pages (`link_wxorx`); `Elf.parse_write` proves `write img = .ok bs → parse bs = some img`, yielding `load_write`.
- **Backend interface (`Top/Sound.lean:34–46, 151–167`, `Top/StackTight.lean:34–57`)**: `Backend.Laws` packages just `load_write` and `run`, allowing `compileWith_sound_of_backend` to compose `Opt.Sim`, `Compile.checks`, `Flat.lower`, `Lin.lower_linearize_stackBytes_le`, and `Backend.Laws` in 16 lines for both targets and all option flags (`compile_sound`, `compile_sound_arm64`, `compileWith_sound`), while `Backend.StackLaw` proves `compile_stack_tight` against the smaller post-regalloc `img.stackSize` (`≤ p.stackBytes t.φ`).

### 4. Audit, Verification-Burden, and Mutation-Teeth Engineering

Basis: source (`Millipede/Meta/{Audit,Emit,Burden}.lean`, `Millipede/Top/Ledger.lean`, `Tests/{Audit,Ledger}.lean`, `scripts/{check,audit,run-tests,cosim}.sh`).

#### 4.1 `#audit` and Structural `bv_decide` Re-Verification (`Meta/Audit.lean`)
`#audit` (`Meta/Audit.lean:180–277`) iterates over `env.constants.toList`, matching `isOurs` (`Millipede.*` or the current module) and stripping `_private` prefixes (`privateToUserName`) so private axioms/theorems cannot hide. For each declaration, `collectAxioms` must contain only `stdAxioms := [propext, Classical.choice, Quot.sound]`, except that `bvDecideMods := [Millipede.Target.A64.Word, Millipede.Target.A64.Decode]` may introduce per-use `bv_decide` axioms (`7` theorems in `A64/Word.lean` plus `parse_encode` via `a64_parse_tac` in `A64/Decode.lean`).

Because an axiom's `_native.bv_decide.ax_*` name can be forged via `Lean.addDecl`, `checkBvDecideAxiomM` (`Meta/Audit.lean:79–134`) enforces four checks before accepting any `_native` axiom `a`:
1. **Owner & module match**: `a` must be universe-monomorphic, safe, and named `P._native.bv_decide.ax_*` where `P` is a `.thmInfo` in the same module `m` (`m ∈ bvDecideMods`).
2. **Exact equation shape**: `a`'s type must be `@Eq Bool (Std.Tactic.BVDecide.Reflect.verifyBVExpr x c) Bool.true`.
3. **Constant-purity filter (`bvDecideArg`, L83–93)**: `x` (`P._expr_def_*`) and `c` (`P._cert_def_*`) must be monomorphic definitions in `m` whose unfolded bodies `d.value` satisfy `(d.value.getUsedConstants.filter (isOurs env)).isEmpty`—blocking user `@[implemented_by]` or `@[extern]` functions in `Millipede.*` from creating a kernel-vs-compiled evaluation discrepancy inside `verifyBVExpr`.
4. **Independent re-execution**: `#audit` rebuilds `mkApp2 verifyBVExpr xv cv` and runs `withoutModifyingEnv <| Meta.nativeEqTrue` to re-verify that compiled execution returns `true`. `Tests/Audit.lean` constructs 9 adversarial `addDecl` test cases (`sorryAx`, user axiom, out-of-module `bv_decide`, `_private` disguised `_native` axiom of `False`, and forged `verifyBVExpr` with an empty certificate `""`) under `#guard_msgs`.

**Architectural audit boundaries identified in source (`source` + `derived`)**:
- *In-process `.olean` trust*: `scripts/audit.sh` runs `lake env lean --stdin` (`import Millipede`), mapping compiled `.olean` files directly into the auditing process rather than exporting declarations to an out-of-process kernel checker.
- *Global `@[csimp]` blindspot*: `bvDecideArg` checks `d.value.getUsedConstants.filter (isOurs env)`, which catches direct references to `Millipede.*` constants, but does not inspect Lean's `CSimp` compiler-rewrite extension; an unsound `@[csimp]` theorem declared in an imported module rewriting an `Init`/`Std` function called internally by `verifyBVExpr` would leave `d.value.getUsedConstants` clean while altering `Meta.nativeEqTrue` compilation.
- *Regex-based open-claims gate*: `scripts/audit.sh:73–86` enforces Decision 23 by grepping `def [A-Za-z0-9_.']+\.Statement\b` across `Millipede/` and `Tests/` and checking via regex that either `theorem ... : ... <Name>` exists in `Millipede/` or `- \`<Name>\` —` appears in `doc/open-claims.md`. Unproved propositions not named `*.Statement`, or type aliases shadowing the suffix, are outside that textual check.

#### 4.2 Safety-Gated Emission, `.ledger.txt` Cross-Checks, `Burden.lean`, and `--selftest` Teeth
- **Emission gate (`Meta/Emit.lean:74–94`)**: Both `#mp_compile` and `mp_entry%` resolve `<p>.safe`, kernel-typecheck `Entry.mk ... p p.safe` against `p.Safe`, and run `Audit.rejectedAxioms (p ++ `safe)`, refusing binary emission if `p.safe` is missing or depends on `sorryAx`/unapproved axioms.
- **Deterministic `.ledger.txt` + existence tests (`Top/Ledger.lean`, `Tests/Ledger.lean`)**: `Millipede.ledger` renders a plain-text assumption ledger naming `p`'s externs (`Exp.externs`), `CompileSound.Statement` theorem (`compile_sound`, `compile_sound_arm64`, or `compileWith_sound`), numeric `stackBytes` and `stepCost`, backend register/selector configuration (`backendText`), and target-specific trusted models with their backing test scripts. `Tests/Ledger.lean` parses rendered ledgers and `#guard`s that every cited `scripts/*` and `Tests/*.lean` path exists on disk, that arm64 ledgers never claim `under qemu`, and that cited `bv_decide` files match `Audit.bvDecideMods`. (`Ledger.openClaims` at `Top/Ledger.lean:46` is unconditionally `[]` because `compile_sound` itself has no open hypotheses.)
- **Zero-dependency burden classifier (`Meta/Burden.lean`)**: Imports only `Init` so `lake env lean --run scripts/burden.lean` runs without building the library, classifying non-comment/non-directive lines into `program`, `contracts` (`: Prop` defs, `mp interface`, `requires`/`ensures`/`invariant`), and `proofs` (`theorem`/`lemma`/`example`/`mp prove`), reporting `(contracts + proofs) / program` as a library-design signal rather than a failing gate (Decision 18).
- **Single-build parallel test runner with mandatory `--selftest` mutation teeth (`scripts/run-tests.sh`, `scripts/audit.sh:47–67`)**: `run-tests.sh` runs one `lake build` of all 13 test binaries/targets to avoid Lake lock races, then launches 39 shell stages concurrently (`cosim.sh`, `a64-cosim.sh`, `a64-encode-check.sh`, `differential.sh`, `differential-a64.sh`, `mpc-check.sh`, `layout-check.sh`, `loader-a64.sh`, `bound-check.sh`, `format-check.sh`, `pe-check.sh`, `macho-check.sh`, `elfrel-check.sh`, `leanq selftest`), running nearly every model check both normally and with `--selftest` (e.g., `cosim.sh --selftest` injects 10 distinct encoder/ISA-model bugs and requires every one to fail `cmp`; `audit.sh` seeds a temporary `mp.selftest.doMutant` file to verify its own mutant-leak scanner).

### 5. Lean 4.35 Proof-Engineering Architecture, Scaling Bottlenecks, and `Meta/` Tooling

Basis: source (`Millipede/Meta/{Elab,Auto,Analyse}.lean`, `Millipede/Analysis/{Domain,Sound}.lean`, `Millipede/Target/{Budget,X64/Budget}.lean`, `Millipede/Top/Accept.lean`, `scripts/leanq.py`, `CLAUDE.md`, and full-library AST/tactic census).

#### 5.1 Quantitative Proof Profile Across 3,332 Library Theorems
Scanning all 3,332 top-level `theorem`/`lemma` declarations across `Millipede/` establishes how proofs stayed compact at 81k LOC:
- **Proof size distribution**: 2,740 tactic-mode (`by`) and 592 term-mode proofs; median length is **6** non-blank/non-comment lines (`44.7%` $\le 5$ lines, `82.4%` $\le 15$ lines, 90th percentile = `25` lines, 99th percentile = `86` lines). Only **79 theorems (`2.4%`)** exceed `CLAUDE.md`'s 60-line refactoring guideline.
- **Where proof mass concentrates**: The longest theorems cluster at multi-argument memory placements and ABI call/return sequences—`Flat.msound_mk` (`LowerCalls.lean:841`, 247L), `Analysis.Exp.an_sound` (`Analysis/Sound.lean:257`, 200L), `A64Reg.run_retR` / `run_callBlock` / `simRet` / `simCall` (`RegAlloc/A64RegCall.lean`, 114–159L), `A64Reg.selOps_ext` / `selOps_laws` (`A64RegProof.lean`, 117–142L), `Flat.place_set` (`LowerPlace.lean:999`, 137L), `Flat.msound_callRef` (`LowerCallRef.lean:1538`, 124L), and `X64.sim_call` / `sim_ret` (`Target/X64/SelectCall.lean`, 105–107L). Notably, shared `Target/Sel*.lean` (6,416L) absorbs CFG, liveness, stack, and budget reasoning once, keeping fixed-width `Target/A64/` + `RegAlloc/A64Reg*` (6,214L combined across 24 allocated registers) comparable in size to variable-length `Target/X64/` (5,882L across 12 allocated registers).
- **Tactic mix and `grind` discipline**: Across library theorems, `simp` (6,593 occurrences), `rw` (3,886), `omega` (3,775), `rfl` (3,665), `exact` (3,632), `obtain` (2,018), `cases` (1,757), `refine` (922), `split` (806), and `decide` (610) dominate, while Lean 4.35's `grind` appears 101 times (for example closing 8 instruction cases of `Sel.pot_step` in 7 lines at `Target/SelSim.lean:387–393` and unpacking `Elf.write_inv` in 1 line at `Object/Elf/Laws.lean:128`). Global `@[grind]` attributes on recursive definitions are avoided (`CLAUDE.md` rule 8) because `UInt64`/`sext32` address arithmetic triggers $>1\text{ s}$ E-matching blowups; definitions are passed explicitly per call (`grind [Lin.exec, pot, ...]`).
- **DAG-memoized subterm instantiation in `mp_auto` (`Meta/Auto.lean:65–117`)**: Verification conditions over sequential calls share nested state subterms heavily (`let s₁ := f₀ s₀; let s₂ := f₁ s₁; ...`), making naive tree traversal exponential in call-chain length; `appsOf` uses `Expr.forEachWhere` (which memoizes visited `Expr` pointers) before instantiating `g.post` hypotheses in `mp_inst_posts`.

#### 5.2 Root Cause 1: `Sel.potential` Kernel Reduction Timeout (`>20 min` on `revchunks`)
`Millipede/Top/Accept.lean:28–43` proves `(compile p t).toBool = true` by `decide +kernel` (with `maxRecDepth 100000`) for `exit42` and `hello`, eliminating trust in Lean's compiler for those two binaries. For `revchunks`, kernel reduction fails to terminate within 20 minutes, leaving `CompileAccepts.Statement` (`Accept.lean:89–90`) as the repository's sole unproved `.Statement`.

Inspecting `Target/Budget.lean:119–184` and `Target/X64/Budget.lean:22–53` reveals why:
- `Sel.potential` represents its DP table as `Table := Array (Array (Option Int))`, initializing nested arrays via `Array.replicate`, updating every PC in every backward sweep via `T.modify i fun r => r.set! pc v` (`Budget.lean:166`), and checking convergence via `T' == T` up to `P.funs.length + 64` sweeps (`iterate`, `Budget.lean:172–183`).
- In compiled C execution (`#eval` / `#guard`), Lean's runtime represents uniquely owned `Array`s as contiguous mutable buffers with $O(1)$ indexing and in-place `set!`. Inside **Lean's kernel reducer (`decide +kernel`)**, however, `Array α` has no primitive flat-array reduction rule—it reduces via its logical wrapper `structure Array α where toList : List α`, turning every `T[i]?`, `r[pc]?`, `T.modify`, and `r.set!` into $O(|code|)$ linked-list traversal and allocation.
- Furthermore, `need` calls `C.ins P i pc fn ins` (`X64/Budget.lean:36`), which re-executes `selInstr` block selection on every instruction during every sweep, and `X64.budgetOk` (`X64/Budget.lean:50–52`) passes `(Sel.potential C κ P).get` directly as a `Cert` closure into `Sel.budgetOk`.

#### 5.3 Root Cause 2: Cubic Kernel Checking of `f.exp_denote` on Jumping Statements
`Meta/Elab.lean:2978–3049` carefully avoids loop-bound and callee-inlining blowups when proving `f.exp_denote`:
- `normalFormOfExp` (`Elab.lean:2978–3010`) abstracts every closed `Exp.loop` bound `b` to an opaque local `nᵢ : Nat` (`abstractLoopBounds`) and every callee to opaque locals `(gExp, g, gEq)` before running `simp`, then checks `prf` against `stmtOf e' = nf` while `nᵢ` and `g` remain opaque FVars and finally lambda-abstracts and re-applies `(bs ++ olds ++ eqs)`—making kernel checking of `f.exp_denote` strictly $O(1)$ in loop bounds even up to `2^64`, and `addDef` sets `hints := .regular (getMaxHeight env value + 1)` so `f` unfolds before inner loops.
- `addThmBudget` (`Elab.lean:3049`) wraps automatic `mp_safe` kernel checks in a `10,000`k-heartbeat cap (`mp.autoSafe.kernelHeartbeats`) so tactic proofs that accidentally unfold large loops fail fast rather than stalling asynchronous kernel checking.

Why, then, does `f.exp_denote` still grow as **$\Theta(K^3)$** in the number of sequential jumping statements (`return`, `break`, `continue`; `doc/open-claims.md:42–44`)? Inspecting `joinStmt` (`Meta/Elab.lean:926–1005`) exposes the exact mechanism:
- Because Core `Exp Γ t` is tree-structured ANF without basic-block join points, `joinStmt` avoids exponential continuation duplication (`joinCopyLimit := 8`, `stmtBudget := 100000` nodes) on a jumping statement by wrapping it in a state-passing `let` join that copies `V` outer mutable variables into temporaries, returns `(jumped : Bool, (z'₀, (z'₁, ...)))`, reassigns each outer variable via `tupCompPlace` (`y.2.2…1`), and branches `if y.1 then tail else next`:
  ```lean
  let y : Pair Bool (Tup [T₀, ...]) := (let z'₀ := z₀; ...; stmt; (jumped, (z'₀, ...)))
  let v₀ := y.2.1; z₀ := v₀; ...
  let f := y.1; if f then <jumpTail> else <next>
  ```
- Across $K$ sequential jumping statements (`if c₁ then return ...; if c₂ then return ...; ...`), each `joinStmt` nests `<next>` inside the `else` arm of the previous `ite`. Although `AExp` AST node count grows only as $O(K \cdot V)$ (staying far below `stmtBudget = 100000`), `normalForm` (`simp` over `Exp.run` / `Exp.denoteM`) must construct nested monadic `bind` + `ite` congruence proofs at depths $k = 1 \dots K$ where the de Bruijn context `Γ : List Ty` and `Env Γ` have accumulated $O(k \cdot V)$ let-bound temporaries, every `Place.set env` reconstructs an $O(k \cdot V)$-element `Env` spine, and each congruence step's implicit motive/continuation arguments embed the remaining $O((K - k) \cdot V)$ normalized tail—producing $\sum_{k=1}^K O(k \cdot (K - k)) = \Theta(K^3)$ proof-term and kernel WHNF checking work.

#### 5.4 Verified Abstract Interpreter (`Analysis/`) and `LoopsOk` Decidability Gap
Before running tactics, `Meta/Analyse.lean` invokes `Millipede/Analysis/` (2,269 lines, 115 theorems): a forward abstract interpreter over closed `UInt64` intervals `Itv`, relational comparisons `Cmp Γ` (`<, ≤, =, ≠`), and affine loop-growth upper bounds `UB Γ` (`x ≤ c₀ + d * y`). Critically, `Exp.relax` / `Exp.anR` (`Analysis/Sound.lean:153–243`) implements **partial obligation stripping**: obligations discharged by `Exp.an` are rewritten to total wrapping primitives (`Prim.wrap`, proved extensionally equal under safety by `Exp.relax_denote` and `loopRelax_safe`), forwarding only unproven residual obligations to `mp_safe`/`mp_auto`. However, `Exp.an_sound` requires `e.LoopsOk` (asserting loop bodies end in canonical tuple constructors `TailsOk`), which `mp def` proves per-function by `rfl` during elaboration rather than via a decidable `Bool` check, blocking `compile` from invoking `Analysis/` directly for constant propagation or runtime-check elimination (`doc/open-claims.md:71, 131`).

## Boundaries

- **Build, proof-checking, and co-simulation execution (`not examined`)**: `lake build`, `scripts/check.sh`, `scripts/audit.sh`, and the `qemu`/native co-simulation harnesses were not executed on this host. All properties of `.lean` definitions, theorem statements, proof scripts, module imports, and shell scripts come from direct static inspection (`source`), while wall-clock timings (`20 min` `Sel.potential` timeout, cubic `f.exp_denote` RAM/time behavior) come from repository documentation (`documentation`) paired with structural complexity analysis of the inspected code (`derived`).
- **Line-by-line semantic adequacy of ISA and ELF models (`not examined`)**: While `Target.{Machine,Isa,Target}`, `Target/A64/Decode.lean`, `Object/LinkProof.lean`, and `Object/Elf/Laws.lean` were inspected, the individual instruction semantics in `Target/X64/Exec.lean` (213L) and `Target/A64/Exec.lean` (226L) were not cross-checked opcode-by-opcode against official Intel SDM or Arm ARM specifications in this study.
- **Standalone object-format subdirectories (`not examined` in depth)**: `Millipede/Object/{ElfRel,Pe,MachO}/` (13 files, 4,768 lines) implement relocatable ELF, Windows PE32+, and macOS Mach-O writers/loaders with standalone round-trip laws, but none is wired into a `Target` or `Backend` in `Millipede/Top/Compile.lean` (`unsupported` in `compile` at `4f13d398`).
- **Scope limits (`known not to apply`)**: Neither `compile_sound` nor `#audit` protects against corrupted `.olean` build artifacts on disk, unsound trusted `Target`/`Abi`/`Format` definitions in the 22-module `Top.Statement` + target closure, or specification omissions such as ignoring short `write` byte counts returned by the adversarial `Oracle`.

## Evidence

All primary evidence was inspected on `2026-11-23` in a clean clone of `https://github.com/graydon/millipede` at commit `4f13d3980a5570177a774e63cfbc95e652dd3cde` (`leanprover/lean4:v4.35.0`).

- **Pipeline, top-level soundness, and backend factoring (`source`)**:
  - `Millipede/Top/Statement.lean` L42–L106 (`CompileSound.Statement`, `Program.sem`, `traceAfter`, `costPrefix`, `sem_neverStuck`).
  - `Millipede/Top/Compile.lean` L59–L312 (`x64Linux`, `arm64Linux`, `Backend`, `Compile.Options`, `prepA`, `backendOf`, `bytesOf`, `firstOk`, `compileWith`, `compile`).
  - `Millipede/Top/Sound.lean` L27–L254 (`Program.Lawful`, `Backend.Laws`, `bytesOf_spec`, `compile_spec`, `compileWith_sound_of_backend`, `x64Backend_laws`, `compile_sound`).
  - `Millipede/Top/SoundA64.lean` L26–L119 (`A64.init_of_link`, `a64Backend_laws`, `compile_sound_arm64`, `compileWith_sound`).
  - `Millipede/Top/StackTight.lean` L25–L122 (`CompileStack.Statement`, `Backend.StackLaw`, `compile_stack_tight`, `compile_stack_tight_arm64`); `Millipede/Top/NoCalls.lean` L18–L41 (`Program.NoCalls.machine`); `Millipede/Top/Accept.lean` L28–L91 (`decide +kernel` acceptance of `exit42` and `hello`, `CompileAccepts.Statement`).
- **Core, optimization, memory refinement, linearization, register allocation, selection, and object laws (`source`)**:
  - `Millipede/Core/Wf.lean` L47–L165 (`Sel.overlap`, `Loan`, `BS`, `BS.access`, `enterBlock`, `exitBlock`); `Millipede/Opt/Pass.lean` L30–L161 (`Opt.Pass`, `Program.Within`, `Program.Sim`, `Pass.apply_sim`).
  - `Millipede/Compile/Sem.lean` L38–L380 (`Sem`, `Sem.Mono`, `TraceEq`, `FwdSim`, `FwdSim.star`, `FwdSim.comp`, `FwdSim.reach`, `FwdSim.neverStuck`, `FwdSim.traceEq`, `FwdSim.schedule`).
  - `Millipede/Compile/LowerInv.lean` L41–L631 (`Hole`, `SI`, `ViewOK`, `PairSI`, `Lens.Lawful`, `Ctor.Lawful`, `Split.Lawful`, `HoleOK`, `Single`, `Compat`, `Lay`, `Prot`, `VarRel`, `MEnvRel`, `FEnvRel`, `HoleAv`, `Exp.Restr`); `Millipede/Compile/LowerSound.lean` L38–L124 (`lowerM_sound`); `Millipede/Compile/LinearizeProof.lean` L44–L180 (`CodeAt`, `Compiled`, `MatchK`).
  - `Millipede/RegAlloc/Check.lean` L45–L185 (`LocMap`, `defOk`, `argsOk`, `resOk`, `check`, `wfCheck`, `frameOk`); `Millipede/RegAlloc/Live.lean` L35–L256 (`idMaps`, `Live.of`, `keepCall`, `clobOk`, `Live.flex`, `R_kill`, `R_call`); `Millipede/RegAlloc/Lock.lean` L22–L198 (`Sel.frameW`, `FrameModel.words`, `Lock`, `Flex`).
  - `Millipede/Target/Budget.lean` L36–L184 (`Counts`, `Cert`, `instrOk`, `budgetOk`, `Table`, `sweepFn`, `iterate`, `potential`); `Millipede/Target/X64/Budget.lean` L22–L53 (`X64.instrs`, `X64.budgetOk`); `Millipede/Target/SelDriver.lean` L28–L181 (`Selector`, `select_spec`); `Millipede/Target/SelCases.lean` L46–L180 (`StepOk`, `LocalOk`, `StepOkAt`, `Cases`); `Millipede/Target/SelSim.lean` L46–L665 (`ticksAt`, `SimPkg.Laws`, `selectSim`, `spOk_run`, `stackPot`, `pot_step`, `rcRun_boundary`, `select_lower_sound`, `select_lower_cost`); `Millipede/Target/PMove.lean` L24–L160 (`PMove.pick`, `PMove.seq`, `pick_spec`); `Millipede/Target/A64/Decode.lean` L34–L167 (`parse`, `decodeWord`, `a64_parse_tac`, `decode_encode`, `decode_spec`).
  - `Millipede/Compile/AssembleLaws.lean` L69–L160 (`Agree`, `Assembler.Laws`); `Millipede/Object/LinkProof.lean` L30–L160 (`Link.Ok`, `link_ok`, `dropZeros_getD`); `Millipede/Object/Elf/Laws.lean` L35–L160 (`loadSeg_segPhdr`, `write_inv`, `parse_write`).
- **Elaboration, abstract interpretation, auditing, ledgers, and test tooling (`source` + `documentation`)**:
  - `Millipede/Meta/Sem.lean` L26–L775 (`Exp.isPure`, `Exp.eval`, `Upto.forIn` with `@[implemented_by Upto.forInImpl]` at L227, `Exp.run_*`, `Exp.denoteM_*`, `CtorLaw.vec`, `loopSafe_invJ`, `range_split`).
  - `Millipede/Meta/Elab.lean` L881–L1005 (`joinCopyLimit`, `stmtBudget`, `joinStmt`), L2930–L3050 (`normalForm`, `abstractLoopBounds`, `normalFormOfExp`, `addDef`, `addThm`, `addThmBudget`), L3509–L3720 (`mp.normalForm`, `mp.autoSafe.kernelHeartbeats`, `withGenVars`, `includedGenVars`, `invCandidates`, `addPureDenotes`).
  - `Millipede/Meta/Auto.lean` L40–L336 (`appsOf` DAG memoization, `mp_inst_posts`, `mp_vcgen_post`, `invFailure`, `evalMpAuto`); `Millipede/Analysis/Sound.lean` L33–L250 (`LoopInv`, `loopAn_sound`, `Exp.relax_denote`, `loopRelax_safe`, `SoundAt`).
  - `Millipede/Meta/Audit.lean` L33–L297 (`bvDecideMods`, `bvDecideArg`, `bvDecideShape`, `checkBvDecideAxiomM`, `rejectedAxioms`, `targets`, `#audit`, `#audit_ledger`); `Millipede/Meta/Emit.lean` L74–L135 (`mkEntry`, `#mp_compile`); `Millipede/Top/Ledger.lean` L46–L215 (`openClaims`, `LedgerTarget.of`, `ledger`); `Millipede/Meta/Burden.lean` L23–L146 (`Burden.classify`, `Counts.percent`).
  - `Tests/Audit.lean` L15–L171; `Tests/Ledger.lean` L25–L98; `scripts/check.sh` L1–L20; `scripts/audit.sh` L1–L87; `scripts/run-tests.sh` L1–L68; `scripts/cosim.sh` L1–L73; `scripts/leanq.py` L1–L163; `CLAUDE.md` L1–L149; `doc/open-claims.md` L1–L164; `doc/design/{compiler,trust,decisions}.md`.

## Revalidation

1. **Fast static revalidation of module closures, recursion hygiene, and audit invariants (~3 s, Python 3.10+ stdlib only)**:
   ```bash
   git clone --depth 1 https://github.com/graydon/millipede.git /tmp/millipede_arch_reval
   python3 - << 'PY'
   import os, re
   from collections import deque
   root = '/tmp/millipede_arch_reval'
   imps, txts = {}, {}
   for dp, _, fns in os.walk(os.path.join(root, 'Millipede')):
       for fn in fns:
           if fn.endswith('.lean'):
               rel = os.path.relpath(os.path.join(dp, fn), root)
               mod = rel[:-5].replace('/', '.')
               txt = open(os.path.join(dp, fn)).read()
               txts[mod] = txt
               imps[mod] = re.findall(r'^\s*import\s+([A-Za-z0-9_.]+)', txt, re.M)
   def closure(m):
       s, q = {m}, deque([m])
       while q:
           for x in imps.get(q.popleft(), []):
               if x in imps and x not in s: s.add(x); q.append(x)
       return s
   for t in ['Millipede.Top.Statement', 'Millipede.Top.Sound', 'Millipede.Top.SoundA64']:
       c = closure(t)
       print(t, len(c), 'Meta:', [x for x in sorted(c) if '.Meta.' in x],
             'Lean:', [x for x in sorted(c) if any(i.startswith('Lean') for i in imps[x])])
   print('noncomputable:', sum(len(re.findall(r'^\s*(?:private |protected )?noncomputable\s+', v, re.M)) for v in txts.values()))
   print('partial outside Meta:', [k for k, v in txts.items() if not k.startswith('Millipede.Meta.') and re.search(r'^\s*(?:private |protected )?partial\s+', v, re.M)])
   PY
   ```
2. **Targeted diff check for the two documented kernel bottlenecks and audit blindspots**:
   ```bash
   git -C /tmp/millipede_arch_reval diff 4f13d3980a5570177a774e63cfbc95e652dd3cde..HEAD -- \
     Millipede/Target/Budget.lean Millipede/Top/Accept.lean \
     Millipede/Meta/Elab.lean Millipede/Meta/Audit.lean \
     Millipede/Analysis/Sound.lean scripts/audit.sh doc/open-claims.md
   ```
   Check specifically whether `Sel.potential` replaces `Array (Array (Option Int))` with a kernel-friendly radix tree (`PTree`) or passes precomputed certificates outside `compile` (closing `CompileAccepts.Statement`), whether `joinStmt` avoids nested monadic `Env` rewrites, whether `Analysis` makes `Exp.LoopsOk` decidable, and whether `Meta/Audit.lean` adds `@[csimp]` or external kernel-export checks.
3. **Full toolchain verification (when `leanprover/lean4:v4.35.0` and `qemu` are available)**: run `./scripts/audit.sh` and `./scripts/check.sh` from the repository root to execute `#audit`, `Tests/Audit.lean`, `Tests/Ledger.lean`, and all 39 `run-tests.sh` normal + `--selftest` stages.
