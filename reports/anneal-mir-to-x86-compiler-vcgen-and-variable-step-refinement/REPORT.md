# Anneal MIR-to-x86-64 Capture, MIR Transform Division of Labor, Byte Provenance, Symbolic VCGen, and Variable-Step Refinement

## Summary

Scaling Anneal's verified compilation and deductive verification stack from
scalar `u64`/`bool` stack slots to multi-field structs, enums, raw pointers,
wide slices (`&[T]`), polymorphic `Src`/`Dst` types, `zerocopy`'s unsafe
primitives, unbounded `while` loops, and variable-step compiler optimizations
requires resolving four tightly coupled problems across the front-end capture
driver (`anneal-rustc-capture`), the `rustc_mir_transform` /
`rustc_codegen_ssa` pipeline, the byte-addressed operational semantics
(`Trusted/X86Semantics.lean`), and the step-indexed refinement and weakest
precondition machinery in `theory/`:

1. **`anneal-rustc-capture` MIR/Layout Extraction & Unified Byte-Addressed Provenance Semantics (`support/ByteMemoryProvenanceProbe.lean`, `support/Phase3SemanticsProbe.lean`):**
   - **Flag Mechanics (`-Z mir-opt-level=0 -C debug-assertions=off -C panic=abort`):**
     In `compiler/rustc_session/src/session.rs:945-951`, `-C debug-assertions=off`
     sets both `sess.overflow_checks()` and `sess.ub_checks()` to `false` (passing
     `-Z ub-checks=no` produces a 0-byte diff in `--emit=mir`). Arithmetic `+`,
     `-`, `*`, `<<`, `>>` overflow checks and pointer alignment/null/enum UB
     checks (`CheckAlignment`, `CheckNull`, `CheckEnums`) are suppressed, whereas
     array/slice bounds checks (`Builder::bounds_check` at
     `compiler/rustc_mir_build/src/builder/expr/as_place.rs:728-757`) and
     division/remainder-by-zero checks (`as_rvalue.rs:530-591`) are emitted
     unconditionally.
   - **Why `DefId` Call Interception Beats `-Z mir-enable-passes=+Inline`:**
     At `-Z mir-opt-level=0`, `LowerIntrinsics` lowers `core::mem::transmute` in
     place to `CastKind::Transmute`, while the other 11 `zerocopy` wrappers
     remain `TerminatorKind::Call`. Enabling `+Inline` destroys per-function
     modular verification boundaries, fails to inline `transmute_copy`, and
     explodes `MaybeUninit` into internal union projections. Intercepting
     `TerminatorKind::Call` by `FnDef(def_id, args)` (`classify_call` in
     [`monomorph_mir_driver.rs`](support/monomorph_mir_driver.rs)) handles all 12
     `zerocopy` operations in 1 basic block per call while preserving modular
     function boundaries, and `TyCtxt` queries in
     [`layout_mir_driver.rs`](support/layout_mir_driver.rs) close all 12 layout
     and ABI gaps omitted by textual `--emit=mir`.
   - **Allocation-Indexed Byte Memory (`mem : Nat → AllocBlock` + `Ptr alloc offset`) & `prelude`-Only Kernel Idioms:**
     Indexing memory by logical allocation (`AllocBlock` with `size : Nat`,
     `perm : BytePerm`, `written : Bool`, `bytes : List (Option UInt8)`, and
     `ptr : Option Ptr`) gives definitional cross-slot framing (`rfl`) even when
     an adjacent slot has symbolic polymorphic byte size `tySizes idx`, while
     first-argument `Nat` recursion (`dropBytes`, `takeBytes`, `writeSliceAt`),
     `Bool.casesOn` (`match ... with | true => ...`) instead of `@ite` + `decide`,
     and avoiding open symbolic `Nat.div`/`Nat.mod` in `whnf_core` enable
     syntax-directed `wpByteX86` to verify padded structs, niche enums, wide
     slices, `copy_nonoverlapping`, and width casts with 89–95% smaller proofs.
2. **Three-Tier `rustc_mir_transform` Division of Labor & `rustc_codegen_ssa` Lowering (`support/support_mir_transform_adaptation_probe.lean`, `support/support_mir_to_anllvm_lowering_probe.lean`):**
   - **Category M1 (~6,200 LOC):** Mandatory pre-codegen lowering and cleanup
     (`ElaborateDrops`, `coroutine::StateTransform`, `shim::make_shim`,
     `AbortUnwindingCalls`, `LowerIntrinsics`, `SimplifyCfg`,
     `CleanupPostBorrowck`, `PostAnalysisNormalize`, `AddMovesForPackedDrops`).
   - **Category M2 (~2,450 LOC):** High-value MIR optimizations exploiting typed
     places, destructive `Operand::Move` ownership transfer, and pre-ABI
     uniformity of `_0` (`RETURN_PLACE`): `DestinationPropagation`
     (`dest_prop.rs`, 670 LOC), `CopyProp` + `SsaLocals` (`copy_prop.rs` +
     `ssa.rs`), `ScalarReplacementOfAggregates` (`sroa.rs`), and `Inline` /
     `ForceInline`. Empirically ([`ablation_results.json`](support/ablation_results.json)),
     on a 256-byte aggregate builder (`[u64; 32]`) moving across a diamond
     branch into an `sret` return (`Pattern 1`), `opt -O2` alone (`C1`) fails to
     eliminate 2 stack `alloca`s and 2 `llvm.memcpy`s, whereas enabling Category
     M2 (`C2`) eliminates **100% of `alloca`s (`8 -> 0`) and 100% of
     `llvm.memcpy`s (`7 -> 0`)**.
   - **Category M3 (~15,000+ LOC):** Redundant or bug-prone MIR passes (`GVN`,
     `JumpThreading`, `DataflowConstProp`, `ReferencePropagation`, `InstSimplify`)
     to skip in MIR and delegate to `AnLLVM`. On `pattern2_option_adapter_chain`,
     Category M2 + `opt -O2` (`C2`) produces a **1-block branchless loop (`BBs =
     1`)**, whereas full `-Zmir-opt-level=2 + opt -O2` (`C3`) degrades to **25
     basic blocks** because MIR's `JumpThreading` creates triangle CFGs that
     defeat LLVM's `SimplifyCFG`.
   - **Single-Pass RPO `LocalAnalyzer` & Universal `TagEncoding::Niche` Round-Trip:**
     `analyze::non_ssa_locals` (`mir/analyze.rs:17-56`) and reverse-postorder
     lowering eliminate frontend $\phi$-placement from the `MIR -> AnLLVM` proof
     obligation; `codegen_get_set_discr_niche_roundtrip` proves universal
     modular round-trip soundness of `TagEncoding::Niche`; and `MaskedWord64`
     `pack_cast_regs`/`bitcast_bytes` eliminate 100% of `PassMode::Cast` and
     `Transmute` `alloca` bounces while fixing `rustc`'s unsound `!noundef` load
     across padding bytes ([`empirical_probe_opt1_nollvm.ll`](support/empirical_probe_opt1_nollvm.ll)).
3. **Syntax-Directed Symbolic Execution (`wpX86`), Canonical Cut-Points (`wpX86Cut`), and Inductive Loop Verification (`support/SymbolicVCGenProbe.lean`, `support/LoopAndJoinVCGenProbe.lean`):**
   - `forallTypedArgsAux` and `initX86State_canonical` replace existential entry
     memory `s.mem` with a concrete `buildArgMem` spine so `wpX86` (45 lines in
     `theory/`, zero changes to `trusted/`) reduces all 9 `X86Instr` cases and
     7 of 9 `X86Term` cases by `whnf`/`rfl`, splitting only on `.jccBool` and
     `.repMovsbJmp`.
   - `canonMemUpTo B m` and `canonState B s` normalize `s.mem : Nat → Option
     X86Val` in place on `Trusted.X86State`, erasing temporary slot closures so
     asymmetric diamond branches merge by `rfl` ($O(D)$ instead of $O(2^D)$) and
     satisfying unconditional forward simulation `canonState_subsumed` and
     `evalX86Step_subsumed`.
   - By strong induction on the `ReachesPrefix` fuel budget `n : Nat`
     (`wpX86_loop_sound`), a single-iteration `wpX86Cut` obligation at `headerBb`
     discharges runtime-trip-count `while` loops (`countUpLoopBody`,
     `sumLoopBody`, `nonZeroLoopBody`, `loopWithInternalDiamondBody`) in 4–20
     lines each.
4. **Variable-Step Compiler Refinement (`π_opt`, `π_progress K`, `π_elastic`) and Stateful Peephole Passes (`support/VariableStepCompilesProbe.lean`, `support/StatefulVariableStepProbe.lean`):**
   - Because `ReachesPrefix` emits a per-step trace `List.replicate k ()`, any
     pass that changes the step count ($k_1 \neq k_2$) refutes lockstep `id` and
     every trace-preserving query map (`not_compiles_any_trace_preserving_query_map`).
   - Defining behavior morphisms `π_opt = π_progress 1` ($q_2.\text{steps} \le
     n_1$) and `π_progress K` ($q_2.\text{steps} \le K \cdot n_1 + (K - 1)$) in
     `theory/` preserves all `SpecOn` specifications (`π_elastic_specOn_le`,
     `verified_of_compiles_elastic`) while **provably forbidding silent infinite
     loops** (`not_compiles_π_opt_infinite_loop`), using the **Terminal
     Stabilization Law** (`reachesPrefix_add_of_terminated`) to handle
     instruction deletion ($K = 1$).
   - Combining the **Block-Suffix Simulation Pattern** (`(passBlock
     blk).instrs.drop s_tgt.ip = passInstrs (blk.instrs.drop s_src.ip)`) with
     zero-`funext` extensional memory congruence (`MemExtEq` and
     `MemAgreesExcept`) proves universal `Compiles X86Lang X86Lang π_x86_opt`
     soundness for `stripNops`, `expandImmMov` ($K = 2$), stateful dead-store
     elimination (`elimDeadStoreDealloc`), 3-to-2 scratch-move fusion
     (`fuseScratchMov`), and their 3-pass composition (`optPipeline_compiles_opt`).

## Applicability

These findings and mechanized probes apply to:

- **Anneal (`joshlf/anneal`):** Durable `origin/main` commits
  `24367bd1a8c784f2578535954f9915e24894a56f` (`trusted/audit/TrustedBoundary.lean`)
  and `beb778bb135474a67dc017c185d2753a60693d8c` (`Trusted/Refinement.lean`,
  `Trusted/StepResult.lean`), together with the self-contained MIR-to-x86-64
  prototype AST and operational semantics (`X86Ast`, `X86Semantics`, `MirAst`,
  `MirSemantics`, `Peephole`) inlined in Section 1 below and mechanized in the
  8 standalone Lean 4.34.1 probes in `support/`.
- **Rust Compiler (`rust-lang/rust`):** Pinned baseline
  `58cf8f9c35b355199727627d07ae34a4e2846d67`, `rustc_mir_transform` /
  `rustc_codegen_ssa` baseline `49d734536222bf28bb6d07d885b3a81d145981da`, and
  bundled nightly `1.98.0-nightly (f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1
  2026-05-30)` (`x86_64-unknown-linux-gnu`).
- **Rust Reference (`rust-lang/reference`):** Commit
  `82da570bafd9efed421bdbae0f8603ede8dd308b` (`r[layout.repr.rust]`,
  `r[layout.repr.c]`, `r[validity.struct]`, `r[validity.enum]`,
  `r[validity.undef]`).
- **LLVM Project (`llvm/llvm-project`):** Release `llvmorg-21.1.8` at commit
  `3623fe661ae35c6c80ac221f14d85be76aa870f1` (`/usr/bin/opt` 21.1.8).
- **Lean 4 (`leanprover/lean4`):** Version `v4.34.1` at commit
  `5045d0056413266e57c625dcd7c365b10e377c52` (`prelude`-only mode with `import
  Init.NotationExtra` and `import Init.Classical`).

## Findings

### 1. Self-Contained Prototype AST, Operational Semantics, and Refinement Kernel Definitions

So that every theorem, counterexample, and VCGen/simulation construction in this
report is self-contained without checking out any prototype branch, we inline
the exact Lean 4.34.1 definitions of the step-indexed refinement kernel
(`Trusted/StepResult.lean`, `Trusted/Refinement.lean`) and the `X86Ast` /
`X86Semantics` target machine (`Trusted/X86Ast.lean`,
`Trusted/X86Semantics.lean`, reproduced in full in
[`SymbolicVCGenProbe.lean`](support/SymbolicVCGenProbe.lean) and
[`VariableStepCompilesProbe.lean`](support/VariableStepCompilesProbe.lean)):

```lean
/-- Single small-step transition outcome (`Trusted/StepResult.lean`). -/
inductive StepResult (State Obs Term Err : Type) where
  | step (next : State) (obs : Obs)
  | terminated (result : Term)
  | failed (err : Err)

/-- Outcome of a finite fuel-bounded execution prefix. -/
inductive PrefixOutcome (Term Err : Type) where
  | running
  | terminated (result : Term)
  | failed (err : Err)

def PrefixOutcome.isSafe : PrefixOutcome Term Err → Prop
  | .failed _ => False
  | _ => True

structure ExecQuery (State : Type) where
  init : State
  steps : Nat

structure PrefixOutput (Obs Term Err : Type) where
  trace : List Obs
  outcome : PrefixOutcome Term Err

structure Machine (Prog State Init Obs Term Err : Type) where
  initState : Prog → Init → State → Prop
  step : Prog → State → StepResult State Obs Term Err → Prop

/-- Relational step-indexed prefix execution with Terminal Stabilization
    on `.terminated` and `.failed` (`steps = n + 1` for arbitrary `n : Nat`). -/
inductive ReachesPrefix (M : Machine Prog State Init Obs Term Err) (p : Prog) :
    Init → Nat → State → List Obs → PrefixOutcome Term Err → Prop where
  | zero (init : Init) (s : State) :
      M.initState p init s →
      ReachesPrefix M p init 0 s [] .running
  | terminated (init : Init) (n : Nat) (s : State) (term : Term) :
      M.initState p init s →
      M.step p s (.terminated term) →
      ReachesPrefix M p init (n + 1) s [] (.terminated term)
  | failed (init : Init) (n : Nat) (s : State) (err : Err) :
      M.initState p init s →
      M.step p s (.failed err) →
      ReachesPrefix M p init (n + 1) s [] (.failed err)
  | step (init : Init) (n : Nat) (s s' : State) (obs : Obs)
      (tr : List Obs) (out : PrefixOutcome Term Err) :
      M.initState p init s →
      M.step p s (.step s' obs) →
      ReachesPrefix (M := { M with initState := fun _ i st => st = i }) p s' n s' tr out →
      ReachesPrefix M p init (n + 1) s (obs :: tr) out

/-- Demonic/angelic specification lattice point (`Trusted/Refinement.lean`). -/
structure SpecPoint (Out : Type) where
  defined : Prop
  val : Out → Prop

/-- `b₁ ≤ b₂` (`b₁` refines `b₂`): whenever `b₂` is defined, `b₁` is defined
    and every possible output of `b₁` is allowed by `b₂`. -/
def SpecPoint.le (b₁ b₂ : SpecPoint Out) : Prop :=
  b₂.defined → b₁.defined ∧ ∀ o, b₁.val o → b₂.val o

structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Query → SpecPoint Out

def Language.Verified (L : Language) (p : L.Prog) (spec : L.Query → SpecPoint L.Out) : Prop :=
  ∀ q, SpecPoint.le (L.sem p q) (spec q)

def Compiles (L₁ L₂ : Language)
    (π : (L₁.Query → SpecPoint L₁.Out) → (L₂.Query → SpecPoint L₂.Out))
    (p₁ : L₁.Prog) (p₂ : L₂.Prog) : Prop :=
  ∀ q, SpecPoint.le (L₂.sem p₂ q) (π (L₁.sem p₁) q)
```

And the `X86Ast` and `X86Semantics` definitions:

```lean
inductive X86Ty where
  | usize | bool | unit | adt (id : Nat) | param (idx : Nat) | refParam (idx : Nat)
  deriving DecidableEq

inductive X86Val where
  | word64 (val : Nat)
  | boolVal (val : Bool)
  | unit
  | adt (id : Nat) (inner : X86Val)
  | bytes (size : Nat) (bits : Nat)
  | stackPtr (slot : Nat)
  deriving DecidableEq

inductive X86Operand where
  | immWord (val : Nat)
  | immBool (val : Bool)
  | immUnit
  | stackSlot (slot : Reg) (consume : Bool)
  | adtField0 (slot : Reg) (adtId : Nat) (consume : Bool)

inductive X86Instr where
  | nop
  | mov (dst : Reg) (src : X86Operand)
  | packAdt (dst : Reg) (adtId : Nat) (src : X86Operand)
  | leaSlot (dst : Reg) (target : Reg)
  | binOp (op : X86BinOp) (dst : Reg) (lhs rhs : X86Operand)
  | cmpOp (op : X86CmpOp) (dst : Reg) (lhs rhs : X86Operand)
  | notBool (dst : Reg) (src : X86Operand)
  | allocSlot (slot : Reg)
  | deallocSlot (slot : Reg)

inductive X86Term where
  | ret
  | jmp (target : BlockId)
  | jccBool (cond : X86Operand) (falseTarget trueTarget : BlockId)
  | abortUb
  | abortPanic
  | assertBoolJmp (cond : X86Operand) (expected : Bool) (target : BlockId)
  | cmpSizeEqJmp (dst : Reg) (lhsTy rhsTy : X86Ty) (target : BlockId)
  | repMovsbJmp (dst : Reg) (srcTy dstTy : X86Ty) (ptrOp : X86Operand) (target : BlockId)
  | call1 (dst : Reg) (calleeBody : X86Body) (argOp : X86Operand) (retTarget : BlockId)

structure X86State where
  mem : Nat → Option X86Val
  tySizes : Nat → Nat
  bb : Nat
  ip : Nat
  curBody : Option X86Body := none
  callerSaved : Option CallerFrame := none

def SafeAndEnsures (P : X86Val → Prop) (out : PrefixOutput Unit X86TermResult X86Err) : Prop :=
  out.outcome.isSafe ∧ (∀ ret, out.outcome = .terminated (.normal ret) → P ret)

def SpecOn (body : X86Body) (P : X86State → Prop) (Q : X86State → X86Val → Prop) :
    ExecQuery X86State → SpecPoint (PrefixOutput Unit X86TermResult X86Err) :=
  fun q =>
    { defined := initX86State body q.init ∧ P q.init
      val := fun out => SafeAndEnsures (Q q.init) out }

def AdmissibleLibInv (libInv : Nat → X86Val → Prop) : Prop :=
  ∀ id v, v.isAdtFree → libInv id v
```

---

### 2. `anneal-rustc-capture` MIR/Layout Extraction and Unified Byte-Addressed Provenance Semantics

#### 2.1 Six-Category Empirical `rustc` Matrix and the 12 Gaps in Textual `--emit=mir`

Running `rustc --emit=mir -Z mir-opt-level=0 -C debug-assertions=off -C
panic=abort` and [`support/layout_mir_driver.rs`](support/layout_mir_driver.rs) /
[`support/monomorph_mir_driver.rs`](support/monomorph_mir_driver.rs) on
[`support/probe_6cat.rs`](support/probe_6cat.rs) establishes the correspondence
between textual `--emit=mir` and internal `TyCtxt` queries:

| Category | Representative Constructs in `probe_6cat.rs` | Textual `--emit=mir` Representation (`-Z mir-opt-level=0 -C debug-assertions=off`) | Hidden Layout / ABI Facts Exposed by `TyCtxt` (`layout_mir_driver.rs` & `monomorph_mir_driver.rs`) |
| :--- | :--- | :--- | :--- |
| **1. Aggregates, Arrays, Slices, Enums** | `Pair { a: u32, b: u64 }`, `ReorderRust { a: u8, b: u64, c: u16 }`, `#[repr(C)] PairC`, `#[repr(C, packed)] PackedPair`, `[u32; 4]`, `&[u8]`, `Option<usize>`, `Option<NonZeroUsize>`, `Result<usize, u32>`, `#[repr(u8)] CLike`, `DataEnum` | Aggregate Rvalues `Pair { a: move _3, b: move _4 }`, `Option::<usize>::Some(move _4)`, `Option::<NonZero<usize>>::Some(move _4)`, `[move _3, ...]`, `[const 0_u8; 16]`. | `Pair` (`16B`, `ScalarPair(Int64, Int32)`) reorders `FieldIdx(1)` (`b`) to offset `0` and `FieldIdx(0)` (`a`) to offset `8`. `ReorderRust` (`16B`, `Memory`) reorders `[1, 2, 0]` to offsets `[10, 0, 8]`. `Option<usize>` is `16B` (`TagEncoding::Direct`, tag at `0`, payload at `8`), whereas `Option<NonZeroUsize>` is `8B` (`TagEncoding::Niche { untagged_variant: 1, niche_variants: 0..=0, niche_start: 0 }`) with identical MIR. |
| **2. Nested Projections & Raw Pointers** | `t.0.1`, `(*p).b`, `arr[idx]`, `slice[idx]`, `*ptr`, `&raw const (*ptr).b`, `&raw mut (*ptr).b`, packed `&raw const (*ptr).b` | `_0 = copy ((_1.0: (u32, u64)).1: u64);`, `_0 = copy ((*_1).1: u64);`, `_0 = &raw const ((*_1).1: u64);`. Indexing emits `PtrMetadata` + `Lt` + `assert(...)` before `(*_1)[_3]`. | In `PackedPair`, `(&raw const ((*_1).1: u64))` is at byte offset `1` (`align = 1B`). Bounds-check `Assert` terminators are emitted unconditionally (`as_place.rs:728-757`). |
| **3. Casts, Provenance, Wide Metadata** | `u8 as u64`, `i32 as i64`, `u64 as u32`, `i32 as u32`, `ptr as usize`, `ptr.addr()`, `with_exposed_provenance`, `without_provenance`, `arr as &[u32]`, `slice.len()`, `intrinsics::ptr_metadata` | `IntToInt`, `PointerExposeProvenance`, `PointerWithExposedProvenance`, `&raw const (*_1)`, `PtrToPtr`, `PointerCoercion(Unsize, AsCast)`, `PtrMetadata(move _2)`. | `CastKind::IntToInt` omits the source operand's type inline; distinguishing `movzx` from `movsxd` requires `body.local_decls[src].ty`. `Unsize` constructs a `16B` `ScalarPair(ptr, const 4_usize)`. |
| **4. Loops & Control Flow** | `while`, `loop` with `break`/`continue`, `for i in 0..n`, `match` on `u32`, `CLike`, `DataEnum`, `Option<usize>`, `Option<NonZeroUsize>` | `goto -> bb_header` back-edges; `_2 = discriminant(_1); switchInt(move _2)`. | `Rvalue::Discriminant(_1)` returns logical discriminant (`0` for `None`, `1` for `Some`) for both `Option<usize>` and `Option<NonZeroUsize>`, and `1, 2, 255` for `CLike`. Lowering `discriminant` requires `Variants::Multiple` (`TagEncoding`) from `tcx.layout_of`. |
| **5. Calls & Generics** | `callee_0..7`, `cat5_generic_id<T: Copy>`, `<T as ComputeTrait>::compute`, `#[track_caller] cat5_tracked_callee` | `_0 = callee(...) -> [return: bb1, unwind unreachable];` | `#[track_caller]` callees (`cat5_tracked_callee`, `ptr::read`, `ptr::write`, `transmute_copy`, `unreachable_unchecked`, `MaybeUninit::assume_init`) append an implicit `&Location` parameter in `FnAbi::args` (`arg_count = N + 1`) absent from MIR `args`. |
| **6. `zerocopy` Intrinsics** | `size_of`, `align_of`, `transmute`, `transmute_copy`, `ptr::{read,write,copy,copy_nonoverlapping,write_bytes}`, `unreachable_unchecked`, `MaybeUninit::{uninit,assume_init}`, `UnsafeCell::get` | Only `mem::transmute` lowers inline (`as Dst (Transmute)`) at `mir-opt-level=0`; the other 11 remain `TerminatorKind::Call` unless intercepted by `DefId`. | `cat6_transmute` returning `[u32; 2]` (`8B`, `BackendRepr::Memory`) uses `PassMode::Cast` in `rax`; `Pair` (`16B`) uses `PassMode::Pair` in `rax:rdx`; `ReorderRust` (`16B`) uses `PassMode::Indirect` (`sret` in `rdi`). |

In [`support/monomorph_mir_driver.rs`](support/monomorph_mir_driver.rs),
`tcx.collect_and_partition_mono_items(())` discovers all 70 reachable local
`MonoItem::Fn(instance)` items (including `cat5_generic_id::<Pair>`,
`cat5_trait_generic::<u64>`, and `<u64 as ComputeTrait>::compute`), and
`instance.instantiate_mir_and_normalize_erasing_regions(tcx,
TypingEnv::fully_monomorphized(), EarlyBinder::bind(raw_body.clone()))`
substitutes `instance.args`, erases regions, and normalizes associated types
(whereas raw `EarlyBinder::instantiate` returns `ty::Unnormalized` without
normalizing associated types). In polymorphic mode
(`TypingEnv::post_analysis(tcx, def_id)`), `body.required_consts()` exposes the
symbolic `<Src as SizedTypeProperties>::SIZE` and `<Dst as
SizedTypeProperties>::SIZE` obligations on `core::mem::transmute_copy<Src,
Dst>`.

#### 2.2 Unified Byte-Addressed Provenance Machine (`AllocBlock`) and `prelude`-Only Kernel Design Idioms

In [`support/ByteMemoryProvenanceProbe.lean`](support/ByteMemoryProvenanceProbe.lean)
and [`support/Phase3SemanticsProbe.lean`](support/Phase3SemanticsProbe.lean),
replacing the prototype's disjoint `X86Val` sum (`.word64`, `.boolVal`, `.unit`,
`.adt`, `.bytes`) with `ByteVec := List (Option UInt8)` inside `AllocBlock`
unifies concrete scalars, multi-field padded structs, enums, wide slices, and
polymorphic `Src`/`Dst` values:

```lean
structure Ptr where
  alloc : Reg
  offset : Nat
  deriving DecidableEq

structure AllocBlock where
  size : Nat
  perm : BytePerm
  written : Bool
  bytes : List (Option UInt8)
  ptr : Option Ptr := none
```

Three `prelude`-only Lean 4.34.1 design choices are critical so that symbolic
byte-slice operations reduce by `rfl` and `dsimp`:

1. **First-argument `Nat` recursion (`dropBytes`, `takeBytes`, `writeSliceAt`) and right-hand offset addition (`width + p.offset`):**
   Putting the `Nat` count/offset parameter first compiles recursion via
   `Nat.rec` rather than `List.rec`. At `offset = 0`, `extractSlice bs 0 sz` and
   `writeSlice (replicateBytes sz none) 0 bs` reduce definitionally (`rfl`) even
   when `bs` has symbolic length `sz = tySizes idx`. Likewise, writing `width +
   p.offset` in `readSlice` and `writeSliceMem` reduces `width + 0` to `width`
   by `rfl` (`Nat.add_zero` is definitional in Lean 4, whereas `0 + width` is
   not).
2. **`Bool.casesOn` (`match ... with | true => ...`) + `Nat.ble`/`Nat.beq` instead of `@ite` + `decide`:**
   `@ite` (`if c then ... else ...`) embeds `s.mem k` inside dependent
   `Decidable` proof terms, causing `rw [hmem]` to fail with `motive is not type
   correct` and preventing `dsimp` from reducing `updateAlloc mem 3 blk 1` on
   symbolic `mem`. Using `Bool` pattern matching and `Nat.ble`/`Nat.beq` makes
   disjoint slot lookups reduce automatically under `dsimp`.
3. **`leaSlot` on uninitialized `StorageLive` destinations:**
   Taking `&raw mut dst` via `.leaSlot` before `copy_nonoverlapping` or
   `repMovsbJmp` writes into `dst` must check `targetBlk.perm.canRead &&
   Nat.ble offset targetBlk.size` without requiring `targetBlk.written = true`,
   because `allocSlotTyped` initializes fresh `StorageLive` stack allocations
   with `written = false`.

#### 2.3 Summary of Verified Byte-Level `CrateTheorem`s and Negative Adequacy Canaries

| Feature Area | Positive Verified `CrateTheorem`s & Specs | Negative Adequacy Canaries (`¬ CrateTheorem`) |
| :--- | :--- | :--- |
| **Multi-Field Padded Structs (`Padded { a: u8, /* 3 pad */ b: u32 }`) & `rep movsb`** | `prove_padded_subfield_crate`, `paddedSubfieldAndCopyBody_verified_vcgen` (12 lines via `wpByteX86`), `defaultLibInv_admissible`, `nonZeroAndPaddedLibInv_admissible` | `canary_alu_on_uninit_padding_rejected` (8B ALU `.add` spanning `none` padding bytes), `canary_pubSafe_padded_rejects_field_restriction`, `canary_pubSafe_padded_rejects_padding_init_requirement` |
| **Spatial Provenance (`Ptr alloc offset`)** | `prove_inbounds_ptr_field_load_crate` (`Ptr ⟨1⟩ 0` + `4` $\mapsto$ `Ptr ⟨1⟩ 4` loading 4B `u32` field `b`) | `canary_oob_ptr_load_rejected` & `canary_oob_ptr_store_rejected` (`Ptr ⟨1⟩ 0` + `8` $\mapsto$ `Ptr ⟨1⟩ 8` rejected even when slot `2` is allocated) |
| **Polymorphic `transmute_checked<Src, Dst>` & PME `sizeEqConst`** | `prove_pme_transmute_single_crate`, `constSucceeds_sizeEqConstBody_vcgen` (2 lines), `transmuteCheckedBody_verified_vcgen` (6 lines) | `canary_transmuteUnchecked_rejected` (omitting `sizeEqConstBody` allows `tySizes 0 ≠ tySizes 1` UB in `repMovsbJmp`) |
| **Niche-Encoded (`Option<NonZeroUsize>`) vs Direct-Tagged (`Option<usize>`) Enums** | `prove_unwrap_or_zero_niche_crate`, `prove_map_nonzero_to_opt_crate` (`mapNonZeroToOptBody_ensures_some_discr`), `prove_unwrap_or_zero_direct_crate`, `enumCrateLibInv_admissible` | `canary_direct_option_uninit_payload_rejected` (reading `none` payload of `Option::<usize>::None`), `canary_niche_forged_zero_nonzero_rejected` (downcasting `0` into `NonZeroUsize`) |
| **Wide Slice Pointers (`&[u32]`), `PtrMetadata`, & Bounds-Checked Indexing** | `prove_slice_get_checked_crate` (under `SliceArgValid`), `prove_slice_make_and_get_crate`, `sliceMakeAndGetBody_ensures_200` | `canary_forged_slice_len_oob_rejected` (wide slice with forged `len = 4` over 2-element buffer faults at `idx = 2`) |
| **`copy_nonoverlapping` Spatial Disjointness** | `prove_copy_nonoverlapping_distinct_slots_crate`, `prove_copy_nonoverlapping_subslices_crate` (`0..4` to `4..8` in same 8B buffer) | `canary_copy_nonoverlapping_overlapping_rejected` (copying 4B from `0..4` to overlapping `2..6` in same 8B allocation) |
| **Signed/Unsigned Width Casts (`movzx`, `movsx`, `truncate`)** | `prove_cast_u8_to_u64_zero_extend_crate`, `prove_cast_i8_to_i64_sign_extend_crate`, `prove_cast_u64_to_u8_truncate_crate`, `movsx_vs_movzx_neg1_and_pos42` | `canary_movsx_uninit_rejected` (`movsx` reading uninitialized `none` byte) |

---

### 3. `rustc_mir_transform` Division of Labor and `rustc_codegen_ssa` Lowering

#### 3.1 Pipeline Phase Architecture in `compiler/rustc_mir_transform/src/lib.rs`

In `compiler/rustc_mir_transform/src/lib.rs` (841 LOC at
`49d734536222bf28bb6d07d885b3a81d145981da`), MIR bodies progress through three
major dialects (`MirPhase::Built`, `MirPhase::Analysis`, and
`MirPhase::Runtime`) governed by six query stages:
1. **`mir_built` (`lib.rs:390-428`):** Constructs initial MIR from HIR/THIR and
   runs `LintAndRemoveUninhabited`, MIR lints, `SimplifyCfg::Initial`, and
   `SanityCheck`.
2. **`mir_promoted` (`lib.rs:431-488`):** Runs `RequiredConstsVisitor`,
   `PromoteTemps`, `SimplifyCfg::PromoteConsts`, and `InstrumentCoverage`,
   transitioning to `MirPhase::Analysis(AnalysisPhase::Initial)`.
3. **`run_analysis_cleanup_passes` (`lib.rs:630-640`):** After `mir_borrowck`,
   runs `ImpossibleClauses`, `CleanupPostBorrowck`, `RemoveNoopLandingPads`,
   `SimplifyCfg::PostAnalysis`, and `Derefer`, transitioning to
   `MirPhase::Analysis(AnalysisPhase::PostCleanup)`.
4. **`run_runtime_lowering_passes` (`lib.rs:643-667`):** Lowers `Analysis` MIR
   into `MirPhase::Runtime(RuntimePhase::Initial)` via `CriticalCallEdges`,
   `PostAnalysisNormalize`, `Subtyper` (`add_subtyping_projections.rs`),
   `ElaborateDrops`, `CheckDropRecursion`, `AbortUnwindingCalls`,
   `AddMovesForPackedDrops`, `EraseDerefTemps`, `ElaborateBoxDerefs`,
   `coroutine::StateTransform`, and `KnownPanicsLint`.
5. **`run_runtime_cleanup_passes` (`lib.rs:670-684`):** Lowers runtime-initial
   MIR into `MirPhase::Runtime(RuntimePhase::PostCleanup)` via `LowerIntrinsics`,
   `RemovePlaceMention`, and `SimplifyCfg::PreOptimizations`. **This
   `Runtime(PostCleanup)` boundary is where `anneal-rustc-capture` extracts MIR.**
6. **`inner_optimized_mir` & `run_optimization_passes` (`lib.rs:686-822`):**
   Runs `remap_mir_for_const_eval_select`, `MentionedItems`, and the 41-stage
   optimization pipeline ending in `MirPhase::Runtime(RuntimePhase::Optimized)`,
   followed by `deduced_param_attrs` (`deduce_param_attrs.rs:144-239`).

#### 3.2 Complete Classification Table of `rustc_mir_transform` Passes

| Pass / Module | File (`rustc_mir_transform/src/`) | LOC | Phase | Default Policy (`mir-opt-level`) | High-Level MIR Invariants Exploited | Historical Soundness Bugs / Hazards | Anneal Category & Recommendation |
| :--- | :--- | ---: | :--- | :--- | :--- | :--- | :--- |
| `ElaborateDrops` | `elaborate_drops.rs` + `elaborate_drop.rs` | 2,217 | `Runtime(Initial)` | `Required` (always) | `MoveData` initialization lattices (`MaybeInitializedPlaces`, `MaybeUninitializedPlaces`), `Place` projection trees, `DropStyle::{Dead, Static, Conditional, Open}`, unwind vs. normal drop paths | Unwind drop-flag desync if flag is not cleared before drop (`elaborate_drop.rs:1556-1581`); packed-field drop alignment (`#46043`) | **M1 (Mandatory Lowering):** Required before `MirSemantics` or `AnLLVM` codegen; highest priority M1 pass to verify in Lean (`PreDropMirLang -> MirLang`). |
| `coroutine::StateTransform` | `coroutine/*.rs` (`mod.rs`, `layout.rs`, `drop.rs`, `by_move_body.rs`) | 2,670 | `Runtime(Initial)` | `Required` (always) | Yield suspension points (`TerminatorKind::Yield`), cross-suspend local liveness (`locals_live_across_suspend_points`), witness struct layout, coroutine drop shims | Query cycles with `JumpThreading`/`DataflowConstProp`; drop-shim pass omission (`FIXME(#91576)` in `shim.rs:82`) | **M1 (Mandatory Pre-Capture):** Keep in `rustc` pre-capture so Anneal captures lowered state-machine `Future::poll` / `Coroutine::resume` MIR. |
| `make_shim` (`MirShims`) | `shim.rs` + `shim/async_destructor_ctor.rs` | 1,781 | On-demand query (`mir_shims`) | `Required` (always) | `ShimKind::{VTable, FnPtr, Reify, ClosureOnce, DropGlue}`, ADT field destructor ordering, `Adjustment::{Identity, Deref, RefMut}` | Coroutine drop-shim pass inconsistency (`#91576`) | **M1 (Mandatory Pre-Capture):** Capture synthesized `DropGlue` and `FnOnce` shims as standard `Runtime(PostCleanup)` MIR bodies. |
| `AbortUnwindingCalls` | `abort_unwinding_calls.rs` | 148 | `Runtime(Initial)` | `Required` (always) | `UnwindAction::{Continue, Unreachable, Terminate, Cleanup}`, caller vs. callee `PanicStrategy::Abort` ABI compatibility | Missing `Terminate(Reason::Abi)` on cross-ABI unwind edges causes UB on panic | **M1 (Mandatory Lowering):** Trivial CFG terminator rewrite; verify in Lean or keep in `PostCleanup` capture. |
| `LowerIntrinsics` | `lower_intrinsics.rs` | 346 | `Runtime(PostCleanup)` | `Required` (always) | `TerminatorKind::Call` to `IntrinsicDef` (`wrapping_add/sub/mul`, `unreachable`, `ub_checks`, `forget`, `copy_nonoverlapping`, `transmute`, `aggregate_raw_ptr`, `ptr_metadata`) | `forget` must use `Operand::Move` to deinitialize argument (`lower_intrinsics.rs:76-82`); `copy_nonoverlapping` overflow check | **M1 (Mandatory Lowering):** Essential bridge turning intrinsic calls into primitive MIR `StatementKind::Intrinsic` / `Rvalue::BinaryOp` / `CastKind::Transmute`. |
| `SimplifyCfg` / `SimplifyLocals` | `simplify.rs` | 538 | All phases (`Initial`..`Final`) | `Optional(true)` for CFG; `>= 1` for `SimplifyLocals` | Dead basic blocks, single-predecessor `Goto` chains, empty switches, unused `LocalDecl` compaction | Must preserve `START_BLOCK` and update `SwitchTargets` consistently | **M1/M2 (Mandatory CFG Cleanup + Local Compaction):** Adapt in Lean to prune unreachable blocks and dead temporaries before `AnLLVM` lowering. |
| `CleanupPostBorrowck` | `cleanup_post_borrowck.rs` | 94 | `Analysis(PostCleanup)` | `Required` (always) | Erases borrowck-only statements (`AscribeUserType`, `FakeRead`, `Assign(Fake)`, `Coverage::BlockMarker`) | Leaving `FakeRead` in runtime MIR causes spurious reads of uninit memory in Miri/codegen | **M1 (Mandatory Pre-Capture):** Pure erasure of borrow-checker ghost statements before `Runtime` phase. |
| `Derefer` / `EraseDerefTemps` / `ElaborateBoxDerefs` | `deref_separator.rs`, `erase_deref_temps.rs`, `elaborate_box_derefs.rs` | 356 | `Analysis` -> `Runtime(Initial)` | `Required` (always) | `DerefTemp` local markers, `Box<T>` unique pointer projection lowering | Debuginfo dangling references after `EraseDerefTemps` | **M1 (Mandatory Pre-Capture):** Normalizes `Box` derefs and temporary chains before `Runtime(PostCleanup)`. |
| `PostAnalysisNormalize` / `Subtyper` / `AddMovesForPackedDrops` / `CriticalCallEdges` | `post_analysis_normalize.rs`, `add_subtyping_projections.rs`, `add_moves_for_packed_drops.rs`, `add_call_guards.rs` | 561 | `Runtime(Initial)` | `Required` (always) | Reveal-all opaque type normalization, variance subtyping projections, aligned temporary copy before dropping `#[repr(packed)]` fields | Dropping unaligned `#[repr(packed)]` field in place is immediate alignment UB (`add_moves_for_packed_drops.rs:1-40`) | **M1 (Mandatory Pre-Capture):** Must run prior to `Runtime(PostCleanup)` capture so types are normalized and packed drops are aligned. |
| `RemovePlaceMention` / `RemoveNoopLandingPads` / `RemoveUninitDrops` / `RemoveUnneededDrops` | `remove_place_mention.rs`, `remove_noop_landing_pads.rs`, `remove_uninit_drops.rs`, `remove_unneeded_drops.rs` | 334 | `Analysis` / `Runtime` | `Required` / `Optional(true)` | Erases `PlaceMention` (unless `-Zmir-preserve-ub`), trivial `Drop`s on `Copy`/uninit types, empty landing pads | None | **M1 (Mandatory Cleanup):** Keep enabled in `PostCleanup`. |
| **`DestinationPropagation`** *(subsumes NRVO)* | `dest_prop.rs` | 670 | `Runtime(Optimized)` (runs twice: `lib.rs:794, 813`) | `mir_opt_level >= 2` | Unifies `dst = move src` across basic blocks when `!borrowed_locals.contains(src)` and `MaybeLiveLocals` ranges of `src` and `dst` are disjoint; **can unify `src` directly with `_0` (`RETURN_PLACE`) before ABI `sret` lowering** (`dest_prop.rs:18-20`) | **`#146383`**: deleting `StorageLive`/`StorageDead` instead of unioning intervals (`dest_prop.rs:273-278`) + interleaved same-statement read/write liveness (`dest_prop.rs:630-656`) | **M2 (High-Value MIR Optimization — Adapt):** Eliminates 256-byte aggregate `alloca`s and `llvm.memcpy`s into `_0` (`sret`) that LLVM `SROA`/`MemCpyOpt` **cannot** eliminate across diamond CFGs with calls (`Pattern 1`). Must fix `StorageLive` interval unioning in Anneal. |
| **`CopyProp` + `SsaLocals`** | `copy_prop.rs` + `ssa.rs` | 649 | `Runtime(Optimized)` (runs twice: `lib.rs:795, 814`) | `mir_opt_level >= 1` | Whole-local pseudo-SSA def-use graph (`SsaLocals`), destructive `Operand::Move` -> `Operand::Copy` conversion when unifying single-assignment chains (`_b = move? _a`), `!borrowed_locals` | If `src` may be `StorageDead` at a propagated use of `dst`, `StorageLive`/`StorageDead` markers must be widened/removed (`copy_prop.rs:59-92`) | **M2 (High-Value MIR Optimization — Adapt):** Eliminates single-assignment aggregate/scalar copy chains in $O(N)$ before `AnLLVM` `alloca` emission; pairs directly with `DestinationPropagation`. |
| **`ScalarReplacementOfAggregates` (`MirSROA`)** | `sroa.rs` | 431 | `Runtime(Optimized)` (`lib.rs:802`) | `mir_opt_level >= 2` | Typed `PlaceElem::Field(idx, ty)` projections on `Variants::Single` (structs/tuples), `Rvalue::Aggregate` decomposition into per-field `Rvalue::Use(op, WithRetag::Yes)`, syntactic `escaping_locals` visitor (`sroa.rs:58-143`) | Must exclude `union`s, `Variants::Multiple` (`enum`s), `#[repr(simd)]`, `#[repr(scalable)]`, and `DynMetadata` (`sroa.rs:163-172`); currently excludes `_0` (`RETURN_PLACE`, `sroa.rs:62`) | **M2 (High-Value MIR Optimization — Adapt):** Replaces typed struct/tuple/closure locals with scalar locals in one linear pass before `AnLLVM` ever creates stack `alloca`s, GEPs, or `memcpy`s. |
| **`Inline` & `ForceInline`** | `inline.rs` + `inline/cycle.rs` | 997 | `Runtime(Optimized)` (`lib.rs:774, 799`) | `ForceInline`: `Required`; `Inline`: `mir_opt_level >= 2` (or `>= 1` with LLVM optimizations) | Monomorphized `Instance` body splicing, closure `SpreadArgs` tuple unpacking (`inline.rs:480-520`), `StorageLive`/`StorageDead` wrapping of callee locals | Must check ABI/target-feature compatibility, unsized RVO params, and call-graph cycles (`inline/cycle.rs`); interacts with `DeduceParamAttrs` | **M2 (High-Value MIR Optimization — Adapt):** Inlines `#[inline]` closures, `Option::map`, and iterator adapters **before** `MirSROA` and `DestinationPropagation`, shrinking emitted LLVM functions by 60% in `Pattern 2`. |
| `RemoveZsts` / `RemoveStorageMarkers` | `remove_zsts.rs`, `remove_storage_markers.rs` | 145 | `Runtime(Optimized)` | `mir_opt_level >= 1` | `Layout::is_zst()` (turns writes to 0-sized types into `Nop`), removes `StorageLive`/`StorageDead` when `!emit_lifetime_markers` | Must not remove write through raw pointer if deref has UB check | **M2 (Lightweight MIR Cleanup — Adapt):** Eliminating ZST assignments in MIR avoids emitting dummy ZST operations into `AnLLVM`. |
| `GVN` (Global Value Numbering) | `gvn.rs` | 2,265 | `Runtime(Optimized)` (`lib.rs:791`) | `mir_opt_level >= 2` | `SsaLocals`, Miri `InterpCx` constant folding, `VnState` value numbering over `Rvalue`s, aggregate field forwarding | **`#120613`**, **`#141038`**, **`#110947`**, **`#118328`**: pointer provenance loss (`PtrToPtr` cast unification), `transmute` padding/uninit byte mishandling, vtable metadata canonicalization, floating-point NaN/signed-zero canonicalization | **M3 (Skip in MIR — Delegate to `AnLLVM`):** Highest bug density in `rustc_mir_transform` (2,265 LOC); 100% subsumed on scalar/pointer arithmetic by `AnLLVM`'s `GVN` + `InstCombine` (`Pattern 4`). |
| `JumpThreading` | `jump_threading.rs` | 1,127 | `Runtime(Optimized)` (`lib.rs:789`) | `mir_opt_level >= 2 && !is_like_gpu` | Backward `ConditionSet` propagation over `SwitchInt`, basic-block duplication (`MAX_COST = 100`) | **`#137086`** (unsound duplication of convergent GPU barriers); in `Pattern 2`, creates multi-predecessor triangle CFGs that **degrade** LLVM `SimplifyCFG` if-conversion (`1 BB -> 25 BBs`) | **M3 (Skip in MIR — Delegate to `AnLLVM`):** Complex 1,127-LOC CFG duplicator that actively interferes with LLVM's `SimplifyCFG` on unrolled adapter loops (`Pattern 2`) and is subsumed on state machines (`Pattern 3`). |
| `DataflowConstProp` | `dataflow_const_prop.rs` | 1,071 | `Runtime(Optimized)` (`lib.rs:771`) | `mir_opt_level >= 3` (not in `-Zmir-opt-level=2`) | `FlatSet<Scalar>` lattice over `rustc_mir_dataflow::value_analysis::Map`, `DummyMachine` `InterpCx` evaluation | Complex interaction with pointer provenance and partial overwrites; capped at `BLOCK_LIMIT = 100` due to cubic transfer cost | **M3 (Skip in MIR — Delegate to `AnLLVM`):** Not enabled at `rustc`'s default `-Zmir-opt-level=2`; completely subsumed by `AnLLVM` `SCCP` + `GVN`. |
| `InstSimplify` + `SimplifyComparisonIntegral` + `MatchBranchSimplification` + `EarlyOtherwiseBranch` | `instsimplify.rs`, `simplify_comparison_integral.rs`, `match_branches.rs`, `early_otherwise_branch.rs` | 1,890 | `Runtime(Optimized)` | `mir_opt_level >= 1` or `>= 2` | Peephole `Rvalue` rewrites, boolean/switch branch merging, enum discriminant equality switches | Duplicate-switch edge bugs when assumptions (`NonDivergingIntrinsic::Assume`) are dropped | **M3 (Skip in MIR — Delegate to `AnLLVM`):** Empirically 100% subsumed by `AnLLVM` `InstCombine` + `SimplifyCFG` (`Patterns 3 & 4`). |
| `ReferencePropagation` | `ref_prop.rs` | 467 | `Runtime(Optimized)` (`lib.rs:790`) | `mir_opt_level >= 2` | Rewrites `*_1` to `_2` when `_1 = &raw? mut? _2`, using `SsaLocals` and `MaybeStorageDead`; mutates all pointer moves into `Operand::Copy` (`ref_prop.rs:88-93`) | **`#63616`** / `deduce_param_attrs` interaction; risks introducing dereferences of `StorageDead` locals unless storage markers on the target local are deleted (`ref_prop.rs:51-55`) | **M3 (Skip in MIR — Delegate to `AnLLVM`):** Once `AnLLVM` `SROA` + `Mem2Reg` promotes stack pointers, local reference propagation happens automatically in SSA without `StorageDead` or `&mut` uniqueness hazards. |
| `DeadStoreElimination` | `dead_store_elimination.rs` | 156 | `Runtime(Optimized)` (`lib.rs:782, 809`) | `mir_opt_level >= 2` | Backward `Liveness` dataflow over `borrowed_locals` | Cannot eliminate stores to any local that has a borrow taken anywhere in the function | **M3 (Optional / Delegate to `AnLLVM`):** Subsumed for scalars by `Mem2Reg`/SSA dead-instruction elimination and for memory by `AnLLVM` `DSE`. |
| `SingleUseConsts` / `SsaRangeProp` / `UnreachablePropagation` / `UnreachableEnumBranching` / `LowerSliceLen` | `single_use_consts.rs`, `ssa_range_prop.rs`, `unreachable_prop.rs`, `unreachable_enum_branching.rs`, `lower_slice_len.rs` | 886 | `Runtime(Optimized)` | `mir_opt_level >= 1` or `>= 2` | Constant operand inlining, `PtrMetadata` range assumptions, unreachable block backward propagation (`Assume` insertion) | `UnreachableEnumBranching` relies on uninhabited variant validity rules | **M3 (Skip in MIR — Delegate to `AnLLVM`):** Subsumed by `AnLLVM` constant propagation and `CorrelatedValuePropagation`. |
| `DeduceParamAttrs` | `deduce_param_attrs.rs` | 239 | Post-`optimized_mir` query (`lib.rs:703`) | `opt_level != No` | Scans final `optimized_mir` to infer `readonly`, `noalias`, `captures(none)` on by-ref parameters (`UsageSummary`) | **Critical Phase-Ordering Hazard (`deduce_param_attrs.rs:8-10, 102-135`):** Marks unmodified by-value parameters as `readonly` assuming `DestinationPropagation`/`CopyProp` will **never** run afterwards | **Post-M2 Boundary Analysis:** Must run **only after** all Category M2 MIR passes (`DestProp`, `CopyProp`, `MirSROA`, `Inline`) have finished, immediately at the `MIR -> AnLLVM` lowering boundary. |

#### 3.3 Empirical Differential Ablation (`support/bench_patterns.rs`, `support/run_ablation.py`, `support/ablation_results.json`)

We evaluate six configurations on [`support/bench_patterns.rs`](support/bench_patterns.rs)
(`#![no_std]`) using `rustc 1.101.0-nightly` (`-Copt-level=2
-Cno-prepopulate-passes -Cpanic=abort --emit=llvm-ir`) and `/usr/bin/opt` (LLVM
21.1.8, `-passes='default<O2>' -S`):

| Pattern / Function | Config | LLVM Insts | `alloca`s | `llvm.memcpy`s | Basic Blocks | `load`s | `store`s |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| **Pattern 1:** `pattern1_large_aggregate_builder`<br>*(256-byte `[u64; 32]` builder + diamond branch + call)* | `C0` *(M1 only, no `opt`)* | 51 | **8** | **7** | 4 | 2 | 2 |
| | `C2_raw` *(M1 + M2, no `opt`)* | **29** | **0** | **0** | 4 | 3 | 6 |
| | `C3_raw` *(`mir-opt=2`, no `opt`)* | 44 | 1 | 1 | 4 | 3 | 10 |
| | `C1` *(M1 only + `opt -O2`)* | 34 | **2** | **2** | 1 | 0 | 8 |
| | `C2` *(M1 + M2 + `opt -O2`)* | **30** | **0** | **0** | **1** | **0** | **8** |
| | `C3` *(`mir-opt=2` + `opt -O2`)* | **30** | **0** | **0** | **1** | **0** | **8** |
| **Pattern 2:** `pattern2_option_adapter_chain`<br>*(8-iter loop with `Option::map` / `and_then` + `Pair<u64, u64>`)* | `C0` *(M1 only, no `opt`)* | 60 *(+14 callees)* | 7 | 0 | 9 | 9 | 7 |
| | `C2_raw` *(M1 + M2, no `opt`)* | 118 *(inlined)* | 7 | 0 | 25 | 19 | 21 |
| | `C3_raw` *(`mir-opt=2`, no `opt`)* | 100 *(inlined)* | 6 | 0 | 12 | 17 | 19 |
| | `C1` *(M1 only + `opt -O2`)* | 119 | 0 | 0 | 17 | 8 | 0 |
| | `C2` *(M1 + M2 + `opt -O2`)* | **117** | **0** | **0** | **1** | **8** | **0** |
| | `C3` *(`mir-opt=2` + `opt -O2`)* | 119 | 0 | 0 | **25** | 8 | 0 |
| **Pattern 3:** `pattern3_enum_state_machine`<br>*(`StepState` 4-variant enum -> `Result<u64, u32>` match chain)* | `C0` *(M1 only, no `opt`)* | 113 | 3 | 0 | 21 | 16 | 30 |
| | `C2_raw` *(M1 + M2, no `opt`)* | 113 | 3 | 0 | 21 | 16 | 30 |
| | `C3_raw` *(`mir-opt=2`, no `opt`)* | 69 | 3 | 0 | 7 | 9 | 19 |
| | `C1` *(M1 only + `opt -O2`)* | **14** | **0** | **0** | **4** | **0** | **3** |
| | `C2` *(M1 + M2 + `opt -O2`)* | **14** | **0** | **0** | **4** | **0** | **3** |
| | `C3` *(`mir-opt=2` + `opt -O2`)* | **14** | **0** | **0** | **4** | **0** | **3** |
| **Pattern 4:** `pattern4_scalar_cse_loop`<br>*(16-element loop with duplicate `x*k1 + k2` and identity ops)* | `C0` *(M1 only, no `opt`)* | 37 | 2 | 0 | 6 | 6 | 4 |
| | `C2_raw` *(M1 + M2, no `opt`)* | 35 | 2 | 0 | 6 | 6 | 4 |
| | `C3_raw` *(`mir-opt=2`, no `opt`)* | 29 | 2 | 0 | 6 | 6 | 4 |
| | `C1` *(M1 only + `opt -O2`)* | **10** | **0** | **0** | **1** | **1** | **0** |
| | `C2` *(M1 + M2 + `opt -O2`)* | **10** | **0** | **0** | **1** | **1** | **0** |
| | `C3` *(`mir-opt=2` + `opt -O2`)* | **10** | **0** | **0** | **1** | **1** | **0** |
| **Pattern 5:** `pattern5_drop_elaboration`<br>*(Unconditional move + conditional move of `Drop` `Guard`)* | `C0` *(M1 only, no `opt`)* | 39 | 5 | 0 | 6 | 6 | 9 |
| | `C2_raw` *(M1 + M2, no `opt`)* | 37 | 5 | 0 | 6 | 6 | 9 |
| | `C3_raw` *(`mir-opt=2`, no `opt`)* | 30 | 4 | 0 | 4 | 5 | 5 |
| | `C1` *(M1 only + `opt -O2`)* | **23** | **3** | **0** | **4** | **0** | **3** |
| | `C2` *(M1 + M2 + `opt -O2`)* | **23** | **3** | **0** | **4** | **0** | **3** |
| | `C3` *(`mir-opt=2` + `opt -O2`)* | **23** | **3** | **0** | **4** | **0** | **3** |

Whole-module totals across [`support/bench_patterns.rs`](support/bench_patterns.rs):

| Config | Description | Emitted Functions | Total Insts | Total `alloca`s | Total `llvm.memcpy`s | Total BBs | Total `load`s | Total `store`s |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `C0` | `-Zmir-opt-level=0` (pre-`opt`) | 20 | 454 | 29 | 11 | 79 | 55 | 78 |
| `C2_raw` | `-Zmir-opt-level=0` + **Category M2** (pre-`opt`) | **8** (`-60%`) | **352** (`-22.5%`) | **18** (`-37.9%`) | **1** (`-90.9%`) | 65 | 51 | 74 |
| `C3_raw` | `-Zmir-opt-level=2` (pre-`opt`) | 7 (`-65%`) | 277 (`-39.0%`) | 16 (`-44.8%`) | 1 (`-90.9%`) | 35 | 41 | 57 |
| `C1` | `-Zmir-opt-level=0` + `opt -O2` | 6 | 203 | 5 | **2** | 28 | 10 | 14 |
| `C2` | `-Zmir-opt-level=0` + **Category M2** + `opt -O2` | **6** | **197** | **3** | **0** | **12** | **10** | **14** |
| `C3` | `-Zmir-opt-level=2` + `opt -O2` | 6 | 199 | 3 | 0 | 36 | 10 | 14 |

#### 3.4 Four Semantic Refinements to Anneal's `MirAst` and `MirSemantics`

1. **Refinement 1 — Three-State `LocalSlot` (`.dead`, `.uninit`, `.init v`) +
   Explicit `Operand::Move` Deinitialization + `StorageLive` Unioning:** In
   `rustc`, `dest_prop.rs:273-278` deletes `StorageLive`/`StorageDead` markers
   rather than unioning them (`FIXME: Don't delete storage statements, but
   "merge" the storage ranges instead`), which caused `rust-lang/rust#146383`.
   Refining `MirState.locals` to `Local → LocalSlot` (`.dead | .uninit | .init
   v`) where writing to `.dead` is immediate `.ub` and requiring
   `DestinationPropagation` and `CopyProp` to **union** the
   `StorageLive`..`StorageDead` intervals of `src` and `dst` eliminates `#146383`
   by construction (`destProp_with_live_union_compiles` and
   `canary_destProp_without_live_union_violates_compiles` in
   [`support_mir_transform_adaptation_probe.lean`](support/support_mir_transform_adaptation_probe.lean)).
2. **Refinement 2 — Explicit `isAddressTaken : Local → Bool` Declaration
   Invariant + `RETURN_PLACE` Field Forwarding in `MirSROA` / `DestProp`:**
   Recording `isAddressTaken : Local → Bool` directly in `MirBody` allows
   `MirSROA` to be formulated as a projection-tree isomorphism over
   `MirState.locals` for any `Variants::Single` local `l` with `!isAddressTaken
   l`, and decomposing `_0 = Rvalue::Aggregate(Adt, [Move(src)])` into `_0.0 =
   move src` closes the `C3_raw` inlined-constructor gap before `AnLLVM` runs.
3. **Refinement 3 — Two-Stage `PreDropMirLang -> MirLang` Lowering for
   `ElaborateDrops`:** Defining `PreDropMirLang` (where `Terminator.drop place
   target` drops `place` iff its `LocalSlot` is currently `.init`) allows
   `ElaborateDrops` to be verified as a `PassCompiler PreDropMirLang MirLang
   preDropToMirCodec` (`elaborateDrops_compiles` and
   `canary_elaborateDrops_missing_move_clear_unsound`).
4. **Refinement 4 — Phase-Locked `DeduceParamAttrs` at the `MIR -> AnLLVM`
   Lowering Boundary:** Never deduce `readonly`/`noalias`/`captures(none)` on
   intermediate MIR phases; compute them exclusively as part of final `MIR ->
   AnLLVM` lowering after `DestinationPropagation`, `CopyProp`, `MirSROA`, and
   `Inline` have completed.

#### 3.5 `FunctionCx`, `LocalAnalyzer`, `TagEncoding::Niche`, and Eliminating the 6 Upstream-LLVM Workarounds

In `compiler/rustc_codegen_ssa/src/mir/mod.rs:203-393` and `mir/analyze.rs:17-407`:
- `codegen_mir` computes `traversal_order =
  traversal::mono_reachable_reverse_postorder(mir, tcx, instance)` and calls
  `analyze::non_ssa_locals(&fx, &traversal_order)` to partition MIR locals into
  dominating SSA operands (`LocalKind::SSA(DefLocation)` ->
  `LocalRef::PendingOperand` / `LocalRef::Operand`) and memory-backed places
  (`LocalKind::Memory` -> `LocalRef::Place(PlaceRef::alloca)`). Because RPO
  visits every dominator before any dominated block, every `PendingOperand` is
  overwritten once before any use is lowered.
- For `TagEncoding::Niche { untagged_variant, niche_variants, niche_start }`,
  `codegen_tag_value` (`mir/place.rs:478-534`) encodes niche variants via
  `((variant_index - niche_variants.start) + niche_start) mod M`, and
  `OperandRef::codegen_get_discr` (`mir/operand.rs:458-699`) decodes via wrapping
  subtraction `relative_discr = (tag - niche_start) mod M` and
  `IntULE(relative_discr, relative_max)`. Theorem
  `codegen_get_set_discr_niche_roundtrip` in
  [`support_mir_to_anllvm_lowering_probe.lean`](support/support_mir_to_anllvm_lowering_probe.lean)
  proves this round-trip identity universally for all moduli $M > 0$.

| # | Upstream `rustc_codegen_ssa` / `rustc_codegen_llvm` Workaround | Exact Source Locations (`49d734536222bf28bb6d07d885b3a81d145981da`) | Clean-Slate `AnLLVM` Design |
| :--- | :--- | :--- | :--- |
| **1** | **`PassMode::Cast` Memory Bounce via Temporary `alloca`** | `mir/mod.rs:341-345, 603-606`, `rustc_codegen_llvm/src/abi.rs:251-282, 310-313`, `mir/block.rs:612-648, 2009-2013, 2058-2098, 2474-2586` | `AnLLVM` represents register words as `MaskedWord64` (per-byte/per-bit initialization mask) and provides first-class `pack_cast_regs(op, layout, cast_target)` and `unpack_cast_regs(reg_tuple, cast_target, layout)` instructions. Padding bytes remain `init = false` inside the register word without contaminating adjacent initialized field bytes (`init = true`), eliminating 4 `alloca`s and 2 `llvm.memcpy`s per C-ABI call site. |
| **2** | **`Rvalue::Cast(CastKind::Transmute)` Memory Bounce via `alloca`** | `FunctionCx::codegen_transmute_operand` (`mir/rvalue.rs:332-440`, fallback arm at `421-439`) and `codegen_transmute` (`mir/rvalue.rs:303-327`) | `AnLLVM`'s `bitcast_bytes(op, src_layout, dst_layout)` slices and concatenates `MaskedWord` byte ranges directly in SSA registers (`evalRegisterTransmute`), handling `Scalar <-> ScalarPair` and `Padded <-> u64` in 1 step with zero `alloca`s. |
| **3** | **Entry-Block Untyped `alloca` Hoisting + `llvm.lifetime.start/end`** | `mir/mod.rs:326-369`, `rustc_codegen_llvm/src/builder.rs:670-680, 1462-1468, 1911-1929`, `mir/place.rs:316-322`, `mir/statement.rs:72-85` | `AnLLVM` declares static stack frame slots in the function header (`FrameSlot(slot_id, size, align)`) and lowers `StorageLive(local)` / `StorageDead(local)` 1-to-1 to `AllocaLive(slot_id)` / `AllocaDead(slot_id)`. |
| **4** | **`SwitchInt` on Niche Discriminants and `icmp` + `@llvm.assume` Chains** | `OperandRef::codegen_get_discr` (`mir/operand.rs:458-699`, `llvm-project#134024` workaround at `588-597`), `codegen_switchint_terminator` (`mir/block.rs:429-565`) | `AnLLVM` provides a first-class `decode_niche_discr(tag, NicheConfig)` operation backed by the universal modular round-trip identity (`codegen_get_set_discr_niche_roundtrip`) and native `SwitchInt` across `i8`..`i128`. |
| **5** | **`noalias` / `readonly` / `dereferenceable` / `noundef` Attribute Juggling vs. Tree Borrows** | `rustc_ty_utils/src/abi.rs:322-420, 669-691`, `rustc_codegen_llvm/src/abi.rs:59-113`, `builder.rs:750-785`, `mir/retag.rs:1-536` | `AnLLVM` uses first-class Tree Borrows `BorrowTag` / `ProtectorId` annotations and bitmask `noundef_mask` attributes rather than ISO C 1999 `restrict` metadata scopes. |
| **6** | **111 `BuilderMethods` Action Methods (`traits/builder.rs:51-690`)** | `compiler/rustc_codegen_ssa/src/traits/{builder.rs,abi.rs,intrinsic.rs,type_.rs,consts.rs}` | Partition cleanly into 8 `AnLLVM` instruction families: (1) CFG & Terminators (15), (2) Integer/Bitwise ALU + Overflow (28), (3) Floating-Point ALU (15), (4) Casts & Byte Pack/Unpack (24 + 3 new), (5) Stack Frame & Memory (23), (6) Atomics & Sync (6), (7) Calls, ABI & Unwinding (17), and (8) Validity & Tree Borrows Retags (13). |

Empirical `rustc --emit=mir,llvm-ir` measurements
([`support/empirical_probe.rs`](support/empirical_probe.rs),
[`support/empirical_probe_opt1.mir`](support/empirical_probe_opt1.mir),
[`support/empirical_probe_opt1_nollvm.ll`](support/empirical_probe_opt1_nollvm.ll)):

| Probe Function (`support/empirical_probe.rs`) | MIR Operation | Upstream `rustc_codegen_llvm` Output (`support/empirical_probe_opt1_nollvm.ll`) | Clean-Slate `AnLLVM` Output | `alloca` Reduction |
| :--- | :--- | :--- | :--- | :--- |
| `probe_pass_mode_cast_caller` | Construct `Padded { a, b }`, pass by value (`PassMode::Cast` `i64`), return result | **4 `alloca`s** (`%0, %1, %2, %_0`), **4 `lifetime.start/end`**, **2 `llvm.memcpy`**, 4 stores, 3 loads, 1 call (19 instructions) | `pack_cast_regs(a, b) -> %arg`, `call @probe_pass_mode_cast_modify(%arg) -> %ret`, `ret %ret` (**3 instructions, 0 `alloca`s**) | **4 -> 0 (-100%)** |
| `probe_pass_mode_cast_construct` | Return `Padded { a, b }` via `PassMode::Cast` (`i64`) | **1 `alloca`** (`%_0`), 2 stores, 1 GEP, 1 widened `load i64, ptr %_0, align 4`, `ret` (6 instructions) | `pack_cast_regs(a, b) -> %0`, `ret %0` (**2 instructions, 0 `alloca`s**) | **1 -> 0 (-100%)** |
| `probe_transmute_pair_to_u64` | `transmute::<(u32, u32), u64>(pair)` | **1 `alloca`** (`%0`), **2 `lifetime.start/end`**, 2 `store i32`, 1 GEP, 1 `load i64`, `ret` (8 instructions) | `bitcast_bytes(pair, Pair32ToU64) -> %0`, `ret %0` (**2 instructions, 0 `alloca`s**) | **1 -> 0 (-100%)** |
| `probe_transmute_u64_to_pair` | `transmute::<u64, (u32, u32)>(bits)` | **1 `alloca`** (`%0`), **2 `lifetime.start/end`**, 1 `store i64`, 2 `load i32`, 1 GEP, 2 `insertvalue`, `ret` (10 instructions) | `bitcast_bytes(bits, U64ToPair32) -> %0`, `ret %0` (**2 instructions, 0 `alloca`s**) | **1 -> 0 (-100%)** |
| `probe_transmute_padded_to_u64` | `transmute::<Padded, u64>(p)` | **1 `alloca`** (`%0`), **2 `lifetime.start/end`**, `store i8`, GEP, `store i32`, `load i64 !noundef`, `ret` (8 instructions; attaches `!noundef` to `load i64` across 3 uninitialized padding bytes at line 358!) | `bitcast_bytes(p, PaddedPairToWord64) -> %0`, `ret %0` (**2 instructions, 0 `alloca`s**, padding bytes explicitly `init = false`) | **1 -> 0 (-100%)** |

---

### 4. Syntax-Directed Symbolic Execution (`wpX86`), In-Place Canonical Cut-Points (`wpX86Cut`), and Inductive Loop Verification

#### 4.1 Entry-State Canonicalization (`forallTypedArgs`) and Syntax-Directed `wpX86`

In `Trusted/X86Semantics.lean`, `initX86State` defines entry states relationally
(`s.mem 0 = none ∧ argsMatchStack s.tySizes body.argTys s.mem`). In
[`support/SymbolicVCGenProbe.lean`](support/SymbolicVCGenProbe.lean),
`buildArgMem` constructs the concrete entry memory for any argument list, and
`forallTypedArgsAux` unpacks each `X86Ty` into its unique `X86Val` constructor
while substituting `buildArgMem` into the goal via `funext`:

```lean
noncomputable def forallTypedArgsAux (tySizes : Nat → Nat) :
    List X86Ty → (List X86Val → Prop) → Prop
  | [], k => k []
  | .usize :: tys, k =>
      ∀ a : Nat, forallTypedArgsAux tySizes tys (fun vs => k (.word64 a :: vs))
  | .bool :: tys, k =>
      ∀ b : Bool, forallTypedArgsAux tySizes tys (fun vs => k (.boolVal b :: vs))
  | .unit :: tys, k =>
      forallTypedArgsAux tySizes tys (fun vs => k (.unit :: vs))
  | .adt id :: tys, k =>
      ∀ a : Nat, forallTypedArgsAux tySizes tys (fun vs => k (.adt id (.word64 a) :: vs))
  | .param idx :: tys, k =>
      ∀ bits : Nat, forallTypedArgsAux tySizes tys
        (fun vs => k (.bytes (tySizes idx) bits :: vs))
  | .refParam _ :: tys, k =>
      ∀ slot : Nat, forallTypedArgsAux tySizes tys
        (fun vs => k (.stackPtr slot :: vs))
```

Once `s.mem` is replaced by `buildArgMem`, every slot lookup `s.mem idx`
(including out-of-bounds slots `idx > argTys.length`) reduces to `some v_idx` or
`none` by pure kernel `whnf`/`rfl`. `wpX86` then computes a sufficient
verification condition for `SafeAndEnsures P out` across all `n : Nat` by
recursing on `fuel : Nat`:

```lean
noncomputable def wpX86 :
    Nat → X86Body → X86State → (X86Val → Prop) → Prop
  | 0, _, _, _ => False
  | fuel' + 1, rootBody, s, P =>
      let activeBody := match s.curBody with | none => rootBody | some b => b
      match activeBody.blocks[s.bb]? with
      | none => False
      | some blk =>
          match blk.instrs[s.ip]? with
          | some instr =>
              match evalX86Instr s instr with
              | .step s' => wpX86 fuel' rootBody s' P
              | .terminated (.normal ret) => P ret
              | .terminated .unwind => True
              | .failed _ => False
          | none =>
              match blk.term with
              | .jccBool cond falseTarget trueTarget =>
                  match evalX86Operand s.mem cond with
                  | some (.boolVal b, mem') =>
                      (b = false →
                        wpX86 fuel' rootBody
                          { s with mem := mem', bb := falseTarget.index, ip := 0 } P) ∧
                      (b = true →
                        wpX86 fuel' rootBody
                          { s with mem := mem', bb := trueTarget.index, ip := 0 } P)
                  | _ => False
              | .repMovsbJmp dst srcTy dstTy ptrOp target => ...
              | term =>
                  match evalX86Term rootBody s term with
                  | .step s' => wpX86 fuel' rootBody s' P
                  | .terminated (.normal ret) => P ret
                  | .terminated .unwind => True
                  | .failed _ => False
```

| Benchmark Suite | Manual `MirLemmas.lean` Lines | `SymbolicVCGenProbe.lean` Lines | AST-Shape Invariance Verified |
| :--- | :---: | :---: | :--- |
| **`id` (`Copy`, `Move`, `const`, `idMultiTempBody k`)** | ~140 lines (20–34 each) | **18 lines total** (1–3 each) | `idMultiTempBody k` has parametric `slotCount := k`, 3 temp copies, interleaved `nop`s, and reordered `deallocSlot`; proved by `(fun _ _ => rfl)`. |
| **Binary ALU (8 ops) & Cmp (6 ops) + `binOpExtraTempsBody`** | ~295 lines (65–82 each) | **32 lines total** (4–8 each) | `binOpExtraTempsBody` has `slotCount = 9` and 2 basic blocks (`jmp`); proved by `(fun _ _ _ => ensuresBinOp_of_eq rfl rfl rfl)`. |
| **`max_usize` (4-block diamond) & `clamp_usize` (6-block 3-way branch)** | 132 lines (`max_usize` `RetLibInv` only) | **3 lines** (`max_usize` `RetLibInv`), **9 lines** (full `if`/`else` spec); **5 / 16 lines** (`clamp_usize`) | Proves full functional specifications `ret = .word64 (if a < b then b else a)` and `ret = .word64 (if x < lo then lo else if hi < x then hi else x)`. |
| **PME `sizeEqConst` (`slotCount = 5` & `6`), `transmute_checked`, `outer_transmute` (`call1`)** | 262 lines (64 + 95 + 103) | **15 lines total** (1 + 1 + 6 + 7) | Identical 1-line proof `constSucceeds_extract 20 h ⟨fun _ => True.intro, of_decide_eq_true⟩` verifies both `slotCount = 5` and `slotCount = 6`. |
| **`NonZeroUsize` Library (`make_nonzero`, `new_unchecked`, `get_unchecked_nonzero`, 2-call `sanitize_nonzero`)** | 206 lines (3 fns) | **16 lines total** (4 fns: 2 + 3 + 3 + 8) | Proves end-to-end 4-function `CrateTheorem` (`prove_nonzero_four_fn_crate`) with `sanitizeNonZeroBody` chaining two `call1` calls across 3 basic blocks. |

#### 4.2 In-Place Canonical Memory Normalization (`canonMemUpTo`), Cut-Point `wpX86Cut`, and Strong-Induction Loop Verification (`wpX86_loop_sound`)

In [`support/LoopAndJoinVCGenProbe.lean`](support/LoopAndJoinVCGenProbe.lean):

```lean
noncomputable def canonMemUpTo :
    Nat → (Nat → Option X86Val) → (Nat → Option X86Val)
  | 0, _ => fun _ => none
  | k + 1, m => updateSlot (canonMemUpTo k m) k (m k)

noncomputable def canonState (B : Nat) (s : X86State) : X86State :=
  { s with mem := canonMemUpTo B s.mem }
```

1. **In-Place Spine Rebuild & Unconditional Forward Simulation (`StateSubsumed`):**
   `canonMemUpTo B m` evaluates `m 0 ..< B` by kernel `whnf` and rebuilds a
   canonical `updateSlot` spine of length `B` rooted at `fun _ => none`. Because
   `evalX86Operand`, `evalX86Instr`, and `evalX86Term` only require `MemSubsumed
   cm m : ∀ i v, cm i = some v → m i = some v`, `canonState_subsumed : ∀ B s,
   StateSubsumed (canonState B s) s` holds **unconditionally** for every `B :
   Nat` and `s : X86State`, and `evalX86Step_subsumed` lifts every non-failing
   step of `cs` to `s`.
2. **Cut-Point `wpX86Cut` and Strong Induction (`wpX86_loop_sound`):**
   Every query `q : ExecQuery X86State` supplies a finite step budget `q.steps :
   Nat`, and whenever `q.steps` runs out while a loop is still executing,
   `ReachesPrefix` produces `out.outcome = .running` (where `SafeAndEnsures P
   .running` is `True`). Because `wpX86Cut` takes $k \ge 1$ transitions before
   reaching `headerBb`, remaining prefix fuel strictly decreases (`n' < steps`),
   allowing `nat_strong_ind` (`reachesPrefix_of_loop_invariant` and
   `wpX86_loop_sound`) to discharge unbounded `while` loops without a
   termination ranking function:

| Verified Benchmark in `LoopAndJoinVCGenProbe.lean` | CFG Structure | Verified Theorems | Proof Size |
| :--- | :--- | :--- | :---: |
| **`countUpLoopBody`** | `while i < n { i = i + 1 } return i` (4 blocks, back-edge `bb3 -> bb1`) | `countUpLoopBody_retLibInv`, `countUpLoopBody_wellFormed`, `countUpLoopBody_ensures_eq_arg` (`ret = .word64 n`), `prove_count_up_loop_crate` | 4–9 lines |
| **`sumLoopBody`** | 2-arg loop accumulating `x` into `acc` `n` times while mutating/deallocating scratch slots `5, 6, 7` every iteration | `sumLoopBody_retLibInv`, `sumLoopBody_ensures_product` (`ret = .word64 (x * n)`), `prove_sum_loop_crate` | 5–20 lines |
| **`nonZeroLoopBody`** | `NonZeroUsize` loop extracting `x.0`, incrementing in a loop, and wrapping `.adt 0` under custom `nonZeroLibInv` | `nonZeroLoopFn_retLibInv`, `prove_non_zero_loop_crate` | 7 lines |
| **`loopWithInternalDiamondBody`** | Loop containing an internal `if i < k / else` diamond mutating asymmetric scratch slots `6` vs `7, 8` before jumping to `bb1` | `loopWithInternalDiamondBody_retLibInv`, `loopWithInternalDiamondBody_ensures_ge` (`ret ≥ n`), `prove_loop_with_internal_diamond_crate` | 8–12 lines |
| **`asymmetricDiamondJoinBody`** | `bb0 -> (bb1 \| bb2) -> bb3` (`bb1` uses scratch slot `4`; `bb2` uses scratch slots `5, 6`; both merge by `rfl` at `bb3`) | `asymmetricDiamondJoinBody_ensures`, `asymmetricDiamondJoinBody_retLibInv` | 4 lines |
| **`doubleDiamondChainBody`** | 2-stage chained diamond `bb0 -> (bb1 \| bb2) -> bb3 -> (bb4 \| bb5) -> bb6` verified via two `byIndexedCut` stages ($O(D)$) | `doubleDiamondChainBody_retLibInv`, `doubleDiamondChainBody_ensures_gt20` (`ret > 20`), `prove_double_diamond_chain_crate` | 9–12 lines |

---

### 5. Variable-Step Compiler Refinement (`π_opt`, `π_progress K`, `π_elastic`) and Stateful Peephole Passes

#### 5.1 Exact `ReachesPrefix` Horizon Laws and Why Lockstep Morphisms Fail When $k_1 \neq k_2`

Because `ReachesPrefix.terminated` and `ReachesPrefix.failed` carry an arbitrary
`n : Nat` in their fuel index `n + 1`, any terminal or failed execution prefix
remains valid at all larger fuel budgets (**Terminal Stabilization Law**,
`reachesPrefix_add_of_terminated` and `reachesPrefix_add_of_failed` in
[`support/VariableStepCompilesProbe.lean`](support/VariableStepCompilesProbe.lean)):
$$\text{ReachesPrefix } M\ p\ \text{init}\ n\ s\ tr\ (\text{.terminated } t) \implies \text{ReachesPrefix } M\ p\ \text{init}\ (n + d)\ s\ tr\ (\text{.terminated } t)$$

For a deterministic `Obs = Unit` machine (`detMachine evalStep`) where `s₀`
steps $k$ times via `.step ()` to `s_k` and then steps to `.terminated term`:
- For all $\text{steps} \le k$ (`reachesPrefix_iff_of_steps_le`):
  $tr = \text{List.replicate steps } () \land \text{out} = \text{.running}$.
- For all $\text{steps} \ge k + 1$ (`reachesPrefix_iff_of_steps_gt`):
  $tr = \text{List.replicate } k\ () \land \text{out} = \text{.terminated term}$.

Whenever a compiler pass changes the step count ($k_1 \neq k_2$),
`not_compiles_lockstep_progWithNop_progWithoutNop` and
`not_compiles_any_trace_preserving_query_map` prove that both `π = id` and every
trace-preserving query reindexing `q ↦ f(q)` are refuted.

#### 5.2 Hierarchy of Step-Abstracting Behavior Morphisms (`π_opt`, `π_progress K`, `π_elastic`)

In [`support/VariableStepCompilesProbe.lean`](support/VariableStepCompilesProbe.lean),
we define three monotone behavior morphisms in `theory/`:

```lean
def π_elastic (decompileInit : State₂ → State₁)
    (decompileOutcome : PrefixOutcome Term₂ Err₂ → PrefixOutcome Term₁ Err₁)
    (b : ExecBehavior State₁ Unit Term₁ Err₁) :
    ExecBehavior State₂ Unit Term₂ Err₂ :=
  fun q₂ =>
    { defined := ∀ n₁ : Nat, (b ⟨decompileInit q₂.init, n₁⟩).defined
      val := fun out₂ =>
        ∃ (n₁ : Nat) (tr₁ : List Unit),
          (b ⟨decompileInit q₂.init, n₁⟩).val
            ⟨tr₁, decompileOutcome out₂.outcome⟩ }

def π_progress (K : Nat) (decompileInit : State₂ → State₁)
    (decompileOutcome : PrefixOutcome Term₂ Err₂ → PrefixOutcome Term₁ Err₁)
    (b : ExecBehavior State₁ Unit Term₁ Err₁) :
    ExecBehavior State₂ Unit Term₂ Err₂ :=
  fun q₂ =>
    { defined := ∀ n₁ : Nat, (b ⟨decompileInit q₂.init, n₁⟩).defined
      val := fun out₂ =>
        ∃ (n₁ : Nat) (tr₁ : List Unit),
          q₂.steps ≤ K * n₁ + (K - 1) ∧
          (b ⟨decompileInit q₂.init, n₁⟩).val
            ⟨tr₁, decompileOutcome out₂.outcome⟩ }

def π_opt := π_progress 1
```

| Morphism | Witness Fuel Constraint | Preserves `SpecOn` (`WellFormed`, `Ensures*`)? | Prevents Introducing Silent Infinite Loops? | Supported Variable-Step Passes |
| :--- | :--- | :---: | :---: | :--- |
| **`id` (Lockstep)** | $n_1 = q_2.\text{steps}$ and $tr_1 = tr_2$ | Yes | Yes | 1-to-1 instruction rewrites (`simplifyAddZero`) |
| **`π_opt` (`π_progress 1`)** | $q_2.\text{steps} \le n_1$ | Yes | **Yes** (`not_compiles_π_opt_infinite_loop`) | Arbitrary instruction deletion & many-to-1 fusion (`stripNops`, `elimDeadStoreDealloc`, `fuseScratchMov`) |
| **`π_progress K` ($K \ge 1$)** | $q_2.\text{steps} \le K \cdot n_1 + (K - 1)$ | Yes | **Yes** (`not_compiles_π_progress_infinite_loop`) | Deletion + up to 1-to-$K$ instruction expansion (`expandImmMov` with $K = 2$) |
| **`π_elastic`** | Unconstrained $n_1 : \text{Nat}$ | Yes (`π_elastic_specOn_le`) | **No** ($n_1 = 0$ matches `.running` forever) | Arbitrary step rescaling when only partial correctness / safety (`SpecOn`) is required |

#### 5.3 Block-Suffix Simulation and Stateful Peephole Passes (`elimDeadStoreDealloc`, `fuseScratchMov`, `optPipeline`)

In [`support/StatefulVariableStepProbe.lean`](support/StatefulVariableStepProbe.lean),
combining the **Block-Suffix Simulation Pattern** (`(passBlock blk).instrs.drop
s_tgt.ip = passInstrs (blk.instrs.drop s_src.ip)`) with zero-`funext`
extensional memory congruence (`MemExtEq m₁ m₂ : ∀ i, m₁ i = m₂ i` and
`MemAgreesExcept deadSlot m₁ m₂ : ∀ i, i ≠ deadSlot → m₁ i = m₂ i`) proves
universal `Compiles X86Lang X86Lang π_x86_opt` soundness for:
1. **`elimDeadStoreDealloc_compiles_opt`:** Rewrites `.mov tmp (.imm v) ::
   .deallocSlot d :: rest` (when `tmp.index == d.index`) to `.deallocSlot d ::
   elimDeadStoreDeallocInstrs rest`.
2. **`fuseScratchMov_compiles_opt`:** Rewrites `.mov tmp (.imm v) :: .mov dst
   (.stackSlot s consume) :: .deallocSlot d :: rest` (when `tmp.index == s.index
   && tmp.index == d.index && !(dst.index == d.index)`) to `.mov dst (.imm v) ::
   .deallocSlot d :: fuseScratchMovInstrs rest` via a two-phase `SimPass ∨
   SimPendingDealloc` simulation.
3. **`optPipeline_compiles_opt`:** Composes `fuseScratchMov`,
   `elimDeadStoreDealloc`, and `stripNops` via `compiles_opt_trans` and verifies
   `stage0Body_optPipeline_verified`.

## Boundaries

- **Textual `--emit=mir` vs. `TyCtxt` Extraction:** Textual `rustc --emit=mir`
  and `-Z print-type-sizes` cannot substitute for `TyCtxt` extraction in
  `anneal-rustc-capture`, because neither emits `FnAbi` `PassMode`s,
  `#[track_caller]` implicit `&Location` arguments, `TagEncoding::Niche`
  parameters (`untagged_variant`, `niche_variants`, `niche_start`), tuple field
  offsets, or `body.required_consts()`.
- **Pass Registration Names in `rustc`:** Passing `-Z
  mir-enable-passes=+InstSimplify` to `rustc` is a no-op with an unknown-pass
  warning; the pass is registered as `InstSimplify-before-inline` and
  `InstSimplify-after-simplifycfg`.
- **Phase-Ordering of `DeduceParamAttrs`:** `DeduceParamAttrs`
  (`deduce_param_attrs.rs:102-135`) must never run before Category M2 MIR passes
  (`DestinationPropagation`, `CopyProp`, `MirSROA`, `Inline`), as marking
  by-value locals `readonly` before `DestinationPropagation` is unsound.
- **Partial Correctness (`wpX86_loop_sound`) vs. Total Termination (`π_opt`):**
  `wpX86_loop_sound` proves `SafeAndEnsures P out` over all `ReachesPrefix`
  queries without a ranking function; proving total liveness requires a
  well-founded ranking measure on the loop header family `α`. Conversely, for
  compiler transformations, unconstrained `π_elastic` does not preserve
  termination; passes that must forbid introducing silent infinite loops must
  use `π_opt` (`q₂.steps ≤ n₁`) or `π_progress K` (`q₂.steps ≤ K * n₁ + (K - 1)`).
- **`noncomputable def` Requirement on `Prop` Recursors:** Recursive
  `Prop`-valued definitions in `theory/` (`wpX86`, `wpX86Cut`, `necX86Normal`,
  `forallTypedArgsAux`, `canonMemUpTo`) must carry `noncomputable def` in Lean
  `v4.34.1` so `addPreDefinitions` does not emit `<fn>._unsafe_rec`
  (`isPartial = true`).

## Evidence

All findings in this report are backed by the 8 standalone Lean 4.34.1 probes
and 13 Rust/LLVM empirical support artifacts preserved in this package:

- **Byte Provenance & `rustc_driver` Capture Artifacts:**
  - [`support/ByteMemoryProvenanceProbe.lean`](support/ByteMemoryProvenanceProbe.lean)
    (`sha256: d584229501aa70396798f81fe77666cc09bdc1c0d1ca6ccb05f95045389a336b`,
    2,625 lines, 0 `sorry`).
  - [`support/Phase3SemanticsProbe.lean`](support/Phase3SemanticsProbe.lean)
    (`sha256: 348282b85d13eb49c685e639adfac4e0627e6dd4d7f9ea9e289d8755e4b89379`,
    4,862 lines, 0 `sorry`).
  - [`support/probe_6cat.rs`](support/probe_6cat.rs)
    (`sha256: 8d4f9acf88995a4e354635a8fba058b17a26f8e82ae8d24c097c39c6379a8c50`).
  - [`support/layout_mir_driver.rs`](support/layout_mir_driver.rs)
    (`sha256: e79065ef77adf4a879e0278e1deabe1d94e62f34d4e3fd4ebc75152c8921d0a9`).
  - [`support/monomorph_mir_driver.rs`](support/monomorph_mir_driver.rs)
    (`sha256: 76a5061bd910780d1a55169f63ee2dea293f1b78848a52a7857483a19ebd7e60`).
  - [`support/driver_extracted_metadata.txt`](support/driver_extracted_metadata.txt)
    (`sha256: 87c1d3647146d498a7018001a96d37d3fffda0894825c7abe120e01ac3743641`).
  - [`support/monomorph_driver_output.txt`](support/monomorph_driver_output.txt)
    (`sha256: a4c4018d664ef0c3f197e5977b1b2bfa225c9265c689ffcd54641fc93a10c7c0`).
- **MIR Transform Division of Labor & `MIR -> AnLLVM` Lowering Artifacts:**
  - [`support/support_mir_transform_adaptation_probe.lean`](support/support_mir_transform_adaptation_probe.lean)
    (`sha256: babfaffbfd0af65b0b9f0019767a793981a33ec378d6f548b22d8f7a007ff1d7`,
    1,446 lines, 0 `sorry`): `mirSroa_compiles`,
    `canary_sroa_on_address_taken_local_unsound`,
    `destProp_with_live_union_compiles`,
    `canary_destProp_without_live_union_violates_compiles`,
    `elaborateDrops_compiles`, `canary_elaborateDrops_missing_move_clear_unsound`,
    `mirCleanupAndOptPipeline_compiles`.
  - [`support/support_mir_to_anllvm_lowering_probe.lean`](support/support_mir_to_anllvm_lowering_probe.lean)
    (`sha256: bd801a91140089fe6bef519fbff256f93c418bb1052eb94d4e37f8d0c79c5d1a`,
    1,589 lines, 0 `sorry`): `codegen_get_set_discr_niche_roundtrip`,
    `lowerMirToAnLlvm_compiles`, `pack_padded_preserves_byte_init_masks`,
    `register_transmute_and_cast_eliminates_alloca`,
    `canary_multi_def_local_as_ssa_without_phi_unsound`.
  - [`support/bench_patterns.rs`](support/bench_patterns.rs)
    (`sha256: 7b96a8a0e83fa5dc40b50ccd80afb4c37ca19998b99d985a8aa4e7b38faa5754`),
    [`support/run_ablation.py`](support/run_ablation.py)
    (`sha256: 52c7dc11676fbca92241aac5497b68ea2691ff8e953987259613017b29d07475`),
    and [`support/ablation_results.json`](support/ablation_results.json)
    (`sha256: 9b5ad4227e2d41178c02724a11907e5571e1d445ef415a2674e244f81bcedc1e`).
  - [`support/empirical_probe.rs`](support/empirical_probe.rs)
    (`sha256: 5dcdd80399e1dbf24fc033bc9a016b7a171e3f36c0fd69af6923addb928e26e0`),
    [`support/empirical_probe_opt1.mir`](support/empirical_probe_opt1.mir)
    (`sha256: 695408cce539bc0b02a537dae9828457dc9ad77c19e32e04742983c28081be1a`),
    and [`support/empirical_probe_opt1_nollvm.ll`](support/empirical_probe_opt1_nollvm.ll)
    (`sha256: c861ba81baaaa02acc88bc1627c4f550e48216c4ba15d1e6747be8c71f3e4b07`).
- **Symbolic VCGen, Cut-Points, Loops, and Variable-Step Refinement Artifacts:**
  - [`support/SymbolicVCGenProbe.lean`](support/SymbolicVCGenProbe.lean)
    (`sha256: 62b694386ee6f3a3da3de1bf88d74c2ce3cc368a2d6534fd71bf1f20e7eea155`,
    1,594 lines, 54 theorems, 0 `sorry`).
  - [`support/LoopAndJoinVCGenProbe.lean`](support/LoopAndJoinVCGenProbe.lean)
    (`sha256: 3c9b2aee3b7028c6824b494bd187e412298840727963f18728accd6041a21d4c`,
    149 declarations, 75 theorems, 0 `sorry`).
  - [`support/ReplayAudit.lean`](support/ReplayAudit.lean)
    (`sha256: d640d0dc042102f123d0ac5c775bfb13bdccbab7a10949c7a04fb4455a19ed62`).
  - [`support/VariableStepCompilesProbe.lean`](support/VariableStepCompilesProbe.lean)
    (`sha256: 1a042c7ccf780bca4939957659df32c5cf75fc5e5424b85a3c6752f03397ba31`,
    2,696 lines, 0 `sorry`).
  - [`support/StatefulVariableStepProbe.lean`](support/StatefulVariableStepProbe.lean)
    (`sha256: 7823354cc604db33510ffff5f78add2c23449400e0acf1efd3ba3c1f580a6219`,
    3,362 lines, 271 theorems, 0 `sorry`).
  - [`support/AuditCheck.lean`](support/AuditCheck.lean)
    (`sha256: 614715c3808e397609f420a1e71aad1695387cb45b3ee3dbb82898a0ed3a4019`).

## Revalidation

Run the standalone `prelude`-only Lean 4.34.1 probes, the `rustc_driver`
extractors, and the differential ablation suite:

```bash
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/ByteMemoryProvenanceProbe.lean
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/Phase3SemanticsProbe.lean
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/support_mir_transform_adaptation_probe.lean
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/support_mir_to_anllvm_lowering_probe.lean
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/VariableStepCompilesProbe.lean
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  -o ./build/StatefulVariableStepProbe.olean support/StatefulVariableStepProbe.lean
LEAN_PATH=./build lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/AuditCheck.lean

rustc --edition=2021 support/layout_mir_driver.rs -o ./build/layout_mir_driver
./build/layout_mir_driver support/probe_6cat.rs --crate-type=lib --edition=2021 \
  -C panic=abort -C debug-assertions=off -Z mir-opt-level=0

rustc --edition=2021 support/monomorph_mir_driver.rs -o ./build/monomorph_mir_driver
./build/monomorph_mir_driver support/probe_6cat.rs --crate-type=lib --edition=2021 \
  -C panic=abort -C debug-assertions=off -Z mir-opt-level=0

python3 support/run_ablation.py
```
