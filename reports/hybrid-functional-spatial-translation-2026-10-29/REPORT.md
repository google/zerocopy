# Hybrid Borrow-and-Heap Functional Translation in Lean 4: Bridging Aeneas Pure Extraction with Unsafe Raw Pointers and C++20 Weak-Memory Atomics

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Vanilla Aeneas-style functional translation (`theory/Anneal/FunctionalTranslation.lean` at `be9cafeb2a401b47d22fb8a5b548d28c46617e54`) achieves near-zero TCB overhead by evaluating a Rust MIR body and an untrusted positional `TransPlan` via a pure total Lean 4 function `evalSymPlan` that reduces safe locals, control flow, and single-level `&` / `&mut` borrows to a pure `Option SymOutcome` by kernel `rfl` (the First Futamura Projection). However, real-world systems Rust crates frequently mix 90% safe borrow/arithmetic logic with 10% `unsafe` raw-pointer manipulation (`*const T` / `*mut T`), pointer-to-reference reborrows (`&mut *raw_p`, as in `slice::split_at_mut`), `UnsafeCell` interior mutability, or C++20 weak-memory atomics (`AtomicUsize::load(Relaxed | Acquire)`). If the translator rejects any function containing a raw pointer or atomic access (`evalSymPlan = none`) and forces the proof engineer to verify the entire function directly against raw `MirLang` (`ReachesPrefix MirMachine`), every safe statement in that function loses functional extraction and requires manual operational stepping (`SafeAndSatisfies.of_step`).

This report investigates how to extend Anneal's shallow functional translation to handle mixed safe + `unsafe`/concurrent Rust functions **without enlarging the Trusted Computing Base (TCB)** and **without paying separation-logic tactic overhead on the safe prefix/suffix of a function**. We synthesize a **three-layer hybrid translation architecture** combining:

1. **Technique A — Hybrid Interaction Trees (`SymTree` + `evalSymTree` + `zipSymTree`)**: Instead of returning `Option SymOutcome`, the untrusted-plan evaluator `evalSymTree` returns a shallow interaction tree (`SymTree RetSummary`) over residual heap and concurrency effects (`.readRaw`, `.writeRaw`, `.promoteRaw`, `.releaseRaw`, `.atomicLoad`). All safe statements, local assignments, arithmetic, `&` / `&mut` borrow dereferences and mutations, `goto` jumps, and `switchInt` branches reduce at translation time by pure Lean 4 kernel definitional equality (`rfl`). When a branch contains only pure `.ret` or `.releaseRaw ... (.ret ...)` outcomes, `zipSymTree` folds the conditional into scalar `if b then ... else ...` expressions (`zipSymTree_eq_ite`), recovering a pure functional spine.
2. **Technique B — Omnisemantics / Characteristic Formula Weakest Preconditions (`symWP` + `FuncTreeLang`)**: Inspired by Charguéraud et al.'s omnisemantics (TOPLAS 2023) and Katamaran's shallow monadic symbolic execution (ICFP 2022), a total recursive predicate transformer `symWP : SymTree RetSummary → (Nat → Option MirVal) → (Nat → Option (Nat × MirVal)) → (Nat → List Message) → View → AcquireExt → (RetSummary → (Nat → Option MirVal) → View → Prop) → Prop` interprets residual `SymTree` nodes directly into first-order `Prop` verification conditions over Anneal's timestamped C++20 memory model (`OwnLoc`, `ReadOwnLoc`, `ReleaseGuarded`, and `visibleMsgsAt`). A single universal theorem `evalSymTree_sound` (and its `Abstracts FuncTreeLang MirLang π_tree (evalSymTree plan body) body` corollary `evalSymTree_abstracts`) proves once and for all that **for every untrusted `plan : TransPlan` and `body : MirBody`**, `symWP (evalSymTree plan body)` guarantees `SafeAndSatisfies body`.
3. **Technique C — RefinedC/Lithium-Style Raw-to-Loan Promotion Hints in `TransPlan` (`reborrowRaw` / `endRawLoan`)**: Extending the untrusted `TransPlan` certificate with `.reborrowRaw loanId next` and `.endRawLoan loanId next` allows an `unsafe` reborrow `let r = &mut *raw_p` to promote a spatial raw pointer (`rawOwn rawId = some mv`) into a tracked functional loan (`LoanEntry` with `rawSource = some rawId`). While promoted, all reads, mutations, and conditional branches through `r` evaluate purely functionally by `rfl`; when `.endRawLoan loanId` fires, the final scalar value of the loan is written back to the spatial `rawOwn` map via a `.releaseRaw` node. Because `TransPlan` remains completely untrusted and verified by universal forward simulation (`evalSymTree_sound`), all static borrow/alias heuristics stay 100% outside the TCB.

We mechanize this entire architecture in a standalone 3,500-line Lean 4.34.1 prototype (`support/HybridBorrowHeapPrototype.lean`), self-contained over exact copies of `Trusted/Refinement.lean` and `Trusted/Memory.lean`, and prove four end-to-end mixed safe + `unsafe`/concurrent MIR case studies with **zero `sorryAx`**, **zero `Classical.choice`**, and **zero `Quot.sound`** (10 theorems with zero axioms; 14 theorems depending only on `[propext]`).

---

## Applicability

The findings and mechanical prototype in this report apply to:

| Component | Target Version / Revision | Role |
| :--- | :--- | :--- |
| Anneal Trusted Core & Theory | `joshlf/anneal` at `be9cafeb2a401b47d22fb8a5b548d28c46617e54` | Target verification platform (`Trusted/Refinement.lean`, `Trusted/Memory.lean`, `theory/Anneal/FunctionalTranslation.lean`) |
| Lean 4 Kernel Toolchain | `leanprover/lean4` v4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`) | Kernel verification engine (`lean -j1 -M1024`) |
| Mechanical Prototype | `support/HybridBorrowHeapPrototype.lean` (SHA-256 `823ac5309f2d67a229f4dda5b4cea7824a7ca5caab4f4aa44b4c2a19a278bea9`, 3,500 lines) | End-to-end mechanized proof of `SymTree`, `evalSymTree`, `symWP`, `StateRel`, `evalSymTree_sound`, `evalSymTree_abstracts`, and 4 MIR case studies |
| Aeneas Translator | `AeneasVerif/aeneas` at `21345f80fa212c596f6437378d7d57984fa2ea77` (`PR #1352`) | Reference symbolic execution engine for borrow and raw-pointer evaluation |
| Gillian-Rust | `GillianPlatform/gillian-rust` at `83d739e23632e07645c1756f97ef47d3d9a8be79` (PLDI 2025, DOI `10.1145/3735592`) | Hybrid borrow-tree + spatial heap symbolic execution baseline |
| RefinedRust / RefinedC | PLDI 2024 (DOI `10.1145/3656423`) / PLDI 2021 (DOI `10.1145/3453483.3454036`) | Lithium goal-directed ownership token / reborrow promotion architecture |
| Omnisemantics | Charguéraud et al., TOPLAS 2023 (DOI `10.1145/3579834`) | All-executions weakest-precondition semantics for demonic nondeterminism |

---

## Findings

### 1. Direct MIR Execution vs. Total/Hybrid Functional Translation

When a Rust crate contains functions that fall outside Aeneas's pure functional subset, Anneal faces a fundamental architectural choice:

#### Option 1: Binary Fallback to Direct `MirLang` Execution
Under the existing `theory/Anneal/FunctionalTranslation.lean`, `evalSymPlan : TransPlan → MirBody → Option SymOutcome` returns `none` whenever it encounters a raw pointer dereference, raw-to-reference reborrow, or atomic operation. A function where `evalSymPlan = none` must be proved directly against `MirLang` (`ReachesPrefix MirMachine body`).

- **Pros**: Zero changes to `FunctionalTranslation.lean`.
- **Cons (The "1-Line Unsafe Cliff")**: A 60-line function that performs 55 lines of safe slice indexing, arithmetic, and `&mut` updates plus a single `AtomicUsize::load(Ordering::Relaxed)` or a single `unsafe { &mut *ptr }` loses **all** functional reduction. The proof engineer must step through every `MirState` basic block and local variable map (`updateLocal`) using `SafeAndSatisfies.of_step`, manually maintaining `OwnLoc` invariants across every safe statement. Furthermore, caller functions cannot compose with a pure functional summary unless an explicit `Abstracts` bridge is manually constructed for that function.

#### Option 2: Total/Hybrid Functional Translation (`evalSymTree` + `symWP` over `SymTree`)
Instead of returning `Option SymOutcome`, we generalize the target of plan-guided evaluation from a flat value to a shallow interaction tree `SymTree RetSummary`.

```lean
inductive SymTree (Val : Type) where
  | ret (v : Val)
  | fail
  | readRaw (rawId : Nat) (k : Nat → SymTree Val)
  | writeRaw (rawId : Nat) (newVal : MirVal) (k : SymTree Val)
  | promoteRaw (rawId : Nat) (loanId : Nat) (k : Nat → SymTree Val)
  | releaseRaw (rawId : Nat) (loanId : Nat) (finalVal : MirVal) (k : SymTree Val)
  | atomicLoad (atomId : Nat) (ord : AtomicOrdering) (k : Nat → SymTree Val)
```

- **Zero Regression on Pure Safe Functions**: For any purely safe function where `evalSymPlan` previously succeeded with `some out`, `evalSymTree` reduces by kernel `rfl` to `.ret { retVal := out.retVal, loan1Val := out.loan1Val }`. Its `symWP` reduces definitionally to `Post summary rawOwn atomView`, identical to the pure functional postcondition.
- **Automatic Partial Evaluation of Mixed Functions**: For a mixed function, `evalSymTree` eliminates 100% of the safe statements, local variables, control-flow jumps, and safe borrow dereferences at translation time by `rfl`. For example, in Case Study 1 (`atomicMaxAssignBody`), a 2-block, 6-statement function combining `&mut usize`, `AtomicUsize::load(Relaxed)`, conditional comparison, and conditional mutation reduces by `rfl` (`atomicMaxAssign_evalSymTree_rfl`) to a single residual node:
  ```lean
  evalSymTree atomicMaxAssignPlan atomicMaxAssignBody =
    .atomicLoad 1 .relaxed (fun vLoaded =>
      .ret {
        retVal := .usize (if x0 < vLoaded then vLoaded else x0)
        loan1Val := some (.usize (if x0 < vLoaded then vLoaded else x0))
      })
  ```
- **Uniform Compositionality (`FuncTreeLang`)**: Every translated function—whether 100% safe or mixed safe/`unsafe`/atomic—inhabits the same intermediate language `FuncTreeLang`, with a single mechanized refinement theorem:
  $$\texttt{evalSymTree\_abstracts} : \forall (\texttt{plan} : \texttt{TransPlan})\; (\texttt{body} : \texttt{MirBody}),\; \texttt{Abstracts}\; \texttt{FuncTreeLang}\; \texttt{MirLang}\; \pi_{\text{tree}}\; (\texttt{evalSymTree}\; \texttt{plan}\; \texttt{body})\; \texttt{body}$$
- **Verdict**: Making the functional translation hybrid via `SymTree` strictly dominates binary fallback to `MirLang`. Direct `MirLang` execution is only needed when a function performs unstructured dynamic jumps or loops whose trip count cannot be unrolled or structurally summarized by a `TransPlan`, and even then a loop body can be summarized via `SymTree`.

---

### 2. Survey and Synthesis of Hybrid Borrow-and-Heap Models in the Literature

We analyzed how existing Rust verification frameworks bridge pure functional borrow translation with spatial/separation-logic reasoning for `unsafe` code:

| System | Safe `&` / `&mut` Representation | Unsafe `*const T` / `*mut T` & Atomics | Bridge Mechanism | TCB & Proof Overhead in ITP |
| :--- | :--- | :--- | :--- | :--- |
| **Aeneas** (ICFP 2022, ICFP 2024, `PR #1352`) | Symbolic values (`VLoan`, `VBorrow`) in an abstract value tree; backward functions at loan expiration | `PR #1352` starts adding raw-pointer symbolic values for safe-usage idioms, but rejects general aliasing raw pointers and weak-memory atomics | Purely syntactic/symbolic in OCaml; no spatial heap or weak-memory view model | External OCaml compiler in TCB unless translation-validated; fails on non-borrow raw pointers & atomics |
| **Gillian-Rust** (Ayoun et al., PLDI 2025, DOI `10.1145/3735592`) | Symbolic borrow tree / prophecy environment (Aeneas-inspired) | Spatial separation-logic heap (`l ↦ v`) for raw pointers and dynamic allocations | **Explicit Hybrid Mode Switch**: places live in *either* functional borrow tree *or* spatial heap; converting `&mut T → *mut T` or `&mut *raw_p` splits/merges resources across the two domains | Automated SMT/symbolic engine in OCaml; not foundationally proved in Lean/Rocq |
| **RustHornBelt** (Matsushita et al., PLDI 2022, DOI `10.1145/3519939.3523704`) | Prophetic First-Order Logic (FOL) encoding (`⟨cur, final⟩` value pairs) | Iris higher-order separation logic (`iProp`) in Rocq (`LambdaRust`) | Semantic type soundness: unsafe libraries are verified manually in Iris against prophetic semantic type specifications; safe clients are verified in pure FOL | Requires full Iris + step-indexed prophetic semantic types for every unsafe boundary |
| **RefinedRust** (Gäher et al., PLDI 2024, DOI `10.1145/3656423`) & **RefinedC** (PLDI 2021) | Ownership refinement types (`&uniq(l, T)`, `&shr(l, T)`) backed by Lithium | `@place` spatial resources, raw pointers, and Radium atomic protocol invariants in Rocq/Iris | Goal-directed **Lithium** proof search consumes/produces ownership tokens deterministically (`subsume`, `find_in_context`) | Fast syntax-directed automation, but backed by a heavyweight Rocq/Iris foundation (~60k+ LOC) |
| **Verus** (OOPSLA 2023) & **Creusot / Pavano** | Pure SMT specifications (`*x`, `^x` prophetic final values in Creusot) | Tracked ghost permission tokens (`PointsTo<T>`, ` Perm<*const T>`) threaded as explicit ghost arguments | Ghost permission tokens act as pure values in the functional/SMT layer | Relies on trusted Rust frontend + Z3/CVC5; assumes sequential consistency for memory |
| **Anneal Hybrid Architecture (This Report)** | Tracked functional loans (`LoanEntry` in `SymState.loans`) reduced by `rfl` in `evalSymTree` | Residual `SymTree` nodes interpreted by `symWP` over first-order `OwnLoc`, `ReleaseGuarded`, and C++20 `View` lattices | **Unified Spatial Simulation (`StateRel`) + Plan-Guided Loan Promotion (`reborrowRaw` / `endRawLoan`)** | **Zero new TCB axioms**; 100% proved against `Trusted/Memory.lean` and `Trusted/Refinement.lean` |

#### Key Architectural Insight from the Literature Synthesis
Gillian-Rust (PLDI 2025) and RefinedRust (PLDI 2024) demonstrate that **a Rust memory location does not need to live permanently in a spatial separation-logic heap**:
1. While a location is governed by a live safe reference (`&T` or `&mut T`), its aliasing discipline is statically fixed (unique for `&mut T`, immutable for `&T`). Therefore, its state transitions are deterministic local environment updates that can be reduced by pure functional computation (`rfl`).
2. Conversely, when a location is accessed via a raw pointer (`*const T` / `*mut T`) or an `UnsafeCell`/atomic (`AtomicUsize`), its aliasing or visibility must be justified at the access point.
3. Most importantly, when `unsafe` code performs a temporary reborrow `let r = &mut *raw_p`, it **temporarily enters the safe borrow discipline** for the lifetime of `r`. By recording `reborrowRaw` and `endRawLoan` in the untrusted `TransPlan`, Anneal can promote a spatial `rawOwn` location into a functional `LoanEntry`, execute the entire lifetime of `r` by pure `rfl`, and release the final value back to `rawOwn` when the loan ends.

---

### 3. Unified Spatial Simulation Invariant (`StateRel`) Over Anneal's C++20 Memory Model

A central contribution of `support/HybridBorrowHeapPrototype.lean` (Section 2, lines 191–676) is proving that **active functional loans (`&mut`), shared references (`&`), raw pointers (`*mut`), release-guarded handoff locations (`ReleaseGuarded`), and weak-memory atomics (`AtomicUsize`) can coexist in a single concrete `Trusted.MemState` without any step-indexed Iris separation logic (`iProp`)**.

We define first-order ownership predicates directly on `Trusted.MemState`:
- **Unique Non-Atomic Ownership (`OwnLoc mem loc val`)**:
  1. `mem.lastNAWrite loc = some ts` for some timestamp `ts`,
  2. `mem.curView loc = ts` (the thread's current view is caught up to the latest write at `loc`),
  3. Every message in `mem.msgs` at `loc` has timestamp `≤ ts`, and
  4. The unique message at `(loc, ts)` has payload `val` and `relView = none`.
- **Shared Immutable Ownership (`ReadOwnLoc mem loc val`)**:
  Same as `OwnLoc`, except `mem.curView loc ≤ ts`, which suffices for `mem.canReadNA loc = true` and `mem.readNAVal loc = some val`.
- **Release-Guarded Ownership (`ReleaseGuarded mem loc guardLoc minTs val`)**:
  Captures a non-atomic location `loc` whose latest write at timestamp `tsWrite` is not yet in the thread's `curView` (`mem.curView loc ≤ tsWrite`), **except** that every message at `guardLoc` with timestamp `≥ minTs` carries a release view `rv` satisfying `rv loc = tsWrite`. We prove (`OwnLoc.transfer_acquire`, **0 axioms**) that executing an `.acquire` load on `guardLoc` that observes any message with `msg.ts ≥ minTs` automatically upgrades `ReleaseGuarded mem loc guardLoc minTs val` into full `OwnLoc mem' loc val`!

We then factor the simulation relation `StateRel` between symbolic state `(sym, rawOwn, relOwn, atomMsgs, atomView)` and concrete `MirState` into four orthogonal components:

$$\texttt{StateRel}\; \texttt{sym}\; \texttt{rawOwn}\; \texttt{relOwn}\; \texttt{atomMsgs}\; \texttt{atomView}\; \texttt{conc} \;\triangleq\; \texttt{LocalRel} \land \texttt{LoanRel} \land \texttt{RawRel} \land \texttt{AtomRel}$$

This factored invariant yields five zero-axiom automatic framing theorems that eliminate separation-logic proof obligations during symbolic execution:

1. **Zero-Obligation Preservation of Loans & Raw Pointers Across Atomic Loads (`LoanRel.preserved_by_atomic_load`, `OwnLoc.preserved_by_atomic_load`, `ReadOwnLoc.preserved_by_atomic_load` — 0 axioms)**:
   When an atomic load (`Relaxed` or `Acquire`) executes at `locAtom`, `applyAtomicLoad` only advances `conc.mem.curView` monotonically (`curView ≤ applyViewLoad ord curView msg`) and leaves `conc.mem.msgs` unchanged. For any location `loc` where `OwnLoc conc.mem loc val` already holds, `conc.mem.curView loc = ts` is already at the maximum timestamp `ts` present in `conc.mem.msgs` at `loc` (and every release view in `conc.mem.msgs` is well-formed, `rv loc ≤ ts`). Therefore, `applyViewLoad ord curView msg loc = ts` holds **automatically without even requiring `loc ≠ locAtom`**! Consequently, an atomic load never invalidates any active `&mut` loan, `&` shared reference, or owned raw pointer.
2. **Automatic Framing of Active Loans Across Raw-Pointer Writes (`LoanRel.preserved_by_raw_write` — 0 axioms)**:
   Because `RawRel` maintains disjointness between owned raw pointers (`rawOwn rawId = some mv`) and active loans (`LoanRel`), any write to an owned raw pointer `rawId` automatically preserves `OwnLoc` and `ReadOwnLoc` for all active `&mut` loans and `&` shared references via `OwnLoc.afterWriteNA_other`.
3. **Zero-Axiom Raw-to-Loan Promotion and Release (`promoteRaw_preserves_loanRel`, `releaseRaw_preserves_rawRel` — 0 axioms)**:
   Promoting `rawOwn rawId = some (.usize n)` into an active `LoanEntry` at `loanId` transfers `OwnLoc conc.mem (conc.rawLocs rawId) (.usize n)` from `RawRel` to `LoanRel` (setting `rawOwn rawId := none`). Releasing `loanId` at `endRawLoan` transfers `OwnLoc` back from `LoanRel` to `RawRel` (`rawOwn rawId := some finalMv`). The disjoint union $\text{ActiveLoans} \uplus \text{RawOwn}$ is conserved at every step.
4. **Pointwise Weak-Memory View Invariance Across Non-Atomic Writes (`AtomRel.preserved_by_writeNA`)**:
   Because `View.bump` in `Trusted/Memory.lean` updates `curView` strictly pointwise at the written non-atomic location `locNA`, for every atomic location `locAtom ≠ locNA`, both `conc.mem.curView locAtom` and `conc.mem.visibleAtomicMsgs locAtom` are 100% invariant across all safe borrow and raw-pointer mutations.

---

### 4. Evaluation of the Four Candidate Techniques in Lean 4

#### Technique A: Hybrid Interaction Trees / Free Monad Partial Evaluation (`SymTree`)
- **Mechanism**: `evalSymTree : TransPlan → MirBody → SymTree RetSummary` runs `evalSymTreeAux` from `initSymState body`. Safe statements (`evalSafeSymStmt`), `goto` jumps, and `switchInt` branches execute purely functionally in `SymState`. Only raw pointer dereferences/writes, raw-to-loan promotions/releases, and atomic loads emit constructors of `SymTree`.
- **Conditional Spine Merging (`zipSymTree`)**: A naive interaction-tree evaluator that emits `if cond then evalSymTreeAux pTrue sTrue else evalSymTreeAux pFalse sFalse` leaves a Lean `ite` outside the `SymTree` constructors, forcing downstream proofs to case-split on `cond`. We solve this with `zipSymTree`, which merges `.ret` and `.releaseRaw r l v (.ret s)` branches into a single constructor spine with `if cond then ... else ...` pushed inside the scalar `MirVal` payloads, accompanied by the soundness theorem:
  ```lean
  theorem zipSymTree_eq_ite (b : Bool) (tTrue tFalse : SymTree RetSummary) :
      zipSymTree b tTrue tFalse = (if b then tTrue else tFalse)
  ```
- **Strengths**: Preserves 100% `rfl` evaluation for all safe paths and promoted raw-pointer lifetimes; completely transparent to Lean's kernel reducer.

#### Technique B: Omnisemantics / Characteristic Formula Weakest Preconditions (`symWP`)
- **Mechanism**: Following Charguéraud et al. (TOPLAS 2023), a single inductive/recursive judgement `symWP` characterizes both safety (`out.isSafe`, i.e., no `.ub` and no `.stuck`) and postcondition satisfaction across both deterministic steps and demonic nondeterministic choices (`StepResult.choice .demonic` for weak-memory atomic loads):
  ```lean
  def symWP (tree : SymTree RetSummary)
      (rawOwn : Nat → Option MirVal)
      (relOwn : Nat → Option (Nat × MirVal))
      (atomMsgs : Nat → List Message)
      (atomView : View)
      (acqExt : AcquireExt)
      (Post : RetSummary → (Nat → Option MirVal) → View → Prop) : Prop :=
    match tree with
    | .ret summary => Post summary rawOwn atomView
    | .fail => False
    | .readRaw rawId k =>
      ∃ n, rawOwn rawId = some (.usize n) ∧
        symWP (k n) rawOwn relOwn atomMsgs atomView acqExt Post
    | .writeRaw rawId newVal k =>
      ∃ oldVal, rawOwn rawId = some oldVal ∧
        symWP k (updateRawOwn rawOwn rawId (some newVal)) relOwn atomMsgs atomView acqExt Post
    | .promoteRaw rawId loanId k =>
      ∃ n, rawOwn rawId = some (.usize n) ∧
        symWP (k n) (updateRawOwn rawOwn rawId none) relOwn atomMsgs atomView acqExt Post
    | .releaseRaw rawId _ finalVal k =>
      rawOwn rawId = none ∧
        symWP k (updateRawOwn rawOwn rawId (some finalVal)) relOwn atomMsgs atomView acqExt Post
    | .atomicLoad atomId ord k =>
      (ord = .relaxed ∨ ord = .acquire) ∧
      (∃ msg, visibleMsgsAt (atomMsgs atomId) atomView msg) ∧
      (∀ msg n, visibleMsgsAt (atomMsgs atomId) atomView msg →
        msg.val = .usize n →
        ∀ rawOwn', acqExt ord atomId msg rawOwn relOwn rawOwn' →
          symWP (k n) rawOwn' relOwn atomMsgs (applyViewLoad ord atomView msg) acqExt Post)
  ```
- **Dynamic Acquire Ownership Transfer (`AcquireExt`)**: Notice the `acqExt : AcquireExt` parameter on `.atomicLoad`. For simple functions where atomic loads do not transfer non-atomic ownership, instantiating `acqExt := NoAcquireExt` (`rawOwn' = rawOwn`) reduces `symWP` by `rfl` without any extra premises. When an `.acquire` load synchronizes with a release write that published a non-atomic raw pointer `rawId` (`relOwn rawId = some (minTs, mv)`), instantiating `acqExt := ReleaseAcquireExt atomId rawId minTs mv` (`WellFormedAcquireExt`) automatically updates `rawOwn' := updateRawOwn rawOwn rawId (some mv)` whenever `ord = .acquire ∧ minTs ≤ msg.ts`, backed by `OwnLoc.transfer_acquire`!

#### Technique C: RefinedC/Lithium-Style Ownership-Token Hints in `TransPlan`
- **Mechanism**: By adding two constructors to `TransPlan`:
  ```lean
  | reborrowRaw (loanId : Nat) (next : TransPlan)
  | endRawLoan (loanId : Nat) (next : TransPlan)
  ```
  an untrusted external analyzer (or lightweight tactic) can instruct `evalSymTree` when to promote a raw pointer to a tracked functional loan (`LoanEntry` with `rawSource = some rawId`) and when to end that loan and write its final scalar value back to the spatial `rawOwn` map.
- **Why This Beats Static Alias Analysis in the TCB**: Static verification of raw-pointer reborrows (as in `slice::split_at_mut`) normally requires trusting a borrow/alias checker or proving complex pointer-arithmetic disjointness inside the translator. With Technique C, the translator does **not** decide disjointness: `evalSymTree` simply emits `.promoteRaw rawId loanId` and `.releaseRaw rawId loanId finalVal`, and `symWP` emits the simple first-order obligation `rawOwn rawId = some (.usize n)` at promotion time. If two raw pointers happen to alias, `RawRel.injectiveRawLocs` cannot be satisfied for both simultaneously in `rawOwn`, so soundness (`evalSymTree_sound`) is 100% preserved regardless of what hints the untrusted `TransPlan` provides.

#### Technique D: Full Embedded Separation Logic (`Iris-Lean`) vs. First-Order `OwnLoc` Maps
- **When First-Order `OwnLoc` + `ReleaseGuarded` + `symWP` Suffices**:
  - Safe `&` / `&mut` borrows mixed with raw pointer reads/writes (`*const T`, `*mut T`),
  - Temporary raw-to-reference reborrows (`&mut *raw_p`, non-overlapping slice/field splitting),
  - Relaxed atomic counters/flags (`Ordering::Relaxed`), and
  - One-shot or structured message-passing / lock-acquisition (`Ordering::Release` / `Ordering::Acquire`) where an acquire load transfers unique ownership (`OwnLoc`) of a guarded non-atomic location (`ReleaseGuarded`).
- **Exact Boundary Where Full Separation Logic (or Ghost Token Algebras) Becomes Necessary**:
  - **Shared Multi-Writer Invariants**: When multiple threads concurrently race on an atomic CAS loop (`fetch_add`, spinlocks, Treiber stack, Michael-Scott queue) where no single thread holds unique `OwnLoc` or monotonic `ReleaseGuarded`, one needs shared invariants over ghost state (partial commutative monoids / cameras).
  - **Unbounded Lock-Free Memory Reclamation**: Hazard pointers and epoch-based reclamation require step-indexed or lifetime-indexed shared protocols (as shown in `relaxed-memory-reclamation-premises-2026`).
  - **Higher-Order Type-Erased Callbacks (`dyn FnMut` / `RawWaker` vtables)**: Require impredicative invariants over code pointers (`iProp`).

---

### 5. Mechanized End-to-End Case Studies in `support/HybridBorrowHeapPrototype.lean`

All four representative mixed safe + `unsafe`/concurrent Rust patterns are mechanized and proved end-to-end against `MirLang` in `support/HybridBorrowHeapPrototype.lean`:

| Case Study | Rust Pattern | Translation Theorem (`by rfl`) | End-to-End `MirLang` Safety & Spec Theorem |
| :--- | :--- | :--- | :--- |
| **1. `atomicMaxAssignBody`** (lines 2536–2742) | `fn atomic_max_assign(x: &mut usize, a: &AtomicUsize) -> usize` (`Relaxed` load + safe `&mut` branch & writeback) | `atomicMaxAssign_evalSymTree_rfl`: reduces 2 blocks / 6 stmts to a single `.atomicLoad 1 .relaxed` wrapping `.ret` | `atomicMaxAssign_satisfies_spec`: proves `SafeAndSatisfies` + `OwnLoc termOut.mem locX (max x0 vLoaded)` for some visible message `vLoaded` |
| **2. `rawAddAndZeroBody`** (lines 2744–2949) | `unsafe fn raw_add_and_zero(x: &mut usize, p: *mut usize) -> usize` (safe `&mut` + unsafe `*p` read & `*p = 0` write) | `rawAddAndZero_evalSymTree_rfl`: reduces 6 stmts to `.readRaw 1 (fun vRaw => .writeRaw 1 (.usize 0) (.ret ...))` | `rawAddAndZero_satisfies_spec`: proves `SafeAndSatisfies` + `OwnLoc termOut.mem locX (x0 + vRaw)` + `OwnLoc termOut.mem locRaw 0` |
| **3. `reborrowRawMaxAssignBody`** (lines 2951–3210) | `unsafe fn reborrow_raw_max_assign(x: &usize, raw_p: *mut usize) -> usize { let r = &mut *raw_p; if *r < *x { *r = *x; } *r }` | `reborrowRawMaxAssign_evalSymTree_rfl`: promotes `raw_p` via `.reborrowRaw 10`, reduces the branch and `*r = *x` mutation by `rfl`, and folds via `zipSymTree` into `.promoteRaw 1 10 (fun vRaw => .releaseRaw 1 10 (max vRaw x0) (.ret ...))` | `reborrowRawMaxAssign_satisfies_spec`: proves `SafeAndSatisfies` + `OwnLoc termOut.mem locRaw (max vRaw x0)` |
| **4. `acquireReadRawBody`** (lines 3212–3468) | `unsafe fn acquire_read_raw(x: &mut usize, flag: &AtomicUsize, data: *const usize) -> usize` (`Acquire` load synchronizing with release-guarded `data`) | `acquireReadRaw_evalSymTree_rfl`: reduces 2 blocks / 7 stmts + branch via `zipSymTree` to `.atomicLoad 1 .acquire (fun vFlag => .readRaw 1 (fun vRaw => .ret ...))` | `acquireReadRaw_satisfies_spec`: under `ReleaseGuarded s.mem locRaw locAtom minTs (.usize vRaw)` and visible message timestamp `≥ minTs`, proves `SafeAndSatisfies` + `OwnLoc termOut.mem locRaw (.usize vRaw)` + `OwnLoc termOut.mem locX (if vFlag == 1 then x0 + vRaw else x0)` |

---

### 6. Concrete Architectural Blueprint for Extending `theory/Anneal/FunctionalTranslation.lean`

To integrate this hybrid architecture into Anneal's main repository (`theory/Anneal/FunctionalTranslation.lean`), we recommend a clean, incremental two-file evolution that keeps existing pure proofs untouched:

1. **Keep `evalSymPlan` for Pure Functions, or Define `evalSymPlan` as a 5-Line Wrapper Around `evalSymTree`**:
   Because `evalSymTree plan body = .ret summary` holds by `rfl` on all pure safe functions, `evalSymPlan plan body` is simply:
   ```lean
   def evalSymPlan (plan : TransPlan) (body : MirBody) : Option SymOutcome :=
     match evalSymTree plan body with
     | .ret summary => some summary
     | _ => none
   ```
2. **Factor the Memory Ownership Lemmas into `theory/Anneal/MemoryOwnership.lean`**:
   Move `OwnLoc`, `ReadOwnLoc`, `ReleaseGuarded`, and the six zero-axiom framing lemmas (`OwnLoc.readNA_preserves`, `OwnLoc.afterWriteNA_self`, `OwnLoc.afterWriteNA_other`, `OwnLoc.preserved_by_atomic_load`, `ReadOwnLoc.preserved_by_atomic_load`, `OwnLoc.transfer_acquire`) into a dedicated module importing only `Anneal.Trusted.Memory`.
3. **Replace Single-Location Ad-Hoc Simulation with Factored `StateRel` (`LocalRel ∧ LoanRel ∧ RawRel ∧ AtomRel`)**:
   In `theory/Anneal/FunctionalTranslation.lean`, upgrade `SymState` to include `loans : Nat → Option LoanEntry`, add `SymTree` and `symWP`, and expose `evalSymTree_sound` and `evalSymTree_abstracts`.
4. **Extend `zipSymTree` Recursion Depth to `fuel : Nat`**:
   In our prototype, `zipSymTree` merges `.ret` and 1-deep `.releaseRaw ... (.ret ...)` spines. For functions that perform multiple raw-pointer releases or writes after a branch join, parameterizing `zipSymTree` by recursion depth covers arbitrary finite suffixes while preserving `zipSymTree_eq_ite`.

---

## Boundaries

1. **Acquiring Ownership Requires Knowing that Visible Messages Meet the Release Threshold**:
   In Case Study 4 (`acquireReadRaw_satisfies_spec`), `OwnLoc.transfer_acquire` transfers `ReleaseGuarded s.mem locRaw locAtom minTs val` to `OwnLoc` whenever the `.acquire` load observes a message with `msg.ts ≥ minTs`. In a real program (`if flag.load(Acquire) == 1 { *data }`), the dereference `*data` only executes on the branch where `vFlag == 1`. In `HybridBorrowHeapPrototype.lean`, `MirBody` supports conditional jumps (`switchInt`), and `evalSymTree` evaluates both branches eagerly. If `*data` is only dereferenced on the `true` branch (`vFlag == 1`), `evalSymTree` emits `.readRaw` only in the `true` sub-tree, so `symWP` only requires `rawOwn rawId = some (.usize vRaw)` when `vFlag == 1` (i.e., when the observed message has value `1` and therefore timestamp `≥ minTs`).
2. **Loops Require Plan Unrolling or Loop Invariant Nodes in `TransPlan`**:
   Like `evalSymPlan` in `plan-guided-shallow-functional-translation-2026-10-29`, `evalSymTree` executes structurally over a finite `TransPlan` tree (`ret`, `step`, `branch`, `reborrowRaw`, `endRawLoan`). Bounded loops are handled by unrolling in `TransPlan`; unbounded loops require adding a `.loop (inv : ...)` cut-point constructor to `TransPlan` and `SymTree`.
3. **Multi-Writer Shared Atomic Protocols Require Ghost State Extensions**:
   First-order `OwnLoc` and `ReleaseGuarded` handle unique ownership and release/acquire handoff (`OwnLoc.transfer_acquire`), which covers message passing, one-shot initialization (`OnceCell`), and exclusive lock handoff, but not concurrent multi-writer CAS invariants without adding a ghost resource algebra.

---

## Evidence

1. **Mechanical Lean 4.34.1 Prototype (`support/HybridBorrowHeapPrototype.lean`)**:
   - **File**: `reports/hybrid-functional-spatial-translation-2026-10-29/support/HybridBorrowHeapPrototype.lean`
   - **SHA-256**: `823ac5309f2d67a229f4dda5b4cea7824a7ca5caab4f4aa44b4c2a19a278bea9`
   - **Size**: 3,500 lines
   - **Toolchain**: `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`
   - **Axiom Footprint**:
     - **Zero `sorryAx`**, **zero `Classical.choice`**, **zero `Quot.sound`**.
     - **10 theorems with zero axioms (`does not depend on any axioms`)**:
       - `OwnLoc.readNA_preserves` (line 262)
       - `OwnLoc.afterWriteNA_self` (line 299)
       - `OwnLoc.afterWriteNA_other` (line 368)
       - `OwnLoc.preserved_by_atomic_load` (line 425)
       - `ReadOwnLoc.preserved_by_atomic_load` (line 456)
       - `OwnLoc.transfer_acquire` (line 488)
       - `LoanRel.preserved_by_raw_write` (line 1383)
       - `LoanRel.preserved_by_atomic_load` (line 1421)
       - `promoteRaw_preserves_loanRel` (line 2216)
       - `releaseRaw_preserves_rawRel` (line 2307)
     - **14 theorems depending only on `[propext]`**:
       - `SafeAndSatisfies.of_step` (line 711)
       - `SafeAndSatisfies.of_terminated` (line 741)
       - `SafeAndSatisfies.of_demonic_choice` (line 776)
       - `zipSymTree_eq_ite` (line 974)
       - `evalSymTree_sound` (line 2400)
       - `evalSymTree_abstracts` (line 2513)
       - `atomicMaxAssign_evalSymTree_rfl` (line 2608)
       - `atomicMaxAssign_satisfies_spec` (line 2625)
       - `rawAddAndZero_evalSymTree_rfl` (line 2807)
       - `rawAddAndZero_satisfies_spec` (line 2820)
       - `reborrowRawMaxAssign_evalSymTree_rfl` (line 3032)
       - `reborrowRawMaxAssign_satisfies_spec` (line 3047)
       - `acquireReadRaw_evalSymTree_rfl` (line 3304)
       - `acquireReadRaw_satisfies_spec` (line 3319)
2. **Recorded Verification Results (`support/verification-results.json`)**:
   Generated by `support/revalidate.py --write-json`, capturing the exact Lean 4.34.1 compiler output, exit code (`0`), SHA-256 digest, and all 24 `#print axioms` lines.
3. **Anneal Source Baseline**:
   - `Trusted/Refinement.lean`, `Trusted/Memory.lean`, and `theory/Anneal/FunctionalTranslation.lean` in `/usr/local/google/home/joshlf/workspace/anneal/.agent-worktrees/skeleton` at commit `be9cafeb2a401b47d22fb8a5b548d28c46617e54`.

---

## Revalidation

Run the standalone revalidation script from the repository root (or any working directory):

```bash
python3 reports/hybrid-functional-spatial-translation-2026-10-29/support/revalidate.py
```

To regenerate `support/verification-results.json`:

```bash
python3 reports/hybrid-functional-spatial-translation-2026-10-29/support/revalidate.py --write-json
```

The script invokes `lean -j1 -M1024 reports/hybrid-functional-spatial-translation-2026-10-29/support/HybridBorrowHeapPrototype.lean`, asserts exit code `0`, verifies that `sorryAx` does not appear anywhere in the output, and checks that all 24 `#print axioms` declarations match their exact expected zero-axiom or `[propext]`-only signatures.
