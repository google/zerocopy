<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Historical Verification and Soundness Failures in High- and Mid-Level IR Optimizations, Language Lowering, and Program Transformations

## Summary

Mid-level intermediate representation (IR) optimizers and high-level language
lowering pipelines sit at the most error-prone seam in modern compilers: they
must preserve high-level language invariants (such as Rust ownership, borrow
protectors, pin stability, drop ordering, and forward progress) while rewriting
control-flow graphs, promoting stack memory to SSA registers, and eliminating
redundant computations. Across three decades of production compilers (`LLVM`,
`rustc`, `GCC`) and formal verification systems (`CompCert`, `Vellvm`,
`Crellvm`, `Alive2`, `Simuliris`, `C2Rust`/`CROWN`), historical failures in this
domain cluster into fifteen recurring root causes across three structural axes:

1. **Non-compositional semantics and broken refinement preorders in IR
   optimizations:**
   - **Dual `undef` / `poison` instability (`PLDI 2017`, `PLDI 2021`):**
     Giving uninitialized or overflowed values per-use angelic nondeterminism
     (`undef`) alongside tainting deferred undefined behavior (`poison`) makes
     the composition of individually plausible passes—Specifically Global Value
     Numbering (`GVN`), `LoopUnswitch`, Scalar Replacement of Aggregates
     (`SROA`), and `InstCombine` (`select`-to-branch)—end-to-end unsound on
     well-defined source programs, forcing the introduction of `freeze` and the
     deprecation of `undef`.
   - **Pointer-integer congruence collapse (`OOPSLA 2018`):** Replacing a
     pointer `p` with `q` under an equality branch `ptrtoint(p) == ptrtoint(q)`
     in `GVN` substitutes a one-past-the-end provenance tag for a valid adjacent
     object's provenance tag, turning a valid dereference into out-of-bounds UB.
   - **`rustc` MIR optimizer and `noalias` miscompilations (`#54878`, `#63818`,
     `#63934`, `#110947`, `#118328`, `#120613`, `#141038`, `#146383`):**
     Emitting LLVM `noalias` on `&mut Self` for self-referential coroutine state
     machines broke `async`/`await` for years until `!Unpin` suppression and
     `PtrMetadata` fixes landed; within `rustc_mir_transform`, `GVN`,
     `ConstProp`, `DestinationPropagation`, and `DeadStoreElimination` (`DSE`)
     repeatedly miscompiled partial moves, mutating borrows, pointer-typed enum
     niches, and `StorageLive`/`StorageDead` stack-slot reuse ranges.
   - **Call-boundary protector failure under divergence (`POPL 2020`,
     `PLDI 2025`, `Simuliris`):** Mechanizing Stacked Borrows and Tree Borrows
     in Rocq/Simuliris revealed that eliminating a dead store `*x = v₁` before
     an unknown external call `ext(); *x = v₂` is **unsound** if `ext()` never
     returns (`loop {}` or `abort()`) unless function-entry protectors enforce
     disjointness eagerly at the foreign access (`Strong` protectors) or emit a
     virtual write on function entry.
   - **Forward-progress infinite-loop deletion (`rust-lang/rust#28728`):**
     Applying C++11's forward-progress assumption (`[intro.progress]`) to Rust
     caused LLVM to delete side-effect-free `loop {}` blocks and execute
     unreachable basic blocks after them until LLVM 12 separated `mustprogress`
     and `willreturn` from default CFG semantics.

2. **State-corruption hazards during SSA destruction, control-flow lowering, and
   high-level desugaring:**
   - **Briggs/Boissinot `Lost-Copy` and `Swap` hazards (`SPE 1998`, `JAR 2008`,
     `CGO 2009`):** Naively sequentializing $\phi$-nodes during out-of-SSA
     translation without critical-edge splitting and cycle-breaking scratch
     moves overwrites live source operands on loop backedges.
   - **Tail-call stack-escape use-after-free (`LLVM tailcallelim`):** Converting
     a tail call `return f(&local)` into a frame-reusing jump or loop when a
     stack local's address or `byval` slot escapes into `f` clobbers the pointee
     during `f`'s prologue.
   - **Coroutine field packing and drop-elaboration unwind hazards (`#24292`,
     `#63616`, `ElaborateDrops`):** Desynchronized `StorageLive`/`StorageDead`
     markers across `Yield` points pack simultaneously live coroutine locals
     into overlapping union offsets; omitting drop-flag updates or panic guards
     during `ElaborateDrops` causes double-drops on unwind or use-after-free
     when safe code bypasses `Drop` ("Leakpocalypse").

3. **Architectural limits of external translation validators, proof-hint
   compilers, and automated C-to-Rust lifters:**
   - **Bounded SMT validation (`Alive2`, `PLDI 2021`):** Unrolling loops to a
     fixed bound $k$ (`-tv-unroll=k`) misses loop-carried miscompilations at
     iteration $k + 1$, while bit-blasting nonlinear integer multiplication,
     floating-point reductions, and wide SIMD permutes triggers SMT timeouts.
   - **Intrusive proof-hint maintenance collapse (`Crellvm`, `PLDI 2018`) and
     pass-coverage limits (`Vellvm`, `ICFP 2021`):** Instrumenting C++ LLVM
     passes to emit step-by-step relational proof hints proved brittle under
     upstream LLVM churn, while full monadic/ITree LLVM semantics remain too
     heavy to verify production C++ optimization passes directly.
   - **Vacuity and raw-pointer fallbacks in C-to-Rust lifting (`C2Rust`,
     `CROWN`, `CAV 2023`):** Ownership-guided lifters cannot safely translate C
     `union`s, non-tree aliasing, or variadics, and naive C-to-Rust refinement
     proofs either hold vacuously when the C source exhibits signed-overflow UB
     or introduce fresh Rust UB by translating valid C `(NULL, 0)` empty buffers
     into `core::slice::from_raw_parts(null(), 0)`.

In Anneal (`trusted-core` at `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` and
`mir-to-x86` at `4f45f0a391a921ced9c9dc773b9a040dbc215d14`), all fifteen
failure classes are ruled out structurally by the four orthogonal `trusted/lean/`
primitives—`Language SemObs` + `BehaviorCodec` + `Compiles`/`Abstracts`,
`ProductiveOn` + `InhabitedPre`, `SmallStepMachine` + `EventualBehaviorOf` +
`StepResult.externalCall`, and positive per-obligation `VerificationResult`—as
mechanized in the zero-axiom Lean 4.34.1 canary development in
[`support/MidLevelIrFailureCanaries.lean`](support/MidLevelIrFailureCanaries.lean).

## Applicability

This report applies to the design and verification of mid-level IR optimization
passes, high-level Rust/MIR lowering transformations, and cross-language
translation validators targeting Anneal's `trusted/` semantic kernel. The fifteen
subjects recorded in `REPORT.json` fall into four groups:

1. **Anneal's Pinned `trusted/` Foundation (`joshlf/anneal`):**
   - `trusted-core` at `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`
     (`trusted/lean/Trusted/Refinement.lean`,
     `trusted/lean/Trusted/StepResult.lean`,
     `trusted/lean/Trusted/MirSemantics.lean`), and
   - `mir-to-x86` at `4f45f0a391a921ced9c9dc773b9a040dbc215d14`
     (`trusted/lean/Trusted/Refinement.lean`,
     `trusted/lean/Trusted/X86Semantics.lean`,
     `trusted/audit/TrustedBoundary.lean`).
2. **Primary Literature on LLVM IR Undefined Behavior, Memory Models, and
   Rust Aliasing:**
   - Lee et al., *Taming Undefined Behavior in LLVM*, PLDI 2017 (`10.1145/3062341.3062343`);
   - Lee et al., *Reconciling High-Level Optimizations and Low-Level Code in
     LLVM*, OOPSLA 2018 (`10.1145/3276495`);
   - Lopes et al., *Alive2: Bounded Translation Validation for LLVM*, PLDI 2021
     (`10.1145/3453483.3454030`);
   - Jung et al., *Stacked Borrows: An Aliasing Model for Rust*, POPL 2020
     (`10.1145/3371109`);
   - Villani et al., *Tree Borrows*, PLDI 2025 (`10.1145/3735592`); and
   - `Simuliris` mechanized Rocq development at
     `e3abfcdc301f92250d4227fc03c00463bf57b982`.
3. **Primary Literature on SSA Destruction, Credible Compilation, Mechanized IR
   Semantics, and C-to-Rust Lifting:**
   - Briggs et al., *Practical Improvements to the Construction and Destruction
     of Static Single Assignment Form*, SPE 1998
     (`10.1002/(SICI)1097-024X(199807)28:8<859::AID-SPE175>3.0.CO;2-Z`);
   - Rideau, Serpette, and Leroy, *Tilting at Windmills with Coq: Formal
     Verification of a Compilation Algorithm for Parallel Moves*, JAR 2008
     (`10.1007/s10817-008-9097-3`);
   - Boissinot et al., *Revisiting Out-of-SSA Translation for Correctness, Code
     Quality, and Efficiency*, CGO 2009 (`10.1109/CGO.2009.19`);
   - Kang et al., *Crellvm: Verified Credible Compilation for LLVM*, PLDI 2018
     (`10.1145/3192366.3192398`);
   - Zakowski et al., *Modular, Compositional, and Executable Formal Semantics
     for LLVM IR* (`Vellvm`), ICFP 2021 (`10.1145/3473572`); and
   - Zhang et al., *Ownership Guided C to Rust Translation* (`CROWN`), CAV 2023
     (`10.1007/978-3-031-37709-9_22`).
4. **Historical `rust-lang/rust` Soundness and Miscompilation Issues:**
   - Issues `#24292` (Drop leakpocalypse / `Vec::drain`), `#28728` (infinite
     loop miscompilation), `#54878` / `#63818` / `#63934` (`mutable-noalias` on
     self-referential generators/Futures), `#63616` (partial initialization in
     generators), `#110947` / `#118328` (`ConstProp` miscompilations), `#120613`
     / `#141038` (`GVN` partial-move and aliasing miscompilations), and
     `#146383` (`DestinationPropagation` miscompilation).

Claims about upstream compiler bugs are scoped to the specific paper models or
issue revisions cited under **Evidence**. Claims about Anneal's prevention
mechanisms apply to the four `trusted/` primitives and are mechanically checked
by the Lean 4.34.1 kernel in `support/MidLevelIrFailureCanaries.lean`.

## Findings

### Finding 1: LLVM `undef` vs. `poison` Composition Paradoxes and Pointer-Integer Provenance Collapse

`Basis: source + execution + derived`

#### 1.1 The `LoopUnswitch` + `GVN` + `InstCombine` Composition Paradox (`PLDI 2017`)

Prior to the introduction of the `freeze` instruction, LLVM IR modeled
uninitialized memory and deferred arithmetic undefined behavior via two distinct
constructs:

- **`undef`**, which represented the set of all bit-patterns of a given type and
  permitted **different uses of the same SSA register** `v = undef` to observe
  independent bit-patterns (so `v ^ v` could refine to any integer, while `v + v`
  was neither guaranteed to be even nor fixed across uses); and
- **`poison`**, a tainting error token produced by arithmetic overflow (`add
  nsw`), out-of-bounds shifts (`shl`), or out-of-bounds `getelementptr inbounds`
  that triggered immediate Undefined Behavior (UB) when used as a branch
  condition (`br i1 %p`), memory address, divisor, or volatile/I/O operand.

As Lee et al. (*Taming Undefined Behavior in LLVM*, PLDI 2017, §§2–3, DOI
`10.1145/3062341.3062343`) demonstrated, this dual semantics made standard
mid-level optimizations **mutually inconsistent**:

1. **Why `LoopUnswitch` was unsound on `poison`:** Consider a well-defined loop
   whose invariant condition `c2` is computed from an expression `x +nsw 1` (or
   an uninitialized variable) that is only guarded inside `if (c1)`:
   ```llvm
   ; Source program (100% well-defined when c1 == false and x == INT_MAX):
   loop:
     %c2 = icmp slt i32 (%x +nsw 1), %y
     br i1 %c1, label %check_c2, label %safe_body
   check_c2:
     br i1 %c2, label %then, label %else
   ```
   When `c1` is `false` and `x == INT_MAX`, `%c2` evaluates to `poison`, but the
   source program never branches on `%c2` and is completely UB-free. If
   `LoopUnswitch` hoists `br i1 %c2` above the loop (duplicating the loop into a
   `%c2 == true` copy and a `%c2 == false` copy), the transformed program
   executes `br i1 poison` unconditionally on entry, turning a well-defined
   execution into immediate UB.
2. **Why `GVN` + `LoopUnswitch` was unsound on `undef`:** Conversely, if a
   variable `y` is uninitialized (`undef`) when a loop runs for `0` iterations or
   takes a non-reading branch, `SROA`/`mem2reg` promotes `y` to `undef`. If
   `LoopUnswitch` branches on `y` (`if (y) { L_true } else { L_false }`) and a
   subsequent `GVN` or `SCCP` pass propagates `y == true` inside `L_true` while
   another use of `y` earlier or later is independently refined as `false` (valid
   under multi-use `undef`), the combined pipeline executes both contradictory
   branches on a single path (LLVM PR21467 / PR31632).
3. **Why `select`-to-branch and `InstCombine` collided (`Alive2`, `PLDI 2021`):**
   Lopes et al. (*Alive2: Bounded Translation Validation for LLVM*, PLDI 2021,
   §§2, 5, DOI `10.1145/3453483.3454030`) further showed that rewriting
   `%r = select i1 %c, i32 %a, i32 %b` into an explicit diamond branch
   `br i1 %c` is unsound whenever `%c` can be `poison` and `%a == %b` (or `%r` is
   unused), because `select poison, %a, %b` merely returns `poison`, whereas
   `br i1 poison` triggers immediate UB. Similarly, `InstCombine` rewrites of
   `select i1 %c, i1 true, i1 %x` into `or i1 %c, %x` leaked `poison` from `%x`
   even when `%c == true`!

The only mathematically consistent resolution (Lee et al., PLDI 2017, §4) was to:
- Make `br i1 poison` immediate UB;
- Introduce a dedicated `freeze(v)` instruction that nondeterministically picks
  a **single, fixed** bit-pattern when `v` is `poison` so all downstream uses of
  `%f = freeze(v)` observe the exact same bitvector;
- Require `LoopUnswitch` and `PRE` to wrap speculated branch conditions in
  `freeze(%c2)` before hoisting `br i1`; and
- Deprecate per-use `undef` in favor of `freeze(poison)`.

#### 1.2 The `ptrtoint` / `inttoptr` + `GVN` Provenance Collapse (`OOPSLA 2018`)

Even with `freeze`, Lee et al. (*Reconciling High-Level Optimizations and
Low-Level Code in LLVM*, OOPSLA 2018, §2, DOI `10.1145/3276495`; LLVM PR34548 /
PR35229) proved that combining `GVN` with alias analysis causes end-to-end
miscompilations when two distinct allocations `p` and `q` happen to sit adjacent
in memory:

```c
char p[1], q[1];
uintptr_t ip = (uintptr_t)(p + 1); // One-past-the-end of p
uintptr_t iq = (uintptr_t)q;       // Base of q
if (ip == iq) {
    *(char *)iq = 10;              // Valid write to q[0] in source!
}
```

1. **Pass 1 (`GVN` equality propagation):** Inside the `if (ip == iq)` block,
   `GVN` observes `ip == iq` and replaces `iq` with `ip`, yielding
   `*(char *)ip = 10`, i.e., `*(char *)(uintptr_t)(p + 1) = 10`.
2. **Pass 2 (`InstCombine` cast folding):** `InstCombine` folds
   `(char *)(uintptr_t)(p + 1)` to `p + 1`, yielding `*(p + 1) = 10`.
3. **Pass 3 (`BasicAA` / `DSE`):** Alias analysis knows that a pointer derived
   from allocation `p` (`p + 1`) cannot alias allocation `q` (`noalias`), and
   furthermore dereferencing one-past-the-end of `p` (`*(p + 1)`) is immediate
   out-of-bounds UB! The optimizer therefore deletes the store `*(p + 1) = 10`
   or folds subsequent reads of `q[0]` to the old value.

The root cause is that `ip == iq` compares only the **numeric address**
(`Addr`), whereas `*(char *)iq` depends on the **allocation provenance**
(`AllocId`) carried by `iq` (or exposed via `ptrtoint`). Substituting `ip` for
`iq` under numeric equality is unsound whenever values carry hidden provenance
that `==` does not compare.

#### 1.3 Architectural Prevention in Anneal's `trusted/` Primitives

In Anneal (`Trusted/Refinement.lean` and `Trusted/MirSemantics.lean`), both
paradoxes are blocked at the root:

1. **Transitive Partial-Behavior Preorder (`Compiles`):** In
   `Trusted/Refinement.lean`, `Behavior Query Out := Query → Partial (Out → Prop)`
   defines refinement `B₂ ≤ B₁` by:
   $$\forall q,\; B_1(q).\text{defined} \implies \bigl(B_2(q).\text{defined} \;\wedge\; \forall o,\; B_2(q).\text{val}(o) \implies B_1(q).\text{val}(o)\bigr)$$
   Because `≤` is a verified reflexive, transitive preorder (`Preorder.le_trans`),
   it is **mathematically impossible** for a chain of verified passes $s = p_0
   \to p_1 \to \dots \to p_n = t$ satisfying `Compiles` at each step to miscompile
   a defined source input $q$. Any pass that attempts to hoist a branch on a
   potentially uninitialized or trapping value onto a path where the source was
   `.defined` fails `B₂(q).defined` at that step, as mechanized in
   `loopUnswitch_without_freeze_violates_compiles` in
   `support/MidLevelIrFailureCanaries.lean`.
2. **Typed Provenance Separation (`MirVal` vs. Numeric `BitVec`):** In
   `MirSemantics.lean`, pointers (`MirVal.ref` / `(AllocId, Offset, Tag)`) are
   distinct from integer bitvectors (`MirVal.int`). Therefore, an integer
   equality guard `ip == iq` proves equality of numeric addresses only, never
   equality of `(AllocId, Offset)` pairs; `GVNCertifier` cannot substitute a
   pointer of provenance `AllocId(p)` for `AllocId(q)` without falsifying the
   memory-step refinement obligation (`gvn_provenance_substitution_rejected` in
   `support/MidLevelIrFailureCanaries.lean`).

---

### Finding 2: `rustc` `-Zmir-opt-level=3/4` and `mutable-noalias` Miscompilations

`Basis: source + documentation + execution + derived`

#### 2.1 The Multi-Year `mutable-noalias` Saga on Self-Referential Generators and `Future`s (`#54878`, `#63818`, `#63934`)

Rust's borrow checker guarantees that safe mutable references `&mut T` are
unique, which in principle maps to LLVM's `noalias` parameter attribute. In
practice, `rustc` had to disable `-Zmutable-noalias` repeatedly for over five
years (`rust-lang/rust#54878`, tracking LLVM bugs and self-referential
miscompilations `#63818` and `#63934`):

- **Root Cause 1 (Self-Referential Coroutine State Machines):** When an `async
  fn` or generator creates a local variable `x` and a reference `r = &x` that
  both live across an `.await` (`Yield`) suspension point, `rustc`'s coroutine
  lowering pass packs both `x` and `r` into fields of the synthesized
  `CoroutineState` struct. When `Future::poll(self: Pin<&mut Self>, cx: &mut
  Context)` is invoked, `self` is passed as `&mut CoroutineState`. If `rustc`
  marks the `self` pointer argument as LLVM `noalias`, LLVM's `ScopedNoAliasAA`
  assumes that **every memory access through a pointer not syntactically derived
  from the `self` parameter argument during that `poll` call does not alias
  `*self`**. However, inside the resumed state block, the coroutine loads the
  stored field `r = (*self).field_r` from memory and then accesses `*r`! Because
  `r` was loaded from memory rather than computed via `getelementptr` from the
  incoming `self` pointer argument, LLVM's alias analysis concluded that `r` was
  not based on `self`, treated `*r` and `(*self).field_x` as non-aliasing, and
  reordered or deleted stores across them (`#63818`, `#63934`).
- **Root Cause 2 (Fix via `!Unpin` and Tree Borrows):** `rustc` had to suppress
  `noalias` on `&mut T` whenever `T` did not implement `Unpin` (i.e., could be a
  pinned self-referential generator/Future) and later align its aliasing model
  with Stacked Borrows (`UnsafePinned` / `Pin<&mut T>`) and Tree Borrows.

#### 2.2 `rustc_mir_transform` Pass Miscompilations (`GVN`, `ConstProp`, `DestinationPropagation`, `DSE`, and Coroutine `StorageLive` Overlap)

As `rustc` expanded its native MIR optimization pipeline (`-Zmir-opt-level=2/3/4`
in `compiler/rustc_mir_transform`), several soundness bugs (`I-unsound`,
`A-mir-opt`) escaped into nightly and stable compilers because passes reasoned
about syntactic MIR places without a mechanized operational semantics:

1. **`GVN` Reusing Partially Moved Function Arguments (`rust-lang/rust#120613`)
   and Overlapping Aliasing Assignments (`#141038`):** In `#120613`, `rustc`'s
   MIR `GVN` pass recorded that `_2 = move (_1.0)` had the same value number as
   `_1.0`. After `_1.0` was moved and dropped/mutated, a subsequent read of `_2`
   was rewritten by `GVN` back into a read of `_1.0`, causing a use-after-move /
   double-drop miscompilation. In `#141038`, `GVN` substituted an aliased place
   into the right-hand side of an assignment `*_1 = *_2` when `_1` and `_2`
   pointed to overlapping memory, violating MIR's requirement that `Assign(dst,
   Use(Operand::Copy(src)))` has non-overlapping `dst` and `src`.
2. **`ConstProp` Propagating Across Mutating Borrows (`rust-lang/rust#110947`)
   and Corrupting Pointer-Typed Enum Fields (`#118328`):** In `#110947`, MIR
   `ConstProp` tracked constant values stored into a local `_1`, failed to
   invalidate that constant knowledge when an interior raw pointer or mutable
   reborrow mutated `_1`, and folded a post-mutation read of `_1` to the stale
   pre-mutation constant. In `#118328`, `ConstProp` misread niche-encoded enum
   layouts containing pointers (`Option<NonNull<T>>`), folding a valid non-null
   pointer field to a zero scalar constant.
3. **`DestinationPropagation` and `DeadStoreElimination` Desynchronizing
   `StorageLive`/`StorageDead` Across Coroutine Yields (`rust-lang/rust#63616`,
   `#146383`):** In MIR, `StorageLive(l)` and `StorageDead(l)` control both
   LLVM's `llvm.lifetime.start`/`end` stack-slot coloring and `rustc`'s
   coroutine state-machine layout packing (`compiler/rustc_mir_transform/src/coroutine.rs`).
   When `DestinationPropagation` (`#146383`) merged destination places `_dst`
   and `_tmp` without taking the union of their `StorageLive`..`StorageDead`
   live ranges, or when coroutine lowering (`#63616`) computed storage conflicts
   for partially initialized aggregates across `Yield`, two locals that were
   simultaneously live across a suspension point were assigned **overlapping
   byte offsets** inside the `CoroutineState` union, silently overwriting each
   other across `.await`.

#### 2.3 Architectural Prevention in Anneal's `trusted/` Primitives

Anneal's architecture prevents every class of `rustc` MIR optimizer and
coroutine-layout miscompilation in two complementary ways:

1. **Extraction of Post-Optimization `Runtime(PostCleanup)` MIR:** For crates
   compiled by `rustc`, `anneal-rustc-capture` extracts `Runtime(PostCleanup)`
   MIR *after* all MIR transformations (`ElaborateDrops`, `Coroutine` lowering,
   `GVN`, `DestinationPropagation`) have already executed. Thus, any bug in an
   upstream `rustc` MIR pass that introduces an overlapping assignment, a stale
   `StorageDead` access, or an overlapping coroutine variant offset is exposed
   directly in the captured `MirBody` and **fails verification** against
   `MirMachine`'s operational semantics (where accessing a `StorageDead` local
   or overlapping `Assign` transitions to `.failed .ub`).
2. **Certifying MIR-to-MIR Validators (`Compiles L_MIR L_MIR`):** When MIR
   optimizations (`GVNCertifier`, `BorrowMemoryOpt`, `CoroutineLoweringValidator`)
   are run inside Anneal's verified pipeline, `MirMachine` tracks per-local
   liveness (`StorageLive`/`StorageDead`), initialization masks, and borrow tags
   explicitly in `State`. A `GVN` rewrite that substitutes a moved/deallocated
   place (`#120613`), a `ConstProp` fold that ignores an aliasing write
   (`#110947`), or a coroutine layout packing that overlaps two co-live fields
   (`#63616`) fails the `Compiles` refinement theorem inside the Lean 4 kernel
   (`coroutine_overlapping_live_fields_rejected` in
   `support/MidLevelIrFailureCanaries.lean`).

---

### Finding 3: Stacked Borrows and Tree Borrows Protector Bugs on Diverging External Calls

`Basis: source + execution + derived`

#### 3.1 The Dead-Store Elimination Paradox Across Diverging External Calls (`POPL 2020`, `PLDI 2025`, `Simuliris`)

One of the primary goals of Rust's aliasing models—Stacked Borrows (Jung et al.,
POPL 2020, DOI `10.1145/3371109`) and Tree Borrows (Villani et al., PLDI 2025,
DOI `10.1145/3735592`)—is to validate intra-function memory optimizations on
unique mutable references `x : &mut i32` across calls to unknown external
functions `ext()`. To keep `x` unaliased for the entire duration of a function
 call `fn foo(x: &mut i32)` even when `foo` does not access `x` after calling
`ext()`, both models attach a **Function-Entry Protector** to `x`'s borrow tag
$\tau_x$ upon entering `foo`, which remains active until `foo` returns.

During the Rocq mechanization of Stacked Borrows and Tree Borrows in
`Simuliris` (`e3abfcdc301f92250d4227fc03c00463bf57b982`), researchers discovered
that **sinking a store or eliminating a dead store across an unknown call
`ext()` is unsound under naive protector semantics if `ext()` diverges or
aborts**:

```rust
// Suppose a raw pointer `RAW_ALIAS` pointing to `*x` was legally created
// before `foo` was called (under Tree Borrows `Reserved` lazy initialization)
// or exposed via a parent tag, and stored in a global/thread-local variable.
pub fn foo(x: &mut i32) {
    *x = 1;      // Store 1 (appears overwritten by Store 2 below!)
    ext();       // Opaque external call: what if `ext()` reads `RAW_ALIAS`,
                 // prints its value, and then enters `loop {}` or `exit(0)`?
    *x = 2;      // Store 2
}
```

Consider what happens if a Dead Store Elimination (`DSE`) pass transforms `foo`
into `foo_opt` by deleting `*x = 1` (reasoning that `ext()` cannot legally read
or write `*x` without violating `x`'s protector, and `*x = 2` overwrites `*x = 1`
immediately after `ext()` returns):

1. **Case A (`ext()` returns normally):** If `ext()` read `RAW_ALIAS` during its
   execution, then in Stacked Borrows (or Tree Borrows once `*x = 1` activated
   $\tau_x$), reading `RAW_ALIAS` either immediately triggered protector UB or
   disabled $\tau_x$ so that either the protector check at `foo`'s exit or the
   subsequent write `*x = 2` triggered UB. Thus on all returning executions,
   `foo` had UB whenever `ext()` observed `*x`, making `DSE` sound.
2. **Case B (`ext()` diverges `loop {}` or terminates the process `exit(0)`):**
   Suppose `ext()` reads `*RAW_ALIAS`, prints the value it observes to standard
   output (`Obs`), and then enters an infinite loop `loop {}`!
   - Because `ext()` **never returns** to `foo`, the statement `*x = 2` in `foo`
     and `foo`'s function-exit protector check **never execute**!
   - Under a **Weak Protector** (or in Tree Borrows if `*x = 1` is deleted so
     $\tau_x$ remains in the `Reserved` state at function entry!), deleting
     `*x = 1` means that when `ext()` reads `*RAW_ALIAS` in `foo_opt`, $\tau_x$
     was never activated by a write! In Tree Borrows without an entry write, a
     foreign read of a `Reserved` mutable reference transitions $\tau_x$ to
     `Frozen`—which is **not UB** unless $\tau_x$ is later written or checked by
     a strong exit rule! Since `ext()` diverges and never returns, `foo_opt`
     never writes to $\tau_x$, whereas in the unoptimized `foo`, `*x = 1` wrote
     `1` and activated $\tau_x$ before `ext()` ran.
   - Even if $\tau_x$ is already `Active`, if protector violation is only
     checked when popping the call frame on return (`Weak` exit-only check), a
     diverging `ext()` never pops `foo`'s frame, so `foo` is UB-free and prints
     `1` before diverging, whereas `foo_opt` prints the old pre-`foo` value of
     `*x` before diverging—a **complete end-to-end miscompilation of a UB-free
     program**!

To restore soundness for `DSE` and store sinking across potentially diverging
external calls, Villani et al. (*Tree Borrows*, PLDI 2025, §4; `Simuliris`
`theories/tree_borrows/`) proved that:
- Protected references must distinguish **`Strong` vs. `Weak` protectors**: a
  `Strong` protector makes any foreign read of an `Active` protected `&mut T`
  **immediate UB at the moment of the foreign read** (even if the function later
  diverges), and
- Deleting or sinking the first write `*x = 1` across `ext()` is sound **only**
  if function entry already performs an implicit/virtual write initialization
  (or `x` enters as `Active` rather than `Reserved`), because otherwise deleting
  `*x = 1` removes the state transition from `Reserved` to `Active` that made
  `ext()`'s foreign read UB in the source program!

#### 3.2 Architectural Prevention in Anneal's `trusted/` Primitives

Anneal's `trusted/` architecture (`StepResult.externalCall` + `EventualBehaviorOf`
in `Trusted/StepResult.lean`, validated by the re-entrancy canaries in
`anneal-structural-external-calls-and-tcb-mutation-testing-2026`) directly
enforces both halves of this invariant:

1. **Immediate Call-Site Boundary Enforcement (`StepResult.externalCall`):**
   ```lean
   StepResult.externalCall (boundaryInv : Bool) (branches : State → Prop) :=
     if boundaryInv then .choice .demonic branches else .failed .ub
   ```
   In `MirMachine`, `boundaryInv` checks caller-side invariants *before* the
   external call begins, and `branches` constrains all reachable states (both on
   return and along internal callback/diverging prefixes) to preserve memory
   locations guarded by active `Strong` caller protectors. Any foreign access to
   an `Active` strongly protected caller location transitions immediately to
   `.failed .ub` at the access step, not lazily at function return.
2. **Distinguishing `Reserved` vs. `Active` in `Compiles`:** In
   `support/MidLevelIrFailureCanaries.lean`
   (`dse_across_diverging_call_unsound_under_weak_or_unactivated_protector` and
   `dse_across_diverging_call_sound_under_strong_active_protector`), Lean's
   kernel machine-checks both directions: when a protector is `Weak` (checked
   only at return) or `Reserved` (not yet activated on entry), eliminating
   `*x = 1` before a diverging `externalCall` violates `Compiles`; when the
   entry state marks `x` as `Active` under a `Strong` protector, any foreign
   observation inside `externalCall` triggers immediate `.failed .ub` in the
   source, so `Compiles` holds across both returning and `.diverges` outcomes.

---

### Finding 4: C++/Rust Forward-Progress (`mustprogress` / `willreturn`) Infinite-Loop Miscompilations

`Basis: normative + source + execution + derived`

#### 4.1 `rust-lang/rust#28728`: How LLVM Deleted Safe Rust `loop {}` Blocks and Executed Unreachable Code

For nearly six years (2015–2021), `rust-lang/rust#28728` (*"LLVM loop
optimization can make safe programs crash"*) stood as one of the most severe
soundness bugs in safe Rust. Under C++11 `[intro.progress]`, the C++ standard
allows an implementation to assume that any thread will eventually either
terminate, make a call to a library I/O function, perform a `volatile` access,
or perform an atomic synchronization operation. Consequently, in C++, a
side-effect-free infinite loop `while (true) {}` is Undefined Behavior.

Because LLVM was originally architected around C/C++ assumptions, multiple LLVM
middle-end passes (`SimplifyCFG`, `LoopDeletion`, `ADCE` — Aggressive Dead Code
Elimination, and `PostDominatorTree` construction) assumed that **every
side-effect-free loop terminates**:

```rust
pub fn hang_forever() -> ! {
    loop {} // 100% safe, well-defined diverging loop in Rust!
}

pub fn safe_caller(cond: bool) -> i32 {
    if cond {
        hang_forever();
    }
    // In Rust, this point is only reachable when `cond == false`!
    42
}
```

When LLVM optimized Rust programs containing side-effect-free infinite loops:
1. **`LoopDeletion` / `ADCE` deleted the loop:** Because `loop {}` has no memory
   writes, `volatile` operations, or calls, `ADCE` marked the loop's branch
   backedge as dead control flow and removed the loop entirely.
2. **Fallthrough into unreachable code (`!`) and missing `ret` instructions:**
   Because `hang_forever() -> !` returns the uninhabited never type `!`, `rustc`
   emitted LLVM's `unreachable` terminator immediately after the `loop {}` body.
   Once LLVM deleted the `loop {}`, execution fell straight into `unreachable`!
   In optimized builds, LLVM stripped everything ending in `unreachable`—meaning
   `hang_forever()` compiled to an **empty `0`-byte function body with no `ret`
   instruction**, falling straight through into whatever function happened to be
   placed next in the `.text` section of the ELF binary!
3. **Backward UB propagation (`cond` forced to `false`):** In `safe_caller`,
   because the `cond == true` branch ended in `unreachable` after loop deletion,
   `SimplifyCFG` deduced that `cond` could *never* be `true` on any valid
   execution, deleted the `if cond` check altogether, and unconditionally
   returned `42` (or corrupted memory when a bounds check was guarded by a
   diverging loop).

Fixing `rust-lang/rust#28728` required a fundamental redesign of LLVM's loop and
function attributes in LLVM 12 (`rust-lang/rust#81255`, `#83359`):
- LLVM introduced the **`mustprogress`** function and loop metadata attribute
  (which Clang emits for C++ functions, but `rustc` omits because Rust permits
  silent infinite loops) and the **`willreturn`** function attribute (asserting
  that a function call is guaranteed to return in finite time without
  diverging).
- `LoopDeletion`, `ADCE`, and `DeadStoreElimination` were restricted to eliminate
  loops or dead operations across calls only when `mustprogress` / `willreturn`
  is proven.

#### 4.2 Related Loop-Speculation Failure: Hoisting Trapping Operations Above Zero-Trip or Diverging Loops (`LICM` and `PRE`)

A closely related failure mode occurs in Loop-Invariant Code Motion (`LICM`) and
Partial Redundancy Elimination (`PRE`, Knoop-Rüthing-Steffen lazy code motion):
- Suppose a loop body contains a loop-invariant division `q = a / d` (which in
  Rust MIR emits an `Assert(d != 0)` panic check, and in x86-64 emits `idiv` /
  `udiv` which raises hardware `#DE` on `d == 0` or `INT64_MIN / -1`), preceded
  inside the loop by an early exit `if exit_now { break; }` or an infinite loop
  `if hang { loop {} }` or an external call `ext()`.
- If `LICM` hoists `q = a / d` into the loop preheader without proving either
  that `q = a / d` is **non-trapping (`d != 0`)** or that the loop executes
  $\ge 1$ iteration (`TripCount ≥ 1`) and `q = a / d` dominates all loop exits,
  external calls, and internal loops, then on an input where `d == 0` and
  `TripCount == 0` (or `hang == true`), the source program returns normally (or
  diverges silently in `loop {}`), whereas the target program panics or traps in
  the preheader!

#### 4.3 Architectural Prevention in Anneal's `trusted/` Primitives

Anneal's `EventualBehaviorOf` primitive (`Trusted/StepResult.lean`) makes silent
divergence a first-class, non-deletable semantic outcome:

1. **Bidirectional Divergence Preservation (`EventualOut.diverges`):**
   In `EventualBehaviorOf`, `EventualOut Obs Val` is the disjoint sum:
   ```lean
   inductive EventualOut (Obs Val : Type) where
     | terminated (trace : List Obs) (term : Terminal Val)
     | diverges
   ```
   A machine state $s$ has outcome `.diverges` iff $\forall n : \mathbb{N},\;
   \exists s',\; \text{StepsN } M\; n\; s\; (.running\; s')$. Under `Compiles`,
   every outcome produced by the target `t` on a defined source query `q` must
   decode (`codec.decodeOut o₂ = some o₁` with `idCodec`) to a valid outcome of
   the source `s`.
   - If the source program `s` diverges (`s` only produces `.diverges` on query
     `q`), any target `t` that deletes the infinite loop and terminates with
     `.terminated trace term` produces an outcome `.terminated ... ∉ {.diverges}`,
     **immediately falsifying `Compiles`** (`infinite_loop_deletion_violates_compiles`
     in `support/MidLevelIrFailureCanaries.lean`)!
   - Conversely, if `s` terminates (`s` only produces `.terminated trace term`),
     any target `t` that introduces a new infinite loop produces `.diverges ∉
     {.terminated trace term}`, also falsifying `Compiles`.
   - Furthermore, under `ProductiveOn`, a diverging loop cannot be replaced by
     an empty (`unreachable`) behavior `fun _ => False` because `ProductiveOn`
     enforces Dijkstra's Law of the Excluded Miracle ($\exists o,\; B(q)(o)$).
2. **Preventing Premature Panics / Traps When Hoisting Across Loops (`LICM` /
   `PRE`):** In `MirSemantics.lean` and `EventualBehaviorOf`, a Rust panic
   (`.terminated trace (.panic msg)`) has a distinct `SemObs` from normal return
   (`.terminated trace (.normal ())`) and from `.diverges`, while hardware
   division-by-zero traps (`.failed .ub`) make `defined = False`. Consequently,
   hoisting `a / d` into a preheader when `s` would have taken 0 iterations or
   diverged in `loop {}` on `d = 0` is provably rejected by `Compiles`
   (`licm_hoisting_trapping_div_above_zero_trip_or_diverging_loop_rejected` in
   `support/MidLevelIrFailureCanaries.lean`).

---

### Finding 5: SSA Destruction (`Lost-Copy` and `Swap` Bugs), Tail-Call Stack-Escape Corruption, and Drop-Elaboration / Unwind Safety Failures

`Basis: source + execution + derived`

#### 5.1 The Briggs/Boissinot `Lost-Copy` and `Swap` Bugs in Naive SSA Destruction (`SPE 1998`, `JAR 2008`, `CGO 2009`)

When lowering a program out of Static Single Assignment (`SSA`) or
block-argument `AnSSA` form (`Goto(bb, [e₁, ..., e_k])`) into mutable registers
or stack slots, all $\phi$-functions (or block parameters) at a basic-block entry
must execute **simultaneously as a parallel assignment** $(x_1, \dots, x_k) :=
(v_1, \dots, v_k)$, reading every right-hand side $v_i$ before any left-hand
side $x_j$ is overwritten.

Cytron et al.'s original out-of-SSA algorithm (TOPLAS 1991) placed sequential
copy instructions `x_i = v_i` at the end of each predecessor block. As Briggs,
Cooper, Harvey, and Simpson (*Practical Improvements to the Construction and
Destruction of Static Single Assignment Form*, SPE 1998, DOI
`10.1002/(SICI)1097-024X(199807)28:8<859::AID-SPE175>3.0.CO;2-Z`) and
Boissinot, Darte, Dupont de Dinechin, Guillon, and Rastello (*Revisiting
Out-of-SSA Translation for Correctness, Code Quality, and Efficiency*, CGO 2009,
DOI `10.1109/CGO.2009.19`) proved, naive predecessor copy placement fails on two
classic control-flow patterns:

1. **The `Swap` Bug (Cyclic Parallel Moves on Loop Backedges):**
   Suppose a loop header block `bb_hdr(a, b)` receives a backedge transfer
   `Goto(bb_hdr, [b, a])` (or two $\phi$-nodes `a₂ = φ(a₁, b₂); b₂ = φ(b₁, a₂)`
   after live-range coalescing maps `a₁, a₂` to register `a` and `b₁, b₂` to
   register `b`). Lowering the parallel edge transfer `(a, b) := (b, a)`
   naively into the sequential assignments:
   ```text
   a := b;
   b := a;   // BUG: reads the newly overwritten `a` (which is now `b`)!
   ```
   clobbers `a` on the first move, leaving both `a` and `b` holding the initial
   value of `b`! More generally, any directed permutation cycle of length $c \ge 2$
   in the parallel-move dependency graph requires either a scratch register
   (`tmp := a; a := b; b := tmp`) or a hardware swap instruction (`xchg`), as
   mechanized in Coq by Rideau, Serpette, and Leroy (*Tilting at Windmills with
   Coq: Formal Verification of a Compilation Algorithm for Parallel Moves*, JAR
   2008, DOI `10.1007/s10817-008-9097-3`).
2. **The `Lost-Copy` Bug (Critical Edges + Copy Folding):**
   Suppose a loop body computes `x₂ = x₁ + 1` and ends with a conditional branch
   `if (p) goto bb_hdr else goto bb_exit`, where `bb_hdr` has $\phi$-node
   `x₁ = φ(x₀, x₂)` and `bb_exit` uses the pre-increment value `x₁`! Because
   the edge from the loop latch to `bb_hdr` shares a predecessor with `bb_exit`
   (a critical edge when `bb_exit` also has other predecessors), inserting the
   backedge copy `x₁ := x₂` at the end of the loop latch *before* the conditional
   branch overwrites `x₁` on the path to `bb_exit`! When the loop exits,
   `bb_exit` observes `x₂` instead of `x₁` (the old copy of `x₁` was lost).

#### 5.2 Tail-Call Stack-Escape Corruption (`LLVM tailcallelim` / `AllocaDerivedValueTracker`)

Tail-Call Optimization (`TCO` / sibling-call elimination / `tailcallelim` in
LLVM and `become` in Rust MIR) replaces a call-followed-by-return sequence
`dest = Call(f, args); Return(dest)` with a direct frame-reusing jump (`TailCall`
or a loop backedge to the entry block for tail recursion), deallocating or
overwriting the caller's stack frame *before* `f` executes.

In LLVM's `TailRecursionElimination.cpp` (`tailcallelim`), historical
miscompilations occurred whenever `AllocaDerivedValueTracker` failed to detect
that a pointer derived from a stack local (`alloca` or an incoming `byval`
stack copy) escaped into the tail-called function's arguments or a global:

```rust
fn caller(n: usize) -> u64 {
    let local_buf: u64 = 99;
    // If `callee(&local_buf)` is lowered to a frame-reusing TailCall,
    // `caller`'s stack frame is popped/reused BEFORE `callee` reads `*ptr`!
    callee(&local_buf, n)
}
```

When `caller`'s stack frame is reused by `callee`'s prologue (or overwritten by
the next loop iteration in tail-recursion elimination), `callee` dereferences a
dangling stack pointer (`&local_buf`), reading its own spilled registers or
return address instead of `99`.

#### 5.3 Drop Elaboration, Unwind Double-Drops, and the `Drop` Leakpocalypse (`rust-lang/rust#24292`, `ElaborateDrops`)

High-level Rust lowering must also desugar scope-based destructors (`Drop::drop`)
and collection iterators across both normal control flow and stack unwinding:

1. **Unwind Double-Drop and Missing Drop-Flag Updates (`ElaborateDrops`):**
   In pre-elaboration MIR, a variable `x` may be conditionally moved out on one
   branch (`if cond { consume(x); }`) and dropped at scope exit. `rustc`'s
   `ElaborateDrops` pass lowers conditional drops by introducing runtime boolean
   stack drop flags (`drop_flag_x : bool`), setting `drop_flag_x = true` on
   initialization, `drop_flag_x = false` before moving or dropping `x`, and
   guarding the cleanup landing pad with `if drop_flag_x { drop_in_place(&mut x) }`.
   If a pass clears `drop_flag_x = false` *after* calling `drop_in_place(&mut x)`
   instead of *before*, or omits updating the flag on an unwind edge when
   dropping field `s.a` of a struct panics during unwinding, the unwind landing
   pad drops `s.a` a **second time** (double-free UB)! Furthermore, if `s.b`'s
   destructor *also* panics while the thread is already unwinding from `s.a`'s
   panic, failing to transition to immediate process `.abort` (Rust's
   double-panic rule) corrupts the unwinder state.
2. **The "Leakpocalypse" (`rust-lang/rust#24292`) and `Vec::drain` Exception
   Safety:** In 2015 (`#24292`), the Rust project discovered that `std::thread::scoped`
   (`JoinGuard`) and `Vec::drain` assumed their `Drop` implementation was
   guaranteed to run before the enclosing function returned. Because safe Rust
   can construct an `Rc<RefCell<...>>` reference cycle (or call `mem::forget`)
   to leak any value without running `Drop`, leaking a pre-fix `Vec::drain`
   iterator left the parent `Vec`'s `len` unchanged after elements had already
   been moved out of its backing buffer—causing safe code after `drain` to read
   uninitialized/already-dropped memory (use-after-free)! Fixing `#24292`
   required `Vec::drain` to set `self.set_len(start)` **before** handing out the
   `Drain` iterator (the "pre-pooping your pants" invariant) so that even if
   `Drain::drop` never runs (or a user callback panics mid-iteration), the
   `Vec`'s `AdtInv` (`initialized_prefix >= len`) remains valid at every external
   observation point.

#### 5.4 Architectural Prevention in Anneal's `trusted/` Primitives

Each of these lowering and cleanup hazards is caught directly by Anneal's four
primitives:

1. **Catching `Swap` and `Lost-Copy` via `Compiles L_AnSSA L_MIR` and
   `EventualBehaviorOf`:** In `SSADestructCertifier`, the source `AnSSA` machine
   executes parallel block-argument assignment atomically in $1$ step, while the
   target `MirMachine` executes the lowered sequential move list in $k + 1$
   steps (`EventualBehaviorOf` absorbs the $1 \to k + 1$ step dilation). When a
   parallel swap `(a, b) := (b, a)` is lowered without a scratch temporary into
   `a := b; b := a`, executing those 2 steps in `MirMachine` produces final
   state `(b, b) ≠ (b, a)`, refuting `Compiles`
   (`naive_ssa_swap_lowering_violates_compiles` and
   `temp_ssa_swap_lowering_satisfies_compiles` in
   `support/MidLevelIrFailureCanaries.lean`).
2. **Blocking Tail-Call Stack Escape via `StorageDead` Frame Deallocation:**
   In `MirMachine`, deallocating the caller's stack frame before a `TailCall`
   marks every caller stack `AllocId` as deallocated (`StorageDead`). If a
   pointer to any caller local was passed in `args` to the tail callee, the
   callee's first dereference of that pointer hits a deallocated `AllocId` and
   transitions to `.failed .ub`, falsifying `Compiles`
   (`tail_call_with_escaping_stack_ref_violates_compiles` in
   `support/MidLevelIrFailureCanaries.lean`).
3. **Catching `ElaborateDrops` Double-Drops and `Vec::drain` Leak/Unwind Bugs:**
   In `MirMachine`, dropping an already-dropped place transitions to
   `.failed .ub`, while `StepResult.externalCall` checks `AdtInv` at every open
   call boundary (`#24292`). If `Vec::drain` fails to set `vec.len = start`
   before yielding to a caller loop body or panicking callback (or if
   `ElaborateDrops` fails to clear `drop_flag` before invoking `Drop::drop`),
   the resulting state violates `AdtInv` or double-drops on unwind, refuting
   `Compiles` (`drop_elaboration_clear_after_drop_double_frees_on_unwind` in
   `support/MidLevelIrFailureCanaries.lean`).

---

### Finding 6: Translation Validator, Credible Compilation, and C-to-Rust Lifting Limitations

`Basis: source + documentation + execution + derived`

#### 6.1 `Alive2`: Bounded Loop Unrolling (`-tv-unroll=k`) and SMT Bitvector Timeouts (`PLDI 2021`)

Lopes et al. (*Alive2: Bounded Translation Validation for LLVM*, PLDI 2021,
§§1, 7, DOI `10.1145/3453483.3454030`) demonstrated that SMT-backed translation
validation is extraordinarily effective at finding LLVM bugs, but faces two
fundamental architectural boundaries when used as a verification gate:

1. **Bounded Loop Unrolling Misses Loop-Carried Miscompilations Past Bound $k$:**
   Because Alive2 lowers CFG validation directly to loop-free SMT queries
   without synthesizing or checking inductive loop invariants, it unrolls loops
   to a fixed small bound $k$ (by default $k = 1$ or $k = 2$ in routine runs).
   Any optimization bug that only manifests when a loop executes $> k$
   iterations—such as an Induction-Variable Strength Reduction (`IVSR`) wrap
   bug, a loop-vectorization (`Simd<T, W>`) tail-lane overwrite on iteration
   $W + 1$, or a wrong trip-count mask—falls outside the unrolled formula and
   is silently accepted as "no counterexample found within bound $k$."
2. **SMT Solver `timeout` / `unknown` on Nonlinear Arithmetic, Floating-Point,
   and Wide Vectors:** Encoding 64-bit integer multiplication/division, IEEE-754
   floating-point associative reductions, or 256/512-bit SIMD shuffle networks
   into monolithic `QF_ABV` / `QF_FPBV` SMT queries frequently causes Z3 to
   return `timeout` or `unknown`. Furthermore, trusting an external C++ SMT
   solver's unverified `unsat` answer places the entire 500k-LoC solver inside
   the Trusted Computing Base (TCB).

#### 6.2 `Crellvm` Proof-Hint Maintenance Collapse (`PLDI 2018`) and `Vellvm` Pass-Coverage Limits (`ICFP 2021`)

To avoid both bounded unrolling and SMT timeouts, Kang et al. (*Crellvm:
Verified Credible Compilation for LLVM*, PLDI 2018, DOI
`10.1145/3192366.3192398`) built a Coq-verified Relational Hoare Logic (`RHL`)
proof checker for LLVM IR and modified C++ LLVM passes (`GVN`, `LICM`, `SROA`,
`InstCombine`) to emit step-by-step **proof hints** (`Hint`) as they mutated
the IR. While Crellvm successfully verified pass runs with a small Coq TCB, the
architecture suffered from a fatal software-engineering failure mode:

- **Intrusive C++ Pass Instrumentation vs. Upstream LLVM Churn:** Every minor
  refactoring inside LLVM's C++ pass implementations (such as changing helper
  traversal order in `GVN.cpp` or `SROA.cpp` across LLVM point releases) broke
  the tightly coupled C++ hint-generation hooks. Maintaining invasive instrumentation
  inside millions of lines of fast-moving C++ LLVM code proved unsustainable,
  leading to the abandonment of the instrumented LLVM fork after LLVM 3.9/7.0.
- **Vellvm's Full-Pass Verification Gap (`ICFP 2021`):** Conversely, Zakowski
  et al. (*Modular, Compositional, and Executable Formal Semantics for LLVM IR*,
  ICFP 2021, DOI `10.1145/3473572`) mechanized a modular Interaction Trees
  (`ITree`) semantics for sequential LLVM IR (`Vellvm`), enabling foundational
  proofs of small reference passes (`helix`, simple constant folding). However,
  proving full production optimization passes directly over monadic `ITree`
  denotations requires re-implementing the entire compiler pass inside Rocq/Coq
  and proving manual simulation lemmas for every case—which cannot validate
  external Rust/C++ compiler passes (`rustc`, `regalloc2`, `isl`, `egg`)
  without a certificate-checking bridge.

#### 6.3 `C2Rust` and `CROWN` Ownership-Lifting Failures and Cross-Language Refinement Vacuity (`CAV 2023`)

In C-to-Rust migration, syntactic transpilers (`C2Rust`) translate C pointer
code into `unsafe extern "C"` Rust using raw pointers (`*mut T`). Ownership-guided
refactoring tools such as `CROWN` (Zhang et al., *Ownership Guided C to Rust
Translation*, CAV 2023, DOI `10.1007/978-3-031-37709-9_22`) solve global
ownership and mutability constraints to rewrite `*mut T` into safe `Box<T>`,
`Option<&mut T>`, and slices `&mut [T]`. Historical experience with `C2Rust` and
`CROWN` exposes three critical verification failures when certifying C-to-Rust
translations:

1. **Inability to Lift C `union`s, Non-Tree Aliasing (Cyclic/Doubly-Linked
   Lists), Pointer Arithmetic, and Variadics:** Whenever a C struct uses an
   untagged `union`, performs sub-object pointer arithmetic (`container_of`), or
   shares mutable aliases across non-tree graphs, `CROWN`'s ownership solver
   cannot assign unique Rust `&mut` ownership and either aborts lifting or falls
   back to unverified `unsafe` raw-pointer blocks.
2. **The Vacuous C-Source UB Trap (`signed` Overflow / Uninitialized Read):**
   Suppose a verifier checks only `Compiles L_Clight L_MIR cToRustCodec f_c f_rust`
   (`L_MIR.sem f_rust ≤ codec (L_Clight.sem f_c)`). If `f_c` contains an
   unintended C Undefined Behavior bug on its input domain (for example, signed
   integer overflow `x + 1` at `x = INT_MAX`, or a missing null precondition),
   then `L_Clight.sem f_c q` is `.undefined` (`defined = False`). Because
   refinement `≤` has `L_Clight.sem f_c q).defined` as its antecedent, **`Compiles`
   holds vacuously even if `f_rust` immediately triggers Rust UB or formats the
   hard drive**!
3. **The `(NULL, 0)` C Buffer vs. Non-Null Rust Slice `&[T]` UB Mismatch:**
   In C, passing `(ptr = NULL, len = 0)` to a function that loops `for (size_t
   i = 0; i < len; i++)` is **100% well-defined** as long as `ptr` is never
   dereferenced (and C23 `N3322` even legalizes `ptr + 0` on `NULL`). When an
   automated C-to-Rust lifter translates `(const uint8_t *ptr, size_t len)` into
   a safe Rust slice parameter `&[u8]` constructed at the FFI boundary via
   `unsafe { core::slice::from_raw_parts(ptr, len) }`, passing `(NULL, 0)`
   triggers **immediate Rust Undefined Behavior** because Rust slice references
   `&[T]` are required to be non-null and aligned (`NonNull::dangling()`) even
   when `len == 0`!

#### 6.4 Architectural Prevention in Anneal's `trusted/` Primitives

Anneal's architecture resolves all three classes of validator and lifter
failures:

1. **Unbounded Inductive Certificates + Kernel-Checked `LRAT`/`Farkas` Instead
   of Bounded SMT (`Alive2`) or Invasive C++ Hooks (`Crellvm`):**
   - Unlike `Alive2`, Anneal never bounds loop iterations in `trusted/`:
     `EventualBehaviorOf` quantifies over **all** step counts $n \in \mathbb{N}$
     (`∃ n` for `.terminated`, `∀ n` for `.diverges`). Loop optimizations
     (`LICM`, `LoopUnroll`, `PolyhedralScheduleValidator`, `IVSR`) supply
     unbounded inductive loop invariants or Farkas affine schedule certificates
     checked in `theory/`.
   - Unlike `Crellvm`, Anneal does not instrument C++ passes with fragile step
     hooks: external solvers and optimizers emit compact, pass-agnostic boundary
     certificates (`Mem2RegCert`, `GVNCert`, `PolyhedralCert`, `LRAT`, `Alethe`)
     checked by total, `native_decide`-free Lean 4 validators in `theory/`. Any
     instruction or loop where an external tool times out or cannot produce a
     certificate is either left unoptimized (backed by `NaiveCodegen`) or
     surfaced as a positive per-obligation entry in `VerificationResult`.
2. **Blocking C-to-Rust Vacuity and `(NULL, 0)` Slice UB via Proof-Gated
   Compilation (`InhabitedPre ∧ ProductiveOn ∧ Compiles`):**
   - Requiring `InhabitedPre cPre ∧ L_Clight.ProductiveOn cPre f_c ∧ Compiles
     L_Clight L_MIR cToRustCodec f_c f_rust` mandates a proof that `cPre` is
     non-empty and that the C source `f_c` is **genuinely UB-free and
     productive** on every query satisfying `cPre` (`c2rust_vacuous_c_ub_blocked_by_productiveOn`
     in `support/MidLevelIrFailureCanaries.lean`).
   - Furthermore, `cToRustCodec.encodeQuery` maps C `(ptr, len)` inputs into
     `MirState`, where constructing `&[T]` with `ptr == 0` and `len == 0` fails
     `MirMachine`'s slice non-null validity guard (`.failed .ub`), immediately
     refuting `Compiles` unless `cPre` excludes `ptr == NULL` or the wrapper
     substitutes `NonNull::dangling()` when `len == 0`
     (`c2rust_null_zero_len_slice_violates_compiles` in
     `support/MidLevelIrFailureCanaries.lean`).

---

### Finding 7: Cross-Cutting Architectural Synthesis: How Anneal's Four `trusted/` Primitives Prevent All Fifteen Historical Failure Classes

`Basis: source + execution + derived`

#### 7.1 Master Failure Postmortem and Prevention Matrix

Across all fifteen historical failure classes examined in Findings 1–6, every
miscompilation or verification failure traces back to violating one or more of
four semantic invariants that Anneal enforces directly in `trusted/lean/`:

1. **`Language SemObs` + `BehaviorCodec` + `Compiles` / `Abstracts`
   (`Trusted/Refinement.lean`):** Enforces a reflexive, transitive partial-behavior
   refinement preorder `L₂.sem t ≤ codec.toMorphism (L₁.sem s)` with partial
   bijective outcome decoding (`decodeOut_encodeOut`, `encodeOut_decodeOut`,
   `obs_decodeOut`).
2. **`ProductiveOn` + `InhabitedPre` (`Trusted/Refinement.lean`):** Enforces
   non-empty input domains (`∃ q, pre q`) and Dijkstra's Law of the Excluded
   Miracle (`∀ q, pre q → ∃ h : defined, ∃ o, val h o`), blocking vacuous
   source-UB refinement and empty-behavior miracles.
3. **`SmallStepMachine` + `EventualBehaviorOf` + `StepResult.externalCall`
   (`Trusted/StepResult.lean`):** Separates finite-trace termination
   (`.terminated trace term`, existential step count `∃ n`) from silent
   divergence (`.diverges`, universal step count `∀ n`) and enforces immediate
   call-site boundary invariants (`boundaryInv : Bool`) and frame/protector
   preservation across opaque calls (`branches : State → Prop`).
4. **Positive Per-Obligation `VerificationResult` (`Trusted/Refinement.lean`):**
   Tracks every pass side-condition, non-trapping guard, layout disjointness
   check, and anti-degeneracy cost/normal-form predicate as an isolated positive
   consequent obligation without antecedent `False.elim` explosion.

| # | Historical Failure Class | Primary Source / Issue | Technical Root Cause | Governing Anneal `trusted/` Primitive(s) | Mechanized Canary in `support/MidLevelIrFailureCanaries.lean` |
| :- | :--- | :--- | :--- | :--- | :--- |
| **1** | `LoopUnswitch` + `GVN` on `undef` / `poison` | Lee et al., PLDI 2017 (`10.1145/3062341.3062343`); LLVM PR21467, PR31632 | Per-use `undef` + branching on unguarded `poison` makes `GVN ∘ LoopUnswitch` non-transitive and introduces UB on 0-trip loops | `Compiles` (`≤ᵇ` transitive preorder) + `Partial.defined` preservation | `loopUnswitch_without_freeze_violates_compiles` (`L165-173`), `loopUnswitch_with_freeze_satisfies_compiles` (`L176-188`) |
| **2** | `select`-to-branch & `InstCombine` poison leaks | Lopes et al., PLDI 2021 (`10.1145/3453483.3454030`) | Lowering `select c, a, b` to `br c` turns value-level `poison` into immediate control-flow UB | `Compiles` (`(L₁.sem s q).defined → (L₂.sem t q).defined`) | `loopUnswitch_without_freeze_violates_compiles` (`L165-173`) |
| **3** | `ptrtoint` / `inttoptr` + `GVN` provenance collapse | Lee et al., OOPSLA 2018 (`10.1145/3276495`); LLVM PR34548, PR35229 | Substituting `p + 1` for `q` under numeric `ip == iq` replaces valid `AllocId(q)` provenance with out-of-bounds `AllocId(p)` | `MirVal.ref (allocId, offset)` provenance separation + `Compiles` | `gvn_provenance_substitution_rejected` (`L213-219`) |
| **4** | `rustc` `mutable-noalias` on `!Unpin` generators / `Future`s | `rust-lang/rust#54878`, `#63818`, `#63934` | Emitting LLVM `noalias` on `Pin<&mut Self>` treats self-referential interior pointers loaded from `*self` as non-aliasing | Post-cleanup MIR capture + `ProductiveOn` pinning precondition + Tree Borrows tags | `coroutine_overlapping_live_fields_rejected` (`L256-265`) |
| **5** | `rustc` MIR `GVN` & `ConstProp` aliasing / partial-move bugs | `rust-lang/rust#110947`, `#118328`, `#120613`, `#141038` | Syntactic place value-numbering reuses moved fields (`#120613`), ignores mutating borrows (`#110947`), or creates overlapping copies (`#141038`) | Operational `MirMachine` state + `Compiles L_MIR L_MIR` | `gvn_provenance_substitution_rejected` (`L213-219`) |
| **6** | Coroutine `StorageLive` / `StorageDead` yield overlap | `rust-lang/rust#63616`, `#146383` (`DestinationPropagation`) | Desynchronized `StorageLive` ranges pack co-live locals into identical union offsets across `Yield` | `Compiles L_CoroutineMIR L_MIR` + cross-yield liveness disjointness check | `coroutine_overlapping_live_fields_rejected` (`L256-265`) |
| **7** | Stacked / Tree Borrows DSE across diverging `externalCall` | Jung et al., POPL 2020; Villani et al., PLDI 2025; `Simuliris` (`e3abfcdc`) | Deleting `*x = 1` before `ext(); *x = 2` is unsound if `ext()` reads an alias and diverges (`loop {}`) under a `Weak` or `Reserved` protector | `StepResult.externalCall` + `EventualOut.diverges` + `Strong` active protector framing | `dse_across_diverging_call_unsound_under_weak_or_unactivated_protector` (`L314-325`), `dse_across_diverging_call_sound_under_strong_active_protector` (`L329-338`) |
| **8** | Forward-progress infinite-loop deletion (`loop {}`) | `rust-lang/rust#28728`, `#81255`, `#83359` (LLVM `mustprogress`) | C++ `[intro.progress]` assumption deletes side-effect-free `loop {}` and falls through into `unreachable` | `EventualBehaviorOf` (`EventualOut.diverges` bidirectional preservation) + `ProductiveOn` | `infinite_loop_deletion_violates_compiles` (`L359-368`) |
| **9** | `LICM` / `PRE` hoisting trapping ops above 0-trip or diverging loops | Knoop et al. (`PRE`); `Chamois-CompCert` (`BTL`); Sub-Domain 3.6 & 3.13 | Hoisting `a / d` into a preheader introduces a panic/trap when the loop takes 0 iterations or diverges before `a / d` | `EventualOut` (`Terminal.panic` vs. `.normal` vs. `.diverges`) + `Compiles` | `licm_hoisting_trapping_div_above_zero_trip_or_diverging_loop_rejected` (`L390-399`) |
| **10** | Briggs/Boissinot `Swap` and `Lost-Copy` out-of-SSA bugs | Briggs et al., SPE 1998; Rideau et al., JAR 2008; Boissinot et al., CGO 2009 | Naive sequentialization of $\phi$-cycles (`a := b; b := a`) or unsplit critical edges overwrites live registers | `Compiles L_AnSSA L_MIR` + `EventualBehaviorOf` ($1 \to k+1$ step dilation) | `naive_ssa_swap_lowering_violates_compiles` (`L429-438`), `temp_ssa_swap_lowering_satisfies_compiles` (`L441-446`) |
| **11** | Tail-call elimination (`TCO`) stack-local address escape | LLVM `TailRecursionElimination.cpp` (`AllocaDerivedValueTracker`) | Reusing caller stack frame when `&local` or `byval` escapes to tail callee causes dangling stack dereference | `MirMachine` frame deallocation (`StorageDead`) before `TailCall` + `Compiles` | `tail_call_with_escaping_stack_ref_violates_compiles` (`L463-469`) |
| **12** | `ElaborateDrops` unwind double-drop & `#24292` Leakpocalypse | `rust-lang/rust#24292` (`Vec::drain`, `JoinGuard`); MIR `ElaborateDrops` | Clearing `drop_flag` after `Drop::drop` double-frees on panic unwind; leaking `Drain` leaves stale `Vec::len` | `MirMachine` drop-flag state + `StepResult.externalCall` `AdtInv` check | `drop_elaboration_clear_after_drop_double_frees_on_unwind` (`L489-495`) |
| **13** | `Alive2` bounded unrolling (`-tv-unroll=k`) & SMT timeouts | Lopes et al., PLDI 2021 (`10.1145/3453483.3454030`) | Bounded loop unrolling misses bugs at iteration $k+1$; monolithic `QF_ABV`/`QF_FPBV` queries time out | Unbounded `EventualBehaviorOf` (`∀ n` / `∃ n`) + kernel-checked `Farkas`/`LRAT` certificates | `Behavior.Refines.trans` (`L49-56`) |
| **14** | `Crellvm` proof-hint fragility & `Vellvm` pass-coverage gap | Kang et al., PLDI 2018 (`10.1145/3192366.3192398`); Zakowski et al., ICFP 2021 (`10.1145/3473572`) | Invasive C++ pass instrumentation breaks on LLVM upgrades; monadic `ITree` proofs require rewriting passes in Rocq | Pass-agnostic boundary certificates checked in `theory/` + `VerificationResult` | `BehaviorCodec.toMorphism` (`L84-92`) |
| **15** | `C2Rust` / `CROWN` C-UB vacuity & `(NULL, 0)` slice UB | Zhang et al., CAV 2023 (`10.1007/978-3-031-37709-9_22`) | Source C UB makes `Compiles` hold vacuously; translating valid C `(NULL, 0)` to `slice::from_raw_parts(null(), 0)` introduces Rust UB | `InhabitedPre ∧ ProductiveOn ∧ Compiles` + `cToRustCodec` non-null slice guard | `c2rust_vacuous_c_ub_blocked_by_productiveOn` (`L515-520`), `c2rust_null_zero_len_slice_violates_compiles` (`L551-559`) |

## Boundaries

To prevent future agents from over-generalizing these findings, the following
scope boundaries apply:

- **Not examined — Hardware relaxed-memory concurrency interactions with
  mid-level scalar passes:** While Finding 3 analyzes sequential and re-entrant
  call-boundary protectors (`Stacked Borrows` / `Tree Borrows`), the interaction
  between mid-level load/store motion and weak hardware memory models (`C11`
  `Relaxed`/`Release`/`Acquire`, `x86-TSO` store buffers, and `AArch64`/`RVWMO`
  out-of-order execution) is **not examined** in this package; it is covered in
  `anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal-2026`.
- **Not examined — Low-level target-ISA peephole, instruction-selection, and
  ELF linker failures:** Failures specific to `x86-64`/`AArch64`/`RISC-V`
  condition-code fusion (`OF`/`CF`), register-allocator spill slot packing, and
  ELF relocation relaxation belong to Sub-Domain 4 and are **not examined** here.
- **Known not to apply — Symmetric equivalence (`=`) for borrow-aware and
  undef/poison-refining optimizations:** As established in Findings 1, 2, and 3
  (and Sub-Domain 3.10 and 3.17), optimizations such as `mem2reg` uninitialized-read
  refinement, Tree Borrows redundant-read elimination, and function inlining
  (which drops Function-Entry Protectors) make the target program strictly
  **more defined** than the source program (`L₂.sem t ≤ L₁.sem s` with strict
  inequality). Symmetric behavioral equivalence (`L₂.sem t = L₁.sem s`) is
  **known not to apply** to these passes; `Compiles` must remain an asymmetric
  refinement preorder (`≤`).
- **Unsupported — Uninstrumented translation validation of arbitrary C++ LLVM
  `-O3` loop passes without inductive invariants:** Neither `Alive2` (which is
  bounded at `-tv-unroll=k`) nor Anneal's certifying validators can validate an
  arbitrary loop-transforming pass without an inductive loop/schedule witness
  (`LICMCert`, `PolyhedralCert`, or `IVSR` recurrence invariant). When an
  external optimizer does not supply a valid certificate, unverified pass output
  is **unsupported** as a silent TCB step and must be either rejected (falling
  back to `NaiveCodegen`) or surfaced explicitly in `VerificationResult`.

## Evidence

### Primary Anneal Repository Sources

- **`joshlf/anneal` (`trusted-core` at `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`):**
  - `trusted/lean/Trusted/Refinement.lean`: Defines `Partial`, `Behavior`,
    `Language`, `BehaviorCodec`, `Compiles`, `ProductiveOn`, and
    `VerificationResultOn`.
  - `trusted/lean/Trusted/StepResult.lean`: Defines `StepResult`, `Terminal`,
    and prefix reachability (`ReachesPrefix`).
  - `trusted/lean/Trusted/MirSemantics.lean`: Defines `MirVal`, `MirState`,
    `MirSem`, and `EnsuresRetLibInv`.
- **`joshlf/anneal` (`mir-to-x86` at `4f45f0a391a921ced9c9dc773b9a040dbc215d14`):**
  - `trusted/lean/Trusted/X86Semantics.lean`, `trusted/audit/TrustedBoundary.lean`,
    and `trusted/rustc-capture/src/lib.rs`.

### Primary Academic and Technical Sources

1. **Lee, Kim, Song, Hur, Das, Majnemer, Regehr, and Lopes (PLDI 2017):**
   *Taming Undefined Behavior in LLVM*, ACM SIGPLAN Notices 52(6), pp. 633–647,
   DOI `10.1145/3062341.3062343`. Establishes the mutual inconsistency of
   `GVN`, `LoopUnswitch`, and `SROA` under LLVM's pre-`freeze` `undef`/`poison`
   semantics (§§2–3) and formalizes the `freeze` instruction (§4).
2. **Lee, Hur, Jung, Liu, Regehr, and Lopes (OOPSLA 2018):** *Reconciling
   High-Level Optimizations and Low-Level Code in LLVM*, Proc. ACM Program.
   Lang. 2(OOPSLA), Article 125, DOI `10.1145/3276495`. Documents the
   `ptrtoint`/`inttoptr` + `GVN` + `InstCombine` adjacent-allocation provenance
   miscompilation (§2, LLVM PR34548 / PR35229) and formalizes twin-allocation
   memory semantics.
3. **Lopes, Lee, Hur, Liu, and Regehr (PLDI 2021):** *Alive2: Bounded
   Translation Validation for LLVM*, Proc. 42nd ACM SIGPLAN Conf. on
   Programming Language Design and Implementation, pp. 65–79, DOI
   `10.1145/3453483.3454030`. Documents `select`-to-branch poison UB bugs (§2),
   refinement semantics (§5), and bounded loop unrolling limitations (§7).
4. **Jung, Dang, Kang, and Dreyer (POPL 2020):** *Stacked Borrows: An Aliasing
   Model for Rust*, Proc. ACM Program. Lang. 4(POPL), Article 41, DOI
   `10.1145/3371109`. Introduces function-entry protectors for `&mut T` / `&T`
   across unknown calls (§4).
5. **Villani, Hostert, Jung, and Dreyer (PLDI 2025):** *Tree Borrows*, Proc. ACM
   Program. Lang. 9(PLDI), DOI `10.1145/3735592`, paired with the `Simuliris`
   mechanization (`https://gitlab.mpi-sws.org/iris/simuliris` at
   `e3abfcdc301f92250d4227fc03c00463bf57b982`). Establishes the distinction
   between `Strong` and `Weak` function-entry protectors and the soundness
   requirements for Dead Store Elimination across diverging external calls.
6. **Briggs, Cooper, Harvey, and Simpson (SPE 1998):** *Practical Improvements
   to the Construction and Destruction of Static Single Assignment Form*,
   Software: Practice and Experience 28(8), pp. 859–881, DOI
   `10.1002/(SICI)1097-024X(199807)28:8<859::AID-SPE175>3.0.CO;2-Z`. Identifies
   and names the `Lost-Copy` and `Swap` bugs in Cytron et al.'s out-of-SSA
   translation.
7. **Rideau, Serpette, and Leroy (JAR 2008):** *Tilting at Windmills with Coq:
   Formal Verification of a Compilation Algorithm for Parallel Moves*, Journal
   of Automated Reasoning 40(4), pp. 307–326, DOI `10.1007/s10817-008-9097-3`.
   Mechanizes the cycle-breaking parallel-move sequentialization algorithm used
   in CompCert.
8. **Boissinot, Darte, Dupont de Dinechin, Guillon, and Rastello (CGO 2009):**
   *Revisiting Out-of-SSA Translation for Correctness, Code Quality, and
   Efficiency*, Proc. 7th IEEE/ACM Int. Symp. on Code Generation and
   Optimization, pp. 114–125, DOI `10.1109/CGO.2009.19`. Proves that general
   coalescing during SSA destruction requires splitting critical edges and
   sequentializing parallel copies via dependency graphs.
9. **Kang et al. (PLDI 2018):** *Crellvm: Verified Credible Compilation for
   LLVM*, Proc. 39th ACM SIGPLAN Conf. on Programming Language Design and
   Implementation, pp. 631–645, DOI `10.1145/3192366.3192398`.
10. **Zakowski et al. (ICFP 2021):** *Modular, Compositional, and Executable
    Formal Semantics for LLVM IR* (`Vellvm`), Proc. ACM Program. Lang. 5(ICFP),
    Article 67, DOI `10.1145/3473572`.
11. **Zhang, David, Yu, and Wang (CAV 2023):** *Ownership Guided C to Rust
    Translation* (`CROWN`), LNCS 13965, pp. 459–482, DOI
    `10.1007/978-3-031-37709-9_22`.
12. **Upstream `rust-lang/rust` Issue Archive:**
    - `#24292` (*std::thread::scoped / JoinGuard and Vec::drain unsoundness when
      Drop is bypassed*);
    - `#28728`, `#81255`, `#83359` (*LLVM forward-progress infinite loop
      miscompilation and `mustprogress` / `willreturn` mitigation*);
    - `#54878`, `#63818`, `#63934` (*`noalias` miscompilations on `&mut` and
      self-referential generators / `Future`s*);
    - `#63616` (*partial initialization and storage-conflict overlap in
      generators*);
    - `#110947`, `#118328` (*MIR `ConstProp` miscompilations across mutating
      borrows and pointer-typed enum fields*);
    - `#120613`, `#141038` (*MIR `GVN` reuse of moved arguments and overlapping
      aliased assignments*); and
    - `#146383` (*MIR `DestinationPropagation` copy/lifetime miscompilation*).

### Preserved Package Artifacts

- [`support/MidLevelIrFailureCanaries.lean`](support/MidLevelIrFailureCanaries.lean):
  561-line standalone Lean 4.34.1 file mechanizing 13 zero-axiom failure-refutation
  and repair-conformance theorems across Findings 1–6 (observed and verified on
  2026-10-31).

## Revalidation

1. **Executable Lean 4.34.1 Kernel Revalidation (< 2 seconds):**
   Run the Lean 4 kernel checker with asynchronous elaboration and kernel-skip
   flags disabled on the preserved canary development:
   ```console
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     reports/anneal-mid-level-ir-optimizations-lowering-verification-failures-2026/support/MidLevelIrFailureCanaries.lean
   ```
   A zero exit code confirms that all 13 refutation and conformance theorems
   (`loopUnswitch_without_freeze_violates_compiles` through
   `c2rust_null_zero_len_slice_violates_compiles`) typecheck in the Lean 4
   kernel with zero axioms.
2. **Revalidating Against Future Changes to Anneal's `trusted/lean/` Primitives:**
   When `Trusted/Refinement.lean`, `Trusted/StepResult.lean`, or
   `Trusted/MirSemantics.lean` is modified, verify that:
   - `Compiles` still enforces `(L₁.sem s q₁).defined → (L₂.sem t (codec.encodeQuery q₁)).defined`
     and `decodeOut` outcome inclusion (Canaries 1a, 2, 3, 6a, 7a, 7b, 8b);
   - `EventualOut` still distinguishes `.diverges`, `.terminated trace (.normal v)`,
     `.terminated trace (.panic msg)`, and `.terminated trace .abort` in `SemObs`
     (Canaries 4a, 5a, 5b); and
   - `ProductiveOn` still requires `∃ h : (L.sem prog q).defined, ∃ o, (L.sem prog q).val h o`
     (Canary 8a).
