# Memory exhaustion as an observable: Jinja's OutOfMemory, unbounded and finite memory models, allocation elision in C/C++/Rust/LLVM, WebAssembly growth failure, and Linux overcommit

## Summary

- **Running out of memory has no common semantic status.** The primary sources examined here use six distinct representations, and each licenses different allocation-changing optimizations:
  1. **In-language, deterministic outcome (Jinja).** `new` throws a preallocated `OutOfMemory` object when `new_Addr h = None`.
     - Source, JVM, and compiler theorem share one heap and one deterministic address chooser (least free address). The compiler theorem can therefore only relate runs in which exhaustion happens at the same allocation.
     - Because `addr = nat`, `new_Addr` never fails on a heap with finitely many objects, so the rule is unreachable from the standard start heap.
  2. **Outside the model.**
     - CompCert's `Mem.alloc` "never fails: we are modeling an infinite memory".
     - In WebAssembly, struct and array allocation and call depth have no failure rule. Exceeding a runtime limit lets an implementation "terminate that computation and report an implementation-specific error".
  3. **Exhaustion as "no behaviour", plus partial behaviours.** Kang et al. (PLDI 2015), following CompCertTSO, model out-of-memory as the empty behaviour set while keeping the I/O prefix. Their source can also run out of memory, at pointer-to-integer casts.
     - MiniRust's demonic address choice also turns exhaustion into "no behavior", and its source flags this as "not what we want".
  4. **One-sided target escape.**
     - CakeML's theorem places machine behaviours in `extend_with_resource_limit` of the source behaviours: early `Resource_limit_hit` after any I/O prefix. The escape disappears only under a safe-for-space side condition.
     - CompCertS's finite memory, conversely, proves the assembly "consumes no more memory than the source code does".
  5. **Implementation-chosen (angelic) non-determinism.**
     - WebAssembly `memory.grow` has an unconditional fail rule that returns −1.
     - LLVM `allockind` permits a "virtual, side-effect-free allocator".
     - Rust's global-allocator contract lets allocations "non-deterministically entirely skip the underlying allocator".
     - C++ `[expr.new]` (from WG21 N3664) lets implementations omit or merge allocations.
  6. **Asynchronous at any point.** The JVM specification "cannot predict where … resource limitations may be encountered", so `VirtualMachineError` subclasses "may be thrown at any time".

  (Basis: source + normative + documentation.)
- **Allocation elision turns exhaustion into completion on real toolchains.** Measured on one x86-64 Linux host, with a 1 PiB request, which must fail under 4-level paging:
  - **C:** GCC 15.2 at `-O0` has `malloc` return NULL (exit 1). At `-O2` the `malloc`/`free` pair is deleted and the null test folds to "succeeded" (exit 0).
  - **C++:** `g++` behaves the same way for `new char[2^50]`: `std::bad_alloc` at `-O0`, completion at `-O2`.
  - **Rust:** with rustc 1.102.0-nightly (LLVM 23.1.5), an unused `Vec::with_capacity(2^50)` aborts with exit 134 at `opt-level=0` and completes at `opt-level=3`. Observing the allocation with `black_box` restores the abort, and `try_reserve` reported `Err` at both levels.
  - LLVM implements this by folding `icmp eq p, null` to `false` (`InstructionCombining.cpp:3787`, `:4000`).
  - ISO C has no counterpart to `[expr.new]`'s permission: C11 §7.22.3p1 says "If the space cannot be allocated, a null pointer is returned". Kang et al. note that this semantics "does not justify dead allocation eliminations". Lee et al. (OOPSLA 2018) state that in their LLVM model "any transformation that may eliminate an out-of-memory condition is unsound", although LLVM performs such transformations routinely.

  (Basis: execution + normative + source + documentation.)
- **Under Linux overcommit, failure moves away from the allocation site.**
  - With `vm.overcommit_memory=0`, a single anonymous mapping is refused only if `pages > totalram_pages() + total_swap_pages` (`mm/util.c:985–988`). The measured boundary matches to 1 MiB: 309222 MiB succeeds and 309223 MiB fails, against MemTotal+SwapTotal = 309222.44 MiB.
  - The heuristic is per request: three untouched 200000 MiB reservations succeed in one process.
  - `RLIMIT_AS`, which is cumulative per process (`mm/mmap.c:1351`), surfaces failure at the call as NULL/ENOMEM.
  - A cgroup v2 `memory.max` of 64 MiB lets `malloc(256 MiB)` succeed. The process is then SIGKILLed while touching pages (exit 137, last progress line at 48 MiB).

  (Basis: source + documentation + execution.)
- **Practical consequence.** A compiler or interoperability theorem that treats exhaustion as observable has to choose a representation explicitly.
  - Dead-allocation removal is sound without side conditions only under "outside the model", the one-sided target escape, angelic choice, or "no behaviour".
  - Under the deterministic in-language representation (Jinja) or a finite memory with C11's NULL guarantee, removal changes observable behaviour unless the theorem pads or ignores the difference.
  - Under CompCertS-style "target uses no more memory", removal is fine, but passes that add memory (spilling) need provisioning in the source semantics.

  (Basis: derived; see Findings §9.)

## Applicability

- **What this report covers.** The *semantic status of memory exhaustion*: whether it is a behaviour, undefined, non-deterministic, or outside the model, where it can surface, and which allocation-changing transformations each choice licenses. It does this for:
  - mechanised languages and compilers: Jinja (Isabelle AFP), CompCert, CakeML, MiniRust, WasmCert-Isabelle;
  - finite C and IR memory models from the literature: Kang et al. 2015, Lee et al. 2018, CompCertS;
  - language standards and library contracts: ISO C (N1570), C++ `[expr.new]`, Rust `GlobalAlloc`, LLVM LangRef, JLS/JVMS, WebAssembly;
  - one operating system: Linux overcommit, cgroup v2, and `RLIMIT_AS`.
- **How the subjects relate.** They are *compared*. The repositories are pinned to the exact revisions listed in `REPORT.json`, and statements about them are about those revisions.
- **Toolchain probes.** These ran on one x86-64 host:
  - Linux 7.1.6, a Debian-derived distribution kernel build;
  - `MemTotal` 247,581,128 kB and `SwapTotal` 69,062,648 kB;
  - `vm.overcommit_memory=0`, `overcommit_ratio=50`, `RLIMIT_AS` unlimited;
  - GCC 15.2.0 (Debian 15.2.0-14);
  - rustc 1.102.0-nightly, commit `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, with LLVM 23.1.5.
- **Limits of the probe results.**
  - They are properties of those toolchain builds at those flags. They are not claims about other versions, other optimisation pipelines, or the language standards.
  - The kernel probe exercises the distribution kernel, not the mainline source revision pinned for `mm/util.c`. Agreement between the measured boundary and the mainline `OVERCOMMIT_GUESS` branch is evidence that the branch is unchanged in that build, not proof.
- **WebAssembly runtimes were not executed.** WebAssembly claims are normative and mechanisation claims only.
- **Versions of the papers read.**
  - Klein–Nipkow: the NICTA technical report 0400001T.1 (March 2004), whose compiler theorem is Theorem 5.4. Page numbers differ from TOPLAS 28(4).
  - CompCertS: the author PDF.
  - All other papers: their published layouts.
  - The C++ `[expr.new]` wording is the working draft as rendered at eel.is on 2026-11-21. The draft revision identifier was not recorded.

## Findings

### 1. Taxonomy of representations

| System (revision or version) | Can allocation fail? | Representation of exhaustion | Where it surfaces | Refinement treatment | Basis |
|---|---|---|---|---|---|
| Jinja (AFP mirror `523cdc72…`) | only when every `nat` address is used | `THROW OutOfMemory` (preallocated object), deterministic | at `new` / `New` | identical heap on both sides, so synchronised | source |
| CompCert (`2685140b…`) | no | absent ("infinite memory") | never | memory injections or extensions; exhaustion not stated | source + documentation |
| Kang et al. 2015 | at pointer-to-integer cast (no concrete space left) | no behaviour, plus partial behaviours (I/O prefix kept) | at cast | target ⊆ source, partial behaviours included | documentation |
| Lee et al. 2018 (LLVM model) | yes (finite memory, twin blocks) | OOM outcome; "malloc either returns a NULL pointer, or a logical pointer" (Thm C.2) | at allocation | eliminating an OOM condition is unsound (§8) | documentation |
| CompCertS (JAR) | yes | allocation fails when no concrete memory can be built | at allocation | "if the source code does not exhaust the memory, then neither does the assembly code" | documentation |
| MiniRust (`063d7841…`) | yes (finite address space) | demonic choice, so exhaustion is "no behavior" (FIXME) | at `allocate` | behaviour inclusion (vacuous on no behaviour) | source |
| CakeML (`2874b664…`) | target only | `Terminate Resource_limit_hit` after any I/O prefix | anywhere in target | `machine_sem ⊆ extend_with_resource_limit' …` | source |
| WebAssembly spec (`6fca7076…`) | `memory.grow` / `table.grow`: always permitted; struct/array: no rule | −1 result; otherwise implementation limit | at `grow`; otherwise anywhere | n/a (spec) | normative |
| WasmCert-Isabelle (`d9b4659c…`) | relational: always permitted; interpreter: only above limits | −1; interpreter `Res_crash (Error_exhaustion …)` for call depth | at `grow`; call depth | soundness theorems cover only value and trap results | source |
| ISO C (N1570 §7.22.3) | yes | `malloc` returns NULL | at call | n/a | normative |
| C++ `[expr.new]` | yes (`bad_alloc` or null) | calls may be omitted or merged | at new-expression, if not omitted | n/a | normative |
| Rust `GlobalAlloc` (`c7d5ba59…`) | yes (null) | allocation may be skipped; optimizer "may further assume that allocation is infallible"; `handle_alloc_error` diverges | at call, if not skipped | "Whether allocations happen or not is not part of the program behavior" | documentation + source |
| LLVM LangRef (`04e0e9cc…`) | yes | non-deterministic choice of a "virtual" allocator | at call, if not elided | n/a; InstCombine folds null tests | normative + source |
| JLS/JVMS (Java SE 27) | yes | `OutOfMemoryError`, synchronous or asynchronous | "at any time" | n/a | normative |
| Linux (`84afebd8…`; probes on a 7.1.6 distribution kernel) | depends on mode and limits | ENOMEM at call, or OOM kill at touch | call, first touch, or kill | n/a | source + documentation + execution |

### 2. Jinja: a deterministic, heap-determined exception shared by source, VM, and compiler

Basis: source (`isabelle-prover/mirror-afp-devel` at `523cdc72b5ae4a91c9ab8e1025d4a30b40472720`, under `thys/Jinja/`) + documentation (Klein–Nipkow technical report).

- **Addresses and the chooser.** `Common/Value.thy:10` declares `type_synonym addr = nat`, and `Common/Objects.thy:36` declares `heap = "addr ⇀ obj"`. The chooser is defined at `Common/Objects.thy:44`:
  ```text
  new_Addr h ≡ if ∃a. h a = None then Some(LEAST a. h a = None) else None
  ```
  It is a *function* of the heap (the least free address), not a non-deterministic choice. The paper omits the definition, saying only that it "returns a 'new' address, i.e. new-Addr h = ⌊a⌋ implies h a = None" (§2.2).
- **Preallocated exception object.** `Common/Exceptions.thy:19–25` makes `OutOfMemory` one of three system exceptions. `start_heap` (lines 33–37) places it at address 2, and `preallocated h` (lines 39–41) requires it to exist, so throwing it never allocates. The paper: "we can simplify their treatment by pre-allocating one object for each system exception class".
- **Failure rules in every layer.** Each layer has the same premise, `new_Addr h = None`:
  - `J/BigStep.thy:23–25`: `NewFail`, `⟨new C,(h,l)⟩ ⇒ ⟨THROW OutOfMemory,(h,l)⟩`;
  - `J/SmallStep.thy:47–49`: `RedNewFail`;
  - `Compiler/J1.thy:51–53`: `NewFail₁`;
  - `JVM/JVMExecInstr.thy`, `exec_instr_New`: `case new_Addr h of None ⇒ (Some (addr_of_sys_xcpt OutOfMemory), h, …)`.
- **Compiler theorem.** `Compiler/Compiler.thy:17–22`, `comp_correct` (paper Theorem 5.4):
  ```text
  assumes wwf_J_prog P, P ⊢ C sees M:Ts→T = (pns,body) in C,
          P ⊢ ⟨body,(h,[this#pns [↦] vs])⟩ ⇒ ⟨e',(h',l')⟩, size vs = size pns + 1, size rest = max_vars body
  shows   J2JVM P ⊢ (None,h,[([],vs@rest,C,M,0)]) -jvm→ (exception e',h',[])
  ```
  - This is a forward simulation of *terminating big-step evaluations* from the **same initial heap `h`** to the **same final heap `h'`**. The paper says "The initial JVM state contains the same heap".
  - The stage lemmas discharge `NewFail` directly: `Correctness1.thy:316` and `Correctness2.thy:408`.
- **Derived consequences.**
  1. **Exhaustion is synchronised.** The heaps are identical and `new_Addr` is deterministic, so a compiled `New` fails exactly when the source `new` fails.
  2. **Non-terminating source runs are not covered.** The theorem speaks only of runs that reach a final expression.
  3. **`OutOfMemory` is unreachable from `start_heap`:**
     - `start_heap` has a 3-element domain, and each `New` adds one address, so every heap reachable in finitely many steps is finite;
     - `nat` is infinite, so `∃a. h a = None` always holds;
     - `NewFail` therefore needs an initial heap whose domain is all of `nat`. Such heaps are admissible arguments to the theorems, but no finite run creates one.
  4. **No allocation-changing optimization is verified.** A pass that removed a dead `new` would shift later least-free addresses and would not fit the identical-heap statement.
- **Size at the pinned revision.** `thys/Jinja/` has 72 `.thy` files, 878,265 bytes, and 20,099 lines; `Correctness1.thy` has 761 lines and `Correctness2.thy` 1,145 lines. (Basis: execution, `wc` on fetched files.)

### 3. Unbounded-block memory: CompCert and Leroy–Blazy

Basis: source (`AbsInt/CompCert` at `2685140bf72c959446981fb99b5e44a8975021bc`) + documentation (Leroy–Blazy, JAR 41(1) 2008).

- **Source.**
  - `common/Memtype.v:99–101`: "Note that [alloc] never fails: we are modeling an infinite memory. *) Parameter alloc: forall (m: mem) (lo hi: Z), mem * block." The result type has no failure case.
  - `common/Memory.v:343–357` returns `m.(nextblock)` and increments it with `Pos.succ`. Identifiers are `positive`, so the supply is unbounded.
- **Paper, §4, p. 9.** "An unspecified, boolean-valued can_allocate function is used to model the possibility of failure if the request (h − l bytes) exceeds the available memory. In the Compcert development, can_allocate always returns true, therefore modeling an infinite memory."
- **Paper, §5, pp. 11–13.** "three passes of the Compcert compiler change the memory behavior of the program":
  - Clight→Cminor uses memory injections. Scalar locals whose address is never taken are "pulled out of memory", and the remaining locals are "grouped as sub-areas of a single memory block": blocks are removed and merged.
  - Register allocation refines stored values.
  - Spilling uses memory extensions: the stack frame "is extended to make room for storing spilled temporaries", so a block is enlarged.
- **Derived.**
  - All three memory-changing passes are sound partly *because* `can_allocate` is constantly true.
  - Under a finite source memory with observable failure, the spilling pass, which adds memory, is the one that breaks. CompCertS confronts exactly this (§4.3).

### 4. Finite memory models

#### 4.1 Kang et al. 2015: the quasi-concrete model; exhaustion is "no behavior" and can occur in the source at casts

Basis: documentation (PLDI 2015, pp. 326–335).

- **How OOM behaviours are handled** (§2.3, pp. 3–4):
  - "we should allow the target program to run out of memory even if the source program does not, because important compiler transformations such as register allocation may increase the program's memory requirements."
  - "the target behavior of a source program running out of memory should not be arbitrary, but should match the source behavior and also run out of memory. Therefore, CompCertTSO models out of memory as the empty set of behaviors, that is no behavior."
  - Because "Discarding I/O events before running out of memory is absurd", partial behaviours "e1, ···, en, partial" are observed.
  - "refinement is defined as inclusion of the set of (possibly partial) behaviors of the target program into that of the source program … unlike CompCertTSO, where only the target language can run out of memory, our source language can also run out of memory due to pointer-to-integer casts."
- **Where exhaustion can arise** (§3.2, pp. 4–5): "allocate all blocks as logical blocks, and assign concrete addresses to logical blocks at casting time. This casting can result in out of memory only when there is not enough free concrete space."
- **Dead allocations.**
  - The infinite logical model "renders their allocation behavior unobservable, which in turn makes it easy for compilers to remove dead allocations" (§2).
  - Footnote 2: under C11's NULL-on-failure `malloc`, "this semantics does not justify dead allocation eliminations … a subsequent allocation may return 0 in the source but return a valid pointer in the target".
  - In the fully concrete model "allocations of dead blocks cannot be removed". Dead casts combined with dead blocks are removed during the lowering from the quasi-concrete to the concrete model.
- **Refinement asymmetry** (§5.2). A source block that is concrete while the corresponding target block is logical is disallowed, because "a pointer-to-integer cast may raise out-of-memory in the source but succeed in the target".
- **Mechanisation.** "about 10,000 lines" of Coq (p. 9). Two compilers were verified: an identity compiler, and quasi-concrete→concrete lowering removing dead casts (§6.6).

#### 4.2 Lee et al. 2018: twin allocation in a finite LLVM memory model; removing OOM is unsound

Basis: documentation (PACMPL 2(OOPSLA), article 125).

- **Why non-determinism alone is not enough.**
  - "when memory is finite, returning a non-deterministic value from allocation functions is not sufficient to prevent programs from guessing addresses" (§3.2).
  - "Memory allocation functions reserve at least two blocks: The block actually observed by the program, and N additional twin blocks. The number N of twin blocks is a parameter of the semantics." (§4).
  - With twin allocation an address-guessing example "would simply run out of memory, and thus the program cannot continue".
- **Result shape** (App. C). Thm C.2: "malloc either returns a NULL pointer, or a logical pointer". Thm C.3: execution from twin states "halts, triggers UB or OOM, or … is successful".
- **Stated limitation** (§8 "Discussion and Future Work", p. 125:24):
  > "Out of memory. A technical problem with our memory model is that any transformation that may eliminate an out-of-memory condition is unsound. However, the necessary conditions for achieving miscompilation via this unsoundness are difficult to meet. First, the compiler must perform a transformation based on knowledge that a program path triggers out-of-memory (LLVM does not do this at present …). Second, it would need to perform an optimization eliminating the out-of-memory condition (these transformations, such as eliminating unused allocations, are performed routinely)."
- **Measured cost of the prototype** (§6.2).
  - SPEC CPU 2017: "a 0.2% slowdown", worst "a 1.75% regression in xalancbmk".
  - LLVM Nightly Tests: worst slowdown 4.3%, best speedup 4.0%, "On average … a 0.3% slowdown".
  - "only 25% (464/1853) of object files were different".
  - [cited]

#### 4.3 CompCertS: finite memory, allocation fails, memory use must not grow, and provisioning in the source semantics

Basis: documentation (Besson, Blazy, Wilke, JAR; author PDF).

- **Abstract.** "unlike CompCert, allocation may fail if no memory is available".
- **§6.**
  - "Our memory model is finite and the memory allocation fails when no more memory is available … It ensures that if the source code does not exhaust the memory, then neither does the assembly code. In other words, the compilation ensures that the assembly code consumes no more memory than the source code does."
  - Of the three passes that change stack usage, SimplLocals and Cminorgen reduce it, while Stacking "is responsible for an increase of the memory usage" (return address, spills, callee-saves, outgoing arguments).
- **The fix (§6.2.1) is padding in the source semantics.** "we parameterise the semantics of all intermediate languages, from C to Linear, with an oracle ns which specifies, for each function f, the additional space that is needed. The semantics therefore include special operations that reserve some space at function entry and release it at function exit."
- **Derived.**
  - CompCertS makes exhaustion observable in the *source*. It then charges the source, per function and through an oracle, what the target will need.
  - This is the "charge in the source what the target charges" resolution. The cost is a source semantics that depends on a compiler-supplied oracle.

#### 4.4 MiniRust: finite address space, demonic address choice, exhaustion as "no behavior"

Basis: source (`minirust/minirust` at `063d784186d3252bee242217f218223205c0b568`, `spec/mem/basic.md`).

- **Rejection of oversized requests.** `allocate` rejects sizes that do not fit `isize` with `throw_ub!("asking for a too large allocation")` (line 102). It then picks an aligned, in-bounds base address in `1 .. 2^PTR_SIZE.bits()` that does not overlap any live allocation.
- **The FIXME** (lines 104–107): "Pick a base address. We use daemonic non-deterministic choice, meaning the program has to cope with every possible choice. FIXME: This makes OOM (when there is no possible choice) into "no behavior", which is not what we want."
- **Open question noted in the file.** Line 6 anticipates "extra tricks to explain OOM-reducing optimizations" and links an open Unsafe Code Guidelines discussion titled "Removing allocations is technically unsound in OOM (out-of-memory) situations".
- **Derived.** Under behaviour-inclusion refinement, a program with no behaviour is refined by anything. Without Kang et al.'s partial behaviours it is also refined *into* anything that also exhausts: a target with no behaviour refines every source, so introducing exhaustion becomes vacuously "sound".

#### 4.5 CakeML: a target-only resource escape, removed by a safe-for-space side condition

Basis: source (`CakeML/cakeml` at `2874b664e10939a3ee462215b2e068c89c1f70eb`) + documentation (Tan et al., JFP 29 e2, preprint).

- **Definition.** `semantics/proofs/semanticsPropsScript.sml:219–226`:
  ```text
  extend_with_resource_limit behaviours =
    behaviours ∪
    { Terminate Resource_limit_hit io_list | io_list | ∃t l. Terminate t l ∈ behaviours ∧ io_list ≼ l } ∪
    { Terminate Resource_limit_hit io_list | io_list | ∃ll. Diverge ll ∈ behaviours ∧ LPREFIX (fromList io_list) ll }
  ```
  `extend_with_resource_limit' precise b = if precise then b else …` (lines 228–232).
- **Top-level theorem.** `compiler/proofs/compilerProofScript.sml:201–222` (`compile_correct_gen`): `machine_sem mc … ms ⊆ extend_with_resource_limit' (∀po. is_safe_for_space … (read_limits cc mc ms)) (semantics_prog …)`.
- **The authors on its weakness** (JFP §2.3): "A trivial compiler that always produces code that runs out of memory would satisfy this kind of theorem. However, it is hard to prove anything stronger when compiling to a machine with finite memory, without exposing unwanted implementation details in the source semantics."
- **Related finite-stack work.** Carbonneaux et al. (PLDI 2014, §3.2): "in CompCert, allocating a stack frame always succeeds, thus CompCert does not model stack overflow". They prove that an execution with bounded stack "is a refinement of the execution … in the semantics with unbounded stack", for stack sizes at least a verified bound.

### 5. Language standards and library contracts

#### 5.1 ISO C

Basis: normative (WG14 N1570, C11 committee draft, 2011-04-12).

- §7.22.3p1: "If the space cannot be allocated, a null pointer is returned."
- §7.22.3.4p3: "The malloc function returns either a null pointer or a pointer to the allocated space."
- N1570 has no clause permitting an implementation to omit a call.
- **Derived.** Read strictly, a conforming `malloc(2^50)` on a 47-bit user address space must return NULL. GCC's `-O2` result in probe E1 below relies on treating `malloc` as a builtin whose result need not reflect real availability. That is the gap Kang et al.'s footnote 2 identifies.

#### 5.2 C++ `[expr.new]`: omission and merging, from N3664

Basis: normative.

- **N3664** (Crowl, Carruth, Smith, 2013-04-19) added: "An implementation is allowed to omit a call to a replaceable global allocation function … When it does so, the storage is instead provided by the implementation or provided by extending the allocation of another new-expression." Its rationale: "the number of allocation calls is not part of the observable behavior of the program", and "the amount of space allocated does not increase peak allocation".
- **Current working draft** (eel.is rendering, observed 2026-11-21):
  - 7.6.2.8/14 is the same omission sentence.
  - /15: "During an evaluation of a constant expression, a call to a replaceable allocation function is always omitted".
  - /16 permits extending `e1` to serve `e2` only if `e1` is sequenced before `e2`, `e2` is evaluated whenever `e1` obtains storage, both use the same replaceable function, both have the same first handler for a throwing function, both pointers reach evaluated delete-expressions, and `e2` is sequenced before `e1`'s delete. Its example `cannot_merge` notes "Merging this allocation would change its catch handler."
  - Note 10: a throwing allocation function "indicates failure to allocate storage by throwing a std::bad_alloc exception". A non-throwing one "returns null to indicate failure".
- **Derived.** The C++ text licenses omitting and merging, constrained so that handlers and lifetimes are unchanged. It does not say whether an *omitted* allocation may fail. Probe E2 shows GCC treats it as succeeding.

#### 5.3 Rust: the global-allocator contract, `handle_alloc_error`, and fallible collection APIs

Basis: documentation (normative for the library contract) + source (`rust-lang/rust` at `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`; `rust-lang/rfcs` at `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`).

- **Skipping and merging.** `library/core/src/alloc/global.rs:99–102`: "Allocation functions may non-deterministically entirely skip the underlying allocator, e.g. if the compiler can show that this allocation can be replaced by a stack variable. The compiler may also merge multiple allocation operations into one, as long as it can also adjust all corresponding deallocation operations accordingly."
- **Infallibility.** Lines 129–134: "The optimizer may detect unused global allocations that it can either eliminate entirely or move to the stack and thus never invoke the global allocator. The optimizer may further assume that allocation is infallible, so code that used to fail due to allocator failures may now suddenly work because the optimizer worked around the need for an allocation."
- **Not program behaviour.** Lines 146–148: "Whether allocations happen or not is not part of the program behavior, even if it could be detected via an allocator that tracks allocations by printing or otherwise having side effects."
- **Null on exhaustion.** Lines 208–215: a null return signals exhaustion or an unsupported layout. "Implementations are encouraged to return null on memory exhaustion rather than aborting, but this is not a strict requirement."
- **`handle_alloc_error`** (`library/alloc/src/alloc.rs:639–669`):
  - It is "guaranteed to diverge".
  - With `std`, the default prints and aborts. The handler at line 700 formats "memory allocation of {size} bytes failed".
  - Without `std` it panics.
  - "Future versions of Rust may panic by default instead."
- **RFC 2116** (`text/2116-alloc-me-maybe.md`):
  - It adds `try_reserve`/`try_reserve_exact`, which return `Result<(), CollectionAllocErr>`, and an `oom=panic` configuration.
  - Its "Overcommit and Killers" section (lines 134–142) says "allocation failure may happen when memory is first *accessed* and not when it's actually requested". It declines to treat that as a reason not to handle failure, because "Windows doesn't do it" and Linux's default fails "obviously" too-large allocations.
- **Derived.**
  - Removable allocations are outside program behaviour, and allocation may be assumed infallible.
  - A failure that does happen diverges, aborting by default.
  - The contract text does not exempt `try_reserve`'s allocation from the "may skip" clause. In probe E3, rustc kept its `Err`.

#### 5.4 LLVM IR: elision as a non-deterministic virtual allocator, implemented by null-folding

Basis: normative (LangRef) + source (`llvm/llvm-project` at `04e0e9cc603537fbc16685f872fba17f937f90ff`).

- **LangRef.** `llvm/docs/LangRef.md:2164–2169` (`allockind`): "Calls to functions annotated with `allockind` are subject to allocation elision: Calls to allocator functions can be removed, and the allocation served from a "virtual" allocator instead. Notably, this is allowed even if the allocator calls have side-effects. In other words, for each allocation there is a non-deterministic choice between calling the allocator as usual, or using a virtual, side-effect-free allocator instead." Lines 2171–2175 restrict this to matching `"alloc-family"` alloc/free pairs.
- **Implementation.** The LangRef text does not say whether the virtual allocator can fail. The implementation treats it as never returning null:
  - `llvm/lib/Transforms/InstCombine/InstructionCombining.cpp:3785–3787` (`isAllocSiteRemovable`): `case Instruction::ICmp: … // We can fold eq/ne comparisons with null to false/true, respectively.`
  - Line 4000 (`visitAllocSite`): `replaceInstUsesWith(*C, ConstantInt::get(C->getType(), C->isFalseWhenEqual()))`.
  - Comparisons on `aligned_alloc` are exempt unless alignment and size are known valid (lines 3796–3798).

#### 5.5 Java: `OutOfMemoryError` may be synchronous or asynchronous

Basis: normative (JLS and JVMS, Java SE 27 editions on docs.oracle.com).

- **JLS §11.1.3.**
  - "An asynchronous exception is, by contrast, an exception that can potentially occur at any point in the execution of a program. Asynchronous exceptions occur only as a result of an internal error or resource limitation in the Java Virtual Machine".
  - "OutOfMemoryError … may be thrown synchronously during class instance creation …, array creation …, class initialization …, and boxing conversion …, as well as asynchronously."
  - "The Java SE Platform permits a small but bounded amount of execution to occur before an asynchronous exception is thrown."
- **JVMS §6.3.** "This specification cannot predict where internal errors or resource limitations may be encountered and does not mandate precisely when they can be reported. Thus, any of the VirtualMachineError subclasses defined below may be thrown at any time during the operation of the Java Virtual Machine."
- **Derived.**
  - Java makes exhaustion an observable exception but permits it anywhere.
  - A Java program cannot rely on exhaustion *not* occurring at a given point.
  - A JVM can elide or add allocations without changing which outcomes are permitted: the asynchronous case already covers them.

### 6. WebAssembly: growth failure is an in-language result; other exhaustion is an implementation limit

Basis: normative (`WebAssembly/spec` at `6fca707686ed4f36a1e30ec2ae7d3dd32b276704`) + source (`WasmCert/WasmCert-Isabelle` at `d9b4659c8b38879a5fc7e0213950751a61091908`) + documentation (Watt, CPP 2018).

- **Prose note.** `document/core/exec/instructions.rst:639–645`: "The memory.grow instruction is non-deterministic. It may either succeed, returning the old memory size sz, or fail, returning −1. Failure *must* occur if the referenced memory instance has a maximum size defined that would be exceeded. However, failure *can* occur in other cases as well. In practice, the choice depends on the resources available to the embedder." `table.grow` has the same note (lines 500–505).
- **Formal rules.** `specification/wasm-latest/4.3-execution.instructions.spectec:564–570`:
  ```text
  rule Step/memory.grow-succeed:
    z; (CONST at n) (MEMORY.GROW x)  ~>  $with_meminst(z, x, mi); (CONST at $(|$mem(z, x).BYTES| / $($(64 * $Ki))))
    -- if mi = $growmem($mem(z, x), n)
  rule Step/memory.grow-fail:
    z; (CONST at n) (MEMORY.GROW x)  ~>  z; (CONST at $inv_signed_($size(at), $(-1)))
  ```
  - The fail rule has **no premise**.
  - `$growmem` (`4.0-execution.configurations.spectec:314–319`) is partial: it is defined only within the declared maximum and `2^($size(at) − 16)` pages.
  - `Step/struct.new` (`4.3-execution.instructions.spectec:707–711`) always allocates at `|$s(z).STRUCTS|`; there is no failure rule.
- **Implementation limits.** `document/core/appendix/implementation.rst:130–152` lists permitted execution-time restrictions, among them the number of allocated structure, array, and memory instances, memory size, and numbers of frames, labels, and values. "If the runtime limits of an implementation are exceeded during execution of a computation, then it may terminate that computation and report an implementation-specific error to the invoking code." Line 157 adds that limits "may be dependent on specifics, interdependent, vary over time".
- **WasmCert-Isabelle mirrors the split.**
  - `WebAssembly/Wasm.thy:331` (`memory_grow`) requires `mem_grow m (nat_of_int c) = Some mem'`. Line 333 (`memory_grow_fail`) has no resource premise.
  - `mem_grow` (`Wasm_Base_Defs.thy:216–220`) returns `None` only above 2^16 pages or the declared maximum.
  - The executable interpreter always succeeds when `mem_grow` returns `Some` (`Wasm_Interpreter.thy:351–362`).
  - It reports call-depth exhaustion as `Res_crash (Error_exhaustion …)` (line 1085).
  - Its soundness theorems cover only `RValue` and `RTrap` results (`Wasm_Interpreter_Properties.thy:3360–3392`).
  - Size: 33 `.thy` files, 27,773 lines, 1,298,804 bytes, plus a 295,801-byte extracted OCaml interpreter (`WebAssembly/code/WasmRef_Isa.ocaml`). (Basis: execution, `wc`.)
- **Watt 2018.**
  - §2 (p. 4): "the grow_memory instruction, which allocates additional memory to the heap, is allowed to fail non-deterministically".
  - §6: the interpreter adds fuel, and a separate depth parameter because "The WebAssembly specification requires all implementations to gracefully implement a limit on the level of nested function calls". The result type includes `CExhaustion`.
  - §1: "~11,000 non-whitespace, non-comment lines of Isabelle code, with the mechanisation of the specification itself coming to ~700 lines".
  - §7: differential testing against major engines (CSmith → Binaryen) found "No errors … either in our implementation or any commercial engine", plus one Binaryen crash bug.
- **Derived.**
  - Linear-memory growth failure is an ordinary observable value, and a conforming implementation may fail any growth.
  - GC-object allocation and call depth have no in-language failure. Their exhaustion terminates the computation outside the formal semantics, and the verified interpreter's crash results carry no semantic claim.

### 7. Probes E1–E3: allocation elision on real toolchains

Basis: execution (support/`run_probes.sh`, output in support/`probe_output.txt`; host and toolchains as in Applicability).

| Probe | Build | Observed (stdout :: exit) | Allocator calls in assembly |
|---|---|---|---|
| E1 C `malloc(2^50)`; NULL test; `free` | `gcc -O0` | `malloc(2^50): NULL` :: 1 | 1 |
| E1 | `gcc -O2` | `malloc(2^50): non-NULL` :: 0 | 0 |
| E1 | `gcc -O2 -fno-builtin-malloc` | `malloc(2^50): NULL` :: 1 | not counted |
| E2 C++ `new char[2^50]` in `try`/`catch (std::bad_alloc&)` | `g++ -O0` | `std::bad_alloc` :: 1 | 1 |
| E2 | `g++ -O2` | `returned` :: 0 | 0 |
| E2 | `g++ -O2 -fno-allocation-dce` | `std::bad_alloc` :: 1 | not counted |
| E3 Rust `Vec::<u8>::with_capacity(2^50)`, unused | `rustc -C opt-level=0` | `memory allocation of 1125899906842624 bytes failed` :: 134 | — |
| E3 | `opt-level=3` | `with_capacity(2^50) unused: returned` :: 0 | — |
| E3 same, but `black_box(&v)` | `opt-level=0` and `3` | abort message :: 134 at both | — |
| E3 `Vec::try_reserve(2^50)` | `opt-level=0` and `3` | `Err(memory allocation failed because the memory allocator returned an error)` :: 0 at both | — |

- **Mechanism (source + execution).** The `opt-level=3` LLVM IR for the probe file still contains `__rust_alloc` calls for the non-elided paths: one `__rust_alloc`, one `__rust_realloc`, and eleven `__rust_dealloc` call sites (`--emit=llvm-ir`, call-site count). The unused-path behaviour matches the InstCombine null-fold in §5.4.
- **What this establishes.** On these builds, an exhaustion outcome of the unoptimised program (NULL/exit 1, `bad_alloc`, abort 134) becomes a completion outcome under optimisation. This is permitted by C++ `[expr.new]` and by the Rust contract, and in tension with a strict reading of C11 §7.22.3p1.
- **What it does not establish.**
  - Elision of allocations whose size is not a constant.
  - Merging of distinct allocations.
  - Other compiler versions.
  - Whether `try_reserve` can ever be elided (§5.3).

### 8. Probe E4 and source: where exhaustion surfaces under Linux

Basis: documentation (`torvalds/linux` at `84afebd853437e44cb71f718be11d90e4c1a59dd`) + source + execution (distribution kernel 7.1.6).

- **Modes** (`Documentation/mm/overcommit-accounting.rst:7–29`):
  - 0: "Heuristic overcommit handling. Obvious overcommits of address space are refused … This is the default."
  - 1: "Always overcommit."
  - 2: "Don't overcommit. The total address space commit for the system is not permitted to exceed swap + a configurable amount (default is 50%) of physical RAM … in most situations this means a process will not be killed while accessing pages but will receive errors on memory allocation as appropriate."
  - Line 48: "In mode 2 the MAP_NORESERVE flag is ignored."
- **Exact mode-0 rule** (`mm/util.c:972–1016`, `__vm_enough_memory`):
  - `OVERCOMMIT_ALWAYS` returns 0 (line 982).
  - `OVERCOMMIT_GUESS` fails only `if (pages > totalram_pages() + total_swap_pages)` (lines 985–988). That is a per-request comparison, ignoring what is already committed.
  - Mode 2 compares `vm_committed_as` against `vm_commit_limit()` minus admin and user reserves (lines 991–1008).
- **Per-process address-space limit.** `mm/mmap.c:1351`: `may_expand_vm` refuses if `mm->total_vm + npages > rlimit(RLIMIT_AS) >> PAGE_SHIFT`. This is cumulative per process.
- **cgroup v2** (`Documentation/admin-guide/cgroup-v2.rst:1411–1418`): "If a cgroup's memory usage reaches this limit and can't be reduced, the OOM killer is invoked in the cgroup … In default configuration regular 0-order allocations always succeed unless OOM killer chooses current task as a victim."

| E4 case (program mallocs N MiB, then writes one byte per 4 KiB page) | Result | Where failure surfaced |
|---|---|---|
| no limit, N = 256 | `touched all 256 MiB`, exit 0; 0.03 s, max RSS 263,364 kB | — |
| `ulimit -v 131072` (RLIMIT_AS 128 MiB), N = 256 | `malloc(256 MiB): NULL (errno=12 Cannot allocate memory)`, exit 2 | at the call |
| `systemd-run --user --scope -p MemoryMax=64M -p MemorySwapMax=0`, N = 256 | `malloc(256 MiB): non-NULL`, last line `touched 48 MiB`, exit 137 (SIGKILL) | at first touch, by OOM kill |
| mode 0, untouched, N = 309221 / 309222 | non-NULL / non-NULL | — |
| mode 0, untouched, N = 309223 / 309422 | NULL (ENOMEM) / NULL | at the call |
| mode 0, three untouched 200000 MiB mallocs in one process | all non-NULL (3,900–8,631 ns each) | — (585.9 GiB reserved against 302.0 GiB RAM+swap) |
| mode 0, three 309223 MiB mallocs | all NULL; 4,380 ns to 32.3 ms per failing call | at the call |

- **Derived boundary.** MemTotal + SwapTotal = 316,643,776 kB = 309,222.44 MiB = 79,160,944 pages. A 309,222 MiB request (79,160,832 pages plus allocator overhead) fits. A 309,223 MiB request (79,161,088 pages) exceeds it. The measured switch is exactly at the predicted MiB.
- **Not examined.** Why some failing calls take tens of milliseconds and others microseconds.

### 9. Which allocation-changing transformations each representation licenses

Basis: derived from §§1–8. Each cell is reasoning from the quoted definitions, not a theorem from the source, unless a source statement is cited.

| Transformation | Deterministic in-language (Jinja) | Outside the model (CompCert) | No behaviour plus partial (Kang; CompCertTSO) | Target escape (CakeML) | Target ≤ source memory (CompCertS) | Angelic elision (C++, Rust, LLVM) | Asynchronous (JVM) |
|---|---|---|---|---|---|---|---|
| Remove a dead allocation | changes later addresses and can remove an `OutOfMemory`, so not an identical-heap refinement | sound (Leroy–Blazy injections) | sound in the logical model; Kang fn. 2: not under C11 NULL semantics; Lee §8: "unsound" in their finite model | sound | sound (memory decreases) | licensed (`[expr.new]`/14; `global.rs:129–134`; LangRef 2164–2169) | permitted outcomes unchanged |
| Merge allocations | as above | sound (Clight→Cminor groups locals) | not examined | sound | sound if size does not grow | licensed with constraints (`[expr.new]`/16; `global.rs:100–102`) | unchanged |
| Heap to stack | n/a | sound | not examined | sound | must count stack in the bound | licensed (`global.rs:129–131`) | unchanged |
| Add memory (spills, boxing, closures) | changes heap | sound (memory extensions) | allowed: "we should allow the target program to run out of memory even if the source program does not" | sound (escape absorbs it) | needs source-level provisioning (`ns` oracle) | not addressed by these texts | unchanged |
| Reorder allocation relative to I/O | shifts where `OutOfMemory` occurs relative to output | sound | partial behaviours must remain prefixes | escape requires an I/O prefix | not examined | `[expr.new]`/16 sequencing conditions | bounded delay permitted |

- **Reading.** Only the representations that let the target fail *more* (CakeML, Kang) or that put allocation outside behaviour (CompCert; C++/Rust/LLVM elision) license the common optimisations without side conditions.
- **The cost of each.** The escape makes the theorem weak: the "trivial compiler" remark. Elision makes source programs unable to rely on exhaustion. Deterministic synchronisation (Jinja) forbids the optimisations altogether.

### 10. Performance and resource footprint (L1–L6)

| Level | Item | Value [evidence] |
|---|---|---|
| L1 authoring | Jinja AFP entry | 72 `.thy` files, 20,099 lines [measured, `wc`] |
| L1 | WasmCert-Isabelle | 33 `.thy` files, 27,773 lines [measured]; Watt 2018 reports ~11,000 Isabelle lines, with the specification ~700 [cited] |
| L1 | Kang et al. Coq development | "about 10,000 lines" [cited] |
| L1 | person-months, token budgets, CompCertS proof size | not measured |
| L2 toolchain build | Isabelle, Coq, or HOL4 builds of these developments | not measured (not built) |
| L3 compile latency | effect of elision on compile time | not measured. Lee et al.: only 25% (464/1853) of object files changed [cited] |
| L4 generated code | Lee et al. prototype | SPEC CPU 2017 mean 0.2% slowdown, worst 1.75%; LLVM Nightly worst −4.3%, best +4.0%, mean −0.3% [cited] |
| L4 | malloc reservation latency, mode 0, untouched 200000 MiB | 3,900–8,631 ns per call [measured, `clock_gettime`, one host] |
| L4 | failing malloc (309223 MiB) | 4,380 ns to 32.3 ms per call [measured; cause of variance not examined] |
| L4 | elision effect on run time of E1–E3 | not measured (programs exit immediately) |
| L5 proof checking | — | not measured |
| L6 footprint | 256 MiB touch probe, no limit | max RSS 263,364 kB [measured, `/usr/bin/time`] |
| L6 | cgroup-limited run | killed after touching 48 MiB of 256 under a 64 MiB limit [measured] |
| L6 | WasmCert extracted interpreter | 295,801 bytes of OCaml [measured, GitHub tree size] |

### 11. Comprehensibility and conceptual simplicity (C1–C2)

- **C1, human legibility.**
  - The deterministic Jinja rule is the easiest to read, but its consequences are nonlocal. A reader must notice that `addr = nat` makes the rule dead, and that the compiler theorem's identical heaps forbid allocation optimisations.
  - Angelic elision is the hardest to audit. Probe E1 shows that a programmer who writes `if (p == NULL)` gets the opposite of the unoptimised behaviour, with no diagnostic. The Rust contract text admits this ("code that used to fail … may now suddenly work").
  - Overcommit adds a third, operating-system-level surprise: failure moves from the call to an asynchronous kill whose victim the program does not choose.
- **C2, simplicity and orthogonality.**
  - The sources use at least six mechanisms for one question: may this execution run out of memory here?
  - A single abstraction that makes every case ordinary is a *budgeted* semantics. Exhaustion is an explicit outcome carrying the I/O prefix, as in Kang et al. and CakeML. Each transformation is then judged by a declared resource relation: equal, ≤ (CompCertS), or "target may additionally exhaust" (CakeML).
  - Elision then becomes the special case "target uses ≤ memory".
  - Overcommit stays outside, as a property of the platform's budget: the budget is not known at the allocation site.
  - The hidden complexity moves into the resource relation each pass must prove, as in CompCertS's `ns` oracle. It is not eliminated.

### 12. Validation (V1–V4)

- **V1, specification adequacy.**
  - WebAssembly's unconditional fail rule is validated by WasmCert-Isabelle mirroring it.
  - Watt's interpreter passes the core conformance tests (§7).
  - Probes E1–E3 are executable checks that compiled behaviour matches the C++, Rust, and LLVM text, and conflicts with a strict reading of the C text.
  - The E4 mode-0 boundary probe checks one kernel source line against a running kernel.
- **V2, compiler and checker fuzzing.**
  - Watt's CSmith → Binaryen differential testing found no engine errors.
  - No differential testing of *exhaustion* behaviour across compilers was found. Fuzzers normally run under generous memory limits, so elision-induced divergence between optimisation levels would not be flagged as a bug: the standards permit it.
  - RFC 2116 notes allocator-level OOM injection in some runtime test suites (line 94).
- **V3, crash and fault injection.** cgroup `memory.max` and `RLIMIT_AS` are cheap OOM injectors. Probe E4 shows they inject *different* failure points (kill at touch versus NULL at call). A test harness must pick the one matching its deployment.
- **V4, plant, HIL, and human-model validation.** Not examined.

## Boundaries

- **Not examined.**
  - Executing any WebAssembly engine's `memory.grow` failure behaviour.
  - `overcommit_memory` modes 1 and 2 on a live kernel (changing the sysctl was not attempted).
  - Windows commit-charge semantics.
  - JVM implementations' actual `OutOfMemoryError` placement.
  - Elision of allocations whose sizes are not constants, and merging.
  - The JAR-published CompCertS layout and its theorem numbering (author PDF read).
  - The TOPLAS 2006 layout of Klein–Nipkow (technical report read).
  - The full text of CompCertTSO.
- **Unknown.**
  - Whether LLVM's virtual allocator is intended to be infallible. LangRef is silent; InstCombine folds null tests.
  - Whether `try_reserve` may be elided under the Rust contract.
  - Why failing large `malloc` calls on the probe host vary between microseconds and tens of milliseconds.
- **Known not to apply.**
  - The Jinja compiler theorem says nothing about runs in which source and target exhaust at different points. Its identical-heap form excludes them.
  - CompCert's theorem says nothing about exhaustion at all.
- **Unsupported.**
  - The WebAssembly core specification has no in-language failure for `struct.new` or `array.new`.
  - Java has no way to forbid an `OutOfMemoryError` at a point.
- **Attractive but unsupported conclusions.**
  - "Elision is harmless because it only removes failures." It also changes observable control flow (the NULL branch, `catch`), and Lee et al. call it unsound in a finite model.
  - "Mode 0 prevents overcommit." It only refuses single requests larger than RAM plus swap, as the three 200000 MiB reservations show.
  - "The probe results generalise to other GCC, rustc, or kernel versions." They do not without rerunning.
- **Provenance limits.** Some subjects lack immutable identities: the C++ working draft at eel.is (moving), the Java specifications (edition URL only), N1570 (dated committee draft), and the GCC and distribution-kernel builds (package version strings).

## Evidence

- **Observation dates.** All evidence was gathered on 2026-11-21 (UTC).
- **Repositories** (read-only; raw files at the pinned commit):
  - `isabelle-prover/mirror-afp-devel` `523cdc72b5ae4a91c9ab8e1025d4a30b40472720`, under `thys/Jinja/`: `Common/Value.thy:10`; `Common/Objects.thy:36,44`; `Common/Exceptions.thy:19–41`; `J/BigStep.thy:23–25`; `J/SmallStep.thy:47–49`; `Compiler/J1.thy:51–53`; `JVM/JVMExecInstr.thy` (`exec_instr_New`); `Compiler/Compiler.thy:17–22`; `Compiler/Correctness1.thy:316`; `Compiler/Correctness2.thy:408,1113–1116`.
  - `AbsInt/CompCert` `2685140bf72c959446981fb99b5e44a8975021bc`: `common/Memtype.v:99–101`; `common/Memory.v:343–357`.
  - `minirust/minirust` `063d784186d3252bee242217f218223205c0b568`: `spec/mem/basic.md:6,102–107`.
  - `CakeML/cakeml` `2874b664e10939a3ee462215b2e068c89c1f70eb`: `semantics/proofs/semanticsPropsScript.sml:219–237`; `compiler/proofs/compilerProofScript.sml:201–222`.
  - `rust-lang/rust` `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`: `library/core/src/alloc/global.rs:99–102,129–148,208–215`; `library/alloc/src/alloc.rs:639–669,700`.
  - `rust-lang/rfcs` `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`: `text/2116-alloc-me-maybe.md:1–14,94,134–142,232–250`.
  - `llvm/llvm-project` `04e0e9cc603537fbc16685f872fba17f937f90ff`: `llvm/docs/LangRef.md:2139–2175`; `llvm/lib/Transforms/InstCombine/InstructionCombining.cpp:3759–3800,3907–4000`.
  - `WebAssembly/spec` `6fca707686ed4f36a1e30ec2ae7d3dd32b276704`: `document/core/exec/instructions.rst:500–505,639–645`; `document/core/appendix/implementation.rst:130–157`; `specification/wasm-latest/4.3-execution.instructions.spectec:564–570,707–711`; `specification/wasm-latest/4.0-execution.configurations.spectec:305–319`.
  - `WasmCert/WasmCert-Isabelle` `d9b4659c8b38879a5fc7e0213950751a61091908`: `WebAssembly/Wasm.thy:331–333`; `Wasm_Base_Defs.thy:216–220`; `Wasm_Interpreter.thy:10–34,351–362,1085`; `Wasm_Interpreter_Properties.thy:3360–3392`; `README.md`.
  - `torvalds/linux` `84afebd853437e44cb71f718be11d90e4c1a59dd`: `Documentation/mm/overcommit-accounting.rst:1–48`; `mm/util.c:972–1016`; `mm/mmap.c:1348–1352`; `Documentation/admin-guide/cgroup-v2.rst:1407–1418`.
- **Toolchains executed.**
  - rustc 1.102.0-nightly, source commit `rust-lang/rust` `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (2026-11-11), LLVM 23.1.5.
  - GCC 15.2.0 (Debian 15.2.0-14). No immutable hash was recorded.
  - Linux 7.1.6, a Debian-derived distribution build; the distribution suffix of the version string is omitted here.
- **Literature** (DOIs verified against Crossref on 2026-11-21):
  - Klein, Nipkow, TOPLAS 28(4) 619–695 (2006), 10.1145/1146809.1146811 [read: NICTA TR 0400001T.1, March 2004; Theorem 5.4, p. 64].
  - Leroy, Blazy, JAR 41(1) 1–31 (2008), 10.1007/s10817-008-9099-0 [§4 p. 9; §5 pp. 11–13].
  - Kang, Hur, Mansky, Garbuzov, Zdancewic, Vafeiadis, PLDI 2015, 326–335, 10.1145/2737924.2738005 [§2.3, §3.2, §5.2, §6.6, §7; fn. 2].
  - Lee, Hur, Jung, Liu, Regehr, Lopes, PACMPL 2(OOPSLA) 1–28 (2018), article 125, 10.1145/3276495 [§3.2, §4, §6.2, §8, App. C].
  - Besson, Blazy, Wilke, "CompCertS", JAR 63(2) 369–392 (online 2018-11-16), 10.1007/s10817-018-9496-y [author PDF; §6, §6.2.1; the PDF's own header says 63(1), August 2019].
  - Carbonneaux, Hoffmann, Ramananandro, Shao, PLDI 2014, 270–281, 10.1145/2594291.2594301 [§3.1–3.2].
  - Tan, Myreen, Kumar, Fox, Owens, Norrish, JFP 29 e2 (2019), 10.1017/S0956796818000229 [preprint 2018-11-19, §2.3].
  - Watt, CPP 2018, 53–65, 10.1145/3167082 [§1 p. 2, §2 p. 4, §6, §7].
- **Standards.**
  - WG21 N3664 (2013-04-19), https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2013/n3664.html.
  - C++ working draft `[expr.new]` 7.6.2.8, https://eel.is/c++draft/expr.new (observed 2026-11-21).
  - WG14 N1570 (2011-04-12) §7.22.3, §7.22.3.4.
  - JLS SE 27 §11.1.3, https://docs.oracle.com/javase/specs/jls/se27/html/jls-11.html.
  - JVMS SE 27 §6.3, https://docs.oracle.com/javase/specs/jvms/se27/html/jvms-6.html.
- **Execution.** `bash support/run_probes.sh`, with sources `elide.c`, `elide.cc`, `elide.rs`, `touch.c` and `multi.c`. The full output is in `support/probe_output.txt`, where the kernel distribution suffix and one temporary-directory path are redacted and marked as such.
- **Synthesis versus source facts.** The §9 matrix and every "Derived" bullet are this report's synthesis. Quotations and measurements are source or execution facts.

## Revalidation

- **Elision.** Rerun `bash support/run_probes.sh` with a new compiler. A change is real if E1/E2 at `-O2` print `NULL`/`bad_alloc`, or E3 `unused` at `opt-level=3` aborts. Also re-grep `InstructionCombining.cpp` for `fold eq/ne comparisons with null`.
- **Contracts.** Diff `global.rs:99–148`, `LangRef.md` `allockind`, `[expr.new]`/14–16, and JVMS §6.3 at the new revision.
- **Mechanisations.** Re-grep for the following at the new revisions:
  - `NewFail` and `new_Addr` in `thys/Jinja/`;
  - `memory_grow_fail` in WasmCert-Isabelle;
  - `Step/memory.grow-fail` (still premise-free?) in the WebAssembly spec;
  - the MiniRust FIXME at `spec/mem/basic.md:106`;
  - `extend_with_resource_limit_def` in CakeML.
- **Kernel.** Compute `MemTotal+SwapTotal` from `/proc/meminfo` and rerun `touch <MiB-1>` and `touch <MiB+1> notouch` at mode 0. Check `mm/util.c` for the `OVERCOMMIT_GUESS` branch. Modes 1 and 2 need privileged sysctl changes and were not exercised.
