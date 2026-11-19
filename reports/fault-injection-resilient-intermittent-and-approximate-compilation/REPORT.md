# Fault-Injection-Resilient, Intermittent, and Approximate Compilation: Why Optimizers Delete Redundancy, How Reboot-Anywhere Programs Stay Consistent, and What Accuracy Qualifiers Guarantee

## Summary

Three families of systems compile for machines that do not execute the program faithfully (soft errors, fault injection), not continuously (energy-harvesting devices that lose power at arbitrary instructions), or not exactly (approximate hardware). They share one structural fact: the property they need is defined over *non-standard executions* (faulty, interrupted, perturbed), while a conventional compiler's correctness criterion speaks only about the standard, fault-free, uninterrupted, exact execution. Everything below follows from that mismatch.

1. **Redundancy inserted for fault detection is dead code in the fault-free semantics, and a correct optimizer may delete all of it.** A shadow computation has the same value number as the original, so common-subexpression elimination (CSE) or global value numbering (GVN) merges them; the comparison then has identical operands and folds; dead-code elimination (DCE) removes the trap. This is stated in the primary literature (the TAL_FT paper shows a CSE'd fragment that silently stores a corrupted pair), is visible in compiler source (CompCert `CSE.transf_instr` rewrites a recomputation into a move; LLVM `EarlyCSE`/`GVN` "eliminate ... redundant instructions"), and was reproduced here twice: GCC 15.2.0 deletes a plain-C duplicate-and-compare and a doubled branch test at every level from `-O1` up, and in an exhaustive single-bit-upset simulation `optimize(SWIFT(P))` is *syntactically equal* to the unprotected `P`, moving silent data corruption from 2.14% back to 31.43% of injections.
2. **Deployed systems survive in one of five ways**, each with a distinct residual risk: (a) run the hardening transformation after the optimizers (SWIFT and TAL_FT insert it "immediately before register allocation and scheduling"; COAST runs as an `opt` pass just before `llc`); (b) hide the redundancy behind constructs the optimizer must preserve (`volatile`, empty inline-assembly barriers such as OpenTitan's `launder32`/`barrier32`, assembly-coded double branches); (c) carry explicit *observations* through the pipeline (opaque copies in the Chamois-Arsene CompCert fork; observation/opacification in Vu et al.); (d) type-check the generated assembly against a fault model (TAL_FT); (e) prove the transformation both semantics-preserving and robust against a formal attacker model (Chamois-Arsene: intra- and inter-procedural control-flow checking, with a single-fault security theorem).
3. **Every detection guarantee is relative to a stated fault model and has documented holes.** SWIFT leaves the interval between validating a store's operands and executing the store unprotected; CFCSS signatures alias for certain fan-in shapes unless buffer blocks are added; TAL_FT assumes fault-free code and data memory and a hardware store queue; the Chamois-Arsene documentation states that only one of its three countermeasures is currently shielded from later optimizations and that most RTL passes erase the `Iassert` facts its robustness proofs use.
4. **Intermittent execution needs idempotent restart regions.** After a power failure volatile state rolls back but non-volatile (NV) writes persist; a region that reads and later writes the same NV location (write-after-read, W-A-R) is not idempotent. Chain forbids the pattern structurally (tasks read input channels and write output channels), Alpaca redirects W-A-R variables to task-private copies and commits them with a resumable redo log, Ratchet has the compiler cut code into W-A-R-free sections separated by checkpoints, and Curricle expresses idempotence requirements in a type system for Rust. Exhaustive power-failure injection (up to three failures) on models of the privatize-and-commit and checkpoint-between-read-and-write disciplines gives the single consistent result on every schedule, against four distinct results for a naive in-place task.
5. **Mayfly is not a type system.** It is a coordination language and runtime whose programs are task graphs with timing constraints on edges (`expires`, `collect`, `misd`); freshness and temporal consistency as compiler-enforced program properties appear later (Ocelot, whose annotations are placed in Rust source and whose atomic regions are inferred on LLVM IR; Curricle).
6. **EnerJ's `@Approx`/`@Precise` qualifiers are an integrity information-flow discipline.** Approximate data may not flow to precise data, may not decide control flow, and may not index arrays, except through an explicit `endorse`; the formal core satisfies non-interference in the absence of endorsements. The language deliberately does not define what approximation does: "one valid execution is to ignore all annotations and execute the code as plain Java".

## Applicability

**What the subjects are and how they relate.** The report is a comparison across three problem families, each anchored in papers and in source code:

- *Transient-fault and fault-injection hardening*: the SWIFT and TAL_FT papers (full text read from author-hosted copies); the commented Coq development page of the Chamois-Arsene fork of CompCert, which is the artifact companion of Pesin, Boulmé, Monniaux and Potet, *Formally Verified Hardening of C Programs against Hardware Fault Injection* (CPP 2025); mainline CompCert 3.18 and LLVM at the pinned commits, examined only for what their redundancy-elimination passes do; OpenTitan's `hardened.h`, examined as an example of production source-level countermeasures written against an optimizing compiler; COAST, examined as an open LLVM implementation of duplication, triplication and CFCSS; and GCC 15.2.0, the only compiler actually executed.
- *Intermittent computing*: the Chain, Alpaca, Ratchet, Mayfly and Curricle papers (full text), the Chain and Alpaca runtime libraries and the Alpaca LLVM pass (source), and the Ocelot artifact (README, annotated Rust benchmarks, Rust stub file).
- *Approximate computing*: the EnerJ paper (full text) and the EnerJ checker/runtime repository (source).

**Scope of each kind of claim.**

- Statements about *papers* apply to the cited publication as fetched on the observation date. For SWIFT, TAL_FT, Alpaca, Chain, Mayfly, EnerJ, Curricle and Ratchet the copy read was an author- or venue-hosted PDF, not the publisher's version of record; bibliographic identity (title, authors, venue, pages, DOI) was confirmed against Crossref.
- Statements about *source* apply to the exact commits in `REPORT.json`. No claim is made about other revisions.
- The two *compiler-behaviour* results were obtained with `gcc (Debian 15.2.0-14) 15.2.0` targeting `x86_64-linux-gnu` only. No LLVM-based compiler and no Rust compiler was available on the observation host, so nothing here is an observation of Clang or rustc output. OpenTitan's barrier is documented by its authors as LLVM-specific; its behaviour under GCC in the probe says nothing about LLVM.
- The three *simulation* results (single-bit-upset campaign, CFCSS aliasing, power-failure injection) are executions of small models written for this report. Their sources are reproduced verbatim under Evidence. They characterize the mechanisms as described in the cited papers and source; they are not runs of SWIFT, COAST, Chain, Alpaca or Ratchet themselves.
- The CPP 2025 paper body could not be retrieved (publisher and archive pages were not reachable through the available fetch path). All statements about that work come from the fork's public documentation page, which cross-references each paper figure, definition and theorem to a Coq identifier, and from an author talk dated 5 June 2024 that predates the paper. Where the two differ in maturity this is stated.
- Out of scope: constant-time and speculative-execution side channels, hardware error-correcting codes as such, radiation test data, and multi-bit or permanent faults.

## Findings

### 1. Fault models actually assumed, by system

Each system's guarantee is meaningless without its fault model. The table collects the models as stated by each primary source.

| System | Level | Fault model | Assumed fault-free | What counts as failure | Basis |
|---|---|---|---|---|---|
| SWIFT | low-level IR before register allocation (IA-64) | "a Single Event Upset (SEU) fault model, in which exactly one bit is flipped throughout the entire program" | "the memory subsystem, including processor caches, are already adequately protected" (ECC) | data leaving the sphere of replication through a store with wrong value or address | documentation (paper §3) |
| TAL_FT | typed assembly on an idealized RISC machine with a store queue | rules `reg-zap` (any register replaced by an arbitrary value, colour tag preserved), `Q-zap1`, `Q-zap2` (address or value of a store-queue entry replaced); "k will always be either 0 or 1" | "both code memory C and value memory M are fully protected" | the externally observable sequence of writes to the memory-mapped output device differs and no fault was signalled | documentation (paper §2.1) |
| CFCSS (as implemented in COAST) | LLVM IR basic blocks | illegal transfer between basic blocks | not stated in the examined documentation | an illegal branch that reaches a block entry whose check passes | documentation + source (COAST `docs/source/cfcss.rst`, `projects/CFCSS/`) |
| Chamois-Arsene CompCert | RTL (and BTL) intermediate languages | faulted transitions added to the RTL semantics: inverted conditional (`exec_Icond_inverted`), and for the inter-procedural pass a skipped call (`exec_Icall_skip`) and a call to the wrong function (`exec_Icall_wrong`); robustness is stated for a *single* fault | everything outside the modelled transitions; passes after RTL | a faulted run that neither reaches the catch handler nor is equivalent to a fault-free run | documentation (fork documentation page; author talk) |
| OpenTitan `hardened.h` | C source for RISC-V firmware | "an attacker can glitch the chip to skip the first branch"; value corruption of booleans | the compiler emitting what the barriers intend | a critical operation bypassed | source (header comments) |
| EnerJ simulator | Java bytecode instrumentation | statistical bit errors in approximate storage and operations: SRAM write failure probability 10^-4.94, SRAM read upset 10^-7.4, DRAM flip probability 10^-5 per second, timing-error probability 1.5% (defaults in `PrecisionRuntimeNoisy.java`) | all data typed precise | none: errors in approximate data are permitted by definition | source |

Two things follow directly. First, "detects all single faults" is never unconditional: SWIFT's own text names its exceptions (Finding 6) and TAL_FT pushes part of the job into assumed hardware. Second, the adversarial models (OpenTitan, Chamois-Arsene) and the stochastic ones (SWIFT, TAL_FT) are different in kind: an attacker chooses the instruction to disturb, so a countermeasure that is merely *probably* present after optimization is not acceptable.

Basis: documentation + source, as marked per row.

### 2. Why a correct optimizer deletes fault-detection redundancy

**2.1 The argument.** Let `H(P)` be `P` with every register computation duplicated into a shadow register and a comparison `if (r != r') trap` inserted before each output. In the fault-free semantics `r'` is computed by the same operator from operands with the same values as `r`. Therefore:

1. value numbering gives `r` and `r'` the same number and replaces the shadow computation with a copy of `r` (or deletes it);
2. after copy propagation the comparison reads `r != r`, which constant-folds to false;
3. the trap is unreachable and the shadow chain is dead, so DCE removes both.

Each step preserves fault-free observable behaviour, which is the only obligation of a conventional compiler-correctness statement. Hence `optimize(H(P))` may legitimately equal `P`. The same reasoning deletes a doubled security test (`if (x != K) return 0; if (x != K) trap;`): on the fall-through path the compiler has learned `x == K`.

Basis: derived (from the definitions of CSE/GVN, constant folding and DCE; confirmed by 2.2-2.4).

**2.2 The primary literature states the same thing.** The TAL_FT paper, after noting that the compiler is free to rename registers and reschedule, continues: "not all conventional optimizations are sound ... For example, common subexpression elimination might result in the following code:

```text
1 mov r1, G 5
2 mov r2, G 256
3 stG r2, r1
4 stB r2, r1
```

In this case, a fault in r1 after instruction 1, or a fault in r2 after instruction 2 will cause both instructions 3 and 4 to manipulate the same, but incorrect, address-value pair." Both the green and the blue store now read the same registers, so the redundant pair no longer has independent failure modes. The paper continues: "Fortunately, the TALFT type system catches reliability errors like this one."

Basis: documentation (TAL_FT paper §3).

**2.3 Compiler source.** In mainline CompCert 3.18, `backend/CSE.v` defines

```text
Definition transf_instr (dm: defmap) (n: numbering) (instr: instruction) :=
  match instr with
  | Iop op args res s =>
      if is_trivial_op op then instr else
        let (n1, vl) := valnum_regs n args in
        match find_rhs n1 (Op op vl) with
        | Some r =>
            Iop Omove (r :: nil) res s
        ...
```

that is, an operation whose right-hand side already has a value number held in register `r` becomes a move from `r`; loads are treated the same way (`find_rhs n1 (Load chunk addr vl Ptop)`). `driver/Compiler.v` runs, in order on RTL, `Tailcall`, `Inlining`, `Renumber`, `Constprop`, `Renumber`, `CSE`, `Deadcode` (labelled "Redundancy elimination"), `Unusedglob`, then register allocation. A shadow computation written at C level therefore meets constant propagation, CSE and dead-code elimination before any code is emitted. The same repository at this commit contains no file or identifier matching `CounterMeasures`, `Iassert`, `EF_observe`, `fsecu` or `RTLfault`: the hardening passes of Finding 4 are not in mainline.

In LLVM at the pinned commit the file headers read: `EarlyCSE.cpp` - "This pass performs a simple dominator tree walk that eliminates trivially redundant instructions."; `GVN.cpp` - "This pass performs global value numbering to eliminate fully redundant instructions. It also performs simple dead load elimination." Neither pass has any notion of a redundancy that is intended.

Basis: source.

**2.4 Execution: GCC 15.2.0 on source-level countermeasures.** Six C functions each contain exactly one check that is dead in the fault-free semantics (source under Evidence, E1). The table gives, per optimization level, the number of surviving references to the trap function and the number of compare instructions in the emitted x86-64 assembly.

```text
gcc (Debian 15.2.0-14) 15.2.0
function                            -O0          -O1          -O2          -O3          -Os
                               trap/cmp     trap/cmp     trap/cmp     trap/cmp     trap/cmp
dup_plain                       1/1          0/0          0/0          0/0          0/0    
dbl_check_plain                 1/2          0/1          0/1          0/1          0/1    
dup_volatile                    1/1          1/1          1/1          1/1          1/1    
dup_barrier                     1/1          1/1          1/1          1/1          1/1    
dbl_check_barrier_first         1/2          1/2          1/2          1/2          1/2    
dbl_check_barrier_second        1/2          1/2          1/2          1/2          1/2    

dbl_check_barrier_second at -O2:
    cmpl	$15525, %edi
    jne	.L24
    cmpl	$15525, %edi
    jne	.L29
    movl	$1, %eax
    ret
    .L24:
    xorl	%eax, %eax
    ret
    .L29:
    pushq	%rax
    call	fault_detected@PLT
```

Reading: the plain-C duplicate-and-compare (`dup_plain`) and the plain-C doubled test (`dbl_check_plain`) lose their check at `-O1` and above; at `-O1` `dup_plain` compiles to `leal (%rdi,%rdi,2), %eax; addl %esi, %eax; movl %eax, sink(%rip); ret`. Routing the shadow operands through `volatile` objects or through an empty `asm volatile("" : "+r"(v))` barrier preserves the comparison at every level. With GCC both barrier placements for the doubled test kept two compares of the live argument register; the hazard OpenTitan documents for the "second test" placement (Finding 3) was not observed with this compiler.

Basis: execution (GCC 15.2.0, x86_64-linux-gnu; this compiler and target only).

**2.5 Execution: an optimizer applied to a SWIFT-style program restores the unprotected program.** A toy register machine (8-bit registers; `ld`, `li`, `mul3`, `add`, `chk`, `st`) runs three programs: an unprotected computation `NOFT`; `SWIFT = swiftify(NOFT)`, which duplicates every register computation and validates both operands of the store immediately before it; and `optimize(SWIFT)`, the result of local value numbering with copy propagation, folding of checks whose operands have the same value number, and DCE. Every (instruction boundary, register, bit) single-bit flip is injected for four input pairs.

```text
NOFT            : [('ld', 'a', 0), ('ld', 'b', 1), ('li', 'p', 64), ('mul3', 't', 'a'), ('add', 'r', 't', 'b'), ('st', 'p', 'r')]
SWIFT           : [('ld', 'a', 0), ('ld', "a'", 0), ('ld', 'b', 1), ('ld', "b'", 1), ('li', 'p', 64), ('li', "p'", 64), ('mul3', 't', 'a'), ('mul3', "t'", "a'"), ('add', 'r', 't', 'b'), ('add', "r'", "t'", "b'"), ('chk', 'r', "r'"), ('chk', 'p', "p'"), ('st', 'p', 'r')]
optimize(SWIFT) : [('ld', 'a', 0), ('ld', 'b', 1), ('li', 'p', 64), ('mul3', 't', 'a'), ('add', 'r', 't', 'b'), ('st', 'p', 'r')]
optimize(SWIFT) == NOFT : True
fault-free outputs identical for all three programs on all inputs: True

NOFT                   insns= 6 regs= 5 injections= 1120 CORRECT=  768 DETECTED=    0 SDC=  352 (31.43% SDC)
SWIFT                  insns=13 regs=10 injections= 4480 CORRECT= 2976 DETECTED= 1408 SDC=   96 ( 2.14% SDC)
optimize(SWIFT)        insns= 6 regs= 5 injections= 1120 CORRECT=  768 DETECTED=    0 SDC=  352 (31.43% SDC)

SWIFT residual SDC sites (boundary index, register, next instruction) -> count:
    (11, 'r', ('chk', 'p', "p'")) -> 32
    (12, 'p', ('st', 'p', 'r')) -> 32
    (12, 'r', ('st', 'p', 'r')) -> 32
```

Reading: the optimizer is correct (all three programs agree on every input without faults) and its output is *identical* to `NOFT`; protection falls from 1408 detections and 2.14% silent corruption back to no detections and 31.43%. The 96 residual corruptions of the SWIFT program all lie at the three sites where a store operand is flipped after its validation, which is exactly the first undetected-error class the SWIFT paper names (Finding 6).

Basis: execution (model written for this report; source under Evidence, E2).

### 3. How hardening survives a compiler: five mechanisms and their residual risk

| Mechanism | Instances examined | What the mechanism relies on | Documented or observed weakness | Basis |
|---|---|---|---|---|
| Insert after optimization | SWIFT: "The fault detection code was inserted into the low level code immediately before register allocation and scheduling." TAL_FT: "The reliability transformation was compiled into the low level code immediately before register allocation and scheduling." COAST: `clang -emit-llvm` per file, `llvm-link`, then `opt <flags> -TMR` (or `-DWC`, `-CFCSS`), then `llc`; its documentation says the pass is one "that the optimizer runs before the back-end compiles the assembly into machine code". | No redundancy-eliminating pass runs later. | Register allocation, scheduling, machine-level CSE, peephole and link-time passes still follow and are outside the argument. OpenTitan records one such case: two calls of a non-`volatile` barrier with the same argument were deduplicated, "from bisecting the passes, it appears to happen during register allocation". Source-level optimizations on the *unhardened* code are kept, which is the benefit. | documentation + source |
| `volatile` objects | probe functions `dup_volatile`; LLVM language reference: "The optimizers must not change the number of volatile operations or change their order of execution relative to other volatile operations." | A normative rule about memory accesses. | Forces memory traffic; protects the access count, not the comparison built on it (the comparison survives because the loaded values are unknown). COAST's troubleshooting notes warn in the other direction: when a replicated variable really is a volatile hardware register, "the copies will fail when compared". | normative (LLVM LangRef) + execution |
| Opaque value barrier | OpenTitan `launder32(val)` = `asm volatile("" : "+r"(val)); return val;` and `barrier32(val)` = `asm volatile("" ::"r"(val));` | The compiler treating an inline-assembly block as a black box that may rewrite its in/out operand. | The header says so itself: "This implementation is LLVM-specific, and should be considered to be a no-op in every other compiler. For example, GCC has in the past peered into the insides of assembly blocks." It is order-sensitive: "while we can stop the compiler from learning new information, it is very hard to make it forget" - with the barrier on the second of two tests the compiler "would be entitled to rewrite this into `launder32(0) == 0`", which "behaves like `0 == 0` at runtime". Without `volatile`, LLVM may treat the block "as behaving like a random oracle determined entirely by its arguments" and merge two calls. | source |
| Assembly-coded check | OpenTitan `HARDENED_CHECK_(op, a, b)`: one `asm volatile` block containing a branch to an OK label, an `unimp`, the OK label, and the inverse branch back to the `unimp`. | The assembler emitting both branches; hardened booleans `0x739`/`0x1d4` ("a Hamming Distance of 8 ... 11-bit values so they can be materialized with a single instruction on RISC-V ... not the complement of each other"). | "in spite of `HARDENED_CHECK` being written in assembly, it is still vulnerable to certain inimical compiler optimizations. For example, `HARDENED_CHECK_EQ(x, 0)` can be written to `HARDENED_CHECK_EQ(0, 0)`"; the check stays in the instruction stream but compares constants ("it will emit the nonsensical `beqz zero, continue`"). | source |
| Observations carried through the compiler | Vu, Cohen, De Grandmaison, Guillon, Heydemann (OOPSLA 2021): "observations of the program state that are intrinsic to the correct execution of security protections", preserved by "an opacification mechanism", "compatible with a production compiler and does not incur any modification to its optimization passes". Chamois-Arsene: a countermeasure pass emits a call to an `observe` builtin (`AST.EF_observe`); a later pass expands it into opaque copy instructions (`Op.Ocopy`) "that should not be optimized by the compiler". | An extended compiler contract: observation points have semantics that every pass must preserve. | The Chamois-Arsene documentation states that at present "only the interprocedural CFI is protected by observations". | documentation |
| Type-check or prove the result | TAL_FT (typed assembly; Finding 6). Chamois-Arsene (Coq proofs; Finding 4). | A formal fault model at the level being checked. | The guarantee stops at that level: TAL_FT assumes special hardware; Chamois-Arsene's robustness theorems are stated on RTL, "only the middle of the compiler: later passes may break CMs" (author talk). | documentation |

A practical corollary: the choice of mechanism determines *what is trusted*. Late insertion trusts the back end; barriers trust undocumented compiler behaviour; observations require a modified compiler; typed assembly trusts only the checker and the hardware model.

### 4. Verified hardening in a CompCert fork (Chamois-Arsene)

The fork's documentation page (titled "Version 3.14, Chamois-Arsene fork, 2025-12-06"; its installation section calls it "This fork of CompCert 3.15" - the two version strings disagree on the page itself) describes "three separate countermeasures against fault injection as program transformations", "primarily focused on the RiscV (32bits) architecture":

| Pass | Languages | Correctness proof | Robustness proof | Default |
|---|---|---|---|---|
| Intra-procedural control-flow checking ("Intra-procedural SWIFT") | RTL to RTL (`CFC`) | `CFCproof` | `CFCsecurity` | `-fsecu-cfc` on, applied only to functions marked `__attribute__((harden("control_flow_checking")))` |
| Inter-procedural control-flow checking ("Inter-procedural SWIFT") | RTL to RTL (`IPCFC`) | `IPCFCproof` | `IPCFCsecurity` | `-fsecu-ip-cfc` off |
| Expansion of `builtin_observe` | RTL to RTL (`ExpandObserve`) | `ExpandObserveproof` | N/A | - |
| Load duplication | BTL to BTL (`BTL_SBsecupasses`) | `BTL_BlockSimulationproof` | N/A | `-fsecu-dup-loads` on, applied only to loads wrapped in `__builtin_secu_wd_int(...)` |

A further option `-fsecu-cfc-return` ("intra-procedural control-flow checks before returns") is off by default.

The page maps the paper to Coq identifiers: Theorem 4.1 "Forward correctness of CFG rewriting" (`transf_function_correct`), Theorem 4.2 "Backward correctness of CFG rewriting" (`transf_function_inv`), Definition 4.3 "Robustness fo a single-fault attack" (`secure_against`; spelling as on the page), Theorem 4.4 "Robustness of the CFI countermeasure" (`transf_program_secure`), and Figure 10 "Attacker models for inter-procedural SWIFT" (`exec_Icall_skip`, `exec_Icall_wrong`).

*The rewriting itself* (author talk, intra-procedural case): a conditional branch `if c then pc1 else pc2` becomes

```text
if c { rts = gsr ^ sig1 } else { rts = gsr ^ sig2 };
if c { gsr = gsr ^ rts; if (gsr != sig1) { cm_catch(); } goto pc1; }
else { gsr = gsr ^ rts; if (gsr != sig2) { cm_catch(); } goto pc2; }
```

with a global signature register `gsr` and a run-time signature `rts`: the condition is evaluated twice, and a single inverted test leaves `gsr` inconsistent with the block reached.

*The security definition* (author talk): "a program G is secure against a single-fault attack with fault F if": for every initial state and every faulted execution whose trace is a fault-free prefix `t1` followed by one fault event, either the execution continues to the `Caught` state, or there is a fault-free continuation `t2` reaching a state that the *unfaulted* program also reaches with trace `t1 + t2`. In words: one fault is either detected or harmless.

*How proofs are connected*: a new RTL instruction `Iassert` "is used to carry global information about registers/memory from the correctness proof to a robustness proof"; it "does not modify the state, but checks that the condition applied to the argument values evaluates to true". The page adds: "Most RTL source-to-source passes remove Iassert by compiling it to an Inop, to simplify the correctness proof."

*What the authors report about optimization*: the 2024 talk's slide of preliminary results on Lazart test cases, comparing no countermeasure at `-O0`, countermeasures at `-O0` and countermeasures at `-O1`, is captioned "Optimizations do break our countermeasures!", and its outlook lists "RTL is only the middle of the compiler: later passes may break CMs" and "Develop a methodology to protect the CMs from optimizations". The 2025 documentation page shows the response - observe/opaque-copy - and its present extent: observations are placed "between the two test ... to prevent constant propagation of the two conditions" and after the test on `GSR` "to prevent its constant propagation, which would weaken (but not invalidate) the countermeasure", and only for the inter-procedural pass.

Basis: documentation (fork documentation page for pass table, options, theorem names, `Iassert`, observations; author talk of 5 June 2024 for the rewriting scheme, the security definition and the preliminary experimental remark). The paper's own statement of Definition 4.3 and Theorem 4.4 was not read.

### 5. CFCSS signature arithmetic, aliasing, and the buffer-block repair

As documented in COAST (`docs/source/cfcss.rst`), every basic block `v` gets a unique compile-time signature `s[v]` and a signature difference `d[v]`; a run-time register `G` holds the signature of the current block. On entry to `v` the code computes `G = G xor d[v]` and traps unless `G == s[v]`. With `d[v] = s[u] xor s[v]` for the single predecessor `u`, a legal transfer yields `s[v]`. For a *branch-fan-in* block (several predecessors) one predecessor is the base, and every predecessor `u` sets a run-time adjuster `D` before leaving, so that entry computes `G = G xor d[v] xor D`; COAST gives `D_3 = s_3 xor d_4 xor s_4`, i.e. `D[u] = s[u] xor s[base(v)]`.

Two consequences can be derived from the formulas and were checked by enumeration (model source under Evidence, E3):

```text
A. original scheme, shared predecessor 2 chosen as base of both fan-in blocks 4 and 5
   fan-in blocks: [4, 5, 6]  adjuster conflicts at: []
   all 9 legal edges pass: True
   illegal block-entry transfers: 33  undetected: [(1, 5), (3, 4)]
B. original scheme, bases 1 (for 4) and 3 (for 5): block 2 needs two different adjusters
   fan-in blocks: [4, 5, 6]  adjuster conflicts at: [2]
   all 9 legal edges pass: False
   illegal block-entry transfers: 33  undetected: []
C. buffer block 7 inserted on edge 2->5 (bases: 4<-1, 5<-7, 6<-4)
   fan-in blocks: [4, 5, 6]  adjuster conflicts at: []
   all 10 legal edges pass: True
   illegal block-entry transfers: 46  undetected: []
```

- *Aliasing (case A).* If one block (2) is a predecessor of two fan-in blocks (4 and 5), a consistent adjuster for it requires both fan-in blocks to use the same base signature. Then any other predecessor of either fan-in block can jump to the *other* one undetected: the illegal transfers 1 -> 5 and 3 -> 4 pass. After the adjuster is applied, `G xor D` equals the shared base signature regardless of where the jump came from.
- *Infeasibility (case B).* Choosing different bases makes block 2 need two different adjuster values; with a single value one of its own legal edges fails the check (a false positive).
- *Repair (case C).* COAST's documented modification - "insert an extra basic block to act as a buffer" between the predecessor and one fan-in successor - removes the shared-base constraint; all 46 illegal block-entry transfers in the repaired graph are then detected.

Independently of aliasing, the scheme checks only at block entries: a transfer into the middle of a block, or within a block, is invisible to it.

Basis: documentation (algorithm and repair as described by COAST) + derived (aliasing condition) + execution (enumeration).

### 6. SWIFT's residual windows and TAL_FT's hardware assumptions

**SWIFT.** The technique is EDDI-style instruction duplication with three changes: memory is not duplicated because it is assumed ECC-protected ("eliminating duplicate store instructions"; loads are still duplicated); control flow is protected by a signature scheme that updates the target signature "based on the redundant conditional instructions"; and signature comparisons are restricted "only to blocks which have stores in them", because "it is only the store instructions that ultimately send data out of the SoR". Function calls are synchronization points: "Before any function call, all input operands are checked against their redundant copies ... the original versions are passed as the parameters ... At the beginning of the function, the parameters must be reduplicated".

The paper's section "Undetected Errors" names two classes: (1) "there can be a delay between validation and use of the validated register values. Any strikes during this gap might corrupt state ... bit flips in store address or data registers are uncaught"; (2) "if an instruction opcode is changed to a store instruction by a transient fault. These stores are unprotected since the compiler did not see this instruction." Class (1) is exactly the 96 residual corruptions in Finding 2.5.

The evaluation modified "a pre-release version of the OpenIMPACT compiler", targeted Itanium 2, and injected faults in 300 runs per benchmark; the paper reports that the EDDI+ECC+CFE and SWIFT builds "detect all of the faults which yield incorrect outputs". One inconsistency inside the fetched copy is preserved rather than resolved: the abstract says SWIFT "demonstrates a 51% average speedup" over the best known single-threaded approach with ECC memory, while the introduction of the same PDF says "a 14% average speedup".

**TAL_FT.** Every value carries a colour, green or blue; a program maintains "two redundant and independent threads of computation, a green (G) computation and a blue (B) computation". The machine adds a store queue between processor and memory: a green store `stG` enqueues an address-value pair (rule `stG-queue`), and the matching blue store `stB` commits a queued pair to memory only when its own address and value agree with it (rule `stB-mem`). Control transfers use a special destination register `d` the same way: `jmpG r1` records the intended target, and a later `jmpB r2` jumps only if `r2` equals `d`; "If the addresses are different, the hardware detects a fault". Faults are exactly the three `zap` rules of Finding 1. The stated theorems are Progress, Preservation, the corollary "No False Positives" ("The hardware never claims to have detected a fault when no fault has occurred during execution of a well-typed program"), and Fault Tolerance (Theorem 4): for a well-typed state whose fault-free run produces output sequence `s`, every run with one fault either produces exactly `s` and ends in a state similar to the fault-free one up to values of one colour, or reaches the `fault` state having produced a prefix of `s`. The reported cost: "it only takes 34% longer to execute than the unreliable version", measured by simulating the scheme on the Itanium 2 instruction set with a modified VELOCITY compiler.

The design point to retain: TAL_FT does not ask the compiler to be careful; it makes *any* compiler's output checkable, at the price of hardware (store queue, colour-aware store and branch instructions) that the paper assumes rather than builds.

Basis: documentation (SWIFT paper §3-§5; TAL_FT paper §2-§5).

### 7. Intermittent execution: the write-after-read condition and three ways to discharge it

**7.1 Execution model.** An energy-harvesting device computes until its storage capacitor is exhausted, loses "the register file and volatile memory (i.e., stack and globals)", and resumes when recharged; "RF-powered devices may reboot hundreds of times per second" (Alpaca paper §2). Variables in non-volatile memory persist. If execution resumes from an earlier point (a checkpoint or a task start), code between that point and the failure runs again against NV state it has already modified. The Alpaca paper's formulation: "a non-volatile value that may be read and later written (i.e., a 'write-after-read', or W-A-R) between two consecutive checkpoints can become inconsistent". `x = x + 1` on NV `x` is the minimal case: each re-execution increments again.

**7.2 Comparison.**

| System | Restart unit | How NV consistency is obtained | Compiler's role | Programmer's obligation | Time and freshness | Basis |
|---|---|---|---|---|---|---|
| Chain (OOPSLA 2016; `libchain`) | task (`TASK(index, body)`; `TRANSITION_TO(task)`) | Tasks exchange data only through channels in NV memory; "A task may not write into any channel for which it is not the source and a task may not read from any channel for which it is not the destination." A self-channel (a task sending to its own next instance) is double-buffered and swapped at the transition. | none required: C macros and a runtime | decompose into tasks and declare every channel and field (`CHANNEL`, `CHAN_FIELD`, `CHAN_IN`n, `CHAN_OUT`n) | logical time only (`curctx->time`, ticks at task boundaries, used to pick the most recently written field) | documentation + source |
| Alpaca (OOPSLA 2017) | task | Task-shared NV variables with a possible W-A-R are *privatized*: the task works on a private copy and, at the transition, a commit list is replayed into the canonical locations ("two-phase commit"). | LLVM pass finds W-A-R variables, creates `<name>_bak` copies, redirects accesses, inserts pre-commit calls | mark tasks and task-shared variables | none | documentation + source |
| Ratchet (OSDI 2016) | compiler-inserted checkpoint | "The compiler identifies idempotent sections by looking for loads and stores to non-volatile memory and then enforcing that no section contains a write after read (WAR) to the same address", "gluing them together with checkpoints of volatile state". | whole mechanism | none (unmodified programs); the Alpaca paper lists Ratchet among prior work "that requires all memory to be non-volatile" | none | documentation |
| Mayfly (SenSys 2017) | task in a statically scheduled task graph | runtime checkpoints "local time", "the execution state", and "the data in each edge of each task graph"; task outputs are committed after the task completes, and an interrupted task or commit is re-executed | the Mayfly compiler generates an Embedded-C runtime that is "a statically defined schedule of tasks" | write tasks, flows (`temp -> wet -> send`) and edge constraints (`light -> wet {expires(10s)}`, `wet -> send {expires(4m), collect(10)}`) | first-class: `expires(time)` "Age of data to discard", `collect(num)` "Collect a buffer of data", `misd(time)` "Time before more data is useful"; relies on hardware timekeeping across outages | documentation |
| Ocelot (PLDI 2021 artifact) | inferred atomic region | regions bracketed by `atomic_start()`/`atomic_end()` re-execute as a unit, so inputs inside are gathered together | "a compiler pass that analyzes a program annotated with Fresh and Consistentcy constraints, then inferrs and instruments atomic region boundaries"; "regions are inferred at the IR level" | annotate Rust variables: `Fresh(reading);`, `Consistent(xs,5);`, `FreshConsistent(avgDiff,1);` (identity functions in `benchmarks/intermittent.rs`) | freshness and temporal consistency of inputs | source + documentation |
| Curricle (PLDI 2023) | atomic region / just-in-time checkpointing | types carry a pair of qualifiers, idempotence (`Id`/`Nid`) and input taint (`Nt`/tainted): "a variable x of type int@<Id, Nt> is idempotent and not tainted"; ill-typed programs "causing undesired non-idempotence" are rejected | "We implement Curricle's type system on top of Rust's compiler" | declare which variables must be idempotent | covers repeated-input (RIO) as well as W-A-R patterns | documentation |

Chain states its own correctness condition and its limit: "Chain is correct because its execution model ensures progress and its memory access model ensures that every task is atomic and idempotent", with progress holding "assuming no task's energy demand exceeds the maximum energy storage of the capacitor on the device". The second clause applies to every task-based system: a task that needs more energy than one charge can supply restarts forever.

**7.3 Runtime invariants visible in source.** Both task runtimes reduce "commit a task" to *one* NV word write.

- *Chain* (`src/chain.c`). Two NV context records (`context_0`, `context_1`) are linked through `next_ctx`; `transition_to` fills the inactive record (`next_ctx->task = next_task; next_ctx->time = curctx->time + 1;`) and then executes `curctx = next_ctx;`. Its comment reasons about every interleaving ("a reboot at any point in this sequence seems to be harmless") and records an open problem: "TODO: handle overflow of timestamp." `task_prologue` distinguishes a first entry from a restart by comparing `curctx->time` with the task's `last_execute_time`; only on a first entry does it swap dirty self-channel buffers, using a single MSP430 `SWPB` instruction on a 16-bit index pair so that "swap AND clear the dirty bit" is one instruction.
- *Alpaca* (`src/alpaca.c`). `transition_to` selects the inactive of two contexts, sets `next_ctx->task` and `next_ctx->needCommit = 1`, then `curctx = next_ctx;` ("atomic update of curctx"). `task_prologue`, which also runs first on every boot, replays the commit list if `curctx->needCommit` is set: `while (gv_index < num_dirty_gv) { ... memcpy(w_data_dest, w_data_src, w_data_size); ++gv_index; }` then `num_dirty_gv = 0; gv_index = 0; curctx->needCommit = 0;`. Because `gv_index` is itself non-volatile and each copy is from an unchanging private buffer, an interrupted commit resumes and repeating a copy is harmless. If `needCommit` is clear (a restart of an unfinished task) the prologue only resets `num_dirty_gv`, discarding the partial list. Arrays are versioned per element through a `<name>_isDirty` table and the 16-bit boot/transition counter `_numBoots`, when `_numBoots` equals `0xFFFF` the prologue calls `clear_isDirty()` before the counter wraps.
- *Alpaca's analysis is deliberately conservative* (`src/AnalyzeTasks.cpp`, `BackwardSearcher.cpp`). A global is W-A-R in a task if some read of it "precedes" some write, where precedence is CFG reachability backwards from the write (not dominance); a `MustAlias` result counts, and a `MayAlias` result is refined by a custom search; `memcpy` is treated as a write; and the comments state the fallbacks: "if a non-task function ever uses any global, consider as WAR" and "if unknown function takes a pointer to a GV, it is WAR".

Basis: source.

**7.4 Execution: exhaustive power-failure injection.** One task performing `x = x + 1` on NV `x` is modelled as micro-steps with a failure possible before every step, under three disciplines; every schedule with at most three failures is enumerated (source under Evidence, E4).

```text
naive          schedules(<= 3 failures)=   1351  final NV x in [1, 2, 3, 4]  INCONSISTENT
ratchet-style  schedules(<= 3 failures)=   2325  final NV x in [1]  CONSISTENT
alpaca-style   schedules(<= 3 failures)= 113653  final NV x in [1]  CONSISTENT
```

The naive in-place task ends with `x` in {1, 2, 3, 4} (one extra increment per failure that lands after the write). The checkpoint-between-read-and-write discipline and the privatize-then-redo-commit discipline, the latter transcribing the order of NV writes in the Alpaca runtime, end with `x == 1` on all 2,325 and 113,653 schedules respectively.

Basis: execution (models written for this report).

### 8. Approximation as a type qualifier (EnerJ)

| Rule | Paper | Checker source (`src/enerj/PrecisionVisitor.java` unless noted) |
|---|---|---|
| Every type is `@Approx` or `@Precise` (default precise); "a @Top qualifier to denote the common supertype of @Approx and @Precise types"; "It is illegal to assign an approximate-typed value into a precise-typed variable." "Precise values carry traditional guarantees of correctness; approximate values have no guarantees." | §2.1 | annotation classes in `src/enerj/lang/` (`Approx`, `Precise`, `Top`, `Context`) |
| `endorse(e)`: "Cast an approximate value to its precise equivalent." | §2.2 | `Endorsements.endorse`, e.g. `public static @Precise int endorse(@Top int param)` |
| No approximate condition: "EnerJ avoids this situation by prohibiting approximate values in conditions that affect control flow (such as if and while statements)." | §2.4 | `conditionCheck` reports `condition.type.incompatible`; called from `visitIf`, `visitWhileLoop` and the other loop/conditional visitors |
| Arrays: "the array's length is always kept precise for memory safety"; "EnerJ prohibits approximate integers from being used as array subscripts." | §2.6 | `visitArrayAccess` reports `array.index.approx` |
| Objects: `@Approximable` classes may have both kinds of instance; `@Context` makes a member's precision follow the enclosing object's; a method naming convention (`APPROX` in the paper's summary table) marks an implementation that "may be invoked when the receiver has approximate type" | §2.5 | `type.invalid.unapproximable` when `@Approx` is applied to a non-approximable class |

*Guarantee.* "We formalize a core of EnerJ and prove a non-interference property in the absence of endorsements"; concretely, "changing approximate values in the heap or runtime environment does not change the precise parts of the heap or the result of the computation." Endorsement is the only downgrade and is outside the theorem.

*What is deliberately unspecified.* The program "does not define the particular approximation strategies that are applied to the program. (In fact, one valid execution is to ignore all annotations and execute the code as plain Java.)" The paper proposes a hardware model (reduced SRAM supply voltage, reduced DRAM refresh, narrower floating-point mantissas, less reliable arithmetic) and reports "significant potential energy savings (7%-38%) at very little accuracy cost" in the copy read; these are simulation estimates from the instrumenting runtime, whose default error parameters are listed in Finding 1.

*Structural reading.* Replace "approximate" by "low integrity" and the rules are those of an integrity information-flow type system: no explicit flow low-to-high, no implicit flow through control, an explicit endorsement operator, non-interference modulo endorsement. Memory-safety-critical data (lengths, indices, references) is pinned to the high level by fiat. Curricle (Finding 7) uses the same toolkit - qualifiers plus non-interference - for a different non-standard execution: its paper states that because programmers may declare variables non-idempotent, "its correctness theorem follows from non-interference".

Basis: documentation (paper) + source (checker and runtime); the structural reading is derived.

### 9. Boundary invariants that recur across the three families

Stated as obligations at an interface between code compiled under the discipline and code that is not. Each is derived from the cited mechanism rather than quoted.

1. **Redundancy does not cross a call unless the convention says so.** SWIFT validates arguments before a call, passes one copy, and re-duplicates in the callee; the return value comes back as one copy. A fault in the single copy between validation and re-duplication is in the same unprotected window as a store operand. COAST exposes the same decision as configuration (replication scope rules; directives that re-copy arguments after a call such as `__xMR_AFTER_CALL(fname, x)`), and checks "to make sure all cloned globals are only used in functions that are also protected. If they are not, the compilation will fail".
2. **A check is only as strong as the weakest pass after it.** Whatever inserted the check (source, IR pass, verified pass), each later stage must be either absent, proven to preserve it, or prevented from seeing through it. Finding 3's table is the menu; Finding 4 shows that even a verified pipeline documents where this is not yet discharged.
3. **Restartable regions must not contain a W-A-R on persistent state, and a foreign call is an unknown write.** Alpaca's fallback - any global whose address escapes to an unknown function is treated as W-A-R - is the conservative closure of this rule. External effects (radio, actuators) are not idempotent and cannot be privatized; they need atomic regions or just-in-time checkpoints, which is the problem Ocelot and Curricle address for inputs.
4. **The commit point of a restartable region must be a single atomic persistent write, and recovery must be idempotent.** Both examined runtimes use a pointer flip between two pre-written context records, with a redo log (Alpaca) or a double buffer (Chain) behind it.
5. **Approximate data crossing into a precise interface is an endorsement.** Passing an `@Approx` value to code typed precise requires `endorse`; lengths and indices stay precise.
6. **The guarantee is a property of sets of executions.** "Detects every single fault", "re-execution is unobservable" and "precise results do not depend on approximate data" each relate a standard execution to a family of perturbed ones. A compiler pass preserves such a property only if its correctness argument covers the perturbed executions too; preserving the standard execution alone is insufficient, which is Finding 2 restated.

Basis: derived.

## Boundaries

**Not examined.**

- The body of the CPP 2025 paper (Pesin et al.); the original CFCSS and EDDI articles (Oh, Shirvani, McCluskey, *IEEE Transactions on Reliability* 51(1), 2002; identities confirmed, text not read - the CFCSS algorithm here is as restated by COAST); the DINO paper body (Lucia and Ransford, PLDI 2015); the body of the Ocelot paper and of *Towards a Formal Foundation of Intermittent Computing* (abstracts only).
- Any LLVM-based compiler's output. In particular the behaviour of `launder32`, `barrier32` and `HARDENED_CHECK` under Clang for RISC-V - the configuration OpenTitan targets - was not executed. Rust source-level countermeasures were not compiled.
- Back-end passes after instruction selection (machine CSE, peephole, register-allocation coalescing, link-time optimization) in any compiler; the SWIFT/TAL_FT/COAST "insert late" argument depends on them.
- The Coq sources of the Chamois-Arsene fork (only its generated documentation page was read); the source of COAST's replication passes beyond the build flow, CFCSS documentation and directive list; Mayfly's implementation; TICS and InK.
- Multi-bit upsets, permanent faults, instruction-skip faults at the binary level, radiation or laser test data, and hardware countermeasures.

**Unknown.**

- Whether the Chamois-Arsene countermeasures are intact in the emitted RISC-V assembly for realistic programs. The documentation establishes RTL-level theorems and says only the inter-procedural pass is protected by observations; the authors' 2024 preliminary results reported breakage at `-O1`; no later binary-level evaluation was found.
- Whether the "second test" barrier placement is rewritten into a constant comparison by current Clang, as the OpenTitan header warns it may be. GCC 15.2.0 on x86-64 did not do so.
- The true SWIFT performance figure relative to the best prior single-threaded approach: the fetched copy says 51% in the abstract and 14% in the introduction.
- How Alpaca's precedence test (backward CFG reachability) and alias fallback behave on programs with pointers into NV arrays beyond the cases its artifact exercises.

**Known not to apply.**

- Mayfly does not provide timeliness *types*: the paper describes "a language and runtime" with edge constraints checked by a generated scheduler, and contains no type system. Type-level treatments are Ocelot's annotations and Curricle.
- Mainline CompCert at the pinned commit contains none of the fault-injection hardening passes; they exist only in the fork.
- The GCC probe results do not transfer to other compilers, versions, targets or even other source shapes; a surviving check in one build is not evidence of a preserved countermeasure in general.
- EnerJ's non-interference theorem does not cover programs that use `endorse`.

**Unsupported (by the subject's own statement).**

- OpenTitan `launder32`: "LLVM-specific, and should be considered to be a no-op in every other compiler."
- SWIFT: faults striking a store's address or data register after validation, and opcodes corrupted into stores.
- TAL_FT: faults in code memory or value memory (assumed protected); recovery ("we omit the former, focusing only on" detection).
- Task-based intermittent systems: tasks whose energy demand exceeds one capacitor charge (non-termination by repeated restart).
- EnerJ: any particular approximation behaviour; the language "does not define the particular approximation strategies".

**Attractive conclusions the evidence does not establish.**

- "`volatile` or an inline-assembly barrier makes code fault-resistant." They only keep an instruction sequence in the output of one compiler; they say nothing about whether the sequence detects the fault of interest.
- "A formally verified compiler preserves countermeasures." Mainline CompCert's theorem is about fault-free behaviour; its CSE pass is precisely the kind that merges duplicates. Only passes proven against a fault model, and shielded from later passes, give that property, and the fork's documentation marks where that is incomplete.
- "Task-based or checkpoint-based intermittent systems make programs correct." They make re-execution of *memory* effects idempotent; repeated inputs, outputs and data age are separate properties.
- "The simulation percentages are fault coverage figures." They are exhaustive counts on a six-instruction toy program and illustrate a mechanism only.

## Evidence

All evidence was acquired on 2026-11-19.

### Git sources

Commits are the default-branch heads resolved on the observation date with `git ls-remote https://github.com/<owner>/<repo>.git HEAD`; files were read from archives or raw files at exactly these commits.

| Repository | Commit | Paths and symbols relied on |
|---|---|---|
| `AbsInt/CompCert` | `2685140bf72c959446981fb99b5e44a8975021bc` | `VERSION` (`version=3.18`); `driver/Compiler.v`, definition of the RTL pass sequence (`Tailcall` ... `Constprop`, `CSE`, `Deadcode`, `Unusedglob`, `Allocation`); `backend/CSE.v`, `transf_instr`; absence of `CounterMeasures`/`Iassert`/`EF_observe`/`fsecu`/`RTLfault` in `*.v`, `*.vp`, `*.ml` |
| `llvm/llvm-project` | `ae9b54f0ebfe606123f5a0762bb9cd12cc46fa69` | file header comments of `llvm/lib/Transforms/Scalar/EarlyCSE.cpp` and `llvm/lib/Transforms/Scalar/GVN.cpp`; `llvm/docs/LangRef.md`, section "Volatile Memory Accesses" |
| `lowRISC/opentitan` | `8d89356bbab7287adffec8109732a2b59a589c09` | `sw/device/lib/base/hardened.h`: `hardened_bool_t` comment, `launder32` (comment and body), `barrier32`, `HARDENED_CHECK_`, `ct_cmov32`; `sw/device/lib/base/hardened_asm.h`: `HARDENED_BOOL_TRUE 0x739`, `HARDENED_BOOL_FALSE 0x1d4` |
| `byuccl/coast` | `397a26ecdb01e7c329884d12c9f6bb2a05c3abc9` | `docs/source/cfcss.rst` (algorithm, fan-in problem, buffer-block modification, implementation note); `docs/source/passes.rst` (directives, replication rules, synchronization changes); `docs/source/troubleshooting.rst`; `tests/makefiles/Makefile.compile.x86` (rules `%.clang.bc`, `$(TARGET).lbc`, `$(TARGET).opt.bc`, `%.s`); `projects/` (pass directories `CFCSS`, `dataflowProtection`, `DWC`, `EDDI`, `TMR`) |
| `CMUAbstract/libchain` | `ccf5b5e599269ba48f25684704f1956b62008ec7` | `README.md` (programming interface); `src/chain.c`: `task_prologue`, `transition_to`, `chan_in`, `chan_out`; `src/include/libchain/chain.h`: `context_t`, `SELF_CHAN_IDX_BIT_*` |
| `CMUAbstract/alpaca-pass-oopsla` | `0f63ff73096df4ba98ff5275e5234a276bdb1e73` | `src/AnalyzeTasks.cpp` (`findReadPrecedingWrite`, non-task and unknown-callee fallbacks, `calcCommitSize`); `src/BackwardSearcher.cpp` (`isPreceding`); `src/TransformTasks.cpp` (`insertPreCommit`, `_bak`, `_isDirty`) |
| `CMUAbstract/libalpaca-oopsla` | `1dbcc27cde661b1f7dc9916ec38c92b37859a250` | `src/alpaca.c`: `task_prologue`, `transition_to`, `write_to_gbuf`, `main` |
| `CMUAbstract/ocelot` | `62e0c7f1b8036a253cb4ee1ed8faf3ba2665c925` | `readme.md`; `benchmarks/intermittent.rs` (`Fresh`, `Consistent`, `FreshConsistent`, `atomic_start`, `atomic_end`); `benchmarks/tire/annotated.rs` |
| `sampsyo/enerj` | `a57bd8aad71d46b7ef35eb317ef2ace8bcf706fe` | `src/enerj/PrecisionVisitor.java` (`conditionCheck`, `visitIf`, `visitWhileLoop`, `visitArrayAccess`); `src/enerj/lang/Endorsements.java`; `src/enerj/lang/{Approx,Precise,Top,Context,Approximable}.java`; `src/enerj/rt/PrecisionRuntimeNoisy.java` (default error parameters) |

The Alpaca pass and runtime are the submodules `LLVM` and `AlpacaRuntime/libalpaca` of `CMUAbstract/alpaca-oopsla` (head `c112575a34765f7b1e8a82141afe1ef22377a592`), itself the submodule `ext/alpaca` of the artifact repository `CMUAbstract/alpaca-oopsla2017` (head `a979300cb51409a89b7a776ead8fe50b50711bfd`); the commits above are the heads of the submodule repositories, not gitlink values read from the superprojects.

### Papers and documentation

| Work | Identity | What was read |
|---|---|---|
| Reis, Chang, Vachharajani, Rangan, August. *SWIFT: Software Implemented Fault Tolerance.* CGO 2005, pp. 243-254 | doi:10.1109/CGO.2005.34 | full text, `https://liberty.princeton.edu/Publications/cgo05_swift.pdf` |
| Perry, Mackey, Reis, Ligatti, August, Walker. *Fault-tolerant Typed Assembly Language.* PLDI 2007, pp. 42-53 | doi:10.1145/1250734.1250741 | full text, `https://www.cs.princeton.edu/~dpw/papers/tal_ft-pldi07.pdf` |
| Pesin, Boulmé, Monniaux, Potet. *Formally Verified Hardening of C Programs against Hardware Fault Injection.* CPP 2025, pp. 140-155 | doi:10.1145/3703595.3705880 | identity only; content via the two items below |
| Chamois-Arsene fork documentation, "Version 3.14, Chamois-Arsene fork, 2025-12-06" | `https://certicompil.gricad-pages.univ-grenoble-alpes.fr/Chamois-Arsene/` | full page |
| Boulmé, Monniaux, Pesin, Potet. Talk "Formally verified hardening of C programs against fault injection", 5 June 2024 (25 slides) | `https://vertmo.org/talks/gdrgpl24.pdf` | full slide text |
| Vu, Cohen, De Grandmaison, Guillon, Heydemann. *Reconciling Optimization with Secure Compilation.* PACMPL 5(OOPSLA), 2021 | doi:10.1145/3485519 | abstract (Crossref record) |
| Oh, Shirvani, McCluskey. *Control-flow checking by software signatures* and *Error detection by duplicated instructions in super-scalar processors.* IEEE Trans. Reliability 51(1), 2002, pp. 111-122 and 63-75 | doi:10.1109/24.994926, doi:10.1109/24.994913 | identity only |
| Colin, Lucia. *Chain: Tasks and Channels for Reliable Intermittent Programs.* OOPSLA 2016, pp. 514-530 | doi:10.1145/2983990.2983995 | full text, `https://brandonlucia.com/pubs/chain.pdf` |
| Maeng, Colin, Lucia. *Alpaca: Intermittent Execution without Checkpoints.* PACMPL 1(OOPSLA), 2017 | doi:10.1145/3133920 | full text, `https://brandonlucia.com/pubs/alpaca-preprint.pdf` |
| Van Der Woude, Hicks. *Intermittent Computation without Hardware Support or Programmer Intervention.* OSDI 2016 | ISBN 978-1-931971-33-1 | full text, `https://files.usenix.org/s3fs-public/cdn/osdi16-van-der-woude.pdf` |
| Hester, Storer, Sorber. *Timely Execution on Intermittently Powered Batteryless Sensors.* SenSys 2017 | doi:10.1145/3131672.3131673 | full text (course-hosted copy of the published PDF) |
| Surbatovich, Jia, Lucia. *Automatically Enforcing Fresh and Consistent Inputs in Intermittent Systems.* PLDI 2021 | arXiv:2104.04616 | abstract |
| Surbatovich, Lucia, Jia. *Towards a Formal Foundation of Intermittent Computing.* PACMPL 4(OOPSLA), 2020 | doi:10.1145/3428231 | abstract |
| Surbatovich, Spargo, Jia, Lucia. *A Type System for Safe Intermittent Computing.* PACMPL 7(PLDI), 2023, pp. 736-760 | doi:10.1145/3591250 | full text (author-hosted) |
| Lucia, Ransford. *A Simpler, Safer Programming and Execution Model for Intermittent Systems.* PLDI 2015 | doi:10.1145/2737924.2737978 | identity only |
| Sampson, Dietl, Fortuna, Gnanapragasam, Ceze, Grossman. *EnerJ: Approximate Data Types for Safe and General Low-Power Computation.* PLDI 2011, pp. 164-174 | doi:10.1145/1993498.1993518 | full text, `https://www.cs.cornell.edu/~asampson/media/papers/enerj-pldi2011.pdf` |

Bibliographic fields were checked against the Crossref REST API (`https://api.crossref.org/works/<doi>`). The Ocelot paper is cited by its arXiv identifier because its DOI was not confirmed.

### Execution environment

`gcc (Debian 15.2.0-14) 15.2.0`, `gcc -dumpmachine` = `x86_64-linux-gnu`; Python 3.13.15 (standard library only). All probes are deterministic.

### E1. Redundancy-survival probe (Finding 2.4)

Save the two files below in one directory and run `python3 count_checks.py`. Output is the table in Finding 2.4.

`redundancy_survival.c`:

```c
/* redundancy_survival.c -- do source-level fault-detection redundancies survive
 * a mainstream optimizer?  Each function carries exactly one redundant check
 * that is dead in the fault-free semantics.  Build with:
 *   gcc -S -O<level> redundancy_survival.c -o out.s
 * and count, per function, references to fault_detected in the assembly. */
#include <stdint.h>

extern void fault_detected(void) __attribute__((noreturn));
extern uint32_t sink;

/* Empty inline-asm value barrier: the compiler must assume v is rewritten. */
static inline uint32_t launder(uint32_t v) {
  __asm__ volatile("" : "+r"(v));
  return v;
}

/* (1) EDDI/SWIFT-style duplication written in plain C. */
void dup_plain(uint32_t a, uint32_t b) {
  uint32_t r = a * 3u + b;
  uint32_t r2 = a * 3u + b; /* shadow computation */
  if (r != r2) fault_detected(); /* check before the store leaves the SoR */
  sink = r;
}

/* (2) Fault-attack "double test" written in plain C. */
int dbl_check_plain(uint32_t pin_ok) {
  if (pin_ok != 0x3CA5u) return 0;
  if (pin_ok != 0x3CA5u) fault_detected(); /* redundant re-test */
  return 1;
}

/* (3) Duplication with volatile shadow inputs. */
void dup_volatile(uint32_t a, uint32_t b) {
  volatile uint32_t va = a, vb = b;
  uint32_t r = a * 3u + b;
  uint32_t r2 = va * 3u + vb;
  if (r != r2) fault_detected();
  sink = r;
}

/* (4) Duplication with laundered shadow inputs. */
void dup_barrier(uint32_t a, uint32_t b) {
  uint32_t r = a * 3u + b;
  uint32_t r2 = launder(a) * 3u + launder(b);
  if (r != r2) fault_detected();
  sink = r;
}

/* (5) Double test, barrier on the FIRST test (compiler never learns the fact). */
int dbl_check_barrier_first(uint32_t pin_ok) {
  if (launder(pin_ok) != 0x3CA5u) return 0;
  if (pin_ok != 0x3CA5u) fault_detected();
  return 1;
}

/* (6) Double test, barrier on the SECOND test (fact already learned). */
int dbl_check_barrier_second(uint32_t pin_ok) {
  if (pin_ok != 0x3CA5u) return 0;
  if (launder(pin_ok) != 0x3CA5u) fault_detected();
  return 1;
}
```

`count_checks.py`:

```python
#!/usr/bin/env python3
"""Count surviving redundant checks per function and optimization level."""
import re, subprocess, sys

SRC = "redundancy_survival.c"
FUNCS = ["dup_plain", "dbl_check_plain", "dup_volatile", "dup_barrier",
         "dbl_check_barrier_first", "dbl_check_barrier_second"]
LEVELS = ["-O0", "-O1", "-O2", "-O3", "-Os"]

def split_functions(asm):
    out, cur = {}, None
    for line in asm.splitlines():
        m = re.match(r"^([A-Za-z_][A-Za-z0-9_]*):", line)
        if m and m.group(1) in FUNCS:
            cur = m.group(1); out[cur] = []
        elif re.match(r"^\s+\.size\s", line):
            cur = None
        elif cur:
            out[cur].append(line)
    return out

print(subprocess.run(["gcc", "--version"], capture_output=True, text=True).stdout.splitlines()[0])
rows = {}
for lv in LEVELS:
    asm = subprocess.run(["gcc", "-S", lv, SRC, "-o", "-"], capture_output=True, text=True, check=True).stdout
    for fn, body in split_functions(asm).items():
        txt = "\n".join(body)
        traps = len(re.findall(r"\b(?:call|jmp)\s+fault_detected", txt))
        cmps = len(re.findall(r"^\s+cmp[lq]?\s", txt, flags=re.M))
        const_cmp = len(re.findall(r"^\s+cmp[lq]?\s+\$15525,", txt, flags=re.M))  # 0x3CA5
        const_mov = len(re.findall(r"^\s+mov[lq]?\s+\$15525,", txt, flags=re.M))
        rows.setdefault(fn, []).append((lv, traps, cmps, const_cmp, const_mov))
print(f"{'function':26s} " + " ".join(f"{lv:>12s}" for lv in LEVELS))
print(f"{'':26s} " + " ".join(f"{'trap/cmp':>12s}" for _ in LEVELS))
for fn in FUNCS:
    print(f"{fn:26s} " + " ".join(f"{t:>6d}/{c:<5d}" for (_, t, c, _, _) in rows[fn]))
print()
print("dbl_check_barrier_second at -O2:")
asm = subprocess.run(["gcc", "-S", "-O2", SRC, "-o", "-"], capture_output=True, text=True, check=True).stdout
for l in split_functions(asm)["dbl_check_barrier_second"]:
    if l.strip() and not l.strip().startswith((".cfi", ".p2align", ".LF")):
        print("   ", l.strip())
```

### E2. Single-bit-upset simulation (Finding 2.5)

Run `python3 swift_fault_sim.py`. Output is the block in Finding 2.5.

```python
#!/usr/bin/env python3
"""swift_fault_sim.py -- exhaustive single-bit-upset simulation of a toy register
machine, comparing (a) an unprotected program, (b) the same program after a
SWIFT-style duplicate-and-compare transformation, and (c) program (b) after a
fault-free-semantics-preserving optimizer (local value numbering / CSE, copy
propagation, trivially-true check folding, dead code elimination).

Fault model (SEU, as in SWIFT section 3 / TAL_FT rule reg-zap restricted to one
bit): exactly one bit of one register flips at one instruction boundary.
Memory (inputs and the output cell) is assumed ECC-protected and is not faulted.
Outcome classes: CORRECT (output equals fault-free output), DETECTED (a check
fired), SDC (silent data corruption: wrong address/value stored or no store)."""
import itertools

W = 8                       # register width in bits
MASK = (1 << W) - 1

# ---- instruction set -------------------------------------------------------
# ("ld", rd, addr)          rd <- MEM[addr]            (addr is a constant)
# ("li", rd, imm)           rd <- imm
# ("mul3", rd, rs)          rd <- 3*rs
# ("add", rd, rs, rt)       rd <- rs + rt
# ("mov", rd, rs)           rd <- rs
# ("chk", rs, rt)           if rs != rt: DETECTED
# ("st", ra, rv)            OUT[ra] <- rv              (leaves the sphere of replication)

NOFT = [
    ("ld", "a", 0), ("ld", "b", 1), ("li", "p", 0x40),
    ("mul3", "t", "a"), ("add", "r", "t", "b"),
    ("st", "p", "r"),
]

def swiftify(prog):
    """Duplicate every register computation into a primed shadow register and
    validate the operands of every store immediately before it."""
    out = []
    for ins in prog:
        op = ins[0]
        if op == "st":
            _, ra, rv = ins
            out += [("chk", rv, rv + "'"), ("chk", ra, ra + "'"), ins]
        else:
            out.append(ins)
            if op in ("ld", "li"):
                out.append((op, ins[1] + "'", ins[2]))
            else:
                out.append((op,) + tuple(x + "'" for x in ins[1:]))
    return out

def optimize(prog):
    """A conventional, fault-free-correct optimizer: local value numbering with
    copy propagation, folding of checks whose operands have the same value
    number, then dead-code elimination."""
    vn, canon, out = {}, {}, []          # expr -> canonical reg ; reg -> canonical reg
    def c(r): return canon.get(r, r)
    for ins in prog:
        op = ins[0]
        if op in ("ld", "li"):
            key = (op, ins[2])
            if key in vn: canon[ins[1]] = vn[key]          # redundant load/const: reuse
            else: vn[key] = ins[1]; out.append(ins)
        elif op in ("mul3", "add", "mov"):
            args = tuple(c(x) for x in ins[2:])
            key = (op,) + args
            if op == "mov": canon[ins[1]] = args[0]
            elif key in vn: canon[ins[1]] = vn[key]        # common subexpression
            else: vn[key] = ins[1]; out.append((op, ins[1]) + args)
        elif op == "chk":
            a, b = c(ins[1]), c(ins[2])
            if a != b: out.append(("chk", a, b))           # same value number => always true => deleted
        elif op == "st":
            out.append(("st", c(ins[1]), c(ins[2])))
    live, kept = set(), []
    for ins in reversed(out):                              # DCE
        if ins[0] in ("st", "chk"):
            live.update(ins[1:]); kept.append(ins)
        elif ins[1] in live:
            live.discard(ins[1]); live.update(x for x in ins[2:] if isinstance(x, str)); kept.append(ins)
    return list(reversed(kept))

def regs_of(prog):
    rs = []
    for ins in prog:
        for x in ins[1:]:
            if isinstance(x, str) and x not in rs: rs.append(x)
    return rs

def run(prog, mem, fault=None):
    """fault = (boundary index, register, bit) or None."""
    R = {r: 0 for r in regs_of(prog)}
    out = {}
    for i, ins in enumerate(prog + [("end",)]):
        if fault and fault[0] == i:
            R[fault[1]] ^= 1 << fault[2]
        op = ins[0]
        if op == "end": break
        if op == "ld": R[ins[1]] = mem[ins[2]] & MASK
        elif op == "li": R[ins[1]] = ins[2] & MASK
        elif op == "mul3": R[ins[1]] = (3 * R[ins[2]]) & MASK
        elif op == "add": R[ins[1]] = (R[ins[2]] + R[ins[3]]) & MASK
        elif op == "mov": R[ins[1]] = R[ins[2]]
        elif op == "chk":
            if R[ins[1]] != R[ins[2]]: return "DETECTED"
        elif op == "st": out[R[ins[1]]] = R[ins[2]]
    return tuple(sorted(out.items()))

def campaign(name, prog, inputs):
    tally = {"CORRECT": 0, "DETECTED": 0, "SDC": 0}
    sdc_sites = {}
    for mem in inputs:
        gold = run(prog, mem)
        for i, r, b in itertools.product(range(len(prog) + 1), regs_of(prog), range(W)):
            res = run(prog, mem, (i, r, b))
            k = "DETECTED" if res == "DETECTED" else ("CORRECT" if res == gold else "SDC")
            tally[k] += 1
            if k == "SDC":
                nxt = prog[i] if i < len(prog) else ("end",)
                sdc_sites[(i, r, nxt)] = sdc_sites.get((i, r, nxt), 0) + 1
    n = sum(tally.values())
    print(f"{name:22s} insns={len(prog):2d} regs={len(regs_of(prog)):2d} injections={n:5d} "
          f"CORRECT={tally['CORRECT']:5d} DETECTED={tally['DETECTED']:5d} SDC={tally['SDC']:5d} "
          f"({100.0 * tally['SDC'] / n:5.2f}% SDC)")
    return sdc_sites

if __name__ == "__main__":
    inputs = [{0: a, 1: b} for a, b in [(5, 7), (0, 0), (200, 99), (85, 170)]]
    SW = swiftify(NOFT)
    OPT = optimize(SW)
    print("NOFT            :", NOFT)
    print("SWIFT           :", SW)
    print("optimize(SWIFT) :", OPT)
    print("optimize(SWIFT) == NOFT :", OPT == NOFT)
    for mem in inputs:                                   # the optimizer is correct in the fault-free semantics
        assert run(NOFT, mem) == run(SW, mem) == run(OPT, mem)
    print("fault-free outputs identical for all three programs on all inputs: True")
    print()
    campaign("NOFT", NOFT, inputs)
    sites = campaign("SWIFT", SW, inputs)
    campaign("optimize(SWIFT)", OPT, inputs)
    print()
    print("SWIFT residual SDC sites (boundary index, register, next instruction) -> count:")
    for k in sorted(sites): print("   ", k, "->", sites[k])
```

### E3. CFCSS aliasing model (Finding 5)

Run `python3 cfcss_alias.py`. Output is the block in Finding 5.

```python
#!/usr/bin/env python3
"""cfcss_alias.py -- executable model of CFCSS signature checking.

Per-block compile-time data: unique signature s[v]; signature difference
d[v] = s[base(v)] xor s[v], where base(v) is one designated predecessor; and,
for predecessors of branch-fan-in blocks, a run-time adjuster
D[u] = s[u] xor s[base(v)].  Run-time state: G (signature register) and D.
On entry to block v:   G <- G xor d[v]            (single predecessor)
                       G <- G xor d[v] xor D      (branch-fan-in block)
then trap if G != s[v]; before leaving block u, D <- D[u].

The script enumerates every ordered pair (u, v) of blocks and reports whether a
control transfer from the end of u to the entry of v passes the check."""
import itertools

def build(edges, sig, base_choice):
    nodes = sorted(sig)
    preds = {v: [u for (u, w) in edges if w == v] for v in nodes}
    base = {v: (base_choice.get(v, preds[v][0]) if preds[v] else None) for v in nodes}
    d = {v: (sig[base[v]] ^ sig[v]) if base[v] is not None else 0 for v in nodes}
    fanin = {v for v in nodes if len(preds[v]) > 1}
    D, conflict = {}, []
    for u in nodes:
        need = {sig[u] ^ sig[base[v]] for (x, v) in edges if x == u and v in fanin}
        if len(need) > 1: conflict.append(u)
        D[u] = next(iter(need)) if need else 0
    return nodes, preds, d, fanin, D, conflict

def passes(u, v, sig, d, fanin, D):
    G = sig[u]                       # G holds s[u] while u executes
    G ^= d[v]
    if v in fanin: G ^= D[u]
    return G == sig[v]

def report(title, edges, sig, base_choice):
    nodes, preds, d, fanin, D, conflict = build(edges, sig, base_choice)
    print(title)
    print("   fan-in blocks:", sorted(fanin), " adjuster conflicts at:", conflict)
    legal_ok = all(passes(u, v, sig, d, fanin, D) for (u, v) in edges)
    undetected = [(u, v) for u, v in itertools.product(nodes, nodes)
                  if (u, v) not in edges and preds[v] and passes(u, v, sig, d, fanin, D)]
    illegal = [(u, v) for u, v in itertools.product(nodes, nodes) if (u, v) not in edges and preds[v]]
    print(f"   all {len(edges)} legal edges pass: {legal_ok}")
    print(f"   illegal block-entry transfers: {len(illegal)}  undetected: {undetected}")

if __name__ == "__main__":
    # entry block 0 fans out to 1, 2, 3; block 2 has two successors that are both fan-in blocks.
    E = [(0, 1), (0, 2), (0, 3), (1, 4), (2, 4), (2, 5), (3, 5), (4, 6), (5, 6)]
    S = {0: 0x11, 1: 0x22, 2: 0x47, 3: 0x8B, 4: 0x1D, 5: 0xE2, 6: 0x74}
    report("A. original scheme, shared predecessor 2 chosen as base of both fan-in blocks 4 and 5",
           E, S, {4: 2, 5: 2, 6: 4})
    report("B. original scheme, bases 1 (for 4) and 3 (for 5): block 2 needs two different adjusters",
           E, S, {4: 1, 5: 3, 6: 4})
    # C: buffer block 7 inserted on edge 2->5 (single predecessor, no adjuster needed on entry)
    E2 = [(0, 1), (0, 2), (0, 3), (1, 4), (2, 4), (2, 7), (7, 5), (3, 5), (4, 6), (5, 6)]
    S2 = dict(S); S2[7] = 0xB8
    report("C. buffer block 7 inserted on edge 2->5 (bases: 4<-1, 5<-7, 6<-4)",
           E2, S2, {4: 1, 5: 7, 6: 4})
```

### E4. Power-failure injection model (Finding 7.4)

Run `python3 war_sim.py` (about five seconds). Output is the block in Finding 7.4.

```python
#!/usr/bin/env python3
"""war_sim.py -- exhaustive power-failure injection for one task that performs
`x = x + 1` on a non-volatile (NV) variable, under three recovery disciplines.

A program is a list of micro-steps; power may fail before any micro-step.  A
failure erases volatile state (V) and control restarts at the discipline's
recovery point.  NV state persists.  Every schedule with at most K failures is
enumerated; the set of final values of NV x is reported (the continuously
powered result is x == 1).

  naive    : restart the task from its beginning; NV is written in place.
  ratchet  : idempotent sections -- a checkpoint of volatile state is committed
             between the NV read and the NV write, so no section contains a
             write-after-read of the same NV address.
  alpaca   : task-private copy + redo-log commit modelled on the libalpaca
             runtime: transition_to() sets needCommit in the inactive context
             and flips the current-context pointer with ONE NV write;
             task_prologue() replays the commit list using the NV cursor
             gv_index; an interrupted commit is resumed after reboot.
"""
import itertools

K = 3

def explore(make):
    """make() -> (nv, steps, recover); steps are functions(nv, v) -> next pc or None(done);
    recover(nv) -> pc to resume at after a power failure."""
    finals, schedules = set(), 0
    # A schedule is a tuple of global step counts at which power fails.
    def run(fail_at):
        nv, steps, recover = make()
        v, pc, count, fails = {}, recover(nv), 0, list(fail_at)
        while pc is not None:
            if fails and count == fails[0]:
                fails.pop(0); v = {}; pc = recover(nv); count += 1
                continue
            pc = steps[pc](nv, v); count += 1
            if count > 10_000: raise RuntimeError("no progress")
        return nv["x"], count
    _, base_len = run(())
    horizon = base_len * (K + 1) + 8
    for k in range(K + 1):
        for fail_at in itertools.combinations(range(horizon), k):
            x, _ = run(fail_at)
            finals.add(x); schedules += 1
    return finals, schedules

# ---- naive: in-place NV update, restart task from the top ---------------------
def naive():
    nv = {"x": 0, "task": "inc"}
    def s0(nv, v): v["t"] = nv["x"]; return 1                 # NV read
    def s1(nv, v): nv["x"] = v["t"] + 1; return 2             # NV write (write-after-read)
    def s2(nv, v): nv["task"] = "done"; return None           # atomic transition
    def recover(nv): return None if nv["task"] == "done" else 0
    return nv, [s0, s1, s2], recover

# ---- ratchet-style: checkpoint volatile state between the read and the write --
def ratchet():
    nv = {"x": 0, "ckpt": ("sec0", None)}
    def s0(nv, v): v["t"] = nv["x"]; return 1                 # section 0: read only
    def s1(nv, v): nv["ckpt"] = ("sec1", v["t"]); return 2    # atomic checkpoint of volatile t
    def s2(nv, v): nv["x"] = v["t"] + 1; return 3             # section 1: write only (idempotent)
    def s3(nv, v): nv["ckpt"] = ("done", None); return None
    def recover(nv):
        tag, t = nv["ckpt"]
        if tag == "done": return None
        if tag == "sec1": return 4                            # restore volatile t, then resume at s2
        return 0
    def s4(nv, v): v["t"] = nv["ckpt"][1]; return 2           # restore step
    return nv, [s0, s1, s2, s3, s4], recover

# ---- alpaca-style: privatization + two-phase redo commit ----------------------
def alpaca():
    nv = {"x": 0, "x_priv": 0, "cur": 0,
          "ctx": [{"task": "inc", "needCommit": 0}, {"task": None, "needCommit": 0}],
          "num_dirty": 0, "gv_index": 0, "list": [None]}
    # task body (pcs 0..4)
    def t0(nv, v): nv["x_priv"] = nv["x"]; return 1                    # privatize at task start
    def t1(nv, v): v["t"] = nv["x_priv"]; return 2
    def t2(nv, v): nv["x_priv"] = v["t"] + 1; return 3                 # W-A-R now hits the private copy only
    def t3(nv, v): nv["list"][nv["num_dirty"]] = ("x_priv", "x"); return 4   # write_to_gbuf: record
    def t4(nv, v): nv["num_dirty"] = nv["num_dirty"] + 1; return 5           # write_to_gbuf: count++
    # transition_to(done) (pcs 5..7)
    def t5(nv, v): nv["ctx"][1 - nv["cur"]]["task"] = "done"; return 6
    def t6(nv, v): nv["ctx"][1 - nv["cur"]]["needCommit"] = 1; return 7
    def t7(nv, v): nv["cur"] = 1 - nv["cur"]; return 8                 # single atomic pointer flip
    # task_prologue() (pcs 8..15); also the reboot entry point
    def p8(nv, v): return 9 if nv["ctx"][nv["cur"]]["needCommit"] else 14
    def p9(nv, v): return 10 if nv["gv_index"] < nv["num_dirty"] else 11
    def p10(nv, v):
        src, dst = nv["list"][nv["gv_index"]]; nv[dst] = nv[src]; return 16   # memcpy
    def p16(nv, v): nv["gv_index"] = nv["gv_index"] + 1; return 9
    def p11(nv, v): nv["num_dirty"] = 0; return 12
    def p12(nv, v): nv["gv_index"] = 0; return 13
    def p13(nv, v): nv["ctx"][nv["cur"]]["needCommit"] = 0; return 15
    def p14(nv, v): nv["num_dirty"] = 0; return 15
    def p15(nv, v): return None if nv["ctx"][nv["cur"]]["task"] == "done" else 0   # jump to current task
    steps = [t0, t1, t2, t3, t4, t5, t6, t7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
    def recover(nv): return 8                                          # main(): task_prologue(); jump
    return nv, steps, recover

if __name__ == "__main__":
    for name, mk in (("naive", naive), ("ratchet-style", ratchet), ("alpaca-style", alpaca)):
        finals, n = explore(mk)
        print(f"{name:14s} schedules(<= {K} failures)={n:7d}  final NV x in {sorted(finals)}"
              f"  {'CONSISTENT' if finals == {1} else 'INCONSISTENT'}")
```

## Revalidation

Cheapest discriminating checks, in order of cost:

1. **Compiler behaviour (minutes).** Re-run E1 with the compiler of interest: replace `gcc` in `count_checks.py`, and for a non-x86 target adapt the two regular expressions that count trap references and compare instructions. The finding "plain-C redundancy is deleted at `-O1` and above" is falsified for that compiler if `dup_plain` or `dbl_check_plain` keeps a trap reference. For Clang, additionally inspect `dbl_check_barrier_second` for a comparison against a materialized constant, which is the failure OpenTitan documents.
2. **Mechanism models (seconds).** Re-run E2, E3, E4; outputs must match byte for byte. They need re-reading, not re-running, if the cited algorithms change.
3. **Mainline CompCert still lacks hardening passes.** In a checkout of `AbsInt/CompCert`, search `*.v`, `*.vp`, `*.ml` for `CounterMeasures`, `Iassert`, `EF_observe`, `fsecu`. Any hit changes the "known not to apply" entry. Confirm `backend/CSE.v` `transf_instr` still rewrites a known right-hand side to `Omove`, and that `driver/Compiler.v` still orders `CSE` before `Deadcode` before `Allocation`.
4. **Chamois-Arsene status.** Re-read the fork's documentation page: the version line, the sentence stating that "only the interprocedural CFI is protected by observations", the pass table's robustness column, and the default values of the `-fsecu-*` options. If the CPP 2025 paper becomes retrievable, compare its Definition 4.3 and Theorem 4.4 with the talk's formulation quoted in Finding 4.
5. **OpenTitan barriers.** Diff `sw/device/lib/base/hardened.h` against the pinned commit around `launder32`, `barrier32` and `HARDENED_CHECK_`; the claims here depend on the `asm volatile("" : "+r"(val))` body and on the comment declaring the implementation LLVM-specific.
6. **Intermittent runtimes.** In `libalpaca` check that `transition_to` still performs exactly one write to `curctx` after preparing the inactive context and that `task_prologue` still advances the non-volatile `gv_index` after each copy; in `libchain` check `transition_to` and the `SWPB` swap in `task_prologue`. A change to either ordering invalidates the corresponding row of Finding 7.3 and the model in E4.
7. **EnerJ rules.** In `src/enerj/PrecisionVisitor.java` confirm the diagnostics `condition.type.incompatible` and `array.index.approx` are still reported from the condition and array-access visitors.

What cannot be revalidated cheaply: the fault-coverage and overhead numbers quoted from SWIFT and TAL_FT (they require the original compilers and Itanium-era infrastructure), and any claim about LLVM back-end passes preserving late-inserted redundancy (this needs a per-target, per-version inspection of emitted code or a fault-injection campaign).
