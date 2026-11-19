# Proof-Carrying Syscall Admission, Kernel-Resident Checkers, and Ring Policies

## Summary

Kernel-resident admission of untrusted code and asynchronous I/O policies faces an intrinsic trust-versus-complexity tension: in-kernel static analyzers and type-safe runtimes either inflate the Ring-0 trusted computing base (TCB) to tens of thousands of lines and suffer path-explosion denial-of-service (`kernel/bpf/verifier.c` at 24,331 lines with a 1,000,000-instruction complexity cap), or trust an off-kernel compiler and cryptographic signature chain (SPIN Modula-3 object signing, Singularity MSIL-to-native Bartok compilation). Proof-Carrying Code (PCC) and Witness-Carrying Abstract Interpretation invert this workload split by shifting synthesis—weak topological orderings, widening/narrowing fixpoints, SAT/SMT solving, and register-level verification—into untrusted user space while shrinking the kernel-resident checker to a sub-2-KLoC, linear-time, deterministic validator.

Three complementary micro-checker architectures bound the Ring-0 TCB without sacrificing expressiveness:
1. **Binary Proof-DAG Bytecode (`mm0-c`, 1,227 LOC across `main.c` + `types.c` + `verifier.c`)**: separates human-auditable specifications from pointer-linked `.mmb` proof streams with `O(1)` header offset lookup, 55-bit bound-variable dependency bitmasks (`TYPE_DEPS_MASK`), and stack/heap replay opcodes suited to Foundational PCC machine-word step-indexed safety proofs.
2. **Hint-Guided Clause Checkers (`lrat-check.c`, 509 LOC)**: eliminates unit-propagation search by attaching explicit clause-ID dependency lists (`getHints`), verifying bitvector/safety UNSAT obligations in a single deterministic linear sweep.
3. **Witness-Carrying Zone Invariants (`PCC-AI`)**: replaces in-kernel Bourdoncle WTO fixpoint iteration (as in PREVAIL's `ZoneDomain` SplitDBM) with a single non-iterative check over $|E|$ CFG edges against user-supplied cut-point invariants, preventing exponential branch-diamond blowup ($2^{20}$ states vs. 41 edge checks at $k=20$).

Beyond packet filters, applying proof-carrying admission to zero-copy `io_uring` rings, userspace-managed DMA/IOMMU scatter-gather rings, and GPU compute shaders requires enforcing **temporal linear ownership** and **assumption-certificate binding**. Static `io_uring` restriction masks (`IORING_REGISTER_RESTRICTIONS`) whitelist only stateless opcodes and SQE flags, leaving shared-memory SQE TOCTOU/double-fetch races and linked-chain invariants unaddressed. Furthermore, when any admitted capability relies on mutable platform assumptions (microcode revisions, speculative execution mitigations, or endorsement roots), revocation must execute synchronously across a four-step quiescent barrier—atomic epoch flip, in-flight SQE/DMA drain, synchronous IOTLB invalidation, and post-order capability deletion modeled after seL4's `cteRevoke`—before physical frames are recycled.

## Applicability

This report characterizes and compares kernel extension safety architectures, proof-checking kernels, and asynchronous zero-copy admission mechanisms across the following concrete subjects pinned in `REPORT.json`:

- **Linux Kernel (`torvalds/linux`, `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`) and `axboe/liburing` (`a10946dc51eeababc48ee10baf0d17489f647a80`)**: Specifically `kernel/bpf/verifier.c` and `include/linux/bpf.h` for in-kernel abstract/path-sensitive eBPF verification, and `include/uapi/linux/io_uring.h` + `io_uring/register.c` for `IORING_REGISTER_RESTRICTIONS`.
- **PREVAIL (`vbpf/prevail`, `169eb5d6f48a59ffe4e902e977ae4e387f2b4e49`, PLDI 2019 `doi:10.1145/3314221.3314590`)**: User-space Zone-domain abstract interpretation over eBPF CFGs via Bourdoncle Weak Topological Ordering (`src/cfg/wto.hpp`) and SplitDBM (`src/crab/zone_domain.hpp`).
- **Kernel-Sized Verification Checkers**: `digama0/mm0` (`0d414c0bfdaaeb7fea571895127abc1fa5a3d956`, `mm0-c`), `marijnheule/drat-trim` (`2e3b2dc0ecf938addbd779d42877b6ed69d9a985`, `lrat-check.c`), and `jrh13/hol-light` (`6dbb775efdff7f75aa20006532bf6336bc645861`, `fusion.ml`), evaluated as models for Ring-0 admission checkers rather than assuming existing kernel patches in those upstream repositories.
- **Historical & Verified OS Architectures**: SPIN (Bershad et al., SOSP 1995 `doi:10.1145/224056.224077`), Microsoft Singularity OS (Fähndrich et al., EuroSys 2006 `doi:10.1145/1217935.1217953`), Necula PCC (POPL 1997 `doi:10.1145/263699.263712`), Appel & McAllester Foundational PCC (TOPLAS 2001 `doi:10.1145/504709.504712`), and seL4 (`seL4/seL4`, `08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`, SOSP 2009 `doi:10.1145/1629575.1629596`) `cteRevoke` (`src/object/cnode.c`).

Findings concerning `mm0-c`, `lrat-check.c`, and `fusion.ml` describe their verified upstream source architectures combined with **derived** engineering constraints for Ring-0 deployment (kernel-heap bounds, non-blocking execution, and memory isolation). Execution data from Probe A reflects an isolated Python 3.13.15 model of path explosion, interval/zone witness validation, and post-order capability revocation, not a live Linux kernel module benchmark.

## Findings

### 1. Kernel Extension and Admission TCB Taxonomy

Basis: source + normative + derived (verified directly against `torvalds/linux`, `vbpf/prevail`, `digama0/mm0`, `marijnheule/drat-trim`, `jrh13/hol-light`, `seL4/seL4`, and primary proceedings for SPIN, Singularity, Necula PCC, and Appel-McAllester FPCC).

Kernel admission architectures divide along three axes: **who synthesizes the safety proof** (trusted compiler, in-kernel analyzer, or untrusted producer), **what belongs to the Ring-0 TCB**, and **whether checking complexity can trigger algorithmic denial-of-service**.

| System / Mechanism | Core Admission Paradigm | Ring-0 TCB Substrate | Checking Complexity | Loop & Termination Handling | Revocation / Retraction Mechanism | Primary Soundness / DoS Risk |
|---|---|---|---|---|---|---|
| **Linux eBPF Verifier** (`torvalds/linux` `kernel/bpf/verifier.c`) | In-kernel abstract + path-sensitive symbolic state pruning | 24,331-LOC C verifier + JIT backend + helper contracts | Exponential worst-case bounded at `1,000,000` insns (`BPF_COMPLEXITY_LIMIT_INSNS`) | Bounded loops, `bpf_loop`, iterators (`BPF_COMPLEXITY_LIMIT_JMP_SEQ = 8192`) | FD release / RCU grace period on prog detach; no assumption-cert tree | Verifier bug = Ring-0 RCE; path-explosion false rejections |
| **PREVAIL** (`vbpf/prevail`) | Bourdoncle WTO + SplitDBM Zone abstract interpretation | ~10+ KLoC C++ analyzer + ELF loader (if in-kernel) | Polynomial typical ($O(\|V\| \cdot n^3)$ DBM ops), unbounded worst-case widening steps | Native arbitrary loops via WTO widening + narrowing | Not modeled inside static verifier | Abstract transformer soundness + C++ heap allocation |
| **SPIN** (Bershad et al., SOSP 1995) | Language type safety (Modula-3) + signed compiler objects | Modula-3 compiler/linker + RT runtime + GC + dispatcher | Load-time signature check + dynamic link | Unbounded (runtime CPU preemption / thread timers) | Guarded event-handler uninstall + `Domains` namespace unlink | Trusted compiler/linker compromise; GC pauses in kernel |
| **Singularity** (Fähndrich et al., EuroSys 2006) | Closed-world SIPs + linear `ExHeap` + static `contract` FSMs | Bartok MSIL->x86 AOT compiler + typed runtime + kernel | Compile-time ownership & protocol FSM checking | Unrestricted inside isolated SIP memory | Channel close / SIP process termination | Compiler/MSIL verification bugs; closed-world code updates |
| **Classic PCC** (Necula, POPL 1997) | Trusted VCGen emits proof obligation; LF typechecker verifies proof | Machine decoder + VCGen (~thousands LOC) + LF checker | Linear in proof term size (often large without sharing) | Loop invariants supplied in annotations | Capability/handle revocation external to proof check | Soundness of trusted VCGen & safety-policy axioms |
| **Foundational PCC** (Appel & McAllester, TOPLAS 2001) | Machine semantics in higher-order logic; step-indexed invariants | Tiny FOL/HOL kernel + raw ISA instruction table | Linear/polynomial in proof term check | Induction over step index $k \ge 0$ & explicit invariants | Explicit precondition/assumption predicates in theorem | Proof size unless compressed via DAG sharing |
| **MM0 `.mmb` Checker** (`digama0/mm0` `mm0-c`) | Untrusted prover compiles proof to RPN bytecode DAG over fixed sorts | 1,227 LOC C (`main.c` 79 + `types.c` 329 + `verifier.c` 819) | Linear $O(\|\text{stream}\|)$ single-pass stack/heap execution | Explicit induction axioms in `.mm0` spec | External; checks validity of `|- theorem` against spec hash | Pre-allocated stack/heap bounds (`STACK_SIZE`) & untrusted parser of `.mm0` text if included |
| **LRAT Checker** (`marijnheule/drat-trim` `lrat-check.c`) | Untrusted solver emits CNF UNSAT proof with explicit clause-ID hints | 509 LOC C (`lrat-check.c`) | Strictly linear $O(\sum \|\text{hints}\|)$ unit propagation | Bounded bitvector unrolling / finite inductive steps | External | Integer overflow / allocation bounds in `realloc` if unbounded |
| **LCF Micro-Kernel** (`jrh13/hol-light` `fusion.ml`) | Abstract `type thm` enforcing forward inference rules in memory | 680 LOC OCaml (`module type Hol_kernel`) | Proportional to inference steps replayed dynamically | Explicit induction theorems | External | Requires OCaml runtime + GC; unsuitable bare in Ring 0 without compilation |

#### SPIN vs. Singularity: Language Capabilities vs. Kernel-Resident Proof Checking

SPIN (Bershad et al., SOSP 1995) demonstrated that moving extensions into the kernel address space collapses IPC/trap overhead by replacing MMU boundary crossings with procedure calls, guarded by Modula-3 strong typing, fine-grained `Domains` capability linking, and dynamic event dispatchers (`guard` predicates routing events to handlers). However, SPIN's safety invariant rests directly on trusting the Modula-3 compiler and digital signatures over compiled object files (`safe` vs. `unsafe` object files), which prohibits arbitrary untrusted native binaries or third-party toolchains from compiling extensions directly.

Microsoft Singularity (Fähndrich et al., EuroSys 2006) addressed SPIN's shared-heap entanglement by forbidding shared mutable memory between Software-Isolated Processes (SIPs) and introducing two complementary static checks:
1. **Linear `ExHeap` ownership**: messages exchanged across IPC channels live in an exchange heap governed by a strict single-owner linear discipline (`T* in ExHeap`), enabling zero-copy pointer handoff across SIPs with static compile-time verification that the sender retains zero aliases after `Send`.
2. **Statically checked channel `contract` state machines**: every bidirectional channel obeys a deterministic finite protocol automaton (`state`, `in message`, `out message`, `-> next_state`) verified at compile time for both endpoint duality and absence of dangling obligations before a SIP starts.

Critically, Singularity still requires trusting the Bartok compiler and MSIL bytecode verifier inside the OS distribution boundary, and forbids dynamic code loading inside an already-running SIP ("closed-world" invariant). Kernel-resident proof checkers eliminate that compiler trust requirement: any untrusted compiler, Rust/C frontend, or SMT/abstract-interpretation engine may optimize arbitrarily as long as it attaches a machine-checkable witness accepted by a tiny Ring-0 verifier.

### 2. Foundational vs. Type-Specialized PCC: Step-Indexed Machine-Word Semantics

Basis: normative + derived (Necula POPL 1997 `doi:10.1145/263699.263712`; Appel & McAllester TOPLAS 2001 `doi:10.1145/504709.504712`).

In Necula's original Proof-Carrying Code (POPL 1997), an untrusted producer submits native machine code paired with loop invariants, and the kernel executes a trusted **Verification Condition Generator (VCGen)** that symbolically walks the binary, substitutes loop invariants, and emits a first-order logic safety predicate checked by an LF (Edinburgh Logical Framework) typechecker. While LF checking is small, VCGen itself encodes instruction semantics, calling conventions, register-liveness assumptions, and memory-aliasing rules—meaning a bug in VCGen or a subtle mismatch in its hardcoded typing axioms breaks kernel safety.

Appel and McAllester's **Foundational Proof-Carrying Code (FPCC)** (TOPLAS 2001) strips VCGen and all high-level type systems out of the kernel TCB. Instead, the kernel logic specifies only:
1. **Operational ISA Step Relation** $\text{step}(s, s')$ directly over raw machine states $s = (\text{pc}, R, M)$ where words are bitvectors/integers in $[0, 2^{64})$ and instructions are decoded purely relationally (`decode(M[\text{pc}])`).
2. **Concrete Safety Predicate** $\text{safe}(s)$ (e.g., $\text{pc}$ points to readable/executable aligned instruction, all memory reads/writes target caller-permitted capability ranges, no privileged traps).
3. **Step-Indexed Semantic Types** $(k, v) \in \llbracket \tau \rrbracket$: a value $v$ belongs to type $\tau$ *for $k$ future machine execution steps* ($k \in \mathbb{N}$).

The key mathematical problem FPCC solved—and why step-indexing became foundational for verifying zero-copy callbacks and closure tables—is **contravariant circularity** in untyped machine code. A callback pointer or ring-handler table $\tau = \mu \alpha.\; (\alpha \to \text{unit})$ stores code pointers whose preconditions reference the very type $\tau$ being defined, creating a cardinality paradox if modeled naively in set theory. Step-indexing stratifies semantic membership by remaining execution budget $k$:

$$(k, \text{pc}) \in \llbracket \tau_1 \to \tau_2 \rrbracket \iff \forall j < k,\; \forall s.\; \bigl((j, R_{\text{arg}}) \in \llbracket \tau_1 \rrbracket \land s.\text{pc} = \text{pc}\bigr) \implies \text{safe}_j(s)$$

Because recursive unfolding strictly decrements the step index ($j < k$, guaranteeing downward closure: $k' \le k \land (k, v) \in \llbracket \tau \rrbracket \implies (k', v) \in \llbracket \tau \rrbracket$), fixpoints $\mu \alpha.\; F(\alpha)$ converge inductively on $k$ without requiring domain theory or trusting any syntactic type checker. To admit code $c$ into the kernel, the producer proves a single theorem:

$$\forall k \in \mathbb{N}.\; \text{init}(s_0) \implies \text{safe}_k(s_0)$$

No VCGen lives in Ring 0: the kernel checks only the proof object establishing that step-indexed safety holds for arbitrary $k$.

### 3. Sub-2-KLoC Kernel-Resident Checkers: Bytecode DAGs, LRAT Hints, and LCF Trade-offs

Basis: source + normative (`digama0/mm0` at `0d414c0bfdaaeb7fea571895127abc1fa5a3d956`; `marijnheule/drat-trim` at `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`; `jrh13/hol-light` at `6dbb775efdff7f75aa20006532bf6336bc645861`).

Moving foundational or SMT-backed proofs into Ring-0 admission paths fails if the checker triggers quadratic term expansion, garbage collection, or dynamic SAT search. Direct inspection of three minimal checkers reveals the concrete engineering mechanisms that keep TCB below 2 KLoC while retaining linear runtime.

#### 3.1 `mm0-c` Binary Proof Bytecode (`digama0/mm0`)

In `digama0/mm0`, the C verifier (`mm0-c`) decouples human-facing specification parsing from binary proof checking:
- **Exact verifier footprint**: `mm0-c/main.c` (79 lines), `mm0-c/types.c` (329 lines), and `mm0-c/verifier.c` (819 lines) total **1,227 lines of C** (excluding optional text `.mm0` spec parser `parser.c` at 904 lines and debug index `index.c` at 161 lines; when a kernel pins a compiled specification table or hash of `.mmb` header declarations, `parser.c` and `index.c` need not reside in Ring 0).
- **Binary layout (`mm0-c/types.c:41-66`)**: `.mmb` begins with a packed `header` carrying `MM0B_MAGIC = 0x42304D4D`, `MM0B_VERSION = 1`, `num_sorts <= 128` (`MAX_SORTS`), `num_terms`, `num_thms`, and direct byte offsets `p_terms`, `p_thms`, `p_proof`, enabling `O(1)` random access into declaration tables directly over a read-only `mmap`ped or kernel-copied buffer.
- **Zero-allocation bound-variable hygiene (`mm0-c/types.c:75-78`)**: every argument descriptor is a single `u64` packing:
  - Bits `0..54` (`TYPE_DEPS_MASK = ((1ULL<<55)-1)`): bitmask of the first 55 bound variables this regular variable may depend on;
  - Bits `56..62` (`TYPE_SORT(type)`): 7-bit sort ID;
  - Bit `63` (`TYPE_BOUND_MASK = (1ULL<<63)`): whether the argument itself is bound.
  Checking variable capture or disjointness in substitution (`CMD_PROOF_TERM`, `CMD_PROOF_THM`) reduces to constant-time bitwise `&` / `|` instructions rather than recursive $\alpha$-renaming or de Bruijn shifting.
- **DAG sharing via RPN stack + indexed heap (`mm0-c/verifier.c:382-613`)**: instead of tree-shaped proof objects whose serialized size blows up exponentially under cut/substitution, `.mmb` encodes a reverse-Polish command stream manipulating a value stack `g_stack` and write-once heap `g_heap`:
  - `CMD_PROOF_TERM_SAVE` / `CMD_PROOF_THM_SAVE` store newly constructed expressions or proven statements into `g_heap`;
  - `CMD_PROOF_REF i` pushes `g_heap[i]` (or discharges a convertibility obligation `e1 =?= e2` if `g_heap[i]` is a `STACK_TYPE_CONV` equality certificate);
  - `CMD_PROOF_UNFOLD` and `CMD_PROOF_CONV` explicitly sequence definition unfolding rather than running an implicit Turing-complete definitional-equality (`isDefEq`) reducer inside the kernel.

Carneiro (arXiv:1910.10703 / CICM 2020) reports verifying the entire `set.mm` ZFC Metamath library in under 200 ms with `mm0-c`, demonstrating that sub-millisecond verification of single-program safety certificates is well within kernel admission latency budgets once `.mmb` stack/store arenas are statically bounded per admission request.

#### 3.2 `lrat-check.c` Linear-Time UNSAT/Safety Checking (`marijnheule/drat-trim`)

When kernel admission encodes bitvector bounds, integer-overflow freedom, or pointer-disjointness queries as CNF formulas (e.g., via bounded bit-blasting of basic-block safety conditions), standard DRAT proofs remain too expensive for Ring 0 because DRAT omits which clauses trigger unit propagation, forcing the checker to maintain two-watched-literal structures and search across potentially millions of active clauses.

In `marijnheule/drat-trim/lrat-check.c` (509 lines total), **LRAT (Linear RAT)** eliminates search entirely:
- Each derived lemma line includes both the new clause literals and an explicit ordered list of antecedent clause IDs (`getHints(list)` at `lrat-check.c:69`), with negated IDs marking RAT resolution witnesses (`getRATs(hints + 1)` at `lrat-check.c:120`).
- `checkRedundancy` (`lrat-check.c:89-115`) sets timestamp-based falsification marks (`mask[clit] = now + RATs`) and walks only the hint clauses fetched via `getClause(res)`. Every non-final hint clause must have at most one unassigned literal (`unit`), which is immediately propagated (`mask[unit^1] = thisMask`), and the final hint must falsify every literal (`unit == 0 -> CONFLICT`).
- **Kernel suitability trade-off**: `lrat-check.c` is only 509 lines and executes strictly linearly in hint count, making its worst-case runtime $O(\text{certificate bytes})$. However, stock `lrat-check.c` uses `realloc` (`lrat-check.c:128`) and stdio file parsing (`fscanf`); a kernel-resident adaptation must replace `realloc` with fixed pre-declared literal/clause-table caps parsed from the certificate header and validate integer bounds (`clit >= max_var * 2 + 2`) upfront to prevent kernel-heap exhaustion.

#### 3.3 LCF Abstract-Datatype Kernels (`jrh13/hol-light/fusion.ml`)

Milner's LCF pattern—epitomized by `jrh13/hol-light/fusion.ml` at **680 lines** of OCaml—exposes `module type Hol_kernel` (`fusion.ml:12-47`) with `type thm` kept abstract behind the module signature so that values of `thm` can only be fabricated by primitive inference constructors (`REFL`, `TRANS`, `MK_COMB`, `ABS`, `BETA`, `ASSUME`, `EQ_MP`, `DEDUCT_ANTISYM_RULE`, `INST_TYPE`, `INST`).

While LCF achieves minimal *logical* TCB, it makes the inverse trade-off for *kernel-resident admission*:
- An LCF kernel checks proofs by **executing forward combinator programs** (or an OpenTheory article interpreter) rather than streaming static bytes.
- Constructing intermediate `term` / `thm` objects allocates continuously on a garbage-collected heap (`OCaml` runtime + GC, or a verified CakeML/Candle binary runtime), introducing GC pauses and heap-sizing unpredictability incompatible with deterministic Ring-0 admission paths unless compiled beforehand into a linear bytecode stream like `.mmb`.

### 4. Fixpoint Abstract Interpretation vs. Linear-Time Witness Checking

Basis: source + execution + derived (`vbpf/prevail` at `169eb5d6f48a59ffe4e902e977ae4e387f2b4e49`, `torvalds/linux` at `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`, and Probe A).

#### 4.1 Why In-Kernel Fixpoint and Path-Sensitive Analyzers Hit DoS Limits

Linux's upstream eBPF verifier (`torvalds/linux/kernel/bpf/verifier.c`, 24,331 lines) explores CFG execution paths forward while attempting to prune states via register-liveness and `states_equal` subsumption. Because register-precision tracking is path-sensitive and branch merges can fail exact subsumption, Linux imposes hard defensive caps:
- `BPF_COMPLEXITY_LIMIT_INSNS = 1000000` (`include/linux/bpf.h:2585`)
- `BPF_COMPLEXITY_LIMIT_JMP_SEQ = 8192` and `BPF_COMPLEXITY_LIMIT_STATES = 64` (`kernel/bpf/verifier.c:203-204`)

Adversarial or compiler-unrolled diamond sequences easily explode visited states before hitting `10^6` processed instructions, rejecting valid memory-safe programs or consuming millisecond-scale kernel CPU time under a global or socket-creation path.

PREVAIL (Gershuni et al., PLDI 2019; `vbpf/prevail`) replaces exponential path-enumeration with **Zone abstract interpretation**:
- **Weak Topological Ordering (`src/cfg/wto.hpp` / `src/cfg/wto.cpp`)**: decomposes arbitrary CFGs (including irreducible or nested loops) into Bourdoncle components `(3 4 (5 6) 7)` with cycle-head nesting tables `WtoNesting`.
- **Relational Difference Constraints (`src/crab/zone_domain.hpp` / `src/crab/splitdbm/split_dbm.cpp`)**: tracks split difference-bound matrices capturing $x - y \le c$ invariants between registers (crucial for eBPF pointer-offset arithmetic `pkt_ptr + len <= pkt_end` where interval bounds $[l, u]$ alone lose the relational invariant `ptr <= end`).
- **Fixpoint Computation (`src/fwd_analyzer.cpp`)**: iterates WTO components using widening ($\nabla$) to guarantee termination followed by narrowing ($\Delta$) to recover precision.

Even with polynomial per-operation SplitDBM costs, running Bourdoncle WTO decomposition + iterative widening/narrowing *inside the kernel* still forces Ring 0 to execute an entire C++ abstract interpreter (~10+ KLoC), run fixpoint loops of variable iteration depth, and perform dense graph closures on untrusted inputs.

#### 4.2 Witness-Carrying Abstract Interpretation (`PCC-AI`)

Splitting abstract interpretation into **untrusted synthesis + linear-time witness checking** eliminates fixpoint iteration in Ring 0:
1. **Untrusted Producer (User Space)**: runs PREVAIL's WTO fixpoint + narrowing to obtain a stable invariant $W(v) \in \mathcal{D}_{\text{Zone}}$ at every cut-point vertex $v \in V_{\text{cut}}$ (specifically loop headers and join vertices, or all basic-block headers).
2. **Kernel-Resident Witness Checker**: performs **one single pass** over the CFG edges $(u, B, v) \in E$:
   - Check initialization: $s_{\text{init}}^\# \sqsubseteq W(v_{\text{entry}})$.
   - Check local abstract post-condition across every basic block $B$ from $u$ to $v$: $\llbracket B \rrbracket^\#(W(u)) \sqsubseteq W(v)$ (requiring only single-step abstract transfer + lattice inclusion $\sqsubseteq$, **zero joins, zero widenings, zero iterations**).
   - Check safety assertions inside each block $B$ under $W(u)$ (e.g., for every memory load/store at `[r_base + off]`, prove `r_base - reg_end <= -access_size` in $W(u)$).

#### 4.3 Executable Micro-Probe A: Diamond-Chain Path Explosion vs. Zone Fixpoint vs. Single-Pass Witness Checking

Basis: execution (Python 3.13.15 standard library micro-probe executed directly; reproduces `unmerged_steps > 1,000,000` at $k=20$ vs. $O(k)$ linear witness checking and rejects tampered witnesses).

```bash
python3 - <<'PY'
#!/usr/bin/env python3
"""Micro-probe A: Diamond-chain path explosion vs. zone fixpoint vs. witness check + CDT revocation."""


def explore_path_sensitive(k: int) -> tuple[int, int]:
    paths = [(0, 0)]
    total_steps = 0
    for _ in range(k):
        nxt = []
        for r0, st in paths:
            nxt.append((r0, st + 2))
            nxt.append((r0 + 2, st + 2))
            total_steps += 4
        paths = nxt
    total_steps += len(paths)
    max_r0 = max(r0 for r0, _ in paths)
    assert max_r0 == 2 * k and len(paths) == (1 << k)
    return len(paths), total_steps


def zone_fixpoint_diamond(k: int) -> tuple[int, tuple[int, int]]:
    inv = {i: None for i in range(k + 1)}
    inv[0] = (0, 0)
    worklist = list(range(k))
    edge_evals = 0
    while worklist:
        u = worklist.pop(0)
        lo, hi = inv[u]
        for delta in (0, 2):
            edge_evals += 1
            cand = (lo + delta, hi + delta)
            v = u + 1
            if inv[v] is None:
                inv[v] = cand
                if v < k:
                    worklist.append(v)
            else:
                old_lo, old_hi = inv[v]
                joined = (min(old_lo, cand[0]), max(old_hi, cand[1]))
                if joined != inv[v]:
                    inv[v] = joined
                    if v < k and v not in worklist:
                        worklist.append(v)
    return edge_evals, inv[k]


def check_witness_linear(k: int, witness: dict[int, tuple[int, int]], buf_len: int) -> tuple[bool, int, str]:
    checks = 0
    if witness[0][0] > 0 or witness[0][1] < 0:
        return False, checks, "entry invariant fails 0 in I(0)"
    for i in range(k):
        lo, hi = witness[i]
        t_lo, t_hi = witness[i + 1]
        for delta in (0, 2):
            checks += 1
            if lo + delta < t_lo or hi + delta > t_hi:
                return False, checks, f"inductive edge ({i}->{i+1}, +{delta}) violated: [{lo+delta},{hi+delta}] !<= [{t_lo},{t_hi}]"
    checks += 1
    exit_lo, exit_hi = witness[k]
    if exit_lo < 0 or exit_hi >= buf_len:
        return False, checks, f"safety obligation violated: [{exit_lo},{exit_hi}] not in [0, {buf_len})"
    return True, checks, "accepted"


def cdt_revoke_probe() -> dict[str, object]:
    cdt = {
        "c_ucode": {"active": True, "parent": None, "children": ["cap_uring_reg"]},
        "cap_uring_reg": {"active": True, "parent": "c_ucode", "children": ["cap_sqe_ring", "cap_dma_sgl"]},
        "cap_sqe_ring": {"active": True, "parent": "cap_uring_reg", "children": ["cap_rx_slice_0"]},
        "cap_dma_sgl": {"active": True, "parent": "cap_uring_reg", "children": []},
        "cap_rx_slice_0": {"active": True, "parent": "cap_sqe_ring", "children": []},
    }
    inflight_dma = {"cap_rx_slice_0": 2, "cap_dma_sgl": 1}
    iotlb_generation = 10

    def revoke_postorder(root: str) -> list[str]:
        order = []
        for ch in list(cdt[root]["children"]):
            order.extend(revoke_postorder(ch))
        if root != "c_ucode":
            cdt[root]["active"] = False
            order.append(root)
        return order

    revoked_order = revoke_postorder("c_ucode")
    drained = {k: 0 for k in inflight_dma}
    iotlb_generation += 1
    all_descendants_inactive = all(not cdt[n]["active"] for n in cdt if n != "c_ucode")
    return {
        "revoked_order": revoked_order,
        "all_descendants_inactive": all_descendants_inactive,
        "drained_inflight": drained,
        "iotlb_generation_after_sync": iotlb_generation,
    }


def main() -> None:
    print("k,unmerged_paths,unmerged_steps,zone_edge_evals,witness_checks,witness_valid,tamper_msg")
    for k in (4, 8, 12, 16, 20):
        paths, steps = explore_path_sensitive(k)
        zone_evals, exit_iv = zone_fixpoint_diamond(k)
        valid_w = {i: (0, 2 * i) for i in range(k + 1)}
        ok, w_checks, _ = check_witness_linear(k, valid_w, 2 * k + 1)
        assert ok and exit_iv == (0, 2 * k)
        bad_w = dict(valid_w)
        bad_w[k] = (0, 2 * k - 2)
        bad_ok, _, bad_msg = check_witness_linear(k, bad_w, 2 * k + 1)
        assert not bad_ok
        print(f"{k},{paths},{steps},{zone_evals},{w_checks},{ok},{bad_msg}")
    print("CDT_REVOCATION:", cdt_revoke_probe())


if __name__ == "__main__":
    main()
PY
```

Observed output:

```text
k,unmerged_paths,unmerged_steps,zone_edge_evals,witness_checks,witness_valid,tamper_msg
4,16,76,14,9,True,inductive edge (3->4, +2) violated: [2,8] !<= [0,6]
8,256,1276,30,17,True,inductive edge (7->8, +2) violated: [2,16] !<= [0,14]
12,4096,20476,46,25,True,inductive edge (11->12, +2) violated: [2,24] !<= [0,22]
16,65536,327676,62,33,True,inductive edge (15->16, +2) violated: [2,32] !<= [0,30]
20,1048576,5242876,78,41,True,inductive edge (19->20, +2) violated: [2,40] !<= [0,38]
CDT_REVOCATION: {'revoked_order': ['cap_rx_slice_0', 'cap_sqe_ring', 'cap_dma_sgl', 'cap_uring_reg'], 'all_descendants_inactive': True, 'drained_inflight': {'cap_rx_slice_0': 0, 'cap_dma_sgl': 0}, 'iotlb_generation_after_sync': 11}
```

At $k=20$, unmerged path exploration visits $1,048,576$ paths and $5,242,876$ steps (exceeding Linux's `BPF_COMPLEXITY_LIMIT_INSNS = 1,000,000` by $>5\times$), whereas single-pass witness checking validates the exact safety obligation in `41` deterministic checks ($2k + 1$) and immediately rejects an artificially narrowed witness `[0, 38]` at inductive edge `(19->20, +2)`.

### 5. Admission Paths Beyond eBPF: Zero-Copy `io_uring`, DMA/IOMMU, and GPU Compute Shaders

Basis: source + derived (`torvalds/linux` `include/uapi/linux/io_uring.h`, `io_uring/register.c`; `axboe/liburing` `src/register.c`).

#### 5.1 Stateful Zero-Copy Ring Policies vs. Linux `IORING_REGISTER_RESTRICTIONS`

Linux `io_uring` provides a static ring-restriction mechanism exposed via `io_uring_register_restrictions` (`axboe/liburing/src/register.c:251-256`) and enforced in `io_register_restrictions` (`torvalds/linux/io_uring/register.c:167-185`):
- The ring must be created in a disabled state (`IORING_SETUP_R_DISABLED`, `include/uapi/linux/io_uring.h:181`) before `IORING_REGISTER_ENABLE_RINGS` activates it (`io_uring/register.c:894-902`).
- Exactly one registration call (`ctx->restrictions.op_registered`) installs an array of `struct io_uring_restriction` records selecting only four stateless primitives (`include/uapi/linux/io_uring.h:989-1003`):
  - `IORING_RESTRICTION_REGISTER_OP = 0` (bitmap of allowed `io_uring_register` opcodes)
  - `IORING_RESTRICTION_SQE_OP = 1` (bitmap of allowed `IORING_OP_*` submission opcodes)
  - `IORING_RESTRICTION_SQE_FLAGS_ALLOWED = 2` (mask of permitted `IOSQE_*` flags)
  - `IORING_RESTRICTION_SQE_FLAGS_REQUIRED = 3` (mask of mandatory flags, e.g., `IOSQE_FIXED_FILE`)

While sufficient for basic sandboxing (forcing fixed registered files/buffers via `IOSQE_FIXED_FILE` and `IORING_OP_READ_FIXED`/`IORING_OP_WRITE_FIXED`), static allowlists are strictly weaker than proof-carrying ring policies in four ways:
1. **Shared-Memory SQE Double-Fetch / TOCTOU**: In a standard `io_uring`, the submission queue (SQ) ring array is mapped `PROT_READ | PROT_WRITE` into untrusted user memory; if a policy attempts to inspect user SQE fields (`addr`, `len`, `buf_index`, `off`) in-place rather than copying into private kernel SQEs prior to validation, a concurrent user thread can mutate the SQE between admission check and DMA/worker dispatch.
2. **Temporal Linear Buffer-Slice Ownership**: Allowing `IORING_OP_READ_FIXED` on registered buffer index `b` does not prove that two concurrent in-flight SQEs write disjoint byte slices `[off_1, off_1 + len_1) \cap [off_2, off_2 + len_2) = \emptyset`, nor that user space refrains from reading/writing `b` while a zero-copy kernel/NIC DMA transfer owns slice `b`.
3. **Linked-Chain (`IOSQE_IO_LINK`) Resource Exhaustion and Sequencing**: A stateless flag allowlist either permits `IOSQE_IO_LINK` globally (allowing unbounded linked chains or violating cross-SQE protocol invariants like `ACCEPT -> RECV -> CLOSE`) or bans chaining outright.
4. **Registered-Buffer Offset Arithmetic**: Stateless bitmaps cannot enforce dynamic data-dependent policies (e.g., packet-length prefix in slot header bounds subsequent scatter-gather write length).

A proof-carrying ring policy resolves these gaps by treating ring admission as an **automaton over registered fixed-buffer capabilities** checked by a micro-verifier at ring registration (or compiled into a verified ring-gate bytecode):
- **Linear Ownership State**: Every registered buffer slice `buf[i][lo..hi]` carries a ghost state $\sigma(i) \in \{\text{UserOwned}, \text{KernelInFlight}(t), \text{DeviceDMA}(t)\}$.
- **Certificate-Verified Producer Loop / Dispatcher**: If untrusted user code runs inside a restricted sandbox (or submits a small ring-policy filter attached to the ring via `IORING_REGISTER_BPF_FILTER` as exposed at `io_uring/register.c:1075-1076`), an attached witness proves that every SQE emitted into the kernel-copied SQ array transitions $\sigma$ linearly (`UserOwned -> KernelInFlight` on submit; restored only on observed CQE completion token `cqe.user_data`), keeping disjoint slices isolated without per-I/O kernel range-tree searches.

#### 5.2 User-Managed DMA/IOMMU Descriptor Rings and GPU Compute Shaders

The same separation between off-kernel synthesis and linear-time in-kernel checking generalizes to two adjacent zero-copy hardware boundaries:
- **DMA / IOMMU Scatter-Gather Rings**: When an untrusted dataplane prepares NVMe or NIC TX/RX descriptor rings containing `(iova, len, flags)`, hardware IOMMU page tables enforce coarse page-level protection (4 KiB or 2 MiB) but cannot enforce sub-page packet-header invariants, descriptor-chain acyclicity, or producer/consumer head-tail monotonicity. A certificate-verifying driver stub checks that untrusted ring-management logic preserves `[iova, iova + len) \subseteq \text{CapIOVA}` and non-overlapping TX descriptors before exposing the doorbell register.
- **GPU Compute Shaders**: Graphics/compute drivers (Vulkan SPIR-V, WebGPU WGSL, CUDA PTX) routinely inject runtime bounds-clamping instructions around every workgroup shared-memory or storage-buffer access (`min(idx, len - 1)`), or rely on complex optimizing shader compilers inside the driver TCB. Attaching a zone/interval or `.mmb`/LRAT proof witness proving $\forall \text{tid} < \text{group\_size}.\; 0 \le \text{addr}(\text{tid}) < \text{buf\_len}$ lets the kernel shader loader admit unclamped memory instructions while verifying bounds safety in one linear pass over the shader IR.

### 6. Synchronous Capability and Assumption-Certificate Revocation

Basis: source + execution + derived (`seL4/seL4` at `08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`, `src/object/cnode.c:317,528-575`; Probe A).

A certificate kernel's soundness theorem always has the conditional form $\Gamma_{\text{platform}} \vdash \text{Safe}(P)$, where $\Gamma_{\text{platform}}$ encodes hardware and environment assumptions (CPU microcode patch level, IOMMU ACS/isolation topology, absence of transient-execution leakage across ring boundaries, or a root endorsement key). When a platform assumption is retracted—for example, a microcode advisory invalidates a speculative bounds-check elision assumption or a tenant capability is revoked—previously admitted extensions and zero-copy rings cannot be allowed to run until "next reboot."

#### 6.1 seL4 Capability Derivation Tree (`cteRevoke`)

`seL4/seL4` (`src/object/cnode.c:528-550`) models transitive capability derivation as a doubly-linked **Capability Derivation Tree (CDT)** embedded in `cte_t.cteMDBNode`:
- `cteRevoke(cte_t *slot)` traverses `nextPtr = CTE_PTR(mdb_node_get_mdbNext(slot->cteMDBNode))` while `isMDBParentOf(slot, nextPtr)` holds, invoking `cteDelete(nextPtr, true)` (`finaliseSlot` + `emptySlot`) on every child and calling `preemptionPoint()` between deletions so long revocation cascades remain interruptible without dropping tree invariants.
- Because every derived capability in seL4 is an explicit node descending from its parent capability slot, revoking a root capability atomically reaches all transitive copies and sub-derivations.

#### 6.2 Four-Phase Quiescent Barrier for Zero-Copy Rings and DMA

Deleting an in-memory capability node alone is **unsound** when asynchronous kernel workers or PCIe DMA engines hold active physical address translations or in-flight descriptors. Synchronous assumption-certificate revocation over zero-copy ring subsystems requires a strict four-phase barrier (demonstrated structurally in Probe A's `cdt_revoke_probe`):
1. **Epoch / Doorbell Freeze**: Atomically advance the ring's `admission_epoch` and mask the user doorbell / `IORING_SETUP_R_DISABLED` submission path so no new SQEs or descriptor tail updates enter dispatch under the stale assumption certificate $\Gamma_{\text{platform}}$.
2. **CDT Post-Order Invalidations**: Walk the derivation tree rooted at assumption node $c_{\text{ucode}}$ (`cap_rx_slice_0 -> cap_sqe_ring -> cap_dma_sgl -> cap_uring_reg`), marking all descendant ring/buffer capabilities invalid (`active = False`) and unmapping user virtual aliases (`zap_vma_ptes` + CPU TLB shootdown).
3. **In-Flight Drain & Synchronous IOTLB Barrier**: Cancel or await completion of all `KernelInFlight` / `DeviceDMA` descriptors (`drained_inflight == 0`) and issue a synchronous hardware **IOMMU IOTLB invalidation + completion fence** (`iotlb_generation` incremented only after device-side ATS/IOTLB flush completes).
4. **Physical Frame Reclamation**: Only after Phase 3 completes may underlying physical pages be zeroed or reassigned to another domain; freeing frames before the synchronous IOTLB fence leaves a classic DMA use-after-free window even if CPU page tables were already unmapped.

## Boundaries

- **Linux kernel patch status (`unsupported` / `not examined`)**: Upstream Linux `torvalds/linux` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`) supports only static `IORING_REGISTER_RESTRICTIONS` and the in-kernel `kernel/bpf/verifier.c` path/abstract verifier; upstream Linux does not natively ship an `.mmb`, `.lrat`, or PREVAIL witness-checking kernel module.
- **Unverified runtime performance of `mm0-c` / `lrat-check.c` inside Ring 0 (`not examined`)**: Direct execution benchmarking inside a Linux kernel module (including `mmap`-replacement via kernel `vmalloc`/`vmap` and stack-depth auditing under 8 KiB/16 KiB kernel stacks) was not performed in this investigation; Probe A models witness scaling in user-space Python.
- **Bounded allocation in stock `lrat-check.c` (`known not to apply`)**: Stock `marijnheule/drat-trim/lrat-check.c` invokes `realloc` and `fscanf` from `<stdio.h>`; those libc calls cannot be used verbatim inside an OS kernel and must be replaced with static ring-0 bounds-checked arena slices before deployment.
- **GPU shader and NVMe/NIC firmware trust boundaries (`unknown`)**: While witness-carrying checks can prove shader buffer bounds or host descriptor IOVA validity prior to doorbell ringing, verifying that proprietary GPU microcontrollers or NIC firmware faithfully execute validated descriptors without internal firmware bugs remains outside host-kernel witness checking unless paired with hardware IOMMU/device attestation.
- **LCF kernel suitability for hard-real-time admission (`known not to apply`)**: `jrh13/hol-light/fusion.ml` establishes a tiny logical TCB (680 lines) in OCaml, but relying on dynamic ML closure execution and tracing garbage collection inside a Ring-0 syscall/interrupt admission hot path does not meet bounded-latency or allocation-free kernel constraints without ahead-of-time compilation to a linear certificate format.

## Evidence

- **Primary Git Sources (verified at exact 40-hex commit SHAs on 2026-11-19)**:
  - `digama0/mm0` (`0d414c0bfdaaeb7fea571895127abc1fa5a3d956`):
    - `mm0-c/main.c` (79 lines), `mm0-c/types.c` (329 lines: `MM0B_MAGIC = 0x42304D4D` at lines 41–66, `TYPE_DEPS_MASK` at lines 75–78), `mm0-c/verifier.c` (819 lines: `CMD_PROOF_REF` lines 382–393, `CMD_PROOF_DUMMY` lines 397–402, `CMD_PROOF_TERM_SAVE` lines 426–432, `CMD_PROOF_THM_SAVE` lines 479–481, `CMD_PROOF_HYP`/`CMD_PROOF_CONV`/`CMD_PROOF_UNFOLD` lines 521–613), `mm0-c/parser.c` (904 lines), `mm0-c/index.c` (161 lines).
  - `marijnheule/drat-trim` (`2e3b2dc0ecf938addbd779d42877b6ed69d9a985`):
    - `lrat-check.c` (509 lines: `getHints`/`getRATs` lines 69–70, `checkRedundancy` lines 89–115, `checkClause` lines 117–135).
  - `jrh13/hol-light` (`6dbb775efdff7f75aa20006532bf6336bc645861`):
    - `fusion.ml` (680 lines: `module type Hol_kernel` lines 12–47).
  - `vbpf/prevail` (`169eb5d6f48a59ffe4e902e977ae4e387f2b4e49`):
    - `CMakeLists.txt` (library file inventory: `src/cfg/wto.cpp`, `src/crab/zone_domain.cpp`, `src/crab/splitdbm/split_dbm.cpp`, `src/fwd_analyzer.cpp`), `src/cfg/wto.hpp` (`WtoNesting`), `src/crab/zone_domain.hpp` (`ZoneDomain`).
  - `torvalds/linux` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`):
    - `kernel/bpf/verifier.c` (24,331 lines; `BPF_COMPLEXITY_LIMIT_JMP_SEQ = 8192` line 203, `BPF_COMPLEXITY_LIMIT_STATES = 64` line 204); `include/linux/bpf.h` (`BPF_COMPLEXITY_LIMIT_INSNS = 1000000` line 2585).
    - `include/uapi/linux/io_uring.h` (`IORING_SETUP_R_DISABLED` line 181, `IORING_OP_READ_FIXED`/`IORING_OP_WRITE_FIXED` lines 261–262, `enum io_uring_register_restriction_op` lines 989–1003).
    - `io_uring/register.c` (`io_parse_restrictions` & `io_register_restrictions` lines 105–185, dispatch lines 894–902 and 1073–1077).
  - `axboe/liburing` (`a10946dc51eeababc48ee10baf0d17489f647a80`):
    - `src/register.c` (`io_uring_register_restrictions` lines 251–256, `io_uring_enable_rings` lines 258–261).
  - `seL4/seL4` (`08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`):
    - `src/object/cnode.c` (`cteRevoke` lines 528–550, `cteDelete` lines 552–564, `emptySlot` lines 566–575).
- **Peer-Reviewed Papers and Specifications**:
  - Bershad et al., *Extensibility, Safety and Performance in the SPIN Operating System*, SOSP 1995, pp. 267–284, `doi:10.1145/224056.224077`.
  - Necula, *Proof-Carrying Code*, POPL 1997, pp. 106–119, `doi:10.1145/263699.263712`.
  - Appel and McAllester, *An Indexed Model of Recursive Types for Foundational Proof-Carrying Code*, ACM TOPLAS 23(5), pp. 657–683, 2001, `doi:10.1145/504709.504712`.
  - Fähndrich et al., *Language Support for Fast and Reliable Message-Based Communication in Singularity OS*, EuroSys 2006, pp. 177–190, `doi:10.1145/1217935.1217953`.
  - Klein et al., *seL4: Formal Verification of an OS Kernel*, SOSP 2009, pp. 207–220, `doi:10.1145/1629575.1629596`.
  - Cruz-Filipe, Heule, Hunt, Kaufmann, and Schneider-Kamp, *Efficient Certified RAT Verification*, CADE 2017, pp. 220–236, `doi:10.1007/978-3-319-63046-5_14`.
  - Gershuni et al., *Simple and Precise Static Analysis of Untrusted Linux Kernel Extensions* (PREVAIL), PLDI 2019, `doi:10.1145/3314221.3314590`.
  - Carneiro, *Metamath Zero: The Cartesian Theorem Prover*, arXiv:1910.10703 (`doi:10.48550/arXiv.1910.10703`) and *Metamath Zero: Designing a Theorem Prover Prover*, CICM 2020, pp. 71–88 (`doi:10.1007/978-3-030-53518-6_5`).
- **Execution Evidence (2026-11-19)**:
  - Self-contained Python 3.13.15 micro-probe embedded in Findings Section 4.3 (`explore_path_sensitive`, `zone_fixpoint_diamond`, `check_witness_linear`, `cdt_revoke_probe`), demonstrating $2^{20}$ path explosion ($5,242,876$ steps) vs. `41` single-pass witness checks, edge-level tampering rejection, and synchronous CDT revocation sequencing.

## Revalidation

To check whether upstream kernel complexity bounds, `io_uring` restriction opcodes, micro-checker LOC/formats, or the analytical scaling model have changed:

1. **Re-run the embedded Python 3 micro-probe (self-contained, standard library only)**:
   Copy and execute the `python3 - <<'PY' ... PY` block in **Findings §4.3**; confirm `witness_checks == 2*k + 1` (41 at $k=20$), `tamper_msg` triggers on edge `(19->20, +2)`, and `all_descendants_inactive == True`.
2. **Diff upstream kernel complexity and `io_uring` restriction interfaces against newer revisions**:
   ```bash
   git -c protocol.version=0 ls-remote https://github.com/torvalds/linux.git HEAD
   curl -sSL https://raw.githubusercontent.com/torvalds/linux/<NEW_SHA>/include/linux/bpf.h | grep -n "BPF_COMPLEXITY_LIMIT_INSNS"
   curl -sSL https://raw.githubusercontent.com/torvalds/linux/<NEW_SHA>/include/uapi/linux/io_uring.h | grep -n -A 18 "enum io_uring_register_restriction_op"
   curl -sSL https://raw.githubusercontent.com/torvalds/linux/<NEW_SHA>/io_uring/register.c | grep -n -A 20 "io_register_restrictions("
   ```
3. **Verify micro-checker TCB footprint and seL4 CDT revocation stability**:
   ```bash
   for f in main.c types.c verifier.c; do
     echo -n "$f: "; curl -sSL "https://raw.githubusercontent.com/digama0/mm0/<NEW_SHA>/mm0-c/$f" | wc -l
   done
   curl -sSL https://raw.githubusercontent.com/marijnheule/drat-trim/<NEW_SHA>/lrat-check.c | wc -l
   curl -sSL https://raw.githubusercontent.com/seL4/seL4/<NEW_SHA>/src/object/cnode.c | grep -n -A 22 "^cteRevoke("
   ```
