# Language-Enforced In-Kernel Fault Isolation and the Metal / Typechain Lineage (1995–2026)

## Summary

Language-enforced in-kernel fault isolation replaces hardware address-space switching (MMU page tables) and runtime software fault isolation (SFI bit-masking) with compile-time static verification of untrusted or mutually distrusting modules executing in a shared address space. Across the historical lineage from **SPIN** (SOSP 1995), **Calculus of Capabilities** (`CL`, POPL 1999 / TOPLAS 2000), **$L^3$** (TLCA 2005), and **Singularity** (EuroSys 2006 / OSR 2007) to Sergio Benitez's **Metal** (`Rusty Types`, PLAS 2016), **Stanford CS140e (`ROS`)** (2018), and **Typechain** (`blockcheck`, PLAS 2020), five structural results govern what a static type system must enforce to isolate extensions safely without a trusted garbage collector or transactional rollback:

1. **Indirect Location-Capability Splitting (`Metal`, PLAS 2016):** Unlike the Calculus of Capabilities (`CL`), which maps whole memory regions *directly* to uniqueness/duplicability flags (`{r^1}` vs `{r^+}`) in Continuation-Passing Style (CPS) and loses uniqueness under subcapability coercion $\{r^1\} \le \{r^+\}$ unless wrapped in bounded quantification $\forall[\rho_1, \rho_2, \epsilon \le \{\rho_1^+, \rho_2^+\}]$, Metal splits static capability tracking into two indirect maps:
   - $\mathcal{A} : x \mapsto \bar{l}$ (mapping each `let`-bound variable $x$ to the fine-grained value locations $\bar{l}$ on which $x$ holds *some* capability), and
   - $\mathcal{C} : l \mapsto \bar{\kappa}$ where $\kappa \in \{\mathsf{move}, \mathsf{read}, \mathsf{write}\}$ (mapping each location $l$ to its currently active permissions).
   This two-level indirection preserves the **Write-Exclusivity Invariant** ($\forall l.\,\mathsf{write} \in \mathcal{C}(l) \implies \exists x.\,\forall y.\,l \in \mathcal{A}(y) \implies x = y$) across immutable borrows (`MR1`), mutable borrows (`MR2`), moves (`MR3`), assignments (`ST1`), and `let`-bindings (`ST2`) while allowing direct-style capability restoration upon exiting a borrow's lexical scope (`moveStep_preserves_writeExclusive`, `stmtStep_preserves_writeExclusive`, and `indirect_borrow_restoration_exact` in [`support/MetalAndTypechainIsolation.lean`](support/MetalAndTypechainIsolation.lean)).
2. **Location-Partitioned Reborrowing (`owned` vs `mut` vs `all`) and Convergence with Rust MIR NLL:** By partitioning a located type $\tau@l$'s locations into $\mathsf{owned}(\tau)$ (locations directly allocated for $\tau$, stopping at `&` and `&mut` boundaries), $\mathsf{mut}(\tau)$ (locations reachable exclusively through `&mut`), and $\mathsf{all}(\tau)$ (all reachable locations), Metal allows a reference variable `x : &mut T` to be reassigned (`x = &mut b`) while its previous target `*x` remains mutably reborrowed in `y = &mut *x`. Although 2016 Rust (`rustc` AST `borrowck`) rejected this pattern, empirical execution on `rustc 1.101.0-nightly` confirms that modern MIR Non-Lexical Lifetimes (NLL, RFC 2094) accepts `x = &mut b` even when `y` is mutated *after* `x = &mut b`—because NLL classifies `x = &mut b` as a shallow write that conflicts with `Box<T>` dereferences (`E0506`) but not `&mut T` dereferences ([`support/metal_vs_rust_probes.rs`](support/metal_vs_rust_probes.rs), [`support/nll_prefix_rules_probe.rs`](support/nll_prefix_rules_probe.rs)).
3. **Two Formal Edge Cases in `Metal` (PLAS 2016):**
   - **Literal `(ST1)` Reference-Rebinding Gap (Fig. 7 vs §4.3 Line 5):** As printed in Figure 7, `(ST1)` checks $\mathcal{A}, \mathcal{C} \vdash_{\text{can}} \mathsf{write}(\mathsf{owned}(\tau_l)) \leftarrow x$ and moves $e_r$ ($\vdash_{\text{move}} e_r \Rightarrow \mathcal{A}', \mathcal{C}'$), leaving $\Gamma$ unchanged and adding no locations to $\mathcal{A}'(x)$. When $e_l$ is a reference variable (`x = &mut b` on §4.3 line 5), `(MR2)` removes $l_b$ from $\mathcal{A}(b)$ without transferring $l_b$ into $\mathcal{A}'(x)$, leaving $l_b$ orphaned (`literal_st1_orphans_rebound_target`). Adding a target-rebinding transition (`StmtStep.st1_rebind_mutRef`) transfers $\mathsf{all}(\tau_{\text{new}}) \setminus \mathsf{owned}(\tau_{\text{new}})$ into $\mathcal{A}'(x)$ while preserving `WriteExclusive`.
   - **Refutation of Unqualified *Single Depth* (`&local`, §5):** Benitez's §5 *Any Depth* relaxation (multiple single-threaded `&local` references to any depth of an object are memory-safe iff the object contains no heap allocations and no sum types) is memory-safe under direct store semantics (`anyDepth_pod_projection_never_invalidated`), though it violates `WriteExclusive` (`noalias`). However, Benitez's unqualified *Single Depth* claim (that multiple `&local` references at the *same* field depth $|.\overline{n}| = d$ are safe even with heap allocations or sum types) fails under reentrant or multi-argument evaluation: two references `r1, r2` at the same depth $d = 1$ aliasing `x.0 : Vector<int>` allow a callback or subexpression mutating `r2` at depth $1$ to reallocate/free the buffer while an active operation on `r1` at depth $1$ reads the old buffer generation (`singleDepth_reentrant_heap_counterexample`).
4. **Why Region-Less Ownership Cannot Soundly Support `Drop` (RAII) Destructors (§4.1):** Without region outlives constraints, `(ST1)` permits assigning a borrow of a younger stack variable `p2` into an older variable `a` (`a = Parent(&p2)`). Because stack frames deallocate variables in LIFO declaration order, `p2` is freed before `Parent::drop(&mut a)` executes, causing a use-after-free in `a`'s destructor (`sec4_1_drop_lifo_dangling_counterexample`; verified against `rustc` `E0597` in [`support/metal_vs_rust_probes.rs`](support/metal_vs_rust_probes.rs)).
5. **Five-Property Static Admission in `Typechain` (`blockcheck`, PLAS 2020) and Its Necessity for In-Kernel Extensions:** To execute untrusted extensions $C'_\tau = C_\tau ; p$ in a shared runtime without hardware fault recovery or transactional rollback, `blockcheck` statically enforces five properties: (1) **Asset Linearity and Liveness** (true non-droppable linearity, preventing both lost and permanently locked handles), (2) **Input-Independent Physical Resource Availability** (static upper bounds on CPU, memory, and stack frames), (3) **Exceptionless Execution** (no `throw`/panic, division-by-zero, or out-of-bounds traps), (4) **Protocol Conformance** (typestate/session types), and (5) **Inter-Extension Safety** (call-frame bounding and non-reentrancy). Dropping *any single one* of the five properties admits a concrete inter-extension failure trace (`typechain_five_way_necessity`), directly explaining the soundness gaps observed in Singularity's `ExHeap` under exceptions (EuroSys 2006 §6) and RedLeaf's cross-domain proxy panics (OSDI 2020).

---

## Applicability

This report applies to the design and verification of language-isolated operating system kernels, in-kernel extension verifiers, and proof-carrying typed admission pipelines across the twelve subjects recorded in [`REPORT.json`](REPORT.json):

- **Primary Calculi and Kernel Architectures Examined:**
  - **Sergio Benitez's `Metal` (`Rusty Types for Solid Safety`, PLAS 2016, DOI `10.1145/2993600.2993604`):** Applies to intraprocedural and interprocedural static ownership/borrow checking without lifetime annotations (§3), region-refined signature checking (§4.2), and single-threaded `&local` aliasing relaxations (§5).
  - **Benitez, Cogan & Russo's `Typechain` (`Blockcheck the Typechain`, PLAS 2020, DOI `10.1145/3411506.3417600`):** Applies to whole-system static admission $\mathsf{blockcheck}(C_\tau ; p)$, monotonic type-system strengthening ($\Gamma' \vdash' e : \tau \implies \Gamma \vdash e : \tau$, instantiated with flow-sensitive `Singleton<T>`), and Curry-Howard proof-witness libraries (`Timed<C>`).
  - **Foundational Safe-OS Lineage (`SPIN` SOSP 1995 / WCSSS 1996, `Calculus of Capabilities` POPL 1999 / TOPLAS 2000, `$L^3$` TLCA 2005, `Singularity` EuroSys 2006 / OSR 2007, and Stanford `CS140e` Winter 2018):** Comparative analysis establishing how pointer capabilities, region capabilities, linear exchange heaps (`ExHeap`), and channel state machines evolve across single-address-space kernels.
- **Execution and Verification Targets:**
  - **Rust Compiler (`rustc 1.101.0-nightly (19833af72 2026-10-20)` on `x86_64-unknown-linux-gnu`):** Used to test `Metal`'s §3.2.2, §4.1, §4.2, §4.3, and §5 behaviors against modern MIR NLL borrow checking (`--edition=2021`).
  - **Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** Used to mechanize all static/dynamic rules, invariants, soundness theorems, and counterexamples in [`support/MetalAndTypechainIsolation.lean`](support/MetalAndTypechainIsolation.lean) with zero `sorryAx`, zero `Classical.choice`, and zero `Lean.ofReduceBool`.
  - **Anneal (`joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`):** Used to connect `Metal` §5's `AnyDepthSafe` pod layout invariants and `Typechain` §3.2's proof-witness types to Anneal's `SafeToRead`/`SafeToWrite` and lock-free verification boundaries.

---

## Findings

### 1. `Metal` Static and Operational Semantics (PLAS 2016)

`Basis: documentation + source + execution + derived`

#### 1.1 Core Syntax, Located Types, and `locate(\tau)` (Figures 1 & 8)
In `Metal` (`rusty-types-2016.pdf`, §3.1, p. 3), surface programs do not contain explicit lifetime or location annotations. Internally, the type checker decorates every type constructor with an explicit location tag $l$:
- **Structured Locations:** $\ell ::= l \mid \ell.n$, where $l \in \mathsf{LocId}$ is a root location and $n \in \mathbb{N}$ is a field index.
- **Located Types:** $\tau ::= \mathsf{unit} \mid \mathsf{int} \mid Q_\mu(\bar{\tau}) \mid \&\tau \mid \&\mathsf{mut}\,\tau \mid (\overline{b:\tau}):\tau \mid \tau@l^\dagger$.
- **Decoration Function `locate(\tau)` (Figure 8, p. 5):** Recursively assigns fresh location identifiers $l'$ to unlocated type constructors while leaving already-located subterms untouched ($\mathsf{locate}(\tau@l) = \tau@l$).
  - *Crucial Semantic Role:* When `&p` or `&mut p` is typed on the right-hand side of `let a = &mut x`, `p` is first typed in LHS context to yield its existing located type $\tau_x@l_x$. The borrow expression then has pre-located RHS type $\&\mathsf{mut}\,(\tau_x@l_x)$, and `locate` allocates a fresh location $l_a$ *only* for the outer reference cell, producing $(\&\mathsf{mut}\,(\tau_x@l_x))@l_a$ (`locate_refMut_alreadyLocated` in [`support/MetalAndTypechainIsolation.lean`](support/MetalAndTypechainIsolation.lean)).

#### 1.2 Static Environments $(\Gamma, \mathcal{A}, \mathcal{C})$ and Location Extractors (Figures 2, 4, 5)
Metal tracks types and capabilities across three primary environments (§3.2, pp. 3–4):
1. $\Gamma : x \mapsto \tau$ maps each bound variable $x$ to a fully located type $\tau$.
2. $\mathcal{A} : x \mapsto \bar{l}$ maps each variable $x$ to the set of locations on which $x$ currently holds *some* capability.
3. $\mathcal{C} : l \mapsto \bar{\kappa}$ where $\kappa \in \{\mathsf{move}, \mathsf{read}, \mathsf{write}\}$ maps each location $l$ to its active capabilities.

Three structural extraction functions partition the locations of any fully located type $\tau$ (Figure 5, p. 4; mechanized in [`support/MetalAndTypechainIsolation.lean`](support/MetalAndTypechainIsolation.lean) lines 113–198):
- $\mathsf{owned}(\tau)$: locations originally allocated for $\tau$, stopping at any borrow constructor ($\mathsf{owned}(\&\tau@l) = \{l\}$, $\mathsf{owned}(\&\mathsf{mut}\,\tau@l) = \{l\}$, $\mathsf{owned}(Q_\mu(\bar{\tau})@l) = \{l\} \cup \bigcup_{\tau_i \in \bar{\tau}} \mathsf{owned}(\tau_i)$).
- $\mathsf{mut}(\tau)$: locations reachable from $\tau$ exclusively through `&mut` borrows ($\mathsf{mut}(\&\mathsf{mut}\,\tau@l) = \mathsf{owned}(\tau) \cup \mathsf{mut}(\tau)$, $\mathsf{mut}(\&\tau@l) = \emptyset$).
- $\mathsf{all}(\tau)$: all locations reachable from $\tau$, traversing through both `&` and `&mut` ($\mathsf{all}(\&\tau@l) = \{l\} \cup \mathsf{all}(\tau)$, $\mathsf{all}(\&\mathsf{mut}\,\tau@l) = \{l\} \cup \mathsf{all}(\tau)$).

Left-hand side path typing $\Gamma, \Psi, \nu \vdash_{\text{lhs}} e : \tau \leftarrow x$ (Figure 2, rules `LT1`, `LT2`) resolves any path projection $x.\bar{n}$ or dereference $*e$ to its sub-term located type $\tau$ and root provenance variable $x$. Rule `(CR1)` (Figure 4, p. 4) then checks whether variable $x$ can exercise capability $\kappa$ on location set $\bar{l}$:
$$\frac{\bar{l} \subseteq \mathcal{A}(x) \qquad \forall l \in \bar{l}.\; \kappa \in \mathcal{C}(l)}{\mathcal{A}, \mathcal{C} \vdash_{\text{can}} \kappa(\bar{l}) \leftarrow x}\;\text{(CR1)}$$

#### 1.3 Flow-Sensitive Move Rules (`MR1`, `MR2`, `MR3`, Figure 6) and Write-Exclusivity Preservation
Metal's move judgment $\Gamma, \Psi, \nu, \mathcal{A}, \mathcal{C} \vdash_{\text{move}} e \Rightarrow \mathcal{A}', \mathcal{C}'$ (Figure 6, p. 5) updates $(\mathcal{A}, \mathcal{C})$ according to the RHS expression form:

| Rule | RHS Form | Static Capability Premise on Provenance $x$ | Environment Update $(\mathcal{A}', \mathcal{C}')$ |
| :--- | :--- | :--- | :--- |
| **`(MR1)`** | `&p` | $\Gamma, \Psi, \nu \vdash_{\text{lhs}} p : \tau \leftarrow x$<br>$\mathcal{A}, \mathcal{C} \vdash_{\text{can}} \mathsf{read}(\mathsf{all}(\tau)) \leftarrow x$ | $\mathcal{A}' = \mathcal{A}$<br>$\mathcal{C}' = \mathcal{C} \oplus \{l \mapsto \mathcal{C}(l) - [\mathsf{move}, \mathsf{write}]\}_{l \in \mathsf{all}(\tau)}$ |
| **`(MR2)`** | `&mut p` | $\Gamma, \Psi, \nu \vdash_{\text{lhs}} p : \tau \leftarrow x$, $\bar{l} = \mathsf{owned}(\tau) \cup \mathsf{mut}(\tau)$<br>$\mathcal{A}, \mathcal{C} \vdash_{\text{can}} \mathsf{write}(\bar{l}) \leftarrow x$ | $\mathcal{A}' = \mathcal{A} \oplus \{x \mapsto \mathcal{A}(x) - \bar{l}\}$<br>$\mathcal{C}' = \mathcal{C} \oplus \{l \mapsto \mathcal{C}(l) - [\mathsf{move}]\}_{l \in \bar{l}}$ |
| **`(MR3)`** | `p` (move) | $\Gamma, \Psi, \nu \vdash_{\text{lhs}} p : \tau \leftarrow x$<br>$\mathsf{move}(\mathsf{owned}(\tau))$, $\mathsf{read}(\mathsf{all}(\tau))$, $\mathsf{write}(\mathsf{mut}(\tau)) \leftarrow x$ | $\mathcal{A}' = \mathcal{A} \oplus \{x \mapsto \mathcal{A}(x) - \mathsf{all}(\tau)\}$<br>$\mathcal{C}' = \mathcal{C}$ |

**Why `(ST2)` (`let b = e`) Preserves Write-Exclusivity (`moveStep_clears_writeable_target_holders`, `stmtStep_preserves_writeExclusive`):**
When `let b = e` executes `(ST2)` (Figure 7, p. 5), the new variable $x_{\text{new}}$ is bound in $\mathcal{A}''$ to $\mathsf{all}(\tau_d)$ where $\tau_d = \mathsf{locate}(\tau)$. Why does adding $\mathsf{all}(\tau_d)$ to $\mathcal{A}''(x_{\text{new}})$ never create two variables holding a location $l$ with $\mathsf{write} \in \mathcal{C}''(l)$?
1. For any outer location $l \in \mathsf{owned}(\tau_d)$ newly allocated by `locate`, $l$ is fresh ($\forall y \ne x_{\text{new}},\, l \notin \mathcal{A}'(y)$).
2. For any pre-existing location $l \in \mathsf{all}(\tau_d) \setminus \mathsf{owned}(\tau_d)$:
   - Under `(MR1)` (`&p`), $\mathsf{write}$ was stripped from *every* $l \in \mathsf{all}(\tau)$ in $\mathcal{C}'$.
   - Under `(MR2)` (`&mut p`), every $l \in \mathsf{owned}(\tau) \cup \mathsf{mut}(\tau)$ was checked for $\mathsf{write}$ on $x$ (so by `WriteExclusive` before the step, $x$ was the *unique* holder of $l$ in $\mathcal{A}$) and was removed from $\mathcal{A}(x)$ in $\mathcal{A}'$; meanwhile, any $l \in \mathsf{all}(\tau) \setminus (\mathsf{owned}(\tau) \cup \mathsf{mut}(\tau))$ lies behind an immutable borrow `&T` and already lacks $\mathsf{write}$ in $\mathcal{C}$ (`ImmSubborrowsNoWrite`).
   - Under `(MR3)` (`p`), every $l \in \mathsf{all}(\tau)$ was checked for $\mathsf{read}$ on $x$; if $\mathsf{write} \in \mathcal{C}(l)$, `WriteExclusive` guarantees $x$ was the unique holder of $l$ in $\mathcal{A}$, and `(MR3)` removes $\mathsf{all}(\tau)$ from $\mathcal{A}(x)$.
Thus, across all three move rules, **zero** variables in $\mathcal{A}'$ retain any location $l \in \mathsf{all}(\tau_d)$ that still has $\mathsf{write} \in \mathcal{C}'(l)$, so binding $x_{\text{new}} \mapsto \mathsf{all}(\tau_d)$ preserves `WriteExclusive` (`stmtStep_preserves_writeExclusive` in [`support/MetalAndTypechainIsolation.lean`](support/MetalAndTypechainIsolation.lean)).

#### 1.4 Operational Semantics `(M, L)` (`L1`, `L2`, `R1`, Figure 9) and Dereference Safety
At runtime (§3.3, p. 5), $M : x \mapsto l$ maps variables to their root locations and $L : l \mapsto v$ maps locations to values, where a borrow value is represented explicitly as $\mathsf{brw}(\ell)^\dagger$.
- Rule `(L1)` looks up $M(x) = l$ and $L(l) = v$; Rule `(L2)` dereferences $\mathsf{brw}(l')$ by looking up $L(l')$; Rule `(R1)` updates $L' = L[l \mapsto v]$ in-place without changing $M(x)$.
- **Mechanized Theorem 1 (`metal_theorem1_deref_progress_and_safety`):** Whenever runtime state $(M, L)$ satisfies well-formedness (`StateWF G A C M L`) and variable $x$ holds a reference that passes `(CR1)` read capability checking (`CanCap A C .read (allLocs t_ref) x`), evaluating `*x` steps deterministically via `(L1)` and `(L2)` to an allocated value $v_{\text{target}}$ in $L$ matching the pointee type—never faulting on an unmapped or deallocated location.

#### 1.5 Outliving-Borrow Function Signature Analysis (`OL`, §3.2.2 & §4.2)
To type-check function calls without lifetime annotations (§3.2.2, p. 4), Metal computes the set $OL$ of input borrows that could potentially escape into a writeable borrow parameter $w \in W$ or return value:
$$OL := \bigcup_{w \in W} \left\{ b \in B \;\middle|\; {*b} \mathrel{\overset{\text{lhs}}{\ne}} {*w} \;\wedge\; b \mathrel{\overset{\text{rhs}}{=}} w \right\}$$
- **Unannotated Conservatism (§3.2.2):** For `(a: &mut Q(&R(int)), b: &R(int)): unit`, $W = \{\&R(\mathsf{int})\}$ and $b \in OL$, so `b` cannot have its capabilities restored after the call.
- **Region-Refined Precision (§4.2, pp. 5–6):** When region annotations are added (`(a: &mut Q(&'a R(int)), b: &'b R(int)): unit` with incompatible regions `'a` and `'b`), RHS type equality $b \mathrel{\overset{\text{rhs}}{=}} w$ requires matching regions, reducing $OL$ to $\emptyset$ and restoring `b`'s capabilities (`sec3_2_2_vs_sec4_2_OL_precision` in [`support/MetalAndTypechainIsolation.lean`](support/MetalAndTypechainIsolation.lean)).

---

### 2. Precision Comparison with Rust (`rustc 1.101.0-nightly`) and Single-Threaded Aliasing (`&local`)

`Basis: documentation + execution + derived`

#### 2.1 Reborrowing and Reference Reassignment (§4.3)
Consider Benitez's §4.3 program (`rusty-types-2016.pdf`, p. 6):
```rust
let mut a = Q(10); // a: [move, write, read]
let mut b = Q(20); // b: [move, write, read]
let mut x = &mut a; // a: []; x, *x: write
let y = &mut *x; // *x: []; *y: write, y: read
x = &mut b; // b: []; *x: write
```
- **Why 2016 Rust Rejected Line 5:** Lexical AST `borrowck` (`rustc 1.0–1.30`) recorded a loan of supporting path `x` for the entire lexical scope of `y`, rejecting `x = &mut b` with `cannot assign to x because it is borrowed`.
- **Why Metal Accepts Line 5:** In Metal, $\mathsf{owned}(\&\mathsf{mut}\,Q(\mathsf{int}@l_a)@l_x) = \{l_x\}$, while $\mathsf{owned}(*x) \cup \mathsf{mut}(*x) = \{l_a\}$. Reborrowing `let y = &mut *x` via `(MR2)` transfers $\{l_a\}$ from $\mathcal{A}(x)$ to $\mathcal{A}(y)$, leaving $l_x \in \mathcal{A}(x)$ with $\mathsf{write} \in \mathcal{C}(l_x)$. Thus `(ST1)`'s premise $\mathcal{A}, \mathcal{C} \vdash_{\text{can}} \mathsf{write}(\mathsf{owned}(\tau_x)) \leftarrow x$ holds (`sec4_3_line4_allows_line5_and_preserves_y`).
- **Why Modern Rust MIR NLL (`rustc 1.101.0-nightly`) Accepts Line 5 Even While `y` Is Live:** Running [`support/metal_vs_rust_probes.rs`](support/metal_vs_rust_probes.rs) and [`support/nll_prefix_rules_probe.rs`](support/nll_prefix_rules_probe.rs) shows that modern `rustc` accepts `x = &mut b;` followed by `y.0 += 1; x.0 += 2;` (returning `(11, 22)`), because MIR NLL classifies `x = &mut b` as a **shallow write** to `x`. A shallow write conflicts with loans through an owned pointer (`x: Box<Q>`, which fails with `E0506` in `fail_box_reassign`), but does not conflict with a reborrow of `*x` when `x: &mut Q`.

#### 2.2 Why Region-Less `Metal` Cannot Soundly Support `Drop` (§4.1)
In §4.1 (`rusty-types-2016.pdf`, p. 5), Benitez analyzes:
```rust
let p1 = Q(1);
let mut a = Parent(&p1);
let p2 = Q(2);
a = Parent(&p2);
```
- In region-less Metal, `(ST1)` accepts `a = Parent(&p2)` because `a` holds `write` on `owned(a)` and `p2` holds `read` on `all(p2)`.
- However, under RAII (`Drop`), stack variables are destroyed in **LIFO order of declaration**: `p2` (declared 3rd) is deallocated before `a` (declared 2nd) runs `Parent::drop(&mut a)`. If `Parent::drop` reads `*a.0`, it dereferences deallocated memory (`sec4_1_drop_lifo_dangling_counterexample`).
- Our empirical probe in [`support/metal_vs_rust_probes.rs`](support/metal_vs_rust_probes.rs) confirms that `rustc 1.101.0-nightly` accepts `a = ParentNoDrop(&p2)` when `ParentNoDrop` has no `Drop` implementation, and rejects `a = ParentWithDrop(&p2)` with `error[E0597]: p2 does not live long enough` (`borrow might be used here, when a is dropped and runs the Drop code for type ParentWithDrop`).

#### 2.3 Critical Analysis of `&local` Single-Depth vs Any-Depth Relaxations (§5)
In §5 (p. 6), Benitez proposes `&local T` / `&local mut T` (single-threaded references that permit aliasing) under two rules:
1. **Any-Depth Rule:** Multiple mutable/immutable references to any depth of an object are memory-safe iff (1) the object contains no heap allocations (`noHeapAllocations`) and (2) neither the object nor its fields are of sum type (`noSumTypes`).
   - **Mechanized Verification (`anyDepth_pod_projection_never_invalidated`):** When both conditions hold (`AnyDepthSafe`), the object is a fixed-layout product of primitive scalars on the stack. Mutating any prefix or field overwrites scalar leaves in-place with valid scalars without changing any discriminant tag or freeing any heap buffer, so all coexisting paths remain valid and type-correct.
   - **Necessity of Both Conditions (`anyDepth_sumType_invalidation_counterexample`, `anyDepth_heapVec_invalidation_counterexample`):** If a sum type (`sumEnum`) is present, mutating depth $d$ from variant `Left` to `Right` invalidates a coexisting reference at depth $d+1$ into `Left`'s payload. If a heap allocation (`heapVec`) is present, mutating depth $d$ (`clear`/`realloc`) frees generation `0` while a reference at depth $d+1$ points into generation `0`.
2. **Refutation of Unqualified Single-Depth Rule (`singleDepth_breaks_writeExclusivity`, `singleDepth_reentrant_heap_counterexample`):**
   - Benitez claimed that multiple mutable/immutable `&local` references to an object are safe even *with* heap allocations or sum types iff all references have the same field-projection depth $|.\overline{n}| = d$.
   - First, coexisting mutable and immutable `&local` references at depth $d$ immediately violate §3.2.1 `WriteExclusive` (`singleDepth_breaks_writeExclusivity`), so `&local mut` cannot emit LLVM `noalias`.
   - Second, if `r1 : &local Vector<int>` and `r2 : &local mut Vector<int>` both point to `x.0`, both have the **exact same depth** $|.[0]| = 1$. Any operation on `r1` that reads `x.0`'s heap buffer at generation `0` while invoking a same-thread callback or subexpression that mutates `r2` at depth $1$ (reallocating `x.0` to generation `1`) causes `r1`'s active read at depth $1$ to access freed memory (`singleDepth_reentrant_heap_counterexample`).

---

### 3. `Typechain` & `blockcheck`: 5-Property Static Admission and Monotonic Strengthening (PLAS 2020)

`Basis: documentation + source + derived`

#### 3.1 Whole-Chain Admission (`blockcheck`) and the 5-Way Necessity Theorem
In `typechain-2020.pdf` (§1–§2, pp. 1–3), an extensible execution substrate maintains a typed sequence of deployed modules $C_\tau = \bar{p} = \overline{\bar{d}; s}$. Admitting a new module $p$ requires $\mathsf{blockcheck}(C_\tau ; p)$, where $\forall p \in C_\tau.\,\mathsf{blockcheck}(p) \iff \mathsf{blockcheck}(C_\tau)$ (`blockcheckChain_append_iff`).

In [`support/MetalAndTypechainIsolation.lean`](support/MetalAndTypechainIsolation.lean) (Section 8, lines 1061–1199), we mechanized `blockcheckProg`, `blockcheckChain`, and `evaluateExtension`, proving both whole-chain safety (`blockcheckChain_guarantees_safeCommit`) and the **5-Way Necessity Theorem** (`typechain_five_way_necessity`): dropping *any single one* of the five properties below admits a concrete failure trace:

1. **Property 1 — Asset Linearity and Liveness (§2.1):** Resources/handles must be true linear types (used *exactly once*, neither implicitly dropped as in affine Rust when `Auction::bid` returns early on `should_close(now)`, nor overwritten as in `self.max_bid = amount`, nor permanently locked in dead state as in the ~\$200M USD Parity multi-sig library bug).
2. **Property 2 — Input-Independent Physical Resource Availability (§2.2):** Every admitted extension must have a static, input-independent upper bound on CPU instructions, memory bytes, and stack frames. As shown by the `GovernMental` bug (where an unbounded array loop in a payout function exceeded the platform gas limit and permanently locked 1,100 ETH), *asset liveness is impossible without static physical resource bounds*.
3. **Property 3 — Exceptionless Execution (§2.3):** Admitted code must be free of runtime exceptions/traps (`throw`, `panic`, division-by-zero, out-of-bounds indexing).
4. **Property 4 — Protocol Conformance (§2.4):** State-machine transitions (`open` vs `closed` in `Auction`) must be enforced statically via typestate or session types.
5. **Property 5 — Inter-Contract / Inter-Extension Safety (§2.5):** Cross-module calls must enforce static call-frame bounds (preventing the $k-2$ stack-frame exhaustion attack on `return_to_sender()`) and non-reentrant state-update discipline (preventing TheDAO ~\$40M USD reentrancy exploit).

#### 3.2 Extensibility via Monotonic Type-System Strengthening (`Singleton<T>`, §3.1) and Proof-Witness Libraries (`Timed<C>`, §3.2)
- **Monotonic Type-System Strengthening (§3.1, pp. 3–4):** A strengthened type system $(\Gamma', \vdash')$ is sound with respect to base system $(\Gamma, \vdash)$ iff $\Gamma' \vdash' e : \tau \implies \Gamma \vdash e : \tau$ (`Strengthens Sys' Sys`, `strengthening_preserves_safety`). To enforce single-instance contracts (`struct Oracle : Singleton<Oracle>`), `Typechain` threads an instantiated-type set $\Delta$ with Rule 0 ($\neg\mathsf{singleton}(\tau) \implies \Delta' = \Delta$) and Rule 1 ($\mathsf{singleton}(\tau) \wedge \tau \notin \Delta \implies \Delta' = \Delta \cup \{\tau\}$). We proved that $(\Gamma, \Delta \vdash_\Delta)$ is a sound monotonic strengthening of $(\Gamma \vdash)$ (`singleton_strengthens_base`) that rejects duplicate instantiation (`singleton_oracle_once_accepted_twice_rejected`).
- **Proof-Witness Type Libraries (`Timed<C>`, §3.2, p. 4):** Using Curry-Howard proof witnesses (`OpenAuctionWitness`), `Timing::check(self, now)` produces an unforgeable witness required by `Auction::bid`, statically eliminating expired-state execution without modifying the compiler (`timed_witness_prevents_expired_bid`).

---

### 4. Synthesis Across SPIN, Calculus of Capabilities, $L^3$, Singularity, Modern Rust OS Kernels, and Anneal

`Basis: documentation + source + derived`

| Dimension | SPIN (SOSP 1995 / WCSSS 1996) | Calculus of Capabilities (POPL 1999) & $L^3$ (TLCA 2005) | Singularity (EuroSys 2006 / OSR 2007) | Metal (PLAS 2016) & CS140e `ROS` (2018) | Typechain (PLAS 2020) | Tock / Asterinas / RedLeaf / Theseus & Anneal (2015–2026) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Capability / Ownership Representation** | Opaque Modula-3 GC reference (`TYPE T <: REFANY`) | `CL`: Direct region mult. $\{r^1\}, \{r^+\}$ in CPS.<br>`L3`: `Cap(l)` (`thawed`) vs `!Frz(l)` (`frozen`) | Per-SIP GC + linear `ExHeap` (`[Claims]`, `expose`, `TCell<T>`) | Indirect 2-level maps: $\mathcal{A} : x \mapsto \bar{l}$ and $\mathcal{C} : l \mapsto \{\mathsf{move},\mathsf{read},\mathsf{write}\}$ | True linear types + typestate + $\vdash_\Delta$ strengthening | Rust affine types (`&T`, `&mut T`), `RRef<T>` (RedLeaf), Aeneas $\to$ Lean 4 (`Anneal`) |
| **Memory Reclamation without GC** | **No** — requires global kernel tracing GC (Bartlett collector) | **Yes** — `CL` `freergn` gated by $\{r^1\}$; `L3` explicit linear free | **Hybrid** — local SIP GC + deterministic `ExHeap` free | **Yes** — deterministic owner scope exit; requires regions if `Drop` is present (§4.1) | **Yes** — static resource bounds + linear consumption | **Yes** — RAII `Drop` + region outlives checking |
| **Interior Pointer & Shared Mutation Safety** | GC prevents dangling pointers, but unrestricted aliasing | `L3` weak updates while `frozen` **dangles** interior pointers into containers | `ExHeap` forbids interior pointers across SIPs; `expose` temporarily unpacks | `(MR1)` freezes `all(\tau)`; `&local` safe at any depth **iff** `noHeap ∧ noSumTypes` (§5) | Linear typestate prevents aliased mutation | Asterinas `Pod` & Anneal `SafeToRead`/`SafeToWrite` require no pointers/invalid tags |
| **Channel / Cross-Domain Protocol & Race Safety** | Dynamic event dispatcher with predicate guards | CPS continuation typing | Channel state-machine contracts: finiteness rule + **send-state endpoint transfer rule** | `OL` outliving-borrow signature check (§3.2.2, §4.2) | Session types + non-reentrant call graph (Properties 4 & 5) | RedLeaf IDL generates cross-domain proxies |
| **Exception & Resource Exhaustion Isolation** | Dispatcher catches Modula-3 exceptions; ephemeral handler preemption | Not modeled | **Soundness gap (EuroSys '06 §6):** exceptions leaked `ExHeap` cells, requiring runtime stack walker | Not modeled in base `Metal` | **Statically enforced** via Properties 2 (resource bounds) & 3 (exceptionless execution) | RedLeaf requires runtime proxy panics + `RRef` copy-out on domain crash |

**Two Cross-Lineage Insights:**
1. **Why Singularity Needed a Runtime Fallback for `ExHeap` and Why `Typechain` Closes It:** In `singularity-eurosys06.pdf` (§6, p. 188), Fähndrich et al. report that unchecked exceptions in Sing# could unwind across frames holding tracked `ExHeap` pointers in local variables or `expose` blocks, forcing Singularity to push tracked addresses onto a runtime shadow stack (`Thread.PushExHeapLocal`). `Typechain`'s combination of **Property 1 (Linearity + Liveness)** and **Property 3 (Exceptionless Execution)** eliminates this runtime shadow stack entirely at compile time.
2. **Singularity's Send-State Endpoint Transfer Rule (`singularity_send_state_prevents_endpoint_race`):** In `singularity-eurosys06.pdf` (§3.3, p. 182), transferring a channel endpoint across a channel is statically restricted to states where every outgoing transition is a send (`!`). If an endpoint in a receive state (`?`) were transferred, its peer could concurrently send a message while the receiving SIP PID is being updated, creating a lock-free race condition; restricting transfer to send states makes endpoint handoff wait-free and lock-free.

---

## Boundaries

- **Full-Language Implementation of `Metal` and `Typechain` (`unsupported` / `not examined`):** Neither `Metal` (PLAS 2016) nor `Typechain` (PLAS 2020) was released as a standalone production compiler; both papers present core formal calculi. We mechanized the complete static capability core, operational store semantics, outliving-borrow analysis, `&local` layout safety/counterexamples, and `blockcheck` admission/strengthening in Lean 4.34.1 ([`support/MetalAndTypechainIsolation.lean`](support/MetalAndTypechainIsolation.lean)), and tested the corresponding borrow-checking behaviors on `rustc 1.101.0-nightly`.
- **Multithreaded Concurrency in `&local` (`known not to apply`):** Benitez's §5 `&local` relaxation explicitly prohibits `&local` references from crossing thread boundaries (analogous to `!Send` / `!Sync` in Rust). Concurrent multi-threaded shared mutation requires atomic or lock-free proof obligations (as in Anneal's `is_lock_free` / concurrent verification domains) and is **known not to apply** to `&local`.
- **LLVM `noalias` Code Generation for `&local mut` (`known not to apply`):** Even when a type satisfies `AnyDepthSafe` (`noHeapAllocations && noSumTypes`), `&local mut` violates the §3.2.1 `WriteExclusive` invariant (`singleDepth_breaks_writeExclusivity`). A backend that emits LLVM `noalias` metadata on `&local mut` parameters would introduce miscompilation undefined behavior; `&local mut` only establishes memory/type safety under aliasing-permissive (`UnsafeCell`/`Cell`) operational semantics.
- **Turing-Complete WCET vs Restricted Resource Bounds in `Typechain` (`unknown`):** `Typechain` §2.2 requires static input-independent bounds on CPU and memory usage, suggesting restricted recursion/loop forms (similar to eBPF's bounded verifier loops), but does not specify a concrete surface syntax for loop bound annotations; the exact surface annotation design is **unknown** from the PLAS 2020 paper.

---

## Evidence

1. **Primary Publications (Verified by SHA-256):**
   - Sergio Benitez, *"Short Paper: Rusty Types for Solid Safety"*, ACM PLAS 2016, pp. 69–75, DOI `10.1145/2993600.2993604`, SHA-256 `45c51690c06855c927f64e4da52774f3982173af9ce7f30aecf81a3e5028521a`:
     - Figure 1 (p. 3): Core syntax of `Metal` ($\ell$, $\tau@l^\dagger$, $\mathsf{brw}(\ell)^\dagger$, paths, expressions, statements).
     - §3.2 & Figures 2–8 (pp. 3–5): Static environments $\Gamma, \mathcal{A}, \mathcal{C}$, Write-Exclusivity invariant (§3.2.1, p. 3), LHS provenance typing `LT1`–`LT2` (Fig. 2), `CR1` (Fig. 4), location extractors `owned`, `mut`, `all` (Fig. 5), move rules `MR1`–`MR3` (Fig. 6), statement rules `ST1`–`ST2` (Fig. 7), and `locate` (Fig. 8).
     - §3.2.2 (p. 4) & §4.2 (pp. 5–6): Outliving-Borrow set $OL$ and region-annotated refinement.
     - §3.3 & Figure 9 (p. 5): Operational semantics $(M, L)$ rules `L1`, `L2`, `R1` and Theorem 1 (memory safety).
     - §4.1 (p. 5) & §4.3 (p. 6): `Drop` LIFO destruction order counterexample and `x = &mut b` reborrow precision example.
     - §5 (p. 6): Single-threaded `&local` *Single Depth* and *Any Depth* aliasing claims.
   - Sergio Benitez, Jonathan Cogan & Alejandro Russo, *"Short Paper: Blockcheck the Typechain"*, ACM PLAS 2020, pp. 45–49, DOI `10.1145/3411506.3417600`, SHA-256 `7e76fe7b6c6f49d9b89d161de57588234ed9e351e4dea015145d70b742ffd0a0`:
     - §1 (p. 1): Whole-chain static admission $C'_\tau = C_\tau ; p$ and $\mathsf{blockcheck}(C_\tau)$.
     - §2.1–§2.5 (pp. 1–3): The 5 mandatory properties (`Auction` running example, Parity multi-sig bug, `GovernMental` 1,100 ETH gas exhaustion, TheDAO reentrancy, and $k-2$ frame exhaustion).
     - §3.1–§3.2 (pp. 3–4): Monotonic type-system strengthening ($\Gamma' \vdash' e : \tau \implies \Gamma \vdash e : \tau$, `Singleton<T>` Rules 0 & 1) and proof-witness type library (`Timed<C>`).
   - Karl Crary, David Walker & Greg Morrisett, *"Typed Memory Management in a Calculus of Capabilities"*, POPL 1999 (DOI `10.1145/292540.292564`) / ACM TOPLAS 22(4):701–771 (2000), SHA-256 `4092218c82e451d60746cee161af8031c2ba228ae4eca22be543dfc866bac70f`:
     - §2–§3 (pp. 7–29): Capability syntax $C ::= \epsilon \mid \emptyset \mid \{r^\varphi\} \mid C_1 \oplus C_2 \mid \bar{C}$, `freergn v`, subcapability relation $\{r^1\} \le \{r^+\}$, and bounded quantification $\forall[\rho_1, \rho_2, \epsilon \le \{\rho_1^+, \rho_2^+\}]$ for uniqueness recovery.
   - Brian N. Bershad et al., *"Extensibility, Safety and Performance in the SPIN Operating System"*, SOSP 1995 (DOI `10.1145/224056.224077`), SHA-256 `9e1dbd98482c67aef6213349db7838878169b1cad604e40879fb4217703923c6`, and Wilson C. Hsieh et al., *"Language Support for Extensible Operating Systems"*, WCSSS 1996, SHA-256 `051111c947d58f528e0573bdb1a88459c76157921b443d69ffc5000d2639be4d`.
   - Manuel Fähndrich et al., *"Language Support for Fast and Reliable Message-based Communication in Singularity OS"*, EuroSys 2006 (DOI `10.1145/1217935.1217953`), SHA-256 `3786a10efb28618520c5e5b789996e8de45225db4d53d12e39dc95ff3ccfeca5`, and Galen C. Hunt & James R. Larus, *"Singularity: Rethinking the Software Stack"*, ACM SIGOPS OSR 41(2):37–49 (2007, DOI `10.1145/1243418.1243424`), SHA-256 `1da2c58082d7b28544086636e50e7d1d1a449f3556ba8e351d81ac1370f3b8a2`.

2. **Preserved Mechanization and Empirical Probes in This Package (`support/`):**
   - [`support/MetalAndTypechainIsolation.lean`](support/MetalAndTypechainIsolation.lean): 1,422-line standalone Lean 4.34.1 mechanization proving 18 primary theorems (`0 sorryAx`, `0 Classical.choice`, `0 Lean.ofReduceBool`) covering `Metal` location extractors, `(CR1)`, `MoveStep` (`MR1`–`MR3`), `StmtStep` (`ST1`, `ST1-Rebind`, `ST2`), `WriteExclusive` preservation, Theorem 1 dereference progress, `OL` signature analysis, §4.1 `Drop` LIFO counterexample, §4.3 reborrow precision, §5 `&local` `AnyDepthSafe` soundness and `SingleDepth`/`AnyDepth` counterexamples, `Typechain` 5-way necessity, `Singleton<T>` monotonic strengthening, `Timed<C>` proof witnesses, and Singularity's send-state endpoint transfer rule.
   - [`support/metal_vs_rust_probes.rs`](support/metal_vs_rust_probes.rs), [`support/nll_reborrow_overwrite_probe.rs`](support/nll_reborrow_overwrite_probe.rs), and [`support/nll_prefix_rules_probe.rs`](support/nll_prefix_rules_probe.rs): Empirical `rustc` test suite verifying MIR NLL behavior on §3.2.2, §4.1, §4.2, and §4.3.

---

## Revalidation

To revalidate all mechanized theorems and empirical `rustc` observations in this package from the repository root:

1. **Verify the Lean 4.34.1 Mechanization and Axiom Audit:**
   ```bash
   lean reports/metal-typechain-language-isolated-kernels-1995-2026/support/MetalAndTypechainIsolation.lean
   ```
   Confirm that the command exits with code `0` and that the `#print axioms` output for all 18 theorems lists zero `sorryAx`, zero `Classical.choice`, and zero `Lean.ofReduceBool`.

2. **Re-run the `rustc` Empirical Probes (Positive and Negative Diagnostics):**
   ```bash
   rustc --edition=2021 reports/metal-typechain-language-isolated-kernels-1995-2026/support/metal_vs_rust_probes.rs -o /tmp/metal_vs_rust_probes && /tmp/metal_vs_rust_probes
   rustc --edition=2021 --cfg 'feature="fail_drop_lifo"' reports/metal-typechain-language-isolated-kernels-1995-2026/support/metal_vs_rust_probes.rs -o /tmp/fail_drop
   rustc --edition=2021 --cfg 'feature="fail_box_reassign"' reports/metal-typechain-language-isolated-kernels-1995-2026/support/nll_prefix_rules_probe.rs -o /tmp/fail_box
   ```
   Confirm that:
   - `/tmp/metal_vs_rust_probes` prints `All positive probes passed: sec4_3=(11, 22), sec4_1_no_drop=2, sec4_2=300`.
   - `--cfg 'feature="fail_drop_lifo"'` fails with `error[E0597]: p2 does not live long enough` when `ParentWithDrop` implements `Drop`.
   - `--cfg 'feature="fail_box_reassign"'` fails with `error[E0506]: cannot assign to x because it is borrowed` when `x` is an owned `Box<Q>` rather than `&mut Q`.
