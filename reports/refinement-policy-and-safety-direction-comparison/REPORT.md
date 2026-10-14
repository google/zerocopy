# Refinement, policy, and safety direction across compiler families

## Summary

LLVM refinement can legally remove source undefined behavior, so a safe refined target does not imply a safe source. A bounded SMT check, a kernel-checked refinement proof, a verified equivalence algorithm, and an ownership-checking safety theorem provide different evidence. Owlang's stated theorem includes an additional ownership and partial-safety argument; ordinary refinement does not supply it. RustCompCert's short paper contains an unresolved inclusion-direction wording conflict, retained here without converting it into an executable guarantee.

## Applicability

This is a theorem-direction comparison of primary CryptOpt2023, Alive2 PLDI2021, Jitterbug OSDI2020, the PLDI2022 inductive-computation paper, and four versioned preprints: Trivet `2609.19583v1`, EquiVM `2607.26306v1`, Owlang `2510.10015v1`, and RustCompCert `2602.07455v1`. The current source observations are limited to pinned CryptOpt, Alive2, Jitterbug, and Vellvm READMEs, plus public repository identities. They are not full implementation or dependency audits. No current Trivet/EquiVM/Owlang artifact was independently pinned and checked.

This addresses P025–P031, T028–T030, and partial T021/T043–T048. The finite witness is an original reduced semantics, not an upstream compiler experiment.

## Findings

### Optimization refinement and its checking path

**Basis: documentation from Alive2 §§5.1–5.3/7/8.1.** Refinement permits more-defined target values; target UB must be permitted by the source. Nondeterministic target outcomes need matching source outcomes under valid related inputs. Bounded loop unrolling excludes paths reaching the unrolling sink, leaving later iterations unexamined. The paper's TCB includes its implementation, Z3, and LLVM parsing. This is an SMT validation path, not an independently kernel-checked proof object for each transformation. [Primary paper](https://web.ist.utl.pt/nuno.lopes/pubs/alive2-pldi21.pdf).

**Basis: source.** `AliveToolkit/alive2@5d0eb277235b73f71000501c3a4f5ab9b2586915` README identifies the IR converter, symbolic executor, refinement checker, and SMT layer. It explicitly excludes interprocedural transformations and warns of spurious counterexamples for those passes. The paper's practical aim of avoiding false alarms cannot be generalized beyond its supported fragment or into a current blanket no-false-alarm guarantee.

**Basis: documentation from Trivet §2.1 Definition2.1 and §§3.3–3.4.** `src ⊒ tgt` permits arbitrary target behavior if the source triggers immediate UB; source poison permits poison or any value but excludes immediate target UB; a defined source value requires the same defined target value. The workflow constructs Lean semantic goals and scaffolds, then checks generated proofs or refutations in Lean. It excludes `undef`, memory operations, and floating-point arithmetic. Loop support covers a source entry preheader, one self-looping body with one backedge and exit, translated to a loop-free single-block target; general loops remain future work. A kernel-valid theorem establishes the encoded proposition; faithful LLVM-to-Lean encoding remains a separate obligation. [Versioned preprint](https://arxiv.org/pdf/2609.19583v1).

### Verified equivalence checking and JIT preservation

**Basis: documentation from CryptOpt §§6.1–6.4, PDF pp.15–17.** Symbolic interpreters for restricted Fiat IR and x86-64 assembly use common logical inputs and an E-graph equality checker. Correctness of symbolic execution connects the expressions to original modeled executions; equivalent output nodes imply equivalent programs. The random optimizer is outside the equivalence argument. The executable checker is extracted; paper guarantees remain relative to modeled instruction semantics and supported straight-line code. [Versioned full paper](https://arxiv.org/pdf/2211.10665v3).

The pinned CryptOpt README describes feeding optimized assembly back into Fiat Cryptography for checking. Its producer pin `c089d8ce3cace748a0a22e25d7adfbf2cfc6a883` does not identify a compiled checker binary. The separately observed Fiat Cryptography repository identity is `b4ad623c6a5bde0c71169493963a308c612fce3f`; the current checker theorem and complete extraction path were not audited here.

**Basis: documentation from Jitterbug §4.1 Definition1, §4.2 Theorem1, §6–§7.** The theorem assumes a safe source program and well-formed JIT context. It preserves source/target traces and return values and checks target calling-convention state preservation. Source safety includes terminating without UB. Stepwise prologue/instruction/epilogue obligations imply whole-JIT correctness. The SMT/Rosette verification checks DSL JITs; extraction to C is unverified, and existing C JITs are manually translated, with separate encoding checks. This does not verify arbitrary current Linux JIT source or the eBPF admission verifier. [Primary paper](https://www.usenix.org/system/files/osdi20-nelson.pdf).

The selected Jitterbug pin `78d1e75ad506498b585fbac66985ff9d9d05952d` README distinguishes architecture C files from Racket implementations. It supplies concrete artifact coordinates; no new per-instruction obligation or C/DSL correspondence was executed.

### Binary refinement can have explicit exceptional allowances

**Basis: documentation from EquiVM §5/Fig.9, PDF pp.15–16.** `runtimeEquiv` universally quantifies over related EVM/specification account states and calls, requires exact code, protocol permission, and bounded calldata length, then requires a refinement judgment. Cases include related normal outcomes, shared dispatch/decode rejection, and an out-of-gas allowance. Deterministic bytecode behavior is included in the nondeterministic specification; termination is a separate obligation. Constructor verification also binds returned deployed bytes to expected runtime code. [Versioned preprint](https://arxiv.org/pdf/2607.26306v1).

**Basis: derived.** The exception allowance is part of the proposition, not a defect or a total-correctness guarantee. An Anneal admission theorem should similarly say which aborts, timeouts, resource failures, or panics are allowed. Universal state quantification and exact byte identity are valuable only when the paired specification's meaning is independently justified.

### Ownership checking adds a safety argument

**Basis: documentation from Owlang §5 Theorems5.1–5.2, PDF pp.19–20.** Successful compilation gives open backward simulation. The separate open-safety theorem assumes source partial safety with memory errors ignored, then concludes total source and target safety under the ownership interface `Iown`, translating the target interface through calling convention `RRA`. Ownership checking supplies the memory-safety component that ordinary preservation does not. The result concerns Owlang and its stated composition interfaces, not unrestricted Rust. [Versioned preprint](https://arxiv.org/pdf/2510.10015v1).

**Unresolved primary-source conflict: RustCompCert §2, PDF p.2.** The short ongoing-work paper writes `⟦target⟧ ⩽ ⟦source⟧`, calls this backward simulation, but explains it as inclusion of source behaviors in target behaviors. Those are opposite inclusion descriptions under the ordinary convention. No interpretation is selected here. Its borrow-checking footnote separately limits safety to partial safety: its authors cite division by zero as an example in their formal safety account. That terminology is not normative Rust: ordinary integer division by zero in Rust [panics](https://github.com/rust-lang/reference/blob/ad35aca481751a06afeb23820a672b0f3b11a476/src/expressions/operator-expr.md#L403). The borrowed safety claim must be read in the paper's own semantics. Its parser is explicitly unverified and the supported sequential fragment excludes several major Rust features. [Versioned short paper](https://arxiv.org/pdf/2602.07455v1).

The equation/prose conflict prevents using this paper alone as a load-bearing end-to-end safety-direction premise. Resolving it requires the actual semantic relation and checked theorem in its artifact, rather than assuming either sentence is authoritative enough. This is not a claim that the compiler implementation has a soundness bug.

### Relation-derived checks are still checks of that relation

**Basis: documentation from the PLDI2022 inductive-computation paper, §3/Fig.1 and §6.3.** Derived partial checkers use `Some true`, `Some false`, and `None` for positive decision, negative decision, and exhausted fuel. The work derives soundness/completeness proofs for supported inductive relations and can use a proved checker for reflection. This does not provide semantic correctness of an arbitrary relation supplied by a compiler designer. [Primary author paper](https://lemonidas.github.io/pdf/ComputingCorrectly.pdf).

The selected Vellvm README at `4c6db50077cbc0df3fb3156c0570129201cc35f3` describes an ongoing formal LLVM-inspired compilation infrastructure and separates building an interpreter from all metatheory. No current Vellvm transformation theorem was inspected deeply enough to supply an additional compiler-preservation endpoint here. Formal semantics, executable interpreter, and proved compiler transformation are different artifacts.

### Original discriminating finite witness

**Basis: execution and derived, original reduced model.** `relation_endpoint_witness.py` exhaustively checks a four-outcome refinement relation: UB, poison, and two defined values. It demonstrates an accepted refinement from source UB to a defined target, while source failure remains true; a safe but wrong-answer target passes the weak target policy and fails refinement; and a transformation can match inputs0–3 while differing at input4. These examples distinguish safety reflection, policy strength, and bounded evidence. They are neither implementations nor proofs of any upstream system.

### Derived Anneal taxonomy and maintenance implications

For each admitted artifact, record the proposition, input class, failure/resource allowances, artifact identity, proof-producing or proved-checker execution path, and unresolved semantic obligations. Kernel checking protects the proof of an encoded relation; it does not establish that source parsing, target encoding, or the selected relation captures every unsafe operation. A verified checker removes its algorithm from the proof assumptions only with an appropriate implementation/execution bridge.

Ordinary UB refinement deliberately permits safe target code for an unsafe source. Anneal needs source-failure reflection or a separately proved source-admission argument to conclude source safety. Jitterbug-style safe-source premises likewise cannot prove the premise they assume. Owlang shows the shape of an additional ownership-checking argument, while its interface obligations remain part of the result.

Maintenance includes changing instruction semantics, adding representations/effects, proving new checker rules, revalidating artifact bindings, and maintaining unsupported/unknown outcomes. The compiler and checker may evolve independently only while the acceptance theorem remains matched to the actual pair and consumer's intended property.

## Boundaries

No LLVM, Lean, Rocq, SMT, CryptOpt, Jitterbug, Vellvm, EquiVM, Owlang, or RustCompCert toolchain was built or executed. Finite-model execution cannot substitute for upstream proof replay. The current source evidence is deliberately narrow. Preprint identities and theorem coordinates do not establish present-day artifact availability, proof completeness, or executable-path safety. P026 current implementation, P028 deployed loader/environment, P029 ownership artifact, and P030 theorem direction remain incomplete.

## Evidence

- Alive2, PLDI2021, DOI `10.1145/3453483.3454030`, 15-page author PDF; §§5/7/8.1. README blob `372a07fc19b0967be02217c01302a59820a7b7d6`.
- CryptOpt full paper `arXiv:2211.10665v3`, 2023-05-22, 32 pages; §§6.1–6.4; artifact DOI `10.5281/zenodo.7710435` identified but not executed. Producer README blob `dabb2871b3dda26ebef571e7d71d12691ecda290`.
- Jitterbug, OSDI2020, primary USENIX paper, 22-page PDF; §§4/6/7; README blob `c4f57da601d1ee124913f16efd14f651ef88bd95`.
- Trivet `arXiv:2609.19583v1`, 2026-09-17, 14 pages; EquiVM `arXiv:2607.26306v1`, 2026-07-28, 34 pages; Owlang `arXiv:2510.10015v1`, 2025-10-11, 34 pages; RustCompCert `arXiv:2602.07455v1`, 2026-02-07, 3 pages. Narrow theorem coordinates above.
- Paraskevopoulou/Eline/Lampropoulos, *Computing Correctly with Inductive Relations*, PLDI2022, 15-page author PDF; §3/Fig.1 and §6.3. Vellvm README blob `08d549602a4f146e6f2016013c2fdb82741be1ff`.
- Primary paper/source acquisition and independent finite witness on2026-10-14. No PDF byte hashes, private mirrors, or upstream executable results are claimed.

## Revalidation

Retrieve versioned PDFs and pinned source files; verify actual relation definitions, supported cases, proof dependencies, and acceptance/rejection handling. Resolve the RustCompCert conflict against its checked artifact before relying on its direction. Pin and replay Trivet/EquiVM/Owlang evidence before executable claims. Run the preserved finite witness with Python3.10+ to reproduce only the illustrative reduced outcomes.

*Authored by an AI agent acting on joshlf's behalf.*
