<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Putnam's Model-Theoretic Permutation Theorem, Syntax-Semantics Dualism, Emitter Non-Surjectivity, and the Irreducible TCB Boundary in Semantic Verification

## Summary

Across sixteen evolutionary candidates (`Candidate 001`–`016`) and forty adversarial red-team evaluations (`PENTEST-1`..`10`, `PENTEST-R2-1`..`10`, `PENTEST-R3-1`..`10`, `PENTEST-R4-1`..`10`) of a 4-primitive semantic compiler-verification framework (`Language`, `Tool`, `BehaviorCodec`, `Spec`), two structural pathologies recurred whenever the framework attempted to verify concrete assembly emission (`emit : L_tgt.Prog → String` or `ByteArray`) or shrink the human-audited Trusted Computing Base (TCB) via in-kernel structural, cardinal, or lexical predicates:

1. **Category B Semantic Spoofing of Concrete Syntax (`PENTEST-9`, `PENTEST-R2-1`, `PENTEST-R3-4`):**
   - When `emit : L_tgt.Prog → String` was left uninterpreted (`PENTEST-9`, `Candidate 003`), `emit := fun _ => "xor eax, eax; ret"` compiled cleanly.
   - When `Candidate 006` required `emit` to refine a round-trip parsed language `L.diskLang parse` (`PENTEST-R2-1`), defining `emit := fun _ => "rm -rf /"` and `parse := fun _ => some .good` satisfied every refinement obligation by definitional equality.
   - When `Candidate 008` required `emit` to refine a standalone assembly language `L_asm` with witness non-degeneracy (`EmitterCompilesWithWitnesses`, `PENTEST-R3-4`), a trojan emitter `emit := fun _ => "xor eax, eax\nret"` passed all 22 bundle obligations by permuting `L_asm.sem` so that `"xor eax, eax\nret"` evaluated to $q + 1$ while `"mov eax, edi; inc eax; ret"` evaluated to $0$.

2. **Category A2 Honest-Tool Lockout paired with Category A1/B Bypass (`PENTEST-R4-2A/B`, `PENTEST-R4-8`):**
   - To block `PENTEST-R3-4`, `Candidate 016` introduced `CanonicalAsmSemantics` (forcing any string whose first non-whitespace mnemonic is `"xor eax, eax"` or `"mov eax, 0"` to evaluate to $0$) and extended `EmitterCompilesWithWitnesses` with query-sensitive surjectivity ($\forall s \in L_{\text{asm}}.\text{Prog},\ \text{QuerySensitive}(s) \to \exists p,\ \text{emit}(p) = s$).
   - The lexical rule (`isZeroClearAsmMnemonic`) simultaneously **locked out** honest multi-instruction routines that initialize an accumulator via `"xor eax, eax\nmov eax, edi\nadd eax, 1\nret"` (`PENTEST-R4-2A`) and was **bypassed** by prepending an assembly label `"main:\nxor eax, eax\nret"` (`PENTEST-R4-2B`).
   - Query-sensitive surjectivity (`PENTEST-R4-8`) rendered `EmitterCompilesWithWitnesses` **logically unsatisfiable (`False`)** whenever the number of query-sensitive assembly programs exceeded $|L_{\text{tgt}}.\text{Prog}|$—locking out every single-program IR ($|L_{\text{tgt}}.\text{Prog}| = 1$) from compiling into any realistic ISA with $\ge 2$ distinct functions ($q + 1$ and $q + 2$).

This report establishes and mechanizes in standalone, zero-axiom Lean 4 (`v4.34.1`, [support/PutnamPermutationAndTcbBoundary.lean](support/PutnamPermutationAndTcbBoundary.lean), 1,842 lines) the three foundational model-theoretic and compiler-correctness laws governing the syntax-semantics boundary, together with a complete **40-Exploit Diagnostic Taxonomy** and a unified **Next-Generation Semantic Verification Blueprint (`NextGen`)**:

1. **The Model-Theoretic Syntax-Permutation Invariance Theorem (`PutnamSyntaxPermutationTheorem`):** Formalizing the Newman (1928) and Putnam (1980) permutation argument within Goguen and Burstall's (1992) theory of institutions, for any language $L : \text{Language } \text{SemObs}$ and any bijection $\pi : \text{SyntaxPerm } L.\text{Prog}$ on its syntax carrier, the syntax-permuted language $\pi^*(L)$ (`L.permProg π`, with `sem s q := L.sem (π s) q`) is **100% invariant** under every purely extensional, structural, or finite-witness predicate (`SafeAt`, `Produces`, `ProductiveOn`, `DeterministicOn`, `QuerySensitiveOn`, `NonChaoticOn`, `HasProductiveContrastOn`, `WellBehavedProgOn`, `TotalWellBehavedDomainOn`, `SemanticallyClosedOn`, `BiNonInterferingOn`, `VerifiedSpineOn`, and `EmitterCompilesWithWitnessesOn`). Consequently, no purely structural in-kernel predicate can distinguish an honest assembly emitter into $L_{\text{asm}}$ from a conjugated trojan emitter $\pi^{-1} \circ \text{emit}$ into $\pi^*(L_{\text{asm}})$ (`pentest_r3_4_corollary_trojan_emitter_passes_under_permuted_semantics`), nor can a round-trip parser `L.diskLang parse` ever constrain `emit` (`pentest_r2_1_circular_diskLang_universal_tautology`). Binding concrete syntax (`String`, `ByteArray`, or `List AsmInstr`) to operational behavior irreducibly requires an audited operational semantics `L_isa.sem` in the TCB.
2. **Dual Failure of Lexical Prefix Heuristics (`LexicalHeuristicDualFailureTheorem` & `prefix_classifier_universal_impossibility`) and Emitter Surjectivity Impossibility (`EmitterSurjectivityImpossibility`):** On any stateful sequential instruction language where instructions compose as state transformers ($\llbracket i_1 ; i_2 \rrbracket = \llbracket i_2 \rrbracket \circ \llbracket i_1 \rrbracket$), any prefix or wildcard classifier that flags a state-clearing instruction (`xor eax, eax`) as globally constant suffers both **False Positives (Honest Lockout, `PENTEST-R4-2A`)** on sequential composition (`[zeroClear, loadAndInc]`) and **False Negatives (Labelled Trojan Bypass, `PENTEST-R4-2B`)** on no-op/label prefixes (`[label "main", zeroClear]`); more generally, **no** $k$-instruction prefix classifier can separate constant-zero routines from accumulator-initialized routines (`prefix_classifier_universal_impossibility`). Independently, requiring `emit` to be surjective onto query-sensitive target programs (`PENTEST-R4-8`) contradicts the cardinal nature of compilation as an **injective/refining embedding** into a strictly richer target language (`EmitterSurjectivityImpossibility`, `pentest_r4_8_single_ir_multi_isa_impossible`).
3. **The 40-Exploit Diagnostic Taxonomy and Next-Generation Minimal Semantic Blueprint (`NextGen`):** Synthesizing all 40 pentest exploits across `Candidate 001`–`016`, we construct and kernel-verify the `NextGen` framework in Lean 4 around 4 orthogonal primitives (`Language`, `Tool`, `FramedCodec`, `Spec`), a single canonical base bundle (`VerifiedCompilerBase`), and an `extends`-based inheritance hierarchy (`VerifiedConstantTimeCompiler`, `VerifiedArtifactPipeline`) that makes clause-drop regressions (`PENTEST-R4-10A/B`) structurally impossible, resolves ABI scratch-register lockouts (`PENTEST-R4-1`), partial-domain lockouts (`PENTEST-R4-3`), and left-associated tuple leakage bypasses (`PENTEST-R4-5A/B`), and isolates the **Irreducible 5-Noun Auditor Boundary**.

---

## Applicability

The findings, impossibility theorems, and mechanized blueprint in this report apply to:

- **Trusted Computing Base (TCB) design in proof assistants** (Lean 4 `v4.34.1`, Coq/Rocq, Isabelle/HOL, HOL4) for verified compilers, static analyzers, translation validators, and artifact emitters (compare Pollack 1998; Leroy 2009; Kumar et al. 2014).
- **Abstract semantic frameworks** parameterized over user-supplied language denotations (`Language`), partial transformations (`Tool`), query/outcome codecs (`BehaviorCodec` / `FramedCodec`), and input/output specifications (`Spec`).
- **Security and red-team auditing of formal specifications**, specifically distinguishing errors that can be eliminated by stronger in-kernel relational definitions (**Category A1** soundness bypasses) without rejecting real compilers (**Category A2** honest-tool lockouts) from obligations that mathematically require human inspection of concrete domain bindings (**Category B** TCB boundaries).

All Lean 4 theorems referenced in this report are self-contained and kernel-checked in [support/PutnamPermutationAndTcbBoundary.lean](support/PutnamPermutationAndTcbBoundary.lean) under Lean `v4.34.1` (`commit 5045d0056413266e57c625dcd7c365b10e377c52`) with `-DElab.async=false -Ddebug.skipKernelTC=false` and depend only on standard Lean axioms (`propext` and `Quot.sound`, with zero `sorryAx` and zero `Classical.choice`).

---

## Findings

### Finding 1: Putnam's Model-Theoretic Permutation Theorem for Semantic Frameworks (`PutnamSyntaxPermutationTheorem`)

`Basis: normative + source + execution + derived`

#### 1.1 Theoretical Foundation: Newman (1928), Putnam (1980), and Goguen–Burstall Institutions (1992)

In 1928, M. H. A. Newman observed against Russell's structural realism that any system of relations specified purely up to isomorphism is satisfied by any set of the appropriate cardinality: given any bijection $\pi$ on the underlying carrier, pushing a relation structure forward along $\pi$ yields an isomorphic model satisfying identical purely structural sentences (Newman 1928, *Mind* 37(146):137–148). Hilary Putnam generalized this observation into the **Model-Theoretic Permutation Theorem** (Putnam 1980, *Journal of Symbolic Logic* 45(3):464–482): given any model $\mathcal{M}$ and any permutation $\pi$ of the individuals of $\mathcal{M}$ that induces a permutation of reference assignments while holding truth-values at every world/query constant, the permuted interpretation $\pi^*(\mathcal{M})$ makes the exact same sentences true under the exact same operational observations.

Translated into Goguen and Burstall's theory of **Institutions** (Goguen & Burstall 1992, *JACM* 39(1):95–146) and verified compiler architectures such as **CompCert** (Leroy 2009, *CACM* 52(7):107–115) and **CakeML** (Kumar, Myreen, Norrish, & Owens 2014, *POPL*, pp. 179–191):

- A programming language inside a semantic framework is a signature-model pair $L = (\text{Prog}, \text{Query}, \text{Out}, \text{obs}, \text{sem}, \text{dom})$ where $\text{Prog}$ is the **syntactic carrier** (e.g., `String`, `ByteArray`, or an AST type) and $\text{sem} : \text{Prog} \to \text{Query} \to \text{Partial}(\text{Out} \to \text{Prop})$ is the **evaluation functor**.
- Every relational or structural predicate inside a generic verification module (`Trusted/Refinement.lean`) quantifies over $p \in L.\text{Prog}$ only through $L.\text{sem}(p)$ and equality on $L.\text{Prog}$.
- Therefore, if $\pi : L.\text{Prog} \simeq L.\text{Prog}$ is any bijection on the syntax carrier, pulling $L.\text{sem}$ back along $\pi$ defines a syntax-permuted language $\pi^*(L)$ (`L.permProg π`) whose syntax-semantics binding is permuted by $\pi$, while its entire extensional model structure is isomorphic to $L$.

#### 1.2 Mechanized Statement (`PutnamSyntaxPermutationTheorem`)

In [support/PutnamPermutationAndTcbBoundary.lean](support/PutnamPermutationAndTcbBoundary.lean) (lines 360–433), we define a constructive syntax permutation `SyntaxPerm α` with two-sided inverse proofs (`left_inv`, `right_inv`), the permuted language `L.permProg π`:

```lean
abbrev Language.permProg {SemObs : Type w} (L : Language SemObs)
    (π : SyntaxPerm L.Prog) : Language SemObs where
  Prog  := L.Prog
  Query := L.Query
  Out   := L.Out
  obs   := L.obs
  sem   := fun s q => L.sem (π.toFun s) q
  dom   := L.dom
```

the conjugated tool `Tool.permProg π₁ π₂ T := fun s => (T (π₁.toFun s)).map π₂.invFun`, and the induced codec `c.toPermTgt π`.

We then prove step-by-step invariance for every semantic and structural predicate introduced across `Candidate 001`–`016` (lines 438–770):

| Predicate / Bundle | Invariance Theorem in `PutnamPermutationAndTcbBoundary.lean` | Mathematical Statement |
| :--- | :--- | :--- |
| `SafeAt` | `permProg_safeAt_iff` (L443) | $\pi^*(L).\text{SafeAt}(s, q) \iff L.\text{SafeAt}(\pi(s), q)$ |
| `Produces` | `permProg_produces_iff` (L450) | $\pi^*(L).\text{Produces}(s, q, v) \iff L.\text{Produces}(\pi(s), q, v)$ |
| `ProductiveOn` | `permProg_productiveOn_iff` (L457) | $\pi^*(L).\text{ProductiveOn}(\text{pre}, s) \iff L.\text{ProductiveOn}(\text{pre}, \pi(s))$ |
| `DeterministicOn` | `permProg_deterministicOn_iff` (L464) | $\pi^*(L).\text{DeterministicOn}(\text{pre}, s) \iff L.\text{DeterministicOn}(\text{pre}, \pi(s))$ |
| `QuerySensitiveOn` | `permProg_querySensitiveOn_iff` (L471) | $\pi^*(L).\text{QuerySensitiveOn}(\text{pre}, s) \iff L.\text{QuerySensitiveOn}(\text{pre}, \pi(s))$ |
| `NonChaoticOn` | `permProg_nonChaoticOn_iff` (L478) | $\pi^*(L).\text{NonChaoticOn}(\text{pre}, s) \iff L.\text{NonChaoticOn}(\text{pre}, \pi(s))$ |
| `WellBehavedProgOn` | `permProg_wellBehavedProgOn_iff` (L485) | $\pi^*(L).\text{WellBehavedProgOn}(\text{pre}, s) \iff L.\text{WellBehavedProgOn}(\text{pre}, \pi(s))$ |
| `HasProductiveContrastOn` | `permProg_hasProductiveContrastOn_iff` (L514) | $\pi^*(L).\text{HasProductiveContrastOn}(\text{pre}, s) \iff L.\text{HasProductiveContrastOn}(\text{pre}, \pi(s))$ |
| `VerifiedSpineOn` | `permProg_verifiedSpineOn_iff` (L542) | $\pi^*(L).\text{VerifiedSpineOn}(\text{dom}, \text{pre}, \text{post}, s) \iff L.\text{VerifiedSpineOn}(\text{dom}, \text{pre}, \text{post}, \pi(s))$ |
| `SpineNonDegenerate` | `permProg_spineNonDegenerate_iff` (L573) | $\pi^*(L).\text{SpineNonDegenerate}(\text{pre}, \text{post}, s, b) \iff L.\text{SpineNonDegenerate}(\text{pre}, \text{post}, \pi(s), \pi(b))$ |
| `TotalWellBehavedDomainOn` | `permProg_totalWellBehavedDomainOn_iff` (L593) | $\pi^*(L).\text{TotalWellBehavedDomainOn}(\text{pre}) \iff L.\text{TotalWellBehavedDomainOn}(\text{pre})$ |
| `SemanticallyClosedOn` | `permProg_semanticallyClosedOn_iff` (L650) | $\text{SemanticallyClosedOn}(\text{pre}, \pi^*(T)) \iff \text{SemanticallyClosedOn}(\text{pre}, T)$ |
| `BiNonInterferingOn` | `permProg_biNonInterferingOn_iff` (L673) | $\pi^*(L).\text{BiNonInterferingOn}(\text{pre}, \approx_L, \approx_{\text{leak}}, s) \iff L.\text{BiNonInterferingOn}(\text{pre}, \approx_L, \approx_{\text{leak}}, \pi(s))$ |
| `EmitterCompilesWithWitnessesOn` | `PutnamSyntaxPermutationTheorem` (L709) | Full conjunction of `EmitterCompilesWithWitnessesOn`, `HasProductiveContrastOn`, `WellBehavedProgOn`, and `TotalWellBehavedDomainOn` is invariant under $\text{emit}'(p) := \pi^{-1}(\text{emit}(p))$ and $b' := \pi^{-1}(b)$ |

#### 1.3 Corollary 1A (`PENTEST-R3-4`): Trojan Assembly Emission Under Transposed Semantics

In `pentest_r3_4_corollary_trojan_emitter_passes_under_permuted_semantics` (lines 775–871), we instantiate `PutnamSyntaxPermutationTheorem` on concrete x86-64 assembly strings:
- Let `goodX86Asm := "mov eax, edi\nadd eax, 1\nret"` and `trojanZeroX86Asm := "xor eax, eax\nret"`.
- Let `L_x86_real` give `goodX86Asm` the semantics $q \mapsto q + 1$, `trojanZeroX86Asm` the constant semantics $q \mapsto 0$, and `"ud2\nret"` undefined behavior (`Partial.ub`), with non-trivial contract precondition $q < 100$.
- The honest emitter `honestEmit (.addOne) := goodX86Asm` satisfies all four components of `PutnamSyntaxPermutationTheorem` against `L_x86_real` (`honestEmit_passes_on_real_x86`, L818).
- Applying the involutive transposition $\pi_{\text{spoof}} := \text{SyntaxPerm.swap}\ \text{goodX86Asm}\ \text{trojanZeroX86Asm}$ produces `L_x86_spoof := L_x86_real.permProg π_spoof` and the conjugated emitter `trojanEmit := fun p => π_spoof.invFun (honestEmit p)`.
- By a single rewrite with `PutnamSyntaxPermutationTheorem`, `trojanEmit` satisfies **every** obligation of `EmitterCompilesWithWitnessesOn`, `HasProductiveContrastOn`, `WellBehavedProgOn`, and `TotalWellBehavedDomainOn` on `L_x86_spoof`—while literally outputting `"xor eax, eax\nret"` (`trojanEmit .addOne = trojanZeroX86Asm`)!

#### 1.4 Corollary 1B (`PENTEST-R2-1`): Universal Tautology of Round-Trip `L.diskLang parse`

In `pentest_r2_1_circular_diskLang_universal_tautology` (lines 888–924), we formalize `Candidate 006`'s `L.diskLang parse` construction:
```lean
abbrev Language.diskLang {SemObs : Type w} (L : Language SemObs)
    (parse : String → Option L.Prog) : Language SemObs where
  Prog  := String
  Query := L.Query
  Out   := L.Out
  obs   := L.obs
  sem   := fun s q =>
    match parse s with
    | some p => L.sem p q
    | none   => Partial.ub
  dom   := L.dom
```
and prove that for **any** target language `L`, **any** constant string `maliciousDiskPayload : String` (such as `"rm -rf /\n"`), and **any** emitter `emit : L.Prog → String` accompanied by a one-sided inverse `parse : String → Option L.Prog` (`∀ t, parse (emit t) = some t`), `EmitterCompilesOn L (L.diskLang parse) (BehaviorCodec.id L) emit` holds **unconditionally** (`does not depend on any axioms`). Because `L.diskLang parse` defines the meaning of a disk string by running `parse` and delegating back to `L.sem`, the round-trip check is a pure syntax-relabeling tautology with zero semantic contact with the target machine.

---

### Finding 2: Impossibility of Lexical Heuristics (`PENTEST-R4-2A/B`) and Emitter Surjectivity (`PENTEST-R4-8`)

`Basis: normative + source + execution + derived`

#### 2.1 Dual Failure of Lexical Prefix/Substring Heuristics on Stateful Sequential Languages (`LexicalHeuristicDualFailureTheorem` & `prefix_classifier_universal_impossibility`)

To prevent `PENTEST-R3-4` without auditing `L_asm.sem`, `Candidate 016` added `CanonicalAsmSemantics` to `Trusted/Refinement.lean`, requiring that any assembly string `s` satisfying `isZeroClearAsmMnemonic s = true` (checking whether the first non-whitespace line starts with `"xor eax, eax"`, `"sub eax, eax"`, or `"mov eax, 0"`) must evaluate to `0` on every query.

In [support/PutnamPermutationAndTcbBoundary.lean](support/PutnamPermutationAndTcbBoundary.lean) (lines 933–1098), we model a faithful sequential instruction language `L_seq_asm` over registers `{ edi : Nat, eax : Nat }` with four instruction forms (`AsmInstr.zeroClear`, `AsmInstr.loadAndInc`, `AsmInstr.label`, `AsmInstr.trap`) and sequential state-transformer semantics:
$$\text{evalSeq}([], \sigma) = \text{some }\sigma, \qquad \text{evalSeq}(i :: \text{rest}, \sigma) = \text{evalInstr}(i, \sigma) \gg\!\!= \text{evalSeq}(\text{rest}).$$
Because `evalInstr` composes sequentially:
1. `trojanZeroProg := [.zeroClear]` evaluates to $0$ on every query $q$.
2. `honestAccumInitProg := [.zeroClear, .loadAndInc]` (corresponding to `"xor eax, eax\nmov eax, edi\nadd eax, 1\nret"`, which initializes `eax := 0` before computing `eax := edi + 1`) evaluates to $q + 1$ on every query $q$.
3. `labelledTrojanZeroProg := [.label "main", .zeroClear]` (corresponding to `"main:\nxor eax, eax\nret"`) evaluates to $0$ on every query $q$.

We prove two theorems demonstrating that no lexical/prefix heuristic can salvage `CanonicalAsmSemantics`:

- **`LexicalHeuristicDualFailureTheorem` (L1002):**
  1. **Part A (`PENTEST-R4-2A` Honest Lockout):** Under `isZeroClearLeading` (or `containsZeroClearAnywhere`), `honestAccumInitProg` is flagged `true`, yet it produces $q + 1 = 1 \neq 0$ at $q = 0$. Therefore, `CanonicalZeroClearRule isZeroClearLeading` (and `CanonicalZeroClearRule containsZeroClearAnywhere`) is **refuted (`¬ CanonicalZeroClearRule ...`)** on the true operational semantics `L_seq_asm`! Any compiler that emits accumulator zero-initialization is locked out.
  2. **Part B (`PENTEST-R4-2B` Labelled Trojan Bypass):** `labelledTrojanZeroProg` (`[.label "main", .zeroClear]`) has `isZeroClearLeading labelledTrojanZeroProg = false`, yet evaluates to $0$ on every query in `L_seq_asm`. Thus a trojan emitter need only prepend a label `"main:\n"` to evade `isZeroClearLeading` completely and execute the `PENTEST-R3-4` semantics-permutation attack.
- **`prefix_classifier_universal_impossibility` (L1035):** For **every** lookahead bound $k \in \mathbb{N}$ and **every** classifier $H : \text{List AsmInstr} \to \text{Bool}$ that depends only on the first $k$ instructions ($\text{List.take } k\ p_1 = \text{List.take } k\ p_2 \implies H(p_1) = H(p_2)$), there exist a constant-zero program $p_{\text{zero}} := \text{replicate } k\ (\text{label } \text{"nop"}) \mathbin{++} [\text{zeroClear}]$ and a query-sensitive accumulator program $p_{\text{accum}} := \text{replicate } k\ (\text{label } \text{"nop"}) \mathbin{++} [\text{zeroClear}, \text{loadAndInc}]$ such that $H(p_{\text{zero}}) = H(p_{\text{accum}})$, so $H$ **cannot** both flag $p_{\text{zero}}$ (`H p_zero = true`) and satisfy `CanonicalZeroClearRule H` on `L_seq_asm`.

#### 2.2 Cardinality and Expressiveness Impossibility of Emitter Surjectivity (`EmitterSurjectivityImpossibility`, `PENTEST-R4-8`)

Also in `Candidate 016`, `EmitterCompilesWithWitnesses` added a fourth conjunct (`EmitterQuerySensitiveSurjective`, lines 1106–1113):
$$\forall s \in L_{\text{asm}}.\text{Prog},\ \big(L_{\text{asm}}.\text{ProductiveOn}(\text{pre}_{\text{asm}}, s) \land L_{\text{asm}}.\text{QuerySensitiveOn}(\text{pre}_{\text{asm}}, s)\big) \implies \exists p \in L_{\text{tgt}}.\text{Prog},\ L_{\text{tgt}}.\text{ProductiveOn}(\text{pre}_{\text{tgt}}, p) \land \text{emit}(p) = s.$$

In `EmitterSurjectivityImpossibility` (lines 1118–1147), we prove that whenever:
1. $L_{\text{tgt}}$ has at most one productive program on $\text{pre}_{\text{tgt}}$ ($\forall p_1, p_2,\ \text{ProductiveOn}(p_1) \to \text{ProductiveOn}(p_2) \to p_1 = p_2$), and
2. $L_{\text{asm}}$ contains two distinct programs $s_1 \neq s_2$ that are both productive and query-sensitive on $\text{pre}_{\text{asm}}$,

then `EmitterQuerySensitiveSurjective` is **logically false (`¬ EmitterQuerySensitiveSurjective ...`)** for **every** function `emit : L_tgt.Prog → L_asm.Prog`! In `pentest_r4_8_single_ir_multi_isa_impossible` (lines 1173–1220), we instantiate this theorem on `L_simple_ir` (whose sole productive program computes $q + 1$) and `L_two_func_isa` (which has `"mov eax, edi; add eax, 1; ret"` computing $q + 1$ and `"mov eax, edi; add eax, 2; ret"` computing $q + 2$). Because compilation is a **forward refinement / injective embedding** of a specialized IR into a general-purpose ISA, requiring an emitter to be *surjective* onto all query-sensitive ISA programs is a category error that renders verification impossible for any realistic target ISA.

---

### Finding 3: Complete 40-Exploit Diagnostic Taxonomy (`Candidate 001`–`016`)

`Basis: normative + source + execution + derived`

Across the 16-candidate design evolution and 4 rounds of adversarial evaluation (`PENTEST-1`..`10`, `PENTEST-R2-1`..`10`, `PENTEST-R3-1`..`10`, `PENTEST-R4-1`..`10`), every failure falls into one of three diagnostic classes:

- **Category A1 (In-Kernel Relational Soundness Bypass):** A flaw in the mathematical definition of refinement, codec framing, domain preservation, non-interference, or bundle inheritance inside `Trusted/Refinement.lean` that allows a buggy or malicious tool to pass even when the 5 Domain Nouns are honestly instantiated. *Fixable in-kernel without locking out honest tools.*
- **Category A2 (In-Kernel Over-Constraint / Honest-Tool Lockout):** An overly rigid in-kernel requirement (such as exact state bijection `encodeOut (decodeOut o) = o`, global domain totality `TotalWellBehavedDomain`, prefix regex `isZeroClearAsmMnemonic`, or emitter surjectivity) that rejects real, standard compiler pipelines. *Must be relaxed to its exact relational invariant (lens frame preservation, explicit `AcceptedDom` subset coverage, forward refinement).*
- **Category B (Irreducible Domain-Noun TCB Boundary):** An attack that succeeds by instantiating one of the concrete domain nouns (`L_src.sem`, `L_isa.sem`, `T.run`, `codec.embedQuery`, `S.obsPost`/`AcceptedDom`) with a dishonest, trivial, or permuted definition. By Putnam's Permutation Theorem (Finding 1) and Gold/Angluin finite-witness impossibility, *Category B boundaries cannot be eliminated by in-kernel structural predicates; attempting to do so invariably causes Category A2 lockouts while leaving Category B open.*

#### 3.1 Master Diagnostic Table of All 40 Pentest Exploits

| Exploit ID | Target Candidate | Attack Vector / Counterexample | Diagnostic Category | Root Mathematical Cause & NextGen Resolution |
| :--- | :--- | :--- | :--- | :--- |
| `PENTEST-1` | `Candidate 003` | `Spec.True` (`obsPost := fun _ _ => True`) admits any output | **Cat A1 + Cat B** | Vacuous postcondition. Resolved by `VerifiedSpineOn` contrast + TCB Noun 5 (`S.obsPost`) audit. |
| `PENTEST-2` | `Candidate 003` | `Spec.False` (`pre := fun _ => False`) vacuously verifies broken compilers | **Cat A1** | Vacuous precondition. Resolved by requiring inhabitation witness `∃ q₀, S.pre q₀` in `VerifiedSpineOn`. |
| `PENTEST-3` | `Candidate 003` | `T := fun _ => Partial.ub` (always-rejecting compiler) passes demonic refinement | **Cat A1** | `Compiles` only guarded `(T p).defined → ...`. Resolved by `AcceptedDom` totality (`∀ p, S.AcceptedDom p → (T p).defined`). |
| `PENTEST-4` | `Candidate 003` | `L_tgt.sem := fun _ _ => Partial.pure (fun _ => False)` (empty outcome set) | **Cat A1** | Demonic refinement vacuously holds when target produces no outcomes. Resolved by target productivity (`ProductiveCompiles`). |
| `PENTEST-5` | `Candidate 003` | `decodeOut := fun _ => 0` with `obsPost _ v := v = 0` erases target output | **Cat A1 + Cat B** | Unconstrained `decodeOut` manufactures constant observations. Resolved by `FramedCodec` lens laws + Noun 4 audit. |
| `PENTEST-6` | `Candidate 003` | `encodeQuery := fun _ => defaultQuery` tests target on a single hardcoded input | **Cat A1** | Non-injective `encodeQuery` collapses query space. Resolved by left-inverse law `decodeQuery (encodeQuery q) = q`. |
| `PENTEST-7` | `Candidate 003` | `L_src.sem := fun _ _ => Partial.ub` makes source UB-vacuous on all inputs | **Cat A1 + Cat B** | Source language never safe on `S.pre`. Resolved by `ProductiveOn S.pre goodProg` + Noun 1 (`L_src.sem`) audit. |
| `PENTEST-8` | `Candidate 003` | Non-deterministic `L_src.sem` (`fun _ _ => Partial.pure (fun _ => True)`) absorbs wrong answers | **Cat A1** | Source chaos allows any target value to refine `L_src`. Resolved by `DeterministicOn S.pre` on accepted spine. |
| `PENTEST-9` | `Candidate 003` | `emit := fun _ => "xor eax, eax; ret"` unverified string emission | **Cat B** | Uninterpreted `String` has no operational meaning. Resolved by `VerifiedArtifactPipeline` into audited `L_isa.sem` (Noun 2). |
| `PENTEST-10` | `Candidate 003` | 18 unbundled hypotheses in top-level theorem allow accidental hypothesis omission | **Cat A1** | Signature bloat. Resolved by single `VerifiedCompilerBase` structure with `extends` hierarchy. |
| `PENTEST-R2-1` | `Candidate 006` | `L.diskLang parse` with `emit := fun _ => "rm -rf /"` and `parse := fun _ => some .good` | **Cat A1 + Cat B** | Circular syntax round-trip (`pentest_r2_1_circular_diskLang_universal_tautology`). Resolved by standalone `L_isa.sem` (Noun 2). |
| `PENTEST-R2-2` | `Candidate 006` | Single-point contrast (`∃ q, ...`) bypassed by compiler that only works at $q = 0$ | **Cat B** | Finite witness cannot replace universal `S.obsPost` audit (Gold 1967). Resolved by auditing `S.obsPost` (Noun 5). |
| `PENTEST-R2-3` | `Candidate 006` | `obs := fun _ => ()` collapses `SemObs` to `Unit` | **Cat A1** | Trivial observation carrier. Resolved by `HasProductiveContrastOn` requiring $\exists v_1 \neq v_2$ produced across queries/programs. |
| `PENTEST-R2-4` | `Candidate 006` | Constant-output `goodProg` (`sem _ _ = 0`) passes if contrast comes from another program | **Cat A2 / B** | Requiring per-program query sensitivity locks out legitimate constant functions; resolved by `HasProductiveContrastOn` disjunction + Noun 5 audit. |
| `PENTEST-R2-5` | `Candidate 006` | `badProgs := [goodProg]` defeated without `goodProg ≠ badProg` | **Cat A1** | Missing syntactic/semantic separation on `badProgs`. Resolved by `bad_rejected : AllHold (badProgs.map (fun b => ¬ (T b).defined))`. |
| `PENTEST-R2-6` | `Candidate 006` | Target program returns both `q + 1` and `999` (multi-valued target nondeterminism) | **Cat A1** | Target nondeterminism hidden if only existential outcome checked. Resolved by universal demonic inclusion + `ProductiveCompiles`. |
| `PENTEST-R2-7` | `Candidate 006` | Multi-stage pipeline `T₁ >=> T₂` drops intermediate productivity on `L_mid` | **Cat A1** | Partial Kleisli composition without intermediate `ProductiveCompiles`. Resolved by `FramedProductiveCompiles.comp`. |
| `PENTEST-R2-8` | `Candidate 006` | Side-channel leakage in constant-time compiler ignored by functional `Produces` | **Cat A1** | 1-safety refinement ignores 2-safety leakage. Resolved by `VerifiedConstantTimeCompiler` (`NominalBiNonInterferingOn`). |
| `PENTEST-R2-9` | `Candidate 006` | `BiNonInterferingOn` with `lowEq := Eq` (public = entire query) is a tautology | **Cat A1** | Trivial `lowEq` equates only identical secret states. Resolved by nominal `PublicSecretQuery Pub Sec` with non-trivial `Sec` witnesses. |
| `PENTEST-R2-10` | `Candidate 006` | Separate pipeline and single-pass bundles drift out of sync | **Cat A1** | Duplicate bundle definitions. Resolved by `VerifiedArtifactPipeline extends VerifiedCompilerBase`. |
| `PENTEST-R3-1` | `Candidate 008` | `CodecFramed` only constrained `encodeOut` range, allowing `decodeOut` to rewrite corrupted callee-saved registers (`rbx := 999`) back to `q + 1` | **Cat A1** | Unconstrained `decodeOut` off the canonical image. Resolved by `FramedCodec` with explicit `Frame` projection `frameOut o₂ = frameIn q₂`. |
| `PENTEST-R3-2` | `Candidate 008` | Partial compiler `T` accepts `goodProg` ($q + 1$) but rejects `goodProg2` ($q + 2$) | **Cat A1** | Pointwise witness `goodProg` did not cover full intended source subset. Resolved by explicit `S.AcceptedDom` totality. |
| `PENTEST-R3-3` | `Candidate 008` | `L_src.sem` returns `q + 1` at $q = 0, 1$ (passing 2-point witness check) and `0` for all $q \ge 2$ (`L_spoof`) | **Cat B** | Finite-witness checks cannot uniquely pin infinite functions. Resolved by TCB Noun 1 (`L_src.sem`) audit + removing redundant witness bloat. |
| `PENTEST-R3-4` | `Candidate 008` | `emit := fun _ => "xor eax, eax\nret"` passes `EmitterCompilesWithWitnesses` by permuting `L_asm.sem` | **Cat B** | Putnam's Permutation Theorem (`PutnamSyntaxPermutationTheorem`). Resolved by TCB Noun 2 (`L_isa.sem`) audit. |
| `PENTEST-R3-5` | `Candidate 008` | `obsPost q v := (v = q + 1 ∨ v = 0)` admits both honest and zeroed outputs while rejecting `badProg` ($v = 999$) | **Cat B** | Disjunctive relational slack in `obsPost`. Resolved by TCB Noun 5 (`S.obsPost`) audit. |
| `PENTEST-R3-6` | `Candidate 008` | `BiNonInterferingOn` with `leakEq := fun _ _ => True` ignores cycle-count/cache-line side channels | **Cat A1** | Coarse `leakEq` equivalence. Resolved by nominal `ValLeakObs Val Leak` requiring exact `o₁.leak = o₂.leak`. |
| `PENTEST-R3-7` | `Candidate 008` | `TotalWellBehavedDomainOn` bypassed by defining `L_src` with a 1-element `Unit` syntax carrier | **Cat A2 / B** | Cardinality/contrast hacks on `Prog`. Replaced by `S.AcceptedDom` + `badProgs` rejection in `VerifiedCompilerBase`. |
| `PENTEST-R3-8` | `Candidate 008` | `encodeQuery q := (q, CorruptHeap)` embeds source query into an unaligned/corrupted target machine frame | **Cat B** | Dishonest initial machine state in `encodeQuery`. Resolved by TCB Noun 4 (`codec.embedQuery`) audit. |
| `PENTEST-R3-9` | `Candidate 008` | `T` inspects syntax and miscompiles programs outside `[goodProg]` while `TotalWellBehavedDomainOn` only checks `L_src` | **Cat A1** | `Compiles` checked only on `goodProg` or without `AcceptedDom`. Resolved by universal `FramedProductiveCompiles` over all `p` coupled with `AcceptedDom`. |
| `PENTEST-R3-10` | `Candidate 008` | Constant-time theorem (`VerifiedConstantTimeCompilerWithGoodBadAndDisk`) dropped `TotalWellBehavedDomain` and `SemanticallyClosed` | **Cat A1** | Parallel structure copy-paste error. Resolved by `extends VerifiedCompilerBase`. |
| `PENTEST-R4-1` | `Candidate 016` | Exact round-trip `c.encodeOut (c.decodeOut o₂) = o₂` (`CodecFramed`) rejects every compiler that touches caller-saved scratch registers (`rcx`, `r8`, `flags`) | **Cat A2** | Over-constrained state bijection. Resolved by `FramedCodec` separating `valOut` from `frameOut` (`nextgen_admits_multi_scratch_and_rejects_callee_saved_clobber`). |
| `PENTEST-R4-2A` | `Candidate 016` | `isZeroClearAsmMnemonic` prefix rule rejects honest multi-instruction routines starting with `"xor eax, eax\nmov eax, edi..."` | **Cat A2** | Lexical prefix rule conflates initial register clear with final return value (`LexicalHeuristicDualFailureTheorem`). Resolved by deleting lexical rules from `Trusted/`. |
| `PENTEST-R4-2B` | `Candidate 016` | `isZeroClearAsmMnemonic` bypassed by prepending assembly label `"main:\nxor eax, eax\nret"` | **Cat A1 + Cat B** | Prefix heuristic defeated by any leading label/directive (`LexicalHeuristicDualFailureTheorem`, `prefix_classifier_universal_impossibility`). |
| `PENTEST-R4-3` | `Candidate 016` | `TotalWellBehavedDomain` + `SemanticallyClosed` rejects every compiler with syntactic typechecking or dead-code division-by-zero (`if false then 1/0 else x+1`) | **Cat A2** | Rice's Theorem: real compilers reject syntactically ill-typed ASTs even when dynamically unreachable (`nextgen_admits_syntactic_typechecker_and_rejects_buggySpike`). |
| `PENTEST-R4-4` | `Candidate 016` | 3-Program `TotalWellBehavedDomain` bypassed by adding 2 dummy AST nodes while `L_src.sem .addOne` still spikes to `999` at $q = 42$ | **Cat A1 + Cat B** | Finite syntactic cardinality cannot prevent single-input semantic spikes (`nextgen_admits_syntactic_typechecker_and_rejects_buggySpike`). |
| `PENTEST-R4-5A` | `Candidate 016` | `NonDegenerateLowEq ((Nat × Nat) × Nat)` bypassed by left-associated tuple `((pub, sec₁), sec₂)` where `Prod.fst` treats `sec₁` as public | **Cat A1** | Structural `Prod.fst` projection on nested tuples. Resolved by nominal `PublicSecretQuery Pub Sec` (`nextgen_nominal_ct_blocks_left_associated_tuple_leaks`). |
| `PENTEST-R4-5B` | `Candidate 016` | `NonDegenerateLeakEq ((Nat × Nat) × Nat)` bypassed by packing `(val, cycleCount)` into `Prod.fst` and ignoring `cycleCount` | **Cat A1** | Structural `Prod.snd` projection on nested tuples. Resolved by nominal `ValLeakObs Val Leak` (`nextgen_nominal_ct_blocks_left_associated_tuple_leaks`). |
| `PENTEST-R4-6` | `Candidate 016` | `HasThreePointContrastOn` (3 distinct points $q_0, q_1, q_2$) bypassed by degree-3 Lagrange interpolation $P(q) = (q+1) + 999 \cdot q(q-1)(q-2)$ | **Cat B** | Any $N$-point witness check is bypassed by degree-$N$ polynomial interpolation. Resolved by TCB Noun 1/5 audit. |
| `PENTEST-R4-7` | `Candidate 016` | `HasTwoPointRelationalContrastOn` bypassed by 3-way disjunctive postcondition `v = q + 1 ∨ v = q + 2 ∨ v = 0` | **Cat B** | Finite negative witnesses at each query cannot exclude a 3rd wrong branch. Resolved by TCB Noun 5 (`S.obsPost`) audit. |
| `PENTEST-R4-8` | `Candidate 016` | `EmitterQuerySensitiveSurjective` makes `EmitterCompilesWithWitnesses` logically `False` for every 1-program IR targeting a $\ge 2$-program ISA | **Cat A2** | Cardinality impossibility (`EmitterSurjectivityImpossibility`, `pentest_r4_8_single_ir_multi_isa_impossible`). Resolved by forward `FramedProductiveCompiles` + `badIsaProgs` distinctness. |
| `PENTEST-R4-9` | `Candidate 016` | `encodeQuery q := (q, 0xDEADBEEF)` passes `NonTrivialDecodeOut` because the defect is in `encodeQuery`, not `decodeOut` | **Cat B** | Initial target machine state embedding is a TCB boundary (`codec.embedQuery`, Noun 4). |
| `PENTEST-R4-10A/B` | `Candidate 016` | `VerifiedPipelineWithGoodBadAndDisk` omitted `SemanticallyClosed` (`R4-10A`), and `VerifiedConstantTimeCompilerWithGoodBadAndDisk` omitted `TotalWellBehavedDomain`, `SemanticallyClosed`, and `HasThreePointContrast` (`R4-10B`) | **Cat A1** | Parallel flat `structure` declarations without inheritance. Resolved by single root `VerifiedCompilerBase` + Lean `extends`. |

---

### Finding 4: The Next-Generation Minimal Semantic Blueprint (`NextGen`) and the Irreducible 5-Noun Auditor Boundary

`Basis: normative + source + execution + derived`

In [support/PutnamPermutationAndTcbBoundary.lean](support/PutnamPermutationAndTcbBoundary.lean) (lines 1222–1842, namespace `PutnamAndTcbBoundary.NextGen`), we construct and kernel-verify a unified Next-Generation Semantic Verification Blueprint that eliminates all Category A1 soundness bypasses and all Category A2 honest-tool lockouts simultaneously.

#### 4.1 The Four Orthogonal Primitives (`Language`, `Tool`, `FramedCodec`, `Spec`)

1. **`Language SemObs`** (L156): Defines syntax `Prog`, inputs `Query`, target outcomes `Out`, observation projection `obs : Out → SemObs`, operational semantics `sem : Prog → Query → Partial (Out → Prop)`, and domain invariant `dom : Prog → Query → Prop`.
2. **`Tool L₁ L₂`** (L231): Partial compiler/analyzer `L₁.Prog → Partial L₂.Prog` with Kleisli composition `T₁ >=> T₂` (`Tool.comp`).
3. **`FramedCodec L₁ L₂`** (L1242): Replaces both the under-constrained `BehaviorCodec` (vulnerable to `PENTEST-R3-1` callee-saved register spoofing) and the over-constrained `CodecFramed` (vulnerable to `PENTEST-R4-1` caller-saved scratch lockout) with an explicit **Lens / Frame architecture**:
   - `Frame : Type` represents the ABI-preserved machine frame (callee-saved registers `rbx`, `rsp`, `rbp`, `r12`–`r15` and non-scratch memory).
   - `embedQuery : L₁.Query → Frame → L₂.Query` embeds a source query into a target machine state with initial frame `f`, with left inverses `projectQuery (embedQuery q f) = q` and `frameIn (embedQuery q f) = f`.
   - `valOut : L₂.Out → L₁.Out` projects the return value (e.g., `rax`), while `frameOut : L₂.Out → Frame` projects the post-execution ABI frame, leaving caller-saved scratch registers (`rcx`, `rdx`, `r8`–`r11`, `rflags`) completely unconstrained!
   - `FramedProductiveCompiles c T` (L1294) requires that for every source program `p`, source query `q`, and initial frame `f`:
     - **Demonic Refinement & ABI Frame Preservation:** Every target outcome `o₂` produced at `c.embedQuery q f` maps to a valid source outcome `c.valOut o₂` **and** preserves the ABI frame (`c.frameOut o₂ = f`).
     - **Productivity Preservation:** Whenever `p` is productive at `q`, `T p` produces at least one outcome `o₂` at `c.embedQuery q f` with `c.frameOut o₂ = f`.
   - **Kleisli Transitivity (`FramedProductiveCompiles.comp`, L1328):** Two framed codecs `c₁₂ : FramedCodec L₁ L₂` and `c₂₃ : FramedCodec L₂ L₃` compose into `FramedCodec.comp c₁₂ c₂₃` with product frame `c₁₂.Frame × c₂₃.Frame`, and `FramedProductiveCompiles` composes transitively across `T₁ >=> T₂`.
4. **`Spec L`** (L1364): Bundles `pre : L.Query → Prop`, `obsPost : L.Query → SemObs → Prop`, and an explicit **Accepted Source Subset** `AcceptedDom : L.Prog → Prop`:
   - Instead of requiring `T` to accept *every* semantically well-behaved AST in `L_src` (which locked out syntactic typecheckers on `if false then 1/0 else x + 1` in `PENTEST-R4-3`), `VerifiedCompilerBase` requires `T` to accept every program in `S.AcceptedDom` (`accepted_total : ∀ p, S.AcceptedDom p → (T p).defined`) and requires every program in `S.AcceptedDom` to satisfy `VerifiedSpineOn` and `HasProductiveContrastOn`.

#### 4.2 Single Root Bundle (`VerifiedCompilerBase`) and `extends` Inheritance Hierarchy (`PENTEST-R4-10A/B` Resolved)

To make clause-drop bugs across theorem variants (`PENTEST-R4-10A/B`) structurally impossible, `NextGen` defines **one** canonical base bundle `VerifiedCompilerBase` (L1379):

```lean
structure VerifiedCompilerBase {SemObs : Type}
    (L_src L_tgt : Language SemObs)
    (c : FramedCodec L_src L_tgt)
    (S : Spec L_src)
    (T : Tool L_src L_tgt)
    (goodProgs : List L_src.Prog)
    (badProgs : List L_src.Prog) : Prop where
  framed_compiles    : FramedProductiveCompiles c T
  accepted_total     : ∀ p, S.AcceptedDom p → (T p).defined
  accepted_spine     : ∀ p, S.AcceptedDom p →
    L_src.VerifiedSpineOn L_src.dom S.pre S.obsPost p ∧
    L_src.HasProductiveContrastOn S.pre p
  goodProgs_nonempty : goodProgs ≠ []
  good_in_accepted   : AllHold (goodProgs.map S.AcceptedDom)
  badProgs_nonempty  : badProgs ≠ []
  bad_rejected       : AllHold (badProgs.map (fun b => ¬ (T b).defined))
```

Every specialized verification bundle **inherits directly from `VerifiedCompilerBase` via Lean's `extends` keyword**:
- **`VerifiedConstantTimeCompiler extends VerifiedCompilerBase`** (L1479): Operates over nominal `PublicSecretQuery Pub Sec` and `ValLeakObs Val Leak` carriers (preventing the left-associated tuple projection bypasses `PENTEST-R4-5A/B`), requires `sec_nondeg : sec₀ ≠ sec₁`, and enforces `NominalBiNonInterferingOn` across `S.AcceptedDom` and all compiled targets.
- **`VerifiedArtifactPipeline extends VerifiedCompilerBase`** (L1501): Extends `VerifiedCompilerBase` with a concrete target ISA language `L_isa : Language SemObs`, a framed codec `c_isa : FramedCodec L_tgt L_isa`, an emitter `emit : L_tgt.Prog → L_isa.Prog` satisfying `FramedProductiveCompiles c_isa (fun t => Partial.pure (emit t))`, and non-empty `badIsaProgs` that are syntactically distinct from every emitted `goodProgs` artifact (replacing the impossible surjectivity requirement of `PENTEST-R4-8`). Its end-to-end theorem `VerifiedArtifactPipeline.end_to_end_isa_framed_compiles` (L1526) composes `T` and `emit` automatically via `FramedProductiveCompiles.comp`.

#### 4.3 Mechanized Proof-of-Concept Resolutions of `PENTEST-R4-1`..`10` Lockouts and Bypasses

We prove four concrete non-lockout and negative-rejection theorems in `PutnamPermutationAndTcbBoundary.lean` (lines 1545–1842):

1. **`nextgen_admits_multi_scratch_and_rejects_callee_saved_clobber` (L1614, resolves `PENTEST-R3-1` & `PENTEST-R4-1`):** On an x86-64 register model with `rax`, caller-saved scratch registers `rcx` and `r8` (`ScratchRegs`), and callee-saved register `rbx`, the honest compiler that uses both `rcx := q + 10` and `r8 := q * 2` as temporary scratch registers satisfies `FramedProductiveCompiles x86AbiFramedCodec`, whereas a buggy compiler that overwrites `rbx := rbx + 1` is **unconditionally refuted (`¬ FramedProductiveCompiles ...`)**.
2. **`nextgen_admits_syntactic_typechecker_and_rejects_buggySpike` (L1687, resolves `PENTEST-R4-3` & `PENTEST-R4-4`):** On a source language containing `.cleanAddOne`, `.deadDivByZeroAddOne` (`if false then 1/0 else q + 1`), `.buggySpikeAt42` (which outputs `999` at $q = 42$), and `.hardDivByZero`, a standard compiler with a syntactic typechecker that accepts `.cleanAddOne` and rejects `.deadDivByZeroAddOne` is **admitted** by `VerifiedCompilerBase` (with `AcceptedDom p := (p = .cleanAddOne)`), while `.buggySpikeAt42` is **proven to violate `VerifiedSpineOn`** at $q = 42$.
3. **`nextgen_verifiedArtifactPipeline_admits_accum_init_and_multi_isa` (L1730, resolves `PENTEST-R4-2A` & `PENTEST-R4-8`):** The multi-instruction accumulator-initializing routine `[.zeroClear, .loadAndInc]` (`"xor eax, eax\nmov eax, edi\nadd eax, 1\nret"`) from a 1-well-behaved-program IR (`L_simple_ir`) into the multi-program sequential ISA (`L_seq_asm`) satisfies `VerifiedArtifactPipeline` with zero lockout.
4. **`nextgen_nominal_ct_blocks_left_associated_tuple_leaks` (L1817, resolves `PENTEST-R4-5A/B`):** On a 2-secret (`Sec := Nat × Nat`), 2-side-channel (`Leak := Nat × Nat`) language using nominal `PublicSecretQuery` and `ValLeakObs`, the constant-time cipher `.honestCtCipher` satisfies `NominalBiNonInterferingOn`, while `.leakFirstSecretInVal` (`val := pub + sec.1`, the `R4-5A` tuple attack) and `.leakSecretInCycleCount` (`leak := (sec.1, 0)`, the `R4-5B` tuple attack) are both **unconditionally refuted**.

---

## Boundaries

### The Irreducible 5-Noun Auditor Boundary (Why TCB Inspection Cannot Be Automated Away)

By **Putnam's Model-Theoretic Permutation Theorem** (`PutnamSyntaxPermutationTheorem`), **Gold's / Polynomial Interpolation Finite-Witness Impossibility** (`PENTEST-R3-3`, `PENTEST-R4-4`, `PENTEST-R4-6`), and **Rice's Theorem** (`PENTEST-R4-3`), any claim that a machine-checked theorem certifies a real-world compiler pipeline rests on the human audit of **exactly five concrete domain nouns** (compare Pollack 1998, "How to Believe a Machine-Checked Proof"):

| TCB Domain Noun | Lean Identifier in `NextGen` | What the Human Auditor Must Verify | What Happens if Unaudited (Pentest Exploit) | Why In-Kernel Predicates Cannot Replace Audit |
| :--- | :--- | :--- | :--- | :--- |
| **Noun 1: Source Language Semantics** | `L_src.sem` | Faithful operational meaning of source programs on all inputs in `S.pre` | `PENTEST-7`, `PENTEST-R3-3`, `PENTEST-R4-4`, `PENTEST-R4-6` (source semantics spoofed or interpolated outside finite witnesses) | Any $N$-point witness check is bypassed by a degree-$N$ polynomial or piecewise spike at point $N+1$. |
| **Noun 2: Target / ISA Operational Semantics** | `L_tgt.sem` / `L_isa.sem` | Faithful instruction-execution semantics of concrete target ASTs, assembly instructions, or machine bytes | `PENTEST-9`, `PENTEST-R2-1` (`L.diskLang parse`), `PENTEST-R3-4` (`L_x86_spoof` permuting `"xor eax, eax\nret"` $\leftrightarrow$ `"mov eax, edi; inc eax; ret"`) | By `PutnamSyntaxPermutationTheorem`, any bijection $\pi$ on syntax preserves 100% of purely semantic/structural predicates; lexical heuristics fail by `LexicalHeuristicDualFailureTheorem`. |
| **Noun 3: Compiler / Emitter Function** | `T` and `emit` | `T` and `emit` are bound to the actual compiler pass and code generator under test (not a stub or constant lookup table) | `PENTEST-3`, `PENTEST-R3-2` (stub compiler accepting only a single hardcoded AST) | In-kernel `AcceptedDom` guarantees totality on the specified domain, but human inspection must confirm `T` is the real compiler implementation. |
| **Noun 4: Framed Codec Embedding & Projection** | `c.embedQuery`, `c.valOut`, `c.frameOut` | `embedQuery q f` initializes a valid hardware state (stack pointer, page tables) and `valOut`/`frameOut` read the real ABI return and callee-saved registers | `PENTEST-5`, `PENTEST-6`, `PENTEST-R3-1`, `PENTEST-R3-8`, `PENTEST-R4-9` (`encodeQuery` injects `0xDEADBEEF` corrupted stack/heap) | Lens laws (`projectQuery (embedQuery q f) = q`, `frameOut o₂ = f`) enforce algebraic framing, but cannot know which hardware register is `rsp` vs. `rcx` without ABI binding. |
| **Noun 5: Specification Contract & Accepted Subset** | `S.pre`, `S.obsPost`, `S.AcceptedDom` | `S.obsPost q v` states the true functional relation on all `q` satisfying `S.pre q`, and `S.AcceptedDom` covers the intended compilable language fragment | `PENTEST-1`, `PENTEST-R2-2`, `PENTEST-R3-5`, `PENTEST-R4-7` (disjunctive `obsPost` admitting `v = q + 1 ∨ v = 0`) | Any finite relational contrast check (`k` negative witnesses per query) is bypassed by a $(k+1)$-way disjunction in `obsPost`. |

**Necessity and Sufficiency of the 5-Noun Boundary:**
- **Necessity:** Each of the 5 nouns corresponds to an independent free variable in the statement of compiler correctness ($\forall p \in \text{AcceptedDom},\ \forall q \in \text{pre},\ \llbracket \text{emit}(T(p)) \rrbracket_{\text{ISA}}(\text{embed}(q, f)) \subseteq \{ o_2 \mid \text{frameOut}(o_2) = f \land \text{obsPost}(q, \text{obs}(\text{valOut}(o_2))) \}$). Permuting or spoofing any single noun yields a counterexample mechanized in `PutnamPermutationAndTcbBoundary.lean`.
- **Sufficiency:** Once the 5 nouns are honestly instantiated, `VerifiedCompilerBase` (and its extensions `VerifiedConstantTimeCompiler` and `VerifiedArtifactPipeline`) guarantees in-kernel—with zero `sorry` and zero custom axioms—that every accepted source program is productively compiled, preserves the ABI frame while permitting arbitrary caller-saved scratch mutation, satisfies the end-to-end functional postcondition on all valid inputs, preserves constant-time 2-safety across all secret inputs and side channels, and emits concrete ISA artifacts verified against `L_isa.sem`.

---

## Evidence

### 1. Mechanized Lean 4 Proof Artifact ([support/PutnamPermutationAndTcbBoundary.lean](support/PutnamPermutationAndTcbBoundary.lean))

All definitions, theorems, counterexamples, and blueprint constructions are mechanized in [support/PutnamPermutationAndTcbBoundary.lean](support/PutnamPermutationAndTcbBoundary.lean) (1,842 lines):

- **Section 1 (Lines 140–353): Core 4-Primitive Semantic Framework (`Language`, `Tool`, `BehaviorCodec`, `Spec`) and Historical Candidate Predicates.**
  - Mechanizes `Partial`, `Language`, `SafeAt`, `Produces`, `ProductiveOn`, `DeterministicOn`, `QuerySensitiveOn`, `NonChaoticOn`, `WellBehavedProgOn`, `HasProductiveContrastOn`, `VerifiedSpineOn`, `SpineNonDegenerate`, `TotalWellBehavedDomainOn`, `Tool.SemanticallyClosedOn`, `BiNonInterferingOn`, `EmitterCompilesOn`, and `EmitterCompilesWithWitnessesOn`.
- **Section 2 (Lines 355–924): Putnam's Model-Theoretic Syntax-Permutation Invariance Theorem (`PutnamSyntaxPermutationTheorem`) & Corollaries (`PENTEST-R3-4`, `PENTEST-R2-1`).**
  - `SyntaxPerm` bijection structure and `SyntaxPerm.swap` transposition (`swapFn_involutive`, L383).
  - Step-by-step invariance lemmas (`permProg_safeAt_iff` through `permProg_emitterCompiles_iff`, L438–706).
  - **`PutnamSyntaxPermutationTheorem`** (L709): Proves simultaneous invariance of `EmitterCompilesWithWitnessesOn`, `HasProductiveContrastOn`, `WellBehavedProgOn`, and `TotalWellBehavedDomainOn` under arbitrary syntax permutations.
  - **`pentest_r3_4_corollary_trojan_emitter_passes_under_permuted_semantics`** (L842): Instantiates `PutnamSyntaxPermutationTheorem` to prove that `trojanEmit` outputting `"xor eax, eax\nret"` passes all 4 obligations under `L_x86_spoof`.
  - **`pentest_r2_1_circular_diskLang_universal_tautology`** (L899): Proves that any emitter with a one-sided inverse parser `parse (emit t) = some t` trivially satisfies `EmitterCompilesOn` into `L.diskLang parse`, even when outputting `"rm -rf /\n"`.
- **Section 3 (Lines 926–1220): Impossibility of Lexical Heuristics (`PENTEST-R4-2A/B`) and Emitter Surjectivity (`PENTEST-R4-8`).**
  - Sequential stateful assembly language `L_seq_asm` (`AsmInstr`, `RegState`, `evalInstr`, `evalSeq`, L933–999).
  - **`LexicalHeuristicDualFailureTheorem`** (L1002): Proves that `isZeroClearLeading` and `containsZeroClearAnywhere` fail on `L_seq_asm` (`PENTEST-R4-2A` honest lockout on `[.zeroClear, .loadAndInc]`), while `[.label "main", .zeroClear]` evades `isZeroClearLeading` and outputs `0` on all queries (`PENTEST-R4-2B`).
  - **`prefix_classifier_universal_impossibility`** (L1035): Proves that for any lookahead $k \in \mathbb{N}$, no $k$-instruction prefix classifier can flag $k$-nop-prefixed zero-clear routines without falsely locking out $k$-nop-prefixed accumulator-initialization routines.
  - **`EmitterSurjectivityImpossibility`** (L1118) and **`pentest_r4_8_single_ir_multi_isa_impossible`** (L1173): Proves that `EmitterQuerySensitiveSurjective` is impossible (`False`) whenever $L_{\text{asm}}$ has $\ge 2$ distinct query-sensitive programs and $L_{\text{tgt}}$ has at most $1$ productive program.
- **Section 4 (Lines 1222–1842): The Next-Generation Minimal Semantic Blueprint (`NextGen`).**
  - `FramedCodec` (L1242), `FramedProductiveCompiles` (L1294), and Kleisli composition `FramedProductiveCompiles.comp` (L1328).
  - `Spec` with explicit `AcceptedDom` (L1364) and root bundle `VerifiedCompilerBase` (L1379).
  - Nominal 2-safety carriers `PublicSecretQuery` (L1424) and `ValLeakObs` (L1430), `VerifiedConstantTimeCompiler extends VerifiedCompilerBase` (L1479), and `VerifiedArtifactPipeline extends VerifiedCompilerBase` (L1501) with `end_to_end_isa_framed_compiles` (L1526).
  - Four concrete non-lockout and negative-rejection theorems (`nextgen_admits_multi_scratch_and_rejects_callee_saved_clobber` L1614, `nextgen_admits_syntactic_typechecker_and_rejects_buggySpike` L1687, `nextgen_verifiedArtifactPipeline_admits_accum_init_and_multi_isa` L1730, and `nextgen_nominal_ct_blocks_left_associated_tuple_leaks` L1817).

### 2. Primary Literature References

1. **Hilary Putnam (1980):** "Models and Reality," *The Journal of Symbolic Logic*, Vol. 45, No. 3, pp. 464–482 (`doi:10.2307/2273415`). Establishes the model-theoretic permutation theorem showing that truth-conditions across possible worlds/queries are invariant under permutations of the underlying reference assignment.
2. **M. H. A. Newman (1928):** "Mr. Russell's 'Causal Theory of Perception'," *Mind*, Vol. 37, No. 146, pp. 137–148 (`doi:10.1093/mind/XXXVII.146.137`). Proves that purely structural/relational descriptions without anchored concrete relations are trivially satisfied up to cardinality by relabeling.
3. **James H. Morris Jr. (1973):** "Types are Not Sets," *Proceedings of the 1st Annual ACM SIGACT-SIGPLAN Symposium on Principles of Programming Languages (POPL '73)*, pp. 120–124 (`doi:10.1145/512927.512938`). Establishes that semantic authenticity and information-hiding guarantees require nominal/opaque type boundaries rather than transparent structural products (`PENTEST-R4-5A/B`).
4. **Joseph A. Goguen and Rod M. Burstall (1992):** "Institutions: Abstract Model Theory for Specification and Programming," *Journal of the ACM*, Vol. 39, No. 1, pp. 95–146 (`doi:10.1145/147508.147524`). Formalizes the satisfaction condition $\mathcal{M}' \models_\Sigma \sigma(\varphi) \iff \sigma^*(\mathcal{M}') \models_{\Sigma'} \varphi$ under signature morphisms $\sigma$, of which `PutnamSyntaxPermutationTheorem` is the syntax-automorphism specialization.
5. **Robert Pollack (1998):** "How to Believe a Machine-Checked Proof," in *Twenty-Five Years of Constructive Type Theory*, Oxford Logic Guides 36, Oxford University Press, pp. 205–220 (`doi:10.1093/oso/9780198501275.003.0011`). Analyzes the gap between internal kernel typechecking and external specification fidelity (the irreducible human-audited TCB boundary).
6. **Xavier Leroy (2009):** "Formal Verification of a Realistic Compiler," *Communications of the ACM*, Vol. 52, No. 7, pp. 107–115 (`doi:10.1145/1538788.1538814`). Defines CompCert's forward/backward simulation architecture between trusted Cight source semantics and trusted assembly semantics.
7. **Ramana Kumar, Magnus O. Myreen, Michael Norrish, and Scott Owens (2014):** "CakeML: A Verified Implementation of ML," *POPL '14*, pp. 179–191 (`doi:10.1145/2535838.2535841`). Eliminates unverified text emission by verifying binary machine-code generation directly against an audited instruction-set architecture model in the TCB.

---

## Revalidation

To revalidate all mechanized proofs and verify that zero `sorry` or custom axioms are used, run Lean `v4.34.1` (`commit 5045d0056413266e57c625dcd7c365b10e377c52`) with synchronous elaboration and full kernel typechecking enabled:

```bash
lean -DElab.async=false -Ddebug.skipKernelTC=false support/PutnamPermutationAndTcbBoundary.lean
```

Expected output (exit code `0`, zero warnings, standard axioms only):

```text
'PutnamAndTcbBoundary.PutnamSyntaxPermutationTheorem' depends on axioms: [propext]
'PutnamAndTcbBoundary.pentest_r3_4_corollary_trojan_emitter_passes_under_permuted_semantics' depends on axioms: [propext,
 Quot.sound]
'PutnamAndTcbBoundary.pentest_r2_1_circular_diskLang_universal_tautology' does not depend on any axioms
'PutnamAndTcbBoundary.LexicalHeuristicDualFailureTheorem' depends on axioms: [propext]
'PutnamAndTcbBoundary.prefix_classifier_universal_impossibility' does not depend on any axioms
'PutnamAndTcbBoundary.EmitterSurjectivityImpossibility' does not depend on any axioms
'PutnamAndTcbBoundary.NextGen.VerifiedArtifactPipeline.end_to_end_isa_framed_compiles' does not depend on any axioms
'PutnamAndTcbBoundary.NextGen.nextgen_admits_multi_scratch_and_rejects_callee_saved_clobber' does not depend on any axioms
'PutnamAndTcbBoundary.NextGen.nextgen_admits_syntactic_typechecker_and_rejects_buggySpike' depends on axioms: [propext]
'PutnamAndTcbBoundary.NextGen.nextgen_verifiedArtifactPipeline_admits_accum_init_and_multi_isa' does not depend on any axioms
'PutnamAndTcbBoundary.NextGen.nextgen_nominal_ct_blocks_left_associated_tuple_leaks' does not depend on any axioms
```
