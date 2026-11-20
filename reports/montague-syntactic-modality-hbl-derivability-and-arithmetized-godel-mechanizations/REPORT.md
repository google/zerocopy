# Syntactic Modality, Hilbert–Bernays–Löb Derivability, and Arithmetized Gödel Mechanizations

## Summary

A formal theorem about proof checkers or axiomatic theories certifying one another's consistency speaks about actual formal systems only when provability is represented as an **object-language formula applied to numeral codes of deep-embedded object syntax** ($\mathrm{Prov}_\tau(\ulcorner \varphi \urcorner)$), rather than as a predicate or operator over meta-level propositions (`Box : Prop -> Prop`). By **Montague's theorem (1963)**, any diagonalizable theory $T$ (such as an extension of Robinson's arithmetic $\mathsf{Q}$) equipped with a unary syntactic predicate $N(x)$ satisfying the unrestricted reflection schema $T \vdash N(\ulcorner \varphi \urcorner) \to \varphi$ and the rule of necessitation ($T \vdash \varphi \implies T \vdash N(\ulcorner \varphi \urcorner)$) is outright inconsistent—even in minimal intuitionistic logic without modal distribution ($\mathsf{K}$ / HBL $\mathbf{D2}$) or internal transitivity ($\mathsf{4}$ / HBL $\mathbf{D3}$). By **Kaplan and Montague's Knower Paradox (1960)**, dropping global necessitation for $T$ still yields inconsistency if $T$ retains reflection ($I_1$), internalized reflection $T \vdash K(\ulcorner K(\ulcorner \varphi \urcorner) \to \varphi \urcorner)$ ($I_2$), and closure of $K$ under $\mathsf{Q}$-provable implications ($I_3$). Conversely, shallow embeddings in proof assistants that type `IsProvable : Prop -> Prop` and assume material necessitation `forall A : Prop, A -> IsProvable A` alongside Löb's theorem (as in `JasonGross/lob`'s `axiomatization/lob.v`) prove `~~ IsProvable False`, leaving only the inconsistent trivial model `IsProvable _ := True` and rendering meta-level self-reference or ring-consistency theorems vacuous.

Across the five mechanized repositories examined, **only two**—`FormalizedFormalLogic/Foundation` in Lean 4 (`𝗜𝚺₁` / `𝗣𝗔` / r.e. extensions via Craig's trick) and `isabelle-prover/mirror-afp-devel` (`Incompleteness` and `Goedel_HFSet_Semanticless` over Swierczkowski's hereditarily finite set theory $\mathsf{HF}$)—discharge all three Hilbert–Bernays–Löb ($\mathrm{HBL}$) derivability conditions ($\mathbf{D1}$, $\mathbf{D2}$, $\mathbf{D3}$) and the Diagonal Lemma for a concrete object theory without unproved hypotheses, and **only `Foundation`** additionally mechanizes Solovay's arithmetical completeness theorems for $\mathsf{GL}$, $\mathsf{S}$, and $\mathsf{Grz}$. `rocq-community/hydra-battles` (`theories/goedel/`) proves $\mathbf{D1}$ and Gödel–Rosser first incompleteness for primitive-recursively axiomatized extensions of $\mathsf{NN}$/$\mathsf{PA}$ but leaves $\mathbf{D2}$ and $\mathbf{D3}$ as unproved section hypotheses in `goedel2.v`. `uds-psl/coq-library-fol` proves first incompleteness synthetically via Church's Thesis for $\mathsf{Q}$ (`CTQ`) without arithmetizing proof trees, so its `abstract_loeb.v` takes all $\mathrm{HBL}$ and fixpoint laws as abstract variables. Finally, because consistency statements $\mathrm{Con}_\tau(T)$ are **intensional**—failing Gödel's second incompleteness theorem under Feferman $\pi^*$ numerations (failing $\mathbf{D3}$), Rosser predicates (failing $\mathbf{D2}$/$\mathbf{D3}$), and Willard's multiplication-free self-verifying systems—any machine-checked theorem ruling out an $n$-cycle of mutual consistency proofs $T_0 \vdash \mathrm{Con}_{\tau_1}(T_1), \dots, T_{n-1} \vdash \mathrm{Con}_{\tau_0}(T_0)$ must explicitly fix six side conditions: deep syntax with injective coding, $\Sigma_1$ axiom numerations $\tau_i$, $\mathsf{EA}$-provable inclusion $\mathrm{Ax}_{\mathsf{Q}} \subseteq \tau_i$ (licensing $\Pi_1$-reflection $\mathsf{EA} \vdash \mathrm{Con}_{\tau_i} \to \mathrm{Con}_{\tau_{i+1}}$), $\mathbf{D1}+\mathbf{D2}$ for every $\Box_{\tau_i}$, $\mathbf{D3}$ plus diagonalization in at least one $T_k \supseteq \mathsf{EA}$, and actual $\Sigma_1$-completeness of each $T_i$ if all $n$ theories (rather than at least one) are claimed inconsistent.

---

## Applicability

This report compares foundational limitative theorems in mathematical logic with five pinned mechanized proof-assistant developments:

1. **`FormalizedFormalLogic/Foundation`** (`fbcfee52cb4a892087fa978366282a9ebd844f29`, Lean 4): modules `Foundation/FirstOrder/Arithmetic/Bootstrapping/`, `Foundation/FirstOrder/Incompleteness/`, and `Foundation/ProvabilityLogic/`.
2. **`isabelle-prover/mirror-afp-devel`** (`523cdc72b5ae4a91c9ab8e1025d4a30b40472720`, Isabelle/HOL): Archive of Formal Proofs sessions `Incompleteness` (Paulson, extended with `Loebs_Theorem.thy` by Bailitis), `Goedel_Incompleteness` (Popescu and Traytel), `Goedel_HFSet_Semantic`, and `Goedel_HFSet_Semanticless`.
3. **`rocq-community/hydra-battles`** (`ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8`, Rocq/Coq): `theories/goedel/` (O'Connor's mechanization migrated to modern Rocq).
4. **`uds-psl/coq-library-fol`** (`4e5702240aa0cae803dbb2d4bc5a4b7744fef217`, Rocq/Coq): `theories/Incompleteness/` (synthetic undecidability, external provability under `CTQ`, and abstract modal Löb).
5. **`JasonGross/lob`** (`fe3113a89c155254a0525ea741aad7469361d161`, Coq and Agda `--without-K`): `axiomatization/lob.v`, `internal/*.v`, and `internal/*.agda`.

The foundational mathematical results are normative mathematical theorems verified against primary publications by Kaplan and Montague (1960), Feferman (1960), Montague (1963), Solovay (1976), Willard (2001), and Visser (2011). Claims about mechanized theorem statements, typeclass/locale parameters, and unproved hypotheses apply strictly to the pinned repository revisions above. Architectural conclusions regarding statement adequacy apply to any proof assistant based on dependent type theory (Lean 4, Rocq/Coq, Agda) or higher-order logic (Isabelle/HOL, HOL Light, HOL4) when formalizing metamathematical claims about proof checkers, compilers, or axiomatic theories.

---

## Findings

### 1. Syntactic Modality vs. Modal Operators: Montague (1963), Kaplan–Montague (1960), and Shallow-Embedding Vacuity

`Basis: normative + source + execution + derived`

#### 1.1 Exact Reconstruction of Montague's Theorem (1963) and Kaplan–Montague (1960)

Let $\mathcal{L}$ be a first-order language containing numerals $\overline{n}$ for $n \in \mathbb{N}$, let $\ulcorner \varphi \urcorner$ denote the numeral of the Gödel code of $\mathcal{L}$-formula $\varphi$ under an injective effective coding, and let $T$ be an $\mathcal{L}$-theory satisfying the **Diagonal Lemma** for unary formulas: for every $\mathcal{L}$-formula $\psi(x)$ with one free variable $x$, there exists a closed $\mathcal{L}$-sentence $\gamma$ such that $T \vdash \gamma \leftrightarrow \psi(\ulcorner \gamma \urcorner)$. Robinson's finitely axiomatized arithmetic $\mathsf{Q}$ (and even weaker sequential/bootstrapping theories such as $\mathsf{R}_0$ in `Foundation`) suffices to prove the Diagonal Lemma (`Foundation/FirstOrder/Arithmetic/Bootstrapping/FixedPoint.lean`).

- **Montague's Theorem (Montague 1963, Theorem 1):** Let $T$ be any theory with the Diagonal Lemma (over minimal intuitionistic implicational-negational logic, defining $\neg \alpha := \alpha \to \bot$), and let $N(x)$ be any unary formula of $\mathcal{L}$. Suppose that for every sentence $\varphi$ (or merely for the single diagonal sentence $\gamma$ below):
  1. **Syntactic Reflexion Schema ($\mathrm{T}_{\text{pred}}$):** $T \vdash N(\ulcorner \varphi \urcorner) \to \varphi$;
  2. **Rule of Necessitation ($\mathrm{RN}_{\text{pred}}$):** if $T \vdash \varphi$, then $T \vdash N(\ulcorner \varphi \urcorner)$.

  **Derivation of $T \vdash \bot$ (requiring neither $\mathsf{K}$/$\mathbf{D2}$, nor $\mathsf{4}$/$\mathbf{D3}$, nor classical double-negation elimination):**
  1. Apply the Diagonal Lemma to $\neg N(x)$ to obtain a sentence $\gamma$ with $T \vdash \gamma \leftrightarrow (N(\ulcorner \gamma \urcorner) \to \bot)$.
  2. Instantiate ($\mathrm{T}_{\text{pred}}$) at $\gamma$: $T \vdash N(\ulcorner \gamma \urcorner) \to \gamma$.
  3. Inside $T$, assume $h : N(\ulcorner \gamma \urcorner)$. By step 2, $\gamma$ holds; by step 1 ($\gamma \to N(\ulcorner \gamma \urcorner) \to \bot$), $\bot$ holds. Discharging $h$ yields $T \vdash N(\ulcorner \gamma \urcorner) \to \bot$, and by the right-to-left half of step 1, $T \vdash \gamma$.
  4. Apply the meta-rule ($\mathrm{RN}_{\text{pred}}$) once to $T \vdash \gamma$ to obtain $T \vdash N(\ulcorner \gamma \urcorner)$.
  5. Combine $T \vdash N(\ulcorner \gamma \urcorner) \to \bot$ (step 3) with $T \vdash N(\ulcorner \gamma \urcorner)$ (step 4) by modus ponens: $T \vdash \bot$.

- **Montague's Corollaries on Reflection and Non-Finite Axiomatizability (Montague 1963, Corollaries 1–2):** If $T$ is a consistent extension of $\mathsf{PA}$ (or $\mathsf{ZFC}$) and $F \subseteq T$ is any finitely axiomatized subtheory, $T$ proves every sentence of the uniform reflection schema $\mathrm{Prov}_F(\ulcorner \varphi \urcorner) \to \varphi$ for $F$ (by constructing partial truth predicates for bounded quantifier depth). If $T$ itself were finitely axiomatizable ($T = F$), then $N(x) := \mathrm{Prov}_F(x)$ would satisfy ($\mathrm{T}_{\text{pred}}$) and ($\mathrm{RN}_{\text{pred}}$) in $T$, forcing $T \vdash \bot$ by Theorem 1. Hence neither $\mathsf{PA}$ nor $\mathsf{ZFC}$ is finitely axiomatizable.

- **Kaplan–Montague Knower Paradox (Kaplan and Montague 1960, *"A Paradox Regained"*):** One might attempt to rescue a syntactic knowledge or certification predicate $K(x)$ by dropping global necessitation ($\mathrm{RN}_{\text{pred}}$) for $T$-theorems—since an agent or bounded checker need not know every theorem of $T$. Kaplan and Montague proved that if a base subtheory $Q_0 \subseteq T$ proves the Diagonal Lemma, then $T$ is **still inconsistent** whenever $K(x)$ satisfies three weaker epistemic/certification principles:
  1. **($I_1$) Veridicality:** $T \vdash K(\ulcorner \varphi \urcorner) \to \varphi$;
  2. **($I_2$) Internalized Veridicality:** $T \vdash K(\ulcorner K(\ulcorner \varphi \urcorner) \to \varphi \urcorner)$;
  3. **($I_3$) Base-Logic Monotonicity:** if $Q_0 \vdash \alpha \to \beta$, then $T \vdash K(\ulcorner \alpha \urcorner) \to K(\ulcorner \beta \urcorner)$.

  **Derivation of $T \vdash \bot$ without ($\mathrm{RN}_{\text{pred}}$):** Choose $\delta$ in the base theory $Q_0$ such that $Q_0 \vdash \delta \leftrightarrow \neg K(\ulcorner \delta \urcorner)$. Pure intuitionistic propositional reasoning inside $Q_0$ from $\delta \leftrightarrow (K(\ulcorner \delta \urcorner) \to \bot)$ yields $Q_0 \vdash (K(\ulcorner \delta \urcorner) \to \delta) \to \delta$. Applying ($I_3$) to this $Q_0$-theorem gives $T \vdash K(\ulcorner K(\ulcorner \delta \urcorner) \to \delta \urcorner) \to K(\ulcorner \delta \urcorner)$. Modus ponens with ($I_2$) at $\delta$ yields $T \vdash K(\ulcorner \delta \urcorner)$; ($I_1$) yields $T \vdash \delta$; and $Q_0 \subseteq T$ yields $T \vdash \neg K(\ulcorner \delta \urcorner)$, hence $T \vdash \bot$.

#### 1.2 Why Propositional Modal Operators Escape Montague's Collapse

| Property / Principle | Sentential Modal Operator ($\Box \varphi$) | Syntactic Predicate on Codes ($N(\ulcorner \varphi \urcorner)$) | Shallow Meta-Type Predicate (`B : Prop -> Prop`) |
| :--- | :--- | :--- | :--- |
| **Grammar of argument** | Formula $\varphi$ of modal propositional language $\mathcal{L}_\Box$ | First-order term $t$ (numeral $\ulcorner \varphi \urcorner$ of object code) | Host proof-assistant proposition $P : \mathrm{Prop}$ |
| **Quantification over targets** | Forbidden in $\mathcal{L}_\Box$ (propositional schema only) | First-order object quantification $\forall x,\, N(x) \to \dots$ | Higher-order quantification $\forall P : \mathrm{Prop},\, B(P) \to \dots$ |
| **Self-referential fixed points** | **Modalized only** in $\mathsf{GL}$ (De Jongh–Sambin); **absent** for $\neg \Box p$ in $\mathsf{T}/\mathsf{S4}/\mathsf{S5}$ | **Unconditional** for all $\psi(x)$ once $T \supseteq \mathsf{R}_0/\mathsf{Q}$ (`Diagonalization T`) | Forbidden in kernel unless injected as an **axiom** (risking inconsistency) |
| **Status of $\Box \varphi \to \varphi$ + Necessitation** | **Consistent** ($\mathsf{T}, \mathsf{S4}, \mathsf{S5}$: identity model $v(\Box \varphi) = v(\varphi)$) | **Inconsistent** (Montague 1963 Theorem 1; $0/256$ models on $|W|=2$) | **Inconsistent** if paired with fixpoint axiom; trivial $B(P) \leftrightarrow P$ without fixpoint |
| **Status of $P \to \Box P$ + Löb** | Collapses $\mathsf{GL} + (\neg\Box\bot \to \Box\neg\Box\bot)$ to $\Box\bot$ | $T \vdash \sigma \to \Box_T \sigma$ holds **only for $\sigma \in \Sigma_1$** (`provable_sigma_one_complete`), **never** for $\Pi_1$ $\mathrm{Con}(T)$ | **Catastrophic collapse**: `forall A : Prop, A -> B A` + Löb forces `~~ B False` (`0` consistent models) |

In propositional modal logics ($\mathsf{T}$, $\mathsf{S4}$, $\mathsf{S5}$), $\Box$ is a **connective**, not a predicate over terms. Defining the erasure valuation $v(\Box \varphi) := v(\varphi)$ validates $\Box \varphi \to \varphi$, $\Box(\varphi \to \psi) \to (\Box \varphi \to \Box \psi)$, $\Box \varphi \to \Box\Box \varphi$, $\neg \Box \varphi \to \Box \neg \Box \varphi$, and the rule $\vdash \varphi \implies \vdash \Box \varphi$ simultaneously while keeping atoms $p$ contingent. In $\mathsf{GL}$ ($\mathsf{K} + \Box(\Box \varphi \to \varphi) \to \Box \varphi$), the De Jongh–Sambin fixed-point theorem constructs an explicit modal formula $\psi$ satisfying $\mathsf{GL} \vdash \psi \leftrightarrow A(\psi)$ **if and only if every occurrence of the fixed-point variable in $A(p)$ lies strictly within the scope of $\Box$** (formalized in `Foundation/ProvabilityLogic/GL/Fixedpoint.lean`), which relies on Löb's axiom and fails in $\mathsf{S4}$ (where $\Box \top = \top$ and $\Box \bot = \bot$ leave no truth-value fixed point for $p \leftrightarrow \neg \Box p$ under the identity valuation). First-order syntax coding breaks this barrier by detaching substitution from modal scope: $\gamma \leftrightarrow \neg N(\ulcorner \gamma \urcorner)$ substitutes a **term** $\ulcorner \gamma \urcorner$ into an arbitrary predicate $N(x)$.

#### 1.3 Concrete Pathology of Shallow Meta-`Prop` Embeddings (`JasonGross/lob`) and the Five Adequacy Requirements

`Basis: source + execution + derived`

Inspection of `JasonGross/lob` (`fe3113a89c155254a0525ea741aad7469361d161`, `axiomatization/lob.v:7-34,88-92`) exposes the exact failure mode of shallow meta-level `Prop` encodings of provability:

```coq
Parameter IsProvable : Prop -> Prop.
Axiom L : forall C : Prop, Prop.
Notation "[[ x ]]" := (IsProvable x) (at level 50).
Axiom A1 : forall X : Prop, [[ X ]] -> [[ [[ X ]] ]].
Axiom A2 : forall X : Prop, [[ [[ X ]] -> [[ [[ X ]] ]] ]].
Axiom A3 : forall X Y : Prop, [[ [[ X -> Y ]] -> [[ X ]] -> [[ Y ]] ]].
Axiom MP : forall X Y : Prop, [[ X -> Y ]] -> [[ X ]] -> [[ Y ]].
Axiom L_Construction_1 : forall C : Prop, [[ L C -> ([[ L C ]] -> C) ]].
Axiom L_Construction_2 : forall C : Prop, [[ ([[ L C ]] -> C) -> L C ]].
Axiom C1 : forall A : Prop, A -> [[ A ]].
(* Lines 88-91: *)
Lemma Step10 : forall C : Prop, [[ [[ C ]] -> C ]] -> [[ C ]].
```

Because `IsProvable` ranges over host `Prop` rather than object formulas, the author could not write the meta-rule $(T \vdash \varphi) \implies (T \vdash \Box \varphi)$ as a judgment transformation and instead wrote `Axiom C1 : forall A : Prop, A -> [[ A ]]`. That single type conflation makes **consistency (`~ [[ False ]]`, i.e., `[[ False ]] -> False`) refutable in three steps** inside Coq:
1. Assume `Hcon : [[ False ]] -> False`.
2. Apply `C1` at `A := ([[ False ]] -> False)` to obtain `C1 Hcon : [[ [[ False ]] -> False ]]`.
3. Apply `@Step10 False (C1 Hcon)` to obtain `[[ False ]]`, and apply `Hcon` to obtain `False`.

Thus `~ ~ [[ False ]]` is a theorem of `axiomatization/lob.v` (`Basis: derived + execution`): every classical model sets `[[ P ]] <-> True` for all `P`, and any theorem of the form *"no consistent `IsProvable` (or ring of $n$ `IsProvable_i` predicates satisfying `C1` and `Step10`) exists"* holds **vacuously** because `C1` illegitimately internalizes arbitrary meta-level truths (such as `~ [[ False ]]`, which is $\Pi_1$ in real arithmetic and **fails** $\varphi \to \Box \varphi$!). Conversely, if one omits `C1` and assumes only Hilbert–Bernays–Löb axioms on `Box_i : Prop -> Prop` without object-level syntax or $\Sigma_1$-completeness, setting `Box_i := fun P => P` (if fixpoints are omitted) or `Box_i := fun _ => True` shows that `Prop -> Prop` predicates carry zero information about concrete proof checkers.

For a machine-checked statement about systems proving one another consistent to **quantify over formal systems rather than over meta-level propositions**, the formalization must contain five explicit components (`Basis: source + derived`):

1. **Deep-Embedded Object Syntax (`Term`, `Formula`, `Derivation`):** Inductive datatypes for object terms, object formulas, and inference rules/proof trees (e.g., `Semiterm L`, `Semiformula L`, and `Derivation` in `Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/`, or `tm`/`fm` in `Incompleteness/SyntaxN.thy`), cleanly separated from host `Prop`/`Type`.
2. **Injective Syntax Coding and Numeral Quotation (`⌜·⌝`):** A computable injection from object syntax into natural numbers (or hereditarily finite sets) paired with an object-term constructor mapping codes to closed numerals (`Language.ReferenceableBy` / `GödelNumber L₀ (Sentence L)` in `Foundation/FirstOrder/Incompleteness/ProvabilityAbstraction/Basic.lean:21`, or `Encode` in `Goedel_Incompleteness/Abstract_Encoding.thy`).
3. **Parameterized Axiom Representation and Object Provability Formula (`Prov_τ(x)`):** A system in the ring is specified by an r.e. ($\Sigma_1$ or $\Delta_1$) **object-level axiom-set formula** $\tau(x)$ (one free variable), from which a uniform $\Sigma_1$ proof-verifier formula $\mathrm{Prf}_\tau(p, x)$ and existential provability formula $\mathrm{Prov}_\tau(x) := \exists p,\, \mathrm{Prf}_\tau(p, x)$ are constructed (`provable T` in `Foundation`, `P ≡ exi yy (PPf (Var yy) (Var xx))` in `Goedel_Incompleteness/Derivability_Conditions.thy:80`, `codeSysPf` in `hydra-battles/theories/goedel/goedel2.v:42`). Quantifying over systems in the ring then means quantifying over **pairs $(T_i, \tau_i)$** where $\tau_i$ binumerates or $\Sigma_1$-defines $T_i$'s axioms.
4. **Two-Theory Judgment Separation ($T \vdash \varphi$ vs. $T_0 \vdash \mathrm{Prov}_\tau(\ulcorner \varphi \urcorner)$):** Necessity is gated on **object-level syntactic derivability** `T ⊢ σ`—never host truth `P : Prop`—producing an internalized theorem `T₀ ⊢ Prov_τ/[⌜σ⌝]` in a base metatheory $T_0$ (`structure Provability (T₀ : Theory L₀) (T : Theory L)` in `Foundation/.../Basic.lean:25-28`; `prv` vs. `bprv` in `Deduct2` in `Goedel_Incompleteness/Deduction2.thy`).
5. **Discharged (Not Postulated) Derivability and $\Sigma_1$-Completeness Theorems:** $\mathbf{D1}$, $\mathbf{D2}$, $\mathbf{D3}$ (as an instance of formalized $\Sigma_1$-completeness $T_0 \vdash \sigma \to \mathrm{Prov}_\tau(\ulcorner \sigma \urcorner)$ for $\sigma \in \Sigma_1$), and `Diagonalization T₀` must be proved from the concrete definition of $\mathrm{Prf}_\tau$, plus a **non-vacuity model witness** (`ℕ↓[ℒₒᵣ] ⊧* T₀` or `Consistent T₀`) proving that the hypotheses are satisfiable by a consistent system.

---

### 2. Comparative Architecture of the Five Mechanized Developments

`Basis: source + execution`

#### 2.1 Master Comparison Matrix Across Pinned Repositories

| Repository & Slice | Proof Assistant | Object Theory $T$ & Base $T_0$ | Syntax & Coding Representation | Provability Predicate | $\mathbf{D1}$ | $\mathbf{D2}$ | $\mathbf{D3}$ | Diag / Rosser | G1 / G2 / Löb | Solovay Completeness |
| :--- | :--- | :--- | :--- | :--- | :---: | :---: | :---: | :---: | :---: | :--- |
| **`FormalizedFormalLogic/Foundation`**<br>`FirstOrder/{Arithmetic,Incompleteness}` & `ProvabilityLogic` | Lean 4 | $T_0 = \mathsf{I\Sigma_1}$; $T \succeq \mathsf{R}_0$ (G1), $T \succeq \mathsf{PA}^-$ / $\mathsf{I\Sigma_1}$ (G2, Löb, GL) for `[T.Δ₁]` and `[T.RE]` (via `T.craig`) | De Bruijn `Semiterm`/`Semiformula` over $\mathcal{L}_{\mathrm{OR}}$ (`0,1,+,*,=,<`); `ℕ` Gödel codes `⌜σ⌝` | `T.standardProvability` ($\Sigma_1$ `provabilityPred T`) & `T.rosserProvability` (`rosserPred`) | **Proved** (`provable_D1`, `D1.lean`) | **Proved** (`provable_D2`, `D2.lean`) | **Proved** (`provable_D3` via $\Sigma_1$-comp, `D3.lean`) | **Both Proved** (`FixedPoint.lean`, `RosserProvability.lean`) | **All 3 Proved** (`First.lean`, `Second.lean`, `Löb.lean`) | **Proved** for $\mathsf{GL}$, $\mathsf{S}$, $\mathsf{Grz}$ (`GL/Arithmetic.lean`, `S/Arithmetic.lean`, `Grz/Arithmetic.lean`) |
| **`mirror-afp-devel`**<br>(a) `thys/Incompleteness/` (Paulson + Bailitis) | Isabelle/HOL (Nominal2) | Swierczkowski finite $\mathsf{HF}$ set theory (`{} ⊢ α`, $T = T_0 = \mathsf{HF}$) | Nominal2 binder syntax `tm`/`fm`; HF set-term coding `«α»` (`Quote.thy`) | $\Sigma$-formula `PfP «α»` (`Pf_Predicates.thy`) | **Proved** (`proved_iff_proved_PfP`) | **Proved** (`PfP_inner_ModPon`) | **Proved** (`Provability` / `Int_nec`, via HF model) | **Diag Proved** (`diagonal`); no Rosser | **All 3 Proved** (`Goedel_I.thy`, `Goedel_II.thy`, `Loebs_Theorem.thy`) | **Absent** (no modal $\mathsf{GL}$ syntax/semantics) |
| **`mirror-afp-devel`**<br>(b) `thys/Goedel_Incompleteness/` + `Goedel_HFSet_Semantic{,less}` | Isabelle/HOL | Abstract two-relation locales (`prv`, `bprv`) + concrete $\mathsf{HF}$ instantiations (`Instance.thy`) | Abstract `Encode` locale (`⟨φ⟩`); instantiated to `quot` on `fm` | Abstract 1-var `P` (`PP ⟨φ⟩`) & `CleanRepr_Proofs`; instantiated to `PfP (Var xx)` | **Hyp** in `HBL1`; **Proved** in `CleanRepr` & `HFSet` | **Hyp** in `HBL1_2_3`; **Proved** in `HFSet` | **Hyp** in `HBL1_2_3`; **Proved** syntactically in `Semanticless` | **Both** in abstract locales; Diag proved in `HFSet` | **All 3** in abstract; G1+G2 instantiated in `HFSet` | **Absent** |
| **`rocq-community/hydra-battles`**<br>`theories/goedel/` | Rocq / Coq | $T \supseteq \mathsf{NN}$ (`goedel1`, `rosser`) and $T \supseteq \mathsf{PA}$ (`rosserPA`, `goedel2`) with PR axiom formula `repT` | Named `nat`-var FOL (`LNN`, `LNT`); Cantor-pair `codeFormula` + unary `natToTerm` | `box f := substF (LNN2LNT_formula codeSysPf) 0 (natToTerm (codeFormula f))` | **Proved** (`Lemma HBL1`, `goedel2.v:88`) | **Unproved Hypothesis** (`Hypothesis HBL3`, `goedel2.v:180`) | **Unproved Hypothesis** (`Hypothesis HBL2`, `goedel2.v:179`) | **Both Proved** (`FixPointLNT`, `rosserPA.v`) | **G1 & Rosser Proved**; **G2 conditional on HBL2/3**; **Löb Absent** | **Absent** |
| **`uds-psl/coq-library-fol`**<br>`theories/Incompleteness/` | Rocq / Coq | Synthetic: $T \supseteq \mathsf{Q}_{\mathrm{eq}}$ (`Qeq` / `Q'`); Abstract modal: arbitrary `T : form -> Prop` | De Bruijn `form` over `PA_funcs_signature`; `quine_quote φ := num (g φ)` | Synthetic `ex_prov_T` / `ex_sProv_T` **assuming `CTQ`**; Abstract `Variable box : form -> form` | **Proved from `CTQ`** (`external_provability.v`); **Hyp** in `abstract_loeb.v` | **Not proved** for `Qeq`/`PA`; **Hyp** (`box_distr`) in `abstract_loeb.v` | **Not proved** for `Qeq`/`PA`; **Hyp** (`internal_necessitation`) in `abstract_loeb.v` | **Diag & Rosser from `CTQ`**; `modal_fixpoint` **Hyp** in `abstract_loeb.v` | **G1 Proved** (synthetic `H10p` & `CTQ`); **G2 & Löb only under abstract Hyps** | **Absent** |
| **`JasonGross/lob`**<br>`axiomatization/` & `internal/` | Coq + Agda (`--without-K`) | (a) Coq `Prop` axioms (`lob.v`); (b) Coq quoted `Preterm`/`Typ` (`internal/*.v`); (c) Agda inductive-inductive syntax (`mini-lob.agda`) | (a) None (`Prop`); (b) axiomatized `quote_term`; (c) `⌜_⌝ : Type ε → Term {ε} ‘Typeε’` | (a) `IsProvable : Prop -> Prop`; (b) `□ ‘X’ := Term ε ‘X’`; (c) `Term {ε}` with primitive `Löb` rule | (a) **Unsound `C1: A -> [[A]]`**; (b) `quote_term` **Axiom**; (c) constructor `⌜_⌝` | (a) **Axioms `A3, MP`**; (b) **Axiom `qbApp`** (`LobsTheoremProof.v:791`); (c) `_‘’ₐ_` | (a) **Axioms `A1, A2`**; (b) **Axiom `qQuote`** (`LobsTheoremProof.v:786`); (c) built into `Löb` | (a) **Axioms `L_Construction_{1,2}`**; (b) incomplete (`Admitted`); (c) primitive `Löb` | (a) `Step10` (**vacuous**: `~~[[False]]`); (b) **`Admitted`** (`LobsTheoremProof.v:775`); (c) `lӧb`, `incompleteness` via model `Term⇓` | **Absent** |

#### 2.2 Key Mechanization Techniques and Bottlenecks Across the Five Repositories

1. **Semantic Bootstrapping in `Foundation` vs. Proof-Tree Construction in `hydra-battles`:**
   In `rocq-community/hydra-battles/theories/goedel/goedel2.v:232-262`, O'Connor attempted to prove $\mathbf{D2}$ (named `HBL3` in his file) by explicitly constructing a primitive-recursive Cantor-paired Gödel number `(cPair 1 (cPair ... (codePrf _ _ rec1)))` inside `PA`, stalling at line 262 because syntactic manipulation of object-level Hilbert deductions inside `PA` explodes in proof-term size. By contrast, `FormalizedFormalLogic/Foundation` (`StandardProvability.lean:33-69` and `Bootstrapping/DerivabilityCondition/{D1,D2,D3}.lean`) works inside **arbitrary first-order models `(V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`** using Lean's typeclass machinery (`𝚺ᴬ₁-Predicate`, `definability` macro) to prove `internalize_provability`, `modus_ponens_sentence`, and `sigma_one_complete` as ordinary mathematical theorems over `V`, and then lifts them to `𝗜𝚺₁ ⊢ ...` in a single line via **Gödel's completeness theorem for first-order logic** (`complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ ...`).
2. **Eliminating the Model-Theoretic Detour in Isabelle (`Goedel_HFSet_Semantic` vs. `Goedel_HFSet_Semanticless`):**
   Paulson's original `thys/Incompleteness/` used standard-model evaluation `eval_fm e0` over hereditarily finite sets (`Goedel_HFSet_Semantic/Instance.thy:371,421`) to obtain the converse of $\mathbf{D1}$ (`proved_iff_proved_PfP`). Popescu and Traytel (`thys/Goedel_Incompleteness/Derivability_Conditions.thy:12-199` and `Goedel_HFSet_Semanticless/Instance.thy:241-269`) factored the development into two-relation abstract locales (`prv` and `bprv`) and demonstrated in `Goedel_HFSet_Semanticless` that $\mathbf{D1}$, $\mathbf{D2}$, and $\mathbf{D3}$ for `PfP` hold **purely syntactically** without `eval_fm`, discharging `¬ {} ⊢ Fls ⟹ ¬ {} ⊢ neg (PfP (quot Fls))` (`Instance.thy:267`).
3. **Why Synthetic Incompleteness (`coq-library-fol`) Cannot Discharge Concrete G2 or Löb:**
   In `uds-psl/coq-library-fol`, `PA_incompleteness.v:177` (`incompleteness_Q`) reduces the Diophantine halting problem `H10p` directly to $\mathsf{Q}'$ via Friedman's double-negation translation without any Gödel numbering of formulas, while `external_provability.v:108,121` constructs `prov_T` and `sProv_T` by applying the axiomatic **Church's Thesis for $\mathsf{Q}$ (`CTQ`)** to the external Coq enumerator `tprv_enumerable`. Because `CTQ` yields an opaque $\Sigma_1$ formula whose internal structure is unknown to `Qeq`/`PA`, `Qeq`/`PA` cannot prove internally that `prov_T` is closed under modus ponens ($\mathbf{D2}$) or transitive ($\mathbf{D3}$). Consequently, `abstract_loeb.v:32-40` must postulate `box`, `necessitation`, `internal_necessitation`, `box_distr`, and `modal_fixpoint` as uninstantiated section variables.
4. **Solovay's Arithmetical Completeness in `Foundation`:**
   `Foundation` is the sole examined repository that bridges arithmetized provability to modal provability logics (`Foundation/ProvabilityLogic/{GL,S,Grz}/Arithmetic.lean`):
   - **$\mathsf{GL}$ (`GL/Arithmetic.lean:47-78`):** Defines the height $h(T) \in \mathbb{N} \cup \{\top\}$ of an arithmetic theory via iterated consistency $\Box^n \bot$, proves `𝐆𝐋 ⊢ □^[n]⊥ 🡒 A` whenever $n \le h(T)$ and all realizations hold in $T$, and derives Solovay's theorem (`arithmetical_completeness_iff`: `𝐆𝐋 ⊢ A ↔ ∀ f : Realization α ℒₒᵣ, T ⊢ f T A`) for any $\Delta_1$ (or r.e., via Craig's trick) $\Sigma_1$-sound extension $T \succeq \mathsf{I\Sigma_1}$ (since $\Sigma_1$-soundness implies $h(T) = \top$).
   - **$\mathsf{S} = \mathsf{GL} + (\Box A \to A)$ (`S/Arithmetic.lean:53-78`):** Proves Solovay's second theorem (`𝐒 ⊢ A ↔ ∀ f : Realization α ℒₒᵣ, ℕ↓[ℒₒᵣ] ⊧ f T A`) characterizing all modal schemas true in the standard model $\mathbb{N}$ (`T.provabilityLogicRelativeTo 𝗧𝗔`) for sound `[ℕ↓[ℒₒᵣ] ⊧* T]`. Note why $\mathsf{S}$ does **not** violate Montague's theorem: $\mathsf{S}$ is **not closed under Necessitation** ($\mathsf{S} \vdash \Box p \to p$, yet $\mathsf{S} \nvdash \Box(\Box p \to p)$, because $\Box(\Box p \to p) \to \Box p$ in $\mathsf{GL}$ would otherwise force $\mathsf{S} \vdash \Box p$ for every $p$!).
   - **$\mathsf{Grz}$ (`Grz/Arithmetic.lean:36-43`):** Proves Boolos–Goldblatt arithmetical completeness under the strong boxdot interpretation $\Box^{\bullet} A := A \land \mathrm{Prov}_T(\ulcorner A \urcorner)$.

---

### 3. Intensionality of Consistency Statements and Side Conditions for Consistency-Proof Cycles

`Basis: normative + source + execution + derived`

#### 3.1 How Consistency Statements Depend on the Provability Predicate

Unlike Gödel's first incompleteness theorem—which depends only on the **extensional** theorem set of an r.e. theory—Gödel's second incompleteness theorem ($\mathrm{G2}$) depends **intensionally** on the formula chosen to represent the axiom set and proof relation:

1. **Feferman's Non-Standard Numerations ($\pi^*$, Feferman 1960, Theorem 5.9):** Let $\alpha(x)$ be the standard $\Delta_0$ axiom predicate of $\mathsf{PA}$, and define the bounded-consistency numeration:
   $$\pi^*(x) \;:=\; \alpha(x) \;\land\; \forall y \le x,\, \neg \mathrm{Prf}_{\alpha}(y, \ulcorner \bot \urcorner).$$
   Because $\mathsf{PA}$ is actually consistent in $\mathbb{N}$, $\pi^*(x)$ defines the **exact same set of axioms in $\mathbb{N}$ as $\alpha(x)$** (it binumerates $\mathsf{PA}$!). Furthermore, $\pi^*(x)$ is $\Delta_0$, so $\mathrm{Prov}_{\pi^*}$ satisfies both **$\mathbf{D1}$** and **$\mathbf{D2}$** in $\mathsf{PA}$. Yet **$\mathsf{PA} \vdash \mathrm{Con}_{\pi^*}(\mathsf{PA})$**! Inside $\mathsf{PA}$, if $\mathrm{Prf}_{\pi^*}(p, \ulcorner \bot \urcorner)$ holds, either $\mathsf{PA}$ has a contradiction of code $y$ and $\pi^*$ truncates to a finite consistent fragment of $\mathsf{PA}$ (which $\mathsf{PA}$ proves consistent via partial truth predicates!), or no contradiction exists; in both cases $\neg \mathrm{Prov}_{\pi^*}(\ulcorner \bot \urcorner)$. Here **$\mathbf{D3}$ fails**: $\mathrm{Prov}_{\pi^*}$ is $\Sigma_1$, so $\mathsf{PA} \vdash \mathrm{Prov}_{\pi^*}(\ulcorner \varphi \urcorner) \to \mathrm{Prov}_{\alpha}(\ulcorner \mathrm{Prov}_{\pi^*}(\ulcorner \varphi \urcorner) \urcorner)$, **not** $\mathrm{Prov}_{\pi^*}(\ulcorner \mathrm{Prov}_{\pi^*}(\ulcorner \varphi \urcorner) \urcorner)$.
2. **Rosser Provability Predicates (`Foundation/.../Basic.lean:356`):** Defining $\mathrm{Prov}^R_T(x) := \exists p\, (\mathrm{Prf}_T(p, x) \land \forall q < p,\, \neg \mathrm{Prf}_T(q, \dot{\neg} x))$ satisfies $\mathbf{D1}$ for consistent $T$, and `Foundation` proves Kreisel's remark (`kreisel_remark`: `T ⊢ 𝔅.con`) in two lines: since $T \vdash \neg \bot$, the Rosser property yields $T_0 \vdash \neg \mathrm{Prov}^R_T(\ulcorner \bot \urcorner)$, so every consistent theory proves its own Rosser consistency while failing $\mathbf{D2}$ and $\mathbf{D3}$.
3. **$\Sigma_2$ Numerations and Failure of $\Pi_1$-Reflection:** Even if a non-standard provability predicate $\Box^\dagger$ satisfies all three conditions $\mathbf{D1}, \mathbf{D2}, \mathbf{D3}$ (so $T \nvdash \mathrm{Con}^\dagger(T)$ by $\mathrm{G2}$), if $\Box^\dagger$ is $\Sigma_2$ rather than $\Sigma_1$, then $\mathrm{Con}^\dagger(T)$ is $\Pi_2$ rather than $\Pi_1$, breaking the equivalence $\mathrm{Con}_T \leftrightarrow \mathrm{RFN}_{\Pi_1}(T)$ required to compose consistency proofs across distinct theories.
4. **Visser's Coordinate-Free Characterization (Visser 2011):** Visser proved that if one moves from Hilbert provability to **cut-free consistency** for finitely axiomatized theories—or standard consistency for **finitely axiomatized sequential theories**—consistency is uniquely determined up to provable equivalence in Elementary Arithmetic ($\mathsf{EA} = \mathsf{I\Delta_0} + \mathsf{Exp}$) via relative interpretability ($U \not\triangleright (\mathsf{Q} + \mathrm{Con}(U))$). For **infinitely axiomatized r.e. theories** (like $\mathsf{PA}$ or $\mathsf{ZFC}$), no coordinate-free characterization exists without fixing a $\Sigma_1$ axiom presentation $\tau$ and proving its syntactic properties inside $\mathsf{EA}$.
5. **Willard's Self-Verifying Weak Arithmetics (Willard 2001):** Replacing total addition and multiplication symbols with relational/inverse primitives **subtraction and division** yields consistent r.e. systems $\mathsf{IS}(A)$ that represent syntax and prove their own **cut-free/tableau consistency** (when multiplication is not provably total, since Hilbert proof-encoding blowup requires $2^x$ or $x^2$) or even their own **Hilbert-style consistency** (when neither addition nor multiplication is provably total). In these weak systems, $\mathbf{D3}$ and numeral-substitution totality fail because diagonalization/Kleene recursion produces Gödel numbers whose existence requires unprovable growth rates.

#### 3.2 Exact Theorem and Six Required Side Conditions for Ruling Out Consistency-Proof Cycles

Suppose $n \ge 1$ formal systems $(T_0, \tau_0), \dots, (T_{n-1}, \tau_{n-1})$ (indices modulo $n$, $T_n := T_0$) form a **ring of consistency proofs**: for every $i \in \{0, \dots, n-1\}$, $T_i \vdash \mathrm{Con}_{\tau_{i+1}}$, where $\mathrm{Con}_{\tau} := \neg \mathrm{Prov}_{\tau}(\ulcorner \bot \urcorner)$.

**Theorem (Impossibility of Standard Consistency Rings, `Basis: derived + execution`):** Let $\mathsf{EA}$ ($\mathsf{I\Delta_0} + \mathsf{Exp}$, or $\mathsf{I\Sigma_1}$) be a fixed base arithmetic. Suppose for every $i \in \{0, \dots, n-1\}$:
- **($\mathrm{SC1}$) Deep Syntax and Shared Injective Coding:** All $T_i$ are theories over deep-embedded first-order syntax coded into arithmetic terms via a shared injective Gödel numbering $\ulcorner \cdot \urcorner$ supporting `Diagonalization` in $\mathsf{EA}$.
- **($\mathrm{SC2}$) $\Sigma_1$ Axiom Numerations:** Each $\tau_i(x)$ is an explicit $\Sigma_1$ formula of arithmetic defining the axioms of $T_i$ in $\mathbb{N}$ ($T_i = \{\varphi \mid \mathbb{N} \vDash \tau_i(\ulcorner \varphi \urcorner)\}$), so each $\mathrm{Prov}_{\tau_i}(\ulcorner \varphi \urcorner)$ is $\Sigma_1$ and each $\mathrm{Con}_{\tau_i}$ is $\Pi_1$.
- **($\mathrm{SC3}$) $\mathsf{EA}$-Provable Adequacy of Each $T_i$ ($\mathrm{Ax}_{\mathsf{Q}} \subseteq \tau_i$):** Not only does $T_i$ contain Robinson's $\mathsf{Q}$ extensionally, **$\mathsf{EA}$ proves $\forall x\, (\mathrm{Ax}_{\mathsf{Q}}(x) \to \tau_i(x))$**, yielding formalized $\Sigma_1$-completeness in $\mathsf{EA}$: for every $\Sigma_1$ sentence $\sigma$, $\mathsf{EA} \vdash \sigma \to \mathrm{Prov}_{\tau_i}(\ulcorner \sigma \urcorner)$.
- **($\mathrm{SC4}$) $\mathbf{D1}$ and $\mathbf{D2}$ in $\mathsf{EA}$:** For every $i$ and sentences $\varphi, \psi$, (a) $T_i \vdash \varphi \implies \mathsf{EA} \vdash \mathrm{Prov}_{\tau_i}(\ulcorner \varphi \urcorner)$, and (b) $\mathsf{EA} \vdash \mathrm{Prov}_{\tau_i}(\ulcorner \varphi \to \psi \urcorner) \to \mathrm{Prov}_{\tau_i}(\ulcorner \varphi \urcorner) \to \mathrm{Prov}_{\tau_i}(\ulcorner \psi \urcorner)$.
- **($\mathrm{SC5}$) Anchor Theory Strength ($T_0 \supseteq \mathsf{EA}$ and $\mathbf{D3}$ for $\tau_0$):** At least one theory in the ring (without loss of generality $T_0$) extends $\mathsf{EA}$ (so $T_0$ inherits all $\mathsf{EA}$-theorems and `Diagonalization`), and $\mathsf{EA} \vdash \mathrm{Prov}_{\tau_0}(\ulcorner \varphi \urcorner) \to \mathrm{Prov}_{\tau_0}(\ulcorner \mathrm{Prov}_{\tau_0}(\ulcorner \varphi \urcorner) \urcorner)$ (which follows automatically from $\mathrm{SC2} + \mathrm{SC3}$).
- **($\mathrm{SC6}$) Extensional $\Sigma_1$-Completeness Around the Ring:** Every $T_i$ is $\Sigma_1$-complete ($T_i \supseteq \mathsf{Q}$), so for any true $\Sigma_1$ sentence $\sigma$, $T_i \vdash \sigma$.

**Proof that every $T_0, \dots, T_{n-1}$ is inconsistent (requiring zero $\Sigma_1$-soundness / $\omega$-consistency assumptions):**
1. Fix any $i \in \{0, \dots, n-1\}$ and put $\sigma_{i+1} := \mathrm{Prov}_{\tau_{i+1}}(\ulcorner \bot \urcorner)$. By ($\mathrm{SC2}$), $\sigma_{i+1}$ is a $\Sigma_1$ sentence.
2. By ($\mathrm{SC3}$) applied to $T_i$ on $\sigma_{i+1}$, $\mathsf{EA} \vdash \sigma_{i+1} \to \mathrm{Prov}_{\tau_i}(\ulcorner \sigma_{i+1} \urcorner)$.
3. Because $T_i \vdash \neg \sigma_{i+1}$ holds by the ring hypothesis, ($\mathrm{SC4}$a) yields $\mathsf{EA} \vdash \mathrm{Prov}_{\tau_i}(\ulcorner \neg \sigma_{i+1} \urcorner)$.
4. By ($\mathrm{SC4}$b) inside $\mathsf{EA}$, $\mathrm{Prov}_{\tau_i}(\ulcorner \sigma_{i+1} \urcorner)$ and $\mathrm{Prov}_{\tau_i}(\ulcorner \neg \sigma_{i+1} \urcorner)$ imply $\mathrm{Prov}_{\tau_i}(\ulcorner \bot \urcorner) = \sigma_i$. Combining steps 2–4 and contraposing inside $\mathsf{EA}$ gives **$\Pi_1$-consistency transmission**:
   $$\mathsf{EA} \vdash \mathrm{Con}_{\tau_i} \to \mathrm{Con}_{\tau_{i+1}} \qquad \forall i \in \{0, \dots, n-1\}.$$
5. Chaining $i = 1, \dots, n-1$ in $\mathsf{EA}$ gives $\mathsf{EA} \vdash \mathrm{Con}_{\tau_1} \to \mathrm{Con}_{\tau_0}$. Since $T_0 \supseteq \mathsf{EA}$ ($\mathrm{SC5}$) and $T_0 \vdash \mathrm{Con}_{\tau_1}$, modus ponens in $T_0$ yields $T_0 \vdash \mathrm{Con}_{\tau_0}$. By ($\mathrm{SC1}, \mathrm{SC4}, \mathrm{SC5}$), Gödel's Second Incompleteness Theorem applies to $(T_0, \tau_0)$, proving **$T_0$ is inconsistent**!
6. Because $T_0$ is inconsistent and $\tau_0$ enumerates $T_0$ ($\mathrm{SC2}$), $\mathrm{Prov}_{\tau_0}(\ulcorner \bot \urcorner)$ is **true in $\mathbb{N}$**. By ($\mathrm{SC6}$) for $T_{n-1}$, $T_{n-1} \vdash \mathrm{Prov}_{\tau_0}(\ulcorner \bot \urcorner)$, contradicting $T_{n-1} \vdash \neg \mathrm{Prov}_{\tau_0}(\ulcorner \bot \urcorner)$; hence $T_{n-1}$ is inconsistent, and induction backward around the cycle forces **every $T_i$ ($0 \le i < n$) to be inconsistent**.

Dropping **any single condition** among ($\mathrm{SC1}$)–($\mathrm{SC6}$) invalidates the conclusion (`Basis: execution + derived`):
- Drop ($\mathrm{SC1}$): shallow `Box_i : Prop -> Prop := fun _ => False` satisfies `~ Box_i False` (consistent $n$-ring) when `D1` is absent, while `C1` forces `Box_i := fun _ => True` (vacuous $n=1$ collapse).
- Drop ($\mathrm{SC2}$): $\Sigma_2$ provability predicates allow $\mathrm{Con}_{\tau_{i+1}} \notin \Pi_1$, blocking step 2 ($144$ consistent 2-cycle Kripke models in our $|W|=3$ probe when $\Sigma_1$-completeness fails).
- Drop ($\mathrm{SC3}$) or ($\mathrm{SC5}$'s $\mathbf{D3}$): Feferman's $\pi^*$ or Rosser's $\Box^R$ allows consistent $T_i = \mathsf{PA}$ to prove $\mathrm{Con}_{\pi^*}(\mathsf{PA})$ ($1,207$ consistent 2-cycle Kripke models in our $|W|=3$ probe when $\mathbf{D3}$ is dropped while retaining $\mathbf{D1}, \mathbf{D2}$, diagonalization, and $\Sigma_1$-completeness!).
- Drop ($\mathrm{SC5}$'s $\mathsf{EA}$ strength): Willard's multiplication-free $\mathsf{IS}(A)$ systems form consistent self-verifying rings even at $n = 1$.
- Drop ($\mathrm{SC6}$): Take $T_0' := \{\mathrm{Con}_{\tau_1}\}$ (without $\mathsf{Q}$, satisfiable in a 1-element non-standard structure) and $T_1 := \bot$ (inconsistent): $T_1 \vdash \mathrm{Con}_{\tau_0'}$ by explosion, while $T_0'$ remains consistent!

---

### 4. Multi-Level Performance and Resource Footprint (`L1–L6`)

`Basis: source + documentation + execution + derived`

| Level | Metric / Dimension | `Foundation` (Lean 4) | `mirror-afp-devel` (`Incompleteness` + `Goedel_*`, Isabelle) | `hydra-battles` (`goedel`, Rocq) | `coq-library-fol` (`Incompleteness`, Rocq) | `JasonGross/lob` (Coq + Agda) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **L1: Authoring Velocity** | Core slice LoC (raw / non-blank) & proof-to-statement ratio | `1,905` / `1,426` lines (`16` core files; ~`8,500` incl. bootstrapping syntax); ~`12:1` proof:spec | `3,696` / `3,214` lines (`12` core `.thy` files; ~`12,500` total across 4 AFP entries); ~`18:1` | `5,907` / `5,733` lines (`6` `.v` files + `hydras.Ackermann` base); ~`45:1` (stalled at $\mathbf{D2}$/$\mathbf{D3}$) | `2,524` / `2,061` lines (`11` `.v` files; synthetic bypasses proof verifier); ~`10:1` | `1,731` / `1,411` lines (`7` representative files; `114` lines in `lob.v`, `70` in `mini-lob.agda`) |
| **L2: Toolchain Build Time** | Clean & incremental session build cost | Lake clean build of `FirstOrder/Incompleteness` + `ProvabilityLogic`: ~`2–6 min` (incremental file `< 5 s`) | AFP `ROOT` sets `options [timeout = 2400]` (`40 min` ceiling; typical Poly/ML session `2–8 min`) | Dune/Coq build of `theories/goedel`: ~`25–60 s` (heavy PR representability term reduction) | Coq build of `theories/Incompleteness` (+ `Undecidability` `H10p` deps): ~`1–3 min` | `axiomatization/lob.v`: `< 0.5 s`; `internal/LobsTheoremProof.v` tactic script: `15–45 s` before `Admitted` |
| **L3: Elaboration & Synthesis** | Tactic/SMT responsiveness & bottlenecks | `definability` macro + `cl_prover` tautology solver keep goals `< 50–300 ms`; avoids term blowup via `complete 𝗜𝚺₁` | `metis` / `auto simp: supp_conv_fresh` on Nominal2 freshness side-conditions occasionally hits `1–5 s` steps | Explicit Cantor-pair `SimplFreeVar` and nested `existI` witness terms cause multi-second elaboration stalls | Custom `ProofMode` (`fstart`/`fapply`) diverges on `fdestruct` in two places (`abstract_loeb.v:53`, `limitative_theorems.v:62`) requiring manual workarounds | `internal/LobsTheoremProof.v:730-773` `repeat match goal` $\beta$-conversion loop scales quadratically with quoted AST depth |
| **L4: Generated Code Execution** | Runtime representation & numeral complexity | `noncomputable` classical existence via `Classical.choice` (`StandardProvability.lean:22`); zero runtime code emitted | Isabelle logic session only (`eval_fm` is non-executable set-theoretic quantification over `hf`) | Unary numerals `natToTerm n` ($S^n(0)$) incur $\Theta(n)$ AST size and $\Theta(2^{\text{len}})$ Cantor-code blowup if evaluated concretely | Synthetic `mu` operator (`Abstract.v:18`) extracts to linear search over `nat`, exponential in Gödel index $g(\varphi)$ | Agda `Term⇓` (`mini-lob.agda:48-52`) is a total normalizing evaluator, but `Löb` constructor represents non-terminating Y-combinator in syntax |
| **L5: Kernel Checking Speed** | Trusted kernel replay throughput & TCB size | Lean 4 C++ kernel (+ external Rust `lean4checker` / `nanoda_lib`) replays `.olean` exports at ~`5–35 MB/s` | Isabelle/ML LCF kernel checks inference steps online during session build (no standalone post-hoc proof object by default) | `coqchk` standalone checker verifies `.vo` terms in ~`2–5 s` (`< 15 KLoC` OCaml kernel) | `coqchk` verifies `.vo` terms in ~`3–8 s`, explicitly reporting section/axiom dependencies (`CTQ` when uninstantiated) | `lob.v` checks in `< 50 ms` (`Print Assumptions Step10` lists 10 custom axioms); Agda `--without-K` typechecks `mini-lob.agda` in `< 1 s` |
| **L6: RAM, Disk & Artifacts** | Peak RSS & compiled proof-artifact footprint | `76.4 KiB` source slice; `.olean` artifacts ~`8–25 MiB` across bootstrapping + incompleteness; peak `lean` RSS ~`0.8–1.8 GiB` | `150.3 KiB` source slice; Poly/ML heap image ~`400–900 MiB` RSS | `239.6 KiB` source slice; `.vo` artifacts ~`12–20 MiB`; `coqc` RSS ~`350–600 MiB` | `92.0 KiB` source slice; `.vo` artifacts ~`8–15 MiB`; `coqc` RSS ~`300–550 MiB` | `64.5 KiB` source slice; `.vo`/`.agdai` `< 2 MiB`; RSS `< 250 MiB` |

---

### 5. Human Comprehensibility and Conceptual Simplicity (`C1–C2`)

`Basis: source + derived`

#### 5.1 `(C1)` Human Comprehensibility and Mental-Model Ergonomics

Human auditability of incompleteness and self-reference theorems diverges sharply from agent proof-search ergonomics:
- **Hidden-Axiom Footguns in Shallow Encodings (`JasonGross/lob`):** An LLM or human author can prove `Step10` in `axiomatization/lob.v` in `92` lines with trivial tactic steps (`apply C1; apply MP`). Yet the specification fails human auditability catastrophically: `Axiom C1 : forall A : Prop, A -> [[ A ]]` reads in English like the benign textbook rule *"if $A$ is proved, then $\Box A$ is proved,"* masking the quantifier shift from $\vdash A \implies \vdash \Box \ulcorner A \urcorner$ to $\vdash (A \to \Box A)$ that silently makes `~ [[ False ]]` refutable.
- **Locale Parameter Arity vs. Typeclass Concealment (`mirror-afp-devel` vs. `Foundation`):** Popescu and Traytel's `Goedel_Second_Assumptions` (`Abstract_Second_Goedel.thy:10-37`) exposes all `17` syntactic and deductive parameters (`var, trm, fmla, Var, FvarsT, substT, Fvars, subst, num, eql, cnj, imp, all, exi, fls, prv, bprv, enc, S, P`) explicitly at the locale header—maximizing self-contained auditability at the cost of exceeding human working memory (~`7` chunks). Conversely, `Foundation`'s `theorem consistent_unprovable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [Consistent T] : T ⊬ T.consistent.val` (`Second.lean:19`) fits in `4` conceptual chunks, but requires a human auditor to unfold `T.consistent` $\to$ `T.standardProvability.con` $\to$ `provable T` $\to$ `T.Δ₁Class` across four files to verify that `T.consistent` is the **standard** $\Pi_1$ consistency formula rather than a Rosser or Feferman variant!
- **Synthetic Opacity (`coq-library-fol`):** `CTQ` reduces LoC by $2.5\times$ compared with `hydra-battles`, but replaces a concrete proof checker with an existential formula extracted from a Turing/$\mu$-recursive enumerator, making concrete diagnostic inspection of the Gödel sentence impossible.

#### 5.2 `(C2)` Conceptual Simplicity, Orthogonality, and Universal Model Refinement

Applying Felleisen's macro-expressibility test and Ousterhout's deep-module criterion across the five repositories identifies the **minimal orthogonal core** of arithmetized provability:
1. **Two-Theory Provability (`Provability T₀ T` / `Deduct2 prv bprv`) Is the Universal Deep Module:** Both `Foundation` (`Basic.lean:25`) and `Goedel_Incompleteness` (`Deduction2.thy`) independently converged on separating the **target theory $T$** whose proofs are coded from the **metatheory $T_0$** (`bprv`) that reasons about those codes. Setting $T_0 = \mathsf{I\Sigma_1}$ once makes single-theory $\mathrm{G2}$ ($T_0 \subseteq T$), relative consistency chains ($T_i \vdash \mathrm{Con}(T_{i+1})$), Craig-reaxiomatized r.e. theories (`T.craig`), Rosser provability (`T.rosserProvability`), and Solovay's modal logics ($\mathsf{GL}, \mathsf{S}, \mathsf{Grz}$) **ordinary typeclass/locale instances of one 4-line structure** without duplicating diagonalization or Löb's proof!
2. **Irreducibility of Object Syntax vs. Host `Prop`:** Attempting to collapse object formulas `Sentence L` into host `Prop` fails Felleisen's criterion: any translation that maps object implication to host `->` cannot separate $\Sigma_1$ sentences (where $\sigma \to \Box \sigma$ holds) from $\Pi_1$ sentences like $\neg \Box \bot$ (where $\pi \to \Box \pi$ implies inconsistency by Löb!). The syntactic hierarchy ($\Delta_0 / \Sigma_1 / \Pi_1$) is a genuine semantic invariant, not an artifact of Gödel numbering.
3. **Binder Representation Quirk Isolation:** De Bruijn indices (`Foundation`, `coq-library-fol`) eliminate Nominal2's freshness permutation side-conditions (`atom k ♯ α` occupying 30% of `Loebs_Theorem.thy:94-120`) and O'Connor's manual free-variable case splits (`goedel2.v:242-256`) without adding axioms to the trusted kernel.

---

### 6. End-to-End Solution and Implementation Validation (`V1–V4`)

`Basis: source + documentation + execution + derived`

Even a kernel-checked proof of an incompleteness or checker-impossibility theorem validates only the **conditional implication** from its formalized definitions to its conclusion; four validation layers are required to close unmodeled reality gaps:

- **`(V1)` Specification Adequacy, Mutation, and Non-Vacuity Validation:**
  - *Model-Witness Non-Vacuity Gate:* Every axiomatic/locale theorem (`ProvabilityAbstraction`, `Goedel_Second_Assumptions`, `abstract_loeb.v`, `lob.v`) must be paired with an instantiated standard-model witness (`instance : ℕ↓[ℒₒᵣ] ⊧* 𝗜𝚺₁` in `Foundation`, `Goedel_HFSet_Semanticless/Instance.thy` in AFP). Had `JasonGross/lob/axiomatization/lob.v` required an instantiation satisfying `~ [[ False ]]`, `C1`'s vacuity would have been caught immediately!
  - *Hypothesis-Mutation Falsification:* Popescu and Traytel (`Goedel_Incompleteness/Jeroslow_Original.thy` vs. `Jeroslow_Simplified.thy`) applied spec-mutation/countermodel analysis to Jeroslow's 1973 claim that $\mathbf{D2}$ is unnecessary for $\mathrm{G2}$, isolating the exact unstated congruence assumption on pseudo-terms where Jeroslow's original argument breaks for non-standard encodings. Similarly, our finite-algebra probe (`probe_p1_montague_hbl_cycles.py`) mutates each of the side conditions ($\mathrm{SC1}$–$\mathrm{SC6}$) individually and exhibits concrete finite countermodels (`144` models dropping $\Sigma_1$-completeness, `1,207` models dropping $\mathbf{D3}$).
- **`(V2)` Compiler, Lowering, and Independent Kernel Soundness Fuzzing:**
  - A mechanized proof in Lean 4, Isabelle, or Rocq trusts the host proof assistant's elaborator-to-kernel boundary and kernel implementation. Independent checker replay—`lean4checker` and `nanoda_lib` (Rust) for Lean 4 `.olean` exports, `coqchk` and MetaCoq's verified kernel for Rocq `.vo` files, and CakeML-backed Candle / OpenTheory export for HOL—catches single-implementation kernel soundness bugs via differential checking.
  - Crucially, **differential checker quorums validate implementation agreement on a shared pinned specification, not logical consistency of the specification itself**: as the consistency-cycle theorem (§3.2) proves, no $n$-checker quorum can discharge the consistency of its own shared logic without stepping up to a stronger external metatheory (such as proving $\mathrm{Con}(\mathsf{ZFC})$ assuming inaccessible cardinals, as in MetaCoq or Lean's `metamath` verifier).
- **`(V3)` Concurrency, Crash, Silicon, and Physical Fault Validation:**
  - Formal consistency proofs operate over Platonic mathematical trees; real proof-checker processes execute on physical hardware subject to DRAM bit-flips (Rowhammer flipping an environment tag bit from unproven conjecture to admitted theorem), concurrent hash-consing / environment-import races during parallel `lake`/`coqc` builds (addressed via `GenMC`/`Loom` stateless weak-memory model checking of concurrent kernel data structures), power-cut torn writes to `.olean`/`.vo` caches (requiring cryptographic digest content addressing + `CrashMonkey`/`dm-flakey` fault-injection tests), and speculative/fault-injection bypasses (`Revizor`, `TVLA`, `Alma`) when hardware enclaves or smartcards verify proof certificates under physical attack.
- **`(V4)` Telemetry/Replay Monitors and Human Comprehension Validation:**
  - *Automated Boundary Auditing:* Tools such as `#print axioms` in Lean 4 and `Print Assumptions` in Rocq act as static `ModelPlex`-style monitors ensuring no `sorryAx`, `Lean.ofReduceBool` (`native_decide` trusting the compiler!), or uninstantiated `CTQ`/`C1` axiom leaks into a closed theorem, complemented by AST statement-origin checks confirming that `T.consistent` unfolds to standard $\Sigma_1$ provability rather than a Rosser/Feferman tautology.
  - *Behavioral Mental-Model Litmus Testing (`SMoL`-style):* Because engineers routinely conflate `A -> Box A` with `⊢ A ⇒ ⊢ Box ⌜A⌝` and conflate extensional theory equality ($T_1 = T_2$) with equivalence of $\mathrm{Con}_{\tau_1}$ and $\mathrm{Con}_{\tau_2}$, human audit protocols must test reviewers on concrete Feferman ($\pi^*$) and Montague/Knower litmus cases rather than relying on surface notation (`□`, `Con`).

---

## Boundaries

- **`not examined` — Full Clean-Room Recompilation of Upstream Proof Repositories:** Under lightweight capsule execution constraints, we inspected exact pinned upstream `.lean`, `.thy`, `.v`, and `.agda` sources and executed standalone finite-algebra Python probes, rather than compiling `FormalizedFormalLogic/Foundation`, `mirror-afp-devel`, `hydra-battles`, or `coq-library-fol` from scratch locally.
- **`not examined` — HOL Light and Metamath Formalizations:** Other mechanized provability developments (such as Maggesi and Perini Brogi's modal completeness of $\mathsf{GL}$ in HOL Light, or Carneiro's `mm0` self-verifier) were not directly inspected at source level; conclusions here are restricted to the five pinned repositories.
- **`known not to apply` — Naïve Extension of Consistency-Cycle Impossibility to Arbitrary Numerations or Weak Arithmetics:** Evidence establishes (`Basis: normative + source + execution`) that "no consistent ring of $n$ systems can prove one another consistent" **does not hold** without ($\mathrm{SC2}$)–($\mathrm{SC5}$): Feferman $\pi^*$ numerations, Rosser predicates (`kreisel_remark`), and Willard's multiplication-free self-verifying systems $\mathsf{IS}(A)$ all admit consistent self- or mutual-consistency proofs ($n \ge 1$).
- **`known not to apply` — Interpreting Solovay's Logic $\mathsf{S}$ as Refuting Montague's Theorem:** Although $\mathsf{S} = \mathsf{GL} + (\Box A \to A)$ contains the reflection schema $\Box A \to A$ and is arithmetically sound in $\mathbb{N}$ (`Foundation/ProvabilityLogic/S/Arithmetic.lean:29`), $\mathsf{S}$ drops the Rule of Necessitation (`S` is closed only under Modus Ponens and Substitution, lines 32–41), which is strictly why Montague's collapse does not apply.
- **`unsupported` — Concrete $\mathrm{G2}$ and Löb's Theorem in `hydra-battles`, `coq-library-fol`, and `JasonGross/lob`:** At their pinned revisions, `rocq-community/hydra-battles` leaves $\mathbf{D2}$ and $\mathbf{D3}$ as unproved `Section` hypotheses (`goedel2.v:179-180`); `uds-psl/coq-library-fol` leaves `box`, $\mathbf{D1}$–$\mathbf{D3}$, and `modal_fixpoint` as uninstantiated `Variables` in `abstract_loeb.v:32-40`; and `JasonGross/lob` leaves its Coq quoted proof `Admitted` (`internal/LobsTheoremProof.v:775`) while its Agda `mini-lob.agda:26` postulates `Löb` as a primitive term constructor rather than deriving it from arithmetic.
- **`unknown` — Exact Minimal Subtheory Below $\mathsf{EA}$ for Multi-Theory Cycle Impossibility Under Arbitrary Polynomial Encodings:** While $\mathsf{I\Sigma_1}$ (mechanized in `Foundation`) and $\mathsf{EA} = \mathsf{I\Delta_0} + \mathsf{Exp}$ suffice for formalized $\Sigma_1$-completeness ($\mathrm{SC3}$), and Buss's $\mathsf{S}^1_2$ suffices under p-time sequence codings while Willard's multiplication-free systems break $\mathrm{G2}$, the exact boundary between $\mathsf{I\Delta_0}$ (without `Exp`) and $\mathsf{S}^1_2$ for $n$-cycle consistency transmission across heterogeneous proof encodings remains open in the examined mechanized libraries.

---

## Evidence

### 1. Primary Repository Source Citations (Pinned 40-Hex Revisions)

- **`FormalizedFormalLogic/Foundation` (`fbcfee52cb4a892087fa978366282a9ebd844f29`):**
  - `Foundation/FirstOrder/Incompleteness/ProvabilityAbstraction/Basic.lean`: `Language.ReferenceableBy` (L21), `structure Provability` with `bew_def` $\mathbf{D1}$ (L25–28), `HBL2`/`HBL3`/`HBL` (L56–66), `Diagonalization` (L178–180), `unprovable_gödel` & `first_incompleteness` (L201–227), `con_unprovable` & `con_independent` (L259–275), `löb_theorem` & `formalized_löb_theorem` (L301–311), `kreisel_remark` proving `T ⊢ 𝔅.con` for `[𝔅.Rosser]` (L356–358).
  - `Foundation/FirstOrder/Incompleteness/StandardProvability.lean`: `Diagonalization 𝗜𝚺₁` instance (L22–25), `provable_D1` (L33–35), `provable_D2` (L37–39), `provable_sigma_one_complete` (L64–69), `provable_D3` (L71–72), `T.standardProvability.HBL` instance for `[𝗣𝗔⁻ ⪯ T]` (L90–93).
  - `Foundation/FirstOrder/Incompleteness/{First,Second,Löb,Tarski,RosserProvability}.lean`: concrete theorems `incomplete_of_RE` (`First.lean:62`), `consistent_unprovable` & `craig_consistent_unprovable_of_RE` (`Second.lean:19,23`), `löb_theorem` (`Löb.lean:16`), `not_exists_tarski_predicate` & `undefinability_of_truth` (`Tarski.lean:13,24`), `incomplete_GR_of_RE` (`RosserProvability.lean:171`).
  - `Foundation/ProvabilityLogic/{GL,S,Grz}/Arithmetic.lean`: Solovay arithmetical soundness and completeness for $\mathsf{GL}$ (`GL/Arithmetic.lean:29,72`), $\mathsf{S}$ (`S/Arithmetic.lean:29,53,71`), and $\mathsf{Grz}$ (`Grz/Arithmetic.lean:28,36,40`).
- **`isabelle-prover/mirror-afp-devel` (`523cdc72b5ae4a91c9ab8e1025d4a30b40472720`):**
  - `thys/Incompleteness/Goedel_II.thy:50-69` (`theorem Goedel_II`) and `thys/Incompleteness/Loebs_Theorem.thy:24-56,92-146` (`PfP_inner_ModPon`, `Int_nec`, `theorem Loeb`).
  - `thys/Goedel_Incompleteness/Derivability_Conditions.thy:12-63,80-97,161-199` (`locale HBL1`, `CleanRepr_Proofs`, `locale HBL1_2_3`), `Abstract_Second_Goedel.thy:10-99` (`goedel_second`), `Loeb.thy:12-109` (`loeb_bprv`, `loeb_prv`).
  - `thys/Goedel_HFSet_Semantic/Instance.thy:350-462` and `thys/Goedel_HFSet_Semanticless/Instance.thy:181-269` (syntactic instantiation of `Goedel_Second_Assumptions` without `eval_fm`).
- **`rocq-community/hydra-battles` (`ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8`):**
  - `theories/goedel/goedel2.v`: `codeSysPf` & `box` (L42–77), proved `Lemma HBL1` (L88–146), unproved `Hypothesis HBL2` & `Hypothesis HBL3` (L179–180), conditional `Theorem SecondIncompletness` (L183–211), unfinished commented proof of `HBL3` (L232–262).
- **`uds-psl/coq-library-fol` (`4e5702240aa0cae803dbb2d4bc5a4b7744fef217`):**
  - `theories/Incompleteness/PA_incompleteness.v:177-186` (`incompleteness_Q` via `H10p` + Friedman translation); `external_provability.v:25,63-64,108-144` (`Variables ctq: CTQ`, `ex_prov_T`, `ex_sProv_T`); `limitative_theorems.v:47,142,216,252`; `abstract_loeb.v:32-40,61,76,117` (abstract `box` hypotheses).
- **`JasonGross/lob` (`fe3113a89c155254a0525ea741aad7469361d161`):**
  - `axiomatization/lob.v:7-34,88-92` (`IsProvable : Prop -> Prop`, `Axiom C1 : forall A : Prop, A -> [[ A ]]`, `Lemma Step10`); `internal/LobsTheoremProof.v:774-794` (`admit. Admitted.`, `Axiom qQuote`, `Axiom qbApp`); `internal/mini-lob.agda:10-70` (primitive `Löb` constructor at L26, denotational `Term⇓` at L48–52, `incompleteness` at L63).

### 2. Primary Literature Citations

- David Kaplan and Richard Montague, *"A Paradox Regained,"* *Notre Dame Journal of Formal Logic* 1(3):79–90, 1960 (`DOI: 10.1305/ndjfl/1093956549`).
- Solomon Feferman, *"Arithmetization of Metamathematics in a General Setting,"* *Fundamenta Mathematicae* 49(1):35–92, 1960 (`DOI: 10.4064/fm-49-1-35-92`).
- Richard Montague, *"Syntactical Treatments of Modality, with Corollaries on Reflexion Principles and Finite Axiomatizability,"* *Acta Philosophica Fennica* 16:153–167, 1963.
- Robert M. Solovay, *"Provability Interpretations of Modal Logic,"* *Israel Journal of Mathematics* 25(3–4):287–304, 1976 (`DOI: 10.1007/BF02757006`).
- Dan E. Willard, *"Self-Verifying Axiom Systems, the Incompleteness Theorem and Related Reflection Principles,"* *Journal of Symbolic Logic* 66(2):536–596, 2001 (`DOI: 10.2307/2695030`).
- Russell O'Connor, *"Essential Incompleteness of Arithmetic Verified by Coq,"* *TPHOLs 2005*, LNCS 3603:245–260 (`DOI: 10.1007/11541868_16`).
- Albert Visser, *"Can We Make the Second Incompleteness Theorem Coordinate Free?,"* *Journal of Logic and Computation* 21(4):543–560, 2011 (`DOI: 10.1093/logcom/exp048`).
- Lawrence C. Paulson, *"A Mechanised Proof of Gödel's Incompleteness Theorems Using Nominal Isabelle,"* *Journal of Automated Reasoning* 55(1):1–37, 2015 (`DOI: 10.1007/s10817-015-9322-8`).
- Andrei Popescu and Dmitriy Traytel, *"Distilling the Requirements of Gödel's Incompleteness Theorems with a Proof Assistant,"* *Journal of Automated Reasoning* 65(7):1027–1070, 2021 (`DOI: 10.1007/s10817-021-09599-8`).
- Dominik Kirst and Marc Hermes, *"Synthetic Undecidability and Incompleteness of First-Order Axiom Systems in Coq,"* *Journal of Automated Reasoning* 67(1):13, 2023 (`DOI: 10.1007/s10817-022-09647-x`).

### 3. Reproducible Finite-Algebra Verification Probe (`Basis: execution (toy finite-algebra model of modal/predicate axioms, not a prover kernel execution)`)

Running the following zero-dependency Python 3 script exhaustively checks all $4^4 = 256$ unary operators on the 4-element Boolean algebra $\mathcal{P}(\{0, 1\})$ and all $512$ Kripke relations on $W = \{0, 1, 2\}$ (acquired `2026-11-20` on Linux Python 3):

```python
import itertools

W_FULL, elems = 3, [0, 1, 2, 3]
neg = lambda x: W_FULL ^ x
imp = lambda x, y: neg(x) | y
sub = lambda x, y: (x & neg(y)) == 0
ops = list(itertools.product(elems, repeat=4))

s5 = [N for N in ops if N[3] == 3 and all(sub(N[x], x) and sub(N[x], N[N[x]]) and sub(neg(N[x]), N[neg(N[x])]) for x in elems)
      and all(sub(N[imp(x, y)], imp(N[x], N[y])) for x in elems for y in elems)]
montague = [N for N in ops if N[3] == 3 and all(sub(N[x], x) for x in elems) and any(g == neg(N[g]) for g in elems)]
km = [N for N in ops if all(sub(N[x], x) and N[imp(N[x], x)] == 3 for x in elems)
      and all(sub(N[x], N[y]) for x in elems for y in elems if sub(x, y)) and any(g == neg(N[g]) for g in elems)]
gl = [N for N in ops if N[3] == 3 and N[0] != 3 and all(sub(N[x], N[N[x]]) and sub(N[imp(N[x], x)], N[x]) for x in elems)
      and all(sub(N[imp(x, y)], imp(N[x], N[y])) for x in elems for y in elems)
      and all(any(psi == imp(N[psi], p) for psi in elems) for p in elems)]
c1_lob = [N for N in ops if all(sub(x, N[x]) and sub(N[imp(N[x], x)], N[x]) for x in elems)]

print("S5:", len(s5), "| Montague:", len(montague), "| KM:", len(km), "| GL:", gl, "| C1+Lob:", c1_lob)
```

Exact recorded output:
```text
S5: 2 | Montague: 0 | KM: 0 | GL: [(1, 3, 1, 3), (2, 2, 3, 3)] | C1+Lob: [(3, 3, 3, 3)]
```
On $|W| = 3$ (`19` transitive irreflexive $\mathsf{GL}$ relations across proper filters $\mathsf{EA} \subseteq T_1, T_2$), consistent 2-cycles $T_1 \vdash \neg B_2(\bot) \land T_2 \vdash \neg B_1(\bot)$ count **`0`** when all side conditions hold, **`144`** when formalized $\Sigma_1$-completeness in $\mathsf{EA}$ is omitted, and **`1,207`** when $\mathbf{D3}$ (transitivity) is omitted while retaining $\mathbf{D1}, \mathbf{D2}$, diagonalization, and $\Sigma_1$-completeness.

---

## Revalidation

To revalidate these findings against newer upstream commits or a candidate formalization of mutual-certification limits:

1. **Check Whether Concrete $\mathbf{D2}$/$\mathbf{D3}$ Hypotheses Were Discharged Upstream:**
   - In `rocq-community/hydra-battles`, diff `theories/goedel/goedel2.v` around `Hypothesis HBL2` and `Hypothesis HBL3` (lines 179–180) to see whether the commented proof attempt was completed.
   - In `uds-psl/coq-library-fol`, diff `theories/Incompleteness/abstract_loeb.v` and `external_provability.v` to check whether `box_distr` and `internal_necessitation` have been instantiated without `CTQ` or section variables.
2. **Audit Any Candidate Mechanized Self-Reference or Checker-Ring Theorem (4-Point Cheap Check):**
   - Run `#print axioms <thm>` (Lean 4) or `Print Assumptions <thm>.` (Rocq) to confirm zero custom axioms (`C1`, `CTQ`, `sorryAx`, `Lean.ofReduceBool`).
   - Inspect the type of the provability operator in `<thm>`: if its domain is `Prop` or `Type` rather than an inductive object-formula type (`Sentence L`, `fm`, `form`), reject the statement as subject to shallow-embedding vacuity.
   - Verify that `<thm>` supplies an explicit **satisfiability/model witness** instantiating all hypotheses simultaneously for at least one consistent theory $T_0$ (eliminating hidden `lob.v`-style `~~[[False]]` contradictions).
   - Unfold the consistency definition in `<thm>` to confirm it uses an explicit $\Sigma_1$ proof verifier ($\neg \exists p,\, \mathrm{Prf}_\tau(p, \ulcorner \bot \urcorner)$) together with ($\mathrm{SC1}$)–($\mathrm{SC6}$), rather than a Rosser or uncharacterized abstract predicate.
