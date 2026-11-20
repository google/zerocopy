# Leftover Typing, Capability Division and Recombination, and Single-Use Typestate in Mechanized Substructural Systems

## Summary

Mechanized substructural type systems and permission-based programming languages solve three tightly coupled design problems: (1) how typing judgments represent and partition linear contexts, (2) how capabilities over heap locations or footprints are divided, temporarily focused, and recombined without aliasing soundness holes, and (3) how single-use (linear/affine/exclusive) capabilities coexist with repeatable (duplicable/unlimited/shared) capabilities in the same typing environment. Direct inspection of five pinned upstream codebases (`gallais/typing-with-leftovers`, `ajrouvoet/ternary.agda`, `laMudri/generic-lr`, `protz/mezzo`, `tov/alms`) and eleven primary specifications establishes five durable engineering invariants:

1. **Context presentation trades algorithmic determinism against syntactic symmetry for parallel composition.** Input–output ("leftover") typing (`Γ ⊢ A ∋ t ⊠ Δ` in `typing-with-leftovers`) makes bidirectional typechecking single-pass and deterministic (`O(N · |Γ|)`), whereas naive top-down binary context splitting explodes super-exponentially on unbalanced ASTs. However, leftover threading imposes a left-to-right syntactic order on multiplicative pairs/parallel branches; proving preservation for right-branch reductions requires four auxiliary metatheoretic lemmas—monotonic consumption (`Γ ⊆ Δ`), framing (`Γ ─ Δ ≡ θ ─ ξ`), `divide`, and `swap`—whereas proof-relevant ternary splitting (`Φₗ ∙ Φᵣ ≣ Φ` in `ternary.agda`) and semiring usage vectors (`P ≤* Q +* R` in `generic-lr`) keep parallel branches symmetric at the cost of `CrossSplit`/`Uncross` lemmas or linear-map (`LinFuncRel`) substitution environments.
2. **Leftover threading is itself a separation algebra instance.** `ternary.agda`'s `Market` construction (`supply l` vs. `demand r`) realizes input–output supply/demand accounting as a commutative partial semigroup `Rel₃ Market`, unifying explicit splitting and leftover subtraction inside one algebraic framework and directly powering a linear heap with strong update (`MonadHeap.write : ∀[ One b ⇒ (V a) ─✴ M (One a ✴ V b) ]`).
3. **Capability division and recombination rules converge on disjointness/exclusivity and obligation conservation, but diverge sharply on static vs. dynamic enforcement and zero-size/empty pieces.** Alias Types and $L^3$ decouple duplicable singleton pointers (`ptr(ρ)` / `Ptr ρ`) from linear cell capabilities (`{ρ ↦ τ}` / `Cap ρ τ`) and support permanent freezing (`freeze`) with zero runtime overhead. Fähndrich–DeLine Adoption & Focus keeps zero runtime overhead by restricting focusing to a lexical scope guarded by a linear implication (`τ₁ ⊸ τ₂`), preventing permanent un-adoption. Mezzo (`protz/mezzo`) separates *dynamic adoption/abandon* (`give`/`take`/`owns`, backed by a hidden per-block `+1`-word `adopter` field checked at runtime) from *static Boyland nesting* (`corelib/nest.mzi`, where `punched a p` is deliberately neither duplicable nor exclusive to block double focusing) and first-class one-shot magic wands (`stdlib/osf.mzi`, `stdlib/focused.mzi`). Fractional permissions (Boyland 2003; `alms` `ex65-popl-Fractional.alms`) strictly require positive fractions (`z > 0`) for reads and `z = 1` for writes; admitting `z = 0` as a read token breaks write-exclusivity soundness.
4. **Coexisting single-use and repeatable capabilities force explicit mode/qualifier stratification across every context boundary.** Combining repeatable and single-use resources in one environment requires: (a) a mode/qualifier lattice (`Qu ⊑ Qa` in `alms`; 4-point diamond `ModeBottom < {ModeDuplicable, ModeExclusive} < ModeAffine` in `mezzo`), (b) closure/subtyping stripping (`keep_only_duplicable` in `mezzo/typing/Permissions.ml`, free-variable qualifier joins `arrowQualifier` in `alms/src/Statics/Expr.hs`), (c) careful handling of flexible type-variable instantiation during subtraction (`was_duplicable` vs. `now_duplicable` in `mezzo/typing/Permissions.ml:752-768`), and (d) explicit value restrictions on additive constructs (`syntacticValue` in `alms/src/Statics/Expr.hs:217-226`) and dynamic single-use wrappers (`affunc` in `alms/lib/libbasis.alms:65-70`) when crossing affine-to-unrestricted boundaries.
5. **Runtime metadata, proof-checker effort, and human auditability vary by orders of magnitude across designs.** Purely static capability systems (`Alias Types`, $L^3$, `Adoption & Focus`, `Vault`) incur `0` bytes of per-object runtime metadata; Mezzo's dynamic adoption adds `1` word (`8 B` on 64-bit) to every compiled algebraic data block (`UntypedMezzo2UntypedOCaml.ml:37-68, 156`); Alms's dynamic escape contract (`affunc`) allocates a `1`-word mutable option ref cell per coerced affine closure. Mechanized metatheory spans `3,577` Agda lines (`typing-with-leftovers`), `4,393` Agda lines (`generic-lr`), `7,084` Agda lines (`ternary.agda`), and `~14,000` Coq lines (Mezzo TOPLAS 2016).

## Applicability

This report synthesizes and compares five pinned software artifacts and eleven peer-reviewed programming-language specifications:

- **Mechanized linear/substructural metatheory (Agda):** `gallais/typing-with-leftovers` (`b0289b34fc47afc67ef8d2881c63a7ef0748a989`, `src/linear/`, `41` files, `3,577` LoC), `ajrouvoet/ternary.agda` (`4097451af88fb512f89fcb06f643e554fcd0a6aa`, `src/`, `78` files, `7,084` LoC), and `laMudri/generic-lr` (`3ee8ce26f6c6ec5860ed323d4cf3c9f6d0f5ef7e`, `src/Generic/Linear/`, `32` files, `4,393` LoC). These findings apply to intrinsically typed syntax, proof-relevant context algebra, and mechanized preservation/substitution/typechecking proofs in intensional Martin-Löf type theory (Agda `--safe --without-K`; note `generic-lr` additionally uses `--sized-types` and `--prop` in `Syntax/Term.agda` and `Semantics/Syntactic.agda`).
- **Permission-based and affine language implementations:** `protz/mezzo` (`4e9d917558bd96067437116341b7a6ea02ab9c39`, OCaml type checker `typing/*.ml*`, `55` files, `15,563` LoC; plus `corelib/`, `stdlib/`, `interpreter/`, `compiler/`) and `tov/alms` (`b35b804abaf7579aae8a57785544562647919c36`, Haskell static semantics `src/Statics/*.hs`, `13` files, `5,251` LoC; plus `src/AST/`, `lib/`, `examples/`).
- **Normative specifications and metatheory papers:** Cervesato–Hodas–Pfenning (TCS 2000), Smith–Walker–Morrisett (ESOP 2000, Alias Types), DeLine–Fähndrich (PLDI 2001, Vault), Fähndrich–DeLine (PLDI 2002, Adoption & Focus), Boyland (SAS 2003, Fractional Permissions), Morrisett–Ahmed–Fluet (TLCA 2005, $L^3$), Tov–Pucella (POPL 2011, Alms), Balabonski–Pottier–Protzenko (ACM TOPLAS 2016, Mezzo), Allais (TYPES 2017 / LIPIcs 2019), Rouvoet–Bach Poulsen–Krebbers–Visser (CPP 2020), and Wood–Atkey (ESOP 2022).

The comparisons characterize sequential and structured fork-join/parallel capability calculi, single-threaded and lock-synchronized heap stores, and compile-time typecheckers/proof assistants. Extensions to weak-memory hardware models (TSO/ARMv8/C11 relaxed atomics) or non-blocking lock-free reclamation protocols are outside the direct scope of these calculi and are delineated under **Boundaries**.

## Findings

### 1. Input–Output, Explicit-Splitting, and Usage-Annotated Presentations of Linear Typing

Basis: source + normative (`gallais/typing-with-leftovers`, `ajrouvoet/ternary.agda`, `laMudri/generic-lr`, Cervesato–Hodas–Pfenning 2000, Allais 2017/2019, Rouvoet et al. 2020, Wood–Atkey 2022)

#### 1.1 Judgment Forms and Core Context Encodings

Each mechanized presentation encodes linear resource accounting in a distinct way that directly determines which structural lemmas must be proved before soundness (progress and preservation) can proceed:

| Dimension | Input–Output / Leftovers (`typing-with-leftovers`) | Explicit Proof-Relevant Splitting (`ternary.agda`) | Usage-Annotated Semiring Vectors (`generic-lr`) | Bottom-Up Occurrence Counting (`alms`, for contrast) |
| :--- | :--- | :--- | :--- | :--- |
| **Core Judgment Form** | Bidirectional: `Γ ⊢ A ∋ t ⊠ Δ` (Check) and `Γ ⊢ t ∈ A ⊠ Δ` (Infer) (`Typing.agda:22, 72`) | Resource-indexed predicates `P : Pred A p` combined via `_∙_≣_ : A → A → Pred A a`, `P ✴ Q`, `P ─✴ Q` (`Core.agda:41-123`) | Generic indexed terms `[ d , sz ] Γ ⊢ A` (`Syntax/Term.agda:27`) where `Γ = ctx {s} P γ` (`Syntax.lagda.tex:26-35`) | Type inference `infer φ δ γ e mσ` (`Statics/Expr.hs:41`) + pattern multiplicity check `τ ⊏: occOf n + as_occs` (`Statics/Patt.hs:117`) |
| **Context Representation** | Fixed-length `γ : Vec Type n` paired with `Γ, Δ : Usages γ`, each slot `[ a ]` (available) or `] a [` (consumed) (`Usage.agda:23-30`) | Abstract carrier `A` (`List T`, `Bag`, `Map`, `Market`, etc.) with ternary split relation `Φ₁ ∙ Φ₂ ≣ Φ` | Binary-tree shape `s : LTree`, `use-ctx : Vector Ann s` over arbitrary `PoSemiring`, `ty-ctx : Vector Ty s` (`Algebra.agda:6`) | Standard map `Γ tv` (`Statics/Env.hs`); AST nodes cache free-variable multiplicity maps `efv_ : FvMap` (`AST/Expr.hs:130, 153-235`) |
| **Variable Rule** | `Γ ⊢ k ∈[ σ ]⊠ Δ`: flips index `k` from `[ σ ]` to `] σ [`, preserving all other slots (`Usage.agda:45-48`) | Singleton ownership `Own (x ∷ [])` / `One a` (`Core.agda:15`, `Monad/State/Linear.agda:40`) | `lvar idx tyq basis` with `basis : P ≤* ⟨ idx ∣` (`1#` at `idx`, `0#` elsewhere; `Variable.agda:27-35`) | Lookup `γ !.! n`; occurrence count `M.singleton v 1` checked at binder site (`AST/Expr.hs:157`, `Patt.hs:114-118`) |
| **Multiplicative Pair / App** | Threads `Γ → Δ → θ`: `Γ ⊢ σ ∋ a ⊠ Δ → Δ ⊢ τ ∋ b ⊠ θ` (`Typing.agda:40-44, 80-84`) | Explicit split witness: `px ∙⟨ sep ⟩ qx` where `sep : Φₗ ∙ Φᵣ ≣ Φ` (`Core.agda:69-77`) | Separating premise `p `✴ q` interpreted as `R ≤* P +* Q` on same shape `s` (`Syntax/Interpretation.lagda.tex:31, 65-66, 85`) | `efv_ = fv e1 |*| fv e2` sums counts (`AST/Expr.hs:189, 199`); `≥ 2` forces `τ ⊏: Qu` |
| **Additive Branching (`&`, `case`)** | Both branches start from same `Γ` (or `Δ`) and MUST produce identical output `Δ` (or `θ`) (`Typing.agda:47-51, 98-105`) | Pointwise intersection `P ∩ Q` on identical `Φ` (`Monad/Weakening.agda:47`) | Sharing premise `p `∧ q` interpreted as `⟦ p ⟧p X ∩ ⟦ q ⟧p X` on same `(R, γ)` (`Syntax/Interpretation.lagda.tex:83`) | `fv (ADDITIVE cas)` takes pointwise `max` across branches (`AST/Expr.hs:172, 214`) |
| **Linear Abstraction (`λ`)** | `[ σ ] ∷ Γ ⊢ τ ∋ b ⊠ ] σ [ ∷ Δ` (`Typing.agda:24-28`); enforces exact consumption of bound `σ` | Magic wand `P ─✴ Q` (`Φᵢ ∙ Φₚ ≣ Φ → P Φₚ → Q Φ`) (`Core.agda:92-104`) | Scope premise `⟨ [ 1# · σ ]ᶜ `⊢ τ ⟩` (`Syntax.lagda.tex:97`, `Example/LR.agda:87`) | `arrowQualifier γ e0 = bigJoin [qualifier (γ =..= n) | n ← keys (fv e0)]` (`Statics/Expr.hs:140, 379-382`) |
| **Mechanization Footprint** | `41` files, `3,577` LoC (`src/linear/**/*.agda`) | `78` files, `7,084` LoC (`src/**/*.agda`) | `32` files, `4,393` LoC (`src/Generic/Linear/**/*.agda*`) | `13` files, `5,251` LoC (`src/Statics/*.hs`, unmechanized checker) |

#### 1.2 Structural Lemmas Required by Each Presentation

Basis: source (`typing-with-leftovers`, `ternary.agda`, `generic-lr`)

1. **`gallais/typing-with-leftovers` (Input–Output Leftovers):**
   - **Consumption / Monotonicity (`Usage/Consumption.agda:15-53`, `Typing/Consumption.agda:17-37`):** Every derivation `Γ ⊢ t ⊠ Δ` satisfies `Γ ⊆ Δ` (defined as `Γ ─ Δ ≡ Γ ─ Δ`, where `Γ ─ Δ ≡ θ ─ ξ` asserts that `Γ → Δ` and `θ → ξ` consume the exact same set of positions). `_⊆_` is proved reflexive (`refl`), transitive (`trans`), antisymmetric (`antisym`), and proof-irrelevant (`irrelevance`).
   - **Framing of Unused Resources (`Usage/Consumption.agda:104`, `Typing/Consumption.agda:40-65`):** `Framing 𝓣 = Γ ─ Δ ≡ θ ─ ξ → 𝓣 Γ t A Δ → 𝓣 θ t A ξ`. Crucially, framing across sequential threading (`app`, `prd⊗`, `let`, `case`) depends on `divide` (`Usage/Consumption.agda:79-85`): given `Γ ─ Δ ≡ θ ─ ξ`, `Γ ⊆ χ`, and `χ ⊆ Δ`, there exists an intermediate context `Φ` such that `Γ ─ χ ≡ θ ─ Φ` and `χ ─ Δ ≡ Φ ─ ξ`.
   - **Order-Swapping (`Usage/Consumption.agda:62-67`):** `swap : Γ ⊆ Δ → Δ ⊆ θ → ∃ λ Δ′ → Γ ─ Δ ≡ Δ′ ─ θ × Δ ─ θ ≡ Γ ─ Δ′`. Combined with `framingCheck`/`framingInfer`, `swap` proves that left-to-right threading is semantically commutative for disjoint subterms.
   - **Weakening and Thinning (`Typing/Substitution.agda:23-36`, `Typing/Thinning.agda:25-55`):** Weakening inserts unused slots (either `[ a ]` or `] a [`) via `U.Mergey` (`_⋈_`) that emerge unchanged in the output context. Thinning is the converse: if every inserted slot passes through unchanged from `Γ ⋈ 𝓜` to `Δ ⋈ 𝓜`, the term cannot mention those indices and thins to `t′` in `Γ ⊢ t′ ⊠ Δ`.
   - **Functional / Deterministic Outputs (`Typing/Functional.agda:24-110`):** `functionalInfer`, `functionalInferPost`, `functionalInferPre`, and `functionalCheckPre` prove that given `(Γ, t)` (for `Infer`) or `(Δ, t)` (pre-context uniqueness), the leftover context is propositionally unique. Notice how **substitution (`Typing/Substitution.agda:82-84, 127, 137`) directly depends on `functionalEnvPre functionalInferPre`** to prove that the two branches of `case` and `prd&` produce propositionally equal leftover environments!
   - **Permutation / Mix (`Typing/Mix.agda:22-75`):** `mixCheck`/`mixInfer` permutes context entries via `splitUsages` and `unsplitUsages` over list-interleaving witnesses `[ p ] Γ₁ ++ Γ₂ ≅ Γ`.
   - **Soundness & Completeness wrt ILL (`Soundness.agda:21-56`, `Completeness.agda`):** Establishes equivalence between closed leftover derivations `[[ γ ]] ⊢ σ ∋ t ⊠ ]] γ [[` and standard Intuitionistic Linear Logic `γ ⊢ σ`.
   - **Handling Additive Top (`⊤`) (Cervesato–Hodas–Pfenning 2000):** `typing-with-leftovers` omits additive `⊤` (`Type.agda` has `𝟙, 𝟘, ⊗, ─o, &, ⊕`). In Cervesato–Hodas–Pfenning's RM0–RM4 systems (TCS 2000), introducing `⊤` breaks deterministic leftovers because `⊤` can consume *any* subset of the input context; preserving efficiency requires tagging leftover contexts with a Boolean strict/lazy flag (`v ∈ {0, 1}`) recording whether an arbitrary slack may still be absorbed.

2. **`ajrouvoet/ternary.agda` (Proof-Relevant Separation Structures):**
   - **Algebraic Axioms Replacing Ad-Hoc Context Lemmas (`Structures/PartialSemigroup.agda:13-65`, `Structures/PartialMonoid.agda:18-90`, `Structures/Commutative.agda`):** Instead of proving syntax-specific framing/permutation lemmas per language, the library packages `IsPartialSemigroup` (`∙-assocₗ`, `∙-assocᵣ`, congruence wrt `_≈_`), `IsPartialMonoid` (`∙-idˡ`, `∙-idʳ`, uniqueness of `ε`), and `IsCommutative` (`∙-comm`), yielding generic combinators `✴-assocₗ`, `✴-assocᵣ`, `✴-idˡ`, `✴-idʳ`, and magic-wand composition `com`.
   - **Cross-Splitting (`Structures/Crosssplit.agda:19-51`):** `CrossSplit` takes two splits `a ∙₁ b ≣ z` and `c ∙₂ d ≣ z` of the same context `z` and produces four disjoint fragments `(ac, ad, bc, bd)` refining both splits; `Uncross` is its dual. Cross-splitting (and `resplit`/`repartition` in `List/Disjoint.agda`) is the exact workhorse needed for **substitution** (distributing a split substitution environment across a split term) and for **heap strong updates** (`Monad/State/Linear.agda:74, 85, 89`).
   - **Framing via Strong Indexed Monads (`Monad.agda:44-89`, `Monad/Weakening.agda:19-52`):** Framing of unused resources is captured once and for all as monadic strength `str : ∀[ Q ⇒ M P ─✴ M (Q ✴ P) ]` (`qx &⟨ σ ⟩ mp`), while affine weakening is the explicit monad `P ⇑ = P ✴ U` (`Weakening.agda:22`) with `th : Φ₁ ∙ Φ₂ ≣ Φ → (P ⇑) Φ₁ → (P ⇑) Φ`.
   - **Leftovers Inside Separation Algebra (`Construct/Market.agda:22-78`, `Monad/State/Linear.agda:31-93`):** `Market` tags resources as `supply l` (available heap) or `demand r` (unfulfilled references) with `Split (supply l₁) (demand r) (supply l₂)` when `l₂ ∙ r ≣ l₁`. Thus input–output subtraction is recovered as a `Rel₃` instance!
   - **Disjoint vs. Overlapping Contexts (`Construct/List/Disjoint.agda` vs. `Construct/List/Overlapping.agda`):** Switching from purely linear splitting (`empty-rel`, no element duplicated) to unrestricted/overlapping splitting (`Agree`, constructor `overlaps σ`) changes only the element-level `Rel₃`, reusing the entire monad and combinator stack.

3. **`laMudri/generic-lr` (Usage-Annotated Contexts Over Partially Ordered Semirings):**
   - **Single Generic Traversal for Both Renaming and Substitution (`Semantics/Syntactic.agda:51-109`):** Because contexts keep a fixed variable shape `s : LTree` and separate types `γ : Vector Ty s` from usage annotations `P : Vector Ann s`, **every** system `d : System fl` over **every** `PoSemiring` inherits:
     - **Sub-usage / Resource Monotonicity (`IsPresheaf`):** `Q ≤* P → ∀[ 𝓥 (ctx P γ) ⇒ 𝓥 (ctx Q γ) ]` (`Environment.agda:34-37`, derived from `ren^⊢` via `ren⇒psh`). Note: framing an unused variable corresponds to extending the `LTree` with grade `0#` (or thinning via a renaming matrix with a zero row), never altering the usage of active variables.
     - **Environments as Linear Functional Relations (`Environment.agda:42-52`):** `[ 𝓥 ] Γ ⇒ᵉ Δ` carries a matrix/linear functional relation `Ψ : LinFuncRel t s 0ℓ` with `sums : Ψ .rel Q P` (morally `P ≤* Q · Ψ`) and `lookup : Ψ .rel Q′ P′ → ∀[ ctx Q′ δ ∋_ ⇒ 𝓥 (ctx P′ γ) ]`.
     - **Renaming (`ren : Γ ⇒ʳ Δ → [ d , ∞ ] Δ ⊢ A → [ d , ∞ ] Γ ⊢ A`)** and **Substitution (`sub : [ d ] Γ ⇒ˢ Δ → [ d , ∞ ] Δ ⊢ A → [ d , ∞ ] Γ ⊢ A`)**: both are 3-line instantiations (`Ren-Kit`, `Sub-Kit`) of `kit→sem : Kit d 𝓥 → Semantics d 𝓥 [ d , ∞ ]_⊢_` (`Semantics/Syntactic.agda:73-109`)!
   - **Nondeterministic Usage Checking (`Example/UsageCheck.agda:73-90`):** Reconstructing usage derivations from unannotated terms requires `NonDetInverses` (`0#⁻¹`, `+⁻¹`, `1#⁻¹`, `*⁻¹`, `rep`), exposing the exact algorithmic cost of top-down splitting when `+⁻¹` enumerates additive decompositions.

#### 1.3 Typing a Parallel Composition (`e₁ ∥ e₂`) Across the Three Presentations

Basis: source + derived + execution (toy model of algorithmic splitting cost)

Consider typing a fork-join parallel composition `e₁ ∥ e₂` whose two branches must receive disjoint portions of one linear context `Γ` and may step independently (`e₁ ⟶ e₁′` or `e₂ ⟶ e₂′`):

- **Input–Output Leftovers (`typing-with-leftovers`):** The typing rule must pick a threading order, e.g. `Γ ⊢ e₁ ⊠ Δ` and `Δ ⊢ e₂ ⊠ θ` (mirroring `` `prd⊗ `` at `Typing.agda:40-44`). Typechecking is **deterministic and linear** in term size (no split guessing). Preservation when `e₁ ⟶ e₁′` is direct (if reduction preserves leftovers, `Γ ⊢ e₁′ ⊠ Δ`), **provided** operational steps never leak or resurrect capabilities. Preservation when the *right* branch steps (`e₂ ⟶ e₂′`) or when proving commutativity `e₁ ∥ e₂ ≡ e₂ ∥ e₁` requires applying `consumption` (`Γ ⊆ Δ`, `Δ ⊆ θ`), `swap` (`Usage/Consumption.agda:62-67`) to obtain `Δ′` with `Γ ─ Δ ≡ Δ′ ─ θ` and `Δ ─ θ ≡ Γ ─ Δ′`, and `framing` (`Typing/Consumption.agda:40-65`) to retype `e₂` from `Γ` to `Δ′` and `e₁` from `Δ′` to `θ` (and vice versa if `e₂` allocates fresh capabilities visible in `Δ′`, which then requires weakening `e₁` via `U.Mergey`!).
- **Explicit Ternary Splitting (`ternary.agda`):** The typing rule is symmetric: `Φₗ ∙ Φᵣ ≣ Φ`, `Φₗ ⊢ e₁`, `Φᵣ ⊢ e₂` (i.e., `P ✴ Q` at `Core.agda:69-87`). Stepping either `e₁` or `e₂` preserves the split witness `σ : Φₗ ∙ Φᵣ ≣ Φ` unchanged (zero reframing), and commutativity is a single application of `∙-comm`. Dynamic capability allocation inside a branch requires extending the heap carrier (as in `Market` / `MonadHeap`) and reassociating with `∙-assocₗ`/`∙-assocᵣ`. The penalty moves to **typechecking** (guessing `Φₗ, Φᵣ`) and **substitution** (which requires `CrossSplit` / `resplit`).
- **Usage-Annotated Semiring Vectors (`generic-lr`):** The typing rule uses the separating premise `⟨ []ᶜ `⊢ A ⟩ `✴ ⟨ []ᶜ `⊢ B ⟩`, requiring `P ≤* Q +* R` over the **same** variable shape `s : LTree` (`Syntax/Interpretation.lagda.tex:65-66`). Both branches remain completely symmetric (commutativity follows immediately from `+*-comm` at `Algebra.agda:77-78`), and variables unused in one branch remain in scope with usage `0#` (eliminating De Bruijn re-indexing across splits!). Disjointness of linear capabilities holds iff the semiring satisfies `1# + 1# ≰ 1#` (e.g., the `{0, 1, ω}` semiring where `1 + 1 = ω` and `ω ≰ 1`, `Example/ZeroOneMany.agda`).

**Algorithmic Splitting Micro-Probe.** Basis: execution (toy model of leftover threading, naive binary split search, and bottom-up occurrence counting in Python, not the upstream Agda/Haskell binaries themselves). On an `N`-variable linear tensor chain (`N` slots all initially available), measuring recursive checker steps reveals a sharp asymmetry:

| Term Shape | `N` | Leftover Threading (`typing-with-leftovers` model) | Bottom-Up `fv` (`alms` model) | Naive Top-Down Binary Split Search (`step_limit = 200,000`) |
| :--- | :-: | :-: | :-: | :-: |
| Right-nested `(x₀ ⊗ (x₁ ⊗ ...))` | 4 / 8 / 12 / 16 | `7` / `15` / `23` / `31` | `7` / `15` / `23` / `31` | `10` / `22` / `34` / `46` (mask `0b0...1` hits on 2nd try) |
| Left-nested `(((x₀ ⊗ x₁) ⊗ ...) ⊗ x_{N-1})` | 4 | `7` | `7` | `84` |
| Left-nested | 6 | `11` | `11` | `8,444` |
| Left-nested | 8 / 10 / 12 | `15` / `19` / `23` | `15` / `19` / `23` | `> 200,000` (aborted) |

Naive top-down splitting exhibits an order-dependent benchmark hazard: right-skewed inputs can mask super-exponential blowup that hits immediately (`N = 8`) on left-skewed inputs, whereas leftover threading and bottom-up occurrence counting both stay strictly at `2N - 1` steps regardless of AST shape.

---

### 2. Capability Division, Focusing, and Recombination Rules Across Permission Calculi

Basis: normative + source (`Smith–Walker–Morrisett ESOP 2000`, `DeLine–Fähndrich PLDI 2001`, `Fähndrich–DeLine PLDI 2002`, `Boyland SAS 2003`, `Morrisett–Ahmed–Fluet TLCA 2005`, `Balabonski–Pottier–Protzenko TOPLAS 2016`, `protz/mezzo`, `tov/alms`)

#### 2.1 Comparative Rule & Side-Condition Matrix

| System | Division / Borrowing / Focusing Operation | Recombination / Restore Operation | Side Conditions on Footprints / Locations | Treatment of Empty / Zero-Size Pieces | Where Pending Obligation Travels | Soundness-Critical Conditions Actually Used in Proof |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Alias Types** (Smith–Walker–Morrisett, ESOP 2000) | Store constraint composition `C₁ ⊗ C₂` (`{ρ ↦ τ}` linear, `{ρ ↦ ω τ}` nonlinear); `new` introduces fresh `ρ` with `{ρ ↦ τ}` | `join` / coercion `C₁ ≤ C₂`; nonlinear promotion `{ρ ↦ τ} ≤ {ρ ↦ ω τ}` (irreversible!) | Linear store map requires **distinct location names** `ρ₁ ≠ ρ₂` in `C₁ ⊗ C₂`; no sub-object byte-offset splitting in base ESOP 2000 calculus (fields are tuple offsets under one `ρ`) | Empty constraint `∅` is identity for `⊗`; zero-field tuple `⟨⟩` at `ρ` still occupies a distinct heap location `ρ` until freed | Carried implicitly in the linear store-type context `C` threaded through continuation-passing basic blocks | **Linear domain disjointness** (`dom(C₁) ∩ dom(C₂) = ∅` for linear cells) and **monotonicity of nonlinear store** (`{ρ ↦ ω τ}` never changes type, banning strong update once shared) |
| **$L^3$: Linear Language with Locations** (Morrisett–Ahmed–Fluet, TLCA 2005) | Decouples duplicable `Ptr ρ` from linear `Cap ρ τ`; `swap` exchanges `(Ptr ρ, Cap ρ τ₁, v : τ₂)` for `(Cap ρ τ₂, v_old : τ₁)`. Extended $L^3$: `freeze` moves linear cell into frozen store `φ`; `thaw` temporarily extracts linear `Cap` | `free` consumes `Cap ρ τ` (leaving dead `Ptr ρ` unusable without `Cap`); `refreeze` returns `Cap` to `φ` | Every live mutable location `ρ` has **at most one linear `Cap ρ τ`** in the entire typing derivation; `Ptr ρ` may alias arbitrarily because dereference requires presenting `Cap ρ τ` | Empty capability `1` (unit); empty/unit payload `Cap ρ 1` still uniquely owns location `ρ` and prevents dangling dereference/double free | `Cap ρ τ` is a **first-class linear value** returned in tuples; under `thaw`/`refreeze`, restoration obligation is tracked via linear capability value (or lexical discipline) | **1-to-1 bijection** between live linear heap cells and linear `Cap ρ τ` tokens in the runtime configuration (store typing invariant); **no duplication of `Cap`**; `freeze` forbids later strong update without exclusive `thaw` |
| **Adoption & Focus** (Fähndrich–DeLine, PLDI 2002; Vault, PLDI 2001) | `adopt e₁ by e₂`: consumes linear adoptee `e₁ : τ₁` and binds its lifetime to nonlinear adopter `e₂ : τ₂`; `focus x = e₁ in e₂`: temporarily extracts linear view of adopted `e₁` inside lexical scope `e₂` | End of `focus` lexical scope automatically applies the linear implication guard `τ₁ ⊸ τ₂` to restore adopter permission | Adopter `e₂` must hold an **adoption relation** covering `e₁`; **no double focus** (focusing consumes the adopter's guard/permission, replacing it with `τ₁ ⊸ τ₂`, so a second nested focus on an alias of `e₁` cannot obtain the adopter capability!) | Empty focus body or zero-field linear key (`tracked(K)` in Vault) still consumes/restores the key state in the held-key set | **Lexically scoped** in the linear context as a **linear implication guard** `τ₁ ⊸ τ₂` (in `tov/alms/examples/ex27-focusing-and-adoption.alms:46-48`, encoded as an explicit affine closure `(('t1,'a) region1 -A> ('t,'a) region)`) | **Linearity of the guard `τ₁ ⊸ τ₂`** (prevents dropping obligation or restoring twice) and **temporary loss of adopter permission during focus** (prevents aliasing via a second focus on the same adopter) |
| **Mezzo Dynamic Adoption & Abandon** (`protz/mezzo` `TypeChecker.ml:1030-1128`, `Interpreter.ml:706-733`, TOPLAS 2016) | `give x to y` (`EGive`): statically consumes `x @ clause` (requiring `FactInference.is_exclusive env clause`, `TypeChecker.ml:1088`), sets `x.adopter := Some y`; `take x from y` (`ETake`): checks `x @ dynamic` and `y` has `adopts clause`, **dynamically tests** `x.adopter == Some y` and resets `x.adopter := None`, yielding `x @ clause` | Permanent abandonment (`take`) needs **no** subsequent restoration obligation! Re-adoption is an explicit `give` | `clause` MUST be `exclusive` (`TypeChecker.ml:1088-1089`); `x` must be `dynamic` (`TypeChecker.ml:1102`); `y` must carry an `adopts clause` concrete permission (`TypeChecker.ml:1105`). `y owns x` (`EOwns`) tests `x.adopter == Some y` without consuming (`TypeChecker.ml:1113-1128`) | `ty_bottom` is the empty `adopts` clause (`TypeChecker.ml:1035`, `Permissions.ml:542-543`). Zero-field blocks still allocate a `block` with `mutable adopter: block option` (`Interpreter.ml:83-93, 313`) | No static return obligation after `take`; ownership state lives in the **runtime `adopter` pointer** on the adoptee heap block (`Interpreter.ml:90`) | **Heap forest / unique-owner invariant**: every heap block has at most one owner—either a unique static `exclusive` permission in some thread's context OR its `adopter` field points to a valid adopter (`Interpreter.ml:709` `assert (b1.adopter = None)`). Dynamic check in `ETake` prevents double-take aliasing! |
| **Mezzo Static Nesting & One-Shot Wands** (`corelib/nest.mzi:8-42`, `stdlib/osf.mzi:3-34`, `stdlib/focused.mzi:1-2`, `corelib/array.mzi:52-53`) | `nest`: consumes `p`, emits duplicable witness `nests x p`; `focus`: consumes `x @ a * nests x p` (where `exclusive a`), emits `x @ punched a p * p`. Array `borrow (r, i)` emits `focused a (r @ array m a) = (x: a, osf::wand (x @ a) (r @ array m a))` | `defocus`: consumes `x @ punched a p * p`, restores `x @ a`; `wand` invoked once consumes `(pre * ammo)` and returns `post` | `exclusive a` required on `focus`/`defocus` (`nest.mzi:29, 33`); `punched a p` is explicitly **neither duplicable nor exclusive** (`nest.mzi:18-23`) specifically to forbid double focusing! | `empty` permission (`TyEmpty`, filtered out by `Permissions.ml:401`) is identity for `*` | In `nest.mzi`, pending obligation rides in the linear permission `x @ punched a p`; in `focused.mzi` / `array.mzi`, it travels as a **first-class existentially packaged one-shot closure** (`osf::wand`, `osf.mzi:31-34`) | **Non-exclusivity + non-duplicability of `punched a p`** blocks re-entering `focus` before `defocus`; **affinity of existential `ammo`** in `wand` ensures the restoration closure can be invoked at most once |
| **Fractional Permissions** (Boyland, SAS 2003; `alms` `ex65-popl-Fractional.alms:3-19`) | `split`: `z · ρ ↦ τ ⊢ z₁ · ρ ↦ τ * z₂ · ρ ↦ τ` where `z = z₁ + z₂` and **`z₁ > 0, z₂ > 0`** (in `alms` `ex65`: `('b, 'c) cap → ('b, 'c/2) cap × ('b, 'c/2) cap`) | `join`: `z₁ · ρ ↦ τ * z₂ · ρ ↦ τ ⊢ (z₁ + z₂) · ρ ↦ τ` on **same location** `ρ` | **Same location `ρ`**, **positive fractions `z₁, z₂ ∈ (0, 1]`**, **sum conservation `z₁ + z₂ = z ≤ 1`**. Write requires `z = 1`; read requires `z > 0` | **Zero fraction (`z = 0`) MUST NOT grant read access.** If `0` granted read, `1 = 1 + 0` would permit concurrent read+write interference! | Carried as affine/linear fractional tokens in contexts or parallel branches; returning from fork-join recombines `1/2 + 1/2 = 1` | **Total permission conservation invariant** (`∑_{threads} π(ρ) ≤ 1` for every location `ρ`): since write needs `π = 1` and every concurrent read needs `π > 0`, `1 + π > 1` is impossible, proving interference freedom and determinism! |

#### 2.2 Disagreements and Structural Gaps Between Spatial-Slice Splitting and Location-Permission Calculi

Basis: derived from primary sources above

A critical distinction separates **contiguous byte-range / slice splitting** (splitting `[base, base + len)` into `[base, mid)` and `[mid, base + len)`, then rejoining adjacent slices) from the classic location-permission calculi tabulated above:

1. **Adjacency vs. Location Identity:** None of Alias Types (2000), $L^3$ (2005), Adoption & Focus (2002), or Mezzo (2016) has a built-in primitive for byte-range adjacency recombination (`[a, b) + [b, c) = [a, c)`). Instead, they track **atomic location identities `ρ`** (whole heap cells or records). Mezzo's `corelib/array.mzi:52-53` borrows a *single* element via `focused a (r @ array m a)` (temporarily locking out the entire array until the wand restores `r @ array m a`), rather than splitting an array into two disjoint mutable sub-slices. Fractional permissions split *access rights* over the *same* location (`z₁ + z₂ = z`), which commutes and recombines without any adjacency side condition—only location identity `ρ₁ = ρ₂` and positivity `z > 0` matter.
2. **Non-Emptiness Side Conditions:**
   - For **spatial slice splits**, non-emptiness (`mid > base` and `end > mid`) is **not** strictly required for spatial disjointness (`[a, a) ∩ [a, b) = ∅`), **provided** zero-size capabilities cannot authorize any byte read/write or strong update and cannot be mistaken for a distinct allocated identity. However, allowing empty slices complicates uniqueness/identity reasoning (infinitely many empty `[a, a)` tokens can be split off an arbitrary range) and makes region-level reclamation subtle unless empty slices carry zero deallocation authority.
   - For **fractional permissions**, positivity (`z > 0`) IS strictly required for soundness whenever `z` authorizes a read: `1 = 1 + 0` would otherwise allow splitting off a `0`-fraction read token while retaining a `1`-fraction write capability!
   - For **Mezzo exclusive permissions**, `Permissions.ml:88-94, 530-533` enforces that `x @ excl₁ * x @ excl₂` is **inconsistent** (`⊥`). That invariant would be violated if a zero-size "exclusive" piece could be split off a parent capability at the *same* address `x` while keeping `x` exclusive!
3. **Where Pending Obligations Travel:**
   - **Lexical obligation** (Fähndrich–DeLine Focus): cheapest (`0` runtime cost, simple scoping), cannot cross function return boundaries.
   - **First-class affine closure / magic wand** (`stdlib/osf.mzi`, `alms` `ex27`): crosses function boundaries without runtime overhead beyond closure representation, but requires affine/one-shot function types (`-A>` or `osf`).
   - **First-class linear token (`punched a p`, `l @ locked`, `Cap ρ τ`)**: zero runtime cost (erased), arbitrarily re-orderable across statements/functions, requires threading the token statically.
   - **Runtime ownership pointer (`adopter` field in Mezzo)**: eliminates static focus scoping entirely and supports cyclic graphs/arbitrary abandonment order, at the permanent cost of `+1` word per heap block and fallible runtime checks on `take`.

---

### 3. Single-Use vs. Repeatable Capabilities in One Context

Basis: source + normative (`DeLine–Fähndrich PLDI 2001`, `protz/mezzo`, `Balabonski–Pottier–Protzenko TOPLAS 2016`, `tov/alms`, `Tov–Pucella POPL 2011`)

#### 3.1 How Three Systems Distinguish Single-Use From Repeatable Capabilities

1. **Vault Key States (DeLine & Fähndrich, PLDI 2001):**
   - Keys are compile-time capability tokens tracked in a per-program-point **held-key set** `K`. Each tracked object carries a key `k` whose type includes a finite-state protocol tag (e.g., `raw`, `named`, `listening`, `closed`).
   - A **single-use operation** (e.g., `close(k)` or a one-shot state transition `raw → named`) has an effect clause that **removes** `k` from the held-key set or **transitions** `k@raw` to `k@named` (making a second call requiring `k@raw` a static type error).
   - A **repeatable operation** (e.g., `read(k)` in state `open`) requires `k@open` in the held-key set and leaves `k@open` unchanged on exit (or uses a `guard` / read-only adoption without state transition).
   - **Metatheoretic impact:** Because Vault separates the unrestricted value environment (variables can be duplicated freely) from the linear/tracked **held-key set** (keys are unique tokens updated by strong state transitions), duplicating a variable of type `tracked(K) T` merely copies the pointer; only the unique key `K` in the held-key set grants access.

2. **Mezzo's Four-Mode Lattice (`protz/mezzo/typing/Mode.ml:20-66`, `FactInference.ml`, `Permissions.ml:752-768, 1031`):**
   - Mezzo classifies every type and permission in a 4-point diamond lattice (`Mode.ml:20-55`):
     - `ModeBottom` (`⊥`, uninhabited/inconsistent)
     - `ModeDuplicable` (repeatable: `p ⊢ p * p`, e.g. immutable data, locks `lock p`, nesting witnesses `nests x p`, `x @ dynamic`)
     - `ModeExclusive` (single-owner mutable: `x @ excl * x @ excl ⊢ ⊥`, e.g. `ref a`, `marray a`, mutable constructors)
     - `ModeAffine` (`⊤`, top: neither known duplicable nor known exclusive—may be dropped, may NOT be duplicated, and two copies do NOT derive `⊥`, e.g. `punched a p`, `l @ locked`, abstract affine types, `osf::wand`)
   - Notice the critical distinction between **`ModeExclusive`** and **`ModeAffine`**:
     - A **single-use non-mutable capability** like `l @ locked` (`corelib/lock.mzi:13`) or `x @ punched a p` (`corelib/nest.mzi:23`) is **`ModeAffine`**, NOT `ModeExclusive`: it is consumed on use (`Permissions.ml:752-758`), cannot be copied, and (for `punched`) explicitly avoids triggering `exclusive`-only rules like `focus`!
     - A **repeatable read capability** is **`ModeDuplicable`**: during permission subtraction (`Permissions.ml:752-758`), `if was_duplicable then env else set_permissions env var remaining` leaves `t_x` intact in `env`!
   - **Subtlety at mixed boundaries (`Permissions.ml:759-768` & `1031`):**
     - **Flexible instantiation race:** When subtracting `t` from an affine-mode flexible variable `t_x`, `sub_type` may unify `t_x` with a duplicable type! Mezzo must re-check `now_duplicable = FactInference.is_duplicable env t_x` after `sub_type` and re-add `t_x` (`JAdd t_x`) if it became duplicable (`Permissions.ml:762-766`), otherwise valid programs lose duplicable facts.
     - **Duplicable context stripping:** When checking subtyping inside a type constructor application `TyApp` (`Permissions.ml:1031`) or typing a duplicable closure (`->`), Mezzo calls `keep_only_duplicable env`, discarding all `ModeExclusive` and `ModeAffine` permissions so they cannot be smuggled into repeatable contexts!
     - **Fact refresh (`Permissions.ml:108-112`):** Whenever a constraint assumption (`TyAnd`, `Permissions.ml:516-520`) reveals that an abstract type `a` is `exclusive`, `refresh_facts` automatically adds the duplicable permission `x @ dynamic` to every `x @ a` in scope.

3. **Alms Usage Kinds & Qualifier Polymorphism (`tov/alms/src/AST/Kind.hs:36-151`, `Statics/Expr.hs:140, 379-382`, `Statics/Patt.hs:114-118`, `Statics/Coercion.hs:94-104`):**
   - Alms uses a 2-point qualifier lattice `QLit`: `Qu` (unlimited/repeatable) `⊑ Qa` (affine/single-use) (`AST/Kind.hs:36-41, 101-107`), extended to qualifier expressions `QExp` with type variables (`QeVar`) and joins (`QeJoin`), plus a **7-point variance lattice** (`Omnivariant < {QCovariant, QContravariant} < {Covariant, QInvariant, Contravariant} < Invariant`, `AST/Kind.hs:60-95`) so type constructors can be covariant purely in the *qualifier* of a type parameter (`Q+`: `T S <: T U` when `|S| ≤ |U|`)!
   - Single-use vs. repeatable capabilities coexist in one context via **kinded subtyping (`U <: A`)**: any unlimited value can be used where an affine value is expected (since `Qu ⊑ Qa`, `Type/Internal.hs:401`), while an affine value can NEVER be used twice (`Patt.hs:117` enforces `τ ⊏: occOf n + as_occs`, which generates `τ ⊏: Qu` whenever `occ ≥ 2`, failing with `"affine type where only an unlimited type is permitted"` at `Statics/Constraint.hs:1087`).
   - **Closure qualification (`Statics/Expr.hs:140, 379-382`):** A lambda's arrow qualifier is computed automatically as `bigJoin [qualifier (γ =..= n) | n ← M.keys (AST.fv e)]`. Capturing *any* affine single-use capability forces the closure's arrow to `Qa` (`-A>` / `-o`, one-shot function); capturing only `Qu` variables produces a repeatable arrow (`->`).
   - **Dynamic promotion across the boundary (`Statics/Coercion.hs:94-104`, `lib/libbasis.alms:65-70`):** Alms supports explicit contract coercions (`e :> T`) that convert an affine function `'a2 -o 'b1` into an unlimited function `'a1 -> 'b2` by wrapping it in `affunc`, which allocates `ref (Some f)` and swaps it to `None` on first invocation, raising a blame exception on any second call.

#### 3.2 What Changes in the Metatheory When Single-Use and Repeatable Capabilities Share One Context

Basis: derived + source + normative (`Tov–Pucella POPL 2011`, `Balabonski–Pottier–Protzenko TOPLAS 2016`, `Wood–Atkey ESOP 2022`)

Merging single-use (`1` / `A` / `exclusive` / `affine`) and repeatable (`ω` / `U` / `duplicable`) capabilities into a single context `Γ` changes six core parts of the soundness metatheory compared to a purely linear calculus:

1. **Context Splitting Becomes Asymmetric (Contraction for `U`, Partitioning for `A`):** In `Γ = Γ₁ ∘ Γ₂`, repeatable bindings appear in *both* `Γ₁` and `Γ₂` (overlapping split, as in `ternary.agda/Construct/List/Overlapping.agda` with `Agree`, or `ω + ω = ω` in `generic-lr`), whereas single-use bindings appear in *at most one* side (`1 + 0 = 1`, `1 + 1` forbidden). Leftover threading (`Γ ⊢ t ⊠ Δ`) must leave repeatable slots `[ a ]` untouched (`[ a ] ↦ [ a ]`) while transitioning single-use slots (`[ a ] ↦ ] a [`), which weakens `antisym` on `_⊆_` unless consumption only counts single-use slots.
2. **Closure / Value-Typing Boundary (`Γ_dup` Restriction):** A repeatable closure (`λx.e : τ₁ →_U τ₂`) may only type-check in the repeatable sub-context `keep_only_duplicable(Γ)` (or `arrowQualifier(Γ, e) ⊑ Qu`). Without this rule, invoking the closure twice duplicates any captured single-use capability—immediately breaking subject reduction / type soundness!
3. **Subtyping and Polymorphism Must Preserve Usage Monotonicity:** Allowing `U <: A` (safe: using an unlimited value once is valid) while forbidding `A <: U` forces **contravariance** in function arguments and **qualifier-sensitive variance** on abstract data types (`Q+`/`Q-` in `alms`, `FactInference.ml` fixed-point mode inference in `mezzo`). Naive parametric polymorphism (`∀α. α → α × α`) is **unsound** unless type variables carry kind/mode bounds (`duplicable a =>` in Mezzo, `'a : U` vs. `` `a : A `` in Alms).
4. **Value Restriction on Additive Products and Polymorphic Generalization:** In `alms` (`Statics/Expr.hs:217-226`), additive records `{+ f₁ = e₁; f₂ = e₂ +}` (which share the same affine variables across fields because only one field may be projected) **must restrict every field `eᵢ` to a syntactic value**; otherwise eagerly evaluating both fields in call-by-value executes both uses of an affine variable! Similarly, ML-style `let`-generalization cannot generalize affine expressions that might be instantiated at multiple types/usages.
5. **Two-Part Store Typing Invariant:** Soundness proofs (Alias Types, $L^3$, Mezzo TOPLAS 2016) must split the runtime store typing into an **immutable/monotonic shared fragment** (whose types never change, justifying arbitrary duplication of read permissions) and a **linear/exclusive fragment** (whose cells have unique owners, justifying strong updates and deallocation). Transitioning a cell from exclusive to duplicable (`freeze` in $L^3$, `freeze` / immutable mode in Mezzo) is **monotonic** (one-way unless guarded by runtime locking or `adopter` abandonment).
6. **Inconsistency (`⊥`) Rules Only Apply to Exclusive, Not Arbitrary Affine, Capabilities:** In Mezzo (`Mode.ml`, `Permissions.ml:530-533`), `x @ excl * x @ excl ⊢ ⊥` is sound *only* because two exclusive capabilities for the same address can never simultaneously exist at runtime. Applying that same elimination rule to generic `ModeAffine` permissions (which subsume `ModeDuplicable`!) would make `x @ int * x @ int ⊢ ⊥`, collapsing the entire type system into unsoundness!

---

### 4. Multi-Level Performance & Resource Footprint Analysis (`L1–L6`)

Basis: source + normative + documentation + execution (toy model where noted)

| Level | Metric / Dimension | `typing-with-leftovers` (Agda) | `ternary.agda` (Agda) | `generic-lr` (Agda) | `protz/mezzo` (OCaml + Coq) | `tov/alms` (Haskell) | Alias Types / $L^3$ / Vault / Boyland (Papers) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **L1: Human & Agent Authoring Velocity** | Core codebase / proof size & maintenance burden | `3,577` LoC (`41` `.agda` files). Adding a new syntactic construct requires updating `Typing`, `Consumption`, `Framing`, `Functional`, `Thinning`, `Substitution`, `Mix`, `Typecheck` (`8` parallel traversals). | `7,084` LoC (`78` `.agda` files) for reusable separation algebra library; downstream interpreter proofs (CPP 2020) shrink by hiding context-split plumbing behind `Strong` monads, though manual `∙-assoc`/`resplit` proof steps remain (`Monad/State/Linear.agda:82-91`). | `4,393` LoC (`32` `.agda*` files). **Highest leverage per new language:** defining a new substructural calculus (`Example/LR.agda` ~`90` LoC) gets `ren` and `sub` for **0 extra proof lines** via `kit→sem`. | `15,563` LoC OCaml type checker (`typing/*.ml*`) + **`~14,000` Coq LoC** (+ `~2,000` LoC `DbLib`) for core soundness & race-freedom (TOPLAS 2016). | `5,251` LoC Haskell static checker (`src/Statics/*.hs`). Qualifier polymorphism (`'a` vs `` `a ``) reduces code duplication vs. monomorphic affine systems; `ex27` encodes adoption/focus in `83` LoC. | Vault (PLDI 2001): Windows 2000 driver protocol annotations authored directly in interface headers; $L^3$ / Alias Types / Boyland: pen-and-paper proofs (higher human audit burden for case completeness). |
| **L2: Framework & Toolchain Build Time** | From-scratch / incremental toolchain build | Agda typechecks `3.6k` LoC (standard library dependency); modular per-file `.agdai` incremental rebuilds. | Agda `--safe --without-K` across `78` modules; heavy instance-search (`{{...}}`) in `Relation.Ternary.Structures` increases Agda elaboration time on large combinator chains. | Agda `--sized-types --without-K --prop` (`Example/LR.agda:72` explicitly comments out fine-grained `PremisesFlags` because *"checking it (with instances) takes too long"*!). | OCaml `ocamlbuild` compiles `mezzo` in seconds; Coq `~14k` LoC proof compiles offline in minutes (not measured directly on this host). | GHC/Cabal builds `alms` Haskell codebase (`~10k` total LoC). | N/A (compiler prototype for Vault; paper calculi for Alias Types, $L^3$, Boyland). |
| **L3: Compilation, Elaboration & Synthesis Latency** | Typechecking algorithmic complexity & tail latency | **Deterministic `O(N · |Γ|)`** single pass (`Typecheck.agda`); zero split backtracking. Interactive LSP latency dominated by Agda term normalization rather than split search. | Proof-relevant splitting is **undecided/manual** unless paired with a solver or `Market` leftover view; naive top-down split search explodes (`>200,000` steps by `N = 8` on left-nested chains in toy probe). | Top-down `UsageCheck.agda` uses nondeterministic `NonDetInverses` (`+⁻¹`), risking `2^k` search on `1`-graded slots; Agda instance resolution adds elaboration tail latency (`Example/LR.agda:72`). | Backtracking permission search (`Permissions.ml:743` `try_several`, `par` at `948` for `Forall-L`/`Exists-R`, priority heuristic `sort` at `730-741`); worst-case exponential on complex polymorphic permission merges (`Merge.ml`), typically fast in practice with heuristics. | **Deterministic `O(N · |Γ|)`** occurrence counting (`AST/Expr.hs` `efv_` cached bottom-up) + subtyping/subqualifier constraint graph (`Statics/Constraint.hs`), with graph-simplification pass (`Constraint.hs:1558`). | Vault / Alias Types / $L^3$ / Boyland: syntax-directed linear/store-context threading (`O(N · |C|)`), except fractional solver if rational fractions are inferred rather than explicitly split. |
| **L4: Generated Code Execution Performance** | Runtime cycles, boundary crossings, dynamic checks | Erased (Agda proof/checker prototype; no native codegen). | Intrinsically typed Agda definitional interpreter (not a native AOT backend). | Agda syntactic/semantic framework (no native codegen). | Compiles to OCaml (`UntypedMezzo2UntypedOCaml.ml`): **0** overhead for static permissions/locks-erased fields, **1 pointer load + branch + null store** on every `take` (`Mezzo2UntypedMezzo.ml:227-237`), **1 store** on every `give` (`221-225`). | Interpreted/compiled via Haskell runtime; **0** overhead for statically checked affine values; `affunc` dynamic coercion (`libbasis.alms:65-70`) incurs **1 heap ref alloc + read/write/branch per call**. | Alias Types, $L^3$, Vault, Adoption & Focus, Boyland: **0 runtime cycles** for capability/permission/key checks (all tokens erased at codegen; strong updates compile to direct in-place stores!). |
| **L5: Proof / Certificate Verification Speed** | Kernel checking throughput & cold-start latency | Agda kernel checks `.agdai` interfaces; small `3.6k` LoC footprint gives fast re-check. | Agda `--safe --without-K` kernel verifies all `78` modules without axioms; `CrossSplit` proofs are structurally small. | Agda kernel checks `4.4k` LoC; note `--sized-types` is known to weaken Agda's consistency boundary compared to pure `--safe --without-K` (see **Boundaries**). | Coq kernel checks `~14k` LoC metatheory once; Mezzo's OCaml type checker itself is **unverified** (emits derivation trees `Derivations.ml` for debugging/printing, not machine-checked certificates). | Unverified Haskell type checker (no emitted proof certificate). | Pen-and-paper proofs only (no machine-checked kernel certificate). |
| **L6: RAM, Disk & Binary Footprints** | Per-object metadata, proof artifacts, peak RSS | Source `149 KB` tarball; proof artifacts live in Agda `.agdai` files; zero runtime binary. | Source `68 KB` tarball; no runtime heap representation. | Source `558 KB` tarball (`LTree`-indexed vectors avoid quadratic list-append copies). | Source `757 KB` tarball. **Runtime heap footprint:** every compiled algebraic data block carries **`+1` word (`8 B` on 64-bit) hidden `adopter` field** (`UntypedMezzo2UntypedOCaml.ml:37-68, 156`, `Interpreter.ml:90`) on top of OCaml's `8 B` GC header! | Source `239 KB` tarball. **`0 B`** extra metadata on statically affine values; **`+1` boxed `ref (Option ...)` cell** per dynamically promoted `affunc` closure. | Alias Types, $L^3$, Vault, Adoption & Focus, Boyland: **`0 B` per-object runtime metadata** (all capabilities, keys, and fractions are completely erasable). |

---

### 5. Human Comprehensibility and Conceptual Simplicity / Model Refinement (`C1–C2`)

Basis: source + normative + derived

#### 5.1 Human Comprehensibility & Mental-Model Ergonomics (`C1`)

- **Local vs. Nonlocal Reasoning Burden:**
  - **Input–output leftovers (`typing-with-leftovers`)** mirror imperative programmer intuition ("this statement consumed capability `x`, leaving `y` available for the next line"), giving crisp local error diagnostics (`Typecheck.agda:26` immediately reports consumption of an already-stale variable `] σ [`). However, **parallel composition** becomes counterintuitive under leftover notation because the syntax implies a temporal ordering between independent branches.
  - **Occurrence counting + usage kinds (`alms`)** delivers the lowest cognitive friction for ML programmers: there are only two qualifiers (`U` vs. `A`, visually marked by `'a` vs. `` `a ``) and no explicit capability threading in ordinary code. The main cognitive trap is **closure capture**: capturing an affine variable silently downgrades a lambda from `->` to `-A>` (`Statics/Expr.hs:379-382`), producing nonlocal type errors when that closure is later passed to a higher-order function expecting an unlimited callback.
  - **Permission systems (`mezzo`)** expose the highest working-memory concept count: programmers must simultaneously track value types, anchored permissions (`x @ T`), floating permissions, the 4-point mode lattice (`bottom`, `duplicable`, `exclusive`, `affine`), `consumes` annotations, `adopts` clauses, `punched` types, and one-shot wands (`osf::wand`). Notably, `protz/mezzo` includes an entire `DerivationPrinter.ml` and interactive merge-conflict explainer (`TypeChecker.ml:1019-1020`, `Debug.explain_merge`) specifically because branch-merging failures (`Merge.ml`) are otherwise opaque to humans!
  - **Fractional permissions (Boyland 2003)** have an intuitive algebraic metaphor ("half a permission for each reader, full `1` for a writer"), but quickly accumulate nonlocal arithmetic boilerplate when functions are polymorphic over unknown incoming fractions `π` (requiring abstract fraction variables or Boyland's `π/2` splitting chains, as visible in `alms/examples/ex65-popl-Fractional.alms:17-18`).
- **Human Auditability vs. Agent/Solver Execution:** A key asymmetry emerges between what is easy for an automated solver or agent versus what a human can audit: Mezzo's backtracking permission engine (`Permissions.ml:743-770, 945-962`) and `generic-lr`'s `LinFuncRel` semiring matrices are straightforward for a machine to manipulate, whereas a human reviewing a soundness trust boundary can audit `typing-with-leftovers`'s `Usage.agda` (`[ a ]` / `] a [`, `90` lines) or `ternary.agda`'s `Rel₃` (`Core.agda`, `125` lines) in minutes.

#### 5.2 Conceptual Simplicity, Orthogonality & Universal Model Refinement (`C2`)

- **Separating Core Semantic Invariants from Presentation Artifacts:**
  - All three Agda mechanizations enforce the **exact same semantic invariant** (each linear assumption is consumed once along every dynamic path, and parallel/multiplicative subcomputations consume disjoint footprints). The proliferation of auxiliary lemmas in `typing-with-leftovers` (`Consumption`, `Framing`, `Divide`, `Swap`, `Functional`) versus `ternary.agda` (`CrossSplit`, `Uncross`, `repartition`) versus `generic-lr` (`LinFuncRel`) reflects **proof-engineering representation choices**, not distinct operational semantics.
  - **`ternary.agda`'s `Market` construction (`Construct/Market.agda:22-78`) provides a deep-module unification (Ousterhout criterion):** rather than treating explicit splitting and input–output leftovers as rival logics, a single commutative partial monoid (`Rel₃`) generates *both* symmetric parallel splitting (`Φ₁ ∙ Φ₂ ≣ Φ`) *and* supply/demand leftover subtraction (`supply l₁ ∙ demand r ≣ supply l₂`) as instances of one interface!
- **Are Single-Use Capabilities, Exclusive Mutable Permissions, and Fractional Reads Redundant or Orthogonal?**
  - **Felleisen macro-expressibility test:**
    - *Static Adoption & Focus* **is** macro-expressible inside an affine language with existential types and one-shot functions (`tov/alms/examples/ex27-focusing-and-adoption.alms:34-83` implements `REGION` with `adopt` and `focus` returning an affine restoration closure `('t1,'a) region1 -A> ('t,'a) region` using zero extra language primitives!).
    - *Fractional capabilities over immutable/read-only views* **are** macro-expressible as an abstract affine type with `split`/`join` (`tov/alms/examples/ex65-popl-Fractional.alms:3-40`), **provided** the runtime/trusted library enforces the `1 = write, (0,1) = read` discipline internally.
    - *Dynamic Adoption & Abandon (`Mezzo` `give`/`take`)* is **NOT** macro-expressible in a purely static erased linear calculus without adding a runtime mutable field (`adopter`) and a fallible dynamic branch (`take` failure): it genuinely trades static lexicality for runtime heap-state tracking.
    - *Distinguishing `ModeExclusive` from `ModeAffine` (Mezzo)* is **genuinely orthogonal** to `ModeDuplicable` whenever a language wants both (a) single-use tokens that are *not* exclusive (like `punched a p` or `l @ locked`, which cannot derive `⊥` on self-collision or trigger `exclusive`-guarded focusing) and (b) exclusive heap locations (where two simultaneous exclusive permissions prove unreachability `⊥`). Merging `exclusive` and `affine` into a single "linear" bit either loses `x @ excl * x @ excl ⊢ ⊥` or makes `punched` double-focusable!

---

### 6. End-to-End Solution & Implementation Validation (`V1–V4`)

Basis: source + normative + documentation

Even when a core calculus has a machine-checked soundness proof (such as Mezzo's `~14k`-line Coq proof or `typing-with-leftovers`'s Agda soundness/completeness proofs), unmodeled reality gaps persist between the core calculus and the full compiler/runtime:

- **V1 (Specification Adequacy, Mutation & Non-Vacuity Validation):**
  - In mechanized metatheory (`typing-with-leftovers`, `ternary.agda`, `generic-lr`), non-vacuity is validated by constructing concrete well-typed example derivations and executable interpreters (`typing-with-leftovers/src/linear/Typecheck/Examples.agda`, `generic-lr/src/Generic/Linear/Example/AllExamples.agda`, `ternary.agda/Monad/State/Linear.agda`).
  - However, `protz/mezzo`'s OCaml implementation (`15.6k` LoC) is **not** extracted from its Coq formalization (`~14k` LoC); the paper (TOPLAS 2016) formalizes a core calculus omitting several surface features (such as full flexible-variable unification heuristics and `Merge.ml` conflict recovery). Thus Mezzo relies on an internal runtime invariant checker (`Permissions.safety_check` at `Permissions.ml:41-100`, checking singleton uniqueness and at-most-one-exclusive-permission at debug level `≥ 5`) and regression tests (`tests/fact-inconsistency.mz`, `merge18.mz`, `merge19.mz`) to catch checker–spec drift! Notice that `Permissions.ml:77-79` explicitly disables one branch of `safety_check` (`if false && ... List.length concrete > 1`) because it proved too restrictive on `twostructural.mz`—a textbook concrete example of a specification–implementation seam!
  - Similarly, `tov/alms` validates its static semantics via paired positive/negative regression examples (`examples/ex01`–`ex66`, including explicit `*-type-error.alms` and `*-blame-error.alms` suites checking that invalid affine duplications and contract violations are rejected for the intended reason).
- **V2 (Compiler, Lowering & Checker Soundness Fuzzing):**
  - Across all five examined repositories, **no automated differential or metamorphic typechecker fuzzer** (skeletal AST fuzzing, QuickChick property-based counterexample generation against an operational semantics, or translation-validation across `Mezzo2UntypedMezzo.ml` → `UntypedMezzo2UntypedOCaml.ml`) is present in the pinned trees. In particular, `Permissions.ml:752-768` (`was_duplicable` vs. `now_duplicable` flexible instantiation) and `Merge.ml` backtracking are high-leverage targets for grammar-based typechecker fuzzing paired with `safety_check` enabled at level `5` and interpreter execution (`Interpreter.ml`).
- **V3 (Concurrency, Crash, Silicon & Physical Leakage Validation):**
  - Mezzo's TOPLAS 2016 Coq proof establishes **data-race freedom under sequential consistency (interleaving concurrency)** for locks and exclusive/duplicable permissions (`corelib/lock.mzi`, `corelib/thread.mzi`). None of the examined implementations (`mezzo`, `alms`, Vault) are validated with stateless weak-memory model checking (`GenMC`/`Loom`) against C11/ARMv8/TSO acquire-release lock semantics, nor crash-consistency fault injection (`VOPR`/`CrashMonkey`) for persistent capabilities, nor side-channel leakage checks (`TVLA`) for secret-dependent `ETake` failure branches.
- **V4 (Plant Falsification, Telemetry & Human Comprehension Validation):**
  - No empirical human comprehension trials (`SMoL`-style litmus tests) were reported in the examined papers for leftover vs. explicit-splitting vs. mode-lattice mental models; DeLine & Fähndrich (PLDI 2001) provide qualitative industrial experience applying Vault to Windows 2000 driver protocols, and Mezzo provides `Debug.explain_merge` (`TypeChecker.ml:1019`) as an engineering response to observed user confusion on permission-merge errors.

## Boundaries

- **Additive `⊤` in `typing-with-leftovers` (`unsupported`):** `gallais/typing-with-leftovers` at `b0289b34fc47afc67ef8d2881c63a7ef0748a989` implements `𝟙, 𝟘, ⊗, ─o, &, ⊕` (`src/linear/Type.agda`) and omits additive `⊤`. Adding `⊤` breaks functional/deterministic leftovers unless extended with strict/lazy flags as in Cervesato–Hodas–Pfenning (TCS 2000).
- **Sized-Types Consistency Caveat in `generic-lr` (`known not to apply` to `--safe` pure MLTT):** While core modules of `laMudri/generic-lr` use `{-# OPTIONS --safe --without-K --prop #-}`, `Syntax/Term.agda:1` and `Semantics/Syntactic.agda:1` use `{-# OPTIONS --sized-types --without-K --prop #-}` (omitting `--safe`), because Agda's `--sized-types` has known soundness interactions with `--safe`.
- **Contiguous Byte-Slice Splitting (`not examined` in upstream repos):** None of the five pinned repositories implements byte-range adjacency splitting/rejoining (`[a, b) + [b, c) = [a, c)`) with arithmetic overlap proofs; comparisons to slice splitting above are `derived` from the atomic-location rules in Alias Types, $L^3$, Mezzo, and fractional permissions.
- **Agda/OCaml/Haskell Live Build & Typecheck Timings (`not examined`):** The five upstream repositories were inspected directly from pinned source tarballs without executing `agda`, `ocamlbuild`, `ghc`, or `coqc` builds on the local host (which lacks Agda/OCaml/Coq toolchains). All L2/L5 compile-time observations come from source comments (e.g., `generic-lr/src/Generic/Linear/Example/LR.agda:72`) and published paper figures (TOPLAS 2016 Coq LoC), not local wall-clock measurements.
- **Toy-Model Scope of Algorithmic Splitting Probe (`known not to apply` as a benchmark of upstream compilers):** The Python probe in Section 1.3 measures an idealized toy model of the three context-splitting algorithms on synthetic tensor chains (`N = 4..16`); it demonstrates the asymptotic worst-case blowup of naive binary splitting on left-nested trees, not the runtime speed of Agda's `Typecheck.agda` or Haskell's `alms` binary.
- **Weak-Memory & Lock-Free Concurrency (`unknown` / `not examined`):** Whether Mezzo's dynamic `adopter` field updates (`Interpreter.ml:706-733`) remain race-free under relaxed memory models without release-acquire fences on `adopter` writes/reads is not established by the sequentially consistent Coq formalization (TOPLAS 2016) and was not examined on hardware.

## Evidence

### Pinned GitHub Source Evidence

1. **`gallais/typing-with-leftovers`** @ `b0289b34fc47afc67ef8d2881c63a7ef0748a989` (`41` files, `3,577` LoC under `src/linear/`):
   - `src/linear/Usage.agda:23-90` (`Usage`, `[ a ]` / `] a [`, `Usages`, `_⊢_∈[_]⊠_`, `Mergey`, `_⋈_`).
   - `src/linear/Typing.agda:22-148` (`_⊢_∋_⊠_`, `_⊢_∈_⊠_`, `` `lam_ ``, `` `let_∷=_`in_ ``, `` `prd⊗ ``, `` `prd& ``, `` `app ``, `` `case ``).
   - `src/linear/Usage/Consumption.agda:15-115` (`_─_≡_─_`, `_⊆_`, `refl`, `trans`, `antisym`, `irrelevance`, `swap` at lines `62-67`, `divide` at lines `79-85`, `Consumption`, `Framing`).
   - `src/linear/Typing/Consumption.agda:17-65` (`consumptionInfer`, `consumptionCheck`, `framingInfer`, `framingCheck`).
   - `src/linear/Typing/Thinning.agda:25-55` (`Thinning`, `Thinning′`, `thinning`).
   - `src/linear/Typing/Functional.agda:16-110` (`functionalInfer`, `functionalInferPost`, `functionalInferPre`, `functionalCheckPre`).
   - `src/linear/Typing/Substitution.agda:23-147` (`weakInfer`, `weakCheck`, `substCase` lines `82-84` using `functionalEnvPre`, `substInfer`, `substCheck`).
   - `src/linear/Typing/Mix.agda:22-75` (`splitUsages`, `unsplitUsages`, `mixCheck`, `mixInfer`).
   - `src/linear/Typecheck.agda:24-85` (decidable `consume`, `infer` threading leftovers deterministically).
   - `src/linear/Soundness.agda:21-56` (`illCheck`) and `src/linear/Completeness.agda`.
2. **`ajrouvoet/ternary.agda`** @ `4097451af88fb512f89fcb06f643e554fcd0a6aa` (`78` files, `7,084` LoC under `src/`):
   - `src/Relation/Ternary/Core.agda:41-125` (`Rel₃`, `_∙_≣_`, `_◆_`, `Conj` / `_✴_`, `Wand` / `_─✴_`).
   - `src/Relation/Ternary/Structures/PartialSemigroup.agda:13-65` (`IsPartialSemigroup`, `∙-assocᵣ`, `∙-assocₗ`, `✴-assocₗ/ᵣ`, `com`).
   - `src/Relation/Ternary/Structures/PartialMonoid.agda:18-90` (`Emptiness`, `IsPartialMonoid`, `∙-idˡ/ʳ`, `arrow`).
   - `src/Relation/Ternary/Structures/Crosssplit.agda:19-51` (`CrossSplit`, `Uncross`, `IsCrosssplittable`).
   - `src/Relation/Ternary/Construct/List/Disjoint.agda:22-56` (`disjoint-split`, `toPermutation`, `⊕-functional`, `threeway`) and `Construct/List/Overlapping.agda:50-70` (`overlaps`, `⊆-⊗`).
   - `src/Relation/Ternary/Construct/Market.agda:22-99` (`Market := supply | demand`, `Split` constructors `supplyₗ`/`supplyᵣ`/`demand`, `market-isSemigroup`, `market-isCommutative`).
   - `src/Relation/Ternary/Monad.agda:26-90` (`Monad`, `Strong`, `str`, `bind`, `kleisli`), `Monad/Weakening.agda:19-52` (`_⇑`, `th`), and `Monad/State/Linear.agda:31-93` (`MonadHeap`, `mkref`, `read`, `write` strong update using `repartition` & `resplit`).
3. **`laMudri/generic-lr`** @ `3ee8ce26f6c6ec5860ed323d4cf3c9f6d0f5ef7e` (`32` files, `4,393` LoC under `src/Generic/Linear/`):
   - `src/Generic/Linear/Algebra.agda:6-90` (`PoSemiring`, `Vᴾ`, `+*-comm`).
   - `src/Generic/Linear/Syntax.lagda.tex:20-130` (`SizedCtx`, `Ctx` over `LTree`, `Premises` with `` `⊤, `∧, `ℑ, `✴, `·, `□ ``, `Rule`, `System`).
   - `src/Generic/Linear/Syntax/Interpretation.lagda.tex:28-88` (`_✴ᶜ_`, `⟦_⟧p`).
   - `src/Generic/Linear/Syntax/Term.agda:1-29` (`[_,_]_⊢_`).
   - `src/Generic/Linear/Variable.agda:27-56` (`_∋_` with `basis : P ≤* ⟨ idx ∣`).
   - `src/Generic/Linear/Environment.agda:34-52` (`IsPresheaf`, `[_]_⇒ᵉ_` carrying `Ψ : LinFuncRel t s 0ℓ`).
   - `src/Generic/Linear/Semantics/Syntactic.agda:51-109` (`Kit`, `kit→sem`, `Ren-Kit`, `ren`, `Sub-Kit`, `sub`).
   - `src/Generic/Linear/Example/LR.agda:72-90` (instance-check latency note; `LR` rules) and `Example/UsageCheck.agda:73-90` (`NonDetInverses`).
4. **`protz/mezzo`** @ `4e9d917558bd96067437116341b7a6ea02ab9c39` (`55` files, `15,563` LoC under `typing/`):
   - `typing/Mode.ml:20-66` (`ModeBottom`, `ModeDuplicable`, `ModeExclusive`, `ModeAffine`, `leq`, `meet`).
   - `typing/Permissions.ml:41-112` (`safety_check`, disabled concrete check at line `79`, `refresh_facts`), `516-565` (`TyAnd`, `ExclusivePerms` inconsistency at `530-533`), `730-770` (`try_several`, `was_duplicable` vs. `now_duplicable` at `752-768`), `945-1039` (`Forall-L`/`Exists-R` `par`, `keep_only_duplicable` at `1031`).
   - `typing/TypeChecker.ml:1016-1129` (`Merge`, `EGive` requiring `is_exclusive` at `1088`, `ETake` requiring `TyDynamic` + `has_adopts_clause` at `1100-1111`, `EOwns` at `1113-1128`).
   - `corelib/nest.mzi:8-42` (`nests`, `punched`, `focus`, `defocus`, `consult`), `corelib/lock.mzi:5-50` (`lock`, `locked`, `new_locked`), `corelib/array.mzi:8-69` (`duplicable a =>`, `borrow`), `stdlib/osf.mzi:3-34` (`osf`, `wand`), `stdlib/focused.mzi:1-2`.
   - `interpreter/Interpreter.ml:83-93, 313, 706-733` (`mutable adopter: block option`, `EGive` `assert (b1.adopter = None)`, `ETake` runtime check) and `compiler/Mezzo2UntypedMezzo.ml:221-245`, `compiler/UntypedMezzo2UntypedOCaml.ml:37-68, 154-157` (`adopter_field` at index `0`, shifting all user fields by `+1`).
5. **`tov/alms`** @ `b35b804abaf7579aae8a57785544562647919c36` (`13` files, `5,251` LoC under `src/Statics/`):
   - `src/AST/Kind.hs:36-151` (`QLit := Qu | Qa`, 7-point `Variance` lattice `Omnivariant`..`Invariant`).
   - `src/AST/Expr.hs:126-235` (`ExprNote.efv_`, multiplicative `|*|` vs. additive `ADDITIVE` / `|+|`).
   - `src/Statics/Patt.hs:47-118` (`occOf n`, `τ ⊏: occOf n + as_occs`).
   - `src/Statics/Expr.hs:140, 217-226, 379-382` (`arrowQualifier`, `syntacticValue` restriction on additive records).
   - `src/Statics/Constraint.hs:33-51, 1087` (`<:, =:, ⊏:, ~:, relate`, affine-where-unlimited error).
   - `src/Statics/Coercion.hs:94-104` and `lib/libbasis.alms:65-70` (`affunc` dynamic single-use ref wrapper).
   - `examples/ex27-focusing-and-adoption.alms:34-83` and `examples/ex65-popl-Fractional.alms:3-40`.

### Primary Literature & Toy-Model Probe Provenance

- All eleven DOIs listed in `REPORT.json` were verified on 2026-11-19 against primary publication records (TCS 2000, ESOP 2000, PLDI 2001, PLDI 2002, SAS 2003, TLCA 2005, POPL 2011, ACM TOPLAS 2016, LIPIcs TYPES 2017/2019, CPP 2020, ESOP 2022).
- The toy-model splitting probe (`Section 1.3`) was executed in Python 3 on Linux (`2026-11-20`) comparing deterministic leftover threading, bottom-up free-variable counting, and naive top-down subset-splitting (`step_limit = 200,000`) over right-nested and left-nested `N`-leaf linear tensor trees (`N ∈ {4, 6, 8, 10, 12, 16}`). Standalone reproducer (save as `/tmp/probe_p1.py` and run `python3 /tmp/probe_p1.py`):

```python
def make_chain(n, left=False):
    t = ("var", 0 if left else n - 1)
    rng = range(1, n) if left else range(n - 2, -1, -1)
    for i in rng:
        t = ("pair", t, ("var", i)) if left else ("pair", ("var", i), t)
    return t

def check_leftover(term, avail):
    steps = 0
    def go(t, ctx):
        nonlocal steps; steps += 1
        if t[0] == "var":
            if not ctx[t[1]]: return None
            nxt = list(ctx); nxt[t[1]] = False; return nxt
        mid = go(t[1], ctx)
        return None if mid is None else go(t[2], mid)
    out = go(term, avail)
    return (out is not None and not any(out)), steps

def check_naive_split(term, avail, step_limit=200000):
    steps, aborted = 0, False
    def splits(ctx):
        active = [i for i, v in enumerate(ctx) if v]; n = len(ctx)
        for mask in range(1 << len(active)):
            l, r = [False] * n, [False] * n
            for bit, idx in enumerate(active):
                (l if (mask >> bit) & 1 else r)[idx] = True
            yield l, r
    def go(t, ctx):
        nonlocal steps, aborted; steps += 1
        if steps > step_limit: aborted = True; return False
        if t[0] == "var": return ctx[t[1]] and sum(ctx) == 1
        for l, r in splits(ctx):
            if go(t[1], l) and go(t[2], r): return True
            if aborted: return False
        return False
    return go(term, avail), steps, aborted

def check_occ_count(term, n):
    steps = 0
    def fv(t):
        nonlocal steps; steps += 1
        if t[0] == "var": return {t[1]: 1}
        a, b = fv(t[1]), fv(t[2])
        for k, v in b.items(): a[k] = a.get(k, 0) + v
        return a
    c = fv(term)
    return all(c.get(i, 0) == 1 for i in range(n)), steps

for left in (False, True):
    print("LEFT-NESTED" if left else "RIGHT-NESTED")
    for n in ([4, 6, 8, 10, 12] if left else [4, 6, 8, 10, 12, 16]):
        t, avail = make_chain(n, left=left), [True] * n
        print(n, check_leftover(t, avail)[1], check_occ_count(t, n)[1], check_naive_split(t, avail)[1:])
```

## Revalidation

1. **Diff targeted structural definitions in upstream repositories:** When evaluating newer revisions of `typing-with-leftovers`, `ternary.agda`, `generic-lr`, `mezzo`, or `alms`, diff only the load-bearing files:
   - `typing-with-leftovers`: `src/linear/Typing.agda`, `Usage/Consumption.agda` (`swap`, `divide`), `Typing/Functional.agda`, `Typecheck.agda`.
   - `ternary.agda`: `src/Relation/Ternary/Core.agda`, `Structures/Crosssplit.agda`, `Construct/Market.agda`, `Monad/State/Linear.agda`.
   - `generic-lr`: `src/Generic/Linear/Syntax/Term.agda` (check whether `--sized-types` is replaced by `--safe`), `Environment.agda`, `Semantics/Syntactic.agda`, `Example/UsageCheck.agda`.
   - `mezzo`: `typing/Mode.ml`, `typing/Permissions.ml` (`safety_check`, `was_duplicable`/`now_duplicable`, `keep_only_duplicable`), `typing/TypeChecker.ml` (`EGive`/`ETake`), `compiler/UntypedMezzo2UntypedOCaml.ml` (`adopter_field`).
   - `alms`: `src/AST/Kind.hs`, `src/AST/Expr.hs` (`efv_`), `src/Statics/Patt.hs` (`occOf`), `src/Statics/Expr.hs` (`arrowQualifier`), `src/Statics/Coercion.hs` (`affunc`).
2. **Re-run the splitting-asymmetry probe:** Any candidate substructural typechecker using top-down context splitting should be tested on **both** right-nested `(x₀ ⊗ (x₁ ⊗ ...))` and left-nested `(((x₀ ⊗ x₁) ⊗ ...) ⊗ x_{N-1})` linear chains for `N = 8, 16, 32` to verify absence of order-dependent exponential backtracking.
3. **Re-check mixed-mode soundness invariants on any new permission calculus:** Construct three discriminating negative test cases before accepting a typechecker mixing single-use and repeatable capabilities: (a) a repeatable closure capturing a single-use capability and invoking it twice, (b) double-focusing or double-taking an adopted exclusive object through aliased references, and (c) splitting a `0`-fraction read token off a `1`-fraction write capability (or duplicating a generic `affine` permission to trigger an `exclusive` inconsistency `⊥`).
