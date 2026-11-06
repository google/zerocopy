# Findings

## Axioms are explicit logical assumptions

Lean represents an axiom as an `AxiomVal` containing a name, universe parameters, a type, and an `isUnsafe` bit. Unlike a theorem, definition, or opaque declaration, an axiom carries no proof or value body for the kernel to check. The declaration elaborator turns source `axiom` syntax directly into `Declaration.axiomDecl`; the kernel checks that the axiom's type is well formed and adds the assumption to the environment.

A theorem that uses an axiom is therefore kernel-correct relative to that assumption, not a derivation of the assumption from earlier declarations.

Basis: **source**.

## Local hypotheses are not global axioms

A local hypothesis is a bound variable in the theorem being proved. It becomes part of the theorem's function/Pi type and does not create an environment-level axiom declaration. The transitive axiom collector records a dependency only when a referenced global constant is stored as `.axiomInfo`.

Thus proving `P → Q` under a local `h : P` does not assert `P` globally. Declaring `axiom h : P` does.

Basis: **source** + **derived** consequence of the declaration representation.

## `sorry` is the axiom `sorryAx`

`Init.Prelude` defines `axiom sorryAx (α : Sort u) (synthetic : Bool) : α` and documents that the `sorry` term/tactic expands to `sorryAx _ (synthetic := false)`. Synthetic error-recovery sorries use the same axiom with the flag set to `true`.

Lean normally warns when a declaration contains `sorry`. The durable trust fact is the dependency on `sorryAx`: downstream declarations and imported modules can retain that dependency even when the original source occurrence is no longer visible.

Basis: **source**.

## `#print axioms` computes the transitive admission set

`Lean.CollectAxioms` recursively walks the type and value of definitions, theorems, and opaque declarations. When it reaches an axiom declaration, it records that axiom and also inspects the axiom's type. For imported modules, Lean serializes and reuses precomputed dependency sets.

`#print axioms foo` invokes this collector. A direct or indirect `sorry` therefore appears as `sorryAx`; an ordinary user axiom appears by name; and assumptions introduced by proof machinery can appear by generated names. A clean result has a deliberately narrow meaning: no environment axiom declarations occur in that declaration's transitive logical dependency closure.

The local `warn.sorry` diagnostic is useful but weaker than this dependency audit: warnings can be suppressed or handled differently by surrounding tooling, while the transitive dependency persists through composition.

Basis: **source** + **derived** operational consequence.

## Safe declarations cannot directly depend on unsafe declarations

Lean declarations carry safety information. `DefinitionSafety` distinguishes `unsafe`, `safe`, and `partial`; axioms carry an `isUnsafe` bit. The kernel type checker rejects a reference to an unsafe constant when the declaration being checked is not unsafe.

The compiler's internal `unsafe axiom lcProof {α : Prop} : α` documents the purpose of this fence: the marker prevents that compiler-only constant from entering regular proofs. This is a kernel-enforced boundary, not a linter convention.

Basis: **source**.

## Compiled implementation substitution is a separate trust boundary

`@[implemented_by impl]` tells the compiler to replace calls to one declaration with calls to another implementation. The attribute checks that the declarations have the same type, but its documentation explicitly says that semantic equivalence is not checked.

This permits a safe logical definition or opaque constant to have a different executable implementation. Ordinary kernel reasoning uses the logical definition. Proof procedures that later trust native execution can make the executable replacement relevant to theorem trust; Lean's own documentation calls out native-evaluation proofs as the important exception.

`@[csimp]` narrows this gap because a compiler-simplification theorem must prove an equality between the original and replacement functions. The source still notes that the equality proof itself can depend on assumptions, so admission auditing remains relevant.

Basis: **source**.

## Native evaluation introduces an assumption after compiled execution

`Lean.Meta.Native.nativeEqTrue`, used by `native_decide` and `bv_decide`, builds a Boolean definition, compiles and executes it, checks that execution returns `true`, and then adds a fresh non-unsafe axiom asserting the successful result. The source describes this path explicitly as native computation followed by asserting the result as an axiom toward the logic.

Consequently, a proof using this route has a larger trust base than ordinary kernel-only proof checking: the compiled execution participates in justifying the generated axiom. `#print axioms` can expose the generated dependency but cannot independently validate the runtime computation.

Basis: **source**.

## `unsafe t` is an executable escape hatch

The term form `unsafe t : α` permits unsafe declarations inside an expression by constructing an auxiliary definition and using the implemented-by mechanism to present a safe interface. Its parser documentation requires the result type to be nonempty for soundness and warns that the compiler cannot establish memory safety for the operation.

By itself this is not a new logical admission mechanism; the kernel's unsafe-declaration fence still governs logical dependencies. It becomes proof-relevant when later proof machinery trusts compiled execution.

Basis: **source** + **derived** composition.

## `debug.skipKernelTC` bypasses the ordinary proof check

`debug.skipKernelTC` defaults to `false`. Its source description warns that enabling it may compromise soundness because proofs are not checked by the Lean kernel. `Lean.AddDecl` implements this directly: when the option is true, declarations use `addDeclWithoutChecking` rather than the kernel-checking path.

A result whose trust claim includes Lean kernel checking must therefore bind that claim to a checker configuration in which `debug.skipKernelTC` is false.

Basis: **source**.

## Opaque and noncomputable declarations are not automatically admissions

The axiom collector treats `.defnInfo`, `.thmInfo`, and `.opaqueInfo` differently from `.axiomInfo`: it recursively inspects their types and values rather than adding the declarations themselves to the axiom set. Opacity therefore does not itself create an assumption.

`noncomputable` concerns executable-code generation rather than creating an environment axiom kind. Such a definition can still participate in kernel-checked logical reasoning.

Basis: **source** + **derived** distinction from declaration and compiler representations.

## Audit output still needs a policy

`#print axioms` reports which assumptions a declaration depends on; it does not decide whether they are acceptable. A verifier must compare the returned set against an explicit trust policy. For Anneal, distinguishing accepted foundational assumptions, unfinished-proof admissions, native-evaluation assumptions, intentional model assumptions, and unexpected dependencies is a design-policy question. Lean supplies the mechanically recoverable dependency set.

Basis: **derived** from the source-level audit interface.
