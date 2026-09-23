# Unsafe Rust source audit

## Claim and verdict

Snapshot: the supplied Cargo.toml, src/lib.rs, POLICY-SCARLET.md, POLICY-INDIGO.md, TCB.md, and REQUEST.md, reviewed source-only on 2026-08-01. There are no dependencies, build scripts, generated artifacts, macros generating APIs, or prior audits in scope.

| Claim | Exact theorem | Verdict |
|---|---|---|
| SOUND | For every configuration in Required and every well-typed safe call value_or_zero(value), execution is free of Rust undefined behavior. | PROVED relative to BUILD-MAP-C and the version-matched Rust axioms below. |
| POST | For those calls, Some(b) returns b and None returns 0. | PROVED. |

Combined mandatory result: PROVED. This is a Rust source-semantics result, not a compiler-backend, binary, or platform theorem.

## Required domain and configuration closure

Let V={1.84.0,1.85.0,1.86.0}, T={X,A,W} as defined by the policies, f=turbo, h=hardened, P=all Cargo profiles, and d∈{debug-assertions-off,on}. Preserve the published predicates:

S = ¬f ∨ (f∧t=X∧(¬h∨v≥1.85.0)) ∨ (f∧t=A∧h).

I = ¬f ∨ (f∧t=X∧(h∨v≥1.86.0)) ∨ (f∧t=A∧¬h∧v≥1.85.0).

Because neither policy has precedence, Required is the conservative audit predicate S∨I, with v∈V, t∈T, both Boolean feature states, p∈P, and d in both states. This is not a resolution or a new support promise. Exact case normalization gives:

Required = ¬f ∨ (f∧t=X) ∨ (f∧t=A∧(h∨v≥1.85.0)).

Proof: on X, (¬h∨v≥1.85)∨(h∨v≥1.86) is true for every h; on A, h∨(¬h∧v≥1.85) equals h∨v≥1.85; neither predicate admits f∧t=W. Thus S⊆Required, I⊆Required, and the reverse inclusion follows by the same target cases.

Effective rejection is separately proved. BUILD-MAP-C maps f and target W to the corresponding cfg predicates. In each exact release, cfg(all(...)) is true exactly when both options are set, and a false cfg removes its item; [1.84](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute), [1.85](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute), [1.86](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute). Each compile_error! page states that encountering it causes compilation to fail: [1.84](https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html), [1.85](https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html), [1.86](https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html). Therefore f∧t=W cannot yield this library. Required already excludes it; ¬f on W remains admitted and selects the safe implementation.

The only actual axes are v,t,f,h,p,d and edition 2021. Hardened, profiles, and debug assertions do not occur in executable expressions; there is no arithmetic, allocation, panic-dependent cleanup, FFI, concurrency, target layout, or target instruction. The proof is parametric over h,p,d and over X/A, and separately covers ¬f on W. Exact per-release axioms avoid any cross-version compatibility premise. Aggregate Covered equals Required, hence Required⊆Covered.

## Boundary, invariant, and obligation coverage

The sole language-reachable project API is the safe public function value_or_zero(Option<u8>)->u8. Mutually exclusive cfg attributes select exactly one definition. There are no public fields, constructors of project types, traits or impls, statics, callbacks, reexports, hidden items, FFI, or custom destruction. No persistent invariant-bearing representation exists.

A transient local fact, INV-SOME, is owned by the turbo function: after value.is_none() evaluates false, value is Some until immediately consumed. It is produced by the branch, never suspended or mutated, and consumed only by unwrap_unchecked.

| ID | Obligation and derivation | Domain | Status |
|---|---|---|---|
| O-CFG | Select exactly one implementation; reject f∧W. cfg axioms plus BUILD-MAP-C establish this. | all policy candidates | PROVED |
| O-SAFE | With ¬f, unwrap_or returns the Some payload or supplied default 0. | Required∧¬f | PROVED |
| O-GUARD | is_none returns true exactly for None; true returns 0, false establishes INV-SOME. Its receiver is &self, so the test does not consume or alter value. | Required∧f | PROVED |
| O-UNSAFE | unwrap_unchecked requires the value not be None. INV-SOME supplies that exact precondition; it returns the contained u8. | Required∧f | PROVED |
| O-POST | Combining None/Some branches establishes the published function postcondition. | Required | PROVED |

For every release, the Option documentation says is_none “Returns true if the option is a None value,” unwrap_unchecked says calling it on None is undefined behavior, and unwrap_or returns the Some value or the default: [1.84 is_none](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none), [unchecked](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked), [unwrap_or](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or); [1.85 is_none](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.is_none), [unchecked](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked), [unwrap_or](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or); [1.86 is_none](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.is_none), [unchecked](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked), [unwrap_or](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or). The adjacent SAFETY comment states the dominating None return and Some conclusion; the full material derivation is O-GUARD/O-UNSAFE.

## TCB audit log

Log identity: supplied TCB.md for this exact snapshot. Trust policy: Rust Reference/std text is authoritative for its exact release; the only admitted non-authoritative premise is the conspicuous human decision BUILD-MAP-C.

| ID | Category/disposition | Exact proposition; consumers; trigger |
|---|---|---|
| BUILD-MAP-C | BUILD-TOOL, accepted | Exact Cargo feature-to-cfg and named-target-to-target_arch mappings for V, supplied manifest/source, and every supported profile; consumed only by O-CFG. It admits no Rust semantics, branch correctness, other versions, or backend correctness. Trigger: any identity, manifest/source cfg, feature/target, profile scope, or disposition change. |
| AX-OPTION-v | AXIOM, verified | Exact is_none, unwrap_unchecked, and unwrap_or propositions linked above for each v∈V; consumed by O-SAFE/O-GUARD/O-UNSAFE/O-POST. Trigger: relevant versioned documentation change. |
| AX-CFG-v | AXIOM, verified | Exact configuration-predicate/cfg-attribute rules ([1.84](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#conditional-compilation), [1.85](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#conditional-compilation), [1.86](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#conditional-compilation)) and compile_error! behavior; consumed by O-CFG. Trigger: relevant documentation change. |

No safe/unsafe dependency, implementation, external, deployment, probabilistic, or tool premise is consumed. No tool-derived evidence was used.

## Findings, residual scope, and attestation

No UNSOUND, UNPROVED, CONTRACT-BROKEN, Rust-documentation-gap, or proof-documentation finding remains. The policy conflict itself remains unresolved; only the explicitly conservative union was audited. Configurations outside S∨I are not certified, although f∧W rejection is established. Build success beyond the stated source/configuration facts and all backend/binary behavior are excluded.

Re-audit on source, manifest, either policy, TCB disposition, supported version/target/feature/profile/debug domain, or consumed authoritative text changing. Every in-scope surface, contract clause, unsafe operation, domain transformation, and TCB consumer has a disposition; no testing or absence-of-counterexample premise supports the verdict.

