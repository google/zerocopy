# R2C2 (arXiv:2611.18036v1): LLVM-IR-level C-to-Rust refinement validation with CRIS, its `undef` rewriting and source-versus-IR UB boundaries, and consequences for MIR-to-LLVM-IR translation validation

## Summary

R2C2 (Eunsu Kim, Sukyoung Ryu, Jaemin Hong; arXiv:2611.18036v1) validates a C-to-Rust translation by compiling both programs to LLVM IR and proving, in Rocq 9.0 on top of the CRIS refinement framework and Interaction Trees, that the Rust IR *refines* the C IR: every trace of the Rust program is a trace of the C program. The proof is a chain of four refinement steps. Three steps (inlining, uninlining, wrapper cancellation) are proved once for all programs; only the second step, a simulation between two modules whose library calls have been inlined, is program specific. That one obligation is discharged by an LLM agent and checked by the Rocq kernel. The paper reports 486 of 519 benchmark translations proved without bounding executions, 26 counterexamples, and 7 failures on unsupported features; its abstract reports three incorrect translations discovered with valid counterexamples.

The points worth retaining for anyone building a translation validator for `rustc` (MIR to LLVM IR) or reusing this architecture:

1. **Direction decides soundness.** A check `T' ⊑ S'` on models of the target `T` and the source `S` establishes `T ⊑ S` when the target model has *at least* the target's behaviors (`T ⊑ T'`) and the source model has *at most* the source's behaviors (`S' ⊑ S`); neither condition can be dropped in general. Every modelling shortcut must be classified by the side it is applied to. This is mechanized here as `model_refinement_transfer`.

2. **R2C2's two `undef` rewrites both go in the unsound direction, and the paper says so.** Its semantics has `poison` but no `undef`; after compilation it rewrites `undef` to `poison` in the C IR (the source) and to zero or `null` in the Rust IR (the target). The paper states that this "may add behaviors to the C program and remove behaviors from the Rust program, making the refinement easier to establish" and that validation "remains sound in most cases, assuming that the translation uses only safe Rust". The *mirror image* (target `undef` to `poison`, source `undef` to a fixed value) is sound, and rewriting `undef` to an explicit per-use choice is exact; both facts are mechanized here.

3. **How much `undef` actually reaches the IR is narrower than one might expect, but not empty.** With clang 22.1.4 at `-O1`, eleven C shapes in which indeterminate bits share an integer with initialized bits (bit-field stores, coerced structs, a union pun) emitted *no* `undef`: LLVM had already resolved the indeterminate bits to zero. A literal `undef` survived (a) as a whole unwritten struct member returned in its own register, and (b) in one shape where a possibly unwritten bit-field storage unit reaches two different masks through a `phi`. For (b), LLVM's own constant folder turns the zero-trip path into a value whose bit 0 is still the argument bit when `undef` is kept, and into `ret i64 poison` after the textual `undef` to `poison` rewrite. On the Rust side, entirely safe code returning `(MaybeUninit<i32>, i32)` emits `insertvalue { i32, i32 } undef, …` with rustc 1.98.0-nightly; the zero rewrite turns the uninitialized component from `undef` into the constant `0`.

4. **Upstream Vellvm at the examined commit itself denotes `undef` as `poison`, and does enforce `noundef`.** `EXP_Undef` "is denoted semantically as [poison]", and call, invoke and function-entry denotations raise undefined behavior on a violated `noundef`. Whether R2C2's own "Vellvm-based" semantics enforces parameter attributes could not be determined from the text examined.

5. **Validating against compiled source IR is sound but incomplete for source-level correctness.** Clang lowers an `int` variable-length-array bound with a plain `zext`, with the source comment "Always zexting here would be wrong if it weren't undefined behavior to have a negative bound" (present at both 21.1.8 and 22.1.4). The source-level undefined behavior of a negative bound becomes a defined huge allocation in IR, while the idiomatic Rust `(n + 1) as usize` sign-extends and reaches the allocation-error path. The Rust output then refines the C *source* but not the C *IR*.

6. **`-Cpanic=abort` removes unwinding code only for code that cannot call unwinding foreign functions.** A safe-Rust-only module had no `invoke`; a call to an `extern "C-unwind"` function is an `invoke` with a `landingpad` that runs pending drops and then calls `panic_cannot_unwind`, with or without a `Drop` guard.

7. **A Lean environment audit must scan the right stage of the constant map.** With Lean 4.34.1, declarations of the file being checked live in `env.constants.map₂`; `map₁` holds imported constants only. Compiled structurally recursive definitions, including `Prop`-valued ones, came with `unsafe` helpers named `<name>._unsafe_rec`; marking the definitions `noncomputable` removed them.

Two limits qualify everything said about the paper. Only a comment-stripped extract of the LaTeX source was examined, and 8 of its 15 files were cut at 6,500 characters; statements that depend on the missing text are marked unknown. The R2C2 implementation was not examined or run, and the compilers executed here (clang 22.1.4, rustc 1.98.0-nightly) are not the paper's (Clang 21.1.8, rustc 1.93.1).

## Applicability

### Subjects and how they relate

- **The paper** (arXiv:2611.18036v1) is the system under study. No immutable artifact identity beyond the arXiv version exists for it here; the implementation it describes was not available. What was examined is described under Evidence.
- **Vellvm** at `7f0610c38d829b79bf6e867edf410c9e6f928f98` and **Interaction Trees** at `284d42248a3c5517cff9f582e335fcee2f6bdc1f` are the upstream libraries the paper names as the basis of its LLVM IR semantics and of its program representation. Both commits were the default-branch heads on the observation date. The paper cites Vellvm by publication, not by revision, and describes "our Vellvm-based LLVM IR semantics"; which Vellvm revision R2C2 builds on, and how far its semantics departs from it, is **unknown**. Findings about Vellvm are findings about this upstream commit, not about R2C2.
- **LLVM/Clang 22.1.4** (`35990504507d79e0b9deb809c8ee5e1b34ceef20`) supplied the `clang` that was executed, the Language Reference that was read, and one Clang source file. **Clang 21.1.8** (`2078da43e25a4623cab2d0d60decddf709aaea28`), the paper's Clang version, was read for the same source file only; it was not executed.
- **rustc 1.98.0-nightly** (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, bundled LLVM 22.1.6) was executed, together with the `opt` shipped in the same toolchain's LLVM tools (reported as `LLVM version 22.1.6-rust-1.98.0-nightly`). **rustc 1.93.1** (`01f6ddf7588f42ae2d7eb0a2f21d44e8e96674cf`), the paper's rustc version, was read for its command-line gating code only; it was not executed.
- **Anneal** at `c131b320eeeb26ef692e5afd5ec8db49ee518613` is a Lean development with a trusted MIR semantics and a kernel-environment audit. It is examined for one seam only: how a MIR-level semantics represents uninitialized storage and unmodelled constructs, which is what a MIR-to-LLVM-IR validator would have to relate to `undef` and `poison`.
- **Lean 4 v4.34.1** (`5045d0056413266e57c625dcd7c365b10e377c52`) checked the accompanying model. The same Lean commit is the one Anneal's audit file pins.

### Configuration of the executions

All compiler observations are for `x86_64-unknown-linux-gnu`.

- C: `clang -std=gnu11 -O1 -fno-unroll-loops -fno-vectorize -fno-slp-vectorize -ffp-contract=off -S -emit-llvm`.
- Rust: `rustc --edition=2021 -Copt-level=1 -Zinline-mir=no -Cno-vectorize-loops -Cno-vectorize-slp -Cllvm-args=--unroll-threshold=0 --emit=llvm-ir`, with `-Cpanic=abort` unless a comparison with `-Cpanic=unwind` is stated.

These are the flags the paper's compilation-settings appendix names that matter for the probes. Not applied: the further unrolling options the appendix refers to only as "and others", `-disable-loop-idiom-vectorize-all`, `-disable-vector-combine`, the `-force-attribute` options that add `noinline` to library functions with specifications, `-D__NO_CTYPE`, and `-fno-builtin-`*f*.

### What extends beyond the exact observations, and why

- The directional rule and the statements about the `undef` rewrites (points 1 and 2 of the Summary) are properties of refinement as set inclusion and of the Language Reference's rule that `poison` may be replaced by `undef` or by any value but not conversely. They do not depend on a compiler version.
- Which C and Rust shapes leave a literal `undef` in `-O1` output is a property of the optimizer pipeline and **does not** extend beyond clang 22.1.4 and rustc 1.98.0-nightly without rerunning the probe. In particular it was not established for Clang 21.1.8 or rustc 1.93.1.
- The variable-length-array lowering is established for Clang 21.1.8 by source (the same four lines exist there) and for 22.1.4 by source and execution.
- The model in `support/CrisRefinementChainAndUndefHazardSoundness.lean` is an abstract model written for this report. It applies to the definitions it contains. It is evidence for the *reasoning* in this report, not for the correctness of CRIS, Vellvm, R2C2 or Anneal.

## Findings

### 1. What R2C2 proves, and in what terms

Basis: documentation (the paper), quoted from the examined extract.

**Correctness statement.** The paper "validates C-to-Rust translation by proving in Rocq that the Rust program *refines* the C program, i.e., every behavior on the Rust side is also a behavior on the C side", and because "no formal semantics defines the behaviors of C and Rust programs in the same terms", it proves "refinement between the two programs compiled to the LLVM intermediate representation". Scope is one public function per program.

**Programs are interaction trees over CRIS events.** An interaction tree is `Ret r`, `Tau T`, or `Vis ev k`. The event signature is

```text
E ::= Call(f, v) | IO(f, v) | Choose X | UB | NB
    | Take X | Assume Q | Guarantee Q          (imaginary operations)
```

A module maps function names to bodies (`Mod ≜ Fname ⇀ (Any → itree E Any)`); "calling a function not in the module causes UB"; linking is union (`M1 ⋆ M2 ≜ M1 ∪ M2`); a program is a module with a designated entry, and its denotation replaces every `Call` by the callee's body.

**Behaviors are trace sets.** A trace is a sequence of `Interact (f, a, r)` items ending in `Done v`. The paper's definition of `Beh` by cases:

```text
Ret v                 { Done v }
Tau T'                Beh(T')
Vis IO(f, a) k        union over r of  Interact (f, a, r) :: Beh(k r)
Vis (Choose X) k      union over x in X of Beh(k x)
Vis UB k              every trace
Vis NB k              no trace
Vis (Take X) k        intersection over x in X of Beh(k x)
Vis (Assume Q) k      if Q then Beh(k ()) else every trace
Vis (Guarantee Q) k   if Q then Beh(k ()) else no trace
```

`M ⊑beh M'` is `Beh(⟦M⟧) ⊆ Beh(⟦M'⟧)`. Two qualifications are in a footnote: the actual CRIS definition "also runs the two programs with ghost resources: M with the empty resource and M′ with some valid initial resource", and "We also omit traces not ending with Done, such as divergence and abort."

**Drivers make the two sides comparable.** Each LLVM IR function `F_X` (X is C or Rust) is wrapped in a driver that is the program entry:

```text
driver(F_X) ≜ λ_.
  v ← trigger IO("input", ());
  if ¬ valid_input_F(v) then Ret None
  else (p, m) ← register_{F,X}(v, m0);
       (r, m') ← ⟦F_X⟧(args_{F,X}(v, p), m);
       o ← observe(r);  o' ← observe(read_{F,X}(p, m'));
       Ret (Some (o, o'))
```

The input is a list of abstract values received through an `IO` event (so it is recorded in the trace); `register` lays it out in the language's representation; `read` reads pointer-argument memory back as abstract values. Outputs pass through `observe`:

```text
observe(v) ≜ trigger Choose { x | x ⊑ v ∧ x ≠ poison }
```

with value refinement defined as: "v refines v′ … if v = v′, or if v′ is `poison` and v has the same type; aggregate values, including abstract values such as lists, are compared element-wise." The stated purpose: "when an LLVM IR function compiled from C produces `poison`, a function compiled from Rust should be considered to refine it regardless of the value it produces." This definition is what makes a source-side `poison` result vacuously refinable (Finding 4).

**Common abstractions.** Data representations differ (a C variable-length array is a pointer to elements; a Rust `Vec` is a header holding capacity, buffer address and length, annotated in the paper's running example as "Vec offsets {cap: 0, ptr: 8, len: 16}" and allocated as `[24 x i8]`). The paper relates them with ghost resources: a points-to assertion carrying a right ("the full right … allows writing, and a smaller right allows only reading"), a memory authority `Auth(m)` per side ("The C and Rust programs run on separate memories, each with its own authority"), representation predicates, and a *representation pair* stating that a C object represents `v_c` and a Rust object represents some `v_r ⊑ v_c`. The supported abstractions, verbatim from the paper's table:

| Common abstraction (abstract value) | C representation | Rust representation |
| :--- | :--- | :--- |
| List (list of elements) | `T*` with a length, `T[n]`, VLA | `&[T]`, `&mut [T]`, `[T; n]`, `Vec<T>` |
| String (list of ASCII bytes) | NUL-terminated `char*` | `&str`, `Vec<char>` |
| Struct (record of fields) | `struct` (non-recursive) | `struct` (non-recursive) |
| Table (list of lists) | two-dimensional VLA | `Vec<Vec<T>>` |
| File (file state) | `FILE*` | `File` |

**Library modules.** Three modules model callees: `lib_LLVM`, `lib_C` and `W_fun(lib_Rust)`. The implementation section counts "29 LLVM intrinsics, 25 C library functions, and 49 Rust library functions"; for Rust `Vec` and slices "the supported element types are `i32`, `u32`, `i64`, `u64`, `u8`, `bool`, and `char`, as well as nested `Vec` for two-dimensional arrays."

### 2. The four-step chain and where the one obligation sits

Basis: documentation (the paper) for the statements; derived plus the Lean model for the composition and for the mechanisms.

**Wrappers.** "`Guarantee(P)` provides resources satisfying P, and `Assume(P)` receives them; if `Assume` cannot receive the required resources, it triggers UB, and if `Guarantee` cannot provide them, it triggers NB." `W_fun(M)` "inserts `Take` and `Assume` for the precondition at the start of each function in M and `Choose` and `Guarantee` for the postcondition at its end"; `W_call(M)` "inserts, around each function call in M, `Choose` and `Guarantee` for the callee's precondition before the call and `Take` and `Assume` for the postcondition after it." Functions without a specification get no imaginary operations.

**The chain**, as displayed in the paper (`⊑ctx` is contextual, `⊑beh` behavioral refinement):

```text
  program(F_Rust, W_fun(lib_Rust))
=    main(F_Rust) ⋆ W_fun(lib_Rust) ⋆ lib_LLVM
⊑ctx Hide(main(F_Rust), W_fun(lib_Rust) ⋆ lib_LLVM)                    (1) inlining
⊑ctx Hide(W_fun(W_call(main(F_C))), W_fun(lib_C) ⋆ lib_LLVM)           (2) simulation
⊑beh W_fun(W_call(main(F_C))) ⋆ W_fun(lib_C) ⋆ lib_LLVM                (3) uninlining
⊑beh main(F_C) ⋆ lib_C ⋆ lib_LLVM                                      (4) cancellation
=    program(F_C, lib_C)
```

- `Hide(M, L)` "keeps only functions from M, replacing any `Call` event to a function from L with the body of that function." Inlining is needed "because C and Rust library functions may differ in their signatures, preventing corresponding `Call` events from being matched in simulation."
- Lemma (Inlining and Uninlining): (i) `M ⋆ L ⊑ctx Hide(M, L)`; (ii) "If M defines an entry and L does not, then `Hide(M, L) ⊑beh M ⋆ L`", with the footnoted extra requirement "that L maintains no state and no function spawns a function in L." The proof sketch of (i): "if a context calls a function in L, the call triggers UB in Hide(M, L), which allows every behavior."
- Step 4 uses "the cancellation theorem of CRIS, which states that `W_fun(W_call(M)) ⊑beh M` if M defines an entry and the precondition of the entry holds at the start", because "`Guarantee` of a caller, inserted by `W_call`, matches `Assume` of the callee, inserted by `W_fun`, and vice versa." The entry precondition "requires the authorities of the two initial memories".
- The asymmetry of wrapping is deliberate: "`main(F_C)` is wrapped, but `main(F_Rust)` is not, because simulation in CRIS provides initial resources to the source (the C side) but not to the target (the Rust side) of the refinement." Note that the *target program itself* is defined with `W_fun(lib_Rust)`: the Rust library enters the correctness statement through its specification wrapper.

**The obligation.** Step 2 is proved through CRIS's adequacy theorem by a relational triple, the only per-program proof:

```text
{ Auth(m_c) ∗ Auth(m_r) ∗ pair^1(a_c : R_c, a_r : R_r)(v) }
   ⟦F_Rust⟧(args_Rust(v, a_r), m_r)  ≲  ⟦F_C⟧(args_C(v, a_c), m_c)
{ λ (r_r, m_r') (r_c, m_c'). Auth(m_c') ∗ Auth(m_r') ∗ ∃ v'. pair(…)(v') ∗ ⌜r_r ⊑ r_c⌝ }
```

Representative rules are `Reduce-C` / `Reduce-Rust` (run event-free code on one side) and `Call-C` / `Call-Rust` (run a library call on one side by its specification, requiring that the library function returns without `IO` events). The rules are usable despite inlining because "ITrees are coinductively defined and their unfolding is lazy".

**What the composition does and does not buy (derived; mechanized).** `cris_four_step_chain_sound` in the accompanying model states the reduction abstractly: given transitivity of `⊑beh`, `⊑ctx ⇒ ⊑beh`, and the three program-independent laws with their side conditions, the refinement of the linked target by the linked source follows from the single simulation hypothesis. It is a composition theorem over an abstract structure of laws (`ChainLaws`); it does not prove those laws for CRIS. The model additionally proves the two *mechanisms* in a concrete finite-tree semantics that follows the `Beh` table above:

- `guarantee_assume_cancel`: a `Guarantee Q` followed by `Assume Q` adds no behavior; `wrapper_cancellation_at_call`: at one call boundary, the caller-side `Choose`/`Guarantee`/…/`Assume` composed with the callee-side `Take`/`Assume`/…/`Guarantee` refines the bare call. The proof instantiates the callee's `Take` with the caller's chosen ghost value, which is exactly the "matches" remark quoted above.
- `inlining_refines_hide`: for a layered, non-recursive setting (a context calls `M`, `M` calls `L`), linking the context with `M` and `L` refines linking it with `Hide(M, L)`, the unresolved-call-is-UB case carrying the proof as in the paper's sketch. `uninlining_layered` is an equality of programs in that fragment.
- `guarantee_unmet_refines_anything` and `wrappedCall_unsatisfiable_pre_is_nb`: a `Guarantee` that cannot be met has *no* behavior and therefore refines everything. A target containing one would be validated vacuously; this is the formal reason the direction in which wrappers are inserted is part of the trusted statement, not a proof detail.

### 3. The directional rule

Basis: derived; mechanized as `model_refinement_transfer`.

Let `T`, `S` be the real target and source behaviors and `T'`, `S'` what the checker reasons about. Then

```text
T ⊑ T'   and   S' ⊑ S   and   T' ⊑ S'      imply      T ⊑ S.
```

Neither premise can be dropped: the counterexamples of Findings 4, 5 and 8 each break one of them. Classifying the modelling decisions met in this report:

| Decision | Side | Effect on that side's behaviors | Sound? |
| :--- | :--- | :--- | :--- |
| rewrite `undef` to `poison` | source | adds | **no** (Finding 4) |
| rewrite `undef` to `poison` | target | adds | yes, possibly incomplete |
| rewrite `undef` to zero / `null` | target | removes | **no** (Finding 5) |
| rewrite `undef` to zero / `null` | source | removes | yes, possibly incomplete |
| rewrite `undef` to a fresh choice per use | either | none | yes, exact |
| freeze `undef` once and share the value | source | removes | yes |
| freeze `undef` once and share the value | target | removes | **no** (Finding 6) |
| ignore an attribute whose violation is UB (`noundef`, `mustprogress`) | source | removes | yes |
| ignore such an attribute | target | removes | **no** (Finding 8) |
| compare against compiled source IR instead of the source | source | removes (compiler refined UB away) | yes, but incomplete (Finding 7) |
| treat a call to an unmodelled function as UB | source | adds | **no**; such a source must be rejected instead |
| treat a call to an unmodelled function as UB | target | adds | yes |

For a C-to-Rust validator the source is C and the target is Rust. For a `rustc` validator the source is MIR and the target is the emitted LLVM IR, so every LLVM-side shortcut is a *target-side* shortcut: it must only add behaviors.

### 4. `undef` on the source side: the paper's rule, upstream Vellvm, and what clang emits

**The rule and the paper's own qualification.** Basis: documentation (the paper).

The background section says: "The LLVM community is working to remove `undef` from LLVM IR entirely, so our semantics only includes `poison` and excludes `undef`; since current compilers may still produce IR with `undef`, we eliminate `undef` from compiled IR". The compilation paragraph of the automation section gives the rule and its justification in full:

> After compilation, since our LLVM IR semantics does not support `undef`, we replace `undef` in the C-side LLVM IR with `poison` and `undef` in the Rust-side LLVM IR with zero or `null`, depending on the value's type. This conversion may add behaviors to the C program and remove behaviors from the Rust program, making the refinement easier to establish. However, the validation remains sound in most cases, assuming that the translation uses only safe Rust. In the C-side IR, `undef` is either never read or represents the value of an uninitialized variable, whose read is already UB in the C source. In the Rust-side IR, `undef` is never read if the compiler is correct, since safe Rust never reads a value before initializing it.

So the paper does not claim unconditional soundness for this step. The remaining question is how large "most cases" is, i.e. whether the stated dichotomy for C (never read, or a read that is already source-level UB) is exhaustive.

**Why the direction is the unsound one.** Basis: normative (LLVM Language Reference at 22.1.4) + derived.

The Language Reference says of poison: "Most instructions return '`poison`' when one of their arguments is '`poison`'" and "It is correct to replace a poison value with an undef value or any value of the type." The converse replacement is not licensed: `undef` "indicates that the user of the value may receive an unspecified bit-pattern", so `and i8 undef, -2` has a result whose bit 0 is 0, whereas the reference's own example reads `%still_poison = and i32 %poison, 0 ; 0, but also poison.` Rewriting `undef` to `poison` therefore replaces a value by a *less defined* one, which adds behaviors; on the source side of a refinement that is the unsound direction of Finding 3. The model proves the general statement (`subst_poison_adds_behaviors`: for every expression over `and`/`or`, the observed result set only grows) and a concrete failure (`ce1_c_bitfield_undef_to_poison_vacuous_refinement`): for the store `(old & 0b10) | arg` with `old = undef`, every result has bit 0 equal to the argument bit, a translation that always returns zero is rejected at the argument with bit 0 set, and after the rewrite the same wrong translation is accepted for *every* argument because the source result is `poison` and `observe(poison)` contains every value.

**Upstream Vellvm at the examined commit makes the same identification.** Basis: source.

At `vellvm/vellvm@7f0610c38d829b79bf6e867edf410c9e6f928f98`:

- `src/rocq/Syntax/LLVMAst.v`, lines 515–519: "[undef] is still accepted by the parser, but the minimal semantics has no dedicated undef value: [EXP_Undef] is denoted semantically as [poison] (see [denote_exp] in Semantics/Denotation.v)", followed by the constructors `EXP_Undef` and `EXP_Poison`.
- `src/rocq/Semantics/Denotation.v`, lines 258–266: the single case `| EXP_Undef | EXP_Poison =>` returns `poison_of_dtyp t`.
- `tests/undef/README.md` states that `undef` "is treated **semantically as `poison`**" and records a consequence: `%agg1 = insertvalue {i32, float} undef, i32 1, 0` now hits an error case, where "Under the old `undef` semantics, `undef` was a real aggregate placeholder and these assertions held."
- `src/rocq/Semantics/LLVMEvents.v`, lines 100–104: nondeterminism is kept only for `freeze`, through an event `Draw (dt : dtyp) : DrawE dvalue` described as "An event resolving the non-determinism of [freeze]: an arbitrary value of type [dt]".

For a tool that uses this semantics for a *target* program the identification is the sound direction; for a *source* program it is not. This is a statement about upstream Vellvm at this commit. Whether R2C2 inherits it or implements its textual rewrite independently is unknown.

**What clang 22.1.4 actually emits at `-O1`.** Basis: execution (`support/probe_r2c2_cris_llvm_ir_and_undef_hazards.py`, results in `support/probe_results.json`, emitted module in `support/ir/c_uninit.clang.O1.ll`). A standalone `undef` token is counted with a tokenizer that does not match `noundef`; a substring test would report `undef` in nearly every function because of the `noundef` attribute.

*Shapes with no `undef` in the output* (0 standalone `undef` tokens each). In all of them indeterminate bits share one SSA integer with initialized bits and meet a single mask or extension, and LLVM has already resolved the indeterminate bits to zero:

| Function | C shape | What the IR returns |
| :--- | :--- | :--- |
| `bf_read_back` | `struct S s; s.a = x & 1; return s.a;` | `and i32 %0, 1` |
| `bf_return_whole` | same store, `return s;` | `and i32 %0, 1` |
| `bf_loop_then_set` | countable loop writes `s.b`, then `s.a = x & 1` | `select i1 %3, i32 %6, i32 0` OR-ed with the bit |
| `bf_switch_then_set` | three-case `switch` writes `s.b`, default leaves it unwritten | `phi i32 [ 0, %2 ], [ %8, %5 ]` OR-ed with the bit |
| `bf_loop_ext` | loop with opaque trip count writes `s.b` | `phi i8 [ 0, %1 ], [ %9, %8 ]` OR-ed with the bit |
| `plain_loop` | two-`char` struct, second byte possibly unwritten | `phi i16 [ 0, %1 ], [ %10, %8 ]` OR-ed with the byte |
| `pun` | `union { int i; char c; }`, write `c`, read `i` | `zext i8 %0 to i32` |
| `partial_coerced`, `arr_part`, `fi` | struct or array coerced into one register, one part unwritten | `zext`, or `zext` then `shl` |
| `two_copies` | possibly unwritten byte copied into two results | `phi i32 [ 0, %2 ], [ %10, %9 ]`, shifted twice |

For these shapes the rewrite has nothing to rewrite. A plain bit-field store into an uninitialized local is therefore **not** an instance of the hazard with this compiler.

*Shapes where a whole member is `undef`.* An entirely unwritten struct member that is returned in its own register stays a literal `undef`:

```llvm
; struct P { long tag; long val; };  struct P partial_pair(long t) { struct P p; p.tag = t; return p; }
define dso_local { i64, i64 } @partial_pair(i64 noundef %0) local_unnamed_addr #0 {
  %2 = insertvalue { i64, i64 } poison, i64 %0, 0
  %3 = insertvalue { i64, i64 } %2, i64 undef, 1
  ret { i64, i64 } %3
}
```

The same holds for `dd` (`double undef`), `li` (`{ i64 undef, i32 poison }`) and `pair_loop` (`phi i64 [ %9, %8 ], [ undef, %1 ]`). Here the rewrite makes exactly that member `poison`, and under the paper's element-wise value refinement only that member becomes unconstrained. This matches the paper's description "represents the value of an uninitialized variable". Whether returning such a struct by value is "already UB in the C source", as the paper's sentence continues, was not checked against the C standard (see Boundaries); the emitted IR does not mark the return value `noundef`.

*The shape where `undef` meets defined bits.* When a possibly unwritten bit-field storage unit is copied and the two copies then receive stores to *different* bit-fields, LLVM cannot fold the masks into the `phi`:

```c
struct S3 { unsigned a : 1; unsigned b : 3; unsigned c : 4; };
struct Two { struct S3 x; struct S3 y; };
struct Two two_masks(int x) {
  struct S3 s, s2; struct Two r;
  (void)&s;
  while (cond()) s.b = next();
  s2 = s;
  s.a = x & 1;
  s2.c = 2;
  r.x = s; r.y = s2;
  return r;
}
```

```llvm
11:
  %12 = phi i8 [ undef, %1 ], [ %10, %8 ]
  %13 = trunc i32 %0 to i8
  %14 = and i8 %13, 1
  %15 = and i8 %12, -2
  %16 = or disjoint i8 %15, %14
  %17 = and i8 %12, 15
  %18 = or disjoint i8 %17, 32
  ...
  ret i64 %22
```

On the path where the loop body never runs, `%12` is `undef`; bit 0 of `%16` is nevertheless `x & 1` and the high nibble of `%18` is `2`. Clang's own output records this: the function's return carries `range(i64 137438953472, 201863463168)`, i.e. the byte holding member `y` (bits 32–39 of the returned integer) lies in `[32, 47]` on every path.

To see what the textual rewrite does to this function, the probe defines `cond` to return 0, and runs LLVM's `opt` with the explicit pipeline `cgscc(inline),function(simplifycfg,instsimplify)` on the original module and on the module after `undef` to `poison`:

```llvm
; original (undef kept)
define dso_local range(i64 137438953472, 201863463168) i64 @two_masks(i32 noundef %0) local_unnamed_addr #1 {
  %2 = trunc i32 %0 to i8
  %3 = and i8 %2, 1
  %4 = zext i8 %3 to i64
  %5 = or disjoint i64 137438953472, %4
  ret i64 %5
}

; after the textual rewrite undef -> poison (1 substitution in the function)
define dso_local range(i64 137438953472, 201863463168) i64 @two_masks(i32 noundef %0) local_unnamed_addr #1 {
  ret i64 poison
}
```

The rewritten source function returns `poison` on that path; under the paper's `observe`, every Rust return value is then an acceptable refinement on inputs that take it, including one whose bit 0 differs from `x & 1`.

Three cautions bound this result. (1) It is a statement about the IR and about the rewrite as described in prose; whether R2C2 would accept this function at all (bit-fields, a by-value struct return, a loop over calls to functions without a library model) is unknown. (2) Whether `two_masks` is free of undefined behavior at the C source level on the zero-trip path depends on the C standard's rules for copying an object with indeterminate value, which were not consulted. (3) An optimizer run is not an oracle for "this value is poison": the full `default<O1>` pipeline, applied to the rewritten module, returned the same bit-preserving function as for the original, because an optimizer may refine `poison` to any value. Only the explicit constant-folding pipeline exhibits the difference.

### 5. `undef` on the target side: safe Rust can return it

Basis: execution; documentation (the paper) for the rule; derived for the consequence.

The paper's justification for rewriting Rust-side `undef` to zero or `null` is that "`undef` is never read if the compiler is correct, since safe Rust never reads a value before initializing it." Safe Rust cannot *read* an uninitialized value, but it can *return* one, and the validation driver observes return values at the IR level. With rustc 1.98.0-nightly and the flags above:

```rust
// entirely safe Rust
pub fn uninit_pair(x: i32) -> (MaybeUninit<i32>, i32) { (MaybeUninit::uninit(), x) }
```

```llvm
define { i32, i32 } @uninit_pair(i32 noundef %x) unnamed_addr #0 {
start:
  %0 = insertvalue { i32, i32 } undef, i32 %x, 1
  ret { i32, i32 } %0
}
```

The probe extracts component 0 through a wrapper and folds with `cgscc(inline),function(instcombine)` (`instsimplify` alone does not forward an `extractvalue` through an `insertvalue` at another index): the original gives `ret i32 undef`; after the rewrite of the aggregate `undef` to `zeroinitializer` it gives `ret i32 0`. The target model's set of possible results for that component shrinks from every value to `{0}`, the unsound direction on the target side. `ce2_rust_undef_to_zero_misses_nonzero_choice` is the corresponding statement in the model: a target returning `undef` is accepted against a source returning zero after the rewrite, and rejected without it.

How much this matters for R2C2 as evaluated is limited by its supported types: the supported `Vec` and slice element types are integer, `bool` and `char`, and the Struct abstraction is described only as a non-recursive record of fields. Whether a `MaybeUninit` field can occur in a supported return type is unknown. The other safe-Rust shapes probed emitted no `undef`: a `#[repr(C)]` struct with interior padding is built on `poison` (`insertvalue { i8, i32 } poison, i8 %x, 0`), `Option<u32>` returns the payload argument in both variants, and a two-variant enum is packed with `zext` and `shl`.

For a `rustc` validator the lesson is direct: the validator exists because the compiler is *not* assumed correct, and unsafe code is in scope, so "never read if the compiler is correct" is not an available premise. Target-side `undef` must be modelled as `poison` (sound, may reject) or as a per-use choice (exact), never as zero.

### 6. Per-use `undef` versus one frozen value

Basis: normative (Language Reference) + derived; mechanized.

`undef` may yield a different bit pattern at each use, so replacing it with *one* chosen value shared by all uses removes behaviors: `xor %r, %r` can be non-zero when `%r` is `undef` and is always zero when `%r` is a single frozen value. In the model, `shared_choice_refines_per_use` shows the shared-value behaviors are a subset and `per_use_undef_strictly_more` shows the subset is strict. Consequently "freeze once and share" is a valid *source-side* approximation only; a target must be modelled with a fresh choice per use. `freeze_undef_set_refinement` proves that the per-occurrence rewrite of `undef` to an explicit choice is exact for the model's expression language: checking refinement after the rewrite on both sides is equivalent to checking it before. The expression language is a tree, so each occurrence is one use; a model with shared SSA names needs the per-use distinction made explicit.

### 7. Source-level UB that the C front end makes defined in IR

**Evaluation figures.** Basis: documentation (the paper).

"Of the 519 translations, R2C2 proves the correctness of 486, finds a counterexample for 26, and fails on 7". "The seven failures are due to unsupported features: four involve recursive structs, one involves an `Option<String>` return value, one involves the `mustprogress` LLVM IR attribute, which our LLVM IR semantics does not model, and one involves closures." The abstract reports that the tool "discovers three incorrect translations, providing valid counterexamples that existing translation validation tools cannot find". The benchmark is the VERT suite (504 programs from TransCoder-IR and 15 from prior C-to-Rust work), "13.3 LOC on average, with a maximum of 154 LOC". The QOI case study validated `qoi_read` and `qoi_write` of a 312-line reference implementation, taking 12.6 and 7.0 hours of agent time.

Derived: 26 − 3 = 23 counterexamples are not counted among the incorrect translations. The paper's own classification and explanation of those 23 lies in text that was not examined (see Boundaries). The counterexample figure in the examined text pairs these source fragments:

| C | Rust |
| :--- | :--- |
| `int n = strlen(s); int arr[n + 1];` | `let n = s.len() as i32; let mut arr = vec![0_i32; (n + 1) as usize];` |
| `buf->data = calloc(n + 1, 1);` (`n: size_t`) | `buf.data = vec![0; n.wrapping_add(1)];` |
| `bool subset[n + 1][sum + 1];` (`n, sum: int`) | `let subset = vec![vec![false; (sum + 1) as usize]; (n + 1) as usize];` |

The counterexample check is described as: "we run the two programs on the suggested input. If the C-side program incurs UB, the counterexample is invalid even when the outputs differ between C and Rust." The UB in question is UB of the *compiled C IR*; the mechanism below shows how that can differ from UB of the C source.

**The mechanism.** Basis: source (Clang) + execution.

Clang's lowering of a variable-length-array bound, `clang/lib/CodeGen/CodeGenFunction.cpp`, identical at `llvmorg-21.1.8` (lines 2567–2570) and `llvmorg-22.1.4` (lines 2577–2580):

```cpp
          // Always zexting here would be wrong if it weren't
          // undefined behavior to have a negative bound.
          // FIXME: What about when size's type is larger than size_t?
          entry = Builder.CreateIntCast(size, SizeTy, /*signed*/ false);
```

Observed output of clang 22.1.4 for `_Bool subset[n + 1][sum + 1]` and of rustc 1.98.0-nightly for the `vec!` translation:

```llvm
; C (support/ir/c_vla.clang.O1.ll)
  %3 = add nsw i32 %0, 1
  %4 = zext i32 %3 to i64
  %5 = add nsw i32 %1, 1
  %6 = zext i32 %5 to i64
  %7 = mul nuw i64 %6, %4
  %8 = alloca i8, i64 %7, align 16

; Rust
  %_6 = add i32 %sum, 1
  %_5 = sext i32 %_6 to i64
  call void @…RawVecInner…try_allocate_in(ptr … sret([24 x i8]) … %_16.i.i, i64 noundef %_5, i1 noundef zeroext true, i64 noundef 1, i64 noundef 1)
  …
  tail call void @…raw_vec…handle_error(i64 noundef %err.0.i.i, i64 %err.1.i.i)
  unreachable
```

(Mangled Rust callee names are abbreviated with `…`; the complete `vec1d` function is in `support/probe_results.json`.) The differences, per bound: C uses `add nsw` and a plain `zext` (not `sext`, and not `zext nneg`); Rust uses a flag-free wrapping `add` and `sext`.

Derived, input by input:

- `sum = -2` (bound `-1`). C source: Clang's comment treats a negative bound as undefined behavior. C IR: `add nsw` does not overflow, `zext` yields 4294967295, and under the Language Reference the `alloca` is an ordinary, defined, very large request (how R2C2's memory model treats a request of that size is unknown). Rust IR: `sext` yields 2^64 − 1, above the maximum allocation size, so the branch to `handle_error` seen in the IR is taken and, with `-Cpanic=abort`, the program aborts. These runs were reasoned from the IR, not executed. The Rust IR does not refine the C IR on this input, yet the Rust program refines the C *source*, which is undefined there. An IR-level validator reports a counterexample for a translation that is correct with respect to the source, unless the input restriction excludes the input. (R2C2 lets the user restrict each argument, for example to nonnegative or positive integers.)
- `sum = INT_MAX`. C IR: `add nsw` overflows and yields `poison`, which reaches the `alloca` size; the paper's `alloca` rule is "if n = `poison` then trigger UB". The C IR is undefined here too, so this input is *not* a false positive. The source-level overflow is preserved as IR-level `poison`, not turned into defined wrapping.

In the model, `ir_level_validation_sound` states the positive half (if the compiled IR refines the source and the target refines the IR, the target refines the source), `ce3_clang_ub_refinement_creates_false_positive` the negative half at bound `-1` using the concrete numbers 4294967295 and 18446744073709551615, and `all_three_agree_at_positive` that the three agree on a positive bound.

For a `rustc` validator the source is MIR, so this particular gap does not arise in the same form; its analogue is that emitted IR may be *more* defined than MIR, which is the allowed direction. The paper names validating at the source level, with separate semantics for the two languages, as future work.

### 8. Call-boundary attributes

Basis: normative (Language Reference) + source (Vellvm) + execution; documentation for the paper's statements; derived for the consequence.

**What the Language Reference requires** (`llvm/docs/LangRef.rst` at 22.1.4). `noundef`: "This attribute applies to parameters and return values. If the value representation contains any undefined or poison bits, the behavior is undefined." The poison section lists as immediate UB "The parameter operand of a call or invoke instruction, when the function or invoking call site has a `noundef` attribute in the corresponding position" and "The operand of a ret instruction if the function or invoking call site has a `noundef` attribute in the return value position." `mustprogress`: "If a `mustprogress` function does not satisfy this contract, the behavior is undefined."

**What rustc attaches.** Observed headers (rustc 1.98.0-nightly, `-Cpanic=abort`):

```llvm
define noundef i32 @takes_ref_and_bool(ptr noalias noundef readonly align 4 captures(none) dereferenceable(4) %r, i1 noundef zeroext %b, ptr noalias noundef align 8 captures(none) dereferenceable(8) %m) unnamed_addr #11 {
define void @slice_and_opt_string(ptr dead_on_unwind noalias noundef writable writeonly sret([24 x i8]) align 8 captures(none) dereferenceable(24) %_0, ptr noalias noundef nonnull readonly align 4 captures(none) %a.0, i64 noundef range(i64 0, 2305843009213693952) %a.1, i1 noundef zeroext %flag) unnamed_addr #6 {
```

Every parameter is `noundef`; references add `noalias`, `readonly`, `align` and `dereferenceable`; a slice length carries `range`; an `Option<String>` result is returned through an `sret([24 x i8])` slot. The token `mustprogress` occurred 25 times in that module and 13 times in the C module (attribute groups and the per-function attribute comments); the attribute groups that contain it also contain `willreturn`, for example `attributes #0 = { mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable … }` in the C module.

**What upstream Vellvm does with them.** At the examined commit the AST has `PARAMATTR_Sret`, `PARAMATTR_Noalias`, `PARAMATTR_Noundef` (`LLVMAst.v` lines 198, 201, 213) and `FNATTR_Mustprogress` (line 354). The denotation enforces `noundef`: `denote_call_args` evaluates each argument and passes it "through its call-site attributes ([apply_attrs]); [msg] reports a violated [noundef]" (`Denotation.v` lines 521–529), with messages "Call argument violates noundef." (line 630), "Invoke argument violates noundef." (line 772) and, on function entry, "Argument of … violates noundef." (line 996). The rule itself is in `src/rocq/Semantics/Attributes.v`: the comment at lines 122–130 reads "[nonnull], [align N], [range(a, b)], and [nofpclass] turn a violating value into poison … [noundef] makes a value that is not well defined immediate UB", and `apply_value_attrs` (lines 214–223) ends in `if existsb attr_is_noundef attrs && negb (dvalue_well_defined v) then raise_ub msg else ret v`; `apply_attrs` (lines 368–376) adds the memory check for `dereferenceable`. `noalias` and `mustprogress` are parsed but have no occurrence in `Attributes.v` or `Denotation.v`. `TERM_Invoke` and `TERM_Resume` are denoted (`Denotation.v` lines 771 and 795).

**What the paper says.** The syntax figure of its semantics appendix is captioned "A subset of the syntax of LLVM IR" and writes a call as `call(τ, e, list e)`, with no attribute position. `mustprogress` is the one attribute the examined text names as unmodelled, and the program involving it is counted as a *failure*, not as a proof. For `sret`, the case study says the pattern is recognized structurally: "Template generation recognizes this pattern by examining the return type and the number of parameters". Whether R2C2's semantics checks `noundef` is **unknown** from the examined text.

**Consequence (derived; mechanized).** Ignoring an attribute whose violation is UB removes behaviors from the side it is applied to (`stripped_le_faithful`). On the source side that is sound (`source_side_strip_is_sound`). On the target side it is not: `ce4_omitted_noundef_attr_misses_argument_poison_ub` exhibits a target that passes `poison` to a `noundef` parameter of a constant callee; with the attribute ignored the target has one defined result and is validated against a matching source, while the faithful target is undefined. For a `rustc` validator this is the important case, because the attributes are *added by the compiler under validation*: a wrongly emitted `noundef`, `noalias`, `dereferenceable` or `range` is precisely a miscompilation such a validator must be able to see. An unmodelled attribute on the target side must make validation fail, as R2C2's `mustprogress` case does, rather than be dropped.

Since `mustprogress` appears routinely in attribute groups of `-O1` output from both compilers used here, "does not model `mustprogress`" cannot mean "rejects any module in which the word occurs" under these toolchains; how R2C2 decides when the attribute matters was not determined.

### 9. Unwinding code under `-Cpanic=abort`

Basis: documentation (the paper) + execution; derived for scope.

The compilation appendix says: "For Rust, we make panics abort (`-Cpanic=abort`), so that the LLVM IR has no unwinding code." Observed with rustc 1.98.0-nightly:

| Module, panic strategy | `invoke` | `landingpad` | `resume` |
| :--- | ---: | ---: | ---: |
| safe Rust only (`vec!` allocation functions), `abort` | 0 | 0 | 0 |
| module with foreign calls, `abort` | 2 | 2 | 0 |
| same module, `unwind` | 8 | 6 | 4 |

So the statement holds for the safe-only module (9 of its 19 function definitions still carry `personality ptr @rust_eh_personality`, without any `invoke`). It does not hold once a function calls an `extern "C-unwind"` function. Under `-Cpanic=abort`:

```llvm
define noundef i32 @call_cunwind_with_guard(ptr noalias noundef align 4 captures(none) dereferenceable(4) %slot, i32 noundef %x) unnamed_addr #6 personality ptr @rust_eh_personality {
start:
  %_0 = invoke noundef i32 @foreign_may_unwind(i32 noundef %x)
          to label %bb1 unwind label %cleanup

cleanup:
  %0 = landingpad { ptr, i32 }
          cleanup
  %1 = load i32, ptr %slot, align 4
  %2 = add i32 %1, 1
  store i32 %2, ptr %slot, align 4
  tail call void @…core…panicking…panic_cannot_unwind()
  unreachable
…
```

(metadata and the comment line elided, the mangled callee name abbreviated; the full function is in `support/probe_results.json`). Per function under `abort`: the guarded and the unguarded `extern "C-unwind"` call each have one `invoke`, one `landingpad` and one call to `panic_cannot_unwind`; the guarded `extern "C"` call has none and is a plain `tail call`. A `Drop` guard is therefore not what introduces the `invoke`; it only adds work to the landing pad, which performs the guard's store *before* aborting. Under `unwind` the unguarded `extern "C-unwind"` call has no `invoke` (the exception simply propagates) and the guarded one has one.

Calling a foreign function requires `unsafe`, so this is outside the safe-Rust input class the paper's soundness remark assumes. It is inside the input class of a general `rustc` validator, which must either model `invoke`/`landingpad` (upstream Vellvm at the examined commit denotes `TERM_Invoke` and `TERM_Resume`) or reject functions that contain them.

### 10. `-Zinline-mir=no` and the stable channel

Basis: documentation (the paper) + source (rustc 1.93.1) + execution (rustc 1.98.0-nightly); derived for the conclusion.

The paper compiles "Rust programs with rustc 1.93.1" and says "For Rust, we also disable inlining at the MIR level (`-Zinline-mir=no`), which would otherwise inline library functions before LLVM sees this attribute." At `rust-lang/rust@01f6ddf7588f42ae2d7eb0a2f21d44e8e96674cf` (`src/version` reads `1.93.1`):

- `compiler/rustc_session/src/config.rs` line 1849 registers `opt(Unstable, Multi, "Z", "", "Set unstable / perma-unstable options", "<FLAG>")`; `nightly_options::check_nightly_options` (lines 2934–2984) reports "the option `{}` is only accepted on the nightly compiler" for a present unstable option unless `match_is_nightly_build` holds.
- `compiler/rustc_feature/src/lib.rs` lines 55–91: `UnstableFeatures::from_environment` returns `Cheat` when `RUSTC_BOOTSTRAP` is `1` or names the crate, `Disallow` when it is `-1`, and otherwise `Disallow` exactly when the compiler was built with `CFG_DISABLE_UNSTABLE_FEATURES`, which the source comments describe as "a feature-staged build, i.e., on the beta or stable channel".
- `compiler/rustc_session/src/options.rs` line 2404 declares `inline_mir: Option<bool>` among the `-Z` options.

Executed on 1.98.0-nightly: with `RUSTC_BOOTSTRAP=-1` the invocation with `-Zinline-mir=no` fails with ``error: the option `Z` is only accepted on the nightly compiler`` (exit status 1); without the variable it succeeds.

Derived: a stable-channel build of 1.93.1 accepts the paper's flag only with `RUSTC_BOOTSTRAP=1` (or the crate-name form). The examined text does not say how the flag was enabled. Anyone reproducing the paper's compilation settings on the released 1.93.1 needs that environment variable; this was not executed on 1.93.1.

### 11. The Lean model: what is checked

Basis: execution (Lean 4.34.1 kernel) of `support/CrisRefinementChainAndUndefHazardSoundness.lean`.

The file is 1,138 lines (1,007 non-blank) with 54 theorem statements, 37 definitions in the model namespace, 6 inductive types and 1 structure. It contains no `sorry`, no `omega`, no `bv_decide`, no `native_decide`, no `partial def`, no `deriving` clause and no use of the `Classical` namespace. It checks with warnings treated as errors, kernel type checking enabled, and prints:

```text
CrisModel constants in map₁ (imported): 0
CrisModel constants in map₂ (this file): 353
theorems: 133
_unsafe_rec constants: 0 []
unsafe or partial constants: 0 []
axioms used: [propext, Quot.sound]
disallowed axiom uses: 0
```

(`theorems: 133` counts theorem constants in the environment, which includes equation lemmas Lean generates for the recursive definitions; 54 are stated in the file.)

Contents, by part:

- **Trace sets and event trees.** `Prog` is an inductive tree with `ret`, `tau`, `io`, `choose`, `take`, `ub`, `nb`, `assume`, `guarantee` and `call`; `beh` follows the paper's table, rendering `Assume Q` as `Q → …` and `Guarantee Q` as `Q ∧ …` (equal to the paper's `if` for decidable `Q`). Theorems: `beh_bind_mono`, `bind_assoc`, `guarantee_assume_cancel`, `assume_weakens`, `guarantee_strengthens`, `assume_of_holds`, `guarantee_of_holds`, `guarantee_unmet_refines_anything`, `anything_refines_assume_unmet`, `wrapper_cancellation_at_call`, `wrappedCall_unsatisfiable_pre_is_nb`.
- **Modules and the chain.** `inline`, `hide`, `Mod.link`; `inline_bind`, `inlining_refines_hide`, `inline_link_eq_of_noCalls`, `uninlining_layered`; the abstract `ChainLaws` structure, `cris_four_step_chain_sound`, a trivial instance `trivialChainLaws` (a consistency witness for the assumed laws, nothing more), and `model_refinement_transfer`.
- **`undef`, `poison`, choice.** A two-bit value domain with `poison`, `and`/`or`/`xor`, value refinement and the paper's `observe`; `Val.and_mono`, `Val.or_mono`; `subst_choice_exact`, `freeze_undef_set_refinement`, `subst_poison_adds_behaviors`, `subst_zero_removes_behaviors`, `mirrored_rewrite_is_sound`, `ce1_c_bitfield_undef_to_poison_vacuous_refinement`, `ce1_choice_lowering_still_rejects`, `ce2_rust_undef_to_zero_misses_nonzero_choice`, `shared_choice_refines_per_use`, `per_use_undef_strictly_more`.
- **Source UB and attributes.** `ir_level_validation_sound`, `ce3_clang_ub_refinement_creates_false_positive`, `all_three_agree_at_positive`, `stripped_le_faithful`, `source_side_strip_is_sound`, `ce4_omitted_noundef_attr_misses_argument_poison_ub`.

What the model is *not*: it imports nothing from Vellvm, CRIS, Interaction Trees, R2C2 or Anneal; its trees are inductive, so it says nothing about divergence; module linking is modelled only for a layered non-recursive fragment; resources, separation logic and the simulation relation itself are absent; the value domain has two bits. The counterexample theorems establish that the corresponding *reasoning step* is invalid in general. They do not establish that any R2C2 proof is wrong.

**Two reusable observations about auditing a Lean file** (execution):

1. The audit command at the end of the file scans the environment for declarations of the model namespace and fails the build on an `unsafe` or `partial` constant, a constant whose name contains `_unsafe_rec`, or a dependency on any axiom other than `propext` and `Quot.sound`. All 353 declarations were found in `env.constants.map₂`; `env.constants.map₁` contained none. A check that inspects only `map₁` for the file's own declarations passes vacuously. The audit refuses to pass when it has scanned no declaration.
2. Before the definitions were marked `noncomputable`, the same audit rejected the file with six `unsafe` constants: `beh._unsafe_rec`, `bind._unsafe_rec`, `inline._unsafe_rec`, `noCallsTo._unsafe_rec`, `den._unsafe_rec` and `subst._unsafe_rec`, one for every structurally recursive definition, including the `Prop`-valued ones. No `deriving` clause was involved. Marking the definitions `noncomputable` suppresses code generation and the helpers disappear. A build with an unfinished proof was rejected with `sorryAx`, and a deliberately added `theorem … : p ∨ ¬ p := Classical.em p` was rejected with `Classical.choice`.

This matches how Anneal's trusted semantics is written at the examined commit (`trusted/lean/Trusted/MirSemantics.lean` contains 135 `noncomputable def` and no plain `def`) and what its audit forbids (Finding 12).

### 12. Consequences for a `rustc` MIR-to-LLVM-IR validator

Basis: derived from Findings 1–11, with source evidence from Anneal where stated.

**The MIR side of the seam.** At `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/lean/Trusted/MirSemantics.lean` models uninitialized data as a *storage state*, not as a value:

- `inductive LocalSlot where | dead | live (val : Option Val)` (line 621), documented as "`live none`: Storage is allocated (`StorageLive`) but uninitialized";
- `inductive AllocByte where | uninit | init (byte : UInt8) (prov : Option AllocId := none)` (line 422);
- `evalPrimitiveOperand` (line 1007) ends in `| none => .error .undefined`, i.e. a primitive read of uninitialized storage is modelled undefined behavior;
- `inductive FaultKind where | undefined | unsupported` (line 332), with the stated design rule (lines 49–52): "Any unmodeled MIR construct, type, or target/profile configuration steps explicitly to `FaultKind.unsupported`, and any modeled Rust Undefined Behavior steps explicitly to `FaultKind.undefined`. Both fault kinds falsify `WellFormed`."

There is no `undef` or `poison` value on this side. A simulation relation between such a MIR semantics and LLVM IR therefore has to relate "uninitialized storage" on the left to registers or memory bytes holding `undef` or `poison` on the right, and must let the LLVM side be `undef`/`poison` *only* where the MIR side is uninitialized.

**Requirements that follow.**

1. *Classify every LLVM-side shortcut as target-side.* By Finding 3 it may only add behaviors. Rewriting emitted `undef` to `poison` is admissible (and coincides with upstream Vellvm's denotation at the examined commit); rewriting it to zero or `null` is not (Finding 5). If precision matters, model `undef` as a fresh choice per use (Finding 6).
2. *Do not rely on "the compiler is correct" or "only safe Rust".* Both premises appear in the paper's soundness remark for its `undef` rewrite. The first is what a compiler validator sets out to check; the second excludes most of the code for which validation is valuable.
3. *Model the attributes the compiler adds, or fail closed on them.* `noundef`, `noalias`, `dereferenceable`, `range`, `nonnull`, `sret` and `mustprogress` all occurred in ordinary `-O1` output (Finding 8). On the target side an ignored UB-carrying attribute hides exactly the miscompilations in which the attribute is wrong. The fail-closed pattern exists on both sides of the seam already: R2C2 counts its `mustprogress` program as a failure, and Anneal steps unmodelled constructs to `FaultKind.unsupported`.
4. *Do not assume the absence of unwinding from `-Cpanic=abort`.* `invoke` and `landingpad` occur for `extern "C-unwind"` calls, and the landing pad runs drops before aborting (Finding 9).
5. *Validate against MIR, not against another compiler's IR.* Comparing two compilers' IR inherits each compiler's refinement of source UB and reports differences the source permits (Finding 7).
6. *Reuse the shape of the chain, not its trust assumptions.* A program-independent inlining/uninlining/cancellation layer with one per-function simulation obligation (Finding 2) fits per-function MIR-to-IR validation: library and intrinsic calls get specifications, the per-function proof is untrusted and kernel-checked. What must stay trusted is the statement being proved, including which side receives wrappers (`guarantee_unmet_refines_anything`).
7. *Keep the proof-acceptance gate explicit.* R2C2: "the Rocq kernel checks it, and we also ensure that no additional axioms or admits have been introduced", and the agent "can only modify its proof files and is not allowed to weaken the final theorem stating the refinement". Anneal's `trusted/audit/TrustedBoundary.lean` at the examined commit is "Pinned to Lean 4.34.1, commit `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`" and rejects reachable constants that are `unsafe` or `isPartial` ("No reachable constant is `unsafe` or `isPartial`", line 1763) and references to `sorryAx` and to the compiler-reflection names `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`, `Lean.reduceBool`, `Lean.reduceNat` (lines 1616–1617). Finding 11's two observations are the practical details such a gate must get right.

**The paper's stated trusted base**, for comparison: "the Rocq kernel, the definitions of ITrees and CRIS modules, from which behaviors and refinement are defined, the Vellvm parser that turns LLVM IR files into Rocq definitions, our Vellvm-based LLVM IR semantics, including its memory model, and our library modules." It also states "Our development adds no axioms: the eight axioms it relies on are all assumed by the libraries it uses." The textual `undef` rewrite, the compiler flags and the two compilers themselves sit before the parser and are not in that list; Findings 4, 5, 7, 9 and 10 are about that pre-parser stage.

## Boundaries

**Not examined**

- The remainder of eight paper source files beyond the first 6,500 characters of each: the introduction after the paragraph on AI-assisted automation; the LLVM background after the event signature; the validation section after the opening of "Building CRIS Programs" (including the definition of correctness the chain refers to); the common-abstraction section from the registration lemma on (including the observation lemma and the library specifications); the simulation section after the first rows of its worked example; the automation section after the first sentence of the counterexample check; the evaluation section after the counterexample figure (including the discussion of the 26 counterexamples and the efficiency and model-choice questions); and the semantics appendix after the denotation of `load` (including the denotations of `call`, `store` and terminators).
- The R2C2 implementation, its Rocq development, its library specifications and any artifact. Nothing of R2C2 was run.
- CRIS itself: its source, its definition of contextual refinement, and its adequacy and cancellation theorems. They are known here only as the paper states them.
- Clang 21.1.8 and rustc 1.93.1 as executables. Clang 21.1.8 was read for one function; rustc 1.93.1 for its option gating.
- The text of the C standard. Statements about source-level undefined behavior in C rest on Clang's source comment (negative variable-length-array bound) or are flagged as unverified (copying or returning an object with indeterminate members).
- Vellvm beyond the cited lines of `Syntax/LLVMAst.v`, `Semantics/Denotation.v`, `Semantics/Attributes.v`, `Semantics/LLVMEvents.v` and `tests/undef/README.md`; in particular its memory model, its `freeze` operation, and whether `noalias` is given meaning anywhere outside those files.
- Anneal beyond the cited lines of `trusted/lean/Trusted/MirSemantics.lean` and `trusted/audit/TrustedBoundary.lean`; in particular how it treats unions such as `MaybeUninit`.
- Targets other than `x86_64-unknown-linux-gnu`, optimization levels other than `-O1` / `-Copt-level=1`, and runtime execution of any compiled program (all compiler observations are of emitted IR).

**Unknown**

- How the paper classifies the 23 counterexamples that are not among the three incorrect translations, and whether its explanation is the mechanism of Finding 7.
- Whether R2C2's LLVM IR semantics enforces `noundef` or any other parameter attribute, and by what criterion a program "involves" `mustprogress`.
- Which Vellvm revision R2C2 builds on and whether the examined commit's `undef`-as-`poison` denotation is related to R2C2's textual rewrite.
- Whether R2C2 accepts C functions with bit-fields, by-value struct returns, or Rust return types containing `MaybeUninit`; hence whether the IR shapes of Findings 4 and 5 can reach its prover.
- How R2C2 treats a C call to a function that has no library model (the framework rule quoted in Finding 1 would make it undefined behavior on the source side).
- How the `-Z` flag was enabled on rustc 1.93.1 in the paper's experiments.
- Whether Clang 21.1.8 at `-O1` leaves `undef` in the same shapes as 22.1.4.

**Known not to apply**

- "A bit-field store into an uninitialized local leaves `and`/`or` over `undef` in clang's `-O1` output": not with clang 22.1.4. All single-mask shapes folded the indeterminate bits to zero (Finding 4). The mixed case needs two different masks on one possibly unwritten storage unit.
- "Clang turns `int` overflow in a variable-length-array bound into defined wrapping": the addition keeps `nsw`; overflow is `poison` in IR. The source-versus-IR difference is in the *extension* of a negative bound (Finding 7).
- "`-Cpanic=abort` output never contains `invoke`": false for `extern "C-unwind"` callees; a `Drop` guard is not required for the `invoke` to appear (Finding 9).
- "A semantics derived from Vellvm ignores `noundef`": false for upstream Vellvm at the examined commit (Finding 8).

**Unsupported (by R2C2, per the paper)**

- `undef` in the semantics (rewritten away), vector types and instructions ("we reject an LLVM IR that still contains vector types or instructions"), recursive structs, an `Option<String>` return value, the `mustprogress` attribute, closures, and full I/O ("we do not claim to fully support I/O operations in this work"). Refinement omits "traces not ending with `Done`, such as divergence and abort."

**Stronger conclusions the evidence does not establish**

- That R2C2 has accepted an incorrect translation, or that any of its 486 proofs is invalid. The findings identify directions in which stated rewrites are unsound in general and exhibit IR shapes where they would matter; no R2C2 run was observed.
- That the paper conceals the `undef` limitation. It states it.
- That the Lean model verifies the four-step chain of CRIS. It proves a composition theorem under assumed laws and proves two mechanisms in a finite, non-recursive fragment.
- That the absence of `undef` in the eleven folded C shapes is guaranteed. It is an observed optimizer outcome for one compiler version and one flag set.

## Evidence

All evidence was acquired on 2026-11-22.

**The paper.** What was examined is a comment-stripped text extract of the LaTeX source of arXiv:2611.18036v1, one text per source file (`0-abstract.tex`, `1-intro.tex`, `2-1-llvm.tex`, `2-2-refinement.tex`, `3-validation.tex`, `4-common.tex`, `5-1-chain.tex`, `5-2-simulation.tex`, `6-automation.tex`, `7-1-eval.tex`, `7-2-eval.tex`, `8-related.tex`, `9-conclusion.tex`, `A-semantics.tex`, `B-compilation.tex`). Each text had been capped at 6,500 characters before it reached this investigation. Seven are complete; eight end exactly at the cap, mid-sentence. `support/paper_extract_manifest.json` lists, per file, the number of characters and lines examined, whether the cap was hit, and the SHA-256 of the examined text. Attempts on the observation date to retrieve the arXiv abstract page, the HTML rendering and the PDF through the available read-only fetch service all failed, so the extract could not be completed or compared against the published rendering. Quotations in this report are from the extract; line numbers of the original source files are not known and are not cited. A web search on the observation date returned secondary summaries consistent with the abstract (title, authors, 519 programs, 486 proved, three incorrect translations); they were not used as evidence for any other statement.

Where each quoted statement sits: the correctness statement, 519/486/three figures (abstract); events, modules, `Beh`, the ghost-resource and divergence footnote (background, sections "LLVM IR" and "Refinement in CRIS"); drivers, `observe`, value refinement, library modules (section "Defining Translation Correctness as Refinement"); resources, representation predicates, common-abstraction table, representation pair (section "Reasoning with Common Abstractions"); wrappers, the chain, the inlining/uninlining lemma, cancellation (subsection "Chain of Refinements"); adequacy, the obligation, simulation rules (subsection "Establishing Simulation"); inputs and restrictions, argument matching, the `undef` rewrite, proof check, counterexample check (section "Automating Translation Validation with AI Agents"); implementation, trusted base, library counts, 486/26/7 and the seven failures, counterexample figure (section "Evaluation"); `sret` driver, file abstraction, I/O limits (subsection "Case Study: QOI"); source-level validation as future work (section "Related Work"); compilers, flags, `-Zinline-mir=no`, `-Cpanic=abort` (appendix "Compilation Settings"); syntax subset, `alloca` rule, `select` rule (appendix "Semantics of LLVM IR").

**Git sources** (repository, commit, path, lines). Commits were resolved on the observation date through the GitHub REST endpoint `repos/<repository>/commits/<ref>`; `support/pin_resolution.json` records each requested ref and the commit returned.

| Repository and commit | Path | Lines | Used for |
| :--- | :--- | :--- | :--- |
| `vellvm/vellvm@7f0610c38d829b79bf6e867edf410c9e6f928f98` | `src/rocq/Syntax/LLVMAst.v` | 198, 201, 213, 354, 515–519, 1043, 1045 | attribute constructors; `EXP_Undef` comment; `TERM_Resume`, `TERM_Invoke` |
| same | `src/rocq/Semantics/Denotation.v` | 258–266, 521–529, 630, 771–772, 795, 987–996 | `undef` as `poison`; `noundef` enforcement; invoke and resume |
| same | `src/rocq/Semantics/Attributes.v` | 122–130, 214–223, 368–376 | `noundef` violation is UB; `nonnull`/`align`/`range` violations yield poison |
| same | `src/rocq/Semantics/LLVMEvents.v` | 100–104, 186–187 | `DrawE` for `freeze`; `UBE` |
| same | `tests/undef/README.md` | whole file | `undef` treated as `poison`; known failing test |
| `DeepSpec/InteractionTrees@284d42248a3c5517cff9f582e335fcee2f6bdc1f` | `theories/Core/ITreeDefinition.v` | 30–42 | `itreeF` with `RetF`, `TauF`, `VisF`; `CoInductive itree` |
| `llvm/llvm-project@35990504507d79e0b9deb809c8ee5e1b34ceef20` (`llvmorg-22.1.4`) | `llvm/docs/LangRef.rst` | 1635–1639, 2726–2735, 4974–4980, 5153–5182 | `noundef`; `mustprogress`; undefined values; poison values |
| same | `clang/lib/CodeGen/CodeGenFunction.cpp` | 2577–2580 | zero-extension of a variable-length-array bound |
| `llvm/llvm-project@2078da43e25a4623cab2d0d60decddf709aaea28` (`llvmorg-21.1.8`) | `clang/lib/CodeGen/CodeGenFunction.cpp` | 2567–2570 | the same four lines in the paper's Clang version |
| `rust-lang/rust@01f6ddf7588f42ae2d7eb0a2f21d44e8e96674cf` (`1.93.1`) | `compiler/rustc_session/src/config.rs` | 1849, 2915–2985 | `-Z` registered as unstable; `nightly_options` |
| same | `compiler/rustc_feature/src/lib.rs` | 55–91 | `UnstableFeatures::from_environment`, `is_nightly_build` |
| same | `compiler/rustc_session/src/options.rs` | 2404–2405 | `inline_mir` |
| same | `src/version` | 1 | `1.93.1` |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirSemantics.lean` | 49–52, 82–90, 332–334, 422–424, 618–623, 1007–1018 | fault kinds; uninitialized storage; primitive read of uninitialized storage |
| same | `trusted/audit/TrustedBoundary.lean` | 16–17, 1616–1617, 1763 | pinned Lean commit; forbidden reflection names; no `unsafe`/`isPartial` |
| same | `trusted/lean/lean-toolchain` | 1 | `leanprover/lean4:v4.34.1` |

`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` is the commit reported by `rustc --version --verbose` of the executed nightly; `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` is both the commit the tag `v4.34.1` resolves to and the commit reported by `lean --githash`; `llvm/llvm-project@35990504507d79e0b9deb809c8ee5e1b34ceef20` is both the commit the tag `llvmorg-22.1.4` resolves to and the commit in the executed clang's version string.

**Execution: compiler probe.** `support/probe_r2c2_cris_llvm_ir_and_undef_hazards.py` (Python standard library only) embeds the C and Rust sources, compiles them, parses the IR, applies the two textual rewrites as reconstructed from the paper's prose, runs `opt`, and writes every observed value to a JSON file. Its 18 checks compare observed values with the claims of this report and the process exits non-zero if any differs. Run of record:

```text
toolchain   clang version 22.1.4 (https://github.com/llvm/llvm-project 35990504507d79e0b9deb809c8ee5e1b34ceef20)
            rustc 1.98.0-nightly (14210df0e 2026-05-31), LLVM version: 22.1.6, host x86_64-unknown-linux-gnu
            opt: LLVM version 22.1.6-rust-1.98.0-nightly
result      18 checks, 0 failed; exit status 0
```

Preserved: `support/probe_results.json` (toolchain lines, flags, per-function `undef` lines, function bodies, folded functions before and after each rewrite, unwinding and attribute counts, the `-Z` gating outcome, and every check with its observed value), `support/probe_stdout.txt`, and the two C-side modules exactly as clang emitted them, `support/ir/c_uninit.clang.O1.ll` and `support/ir/c_vla.clang.O1.ll`. Rust-side modules are large and are preserved as function excerpts inside the JSON file.

The rewrites in the probe are reconstructions: C side, every standalone `undef` token becomes `poison`; Rust side, `<type> undef` becomes `<type> 0`, `null`, `0.0` or `zeroinitializer` according to the type, and the probe raises if an `undef` remains that it cannot classify.

**Execution: Lean.** `support/CrisRefinementChainAndUndefHazardSoundness.lean` (SHA-256 `4344c3dd8f9bffd115372774dd5452949ceed899c520213660b16dc631d9b8ba`) was checked with

```text
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true CrisRefinementChainAndUndefHazardSoundness.lean
```

using Lean 4.34.1 (commit `5045d0056413266e57c625dcd7c365b10e377c52`), exit status 0. The printed audit summary is preserved as `support/lean_check_output.txt` and reproduced in Finding 11. The three rejected builds described in Finding 11 (six `_unsafe_rec` helpers before `noncomputable`; `sorryAx` with an unfinished proof; `Classical.choice` with an added classical theorem) were observed with the same command; they are described, not preserved, and Revalidation says how to reproduce two of them.

**Synthesis versus source.** The classification table of Finding 3, the input-by-input reading of Finding 7, the conclusion of Finding 10 and all of Finding 12 are this report's synthesis. The quoted paper text, the cited source lines and the recorded tool outputs are the facts they rest on.

## Revalidation

**Cheapest checks, in order of value.**

1. *Does a newer clang or rustc still behave as described?* Rerun the probe with the toolchain of interest:

   ```text
   python3 support/probe_r2c2_cris_llvm_ir_and_undef_hazards.py \
       --clang /path/to/clang --rustc /path/to/rustc --opt /path/to/opt \
       --out /tmp/probe_results.json --keep-ir /tmp/probe_ir
   ```

   Exit status 0 with `18 checks, 0 failed` means every compiler-dependent statement of Findings 4, 5, 7, 8, 9 and 10 still holds for that toolchain. A failed check names the statement that changed; compare `/tmp/probe_results.json` with `support/probe_results.json`. The checks most likely to move are `c.undef_phi_reaches_two_masks` (a smarter fold removes the remaining `undef`), `c.single_use_indeterminate_bits_are_folded` (a weaker fold leaves more), `rust.safe_maybeuninit_return_is_undef` (rustc may switch that aggregate to `poison`), and `c.vla_bound_is_nsw_add_then_zext` (Clang may start emitting `zext nneg`, which would make a negative bound `poison`). The `-Z` gating check needs a nightly `rustc`; `opt` should come from an LLVM of the same major version as the compilers so that it parses their output. A passing probe says nothing about R2C2 itself.

2. *Is the model still accepted by Lean?* Rerun the `lean` command under Evidence with a Lean 4.34.1 toolchain and compare the output with `support/lean_check_output.txt`. To confirm that the audit is not vacuous, delete the word `noncomputable` in front of `def bind` and rerun: the build must fail with `purity audit failed` after printing `_unsafe_rec constants: 1 [CrisModel.bind._unsafe_rec]` (observed). Adding `theorem t (p : Prop) : p ∨ ¬ p := Classical.em p` inside the namespace must fail naming `Classical.choice`. On another Lean version, expect the field names `map₁` and `map₂` and the presence of `_unsafe_rec` helpers to be the first things to change.

3. *Has upstream Vellvm changed its treatment of `undef` or `noundef`?* At the commit of interest, read the `EXP_Undef` case of `denote_exp` in `src/rocq/Semantics/Denotation.v` and search that file for `violates noundef`. If `EXP_Undef` regains a dedicated value, Finding 4's statement about Vellvm no longer applies to that commit.

4. *Has Clang changed the variable-length-array lowering?* Search `clang/lib/CodeGen/CodeGenFunction.cpp` for `Always zexting here`.

5. *Has rustc changed option gating?* Read `nightly_options::check_nightly_options` in `compiler/rustc_session/src/config.rs` and `UnstableFeatures::from_environment` in `compiler/rustc_feature/src/lib.rs`.

**What cannot be revalidated cheaply.** Every statement marked unknown under Boundaries requires the complete paper text or the R2C2 implementation. With the complete text, the first things to read are: the discussion following the counterexample figure in the evaluation section (the classification of the 26 counterexamples), the denotation of `call` in the semantics appendix (parameter attributes), and the remainder of the counterexample-check paragraph (how C-side UB is detected). With the implementation, the decisive experiment for Finding 4 is to submit `two_masks` (or a variant whose loop reads an input array instead of calling external functions) together with a Rust function that returns a wrong low bit on the zero-trip path, and to see whether a proof is accepted; for Finding 5, to submit a Rust function returning a `MaybeUninit` component against a C function returning zero.
