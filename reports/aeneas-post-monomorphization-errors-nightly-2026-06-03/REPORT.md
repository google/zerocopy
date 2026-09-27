# Post-monomorphization errors at the Anneal Aeneas/Charon boundary

## Summary

Zerocopy uses post-monomorphization errors (PMEs) as compile-time admission checks for some generic operations whose runtime implementation is only sound for particular concrete types. Its `static_assert!` macro deliberately evaluates a type-dependent condition after monomorphization and turns failure into a compile error. Callers can therefore rely on a property such as equal size or non-increasing alignment even when the generic Rust function has no trait bound that states that property.

That guarantee does not automatically appear in the ordinary Aeneas input at the versions selected by Anneal. Aeneas `nightly-2026.06.03` requires LLBC generated with Charon's `--preset=aeneas`. At the pinned Charon revision, that preset does not enable Charon's separate `--monomorphize` mode. Charon normally translates the generic item, and its LLBC/Aeneas pipeline can preserve generic const parameters and associated-const computations symbolically. The checked-in Aeneas Lean output demonstrates that behavior.

The resulting distinction is important for soundness work. A generic Aeneas proof can be stronger than native Rust and prove a body correct for every modeled instantiation. If it does so, excluded Rust instantiations are harmless. But when the Rust implementation's safety argument specifically depends on a PME excluding bad concrete instantiations, a proof over the polymorphic body must establish an equivalent condition or otherwise restrict the theorem to Rust-admitted instantiations. Merely translating the body through the normal Aeneas preset does not establish that rustc's post-monomorphization rejection was represented.

Charon 0.1.210 also has a separate `--monomorphize` mode. Source inspection shows that it substitutes concrete generic arguments into translated items, but this report does **not** establish that the mode reproduces rustc's PME checks or rejects exactly the same instantiations. No fresh Charon, rustc, Aeneas, or Lean execution was available for this report. The cheapest experiment needed to resolve that question is specified under **Revalidation**.

## Applicability

The Aeneas subject is `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, released as `nightly-2026.06.03`. That is the release selected by the examined Anneal configuration.

The corresponding Charon subject is `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, version `0.1.210`, using `nightly-2026-05-31`. Aeneas's own entry point requires input produced with `--preset=aeneas`, so that preset is the default compatibility boundary considered here.

The concrete PME mechanism was examined in current zerocopy source at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`. The historical Anneal concern is recorded in `google/zerocopy#3030`, created on 2026-02-11, which links to the contemporaneous Aeneas Zulip discussion. Issues #3199 and #3208 later list #3030 among soundness work. This report uses those issues to establish why PMEs matter to Anneal, not as authority for compiler behavior.

The report concerns PMEs implemented through required constant evaluation of type-dependent generic expressions, especially zerocopy's `static_assert!` pattern. “PME” here is not a distinct Rust source construct or an Aeneas AST node. It describes a compilation failure that becomes knowable only after generic parameters are instantiated sufficiently for a required compile-time check to fail.

## Findings

### Zerocopy uses PMEs as compile-time admission checks

Zerocopy's `static_assert!` macro states its contract directly: unlike `const_assert!`, it is strictly a compile-time check; its condition is checked after monomorphization; and failure emits a compile error.

The implementation creates a local `StaticAssert` trait with an associated `ASSERT` constant. A generic implementation computes `ASSERT` using `const_assert!($condition)`. The call site then requires evaluation of the associated constant for the concrete generic arguments. A false condition therefore prevents the concrete use from compiling instead of becoming a runtime branch.

This mechanism appears on paths that participate in unsafe-code justification. Examples at the examined zerocopy revision include:

- `try_transmute<Src, Dst>`, which requires `size_of::<Dst>() == size_of::<Src>()`;
- reference and mutable-reference transmutation paths that assert size or alignment relationships before an unsafe pointer/reference step;
- `layout::CastFrom::project`, whose documentation says it generates a PME when the requested generic pointer cast cannot be implemented soundly. Its type-dependent `CastParams::try_compute` result is forced through an associated constant and panics during required const evaluation when the layouts are incompatible.

These checks are not merely diagnostics layered over an independently sufficient type-system proof. Where a safety comment relies on the asserted size or alignment relationship, excluding a bad monomorphization is part of the Rust-side argument that the unsafe operation cannot execute under an invalid relationship.

Basis: **source** — `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, especially `zerocopy/src/util/macros.rs`, `zerocopy/src/util/macro_util.rs`, and `zerocopy/src/layout.rs`.

### Zerocopy's test infrastructure treats PMEs as a separate compile-failure class

`zerocopy/src/doctests.rs` explains that the crate's `trybuild`-based UI framework does not support testing PMEs, so the project uses doctests for them instead. This is useful evidence about the operational boundary: the relevant observable result is compilation failure for a concrete use, not a runtime panic from the generic function.

Basis: **source** — `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `zerocopy/src/doctests.rs`.

### Aeneas requires the Aeneas Charon preset

At the pinned Aeneas revision, the README instructs users to generate LLBC with:

```text
charon cargo --preset=aeneas
```

Aeneas also checks the serialized crate metadata in `src/Main.ml` and rejects input that was generated without `Preset::Aeneas`. This is therefore more than an example command: it is an input-compatibility condition enforced by Aeneas.

Basis: **documentation** + **source** — `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `README.md` and `src/Main.ml`.

### The required Aeneas preset does not request full monomorphization

At Charon `0.1.210`, full monomorphization is a separate `--monomorphize` option. Its help text says Charon will monomorphize encountered items when possible and skip generic items found directly in the crate; it recommends combining the mode with `--start-from` when translating a particular call graph.

The `Preset::Aeneas` branch changes associated-type handling, built-in/container treatment, operation reconstruction, marker-trait visibility, allocator visibility, and related normalization options. It does **not** set `monomorphize`. By contrast, the `Preset::Soteria` branch explicitly sets `self.monomorphize = true`. The distinction is explicit in the pinned source.

Accordingly, `--preset=aeneas` alone should not be read as “run Charon after specializing every generic item to the set of rustc codegen instances.” The ordinary Aeneas input remains a polymorphic representation where Charon can translate the generic definition and generic references.

Basis: **source** — `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `charon/src/options.rs`.

### Charon's normal Aeneas path obtains MIR before the ordinary runtime optimization/codegen boundary

At the same revision, Charon's default MIR level for local items is Promoted, and the Aeneas preset does not change that choice. `translate/get_mir.rs` maps that level to rustc's `mir_promoted` query. For globals and const functions where the earlier body is unavailable or inappropriate, Charon can use CTFE MIR, and dependencies can enter through optimized MIR.

The important point for PMEs is narrower than a complete MIR-stage taxonomy: the ordinary polymorphic Aeneas path is not itself evidence that Charon observed the final set of codegen monomorphizations that rustc accepted. Charon has its own optional monomorphization path, but the required preset does not enable it.

Basis: **source** — `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `charon/src/options.rs` and `charon/src/bin/charon-driver/translate/get_mir.rs`.

### Aeneas preserves generic constant structure symbolically

The pinned Aeneas repository contains source/golden-output pairs that show generic constants surviving into generated Lean as parameters and definitions.

In `tests/src/constants.rs`, `V<const N: usize, T>` has an associated constant `LEN = N`, and `use_v<const N, T>` returns `V::<N, T>::LEN`. The checked-in `tests/lean/Constants.lean` translates `V` as a definition parameterized by Lean `N`, translates `V.LEN` as a Lean function of `N`, and translates `use_v` as a Lean function that returns `V.LEN T N`.

The `constants-lean` fixture goes further. Generic associated constants such as `Wrapper<N, M>::NM = N * M`, trait-associated constants, and default associated-constant expressions become Lean definitions or structure fields over symbolic parameters. They are not replaced wholesale by one list of concrete rustc codegen instances.

Charon's own constant translator is compatible with that observation: generic const references may become `ConstantExprKind::Var`, while named globals and other constant structure remain represented in LLBC when supported.

This is valuable capability, but it is not the same fact as “rustc accepted this concrete monomorphization after evaluating every PME guard.” A symbolic proof and a compiler admission check have different domains unless the relationship is made explicit.

Basis: **source** + **checked-in generated evidence** — `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `tests/src/constants.rs`, `tests/lean/Constants.lean`, `tests/src/constants-lean.rs`, and `tests/lean/ConstantsLean.lean`; `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `charon/src/bin/charon-driver/translate/translate_constants.rs`.

### A polymorphic proof does not automatically inherit rustc's accepted-instantiation set

The historical Anneal concern can now be stated precisely.

Suppose a generic Rust function contains an unsafe operation whose safety argument depends on a `static_assert!` condition `P<T>`. Native Rust gets an important fact from compilation: any concrete instantiation that reaches a successful binary has passed the required compile-time check, so `P<T>` held for that admitted instantiation.

The ordinary pinned Aeneas path instead starts from a polymorphic LLBC representation. The evidence examined here does not show a dedicated LLBC or Aeneas predicate meaning “this generic argument tuple belongs to the set of monomorphizations rustc accepted after required const evaluation.” Nor does the checked-in generic-constant output encode that admission set implicitly: it represents generic const computations as ordinary symbolic definitions and results.

Two verification strategies can nevertheless be sound:

1. **Prove the stronger generic theorem.** If Lean establishes the unsafe operation's precondition for every modeled `T`, no PME assumption is needed. Rust's rejection of additional impossible or invalid instantiations only narrows the native program further.
2. **Carry an admission premise.** If the proof needs the same type-dependent fact that Rust obtains from the PME, Anneal must establish that fact in the proof domain or otherwise connect the theorem to only those concrete instantiations that rustc admits.

What is unsafe is the inference between those two without evidence: translating the generic body does not by itself justify importing a post-monomorphization compiler fact as a theorem hypothesis.

Basis: **derived** from zerocopy's PME implementation, Charon's preset/monomorphization split, and Aeneas's checked-in symbolic constant translation.

### Charon's `--monomorphize` mode is a candidate bridge, not an established PME solution

The pinned Charon source has a full `--monomorphize` option. In monomorphic item translation, `get_mir.rs` uses Hax substitution to apply concrete rustc generic arguments to the MIR body, and the crate translator distinguishes polymorphic from monomorphic item sources.

That establishes that Charon can specialize representations. It does **not** establish that Charon's specialization path invokes exactly the same required-const-evaluation checks that native rustc codegen uses, or that a concrete instance omitted/rejected by rustc would be omitted/rejected for the same reason by Charon. This report found no pinned source or checked-in specimen that closes that equivalence for zerocopy's `static_assert!` pattern.

Therefore an Anneal design may reasonably investigate `--monomorphize` as part of the solution, but should not treat the existence of the flag as proof that PMEs have been modeled faithfully.

Basis: **source** + **derived** — Charon `charon/src/options.rs`, `translate/get_mir.rs`, and `translate/translate_crate.rs`; absence of a demonstrated equivalence is recorded as a boundary below.

### The historical Anneal discussion identified the right semantic split

The message linked from zerocopy issue #3030 describes the core problem: zerocopy deliberately emits generic code that could be unsound for some instantiations and relies on PMEs to keep those instantiations out of binaries. It asks whether Aeneas can accommodate that pattern and suggests, as a fallback, proving the const-domain condition and runtime-domain behavior separately and connecting them explicitly.

That fallback remains consistent with the source evidence above. It should be treated as a proposed proof architecture, not as a facility already implemented by Aeneas. The current Anneal design deliberately leaves the exact Rust/Charon/Aeneas/Lean proof boundary open.

Basis: **historical primary discussion** + **derived** — Aeneas Zulip message `573180904`, linked from `google/zerocopy#3030`; current Anneal `PRINCIPLES.md` and `DESIGN.md` govern any eventual architecture choice.

## Boundaries

- **No fresh compiler/tool execution was performed.** The report is based on pinned source, checked-in generated Aeneas output, current zerocopy source, and preserved historical discussion. It does not claim an empirical end-to-end result for a zerocopy PME specimen through the pinned toolchain.
- **Whether Charon `--monomorphize` reproduces rustc PME admission is unknown here.** The source proves that the option specializes items; it does not prove equivalence to rustc's post-monomorphization required const checks.
- **This is not a claim that Aeneas is unsound.** Aeneas may prove a stronger polymorphic theorem, or an Anneal integration may add the missing admission premise. The issue is identifying which theorem has actually been established.
- **This report does not claim every PME has the same mechanism.** The concrete zerocopy examples use type-dependent required constant evaluation. Other compiler failures that are also described as post-monomorphization errors may arise from other checks and need separate analysis.
- **The concrete zerocopy source is current `main`, not a reconstruction of the exact February 2026 tree.** Issue #3030 and the Zulip message establish the historical motivation; the pinned source identities establish current examples and the Anneal-era Aeneas/Charon behavior.
- **Neighboring replies in the original Zulip discussion were not recovered.** The exact linked message is available, but the topic was later moved to the Hermes/Zerocopy channel and the available structured search did not return the surrounding historical messages. No response or maintainer conclusion is inferred from the missing context.
- **Aeneas's generic-constant fixtures are positive representation evidence, not PME fixtures.** They show symbolic preservation of generic constant structure. They do not test a failing `static_assert!` or prove how the translator behaves after native compilation rejects an instantiation.
- **The exact rustc internal phase called “post-monomorphization” is not exhaustively reconstructed here.** Zerocopy's own macro contract supplies the relevant compile-time guarantee. A future report may trace the compiler query/codegen path more finely if Anneal needs to reproduce the admission relation itself.
- **No Anneal architecture decision is made here.** Whether to prove PME predicates generically, specialize proofs, import compiler evidence, or split const/runtime proof domains belongs to Anneal design authority on `main`.

## Evidence

**Aeneas input contract and generated output.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`:

- `README.md` — documents `charon cargo --preset=aeneas` as the required Charon invocation before running Aeneas.
- `src/Main.ml` — checks serialized LLBC metadata for `Preset::Aeneas` and rejects input generated without it.
- `tests/src/constants.rs` and `tests/lean/Constants.lean` — source/golden pair for generic const parameters, associated constants, and generated Lean definitions.
- `tests/src/constants-lean.rs` and `tests/lean/ConstantsLean.lean` — source/golden pair for generic and trait-associated constant computations in Lean.

**Charon translation boundary.** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`:

- `charon/src/options.rs` — independent `--monomorphize` option; `Preset::Aeneas` configuration; contrast with `Preset::Soteria`, which explicitly enables full monomorphization.
- `charon/src/bin/charon-driver/translate/get_mir.rs` — MIR query selection and generic-argument substitution in monomorphic item translation.
- `charon/src/bin/charon-driver/translate/translate_crate.rs` — polymorphic versus monomorphic item-source selection.
- `charon/src/bin/charon-driver/translate/translate_constants.rs` — symbolic generic const references and supported constant-expression translation.

**Concrete zerocopy PME mechanism.** `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`:

- `zerocopy/src/util/macros.rs` — `const_assert!`, `static_assert!`, and the explicit post-monomorphization compile-error contract.
- `zerocopy/src/util/macro_util.rs` — size/alignment `static_assert!` guards on transmutation-related paths.
- `zerocopy/src/layout.rs` — `CastParams` computation and the documented PME behavior of generic pointer-cast projection.
- `zerocopy/src/doctests.rs` — documents the dedicated doctest route for PME compile-failure testing.

**Historical Anneal motivation.** `google/zerocopy#3030`, “What about: PMEs?”, created 2026-02-11, links Aeneas Zulip message `573180904` in the `Zerocopy/Hermes` discussion. The message records the PME/soundness concern and a possible split const-domain/runtime-domain proof strategy. `google/zerocopy#3199` and #3208 later reference #3030 in soundness tracking.

No item above is fresh **execution** evidence from this report run.

## Revalidation

For a newer Aeneas/Charon pair, first repeat the cheap source checks:

1. Confirm the Charon preset Aeneas requires and whether Aeneas still validates it in serialized input.
2. Inspect the current Aeneas preset and determine whether it enables full monomorphization or another specialization mechanism.
3. Inspect Charon's monomorphic body path and constant translation for a representation of required const-evaluation failure or admitted-instance constraints.
4. Inspect Aeneas's generated representation of generic associated constants and const-dependent predicates.
5. Inspect zerocopy's `static_assert!` implementation and the particular unsafe paths whose safety arguments rely on it.

On an execution-capable surface, use a minimal crate with the same structural pattern as zerocopy:

```rust
fn guarded<T, U>() {
    static_assert!(T, U => core::mem::size_of::<T>() == core::mem::size_of::<U>());
    // Marker representing an operation whose proof relies on the equality.
}

fn valid() { guarded::<u32, i32>(); }
fn invalid() { guarded::<u8, u64>(); }
```

Use the actual zerocopy macro or an equivalent minimal associated-const implementation whose failure is demonstrably a PME. Preserve two variants if necessary: one with only the valid call reachable and one with the invalid call reachable.

For each variant, record:

- ordinary `cargo`/`rustc` compilation and its diagnostic;
- `charon cargo --preset=aeneas --print-original-ullbc` output;
- the same Charon invocation with `--monomorphize` and an appropriate `--start-from` root;
- final LLBC for both modes;
- generated Aeneas Lean for every LLBC that Aeneas accepts.

The decisive questions are:

- Does ordinary Aeneas-preset LLBC expose the `static_assert!` condition, erase it, or encode it only as a generic const computation?
- Does Charon full monomorphization reject the invalid instance, omit it, preserve an explicit failure, or still emit a specialized body?
- If both native Rust and Charon reject the invalid instance, are they using the same compiler admission fact or merely producing coincidentally equivalent outcomes?
- What proposition, if any, reaches Lean and can be used to justify the runtime unsafe step?

A passing valid specimen plus failing invalid specimen would establish behavior for that exact pattern and toolchain. It would not prove that every class of rustc PME has the same relationship to Charon/Aeneas.