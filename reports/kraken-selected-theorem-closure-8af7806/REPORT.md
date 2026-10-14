# Kraken selected theorem closure and permission-effect interpretation

## Summary

At Kraken `8af78062037bc237b341d20252aafd1797c1bcb7`, both X64 and AArch64 expose useful sequential proof models, but their default `Effects.All` interpretation does not check read, write, or execute permissions. X64 vector helpers also emit an eight-byte permission request before accessing 16, 32, or 64 bytes. A permission interpreter must account for that producer mismatch before its requests can describe complete vector footprints.

Fresh checks on Lean 4.34.1 distinguish selected closed examples, admitted examples, and a native verification axiom. They also check a new AArch64 addition theorem and an effect-interpreter erasure theorem. These are theorems about the identified formal model. They do not establish ISA fidelity, binary identity, a Rust resource bridge, or the pinned nightly toolchain's behavior.

## Applicability

The source subject is the exact Kraken commit above, containing both architecture models. Its `lean-toolchain` requests `nightly-2026-09-21`; its Lake manifest has no external packages. The observed build and probes instead used installed Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, on `arm64-apple-darwin24.6.0`. This is a cross-version observation, not a reproduction on the requested nightly. The shared prerequisite build completed both libraries, including their example modules; this package rechecks selected imports and owned declarations. [Pinned build configuration](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/lakefile.toml), [toolchain](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/lean-toolchain).

The X64 and AArch64 modules define several same-named root declarations. The probes import them in separate Lean processes. `import all` is needed to inspect the examples' private declarations under Lean's module system. The exact programs, statements, commands, exit statuses, and printed dependency lists are preserved in `support/`; no local olean is required to understand the findings.

This package answers selected parts of AS01, AS04, and AS05. It inventories the examined model boundary and selected theorem closures. Detailed instruction-by-instruction correspondence to an independent authoritative ISA remains unexamined.

## Findings

### The state and proof endpoint are explicit and selective

X64 `MachineData` contains the general-register bank, a ZMM register bank, six status flags, and a finite byte map; `MachineState` adds an `Int64` PC. Syntax supports scalar widths 8/16/32/64, vector widths 128/256/512, partial registers, labels and constant expressions, regular operations, and a small vector-operation family. The actual vector family is `movups`, `vmovups`, `movaps`, `subps`, and `addps`; it is not a claim of general AVX or floating-point coverage. `MXCSR` is explicitly a TODO. AArch64 has X0–X30/SP, NZCV status, byte memory, and a PC, with scalar arithmetic, logical, bit manipulation, load/store, conditional, and branch forms. `capability-inventory.json` lists the constructor names extracted from the pinned syntax, retaining the distinction between syntax and valid encodings. [X64 state/effects](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/X64/Semantics.lean#L235), [X64 syntax](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/X64/Syntax.lean#L189), [AArch64 state](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/AArch64/Semantics.lean#L145).

`Eventually trans post initial` is an inductive eventual-postcondition judgment. Its constructors permit an already satisfied postcondition or a transition to a predicate whose every member has another eventuality proof. `step1` uses directives at the current address; `straightlineStep` uses the remaining directive suffix. They do not have interchangeable meanings merely because they share `Effects.All`. The examples below prove exactly their named register postconditions under those transitions. They do not automatically state a whole-state frame, access trace, ABI result, or behavioral equivalence. [Common judgment and composition](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/OmniSemantics.lean#L13), [X64 transition wrappers](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/X64/OmniSemantics.lean#L24).

Basis: **source**; formal endpoint explanation **derived** from the definitions.

The X64 README declares 64-bit-mode sequential software as its intended domain and excludes OS/concurrency features, virtual memory, segment registers, MSRs, other execution modes, mutable globals, and handling of most exceptions/faults. Its inclusion of memory access does not override the actual permission interpretation inspected below. These are the README's X64 scope declarations; this report does not transfer them into an exhaustive AArch64 support claim. [Declared X64 scope](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/README.md#x64-model-scope).

### Selected theorem closure is more informative than a build or admission count

Let `B = {propext, Classical.choice, Quot.sound}`. Fresh `#print axioms` results were:

| Architecture and selected declaration | Observed dependencies | Exact useful scope |
|---|---|---|
| X64 `swap_correct` | B | XOR register swap, `Eventually straightlineStep`, any supplied layout |
| X64 `move_2_regs_to_heap_correct` | B | Two eight-byte owned map cells; stores/loads establish R12/R13 results and retain RDI |
| X64 `alu_mem_example_correct` | B | Selected bounded-memory arithmetic example's register postcondition |
| X64 `Mem.loadInt_sep`, `Mem.storeInt_sep` | B | Map/separation lemmas used by memory examples |
| X64 `p3_correct`, `dynamic_stack_example_correct` | B plus `sorryAx` | Admitted examples; unsuitable as closed certificates |
| AArch64 `swap_correct`, `move_2_regs_to_heap_correct`, `reg_offset_example_correct` | B | Their exact swap/memory/register-offset statements |
| AArch64 `arith_shift_correct` | B plus `arith_shift_correct._native.bv_decide.ax_1_10` | Arithmetic/shift statement with additional native verification premise |
| Owned AArch64 `addPilot_correct` | B | For every initial MachineData/layout, `add x0,x1,#42` produces X0 = initial X1 + 42 in `straightlineStep` |

The memory examples assume a separation decomposition of the byte map containing two `UInt64.At` cells and a remainder predicate. Their listed result clauses do not themselves return that entire decomposition as a postcondition. The source admits in other declarations did not add `sorryAx` to the selected closed declarations. Conversely, absence of `sorryAx` did not remove the arithmetic theorem's native axiom. [X64 selected statements](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/X64/Examples/Examples.lean#L311), [AArch64 arithmetic](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/AArch64/Examples/Examples.lean#L66).

`NativeAxiom.log` prints the extra axiom's type: the Boolean certificate verifier `Std.Tactic.BVDecide.Reflect.verifyBVExpr` applied to the theorem's reflected expression and certificate equals true. In the examined Lean 4.34.1 implementation, `LratCert.toReflectionProof` obtains this equality through `nativeEqTrue`. This is an additional native computation trust boundary, distinct from an admitted proposition. The fresh addition proof uses ordinary simplification and does not add that axiom. The Lean source path is `Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean`, symbol `LratCert.toReflectionProof`; the selected Lean commit is recorded in metadata.

Basis: **execution** + **source**. The printed lists concern the actual cross-version imports, not every theorem or the requested nightly.

### Default effect interpretation checks some modeled failures but no permissions

For both architectures, `Effects.All post` requires `post` at `.done`, requires every continuation result for `.undefined`, and rejects unimplemented/nonmemory operations and the modeled alignment errors. Each access request simply calls its continuation. Thus undefined architectural results are demonic choices in the proof judgment, not one convenient concrete run and not a Rust source-UB judgment. X64's executable testing evaluator separately chooses undefined values from a register-state hash; its runs do not establish the universal theorem. [X64 All](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/X64/OmniSemantics.lean#L13), [AArch64 All](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/AArch64/OmniSemantics.lean#L13), [concrete X64 evaluator](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/X64/Semantics.lean#L818).

`EffectsProbe.lean` checks ignored read/write/execute requests, rejection of `.unimplemented`, and rejection of a postcondition that holds for only one Boolean undefined result. `MissingState.lean` is an expected elaboration failure for `MachineData.mxcsr`; no failed file is imported as proof evidence. A missing `syscall` parser form is tested in the companion parser package.

### Full map membership, access requests, and authority are separate premises

`Mem.loadBytes m a n` looks up every address `a + i` for `i < n`, in modular BitVec address arithmetic. Scalar stores first require that the complete destination range is present in this map. An absent byte routes a scalar load/store to a nonmemory effect, which default All rejects. This is stronger than checking only the first byte; it is weaker than checking read/write authority over a mapped region. A mapped byte does not itself establish a VM page permission, allocation lifetime, Rust borrow/provenance resource, or valid instruction fetch. [Memory access definitions](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/Mem.lean#L23), [scalar load/store](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/X64/Semantics.lean#L300).

X64 `loadAvx` and `storeAvx` instead emit `require_*_access addr .W64`, then use `w.bytes` for their actual byte-map access. Fresh execution reports request widths 8 and 8 for W256 and W512, whose byte widths are 32 and 64. Checking every byte of the emitted request still underchecks those accesses. Alignment checking is another independent branch. [Vector access helpers](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/X64/Semantics.lean#L317).

`PermissionInterpretation.lean` defines a stricter interpretation over the actual X64 Effects type: read/write predicates receive each emitted request's byte width, an execute predicate receives its range, undefined choices remain universal, and errors remain false. The checked `permission_erasure` theorem proves that this interpretation implies default All. A two-write request skeleton is accepted by default All and rejected when all write permissions are false. This is a proved logical strengthening at the effect-tree boundary. It is not a proof that the producer emits every physical access, nor a complete vector-footprint repair, nor an independent trace adequacy theorem. Full memory mutations and restoration are illustrated separately by the comparative frame probe.

### The build diagnostic has a localized explanation and an unresolved root cause

The shared build exited zero but emitted pretty-printer fallbacks for unknown free variables while logging memory tactic subgoals. The preserved diagnostic summary records affected declarations and message kinds. Pinned `Tactics.lean` obtains expressions from subgoal metavariables and logs them at `Found sep goal`, `Solved by exact`, and `Already solved` sites without a local `subGoal.mvarId.withContext` at those calls. A mismatched logging context is a supported explanation for these particular fallbacks; a definitive Lean-level root-cause reproduction was not performed. No panic/assertion occurred. Importing and printing the checked declarations produced no such fallbacks. Their axiom lists are the proof-closure evidence; the diagnostic is not silently classified as a healthy memory-tactic run. [Logging sites](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/Tactics.lean#L438).

## Boundaries

- **Known not to apply:** default All does not establish access permissions; the owned strengthening does not recover bytes omitted from vector request widths.
- **Known not to apply:** the selected admitted X64 examples are not closed proofs. The selected AArch64 arithmetic/shift example has additional native reduction trust on the observed Lean version.
- **Not examined:** independent ISA refinement for carry/overflow flags, overlap, partial registers, shifts, faults, feature modes, and SIMD/FP. Kraken's review guidance and native test suite are validation procedures, not an inspected semantic-equivalence theorem. The authoritative instruction details themselves remain unexamined here, beyond the model's explicit scope and MXCSR omission.
- **Not examined:** kernel rechecking on `nightly-2026-09-21`, full imported theorem closures for every example, a complete producer-to-trace adequacy theorem, resource/ABI linking, atomics, weak memory, devices, and system execution.
- **Unknown:** the definitive cause and version dependence of the memory diagnostic. No upstream source was modified to suppress it.

## Evidence

Primary Git sources are pinned throughout the links. `source-manifest.json` records source identities and narrow symbols. `support/results.json` records all seven owned Lean invocations and expected statuses. `X64Closure.log`, `AArch64Closure.log`, and `NativeAxiom.log` preserve closure evidence; `AArch64Add.lean` preserves the new arithmetic proof; `EffectsProbe.lean` and `PermissionInterpretation.lean` preserve the access experiments. Initial ordinary elaboration failures are retained as initial logs, clearly distinct from final successful checks.

The source archive prerequisite was independently acquired by the parent workflow at SHA256 `b2acfb541396a9cacec36bf4e954b9294ae4272d4d32e61f73c8716cf2de1d60`. The package does not require that local archive or compiled library for its account; revalidation needs a fresh built library for the identified source/toolchain. Observation date: 2026-10-14. No native Rust, target assembly, or hardware test ran in this package.

Historical command, generated-manifest path and log strings are explicitly path-normalized for publication; `public-path-projection.json` records original and public hashes. Raw process statuses and technical outcomes are unchanged. Historical producer hashes refer to their original observations; the package file manifest binds the published bytes. The retained Rust/Lean program and source-archive bytes are unchanged.

## Revalidation

Build the exact Kraken source with the selected Lean version, then run `python3 support/run_lean.py --lean /path/to/lean --kraken-lib /path/to/build/lib/lean`. Inspect `results.json` and the exact dependency lists, especially `sorryAx` and the native verifier axiom. Repeating this on the requested nightly is a separate version-specific observation.

For access changes, diff scalar/vector request sites and both All definitions, rerun the width probe, and check the owned erasure theorem. Adding a permission conjunction alone is insufficient if a producer still emits W64 for larger accesses. For instruction correspondence, inspect a named reference ISA's exact configurations and prove or validate each selected operation relation; these probes do not replace that work.

*Authored by an AI agent acting on joshlf's behalf.*
