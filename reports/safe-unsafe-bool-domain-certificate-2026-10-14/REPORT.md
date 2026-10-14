# A complete small safe API over an unsafe Boolean representation operation

## Summary

The original `checked_bool(u8) -> Option<bool>` API has one unsafe operation: by-value transmutation after a `byte < 2` guard. A Lean certificate covers every byte input, preserves an invariant across every modeled step, and excludes the first invalid-value operation. Native execution passes all 256 inputs. Widening the guard admits a bad input that a model restricted to `Fin 2` hides.

This is a bounded source-domain experiment. The Rust-to-state-machine interpretation is explicit and manually reviewed; it is not a checked Rust parser/import theorem or a proof about zerocopy's whole safe API.

## Applicability

The complete API, native harness and logical certificate are preserved under `support/`, with SHA-256 identities in `input-identities.json`. The certificate was checked using Lean 4.31.0 at revision `68218e876d2a38b1985b8590fff244a83c321783`; native compilation used rustc 1.99.0 `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, aarch64-apple-darwin, edition 2021 and default debug settings. The program has no references, callbacks, allocation, custom destruction, shared state or external code other than core's transmute.

The selected contract interpretation uses the separately pinned Reference and core transmute documentation. It does not silently identify all Rust revisions or every operational Rust model.

## Findings

### The public domain includes every byte

Basis: source + normative contracts + derived interpretation.

The API receives an ordinary valid `u8` by value. Its semantic input domain is `Fin 256`; it imposes no caller precondition that the byte already encodes a Boolean. Values zero and one return Some(false/true); all other values return None before transmutation. The [Reference validity rule](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/behavior-considered-undefined.md#L115) makes producing an invalid Boolean immediately UB. The [core transmute contract](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/intrinsics/mod.rs) requires valid source and result values. Boolean and u8 size and scalar validity justify this selected by-value interpretation; there is no pointer permission or padding-bearing payload in this specimen.

`castResult` explicitly returns bad for an invalid Boolean representation, retaining inputs that a Bool carrier would omit. `Step` distinguishes entry, pending cast and completed outcomes. The entry invariant holds for every Byte. The cast-state invariant requires value zero or one; the guard establishes it before the unsafe operation. The terminal invariant excludes bad. `step_preserves` checks each constructor, so a finite-prefix induction cannot reach bad from an entry state. It does not assume complete implementation safety.

### Checked properties and negative witnesses

Basis: original Lean definitions + kernel execution.

`all_inputs` proves the whole output specification for every Byte, and `no_bad` excludes the bad outcome. `entry_covers_all` has no axioms; the other general endpoints report only propext and Quot.sound. There is no sorryAx, native-computation axiom or producer-added assumption. The exact printed assumption list and successful status are preserved.

`wider_guard_bad` proves that threshold three reaches bad on byte two. `unguarded_bad` exposes the same invalid-value operation without a guard. These are logical witnesses; no invalid native Rust is executed. `narrowed_model_hides` proves that the changed implementation agrees with the desired output on every `Fin 2` input, despite its bad native-domain input. Thus a correct theorem over the narrowed carrier supplies no coverage of the advertised safe entry domain. The independently selected consumer domain must remain Fin 256.

The API itself and the predicate being proved are separate preserved artifacts. Relating their bytes to this state machine remains trusted manual capture. The experiment does not claim that matching model and generated requirement detects a common erroneous interpretation automatically. A production certificate must prove or retain that import/contract premise visibly.

### Native execution and scope of the comparison

Basis: execution.

The native harness calls the exact complete API on all 256 u8 values using black_box, compares each output to an independently written match, and reports `all_native_u8_inputs=256; accepted=2; rejected=254`. Compilation and execution exit zero with empty stderr. The guard prevents the unsafe operation on every other byte; the harness executes no invalid Boolean construction.

The kernel check took about six seconds in this observation, native compilation about half a second, and the native exhaustive run about 46 ms. These single observations include startup and cache effects; they are not a candidate ranking, scalability claim or comparison with a proof-produced compiler. `results.json` records exact values. Initial failed proof elaboration remained scratch-only and was never accepted as evidence.

### What this discharges for an Anneal design

Basis: derived.

This completes a representative P135 safe-wrapper/domain-coverage experiment under the named import and contract interpretation. It demonstrates an all-permitted-input theorem, a bad-operation monitor, a guard-establishment obligation and a discriminating narrowed-model witness. A producer may discover a proof or invariant; it must not select a smaller caller domain to make the proof succeed.

The result supports retaining representation invalidity until after checked guards, and selecting native entry coverage independently from mathematical decoding. It does not discharge general byte loads, provenance, aliasing or lifetime obligations. Those require richer state and primitive interpretations even when the same Fin 256 decoder is reused.

## Boundaries

**Known checker boundary (source reviewed 2026-10-14):** the recorded Lean 4.31 and legacy 4.30rc2 runs are observations conditional on checker soundness. Their pinned `src/kernel/inductive.cpp` lacks the final nested-parameter validation added by [fix a39eab69](https://github.com/leanprover/lean4/commit/a39eab69e1eee9ad38f4efe507907b1026a77808). The [official 4.32.2 notes](https://lean-lang.org/doc/reference/latest/releases/v4.32.2/) describe arbitrary false-theorem acceptance and a combined external-checker exploit. This source finding does not establish exact exploit portability or invalidate these owned terms, but successful exit and a clean axiom list do not establish sound acceptance of arbitrary producer proofs. No exploit was executed, toolchain upgraded, or recorded result rewritten. A deployment needs a separately justified checker/version and dependency policy; presence of the fix in 4.34.1 is not a universal soundness theorem.

Known not to establish: verified Rust parsing/elaboration, rustc compilation, machine-code execution, arbitrary safe Rust contextual soundness, or a zerocopy-wide safety theorem. The native test corroborates this build; its result is not the source correspondence proof.

The manually selected state machine is a contract interpretation for this finite, by-value fragment. Additional operations or hidden source effects require extending and justifying it. No claim is made for uninitialized inputs, pointers, unwinding cleanup, threads or foreign interactions. Future integration into Anneal must bind the complete source, domain, semantics, property and proof independently.

## Evidence

All evidence was observed 2026-10-14. The package preserves complete owned Rust/Lean inputs, identities, exact proof assumptions, compile/run outputs and timings. Evidence roles are normative for the selected Rust contracts, source for the inputs, execution for the two tool runs, and derived for the interpretation and adoption implications. No larger upstream source mirror or platform binary is needed.

## Revalidation

Copy support to fresh scratch via `python3 -B support/revalidate.py --lean-bin <Lean4.31>/bin/lean --rustc <Rust1.99>/bin/rustc --out <new-scratch>`. Recheck every general endpoint and axiom list, then the 256 native inputs. Changing the guard, input type, return representation or source operation requires a new import and validity review; the old theorem does not certify changed source bytes.

*Authored by an AI agent acting on joshlf's behalf.*
