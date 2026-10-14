# Rust inline assembly contracts and proof obligations

## Summary

A source-level proof of an `asm!` block must justify its operand and effect contract for every compiler-permitted instantiation covered by the claim. An ABI theorem for a standalone function supplies a different interface. A theorem for one emitted register allocation can support a build-specific certificate, but does not establish that the source template is valid for all allocations or future compilations.

The most useful first fragment is one instruction that reads all inputs before producing its output. Our checked finite-register theorem permits output/input overlap for atomic addition, while a two-instruction early overwrite has a concrete counterexample. Current rustc also accepts two deliberately false effect contracts in compile-only specimens. Their acceptance establishes that compilation is not a semantic proof of the options; neither specimen was executed.

## Applicability

Normative rules are read from Rust Reference revision `2dafab96d919d6ab2884488e970bf95610ff83eb`, principally `src/inline-assembly.md`. Compiler observations use Rust 1.99.0 `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, target `aarch64-apple-darwin`. The separate pilot report preserves real AArch64 inline/naked implementations and generated LLVM interfaces. `support/InlineContracts.lean` is an owned contract model checked with Lean 4.34.1 `5045d0056413266e57c625dcd7c365b10e377c52`; it is not an import or formalization of the entire Rust Reference.

The report investigates AS08–AS10 and the ordinary-inline unwind part of AS13 in #3874. All semantic conclusions about the owned model are confined to its stated finite register and access abstractions.

## Findings

### Operand timing determines the quantifiers

Basis: normative + execution + derived.

Read the source interface before selecting assembly registers. Inputs describe initial values; outputs describe the produced values and permitted destruction. Tied operands require the same physical location. Late outputs permit overlaps that ordinary outputs exclude, subject to the specified input-consumption timing. Register classes, explicit registers, subregisters, type widths and implicit instruction operands all constrain the instantiation relation.

Let `instantiate(template, assignment)` produce the physical program, and let `allowed(assignment, operands, target)` state the compiler-facing constraints. A reusable source theorem needs the shape:

```
∀ assignment, allowed assignment →
  ∀ initial_state, input_relation assignment initial_state →
    safe_execution_and_contract (instantiate template assignment) initial_state
```

A certificate for the final compiled program can replace the first universal quantifier with an exact bound assignment and bytes. The consumer must then reject stale assignments and recompilations that invalidate that binding. It cannot export the stronger source-template claim.

`atomicAdd_all_allocations` proves the result for arbitrary source/output registers in a three-register, 8-bit model; `atomicAdd_frame` preserves all non-output registers. The model reads both operands from the pre-state. `illegal_lateout_witness` instead models moving an input into the output before reading the other input: output register 1 overlaps that unread input, and inputs 1/2 yield 2 rather than 3. This is a checked counterexample to accepting late-output overlap without proving its timing premise. It does not claim three registers model every target allocator.

### Effect promises need independent semantic evidence

Basis: normative + source + execution + derived.

For each option, an adapter should translate its promise into a separately checkable obligation rather than infer the promise from the option being present:

| Contract dimension | Required evidence | Distinguishing failure |
|---|---|---|
| External memory effects | Complete read/write footprint, including implicit accesses | Read or store hidden by an overly strong memory declaration |
| Purity | Allowed observations depend only on declared inputs and permitted read state; no extra observable effects | Hidden state dependence or externally visible event |
| Flags/state preservation | Equality of all target-specific state covered by the promise | Only integer flags modeled while an omitted state component changes |
| Stack usage | Scratch bounds, restoration and the applicable stack-option premise | Undeclared stack use or SP not restored |
| Nonreturning/control exits | Every possible exit belongs to the declared exit interface | Fallthrough or a jump to an unrelated continuation |
| Calls | Call-clobber set plus callee/resource/exit contract | Callee destroys an undeclared register or escapes by an inadmissible unwind |

`compile_only_invalid_contract.rs` contains a store advertised as `nomem` and a flag-changing comparison advertised as `preserves_flags`. Rustc emitted metadata successfully for both. We compile declarations only; no call or invalid Rust execution occurs. These results support the need for semantic checking, not a compiler defect: the interface imposes caller/author obligations.

The real register-only pilot uses conservative flag clobbering and `pure, nomem, nostack`. Its emitted LLVM call includes the actual operand constraints and flag clobber. A load pilot has an external-memory effect and a different LLVM memory interface. Preserve those generated interfaces with the source; the template alone does not identify the compiler contract.

### Whole execution matters even when bytes are restored

Basis: normative + derived + checked owned witness.

The owned `temporaryWrite` model preserves the final byte function while adding an out-of-footprint access to the trace. `final_frame_does_not_imply_trace_safety` proves both facts simultaneously. A final-state frame condition is therefore insufficient evidence for the complete footprint contract. A real adapter must interpret each modeled instruction access, width and fault condition, or prove an equivalent trace-safety theorem. Kraken's default access interpretation is examined in the companion Kraken reports.

This remains necessary for a read-only output contract: an OOB read may leave every final register and byte in an otherwise acceptable state. It also explains why byte equality cannot recover permissions, initialization or provenance that were erased from the state relation.

### Continuations, stacks and unwinding are distinct interfaces

Basis: normative + derived.

For ordinary inline assembly, the continuation belongs to compiler-managed Rust control flow. The proof must quantify the permitted initial scratch/stack state, restore the required state at each returning or label exit, and preserve the resources needed by that continuation. Ordinary inline unwinding restrictions cannot be relaxed merely by selecting an unwinding function ABI elsewhere.

Private assembly scratch memory and external memory have different contract roles. Treating all stack accesses as forbidden under every memory option would reject valid cases; treating them as unbounded private storage would accept invalid ones. The consumer needs a target-specific stack region, alignment, guard/probing premise where applicable, and a resource rule for each exit. A whole naked function instead begins with a function-call ABI state and must implement its own prologue/epilogue duties.

The source Reference permits compiler transformations that break a one-block/one-binary-instance assumption. Proof attachment must survive duplication, deduplication or outlining, or move to a post-compilation subject that enumerates all actual instances. Cross-block jumps and context switches require a richer continuation/environment relation; an intraprocedural proof does not establish it by default.

### A small admission interface

Basis: derived design assessment.

A useful proof-producing adapter can expose four independently bound claims: instantiated program identity; input/output/register relation; complete effects and exit relation; preservation of caller resources. Automation may propose proofs, allocations and summaries. The checker must reconstruct the exact advertised obligation and verify its proof, including dependencies on target state components.

Unsupported instructions or unmodeled preservation obligations should produce an explicit unsupported result. A false theorem about a simplified state must not substitute for a proof about the richer inline contract. Conversely, rejecting a missing model component need not force the entire assembler or optimizer into Anneal's internal logical TCB: checked local instruction summaries or a verified lifting relation are alternatives.

## Boundaries

The owned register and trace models demonstrate necessary distinctions; they do not formalize LLVM, rustc allocation, real stack permissions or the complete Rust inline contract. The false-contract specimens establish compile-time acceptance only. No invalid assembly was run.

The actual AArch64 pilot does not establish arbitrary source-template allocation correctness through rustc. Its Kraken theorem is about the selected fixed-register program; its native run and byte binding are separate evidence. There is no complete checked Rust/LLVM/ISA contextual-linking theorem in this package. Privileged operations, interrupts, relaxed memory, FP status and context switching require the separately researched extensions.

## Evidence

- [Pinned Rust inline specification](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/inline-assembly.md): `asm.operand-type.*`, `asm.options.*`, `asm.rules.*`, `asm.naked-rules.*`.
- [Pinned naked-function constraints](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/attributes/codegen.md): `attributes.codegen.naked.*`.
- `support/InlineContracts.lean`: arbitrary-allocation/frame theorems and checked negative distinctions. Reported axioms are `propext` for the first four theorems, none for `same_address_is_not_resource_authority`.
- `support/compile_only_invalid_contract.rs`, compilation log and tool identity: accepted metadata at Rust1.99/AArch64, never executed.
- Companion `kraken-rust-assembly-pilot-8af7806` report: native source, exact Kraken proof, LLVM operand constraints and linked-code observations.

## Revalidation

Check the named Reference clauses after an upstream change; inspect emitted LLVM operand/effect interfaces for the unchanged pilot at the compiler/target under consideration. Run `lean support/InlineContracts.lean` and inspect both exit status and theorem axiom output. Compile the false-contract source with `rustc --edition=2024 --emit=metadata --out-dir <scratch>`; never execute it. Acceptance is the observed compiler boundary, not the semantic expected verdict.

For a real adapter, add an instruction/operand mutant, a hidden-memory-effect mutant and an exit-resource mutant to the exact chosen checker. A passing general register witness cannot replace those source-specific checks.

*Authored by an AI agent acting on joshlf's behalf.*
