# Rust inline and global assembly at nightly-2026-05-31

## Summary

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, Rust inline assembly is an explicit semantic boundary rather than an opaque function call. `asm!` and `naked_asm!` reach MIR as `TerminatorKind::InlineAsm`, where rustc still records the assembly macro kind, template, typed operands, options, source-line spans, control-flow targets, and unwind action. `global_asm!` follows a different path: rustc keeps it as a module-level HIR item and later emits it as a `MonoItem::GlobalAsm`.

The Rust Reference makes several optimizer-visible promises part of the contract. Options such as `pure`, `nomem`, `readonly`, `preserves_flags`, `noreturn`, and `nostack` constrain what the assembly may do; violating some of those promises is undefined behavior. The instruction semantics themselves are target-specific, and the Reference explicitly treats the assembly language as opaque to rustc except for operand substitution and the declared interface.

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, that boundary loses most of the information rustc still has. Charon translates a MIR inline-assembly terminator to an ULLBC `InlineAsm` containing only the rendered template string, control-flow targets, and unwind target. It drops operands, register constraints/classes, options, and per-line source spans. ULLBC→LLBC then drops the unwind edge as well. Separately, Charon's crate traversal explicitly skips `GlobalAsm` items.

For verification, the consequence is stronger than “assembly is unmodeled.” At this pin, the extracted representation is insufficient to reconstruct the Rust-declared interface and optimizer promises of inline assembly, while global assembly can disappear from the translated item universe entirely. A sound consumer must therefore treat these cases as explicit unsupported/opaque trust boundaries unless another independently justified mechanism supplies the missing semantics.

No fresh compilation, Charon extraction, assembler run, or target execution was performed.

## Applicability

Language claims apply to `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

Compiler claims apply to `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the compiler revision behind `nightly-2026-05-31`.

Extraction claims apply to `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, Charon 0.1.210 as pinned by Aeneas nightly-2026.06.03.

This report distinguishes function-scoped `asm!`, `naked_asm!`, and module-scoped `global_asm!`. It does not infer behavior for adjacent Rust or Charon revisions.

## Findings

### Rust's inline-assembly contract includes more than the instruction text

The Reference defines `asm!`, `naked_asm!`, and `global_asm!` as ways to embed handwritten assembly. For ordinary `asm!`, the assembly is integrated into a Rust function and must obey Rust's inline-assembly rules. `naked_asm!` constitutes the full body of a naked function. `global_asm!` emits assembly at global scope and can define whole functions or other assembler-level objects.

The assembly syntax itself is target-specific and, except for template substitution, opaque to the compiler. Rust nevertheless gives the invocation a structured interface: templates, input/output registers, `inout` relationships, constants, symbols, labels, clobber ABIs, and options.

**Evidence:** **normative** Rust Reference.

### Assembly options are semantic promises to the compiler

The Reference assigns optimizer-visible meaning to options. `pure` promises no side effects and eventual return; `nomem` promises no access to externally accessible memory and no synchronization; `readonly` permits reads but forbids writes and synchronization; `preserves_flags` constrains flags; `noreturn` promises no fallthrough; and `nostack` constrains stack use.

These are not descriptive comments. Rust allows optimization based on them, and the Reference gives explicit undefined-behavior examples for violating promises such as `nomem`, `readonly`, `noreturn`, and `nostack`.

A verifier that sees only instruction text cannot in general recover these Rust-level assumptions, especially when the instruction language is deliberately opaque and target-specific.

**Evidence:** **normative**.

### rustc carries a structured inline-assembly terminator through MIR

The pinned rustc development guide describes the lowering pipeline from AST through HIR and THIR to MIR. It identifies three persistent components: template pieces, operands, and options. Type checking validates register classes and operand types; THIR resolves `sym` operands to functions or statics; MIR lowers split `inout` operands to explicit input values and output places.

Pinned MIR represents inline assembly as a terminator because assembly may diverge. `TerminatorKind::InlineAsm` records:

- the macro kind (`asm!` or `naked_asm!`);
- template pieces;
- operands;
- options;
- source spans for assembly lines;
- valid control-flow targets;
- an unwind action.

rustc's unwind passes specifically inspect the `MAY_UNWIND` option when deciding whether an inline-assembly terminator can unwind. This is implementation evidence for the pinned compiler; `MAY_UNWIND` is not promoted here to a stable Reference guarantee where the inspected Reference does not specify it.

**Evidence:** rustc **documentation** and **source**.

### Global assembly is a separate compiler item, not a MIR inline-asm terminator

Pinned HIR has `ItemKind::GlobalAsm`, with an `InlineAsm` payload plus a fake body used to type-check symbol operands. Code generation resolves `const` and `sym` operands and emits the template, operands, options, and line spans through the global-assembly codegen interface.

The monomorphization layer has a distinct `MonoItem::GlobalAsm`. This separation matters for coverage: a tool that only translates function MIR does not thereby cover module-scoped assembly.

**Evidence:** rustc **source**.

### Charon discards the structured operand/effect interface of inline assembly

Pinned Charon's rustc translator matches `TerminatorKind::InlineAsm` but destructures only `template`, `targets`, and `unwind`; the remaining MIR fields are ignored. It renders the template to a string, translates the control-flow targets and unwind action, and creates ULLBC `TerminatorKind::InlineAsm`.

The pinned ULLBC type documents the limitation directly: “For now we only preserve the template string.” Its representation contains only:

- `asm: String`;
- normal targets;
- an unwind target.

Consequently the exported ULLBC does not retain the MIR operands, register classes or explicit registers, input/output places, `sym` identities, `const` values as structured operands, options such as `nomem` or `noreturn`, macro kind, or per-line source spans.

This is a source-level information-loss result. It does not require executing Charon.

**Evidence:** Charon **source** + **derived** comparison with pinned MIR.

### LLBC loses the unwind edge too

During ULLBC→LLBC control-flow reconstruction, pinned Charon translates inline assembly to an LLBC statement containing only the assembly string and translated normal targets. The source contains an explicit TODO for unwind handling and discards the ULLBC `on_unwind` field.

Thus LLBC carries less information than ULLBC for this construct: even the already-reduced unwind distinction disappears.

**Evidence:** Charon **source**.

### Charon skips global assembly items

Pinned Charon's crate traversal maps ordinary functions, types, globals, modules, traits, and impls to translation kinds, but explicitly returns no translation kind for `GlobalAsm`.

A `global_asm!` item can therefore contribute machine code or symbols to the compiled crate while having no corresponding translated Charon item. This is a coverage boundary, not merely an inability to interpret an existing LLBC node.

**Evidence:** Charon **source**.

### A target instruction model alone would not repair the pinned extraction loss

To assign assembly semantics, a verifier would normally need an ISA/ABI model for the target instruction stream. At this Charon pin, that is necessary but not sufficient: the translation has already discarded Rust-side operand bindings and optimizer promises that connect the assembly to surrounding Rust state.

For example, knowing the semantics of a load instruction does not reconstruct which Rust operand supplied its address after operand metadata has been erased, nor whether Rust was permitted to assume `nomem` or `readonly`.

The safe architectural conclusion is narrow: a downstream proof cannot derive complete Rust semantics for these nodes solely from pinned LLBC plus an ISA model. It needs either richer extraction, a separately preserved interface, or an explicit opaque/trusted boundary.

**Evidence:** **derived**.

## Boundaries

- No fresh rustc, Charon, assembler, linker, or machine execution was performed.
- No ISA semantics are supplied for x86, Arm, RISC-V, or any other architecture.
- The report does not prove how LLVM lowers any particular instruction sequence or register constraint.
- The Reference and rustc source are intentionally separated: rustc's `MAY_UNWIND` representation is not treated as a stable language guarantee absent corresponding normative text at the pinned Reference revision.
- The report establishes information present or absent in pinned Charon source; it does not establish downstream Aeneas behavior for every assembly node.
- It does not claim that Charon silently accepts every assembly construct. Some paths may reject later; source-only inspection here establishes what the AST can represent and what crate traversal skips.
- `global_asm!` may create symbols whose semantics become observable through calls or linking even though the item itself is absent from Charon's translated item set. This report does not enumerate all such reachability paths.
- No Anneal policy for rejecting, modeling, or trusting assembly is selected.

## Evidence

**Normative:** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/inline-assembly.md`, blob `230dee5515749230c87ca37d54b153dec7f9c5ab`: macro scopes, operands, target-opaque template semantics, options, optimizer promises, and UB conditions.

**Documentation/source:** `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `src/doc/rustc-dev-guide/src/asm.md`: AST→HIR→THIR→MIR→codegen pipeline, structured operands/options, and MIR role.
- `compiler/rustc_middle/src/mir/syntax.rs`, blob `07eaa085fabc9742d0d51c73eeba91dcc9e67d2e`: full MIR `InlineAsm` fields and unwind action.
- `compiler/rustc_hir/src/hir.rs`, blob `59d1b4b5576ee47ea6c994977d40d5a948f139ce`: `ItemKind::GlobalAsm` and its fake type-checking body.
- `compiler/rustc_codegen_ssa/src/base.rs`, blob `78bc07869895ad2a8b67cb5d6115eb1cdbc96db3`: global-assembly operand resolution and codegen.
- `compiler/rustc_middle/src/mono.rs`: `MonoItem::GlobalAsm`.
- `compiler/rustc_mir_transform/src/ffi_unwind_calls.rs` and `abort_unwinding_calls.rs`: inline-assembly unwind treatment.

**Source:** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.

- `charon/src/bin/charon-driver/translate/translate_bodies.rs`, blob `c03ca8077f131a2ef701e9d27eaa9e69bb617124`: MIR inline assembly reduced to rendered template, targets, and unwind.
- `charon/src/ast/ullbc_ast.rs`, blob `3c6179f10742b2ee82c8ca07e6d51be6c8dc7694`: ULLBC inline-assembly representation.
- `charon/src/ast/llbc_ast.rs`, blob `40f29f8a4b19f98e929b5fe82b8a009d813120ad`: LLBC inline-assembly representation.
- `charon/src/transform/control_flow/ullbc_to_llbc.rs`, blob `07322359e92f92a4d8b55865a67257bedacb0a62`: normal targets preserved while unwind is discarded.
- `charon/src/bin/charon-driver/translate/translate_crate.rs`, blob `53536c6df6e241c9655840f6b1f8a4aca2113f90`: `GlobalAsm` explicitly skipped.

No evidence above is fresh **execution**.

## Revalidation

For a later pin, first diff the MIR `InlineAsm` fields, Charon's translator arm, ULLBC/LLBC assembly nodes, ULLBC→LLBC conversion, and the crate traversal's `GlobalAsm` handling.

On an execution-capable surface, use one target-specific fixture containing: an `asm!` with an input, output, `sym`, `const`, and at least one optimizer-relevant option; a diverging or labeled-control-flow case; an unwind-enabled case if supported by that toolchain; a `naked_asm!` function; and a `global_asm!` definition referenced from Rust.

Preserve exact rustc and Charon revisions, target triple, commands, MIR, serialized ULLBC/LLBC, object symbols, diagnostics, and hashes. Compare the MIR operand/options/targets/unwind data against ULLBC and LLBC and verify whether the global-assembly item appears in Charon's item universe.

That probe establishes the concrete extraction behavior for the tested pin and target. It does not establish ISA-level correctness of the handwritten assembly.
