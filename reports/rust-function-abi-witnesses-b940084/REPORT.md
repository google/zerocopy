# Rust function ABI witnesses and assembly entry/return contracts

## Summary

An assembly entry contract needs more than Rust type sizes. It must describe argument/result placement, hidden parameters, extension and validity obligations, preserved machine state, stack/environment resources and admissible exits. Native Rust ABI evidence must be compiler/configuration specific; the current Reference offers no native-ABI stability guarantee and excludes it from naked functions.

The performed Rust witness makes the distinction concrete: a two-word `repr(C)` struct and a two-word Rust tuple use different LLVM signature shapes, a three-word C struct uses a hidden result pointer, a Rust slice has pointer/length operands and semantic attributes, and unit has no machine argument. Four-target C assembly witnesses independently show incompatible platform register/aggregate conventions. These are compiler observations, not verified ABI export or source-to-machine proofs.

## Applicability

Rust compiler source and execution are pinned to 1.99.0 `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`; actual Rust code generation uses `aarch64-apple-darwin`, optimization3, panic abort. The Reference is `2dafab96d919d6ab2884488e970bf95610ff83eb`. Platform sources are AAPCS64 `ec3e2fb69065768aa1caf298813a7808b50bc264`, Microsoft x64 documentation `281a0a0eae55fe97f5decd244db18ed5096d4687`, and Apple's live ARM64 ABI documentation, observed2026-10-14. Apple documentation has no immutable revision established here.

Apple clang21.0.0 (`clang-2100.3.34.2`) emitted C assembly for x86-64 Linux, x86-64 MSVC, AArch64 Linux and arm64 macOS14 without linking or executing cross-target code. C outputs are evidence for those compiler invocations only. They do not claim Rust cross-target execution or every platform ABI detail.

This report addresses AS06/AS11–AS13 and inputs to AS14/AS15. The actual naked leaf and native observations live with the companion pilot.

## Findings

### Layout, passing convention and semantic attributes are separate

Basis: normative + source + execution.

The Reference explicitly separates type layout from function-call ABI compatibility. Rust compiler `callconv::PassMode` represents ignored, direct, scalar-pair, cast and indirect passing; indirect passing also records metadata and stack-offset behavior. `FnAbi` adds calling convention, variadic information and unwind permission. Its construction uses target ABI mapping, layouts, virtual-call adjustment and caller-location information before the Rust/foreign ABI adjustment.

The actual generated LLVM signatures for the owned specimen are:

| Source shape | Observed LLVM interface at the pinned Rust target |
|---|---|
| C `Pair {u64,u64}` input/result | `[2 x i64]` argument and result |
| Rust `(u64,u64)` input/result | two `i64` arguments and `{i64,i64}` result |
| C `Triple {u64,u64,u64}` | hidden `sret([24 x i8])` output pointer and indirect input |
| Rust `&[u8]` | pointer plus length, with validity/alias/read and range attributes |
| Rust `()` argument/result | `void` function with no explicit machine parameter |

The pair example does not prove different physical registers in this target; it proves that identical size/alignment is insufficient to reconstruct the compiler interface. The triple's AArch64 assembly uses `x8` for the indirect result location while reading its input through `x0`. The slice's attributes cannot be recovered from “two words” either.

The inspected `arg_attrs_for_rust_scalar` derives `noundef`, nonnull and pointee properties from validity/layout information, then conditionally derives reference-related attributes using frozen/Unpin/global facts and compiler options. Deduced body attributes form another adjustment layer. These source facts are compiler behavior, not a complete normative Rust aliasing model. An ABI adapter must avoid inferring Rust permission simply from an LLVM attribute or its absence.

### Platform identity cannot be erased

Basis: normative + execution + derived.

The same C addition source emitted `%rdi/%rsi → %rax` on x86-64 Linux and `%rcx/%rdx → %rax` on x86-64 MSVC. The pair is directly rearranged through integer registers on SysV, whereas the MSVC specimen receives input/result pointers and uses vector moves. The three-word SysV input is loaded from the stack, with a separate result pointer. Both AArch64 specimens use `x0/x1` for the small scalar/pair cases and an indirect result location for the triple.

These observations discriminate configurations; a compiler can be wrong, so they do not replace the ABI specification. AAPCS64, Windows x64 and SysV each need their own entry/return predicate. At minimum record target triple, ABI spelling/canonical convention, relevant target features, compiler revision and flags, full signature/instantiation, argument/result passing witnesses and stack policy.

Apple's documented ARM64 choices include reserved `x18`, a platform red zone and differences from generic AAPCS64 in narrow arguments, aligned arguments and variadics. Thus `aarch64` alone is not a sufficient ABI identity. The scalar leaf avoids these discriminating cases; its successful run cannot generalize to them. Vector ABI classification can additionally depend on CPU features and platform rules.

### A reusable entry and return relation

Basis: derived.

Define `Enter(signature, abi, rust_values, resources, machine_state)` to require valid representations and placements, the stack/return continuation, admitted scratch state and transferred memory resources. Define `Return` to recover valid Rust outputs, the permitted event/exit, required preserved state and the caller's resource interpretation. The assembly theorem must cover all machine states admitted by `Enter`, including arbitrary values of unconstrained scratch registers.

A function proof should preserve complete callee-saved state, not a hardcoded list of registers copied from a different platform. It must account for machine return address behavior and, where relevant, stack arguments, alignment, red-zone/shadow-space ownership, SIMD/FP state and unwind metadata. Instruction semantics for `call`/`ret` supplies only the operational transition. The ABI predicate supplies the linking obligation.

For the register-only AArch64 add leaf, the companion Kraken theorem preserves the entire modeled `MachineData` except `X0`, computes modular addition and returns to the original `X30` bits. This is stronger than checking selected callee-saved registers, but only for the state Kraken models. It leaves ISA faithfulness, byte decoding and Rust source/resource interpretation explicit.

### Native Rust witness versus C wrapper

Basis: normative + source + derived.

A C ABI wrapper offers a publicly documented target convention and is a practical first domain for a whole-assembly implementation. It still requires Rust value validity and memory/alias contracts; `extern "C"` does not make arbitrary bits valid. Naked function bodies also have explicit source restrictions and must uphold their signatures and return/diverge requirements.

Native Rust integration could export compiler-pinned `FnAbi` evidence, but the current compiler structure is not a self-authenticating certificate. A consumer must bind it to the exact instance and build, verify its passing/attribute meaning, and connect it to the selected machine interface. The witness might be checked against a separately specified classification algorithm, validated against emitted code, or remain a declared compiler assumption. None of those routes is automatically supplied by printing an LLVM signature.

Hidden caller-location arguments, virtual receivers, unsized metadata, ZSTs, aggregate casts and indirect results are direct reasons to prefer a structured witness over source-level argument counting. A proof for one instantiation cannot be attached to every generic instance or a different signature merely because its symbol name resembles the original.

### Calls, callbacks and exceptional exits

Basis: normative + source + derived.

The callee interface must specify normal, divergent and exceptional outcomes independently. Rust's ABI/unwind policy and panic runtime decide which crossings are admitted; ordinary `asm!` has its own unwind restriction. Selecting an unwinding ABI does not erase that inline restriction. Native/foreign/forced unwinding and nonlocal jumps must be classified separately rather than treated as ordinary returns.

A verified helper call needs the helper's exact contract and identity, the caller-saved clobber/effect allowance, and a continuation invariant. A callback may safely use aliases retained by Rust, making resource restoration and reentrancy part of the theorem. A function that restores scalar outputs but invalidates a protected borrow can fail the Rust continuation. Whole-function frame/CFI metadata must describe actual prologue and exit behavior; a parser dropping those directives is not an unwind proof.

The performed pilot deliberately uses a leaf, panic-abort configuration and no unwind. It isolates the first ABI seam rather than providing empirical evidence for unwinding or callbacks. The resource/linking report supplies checked counterexamples and a conditional composition theorem for those higher-level obligations.

## Boundaries

No verified native-Rust `FnAbi` exporter, platform classification algorithm, loader or unwind runtime was constructed. No cross-target C code was executed. Four-target outputs and the selected Rust signatures are observations, not universal ABI conformance results. This report does not formalize all vector, variadic, SVE/SME, PAC/BTI or Windows unwind rules; it identifies their role and a disciplined restricted entry domain.

Apple's live documentation is version-limited by observation date. Generic AAPCS64 evidence does not silently establish Apple-specific behavior. The exact pilot can be rechecked without assuming the whole platform ABI has been mechanized.

## Evidence

- [Rust `FnAbi` and `PassMode`](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/compiler/rustc_target/src/callconv/mod.rs): `PassMode`, `ArgAttributes`, `FnAbi`, Rust/foreign adjustments.
- [Rust ABI construction](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/compiler/rustc_ty_utils/src/abi.rs): `fn_sig_for_fn_abi`, `arg_attrs_for_rust_scalar`, `fn_abi_new_uncached`, `fn_abi_adjust_for_deduced_attrs`.
- [Reference ABI rules](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/items/external-blocks.md), [layout](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/type-layout.md), [unwinding](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/items/functions.md), [naked constraints](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/attributes/codegen.md).
- [AAPCS64](https://github.com/ARM-software/abi-aa/blob/ec3e2fb69065768aa1caf298813a7808b50bc264/aapcs64/aapcs64.rst), [Microsoft x64](https://github.com/MicrosoftDocs/cpp-docs/blob/281a0a0eae55fe97f5decd244db18ed5096d4687/docs/build/x64-calling-convention.md), [Apple ARM64](https://developer.apple.com/documentation/xcode/writing-arm64-code-for-apple-platforms), [SysV primary sources](https://gitlab.com/x86-psABIs/x86-64-ABI).
- `support/abi_witness.c`, four generated assembly files, `results.json` and compiler identity. Companion pilot preserves Rust source/LLVM/object-binding evidence.

## Revalidation

Compile the C specimen with the same four explicit triples and compare the named functions' input/result accesses. Recompile the Rust specimen with `--crate-type=lib --emit=llvm-ir,asm,obj -Copt-level=3 -Cpanic=abort`; inspect signature types, attributes, hidden operands and final assembly. Changing compiler, target, ABI, flags, features or generic instance requires renewed evidence.

For a future structured ABI certificate, include negative controls for a wrong aggregate return mode, omitted hidden argument, stale signature, wrong target and false alias/validity premise. Merely reproducing these witness outputs would not validate that future consumer.

*Authored by an AI agent acting on joshlf's behalf.*
