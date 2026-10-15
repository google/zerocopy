# Sail RV64D supplied-word decoding: failure domain, Machine success and state framing

## Summary

The actual generated decoder reads privilege state even for ADD word `0x002081b3`. Lean therefore formally refutes universal decode→execute success with only x1/x2 initialized. A separate positive theorem succeeds for every pair of 64-bit operands and every `mseccfg` value when x1/x2, Machine privilege and that CSR are present: actual decoding and execution retire successfully, changing only x3 to the modulo 2^64 sum. An exact effect certificate proves the decoder's Machine path reads privilege, then `mseccfg`, then returns the selected ADD. Actual encoding and closed byte-word layout are also checked.

The 16-theorem diagnostic and four-theorem Machine module both passed official Lean 4.29 at trust level zero; independent unchanged-source replays produced identical artifacts. This is the configured, repaired full-model integration subject, with disclosed assumptions. It does not include memory fetch, step/PC advancement or an ABI/Rust bridge.

*Authored by an AI agent acting on joshlf's behalf.*

## Applicability

The [published integration subject](https://github.com/google/zerocopy/blob/f0d53bae94412c92b1bbd5aac8c11ba3695eb3eb/reports/sail-rv64d-lean-integration-effects-and-framing-2026/REPORT.md) combines Sail `7e0e53d183cad75b8f36bfbbecc0ef75614a8418`, riscv/sail-riscv `7d3c9c2568b77f516783aa2ac63bd9c0e0c6df86`, lean-sail `01bb54c7c8a69e52ba11863c67e7c403a6cd198a` and official Lean 4.29.0 AArch64 Linux `98dc76e3c0a9b856c9b98726b713fb04fab16740`. It uses `rv64d_v256_e64.json`, architecture interface 2, default FakeReal, upstream proof-oriented Lean switches and all-modules generation. The configuration and two integration-patch hashes are in REPORT.json. Only the final subject, incorporating termination-ranking maintenance and three abstract undeclared-hook bindings, supports these results. It is not unchanged upstream generation or a source-generator correctness proof.

The checked model import closure is the same 143 compiled modules as the published subject. Replays validated their exact hashes; they did not rebuild them. [Pinned base files and archive hashes](support/published-base.json) and [143-import preflight](support/import-identity-preflight.json) bind this result to that subject without copying its full source/tool mirrors. The selected real AST is `RTYPE (Regidx 2, Regidx 1, Regidx 3, ADD)` in rs2/rs1/rd/op order.

## Findings

### Encoding and word layout are checked separately from fetching

`encode_add` proves actual `Functions.encdec_forwards selected_ADD = pure 0x002081b3`. `selected_little_endian_word` proves that appending bytes `00`, `20`, `81`, `b3` from high to low yields that word; the corresponding low-address-first layout is `b3 81 20 00`. This is a closed BitVec equality, with no model memory read. Basis: source + execution. [Accepted diagnostic](ByteDiagnostic5.lean).

### The original x1/x2-only universal success claim is false

The actual `Functions.ext_decode` equals a real leading `cur_privilege` read with an existential continuation. Missing that register causes interpreted `Unreachable` with the entire original state unchanged, both for decoder-only and for actual decoder→executor composition. The accepted `Controls.fixture12` has x1=1 and x2=2 but no privilege entry; checked fixture theorems establish its actual errors. Specializing the alleged universal success theorem to this fixture yields incompatible error/ok constructors. `x1x2_only_composition_success_is_false` therefore refutes exactly the original all-operands/all-states, x1/x2-only domain. This is semantic counterevidence, not an inference from an unsuccessful proof script. The fixture is admitted by the sequential model’s partial register map; it is not claimed to be a complete architectural state, and the result does not imply that hardware ADD intrinsically requires this CSR. Anneal must justify decoder and platform-state invariants before composing instruction proofs. `decoder_is_not_pure_selected_add` separately rejects a state-free pure decoder equality. Basis: source + execution. [Independent diagnostic review](support/independent-byte/REVIEW.md).

The generated LPAD guard asks whether Zicfilp is enabled before comparing this word's opcode. That extension check reads privilege and calls `get_xLPE`, explaining why a non-LPAD ADD word still needs decoder state. [Pinned narrow source fragments](support/source-fragments/manifest.json).

### A distinct stronger Machine domain succeeds with arbitrary CSR contents

`decode_add_machine` quantifies every `csr : BitVec 64` and every actual sequential state with `cur_privilege=Machine` and `mseccfg=csr`; actual decoding returns the selected ADD and the exact unchanged state. It needs no x1/x2 premise because it does not execute the instruction.

`decode_execute_add_machine` additionally quantifies arbitrary `a b : BitVec 64` and assumes x1=a, x2=b. It runs actual `ext_decode`, binds the result to actual `Functions.execute`, and proves:

```text
.ok (Retire_Success ()) {s with regs := s.regs.insert x3 (a+b)}
```

This is equality of the entire final state. Every other register, including PC, nextPC, privilege and the CSR, and all memory, tags, cycleCount and sailOutput are framed. Unrelated register entries need not be present. CSR bits are unrestricted; neither MLPE value is assumed. The new theorem leaves the earlier weak-domain refutation intact. Basis: source + execution. [Accepted Machine source](MachineDecodeFinal2.lean), [independent review](support/independent-machine/REVIEW.md).

### The real Machine decoder path has exactly two reads

`decoder_machine_effects` exhibits a continuation k such that the entire actual decoder is the `cur_privilege` read followed by k, and k Machine is exactly the `mseccfg` read followed by pure selected ADD. Thus this decoder branch has two reads, no writes or hidden extra effects/errors. Other privilege continuations remain unconstrained. The Machine helper uses generated `get_xLPE.eq_def`; continuation equality considers both actual extracted MLPE Boolean values. The proof supplies no replacement decoder or semantic definition. Basis: source + execution.

## Boundaries

The result begins with an already supplied 32-bit word. Memory-byte loading, instruction-length selection, translation, permissions, faults, fetch/step/postlude bookkeeping and PC+4 are not examined by these theorems. A Rust ABI/register assignment, memory/resource relation, compiler correctness, hardware correspondence and weak-memory claim remain outside scope. The positive Machine premises are sufficient here; minimality and other privilege modes are not established.

All 20 individual axiom lists are retained. Eleven diagnostic lists and three Machine lists contain `propext`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound`; byte layout has `propext`/`Quot.sound`; fixture operand presence has the three logical foundations. Three diagnostic composition/refutation lists and Machine composition each have the disclosed 78-name whole-executor syntactic closure. It includes abstract platform/FP interfaces, not merely effects reached on ADD. None contains `sorryAx`. The [base report's assumptions and transformations](https://github.com/google/zerocopy/blob/f0d53bae94412c92b1bbd5aac8c11ba3695eb3eb/reports/sail-rv64d-lean-integration-effects-and-framing-2026/REPORT.md) remain part of the subject boundary. No new axiom, sorry/admit or native_decide appears in the accepted sources.

Accepted Machine source comments saying “uncompiled” or “proposed” are inherited stale comments. The exact executed bytes are retained; successful whole-file receipts and independent review establish their accepted status. Failed-development streams may print declarations containing temporary elaborator admissions; those failed files are never acceptance evidence.

## Evidence

Evidence was acquired on 2026-10-15. [Diagnostic source](ByteDiagnostic5.lean) SHA256 is `5a71c58874e82df4788df8e1f9489567f70e38d14d8b6dde112dfd5f0ae16446`; artifact `b0ace1a1595a984ae81b48d9c47b38c6769136597a529efaa8d13894375dc35e`. [Machine source](MachineDecodeFinal2.lean) SHA256 is `fe89f0f6f1bf36db7877a9848e9c68d81d8ed130c354a9f6f7e2c7dee6c96965`; artifact `c8401aabc472b3a5c367a32b5248f7a5310957aeec8be745002ca99f6d49bcae`. [Exact artifacts](support/accepted-artifacts.tar.gz).

| Module | Author check | Independent replay | Individual closures |
| --- | --- | --- | --- |
| Diagnostic, 16 theorems | 0; 2.238 s | 0; 2.502 s; identical artifact | [16 lists](support/diagnostic/accepted-axioms.json) |
| Machine, 4 theorems | 0; 3.251 s | 0; 3.496 s; identical artifact | [4 lists](support/machine/accepted-axioms.json) |

[Author diagnostic receipt](support/diagnostic/accepted-native.json), [author Machine receipt](support/machine/accepted-native.json), [independent diagnostic receipt](support/independent-byte/result.json) and [independent Machine receipt](support/independent-machine/result.json) retain complete argv, status, timing, resources and hashes. Separate complete stdout/stderr preserve theorem types, individual axiom lists and ordinary unused-simp warnings. Independent preflights rechecked the official compiler, original inputs and every copied import. All accepted checks used `-j1 -M4500 --tstack=400000 -t0`, one compiler, 120-second timeout plus five-second grace; no timeout or panic occurred.

[Failed development](support/failed-development.tar.gz) retains the author's unsuccessful diagnostic/Machine scripts and outputs; [original designer pilot](support/original-designer-failed-pilot.tar.gz) retains its three failed checks. These explain tactic/alias/propositional-unfolding failures; they supply no accepted theorem. The corrected proof explicitly unfolds the readReg alias and `PreSail.readReg`, types the dependent effect constructor, and reuses the accepted actual-executor full-state theorem. The archives preserve failed versions without altering accepted sources. [Upstream model license](support/licenses/LICENCE) accompanies narrow generated source excerpts. Package membership and archive member identities are in [manifest](package-manifest.json).

## Revalidation

Follow [reproduction instructions](REPRODUCE.md). Restore the exact 143 compiled imports and Proof/Controls dependencies from the immutable base package; verify all hashes before fresh output compilation. Compile the unchanged diagnostic, then unchanged Machine source at `-t0`; require whole-file exit 0, all 20 individual lists without sorryAx, and compare artifact hashes on the pinned toolchain. The portable reproduction driver is preserved but was not run while assembling this package.

For a changed model or toolchain, the discriminating obligations are the actual decoder privilege prefix, missing-privilege error fixture and weak-domain refutation, arbitrary-CSR Machine decoding, two-read certificate and whole-state composition. Recheck the source guards and generated well-founded equations as well as replaying the proofs. Passing encoder/layout alone cannot validate decode success or fetching.
