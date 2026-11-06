# Exact HOL control preparation and execution gate

*Authored by an AI agent acting on joshlf's behalf.*

This frozen plan contains prepared source/data and proposed commands only. No control source has been staged, compiled or executed, and no new native process has run. The original positive program ran once and must not be repeated by the author. Existing C1–C9 descriptions did not grant execution; this plan also does not grant it.

The positive candidate is frozen separately at `reports/hol-light-s2n-bignum-add-native-replay-b19af693`: report SHA256 `dda6249e12763e4ae2bb12eea7947c63b2a3b017b57be1f2f75d8289650b2996`, manifest SHA256 `542dca2e5208bb559138078cf4aeccf9157011a75d5d06a4d67e843911182917`. This plan does not modify that package, its objects, source, positive executable, checker or observations.

## Subjects and producer scope

Reuse only the existing exact HOL b19 module and49-package hol54 switch in container `94afa6889b4a4af6f3dce4eb3e81bb6c698522130a9be617166e1a92a32535aa`. No module rebuild, install, acquisition, resource creation or upstream edit is proposed. Proposed new runtime writes are confined to a fresh `/home/opam/anneal-cross-output/controls` subtree; parent must approve its creation/staging and exact operations separately.

There are three separate source/producer subjects:

1. `source/ImporterControl.ml` loads only the unchanged `x86/proofs/base.ml` through the original inliner. Its additional original source closure is the34 original dependencies already traversed by the positive run, excluding `bignum_add.ml`. Predicted selected inliner census: one owned file +34 originals. The compiled HOL module contributes its existing47-file core. This program accepts a case/path pair and calls the actual `define_assert_from_elf`; it never loads the full bignum-add proof or either positive audit entry. It contains no `new_axiom` call. Each case below needs a **fresh process**, with the original qualified checker before/after base loading. Its expected pre-import runtime ledger is81 entries.
2. `source/ArithmeticObservation.ml` uses only the compiled HOL core, with no s2n imports. Three actual `NUM_REDUCE_CONV` calls should derive the concrete sum0, carry1 and false equality0=1 observations. Each conversion's left/right conclusion is checked structurally, and original `hyp` and axiom policy are checked. This is an arithmetic observation control, not an x86 state, Rust ABI or same-domain correspondence theorem.
3. `source/AxiomPolicyNegative.ml` is a separate core-only program and process. After the original qualified baseline policy passes, it deliberately registers `T` with the original `Hol_lib.Hol.new_axiom` and calls the captured original checker. `T` is provable, but registering it as a non-basic axiom should still violate this policy. No false desired-result axiom is introduced. This subject must never share a process/import entry with the importer, arithmetic or positive proof.

`build-one-control.sh` is the exact proposed owned preserving producer for these three whitelisted entries. It reuses the same inliner/preprocessor/compiler/linker operations and flags as the successful producer, preserves every generated intermediate and does not execute any binary. Each output must be initially absent. `native_once.py` remains ungranted and must not be staged or used.

## Exact finite cases and distinctions

| ID | Subject and expected observation | Classification |
| --- | --- | --- |
| C0 | Original1528-byte ELF, exact185-byte literal; importer accepts, original checker passes, closed definition theorem and completion marker print | Coherent importer baseline; no full positive-proof replay |
| C1 | Original ELF, literal `[0]`; importer raises `Failure("assert_word_list")` after readiness, without accepted marker | Expected byte-list/length rejection |
| C2 | Frozen `bad-text.o`, exact original185-byte literal; same original assertion failure | Expected single-byte binding rejection |
| C3 | Frozen `wrong-machine.o`, unchanged text; original loader rejects architecture with `unexpected ELF architecture: b7` | Expected domain rejection |
| C4 | Frozen `renamed-symbol.o`, unchanged text; original importer should accept, while separate `require_symbol.py` rejects absence of `bignum_add` | Accepted importer insensitivity plus independent name-binding rejection, not an importer symbol guarantee |
| C5 | Core-only arithmetic program prints three closed conversion theorems whose RHSs are respectively0,1,F, and original policy passes | Finite observation difference, not model execution/refutation |
| C6 | Separate axiom-negative process prints baseline and registered-`T` markers; captured original policy rejects with `check_axioms:`; no unexpected-acceptance marker | Expected original global-policy rejection, not an accepted theorem result |
| C7 | `check_shadow_fixture.py` rejects the exact text fixture containing `let check_axioms () = ()` | Static literal guard; fixture is never compiled, not a complete OCaml shadowing analysis |
| C8 | A copied successful log loses only its final marker; copied receipt explicitly binds that new SHA and still asserts exit0; unchanged observed verifier rejects `outer_end_once` | Harness completeness check, not a theorem rejection or merely a manifest-hash failure |
| C9 | Fresh nonexistent `objects/missing.o`; original `open_in` path raises a missing-file `Sys_error` | Operational I/O control, never counted as semantic or byte rejection |

`objects/` contains an unchanged coherent ELF copy and three prepared data mutants. `mutation-receipt.json` binds exact bytes and changes: C2 changes byte64 from243 to242; C3 changes byte18 from62 to183; C4 changes only two symbol-string bytes, renaming `bignum_add` to equal-length `bignum_bad`. No mutant is executable input to a CPU. Only ELF-reading/importer operations are proposed. The positive object was independently rehashed unchanged after data preparation.

## Execution acceptance and stop rules

The owner should first approve exact source/command hashes and source imports. Before any producer, verify the original23,177 source files,69 tools,2,417 compiler-library files, existing HOL generated objects, both original ELF inputs, original positive executable and every pre-existing positive output hash. Newly granted control files must lie only under the fresh controls subtree. Preserve actual tool versions/flags, all argv/cwd/env selections, full streams, phase-specific exit/status/time and artifact SHA256s.

After each producer, inspect actual inlined source inclusion paths/order and digest records against the declared imports before consuming its binary. Reuse the parent's approved final digest predicate; do not redesign an observation/lifecycle wrapper. Require the exact new binary SHA before/after each fresh case. An expected nonzero is accepted only for the named expected cause and absence of its forbidden completion marker. A timeout, assertion, unknown case, unexpected exception, extra axiom, incomplete ledger, identity discrepancy or producer failure is **not** a passing negative. Stop for parent diagnosis; do not repair/retry automatically.

The proposed native calls are six fresh importer processes (C0/C1/C2/C3/C4/C9), one arithmetic process and one negative-only axiom process. The C7/C8 checks and symbol observer are ordinary host/data checks. This is not nine independent kernel-negative tests. No source/library proof is weakened, and no checker's negative state survives its process.

Proposed bounds, not a grant: existing CPU2/memory4GiB runtime; one producer/proof process at a time; no parallel native cases; combined producer wall budget300s, each native invocation `timeout --signal=KILL 120`, combined native budget600s, additional controls outputs at most500MiB observed before/after, and the existing overall2GiB project allowance. No RSS/native-PID/procfs measurement is required; wall time and ordinary captured status are sufficient. Stop on any bound rather than infer completion.

## Efficient handoff and remaining scope

The [execution-efficiency skill](../../../skills/execution-efficiency/SKILL.md) v0.1.5 was read for standing use. This plan reuses exact inputs and ordinary existing tools; it makes no measured savings or model-switch claim. Parent reviewed the lifecycle risk in a proposed custom observer and selected GNU timeout instead; that observer never ran. This experience is retained as conditional guidance evidence, not a benchmark. No external feedback was sent by this child because the parent owns external effects; parent can batch that disposition. No nested worker was created. A mechanical worker can run the frozen commands after owner review without redesigning proofs or acceptance.

Even successful controls would establish only these finite acceptance/rejection distinctions. They would not establish individual HOL theorem axiom dependencies, an independent serialized-proof checker, compiler/hardware soundness, Rust/MiniRust correspondence, all x86 behavior, whole-library adequacy, or broad E03/E31 completion.
