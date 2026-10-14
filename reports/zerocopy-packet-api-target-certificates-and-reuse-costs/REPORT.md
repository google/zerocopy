# A composed packet API: two-target controls and certificate reuse costs

## Summary

An owned packet decoder/writer composes actual zerocopy Boolean-array validation, little-endian length decoding and bounded prefix writing. It passed 58,240 structured cases and 1,024 flag controls on both native arm64 and wasm32. A shared Lean model supplies all-list success, rejection and suffix-frame laws; small target receipts instantiate layout and bounded arithmetic facts.

The measured receipts cost about 0.33–0.37 seconds to check after a roughly 1.20-second shared model build. Generation here is a small trusted template, not automated discovery of a Rust correspondence proof. These measurements test a modest composed API and reuse boundary; they do not predict full-crate proof costs or establish a verified source frontend.

## Applicability

The owned `decode_write` accepts source/destination slices. It requires a six-byte header, validates four Boolean bytes, decodes a u16 LE payload length, obtains that payload using a checked slice, and calls `write_to_prefix`. Its result is a four-bit flag mask and written length, with separate header, flag, payload and destination errors. zerocopy comes from unchanged PR-stack commit `cce761ad53785973ec2f4a6b13715b770b340c87`.

Both builds use Rust 1.99.0 `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, edition 2024, default debug Cargo settings and offline extraction. Native execution uses aarch64-apple-darwin. wasm32 uses the previously identified task-local official std component and Node 24.21.0/V8 13.6.233.17-node.53, with zero module imports. Certificate checking uses Lean 4.34.1 `5045d0056413266e57c625dcd7c365b10e377c52` and Std. The same named sources are not thereby compiler-equivalent across targets.

## Findings

### F1. The workload exercises actual validation, error and write paths

Basis: source + execution.

The original library/harness checks 32 flag seeds, lengths 0–64, seven destination lengths and four modes: ordinary input, an invalid flag, a truncated payload and a truncated header. This yields 58,240 cases on each target. Every flag position is additionally tested against all 256 byte values, with the other flags and length zero, giving 1,024 controls. Two out-of-domain adapter inputs return the distinguished 99 result. All expected values come from the selected input and independent scalar rules, rather than from the API's returned value.

Successful cases write exactly the source payload and preserve the rest of the destination/backing array. Error cases preserve the whole destination. The adapter compares all 128 backing bytes, including bytes outside the passed destination slice. It uses safe Rust array/slice operations and the public zerocopy methods; no invalid Boolean or deliberately incorrect unsafe variant is executed.

This is not an exhaustive native test of every four-byte input, every u16 length or every payload byte sequence. The case family tests each flag independently and all valid masks within its structured seeds, but arbitrary combinations of invalid flag bytes are outside the native enumeration. The logical universal laws have a separate import premise.

### F2. Mathematical laws expose the source bridge rather than hiding it

Basis: original definitions + execution + derived.

`PacketModel.lean` uses `Fin 256` bytes and list payloads/destinations. `writePayload` checks capacity, then returns `payload ++ destination.drop payload.length`. `write_success` and `write_short` prove both branches, and `write_frame` proves the returned suffix equals the old suffix. `process` additionally checks four valid flag bytes and the availability of the payload. Checked laws reject invalid flags/missing payload and compose successful processing with writing. They quantify over arbitrary lists, not just the native seeds.

The concrete import must establish that Rust slices denote these lists; that Boolean validity is exactly the two accepted representations; that LE length decoding, source bounds and error order match the model; that exclusive destination authority and initialized source bytes justify the copy; and that primitive/compiler effects preserve the represented frame. `available` is an explicit model input, not a proved fact about arbitrary source slicing. The source source-to-model mapping remains manual and trusted. A true list-frame theorem cannot prove pointer authority by itself.

All six model endpoints checked with `propext` dependencies. The complete source and stdout are retained. The same model's validity and suffix laws can support different target receipts, provided these import premises and the consumer's actual claim are preserved.

### F3. Observed layout and small machine bounds are independently scoped

Basis: execution + original definitions + derived.

The native layout vector is `[8,4,1,2,1]`; wasm32 gives `[4,4,1,2,1]`. Its entries are usize width, Boolean-array size/alignment and zerocopy U16 LE size/alignment. `layout_agrees` checks literal equality against the shared expected layout for the selected word width. `bounded_machine_length` proves `6+n < 2^(wordBytes*8)` for `n ≤ 64`. The latter uses `propext` and `Quot.sound`; layout/source-index equations use no axioms, and the all-payload theorem uses `propext`.

The literals come from actual compiler/runtime observations, but their insertion into Lean is a trusted transport. No theorem proves that an observed stdout line denotes the actual compiler type layout. The bounded length theorem does not replace overflow reasoning for arbitrary u16 payloads, arbitrary allocation sizes or changed integer widths. It does replace repeated arithmetic search for this explicitly selected domain.

Using the native observation with a wasm-width request fails elaboration. Changing the provided Boolean-array size from four to eight also fails. These are actual checker rejections. Three additional source/model/domain comparison controls demonstrate unequal prospective policy inputs; they are ordinary hash/value comparisons, not an implemented independent acceptance service. In particular, the template writes its calculated source hash on both sides of the source-index equation: that equation alone cannot authenticate a consumer's requested Rust subject. The earlier [consumer protocol](../consumer-binding-and-failure-protocol-prototype-2026-10-14/REPORT.md) investigates that separate wrapper obligation.

### F4. Measured generation, checking and reuse have a concrete cost boundary

Basis: execution + derived.

The shared model build took 1.200 seconds and produced a 64,008-byte olean. Three native receipts were 972 source bytes each; their check times were 364, 367 and 351 ms. Three wasm receipts were 962 bytes each; check times were 335, 332 and 337 ms. Generated receipt oleans were 46,096 and 44,904 bytes. Template generation including a write took approximately 0.11–0.16 ms per receipt. These times include process startup, imported model use, elaboration, kernel checking and axiom printing. Caches and concurrent host load were uncontrolled; three samples do not support a general solver/checker ranking.

Native and wasm compilation each took about 2.2 seconds in fresh temporary Cargo targets; native case-loop time was about 81.5 ms and the Node loop about 92.3 ms. Those loops perform different runtime/host work and are not proof-checking comparisons. The debug wasm was 1,975,955 bytes. Build/proof artifact size and timing distinguish reusable logical work, small target instantiation, native code generation and concrete execution.

Reusing the model olean avoids repeating its elaboration, but transfers trust to the exact stored compiled module and its runtime/import closure. This investigation recompiles the shared source in fresh scratch before measuring receipts. A production reuse design needs the independent challenge, exact dependency identities and freshness policy discussed elsewhere; a cached successful exit is not authority for a changed implementation or contract.

## Boundaries

Not examined: whole-crate compilation certificates, an actual Rust parser/obligation generator, automatic spatial proof generation, optimized builds, full u16 lengths, arbitrary buffers/alias configurations, large application scalability, or proof-producing compilation of this packet API. The measured generator instantiates a manually supplied mathematical model. Future integration effort includes proving the primitive/import bridge and independently binding every target/type/source/domain input.

The initial native build failed because an extern-C function item was passed directly as an Iterator closure. Its source/diagnostics were retained; an explicit ordinary closure corrected the harness before any reported successful native/Wasm run. This was an ordinary compile rejection, not unsupported packet semantics. These Lean 4.34 observations retain a kernel-soundness premise; presence of the known nested-inductive fix is not a universal correctness theorem about that checker.

## Evidence

Source/execution: all owned source, target driver, recorded tool versions, normalized commands/statuses and native/Wasm output are in `support/`. `certificates/` preserves the shared source, six receipt inputs/outputs, both failed target/type variants, policy comparisons, timings and artifact sizes. `artifact-identities.json` binds the retained files. Evidence date: 2026-10-14.

Primary crate: [PR-stack source](https://github.com/google/zerocopy/tree/cce761ad53785973ec2f4a6b13715b770b340c87/zerocopy). The earlier [two-target report](../zerocopy-two-target-byte-and-layout-controls-2026-10-14/REPORT.md) identifies the wasm std artifact and execution substrate separately. Kernel/source/compiler/native observations have different evidence roles; source-index literals do not prove their relationships.

## Revalidation

Run `support/run_cross.py` with Python 3.14+, the source repository and matching extracted wasm std component, in a task-owned copy; require both complete result sets and zero imports. Run `measure_certificates.py` with the explicit Lean 4.34.1 binary and a new output directory. Inspect all source/hash/domain/type choices, rebuild the model and require six accepted receipts and both failed variants. Compare complete axiom sets and artifact sizes, while keeping new timing observations separate. Changed Rust or target subjects require a new import/binding review even if the same abstract theorem still checks.

*Authored by an AI agent acting on joshlf's behalf.*
