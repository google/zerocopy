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

### F5. Actual layout observations instantiate the shared PR geometry theorem

Basis: owned source + execution + shared-source theorem application (P130).

The earlier receipts compare their five observed fields with a hand-written expected vector. This followup privately compiles the unchanged PR `anneal/lean/Rust/Layout.lean` at `cce761ad53785973ec2f4a6b13715b770b340c87`, SHA-256 `be6a923a4c4a993a0d9cccf5c6b76978043abb8b52b4611246d5486e1fc0f5db`. The original `LayoutBridge.lean` imports `Rust.Layout` and applies `reprCSliceDstSize_aligned` and `roundUpToAlign_ge`. It does not replace those applications with equality of two literal layout lists. The [shared source](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/anneal/lean/Rust/Layout.lean) has no general Rust aggregate-layout theorem: this specimen defines an explicit mathematical aggregate and reuses its padding/alignment theorems.

The consumer separately selects one-byte Boolean representation, a four-element flag array and a two-byte, one-aligned header representation. A mathematical record has one word followed by those flags and header; its containing alignment is the selected word alignment. Its size is `reprCSliceDstSize` for trailing offset `wordBytes + flagsSize 4`, element stride `headerSize`, and count one. Constructing `recordLayout` uses the imported alignment theorem. The generic `admitted_geometry` theorem connects a consumed five-field observation to that construction and proves that its word alignment divides the complete size, its flag alignment divides the array size, and the padded record is no smaller than its fields. It accepts the retained packet observations `[8,4,1,2,1]` and `[4,4,1,2,1]` under separately selected native/wasm targets.

A second, actual safe Rust subject is deliberately distinct from the earlier byte-slice packet API: `#[repr(C)] PacketRecord { word: usize, flags: [bool;4], header: [u8;2] }`. Its probe observes complete size/alignment, both nonzero field offsets, and the size/alignment of Boolean, array, header and word primitives. Rust1.99.0@`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, LLVM23.1.1, edition2024 and opt-level2 produce these results:

| Subject | Record size/align | Flags/header offsets | Boolean size/align | Flags4 size/align | Header2 size/align | Word size/align |
| --- | --- | --- | --- | --- | --- | --- |
| aarch64-apple-darwin | 16/8 | 8/12 | 1/1 | 4/1 | 2/1 | 8/8 |
| wasm32-unknown-unknown | 12/4 | 4/8 | 1/1 | 4/1 | 2/1 | 4/4 |

The wasm subject is a standalone zero-import module executed with Node24.21.0/V8 13.6.233.17-node.53. The existing task-local Rust1.99 wasm standard-library component is reused without installation. `admitted_aggregate_geometry` checks the complete twelve-field observation against the independently selected model, then derives that observed alignment divides observed size and that the observed header extent fits inside the observed complete size. Both actual-vector consumer proofs pass. This is a small theorem-instantiation experiment, not a measurement of general certificate-generation effort.

Four positive consumer invocations accept the two old primitive vectors and the two new actual aggregate vectors. Eight fresh negative Lean invocations reject wrong ABI, flag length, header type, missing/extra fields, and aggregate ABI/offset/type substitutions. The array-length control is discriminating: three flags and four flags both round to a 16-byte native aggregate. Total size alone would miss the changed field; checking the field vector rejects it. A four-byte header can similarly leave the native total size unchanged. Geometry cannot distinguish `[u8;4]` from `[bool;4]` when their size/alignment facts agree; source type/validity meaning must be bound separately.

The selected checker is Lean4.31.0@`68218e876d2a38b1985b8590fff244a83c321783`. Final geometry endpoints print `propext`/`Quot.sound` and no `sorryAx`; the simpler alignment endpoints print `propext`. A first source-root invocation, a later ordinary simplification failure and an extern-C-function iterator-adapter compile failure are retained as rejected attempts. Only the final zero-exit proofs and expected negative rejections count. This old Lean source is affected by the documented nested-parameter validation defect; no exploit is executed. The results are conditional checker observations, not evidence that this kernel can safely admit an arbitrary producer.

This closes the missing shared-theorem application in the bounded P130 prototype. Rust compiler/engine execution, faithful observation import, primitive representation/stride, aggregate field ordering and the relationship between the selected Rust type and mathematical record remain explicit premises. The actual aggregate supplies a concrete observation of these facts, not a proof of rustc or the Rust abstract machine. The new header is `[u8;2]`; equating its representation with the earlier `U16<LE>` remains a separate source interpretation. Neither layout agreement nor this certificate establishes pointer provenance, initializedness, access authority, ownership transfer or a runtime memory operation.

For reproduction, privately copy the exact shared source, verify its hash, and compile only `Rust/Layout.lean` with the recorded Lean pin. Compile `LayoutBridge.lean` with that private import path, then check the supplied positive/negative files. Compile/run `aggregate.rs` natively and as a wasm cdylib using the recorded existing sysroot; execute `aggregate-wasm.mjs` and compare all twelve fields. Preserve selected-model expectations independently of consumed observations. `support/shared-pr-layout/results.json`, `aggregate-results.json`, `input-binding.json`, `artifact-identities.json` and raw logs record the commands, inputs, outputs and scopes. Future adoption requires an independently justified checker and a chosen physical source interpretation rather than promoting these observations to universal layout correctness.

The parent independently replayed the exact shared-source reconstruction, original bridge, all four positive/eight negative consumer controls, and both target builds/executions in a fresh private directory:18commands matched their expected statuses. This is separately recorded in support/shared-pr-layout/parent-replay.json; it retains the same historical checker/source/engine premises.

### F6. A matched four-law byte comparison preserves rejected certificates


#### Summary

The requested comparison was performed on one finite judgment. Direct and reflected Lean4.34.1 check all four guarded laws. cvc5 finds each negated law unsatisfiable, but strict Carcara accepts only the complete byte-view admission law. The other three exported proofs remain incomplete or rejected for named export rules. Its separate outside-byte frame projection checks. These are comparative outcomes, not four verified SMT laws.

Five SAT mutants are confirmed against every exact input assertion and reified into checked Lean refutations; a missing-stability control is included. A narrowed Boolean-domain theorem is valid locally but hides byte2 from the full-u8 caller domain. No invalid native Rust is executed.

#### Applicability

This is R095 at the **certificate-architecture** level: direct/reflected Lean versus cvc5→Alethe→strict Carcara. It complements existing source/theorem comparisons of named Rust verifiers; it is not a Verus/Creusot/RefinedRust feature-parity run or proof of an actual zerocopy body. The finite memory has two byte cells, initialized/read/write metadata, and two addresses. It deliberately represents a padding-free two-byte object; all payload bytes range over0–255.

Exact tools: Lean4.34.1 `5045d0056413266e57c625dcd7c365b10e377c52`; cvc5 1.4.2 `282d5e0c84baf49c780704c532f87ba66d8b513d`; Carcara1.1.0 from `20bf49c5ce31089ac83118574c888669355aaae1`. `identities.json` binds executing binaries, Lean shared library/Init, and owned files. The launcher hash alone does not identify Lean's version/runtime.

#### Findings

##### F1. One finite meaning fixes all four obligations

`ByteLaws.lean` defines the actual guarded judgments independently of process success. `observe` returns the same two byte values only with initialization and read authority. `writeByte` requires write authority, updates one cell/initialization flag, and preserves the distinct frame. Boolean validation requires readable initialized snapshot/current cells, a stable value, and the full-byte validity predicate. Array validation additionally checks both indices.

`IntoLaw`, `WriteLaw`, `BoolLaw` and `ArrayLaw` quantify over arbitrary finite memories, byte values and applicable addresses. Their source assumptions are identical across the compared encodings, not added to recover an SMT proof. The reflected `check` decides each data-instantiated guarded proposition; `check_sound` identifies its meaning. `all_reflected` derives generic success using the same direct rule lemmas. Thus these two Lean routes share definitions and proof infrastructure; they are not independent algorithms or kernels.

The SMT problems contain actual array selections/stores, initialization/permission entries, integer byte bounds, address alternatives, value stability and negated postconditions. They contain no proposition asserting that an upstream checker, compiler or source safety proof succeeded. Integer arrays may have other entries, but every observed address is constrained to0/1 and every relevant byte to0–255. `predicate-map.json` records each precise term and premise.

Checked helpers establish byte/address domains, Boolean validity under integer projection, the `<2` versus `not >=2` normal form, read-success equivalence, and the store/value/initialization projections. Syntax generation, parsing, actual SMT-formula attachment, array semantics and the Rust/model correspondence remain explicit interpretation premises; these helpers do not prove the Python emitter or a Rust frontend.

##### F2. Strict verdicts expose an export compatibility boundary

| Whole law | Direct/reflected Lean | Initial theory-rewrite Alethe | Final DSL/normal form |
| --- | --- | --- | --- |
| IntoBytes-style byte-view admission | checked | `valid`, exit0 | `valid`, exit0 |
| Byte writing, written value/init and framed value/init | checked | `holey`, exit0 | `invalid`, exit1: `array-read-over-write` missing |
| Boolean validation-to-use | checked | `holey`, exit0 | `invalid`, exit1: `bool-double-not-elim` missing |
| Two-element Boolean-array validity | checked | `holey`, exit0 | `invalid`, exit1: `bool-double-not-elim` missing |

Three bounded export/encoding configurations were tried: original `<2` with theory-rewrite; the same formulas with DSL-rewrite-strict; and the equivalent `not >=2` form plus an exact conjunction decomposition for writing. The four write components retain the original premises and all remain mandatory. Only its outside-byte frame component becomes `valid`; the conjunction is not accepted. Other component failures include `array-read-over-write` and `eq-symm`.

The initial proofs explicitly contain `hole`/untranslated rewrite steps. DSL proofs instead name `rare_rewrite` rules that this exact consumer cannot find. These results establish a current export/consumer rule-interface limitation, not false laws, Rust unsafety, or global absence of SMT support. No allowed-rule, ignore-unknown or custom-checker bypass is used. Acceptance requires exit0 and the exact complete `valid\n` verdict; `holey` with exit0 is denied. No additional repair is claimed.

##### F3. Incorrect variants preserve their real logical distinction

| Variant | Actual evidence |
| --- | --- |
| Missing initialization at byte0 | SAT; original read guard fails; exact valuation refuted in Lean |
| Dropped distinct-frame premise | SAT with changed=framed; written byte/frame equality fails; Lean refutation |
| Widened Boolean guard accepting2 | SAT with source/current byte2; Lean full-domain refutation |
| Wrong narrowed u8 domain | Lean proves the changed guard safe under byte<2; full-domain byte2 refutes it. SMT narrowed problem is UNSAT but its exported proof is not strict-valid. Checking it against the full-domain problem separately rejects unmatched assumption `<source[0]2`. |
| Omitted array index1 | SAT with unchecked element invalid; both-index judgment refuted in Lean |
| Missing validation-to-use stability | SAT with valid snapshot/invalid current byte; Lean refutation |

The five SAT valuations are read from actual solver output. An owned parser/evaluator checks every assertion in the exact submitted file, then emits literal typed memories for `SolverWitnesses.lean`; all five bad guarded judgments have checked refutations. The parser and literal binding remain trusted I/O/quotation code. They do not validate arbitrary solver models or unsafe Rust traces. No claim is made that the rejected narrowed Alethe proof was ever accepted locally.

##### F4. Observed costs distinguish stages without ranking systems

Three process-inclusive samples check identical four universal plus four concrete propositions per Lean route, importing the same compiled model. Median checks are264.1ms direct and271.5ms reflected; source/template creation is about94.6/100.3µs. Sources are895/1134bytes. Reflected concrete instances use kernel `decide`; generic reflected validity shares the direct lemmas.

For IntoBytes/write/Boolean/array respectively, final cvc5 generation medians are9.69/10.49/10.85/11.47ms. Carcara processing medians are3.32/3.41/3.44/3.60ms, but the last three are **rejection processing**, not successful verification times. Proof payloads are834/4495/10946/11275bytes. Rewriting the already specified SMT input costs approximately131–143µs. It is not measured source-to-VC generation.

The processes perform different work: Lean checks shared imported theorems and concrete reductions; cvc5 searches and exports, while Carcara checks or rejects that export. Startup, imports, caches and host load are uncontrolled. Three samples establish exercised phases, not a performance ranking or production-cost forecast.

##### F5. Proof closure and operational failures remain visible

Successful direct/reflected/model/witness runs contain no `sorryAx` or native-computation axiom. The owned endpoints use only the printed standard dependencies: `propext`, with choice/quotient dependencies in selected integer-normalization helpers. `measurements/` retains actual exit codes and complete final stdout/stderr. These4.34 observations still depend on the checker/runtime; a fixed historical kernel defect is not universal soundness of the newer version.

Ordinary initial elaboration failures are preserved separately, including failed declarations that print `sorryAx` while the process exits1; they were not accepted. The first SMT logging helper had a suffix collision, so those initial per-case stdout files contain the final phase only; its formulas, proof payloads, result rows and limited-capture qualification are retained. Subsequent attempts use separate phase files. The initial measurement controller expected `holey` but observed the named DSL-rule rejection and stopped; corrected final measurements record the actual nonzero rejection. None is classified as unsupported Rust semantics or a successful proof.

#### Boundaries

Completed research: the same four finite laws were investigated across the named certificate architectures, including incorrect variants, strict status handling, real countermodels, semantic reification and separate small timing phases. The SMT route verified one complete law and a write projection; the remaining full proofs were not independently accepted. This is a completed comparison with a material negative outcome, not a missing experiment or an all-four-SMT-verification claim.

Not established: general IntoBytes derivation, padding/provenance-bearing representations, real allocation/alias/lifetime semantics, larger arrays, compiler/IR extraction, arbitrary client coverage, native Carcara correctness, complete tool distribution closure, or named Rust-backend feature parity. Initialization/permission/stability flags have explicit finite meaning but need a justified physical interpretation for actual Rust. Future integration must preserve that source/quoting/root relation; it is separate from this performed architecture comparison.

#### Evidence and revalidation

`verdict-matrix.json`, `predicate-map.json`, `countermodels.json`, `measurements.json` and `identities.json` bind the scope. All sources are owned specimens; no upstream source mirror or installed tool is included. Historical failed attempts are separated from final accepted/rejected observations.

Run `python3 -B replay_case.py --lean /path/to/lean4.34.1 --cvc5 /path/to/cvc5 --carcara /path/to/carcara --out /fresh/scratch`. It copies only owned source, replaces tool-location selectors in-process, regenerates the exact formulas, checks every status, reifies SAT witnesses into Lean and repeats the small samples. Compare full tool/runtime/file identities and all assumptions. A changed exporter or newly supported rule can change the matrix; retain that new observation separately rather than editing this one.

All filenames in this subsection refer to support/matched-byte-laws/. The parent independently replayed the portable helper in fresh scratch and reproduced every law verdict, five SAT-to-Lean refutations, six Lean check processes, twelve SMT generation/check pairs and the wrong-domain root rejection. Parent replay uses the final identical three implementation sources and retains the same source/quotation/checker/runtime premises.

## Boundaries

Not examined: whole-crate compilation certificates, an actual Rust parser/obligation generator, automatic spatial proof generation, optimized packet-API builds (the separate F5 aggregate uses opt-level2), full u16 lengths, arbitrary buffers/alias configurations, large application scalability, or proof-producing compilation of this packet API. The measured generator instantiates a manually supplied mathematical model. Future integration effort includes proving the primitive/import bridge and independently binding every target/type/source/domain input.

The initial native build failed because an extern-C function item was passed directly as an Iterator closure. Its source/diagnostics were retained; an explicit ordinary closure corrected the harness before any reported successful native/Wasm run. This was an ordinary compile rejection, not unsupported packet semantics. These Lean 4.34 observations retain a kernel-soundness premise; presence of the known nested-inductive fix is not a universal correctness theorem about that checker.

## Evidence

Source/execution: all owned source, target driver, recorded tool versions, normalized commands/statuses and native/Wasm output are in `support/`. `certificates/` preserves the shared source, six receipt inputs/outputs, both failed target/type variants, policy comparisons, timings and artifact sizes. `artifact-identities.json` binds the retained files. Evidence date: 2026-10-14.

Primary crate: [PR-stack source](https://github.com/google/zerocopy/tree/cce761ad53785973ec2f4a6b13715b770b340c87/zerocopy). The earlier [two-target report](../zerocopy-two-target-byte-and-layout-controls-2026-10-14/REPORT.md) identifies the wasm std artifact and execution substrate separately. Kernel/source/compiler/native observations have different evidence roles; source-index literals do not prove their relationships.

## Revalidation

Run `support/run_cross.py` with Python 3.14+, the source repository and matching extracted wasm std component, in a task-owned copy; require both complete result sets and zero imports. Run `measure_certificates.py` with the explicit Lean 4.34.1 binary and a new output directory. Inspect all source/hash/domain/type choices, rebuild the model and require six accepted receipts and both failed variants. Compare complete axiom sets and artifact sizes, while keeping new timing observations separate. Changed Rust or target subjects require a new import/binding review even if the same abstract theorem still checks.

*Authored by an AI agent acting on joshlf's behalf.*
