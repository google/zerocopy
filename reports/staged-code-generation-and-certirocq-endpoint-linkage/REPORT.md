# Staged code generation and exact CertiRocq endpoint linkage

## Summary

Static certificates can constrain code that will be generated later, as Cyclone/TAL/T illustrates. Their conclusion is a selected type-safety policy, not source behavioral equivalence. CertiRocq’s current local ANF theorem has an exact successful-evaluation/cost/value endpoint; its apparent naming gap is resolved by a notation declaration. An original restricted Wasm validator now has a generic expression-to-stack theorem, complete canonical-byte admission, native execution and measured cost observations. Printing, primitives, reification, runtime/FFI and engine adequacy remain separate composition interfaces.

## Applicability

The comparison directly inspects the original PEPM1999 Cyclone paper in BRICS NS-99-1, Cornell TR2000-1824 and CertiRocq commit `906241771e0ac0088403dec12a0027213f114dd1`. The papers and source are separate subjects. No TAL distribution, Rocq compiler or CertiRocq printer was built/run. The report answers P003’s staged-generation mechanism and P021/T023’s local linkage questions. P136 receives an actual original proof-produced executable comparison for the declared small grammar using existing Lean 4.34.1 and Node 24.21; it is not a complete Anneal checker or a CertiRocq build.

## Findings

### F1. Cyclone makes staging and error policy explicit

Basis: primary paper + documentation.

Hornof/Jim’s core has codegen, cut, splice and fill with visible/hidden typing frames. Templates have entry/exit and typed-hole conditions; a region becomes callable after its holes and endpoint conditions are satisfied. Appendix A’s Safety theorem excludes a reachable `error` from a well-typed heap/statement. It deliberately permits `errorreturn` when a function falls through; the implementation also has checked bounds, stack and memory failures. TAL/T typing/macros/verifier and assembly/linking are distinct components. [PEPM1999 paper, printed pp64–66 and Appendix A p73; PDF pp65–67/74](https://www.brics.dk/NS/99/1/BRICS-NS-99-1.pdf).

The author project description says TAL/T statically checks the safety of every possible generated code instance, with no runtime type checking. [Primary project page](https://www.cs.cornell.edu/info/people/fms/rtcg.html).

The precise policy must therefore accompany the certificate. Excluding type errors is compatible with resource failures and does not establish termination or functional equivalence. The staged subject includes generator state, templates, holes and the transition to callable code; certifying only the initial instruction sequence would omit that future behavior.

### F2. Optimization across template instances has extra side conditions

Basis: primary paper; Anneal implications are derived.

The later Cornell report distinguishes within-instance and between-instance CFG edges. Duplicating/removing holes requires corresponding fill updates. Hoisting a hole across instances can change meaning because each copied template may receive a different value; its implementation avoids that move. Its Appendix A gives a formal translation but explicitly leaves correctness proof, complete source/target semantics and a hoped-for bisimulation outside that work. [TR2000-1824, §6.2 p13–14 and Appendix A p21](https://www.cs.cornell.edu/talc/papers/compile_rtcg-tr.pdf).

Derived extension interface: a staged specialization rule must bind template identity, captured resources/values, instance identity, hole types/content, patch targets and the emitted artifact. A proof-generating rule may specialize a logical function and produce a theorem per instance; a type certificate may establish a narrower target-safety invariant. Neither silently substitutes for the other. Actual executable-memory access, macro expansion, assembler/linker and OS/ISA behavior require their own interpretation.

### F3. The CertiRocq name linkage is exact, not inferred

Basis: source.

`Compiler/correctness.v:122` declares `refines_toplevel` as notation for `refines_top` with the selected tags/environment parameters. `LambdaBox_to_LambdaANF/anf_toplevel.v:569–570` defines refines_top by the underlying refines relation and constructed top_cenv. [Notation](https://github.com/CertiRocq/certirocq/blob/906241771e0ac0088403dec12a0027213f114dd1/theories/Compiler/correctness.v#L122), [definition](https://github.com/CertiRocq/certirocq/blob/906241771e0ac0088403dec12a0027213f114dd1/theories/LambdaBox_to_LambdaANF/anf_toplevel.v#L569).

The underlying proposition at143–149 quantifies over a source evaluation to a value with fuel/trace indices. It produces a target ANF evaluation to a related value, with target cost bounded by source trace plus M:

```text
∀ sourceValue sourceFuel sourceTrace,
  sourceEval([],sourceTerm,Val sourceValue,sourceFuel,sourceTrace)
  ⇒ ∃ targetValue targetCost,
       targetEval(emptyEnv,targetTerm,targetCost,Res targetValue)
       ∧ targetCost ≤ sourceTrace + M
       ∧ value_ref(sourceValue,targetValue).
```

This closes the local alias ambiguity. It also exposes the semantic boundary: successful source evaluation is a premise. The displayed relation is not a source-UB reflection theorem or a statement about printed C/machine-code execution.

### F4. Erasure, conversion and execution have different accepted domains

Basis: source + derived.

`metarocq_to_anf_correct/total` require the selected MetaRocq-pipeline postcondition and stronger well-formedness flags excluding axioms and primitives; successful conversion yields the refinement above. A broader pipeline sketch in the file is commented text. [correctness.v:124–214](https://github.com/CertiRocq/certirocq/blob/906241771e0ac0088403dec12a0027213f114dd1/theories/Compiler/correctness.v#L124).

`metarocq_pipeline.v` composes typed/untyped erasure with additional transformations and requires an abstract guard implementation plus its precondition. [lines22–75](https://github.com/CertiRocq/certirocq/blob/906241771e0ac0088403dec12a0027213f114dd1/theories/Compiler/metarocq_pipeline.v#L22).

`pipeline.v:21–23` declares printing functions realized outside Rocq. Lines46–80 consume well-formed-inductive-mapping and well-typed-erasure assumptions. `check_axioms` treats registered extracted primitives differently from unregistered axioms; the executable pipeline then chooses ANF/CPS and code generation. [pipeline.v:19–110](https://github.com/CertiRocq/certirocq/blob/906241771e0ac0088403dec12a0027213f114dd1/theories/Compiler/pipeline.v#L19). Function-valued printing declarations are an external execution interface; their presence is not an arbitrary false proposition. They also do not justify the actual emitted text.

Derived checker route: bind the verified logical checker, its quoted/reified AST and dependency environment; discharge erasure/guard/primitive premises; obtain the compiler theorem for the selected AST; relate the printed program to it; then supply runtime/GC/FFI, linking and installed-code premises. Logical extraction of a checker theorem does not select or prove that whole deployed route. Foreign primitive correctness must be proved against the exact registered model and ABI/resource interface.

### F5. An actual restricted checker route binds instructions and complete module bytes

Basis: original proof + execution; external interpretation is explicit.

`WasmValidator.lean` defines Boolean expressions built from unsigned input-less-than-small-constant and conjunction; input indices are Fin4, values Fin(2^32), constants Fin64. Its generic compiler emits local.get, i32.const, i32.lt_u and i32.and instructions. Induction proves, for every expression, all four 32-bit inputs and every continuation stack:

```text
run(inputs,compile(expression),stack)
  = some(bit(eval(inputs,expression)) :: stack).
```

The stack semantics uses mathematical unsigned comparison and bitwise conjunction; the compiler theorem shows intermediate comparisons yield 0/1, so conjunction matches Boolean and. This is a generic compiler proof for the declared expression language, not a finite test of one AST. The selected expression requires all four parameters <2, modeling four byte-Boolean representation checks. It deliberately takes words by value and proves no physical memory/read authority.

The binary emitter supplies the whole module: magic/version, four-i32→i32 type, one function, sole validate export, no imports/memory/start, code lengths, zero locals and final end marker. The decoder accepts only canonical single-byte immediates, constants 0–63, indices 0–3 and those four instructions. It checks the exact complete wrapper, lengths and end marker, then verifies equality to canonical re-emission. `body_roundtrip` and `module_roundtrip` prove roundtrip (code length+4<128); `accepted_bytes` proves successful decoding binds the entire byte list to its emitted code. `admit_sound` additionally binds code to the independently selected expression and its all-input semantics.

The physical `boolean4.wasm` is 66 bytes, SHA256 `fd0023c344d5d55bb4c7c8f4920764bf5c198777c3411bffea0d99b550cfe158`. `WasmArtifact.lean` reifies that literal byte list, kernel-checks its admission with `by decide`, and applies the generic all-input theorem. The original Python bridge reads the printed list/writes the file and reified source; its I/O is trusted and recorded, rather than a proved filesystem. Parser and compiler proofs use propext, with Quot.sound additionally printed for generic roundtrip proofs; no native_decide, sorryAx or accepted admission appears in final logs. Ordinary initial unknown-lemma and later recursion-limit errors are retained as failed runs, corrected before acceptance. Only authored small proof modules were compiled for imports.

Node 24.21.0/V8 validates and instantiates the zero-import module. All {0,1,2,3}^4 tuples (256) match the source predicate, with 16 accepted; 1,024 single-coordinate byte checks also match. These observations supplement the generic theorem. Seven kernel controls reject changed constant, changed predicate, changed opcode, unknown opcode, wrong length, missing end and appended custom section. Native validation still accepts constant 64 (signed-LEB -64), threshold 3, signed-lt and custom-section variants. The first two cause 16/8 sample mismatches; the latter two agree on this sample yet fail canonical admission. Canonical acceptance is intentionally narrower than general Wasm equivalence. Passing 2^32 demonstrates host wrapping and lies outside the Fin(2^32) theorem domain.

Five fresh-process observations on the same 256-input domain give median 0.762s for kernel `by decide` sample validation,0.199s for import baseline and0.279s for literal admission plus controls. Five warmed Node batches, each 1,000 repetitions of those 256 tuples with JS source comparison, have median 0.00699ms per 256; compilation/instantiation were separately 0.720/0.039ms. These are recorded wall times with different process/import/elaboration and engine/warmup overheads, not an isolated kernel-versus-engine speed ratio or a claim about larger checkers. `wasm-comparison.json` retains every trial and host identity.

The measured trust comparison is not a reduction in the overall trusted implementation. Kernel evaluation uses the logical checker, its interpretation and the checker/runtime/I-O environment per query. The executable route kernel-checks the compiler and literal admission once, then places per-input execution in Node/V8 plus the external Wasm interpretation and host input conversion. It removes online kernel evaluation from that route but adds an unverified engine and leaves offline proof checking. No strict subset-of-TCB or machine-code-verification conclusion follows from the timings.

Trusted interpretation frontier: the recorded WebAssembly specification assigns the selected binary opcodes, unsigned comparison/bitwise operations, signed-LEB constants and module-section grammar. [Pinned primary specification source](https://github.com/WebAssembly/spec/tree/340650f2f620169685814774bc5b019d05d4d3d7/document/core), [numeric opcode table](https://webassembly.github.io/spec/core/binary/instructions.html#numeric-instructions). This experiment assumes that those normative module/instruction meanings coincide with the original restricted stack model and that Node/V8 correctly executes them. It does not mechanize the full Wasm specification connection, prove Node’s JIT/native code, or remove host/runtime/hardware trust. Lean 4.34.1 revision 5045d0056413266e57c625dcd7c365b10e377c52 identities are separate from the affected 4.31 observations in the other two packages; no exploit or general kernel audit was performed here.

### F6. Adoption and maintenance consequences

Basis: derived.

The useful research result is the exact endpoint and prerequisite map. A route can adopt proved local compilation while retaining named printer/runtime premises, then shrink those premises independently. Changes to erasure mode, primitive registration, tags/environment, compiler options, formatter, linked runtime or FFI can invalidate applicability even when a logical checker theorem is unchanged.

A staged checker could emit certificates for specialized instances, but each instance must remain bound to the independently chosen relation/property and concrete artifact. Runtime-generated type safety is a precedent for certifying future outputs; it does not remove source/model correspondence or original-specification meaning.

## Boundaries

Not examined: full TAL/T formal rules/artifact implementation, transitive built CertiRocq theorem assumptions, live reifier or complete CertiRocq printing/assembly/runtime/FFI composition. The original restricted Wasm validator has actual byte/engine identities; its external normative interpretation and Node/V8 implementation remain premises. The source-level alias is resolved; the later compiler/runtime chain is not thereby verified. No general Rust extraction or arbitrary unsafe Rust support follows.

Future engineering: instantiate these known interfaces for an Anneal checker. Remaining artifact research: inspect a single fully selected dependency/build/runtime route and its exact compiled theorem closure. The requested P136 comparison is completed at the restricted-grammar scope above; scaling to a full checker or verifying an engine is future integration work, not missing evidence for this small experiment.

## Evidence

Primary paper identities/coordinates and immutable source pins are in `REPORT.json`. `source-identities.json` records narrow source paths/hashes. The original 1999 paper was acquired through its primary BRICS proceedings after the linked compressed-PostScript retrieval failed; the later translation report is a different subject. The original Wasm/Lean/Node sources, physical module, exact literal, mutation cases, proof logs, identities and all timing trials are included. No upstream source mirror or compiler installation is included. Evidence acquired 2026-10-14.

## Revalidation

Trace notation→refines_top→refines at a new pin before comparing theorem names. Reinspect the exact flags, erasure guard, primitive registry, printing declarations and called compiler route. For an executable claim, replay its theorem and bind the actual printed/runtime/binary artifacts. For staging, check the template/hole/instance and code-finalization rules plus preserved failure policy. For the original route, run `python3 -B -I replay_wasm.py --out /absolute/new/scratch --lean /path/to/recorded/lean --node /path/to/node`; the included runner copies only original specimen sources into that fresh scratch, checks exact byte identity, replays proofs/controls and records fresh timings; compare exact bytes, all final statuses/assumptions and mutated rejection controls. Do not equate finite comparisons or refreshed timings with the generic compiler theorem.

*Authored by an AI agent acting on joshlf's behalf.*
