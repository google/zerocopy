# Matched four-law byte case: direct/reflected Lean and strict Alethe checking

## Summary

The requested comparison was performed on one finite judgment. Direct and reflected Lean4.34.1 check all four guarded laws. cvc5 finds each negated law unsatisfiable, but strict Carcara accepts only the complete byte-view admission law. The other three exported proofs remain incomplete or rejected for named export rules. Its separate outside-byte frame projection checks. These are comparative outcomes, not four verified SMT laws.

Five SAT mutants are confirmed against every exact input assertion and reified into checked Lean refutations; a missing-stability control is included. A narrowed Boolean-domain theorem is valid locally but hides byte2 from the full-u8 caller domain. No invalid native Rust is executed.

## Applicability

This is R095 at the **certificate-architecture** level: direct/reflected Lean versus cvc5→Alethe→strict Carcara. It complements existing source/theorem comparisons of named Rust verifiers; it is not a Verus/Creusot/RefinedRust feature-parity run or proof of an actual zerocopy body. The finite memory has two byte cells, initialized/read/write metadata, and two addresses. It deliberately represents a padding-free two-byte object; all payload bytes range over0–255.

Exact tools: Lean4.34.1 `5045d0056413266e57c625dcd7c365b10e377c52`; cvc5 1.4.2 `282d5e0c84baf49c780704c532f87ba66d8b513d`; Carcara1.1.0 from `20bf49c5ce31089ac83118574c888669355aaae1`. `identities.json` binds executing binaries, Lean shared library/Init, and owned files. The launcher hash alone does not identify Lean's version/runtime.

## Findings

### F1. One finite meaning fixes all four obligations

`ByteLaws.lean` defines the actual guarded judgments independently of process success. `observe` returns the same two byte values only with initialization and read authority. `writeByte` requires write authority, updates one cell/initialization flag, and preserves the distinct frame. Boolean validation requires readable initialized snapshot/current cells, a stable value, and the full-byte validity predicate. Array validation additionally checks both indices.

`IntoLaw`, `WriteLaw`, `BoolLaw` and `ArrayLaw` quantify over arbitrary finite memories, byte values and applicable addresses. Their source assumptions are identical across the compared encodings, not added to recover an SMT proof. The reflected `check` decides each data-instantiated guarded proposition; `check_sound` identifies its meaning. `all_reflected` derives generic success using the same direct rule lemmas. Thus these two Lean routes share definitions and proof infrastructure; they are not independent algorithms or kernels.

The SMT problems contain actual array selections/stores, initialization/permission entries, integer byte bounds, address alternatives, value stability and negated postconditions. They contain no proposition asserting that an upstream checker, compiler or source safety proof succeeded. Integer arrays may have other entries, but every observed address is constrained to0/1 and every relevant byte to0–255. `predicate-map.json` records each precise term and premise.

Checked helpers establish byte/address domains, Boolean validity under integer projection, the `<2` versus `not >=2` normal form, read-success equivalence, and the store/value/initialization projections. Syntax generation, parsing, actual SMT-formula attachment, array semantics and the Rust/model correspondence remain explicit interpretation premises; these helpers do not prove the Python emitter or a Rust frontend.

### F2. Strict verdicts expose an export compatibility boundary

| Whole law | Direct/reflected Lean | Initial theory-rewrite Alethe | Final DSL/normal form |
| --- | --- | --- | --- |
| IntoBytes-style byte-view admission | checked | `valid`, exit0 | `valid`, exit0 |
| Byte writing, written value/init and framed value/init | checked | `holey`, exit0 | `invalid`, exit1: `array-read-over-write` missing |
| Boolean validation-to-use | checked | `holey`, exit0 | `invalid`, exit1: `bool-double-not-elim` missing |
| Two-element Boolean-array validity | checked | `holey`, exit0 | `invalid`, exit1: `bool-double-not-elim` missing |

Three bounded export/encoding configurations were tried: original `<2` with theory-rewrite; the same formulas with DSL-rewrite-strict; and the equivalent `not >=2` form plus an exact conjunction decomposition for writing. The four write components retain the original premises and all remain mandatory. Only its outside-byte frame component becomes `valid`; the conjunction is not accepted. Other component failures include `array-read-over-write` and `eq-symm`.

The initial proofs explicitly contain `hole`/untranslated rewrite steps. DSL proofs instead name `rare_rewrite` rules that this exact consumer cannot find. These results establish a current export/consumer rule-interface limitation, not false laws, Rust unsafety, or global absence of SMT support. No allowed-rule, ignore-unknown or custom-checker bypass is used. Acceptance requires exit0 and the exact complete `valid\n` verdict; `holey` with exit0 is denied. No additional repair is claimed.

### F3. Incorrect variants preserve their real logical distinction

| Variant | Actual evidence |
| --- | --- |
| Missing initialization at byte0 | SAT; original read guard fails; exact valuation refuted in Lean |
| Dropped distinct-frame premise | SAT with changed=framed; written byte/frame equality fails; Lean refutation |
| Widened Boolean guard accepting2 | SAT with source/current byte2; Lean full-domain refutation |
| Wrong narrowed u8 domain | Lean proves the changed guard safe under byte<2; full-domain byte2 refutes it. SMT narrowed problem is UNSAT but its exported proof is not strict-valid. Checking it against the full-domain problem separately rejects unmatched assumption `<source[0]2`. |
| Omitted array index1 | SAT with unchecked element invalid; both-index judgment refuted in Lean |
| Missing validation-to-use stability | SAT with valid snapshot/invalid current byte; Lean refutation |

The five SAT valuations are read from actual solver output. An owned parser/evaluator checks every assertion in the exact submitted file, then emits literal typed memories for `SolverWitnesses.lean`; all five bad guarded judgments have checked refutations. The parser and literal binding remain trusted I/O/quotation code. They do not validate arbitrary solver models or unsafe Rust traces. No claim is made that the rejected narrowed Alethe proof was ever accepted locally.

### F4. Observed costs distinguish stages without ranking systems

Three process-inclusive samples check identical four universal plus four concrete propositions per Lean route, importing the same compiled model. Median checks are264.1ms direct and271.5ms reflected; source/template creation is about94.6/100.3µs. Sources are895/1134bytes. Reflected concrete instances use kernel `decide`; generic reflected validity shares the direct lemmas.

For IntoBytes/write/Boolean/array respectively, final cvc5 generation medians are9.69/10.49/10.85/11.47ms. Carcara processing medians are3.32/3.41/3.44/3.60ms, but the last three are **rejection processing**, not successful verification times. Proof payloads are834/4495/10946/11275bytes. Rewriting the already specified SMT input costs approximately131–143µs. It is not measured source-to-VC generation.

The processes perform different work: Lean checks shared imported theorems and concrete reductions; cvc5 searches and exports, while Carcara checks or rejects that export. Startup, imports, caches and host load are uncontrolled. Three samples establish exercised phases, not a performance ranking or production-cost forecast.

### F5. Proof closure and operational failures remain visible

Successful direct/reflected/model/witness runs contain no `sorryAx` or native-computation axiom. The owned endpoints use only the printed standard dependencies: `propext`, with choice/quotient dependencies in selected integer-normalization helpers. `measurements/` retains actual exit codes and complete final stdout/stderr. These4.34 observations still depend on the checker/runtime; a fixed historical kernel defect is not universal soundness of the newer version.

Ordinary initial elaboration failures are preserved separately, including failed declarations that print `sorryAx` while the process exits1; they were not accepted. The first SMT logging helper had a suffix collision, so those initial per-case stdout files contain the final phase only; its formulas, proof payloads, result rows and limited-capture qualification are retained. Subsequent attempts use separate phase files. The initial measurement controller expected `holey` but observed the named DSL-rule rejection and stopped; corrected final measurements record the actual nonzero rejection. None is classified as unsupported Rust semantics or a successful proof.

## Boundaries

Completed research: the same four finite laws were investigated across the named certificate architectures, including incorrect variants, strict status handling, real countermodels, semantic reification and separate small timing phases. The SMT route verified one complete law and a write projection; the remaining full proofs were not independently accepted. This is a completed comparison with a material negative outcome, not a missing experiment or an all-four-SMT-verification claim.

Not established: general IntoBytes derivation, padding/provenance-bearing representations, real allocation/alias/lifetime semantics, larger arrays, compiler/IR extraction, arbitrary client coverage, native Carcara correctness, complete tool distribution closure, or named Rust-backend feature parity. Initialization/permission/stability flags have explicit finite meaning but need a justified physical interpretation for actual Rust. Future integration must preserve that source/quoting/root relation; it is separate from this performed architecture comparison.

## Evidence and revalidation

`verdict-matrix.json`, `predicate-map.json`, `countermodels.json`, `measurements.json` and `identities.json` bind the scope. All sources are owned specimens; no upstream source mirror or installed tool is included. Historical failed attempts are separated from final accepted/rejected observations.

Run `python3 -B replay_case.py --lean /path/to/lean4.34.1 --cvc5 /path/to/cvc5 --carcara /path/to/carcara --out /fresh/scratch`. It copies only owned source, replaces tool-location selectors in-process, regenerates the exact formulas, checks every status, reifies SAT witnesses into Lean and repeats the small samples. Compare full tool/runtime/file identities and all assumptions. A changed exporter or newly supported rule can change the matrix; retain that new observation separately rather than editing this one.
