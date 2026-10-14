# DDC and proof-produced checker executables

## Summary

Diverse double compilation addresses whether a compiler executable corresponds to its stated source under a selected environment and language interpretation. It does not prove that source implements a sound checker. Proof-producing synthesis and compilation can additionally connect a logical checking function, its I/O wrapper and modeled machine code. The inspected CakeML LPR endpoint relates printed successful checking to unsatisfiability of the parsed input, while retaining installation, filesystem/FFI, resource and execution-model premises.

## Applicability

The DDC subject is Wheeler's 2009 dissertation, primary author HTML §§4/5 and the 2019-07-25 errata. The implementation subject is CakeML/cakeml f73189499bb295f0859dec7ee38c169c48da682c, with selected LPR checker, compilation, machine proof and native basis FFI files. The proof-checker author preprint dated 2019-10-28, related to the JLAMP 2020 publication, is a separate subject.

The report answers T045/P120's mechanism questions, addresses T047/P121's modeled I/O route and partially covers T043's runtime frontier. It does not perform the actual generated-checker comparison/measurement requested by P136. No real compiler bootstrap, DDC, HOL build, assembler or checker executable was run. The original finite DDC specimen is expressly illustrative.

## Findings

### Wheeler's implication and its assumptions

**Basis: primary dissertation.** DDC builds stage1 by compiling parent source sP with a trusted diverse compiler cT, then builds stage2 by compiling candidate source sA with stage1. Proof# 1 concludes:

    stage2 = cA → exactly_correspond(cA, sA, lsA, eArun).

It assumes accurate cT compilation of sP and that accurately compiled sP implements a suitable compiler for sA. Environments, their effects, acquisition and equality comparison remain explicit. Proof# 2 separately supplies equality under normal origin/portability/determinism premises. Nonmatching output is not by itself proof of maliciousness; it may expose a false premise. [Dissertation §§4.2/5.6/5.7](https://dwheeler.com/trusting-trust/dissertation/html/wheeler-trusting-trust-ddc.html).

The primary Proof# 1 input independently declares the translation-to-correspondence rule, trusted compilation premise, parent-source compiler premise and two stage definitions before the goal. Its formal proof is separate from evidence that an actual build satisfies those premises. [Author's Prover9 input](https://dwheeler.com/trusting-trust/dissertation/ddc.in).

The source/language interpretation must cover sP/sA's actual requirements. Calling a compiler diverse cannot replace its accurate-parent-compilation premise.

### Correspondence is not checker soundness

**Basis: derived.** If the audited checker source contains an incorrect acceptance rule, producing exactly that source's binary preserves the defect. A DDC success can answer a producer/executable authenticity question while leaving the algorithmic soundness theorem absent.

Likewise, compiling twice with the same compromised executable can reproduce its hidden behavior. Reproducibility controls inputs and makes comparison possible, but it does not supply the diverse-compilation premise. Conversely, different trusted compilers need not generate identical first-stage binaries; the meaningful comparison is the prescribed second stage against the candidate executable.

Preserve the whole execution-relevant subject: selected source, preprocessing/build inputs, runtime components, configurations, comparison semantics and execution environment. Equality of an unrelated file or a hash manifest with no justified provenance is not the theorem's premise.

### Original finite specimen separates these claims

ddc_witness.py models a tiny compiler family with finite clean/infected executable identities. An infected compiler compiling clean compiler source reproduces infection, so regeneration passes. The trusted diverse first stage and prescribed second stage produce the clean executable and expose the mismatch.

A second case intentionally places the infected behavior in the source. DDC then agrees with the infected executable while the independent application safety predicate fails. This is an original finite demonstration of the proposition distinction; it is not a proof of Wheeler's general argument, a compiler experiment or evidence about an actual trusting-trust attack.

The preserved results record both comparisons and the separate behavior check. No numerical performance, proof-cost or practical attack-detection claim is made.

### CakeML LPR: from modeled I/O to a logical result

**Basis: source.** examples/lpr_checker/array/compilation/proofs/lpr_arrayProofScript.sml:60–64 defines cake_lpr_run from well-formed command line/filesystem, standard streams, a free descriptor and installed_x64 code. machine_code_sound:94–113 bounds machine behavior by a resource-extended successful I/O trace. In the three-argument mode, nonempty output is the VERIFIED UNSAT line and implies that the designated file parses as DIMACS fml with unsatisfiable(interp fml).

This binds the logical property to the input parser and visible output, rather than merely proving an internal Boolean. Other command-line modes have separate conclusions; the theorem must not be generalized to every printed string or mode. Resource-limited prefixes remain admitted behavior.

The native executable and physical environment must realize the theorem's installed code, filesystem and machine/FFI semantics. A modeled success result does not identify a downloaded release binary, guarantee termination without resource failure or prove every native environmental behavior.

### The I/O wrapper is part of the proof-facing program

**Basis: source.** lpr_arrayFullProgScript.sml:1684–1694 gives check_unsat_spec with COMMANDLINE and STDIO resources. Its postcondition returns the same command-line resource, an updated stdout/stderr filesystem and check_unsat_sem. Earlier functions verify parsing and file/proof processing under their specifications. The checker theorem therefore includes a modeled wrapper, rather than assuming that an arbitrary file reader supplied the intended logical input.

**Basis: primary author preprint (2019-10-28, related JLAMP 2020 publication).** The OpenTheory checker comparison verifies its I/O wrapper and obtains an in-logic compilation theorem with installed-machine and filesystem premises, retaining resource-limited failure. The final theorem connects error-free output theorems to HOL semantics under its set-theoretic model. These are different endpoints from proving a pure inference rule alone. [Paper, §§6–8](https://cakeml.org/jlamp20.pdf).

File existence, the bytes consumed, stream termination/error behavior and output decoding are semantic interfaces. A caller using a different wrapper or printing its own success string does not inherit this theorem.

### Proof-produced compilation supplies an artifact-specific theorem

**Basis: source.** lpr_arrayCompileScript.sml:15–16 invokes eval_cake_compile_x64 on check_unsat_prog_def and names cake_lpr.S, obtaining lpr_array_compiled. lpr_arrayProofScript.sml:23–35 applies compiler correctness, the source I/O result and machine-configuration conditions to this compilation theorem.

The producer's computation is therefore accompanied by a theorem about the particular compiler result in HOL. This route can avoid trusting a separate compiler execution for that artifact, while retaining the proof kernel, its execution environment and the relationship between the formal result and installed bytes. A freshly rebuilt external executable with no binding argument is a different subject.

**Basis: derived.** Verified bootstrapping applies the compiler route to the compiler itself and connects the resulting compiler code to the logical compiler. DDC instead compares a prescribed rebuilt compiler with a candidate, under diverse-compilation assumptions. A compiler self-reproduction test alone establishes neither semantic compiler correctness nor the DDC premise. A verified compiler executable also needs its installation/runtime theorem applied when it is actually run.

No generated assembly, object or release binary was acquired in this wave. The source tells a future investigator which proposition/result to replay and bind; it does not substitute for that actual artifact.

### Runtime and native FFI remain a concrete frontier

**Basis: source.** basis/basis_ffi.c describes itself as a thin wrapper over system calls. ffiread:141–154 calls POSIX read, ffiwrite:156 onward calls write, and startup allocates heap/stack storage with malloc:506. These are concrete native dependencies below the modeled basis_ffi oracle.

**Basis: derived.** A logical kernel proof needs the assumed memory layout, GC/stack behavior and external contracts to match execution. Compiler and application theorems can verify substantial managed runtime behavior, but do not make all native code, OS services, concurrency or foreign mutation disappear. This wave inspected selected C interfaces; it did not audit the complete runtime proof/dependency closure or concurrent native execution.

For an Anneal checker, explicitly choose whether a wrapper is proved in the same semantic route or accepted as an external contract. Capture malformed-file and read-error behavior before interpreting successful output. Isolation may constrain a producer's effects, but does not itself prove that its checker binary computes the right relation.

### Derived adoption and maintenance gates

There are four separable assurance steps: prove the checking relation sound; bind generated implementation to the logical function; prove decoding/I/O/resource behavior; and bind compiled code plus runtime/environment to the installed executable. DDC can strengthen one executable/source relationship, while proof-producing compilation can supply a more semantic artifact-specific theorem. Neither addresses all four steps by name alone.

A useful adoption pilot should select a small actual checking relation, preserve its proof and generated program, then compare kernel checking with the executable including parsing and output handling. P136 additionally requires observed performance/integration and trust reduction; the finite specimen does not count as that prototype.

Maintenance includes theorem dependencies, synthesis/compilation configuration, parser formats, filesystem/FFI models, machine installation and native build inputs. Revalidation should follow changes to those interfaces rather than repeat a broad survey of compiler families.

## Boundaries

No real DDC or executable-checker prototype was performed. No HOL proof replay, kernel binary identity, generated code bytes or installed CakeML release was established. Selected current script statements and historical paper endpoints remain distinct.

Wheeler's argument is relative to its language/environment and compilation assumptions. It does not certify an arbitrary checker algorithm or runtime. CakeML's selected endpoint includes resource-limited behavior and a modeled FFI; complete concurrency, native-library and host unsafe-operation accounting remains partial.

## Evidence

- Wheeler2009 dissertation, primary author HTML §§4.2/4.3 and5.6/5.7; printed pp32–37/60–88; Proof# 1/Table2 and exact-correspondence definition. Author errata dated 2019-07-25 consulted. No downloaded dissertation bytes or fresh prover execution.
- CakeML full pin in metadata: examples/lpr_checker/array/compilation/proofs/lpr_arrayProofScript.sml, blob 6bc4de12bd7c1bfe28f9875610251de83eb2b9a6, installed_x64:40–53/cake_lpr_run:60–64/machine_code_sound:94 onward.
- examples/lpr_checker/array/lpr_arrayFullProgScript.sml, blob 35f0fac4ffa8760b81e7e8ebefda60e72ea88571, check_unsat_spec:1684–1694. Compilation script: examples/lpr_checker/array/compilation/lpr_arrayCompileScript.sml, blob 45c9ecf5a669ef32788ee3ebf475ee5b97013498.
- basis/basis_ffi.c, blobcd672060888597dc16acdfd4b2b297fec85cd364, ffiread/ffiwrite/startup allocation. The exact C file is a source observation; model correspondence is not inferred from it.
- Author preprint dated 2019-10-28, related JLAMP 2020 publication, 31 pages, §§6–8, Theorems (3)–(5), PDF pp11–14. Original ddc_witness.py/ddc-results.json, Python3.14.8 -B -I. Evidence acquired 2026-10-14; no upstream source mirrors or proof-cost measurements.

## Revalidation

Inspect the exact DDC assumptions, parent/source/build identities and execution-relevant comparison before using a successful comparison as evidence. Re-run the finite specimen only for its proposition distinction. For CakeML, replay the selected source/synthesis/compiler/I/O theorem chain, preserve generated bytes and identify the installed runtime/FFI/ISA configuration. An actual P136 comparison must measure the concrete generated checker and its complete invocation rather than extrapolate from historical benchmarks.

*Authored by an AI agent acting on joshlf's behalf.*
