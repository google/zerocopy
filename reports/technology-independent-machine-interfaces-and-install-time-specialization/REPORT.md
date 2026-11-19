# Technology-Independent Machine Interfaces and Install-Time Specialization: Retained Neutral Code, Derived Native Code, and Checkable Translation

## Summary

Systems that ship a target-neutral program form and produce machine code where the hardware is known fall into two groups, and the difference is architectural, not incidental:

- **Survivors retain the neutral form on the target as the authoritative program and treat native code as a derived, discardable artifact.** IBM's machine interface (System/38, AS/400, IBM i) creates an executable program object by translating machine-interface instructions and keeps the "creation data" needed to re-create it; for programs created for V5R1 or later this survives a user's removal of observability. Android ART keeps DEX and regenerates `.odex`/`.vdex`/`.art` files. .NET ReadyToRun images carry "a full copy of the input IL and MSIL metadata". Wasmtime compiles a WebAssembly module or component into a host-specific ELF artifact that it refuses to load under another version or configuration. Each attaches to the derived code the assumptions it was compiled under and, when they no longer hold, discards the derived code and goes back to the neutral form (by interpretation, recompilation, or an error that makes the embedder recompile).
- **The two formats that ended tried to make a compiler intermediate language the distribution contract without that structure.** TDF/ANDF abstracts the platform API through tokens whose definitions must be built per platform from system headers, changed its own bit encoding between issues, and the surviving TenDRA tree has no 64-bit code generators other than Alpha. LLVM bitcode is, by LLVM's own documentation, not platform-independent for C and C++, and its compatibility promise is one-directional upgrade with possible performance loss; Xcode 14 deprecated it and the App Store stopped accepting it.
- **What the trusted path checks is integrity and compatibility, not translation correctness.** IBM i recomputes a validation value when a program is restored and, on mismatch, re-creates the program from retained creation data or refuses it; restricted machine-interface instructions patched into a user program are blocked. Wasmtime checks the version, target, flags, tunables and features recorded in a precompiled artifact but not the code itself: a one-byte patch to its machine code executed unchallenged in the probe, which is why deserialization is an `unsafe` API. None of the examined production systems validates, at install time, that the generated native code refines the neutral program.
- **Mechanisms exist to close that gap with a small checker.** Proof-carrying code has the producer attach a proof the consumer validates; translation validation checks each compilation rather than the compiler; regalloc2's symbolic checker validates register allocation with a simple lattice; VeriWasm checks sandboxing properties of native-compiled WebAssembly; Crocus verifies instruction-lowering rules offline. A model probe shows one target-independent checker accepting specializations for three machine variants and rejecting injected miscompilations.
- **Mill's documented tool chain** translates LLVM IR to `genAsm`, a dataflow single-assignment form, and a separate specializer produces `conAsm` for one family member. The examined primary material does not state when specialization runs or whether its output is checked.

## Applicability

This is a comparative design study. The subjects are independent systems; nothing here describes their combination.

- **IBM** findings rest on IBM publications: the 1978 *IBM System/38 Technical Developments* collection (scanned copy; quotations normalize optical-recognition errors), the IBM i *Security reference* SC41-5302-13 (title page: IBM i 7.3, applying to subsequent releases), *ILE Concepts* SC41-5606-12, the abstract page of Redpaper REDP-4293-01 (2010), and Redbook SG24-7680-00 (2009). These documents call the interface the "Machine Interface (MI)" and, in 1978, the "high-level machine interface"; the widely used name "Technology Independent Machine Interface" does not occur in the passages read. No IBM i system was available. Text extraction of the long PDFs was truncated at roughly the first 200,000 characters of each, so only early chapters were read.
- **TenDRA/ANDF** findings are readings of `tendra/tendra` at `1eadfd8b7de313b3bcb4cd9416ecb477f70d18fe` (TDF Specification Issue 4.0 revision 1, the TDF guide, the token register, and the top-level build notes).
- **LLVM/Apple** findings are readings of LLVM documentation at `llvm/llvm-project` `70d1fc87689a919f1e0be645cf1c6755009356c8` and of Apple's Xcode 14 release notes.
- **Android** findings are readings of two Android Open Source Project documentation pages, each marked "Last updated 2026-10-09 UTC". ART source was not read.
- **.NET** findings are readings of design documents and one header in `dotnet/runtime` at `db341b0b461356d954079d27e86cb47c929e7e8a`.
- **Wasmtime** findings combine source at tag `v50.0.2` (`f9a93b049a23bef9a33cfa3888f32af33a178749`) with execution of the official `wasmtime-v50.0.2-x86_64-linux` release binary on an x86_64 Linux host whose CPU reports `popcnt` and `avx2` but not `avx512vl`. The Cranelift compiler was used (the default); the Winch and Pulley back ends were not exercised.
- **Mill** findings are limited to two talk-abstract pages on the vendor's site. Mill hardware and tools are not publicly available.
- **Verification** findings come from the abstracts and introductions of two papers, the header documentation of `regalloc2`'s checker at `4eb655fa745fba271af74be8495154a4b0cac56f`, and the READMEs of two research artifacts.
- The third probe executes a *model* written for this report. It characterizes the checking discipline, not any shipping system.

Statements labelled `derived` are this report's synthesis; the reasoning is given in place.

## Findings

### 1. Reference model

```text
N                    target-neutral program (machine-interface template, DEX, IL, Wasm, genAsm, TDF)
D_T = <isa, features, runtime version, dependency versions, options>      target description
spec  : N x D_T -> C_T x K          C_T native code, K the assumptions recorded with it
valid : K x D_T' -> bool            cheap check before C_T is used on the actual target D_T'
run(N, D_T') = if valid(K, D_T') then C_T else (interpret N | re-run spec | reject)
```

Three independent questions organize the rest of the report: (1) is `N` retained wherever `C_T` is used; (2) what is in `K`, and what happens when `valid` fails; (3) who is trusted for the claim that `C_T` behaves as `N`.

### 2. IBM System/38, AS/400 and IBM i

#### 2.1 The 1978 design: a non-executable interface with a program-creation step

Basis: documentation (IBM, 1978).

The article "System/38—A high-level machine" (Dahlby, Henry, Reynolds, Taylor) lists as the first system objective "Programming independence from machine implementation and configuration details" and explains: "In System/38, hardware dependencies have been absorbed by internal microcode functions that provide an instruction interface, which is largely independent of hardware details." On overhead it states the mechanism:

> the System/38 instruction interface definition does not require a directly executable implementation of the instruction interface. The instructions and the operand definition dictionary are presented to the instruction interface and are translated into an executable microcode structure called a program object. The internal microcode format is not apparent at the interface.

and the purpose: "Having an executable program creation step allows the system to have the advantage of both a high-level instruction interface and reduced overhead at execution time." Objects "can be operated upon functionally, but not as a byte string", which "enables applications to remain independent of evolving internal implementations of the machine"; the example given of a detected misuse is "the attempt to directly change a byte within a program object." The companion article on addressing and authorization (Berstis, Truxal, Ranweiler) says the program "is said to be encapsulated because there is no direct access to the storage".

#### 2.2 Retained creation data and observability

Basis: documentation (ILE Concepts).

Modules and programs store data beside compiled code. "Creation Data (\*CRTDTA) ... is required to re-create or convert the module (for example, to change its optimization level). Newly created modules always contain creation data." Removing observability (`RMVOBS` on `CHGMOD`, `CHGPGM`, `CHGSRVPGM`) cannot be undone, and for most data it deletes the data. Creation data is the exception:

> Creation Data (\*CRTDTA) is not removed from the object; it is transformed into an unobservable form. The operating system cannot use the data, but the machine can use unobservable creation data to convert the object.

Derived reading: the neutral form has two visibility levels: observable above the machine interface (debuggers, optimizers, user tools) and unobservable but present below it.

#### 2.3 Conversion as a routine operation

Basis: documentation (Redpaper abstract, Security reference).

For IBM i 6.1, "all MI programs created for previous releases must be converted to run on 6.1 or a later release." The requirement and its coverage are stated precisely:

> To convert a program, its creation data, which is a subset of observability, must be available. MI programs retain creation data by default, so that most programs can be converted, going all the way back to programs that were originally created for System/38. Even if an option was chosen to remove creation data from external access, Licensed Internal Code (LIC) can still access the creation data if the target releases of the program and its constituent modules are V5R1 or later. Thus a program lacks sufficient creation data for conversion only if the program or at least one of its modules was created for IBM OS/400 V4R5 or an earlier release and creation data was explicitly removed.

The Security reference gives the same boundary from the restore side: programs "can contain information that allows the program to be re-created at restore time, without requiring the program source"; programs for V5R1 and later "contain the information needed for re-creation even when the observability of the program is removed"; earlier ones "can only be re-created at restore time if the observability of the program has not been deleted."

The single recorded failure mode is therefore deletion of the neutral form, and the design response (from V5R1) was to make it undeletable by users.

#### 2.4 Trust boundary at restore

Basis: documentation (Security reference; corroborated by SG24-7680-00).

- **Validation value.** "When a program is created, the system calculates a validation value, which is stored with the program. When the program is restored, the validation value is calculated again and compared to the validation value that is stored with the program."
- **Three filters.** The system values `QVFYOBJRST`, `QFRCCVNRST` and `QALWOBJRST` "act as a series of filters to determine whether a program will be restored without change, whether it will be re-created (converted) as it is restored, or whether it will not be restored to the system." "System state programs must have a valid IBM digital signature. Otherwise, they cannot be restored, no matter how the system values are set".
- **Missing validation value.** "At security level 40, the system translates any program that is restored without a validation value. This can add considerable time to the restore process."
- **Restricted instructions.** Many machine-interface instructions "are reserved for operating system use" and "are never generated by the underlying compile process of user code"; because "it is possible to patch or alter a program, by using the service tools or offline", the system blocks their use from user-level programs, and "The restore process will also look for patched programs during restore and will either remove the patch, audit the restore, or allow the patched program on the system". In the function-comparison table, "Programs that contain restricted instructions cannot be created or recompiled" holds at every listed level (20 to 50), and "Programs that use unsupported interfaces fail at run time" at levels 40 and 50.
- **Hardening recommendation** (SG24-7680-00): set `QFRCCVNRST` to "force conversion. Objects that contain sufficient creation data will be converted."

Derived reading: the remedy for an untrusted program object is to discard its native part and regenerate it from the retained neutral form with the trusted translator. Integrity of native code is reduced to integrity of the neutral form plus trust in the translator and in what lies below the interface. The examined text describes no check that the translator's output is semantically correct; the translator is simply inside the trusted base.

#### 2.5 Invariants extracted

| Invariant | Where stated |
|---|---|
| The interface is not directly executable; executable form is produced by a creation step | 1978 article |
| The executable form's internal format is not visible above the interface | 1978 article |
| The neutral form is retained by default and, from V5R1, survives removal of observability | ILE Concepts; Redpaper abstract |
| Re-creation needs no source and can be forced at restore | Security reference |
| Native code arriving from outside is validated and, on doubt, regenerated or refused | Security reference |
| Privileged interface instructions are excluded by the generator and blocked if patched in | Security reference |

### 3. Two neutral formats that ended

#### 3.1 TDF / ANDF as preserved in TenDRA

Basis: documentation and source tree at the pinned revision.

- **Claim of neutrality.** The TDF guide requires "that the production is precisely that - architecture neutral - so that precisely the same TDF is installed on all the target machines."
- **Platform API by tokens.** The API is described "in the form of a set of target independent headers"; token definitions are produced per platform by "a token library building process which analyses the architecture neutral header files for the API concerned, together with the platform specific header files", stored as TDF libraries, and "in the installation, the target independent capsule is combined with the local token definition library to form a target dependent capsule". Some tokens "frequently require built-in support from installers".
- **Format instability.** The specification preface: "This is Issue 4.0 of the TDF Specification. TDF version 4.0 is not bitwise compatible with earlier versions."
- **State of the installers.** The build notes: "there is currently no code generation for 64-bit platforms (other than Alpha) - so no x86_64, mips64, UltraSPARC, 64-bit PA-RISC etc." and "There is currently no code generation for x86_64 assembly." The translator directory contains `alpha`, `hppa`, `m68k`, `mips`, `power`, `sparc` and `x86`.
- **Coupling to each platform's C library.** "The particular version of your libc matters due to the version-specific workarounds for various non-standard or incorrect things in your system headers."

Derived diagnosis: every target needs (a) an installer, (b) a token library derived from that platform's headers for every API used, and (c) agreement on the TDF issue. The neutral form is consumed at installation and nothing in the examined documents has the target retain it for later re-translation. A new architecture therefore needs new work from the platform side *and* re-shipping from the producer side.

#### 3.2 LLVM bitcode as a distribution format

Basis: documentation (LLVM, Apple).

- LLVM FAQ, "Can I compile C or C++ code to platform-independent LLVM bitcode?": "No. C and C++ are inherently platform-dependent languages." The reasons given are preprocessing ("information about other platforms is lost after preprocessing"), `sizeof` ("hard-wiring a platform-specific detail"), and ABI lowering ("front-ends currently must emit platform-specific IR in order to have the result conform to the platform ABI").
- A module carries `target datalayout` ("a target-specific data layout string") and `target triple` ("describes the target host").
- Compatibility policy: "The textual format is not backwards compatible"; "The current LLVM version supports loading any bitcode since version 3.0"; "Newer releases can ignore features from older releases, but they cannot miscompile them"; "Debug metadata is special in that it is currently dropped during upgrades"; "Legacy bitcode may have degraded performance when compared to the compiled output with the legacy compiler."
- Xcode 14 release notes: "Starting with Xcode 14, bitcode is no longer required for watchOS and tvOS applications, and the App Store no longer accepts bitcode submissions from Xcode 14." "Xcode no longer builds bitcode by default and generates a warning message if a project explicitly enables bitcode ... The capability to build with bitcode will be removed in a future Xcode release. IPAs that contain bitcode will have the bitcode stripped before being submitted to the App Store."

Apple's notes state the deprecation, not a reason. The LLVM documents establish the structural limits on their own: the form is specific to a target triple and data layout, and only forward loading is promised.

#### 3.3 Structural comparison

| Property | IBM machine interface | TDF / ANDF | LLVM bitcode (App Store use) |
|---|---|---|---|
| Neutral form designed as the product interface | yes | yes | no (compiler IR) |
| Target ABI, data layout and API baked into the shipped form | no | API via per-platform token libraries | yes (triple, data layout, lowered ABI) |
| Neutral form retained on the target | yes, by default; undeletable from V5R1 | not described | no (held by the distributor) |
| Who re-translates | the machine, below the interface | per-platform installer | the distributor |
| Format evolution | conversion performed by the platform | issue 4.0 not bit-compatible with earlier issues | upgrade-only loading since 3.0 |
| Documented outcome | conversions across releases back to System/38 programs | no 64-bit installers except Alpha in the surviving tree | deprecated in Xcode 14 |

Basis: derived from 2 and 3.1-3.2.

### 4. Survivors: neutral form retained, native code as a keyed cache

#### 4.1 Android ART

Basis: documentation.

- Artifacts: `dex2oat` "takes an APK file and generates one or more compilation artifact files": `.vdex` ("additional metadata to speed up verification, sometimes along with the uncompressed DEX code of the APK"), `.odex` ("AOT-compiled code for methods in the APK"), `.art` (optional, "ART internal representations of some strings and classes"). "The number of files, their extensions, and names are subject to change across releases".
- Policy is a compiler filter: `verify` ("Runs only DEX code verification (no AOT compilation)"), `speed` (verification and "AOT-compiles all methods"), `speed-profile` ("AOT-compiles methods listed in the profile").
- Lifecycle on the documented example configuration: install with a cloud profile and compile listed methods; interpret and JIT the rest while collecting a local profile; "When the device is idle and charging, a compilation daemon runs to re-compile the application based on the combined profile".
- Fallback: "If the .oat file does not contain compiled code, ART runs through JIT and the interpreter to execute the .dex file."
- Invalidation: preinstalled compiled files "are usable as long as all dependencies remain unchanged, in particular the boot classpath"; a boot classpath change "renders all dexpreopt files stale and unusable."
- Signing covers the shipped form: the `nostripping` option exists because keeping `classes.dex` in the APK "is necessary to allow third-party APK signatures to remain valid."

#### 4.2 .NET ReadyToRun and crossgen2

Basis: documentation and source.

- Motivation: the IL format "must either be interpreted or compiled to native code sometime before the code is run", and "For security / tamper-resistance, there is a very strong desire to validate any native code that gets run (e.g. code is signed)."
- Contract: unlike the earlier NGEN, which "is fundamentally a cache", "A native file format carries a strong guarantee that the file will continue to run despite updates and improvements to the runtime or framework."
- Retained neutral form: the image's metadata "represent a full copy of the input IL and MSIL metadata it was generated from."
- Assumption scope: "A version bubble is a set of DLLs that we are willing to update as a set"; "The proposal is to disallow cross-version bubble inlining by default".
- Per-method assumptions are fixups: `READYTORUN_FIXUP_Check_InstructionSetSupport` ("the instruction sets that must be supported/unsupported to use the R2R code associated with the fixup"); `READYTORUN_FIXUP_Check_IL_Body` ("A failed match will cause code not to be used"); `READYTORUN_FIXUP_Verify_IL_Body` ("A failed match will cause a hard runtime failure").
- Hardware model: crossgen2 has a baseline instruction set "which defaults to x86-64-v2" and an optimistic set; "Code which takes advantage of instructions sets in the optimistic set will not be used on a machine which only supports the baseline instruction set." "Any code which uses `Vector<T>` will not be compiled AOT unless the size of `Vector<T>` is known."
- Format versioning: "The runtime should refuse to execute native code from image of version 3.0" when it supports 2.x. At the pinned revision `READYTORUN_MAJOR_VERSION` and `MINIMUM_READYTORUN_MAJOR_VERSION` are both `34`. Derived: the "continue to run" guarantee is carried by the retained IL and the JIT whenever native code is refused.
- Escape hatch: "selective use of the JIT compiler is another tool that can be used to avoid code quality penalties associated with version resilience".

#### 4.3 Wasmtime ahead-of-time artifacts

Basis: source at `v50.0.2` + execution.

`Engine::precompile_module` and `Engine::precompile_component` produce an ELF file; "the data for the engine here is stored into a section of the output file": a version byte, a version string and a serialized `Metadata { target, shared_flags, isa_flags, tunables, features }`. On load, `check_compatible` compares the version string, then `check_triple`, `check_shared_flags`, `check_isa_flags`, `check_tunables` and `check_features`. For CPU features, a flag that is disabled is always compatible; an enabled flag is tested against the running host.

`Module::deserialize` and `Component::deserialize` are `unsafe`. The documented reason: "The structure of the binary blob read here is only lightly validated ... Arbitrary input could, for example, replace valid compiled code with any other valid compiled code, meaning that this can trivially be used to execute arbitrary code". Artifacts from other Wasmtime versions "will deterministically and safely produce an `Err`".

Observed with the release binary (probe in section 7.1):

| Step | Observation |
|---|---|
| Compile the same module twice for the host | identical SHA-256 (deterministic for this input) |
| Compile for host, for explicit `x86_64-unknown-linux-gnu`, for `aarch64-unknown-linux-gnu` | three different artifacts from one source |
| Disassemble `i64.popcnt` function | host artifact contains a `popcnt` instruction; explicit-target artifact contains none (the host's CPU features were not assumed); both return `8` for input `255` |
| Run a precompiled artifact without opt-in | error: "running a precompiled module requires the `--allow-precompiled` flag" |
| Run the aarch64 artifact on x86_64 | `Module was compiled for architecture 'aarch64'` |
| Run an artifact compiled with `has_avx512vl` on a host without it | `compilation setting "has_avx512vl" is enabled, but not available on the host` |
| Change one byte of an immediate in the artifact's machine code | runs and returns the altered constant (`1094795586` instead of `1094795585`) |
| Precompile a component | ELF artifact produced by the same command |
| Synthetic 20,000-function module on 8 CPUs (section 7.2) | compile about 2.2 s (4.3 s on one thread); run with compilation at load about 3.4 s; run from the precompiled artifact about 0.05 s |

The component layer is the same structure at a higher level: a component binary is distinguished from a core module by the preamble's `layer` field (`0x01 0x00`, with a pre-standard `version` of `0x0d 0x00`), and it is compiled by the same engine into one artifact. Basis: documentation (binary format explainer) + execution.

Consequences (derived): the artifact is a cache keyed by engine version, target and configuration, and the compatibility check is not an integrity check. The artifact store is inside the trusted base unless the embedder authenticates artifacts or recompiles from the retained WebAssembly.

#### 4.4 Cross-system matrix

| | IBM i | Android ART | .NET ReadyToRun | Wasmtime AOT |
|---|---|---|---|---|
| Neutral form | machine-interface creation data | DEX | IL and metadata | Wasm module or component |
| Where it is kept | inside the program object | APK or `.vdex` | inside the R2R image | with the embedder |
| When native code is made | creation, restore, conversion | system-image build, install, idle time, or never (`verify`) | publish time | embedder's choice |
| Recorded assumptions | validation value; target release | compiler filter; boot classpath dependency | version bubble; fixups; instruction sets; major version | version; triple; flags; tunables; features |
| On mismatch | re-create or refuse | interpret, JIT, recompile | drop that method's native code and JIT, or reject image | return an error |
| Native code authenticated | validation value; signatures for system-state programs | not described in the examined pages | not described in the examined documents | no; caller's obligation |
| Per-device specialization | by the machine | by profile and device | baseline plus optimistic sets with runtime checks | host feature detection |

Basis: derived from sections 2 and 4.1-4.3; empty knowledge is marked "not described".

### 5. Mill: `genAsm` to `conAsm`

Basis: documentation (vendor talk abstracts only).

"The Mill tool chain is unusual in that it translates LLVM intermediate representation (IR) not into object code but into a different IR (genAsm), tailored for the Mill architecture family. Then a separate tool, the specializer, converts genAsm input into executable binary code (conAsm) for a particular Mill architecture family member. genAsm is a dataflow language, essentially a programmable representation of a single-assignment compiler IR." The specializer has to follow "the location of operands as they move along the belt", and because the machine "is statically scheduled with an exposed pipeline", scheduling and operand spilling "are the rough equivalent of instruction selection, register coloring, and spill on a conventional machine." Family members are generated from a specification "processed by Mill configuration software to build a member-specific assembler, simulator, compiler back-ends, Verilog for the hardware implementation, documentation, and other tools and components."

Derived reading: `genAsm` is family-specific but member-neutral, so the neutral/specific split sits inside one architecture family; the member-dependent work (scheduling against exposed latencies, belt positions, spill) is concentrated in one pass whose input and output are both explicit program forms. That is the shape a per-specialization checker needs (section 6). The examined pages do not say that software is distributed as `genAsm`, that specialization happens at installation, or that its result is validated.

### 6. Checking the specialization step

#### 6.1 What production systems check today

| System | Check performed before native code is used | Establishes |
|---|---|---|
| IBM i | validation value recomputed at restore; optional signature; restricted-instruction blocking | the object is the one the trusted translator produced |
| .NET ReadyToRun | format major version; per-method fixups for instruction sets and IL bodies | assumptions still hold |
| Wasmtime | version string, target triple, compiler flags, tunables, features | the artifact was built for this engine configuration |
| Android ART | dependency staleness (boot classpath) | the artifact matches current dependencies |

Basis: sections 2 and 4. None establishes that native code refines the neutral program; all place the translator in the trusted base.

#### 6.2 Two classical ways to remove the translator from the trusted base

- **Proof-carrying code** (Necula, POPL 1997): "the untrusted code producer must supply with the code a safety proof that attests to the code's adherence to a previously defined safety policy. The host can then easily and quickly validate the proof without using cryptography and without consulting any external agents." The property is a *safety policy*, not equivalence to a source program. Basis: paper abstract.
- **Translation validation** (Necula, PLDI 2000, building on Pnueli, Siegel and Singerman's proposal): "if we cannot prove that a compiler is always correct maybe we can at least check the correctness of each compilation." The reported infrastructure for GCC "compares the intermediate form of the program before and after each compiler pass and verifies the preservation of semantics", and "can be implemented with about the effort typically required to implement one compiler pass." The paper also describes "a general framework that the optimizer can use to communicate to the validator what transformations were performed" — hints. Basis: paper abstract and introduction.

#### 6.3 Checkers in or around a production WebAssembly compiler

- **regalloc2 symbolic checker** (source). "Checker: verifies that spills/reloads/moves retain equivalent dataflow to original, VReg-based code." State is a map from each allocation (register or stack slot) to a set of virtual registers; the lattice is the powerset ordered by inclusion with intersection as meet. Transfer functions: an allocator-inserted move copies the source's set; an original instruction defining `V_i` sets its destination to `{V_i}` and removes `V_i` everywhere else. "To check correctness, we first find the dataflow fixpoint ... Then, at each op, we examine the dataflow solution at the preceding program point, and check that the allocation for each op arg (input/use) contains the symbol corresponding to the original virtual register". It is deliberately incomplete: "we only need to verify the programs that we produce, not arbitrary programs."
- **VeriWasm** (README): motivated by the fact that sandboxing "requires trust in the compiler's correctness—trust that the compiler has inserted each necessary check, correctly formed, in each proper place"; the tool checks native-compiled modules after the fact.
- **Crocus** (artifact README): "a new tool for verifying the correctness of instruction lowering rules written in ISLE", initially "integer operations in WebAssembly 1.0 within Cranelift". This is offline verification of the rule set, complementary to per-compilation checking.

#### 6.4 Derived decomposition for a verified neutral IR with install-time specialization

```text
Spec_T  : N x D_T -> C_T x Hint          untrusted (selection, scheduling, allocation, layout)
Check   : N x C_T x Hint x Sem_T -> bool trusted; Sem_T = machine semantics of target T
Trusted base = Check + Sem_T + loader + storage integrity of whatever is not re-checked
```

| Pass | Certificate (hint) | Checker obligation | Precedent |
|---|---|---|---|
| Register or belt allocation, spill, moves | final location of each value at each use | value-set dataflow | regalloc2 checker |
| Instruction selection | rule instance per selected instruction | rule proved once offline | Crocus |
| Scheduling against latencies | schedule order and timing | dependency order preserved | none examined |
| Isolation checks (bounds, control flow) | none needed | re-derive from machine code | VeriWasm |
| Whole-pass optimization | transformation hints or none | simulation relation between before and after | translation validation |

Design consequences:

1. **Check at specialization time or authenticate afterwards.** A cache of unchecked native code needs storage integrity (IBM i validation value, signatures) or re-validation on load. Wasmtime's documentation makes this the caller's duty.
2. **Compatibility metadata is not a certificate.** It says which configuration the code was built for, not that the code is right for it (section 4.3, tampering row).
3. **The checker must not depend on member-specific heuristics.** In the model probe the same checker accepts code for 2, 3 and 8 registers; only `Sem_T` should vary by target.
4. **Signed bytes and executed bytes differ.** Signatures cover the neutral form (ART's `nostripping` note); the native bytes differ per device and, with profiles, per usage. Where specialization is deterministic (the Wasmtime run was, for one module and configuration) the mapping from neutral form and target description to native bytes can be recomputed by a verifier; profile-guided specialization gives that up.
5. **Retention is a requirement, not an optimization.** Every survivor re-derives native code from the neutral form on a mismatch. IBM's documented failure was deleted creation data; LLVM-bitcode distribution kept the neutral form away from the device.

### 7. Reproducible probes

#### 7.1 Wasmtime artifact compatibility and integrity

Environment: x86_64 Linux (kernel 7.1), GNU `objdump` and `readelf`, Python 3. Binary: `wasmtime` from `wasmtime-v50.0.2-x86_64-linux.tar.xz` (archive SHA-256 `5db0ca8e838ab95a51ba9acdf11f42888bcd0092dda45a86129ae540c4fa952c`; extracted `wasmtime` SHA-256 `45b48cfa0c04a1564cba14d76fe22ffb764bf0fc661b802e73b3784f8827e46e`). Save the script as `/tmp/probe_aot.sh` and run `bash /tmp/probe_aot.sh /path/to/wasmtime`. Script SHA-256 (file ending in a single newline): `4ff0de1a02c023d141f08305c2dd0e4d681d94b420454852b88312037d4f883d`.

```bash
#!/usr/bin/env bash
# AOT specialization probe for a released Wasmtime CLI. Usage: probe_aot.sh /path/to/wasmtime
set -u
W="$1"; D="$(mktemp -d /tmp/aot_probe.XXXXXX)"; cd "$D"
cat > m.wat <<'EOF'
(module
  (func (export "pc") (param i64) (result i64)
    local.get 0
    i64.popcnt)
  (func (export "answer") (result i32)
    i32.const 1094795585))
EOF
cat > c.wat <<'EOF'
(component
  (core module $m (func (export "answer") (result i32) i32.const 7))
  (core instance $i (instantiate $m)))
EOF
h() { sha256sum "$1" | cut -c1-16; }
echo "[0] $("$W" --version)"
"$W" compile m.wat -o host.cwasm
"$W" compile m.wat -o host2.cwasm
"$W" compile --target x86_64-unknown-linux-gnu m.wat -o base.cwasm
"$W" compile --target aarch64-unknown-linux-gnu m.wat -o a64.cwasm
"$W" compile --target x86_64-unknown-linux-gnu -C cranelift-has-avx512vl m.wat -o avx512.cwasm
echo "[1] source m.wat=$(h m.wat) host=$(h host.cwasm) host-again=$(h host2.cwasm) baseline-x86_64=$(h base.cwasm) aarch64=$(h a64.cwasm)"
echo "[2] ELF machine: host=$(readelf -h host.cwasm | awk -F: '/Machine/{gsub(/^ +/,"",$2);print $2}') a64=$(readelf -h a64.cwasm | awk -F: '/Machine/{gsub(/^ +/,"",$2);print $2}')"
pc() { objdump -d -j .text "$1" 2>/dev/null | grep -c -w popcnt; }
echo "[3] popcnt instructions in .text: host=$(pc host.cwasm) baseline-x86_64=$(pc base.cwasm)"
echo "[4] run host artifact without opt-in : $("$W" run --invoke answer host.cwasm 2>&1 | grep -v "^$" | tail -1 | sed "s/^ *//")"
echo "[5] run host artifact                : $("$W" run --allow-precompiled --invoke answer host.cwasm 2>&1 | grep -v "^$" | tail -1 | sed "s/^ *//")"
echo "[6] run host artifact pc(255)        : $("$W" run --allow-precompiled --invoke pc host.cwasm 255 2>&1 | grep -v "^$" | tail -1 | sed "s/^ *//")"
echo "[7] run baseline artifact pc(255)    : $("$W" run --allow-precompiled --invoke pc base.cwasm 255 2>&1 | grep -v "^$" | tail -1 | sed "s/^ *//")"
echo "[8] run aarch64 artifact on x86_64   : $("$W" run --allow-precompiled --invoke answer a64.cwasm 2>&1 | grep -v "^$" | tail -1 | sed "s/^ *//")"
echo "[9] run avx512vl artifact on this host: $("$W" run --allow-precompiled --invoke answer avx512.cwasm 2>&1 | grep -v "^$" | tail -1 | sed "s/^ *//")"
python3 - <<'EOF'
b = bytearray(open("host.cwasm", "rb").read()); needle = bytes.fromhex("41414141")
n = b.count(needle); i = b.find(needle); b[i] = 0x42
open("tampered.cwasm", "wb").write(b); print(f"[10] immediates 0x41414141 found: {n}; patched byte at offset {i}")
EOF
echo "[11] run tampered artifact           : $("$W" run --allow-precompiled --invoke answer tampered.cwasm 2>&1 | grep -v "^$" | tail -1 | sed "s/^ *//")"
"$W" compile c.wat -o c.cwasm && echo "[12] component artifact: $(h c.cwasm) ELF machine=$(readelf -h c.cwasm | awk -F: '/Machine/{gsub(/^ +/,"",$2);print $2}')"
echo "[13] host cpu flags of interest: $(grep -m1 -o -w -e popcnt -e avx2 -e avx512vl /proc/cpuinfo | sort -u | tr '\n' ' ')"
```

Observed output (2026-11-19):

```text
[0] wasmtime 50.0.2 (f9a93b049 2026-11-16)
[1] source m.wat=930c369a4e5a906a host=5042bcd83efce9ff host-again=5042bcd83efce9ff baseline-x86_64=23b8bc2f05972bbf aarch64=45540455d04b2930
[2] ELF machine: host=Advanced Micro Devices X86-64 a64=AArch64
[3] popcnt instructions in .text: host=1 baseline-x86_64=0
[4] run host artifact without opt-in : Error: running a precompiled module requires the `--allow-precompiled` flag
[5] run host artifact                : 1094795585
[6] run host artifact pc(255)        : 8
[7] run baseline artifact pc(255)    : 8
[8] run aarch64 artifact on x86_64   : Module was compiled for architecture 'aarch64'
[9] run avx512vl artifact on this host: 1: compilation setting "has_avx512vl" is enabled, but not available on the host
[10] immediates 0x41414141 found: 1; patched byte at offset 4133
[11] run tampered artifact           : 1094795586
[12] component artifact: 3cbb42ca9005ce85 ELF machine=Advanced Micro Devices X86-64
[13] host cpu flags of interest: avx2 popcnt 
```

Step 10-11 patches the least significant byte of the constant `0x41414141` inside the artifact; the tampered artifact is accepted and returns `0x41414142`. Lines 8 and 9 show the last line of a multi-line error. Line 9 depends on the host lacking AVX-512VL.

#### 7.2 Wasmtime: compiling at load versus loading a precompiled artifact

Same binary and host as 7.1 (8 logical CPUs, shared machine). Save as `/tmp/probe_cost.sh` and run `bash /tmp/probe_cost.sh /path/to/wasmtime 20000`. Script SHA-256 (file ending in a single newline): `e9a63f382443bec75293b44aa3b76dd5995f28d93864ba5ab5a8f7d68d25d8f6`. The module is generated in the text format, so every timing includes text parsing; timings are wall-clock medians of three runs and are indicative only.

```bash
#!/usr/bin/env bash
# Cost probe: compile-at-load versus precompiled load for one synthetic module.
# Usage: probe_cost.sh /path/to/wasmtime [functions]
set -u
W="$1"; N="${2:-20000}"; D="$(mktemp -d /tmp/aot_cost.XXXXXX)"; cd "$D"
python3 - "$N" <<'EOF'
import sys
n = int(sys.argv[1]); out = ["(module"]
for i in range(n):
    out.append(f"  (func $f{i} (param i64 i64) (result i64)"
               f" local.get 0 local.get 1 i64.mul i64.const {i + 3} i64.add"
               f" local.get 0 i64.popcnt i64.xor local.get 1 i64.const {i % 61 + 1} i64.rotl i64.sub)")
out.append('  (func (export "answer") (result i64) i64.const 6 i64.const 7 call $f0)')
out.append(")")
open("big.wat", "w").write("\n".join(out) + "\n")
EOF
ms() { local s e; s=$(date +%s%N); "$@" >/dev/null 2>&1; e=$(date +%s%N); echo $(( (e - s) / 1000000 )); }
med() { printf '%s\n' "$@" | sort -n | sed -n 2p; }
c=(); s1=(); l=(); p=()
for i in 1 2 3; do
  s1+=("$(ms "$W" compile -C cache=n -C parallel-compilation=n big.wat -o one.cwasm)")
  c+=("$(ms "$W" compile -C cache=n big.wat -o big.cwasm)")
  l+=("$(ms "$W" run -C cache=n --invoke answer big.wat)")
  p+=("$(ms "$W" run -C cache=n --allow-precompiled --invoke answer big.cwasm)")
done
echo "functions=$N cpus=$(nproc) wat_bytes=$(stat -c %s big.wat) artifact_bytes=$(stat -c %s big.cwasm)"
echo "median_ms: compile_one_thread=$(med "${s1[@]}") compile=$(med "${c[@]}") run_from_source=$(med "${l[@]}") run_precompiled=$(med "${p[@]}")"
echo "result: $("$W" run -C cache=n --allow-precompiled --invoke answer big.cwasm 2>&1 | tail -1)"
```

Observed output (2026-11-19):

```text
functions=20000 cpus=8 wat_bytes=3474923 artifact_bytes=4028128
median_ms: compile_one_thread=4330 compile=2221 run_from_source=3414 run_precompiled=48
result: 33
```

For this input, moving compilation ahead of the run reduced start-up from seconds to tens of milliseconds (a factor of about 70 in this run), at the cost of an artifact about 1.16 times the size of the text source and tied to one engine version and configuration.

#### 7.3 Model: per-member specializer with a target-independent checker

Environment: CPython 3.13.15, standard library only. Save as `/tmp/probe_spec.py`, run `python3 /tmp/probe_spec.py`; exit status 0. Script SHA-256 (file ending in a single newline): `1b20622e261b272a5544bb20cf8681e73ed8d30427ff525904d746f088dcd107`.

The neutral program is six single-assignment statements over 64-bit integers. `specialize(k)` is an untrusted allocator for a machine with `k` registers that spills by furthest next use; `drop_reload=n` omits its `n`-th reload to model a miscompilation. `check` is a set-valued location analysis in the style quoted in section 6.3. `agree` is an independent differential test on 200 random inputs.

```python
#!/usr/bin/env python3
"""Model: untrusted per-target specializer plus a small target-independent checker (stdlib only)."""
import random

GEN = [("v2", "mul", "v0", "v1"), ("v3", "add", "v2", "v0"), ("v4", "mul", "v3", "v3"),
       ("v5", "sub", "v4", "v1"), ("v6", "add", "v5", "v2"), ("v7", "mul", "v6", "v3")]
INPUTS, RESULT, M = ("v0", "v1"), "v7", 2**64
OPS = {"add": lambda a, b: (a + b) % M, "sub": lambda a, b: (a - b) % M, "mul": lambda a, b: (a * b) % M}

def run_gen(x, y):
    env = dict(zip(INPUTS, (x, y)))
    for d, op, a, b in GEN: env[d] = OPS[op](env[a], env[b])
    return env[RESULT]

def specialize(k, drop_reload=None):
    """Untrusted: allocate k registers, spilling by furthest next use. Returns target code."""
    reg, home, code, reloads = {}, {}, [], 0          # reg: preg -> vreg, home: vreg -> slot
    for i, v in enumerate(INPUTS): home[v] = f"s{i}"   # arguments arrive in stack slots
    def next_use(v, i): return next((j for j in range(i, len(GEN)) if v in GEN[j][2:]), 10**6)
    def ensure(v, i, keep):
        nonlocal reloads
        for p, w in reg.items():
            if w == v: return p
        p = take(i, keep); reloads += 1
        if reloads != drop_reload: code.append(("move", p, home[v]))
        reg[p] = v; return p
    def take(i, keep):
        free = [f"r{n}" for n in range(k) if f"r{n}" not in reg]
        if free: return free[0]
        p = max((q for q in reg if q not in keep), key=lambda q: next_use(reg[q], i))
        v = reg.pop(p)
        if v not in home and next_use(v, i) < 10**6:
            home[v] = f"s{len(home)}"; code.append(("move", home[v], p))
        return p
    for i, (d, op, a, b) in enumerate(GEN):
        pa = ensure(a, i, ()); pb = ensure(b, i, (pa,))
        pd = take(i + 1, ()); reg[pd] = d                 # may reuse an operand register
        code.append(("op", pd, op, pa, pb, (d, a, b)))  # last field: the genIR statement realized
    return code, next(p for p, v in reg.items() if v == RESULT)

def run_con(code, out, x, y):
    loc = {"s0": x, "s1": y}
    for ins in code:
        if ins[0] == "move": loc[ins[1]] = loc.get(ins[2], 0xDEAD)
        else: loc[ins[1]] = OPS[ins[2]](loc.get(ins[3], 0xDEAD), loc.get(ins[4], 0xDEAD))
    return loc.get(out, 0xDEAD)

def check(code, out):
    """Trusted: each location holds a set of genIR values; every use must find its value."""
    holds, stmts = {"s0": {"v0"}, "s1": {"v1"}}, iter(GEN)
    for ins in code:
        if ins[0] == "move":
            holds[ins[1]] = set(holds.get(ins[2], ())); continue
        _, pd, op, pa, pb, (d, a, b) = ins
        if (d, op, a, b) != next(stmts, None): return "reject: not the next genIR statement"
        if a not in holds.get(pa, ()) or b not in holds.get(pb, ()): return f"reject: operand of {d} not in place"
        for s in holds.values(): s.discard(d)
        holds[pd] = {d}
    if next(stmts, None) is not None: return "reject: statements missing"
    return "accept" if RESULT in holds.get(out, ()) else "reject: result not in place"

if __name__ == "__main__":
    rnd = random.Random(1); tests = [(rnd.randrange(M), rnd.randrange(M)) for _ in range(200)]
    for k, drop in ((2, None), (3, None), (8, None), (2, 3), (3, 2)):
        code, out = specialize(k, drop)
        agree = sum(run_con(code, out, x, y) == run_gen(x, y) for x, y in tests)
        moves = sum(i[0] == "move" for i in code)
        print(f"member k={k} drop_reload={drop}: {len(code)} instrs ({moves} moves) "
              f"checker={check(code, out)!r} agree={agree}/200")
```

Observed output (2026-11-19):

```text
member k=2 drop_reload=None: 13 instrs (7 moves) checker='accept' agree=200/200
member k=3 drop_reload=None: 10 instrs (4 moves) checker='accept' agree=200/200
member k=8 drop_reload=None: 8 instrs (2 moves) checker='accept' agree=200/200
member k=2 drop_reload=3: 12 instrs (6 moves) checker='reject: operand of v5 not in place' agree=0/200
member k=3 drop_reload=2: 9 instrs (3 moves) checker='reject: operand of v2 not in place' agree=0/200
```

The checker accepts all three correct specializations and rejects both injected faults, in agreement with differential execution. The model has no control flow, so it exercises none of the fixpoint machinery a real checker needs.

## Boundaries

- **Not examined:** any running IBM i system; the body of Redpaper REDP-4293-01 (only its abstract page could be retrieved); later chapters of the IBM manuals beyond the extracted prefix; IBM's mid-1990s change of AS/400 processor architecture, which secondary sources describe and for which no primary document was retrieved. The statement that conversion reaches "programs that were originally created for System/38" is IBM's, from the Redpaper abstract.
- **Not examined:** ART source code, the on-device artifact formats, how ART authenticates or validates `.odex`/`.vdex` files, and ART's instruction-set feature handling. The corresponding matrix cells say "not described".
- **Not examined:** .NET runtime source for image loading, and how R2R images are signed or validated in practice; Native AOT.
- **Not examined:** Wasmtime's Winch and Pulley back ends, its on-disk compilation cache, component-specific compatibility checks beyond successful precompilation, and determinism across inputs, thread counts or hosts. Determinism was observed for one module, one configuration, two runs.
- **Not examined:** Java ahead-of-time and class-data-sharing facilities, Portable Native Client, Oberon slim binaries, firmware bytecode formats, GPU shader pipelines, and operating-system-level mechanisms for choosing among precompiled variants.
- **Not examined:** the full texts of the two papers beyond abstract and introduction; the original translation-validation paper by Pnueli, Siegel and Singerman (TACAS 1998) was identified through citations only.
- **Unknown:** why Apple deprecated bitcode. The release notes give no reason; the structural limits in section 3.2 are consistent with the decision but are not Apple's stated rationale.
- **Unknown:** why ANDF was not adopted commercially. Section 3.1 documents properties of the technology and the state of the surviving tree, not market history.
- **Unknown:** whether Mill software is distributed as `genAsm`, when specialization runs, whether `conAsm` is cached, and whether specialization is validated. The term "install-time specialization" for Mill is not supported by the examined primary pages.
- **Unknown:** how IBM i's validation value is computed and what cryptographic strength it has; whether the translator below the machine interface has been formally verified.
- **Known not to apply:** Wasmtime's precompiled-artifact compatibility check as an integrity or authenticity check (execution, section 7.1); LLVM bitcode as a platform-independent form for C or C++ (LLVM FAQ).
- **Unsupported by the subject:** loading LLVM bitcode older than version 3.0; running native code from a ReadyToRun image whose major version the runtime does not support; deserializing Wasmtime artifacts from a different Wasmtime version under the default version strategy.
- **Stronger conclusions not established:** that any examined production system would be unsound in practice; that the checker model scales to real code generators; that retained-neutral-form designs have lower total cost. The only cost measurement is one synthetic module on one shared host (section 7.2); no install-time or first-run cost was measured for IBM i, ART or .NET.

## Evidence

All sources were read on 2026-11-19.

**IBM**

- *IBM System/38 Technical Developments*, IBM, 1978, ISBN 0-933186-00-2, scanned copy at the URL in the metadata. Articles used: S.H. Dahlby, G.G. Henry, D.N. Reynolds, P.T. Taylor, "System/38—A high-level machine" (sections "Relevant system objectives", "Independence from machine implementation and configuration", "Integrity and authorization", "Overhead considerations"); V. Berstis, C.D. Truxal, J.G. Ranweiler, "System/38 addressing and authorization" (section "Objects and spaces"). Text was obtained by optical recognition; quotations correct evident recognition errors only.
- *IBM i Security reference*, SC41-5302-13, chapter "Using System Security (QSecurity) system value": sections "Security level 40" (comparison table and restricted-instruction discussion), "Validation of programs being restored", "Changing to security level 40".
- *IBM i ILE Concepts*, SC41-5606-12, section "Stored data in modules and programs".
- *IBM i Program Conversion: Getting Ready for 6.1 and Beyond*, REDP-4293-01, published 17 March 2010, abstract page.
- *Security Guide for IBM i V6.1*, SG24-7680-00, First Edition (May 2009), sections "Validation of program restored" and "Restricting the ability to place tampered objects on the system".

**TenDRA** (`tendra/tendra` @ `1eadfd8b7de313b3bcb4cd9416ecb477f70d18fe`): `tdf/doc/specification/preface.xml` (line 7); `tdf/doc/guide/tdf.xml` (lines 35, 145, 169, 249, 350); `tdf/doc/register/api.xml` (line 20 and the following paragraph on installer support); `README.md` (lines 42-44, 57-59, 101); directory listing of `trans/src`.

**LLVM** (`llvm/llvm-project` @ `70d1fc87689a919f1e0be645cf1c6755009356c8`): `llvm/docs/FAQ.md` (139-155); `llvm/docs/DeveloperPolicy.md` "IR Backwards Compatibility" (695-718); `llvm/docs/LangRef.md` data layout (3536-3543) and target triple (3762-3776).

**Apple**: Xcode 14 Release Notes, deprecation entries carrying Apple reference numbers 86118779 and 87590506.

**Android**: "Configure ART" (sections "How ART works", "Compiler filters", "System ROM configuration", `LOCAL_DEX_PREOPT`) and "Implement ART just-in-time compiler" (section "JIT compilation"), both last updated 2026-10-09 UTC.

**.NET** (`dotnet/runtime` @ `db341b0b461356d954079d27e86cb47c929e7e8a`): `docs/design/coreclr/botr/readytorun-overview.md` (motivation 4-18, constraints 21-27, version bubbles 97-110, selective JIT 128-130, inlining 262); `docs/design/coreclr/botr/readytorun-format.md` (IL copy 28-30, version rule 106-112, fixup table 304-310); `docs/design/coreclr/botr/vectors-and-intrinsics.md` (41-52); `src/coreclr/inc/readytorun.h` (20-25).

**Wasmtime** (`bytecodealliance/wasmtime` @ `f9a93b049a23bef9a33cfa3888f32af33a178749`): `crates/wasmtime/src/engine/serialization.rs` (module documentation 1-22, `check_compatible` 49-127, `Metadata` 181-189, checks 204-253); `crates/wasmtime/src/engine.rs` (`detect_precompiled` 329, `check_compatible_with_isa_flag` 553 onward, `precompile_module` 732, `precompile_component` 741); `crates/wasmtime/src/runtime/module.rs` (`deserialize` documentation 374-422); `crates/wasmtime/src/runtime/component/component.rs` (`deserialize` 222-242). Execution: section 7.1.

**WebAssembly Component Model** (`WebAssembly/component-model` @ `585526aa1f2c7f76f07557d16e265dede38b3acb`): `design/mvp/Binary.md` (preamble grammar 22-26, notes 46-55).

**Mill Computing**: talk pages "The Compiler" (Ivan Godard, 2015-06-10) and "Specification" (Ivan Godard, 2014-05-14); abstracts only.

**Verification**

- G.C. Necula, "Proof-Carrying Code", POPL 1997, DOI `10.1145/263699.263712`; abstract read from a university-hosted copy of the paper.
- G.C. Necula, "Translation Validation for an Optimizing Compiler", PLDI 2000, pages 83-95, DOI `10.1145/349299.349314`; abstract and introduction.
- `bytecodealliance/regalloc2` @ `4eb655fa745fba271af74be8495154a4b0cac56f`: `src/checker.rs` (header documentation 9-91).
- `PLSysSec/veriwasm` @ `60a64d279ecb676549aab51838d52b41ec6d1360`: `README.md`.
- `avanhatt/asplos24-ae-crocus` @ `762320d87b288ac06d67e790935f3a7d7cd7ea92`: `README.md` (archival DOI `10.5281/zenodo.10433722`).

**Execution.** All three probes are reproduced completely in section 7 with their outputs; no other file is required. The two Wasmtime probes need the release binary identified above.

## Revalidation

- **Wasmtime.** Re-run section 7.1 against a newer release. Lines 4, 8, 9 and 11 are the discriminating ones: if line 11 starts failing, an integrity check has been added and section 4.3's consequence must be revised; if line 9 passes on a host with AVX-512VL, use another feature the host lacks. Then diff `crates/wasmtime/src/engine/serialization.rs` for the `Metadata` fields and the list of `check_*` calls, and re-read the "Unsafety" paragraph of `Module::deserialize`.
- **.NET.** Check `READYTORUN_MAJOR_VERSION` and `MINIMUM_READYTORUN_MAJOR_VERSION` in `src/coreclr/inc/readytorun.h`, and search `readytorun-format.md` for `Check_InstructionSetSupport` and `Check_IL_Body`. An empirical check not done here: publish a ReadyToRun assembly, run it under a runtime with a higher minimum major version, and observe JIT fallback through runtime events.
- **Android.** Re-read the "How ART works" and "Compiler filters" sections; the list of filters and artifact files is explicitly "subject to change across releases". On a device, the documented command `adb shell cmd package compile -m speed-profile -f <package>` forces compilation under a chosen filter.
- **IBM i.** In a newer edition of the Security reference, find "Validation of programs being restored" and compare the three numbered notes on re-creation. On a system: remove observability from a test program, save it, restore it with `QFRCCVNRST` forcing conversion, and confirm that it is re-created.
- **LLVM / Apple.** Re-read the FAQ entry on platform-independent bitcode and the "IR Backwards Compatibility" list. Check later Xcode release notes for removal of the bitcode build capability.
- **TenDRA.** List `trans/src` for new architecture directories and re-read the README notes on 64-bit code generation.
- **Mill.** Any new primary publication that states the distribution format or the time of specialization resolves the unknowns listed under Boundaries.
- **Checker model.** Re-run section 7.3; it is deterministic (fixed random seed). Extending it with branches and joins is the cheapest way to test whether the set-valued analysis still suffices for a given neutral IR.
